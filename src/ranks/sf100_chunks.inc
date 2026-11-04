/* Physical storage only. Logical names and all rank formats are unchanged. */
static char *cf_files_table_sql_ident(void);
typedef struct CfLargeMap {
    MemoryContextCallback cleanup;
    void *address;
    size_t length;
    int fd;
} CfLargeMap;

static void cf_large_map_release(void *arg) {
    CfLargeMap *map=(CfLargeMap *)arg;
    if(map->address && map->length)munmap(map->address,map->length);
    if(map->fd>=0)close(map->fd);
    map->address=NULL;map->fd=-1;
}

static CfLargeMap *cf_large_map_context(MemoryContext context,int fd) {
    CfLargeMap *map=MemoryContextAllocZero(context,sizeof(*map));
    map->fd=fd;map->cleanup.func=cf_large_map_release;map->cleanup.arg=map;
    MemoryContextRegisterResetCallback(context,&map->cleanup);
    return map;
}

static void cf_large_map_finish(CfLargeMap *map,size_t length,MemoryContext context,LoadedArtifact *out) {
    map->length=length;
    if(length) {
        map->address=mmap(NULL,length,PROT_READ,MAP_PRIVATE,map->fd,0);
        if(map->address==MAP_FAILED){map->address=NULL;ereport(ERROR,(errmsg("Cannot map rank artifact: %m")));}
    }
    /* The old ownership checks see a normal small context-owned handle. */
    out->data=MemoryContextAlloc(context,VARHDRSZ);SET_VARSIZE(out->data,VARHDRSZ);
    out->raw_data=map->address;out->len=length;out->owned=true;
}

static bool cf_large_file(const char *name,MemoryContext context,LoadedArtifact *out) {
    char path[MAXPGPATH];struct stat info;
    if(!is_absolute_path(cf_artifact_directory))ereport(ERROR,(errmsg("Artifact directory must be absolute")));
    if(snprintf(path,sizeof(path),"%s/%s",cf_artifact_directory,name)>=sizeof(path))ereport(ERROR,(errmsg("Artifact path too long")));
    int fd=open(path,O_RDONLY|O_CLOEXEC);
    if(fd<0){if(errno==ENOENT)return false;ereport(ERROR,(errmsg("Cannot open rank artifact: %m")));}
    CfLargeMap *map=cf_large_map_context(context,fd);
    if(fstat(fd,&info) || !S_ISREG(info.st_mode) || info.st_size<0 || (uint64)info.st_size>SIZE_MAX)
        ereport(ERROR,(errmsg("Invalid rank artifact file")));
    cf_large_map_finish(map,(size_t)info.st_size,context,out);return true;
}

static bool cf_large_blob(const char *name,MemoryContext context,LoadedArtifact *out) {
    char *relation=cf_files_table_sql_ident();
    char *statement=psprintf("SELECT part_no,total_bytes,file FROM %s WHERE run_id=COALESCE(current_setting('custom_filter_new.run_id',true),'') AND name=$1 ORDER BY part_no",relation);
    Oid types[1]={TEXTOID};Datum values[1]={CStringGetTextDatum(name)};char nulls[1]={' '};
    Portal cursor=SPI_cursor_open_with_args(NULL,statement,1,types,values,nulls,true,0);
    pfree(relation);pfree(statement);
    if(!cursor)ereport(ERROR,(errmsg("Cannot open chunked artifact cursor")));
    CfLargeMap *map=NULL;size_t position=0,total=0;int expected=0;
    for(;;) {
        SPI_cursor_fetch(cursor,true,1);
        if(!SPI_processed)break;
        bool isnull=false;HeapTuple tuple=SPI_tuptable->vals[0];TupleDesc desc=SPI_tuptable->tupdesc;
        Datum part=SPI_getbinval(tuple,desc,1,&isnull);
        if(isnull || DatumGetInt32(part)!=expected++)ereport(ERROR,(errmsg("Non-contiguous rank artifact chunks: %s",name)));
        Datum size=SPI_getbinval(tuple,desc,2,&isnull);
        if(isnull || DatumGetInt64(size)<0 || (uint64)DatumGetInt64(size)>SIZE_MAX)
            ereport(ERROR,(errmsg("Invalid logical rank artifact size")));
        size_t current=(size_t)DatumGetInt64(size);
        if(!map) {
            char directory[MAXPGPATH],path[MAXPGPATH];
            total=current;
            snprintf(directory,sizeof(directory),"%s/base/pgsql_tmp",DataDir);
            if(MakePGDirectory(directory)<0 && errno!=EEXIST)ereport(ERROR,(errmsg("Cannot create artifact spool directory: %m")));
            snprintf(path,sizeof(path),"%s/memento-rank-XXXXXX",directory);
            int fd=mkstemp(path);
            if(fd<0)ereport(ERROR,(errmsg("Cannot create artifact spool: %m")));
            map=cf_large_map_context(context,fd);
            if(unlink(path)<0)ereport(ERROR,(errmsg("Cannot unlink artifact spool: %m")));
            if(ftruncate(fd,(off_t)total)<0)ereport(ERROR,(errmsg("Cannot size artifact spool: %m")));
        } else if(current!=total)ereport(ERROR,(errmsg("Inconsistent rank artifact chunk lengths")));
        Datum data=SPI_getbinval(tuple,desc,3,&isnull);
        if(isnull)ereport(ERROR,(errmsg("NULL rank artifact chunk")));
        bytea *chunk=DatumGetByteaPP(data);size_t length=VARSIZE_ANY_EXHDR(chunk);
        if(length>(64U<<20) || position>total || length>total-position)
            ereport(ERROR,(errmsg("Rank artifact chunk outside its logical file")));
        size_t copied=0;
        while(copied<length) {
            CHECK_FOR_INTERRUPTS();
            ssize_t wrote=pwrite(map->fd,VARDATA_ANY(chunk)+copied,length-copied,(off_t)(position+copied));
            if(wrote<0 && errno==EINTR)continue;
            if(wrote<=0)ereport(ERROR,(errmsg("Rank artifact spool write failed: %m")));
            copied+=(size_t)wrote;
        }
        position+=length;
        if((Pointer)chunk!=DatumGetPointer(data))pfree(chunk);
        SPI_freetuptable(SPI_tuptable);
    }
    SPI_cursor_close(cursor);
    if(!map)return false;
    if(position!=total)ereport(ERROR,(errmsg("Truncated rank artifact chunks: %s",name)));
    cf_large_map_finish(map,total,context,out);return true;
}

static bool cf_load_large_artifacts(char **names,int count,MemoryContext context,LoadedArtifact *out,StringInfo missing) {
    bool complete=true;
    for(int i=0;i<count;++i) {
        if(!pac_artifact_name_allowed(names[i]))ereport(ERROR,(errmsg("Forbidden artifact: %s",names[i])));
        bool found=(cf_artifact_directory && cf_artifact_directory[0]) ?
            cf_large_file(names[i],context,&out[i]) : cf_large_blob(names[i],context,&out[i]);
        if(!found){if(missing && missing->len)appendStringInfoString(missing,", ");if(missing)appendStringInfoString(missing,names[i]);complete=false;}
    }
    return complete;
}

/* A superuser-only physical loader check; it does not evaluate a policy. */
PG_FUNCTION_INFO_V1(sf100_artifact_slice);
Datum sf100_artifact_slice(PG_FUNCTION_ARGS) {
    if(!superuser())ereport(ERROR,(errmsg("Artifact inspection requires superuser")));
    char *name=text_to_cstring(PG_GETARG_TEXT_PP(0));
    int64 offset=PG_GETARG_INT64(1);int length=PG_GETARG_INT32(2);
    if(!pac_artifact_name_allowed(name))ereport(ERROR,(errmsg("Forbidden artifact: %s",name)));
    if(offset<0 || length<0 || length>(1<<20))ereport(ERROR,(errmsg("Invalid artifact slice")));
    MemoryContext context=AllocSetContextCreate(CurrentMemoryContext,"SF100 physical loader check",ALLOCSET_DEFAULT_SIZES);
    LoadedArtifact artifact={0};
    if(SPI_connect()!=SPI_OK_CONNECT)ereport(ERROR,(errmsg("Cannot inspect artifact")));
    bool found=(cf_artifact_directory && cf_artifact_directory[0])?
        cf_large_file(name,context,&artifact):cf_large_blob(name,context,&artifact);
    SPI_finish();
    if(!found)ereport(ERROR,(errmsg("Missing artifact: %s",name)));
    if((uint64)offset>artifact.len || (size_t)length>artifact.len-(size_t)offset)
        ereport(ERROR,(errmsg("Artifact slice out of range")));
    bytea *result=palloc(VARHDRSZ+length);SET_VARSIZE(result,VARHDRSZ+length);
    if(length)memcpy(VARDATA(result),(char*)artifact.raw_data+offset,length);
    MemoryContextDelete(context);pfree(name);PG_RETURN_BYTEA_P(result);
}

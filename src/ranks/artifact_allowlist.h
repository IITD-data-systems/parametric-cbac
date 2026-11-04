#pragma once
#include <stdbool.h>
#include <string.h>

/* Only rank structures, their catalog, and PostgreSQL row locations. */
static inline bool pac_artifact_name_allowed(const char *name) {
    if (!name || !*name || strstr(name,"..") || strchr(name,'\\')) return false;
    if (!strcmp(name,"meta/col_domain") || !strcmp(name,"meta/cols") ||
        !strcmp(name,"meta/join_classes")) return true;
    const char *leaf = NULL;
    if (!strncmp(name,"universe/domain/",16)) leaf=name+16;
    else if (!strncmp(name,"meta/cols/",10)) leaf=name+10;
    if (leaf) return *leaf && !strchr(leaf,'/');
    if (!strncmp(name,"canon_fwdidx/",13)) leaf=name+13;
    else if (!strncmp(name,"canon_invidx/",13)) leaf=name+13;
    if (leaf) {
        const char *slash=strchr(leaf,'/');
        return slash && slash!=leaf && slash[1] && !strchr(slash+1,'/');
    }
    const size_t n=strlen(name);
    return n>5 && !strchr(name,'/') && !strcmp(name+n-5,"_ctid");
}

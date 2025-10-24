
// Policy: l.l_orderkey =o.o_orderkey and o.o_custkey= c.c_custkey and c.c_mktsegment ='AUTOMOBILE'


#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <string>
#include <vector>
#include <array>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <chrono>
#include <filesystem>
#include <cerrno>
#include <algorithm>

#include <cvc5/cvc5.h>
namespace fs = std::filesystem;
namespace api = cvc5;

//---------------- helpers ----------------
static std::string slurp(const fs::path& p){
  std::ifstream in(p, std::ios::binary);
  if(!in) throw std::runtime_error("open: "+p.string());
  in.seekg(0,std::ios::end);
  std::string s; s.resize((size_t)in.tellg());
  in.seekg(0,std::ios::beg);
  if(!s.empty()) in.read(&s[0], (std::streamsize)s.size());
  return s;
}
static std::vector<uint8_t> read_file_bytes(const fs::path& p){
  std::ifstream in(p, std::ios::binary);
  if(!in) throw std::runtime_error("open: "+p.string());
  in.seekg(0,std::ios::end);
  size_t n = (size_t)in.tellg();
  std::vector<uint8_t> buf(n);
  in.seekg(0,std::ios::beg);
  if(n>0) in.read((char*)buf.data(), (std::streamsize)n);
  return buf;
}
static int col_index(const std::string& schema_json, const std::string& name){
  const std::string key = "\"name\"";
  size_t pos=0; int idx=0;
  while(true){
    size_t k = schema_json.find(key, pos); if(k==std::string::npos) break;
    size_t c = schema_json.find(':', k+key.size()); if(c==std::string::npos) break;
    size_t q1 = schema_json.find('"', c+1); if(q1==std::string::npos) break;
    size_t q2 = schema_json.find('"', q1+1); if(q2==std::string::npos) break;
    std::string val = schema_json.substr(q1+1, q2-q1-1);
    if(val==name) return idx;
    ++idx; pos=q2+1;
  }
  throw std::out_of_range("Column not found in schema: "+name);
}

//---------------- minimal .npy readers: 1D domain + 2D codes(int32) ----------------
struct Npy1D {
  size_t data_offset{0}, count{0}, itemsize{0};
  enum class DType { BYTES, UNICODE, I64, U64, I32, U32, I16, U16, I8, U8, F32, F64, BOOL } dt{DType::BYTES};
  char endian{'|'}; // '<' little, '>' big, '|' n/a
};
static Npy1D parse_npy_1d(const std::vector<uint8_t>& buf){
  auto bad=[&](const char* m){ throw std::runtime_error(std::string("npy: ")+m); };
  if(buf.size()<14) bad("too small");
  const uint8_t* p = buf.data();
  const char magic[6] = {'\x93','N','U','M','P','Y'};
  for(int i=0;i<6;++i) if(p[i]!=(uint8_t)magic[i]) bad("bad magic");
  uint8_t maj=p[6], min=p[7]; size_t off=8; uint64_t hlen=0;
  if(maj==1&&min==0){ uint16_t t=p[8]|(p[9]<<8); hlen=t; off=10; }
  else if(maj==2&&min==0){ uint32_t t=p[8]|(p[9]<<8)|(p[10]<<16)|(p[11]<<24); hlen=t; off=12; }
  else bad("only v1.0/v2.0 supported");
  if(buf.size()<off+hlen) bad("short header");
  std::string header((const char*)p+off, (size_t)hlen);
  auto findv=[&](const std::string& k)->std::string{
    auto a = header.find("'"+k+"'"); if(a==std::string::npos) bad(("missing "+k).c_str());
    auto c = header.find(':', a); auto s=header.find("'", c+1); auto e=header.find("'", s+1);
    return header.substr(s+1, e-s-1);
  };
  auto findb=[&](const std::string& k)->bool{
    auto a = header.find("'"+k+"'"); if(a==std::string::npos) bad(("missing "+k).c_str());
    auto c = header.find(':', a); auto t=header.find_first_not_of(" \t", c+1);
    if(header.compare(t,4,"True")==0) return true;
    if(header.compare(t,5,"False")==0) return false;
    bad("bad bool"); return false;
  };
  auto shapesz=[&]()->size_t{
    auto a=header.find("'shape'"); if(a==std::string::npos) bad("missing shape");
    auto lp=header.find('(',a), rp=header.find(')',lp);
    std::string inside=header.substr(lp+1,rp-lp-1);
    size_t i=0, n=0;
    while(i<inside.size()){
      while(i<inside.size() && (inside[i]==','||isspace((unsigned char)inside[i]))) ++i;
      size_t j=i; while(j<inside.size() && isdigit((unsigned char)inside[j])) ++j;
      if(j>i){ ++n; } i=j+1;
    }
    if(n!=1) bad("expect 1D");
    size_t k1=inside.find_first_of("0123456789");
    size_t k2=k1; while(k2<inside.size() && isdigit((unsigned char)inside[k2])) ++k2;
    return (size_t)std::stoull(inside.substr(k1,k2-k1));
  };

  Npy1D h;
  std::string descr = findv("descr");
  h.endian = descr.size()?descr[0]:'|';
  std::string base  = descr.size()>=2?descr.substr(1):"";
  if(base.size() && (base[0]=='S')){ h.dt=Npy1D::DType::BYTES;   h.itemsize=(size_t)std::stoull(base.substr(1)); }
  else if(base.size() && (base[0]=='U')){ h.dt=Npy1D::DType::UNICODE; h.itemsize=4*(size_t)std::stoull(base.substr(1)); }
  else if(descr=="<i8"||descr==">i8"||descr=="|i8"){ h.dt=Npy1D::DType::I64; h.itemsize=8; }
  else if(descr=="<u8"||descr==">u8"||descr=="|u8"){ h.dt=Npy1D::DType::U64; h.itemsize=8; }
  else if(descr=="<i4"||descr==">i4"||descr=="|i4"){ h.dt=Npy1D::DType::I32; h.itemsize=4; }
  else if(descr=="<u4"||descr==">u4"||descr=="|u4"){ h.dt=Npy1D::DType::U32; h.itemsize=4; }
  else if(descr=="<i2"||descr==">i2"||descr=="|i2"){ h.dt=Npy1D::DType::I16; h.itemsize=2; }
  else if(descr=="<u2"||descr==">u2"||descr=="|u2"){ h.dt=Npy1D::DType::U16; h.itemsize=2; }
  else if(descr=="<i1"||descr==">i1"||descr=="|i1"){ h.dt=Npy1D::DType::I8;  h.itemsize=1; }
  else if(descr=="<u1"||descr==">u1"||descr=="|u1"){ h.dt=Npy1D::DType::U8;  h.itemsize=1; }
  else if(descr=="<f4"||descr==">f4"||descr=="|f4"){ h.dt=Npy1D::DType::F32; h.itemsize=4; }
  else if(descr=="<f8"||descr==">f8"||descr=="|f8"){ h.dt=Npy1D::DType::F64; h.itemsize=8; }
  else if(descr=="|b1"){ h.dt=Npy1D::DType::BOOL; h.itemsize=1; }
  else throw std::runtime_error("npy: unsupported descr "+descr);
  (void)findb("fortran_order"); // 1D domain — order irrelevant
  h.count = shapesz();
  h.data_offset = (size_t)(off+hlen);
  return h;
}

struct Npy2D {
  size_t data_offset{0}, rows{0}, cols{0};
};
static Npy2D parse_npy_2d_i32_header(std::ifstream& in){
  char magic[6]; if(!in.read(magic,6)) throw std::runtime_error("npy: short read (magic)");
  const char exp[6]={'\x93','N','U','M','P','Y'}; for(int i=0;i<6;++i) if(magic[i]!=exp[i]) throw std::runtime_error("npy: bad magic");
  unsigned char v[2]; if(!in.read((char*)v,2)) throw std::runtime_error("npy: short read (ver)");
  uint64_t hlen=0; size_t off=8;
  if(v[0]==1&&v[1]==0){ uint16_t t; if(!in.read((char*)&t,2)) throw std::runtime_error("npy: short read (hlen)"); hlen=t; off=10; }
  else if(v[0]==2&&v[1]==0){ uint32_t t; if(!in.read((char*)&t,4)) throw std::runtime_error("npy: short read (hlen)"); hlen=t; off=12; }
  else throw std::runtime_error("npy: only v1.0/v2.0 supported");
  std::string hdr; hdr.resize((size_t)hlen); if(!in.read(hdr.data(),(std::streamsize)hlen)) throw std::runtime_error("npy: short read (header)");
  if(hdr.find("<i4")==std::string::npos && hdr.find("|i4")==std::string::npos) throw std::runtime_error("codes.npy must be <i4/|i4");
  if(hdr.find("'fortran_order': False")==std::string::npos) throw std::runtime_error("fortran_order must be False");
  auto shp=hdr.find("'shape'"); auto lp=hdr.find('(',shp), rp=hdr.find(')',lp);
  std::string inside=hdr.substr(lp+1,rp-lp-1);
  size_t i=0; std::vector<size_t> dims; while(i<inside.size()){
    while(i<inside.size() && (inside[i]==','||isspace((unsigned char)inside[i]))) ++i;
    size_t j=i; while(j<inside.size() && isdigit((unsigned char)inside[j])) ++j;
    if(j>i){ dims.push_back((size_t)std::stoull(inside.substr(i,j-i))); }
    i=j+1;
  }
  if(dims.size()!=2) throw std::runtime_error("codes.npy must be 2D");
  Npy2D m; m.rows=dims[0]; m.cols=dims[1]; m.data_offset=(size_t)in.tellg();
  return m;
}

// decode dict token utilities
static bool dict_token_is_AUTOMOBILE(const Npy1D& h, const std::vector<uint8_t>& buf, int32_t code){
  if(code<0 || (size_t)code>=h.count) return false;
  const uint8_t* base = buf.data() + h.data_offset + (size_t)code * h.itemsize;
  std::string s;
  switch(h.dt){
    case Npy1D::DType::BYTES: {
      s.assign((const char*)base, h.itemsize);
      size_t j=h.itemsize; while(j>0 && (s[j-1]=='\0' || s[j-1]==' ')) --j; s.resize(j);
      break;
    }
    case Npy1D::DType::UNICODE: {
      int items = (int)(h.itemsize/4);
      for(int k=0;k<items;++k){ uint32_t cp = base[4*k]; if(cp==0) break; s.push_back(cp<128 ? char(cp) : '?'); }
      break;
    }
    default: return false;
  }
  return s=="AUTOMOBILE";
}
static bool dict_decode_i64(const Npy1D& h, const std::vector<uint8_t>& buf, int32_t code, int64_t& out){
  if(code<0 || (size_t)code>=h.count) return false;
  const uint8_t* base = buf.data() + h.data_offset + (size_t)code * h.itemsize;
  switch(h.dt){
    case Npy1D::DType::BYTES: {
      std::string s((const char*)base, h.itemsize);
      size_t j=h.itemsize; while(j>0 && (s[j-1]=='\0' || s[j-1]==' ')) --j; s.resize(j);
      if(s.empty()) return false; char* e=nullptr; long long v=strtoll(s.c_str(), &e, 10); if(!e||*e!='\0') return false; out=(int64_t)v; return true;
    }
    case Npy1D::DType::UNICODE: return false;
    case Npy1D::DType::I8:  out=*(const int8_t*)base; return true;
    case Npy1D::DType::U8:  out=*(const uint8_t*)base; return true;
    case Npy1D::DType::I16: out=*(const int16_t*)base; return true;
    case Npy1D::DType::U16: out=*(const uint16_t*)base; return true;
    case Npy1D::DType::I32: out=*(const int32_t*)base; return true;
    case Npy1D::DType::U32: out=(int64_t)*(const uint32_t*)base; return true;
    case Npy1D::DType::I64: out=*(const int64_t*)base; return true;
    case Npy1D::DType::U64: out=(int64_t)*(const uint64_t*)base; return true;
    case Npy1D::DType::F32: out=(int64_t)llround(*(const float*)base); return true;
    case Npy1D::DType::F64: out=(int64_t)llround(*(const double*)base); return true;
    case Npy1D::DType::BOOL: out = (*(const uint8_t*)base)!=0; return true;
  }
  return false;
}

int main(int argc, char** argv){
  const auto T0 = std::chrono::steady_clock::now();

  const fs::path LDIR = (argc>1? fs::path(argv[1]) : fs::path("tables10/lineitem"));
  const fs::path ODIR = (argc>2? fs::path(argv[2]) : fs::path("tables10/orders"));
  const fs::path CDIR = (argc>3? fs::path(argv[3]) : fs::path("tables10/customer"));

  // Schemas
  const std::string schemaL = slurp(LDIR / "schema.json");
  const std::string schemaO = slurp(ODIR / "schema.json");
  const std::string schemaC = slurp(CDIR / "schema.json");

  const std::string L_OK="l_orderkey", L_LN="l_linenumber";
  const std::string O_OK="o_orderkey", O_CK="o_custkey";
  const std::string C_CK="c_custkey", C_SEG="c_mktsegment";

  const int i_l_ok = col_index(schemaL, L_OK);
  const int i_l_ln = col_index(schemaL, L_LN);
  const int i_o_ok = col_index(schemaO, O_OK);
  const int i_o_ck = col_index(schemaO, O_CK);
  const int i_c_ck = col_index(schemaC, C_CK);
  const int i_c_seg= col_index(schemaC, C_SEG);


  const std::vector<uint8_t> l_ok_buf = read_file_bytes(LDIR / (L_OK + ".npy"));
  const std::vector<uint8_t> l_ln_buf = read_file_bytes(LDIR / (L_LN + ".npy"));
  const std::vector<uint8_t> o_ok_buf = read_file_bytes(ODIR / (O_OK + ".npy"));
  const std::vector<uint8_t> o_ck_buf = read_file_bytes(ODIR / (O_CK + ".npy"));
  const std::vector<uint8_t> c_ck_buf = read_file_bytes(CDIR / (C_CK + ".npy"));
  const std::vector<uint8_t> c_seg_buf= read_file_bytes(CDIR / (C_SEG + ".npy"));

  const Npy1D l_okDom = parse_npy_1d(l_ok_buf);
  const Npy1D l_lnDom = parse_npy_1d(l_ln_buf);
  const Npy1D o_okDom = parse_npy_1d(o_ok_buf);
  const Npy1D o_ckDom = parse_npy_1d(o_ck_buf);
  const Npy1D c_ckDom = parse_npy_1d(c_ck_buf);
  const Npy1D c_segDom= parse_npy_1d(c_seg_buf);

  // codes.npy 
  auto open_codes = [&](const fs::path& dir)->std::pair<Npy2D,std::ifstream*>{
    std::ifstream* in = new std::ifstream(dir/"codes.npy", std::ios::binary);
    if(!*in) throw std::runtime_error("open codes.npy at: "+dir.string());
    Npy2D m = parse_npy_2d_i32_header(*in);
    return {m,in};
  };
  auto Lc = open_codes(LDIR);
  auto Oc = open_codes(ODIR);
  auto Cc = open_codes(CDIR);
  Npy2D Lm=Lc.first, Om=Oc.first, Cm=Cc.first;
  std::ifstream& Lin=*Lc.second; std::ifstream& Oin=*Oc.second; std::ifstream& Cin=*Cc.second;

  // Stream codes for columns we need
  std::vector<int32_t> L_ok_code, L_ln_code;
  L_ok_code.reserve(Lm.rows); L_ln_code.reserve(Lm.rows);
  {
    const size_t rowbytes = Lm.cols*sizeof(int32_t);
    std::vector<int32_t> row(Lm.cols);
    Lin.seekg((std::streamoff)Lm.data_offset, std::ios::beg);
    for(size_t r=0;r<Lm.rows;++r){
      if(!Lin.read((char*)row.data(), (std::streamsize)rowbytes)) throw std::runtime_error("short read L codes");
      L_ok_code.push_back(row[i_l_ok]);
      L_ln_code.push_back(row[i_l_ln]);
    }
  }

  std::vector<int32_t> O_ok_code, O_ck_code;
  O_ok_code.reserve(Om.rows); O_ck_code.reserve(Om.rows);
  {
    const size_t rowbytes = Om.cols*sizeof(int32_t);
    std::vector<int32_t> row(Om.cols);
    Oin.seekg((std::streamoff)Om.data_offset, std::ios::beg);
    for(size_t r=0;r<Om.rows;++r){
      if(!Oin.read((char*)row.data(), (std::streamsize)rowbytes)) throw std::runtime_error("short read O codes");
      O_ok_code.push_back(row[i_o_ok]);
      O_ck_code.push_back(row[i_o_ck]);
    }
  }

  std::vector<int32_t> C_ck_code, C_seg_code;
  C_ck_code.reserve(Cm.rows); C_seg_code.reserve(Cm.rows);
  {
    const size_t rowbytes = Cm.cols*sizeof(int32_t);
    std::vector<int32_t> row(Cm.cols);
    Cin.seekg((std::streamoff)Cm.data_offset, std::ios::beg);
    for(size_t r=0;r<Cm.rows;++r){
      if(!Cin.read((char*)row.data(), (std::streamsize)rowbytes)) throw std::runtime_error("short read C codes");
      C_ck_code.push_back(row[i_c_ck]);
      C_seg_code.push_back(row[i_c_seg]);
    }
  }
  Lin.close(); Oin.close(); Cin.close();

  const auto T1 = std::chrono::steady_clock::now(); // end load

  // Row stamp (Customer): T_C_segA[r]
  std::vector<uint8_t> T_C_segA(C_seg_code.size(), 0);
  for(size_t r=0;r<C_seg_code.size();++r){
    int32_t tid = C_seg_code[r];
    T_C_segA[r] = dict_token_is_AUTOMOBILE(c_segDom, c_seg_buf, tid) ? 1 : 0;
  }

  const auto T2 = std::chrono::steady_clock::now(); // end row stamps

  // ok across Lineitem/Orders; ck across Orders/Customer
  std::unordered_map<int64_t,int> ok_val2gid; ok_val2gid.reserve(l_okDom.count + o_okDom.count);
  std::unordered_map<int64_t,int> ck_val2gid; ck_val2gid.reserve(o_ckDom.count + c_ckDom.count);
  std::vector<int> L_ok_tid2gid(l_okDom.count, -1), O_ok_tid2gid(o_okDom.count, -1);
  std::vector<int> O_ck_tid2gid(o_ckDom.count, -1), C_ck_tid2gid(c_ckDom.count, -1);
  int next_ok_gid=0, next_ck_gid=0;

  auto add_domain_gid = [&](const Npy1D& dom, const std::vector<uint8_t>& buf,
                            std::unordered_map<int64_t,int>& val2gid, std::vector<int>& tid2gid, int& next_gid){
    for(size_t t=0;t<dom.count;++t){
      int64_t v=0; if(!dict_decode_i64(dom, buf, (int32_t)t, v))
        throw std::runtime_error("domain must be numeric (token decode failed)");
      auto it = val2gid.find(v);
      if(it==val2gid.end()){ it = val2gid.emplace(v, next_gid++).first; }
      tid2gid[t] = it->second;
    }
  };
  add_domain_gid(l_okDom, l_ok_buf, ok_val2gid, L_ok_tid2gid, next_ok_gid);
  add_domain_gid(o_okDom, o_ok_buf, ok_val2gid, O_ok_tid2gid, next_ok_gid);
  add_domain_gid(o_ckDom, o_ck_buf, ck_val2gid, O_ck_tid2gid, next_ck_gid);
  add_domain_gid(c_ckDom, c_ck_buf, ck_val2gid, C_ck_tid2gid, next_ck_gid);

  auto L_row_ok_gid = [&](size_t r)->int{
    int32_t tid=L_ok_code[r]; if(tid<0 || (size_t)tid>=L_ok_tid2gid.size()) return -1; return L_ok_tid2gid[tid];
  };
  auto O_row_ok_gid = [&](size_t r)->int{
    int32_t tid=O_ok_code[r]; if(tid<0 || (size_t)tid>=O_ok_tid2gid.size()) return -1; return O_ok_tid2gid[tid];
  };
  auto O_row_ck_gid = [&](size_t r)->int{
    int32_t tid=O_ck_code[r]; if(tid<0 || (size_t)tid>=O_ck_tid2gid.size()) return -1; return O_ck_tid2gid[tid];
  };
  auto C_row_ck_gid = [&](size_t r)->int{
    int32_t tid=C_ck_code[r]; if(tid<0 || (size_t)tid>=C_ck_tid2gid.size()) return -1; return C_ck_tid2gid[tid];
  };

  //  per-ck flag that some Customer row at ck has seg='AUTOMOBILE'
  std::vector<uint8_t> CK_has_segA(next_ck_gid, 0);
  for(size_t r=0;r<C_ck_code.size();++r){
    if(!T_C_segA[r]) continue;
    int j = C_row_ck_gid(r); if(j>=0) CK_has_segA[j] = 1;
  }

  //  adjacency from Orders rows: ok_gid -> {ck_gid}
  std::vector<std::unordered_set<int>> OK_to_CK(next_ok_gid);
  std::vector<uint8_t> OK_has_O(next_ok_gid, 0);
  for(size_t r=0;r<O_ok_code.size();++r){
    int i = O_row_ok_gid(r); if(i<0) continue;
    int j = O_row_ck_gid(r); if(j<0) continue;
    OK_to_CK[i].insert(j);
    OK_has_O[i] = 1;
  }

  const auto T3 = std::chrono::steady_clock::now(); // end hub build

  // Signature bits over I_ok (gid)
  enum : uint8_t {
    BIT_Y1 = 1u<<0, 
    BIT_Y3 = 1u<<1, 
    BIT_Y5 = 1u<<2  
  };
  std::unordered_map<int, uint8_t> sig; sig.reserve(4096);

  // Y1
  for(size_t r=0;r<L_ok_code.size();++r){
    int i=L_row_ok_gid(r); if(i<0) continue;
    sig[i] |= BIT_Y1;
  }
  // Y3 and Y5
  for(int i=0;i<next_ok_gid;++i){
    if(OK_has_O[i]) sig[i] |= BIT_Y3;
    if(!OK_to_CK[i].empty()){
      for(int j : OK_to_CK[i]){
        if(j>=0 && j<next_ck_gid && CK_has_segA[j]){ sig[i] |= BIT_Y5; break; }
      }
    }
  }

  const auto T4 = std::chrono::steady_clock::now(); // end signatures

  // Binning
  std::unordered_map<uint8_t, std::vector<int>> bins; bins.reserve(16);
  for(auto& kv : sig) bins[kv.second].push_back(kv.first);

  const auto T5 = std::chrono::steady_clock::now(); // end binning

  // SAT per class
  api::TermManager tm; api::Solver slv(tm);
  slv.setOption("produce-models","true");
  slv.setLogic("QF_UF"); 
  const api::Sort B = tm.getBooleanSort();

  std::unordered_map<uint8_t, api::Term> X;
  for(auto& kv : bins){
    uint8_t s = kv.first;
    bool y1 = (s & BIT_Y1)!=0;
    bool y3 = (s & BIT_Y3)!=0;
    bool y5 = (s & BIT_Y5)!=0;

    api::Term Xs   = tm.mkConst(B, "X_"+std::to_string((int)s));
    api::Term c1   = tm.mkBoolean(y1);
    api::Term c3   = tm.mkBoolean(y3);
    api::Term c5   = tm.mkBoolean(y5);
    api::Term andA = tm.mkTerm(api::Kind::AND, std::vector<api::Term>{ c1, c3, c5 });
    api::Term eq   = tm.mkTerm(api::Kind::EQUAL, std::vector<api::Term>{ Xs, andA });
    slv.assertFormula(eq);
    X[s]=Xs;
  }
  auto satres = slv.checkSat();
  if(!satres.isSat()) throw std::runtime_error("UNSAT on class constraints (unexpected)");

  std::unordered_set<int> S_ok_gid; S_ok_gid.reserve(sig.size());
  for(auto& kv : bins){
    uint8_t s = kv.first; api::Term Xs = X[s];
    auto v = slv.getValue(Xs);
    if(v.isBooleanValue() && v.getBooleanValue()){
      for(int gid : kv.second) S_ok_gid.insert(gid);
    }
  }

  const auto T6 = std::chrono::steady_clock::now(); // end solve

  // Projection
  std::ofstream out("result.txt"); if(!out) throw std::runtime_error("open result.txt");
  auto flush_pair = [&](int32_t ok_tid, int32_t ln_tid){
    int64_t okv=0, lnv=0;
    if(!dict_decode_i64(l_okDom, l_ok_buf, ok_tid, okv)) return;
    if(!dict_decode_i64(l_lnDom, l_ln_buf, ln_tid, lnv)) return;
    out << okv << "," << lnv << "\n";
  };
  for(size_t r=0;r<L_ok_code.size();++r){
    int i = L_row_ok_gid(r); if(i<0) continue;
    if(S_ok_gid.find(i)!=S_ok_gid.end()) flush_pair(L_ok_code[r], L_ln_code[r]);
  }
  out.close();

  const auto T7 = std::chrono::steady_clock::now();
  std::cout<<"Phase(load):   "<<std::chrono::duration_cast<std::chrono::milliseconds>(T1-T0).count()<<" ms\n";
  std::cout<<"Phase(stamp):  "<<std::chrono::duration_cast<std::chrono::milliseconds>(T2-T1).count()<<" ms\n";
  std::cout<<"Phase(hubs):   "<<std::chrono::duration_cast<std::chrono::milliseconds>(T3-T2).count()<<" ms\n";
  std::cout<<"Phase(sign):   "<<std::chrono::duration_cast<std::chrono::milliseconds>(T4-T3).count()<<" ms\n";
  std::cout<<"Phase(bin):    "<<std::chrono::duration_cast<std::chrono::milliseconds>(T5-T4).count()<<" ms\n";
  std::cout<<"Phase(assert): "<<std::chrono::duration_cast<std::chrono::milliseconds>(T6-T5).count()<<" ms\n";
  std::cout<<"Phase(write):  "<<std::chrono::duration_cast<std::chrono::milliseconds>(T7-T6).count()<<" ms\n";
  std::cout<<"Total:         "<<std::chrono::duration_cast<std::chrono::milliseconds>(T7-T0).count()<<" ms\n";
  return 0;
}

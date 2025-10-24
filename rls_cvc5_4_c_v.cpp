//  policy: l.l_orderkey = o.o_orderkey and o.o_orderstatus = 'O'

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
  char endian{'|'}; // '<' little, '>' big, '|' not applicable
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
static bool dict_token_is_O(const Npy1D& h, const std::vector<uint8_t>& buf, int32_t code){
  if(code<0 || (size_t)code>=h.count) return false;
  const uint8_t* base = buf.data() + h.data_offset + (size_t)code * h.itemsize;
  switch(h.dt){
    case Npy1D::DType::BYTES:   return h.itemsize>0 && base[0]=='O';
    case Npy1D::DType::UNICODE: return h.itemsize>=4 && base[0]=='O'; // UTF-32LE: 'O' byte first on LE
    case Npy1D::DType::I8:  return *(const int8_t*)base == 79;
    case Npy1D::DType::U8:  return *(const uint8_t*)base == 79u;
    case Npy1D::DType::I16: return *(const int16_t*)base == 79;
    case Npy1D::DType::U16: return *(const uint16_t*)base == 79u;
    case Npy1D::DType::I32: return *(const int32_t*)base == 79;
    case Npy1D::DType::U32: return *(const uint32_t*)base == 79u;
    case Npy1D::DType::I64: return *(const int64_t*)base == 79;
    case Npy1D::DType::U64: return *(const uint64_t*)base == 79u;
    case Npy1D::DType::F32: case Npy1D::DType::F64: case Npy1D::DType::BOOL: return false;
  }
  return false;
}
static bool dict_decode_i64(const Npy1D& h, const std::vector<uint8_t>& buf, int32_t code, int64_t& out){
  if(code<0 || (size_t)code>=h.count) return false;
  const uint8_t* base = buf.data() + h.data_offset + (size_t)code * h.itemsize;
  switch(h.dt){
    case Npy1D::DType::BYTES: {
      std::string s((const char*)base, h.itemsize);
      size_t j=h.itemsize; while(j>0 && (s[j-1]=='\0' || s[j-1]==' ')) --j;
      s.resize(j);
      if(s.empty()) return false;
      char* e=nullptr; long long v=strtoll(s.c_str(), &e, 10); if(!e || *e!='\0') return false; out=(int64_t)v; return true;
    }
    case Npy1D::DType::UNICODE: return false; // assume ok/ln numeric domains
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

  // Schemas
  const std::string schemaL = slurp(LDIR / "schema.json");
  const std::string schemaO = slurp(ODIR / "schema.json");

  const std::string L_OK="l_orderkey", L_LN="l_linenumber";
  const std::string O_OK="o_orderkey", O_OS="o_orderstatus";

  const int i_l_ok = col_index(schemaL, L_OK);
  const int i_l_ln = col_index(schemaL, L_LN);
  const int i_o_ok = col_index(schemaO, O_OK);
  const int i_o_os = col_index(schemaO, O_OS);

   const std::vector<uint8_t> l_ok_buf = read_file_bytes(LDIR / (L_OK + ".npy"));
  const std::vector<uint8_t> l_ln_buf = read_file_bytes(LDIR / (L_LN + ".npy"));
  const std::vector<uint8_t> o_ok_buf = read_file_bytes(ODIR / (O_OK + ".npy"));
  const std::vector<uint8_t> o_os_buf = read_file_bytes(ODIR / (O_OS + ".npy"));

  const Npy1D l_okDom = parse_npy_1d(l_ok_buf);
  const Npy1D l_lnDom = parse_npy_1d(l_ln_buf);
  const Npy1D o_okDom = parse_npy_1d(o_ok_buf);
  const Npy1D o_osDom = parse_npy_1d(o_os_buf);

  // codes.npy 
  auto open_codes = [&](const fs::path& dir)->std::pair<Npy2D,std::ifstream*>{
    std::ifstream* in = new std::ifstream(dir/"codes.npy", std::ios::binary);
    if(!*in) throw std::runtime_error("open codes.npy at: "+dir.string());
    Npy2D m = parse_npy_2d_i32_header(*in);
    return {m,in};
  };
  auto Lc = open_codes(LDIR); auto Oc = open_codes(ODIR);
  Npy2D Lm=Lc.first, Om=Oc.first;
  std::ifstream& Lin=*Lc.second; std::ifstream& Oin=*Oc.second;

  // Stream codes into column vectors we need
  std::vector<int32_t> L_ok_code, L_ln_code; L_ok_code.reserve(Lm.rows); L_ln_code.reserve(Lm.rows);
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
  std::vector<int32_t> O_ok_code, O_os_code; O_ok_code.reserve(Om.rows); O_os_code.reserve(Om.rows);
  {
    const size_t rowbytes = Om.cols*sizeof(int32_t);
    std::vector<int32_t> row(Om.cols);
    Oin.seekg((std::streamoff)Om.data_offset, std::ios::beg);
    for(size_t r=0;r<Om.rows;++r){
      if(!Oin.read((char*)row.data(), (std::streamsize)rowbytes)) throw std::runtime_error("short read O codes");
      O_ok_code.push_back(row[i_o_ok]);
      O_os_code.push_back(row[i_o_os]);
    }
  }
  Lin.close(); Oin.close();

  const auto T1 = std::chrono::steady_clock::now(); // end load

  // Row truth for Orders: ost == 'O' (stamp once using domain token)
  std::vector<uint8_t> TO_ostO; TO_ostO.resize(O_os_code.size(), 0);
  for(size_t r=0;r<O_os_code.size();++r){
    int32_t tid = O_os_code[r];
    TO_ostO[r] = dict_token_is_O(o_osDom, o_os_buf, tid) ? 1 : 0;
  }

  const auto T2 = std::chrono::steady_clock::now(); // end row truth

  std::unordered_map<int32_t,uint8_t> sig; sig.reserve(4096);
  for(size_t r=0;r<L_ok_code.size();++r){ int32_t i=L_ok_code[r]; if(i>=0) sig[i]|=0b001; }
  for(size_t r=0;r<O_ok_code.size();++r){
    int32_t i=O_ok_code[r]; if(i<0) continue;
    uint8_t& b = sig[i]; b |= 0b010; if(TO_ostO[r]) b |= 0b100;
  }

  const auto T3 = std::chrono::steady_clock::now(); // end signatures

  // Binning
  std::unordered_map<uint8_t,std::vector<int32_t>> bins; bins.reserve(8);
  for(auto& kv: sig) bins[kv.second].push_back(kv.first);

  const auto T4 = std::chrono::steady_clock::now(); // end binning

  // SAT per class
  api::TermManager tm; api::Solver slv(tm); slv.setLogic("QF_UF"); slv.setOption("produce-models","true");
  const api::Sort B = tm.getBooleanSort();
  std::unordered_map<uint8_t, api::Term> X;
  for(auto& kv: bins){
    uint8_t s = kv.first;
    bool y1 = (s & 0b001)!=0;
    bool y4 = (s & 0b100)!=0;
    api::Term Xs = tm.mkConst(B, "X_"+std::to_string((int)s));
    api::Term And = tm.mkTerm(api::Kind::AND, std::vector<api::Term>{ tm.mkBoolean(y1), tm.mkBoolean(y4) });
    api::Term Eq  = tm.mkTerm(api::Kind::EQUAL, std::vector<api::Term>{ Xs, And });
    slv.assertFormula(Eq);
    X[s]=Xs;
  }
  auto satres = slv.checkSat();
  if(!satres.isSat()) throw std::runtime_error("UNSAT on class constraints (unexpected)");

  std::unordered_set<int32_t> S_ok; S_ok.reserve(sig.size());
  for(auto& kv: bins){
    uint8_t s = kv.first; api::Term Xs = X[s];
    auto v = slv.getValue(Xs);
    if(v.isBooleanValue() && v.getBooleanValue()){ for(int32_t i: kv.second) S_ok.insert(i); }
  }

  const auto T5 = std::chrono::steady_clock::now(); // end solve

  // Projection: emit Lineitem rows with ok in S_ok (decoded values)
  std::ofstream out("result.txt"); if(!out) throw std::runtime_error("open result.txt");
  auto flush_pair = [&](int32_t okc, int32_t lnc){
    int64_t okv=0, lnv=0;
    if(!dict_decode_i64(l_okDom, l_ok_buf, okc, okv)) return;
    if(!dict_decode_i64(l_lnDom, l_ln_buf, lnc, lnv)) return;
    out << okv << "," << lnv << "\n";
  };
  for(size_t r=0;r<L_ok_code.size();++r){
    int32_t okc=L_ok_code[r]; if(okc<0) continue;
    if(S_ok.find(okc)!=S_ok.end()) flush_pair(okc, L_ln_code[r]);
  }
  out.close();

  const auto T6 = std::chrono::steady_clock::now();
  std::cout<<"Phase(load):   "<<std::chrono::duration_cast<std::chrono::milliseconds>(T1-T0).count()<<" ms\n";
  std::cout<<"Phase(row):    "<<std::chrono::duration_cast<std::chrono::milliseconds>(T2-T1).count()<<" ms\n";
  std::cout<<"Phase(sign):   "<<std::chrono::duration_cast<std::chrono::milliseconds>(T3-T2).count()<<" ms\n";
  std::cout<<"Phase(bin):    "<<std::chrono::duration_cast<std::chrono::milliseconds>(T4-T3).count()<<" ms\n";
  std::cout<<"Phase(assert): "<<std::chrono::duration_cast<std::chrono::milliseconds>(T5-T4).count()<<" ms\n";
  std::cout<<"Phase(write):  "<<std::chrono::duration_cast<std::chrono::milliseconds>(T6-T5).count()<<" ms\n";
  std::cout<<"Total: "<<std::chrono::duration_cast<std::chrono::milliseconds>(T6-T0).count()<<" ms\n";
  return 0;
}

#include <bits/stdc++.h>
using namespace std;

struct V256 {
    uint64_t w[4]{};
    bool operator==(V256 const& o) const { return memcmp(w,o.w,sizeof(w))==0; }
};
struct VHash {
    size_t operator()(V256 const& v) const noexcept {
        uint64_t h=0x9e3779b97f4a7c15ULL;
        for(int i=0;i<4;i++) { uint64_t x=v.w[i]+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2); h^=x; }
        return (size_t)h;
    }
};
struct VLess {
    bool operator()(V256 const&a,V256 const&b) const {
        for(int i=3;i>=0;i--) if(a.w[i]!=b.w[i]) return a.w[i]<b.w[i];
        return false;
    }
};
static inline V256 vx(V256 a,V256 const& b){ for(int i=0;i<4;i++) a.w[i]^=b.w[i]; return a; }
static inline V256 va(V256 a,V256 const& b){ for(int i=0;i<4;i++) a.w[i]&=b.w[i]; return a; }
static inline bool zero(V256 const&a){ return !(a.w[0]|a.w[1]|a.w[2]|a.w[3]); }
static inline int pivot(V256 const&a){ for(int i=3;i>=0;i--) if(a.w[i]) return i*64 + 63-__builtin_clzll(a.w[i]); return -1; }
static inline bool bit(V256 const&a,int p){ return (a.w[p>>6]>>(p&63))&1ULL; }
static inline void setbit(V256 &a,int p){ a.w[p>>6] |= 1ULL<<(p&63); }

struct Basis {
    array<V256,256> row{};
    array<uint8_t,256> has{};
    int dim=0;
    V256 reduce(V256 x) const {
        for(int p=255;p>=0;p--) if(has[p] && bit(x,p)) x=vx(x,row[p]);
        return x;
    }
    bool insert(V256 x){
        x=reduce(x); if(zero(x)) return false;
        int p=pivot(x);
        // eliminate pivot from other rows for canonical RREF
        for(int q=0;q<256;q++) if(has[q] && bit(row[q],p)) row[q]=vx(row[q],x);
        row[p]=x; has[p]=1; dim++;
        return true;
    }
    vector<V256> vectors() const { vector<V256> v; v.reserve(dim); for(int p=255;p>=0;p--) if(has[p]) v.push_back(row[p]); return v; }
};

struct State {
    Basis V;
    int targetDim=0;
};

static Basis AFF, W;
static vector<V256> TARGET;
static size_t canonical_stabilizer_size=0;

static int intersection_dim(Basis const&A,Basis const&B){
    Basis C=A; for(auto &v:B.vectors()) C.insert(v);
    return A.dim + B.dim - C.dim;
}
static int target_dim(Basis const&V){ return intersection_dim(V,W)-AFF.dim; }

static V256 tt_var(int idx){ V256 x{}; for(int a=0;a<256;a++) if((a>>idx)&1) setbit(x,a); return x; }
static V256 tt_const1(){ V256 x{}; for(int i=0;i<4;i++) x.w[i]=~0ULL; return x; }
static V256 tt_target(int k){
    V256 out{};
    for(int a=0;a<256;a++){
        int b=0;
        for(int i=0;i<4;i++){ int j=k-i; if(j>=0&&j<4) b^=((a>>i)&1)&((a>>(4+j))&1); }
        if(b) setbit(out,a);
    }
    return out;
}

static vector<V256> span_values(Basis const&B){
    auto bv=B.vectors(); int d=bv.size(); size_t N=1ULL<<d;
    vector<V256> vals(N); V256 cur{}; vals[0]=cur;
    for(size_t t=1;t<N;t++){
        size_t g=t^(t>>1), pg=(t-1)^((t-1)>>1); size_t diff=g^pg; int i=__builtin_ctzll(diff);
        cur=vx(cur,bv[i]); vals[g]=cur;
    }
    return vals;
}


struct Q192 { uint64_t w[3]{}; };
static inline Q192 qxor(Q192 a,Q192 const&b){a.w[0]^=b.w[0];a.w[1]^=b.w[1];a.w[2]^=b.w[2];return a;}
static inline bool qzero(Q192 const&a){return !(a.w[0]|a.w[1]|a.w[2]);}
static inline int qpiv(Q192 const&a){for(int i=2;i>=0;i--)if(a.w[i])return i*64+63-__builtin_clzll(a.w[i]);return -1;}
static inline bool qbit(Q192 const&a,int p){return (a.w[p>>6]>>(p&63))&1ULL;}
static inline void qset(Q192&a,int p){a.w[p>>6]|=1ULL<<(p&63);}
struct Tag { Q192 q{}; uint8_t z=0; };
static inline Tag tx(Tag a,Tag const&b){a.q=qxor(a.q,b.q);a.z^=b.z;return a;}

struct TagBasis {
    array<V256,256> row{}; array<Tag,256> tag{}; array<uint8_t,256> has{};
    // reduce x while accumulating coordinates
    pair<V256,Tag> reduce_tag(V256 x, Tag init={}) const {
        Tag a=init;
        for(int p=255;p>=0;p--) if(has[p] && bit(x,p)){x=vx(x,row[p]);a=tx(a,tag[p]);}
        return {x,a};
    }
    bool insert(V256 x, Tag desired){
        auto [r,a]=reduce_tag(x,desired); if(zero(r)) return false; int p=pivot(r); row[p]=r;tag[p]=a;has[p]=1;return true;
    }
    Tag decompose(V256 x) const { auto [r,a]=reduce_tag(x,{}); if(!zero(r)){cerr<<"decompose outside span\n";abort();} return a; }
};

static vector<V256> useful_children(Basis const& V){
    // Build quotient coordinates P/V = (U/V) + (P/U), where U=V+W and
    // P is the span of U and all pairwise products of basis functions in V.
    auto b=V.vectors(); int d=b.size();
    TagBasis TB;
    for(auto &v:b) TB.insert(v,{});
    vector<V256> zvec;
    int zdim=0;
    for(auto &w:W.vectors()){
        auto [r,tmp]=TB.reduce_tag(w,{});
        if(!zero(r)){
            if(zdim>=8){cerr<<"zdim too large\n";abort();}
            Tag des{}; des.z=(uint8_t)(1u<<zdim);
            TB.insert(w,des); zvec.push_back(w); zdim++;
        }
    }
    vector<vector<V256>> prod(d,vector<V256>(d));
    for(int i=0;i<d;i++)for(int j=0;j<d;j++)prod[i][j]=va(b[i],b[j]);
    int qdim=0;
    for(int i=0;i<d;i++)for(int j=i;j<d;j++){
        auto [r,tmp]=TB.reduce_tag(prod[i][j],{});
        if(!zero(r)){
            if(qdim>=192){cerr<<"qdim>192\n";abort();}
            Tag des{};qset(des.q,qdim++);TB.insert(prod[i][j],des);
        }
    }
    vector<vector<Tag>> M(d,vector<Tag>(d));
    for(int i=0;i<d;i++)for(int j=0;j<d;j++)M[i][j]=TB.decompose(prod[i][j]);

    vector<uint8_t> zcol(d,0);
    unordered_set<uint8_t> zchildren; // cosets in U/V, at most 127
    size_t total=1ULL<<d;
    if(qdim <= 64){
        vector<uint64_t> qcol(d,0);
        size_t prevg=0;
        for(size_t t=1;t<total;t++){
            size_t g=t^(t>>1),diff=g^prevg;prevg=g;int i=__builtin_ctzll(diff);
            for(int j=0;j<d;j++){qcol[j]^=M[i][j].q.w[0];zcol[j]^=M[i][j].z;}
            uint64_t qb[64]{}; uint8_t zb[64]{}; uint8_t has[64]{}; uint8_t zimBasis[8]{};
            for(int j=0;j<d;j++){
                uint64_t q=qcol[j]; uint8_t z=zcol[j];
                while(q){int p=63-__builtin_clzll(q); if(!has[p]){has[p]=1;qb[p]=q;zb[p]=z;break;} q^=qb[p];z^=zb[p];}
                if(!q&&z){uint8_t y=z;for(int p=7;p>=0;p--)if((y>>p)&1){if(zimBasis[p])y^=zimBasis[p];else{zimBasis[p]=y;break;}}}
            }
            uint8_t zi[8];int h=0;for(int p=7;p>=0;p--)if(zimBasis[p])zi[h++]=zimBasis[p];
            if(!h) continue;
            uint8_t cur=0;size_t pg=0;
            for(size_t ss=1;ss<(1ULL<<h);ss++){size_t gg=ss^(ss>>1),dd=gg^pg;pg=gg;int ii=__builtin_ctzll(dd);cur^=zi[ii];zchildren.insert(cur);}
        }
    } else {
        vector<Q192> qcol(d); size_t prevg=0;
        for(size_t t=1;t<total;t++){
            size_t g=t^(t>>1),diff=g^prevg;prevg=g;int i=__builtin_ctzll(diff);
            for(int j=0;j<d;j++){qcol[j]=qxor(qcol[j],M[i][j].q);zcol[j]^=M[i][j].z;}
            array<Q192,192> qb{}; array<uint8_t,192> zb{}; array<uint8_t,192> has{}; uint8_t zimBasis[8]{};
            for(int j=0;j<d;j++){
                Q192 q=qcol[j]; uint8_t z=zcol[j];
                while(!qzero(q)){int p=qpiv(q);if(!has[p]){has[p]=1;qb[p]=q;zb[p]=z;break;}q=qxor(q,qb[p]);z^=zb[p];}
                if(qzero(q)&&z){uint8_t y=z;for(int p=7;p>=0;p--)if((y>>p)&1){if(zimBasis[p])y^=zimBasis[p];else{zimBasis[p]=y;break;}}}
            }
            uint8_t zi[8];int h=0;for(int p=7;p>=0;p--)if(zimBasis[p])zi[h++]=zimBasis[p];
            if(!h) continue;
            uint8_t cur=0;size_t pg=0;
            for(size_t ss=1;ss<(1ULL<<h);ss++){size_t gg=ss^(ss>>1),dd=gg^pg;pg=gg;int ii=__builtin_ctzll(dd);cur^=zi[ii];zchildren.insert(cur);}
        }
    }
    vector<V256> out; out.reserve(zchildren.size());
    for(uint8_t zm:zchildren){ V256 r{}; for(int i=0;i<zdim;i++)if((zm>>i)&1)r=vx(r,zvec[i]); r=V.reduce(r); if(!zero(r))out.push_back(r); }
    return out;
}

static uint64_t nodes=0, child_calls=0; static int maxdepth=0;
static bool dfs(Basis const&V,int gates_used, vector<V256>& path){
    nodes++; maxdepth=max(maxdepth,gates_used);
    int td=target_dim(V);
    if(td==7){ cerr<<"HIT at gates "<<gates_used<<"\n"; return true; }
    if(gates_used>=8 || td+(8-gates_used)<7) return false;
    child_calls++;
    auto ch=useful_children(V);
    for(auto r:ch){ Basis N=V; bool ok=N.insert(r); if(!ok) continue; path.push_back(r); if(dfs(N,gates_used+1,path)) return true; path.pop_back(); }
    return false;
}

static vector<Basis> prefix_states(int useful_count){
    // The exact all-useful profile for n=4 is generated by the three P^1(F2) directions.
    // useful_count=1: three singleton spans; 2: three pair spans; 3: one triple span.
    vector<V256> e={TARGET[0], TARGET[6]}; V256 sum{}; for(auto&t:TARGET) sum=vx(sum,t); e.push_back(sum);
    vector<Basis> out;
    if(useful_count==1){ for(int i=0;i<3;i++){ Basis B=AFF; B.insert(e[i]); out.push_back(B);} }
    else if(useful_count==2){ for(int i=0;i<3;i++)for(int j=i+1;j<3;j++){ Basis B=AFF; B.insert(e[i]);B.insert(e[j]);out.push_back(B);} }
    else if(useful_count==3){ Basis B=AFF; for(auto&t:e)B.insert(t); out.push_back(B); }
    return out;
}


static V256 tt_to_anf_slow(V256 const& f){
    uint8_t a[256]; for(int x=0;x<256;x++)a[x]=bit(f,x)?1:0;
    for(int i=0;i<8;i++)for(int x=0;x<256;x++)if((x>>i)&1)a[x]^=a[x^(1<<i)];
    V256 o{};for(int x=0;x<256;x++)if(a[x])setbit(o,x);return o;
}

static string high_mons(V256 const& f){V256 a=tt_to_anf_slow(f);ostringstream os;bool first=true;for(int m=0;m<256;m++)if(bit(a,m)&&__builtin_popcount((unsigned)m)>=3){if(!first)os<<",";first=false;os<<hex<<m<<dec<<":"<<__builtin_popcount((unsigned)m);}return os.str();}

static vector<V256> seed_residuals(Basis const&V){
    auto vals=span_values(V); size_t n=vals.size();
    unordered_set<V256,VHash> seeds; seeds.reserve(n*n/8);
    for(size_t i=1;i<n;i++) for(size_t j=i;j<n;j++){
        V256 p=va(vals[i],vals[j]); V256 r=V.reduce(p); if(zero(r)) continue;
        // Before seed V subset W.  If r is not in W, adding it is exactly a non-useful/garbage extension.
        if(!zero(W.reduce(r))) seeds.insert(r);
    }
    vector<V256> out; out.reserve(seeds.size()); for(auto const&r:seeds) out.push_back(r); return out;
}


static array<uint8_t,16> coeff_map3(int a,int b,int c,int d){
    array<uint8_t,4> col{};
    for(int i=0;i<4;i++){
        uint8_t poly=1; int deg=0;
        auto multlin=[&](int lx,int ly){uint8_t np=0;for(int j=0;j<=deg;j++)if((poly>>j)&1){if(ly)np^=1u<<j;if(lx)np^=1u<<(j+1);}poly=np;deg++;};
        for(int t=0;t<i;t++) multlin(a,b);
        for(int t=i;t<3;t++) multlin(c,d);
        col[i]=poly;
    }
    array<uint8_t,16> tab{};
    for(int x=0;x<16;x++){uint8_t y=0;for(int i=0;i<4;i++)if((x>>i)&1)y^=col[i];tab[x]=y;}
    return tab;
}
static V256 transform_map(V256 const&f, array<uint8_t,256> const&mp){V256 o{};for(int x=0;x<256;x++)if(bit(f,mp[x]))setbit(o,x);return o;}
static array<uint8_t,256> make_assignment_map(array<uint8_t,16> const&T,bool swap){array<uint8_t,256> mp{};for(int x=0;x<256;x++){int A=T[x&15],B=T[(x>>4)&15];if(swap)std::swap(A,B);mp[x]=(uint8_t)(A|(B<<4));}return mp;}
static vector<array<uint8_t,256>> symmetry_maps(){
    vector<array<uint8_t,256>> maps;
    for(int a=0;a<2;a++)for(int b=0;b<2;b++)for(int c=0;c<2;c++)for(int d=0;d<2;d++)if(((a*d)^(b*c))==1){auto T=coeff_map3(a,b,c,d);for(int sw=0;sw<2;sw++)maps.push_back(make_assignment_map(T,sw));}
    return maps;
}
static vector<V256> canonical_seed_orbits(Basis const&V, vector<V256> const&seeds, vector<array<uint8_t,256>> const&maps){
    vector<int> stab;
    for(int gi=0;gi<(int)maps.size();gi++){
        bool ok=true; for(auto &v:V.vectors()) if(!zero(V.reduce(transform_map(v,maps[gi])))){ok=false;break;} if(ok)stab.push_back(gi);
    }
    canonical_stabilizer_size=stab.size();
    VLess less; unordered_set<V256,VHash> reps; reps.reserve(seeds.size());
    for(auto &r:seeds){V256 best=V.reduce(r);for(int gi:stab){V256 z=V.reduce(transform_map(r,maps[gi]));if(less(z,best))best=z;}reps.insert(best);}
    vector<V256> out;out.reserve(reps.size());for(auto&r:reps)out.push_back(r);sort(out.begin(),out.end(),VLess{});return out;
}


int main(){
    AFF.insert(tt_const1()); for(int i=0;i<8;i++) AFF.insert(tt_var(i));
    TARGET.resize(7); W=AFF; for(int k=0;k<7;k++){TARGET[k]=tt_target(k);W.insert(TARGET[k]);}
    auto maps=symmetry_maps();
    auto prefixes=prefix_states(3); Basis P=prefixes[0];
    auto raw=seed_residuals(P); auto seeds=canonical_seed_orbits(P,raw,maps);
    vector<int> reps={732,733,735,736,737,738,739,740,741,743,30131,30180,30209,30251};
    cout<<"orbit_reps="<<seeds.size()<<"\n";
    for(int rep:reps){
        Basis V=P; V.insert(seeds[(size_t)rep]);
        auto ch=useful_children(V);
        cout<<"rep="<<rep<<" first="<<ch.size()<<" high="<<high_mons(seeds[(size_t)rep]);
        size_t second_total=0, second_max=0;
        for(auto const& r:ch){
            Basis N=V; N.insert(r);
            auto ch2=useful_children(N);
            second_total += ch2.size();
            second_max=max(second_max,ch2.size());
        }
        cout<<" second_total="<<second_total<<" second_max="<<second_max<<"\n";
    }
    cout<<"stabilizer="<<canonical_stabilizer_size<<"\n";
}

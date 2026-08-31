#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <unordered_map>
#include <vector>

using Poly = std::array<uint64_t, 16>;

static Poly multiply(const Poly &a, const Poly &b) {
    Poly out{};
    std::vector<int> as, bs;
    for (int m = 0; m < 1024; ++m) {
        if ((a[m >> 6] >> (m & 63)) & 1ULL) as.push_back(m);
        if ((b[m >> 6] >> (m & 63)) & 1ULL) bs.push_back(m);
    }
    for (int x : as) for (int y : bs) {
        int z = x | y;
        out[z >> 6] ^= 1ULL << (z & 63);
    }
    return out;
}

static Poly linear_poly(uint16_t coeff, const std::array<uint16_t, 10> &forms) {
    Poly p{};
    for (int i = 0; i < 10; ++i) if ((coeff >> i) & 1) {
        uint16_t f = forms[i];
        while (f) {
            int v = std::countr_zero(f);
            f &= f - 1;
            int monomial = 1 << v;
            p[monomial >> 6] ^= 1ULL << (monomial & 63);
        }
    }
    return p;
}

static Poly xor_poly(Poly a, const Poly &b) {
    for (int i = 0; i < 16; ++i) a[i] ^= b[i];
    return a;
}

static uint64_t degree_two(const Poly &p) {
    uint64_t out = 0;
    int k = 0;
    for (int i = 0; i < 10; ++i) for (int j = i + 1; j < 10; ++j, ++k) {
        int m = (1 << i) | (1 << j);
        if ((p[m >> 6] >> (m & 63)) & 1ULL) out |= 1ULL << k;
    }
    return out;
}

static std::array<uint64_t, 2> degree_three(const Poly &p) {
    std::array<uint64_t, 2> out{};
    int k = 0;
    for (int i = 0; i < 10; ++i)
        for (int j = i + 1; j < 10; ++j)
            for (int l = j + 1; l < 10; ++l, ++k) {
                int m = (1 << i) | (1 << j) | (1 << l);
                if ((p[m >> 6] >> (m & 63)) & 1ULL) out[k >> 6] |= 1ULL << (k & 63);
            }
    return out;
}

static uint64_t quad_product(uint16_t f, uint16_t g) {
    uint64_t out = 0;
    int k = 0;
    for (int i = 0; i < 10; ++i) for (int j = i + 1; j < 10; ++j, ++k) {
        int bit = (((f >> i) & 1) & ((g >> j) & 1)) ^
                  (((f >> j) & 1) & ((g >> i) & 1));
        if (bit) out |= 1ULL << k;
    }
    return out;
}

struct BasisRow { uint64_t v = 0; uint8_t tag = 0; };

static bool insert(std::array<BasisRow, 45> &basis, uint64_t v, uint8_t tag) {
    for (int p = 44; p >= 0; --p) if ((v >> p) & 1ULL) {
        if (basis[p].v) {
            v ^= basis[p].v;
            tag ^= basis[p].tag;
        } else {
            basis[p] = {v, tag};
            return true;
        }
    }
    return false;
}

static std::pair<uint64_t,uint8_t> reduce(const std::array<BasisRow,45> &basis,
                                          uint64_t v) {
    uint8_t tag = 0;
    for (int p = 44; p >= 0; --p) if (((v >> p) & 1ULL) && basis[p].v) {
        v ^= basis[p].v;
        tag ^= basis[p].tag;
    }
    return {v, tag};
}

struct Key {
    uint64_t h0, h1, residue;
    bool operator==(const Key &o) const {
        return h0 == o.h0 && h1 == o.h1 && residue == o.residue;
    }
};
struct KeyHash {
    size_t operator()(const Key &k) const {
        uint64_t x = k.h0 ^ (k.h1 + 0x9e3779b97f4a7c15ULL + (k.h0<<6) + (k.h0>>2));
        x ^= k.residue + 0x9e3779b97f4a7c15ULL + (x<<6) + (x>>2);
        x ^= x >> 30; x *= 0xbf58476d1ce4e5b9ULL;
        x ^= x >> 27; x *= 0x94d049bb133111ebULL;
        return size_t(x ^ (x >> 31));
    }
};
struct Witness { uint8_t tag, plane; uint16_t ell, m; };

struct AffineRow {
    std::array<uint64_t,3> v{};
    uint8_t rhs = 0;
};

static bool insert_affine(std::array<AffineRow,166> &basis,
                          std::array<uint64_t,3> v, uint8_t rhs) {
    for (int p=165; p>=0; --p) if ((v[p>>6]>>(p&63))&1ULL) {
        if (basis[p].v[p>>6] & (1ULL<<(p&63))) {
            for (int w=0;w<3;++w) v[w]^=basis[p].v[w];
            rhs^=basis[p].rhs;
        } else {
            basis[p].v=v; basis[p].rhs=rhs; return true;
        }
    }
    return rhs==0;
}

static uint8_t pluecker(uint8_t q, uint8_t c) {
    uint8_t z = 0;
    int k = 0;
    for (int i = 0; i < 4; ++i) for (int j = i + 1; j < 4; ++j, ++k) {
        int bit = (((q >> i) & 1) & ((c >> j) & 1)) ^
                  (((q >> j) & 1) & ((c >> i) & 1));
        if (bit) z |= uint8_t(1 << k);
    }
    return z;
}

int main() {
    const std::array<uint16_t,10> eval = {
        uint16_t((1<<0)|(1<<2)|(1<<3)),
        uint16_t((1<<1)|(1<<2)|(1<<4)),
        uint16_t(1<<0),
        uint16_t((1<<0)|(1<<1)|(1<<2)|(1<<3)|(1<<4)),
        uint16_t(1<<4),
        uint16_t((1<<5)|(1<<7)|(1<<8)),
        uint16_t((1<<6)|(1<<7)|(1<<9)),
        uint16_t(1<<5),
        uint16_t((1<<5)|(1<<6)|(1<<7)|(1<<8)|(1<<9)),
        uint16_t(1<<9)
    };
    std::array<Poly,10> lin;
    for (int i = 0; i < 10; ++i) lin[i] = linear_poly(uint16_t(1<<i), eval);

    const std::array<std::pair<int,int>,4> local_edges = {{{0,5},{0,6},{1,5},{1,6}}};
    std::array<Poly,4> x;
    std::array<uint64_t,4> x2;
    for (int i = 0; i < 4; ++i) {
        x[i] = multiply(lin[local_edges[i].first], lin[local_edges[i].second]);
        x2[i] = degree_two(x[i]);
    }
    auto local_quad = [&](uint8_t q) {
        Poly p{};
        for (int i = 0; i < 4; ++i) if ((q>>i)&1) p = xor_poly(p,x[i]);
        return p;
    };

    std::vector<std::pair<uint8_t,uint8_t>> planes;
    bool seen[256]{};
    for (uint8_t q = 1; q < 16; ++q) for (uint8_t c = q+1; c < 16; ++c) {
        if (q == c) continue;
        auto qc = multiply(local_quad(q), local_quad(c));
        bool quartic = false;
        for (int m = 0; m < 1024; ++m) if (std::popcount(unsigned(m)) == 4 &&
            ((qc[m>>6] >> (m&63)) & 1ULL)) quartic = true;
        if (quartic) continue;
        uint8_t a=q,b=c,d=q^c;
        uint8_t lo=std::min({a,b,d}), hi=std::max({a,b,d});
        uint8_t mid=a^b^d^lo^hi;
        int code = lo | (mid<<4);
        if (!seen[code]) { seen[code]=true; planes.push_back({lo,mid}); }
    }
    std::cerr << "planes=" << planes.size() << "\n";

    std::array<BasisRow,45> basis{};
    for (uint64_t q : x2) insert(basis,q,0);
    for (int p : {2,3,4}) insert(basis,degree_two(multiply(lin[p],lin[p+5])),0);
    auto target_E = [&](int s) {
        uint64_t q=0;
        for (int i=0;i<5;++i) { int j=s-i; if (0<=j && j<5) q ^= quad_product(1<<i,1<<(5+j)); }
        return q;
    };
    int rank = 7;
    for (int s=1;s<=4;++s) {
        if (!insert(basis,target_E(s),uint8_t(1<<(s-1)))) {
            std::cerr << "E"<<s<<" dependent\n"; return 2;
        }
        ++rank;
    }
    std::cerr << "W+quotient-rank=" << rank << "\n";

    std::array<Poly,1024> linears;
    for (int a=0;a<1024;++a) linears[a]=linear_poly(uint16_t(a),eval);
    std::unordered_map<Key,Witness,KeyHash> fibers;
    fibers.reserve(1<<22);
    uint64_t checked=0, duplicate_same_plane=0, duplicate_radical=0,
             duplicate_other_plane=0;
    // Pair coordinates are 01,02,03,12,13,23.
    const uint8_t local_radical = uint8_t((1<<2) | (1<<3));
    std::array<AffineRow,166> affine_basis{};
    bool affine_possible=true;
    for (int pi=0; pi<(int)planes.size(); ++pi) {
        Poly Q=local_quad(planes[pi].first), C=local_quad(planes[pi].second);
        for (int e=0;e<1024;++e) {
            Poly F=xor_poly(Q,linears[e]);
            for (int m=0;m<1024;++m) {
                Poly G=xor_poly(C,linears[m]);
                Poly product=multiply(F,G);
                auto h=degree_three(product);
                auto [residue,tag]=reduce(basis,degree_two(product));
                Key key{h[0],h[1],residue};
                if (affine_possible) {
                    std::array<uint64_t,3> av{h[0],h[1],0};
                    for (int b=0;b<45;++b) if ((residue>>b)&1ULL) {
                        int pos=120+b; av[pos>>6]^=1ULL<<(pos&63);
                    }
                    av[165>>6]^=1ULL<<(165&63);
                    if (!insert_affine(affine_basis,av,tag)) {
                        affine_possible=false;
                        std::cerr << "no affine target functional at plane="<<pi
                                  <<" ell="<<e<<" m="<<m<<"\n";
                    }
                }
                auto [it,fresh]=fibers.emplace(key,Witness{tag,uint8_t(pi),uint16_t(e),uint16_t(m)});
                if (!fresh && it->second.tag != tag) {
                    auto w=it->second;
                    std::cout << "NONCONSTANT\n"
                              << "tag_difference=" << int(w.tag^tag) << "\n"
                              << "first plane=" << int(w.plane) << " Q=" << int(planes[w.plane].first)
                              << " C=" << int(planes[w.plane].second) << " ell=" << w.ell << " m=" << w.m << " tag=" << int(w.tag) << "\n"
                              << "second plane=" << pi << " Q=" << int(planes[pi].first)
                              << " C=" << int(planes[pi].second) << " ell=" << e << " m=" << m << " tag=" << int(tag) << "\n"
                              << "h=" << h[0] << "," << h[1] << " residue=" << residue << "\n";
                    return 1;
                }
                if (!fresh) {
                    uint8_t z0 = pluecker(planes[it->second.plane].first,
                                          planes[it->second.plane].second);
                    uint8_t z1 = pluecker(planes[pi].first,planes[pi].second);
                    if (z0 == z1) ++duplicate_same_plane;
                    else if ((z0 ^ z1) == local_radical) ++duplicate_radical;
                    else ++duplicate_other_plane;
                }
                ++checked;
            }
        }
        std::cerr << "plane "<<pi<<" checked, fibers="<<fibers.size()<<"\n";
    }
    std::cout << "CONSTANT checked="<<checked<<" fibers="<<fibers.size()
              << " duplicate_same_plane="<<duplicate_same_plane
              << " duplicate_radical="<<duplicate_radical
              << " duplicate_other_plane="<<duplicate_other_plane
              << " affine_possible="<<affine_possible<<"\n";
    return 0;
}

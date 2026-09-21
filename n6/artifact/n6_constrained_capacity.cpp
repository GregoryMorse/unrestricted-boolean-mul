#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

using U32 = std::uint32_t;
using U16 = std::uint16_t;
using U64 = std::uint64_t;
using U128 = unsigned __int128;

namespace {

constexpr int N = 6;
constexpr int NA = 5;
constexpr int NB = 6;
constexpr int TARGET = 11;
constexpr int AMBIENT = NA * NB;
constexpr int QUOTIENT = AMBIENT - TARGET;

struct U128Hash {
  std::size_t operator()(U128 x) const noexcept {
    const U64 lo = static_cast<U64>(x);
    const U64 hi = static_cast<U64>(x >> 64);
    U64 h = lo ^ (hi + 0x9e3779b97f4a7c15ULL + (lo << 6) + (lo >> 2));
    h ^= h >> 30;
    h *= 0xbf58476d1ce4e5b9ULL;
    h ^= h >> 27;
    h *= 0x94d049bb133111ebULL;
    return static_cast<std::size_t>(h ^ (h >> 31));
  }
};

int rank_mask(U32 x) { return 31 - __builtin_clz(x); }

std::vector<U32> canonical_basis(std::vector<U32> generators) {
#ifdef LEXICOGRAPHIC_CANONICAL_AUDIT
  // Independent publication audit.  First recover any insertion-echelon
  // basis, enumerate the complete point set of the (at most four-dimensional)
  // subspace, and then greedily choose the lexicographically first basis.
  // This key is determined by the point set and does not use RREF.
  std::array<U32, QUOTIENT> insertion_rows{};
  for (U32 x : generators) {
    for (int p = QUOTIENT - 1; p >= 0; --p) {
      if (((x >> p) & 1U) == 0) continue;
      if (insertion_rows[p]) x ^= insertion_rows[p];
      else {
        insertion_rows[p] = x;
        break;
      }
    }
  }
  std::vector<U32> insertion_basis;
  for (int p = QUOTIENT - 1; p >= 0; --p) {
    if (insertion_rows[p]) insertion_basis.push_back(insertion_rows[p]);
  }
  std::vector<U32> all_points{0};
  for (U32 row : insertion_basis) {
    const std::size_t old_size = all_points.size();
    for (std::size_t i = 0; i < old_size; ++i) {
      all_points.push_back(all_points[i] ^ row);
    }
  }
  std::sort(all_points.begin(), all_points.end());
  std::array<U32, QUOTIENT> greedy_rows{};
  std::vector<U32> result;
  for (U32 point : all_points) {
    U32 x = point;
    for (int p = QUOTIENT - 1; p >= 0; --p) {
      if (((x >> p) & 1U) == 0) continue;
      if (greedy_rows[p]) x ^= greedy_rows[p];
      else {
        greedy_rows[p] = x;
        result.push_back(point);
        break;
      }
    }
  }
  assert(result.size() == insertion_basis.size());
  return result;
#else
  std::array<U32, QUOTIENT> rows{};
  for (U32 x : generators) {
    for (int p = QUOTIENT - 1; p >= 0; --p) {
      if (((x >> p) & 1U) == 0) continue;
      if (rows[p]) {
        x ^= rows[p];
      } else {
        // Reduce the new row against every existing lower pivot before it is
        // installed.  Without this pass the basis still spans the right
        // space, but its packed representation depends on insertion order and
        // the candidate sets retain many duplicates.
        for (int q = p - 1; q >= 0; --q) {
          if (rows[q] && ((x >> q) & 1U)) x ^= rows[q];
        }
        rows[p] = x;
        for (int q = 0; q < QUOTIENT; ++q) {
          if (q != p && rows[q] && ((rows[q] >> p) & 1U)) rows[q] ^= x;
        }
        break;
      }
    }
  }
  std::vector<U32> result;
  for (int p = QUOTIENT - 1; p >= 0; --p) if (rows[p]) result.push_back(rows[p]);
  return result;
#endif
}

U128 pack_basis(const std::vector<U32>& basis) {
  U128 key = 0;
  for (int i = 0; i < static_cast<int>(basis.size()); ++i) {
    key |= U128(basis[i]) << (QUOTIENT * i);
  }
  return key;
}

std::vector<U32> unpack_basis(U128 key, int dim) {
  std::vector<U32> basis(dim);
  const U32 mask = (U32{1} << QUOTIENT) - 1;
  for (int i = 0; i < dim; ++i) basis[i] = U32(key >> (QUOTIENT * i)) & mask;
  return basis;
}

std::vector<U32> points(const std::vector<U32>& basis) {
  std::vector<U32> result{0};
  for (U32 b : basis) {
    const std::size_t old = result.size();
    for (std::size_t i = 0; i < old; ++i) result.push_back(result[i] ^ b);
  }
  return result;
}

struct TargetBasis {
  std::array<U16, TARGET> rows{};
  int dimension = 0;
  bool add(U16 x) {
    for (int p = TARGET - 1; p >= 0; --p) {
      if (((x >> p) & 1U) == 0) continue;
      if (rows[p]) x ^= rows[p];
      else {
        rows[p] = x;
        ++dimension;
        return true;
      }
    }
    return false;
  }
};

struct Reduction {
  std::array<U32, AMBIENT> rows{};
  std::array<U16, AMBIENT> tags{};
  std::array<bool, AMBIENT> has{};
  std::array<int, QUOTIENT> nonpivots{};
  std::array<U32, NA> input_basis{};

  explicit Reduction(U32 constraint) {
    assert(constraint && constraint < (1U << N));
    const int pivot = rank_mask(constraint);
    int a = 0;
    for (int i = 0; i < N; ++i) {
      if (i == pivot) continue;
      U32 v = U32{1} << i;
      if ((constraint >> i) & 1U) v ^= U32{1} << pivot;
      assert((__builtin_popcount(v & constraint) & 1) == 0);
      input_basis[a++] = v;
    }
    assert(a == NA);

    int target_rank = 0;
    for (int s = 0; s < TARGET; ++s) {
      U32 x = 0;
      for (int i = 0; i < NA; ++i) {
        for (int j = 0; j < NB; ++j) {
          const int source = s - j;
          if (0 <= source && source < N && ((input_basis[i] >> source) & 1U)) {
            x ^= U32{1} << (i * NB + j);
          }
        }
      }
      U16 tag = U16{1} << s;
      for (int p = AMBIENT - 1; p >= 0; --p) {
        if (((x >> p) & 1U) == 0) continue;
        if (has[p]) {
          x ^= rows[p];
          tag ^= tags[p];
        } else {
          has[p] = true;
          rows[p] = x;
          tags[p] = tag;
          ++target_rank;
          break;
        }
      }
    }
    // The endpoint orbit h=a_0 (mask 1, together with its PGL images) has
    // target rank ten, not eleven, and belongs to the separate rectangular
    // 5-by-6 calculation.  Refuse to run this eleven-target program on it.
    assert(target_rank == TARGET);
    int q = 0;
    for (int p = 0; p < AMBIENT; ++p) if (!has[p]) nonpivots[q++] = p;
    assert(q == QUOTIENT);
  }

  std::pair<U32, U16> reduce(U32 x) const {
    U16 tag = 0;
    for (int p = AMBIENT - 1; p >= 0; --p) {
      if (((x >> p) & 1U) && has[p]) {
        x ^= rows[p];
        tag ^= tags[p];
      }
    }
    U32 q = 0;
    for (int i = 0; i < QUOTIENT; ++i) {
      if ((x >> nonpivots[i]) & 1U) q ^= U32{1} << i;
    }
    return {q, tag};
  }
};

struct Fiber {
  U16 base = 0;
  std::vector<U16> differences;
  std::vector<std::pair<int, int>> gates;
};

struct Catalogue {
  Reduction reduction;
  std::unordered_map<U32, Fiber> fibers;
  std::vector<U32> populated;
  std::unordered_map<U32, int> weight;

  explicit Catalogue(U32 constraint) : reduction(constraint) {
    std::map<U32, std::vector<std::tuple<U16, int, int>>> grouped;
    for (int a = 1; a < (1 << NA); ++a) {
      for (int b = 1; b < (1 << NB); ++b) {
        U32 gate = 0;
        for (int i = 0; i < NA; ++i) if ((a >> i) & 1) {
          for (int j = 0; j < NB; ++j) if ((b >> j) & 1) {
            gate ^= U32{1} << (i * NB + j);
          }
        }
        const auto [q, tag] = reduction.reduce(gate);
        grouped[q].push_back({tag, a, b});
      }
    }
    for (const auto& [q, entries] : grouped) {
      Fiber f;
      f.base = std::get<0>(entries.front());
      TargetBasis diff;
      for (const auto& [tag, a, b] : entries) {
        diff.add(tag ^ f.base);
        f.gates.push_back({a, b});
      }
      for (U16 row : diff.rows) if (row) f.differences.push_back(row);
      weight[q] = static_cast<int>(entries.size());
      fibers.emplace(q, std::move(f));
      if (q) populated.push_back(q);
    }
  }

  int w(U32 q) const {
    const auto it = weight.find(q);
    return it == weight.end() ? 0 : it->second;
  }

  int subspace_weight(const std::vector<U32>& basis) const {
    int total = 0;
    for (U32 q : points(basis)) total += w(q);
    return total;
  }

  int capacity(const std::vector<U32>& basis) const {
    TargetBasis target;
    std::array<U32, QUOTIENT> qrows{};
    std::array<U16, QUOTIENT> qtags{};
    for (U32 q : points(basis)) {
      const auto it = fibers.find(q);
      if (it == fibers.end()) continue;
      const Fiber& f = it->second;
      for (U16 d : f.differences) target.add(d);
      U32 x = q;
      U16 tag = f.base;
      bool inserted = false;
      for (int p = QUOTIENT - 1; p >= 0; --p) {
        if (((x >> p) & 1U) == 0) continue;
        if (qrows[p]) {
          x ^= qrows[p];
          tag ^= qtags[p];
        } else {
          qrows[p] = x;
          qtags[p] = tag;
          inserted = true;
          break;
        }
      }
      if (!inserted) target.add(tag);
    }
    return target.dimension;
  }
};

// Exact capacity search.  If a four-space contains at least seven populated
// nonzero quotient points, two disjoint pairs have the same sum.  The four
// points form an affine plane and span a three-dimensional hyperplane.  We
// enumerate all such hyperplanes, then scan their populated quotient cosets.
void search(U32 constraint, const std::string& mode) {
  Catalogue c(constraint);
  int max_fiber = 0;
  std::map<int, int> fiber_hist;
  for (const auto& [q, f] : c.fibers) {
    ++fiber_hist[f.gates.size()];
    max_fiber = std::max(max_fiber, static_cast<int>(f.gates.size()));
  }
  std::cout << "mask=" << constraint << " populated=" << c.populated.size()
            << " fibers=" << c.fibers.size() << " max_fiber=" << max_fiber
            << " zero_weight=" << c.w(0)
            << " rho0=" << c.capacity({})
            << " fiber_hist";
  for (auto [w, count] : fiber_hist) std::cout << ' ' << w << ':' << count;
  std::cout << '\n' << std::flush;

  TargetBasis base_local;
  const auto zero_it = c.fibers.find(0);
  assert(zero_it != c.fibers.end());
  base_local.add(zero_it->second.base);
  for (U16 d : zero_it->second.differences) base_local.add(d);
  assert(base_local.dimension == c.capacity({}));
  TargetBasis all_local = base_local;
  std::map<int, int> local_gain_hist;
  int effective = 0;
  std::vector<U32> effective_points;
  for (U32 q : c.populated) {
    TargetBasis one = base_local;
    for (U16 d : c.fibers.at(q).differences) one.add(d);
    const int gain = one.dimension - base_local.dimension;
    ++local_gain_hist[gain];
    if (gain) {
      ++effective;
      effective_points.push_back(q);
    }
    for (U16 d : c.fibers.at(q).differences) all_local.add(d);
  }
  std::cout << "effective=" << effective
            << " all_local_gain=" << all_local.dimension - base_local.dimension
            << " local_gain_hist";
  for (auto [gain, count] : local_gain_hist) std::cout << ' ' << gain << ':' << count;
  std::cout << '\n' << std::flush;

  std::vector<std::unordered_set<U128, U128Hash>> effective_spans(5);
  effective_spans[0].insert(0);
  for (U32 q : effective_points) {
    auto old = effective_spans;
    for (int dim = 0; dim < 4; ++dim) {
      for (U128 key : old[dim]) {
        auto b = unpack_basis(key, dim);
        b.push_back(q);
        b = canonical_basis(std::move(b));
        if (static_cast<int>(b.size()) == dim + 1) {
          effective_spans[dim + 1].insert(pack_basis(b));
        }
      }
    }
  }
  for (int dim = 0; dim <= 4; ++dim) {
    int max_local = 0;
    std::map<int, U64> hist;
    for (U128 key : effective_spans[dim]) {
      const auto b = unpack_basis(key, dim);
      const auto qs = points(b);
      TargetBasis local = base_local;
      for (U32 q : effective_points) {
        if (std::find(qs.begin(), qs.end(), q) == qs.end()) continue;
        for (U16 d : c.fibers.at(q).differences) local.add(d);
      }
      const int gain = local.dimension - base_local.dimension;
      ++hist[gain];
      max_local = std::max(max_local, gain);
    }
    std::cout << "effective_span_dim=" << dim
              << " count=" << effective_spans[dim].size()
              << " local_hist";
    for (auto [gain, count] : hist) std::cout << ' ' << gain << ':' << count;
    std::cout << " max=" << max_local << '\n';
  }
  std::cout << std::flush;
  if (mode == "--stats") return;

  if (mode == "--planes" || mode == "--exact") {
    std::vector<std::vector<U64>> pairs(U32{1} << QUOTIENT);
    for (std::size_t i = 0; i < c.populated.size(); ++i) {
      for (std::size_t j = i + 1; j < c.populated.size(); ++j) {
        const U32 x = c.populated[i];
        const U32 y = c.populated[j];
        pairs[x ^ y].push_back(U64(x) | (U64(y) << QUOTIENT));
      }
    }
    std::unordered_set<U128, U128Hash> plane_q3;
    plane_q3.reserve(1000000);
    U64 pair_pair_visits = 0;
    const U32 qmask = (U32{1} << QUOTIENT) - 1;
    for (const auto& bucket : pairs) {
      for (std::size_t i = 0; i < bucket.size(); ++i) {
        const U32 x = U32(bucket[i]) & qmask;
        const U32 y = U32(bucket[i] >> QUOTIENT);
        for (std::size_t j = i + 1; j < bucket.size(); ++j) {
          ++pair_pair_visits;
          const U32 z = U32(bucket[j]) & qmask;
          const U32 w = U32(bucket[j] >> QUOTIENT);
          assert(x != z && x != w && y != z && y != w);
          auto b3 = canonical_basis({x, y, z});
          assert(b3.size() == 3);
          plane_q3.insert(pack_basis(b3));
        }
      }
    }
    std::map<int, U64> internal_hist;
    for (U128 key : plane_q3) {
      int k = 0;
      for (U32 q : points(unpack_basis(key, 3))) if (q && c.w(q)) ++k;
      ++internal_hist[k];
    }
    std::cout << "pair_pair_visits=" << pair_pair_visits
              << " plane_q3=" << plane_q3.size() << " internal_hist";
    for (auto [k, count] : internal_hist) std::cout << ' ' << k << ':' << count;
    std::cout << '\n' << std::flush;
    if (mode == "--planes") return;

    auto populated_count = [&](const std::vector<U32>& basis) {
      int k = 0;
      for (U32 q : points(basis)) if (q && c.w(q)) ++k;
      return k;
    };
    auto local_gain = [&](const std::vector<U32>& basis) {
      const auto qs = points(basis);
      TargetBasis local = base_local;
      for (U32 q : effective_points) {
        if (std::find(qs.begin(), qs.end(), q) == qs.end()) continue;
        for (U16 d : c.fibers.at(q).differences) local.add(d);
      }
      return local.dimension - base_local.dimension;
    };
    auto coset_representative = [](U32 q, const std::vector<U32>& subspace_points) {
      U32 result = q;
      for (U32 u : subspace_points) result = std::min(result, q ^ u);
      return result;
    };

    std::unordered_set<U128, U128Hash> q4_candidates;
    q4_candidates.reserve(1000000);
    U64 generated_q4 = 0;
    U64 optimistic_pruned = 0;
    U64 exact_upper_pruned = 0;
    const int global_local_gain = all_local.dimension - base_local.dimension;
    auto consider_q4 = [&](const std::vector<U32>& b4) {
      assert(b4.size() == 4);
      ++generated_q4;
      const int k = populated_count(b4);
      if (base_local.dimension + global_local_gain + std::max(0, k - 4)
          < TARGET) {
        ++optimistic_pruned;
        return;
      }
      const int d = local_gain(b4);
      if (base_local.dimension + d + std::max(0, k - 4) < TARGET) {
        ++exact_upper_pruned;
        return;
      }
      q4_candidates.insert(pack_basis(b4));
    };
    U64 q3_progress = 0;
    U64 scanned_all_extensions = 0;
    U64 scanned_effective_extensions = 0;
    for (U128 key : plane_q3) {
      const auto b3 = unpack_basis(key, 3);
      const auto q3points = points(b3);
      const int inside_k = populated_count(b3);
      const int inside_d = local_gain(b3);

      // Every outside coset containing at least two populated points has a
      // populated pair whose difference is a nonzero direction of Q3.
      std::unordered_set<U32> outside_cosets;
      for (U32 direction : q3points) {
        if (!direction) continue;
        for (U64 pair : pairs[direction]) {
          const U32 x = U32(pair) & qmask;
          const U32 representative = coset_representative(x, q3points);
          if (representative) outside_cosets.insert(representative);
        }
      }
      for (U32 representative : outside_cosets) {
        auto b4 = canonical_basis({b3[0], b3[1], b3[2], representative});
        if (b4.size() == 4) consider_q4(b4);
      }

      // A one-populated-point outside coset is invisible to the pair scan.
      // It can matter only if the local term is already large enough, or if
      // that one point is itself effective and supplies the missing local
      // gain.  These two cases are scanned separately.
      const int needed_d_one_outside =
          TARGET - base_local.dimension - ((inside_k + 1) - 4);
      if (inside_d >= needed_d_one_outside) {
        ++scanned_all_extensions;
        for (U32 q : c.populated) {
          const U32 representative = coset_representative(q, q3points);
          if (!representative) continue;
          auto b4 = canonical_basis({b3[0], b3[1], b3[2], representative});
          if (b4.size() == 4) consider_q4(b4);
        }
      } else if (inside_d + 2 >= needed_d_one_outside) {
        ++scanned_effective_extensions;
        for (U32 q : effective_points) {
          const U32 representative = coset_representative(q, q3points);
          if (!representative) continue;
          auto b4 = canonical_basis({b3[0], b3[1], b3[2], representative});
          if (b4.size() == 4) consider_q4(b4);
        }
      }
      if ((++q3_progress % 500000) == 0) {
        std::cout << "q3_progress=" << q3_progress
                  << " q4_candidates=" << q4_candidates.size() << '\n'
                  << std::flush;
      }
    }

    // The only masks for which fewer than seven populated points can meet the
    // capacity upper bound require the mask's maximum local gain.  The table
    // above verifies that this gain first occurs on a four-dimensional span
    // of effective points.  Adding every effective four-span therefore covers
    // all sparse candidates (and harmlessly duplicates some dense ones).
    for (U128 key : effective_spans[4]) consider_q4(unpack_basis(key, 4));

    std::map<int, U64> upper_hist;
    std::map<int, U64> rho_hist;
    U64 exact_evaluated = 0;
    int best_rho = 0;
    U128 best_key = 0;
    for (U128 key : q4_candidates) {
      const auto b4 = unpack_basis(key, 4);
      const int k = populated_count(b4);
      const int d = local_gain(b4);
      const int upper = base_local.dimension + d + std::max(0, k - 4);
      ++upper_hist[upper];
      if (upper < TARGET) continue;
      ++exact_evaluated;
      const int rho = c.capacity(b4);
      ++rho_hist[rho];
      if (rho > best_rho) {
        best_rho = rho;
        best_key = key;
      }
    }
    std::cout << "q4_candidates=" << q4_candidates.size()
              << " generated_q4=" << generated_q4
              << " optimistic_pruned=" << optimistic_pruned
              << " exact_upper_pruned=" << exact_upper_pruned
              << " all_extension_q3=" << scanned_all_extensions
              << " effective_extension_q3=" << scanned_effective_extensions
              << " exact_evaluated=" << exact_evaluated << " upper_hist";
    for (auto [upper, count] : upper_hist) std::cout << ' ' << upper << ':' << count;
    std::cout << " rho_hist";
    for (auto [rho, count] : rho_hist) std::cout << ' ' << rho << ':' << count;
    const auto best_basis = unpack_basis(best_key, 4);
    std::cout << " best=" << best_rho
              << " best_k=" << populated_count(best_basis)
              << " best_local_gain=" << local_gain(best_basis)
              << " best_relation_gain="
              << best_rho - base_local.dimension - local_gain(best_basis)
              << " best_basis=";
    for (U32 b : best_basis) std::cout << b << ',';
    std::cout << '\n' << std::flush;
    return;
  }

  // Enumerate all distinct two-spaces generated by populated points.
  std::unordered_set<U128, U128Hash> q2_set;
  q2_set.reserve(c.populated.size() * c.populated.size() / 3);
  for (std::size_t i = 0; i < c.populated.size(); ++i) {
    for (std::size_t j = i + 1; j < c.populated.size(); ++j) {
      const auto b = canonical_basis({c.populated[i], c.populated[j]});
      if (b.size() == 2) q2_set.insert(pack_basis(b));
    }
  }
  std::cout << "q2=" << q2_set.size() << '\n' << std::flush;

  std::vector<U128> dense_q2;
  for (U128 key : q2_set) {
    const auto b2 = unpack_basis(key, 2);
    if (c.subspace_weight(b2) >= 3) dense_q2.push_back(key);
  }
  std::cout << "dense_q2=" << dense_q2.size() << '\n' << std::flush;

  // Generate three-spaces but only retain dense ones.  This may visit the same
  // Q3 through several Q2 hyperplanes; the set canonicalizes them.
  std::unordered_set<U128, U128Hash> dense_q3;
  dense_q3.reserve(1000000);
  U64 visits = 0;
  for (U128 key : dense_q2) {
    const auto b2 = unpack_basis(key, 2);
    for (U32 q : c.populated) {
      const auto b3 = canonical_basis({b2[0], b2[1], q});
      if (b3.size() != 3) continue;
      ++visits;
      if (c.subspace_weight(b3) >= 7) dense_q3.insert(pack_basis(b3));
    }
  }
  std::cout << "q3_visits=" << visits << " dense_q3=" << dense_q3.size() << '\n'
            << std::flush;

  std::unordered_set<U128, U128Hash> candidates;
  std::map<int, U64> candidate_weight_hist;
  for (U128 key : dense_q3) {
    const auto b3 = unpack_basis(key, 3);
    const int inside = c.subspace_weight(b3);
    std::unordered_map<U32, int> coset_weight;
    for (U32 q : c.populated) {
      U32 representative = q;
      for (U32 u : points(b3)) representative = std::min(representative, q ^ u);
      if (representative) coset_weight[representative] += c.w(q);
    }
    for (const auto& [representative, outside] : coset_weight) {
      const int total = inside + outside;
      if (total < 15) continue;
      auto b4 = canonical_basis({b3[0], b3[1], b3[2], representative});
      assert(b4.size() == 4);
      const U128 q4key = pack_basis(b4);
      if (candidates.insert(q4key).second) ++candidate_weight_hist[total];
    }
  }
  std::map<int, U64> rho_hist;
  int best_rho = 0;
  U128 best_key = 0;
  for (U128 key : candidates) {
    const auto b4 = unpack_basis(key, 4);
    const int rho = c.capacity(b4);
    ++rho_hist[rho];
    if (rho > best_rho) {
      best_rho = rho;
      best_key = key;
    }
  }
  std::cout << "candidates=" << candidates.size() << " weight_hist";
  for (auto [w, count] : candidate_weight_hist) std::cout << ' ' << w << ':' << count;
  std::cout << " rho_hist";
  for (auto [rho, count] : rho_hist) std::cout << ' ' << rho << ':' << count;
  std::cout << " best=" << best_rho << " best_basis=";
  for (U32 b : unpack_basis(best_key, 4)) std::cout << b << ',';
  std::cout << '\n' << std::flush;
}

}  // namespace

int main(int argc, char** argv) {
  if (argc < 2 || argc > 3) {
    std::cerr << "usage: " << argv[0]
              << " constraint-mask [--stats|--planes|--exact]\n";
    return 2;
  }
  search(static_cast<U32>(std::stoul(argv[1], nullptr, 0)),
         argc == 3 ? std::string(argv[2]) : std::string{});
  return 0;
}

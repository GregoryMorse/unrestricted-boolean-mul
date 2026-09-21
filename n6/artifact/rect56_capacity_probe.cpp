#include <algorithm>
#include <atomic>
#include <array>
#include <cassert>
#include <cstdint>
#include <cmath>
#include <iostream>
#include <map>
#include <mutex>
#include <random>
#include <string>
#include <thread>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using U16 = std::uint16_t;
using U32 = std::uint32_t;
using U64 = std::uint64_t;
using U128 = unsigned __int128;

namespace {

#ifndef RECT_NA
#define RECT_NA 5
#endif
#ifndef RECT_NB
#define RECT_NB 6
#endif
constexpr int NA = RECT_NA;
constexpr int NB = RECT_NB;
constexpr int TARGET = NA + NB - 1;
constexpr int AMBIENT = NA * NB;
constexpr int QUOTIENT = AMBIENT - TARGET;

struct VectorHash {
  std::size_t operator()(const std::vector<U32>& xs) const noexcept {
    U64 h = 0x9e3779b97f4a7c15ULL;
    for (U32 x : xs) h ^= U64(x) + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    return static_cast<std::size_t>(h);
  }
};

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

std::vector<U32> canonical_basis(const std::vector<U32>& generators) {
  std::array<U32, QUOTIENT> rows{};
  for (U32 x : generators) {
#ifdef LOW_PIVOT_CANONICAL_AUDIT
    // Independent audit form: unique RREF with least-significant pivots.
    // The production enumerator uses the opposite pivot orientation.
    for (int p = 0; p < QUOTIENT; ++p) {
      if (((x >> p) & 1U) == 0) continue;
      if (rows[p]) {
        x ^= rows[p];
      } else {
        for (int q = p + 1; q < QUOTIENT; ++q) {
          if (rows[q] && ((x >> q) & 1U)) x ^= rows[q];
        }
        rows[p] = x;
        for (int q = 0; q < QUOTIENT; ++q) {
          if (q != p && rows[q] && ((rows[q] >> p) & 1U)) rows[q] ^= x;
        }
        break;
      }
    }
#else
    for (int p = QUOTIENT - 1; p >= 0; --p) {
      if (((x >> p) & 1U) == 0) continue;
      if (rows[p]) {
        x ^= rows[p];
      } else {
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
#endif
  }
  std::vector<U32> result;
#ifdef LOW_PIVOT_CANONICAL_AUDIT
  for (int p = 0; p < QUOTIENT; ++p) if (rows[p]) result.push_back(rows[p]);
#else
  for (int p = QUOTIENT - 1; p >= 0; --p) if (rows[p]) result.push_back(rows[p]);
#endif
  return result;
}

std::vector<U32> points(const std::vector<U32>& basis) {
  std::vector<U32> result{0};
  for (U32 b : basis) {
    const std::size_t old = result.size();
    for (std::size_t i = 0; i < old; ++i) result.push_back(result[i] ^ b);
  }
  return result;
}

U128 pack_basis(const std::vector<U32>& basis) {
  U128 key = 0;
  for (int i = 0; i < static_cast<int>(basis.size()); ++i) {
    key |= U128(basis[i]) << (QUOTIENT * i);
  }
  return key;
}

std::vector<U32> unpack_basis(U128 key, int dimension) {
  const U32 mask = (U32{1} << QUOTIENT) - 1;
  std::vector<U32> result(dimension);
  for (int i = 0; i < dimension; ++i) {
    result[i] = static_cast<U32>(key >> (QUOTIENT * i)) & mask;
  }
  return result;
}

U32 reduce_mod(U32 x, const std::vector<U32>& basis) {
  for (U32 row : basis) {
#ifdef LOW_PIVOT_CANONICAL_AUDIT
    const int pivot = __builtin_ctz(row);
#else
    const int pivot = 31 - __builtin_clz(row);
#endif
    if ((x >> pivot) & 1U) x ^= row;
  }
  return x;
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

  Reduction() {
    int target_rank = 0;
    for (int degree = 0; degree < TARGET; ++degree) {
      U32 x = 0;
      for (int i = 0; i < NA; ++i) {
        const int j = degree - i;
        if (0 <= j && j < NB) x ^= U32{1} << (i * NB + j);
      }
      U16 tag = U16{1} << degree;
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
  int weight = 0;
};

struct State {
  int rho = 0;
  int relation = 0;
  int local = 0;
  int populated = 0;
};

bool better(const State& a, const State& b) {
  return std::tie(a.rho, a.relation, a.local, a.populated)
       > std::tie(b.rho, b.relation, b.local, b.populated);
}

struct Catalogue {
  Reduction reduction;
  std::unordered_map<U32, Fiber> fibers;
  std::vector<U32> populated;
  std::vector<U32> effective;
  TargetBasis base_local;

  Catalogue() {
    std::map<U32, std::vector<U16>> grouped;
    for (int a = 1; a < (1 << NA); ++a) {
      for (int b = 1; b < (1 << NB); ++b) {
        U32 gate = 0;
        for (int i = 0; i < NA; ++i) if ((a >> i) & 1) {
          for (int j = 0; j < NB; ++j) if ((b >> j) & 1) {
            gate ^= U32{1} << (i * NB + j);
          }
        }
        const auto [q, tag] = reduction.reduce(gate);
        grouped[q].push_back(tag);
      }
    }
    for (const auto& [q, tags] : grouped) {
      Fiber fiber;
      fiber.base = tags.front();
      fiber.weight = static_cast<int>(tags.size());
      TargetBasis differences;
      for (U16 tag : tags) differences.add(tag ^ fiber.base);
      for (U16 row : differences.rows) if (row) fiber.differences.push_back(row);
      fibers.emplace(q, std::move(fiber));
      if (q) populated.push_back(q);
    }
    const Fiber& zero = fibers.at(0);
    base_local.add(zero.base);
    for (U16 d : zero.differences) base_local.add(d);
    for (U32 q : populated) {
      TargetBasis one = base_local;
      for (U16 d : fibers.at(q).differences) one.add(d);
      if (one.dimension > base_local.dimension) effective.push_back(q);
    }
  }

  State state(const std::vector<U32>& basis) const {
    TargetBasis target;
    TargetBasis local = base_local;
    std::array<U32, QUOTIENT> qrows{};
    std::array<U16, QUOTIENT> qtags{};
    State result;
    for (U32 q : points(basis)) {
      const auto it = fibers.find(q);
      if (it == fibers.end()) continue;
      if (q) ++result.populated;
      for (U16 d : it->second.differences) {
        target.add(d);
        local.add(d);
      }
      U32 x = q;
      U16 tag = it->second.base;
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
    result.rho = target.dimension;
    result.local = local.dimension - base_local.dimension;
    result.relation = result.rho - base_local.dimension - result.local;
    return result;
  }
};

struct BeamItem {
  std::vector<U32> basis;
  State state;
};

void exact_three_space_search() {
  static_assert(QUOTIENT * 3 <= 64);
  Catalogue catalogue;
  std::unordered_set<U64> q3_spaces;
  q3_spaces.reserve(2000000);
  for (std::size_t i = 0; i < catalogue.populated.size(); ++i) {
    for (std::size_t j = i + 1; j < catalogue.populated.size(); ++j) {
      auto q2 = canonical_basis({catalogue.populated[i], catalogue.populated[j]});
      if (q2.size() != 2) continue;
      for (std::size_t k = j + 1; k < catalogue.populated.size(); ++k) {
        auto q3 = canonical_basis({q2[0], q2[1], catalogue.populated[k]});
        if (q3.size() == 3) q3_spaces.insert(static_cast<U64>(pack_basis(q3)));
      }
    }
  }
  int best = 0;
  int zero_local_best = 0;
  int zero_local_relation_best = 0;
  std::map<int, U64> histogram;
  std::vector<U32> best_basis;
  for (U64 key : q3_spaces) {
    const auto basis = unpack_basis(key, 3);
    const State state = catalogue.state(basis);
    ++histogram[state.rho];
    if (state.local == 0) {
      zero_local_best = std::max(zero_local_best, state.rho);
      zero_local_relation_best = std::max(zero_local_relation_best, state.relation);
    }
    if (state.rho > best) {
      best = state.rho;
      best_basis = basis;
    }
  }
  std::cout << "exact3 populated=" << catalogue.populated.size()
            << " effective=" << catalogue.effective.size()
            << " rho0=" << catalogue.base_local.dimension
            << " q3=" << q3_spaces.size()
            << " zero_local_best=" << zero_local_best
            << " zero_local_relation_best=" << zero_local_relation_best
            << " rho_hist";
  for (const auto& [rho, count] : histogram) std::cout << ' ' << rho << ':' << count;
  std::cout << " best=" << best << " basis=";
  for (U32 b : best_basis) std::cout << b << ',';
  std::cout << '\n';
}

void exact_search(bool stats_only = false) {
  Catalogue catalogue;
  const U32 qmask = (U32{1} << QUOTIENT) - 1;
  auto populated_count = [&](const std::vector<U32>& basis) {
    int count = 0;
    for (U32 q : points(basis)) if (q && catalogue.fibers.count(q)) ++count;
    return count;
  };

  // Pair buckets are the common primitive at both extension levels: two
  // populated points lie in one coset of H exactly when their difference is
  // a nonzero direction of H.
  std::vector<std::vector<U64>> pairs(U32{1} << QUOTIENT);
  for (std::size_t i = 0; i < catalogue.populated.size(); ++i) {
    for (std::size_t j = i + 1; j < catalogue.populated.size(); ++j) {
      const U32 x = catalogue.populated[i];
      const U32 y = catalogue.populated[j];
      pairs[x ^ y].push_back(U64(x) | (U64(y) << QUOTIENT));
    }
  }

  std::unordered_set<U64> plane_q3;
  plane_q3.reserve(2000000);
  U64 pair_pair_visits = 0;
  for (const auto& bucket : pairs) {
    for (std::size_t i = 0; i < bucket.size(); ++i) {
      const U32 x = U32(bucket[i]) & qmask;
      const U32 y = U32(bucket[i] >> QUOTIENT);
      for (std::size_t j = i + 1; j < bucket.size(); ++j) {
        ++pair_pair_visits;
        const U32 z = U32(bucket[j]) & qmask;
        auto basis = canonical_basis({x, y, z});
        assert(basis.size() == 3);
        plane_q3.insert(static_cast<U64>(pack_basis(basis)));
      }
    }
  }
  std::cout << "exact pair_pair_visits=" << pair_pair_visits
            << " plane_q3=" << plane_q3.size() << '\n' << std::flush;
  std::map<std::tuple<int, int, int>, U64> plane_profile;
  for (U64 key : plane_q3) {
    const auto h3 = unpack_basis(key, 3);
    const State state = catalogue.state(h3);
    ++plane_profile[{populated_count(h3), state.local, state.rho}];
  }
  std::cout << "exact plane_profile";
  for (const auto& [profile, count] : plane_profile) {
    std::cout << " (k=" << std::get<0>(profile)
              << ",d=" << std::get<1>(profile)
              << ",rho=" << std::get<2>(profile) << "):" << count;
  }
  std::cout << '\n' << std::flush;
  std::map<int, U64> hidden_upper_histogram;
  int hidden_best_upper = 0;
  std::vector<U64> tight_hidden_h3;
  for (U64 key : plane_q3) {
    const auto h3 = unpack_basis(key, 3);
    const int inside_count = populated_count(h3);
    if (inside_count < 6) continue;
    const State hstate = catalogue.state(h3);
    int max_local_increment = 0;
    for (std::size_t i = 0; i < catalogue.effective.size(); ++i) {
      auto qspace = canonical_basis({h3[0], h3[1], h3[2], catalogue.effective[i]});
      if (qspace.size() <= 5) {
        max_local_increment = std::max(
            max_local_increment, catalogue.state(qspace).local - hstate.local);
      }
      for (std::size_t j = i + 1; j < catalogue.effective.size(); ++j) {
        qspace = canonical_basis({h3[0], h3[1], h3[2],
                                  catalogue.effective[i], catalogue.effective[j]});
        if (qspace.size() <= 5) {
          max_local_increment = std::max(
              max_local_increment, catalogue.state(qspace).local - hstate.local);
        }
      }
    }
    // If every outside H3-coset is a singleton, at most three outside points
    // occur and the relation-kernel dimension grows by at most one.  All local
    // growth is generated by the effective outside cosets considered above.
    const int upper = hstate.rho + max_local_increment + 1;
    ++hidden_upper_histogram[upper];
    hidden_best_upper = std::max(hidden_best_upper, upper);
    if (upper >= TARGET) tight_hidden_h3.push_back(key);
  }
  std::cout << "exact hidden_singleton_upper";
  for (const auto& [upper, count] : hidden_upper_histogram) {
    std::cout << ' ' << upper << ':' << count;
  }
  std::cout << " best=" << hidden_best_upper << '\n' << std::flush;
  if (stats_only) return;

  // Every dense candidate has an affine plane H3 and, among the three
  // outside H3-cosets in Q5, one containing at least two populated points.
  // Generate the corresponding Q4 and retain the necessary inside count six.
  std::unordered_set<U128, U128Hash> dense_q4;
  dense_q4.reserve(1000000);
  TargetBasis all_local = catalogue.base_local;
  for (U32 q : catalogue.effective) {
    for (U16 d : catalogue.fibers.at(q).differences) all_local.add(d);
  }
  const int global_local_gain = all_local.dimension - catalogue.base_local.dimension;
  assert(global_local_gain == 5);
  U64 q4_upper_pruned = 0;
  auto consider_dense_q4 = [&](const std::vector<U32>& q4) {
    const State state = catalogue.state(q4);
    U64 pair_mass = 0;
    for (U32 direction : points(q4)) {
      if (direction) pair_mass += pairs[direction].size();
    }
    // A coset with w populated points contributes C(w,2) pairs whose
    // differences lie in Q4.  The total pair mass therefore bounds the
    // largest possible outside-coset population.
    const int max_coset = static_cast<int>(
        (1.0 + std::sqrt(1.0 + 8.0 * static_cast<double>(pair_mass))) / 2.0);
    const int upper = state.rho + (global_local_gain - state.local)
                    + std::max(0, max_coset - 1);
    if (upper < TARGET) {
      ++q4_upper_pruned;
      return;
    }
    dense_q4.insert(pack_basis(q4));
  };
  U64 q3_progress = 0;
  for (U64 key : plane_q3) {
    const auto h3 = unpack_basis(key, 3);
    const auto hpoints = points(h3);
    bool effective_inside = false;
    for (U32 effective : catalogue.effective) {
      auto q4 = canonical_basis({h3[0], h3[1], h3[2], effective});
      if (q4.size() == 4) {
        consider_dense_q4(q4);
      } else {
        effective_inside = true;
      }
    }
    // If the effective anchor lies in H3, use a two-point outside coset to
    // obtain Q4.  Singleton-only outside patterns were isolated above.
    if (effective_inside) {
      std::unordered_set<U32> outside_cosets;
      for (U32 direction : hpoints) {
        if (!direction) continue;
        for (U64 pair : pairs[direction]) {
          const U32 x = U32(pair) & qmask;
          const U32 representative = reduce_mod(x, h3);
          if (representative) outside_cosets.insert(representative);
        }
      }
      for (U32 representative : outside_cosets) {
        auto q4 = canonical_basis({h3[0], h3[1], h3[2], representative});
        if (q4.size() == 4) consider_dense_q4(q4);
      }
    }
    if ((++q3_progress % 50000) == 0) {
      std::cout << "exact q3_progress=" << q3_progress
                << " dense_q4=" << dense_q4.size() << '\n' << std::flush;
    }
  }
  std::cout << "exact dense_q4=" << dense_q4.size()
            << " q4_upper_pruned=" << q4_upper_pruned << '\n' << std::flush;

  std::unordered_set<U128, U128Hash> q5_candidates;
  q5_candidates.reserve(2000000);
  U64 generated_q5 = 0;
  U64 upper_pruned = 0;
  std::map<int, U64> rho_histogram;
  int best = 0;
  std::vector<U32> best_basis;
  auto consider_q5 = [&](const std::vector<U32>& q5) {
    assert(q5.size() == 5);
    ++generated_q5;
    const State quick = catalogue.state(q5);
    const int upper = catalogue.base_local.dimension + quick.local
                    + std::max(0, quick.populated - 5);
    if (upper < TARGET) {
      ++upper_pruned;
      return;
    }
    if (!q5_candidates.insert(pack_basis(q5)).second) return;
    ++rho_histogram[quick.rho];
    if (quick.rho > best) {
      best = quick.rho;
      best_basis = q5;
    }
  };

  // The only dense configurations invisible to pair-detected Q4 extensions
  // have six or seven populated points in H3 and three singleton outside
  // cosets.  Only the tight H3 upper bounds need examination.  Their three
  // cosets form a line r1+r2+r3=0 in the quotient by H3.
  U64 hidden_lines = 0;
  for (U64 key : tight_hidden_h3) {
    const auto h3 = unpack_basis(key, 3);
    std::unordered_map<U32, std::pair<int, U32>> cosets;
    cosets.reserve(catalogue.populated.size() * 2);
    for (U32 q : catalogue.populated) {
      const U32 representative = reduce_mod(q, h3);
      if (!representative) continue;
      auto& entry = cosets[representative];
      ++entry.first;
      entry.second = q;
    }
    std::vector<U32> singleton;
    for (const auto& [representative, entry] : cosets) {
      if (entry.first == 1) singleton.push_back(representative);
    }
    std::sort(singleton.begin(), singleton.end());
    for (std::size_t i = 0; i < singleton.size(); ++i) {
      for (std::size_t j = i + 1; j < singleton.size(); ++j) {
        const U32 third = singleton[i] ^ singleton[j];
        if (third <= singleton[j]) continue;
        const auto it = cosets.find(third);
        if (it == cosets.end() || it->second.first != 1) continue;
        ++hidden_lines;
        auto q5 = canonical_basis(
            {h3[0], h3[1], h3[2], singleton[i], singleton[j]});
        if (q5.size() == 5) consider_q5(q5);
      }
    }
  }
  std::cout << "exact tight_hidden_h3=" << tight_hidden_h3.size()
            << " hidden_lines=" << hidden_lines
            << " hidden_candidates=" << q5_candidates.size() << '\n'
            << std::flush;

  // Extend every dense Q4 through each outside coset containing at least two
  // populated points.  A one-point outside coset is scanned separately only
  // when its maximum possible local contribution can meet the upper bound.
  std::atomic<U64> q4_progress{0};
  std::atomic<U64> dense_evaluated{0};
  std::atomic<U64> dense_upper_pruned{0};
  std::atomic<U64> all_singleton_scans{0};
  std::atomic<U64> effective_singleton_scans{0};
  std::atomic<int> dense_best{best};
  std::atomic<bool> found_target{false};
  std::mutex witness_mutex;
  std::vector<U32> dense_best_basis;
  const unsigned thread_count = std::min(8u, std::max(1u, std::thread::hardware_concurrency()));
  auto worker = [&](unsigned thread_index) {
    int local_best = 0;
    std::vector<U32> local_best_basis;
    auto evaluate = [&](const std::vector<U32>& q5) {
      if (found_target.load(std::memory_order_relaxed)) return;
      const State state = catalogue.state(q5);
      const int upper = catalogue.base_local.dimension + state.local
                      + std::max(0, state.populated - 5);
      if (upper < TARGET) {
        ++dense_upper_pruned;
        return;
      }
      ++dense_evaluated;
      if (state.rho > local_best) {
        local_best = state.rho;
        local_best_basis = q5;
      }
      if (state.rho == TARGET) {
        std::lock_guard<std::mutex> lock(witness_mutex);
        dense_best_basis = q5;
        found_target.store(true, std::memory_order_relaxed);
      }
    };
    const std::size_t buckets = dense_q4.bucket_count();
    for (std::size_t bucket = thread_index; bucket < buckets; bucket += thread_count) {
      if (found_target.load(std::memory_order_relaxed)) break;
      for (auto it = dense_q4.begin(bucket); it != dense_q4.end(bucket); ++it) {
        const auto q4 = unpack_basis(*it, 4);
        const auto q4points = points(q4);
        const State inside = catalogue.state(q4);
        std::unordered_map<U32, int> outside_pair_count;
        for (U32 direction : q4points) {
          if (!direction) continue;
          for (U64 pair : pairs[direction]) {
            const U32 x = U32(pair) & qmask;
            const U32 representative = reduce_mod(x, q4);
            if (representative) ++outside_pair_count[representative];
          }
        }
        for (const auto& [representative, pair_count] : outside_pair_count) {
          const int coset_population = static_cast<int>(
              (1.0 + std::sqrt(1.0 + 8.0 * static_cast<double>(pair_count))) / 2.0);
          const int relative_upper = inside.rho
              + (global_local_gain - inside.local) + (coset_population - 1);
          if (relative_upper < TARGET) continue;
          auto q5 = q4;
          q5.push_back(representative);
          q5 = canonical_basis(q5);
          if (q5.size() == 5) evaluate(q5);
        }
        const int needed_local = 11 - inside.populated;
        if (inside.local >= needed_local) {
          ++all_singleton_scans;
          for (U32 q : catalogue.populated) {
            const U32 representative = reduce_mod(q, q4);
            if (!representative) continue;
            auto q5 = q4;
            q5.push_back(representative);
            q5 = canonical_basis(q5);
            if (q5.size() == 5) evaluate(q5);
          }
        } else if (inside.local + 2 >= needed_local) {
          ++effective_singleton_scans;
          for (U32 q : catalogue.effective) {
            const U32 representative = reduce_mod(q, q4);
            if (!representative) continue;
            auto q5 = q4;
            q5.push_back(representative);
            q5 = canonical_basis(q5);
            if (q5.size() == 5) evaluate(q5);
          }
        }
        const U64 progress = ++q4_progress;
        if ((progress % 1000000) == 0) {
          std::cout << "exact q4_progress=" << progress
                    << " dense_best=" << dense_best.load() << '\n'
                    << std::flush;
        }
      }
    }
    std::lock_guard<std::mutex> lock(witness_mutex);
    if (local_best > dense_best.load()) {
      dense_best.store(local_best);
      dense_best_basis = std::move(local_best_basis);
    }
  };
  std::vector<std::thread> workers;
  for (unsigned thread = 0; thread < thread_count; ++thread) workers.emplace_back(worker, thread);
  for (auto& thread : workers) thread.join();
  if (found_target.load()) {
    std::cout << "exact FOUND_CAPACITY_TEN_IN_DENSE_SECTOR basis=";
    for (U32 b : dense_best_basis) std::cout << b << ',';
    std::cout << '\n';
    return;
  }
  if (dense_best.load() > best) {
    best = dense_best.load();
    best_basis = dense_best_basis;
  }
  std::cout << "exact dense_evaluated=" << dense_evaluated.load()
            << " dense_upper_pruned=" << dense_upper_pruned.load()
            << " dense_best=" << dense_best.load() << '\n' << std::flush;

  // Sparse candidates have at most eight populated points.  The upper bound
  // then requires local gain five (k=7) or at least four (k=8).  The effective
  // span table shows these gains first occur in dimensions four and three.
  std::vector<std::unordered_set<std::vector<U32>, VectorHash>> effective_spans(6);
  effective_spans[0].insert(std::vector<U32>{});
  for (U32 q : catalogue.effective) {
    const auto old = effective_spans;
    for (int dimension = 0; dimension < 5; ++dimension) {
      for (const auto& basis : old[dimension]) {
        auto generators = basis;
        generators.push_back(q);
        auto extended = canonical_basis(generators);
        if (static_cast<int>(extended.size()) == dimension + 1) {
          effective_spans[dimension + 1].insert(std::move(extended));
        }
      }
    }
  }
  for (const auto& e5 : effective_spans[5]) consider_q5(e5);
  for (const auto& e4 : effective_spans[4]) {
    if (catalogue.state(e4).local < 4) continue;
    for (U32 q : catalogue.populated) {
      auto q5 = e4;
      q5.push_back(q);
      q5 = canonical_basis(q5);
      if (q5.size() == 5) consider_q5(q5);
    }
  }
  for (const auto& e3 : effective_spans[3]) {
    if (catalogue.state(e3).local < 4) continue;
    for (std::size_t i = 0; i < catalogue.populated.size(); ++i) {
      for (std::size_t j = i + 1; j < catalogue.populated.size(); ++j) {
        auto q5 = e3;
        q5.push_back(catalogue.populated[i]);
        q5.push_back(catalogue.populated[j]);
        q5 = canonical_basis(q5);
        if (q5.size() == 5) consider_q5(q5);
      }
    }
  }

  std::cout << "exact generated_q5=" << generated_q5
            << " upper_pruned=" << upper_pruned
            << " candidates=" << q5_candidates.size()
            << " all_singleton_scans=" << all_singleton_scans
            << " effective_singleton_scans=" << effective_singleton_scans
            << " rho_hist";
  for (const auto& [rho, count] : rho_histogram) std::cout << ' ' << rho << ':' << count;
  std::cout << " best=" << best << " best_basis=";
  for (U32 b : best_basis) std::cout << b << ',';
  std::cout << '\n';
}

void run(int width, int pool_limit, int random_trials, bool require_zero_local = false,
         bool prefer_density = false) {
  Catalogue catalogue;
  std::vector<std::unordered_set<std::vector<U32>, VectorHash>> effective_spans(6);
  effective_spans[0].insert(std::vector<U32>{});
  for (U32 q : catalogue.effective) {
    const auto old = effective_spans;
    for (int dimension = 0; dimension < 5; ++dimension) {
      for (const auto& basis : old[dimension]) {
        auto generators = basis;
        generators.push_back(q);
        auto extended = canonical_basis(generators);
        if (static_cast<int>(extended.size()) == dimension + 1) {
          effective_spans[dimension + 1].insert(std::move(extended));
        }
      }
    }
  }
  std::vector<U32> pool = catalogue.effective;
  for (int i = 0; i < NA; ++i) {
    for (int j = 0; j < NB; ++j) {
      const U32 gate = U32{1} << (i * NB + j);
      const U32 q = catalogue.reduction.reduce(gate).first;
      if (q) pool.push_back(q);
    }
  }
  std::vector<U32> heavy = catalogue.populated;
  std::sort(heavy.begin(), heavy.end(), [&](U32 a, U32 b) {
    const int wa = catalogue.fibers.at(a).weight;
    const int wb = catalogue.fibers.at(b).weight;
    return wa != wb ? wa > wb : a < b;
  });
  for (int i = 0; i < std::min(pool_limit, static_cast<int>(heavy.size())); ++i) {
    pool.push_back(heavy[i]);
  }
  std::mt19937 rng(0x56c0ffeeU);
  std::shuffle(heavy.begin(), heavy.end(), rng);
  for (int i = 0; i < std::min(pool_limit, static_cast<int>(heavy.size())); ++i) {
    pool.push_back(heavy[i]);
  }
  std::sort(pool.begin(), pool.end());
  pool.erase(std::unique(pool.begin(), pool.end()), pool.end());

  std::cout << "populated=" << catalogue.populated.size()
            << " effective=" << catalogue.effective.size()
            << " rho0=" << catalogue.base_local.dimension
            << " pool=" << pool.size() << '\n';
  for (int dimension = 0; dimension <= 5; ++dimension) {
    int max_local = 0;
    std::map<int, int> histogram;
    for (const auto& basis : effective_spans[dimension]) {
      const int local = catalogue.state(basis).local;
      ++histogram[local];
      max_local = std::max(max_local, local);
    }
    std::cout << "effective_span dimension=" << dimension
              << " count=" << effective_spans[dimension].size()
              << " local_hist";
    for (const auto& [local, count] : histogram) std::cout << ' ' << local << ':' << count;
    std::cout << " max=" << max_local << '\n';
  }

  std::vector<BeamItem> beam{{{}, catalogue.state({})}};
  BeamItem overall = beam.front();
  for (int dimension = 1; dimension <= 5; ++dimension) {
    std::unordered_set<std::vector<U32>, VectorHash> seen;
    std::vector<BeamItem> next;
    seen.reserve(beam.size() * pool.size());
    for (const BeamItem& item : beam) {
      for (U32 q : pool) {
        auto generators = item.basis;
        generators.push_back(q);
        auto basis = canonical_basis(generators);
        if (static_cast<int>(basis.size()) != dimension || !seen.insert(basis).second) continue;
        State state = catalogue.state(basis);
        if (require_zero_local && state.local != 0) continue;
        next.push_back({std::move(basis), state});
        const bool improves = prefer_density
            ? std::tie(state.populated, state.rho, state.relation)
                > std::tie(overall.state.populated, overall.state.rho, overall.state.relation)
            : better(state, overall.state);
        if (improves) overall = next.back();
        if (state.rho == TARGET) {
          std::cout << "SATURATES method=beam dimension=" << dimension << " basis=";
          for (U32 b : next.back().basis) std::cout << b << ',';
          std::cout << '\n';
          return;
        }
      }
    }
    std::sort(next.begin(), next.end(), [prefer_density](const BeamItem& a, const BeamItem& b) {
      if (prefer_density) {
        const auto ka = std::tie(a.state.populated, a.state.rho, a.state.relation);
        const auto kb = std::tie(b.state.populated, b.state.rho, b.state.relation);
        if (ka != kb) return ka > kb;
      } else {
        if (better(a.state, b.state)) return true;
        if (better(b.state, a.state)) return false;
      }
      return a.basis < b.basis;
    });
    if (next.empty()) {
      std::cout << "beam dimension=" << dimension << " EMPTY\n";
      break;
    }
    if (static_cast<int>(next.size()) > width) next.resize(width);
    beam = std::move(next);
    const State& best = beam.front().state;
    std::cout << "beam dimension=" << dimension << " best=" << best.rho
              << " relation=" << best.relation << " local=" << best.local
              << " populated=" << best.populated << '\n';
  }

  std::uniform_int_distribution<int> pick(0, static_cast<int>(catalogue.populated.size()) - 1);
  for (int trial = 0; trial < random_trials; ++trial) {
    std::vector<U32> generators;
    for (int i = 0; i < 5; ++i) generators.push_back(catalogue.populated[pick(rng)]);
    auto basis = canonical_basis(generators);
    if (basis.size() != 5) continue;
    const State state = catalogue.state(basis);
    if (require_zero_local && state.local != 0) continue;
    const bool improves = prefer_density
        ? std::tie(state.populated, state.rho, state.relation)
            > std::tie(overall.state.populated, overall.state.rho, overall.state.relation)
        : better(state, overall.state);
    if (improves) overall = {basis, state};
    if (state.rho == TARGET) {
      std::cout << "SATURATES method=random basis=";
      for (U32 b : basis) std::cout << b << ',';
      std::cout << '\n';
      return;
    }
  }
  std::cout << "NO_WITNESS best=" << overall.state.rho
            << " relation=" << overall.state.relation
            << " local=" << overall.state.local
            << " populated=" << overall.state.populated << " basis=";
  for (U32 b : overall.basis) std::cout << b << ',';
  std::cout << '\n';
}

}  // namespace

int main(int argc, char** argv) {
  if (argc == 7 && std::string(argv[1]) == "--state") {
    Catalogue catalogue;
    std::vector<U32> basis;
    for (int i = 2; i < 7; ++i) basis.push_back(static_cast<U32>(std::stoul(argv[i], nullptr, 0)));
    basis = canonical_basis(basis);
    const State state = catalogue.state(basis);
    std::cout << "state dimension=" << basis.size() << " rho=" << state.rho
              << " relation=" << state.relation << " local=" << state.local
              << " populated=" << state.populated << " basis=";
    for (U32 q : basis) std::cout << q << ',';
    std::cout << '\n';
    return 0;
  }
  if (argc == 2 && std::string(argv[1]) == "--exact3") {
    exact_three_space_search();
    return 0;
  }
  if (argc == 2 && std::string(argv[1]) == "--plane-stats") {
    exact_search(true);
    return 0;
  }
  if (argc == 2 && std::string(argv[1]) == "--exact") {
    exact_search();
    return 0;
  }
  if (argc >= 2 && std::string(argv[1]) == "--zero-local") {
    const int width = argc > 2 ? std::stoi(argv[2]) : 5000;
    const int pool_limit = argc > 3 ? std::stoi(argv[3]) : 2000;
    const int random_trials = argc > 4 ? std::stoi(argv[4]) : 2000000;
    run(width, pool_limit, random_trials, true);
    return 0;
  }
  if (argc >= 2 && std::string(argv[1]) == "--zero-local-density") {
    const int width = argc > 2 ? std::stoi(argv[2]) : 5000;
    const int pool_limit = argc > 3 ? std::stoi(argv[3]) : 2000;
    const int random_trials = argc > 4 ? std::stoi(argv[4]) : 2000000;
    run(width, pool_limit, random_trials, true, true);
    return 0;
  }
  const int width = argc > 1 ? std::stoi(argv[1]) : 1000;
  const int pool_limit = argc > 2 ? std::stoi(argv[2]) : 256;
  const int random_trials = argc > 3 ? std::stoi(argv[3]) : 200000;
  run(width, pool_limit, random_trials);
}

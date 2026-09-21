#include <algorithm>
#include <array>
#include <atomic>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <mutex>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using U16 = std::uint16_t;
using U32 = std::uint32_t;
using U64 = std::uint64_t;

namespace {

constexpr int NA = 5;
constexpr int NB = 6;
constexpr int TARGET = 10;
constexpr int AMBIENT = 30;
constexpr int QUOTIENT = 20;
constexpr U32 QMASK = (U32{1} << QUOTIENT) - 1;

std::vector<U32> canonical_basis(std::vector<U32> generators) {
  std::array<U32, QUOTIENT> rows{};
  for (U32 x : generators) {
#ifdef LOW_PIVOT_CANONICAL_AUDIT
    // Independent audit form: canonicalize with least-significant pivots.
    for (int p = 0; p < QUOTIENT; ++p) {
      if (((x >> p) & 1U) == 0) continue;
      if (rows[p]) x ^= rows[p];
      else {
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
      if (rows[p]) x ^= rows[p];
      else {
        for (int q = p - 1; q >= 0; --q) if (rows[q] && ((x >> q) & 1U)) x ^= rows[q];
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

U64 pack3(const std::vector<U32>& basis) {
  assert(basis.size() == 3);
  return U64(basis[0]) | (U64(basis[1]) << QUOTIENT)
       | (U64(basis[2]) << (2 * QUOTIENT));
}

std::array<U32, 3> unpack3(U64 key) {
  return {U32(key) & QMASK, U32(key >> QUOTIENT) & QMASK,
          U32(key >> (2 * QUOTIENT)) & QMASK};
}

U32 reduce_mod(U32 x, const std::array<U32, 3>& basis) {
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
  U16 reduce(U16 x) const {
    for (int p = TARGET - 1; p >= 0; --p) {
      if (((x >> p) & 1U) && rows[p]) x ^= rows[p];
    }
    return x;
  }
};

struct Reduction {
  std::array<U32, AMBIENT> rows{};
  std::array<U16, AMBIENT> tags{};
  std::array<bool, AMBIENT> has{};
  std::array<int, QUOTIENT> nonpivots{};

  Reduction() {
    for (int degree = 0; degree < TARGET; ++degree) {
      U32 x = 0;
      for (int i = 0; i < NA; ++i) {
        const int j = degree - i;
        if (0 <= j && j < NB) x ^= U32{1} << (i * NB + j);
      }
      U16 tag = U16{1} << degree;
      for (int p = AMBIENT - 1; p >= 0; --p) {
        if (((x >> p) & 1U) == 0) continue;
        if (has[p]) { x ^= rows[p]; tag ^= tags[p]; }
        else { has[p] = true; rows[p] = x; tags[p] = tag; break; }
      }
    }
    int q = 0;
    for (int p = 0; p < AMBIENT; ++p) if (!has[p]) nonpivots[q++] = p;
    assert(q == QUOTIENT);
  }

  std::pair<U32, U16> reduce(U32 x) const {
    U16 tag = 0;
    for (int p = AMBIENT - 1; p >= 0; --p) {
      if (((x >> p) & 1U) && has[p]) { x ^= rows[p]; tag ^= tags[p]; }
    }
    U32 q = 0;
    for (int i = 0; i < QUOTIENT; ++i) if ((x >> nonpivots[i]) & 1U) q ^= U32{1} << i;
    return {q, tag};
  }
};

struct Catalogue {
  std::vector<U32> zero_local;
  std::vector<U32> effective;
  std::unordered_map<U32, U16> labels;
  std::unordered_map<U32, U32> left_masks;
  std::unordered_map<U32, U64> right_masks;
  TargetBasis base;

  Catalogue() {
    Reduction reduction;
    std::unordered_map<U32, std::vector<U16>> fibers;
    for (int a = 1; a < (1 << NA); ++a) {
      for (int b = 1; b < (1 << NB); ++b) {
        U32 gate = 0;
        for (int i = 0; i < NA; ++i) if ((a >> i) & 1) {
          for (int j = 0; j < NB; ++j) if ((b >> j) & 1) gate ^= U32{1} << (i * NB + j);
        }
        auto [q, tag] = reduction.reduce(gate);
        fibers[q].push_back(tag);
        left_masks[q] |= U32{1} << a;
        right_masks[q] |= U64{1} << b;
      }
    }
    const auto& zero_tags = fibers.at(0);
    base.add(zero_tags.front());
    for (U16 tag : zero_tags) base.add(tag ^ zero_tags.front());
    assert(base.dimension == 3);
    for (const auto& [q, tags] : fibers) {
      if (!q) continue;
      TargetBasis local = base;
      for (U16 tag : tags) local.add(tag ^ tags.front());
      if (local.dimension == 3) {
        zero_local.push_back(q);
        labels.emplace(q, base.reduce(tags.front()));
      } else {
        effective.push_back(q);
      }
    }
    std::sort(zero_local.begin(), zero_local.end());
    std::sort(effective.begin(), effective.end());
    assert(zero_local.size() == 1785 && effective.size() == 12);
  }
};

struct SpaceKey {
  std::array<U32, 5> basis{};
  std::uint8_t dimension = 0;
  bool operator==(const SpaceKey& other) const {
    return dimension == other.dimension && basis == other.basis;
  }
};

struct SpaceKeyHash {
  std::size_t operator()(const SpaceKey& key) const {
    std::size_t hash = key.dimension;
    for (U32 row : key.basis) {
      hash ^= std::size_t(row) + 0x9e3779b9U + (hash << 6) + (hash >> 2);
    }
    return hash;
  }
};

int factor_rank(U64 mask, int width) {
  std::array<U64, NB> rows{};
  int rank = 0;
  for (int value = 1; value < (1 << width); ++value) {
    if (((mask >> value) & 1U) == 0) continue;
    U64 x = value;
    for (int p = width - 1; p >= 0; --p) {
      if (((x >> p) & 1U) == 0) continue;
      if (rows[p]) x ^= rows[p];
      else { rows[p] = x; ++rank; break; }
    }
  }
  return rank;
}

bool contains_degree_two_block(const TargetBasis& relation) {
  // Lifts of K=ker<02,3d,41> from T/R to the ten target coordinates.
  return relation.reduce(0x018) == 0 && relation.reduce(0x028) == 0
      && relation.reduce(0x048) == 0 && relation.reduce(0x08a) == 0;
}

}  // namespace

int main(int argc, char** argv) {
  const bool exhaustive = argc == 2 && std::string(argv[1]) == "--exhaustive";
  Catalogue catalogue;
  std::vector<std::vector<U64>> pairs(U32{1} << QUOTIENT);
  for (std::size_t i = 0; i < catalogue.zero_local.size(); ++i) {
    for (std::size_t j = i + 1; j < catalogue.zero_local.size(); ++j) {
      const U32 x = catalogue.zero_local[i];
      const U32 y = catalogue.zero_local[j];
      pairs[x ^ y].push_back(U64(x) | (U64(y) << QUOTIENT));
    }
  }

  std::unordered_set<U64> planes;
  planes.reserve(2000000);
  U64 pair_pair_visits = 0;
  for (const auto& bucket : pairs) {
    for (std::size_t i = 0; i < bucket.size(); ++i) {
      const U32 x = U32(bucket[i]) & QMASK;
      const U32 y = U32(bucket[i] >> QUOTIENT);
      for (std::size_t j = i + 1; j < bucket.size(); ++j) {
        ++pair_pair_visits;
        const U32 z = U32(bucket[j]) & QMASK;
        auto basis = canonical_basis({x, y, z});
        assert(basis.size() == 3);
        planes.insert(pack3(basis));
      }
    }
  }
  std::cout << "zero_local_points=" << catalogue.zero_local.size()
            << " effective=" << catalogue.effective.size()
            << " pair_pair_visits=" << pair_pair_visits
            << " planes=" << planes.size() << '\n' << std::flush;

  std::vector<U64> plane_keys(planes.begin(), planes.end());
  planes.clear();
  planes.rehash(0);
  std::atomic<std::size_t> cursor{0};
  std::atomic<U64> checked{0};
  std::atomic<int> best{0};
  std::atomic<int> best_relation{0};
  std::atomic<bool> found{false};
  std::atomic<U64> dense_occurrences{0};
  std::atomic<U64> k_block_occurrences{0};
  std::array<std::atomic<U64>, (NA + 1) * (NB + 1)> k_support_hist{};
  std::atomic<U64> k_support_violations{0};
  std::atomic<U64> fixed_rectangle_violations{0};
  std::unordered_set<SpaceKey, SpaceKeyHash> k_spaces;
  std::mutex k_space_mutex;
  U32 fixed_left_mask = 0;
  U64 fixed_right_mask = 0;
  for (int a = 1; a < (1 << NA); ++a) {
    if ((__builtin_popcount(a & 0x15) & 1) == 0) fixed_left_mask |= U32{1} << a;
  }
  for (int b = 1; b < (1 << NB); ++b) {
    if ((__builtin_popcount(b & 0x15) & 1) == 0
        && (__builtin_popcount(b & 0x2a) & 1) == 0) {
      fixed_right_mask |= U64{1} << b;
    }
  }
  std::mutex witness_mutex;
  std::array<U32, 5> witness{};
  std::atomic<int> witness_dimension{0};
  const unsigned thread_count = std::min(8u, std::max(1u, std::thread::hardware_concurrency()));

  auto worker = [&]() {
    struct Summary {
      U16 count = 0;
      U16 base = 0;
      TargetBasis differences;
      U32 left_mask = 0;
      U64 right_mask = 0;
    };
    std::vector<Summary> summaries(U32{1} << QUOTIENT);
    std::vector<U32> touched;
    touched.reserve(catalogue.zero_local.size());
    std::array<U32, 12> forbidden{};
    while (exhaustive || !found.load(std::memory_order_relaxed)) {
      const std::size_t index = cursor.fetch_add(1);
      if (index >= plane_keys.size()) break;
      const auto h = unpack3(plane_keys[index]);
      bool bad_h = false;
      for (std::size_t i = 0; i < catalogue.effective.size(); ++i) {
        forbidden[i] = reduce_mod(catalogue.effective[i], h);
        if (!forbidden[i]) bad_h = true;
      }
      if (bad_h) continue;

      std::array<U32, QUOTIENT> qrows{};
      std::array<U16, QUOTIENT> qtags{};
      TargetBasis hrelations;
      for (U32 q : catalogue.zero_local) {
        if (reduce_mod(q, h) != 0) continue;
        U32 x = q;
        U16 tag = catalogue.labels.at(q);
        bool inserted = false;
        for (int p = QUOTIENT - 1; p >= 0; --p) {
          if (((x >> p) & 1U) == 0) continue;
          if (qrows[p]) { x ^= qrows[p]; tag ^= qtags[p]; }
          else { qrows[p] = x; qtags[p] = tag; inserted = true; break; }
        }
        if (!inserted) hrelations.add(tag);
      }

      touched.clear();
      for (U32 q : catalogue.zero_local) {
        const U32 r = reduce_mod(q, h);
        U32 x = q;
        U16 tag = catalogue.labels.at(q);
        for (int p = QUOTIENT - 1; p >= 0; --p) {
          if (((x >> p) & 1U) && qrows[p]) { x ^= qrows[p]; tag ^= qtags[p]; }
        }
        tag = hrelations.reduce(tag);
        Summary& summary = summaries[r];
        summary.left_mask |= catalogue.left_masks.at(q);
        summary.right_mask |= catalogue.right_masks.at(q);
        if (summary.count++ == 0) {
          summary.base = tag;
          touched.push_back(r);
        } else {
          summary.differences.add(tag ^ summary.base);
        }
      }
      const int inside = summaries[0].count;
      // A relation-only saturating space can have dimension four: it then
      // needs at least 4+7=11 populated points.  Relative to H there is only
      // one outside coset, whose internal differences give every new
      // relation.
      for (U32 r : touched) {
        if (!r || inside + summaries[r].count < 11) continue;
        bool r_forbidden = false;
        for (U32 f : forbidden) if (f == r) r_forbidden = true;
        if (r_forbidden) continue;
        TargetBasis relation = hrelations;
        for (U16 row : summaries[r].differences.rows) if (row) relation.add(row);
        int old_relation = best_relation.load();
        while (relation.dimension > old_relation
               && !best_relation.compare_exchange_weak(old_relation, relation.dimension)) {}
        if (contains_degree_two_block(relation)) {
          ++k_block_occurrences;
          const int arank = factor_rank(
              U64(summaries[0].left_mask | summaries[r].left_mask), NA);
          const int brank = factor_rank(
              summaries[0].right_mask | summaries[r].right_mask, NB);
          ++k_support_hist[arank * (NB + 1) + brank];
          if (arank > 4 || brank > 4) ++k_support_violations;
          if (((summaries[0].left_mask | summaries[r].left_mask) & ~fixed_left_mask)
              || ((summaries[0].right_mask | summaries[r].right_mask) & ~fixed_right_mask)) {
            ++fixed_rectangle_violations;
          }
          auto q4 = canonical_basis({h[0], h[1], h[2], r});
          SpaceKey key;
          key.dimension = 4;
          for (int i = 0; i < 4; ++i) key.basis[i] = q4[i];
          std::lock_guard<std::mutex> lock(k_space_mutex);
          k_spaces.insert(key);
        }
        if (relation.dimension == 7) {
          auto q4 = canonical_basis({h[0], h[1], h[2], r});
          assert(q4.size() == 4);
          std::lock_guard<std::mutex> lock(witness_mutex);
          for (int i = 0; i < 4; ++i) witness[i] = q4[i];
          witness[4] = 0;
          witness_dimension.store(4);
          found.store(true);
          break;
        }
      }
      if (found.load() && !exhaustive) {
        for (U32 r : touched) summaries[r] = Summary{};
        break;
      }
      const int heavy_threshold = (12 - inside + 2) / 3;
      for (U32 r : touched) {
        if (!r || summaries[r].count < heavy_threshold) continue;
        bool r_forbidden = false;
        for (U32 f : forbidden) if (f == r) r_forbidden = true;
        if (r_forbidden) continue;
        for (U32 s : touched) {
          if (!s || s == r) continue;
          const U32 t = r ^ s;
          bool line_forbidden = false;
          for (U32 f : forbidden) if (f == s || f == t) line_forbidden = true;
          if (line_forbidden) continue;
          const int population = inside + summaries[r].count
                               + summaries[s].count + summaries[t].count;
          int old = best.load();
          while (population > old && !best.compare_exchange_weak(old, population)) {}
          if (population >= 12) {
            ++dense_occurrences;
            TargetBasis relation = hrelations;
            for (U16 row : summaries[r].differences.rows) if (row) relation.add(row);
            for (U16 row : summaries[s].differences.rows) if (row) relation.add(row);
            for (U16 row : summaries[t].differences.rows) if (row) relation.add(row);
            if (summaries[t].count) {
              relation.add(summaries[r].base ^ summaries[s].base ^ summaries[t].base);
            }
            int old_relation = best_relation.load();
            while (relation.dimension > old_relation
                   && !best_relation.compare_exchange_weak(old_relation, relation.dimension)) {}
            if (contains_degree_two_block(relation)) {
              ++k_block_occurrences;
              const U32 left_mask = summaries[0].left_mask | summaries[r].left_mask
                                  | summaries[s].left_mask | summaries[t].left_mask;
              const U64 right_mask = summaries[0].right_mask | summaries[r].right_mask
                                   | summaries[s].right_mask | summaries[t].right_mask;
              const int arank = factor_rank(U64(left_mask), NA);
              const int brank = factor_rank(right_mask, NB);
              ++k_support_hist[arank * (NB + 1) + brank];
              if (arank > 4 || brank > 4) ++k_support_violations;
              if ((left_mask & ~fixed_left_mask) || (right_mask & ~fixed_right_mask)) {
                ++fixed_rectangle_violations;
              }
              auto q5 = canonical_basis({h[0], h[1], h[2], r, s});
              SpaceKey key;
              key.dimension = 5;
              for (int i = 0; i < 5; ++i) key.basis[i] = q5[i];
              std::lock_guard<std::mutex> lock(k_space_mutex);
              k_spaces.insert(key);
            }
            if (relation.dimension == 7) {
              auto q5 = canonical_basis({h[0], h[1], h[2], r, s});
              assert(q5.size() == 5);
              std::lock_guard<std::mutex> lock(witness_mutex);
              for (int i = 0; i < 5; ++i) witness[i] = q5[i];
              witness_dimension.store(5);
              found.store(true);
              break;
            }
            continue;
          }
        }
        if (found.load()) break;
      }
      for (U32 r : touched) summaries[r] = Summary{};
      const U64 done = ++checked;
      if ((done % 100000) == 0) {
        std::cout << "checked=" << done << " best=" << best.load()
                  << " best_relation=" << best_relation.load() << '\n' << std::flush;
      }
    }
  };

  std::vector<std::thread> threads;
  for (unsigned i = 0; i < thread_count; ++i) threads.emplace_back(worker);
  for (auto& thread : threads) thread.join();
  std::cout << "completed=" << checked.load() << " best=" << best.load()
            << " best_relation=" << best_relation.load()
            << " dense_occurrences=" << dense_occurrences.load()
            << " k_block_occurrences=" << k_block_occurrences.load()
            << " k_support_violations=" << k_support_violations.load()
            << " fixed_rectangle_violations=" << fixed_rectangle_violations.load()
            << " unique_k_spaces=" << k_spaces.size()
            << " found_twelve=" << found.load();
  if (found.load()) {
    std::cout << " dimension=" << witness_dimension.load() << " basis=";
    for (int i = 0; i < witness_dimension.load(); ++i) std::cout << witness[i] << ',';
  }
  int printed = 0;
  std::cout << " k_space_examples=";
  for (const SpaceKey& key : k_spaces) {
    if (printed++ == 20) break;
    std::cout << int(key.dimension) << ':';
    for (int i = 0; i < key.dimension; ++i) std::cout << key.basis[i] << '.';
    std::cout << ',';
  }
  std::cout << " k_support_hist=";
  for (int a = 0; a <= NA; ++a) for (int b = 0; b <= NB; ++b) {
    const U64 count = k_support_hist[a * (NB + 1) + b].load();
    if (count) std::cout << '(' << a << ',' << b << "):" << count << ',';
  }
  std::cout << '\n';
  return found.load() ? 10 : 0;
}

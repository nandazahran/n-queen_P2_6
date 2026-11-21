// Solver for the Pre-placed case: adaptive bitmask backtracking with D4 symmetry (P = 0), gap-shift bitmask DFS
// (P = 1), and bitmask MRV with forward checking & hidden-single propagation (P >= 2).
//
// ---- Mode & entry point --------------------------------------------------------------------------------------------
//   solvePreplaced(n, preplaced)    Pre-placed case: locked queens at (row, col) must stay in every solution.
//
// ---- The idea ------------------------------------------------------------------------------------------------------
// Pre-placed boards vary from completely unconstrained (P = 0) to heavily constrained (P >= 2). A single fixed
// search strategy leaves performance on the table, so this solver validates the locked queens first and picks the
// fastest exact search for the constraint level:
//
//   P == 0   The board is empty, so 8-fold D4 canonical border-symmetry bitmask search solves it directly.
//   P == 1   One locked queen leaves N - 1 free rows. Pre-baking its column and diagonal attacks into per-row allowed
//            masks lets a pure gap-shift bitmask DFS walk the remaining rows without MRV scanning overhead.
//   P >= 2   Multiple locked queens tightly restrict rows and columns. Keeping taken columns and both diagonals in
//            three shiftable bitmasks (colMask, diagSum, diagDiff) computes any row's open columns in O(1), enabling
//            Minimum Remaining Values (MRV) branching, row/column forward checking, hidden-single unit propagation,
//            and last-two-rows unrolling.
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "nqueens.h"

namespace {  // names in here belong to this file only

constexpr int kMaxN = 16;

struct Fundamental {
  uint8_t cols[kMaxN];
  uint8_t mask;
};

inline void applyD4(int k, const uint8_t* src, uint8_t* dst, int n) {
  const int m = n - 1;
  switch (k) {
    case 0: for (int r = 0; r < n; ++r) dst[r] = src[r]; break;
    case 1: for (int r = 0; r < n; ++r) dst[r] = static_cast<uint8_t>(m - src[r]); break;
    case 2: for (int r = 0; r < n; ++r) dst[m - r] = src[r]; break;
    case 3: for (int r = 0; r < n; ++r) dst[m - r] = static_cast<uint8_t>(m - src[r]); break;
    case 4: for (int r = 0; r < n; ++r) dst[src[r]] = static_cast<uint8_t>(r); break;
    case 5: for (int r = 0; r < n; ++r) dst[src[r]] = static_cast<uint8_t>(m - r); break;
    case 6: for (int r = 0; r < n; ++r) dst[m - src[r]] = static_cast<uint8_t>(r); break;
    default: for (int r = 0; r < n; ++r) dst[m - src[r]] = static_cast<uint8_t>(m - r); break;
  }
}

inline int cmpBoard(const uint8_t* a, const uint8_t* b, int n) {
  for (int r = 0; r < n; ++r) {
    if (a[r] != b[r]) return a[r] < b[r] ? -1 : 1;
  }
  return 0;
}

// Fast D4 canonical symmetry solver used when P == 0.
struct NormalD4 {
  int n = 0, m = 0;
  uint32_t full = 0;
  uint32_t rowMask[kMaxN]{};
  uint8_t cols[kMaxN]{};
  static constexpr int kStackCap = 2048;
  Fundamental stackBuf[kStackCap];
  int stackCount = 0;
  std::vector<Fundamental> heapBuf;
  size_t totalSolutions = 0;

  void addFundamental(uint8_t mask, int orbitSize) {
    Fundamental f;
    for (int r = 0; r < n; ++r) f.cols[r] = cols[r];
    f.mask = mask;
    if (stackCount < kStackCap) stackBuf[stackCount++] = f;
    else heapBuf.push_back(f);
    totalSolutions += static_cast<size_t>(orbitSize);
  }

  void onCornerLeaf(int c1) {
    if (cols[c1] != 1) { addFundamental(0xFFu, 8); return; }
    uint8_t inv[kMaxN];
    for (int r = 0; r < n; ++r) inv[cols[r]] = static_cast<uint8_t>(r);
    const int c = cmpBoard(cols, inv, n);
    if (c > 0) return;
    addFundamental(c == 0 ? 0x69u : 0xFFu, c == 0 ? 4 : 8);
  }

  void onInteriorLeaf(int c0) {
    const bool tied = (cols[m] == c0 || cols[m] == m - c0 ||
                       cols[c0] == 0 || cols[c0] == m ||
                       cols[m - c0] == 0 || cols[m - c0] == m);
    if (!tied) { addFundamental(0xFFu, 8); return; }
    uint8_t imgs[8][kMaxN];
    for (int r = 0; r < n; ++r) imgs[0][r] = cols[r];
    for (int k = 1; k < 8; ++k) {
      applyD4(k, cols, imgs[k], n);
      if (cmpBoard(imgs[k], imgs[0], n) < 0) return;
    }
    uint8_t mask = 1u;
    int orbitSize = 1;
    for (int k = 1; k < 8; ++k) {
      bool dup = false;
      for (int j = 0; j < k; ++j) {
        if (((mask >> j) & 1u) && cmpBoard(imgs[k], imgs[j], n) == 0) { dup = true; break; }
      }
      if (!dup) { mask |= static_cast<uint8_t>(1u << k); ++orbitSize; }
    }
    addFundamental(mask, orbitSize);
  }

  template <bool Corner>
  void dfs(int row, uint32_t col, uint32_t d1, uint32_t d2, int keyCol) {
    uint32_t avail = rowMask[row] & ~(col | d1 | d2);
    if (row == n - 2) {
      const uint32_t lastMask = rowMask[n - 1];
      while (avail) {
        const uint32_t b = avail & -avail;
        avail ^= b;
        const uint32_t c2 = col | b;
        const uint32_t last = lastMask & ~(c2 | ((d1 | b) << 1) | ((d2 | b) >> 1));
        if (last) {
          cols[n - 2] = static_cast<uint8_t>(__builtin_ctz(b));
          cols[n - 1] = static_cast<uint8_t>(__builtin_ctz(last));
          if constexpr (Corner) onCornerLeaf(keyCol);
          else onInteriorLeaf(keyCol);
        }
      }
      return;
    }
    while (avail) {
      const uint32_t b = avail & -avail;
      avail ^= b;
      cols[row] = static_cast<uint8_t>(__builtin_ctz(b));
      dfs<Corner>(row + 1, col | b, (d1 | b) << 1, (d2 | b) >> 1, keyCol);
    }
  }

  std::vector<std::vector<int>> solve(int size) {
    if (size == 1) {
      std::vector<std::vector<int>> out = {{0}};
      NQ_SNAPSHOT(nq::queensOf(out[0]), "solution 1");
      return out;
    }
    if (size < 4) return {};
    n = size; m = size - 1; full = (1u << n) - 1u;

    cols[0] = 0;
    for (int c1 = 2; c1 < n; ++c1) {
      cols[1] = static_cast<uint8_t>(c1);
      for (int r = 2; r < n; ++r) rowMask[r] = (r < c1) ? (full & ~2u) : full;
      const uint32_t b0 = 1u, b1 = 1u << c1;
      dfs<true>(2, b0 | b1, ((b0 << 1) | b1) << 1, ((b0 >> 1) | b1) >> 1, c1);
    }

    const uint32_t noSides = full & ~(1u | (1u << m));
    for (int c0 = 1; c0 <= (n - 2) / 2; ++c0) {
      cols[0] = static_cast<uint8_t>(c0);
      for (int r = 1; r < n - 1; ++r) rowMask[r] = (r < c0 || r >= n - c0) ? noSides : full;
      rowMask[n - 1] = ((1u << (n - 2 * c0)) - 1u) << c0;
      const uint32_t b0 = 1u << c0;
      dfs<false>(1, b0, b0 << 1, b0 >> 1, c0);
    }

    std::vector<std::vector<int>> solutions;
    solutions.reserve(totalSolutions);
    const bool debug = snapshotsEnabled();
    auto emit = [&](const Fundamental& f) {
      uint8_t tmp[kMaxN];
      int buf[kMaxN];
      for (int k = 0; k < 8; ++k) {
        if (!((f.mask >> k) & 1u)) continue;
        applyD4(k, f.cols, tmp, n);
        for (int r = 0; r < n; ++r) buf[r] = tmp[r];
        solutions.emplace_back(buf, buf + n);
        if (__builtin_expect(debug, 0)) {
          snapshot(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));
        }
      }
    };
    for (int i = 0; i < stackCount; ++i) emit(stackBuf[i]);
    for (const auto& f : heapBuf) emit(f);
    return solutions;
  }
};

struct CompactSol {
  uint8_t cols[kMaxN];
};

struct PreplacedSearch {
  int n = 0;
  int m = 0;
  uint32_t full = 0;
  uint8_t cols[kMaxN]{};
  int remRows[kMaxN]{};

  static constexpr int kStackCap = 2048;
  CompactSol stackSols[kStackCap];
  int stackCount = 0;
  std::vector<CompactSol> heapSols;

  inline void record() {
    CompactSol s;
    for (int r = 0; r < n; ++r) s.cols[r] = cols[r];
    if (stackCount < kStackCap) stackSols[stackCount++] = s;
    else heapSols.push_back(s);
  }

  // O(1) bitmask availability for row r:
  // diagSum holds bit (r + c), diagDiff holds bit (c - r + n - 1).
  inline uint32_t availFor(int r, uint32_t colMask, uint32_t diagSum, uint32_t diagDiff) const {
    return full & ~(colMask | (diagSum >> r) | (diagDiff >> (m - r)));
  }

  // Bitmask MRV search with row/column forward checking, unit propagation, and last-two-rows unrolling.
  void dfs(int rem, uint32_t colMask, uint32_t diagSum, uint32_t diagDiff) {
    if (rem == 1) {
      const int r0 = remRows[0];
      const uint32_t a0 = availFor(r0, colMask, diagSum, diagDiff);
      if (a0) {
        cols[r0] = static_cast<uint8_t>(__builtin_ctz(a0));
        record();
      }
      return;
    }
    if (rem == 2) {
      const int r0 = remRows[0], r1 = remRows[1];
      uint32_t a0 = availFor(r0, colMask, diagSum, diagDiff);
      if (!a0) return;
      const uint32_t a1Base = availFor(r1, colMask, diagSum, diagDiff);
      if (!a1Base) return;
      while (a0) {
        const uint32_t b0 = a0 & -a0;
        a0 ^= b0;
        const int c0 = __builtin_ctz(b0);
        const uint32_t ds = diagSum | (1u << (r0 + c0));
        const uint32_t dd = diagDiff | (1u << (c0 - r0 + m));
        const uint32_t a1 = a1Base & ~(b0 | (ds >> r1) | (dd >> (m - r1)));
        if (a1) {
          cols[r0] = static_cast<uint8_t>(c0);
          cols[r1] = static_cast<uint8_t>(__builtin_ctz(a1));
          record();
        }
      }
      return;
    }

    uint32_t rowAvail[kMaxN];
    int bestIdx = -1;
    int bestCount = 32;
    uint32_t once = 0, twice = 0;

    for (int i = 0; i < rem; ++i) {
      const int r = remRows[i];
      const uint32_t a = availFor(r, colMask, diagSum, diagDiff);
      if (!a) return;  // dead row
      rowAvail[i] = a;
      const int cnt = __builtin_popcount(a);
      if (cnt < bestCount) {
        bestCount = cnt;
        bestIdx = i;
        if (cnt == 1) {
          // Forced row: propagate immediately.
          const int c = __builtin_ctz(a);
          cols[r] = static_cast<uint8_t>(c);
          remRows[i] = remRows[rem - 1];
          dfs(rem - 1, colMask | a, diagSum | (1u << (r + c)), diagDiff | (1u << (c - r + m)));
          remRows[i] = r;
          return;
        }
      }
      twice |= (once & a);
      once |= a;
    }

    // Column forward checking: every free column must be reachable by at least one remaining row.
    if ((once | colMask) != full) return;

    // Hidden single column: a free column reachable by only one remaining row forces that cell.
    const uint32_t uniqueCols = once & ~twice;
    if (uniqueCols) {
      const uint32_t colBit = uniqueCols & -uniqueCols;
      const int c = __builtin_ctz(colBit);
      int idx = 0;
      while (!(rowAvail[idx] & colBit)) ++idx;
      const int r = remRows[idx];
      cols[r] = static_cast<uint8_t>(c);
      remRows[idx] = remRows[rem - 1];
      dfs(rem - 1, colMask | colBit, diagSum | (1u << (r + c)), diagDiff | (1u << (c - r + m)));
      remRows[idx] = r;
      return;
    }

    // Branch on the most constrained row.
    const int r = remRows[bestIdx];
    uint32_t avail = rowAvail[bestIdx];
    remRows[bestIdx] = remRows[rem - 1];
    while (avail) {
      const uint32_t b = avail & -avail;
      avail ^= b;
      const int c = __builtin_ctz(b);
      cols[r] = static_cast<uint8_t>(c);
      dfs(rem - 1, colMask | b, diagSum | (1u << (r + c)), diagDiff | (1u << (c - r + m)));
    }
    remRows[bestIdx] = r;
  }

  uint32_t rowAllowed[kMaxN]{};
  int gap[kMaxN]{};
  int freeCount = 0;

  // Fast gap-shift bitmask DFS for P == 1: locked-queen attacks are baked into rowAllowed[i].
  void dfsShift(int i, uint32_t col, uint32_t d1, uint32_t d2) {
    uint32_t avail = rowAllowed[i] & ~(col | d1 | d2);
    const int r = remRows[i];
    if (i == freeCount - 2) {
      const int g = gap[i];
      const int rLast = remRows[i + 1];
      const uint32_t lastAllowed = rowAllowed[i + 1];
      while (avail) {
        const uint32_t b = avail & -avail;
        avail ^= b;
        const uint32_t last = lastAllowed & ~((col | b) | ((d1 | b) << g) | ((d2 | b) >> g));
        if (last) {
          cols[r] = static_cast<uint8_t>(__builtin_ctz(b));
          cols[rLast] = static_cast<uint8_t>(__builtin_ctz(last));
          record();
        }
      }
      return;
    }
    const int g = gap[i];
    while (avail) {
      const uint32_t b = avail & -avail;
      avail ^= b;
      cols[r] = static_cast<uint8_t>(__builtin_ctz(b));
      dfsShift(i + 1, col | b, ((d1 | b) << g) & full, (d2 | b) >> g);
    }
  }

  std::vector<std::vector<int>> materialize() const {
    const size_t total = static_cast<size_t>(stackCount) + heapSols.size();
    std::vector<std::vector<int>> solutions;
    solutions.reserve(total);
    const bool debug = snapshotsEnabled();
    int buf[kMaxN];
    auto emit = [&](const CompactSol& s) {
      for (int r = 0; r < n; ++r) buf[r] = s.cols[r];
      solutions.emplace_back(buf, buf + n);
      if (__builtin_expect(debug, 0)) {
        snapshot(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));
      }
    };
    for (int i = 0; i < stackCount; ++i) emit(stackSols[i]);
    for (const auto& s : heapSols) emit(s);
    return solutions;
  }
};

}  // namespace

std::vector<std::vector<int>> solvePreplaced(int n, const std::vector<std::pair<int, int>>& preplaced) {
  if (n <= 0 || n > kMaxN) return {};
  if (preplaced.empty()) {
    NormalD4 normal;
    return normal.solve(n);
  }

  const int m = n - 1;
  uint32_t usedRows = 0, colMask = 0, diagSum = 0, diagDiff = 0;
  PreplacedSearch search;
  search.n = n;
  search.m = m;
  search.full = (1u << n) - 1u;

  for (const auto& q : preplaced) {
    const int r = q.first, c = q.second;
    if (r < 0 || r >= n || c < 0 || c >= n) return {};
    const uint32_t rb = 1u << r;
    const uint32_t cb = 1u << c;
    const uint32_t s1 = 1u << (r + c);
    const uint32_t s2 = 1u << (c - r + m);
    if ((usedRows & rb) || (colMask & cb) || (diagSum & s1) || (diagDiff & s2)) return {};
    usedRows |= rb;
    colMask |= cb;
    diagSum |= s1;
    diagDiff |= s2;
    search.cols[r] = static_cast<uint8_t>(c);
  }

  int rem = 0;
  for (int r = 0; r < n; ++r) {
    if (!((usedRows >> r) & 1u)) search.remRows[rem++] = r;
  }

  if (rem == 0) {
    search.record();
  } else if (preplaced.size() == 1 && rem >= 3) {
    // Visit from the half containing the locked queen so tighter rows are pruned earlier.
    if (preplaced[0].first > m / 2) {
      for (int i = 0; i < rem / 2; ++i) std::swap(search.remRows[i], search.remRows[rem - 1 - i]);
    }
    search.freeCount = rem;
    for (int i = 0; i < rem; ++i) {
      const int r = search.remRows[i];
      search.rowAllowed[i] = search.availFor(r, colMask, diagSum, diagDiff);
      if (!search.rowAllowed[i]) return {};
      if (i + 1 < rem) {
        const int diff = search.remRows[i + 1] - r;
        search.gap[i] = diff < 0 ? -diff : diff;
      }
    }
    search.dfsShift(0, 0, 0, 0);
  } else {
    search.dfs(rem, colMask, diagSum, diagDiff);
  }
  return search.materialize();
}

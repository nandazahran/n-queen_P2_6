// Solver for the Normal case: 8-fold dihedral (D4) canonical border-symmetry bitmask backtracking.
//
// ---- Mode & entry point --------------------------------------------------------------------------------------------
//   solveNQueens(n)    Normal case: N queens on an empty N x N board, one queen per row.
//
// ---- The idea ------------------------------------------------------------------------------------------------------
// The square board has eight symmetries (four rotations and four reflections: the dihedral group D4). Rather than
// searching all solutions and deduplicating afterwards, this solver partitions every valid board into two disjoint
// symmetry families and searches only one canonical representative per orbit:
//
//   1. Corner queen: at most one corner can hold a queen. Rotate it to (0, 0), which leaves only main-diagonal
//      reflection symmetry. Forbidding column 1 in rows 2..cols[1]-1 and checking cols <= transpose(cols) at the leaf
//      selects the unique canonical board of the orbit.
//   2. No corner queen: consider the eight distances from the four border queens to their adjacent corners. Rotate and
//      reflect so the minimum distance c0 sits at (0, c0) with 1 <= c0 <= (N - 2) / 2. Columns 0 and N - 1 are then
//      forbidden within distance < c0 of any corner, and row N - 1 is restricted to columns c0..N - 1 - c0.
//
// The search itself uses three bitmasks (columns, down-right diagonals, down-left diagonals), unrolls the last two
// rows to avoid two levels of recursion, and buffers compact fundamental solutions on the stack before reserving the
// exact output vector size and expanding each orbit into all distinct D4 images.
#include <cstdint>
#include <string>
#include <vector>

#include "nqueens.h"

namespace {  // names in here belong to this file only

constexpr int kMaxN = 16;

// One canonical representative of a D4 orbit, together with a bitmask of its distinct transforms.
struct Fundamental {
  uint8_t cols[kMaxN];
  uint8_t mask;  // bit k set iff D4 transform k is distinct from earlier transforms 0..k-1
};

// Writes D4 transform `k` (0..7) of `src` (size n) into `dst`.
// 0: identity, 1: mirror L/R, 2: mirror T/B, 3: rot180, 4: transpose, 5: rot90, 6: rot270, 7: anti-transpose.
inline void applyD4(int k, const uint8_t* src, uint8_t* dst, int n) {
  const int m = n - 1;
  switch (k) {
    case 0:
      for (int r = 0; r < n; ++r) dst[r] = src[r];
      break;
    case 1:
      for (int r = 0; r < n; ++r) dst[r] = static_cast<uint8_t>(m - src[r]);
      break;
    case 2:
      for (int r = 0; r < n; ++r) dst[m - r] = src[r];
      break;
    case 3:
      for (int r = 0; r < n; ++r) dst[m - r] = static_cast<uint8_t>(m - src[r]);
      break;
    case 4:
      for (int r = 0; r < n; ++r) dst[src[r]] = static_cast<uint8_t>(r);
      break;
    case 5:
      for (int r = 0; r < n; ++r) dst[src[r]] = static_cast<uint8_t>(m - r);
      break;
    case 6:
      for (int r = 0; r < n; ++r) dst[m - src[r]] = static_cast<uint8_t>(r);
      break;
    default:
      for (int r = 0; r < n; ++r) dst[m - src[r]] = static_cast<uint8_t>(m - r);
      break;
  }
}

inline int cmpBoard(const uint8_t* a, const uint8_t* b, int n) {
  for (int r = 0; r < n; ++r) {
    if (a[r] != b[r]) return a[r] < b[r] ? -1 : 1;
  }
  return 0;
}

struct NormalSearch {
  int n = 0;
  int m = 0;
  uint32_t full = 0;
  uint32_t rowMask[kMaxN]{};
  uint8_t cols[kMaxN]{};

  // Up to 2048 fundamentals stay on the stack; larger N spills to heapBuf.
  static constexpr int kStackCap = 2048;
  Fundamental stackBuf[kStackCap];
  int stackCount = 0;
  std::vector<Fundamental> heapBuf;
  size_t totalSolutions = 0;

  void addFundamental(uint8_t mask, int orbitSize) {
    Fundamental f;
    for (int r = 0; r < n; ++r) f.cols[r] = cols[r];
    f.mask = mask;
    if (stackCount < kStackCap) {
      stackBuf[stackCount++] = f;
    } else {
      heapBuf.push_back(f);
    }
    totalSolutions += static_cast<size_t>(orbitSize);
  }

  // Checks main-diagonal reflection symmetry for a corner-queen leaf with cols[1] == c1.
  void onCornerLeaf(int c1) {
    // Column 1 was forbidden in rows 2..c1-1, so if cols[c1] != 1 then transpose(cols)[1] > c1.
    if (cols[c1] != 1) {
      addFundamental(0xFFu, 8);
      return;
    }
    uint8_t inv[kMaxN];
    for (int r = 0; r < n; ++r) inv[cols[r]] = static_cast<uint8_t>(r);
    const int c = cmpBoard(cols, inv, n);
    if (c > 0) return;
    if (c == 0) {
      // Self-transpose corner solution: orbit consists of the 4 rotations (k = 0, 3, 5, 6).
      addFundamental(0x69u, 4);
    } else {
      addFundamental(0xFFu, 8);
    }
  }

  // Checks canonicality and orbit size for a non-corner leaf with cols[0] == c0.
  void onInteriorLeaf(int c0) {
    // Fast path: if no other border queen ties corner distance c0, the orbit has size 8 and this board is canonical.
    const bool tied = (cols[m] == c0 || cols[m] == m - c0 ||
                       cols[c0] == 0 || cols[c0] == m ||
                       cols[m - c0] == 0 || cols[m - c0] == m);
    if (!tied) {
      addFundamental(0xFFu, 8);
      return;
    }
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
        if (((mask >> j) & 1u) && cmpBoard(imgs[k], imgs[j], n) == 0) {
          dup = true;
          break;
        }
      }
      if (!dup) {
        mask |= static_cast<uint8_t>(1u << k);
        ++orbitSize;
      }
    }
    addFundamental(mask, orbitSize);
  }

  // Row-by-row bitmask DFS with last-two-rows unrolling.
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
          if constexpr (Corner) {
            onCornerLeaf(keyCol);
          } else {
            onInteriorLeaf(keyCol);
          }
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

  void run(int size) {
    n = size;
    m = size - 1;
    full = (1u << n) - 1u;

    // Family 1: Corner queen at (0, 0).
    cols[0] = 0;
    for (int c1 = 2; c1 < n; ++c1) {
      cols[1] = static_cast<uint8_t>(c1);
      for (int r = 2; r < n; ++r) {
        rowMask[r] = (r < c1) ? (full & ~2u) : full;
      }
      const uint32_t b0 = 1u;
      const uint32_t b1 = 1u << c1;
      dfs<true>(2, b0 | b1, ((b0 << 1) | b1) << 1, ((b0 >> 1) | b1) >> 1, c1);
    }

    // Family 2: No corner queen; minimum border distance c0 sits at (0, c0).
    const uint32_t noSides = full & ~(1u | (1u << m));
    const int maxC0 = (n - 2) / 2;
    for (int c0 = 1; c0 <= maxC0; ++c0) {
      cols[0] = static_cast<uint8_t>(c0);
      for (int r = 1; r < n - 1; ++r) {
        rowMask[r] = (r < c0 || r >= n - c0) ? noSides : full;
      }
      rowMask[n - 1] = ((1u << (n - 2 * c0)) - 1u) << c0;
      const uint32_t b0 = 1u << c0;
      dfs<false>(1, b0, b0 << 1, b0 >> 1, c0);
    }
  }

  // Expands all buffered canonical fundamentals into the final solution list with exact capacity.
  std::vector<std::vector<int>> materialize() const {
    std::vector<std::vector<int>> solutions;
    solutions.reserve(totalSolutions);
    const bool debug = snapshotsEnabled();

    auto emit = [&](const Fundamental& f) {
      const uint8_t* src = f.cols;
      int buf[kMaxN];
      if (f.mask == 0xFFu) {
        for (int r = 0; r < n; ++r) buf[r] = src[r];
        solutions.emplace_back(buf, buf + n);
        if (__builtin_expect(debug, 0)) snapshot(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));

        for (int r = 0; r < n; ++r) buf[r] = m - src[r];
        solutions.emplace_back(buf, buf + n);
        if (__builtin_expect(debug, 0)) snapshot(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));

        for (int r = 0; r < n; ++r) buf[m - r] = src[r];
        solutions.emplace_back(buf, buf + n);
        if (__builtin_expect(debug, 0)) snapshot(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));

        for (int r = 0; r < n; ++r) buf[m - r] = m - src[r];
        solutions.emplace_back(buf, buf + n);
        if (__builtin_expect(debug, 0)) snapshot(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));

        for (int r = 0; r < n; ++r) buf[src[r]] = r;
        solutions.emplace_back(buf, buf + n);
        if (__builtin_expect(debug, 0)) snapshot(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));

        for (int r = 0; r < n; ++r) buf[src[r]] = m - r;
        solutions.emplace_back(buf, buf + n);
        if (__builtin_expect(debug, 0)) snapshot(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));

        for (int r = 0; r < n; ++r) buf[m - src[r]] = r;
        solutions.emplace_back(buf, buf + n);
        if (__builtin_expect(debug, 0)) snapshot(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));

        for (int r = 0; r < n; ++r) buf[m - src[r]] = m - r;
        solutions.emplace_back(buf, buf + n);
        if (__builtin_expect(debug, 0)) snapshot(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));
      } else {
        uint8_t tmp[kMaxN];
        for (int k = 0; k < 8; ++k) {
          if (!((f.mask >> k) & 1u)) continue;
          applyD4(k, src, tmp, n);
          for (int r = 0; r < n; ++r) buf[r] = tmp[r];
          solutions.emplace_back(buf, buf + n);
          if (__builtin_expect(debug, 0)) {
            snapshot(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));
          }
        }
      }
    };

    for (int i = 0; i < stackCount; ++i) emit(stackBuf[i]);
    for (const auto& f : heapBuf) emit(f);
    return solutions;
  }
};

}  // namespace

std::vector<std::vector<int>> solveNQueens(int n) {
  if (n <= 0 || n > kMaxN) return {};
  if (n == 1) {
    std::vector<std::vector<int>> out = {{0}};
    NQ_SNAPSHOT(nq::queensOf(out[0]), "solution 1");
    return out;
  }
  if (n < 4) return {};

  NormalSearch search;
  search.run(n);
  return search.materialize();
}

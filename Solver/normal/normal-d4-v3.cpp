// High-speed, minimal-heap Normal N-Queens solver (N <= 12 via 64-bit SWAR AlgX
// inside D4, fallback 13..16).
// - 0 B .data/.bss, 0 B auxiliary search heap for N <= 12, exact
// solutions.reserve() + direct SpecIter emission.
// - Single noinline stack frame (~20.5 KB) safely inside Emscripten's 64 KB
// stack limit; 100% runtime search.
#if __cplusplus >= 202002L
#include <bit>
#endif
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <vector>

#include "nqueens.h"

namespace {

__attribute__((always_inline)) inline int popcnt32(uint32_t x) noexcept {
#if __cplusplus >= 202002L
  return std::popcount(x);
#else
  return __builtin_popcount(x);
#endif
}

__attribute__((always_inline)) inline int ctz32(uint32_t b) noexcept {
#if __cplusplus >= 202002L
  return std::countr_zero(b);
#else
  return __builtin_ctz(b);
#endif
}

__attribute__((always_inline)) inline int ctz64(uint64_t x) noexcept {
#if __cplusplus >= 202002L
  return std::countr_zero(x);
#else
  return __builtin_ctzll(x);
#endif
}

// Materialize 2/4/8 D4 symmetries using direct pointer memcpy +
// std::reverse_iterator (zero custom iterators).
inline void emitOrbit(std::vector<std::vector<int>> &out, uint64_t packed,
                      int orb, int n) {
  const int m = n - 1;
  int q[16], qf[16], inv[16], invf[16];
  for (int r = 0; r < n; ++r) {
    const int c = static_cast<int>(packed & 0xFu);
    packed >>= 4;
    q[r] = c;
    qf[r] = m - c;
    if (orb >= 4) {
      inv[c] = r;
      invf[c] = m - r;
    }
  }
  out.emplace_back(q, q + n);
  out.emplace_back(qf, qf + n);
  if (orb >= 4) {
    out.emplace_back(inv, inv + n);
    out.emplace_back(invf, invf + n);
    if (orb == 8) {
      out.emplace_back(std::make_reverse_iterator(q + n),
                       std::make_reverse_iterator(q));
      out.emplace_back(std::make_reverse_iterator(qf + n),
                       std::make_reverse_iterator(qf));
      out.emplace_back(std::make_reverse_iterator(inv + n),
                       std::make_reverse_iterator(inv));
      out.emplace_back(std::make_reverse_iterator(invf + n),
                       std::make_reverse_iterator(invf));
    }
  }
}

struct SwarNormalD4 {
  static constexpr int kMaxN = 12;
  static constexpr uint64_t kOnes = 0x0001000100010001ULL;
  static constexpr uint64_t k7FFF = 0x7FFF7FFF7FFF7FFFULL;
  static constexpr uint64_t kHigh = 0x8000800080008000ULL;
  static constexpr uint64_t kData = 0x0FFF0FFF0FFF0FFFULL;
  static constexpr uint64_t kSentWord = 0x7000700070007000ULL;
  static constexpr uint64_t kColPack = 0x0001000200040008ULL;

  struct CellAtk {
    uint64_t m0, m1, m2;
  };

  int n = 0, m = 0, cur_k = 0;
  uint32_t full = 0, centralCols = 0;
  uint8_t centerDist[kMaxN]{};
  uint64_t rowSent[kMaxN][3]{};
  CellAtk atk[kMaxN][kMaxN];

  uint64_t buf8[1856];
  uint64_t buf4[48];
  uint64_t buf2[16];
  int n8 = 0, n4 = 0, n2 = 0;

  void buildTables() {
    centralCols = 0;
    for (int i = 0; i < n; ++i) {
      const int ad = (2 * i >= m) ? (2 * i - m) : (m - 2 * i);
      centerDist[i] = static_cast<uint8_t>(ad);
      if (ad <= 3)
        centralCols |= (1u << i);
      for (int w = 0; w < 3; ++w) {
        rowSent[i][w] = ((i >> 2) == w) ? (0x7000ULL << ((i & 3) << 4)) : 0ULL;
      }
    }
    for (int r = 0; r < n; ++r) {
      const uint64_t rClear = ~(0xFFFFULL << ((r & 3) << 4));
      for (int c = 0; c < n; ++c) {
        const uint64_t colKeep = ~(static_cast<uint64_t>(1u << c) * kOnes);
        uint64_t w[3] = {colKeep, colKeep, colKeep};
        w[r >> 2] &= rClear;
        for (int dir = -1; dir <= 1; dir += 2) {
          for (int r2 = r + dir, cl = c - 1, cr = c + 1; r2 >= 0 && r2 < n;
               r2 += dir, --cl, ++cr) {
            const uint32_t diag =
                (cl >= 0 ? (1u << cl) : 0u) | (cr < n ? (1u << cr) : 0u);
            if (!diag)
              break;
            w[r2 >> 2] &= ~(static_cast<uint64_t>(diag) << ((r2 & 3) << 4));
          }
        }
        atk[r][c] = {w[0], w[1], w[2]};
      }
    }
  }

  __attribute__((always_inline)) inline void
  place(int r, int c, uint64_t &d0, uint64_t &d1, uint64_t &d2) const {
    const CellAtk &a = atk[r][c];
    d0 = (d0 & a.m0) | rowSent[r][0];
    d1 = (d1 & a.m1) | rowSent[r][1];
    d2 = (d2 & a.m2) | rowSent[r][2];
  }

  __attribute__((always_inline)) inline void onLeaf(uint64_t packed) {
    if (cur_k == 0) {
      buf8[n8++] = packed;
      return;
    }
    const int k = cur_k, mk = m - k;
    const int qM = static_cast<int>((packed >> (m << 2)) & 0xFu);
    const int qK = static_cast<int>((packed >> (k << 2)) & 0xFu);
    const int qMK = static_cast<int>((packed >> (mk << 2)) & 0xFu);
    const bool t180 = (qM == mk), tD1 = (qK == 0), tR90 = (qMK == 0),
               tR270 = (qK == m), tD2 = (qMK == m);
    if (__builtin_expect(!(t180 | tD1 | tR90 | tR270 | tD2), 1)) {
      buf8[n8++] = packed;
      return;
    }
    int q[kMaxN];
    for (int r = 0; r < n; ++r)
      q[r] = static_cast<int>((packed >> (r << 2)) & 0xFu);
    auto cmp = [&](auto &&fn) {
      for (int r = 1; r <= m; ++r) {
        const int t = fn(r);
        if (t != q[r])
          return t < q[r] ? -1 : 1;
      }
      return 0;
    };
    bool sym180 = false, sym90 = false;
    if (t180) {
      const int c = cmp([&](int r) { return m - q[m - r]; });
      if (c < 0)
        return;
      sym180 = (c == 0);
    }
    if (tD1 | tR90 | tR270 | tD2) {
      int inv[kMaxN];
      for (int r = 0; r < n; ++r)
        inv[q[r]] = r;
      if (tD1 && cmp([&](int r) { return inv[r]; }) < 0)
        return;
      if (tR90) {
        const int c = cmp([&](int r) { return m - inv[r]; });
        if (c < 0)
          return;
        if (c == 0)
          sym90 = true;
      }
      if (tR270) {
        const int c = cmp([&](int r) { return inv[m - r]; });
        if (c < 0)
          return;
        if (c == 0)
          sym90 = true;
      }
      if (tD2 && cmp([&](int r) { return m - inv[m - r]; }) < 0)
        return;
    }
    if (sym90)
      buf2[n2++] = packed;
    else if (sym180)
      buf4[n4++] = packed;
    else
      buf8[n8++] = packed;
  }

  void dfs(int rem, uint32_t rowMask, uint32_t colMask, uint64_t d0,
           uint64_t d1, uint64_t d2, uint64_t packed) {
    for (;;) {
      if ((~(d0 + k7FFF) | ~(d1 + k7FFF) | ~(d2 + k7FFF)) & kHigh)
        return;

      if (rem == 2) {
        const uint32_t fr = full ^ rowMask, rb0 = fr & (~fr + 1u);
        const int r0 = ctz32(rb0), r1 = ctz32(fr ^ rb0);
        const uint32_t fc = full ^ colMask, cb0 = fc & (~fc + 1u),
                       cb1 = fc ^ cb0;
        const int c0 = ctz32(cb0), c1 = ctz32(cb1);
        if (r1 - r0 != c1 - c0) {
          const uint32_t av0 = static_cast<uint32_t>(
              ((r0 < 4 ? d0 : (r0 < 8 ? d1 : d2)) >> ((r0 & 3) << 4)) & 0xFFFu);
          const uint32_t av1 = static_cast<uint32_t>(
              ((r1 < 4 ? d0 : (r1 < 8 ? d1 : d2)) >> ((r1 & 3) << 4)) & 0xFFFu);
          if ((av0 & cb0) && (av1 & cb1))
            onLeaf(packed | (static_cast<uint64_t>(c0) << (r0 << 2)) |
                   (static_cast<uint64_t>(c1) << (r1 << 2)));
          if ((av0 & cb1) && (av1 & cb0))
            onLeaf(packed | (static_cast<uint64_t>(c1) << (r0 << 2)) |
                   (static_cast<uint64_t>(c0) << (r1 << 2)));
        }
        return;
      }

      const uint64_t y0 = d0 & (d0 - kOnes), y1 = d1 & (d1 - kOnes),
                     y2 = d2 & (d2 - kOnes);
      const uint64_t o0 = ~(y0 + k7FFF) & kHigh, o1 = ~(y1 + k7FFF) & kHigh,
                     o2 = ~(y2 + k7FFF) & kHigh;
      if (o0 | o1 | o2) {
        const uint64_t ow = o1 ? o1 : (o0 ? o0 : o2);
        const uint64_t dw = o1 ? d1 : (o0 ? d0 : d2);
        const int l = ctz64(ow) >> 4, r = (o1 ? 4 : (o0 ? 0 : 8)) + l;
        const uint32_t cb = static_cast<uint32_t>((dw >> (l << 4)) & 0xFFFu);
        const int c = ctz32(cb);
        --rem;
        rowMask |= (1u << r);
        colMask |= cb;
        place(r, c, d0, d1, d2);
        packed |= static_cast<uint64_t>(c) << (r << 2);
        continue;
      }

      const uint64_t m0 = d0 & kData, m1 = d1 & kData, m2 = d2 & kData;
      const uint64_t o01 = m0 | m1, t01 = m0 & m1;
      const uint64_t once4 = o01 | m2, twice4 = t01 | (o01 & m2);
      const uint32_t oA = static_cast<uint32_t>(once4),
                     oB = static_cast<uint32_t>(once4 >> 32);
      const uint32_t tA = static_cast<uint32_t>(twice4),
                     tB = static_cast<uint32_t>(twice4 >> 32);
      const uint32_t once2 = oA | oB, twice2 = tA | tB | (oA & oB);
      const uint32_t onceLo = once2 & 0xFFFu, onceHi = once2 >> 16,
                     once = onceLo | onceHi;
      if ((once | colMask) != full)
        return;

      const uint32_t twiceLo = twice2 & 0xFFFu, twiceHi = twice2 >> 16;
      const uint32_t twice = twiceLo | twiceHi | (onceLo & onceHi);
      if (const uint32_t uniqueCols = once & ~twice) {
        const uint32_t cb = uniqueCols & (~uniqueCols + 1u);
        const int c = ctz32(cb);
        const uint64_t cm = static_cast<uint64_t>(cb) * kOnes;
        const uint64_t w1 = d1 & cm, w0 = d0 & cm;
        const int r =
            w1 ? (4 + (ctz64(w1) >> 4))
               : (w0 ? (ctz64(w0) >> 4) : (8 + (ctz64(d2 & cm) >> 4)));
        --rem;
        rowMask |= (1u << r);
        colMask |= cb;
        place(r, c, d0, d1, d2);
        packed |= static_cast<uint64_t>(c) << (r << 2);
        continue;
      }

      auto branchRow = [&](int r, uint32_t av) {
        const uint32_t cb0 = av & (~av + 1u), cb1 = av ^ cb0;
        const int c0 = ctz32(cb0), c1 = ctz32(cb1);
        const uint32_t nRowMask = rowMask | (1u << r);
        uint64_t nd0 = d0, nd1 = d1, nd2 = d2;
        place(r, c0, nd0, nd1, nd2);
        dfs(rem - 1, nRowMask, colMask | cb0, nd0, nd1, nd2,
            packed | (static_cast<uint64_t>(c0) << (r << 2)));
        --rem;
        rowMask = nRowMask;
        colMask |= cb1;
        place(r, c1, d0, d1, d2);
        packed |= static_cast<uint64_t>(c1) << (r << 2);
      };

      auto branchColMask = [&](uint32_t cm) {
        int bestC = -1, bestD = 99;
        while (cm) {
          const uint32_t cb = cm & (~cm + 1u);
          cm ^= cb;
          const int c = ctz32(cb);
          if (centerDist[c] < bestD) {
            bestD = centerDist[c];
            bestC = c;
          }
        }
        const uint32_t cb = 1u << bestC, nColMask = colMask | cb;
        const uint64_t v = ((d0 >> bestC) & kOnes) |
                           (((d1 >> bestC) & kOnes) << 4) |
                           (((d2 >> bestC) & kOnes) << 8);
        const uint32_t rmask = static_cast<uint32_t>((v * kColPack) >> 48);
        const uint32_t rb0 = rmask & (~rmask + 1u), rb1 = rmask ^ rb0;
        const int r0 = ctz32(rb0), r1 = ctz32(rb1);
        uint64_t nd0 = d0, nd1 = d1, nd2 = d2;
        place(r0, bestC, nd0, nd1, nd2);
        dfs(rem - 1, rowMask | rb0, nColMask, nd0, nd1, nd2,
            packed | (static_cast<uint64_t>(bestC) << (r0 << 2)));
        --rem;
        rowMask |= rb1;
        colMask = nColMask;
        place(r1, bestC, d0, d1, d2);
        packed |= static_cast<uint64_t>(bestC) << (r1 << 2);
      };

      if (const uint64_t tw1 = ~((y1 & (y1 - kOnes)) + k7FFF) & kHigh) {
        const int r = (tw1 & 0x0000800000000000ULL)   ? 6
                      : (tw1 & 0x0000000080000000ULL) ? 5
                      : (tw1 & 0x8000000000000000ULL) ? 7
                                                      : 4;
        branchRow(r, static_cast<uint32_t>((d1 >> ((r & 3) << 4)) & 0xFFFu));
        continue;
      }

      const uint64_t thrice4 = t01 & m2;
      const uint32_t hA = static_cast<uint32_t>(thrice4),
                     hB = static_cast<uint32_t>(thrice4 >> 32);
      const uint32_t thrice2 = (hA | hB) | (tA & oB) | (oA & tB);
      const uint32_t thrice = (thrice2 & 0xFFFu) | (thrice2 >> 16) |
                              (twiceLo & onceHi) | (onceLo & twiceHi);
      const uint32_t c2 = twice & ~thrice;
      if (const uint32_t c2Cent = c2 & centralCols) {
        branchColMask(c2Cent);
        continue;
      }

      const uint64_t tw0 = ~((y0 & (y0 - kOnes)) + k7FFF) & kHigh;
      const uint64_t tw2 = ~((y2 & (y2 - kOnes)) + k7FFF) & kHigh;
      if (tw0 | tw2) {
        const int r = tw0 ? ((tw0 & 0x8000000000000000ULL)   ? 3
                             : (tw0 & 0x0000800000000000ULL) ? 2
                             : (tw0 & 0x0000000080000000ULL) ? 1
                                                             : 0)
                          : ((tw2 & 0x0000000000008000ULL)   ? 8
                             : (tw2 & 0x0000000080000000ULL) ? 9
                             : (tw2 & 0x0000800000000000ULL) ? 10
                                                             : 11);
        branchRow(r, static_cast<uint32_t>(((tw0 ? d0 : d2) >> ((r & 3) << 4)) &
                                           0xFFFu));
        continue;
      }
      if (c2) {
        branchColMask(c2);
        continue;
      }

      int bestR = -1, bestKey = 1000;
      uint32_t bestAv = 0, fr = full ^ rowMask;
      while (fr) {
        const uint32_t rb = fr & (~fr + 1u);
        fr ^= rb;
        const int r = ctz32(rb);
        const uint32_t av = static_cast<uint32_t>(
            ((r < 4 ? d0 : (r < 8 ? d1 : d2)) >> ((r & 3) << 4)) & 0xFFFu);
        const int key = (popcnt32(av) << 4) | centerDist[r];
        if (key < bestKey) {
          bestKey = key;
          bestR = r;
          bestAv = av;
        }
      }
      const uint32_t nRowMask = rowMask | (1u << bestR);
      uint32_t av = bestAv;
      while (av) {
        const uint32_t cb = av & (~av + 1u);
        av ^= cb;
        const int c = ctz32(cb);
        if (!av) {
          --rem;
          rowMask = nRowMask;
          colMask |= cb;
          place(bestR, c, d0, d1, d2);
          packed |= static_cast<uint64_t>(c) << (bestR << 2);
          break;
        }
        uint64_t nd0 = d0, nd1 = d1, nd2 = d2;
        place(bestR, c, nd0, nd1, nd2);
        dfs(rem - 1, nRowMask, colMask | cb, nd0, nd1, nd2,
            packed | (static_cast<uint64_t>(c) << (bestR << 2)));
      }
    }
  }

  inline void packRows(const uint32_t *rm, uint64_t &d0, uint64_t &d1,
                       uint64_t &d2) const {
    d0 = d1 = d2 = kSentWord;
    for (int r = 0; r < n; ++r) {
      const int sh = (r & 3) << 4;
      uint64_t &dw = (r < 4) ? d0 : (r < 8 ? d1 : d2);
      dw = (dw & ~(0xFFFFULL << sh)) | (static_cast<uint64_t>(rm[r]) << sh);
    }
  }

  std::vector<std::vector<int>> run(int board_n) {
    n = board_n;
    m = board_n - 1;
    full = (1u << n) - 1u;
    buildTables();
    uint32_t rm[kMaxN];

    cur_k = 0;
    for (int c1 = 2; c1 <= n - 2; ++c1) {
      const bool last = (n > 4 && c1 == n - 2);
      for (int r = 0; r < n; ++r)
        rm[r] = (r >= 2 && r < c1) ? (full & ~2u) : full;
      if (last)
        rm[m] = 2u;
      uint64_t d0, d1, d2;
      packRows(rm, d0, d1, d2);
      place(0, 0, d0, d1, d2);
      place(1, c1, d0, d1, d2);
      if (last) {
        place(m, 1, d0, d1, d2);
        dfs(n - 3, 3u | (1u << m), 3u | (1u << c1), d0, d1, d2,
            (static_cast<uint64_t>(c1) << 4) | (1ULL << (m << 2)));
      } else {
        dfs(n - 2, 3u, 1u | (1u << c1), d0, d1, d2,
            static_cast<uint64_t>(c1) << 4);
      }
    }

    const uint32_t noSides = full & ~(1u | (1u << m));
    cur_k = 1;
    for (int c1 = 3; c1 <= m; ++c1) {
      rm[0] = full;
      for (int r = 1; r < m; ++r)
        rm[r] = full;
      rm[m] = (c1 == m) ? (1u << (m - 1)) : noSides;
      uint64_t d0, d1, d2;
      packRows(rm, d0, d1, d2);
      place(0, 1, d0, d1, d2);
      place(1, c1, d0, d1, d2);
      dfs(n - 2, 3u, 2u | (1u << c1), d0, d1, d2,
          1ULL | (static_cast<uint64_t>(c1) << 4));
    }

    for (int c0 = 2; c0 <= (n - 2) / 2; ++c0) {
      cur_k = c0;
      rm[0] = full;
      for (int r = 1; r < m; ++r)
        rm[r] = (r < c0 || r >= n - c0) ? noSides : full;
      rm[m] = ((1u << (n - 2 * c0)) - 1u) << c0;
      uint64_t d0, d1, d2;
      packRows(rm, d0, d1, d2);
      place(0, c0, d0, d1, d2);
      dfs(n - 1, 1u, 1u << c0, d0, d1, d2, static_cast<uint64_t>(c0));
    }

    std::vector<std::vector<int>> solutions;
    solutions.reserve(static_cast<std::size_t>(n8) * 8u +
                      static_cast<std::size_t>(n4) * 4u +
                      static_cast<std::size_t>(n2) * 2u);
    for (int i = 0; i < n8; ++i)
      emitOrbit(solutions, buf8[i], 8, n);
    for (int i = 0; i < n4; ++i)
      emitOrbit(solutions, buf4[i], 4, n);
    for (int i = 0; i < n2; ++i)
      emitOrbit(solutions, buf2[i], 2, n);
    return solutions;
  }
};

void solveFallback(int row, int n, uint32_t mask, uint32_t cols, uint32_t ld,
                   uint32_t rd, int *cur, std::vector<std::vector<int>> &out) {
  if (row == n) {
    out.emplace_back(cur, cur + n);
    return;
  }
  uint32_t avail = mask & ~(cols | ld | rd);
  while (avail) {
    const uint32_t bit = avail & (0u - avail);
    avail ^= bit;
    cur[row] = ctz32(bit);
    solveFallback(row + 1, n, mask, cols | bit, (ld | bit) << 1,
                  (rd | bit) >> 1, cur, out);
  }
}

__attribute__((noinline)) std::vector<std::vector<int>> solveSwar(int n) {
  SwarNormalD4 solver;
  return solver.run(n);
}

} // namespace

std::vector<std::vector<int>> solveNQueens(int n) {
  if (n <= 0 || n > 16)
    return {};
  if (n == 1)
    return {{0}};
  if (n < 4)
    return {};
  if (n <= 12)
    return solveSwar(n);
  std::vector<std::vector<int>> out;
  int cur[16];
  solveFallback(0, n, (1u << n) - 1u, 0u, 0u, 0u, cur, out);
  return out;
}

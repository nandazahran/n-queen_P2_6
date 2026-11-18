// Solver for the Walled case: branch and bound for the largest number of queens, walls stopping the attacks.
//
// ---- The idea ------------------------------------------------------------------------------------------------------
// A wall stops an attack, so on a walled board a row or a column can hold more than one queen: all that matters is that
// no two queens see each other. Between two walls a row (or a column) is one uninterrupted run of cells, and two queens
// inside one run always see each other. So a run holds at most one queen, and that is the bound this solver prunes with.
//
//   rowBoundSuffix[r]  how many runs rows r..N-1 have, so at most that many queens are still possible below.
//   colBound(row)      how many column runs reaching row or lower are still empty.
//
// Both are upper bounds on what is left. A branch is dropped only when `count + bound` is strictly below the best board
// found so far: an equal branch still has to be explored, because the answer is EVERY board of the maximum size.
//
// The search walks the rows in order. In a row it walks the runs left to right and either skips a run or puts one queen
// in it, which counts each board exactly once. Attacks are tested with a bitset per cell that already lists every cell
// it can see, precomputed once with the walls taken into account.
#include <array>
#include <cstdint>
#include <cstdlib>  // std::abs
#include <string>
#include <utility>
#include <vector>

#include "nqueens.h"

namespace {  // names in here belong to this file only

using Board = std::vector<std::pair<int, int>>;   // the queens of one board, in the order they were placed

// True when a wall stands strictly between the two cells. They must share a row, a column or a diagonal.
bool wallBetween(const std::vector<std::string>& grid, int r1, int c1, int r2, int c2) {
  const int dr = (r2 > r1) - (r2 < r1);
  const int dc = (c2 > c1) - (c2 < c1);
  for (int r = r1 + dr, c = c1 + dc; r != r2 || c != c2; r += dr, c += dc)
    if (grid[r][c] == 'W') return true;
  return false;
}

struct WalledSearch {
  int n = 0;
  std::vector<std::vector<std::pair<int, int>>> rowSegments;  // per row, the [start, end] column runs without a wall

  struct ColSeg {
    int c, r1, r2;  // the run of column c from row r1 to row r2
  };
  std::vector<ColSeg> colSegs;
  std::vector<std::vector<int>> colSegIndex;  // [r][c] = index into colSegs, -1 on a wall
  std::vector<char> colSegUsed;

  std::vector<int> rowBoundSuffix;                     // rowBoundSuffix[r] = runs in rows r..N-1
  std::vector<std::array<uint64_t, 3>> attackMask;      // per cell, the cells it can see (n * n bits)
  std::array<uint64_t, 3> occupied{};

  Board queens;
  std::vector<Board> best;
  int bestSize = 0;

  WalledSearch(int size, const std::vector<std::string>& grid) : n(size) {
    buildRowSegments(grid);
    buildColSegments(grid);
    rowBoundSuffix.assign(static_cast<size_t>(n) + 1, 0);
    for (int r = n - 1; r >= 0; --r)
      rowBoundSuffix[r] = rowBoundSuffix[r + 1] + static_cast<int>(rowSegments[r].size());
    buildAttackMasks(grid);
  }

  std::vector<Board> run() {
    dfs(0, 0);
    return std::move(best);
  }

 private:
  void buildRowSegments(const std::vector<std::string>& grid) {
    rowSegments.assign(static_cast<size_t>(n), {});
    for (int r = 0; r < n; ++r) {
      int start = -1;
      for (int c = 0; c < n; ++c) {
        if (grid[r][c] != 'W') {
          if (start < 0) start = c;
        } else if (start >= 0) {
          rowSegments[r].emplace_back(start, c - 1);
          start = -1;
        }
      }
      if (start >= 0) rowSegments[r].emplace_back(start, n - 1);
    }
  }

  void buildColSegments(const std::vector<std::string>& grid) {
    colSegIndex.assign(static_cast<size_t>(n), std::vector<int>(static_cast<size_t>(n), -1));
    for (int c = 0; c < n; ++c) {
      int start = -1;
      auto close = [&](int r1, int r2) {
        const int id = static_cast<int>(colSegs.size());
        colSegs.push_back({c, r1, r2});
        for (int r = r1; r <= r2; ++r) colSegIndex[r][c] = id;
      };
      for (int r = 0; r < n; ++r) {
        if (grid[r][c] != 'W') {
          if (start < 0) start = r;
        } else if (start >= 0) {
          close(start, r - 1);
          start = -1;
        }
      }
      if (start >= 0) close(start, n - 1);
    }
    colSegUsed.assign(colSegs.size(), 0);
  }

  // For every free cell, the bits of the cells a queen there would attack: same row, column or diagonal, with no wall
  // in between.
  void buildAttackMasks(const std::vector<std::string>& grid) {
    attackMask.assign(static_cast<size_t>(n) * static_cast<size_t>(n), {0, 0, 0});
    for (int r1 = 0; r1 < n; ++r1) {
      for (int c1 = 0; c1 < n; ++c1) {
        if (grid[r1][c1] == 'W') continue;
        auto& mask = attackMask[static_cast<size_t>(r1) * n + c1];
        for (int r2 = 0; r2 < n; ++r2) {
          for (int c2 = 0; c2 < n; ++c2) {
            if ((r1 == r2 && c1 == c2) || grid[r2][c2] == 'W') continue;
            const bool sharesLine = r1 == r2 || c1 == c2 || std::abs(r1 - r2) == std::abs(c1 - c2);
            if (!sharesLine || wallBetween(grid, r1, c1, r2, c2)) continue;
            const int idx = r2 * n + c2;
            mask[static_cast<size_t>(idx) / 64] |= 1ull << (idx % 64);
          }
        }
      }
    }
  }

  bool attacked(int r, int c) const {
    const auto& mask = attackMask[static_cast<size_t>(r) * n + c];
    return (occupied[0] & mask[0]) || (occupied[1] & mask[1]) || (occupied[2] & mask[2]);
  }

  void place(int r, int c) {
    queens.emplace_back(r, c);
    const int idx = r * n + c;
    occupied[static_cast<size_t>(idx) / 64] |= 1ull << (idx % 64);
    colSegUsed[static_cast<size_t>(colSegIndex[r][c])] = 1;
  }

  void unplace() {
    const auto queen = queens.back();
    const int idx = queen.first * n + queen.second;
    occupied[static_cast<size_t>(idx) / 64] &= ~(1ull << (idx % 64));
    colSegUsed[static_cast<size_t>(colSegIndex[queen.first][queen.second])] = 0;
    queens.pop_back();
  }

  // Column runs that reach this row or lower and hold no queen yet: at most one queen each is still possible.
  int colBound(int row) const {
    int count = 0;
    for (size_t i = 0; i < colSegs.size(); ++i)
      if (!colSegUsed[i] && colSegs[i].r2 >= row) ++count;
    return count;
  }

  void record() {
    const int size = static_cast<int>(queens.size());
    if (size > bestSize) {
      bestSize = size;
      best.clear();
      best.push_back(queens);
      NQ_SNAPSHOT(queens, "new record: " + std::to_string(bestSize) + " queens");
    } else if (size == bestSize) {
      best.push_back(queens);
      NQ_SNAPSHOT(queens, "another board with " + std::to_string(bestSize) + " queens");
    }
  }

  // Skip or fill each run of this row, left to right. One queen per run at most, so every board is built once.
  void chooseInRow(int row, int segIdx, int count) {
    const int remainingInRow = static_cast<int>(rowSegments[row].size()) - segIdx;
    if (count + remainingInRow + rowBoundSuffix[row + 1] < bestSize) return;  // too few rows left to catch up
    if (count + colBound(row) < bestSize) return;
    if (segIdx == static_cast<int>(rowSegments[row].size())) {
      dfs(row + 1, count);
      return;
    }
    chooseInRow(row, segIdx + 1, count);  // this run stays empty
    const auto segment = rowSegments[row][segIdx];
    for (int c = segment.first; c <= segment.second; ++c) {
      if (attacked(row, c)) continue;
      place(row, c);
      chooseInRow(row, segIdx + 1, count + 1);
      unplace();
    }
  }

  void dfs(int row, int count) {
    if (row == n) {
      record();
      return;
    }
    if (count + rowBoundSuffix[row] < bestSize) return;  // rows below cannot hold enough queens
    if (count + colBound(row) < bestSize) return;        // columns below cannot hold enough queens
    chooseInRow(row, 0, count);
  }
};

}  // namespace

std::vector<std::vector<std::pair<int, int>>> solveWalled(int n, const std::vector<std::string>& grid) {
  if (n <= 0 || static_cast<int>(grid.size()) != n) return {};
  for (const std::string& line : grid)
    if (static_cast<int>(line.size()) != n) return {};
  return WalledSearch(n, grid).run();
}

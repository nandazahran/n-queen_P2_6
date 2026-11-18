// Solver for the Normal, Pre-placed and Holes cases: backtracking with the taken cells kept in three bitmasks.
//
// ---- The idea ------------------------------------------------------------------------------------------------------
// Same row-by-row search as the plain backtracking solver, but there are no per-cell tables. One integer holds the
// columns that are taken, and two more hold the two diagonal directions. Walking one row down simply shifts the
// diagonals: a queen takes (row + k, column + k), so everything that blocked row + 1 is the column mask shifted left by
// one, and the other diagonal is shifted right by one.
//
// The free columns of a row are then one bitwise expression, and its set bits are walked with the lowest-bit trick:
// `avail & -avail` is the lowest set bit and `__builtin_ctz` gives its index. That removes the inner column loop.
#include <cstdlib>  // std::abs
#include <string>
#include <utility>
#include <vector>

#include "nqueens.h"

namespace {  // names in here belong to this file only

// A Debug run keeps only the first and the last snapshots, so a dead end is shown the first time and then every
// DEAD_END_EVERY-th time. Lower it to see more of them.
const long long DEAD_END_EVERY = 1000;

// Checks that the pre-placed queens fit an N x N board and do not attack each other.
// On success `fixed[r]` is the column of the pre-placed queen in row r, or -1 when row r is still free.
bool readPreplaced(int n, const std::vector<std::pair<int, int>>& preplaced, std::vector<int>& fixed) {
  fixed.assign(n, -1);
  for (const auto& queen : preplaced) {
    const int r = queen.first, c = queen.second;
    if (r < 0 || r >= n || c < 0 || c >= n) return false;  // off the board
    if (fixed[r] != -1) return false;                      // two queens in one row
    fixed[r] = c;
  }
  for (size_t i = 0; i < preplaced.size(); ++i) {
    for (size_t j = i + 1; j < preplaced.size(); ++j) {
      const int r1 = preplaced[i].first, c1 = preplaced[i].second;
      const int r2 = preplaced[j].first, c2 = preplaced[j].second;
      if (c1 == c2 || std::abs(c1 - c2) == std::abs(r1 - r2)) return false;  // share a column or a diagonal
    }
  }
  return true;
}

struct BitmaskSearch {
  int n = 0;
  int full = 0;                    // n columns set
  std::vector<int> cols;           // cols[r] = column of row r, -1 = not placed
  std::vector<int> holeMask;       // bit c set when the cell (r, c) is a hole
  std::vector<int> fixed;          // column of the pre-placed queen in row r, or -1
  std::vector<std::vector<int>> solutions;
  long long deadEnds = 0;          // only counted in a Debug run

  void run(const std::vector<int>& preplacedColumns) {
    cols.assign(n, -1);
    fixed = preplacedColumns;
    place(0, 0, 0, 0);
  }

  void deadEnd(int row) {
    // Written out as a plain snapshot() call so that a normal run does not even count the dead ends.
    if (++deadEnds == 1 || deadEnds % DEAD_END_EVERY == 0)
      snapshot(nq::queensOf(cols), "dead end at row " + std::to_string(row));
  }

  // `colMask` holds the taken columns, `d1` the taken down-right diagonals, `d2` the taken down-left diagonals, both
  // already shifted to this row.
  void place(int row, int colMask, int d1, int d2) {
    if (row == n) {
      solutions.push_back(cols);
      NQ_SNAPSHOT(nq::queensOf(cols), "solution " + std::to_string(solutions.size()));
      return;
    }
    if (fixed[row] >= 0) {
      // A row with a pre-placed queen has exactly one candidate column.
      const int bit = 1 << fixed[row];
      if ((colMask | d1 | d2) & bit) {
        if (snapshotsEnabled()) deadEnd(row);
        return;
      }
      cols[row] = fixed[row];
      place(row + 1, colMask | bit, (d1 | bit) << 1, (d2 | bit) >> 1);
      cols[row] = -1;
      return;
    }
    int avail = full & ~(colMask | d1 | d2) & ~holeMask[row];
    if (!avail) {
      if (snapshotsEnabled()) deadEnd(row);
      return;
    }
    while (avail) {
      const int bit = avail & -avail;
      const int c = __builtin_ctz(static_cast<unsigned>(bit));
      cols[row] = c;
      place(row + 1, colMask | bit, (d1 | bit) << 1, (d2 | bit) >> 1);
      cols[row] = -1;
      avail -= bit;
    }
  }
};

}  // namespace

std::vector<std::vector<int>> solveNQueens(int n) {
  BitmaskSearch search;
  search.n = n;
  search.full = (1 << n) - 1;
  search.holeMask.assign(static_cast<size_t>(n), 0);
  search.run(std::vector<int>(static_cast<size_t>(n), -1));
  return search.solutions;
}

std::vector<std::vector<int>> solvePreplaced(int n, const std::vector<std::pair<int, int>>& preplaced) {
  std::vector<int> fixed;
  if (!readPreplaced(n, preplaced, fixed)) return {};

  BitmaskSearch search;
  search.n = n;
  search.full = (1 << n) - 1;
  search.holeMask.assign(static_cast<size_t>(n), 0);
  search.run(fixed);
  return search.solutions;
}

std::vector<std::vector<int>> solveHoles(int n, const std::vector<std::string>& grid) {
  if (static_cast<int>(grid.size()) != n) return {};
  for (const std::string& line : grid)
    if (static_cast<int>(line.size()) != n) return {};

  BitmaskSearch search;
  search.n = n;
  search.full = (1 << n) - 1;
  search.holeMask.assign(static_cast<size_t>(n), 0);
  for (int r = 0; r < n; ++r)
    for (int c = 0; c < n; ++c)
      if (grid[r][c] == 'H') search.holeMask[r] |= 1 << c;
  search.run(std::vector<int>(static_cast<size_t>(n), -1));
  return search.solutions;
}

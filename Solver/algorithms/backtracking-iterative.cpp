// Solver for the Normal, Pre-placed and Holes cases: backtracking with an explicit stack instead of recursion.
//
// ---- The idea ------------------------------------------------------------------------------------------------------
// The same search as the plain backtracking solver, with the call stack replaced by a stack of frames it owns:
//
//   struct Frame { int idx; int nextCol; };
//
// `idx` is the row being filled and `nextCol` is the next candidate column to try in it. A frame therefore remembers
// exactly where a recursive call would have resumed, and stepping back is one `pop_back` plus one `unplace`. That makes
// the search stack shallow on the C++ side (one loop, one frame) instead of N call frames deep.
//
// The three cases only differ in what the frames work on:
//   Normal      every row is free.
//   Pre-placed  the rows holding a pre-placed queen are taken up front, so the frames never see them.
//   Holes       a hole removes one candidate column of its own row; attacks pass through it.
#include <cstdlib>  // std::abs
#include <numeric>  // std::iota
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

// One entry of the search stack: the row being filled, and the next column to try in it.
struct Frame {
  int idx;
  int nextCol;
};

struct IterativeSearch {
  int n = 0;
  std::vector<int> rows;           // rows still to fill, in the order the search fills them
  std::vector<int> cols;           // cols[r] = column of row r, -1 = not placed
  std::vector<char> colUsed;       // column c is taken
  std::vector<char> d1, d2;        // diagonal r + c, and diagonal r - c + n - 1, are taken
  std::vector<int> holeMask;       // bit c set when the cell (r, c) is a hole
  std::vector<std::vector<int>> solutions;
  long long deadEnds = 0;          // only counted in a Debug run

  void place(int row, int c) {
    cols[row] = c;
    colUsed[c] = 1;
    d1[row + c] = 1;
    d2[row - c + n - 1] = 1;
  }

  void unplace(int row) {
    const int c = cols[row];
    colUsed[c] = 0;
    d1[row + c] = 0;
    d2[row - c + n - 1] = 0;
    cols[row] = -1;
  }

  bool available(int row, int c) const {
    return !colUsed[c] && !d1[row + c] && !d2[row - c + n - 1] && !(holeMask[row] & (1 << c));
  }

  void readHoles(const std::vector<std::string>& grid) {
    holeMask.assign(n, 0);
    for (int r = 0; r < n; ++r)
      for (int c = 0; c < n; ++c)
        if (grid[r][c] == 'H') holeMask[r] |= 1 << c;
  }

  void run(int size, const std::vector<int>& fillRows) {
    n = size;
    rows = fillRows;
    cols.assign(static_cast<size_t>(n), -1);
    colUsed.assign(static_cast<size_t>(n), 0);
    d1.assign(2 * static_cast<size_t>(n), 0);
    d2.assign(2 * static_cast<size_t>(n), 0);
    holeMask.assign(static_cast<size_t>(n), 0);
    loop();
  }

  void loop() {
    const int depth = static_cast<int>(rows.size());
    std::vector<Frame> stack;
    stack.push_back({0, 0});
    while (!stack.empty()) {
      Frame& frame = stack.back();
      if (frame.idx == depth) {
        // Every row is filled. Take the board and step back over the row that produced this frame.
        solutions.push_back(cols);
        NQ_SNAPSHOT(nq::queensOf(cols), "solution " + std::to_string(solutions.size()));
        stack.pop_back();
        if (!stack.empty()) unplace(rows[stack.back().idx]);
        continue;
      }
      const int row = rows[frame.idx];
      int c = frame.nextCol;
      while (c < n && !available(row, c)) ++c;
      if (c == n) {
        // No candidate column left in this row: this branch is a dead end.
        if (snapshotsEnabled() && (++deadEnds == 1 || deadEnds % DEAD_END_EVERY == 0))
          snapshot(nq::queensOf(cols), "dead end at row " + std::to_string(row));
        stack.pop_back();
        if (!stack.empty()) unplace(rows[stack.back().idx]);
        continue;
      }
      frame.nextCol = c + 1;
      place(row, c);
      stack.push_back({frame.idx + 1, 0});
    }
  }
};

}  // namespace

std::vector<std::vector<int>> solveNQueens(int n) {
  IterativeSearch search;
  std::vector<int> rows(static_cast<size_t>(n));
  std::iota(rows.begin(), rows.end(), 0);
  search.run(n, rows);
  return search.solutions;
}

std::vector<std::vector<int>> solvePreplaced(int n, const std::vector<std::pair<int, int>>& preplaced) {
  std::vector<int> fixed;
  if (!readPreplaced(n, preplaced, fixed)) return {};

  IterativeSearch search;
  std::vector<int> rows;
  search.n = n;
  search.cols.assign(fixed.begin(), fixed.end());
  search.colUsed.assign(static_cast<size_t>(n), 0);
  search.d1.assign(2 * static_cast<size_t>(n), 0);
  search.d2.assign(2 * static_cast<size_t>(n), 0);
  search.holeMask.assign(static_cast<size_t>(n), 0);
  for (int r = 0; r < n; ++r) {
    if (fixed[r] == -1) {
      rows.push_back(r);
      continue;
    }
    search.colUsed[fixed[r]] = 1;
    search.d1[r + fixed[r]] = 1;
    search.d2[r - fixed[r] + n - 1] = 1;
  }
  search.rows = rows;
  search.loop();
  return search.solutions;
}

std::vector<std::vector<int>> solveHoles(int n, const std::vector<std::string>& grid) {
  if (static_cast<int>(grid.size()) != n) return {};
  for (const std::string& line : grid)
    if (static_cast<int>(line.size()) != n) return {};

  IterativeSearch search;
  std::vector<int> rows(static_cast<size_t>(n));
  std::iota(rows.begin(), rows.end(), 0);
  search.n = n;
  search.cols.assign(static_cast<size_t>(n), -1);
  search.colUsed.assign(static_cast<size_t>(n), 0);
  search.d1.assign(2 * static_cast<size_t>(n), 0);
  search.d2.assign(2 * static_cast<size_t>(n), 0);
  search.readHoles(grid);
  search.rows = rows;
  search.loop();
  return search.solutions;
}

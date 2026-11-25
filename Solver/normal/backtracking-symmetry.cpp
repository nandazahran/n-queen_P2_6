// Solver for the Normal case: backtracking that uses the board's own symmetry to cut the search.
//
// ---- The idea ------------------------------------------------------------------------------------------------------
// The square board has eight symmetries: four rotations and four reflections. Each one maps a solution to a solution, so
// the solutions fall into groups of at most eight and searching every member of a group is wasted work.
//
// Every group has a member whose queen in row 0 stands in the left half of the board: mirroring the board left to right
// turns column c into N-1-c, so one of the two is in the left half. The search therefore only tries the columns
// 0..(N-1)/2 in row 0, which halves the tree, and then writes out all eight images of every board it finds. Sorting the
// images and dropping the neighbours removes the duplicates, because a board can be its own image (the four solutions of
// N=4 are two groups of four, and the twelve of N=8 include boards that a rotation maps to themselves).
//
// The search itself is the bitmask one: one integer for the taken columns and two for the diagonals, shifted one row
// down at a time. Only the Normal case is solved here: a pre-placed queen or a hole breaks the symmetry, so the images
// of a board would no longer be boards of the same problem.
//
// The trade-off is worth knowing, because the search is not the whole cost. Halving the tree saves about half of the
// search, but the answer still has to be written out in full, so the eight images and their sorting cost more than the
// halved search saves at the sizes the tester uses (N=12: about 23 ms here against about 19 ms for the plain bitmask
// search). The gain would show on a problem where the search dominates the output, which for N queens it does not:
// almost every search node becomes a solution.
#include <algorithm>  // std::sort, std::unique
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "nqueens.h"

namespace {  // names in here belong to this file only

// The eight symmetries of the square, as (row, column) -> (row, column).
std::pair<int, int> transform(int which, int r, int c, int n) {
  switch (which) {
    case 0: return {r, c};                      // as it is
    case 1: return {c, n - 1 - r};              // turned a quarter
    case 2: return {n - 1 - r, n - 1 - c};      // turned half
    case 3: return {n - 1 - c, r};              // turned three quarters
    case 4: return {r, n - 1 - c};              // mirrored left to right
    case 5: return {n - 1 - r, c};              // mirrored top to bottom
    case 6: return {c, r};                      // mirrored on the main diagonal
    default: return {n - 1 - c, n - 1 - r};     // mirrored on the other diagonal
  }
}

// Adds the eight images of one board to `out` as packed keys. Every image is a board again: the transforms are
// bijections that keep rows and columns, so each row still holds exactly one queen.
//
// A board fits one 64-bit number with four bits per column, so the images are compared as numbers instead of as vectors:
// sorting a few thousand integers is far cheaper than sorting a few thousand vectors of vectors. Four bits per column
// covers N up to 16, which is well past what any of these solvers can enumerate anyway.
void addImages(const std::vector<int>& cols, std::vector<uint64_t>& out) {
  const int n = static_cast<int>(cols.size());
  for (int which = 0; which < 8; ++which) {
    std::vector<int> image(static_cast<size_t>(n), -1);
    for (int r = 0; r < n; ++r) {
      const auto cell = transform(which, r, cols[r], n);
      image[cell.first] = cell.second;
    }
    uint64_t key = 0;
    for (int r = 0; r < n; ++r) key |= static_cast<uint64_t>(image[r]) << (4 * r);
    out.push_back(key);
  }
}

struct Search {
  int n = 0;
  int full = 0;                    // n columns set
  int firstRowMask = 0;            // the columns row 0 may use: the left half
  std::vector<int> cols;           // cols[r] = column of row r, -1 = not placed
  std::vector<std::vector<int>> groups;  // one board per group, not every solution

  void run(int size) {
    n = size;
    full = (1 << n) - 1;
    firstRowMask = (1 << ((n + 1) / 2)) - 1;  // columns 0 .. (n-1)/2
    cols.assign(static_cast<size_t>(n), -1);
    place(0, 0, 0, 0);
  }

  void place(int row, int colMask, int d1, int d2) {
    if (row == n) {
      groups.push_back(cols);
      NQ_SNAPSHOT(nq::queensOf(cols), "group " + std::to_string(groups.size()));
      return;
    }
    int avail = full & ~(colMask | d1 | d2);
    if (row == 0) avail &= firstRowMask;
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
  if (n > 16) return {};  // the packed key holds four bits per column

  Search search;
  search.run(n);

  // Eight images per group, with repeats where a board is its own image.
  std::vector<uint64_t> keys;
  keys.reserve(search.groups.size() * 8);
  for (const std::vector<int>& group : search.groups) addImages(group, keys);
  std::sort(keys.begin(), keys.end());
  keys.erase(std::unique(keys.begin(), keys.end()), keys.end());

  std::vector<std::vector<int>> boards;
  boards.reserve(keys.size());
  for (uint64_t key : keys) {
    std::vector<int> cols(static_cast<size_t>(n));
    for (int r = 0; r < n; ++r) cols[r] = static_cast<int>((key >> (4 * r)) & 15u);
    boards.push_back(std::move(cols));
  }
  return boards;
}

// Solver for the Normal and Holes cases: the problem written as an exact cover and solved with Dancing Links.
//
// ---- The idea ------------------------------------------------------------------------------------------------------
// Exact cover asks for a set of rows of a 0/1 matrix that covers every column exactly once. N queens fit it like this:
//
//   primary columns    N for the rows of the board, N for its columns. Each must be covered exactly once, which is what
//                      "one queen per row and per column" means.
//   secondary columns  2(2N-1) for the diagonals. Each may be covered at most once, which is what "no two queens on one
//                      diagonal" means. A secondary column is allowed to stay empty, so it is not a plain exact cover.
//   matrix rows        one per cell: placing a queen there covers its row, its column and its two diagonals.
//
// Knuth's Algorithm X solves it: pick the column with the fewest rows, try each of its rows, and remove the columns that
// row covers. Dancing Links keeps the matrix as a mesh of four-way linked nodes, so removing and restoring a column is a
// handful of pointer writes and no copying.
//
// A hole is one line of work: the cell's matrix row is simply not built, so no queen can land there. Attacks still pass
// through a hole, which is exactly what the diagonal columns already say.
#include <climits>  // INT_MAX
#include <string>
#include <utility>
#include <vector>

#include "nqueens.h"

namespace {  // names in here belong to this file only

// One node of the mesh. A column header is a node too, and `col` points at the header it belongs to.
struct Node {
  int left, right, up, down, col, row;
};

struct Dlx {
  int n = 0;
  std::vector<Node> nodes;
  std::vector<int> size;      // rows left in each column
  std::vector<char> primary;  // 1 for a row or column of the board, 0 for a diagonal
  std::vector<int> header;    // column index -> its header node
  int root = 0;
  std::vector<int> chosen;    // matrix rows of the queens placed so far
  std::vector<std::vector<int>> solutions;

  int addNode(int col, int row) {
    nodes.push_back({0, 0, 0, 0, col, row});
    return static_cast<int>(nodes.size()) - 1;
  }

  // Builds the mesh. `blocked[r][c]` is true for a hole, whose matrix row is left out.
  void build(const std::vector<std::vector<char>>& blocked) {
    const int diagonals = 2 * (2 * n - 1);
    const int columns = 2 * n + diagonals;

    root = addNode(-1, -1);
    nodes[root].left = nodes[root].right = root;
    size.assign(static_cast<size_t>(columns), 0);
    primary.assign(static_cast<size_t>(columns), 0);

    // The column headers, in a ring with the root.
    header.assign(static_cast<size_t>(columns), -1);
    for (int c = 0; c < columns; ++c) {
      const int h = addNode(c, -1);
      header[c] = h;
      primary[c] = c < 2 * n ? 1 : 0;
      nodes[h].up = nodes[h].down = h;
      nodes[h].left = nodes[root].left;
      nodes[h].right = root;
      nodes[nodes[root].left].right = h;
      nodes[root].left = h;
    }

    // One matrix row per free cell: its board row, its board column, and its two diagonals.
    for (int r = 0; r < n; ++r) {
      for (int c = 0; c < n; ++c) {
        if (blocked[r][c]) continue;
        const int row = r * n + c;
        const int cols[4] = {r, n + c, 2 * n + (r + c), 2 * n + (2 * n - 1) + (r - c + n - 1)};
        int first = -1, last = -1;
        for (int k = 0; k < 4; ++k) {
          const int h = header[cols[k]];
          const int node = addNode(cols[k], row);
          // Into the column, above its header.
          nodes[node].down = h;
          nodes[node].up = nodes[h].up;
          nodes[nodes[h].up].down = node;
          nodes[h].up = node;
          ++size[cols[k]];
          // Into the row, left to right.
          if (first < 0) {
            first = last = node;
            nodes[node].left = nodes[node].right = node;
          } else {
            nodes[node].left = last;
            nodes[node].right = first;
            nodes[last].right = node;
            nodes[first].left = node;
            last = node;
          }
        }
      }
    }
  }

  void cover(int c) {
    const int h = c;  // the header of column c is the node whose col is c and whose row is -1
    nodes[nodes[h].right].left = nodes[h].left;
    nodes[nodes[h].left].right = nodes[h].right;
    for (int i = nodes[h].down; i != h; i = nodes[i].down) {
      for (int j = nodes[i].right; j != i; j = nodes[j].right) {
        nodes[nodes[j].down].up = nodes[j].up;
        nodes[nodes[j].up].down = nodes[j].down;
        --size[nodes[j].col];
      }
    }
  }

  void uncover(int c) {
    const int h = c;
    for (int i = nodes[h].up; i != h; i = nodes[i].up) {
      for (int j = nodes[i].left; j != i; j = nodes[j].left) {
        ++size[nodes[j].col];
        nodes[nodes[j].down].up = j;
        nodes[nodes[j].up].down = j;
      }
    }
    nodes[nodes[h].right].left = h;
    nodes[nodes[h].left].right = h;
  }

  // The primary column with the fewest rows, or -1 when every primary column is covered: that is a solution.
  int chooseColumn() const {
    int best = -1, bestSize = INT_MAX;
    for (int h = nodes[root].right; h != root; h = nodes[h].right) {
      if (!primary[nodes[h].col]) continue;
      if (size[nodes[h].col] < bestSize) {
        bestSize = size[nodes[h].col];
        best = h;
        if (bestSize == 0) break;
      }
    }
    return best;
  }

  void record() {
    std::vector<int> cols(static_cast<size_t>(n), -1);
    for (int row : chosen) cols[row / n] = row % n;
    solutions.push_back(cols);
    NQ_SNAPSHOT(nq::queensOf(cols), "solution " + std::to_string(solutions.size()));
  }

  void search() {
    const int h = chooseColumn();
    if (h < 0) {
      record();
      return;
    }
    cover(h);
    for (int i = nodes[h].down; i != h; i = nodes[i].down) {
      chosen.push_back(nodes[i].row);
      for (int j = nodes[i].right; j != i; j = nodes[j].right) cover(header[nodes[j].col]);
      search();
      for (int j = nodes[i].left; j != i; j = nodes[j].left) uncover(header[nodes[j].col]);
      chosen.pop_back();
    }
    uncover(h);
  }
};

}  // namespace

std::vector<std::vector<int>> solveNQueens(int n) {
  Dlx dlx;
  dlx.n = n;
  dlx.build(std::vector<std::vector<char>>(static_cast<size_t>(n), std::vector<char>(static_cast<size_t>(n), 0)));
  dlx.search();
  return dlx.solutions;
}

std::vector<std::vector<int>> solveHoles(int n, const std::vector<std::string>& grid) {
  if (static_cast<int>(grid.size()) != n) return {};
  for (const std::string& line : grid)
    if (static_cast<int>(line.size()) != n) return {};

  std::vector<std::vector<char>> blocked(static_cast<size_t>(n), std::vector<char>(static_cast<size_t>(n), 0));
  for (int r = 0; r < n; ++r)
    for (int c = 0; c < n; ++c)
      if (grid[r][c] == 'H') blocked[r][c] = 1;

  Dlx dlx;
  dlx.n = n;
  dlx.build(blocked);
  dlx.search();
  return dlx.solutions;
}

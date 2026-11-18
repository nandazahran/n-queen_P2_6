# projectmem - proyek-analgor-kelompok-6-P2

_Last updated: 2026-11-18_

## Project purpose
A local browser app for testing N-Queens solvers written in C++. A solver is a plain function: it gets the problem as arguments and returns every solution, like any N-Queens exercise. Solvers are compiled to WebAssembly and run in a Web Worker. The app times the function over several runs and…

## Recent issues
- [DONE] #legacy_e9c4 Legacy issue: fix(ui): the Debug run switch is a switch again -> fix(ui): the Debug run switch is a switch again (fixed)

## Decisions
- No decisions logged yet.

## Notes
- Initial release: the N-Queen tester with four example solvers
- Update README.md
- feat: H and W replace K, and a wall in the Walled grid is 'W' instead of 'P'
- docs(readme): drop the note about the earlier 'P' for a wall
- New feature: feat(solvers): add six N-Queens algorithms under Solver/algorithms [Solver/algorithms/backtracking-bitmask.cpp]

## Key files
- `.gitignore`
- `README.md`
- `Solver/example/bruteforce-holes.cpp`
- `Solver/example/bruteforce-normal.cpp`
- `Solver/example/bruteforce-preplaced.cpp`
- `Solver/example/bruteforce-walled.cpp`
- `Tester/Board/conflicts.ts`
- `Tester/Board/feasibility.ts`
- `Tester/Board/positions.ts`
- `Tester/Board/preplaced.ts`
- `Tester/Board/rng.ts`
- `Tester/Board/solution-check.ts`
- `Tester/Board/solution-set.ts`
- `Tester/Board/terrain.ts`
- `Tester/Board/validator.ts`
- `Tester/Configuration/budget.ts`
- `Tester/Configuration/config.ts`
- `Tester/Configuration/tester.config.json`
- `Tester/Execution/judge.ts`
- `Tester/Execution/measure.ts`

## Open questions
- None logged yet.

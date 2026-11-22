# Sokoban solver — make.fun sokoban-solver-01-run-20261121

A push-optimal Sokoban solver for make.fun's "Build the best Sokoban solver, 21 November 2026"
bounty, rerun run-20261121. One program, `main.ts` at the repository root, answers every
instance of a set in a single run: it reads `/input/<id>/level.txt` (XSB) and writes
`/output/<id>/solution.txt` (the player's moves in LURD), creating the output directories
itself.

## How it works

The levels this competition draws are a one-square hallway with one to four small rooms off
it, 3 or 4 boxes per room, and a box can never leave its room — so a level's push optimum is
the sum of its rooms' optima. The solver:

1. **Splits the level into rooms.** The dead squares of the player's row (the hallway) are
   cut out of the floor; each connected part left that holds a box is a room.
2. **Solves each room exactly.** An A* search over pushes (a state is the boxes' squares plus
   the player's reachable region) with an admissible estimate — a minimum-cost matching of
   boxes to goals over true one-box push distances — so the first solution settled is
   push-optimal. Dead squares, frozen 2x2 blocks and freeze deadlocks are pruned, and a
   transposition table keeps the search small. The other rooms' boxes stand as walls while
   one room is solved, and the player walks on from where the last room left it.
3. **Falls back and self-checks.** A level that is not a set of rooms is searched whole with
   the same exact search, and every answer is verified by replay before it is written.

All budgets are counts of expanded states, never the clock, and every tie is broken by
square order, so two runs write byte-identical output.

## Run it locally

```sh
mkdir -p out
MAKEFUN_INPUT_DIR=<dir with i001..i005/level.txt> MAKEFUN_OUTPUT_DIR=out node main.ts
```

Node 22, no dependencies.

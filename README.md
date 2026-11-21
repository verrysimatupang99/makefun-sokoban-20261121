# Room-decomposed Sokoban solver

A `main.ts` entry for make.fun's `sokoban-solver-01-run-20261121` bounty. Each
level is a hallway with 1-4 small rooms off it, one door each; a box pushed out
of a door is lost, so rooms are independent and the level's push-optimum is the
sum of the rooms' optima.

The solver cuts the hallway out of the floor, flood-fills the rest into rooms,
and solves each room with a breadth-first search over pushes (state: box set +
player's reachable region) pruned by pull-back dead squares and frozen 2x2
blocks — provably push-optimal per room. Runs on Node 22, stdlib only.

Local test:
`MAKEFUN_INPUT_DIR=<kit>/practice/input MAKEFUN_OUTPUT_DIR=out node main.ts`

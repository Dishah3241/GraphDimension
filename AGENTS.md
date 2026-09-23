# GraphDimension working rules

The shared library of the Math workspace's ADR 0004 ladder: unit-distance representations, the
Erdős–Harary–Tutte dimension, and the API every rung re-uses. `../../AGENTS.md` holds the workspace
rules and governs here too; read it first. The design is `../../docs/design/graph-dimension-library.md`
(ROADMAP P2). Its §2 definitions were signed off by the owner on 2026-09-22 and live in
`GraphDimension/Basic.lean`; the owner approved renaming `HasDimension` to `HasUnitDistDim` on 2026-09-23 (A34). Changing them is its own reviewed change.

- **Rungs import this library; it imports nothing of theirs.** A rung's `Solution` requires it at a
  40-character revision, and each rung bridges its inlined statement definitions by `Iff.rfl`.
- **Never reuse a `formal-conjectures` name.** `FormalConjecturesForMathlib` defines
  `SimpleGraph.HasDimension`. This library's dimension was renamed `SimpleGraph.HasUnitDistDim` so that one
  environment can import both (Math finding A34).
  Before adding a definition, `grep` `~/Code/Math/.cache/formal-conjectures` for its full name.
- **Naming and style follow the design's §4:** Mathlib spelling in the `SimpleGraph` namespace, and
  hypotheses in the weakest form the proof allows. Nothing project-specific goes in.
- **Gates:** `lake build` (`warningAsError`, so no `sorry`) and `lake exe axioms` (only `propext`,
  `Classical.choice` and `Quot.sound`).
- **Worktrees:** run `scripts/worktree-setup.sh` before the first `lake` command. Never run
  `lake exe cache get`; Mathlib is shared with `../Erdos1007`.
- **Seed:** rung 1's proved modules in `../Erdos1007` (Apache-2.0) are copied in, not moved.
  Erdos1007 stays as it is.

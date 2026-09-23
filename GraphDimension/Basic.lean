/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Unit-distance representations and the Erdős–Harary–Tutte dimension

The two definitions every rung of the Math workspace's ADR 0004 ladder shares, fixed by
`docs/design/graph-dimension-library.md` §2. They are identical to the definitions that
`formal-conjectures` states for `erdos_1007`, so each rung bridges them by `Iff.rfl`.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- An injective placement in `ℝⁿ` that puts every edge at distance one. Non-edges are
unconstrained (Erdős–Harary–Tutte), unlike a unit-distance graph. -/
def UnitDistEmbeddable (n : ℕ) : Prop :=
  ∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧
    ∀ u v, G.Adj u v → dist (f u) (f v) = 1

/-- `n` is the least dimension admitting such a placement. -/
def HasDimension (n : ℕ) : Prop := IsLeast {m | G.UnitDistEmbeddable m} n

end SimpleGraph

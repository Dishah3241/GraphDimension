/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.UnitDistance.Basic

/-!
# Bridge to Mathlib's unit-distance graph embeddings

Mathlib carries a structure `SimpleGraph.UnitDistEmbedding` bundling a vertex embedding into a
metric space with the condition that adjacent vertices land at distance one. This module shows
that the library's predicate `SimpleGraph.UnitDistEmbeddable` is exactly its nonemptiness for the
ambient space `ℝⁿ`: the placement functions, injectivity and edge-distance data are the same,
only packed differently.
-/

@[expose] public section

namespace SimpleGraph

/-- `G` admits an injective unit-distance placement in `ℝⁿ` if and only if Mathlib's
`UnitDistEmbedding` structure of `G` into `EuclideanSpace ℝ (Fin n)` is inhabited. -/
theorem unitDistEmbeddable_iff_nonempty_unitDistEmbedding {V : Type*} {G : SimpleGraph V} {n : ℕ} :
    G.UnitDistEmbeddable n ↔
      Nonempty (G.UnitDistEmbedding (EuclideanSpace ℝ (Fin n))) := by
  constructor
  · rintro ⟨f, hfInj, hfDist⟩
    exact ⟨⟨⟨f, hfInj⟩, fun {u v} huv => hfDist u v huv⟩⟩
  · rintro ⟨U⟩
    exact ⟨U.p, U.p.injective, fun _ _ huv => U.unit_dist huv⟩

end SimpleGraph

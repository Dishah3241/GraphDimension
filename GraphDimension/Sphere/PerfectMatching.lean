/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Combinatorics.SimpleGraph.MatchingPairs
public import GraphDimension.Sphere.CrossPolytope

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Placements from a complement perfect matching

If the complement of a graph on `2d` vertices has a perfect matching, the graph itself sits on the
sphere of radius `1/√2` in `ℝᵈ`: the `d` matched pairs go to `±eᵢ/√2` and every vertex is matched,
so the cross-polytope construction applies with `k = d` and has no leftover vertices to place.
-/

@[expose] public section

namespace SimpleGraph

-- M2
/-- **Placement from a complement perfect matching** (Frankl–Kupavskii–Swanepoel's cross-polytope
lemma with `k = d`).

If the complement of a graph on `2d` vertices has a perfect matching, the graph has a spherical
placement in `ℝᵈ`: each matched pair goes to a pair of opposite axes scaled by `1/√2`. -/
theorem SphereEmbeddable.of_compl_perfectMatching
    {V : Type*} [Finite V] {G : SimpleGraph V} {d : ℕ}
    (hcard : Nat.card V = 2 * d)
    (hM : ∃ M : Gᶜ.Subgraph, M.IsPerfectMatching) :
    G.SphereEmbeddable d := by
  classical
  have : Fintype V := Fintype.ofFinite V
  obtain ⟨M, hM⟩ := hM
  obtain ⟨a, b, hinj, hadj⟩ := hM.exists_indexed_edges hcard
  have hle : Fintype.card V ≤ d + d := by
    rw [← Nat.card_eq_fintype_card, hcard]
    omega
  refine SphereEmbeddable.of_compl_matching (Nat.le_refl d) hle a b hinj fun i => ?_
  exact (G.compl_adj (a i) (b i)).mp (hadj i).adj_sub |>.2

end SimpleGraph

/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Sphere.Extend
public import Mathlib.Combinatorics.SimpleGraph.Finite

import Mathlib.Tactic.Linarith

/-!
# Reduction of the maximum-degree-two case to two-regular graphs

Deleting vertices with at most one remaining neighbour leaves a core in which every vertex has
degree two. `SphereEmbeddable.exists_core` re-attaches the deleted vertices after the core is
placed. The missing part of the `d = 3` base of FKS Proposition 2 is a spherical placement of
every finite two-regular graph.
-/

namespace SimpleGraph

universe u

@[expose] public section

/-- To place every graph of maximum degree two in `ℝ³`, it suffices to place every finite
two-regular graph there. The `(d - 1)`-core with `d = 3` removes vertices of degree at most one;
the maximum-degree hypothesis makes every remaining degree exactly two. -/
theorem SphereEmbeddable.of_degree_le_three_of_regular
    {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hregular : ∀ {W : Type u} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (∀ w, H.degree w = 2) → H.SphereEmbeddable 3)
    (h : ∀ v, G.degree v ≤ 2) : G.SphereEmbeddable 3 := by
  classical
  obtain ⟨c, hcore, hprop⟩ := SphereEmbeddable.exists_core (G := G) (d := 3) (by omega)
  apply hprop
  let H : SimpleGraph {v // v ∈ (c : Set V)} := G.induce (c : Set V)
  have hdeg : ∀ x : {v // v ∈ (c : Set V)}, H.degree x = 2 := by
    intro x
    have heq : H.degree x = (G.neighborFinset x.1 ∩ c).card := by
      calc
        H.degree x = (H.neighborFinset x).card := (card_neighborFinset_eq_degree H x).symm
        _ = ((H.neighborFinset x).map (Function.Embedding.subtype (· ∈ (c : Set V)))).card :=
          (Finset.card_map _).symm
        _ = (G.neighborFinset x.1 ∩ c).card := by
          congr 1
          ext y
          simp [H, SimpleGraph.mem_neighborFinset, and_comm]
    have hfilter : c.filter (G.Adj x.1) = G.neighborFinset x.1 ∩ c := by
      ext y
      simp [SimpleGraph.mem_neighborFinset, and_comm]
    have hlo : 2 ≤ H.degree x := by
      rw [heq, ← hfilter]
      have hc := hcore x.1 x.2
      omega
    have hhi : H.degree x ≤ 2 := by
      rw [heq]
      exact (Finset.card_le_card Finset.inter_subset_left).trans
        (by simpa only [card_neighborFinset_eq_degree] using h x.1)
    omega
  exact hregular H hdeg

end

end SimpleGraph

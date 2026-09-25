/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Combinatorics.SimpleGraph.SevenVerticesComplement
public import GraphDimension.Combinatorics.SimpleGraph.SevenVerticesContainment
public import GraphDimension.Geometry.CompleteMultipartiteOneOneFive
public import GraphDimension.Geometry.ConeTwoTriangles
public import GraphDimension.Geometry.UnitDistanceComap
public import GraphDimension.Extremal.TenEdges
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Finite

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card

/-!
# The seven-vertex disjunction, given the ten-edge lemma

Leaf T4 of the FKS leaf plan (design `2026-09-24-p9-d1-blueprint-design.md`, §1): assuming the
ten-edge lemma (leaf E), every graph on seven vertices, or its complement, has a unit-distance
placement in `ℝ³`.

By T3 a graph `G` on seven vertices and its complement together have `21 = 7.choose 2` edges, so
one of them, the sparse colour `H`, has at most ten. If `H` contains neither a `K₅` nor a
`K₃,₃`, the ten-edge lemma places `H`. If `H` contains a `K₅`, T1 embeds the other colour in
`K₁,₁,₅`, which P5 places; if `H` contains a `K₃,₃`, T2 embeds the other colour in the cone over
two triangles, which P6 places.
-/

@[expose] public section

namespace SimpleGraph

/-- The ten-edge lemma's statement (leaf E), as a hypothesis. -/
def TenEdgeLemma : Prop :=
  ∀ {V : Type} [Finite V] (G : SimpleGraph V), Nat.card V ≤ 7 → G.edgeSet.ncard ≤ 10 →
    ¬ ((⊤ : SimpleGraph (Fin 5)) ⊑ G) →
    ¬ ((completeBipartiteGraph (Fin 3) (Fin 3)) ⊑ G) → G.UnitDistEmbeddable 3

/-- One of a sparse colour `H` on seven vertices and its complement `J` is placed: if `H`
contains neither a `K₅` nor a `K₃,₃`, the ten-edge lemma places `H`; otherwise T1 or T2 embeds
`J` in `K₁,₁,₅` or in the cone over two triangles, and P5 or P6 places the container. -/
private theorem unitDistEmbeddable_three_or_compl_of_ncard_edgeSet_le (hTen : TenEdgeLemma)
    {H J : SimpleGraph (Fin 7)} (hE : H.edgeSet.ncard ≤ 10) (hJ : Hᶜ = J) :
    H.UnitDistEmbeddable 3 ∨ J.UnitDistEmbeddable 3 := by
  have hcard : Nat.card (Fin 7) ≤ 7 := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  by_cases hK5 : (⊤ : SimpleGraph (Fin 5)) ⊑ H
  · have h := compl_isContained_completeMultipartiteGraph_one_one_five H hK5
    rw [hJ] at h
    obtain ⟨f⟩ := h
    exact Or.inr (UnitDistEmbeddable.comap f.toHom f.injective
      unitDistEmbeddable_completeMultipartiteGraph_one_one_five)
  by_cases hK33 : (completeBipartiteGraph (Fin 3) (Fin 3)) ⊑ H
  · have h := compl_isContained_coneTwoTrianglesGraph H hK33
    rw [hJ] at h
    obtain ⟨f⟩ := h
    exact Or.inr (UnitDistEmbeddable.comap f.toHom f.injective
      unitDistEmbeddable_coneTwoTrianglesGraph)
  · exact Or.inl (hTen H hcard hE hK5 hK33)

/-- **T4** (given E): every graph on seven vertices, or its complement, admits a unit-distance
placement in `ℝ³`. -/
theorem unitDistEmbeddable_three_or_compl_fin_seven_of_tenEdgeLemma (hTen : TenEdgeLemma)
    (G : SimpleGraph (Fin 7)) :
    G.UnitDistEmbeddable 3 ∨ Gᶜ.UnitDistEmbeddable 3 := by
  have hsum := edgeSet_ncard_add_compl_fin_seven G
  rcases (show G.edgeSet.ncard ≤ 10 ∨ Gᶜ.edgeSet.ncard ≤ 10 by omega) with hE | hE
  · exact unitDistEmbeddable_three_or_compl_of_ncard_edgeSet_le hTen hE rfl
  · exact (unitDistEmbeddable_three_or_compl_of_ncard_edgeSet_le hTen hE
      (compl_compl G)).symm

/-- **T4**: every graph on seven vertices, or its complement, admits a unit-distance
representation in `ℝ³`. This is T4 with leaf E, the ten-edge lemma
`unitDistEmbeddable_three_of_ncard_edgeSet_le_ten`, discharging its hypothesis. -/
theorem unitDistEmbeddable_three_or_compl_fin_seven (G : SimpleGraph (Fin 7)) :
    G.UnitDistEmbeddable 3 ∨ Gᶜ.UnitDistEmbeddable 3 :=
  unitDistEmbeddable_three_or_compl_fin_seven_of_tenEdgeLemma
    (fun G hV hE hK5 hK33 => unitDistEmbeddable_three_of_ncard_edgeSet_le_ten G hV hE hK5 hK33) G

end SimpleGraph

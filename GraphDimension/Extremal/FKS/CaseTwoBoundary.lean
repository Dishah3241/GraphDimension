/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.FKS.Defs
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Fin.VecNotation

/-!
# An extra vertex in the dimension-three Case 2 configuration

The equality edge count does not force `d + 3` vertices when `d = 3`. The seven-vertex
graph below has the required core degrees and an almost-complete copy after deleting a
maximum-degree vertex and its non-neighbour, but that deletion also has an isolated vertex.
Thus the hypotheses of `SphereEmbeddable.of_case_two` do not follow from the count alone.
-/

@[expose] public section

namespace SimpleGraph

set_option maxRecDepth 4096 in
/-- The dimension-three Case 2 edge count can be saturated on seven vertices, even with
both forbidden larger subgraphs absent. Vertices `0, 1` are the deleted pair; `6` is the
extra vertex, adjacent to both of them. -/
theorem exists_fks_case_two_extra_vertex :
    ∃ G : SimpleGraph (Fin 7), G.edgeSet.ncard = 8 ∧
      (∀ x, 2 ≤ (G.neighborSet x).ncard ∧ (G.neighborSet x).ncard ≤ 3) ∧
      (G.neighborSet 0).ncard = 3 ∧ (G.neighborSet 1).ncard = 2 ∧
      ¬ G.Adj 0 1 ∧ G.CliqueFree 4 ∧ (completeMinusTriangle 5).Free G ∧
      completeMinusTriangle 4 ⊑ G.induce {x | x ≠ 0 ∧ x ≠ 1} := by
  let G : SimpleGraph (Fin 7) := fromRel fun i j =>
    (i, j) ∈ ({(2, 3), (2, 4), (2, 5), (0, 3), (0, 4), (0, 6), (1, 5), (1, 6)} :
      Finset (Fin 7 × Fin 7))
  have hE : G.edgeFinset.card = 8 := by decide
  have hdeg : ∀ x, 2 ≤ G.degree x ∧ G.degree x ≤ 3 := by decide
  have h0 : G.degree 0 = 3 := by decide
  have h1 : G.degree 1 = 2 := by decide
  have hnadj : ¬ G.Adj 0 1 := by decide
  have hK : G.CliqueFree 4 := by unfold CliqueFree; decide
  let q : Fin 4 → {x : Fin 7 // x ≠ 0 ∧ x ≠ 1} :=
    ![⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨2, by decide⟩]
  let _ : DecidableRel (completeMinusTriangle 4).Adj :=
    fun i j => inferInstanceAs (Decidable (i ≠ j ∧ ¬ (i.val < 3 ∧ j.val < 3)))
  have hcopy : completeMinusTriangle 4 ⊑ G.induce {x | x ≠ 0 ∧ x ≠ 1} :=
    ⟨{ toHom := { toFun := q, map_rel' := by decide }, injective' := by decide }⟩
  have hT : (completeMinusTriangle 5).Free G := by
    intro ⟨f⟩
    let _ : DecidableRel (completeMinusTriangle 5).Adj :=
      fun i j => inferInstanceAs (Decidable (i ≠ j ∧ ¬ (i.val < 3 ∧ j.val < 3)))
    have hlarge : (completeMinusTriangle 5).degree 3 = 4 := by decide
    have hle := f.degree_le 3
    have hsmall := (hdeg (f 3)).2
    omega
  refine ⟨G, ?_, ?_, ?_, ?_, hnadj, hK, hT, hcopy⟩
  · simpa only [edgeFinset_card, Set.fintypeCard_eq_ncard] using hE
  · simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hdeg
  · simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using h0
  · simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using h1

end SimpleGraph

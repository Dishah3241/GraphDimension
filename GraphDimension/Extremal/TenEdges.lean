/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic
public import GraphDimension.Combinatorics.SimpleGraph.FiveVerticesContainment
public import GraphDimension.Extremal.TenEdges.DegreeTwo
public import GraphDimension.Extremal.TenEdges.SixVertices
public import GraphDimension.Geometry.CompleteMinusEdge

import GraphDimension.Geometry.Reattach
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card

/-!
# Ten edges on at most seven vertices

A graph on at most seven vertices and with at most ten edges has a unit-distance placement in
`ℝ³` unless it contains `K₅` or `K₃,₃`. The proof deletes vertices of degree at most one,
uses the degree-two reduction, and applies the five- and six-vertex results when the minimum
degree is at least three.
-/

namespace SimpleGraph

noncomputable section

open Finset

private lemma edgeSet_ncard_eq {V : Type*} (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeSet.ncard = #G.edgeFinset := by
  rw [edgeFinset_card, Set.fintypeCard_eq_ncard]

private lemma card_edgeFinset_induce_ne {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (u : V) :
    (G.induce {v | v ≠ u}).edgeFinset.card = G.edgeFinset.card - G.degree u := by
  rw [← G.card_edgeFinset_deleteIncidenceSet u,
    ← G.card_edgeFinset_induce_compl_singleton u]
  rfl

private lemma edgeSet_ncard_overFin {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (hV : Fintype.card V = n) : (G.overFin hV).edgeSet.ncard = G.edgeSet.ncard := by
  classical
  rw [edgeSet_ncard_eq, edgeSet_ncard_eq (G := G), (G.overFinIso hV).card_edgeFinset_eq]

private theorem unitDistEmbeddable_three_of_minDegree_ge_three {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hE : G.edgeSet.ncard ≤ 10)
    (hK5 : ¬ ((⊤ : SimpleGraph (Fin 5)) ⊑ G))
    (hK33 : ¬ ((completeBipartiteGraph (Fin 3) (Fin 3)) ⊑ G))
    (hδ : ∀ v, 3 ≤ G.degree v) : G.UnitDistEmbeddable 3 := by
  classical
  have hcardE : #G.edgeFinset ≤ 10 := by
    rw [← edgeSet_ncard_eq]
    exact hE
  have hsum : ∑ v, G.degree v = 2 * #G.edgeFinset := G.sum_degrees_eq_twice_card_edges
  have hlower : 3 * Fintype.card V ≤ ∑ v, G.degree v := by
    have hs : ∑ v : V, (3 : ℕ) ≤ ∑ v, G.degree v :=
      Finset.sum_le_sum fun v _ => hδ v
    have hconst : ∑ v : V, (3 : ℕ) = 3 * Fintype.card V := by
      rw [Finset.sum_const, Finset.card_univ]
      simp [mul_comm]
    simpa [hconst] using hs
  have hle6 : Fintype.card V ≤ 6 := by
    rw [hsum] at hlower
    omega
  by_cases h5 : Fintype.card V ≤ 5
  · obtain ⟨f⟩ := isContained_completeGraph_five_deleteEdge_of_card_le_five G h5 hK5
    exact UnitDistEmbeddable.comap f.toHom f.injective
      unitDistEmbeddable_completeGraph_five_deleteEdge
  · have h6 : Fintype.card V = 6 := by omega
    have hE' : (G.overFin h6).edgeSet.ncard ≤ 10 := by
      rw [edgeSet_ncard_overFin h6]
      exact hE
    have hδ' : ∀ v, 3 ≤ (G.overFin h6).degree v := by
      intro v
      have hdeg := (G.overFinIso h6).degree_eq ((G.overFinIso h6).symm v)
      rw [(G.overFinIso h6).apply_symm_apply] at hdeg
      rw [hdeg]
      exact hδ _
    have hK33' : ¬ ((completeBipartiteGraph (Fin 3) (Fin 3)) ⊑ G.overFin h6) := by
      intro h
      exact hK33 (h.trans (G.overFinIso h6).symm.isContained)
    exact (UnitDistEmbeddable.of_iso (G.overFinIso h6)).mpr
      (unitDistEmbeddable_three_fin_six_of_minDegree_ge_three (G.overFin h6) hE' hδ' hK33')

private theorem unitDistEmbeddable_three_of_ncard_edgeSet_le_ten_aux
    (n : ℕ) {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V ≤ n)
    (hn : n ≤ 7)
    (hE : G.edgeSet.ncard ≤ 10)
    (hK5 : ¬ ((⊤ : SimpleGraph (Fin 5)) ⊑ G))
    (hK33 : ¬ ((completeBipartiteGraph (Fin 3) (Fin 3)) ⊑ G)) :
    G.UnitDistEmbeddable 3 := by
  induction n generalizing V with
  | zero =>
    have : IsEmpty V := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hV)
    exact ⟨isEmptyElim, isEmptyElim, isEmptyElim⟩
  | succ n ih =>
    classical
    by_cases hlt : Fintype.card V ≤ n
    · exact ih G hlt (by omega) hE hK5 hK33
    · have hcard : Fintype.card V = n + 1 := by omega
      by_cases hlow : ∃ u, G.degree u ≤ 1
      · obtain ⟨u, hu⟩ := hlow
        let H : SimpleGraph {v : V // v ≠ u} := G.induce {v | v ≠ u}
        have hcardH : Fintype.card {v : V // v ≠ u} ≤ n := by
          rw [Fintype.card_subtype_compl (p := (· = u)), Fintype.card_subtype_eq u, hcard]
          omega
        have hEH : H.edgeSet.ncard ≤ 10 := by
          rw [edgeSet_ncard_eq, card_edgeFinset_induce_ne (G := G) u]
          rw [edgeSet_ncard_eq] at hE
          omega
        have hK5H : ¬ ((⊤ : SimpleGraph (Fin 5)) ⊑ H) := by
          intro h
          exact hK5 (h.trans ⟨Copy.induce G {v | v ≠ u}⟩)
        have hK33H : ¬ ((completeBipartiteGraph (Fin 3) (Fin 3)) ⊑ H) := by
          intro h
          exact hK33 (h.trans ⟨Copy.induce G {v | v ≠ u}⟩)
        obtain ⟨f, hfInj, hfDist⟩ := ih H hcardH (by omega) hEH hK5H hK33H
        refine UnitDistEmbeddable.extend_degree_le_two_fin_three (by omega : G.degree u ≤ 2)
          ⟨f, hfInj, ?_⟩
        intro a b hcond
        rcases hcond with hadj | ⟨h2, -, -, -⟩
        · exact hfDist a b hadj
        · omega
      · by_cases htwo : ∃ u, G.degree u = 2
        · obtain ⟨u, hu⟩ := htwo
          exact unitDistEmbeddable_three_of_degree_eq_two G u (by omega) hE hK33 hu
        · have hδ : ∀ v, 3 ≤ G.degree v := by
            intro v
            have h1 : ¬ G.degree v ≤ 1 := fun h => hlow ⟨v, h⟩
            have h2 : G.degree v ≠ 2 := fun h => htwo ⟨v, h⟩
            omega
          exact unitDistEmbeddable_three_of_minDegree_ge_three G hE hK5 hK33 hδ

@[expose] public section

/-- A graph on at most seven vertices with at most ten edges embeds in `ℝ³` if it contains
neither `K₅` nor `K₃,₃` as a subgraph. -/
theorem unitDistEmbeddable_three_of_ncard_edgeSet_le_ten
    {V : Type*} [Finite V] (G : SimpleGraph V)
    (hV : Nat.card V ≤ 7)
    (hE : G.edgeSet.ncard ≤ 10)
    (hK5 : ¬ ((⊤ : SimpleGraph (Fin 5)) ⊑ G))
    (hK33 : ¬ ((completeBipartiteGraph (Fin 3) (Fin 3)) ⊑ G)) :
    G.UnitDistEmbeddable 3 := by
  classical
  have := Fintype.ofFinite V
  exact unitDistEmbeddable_three_of_ncard_edgeSet_le_ten_aux 7 G
    (by simpa using hV) (by omega) hE hK5 hK33

end

end

end SimpleGraph

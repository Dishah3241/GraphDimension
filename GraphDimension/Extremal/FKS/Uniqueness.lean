/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.FKS.EqualityBranches

/-!
# Uniqueness at the complete-graph edge count

For `d ≥ 6`, a graph with `C(d + 2, 2)` edges, no isolated vertices, and no injective
unit-distance placement in `ℝᵈ` is the complete graph on `d + 2` vertices. The proof
runs the FKS branches at the equality budget, using `S(d - 1)` for the spherical branch.
-/

@[expose] public section

namespace SimpleGraph

open Finset

/-- A clique exhausting the edge budget exhausts every non-isolated vertex. -/
theorem nonempty_iso_completeGraph_of_isNClique {V : Type*} [Finite V]
    {G : SimpleGraph V} {n : ℕ} {s : Finset V} (hK : G.IsNClique n s)
    (hbudget : G.edgeSet.ncard ≤ n.choose 2) (hdeg : ∀ v, ∃ w, G.Adj v w) :
    Nonempty (G ≃g (⊤ : SimpleGraph (Fin n))) := by
  classical
  let _ := Fintype.ofFinite V
  have hinside : #(G.edgeFinset.filter (fun e => e.toFinset ⊆ s)) = n.choose 2 := by
    rw [card_filter_edgeFinset_toFinset_subset]
    rw [edgeFinset_card, Set.fintypeCard_eq_ncard, G.induce_eq_top.mpr hK.isClique,
      ← Set.fintypeCard_eq_ncard, ← edgeFinset_card,
      card_edgeFinset_top_eq_card_choose_two]
    exact congrArg (fun n => n.choose 2) ((Fintype.card_coe s).trans hK.card_eq)
  have heq : G.edgeFinset.filter (fun e => e.toFinset ⊆ s) = G.edgeFinset := by
    apply eq_of_subset_of_card_le (filter_subset _ _)
    rw [hinside, edgeFinset_card, Set.fintypeCard_eq_ncard]
    exact hbudget
  have hsu : s = univ := by
    apply eq_univ_of_forall
    intro v
    obtain ⟨w, hvw⟩ := hdeg v
    have hmem : s(v, w) ∈ G.edgeFinset := mem_edgeFinset.mpr hvw
    rw [← heq] at hmem
    exact (mem_filter.mp hmem).2 (by simp)
  have htop : G = ⊤ := isClique_univ.mp (by simpa only [hsu, coe_univ] using hK.isClique)
  have hcard : Fintype.card V = n := by simpa only [hsu, card_univ] using hK.card_eq
  rw [htop]
  exact ⟨Iso.completeGraph (Fintype.equivFinOfCardEq hcard)⟩

/-- The degree of a vertex induced on a finite set counts its neighbours in that set. -/
private lemma degree_induce_finset_eq {V : Type*} {G : SimpleGraph V}
    [DecidableRel G.Adj] (s : Finset V) (v : (s : Set V)) :
    (G.induce (s : Set V)).degree v = (s.filter (G.Adj v.val)).card := by
  classical
  rw [← card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun w _ => w.val)
  · intro w hw
    exact mem_filter.mpr ⟨w.property,
      ((G.induce (s : Set V)).mem_neighborFinset _ _).mp hw⟩
  · intro w _ w' _ he
    exact Subtype.ext he
  · intro x hx
    obtain ⟨hxs, hAdj⟩ := mem_filter.mp hx
    exact ⟨⟨x, hxs⟩, (mem_neighborFinset _ _ _).mpr hAdj, rfl⟩

/-- For `d ≥ 6`, the complete graph is the unique graph without isolated vertices at
`C(d + 2, 2)` edges that has no injective unit-distance placement in `ℝᵈ`. -/
theorem nonempty_iso_completeGraph_of_not_unitDistEmbeddable {V : Type} [Finite V]
    (G : SimpleGraph V) {d : ℕ} (hd : 6 ≤ d) (hemb : ¬ G.UnitDistEmbeddable d)
    (hcard : G.edgeSet.ncard = (d + 2).choose 2) (hdeg : ∀ v, ∃ w, G.Adj v w) :
    Nonempty (G ≃g (⊤ : SimpleGraph (Fin (d + 2)))) := by
  classical
  let _ := Fintype.ofFinite V
  obtain ⟨s, hsdeg, hsmax⟩ := exists_core_maximal (G := G) (d - 2)
  let H := G.induce (s : Set V)
  have hdegree (v : (s : Set V)) : d - 1 ≤ H.degree v := by
    have := hsdeg v.val v.property
    change d - 1 ≤ (G.induce (s : Set V)).degree v
    rw [degree_induce_finset_eq]
    omega
  have hdegSet (v : (s : Set V)) : d - 1 ≤ (H.neighborSet v).ncard := by
    simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hdegree v
  by_cases hT : (completeMinusTriangle (d + 2)).Free H
  · exfalso
    apply hemb
    by_cases hK : H.CliqueFree (d + 1)
    · have hH := SphereEmbeddable.of_fks_core_le_choose hd (fksStatement (by omega))
        hdegree ((ncard_edgeSet_induce_le G (s : Set V)).trans hcard.le) hK hT
      exact (SphereEmbeddable.of_core_maximal (by omega) hsmax hH).toUnitDist
    · exact UnitDistEmbeddable.of_core_containing_clique_le_choose (by omega)
        hdegSet hsmax hK hT hcard.le (by omega)
  · have hcopy : completeMinusTriangle (d + 2) ⊑ H := not_not.mp hT
    rcases unitDistEmbeddable_or_isNClique_of_core_completeMinusTriangle (by omega)
      s hdegSet hcopy hcard.le (by omega) with hplace | hclique
    · exact (hemb hplace).elim
    · exact nonempty_iso_completeGraph_of_isNClique hclique hcard.le hdeg

end SimpleGraph

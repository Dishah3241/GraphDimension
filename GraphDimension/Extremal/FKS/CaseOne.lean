/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.FKS.Counting

/-!
# Exclusion of FKS Case 1

Two cliques supplied by distinct non-neighbours force one of the two edge-count
contradictions, according to their intersection size. Maximum degree is not needed here:
the chosen vertex need only have degree at least `d` and a distinct non-neighbour.
-/

@[expose] public section

namespace SimpleGraph

open Finset

/-- Case 1 is impossible under its explicit edge budget and core hypotheses. -/
theorem not_forall_clique_of_edgeSet_ncard_lt {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ} (hd : 3 ≤ d)
    (hcard : d + 3 ≤ Fintype.card V) (hdeg : ∀ x, d - 1 ≤ G.degree x)
    (hbudget : G.edgeSet.ncard < (d + 2).choose 2 + d - 4)
    (hfree : G.CliqueFree (d + 1)) {v w : V} (hvw : v ≠ w)
    (hnadj : ¬ G.Adj v w) (hdv : d ≤ G.degree v) :
    ¬ (∀ x, x ≠ v → ¬ G.Adj v x →
      ∃ K : Finset V, G.IsNClique d K ∧ v ∉ K ∧ x ∉ K) := by
  classical
  intro hall
  obtain ⟨K, hK, hvK, -⟩ := hall w hvw.symm hnadj
  have hmiss : ∃ x ∈ K, ¬ G.Adj v x := by
    by_contra! h
    exact hfree _ (hK.insert (a := v) h)
  obtain ⟨x, hx, hnx⟩ := hmiss
  have hxv : x ≠ v := fun he => hvK (he ▸ hx)
  obtain ⟨K', hK', hvK', hxK'⟩ := hall x hxv hnx
  have hvU : v ∉ K ∪ K' := by simpa only [mem_union, not_or] using ⟨hvK, hvK'⟩
  have hchoose : 4 ≤ (d + 2).choose 2 :=
    (by decide : 4 ≤ (5 : ℕ).choose 2).trans (Nat.choose_le_choose 2 (by omega))
  by_cases hinter : #(K ∩ K') ≤ d - 2
  · have := card_edgeSet_ge_of_cliques_small_inter (by omega) hK hK' hinter hvU hdv
    omega
  have hinterlt : #(K ∩ K') < d := by
    have hsub : K ∩ K' ⊂ K := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨inter_subset_left, ?_⟩
      intro he
      have hx' : x ∈ K ∩ K' := he.symm ▸ hx
      exact hxK' (mem_inter.mp hx').2
    simpa only [hK.card_eq] using card_lt_card hsub
  have hintereq : #(K ∩ K') = d - 1 := by omega
  have hUcard : #(K ∪ K') = d + 1 := by
    have := card_union_add_card_inter K K'
    rw [hK.card_eq, hK'.card_eq, hintereq] at this
    omega
  have hleft : (univ \ insert v (K ∪ K')).Nonempty := by
    apply card_pos.mp
    rw [card_sdiff_of_subset (subset_univ _), card_univ,
      card_insert_of_notMem hvU, hUcard]
    omega
  obtain ⟨y, hy⟩ := hleft
  have hyU : y ∉ K ∪ K' := fun h => (mem_sdiff.mp hy).2 (mem_insert_of_mem h)
  have hvy : v ≠ y := by
    intro he
    exact (mem_sdiff.mp hy).2 (he ▸ mem_insert_self v (K ∪ K'))
  have hcount := card_edgeSet_ge_of_cliques_inter_pred (by omega) hK hK' hintereq
    hvU hyU hvy hdv (hdeg y)
  have hrec : (d + 2).choose 2 = (d + 1).choose 2 + (d + 1) := by
    rw [show d + 2 = (d + 1) + 1 by omega, Nat.choose_succ_succ,
      Nat.choose_one_right, Nat.add_comm]
  omega

/-- Some non-neighbour of a high-degree vertex leaves a `d`-clique-free two-vertex deletion. -/
theorem exists_cliqueFree_pair_of_edgeSet_ncard_lt {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ} (hd : 3 ≤ d)
    (hcard : d + 3 ≤ Fintype.card V) (hdeg : ∀ x, d - 1 ≤ G.degree x)
    (hbudget : G.edgeSet.ncard < (d + 2).choose 2 + d - 4)
    (hfree : G.CliqueFree (d + 1)) {v w : V} (hvw : v ≠ w)
    (hnadj : ¬ G.Adj v w) (hdv : d ≤ G.degree v) :
    ∃ x, x ≠ v ∧ ¬ G.Adj v x ∧ (G.induce {y | y ≠ v ∧ y ≠ x}).CliqueFree d := by
  classical
  by_contra! h
  apply not_forall_clique_of_edgeSet_ncard_lt hd hcard hdeg hbudget hfree hvw hnadj hdv
  intro x hx hnx
  have hnfree := h x hx hnx
  obtain ⟨K, hK⟩ := not_forall.mp hnfree
  have hK' : (G.induce {y | y ≠ v ∧ y ≠ x}).IsNClique d K := by simpa using hK
  refine ⟨K.map (.subtype _), (isNClique_induce_iff _ _ _).mp hK', ?_, ?_⟩
  · intro hv
    obtain ⟨y, -, hy⟩ := mem_map.mp hv
    exact y.property.1 hy
  · intro hx'
    obtain ⟨y, -, hy⟩ := mem_map.mp hx'
    exact y.property.2 hy

end SimpleGraph

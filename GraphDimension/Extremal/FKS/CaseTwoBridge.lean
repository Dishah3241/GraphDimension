/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.FKS.CaseTwoCount
public import GraphDimension.Extremal.FKS.CaseTwo
public import GraphDimension.Extremal.FKS.BranchC

/-!
# The repaired bridge for FKS Case 2

Equality of edge counts makes the two-vertex deletion an almost-complete copy together
with isolated vertices. In dimension four the core degree bound excludes these extra
vertices. In dimension three we instead delete the star centre and the original
maximum-degree vertex, leaving at most two edges for the inductive spherical placement.
-/

@[expose] public section

namespace SimpleGraph

open Finset

/-- A copy accounting for every edge describes adjacency even outside its vertex image. -/
theorem Copy.adj_iff_of_edgeSet_ncard_eq {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H)
    (hcard : G.edgeSet.ncard = H.edgeSet.ncard) (x y : W) :
    H.Adj x y ↔ ∃ i j, G.Adj i j ∧ f i = x ∧ f j = y := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite W
  have hsub : G.edgeFinset.image (Sym2.map (⇑f)) ⊆ H.edgeFinset := by
    rintro e he
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    exact mem_edgeFinset.mpr (f.toHom.map_mem_edgeSet (mem_edgeFinset.mp he'))
  have heq : G.edgeFinset.image (Sym2.map (⇑f)) = H.edgeFinset := by
    apply eq_of_subset_of_card_le hsub
    have hinj : Function.Injective (⇑f) := f.injective
    rw [card_image_of_injective _ (Sym2.map.injective hinj)]
    simpa only [edgeFinset_card, Set.fintypeCard_eq_ncard] using hcard.ge
  constructor
  · intro hxy
    have hm : s(x, y) ∈ G.edgeFinset.image (Sym2.map (⇑f)) :=
      heq.symm ▸ mem_edgeFinset.mpr hxy
    obtain ⟨e, he, hmap⟩ := mem_image.mp hm
    induction e using Sym2.ind with
    | _ i j =>
      have hij : G.Adj i j := mem_edgeFinset.mp he
      rcases Sym2.eq_iff.mp hmap with h | h
      · exact ⟨i, j, hij, h⟩
      · exact ⟨j, i, hij.symm, h.2, h.1⟩
  · rintro ⟨i, j, hij, rfl, rfl⟩
    exact f.toHom.map_rel' hij

/-- Fewer than three edges precludes a triangle. -/
private lemma fks_cliqueFree_of_edgeSet_ncard_le_two {V : Type*} [Finite V]
    {G : SimpleGraph V} (h : G.edgeSet.ncard ≤ 2) : G.CliqueFree 3 := by
  classical
  by_contra hn
  obtain ⟨f⟩ := (not_cliqueFree_iff_top_isContained 3).mp hn
  have hlow := ncard_edgeSet_le_of_copy f
  have he : (completeGraph (Fin 3)).edgeSet.ncard = 3 := by
    rw [← Set.fintypeCard_eq_ncard, ← edgeFinset_card]
    exact card_edgeFinset_top_eq_card_choose_two
  omega

/-- In dimension three, changing the deleted pair to the star centre and `v` repairs
the possible presence of isolated vertices in the original deletion. -/
private lemma fks_case_two_three {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (ih : FKSStatement 2) {v w : V}
    (hmax : ∀ x, G.degree x ≤ 3) (hdv : G.degree v = 3)
    (hbudget : G.edgeSet.ncard ≤ 8)
    (hcopy : completeMinusTriangle 4 ⊑ G.induce {x | x ≠ v ∧ x ≠ w}) :
    G.SphereEmbeddable 3 := by
  classical
  obtain ⟨f⟩ := hcopy
  let c : V := (f 3).val
  let L : Finset V := ((univ : Finset (Fin 4)).erase 3).image (fun i => (f i).val)
  have hinj : Function.Injective (fun i => (f i).val) :=
    fun _ _ he => f.injective (Subtype.ext he)
  have hLcard : L.card = 3 := by
    rw [card_image_of_injective _ hinj]
    decide
  have hLsub : L ⊆ G.neighborFinset c := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    apply (G.mem_neighborFinset _ _).mpr
    exact f.toHom.map_rel' ⟨(mem_erase.mp hi).1.symm, by simp⟩
  have hLeq : L = G.neighborFinset c := eq_of_subset_of_card_le hLsub (by
    rw [card_neighborFinset_eq_degree, hLcard]
    exact hmax c)
  have hdc : G.degree c = 3 := by
    rw [← card_neighborFinset_eq_degree, ← hLeq, hLcard]
  have hcv : c ≠ v := (f 3).property.1
  have hnadj : ¬ G.Adj c v := by
    intro h
    have hvL : v ∈ L := hLeq.symm ▸ (G.mem_neighborFinset _ _).mpr h
    obtain ⟨i, -, hi⟩ := mem_image.mp hvL
    exact (f i).property.1 hi
  let J := G.induce {x | x ≠ c ∧ x ≠ v}
  have hE : J.edgeSet.ncard ≤ 2 := by
    dsimp [J]
    rw [ncard_edgeSet_induce_ne_pair G hcv hnadj, hdc, hdv]
    omega
  have hT : (completeMinusTriangle 4).Free J := by
    rintro ⟨g⟩
    have := ncard_edgeSet_le_of_copy g
    rw [card_edgeFinset_completeMinusTriangle (by decide)] at this
    norm_num [Nat.choose] at this
    omega
  have hs := (ih _ J (hE.trans (by decide))).2
    (fks_cliqueFree_of_edgeSet_ncard_le_two hE) hT
  exact hs.poles hcv hnadj

/-- In dimension four every vertex of the core belongs to the copy or the deleted pair. -/
private lemma fks_case_two_four {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {v w : V} (hvw : v ≠ w) (hnadj : ¬ G.Adj v w)
    (hdeg : ∀ x, 3 ≤ G.degree x) (hdv : G.degree v = 4) (hdw : G.degree w = 3)
    (hE : (G.induce {x | x ≠ v ∧ x ≠ w}).edgeSet.ncard = 7)
    (hcopy : completeMinusTriangle 5 ⊑ G.induce {x | x ≠ v ∧ x ≠ w}) :
    G.SphereEmbeddable 4 := by
  classical
  obtain ⟨f⟩ := hcopy
  have heq : (completeMinusTriangle 5).edgeSet.ncard =
      (G.induce {x | x ≠ v ∧ x ≠ w}).edgeSet.ncard := by
    rw [card_edgeFinset_completeMinusTriangle (by decide), hE]
    decide
  have hsurj : Function.Surjective f := by
    intro x
    by_contra hx
    have hsub : G.neighborFinset x.val ⊆ {v, w} := by
      intro y hy
      by_contra hy'
      have hyne : y ≠ v ∧ y ≠ w := by simpa using hy'
      have hadj : (G.induce {x | x ≠ v ∧ x ≠ w}).Adj x ⟨y, hyne⟩ :=
        (G.mem_neighborFinset _ _).mp hy
      obtain ⟨i, j, -, hi, -⟩ := (f.adj_iff_of_edgeSet_ncard_eq heq _ _).mp hadj
      exact hx ⟨i, hi⟩
    have hc := card_le_card hsub
    rw [card_neighborFinset_eq_degree, card_pair hvw] at hc
    have := hdeg x.val
    omega
  let p : Fin 5 ↪ V := ⟨fun i => (f i).val,
    fun _ _ he => f.injective (Subtype.ext he)⟩
  let B : Finset V := univ.map p
  have hvB : v ∉ B := by
    intro h
    obtain ⟨i, -, hi⟩ := mem_map.mp h
    exact (f i).property.1 hi
  have hwB : w ∉ B := by
    intro h
    obtain ⟨i, -, hi⟩ := mem_map.mp h
    exact (f i).property.2 hi
  have hcover : (univ : Finset V) = insert v (insert w B) := by
    ext x
    simp only [mem_univ, true_iff, mem_insert]
    by_cases hxv : x = v
    · exact Or.inl hxv
    by_cases hxw : x = w
    · exact Or.inr (Or.inl hxw)
    obtain ⟨i, hi⟩ := hsurj ⟨x, hxv, hxw⟩
    exact Or.inr (Or.inr (mem_map.mpr ⟨i, mem_univ _, congrArg Subtype.val hi⟩))
  have hcard : Fintype.card V = 4 + 3 := by
    rw [← card_univ, hcover, card_insert_of_notMem (by simp [hvw, hvB]),
      card_insert_of_notMem hwB]
    simp [B]
  let T : Finset V := ((univ : Finset (Fin 5)).filter (fun i => i.val < 3)).map p
  have hT : T.card = 3 := by rw [card_map]; decide
  have hTvw : v ∉ T ∧ w ∉ T := by
    have hsub : T ⊆ B := map_subset_map.mpr (filter_subset _ _)
    exact ⟨fun h => hvB (hsub h), fun h => hwB (hsub h)⟩
  have hmem (i : Fin 5) : p i ∈ T ↔ i.val < 3 := by simp [T]
  apply SphereEmbeddable.of_case_two (by decide) hvw hnadj hcard T hT hTvw
    ?_ hdv hdw
  intro x y hxy hxv hxw hyv hyw
  obtain ⟨i, hi⟩ := hsurj ⟨x, hxv, hxw⟩
  obtain ⟨j, hj⟩ := hsurj ⟨y, hyv, hyw⟩
  have hpx : p i = x := congrArg Subtype.val hi
  have hpy : p j = y := congrArg Subtype.val hj
  rw [← hpx, ← hpy, hmem, hmem]
  have hiff := f.adj_iff_of_edgeSet_ncard_eq heq (f i) (f j)
  constructor
  · intro hadj
    obtain ⟨a, b, hab, ha, hb⟩ := hiff.mp hadj
    have hai := f.injective ha
    have hbj := f.injective hb
    subst a
    subst b
    exact hab.2
  · intro h
    exact f.toHom.map_rel' ⟨fun hij => hxy (hpx.symm.trans
      ((congrArg p hij).trans hpy)), h⟩

/-- FKS Case 2, including the repaired dimension-three argument. -/
theorem SphereEmbeddable.of_fks_case_two {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hd : 3 ≤ d) (ih : FKSStatement (d - 1))
    {v w : V} (hvw : v ≠ w) (hnadj : ¬ G.Adj v w)
    (hmax : ∀ x, G.degree x ≤ G.degree v) (hdv : d ≤ G.degree v)
    (hdeg : ∀ x, d - 1 ≤ G.degree x) (hbudget : G.edgeSet.ncard ≤ fksBudget d)
    (hcopy : completeMinusTriangle (d + 1) ⊑ G.induce {x | x ≠ v ∧ x ≠ w}) :
    G.SphereEmbeddable d := by
  classical
  obtain ⟨hd4, hv, hw, hE, -⟩ :=
    fks_case_two_degrees hd hvw hnadj hdv (hdeg w) hbudget hcopy
  interval_cases d
  · exact fks_case_two_three ih (fun x => (hmax x).trans_eq hv) hv hbudget hcopy
  · exact fks_case_two_four hvw hnadj hdeg hv hw hE hcopy

end SimpleGraph

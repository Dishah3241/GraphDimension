/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.FKS.BranchC
import Mathlib.Tactic.FinCases

/-!
# FKS's small-core branch

On `d + 2` vertices a core has at most two missing neighbours per vertex. If there are
no two disjoint missing edges, all missing edges lie in one triangle.
-/

@[expose] public section

namespace SimpleGraph

open Finset

/-- If every missing edge has both ends in a fixed triangle, the graph contains `K_n − K₃`. -/
theorem completeMinusTriangle_isContained_of_missing_edges_in_triangle {V : Type*}
    [Fintype V] {G : SimpleGraph V} {n : ℕ} (hcard : Fintype.card V = n)
    {T : Finset V} (hT : T.card = 3)
    (hadj : ∀ x y, x ≠ y → ¬ (x ∈ T ∧ y ∈ T) → G.Adj x y) :
    completeMinusTriangle n ⊑ G := by
  classical
  let R := univ \ T
  have hR : R.card = n - 3 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hT, hcard]
  let eT : Fin 3 ≃ T := (equivFinOfCardEq hT).symm
  let eR : Fin (n - 3) ≃ R := (equivFinOfCardEq hR).symm
  let f (i : Fin n) : V :=
    if hi : i.val < 3 then (eT ⟨i.val, hi⟩).val
    else (eR ⟨i.val - 3, by omega⟩).val
  have hmem (i : Fin n) : f i ∈ T ↔ i.val < 3 := by
    dsimp only [f]
    split_ifs with hi
    · exact iff_of_true (eT _).property hi
    · exact iff_of_false (mem_sdiff.mp (eR _).property).2 hi
  have hinj : Function.Injective f := by
    intro i j he
    by_cases hi : i.val < 3 <;> by_cases hj : j.val < 3
    · simp only [f, dite_eq_left hi, dite_eq_left hj] at he
      exact Fin.ext (congrArg (fun z : Fin 3 => z.val) (eT.injective (Subtype.ext he)))
    · exact (hj ((hmem j).mp (he ▸ (hmem i).mpr hi))).elim
    · exact (hi ((hmem i).mp (he.symm ▸ (hmem j).mpr hj))).elim
    · simp only [f, dite_eq_right hi, dite_eq_right hj] at he
      have hval := congrArg Fin.val (eR.injective (Subtype.ext he))
      exact Fin.ext (by dsimp at hval; omega)
  refine ⟨{ toHom := { toFun := f, map_rel' := ?_ }, injective' := hinj }⟩
  intro i j hij
  exact hadj _ _ (fun he => hij.1 (hinj he))
    (fun h => hij.2 ⟨(hmem i).mp h.1, (hmem j).mp h.2⟩)

/-- Branch C for all cores on at most `d + 2` vertices, without an edge-budget assumption. -/
theorem SphereEmbeddable.of_fks_small_core {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hd : 2 ≤ d) (hcard : Fintype.card V ≤ d + 2)
    (hdeg : ∀ v, d - 1 ≤ G.degree v) (hK : G.CliqueFree (d + 1))
    (hT : (completeMinusTriangle (d + 2)).Free G) : G.SphereEmbeddable d := by
  classical
  by_cases hsmall : Fintype.card V ≤ d + 1
  · exact SphereEmbeddable.of_cliqueFree_card_le (by omega) hsmall hK
  have hcard' : Fintype.card V = d + 2 := by omega
  by_cases hmatch : ∃ a b c e : V, a ≠ b ∧ c ≠ e ∧ a ≠ c ∧ a ≠ e ∧ b ≠ c ∧ b ≠ e ∧
      ¬ G.Adj a b ∧ ¬ G.Adj c e
  · obtain ⟨a, b, c, e, hab, hce, hac, hae, hbc, hbe, hnab, hnce⟩ := hmatch
    apply SphereEmbeddable.of_compl_matching hd hcard ![a, c] ![b, e]
    · intro i j hij
      cases i with
      | inl i =>
        cases j with
        | inl j => fin_cases i <;> fin_cases j <;> simp_all
        | inr j => fin_cases i <;> fin_cases j <;> simp_all
      | inr i =>
        cases j with
        | inl j => fin_cases i <;> fin_cases j <;> simp_all
        | inr j => fin_cases i <;> fin_cases j <;> simp_all
    · intro i; fin_cases i <;> assumption
  have hmiss (v : V) : ∃ a b, a ≠ v ∧ b ≠ v ∧ a ≠ b ∧ ¬ G.Adj a b := by
    by_contra! h
    apply hK (univ.erase v)
    refine ⟨?_, by simp [hcard']⟩
    intro a ha b hb hab
    exact h a b (mem_erase.mp ha).1 (mem_erase.mp hb).1 hab
  have hnonempty : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := hnonempty
  obtain ⟨a, b, -, -, hab, hnab⟩ := hmiss v
  obtain ⟨x, y, hxa, hya, hxy, hnxy⟩ := hmiss a
  have hbc : ∃ c, c ≠ a ∧ c ≠ b ∧ ¬ G.Adj b c := by
    by_cases hbx : b = x
    · subst x
      exact ⟨y, hya, hxy.symm, hnxy⟩
    · by_cases hby : b = y
      · subst y
        exact ⟨x, hxa, hxy, fun h => hnxy h.symm⟩
      · exact (hmatch ⟨a, b, x, y, hab, hxy, hxa.symm, hya.symm, hbx, hby,
          hnab, hnxy⟩).elim
  obtain ⟨c, hca, hcb, hnbc⟩ := hbc
  have hboutside : ∀ y, y ≠ a → y ≠ b → y ≠ c → G.Adj b y := by
    intro y hya hyb hyc
    by_contra hnby
    have hN : G.neighborFinset b ⊆ univ \ {a, b, c, y} := by
      intro z hz
      have hbz : G.Adj b z := by simpa only [mem_neighborFinset] using hz
      refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
      simp only [mem_insert, mem_singleton]
      rintro (rfl | rfl | rfl | rfl)
      · exact hnab hbz.symm
      · exact hbz.ne rfl
      · exact hnbc hbz
      · exact hnby hbz
    have hc4 : ({a, b, c, y} : Finset V).card = 4 := by
      simp [hab, hca.symm, hcb.symm, hya.symm, hyb.symm, hyc.symm]
    have hbound := card_le_card hN
    rw [card_neighborFinset_eq_degree, card_sdiff_of_subset (subset_univ _), card_univ,
      hc4, hcard'] at hbound
    have := hdeg b
    omega
  have hmeet {x y z t : V} (hxy : x ≠ y) (hzt : z ≠ t)
      (hnxy : ¬ G.Adj x y) (hnzt : ¬ G.Adj z t) :
      x = z ∨ x = t ∨ y = z ∨ y = t := by
    by_contra! h
    exact hmatch ⟨x, y, z, t, hxy, hzt, h.1, h.2.1, h.2.2.1, h.2.2.2, hnxy, hnzt⟩
  apply (hT ?_).elim
  apply completeMinusTriangle_isContained_of_missing_edges_in_triangle hcard'
    (T := {a, b, c}) (by simp [hab, hca.symm, hcb.symm])
  intro x y hxy hnot
  by_contra hnxy
  have hm1 := hmeet hab hxy hnab hnxy
  have hm2 := hmeet hcb.symm hxy hnbc hnxy
  have hxb : x ≠ b := by
    intro he; subst x
    have hout : y ≠ a ∧ y ≠ b ∧ y ≠ c := by simpa using hnot
    exact hnxy (hboutside y hout.1 hout.2.1 hout.2.2)
  have hyb : y ≠ b := by
    intro he; subst y
    have hout : x ≠ a ∧ x ≠ b ∧ x ≠ c := by simpa using hnot
    exact hnxy (hboutside x hout.1 hout.2.1 hout.2.2).symm
  apply hnot
  simp only [mem_insert, mem_singleton]
  rcases hm1 with rfl | rfl | he | he <;>
    rcases hm2 with he' | he' | he' | he' <;> aesop

end SimpleGraph

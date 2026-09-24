/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.FKS.Budget
public import GraphDimension.Extremal.FKS.Counting
public import GraphDimension.Geometry.TwoSimplices

/-!
# FKS Branch A

A core containing `K_{d+2} − K₃` has exactly those vertices. A missing edge gives a
two-simplex placement, and the strict complete-graph budget leaves at most two tail edges.
-/

@[expose] public section

namespace SimpleGraph

open Finset

/-- An injective graph homomorphism cannot decrease the number of edges. -/
theorem ncard_edgeSet_le_of_copy {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite W
  have hsub : G.edgeFinset.image (Sym2.map (⇑f)) ⊆ H.edgeFinset := by
    rintro e he
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    exact mem_edgeFinset.mpr (f.toHom.map_mem_edgeSet (mem_edgeFinset.mp he'))
  have hcard := card_le_card hsub
  have hinj : Function.Injective (⇑f) := f.injective
  rw [card_image_of_injective _ (Sym2.map.injective hinj)] at hcard
  simpa only [edgeFinset_card, Set.fintypeCard_eq_ncard] using hcard

/-- Taking an induced subgraph cannot increase the number of edges. -/
theorem ncard_edgeSet_induce_le {V : Type*} [Finite V] (G : SimpleGraph V) (s : Set V) :
    (G.induce s).edgeSet.ncard ≤ G.edgeSet.ncard := by
  exact ncard_edgeSet_le_of_copy
    { toHom := { toFun := Subtype.val, map_rel' := fun h => h }
      injective' := Subtype.val_injective }

/-- Branch A: a core containing the almost-complete obstruction is Euclidean embeddable
together with its tail. The two explicit budget inequalities also support other budgets. -/
theorem UnitDistEmbeddable.of_core_completeMinusTriangle {V : Type*} [Finite V]
    {G : SimpleGraph V} {d : ℕ} (hd : 3 ≤ d) (s : Finset V)
    (hdeg : ∀ v : (s : Set V), d - 1 ≤ ((G.induce ↑s).neighborSet v).ncard)
    (hcopy : completeMinusTriangle (d + 2) ⊑ G.induce ↑s)
    (hbudget : G.edgeSet.ncard < (d + 2).choose 2)
    (hcount : G.edgeSet.ncard < (d + 2).choose 2 + d - 4) :
    G.UnitDistEmbeddable d := by
  classical
  let _ := Fintype.ofFinite V
  let H := G.induce (s : Set V)
  obtain ⟨f⟩ := hcopy
  have hHle : H.edgeSet.ncard ≤ G.edgeSet.ncard := ncard_edgeSet_induce_le G ↑s
  have hchoose : 3 ≤ (d + 2).choose 2 := by
    exact (by decide : 3 ≤ (5 : ℕ).choose 2).trans
      (Nat.choose_le_choose 2 (by omega))
  have hsurj : Function.Surjective f := by
    intro v
    by_contra hv
    have hdeg' : d - 1 ≤ H.degree v := by
      simpa only [← H.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hdeg v
    have hlow := card_edgeSet_ge_of_copy_add_vertex hd f hv hdeg'
    change (d + 2).choose 2 - 3 + (d - 1) ≤ H.edgeSet.ncard at hlow
    omega
  let e : Fin (d + 2) ≃ (s : Set V) := Equiv.ofBijective f ⟨f.injective, hsurj⟩
  have hcard : Fintype.card (s : Set V) = d + 2 := by
    simpa using (Fintype.card_congr e).symm
  have hnotTop : H ≠ ⊤ := by
    intro htop
    have hcardE : H.edgeSet.ncard = (d + 2).choose 2 := by
      rw [htop, ← Set.fintypeCard_eq_ncard, ← edgeFinset_card,
        card_edgeFinset_top_eq_card_choose_two, hcard]
    omega
  have hmissing : ∃ a b, a ≠ b ∧ ¬ H.Adj (e a) (e b) := by
    by_contra! h
    apply hnotTop
    apply top_unique
    intro x y hxy
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    exact h a b (fun hab => hxy.ne (congrArg e hab))
  obtain ⟨a, b, hab, hnab⟩ := hmissing
  obtain ⟨p, hpInj, hpDist, -, hpClose⟩ := exists_twoSimplices_placement (by omega) hab
  let q : ↥(s : Set V) → EuclideanSpace ℝ (Fin d) := p ∘ e.symm
  have hqDist : ∀ x y, H.Adj x y → dist (q x) (q y) = 1 := by
    intro x y hxy
    apply hpDist
    · exact fun h => hxy.ne (e.symm.injective h)
    · rintro ⟨hx, hy⟩
      apply hnab
      simpa only [← hx, ← hy, e.apply_symm_apply] using hxy
    · rintro ⟨hx, hy⟩
      apply hnab
      simpa only [← hx, ← hy, e.apply_symm_apply] using hxy.symm
  have hqClose : ∀ x y, dist (q x) (q y) < 2 := by
    intro x y
    by_cases hxy : e.symm x = e.symm y
    · simp [q, Function.comp_def, hxy]
    · by_cases hab' : e.symm x = a ∧ e.symm y = b
      · simpa [q, Function.comp_def, hab'.1, hab'.2] using hpClose
      · by_cases hba' : e.symm x = b ∧ e.symm y = a
        · simpa [q, Function.comp_def, hba'.1, hba'.2, dist_comm] using hpClose
        · change dist (p (e.symm x)) (p (e.symm y)) < 2
          rw [hpDist _ _ hxy hab' hba']; norm_num
  have hlow : (d + 2).choose 2 - 3 ≤ H.edgeSet.ncard := by
    have := ncard_edgeSet_le_of_copy f
    rwa [card_edgeFinset_completeMinusTriangle (by omega)] at this
  let tail := G.edgeFinset.filter fun edge => ¬ edge.toFinset ⊆ s
  have hpartition : #tail + #H.edgeFinset = #G.edgeFinset := by
    have := card_filter_add_card_filter_not (s := G.edgeFinset)
      (fun edge => edge.toFinset ⊆ s)
    rw [card_filter_edgeFinset_toFinset_subset] at this
    exact this.symm.trans (Nat.add_comm _ _).symm |>.symm
  have htail : #tail ≤ 2 := by
    simp only [edgeFinset_card, Set.fintypeCard_eq_ncard] at hpartition
    omega
  apply UnitDistEmbeddable.extend_tail hd q (hpInj.comp e.symm.injective) hqDist hqClose
  refine ⟨tail, htail, ?_⟩
  intro x y hxy hnot
  have hsub : (s(x, y)).toFinset ⊆ s := by
    by_contra h
    exact hnot (mem_filter.mpr ⟨mem_edgeFinset.mpr hxy, h⟩)
  exact ⟨hsub (by simp), hsub (by simp)⟩

end SimpleGraph

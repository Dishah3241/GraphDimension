/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.FKS.Theorem3
public import GraphDimension.Geometry.TailThree
public import GraphDimension.Geometry.ExtendClique

/-!
# The equality budget in the FKS branches

At `C(d + 2, 2)` edges the spherical branch closes for `d ≥ 6`. The almost-complete
core either is a complete graph or admits the two-simplex placement with a three-edge tail.
The clique branch also admits the case where every clique vertex has an outside neighbour.
-/

@[expose] public section

namespace SimpleGraph

open Finset

/-- The spherical branch for a core avoiding both FKS obstructions. -/
theorem SphereEmbeddable.of_fks_core_le_choose {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hd : 6 ≤ d) (ih : FKSStatement (d - 1))
    (hdeg : ∀ x, d - 1 ≤ G.degree x) (hbudget : G.edgeSet.ncard ≤ (d + 2).choose 2)
    (hK : G.CliqueFree (d + 1)) (hT : (completeMinusTriangle (d + 2)).Free G) :
    G.SphereEmbeddable d := by
  classical
  have hrec : (d + 2).choose 2 = (d + 1).choose 2 + (d + 1) := by
    rw [show d + 2 = (d + 1) + 1 by omega, Nat.choose_succ_succ,
      Nat.choose_one_right, Nat.add_comm]
  have hpred : G.edgeSet.ncard ≤ fksBudget (d - 1) + (d + 2) := by
    rw [fksBudget_of_four_le (by omega), show d - 1 + 2 = d + 1 by omega]
    have := Nat.choose_pos (show 2 ≤ d + 1 by omega)
    omega
  by_cases hsmall : Fintype.card V ≤ d + 2
  · exact SphereEmbeddable.of_fks_small_core (by omega) hsmall hdeg hK hT
  have hcard : d + 3 ≤ Fintype.card V := by omega
  by_cases hlow : ∀ x, G.degree x + 1 ≤ d
  · exact SphereEmbeddable.of_degree_le (by omega) hlow
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hmax (x : V) : G.degree x ≤ G.degree v := hv ▸ G.degree_le_maxDegree x
  have hdv : d ≤ G.degree v := by
    push Not at hlow
    obtain ⟨x, hx⟩ := hlow
    have := hmax x
    omega
  by_cases huni : ∀ x, x ≠ v → G.Adj v x
  · have hvdeg : G.degree v = Fintype.card V - 1 :=
      (G.degree_eq_card_sub_one v).mpr (fun _ hx => huni _ hx.symm)
    exact SphereEmbeddable.of_fks_pole (by omega) ih huni (by omega)
      hpred hK hT
  push Not at huni
  obtain ⟨w, hwv, hn⟩ := huni
  obtain ⟨x, hxv, hnx, hKx⟩ := exists_cliqueFree_pair_of_edgeSet_ncard_lt (by omega) hcard hdeg
    (by omega) hK hwv.symm hn hdv
  by_cases hTx : (completeMinusTriangle (d + 1)).Free
      (G.induce {y | y ≠ v ∧ y ≠ x})
  · exact SphereEmbeddable.of_fks_poles (by omega) ih hxv.symm hnx hdv (hdeg x)
      (by omega) hKx hTx
  · obtain ⟨f⟩ := not_not.mp hTx
    let g : (completeMinusTriangle (d + 1)).Copy G :=
      (Copy.induce G {y | y ≠ v ∧ y ≠ x}).comp f
    have hcount := card_edgeSet_ge_of_copy_two_external (by omega : 3 ≤ d)
      hxv.symm hnx hdv (hdeg x) g (fun i => (f i).property)
    have hchoose : 3 ≤ (d + 1).choose 2 :=
      (by decide : 3 ≤ (3 : ℕ).choose 2).trans (Nat.choose_le_choose 2 (by omega))
    omega

/-- At the complete-graph budget, Branch A either places the core and its three-edge tail,
or the core is a complete graph on `d + 2` vertices. -/
theorem unitDistEmbeddable_or_isNClique_of_core_completeMinusTriangle {V : Type*} [Finite V]
    {G : SimpleGraph V} {d : ℕ} (hd : 4 ≤ d) (s : Finset V)
    (hdeg : ∀ v : (s : Set V), d - 1 ≤ ((G.induce ↑s).neighborSet v).ncard)
    (hcopy : completeMinusTriangle (d + 2) ⊑ G.induce ↑s)
    (hbudget : G.edgeSet.ncard ≤ (d + 2).choose 2)
    (hcount : G.edgeSet.ncard < (d + 2).choose 2 + d - 4) :
    G.UnitDistEmbeddable d ∨ G.IsNClique (d + 2) s := by
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
    have hlow := card_edgeSet_ge_of_copy_add_vertex (by omega) f hv hdeg'
    change (d + 2).choose 2 - 3 + (d - 1) ≤ H.edgeSet.ncard at hlow
    omega
  let e : Fin (d + 2) ≃ (s : Set V) := Equiv.ofBijective f ⟨f.injective, hsurj⟩
  have hcard : Fintype.card (s : Set V) = d + 2 := by
    simpa using (Fintype.card_congr e).symm
  by_cases htop : H = ⊤
  · exact Or.inr ⟨G.induce_eq_top.mp htop, (Fintype.card_coe s).symm.trans hcard⟩
  apply Or.inl
  have hmissing : ∃ a b, a ≠ b ∧ ¬ H.Adj (e a) (e b) := by
    by_contra! h
    apply htop
    apply top_unique
    intro x y hxy
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    exact h a b (fun hab => hxy.ne (congrArg e hab))
  obtain ⟨a, b, hab, hnab⟩ := hmissing
  obtain ⟨p, hpInj, hpDist, hpApex, hpClose⟩ := exists_twoSimplices_placement (by omega) hab
  let q : ↥(s : Set V) → EuclideanSpace ℝ (Fin d) := p ∘ e.symm
  have hqDist : ∀ x y, H.Adj x y → Dist.dist (q x) (q y) = 1 := by
    intro x y hxy
    apply hpDist
    · exact fun h => hxy.ne (e.symm.injective h)
    · rintro ⟨hx, hy⟩
      apply hnab
      simpa only [← hx, ← hy, e.apply_symm_apply] using hxy
    · rintro ⟨hx, hy⟩
      apply hnab
      simpa only [← hx, ← hy, e.apply_symm_apply] using hxy.symm
  have hqClose : ∀ x y, Dist.dist (q x) (q y) < 2 := by
    intro x y
    by_cases hxy : e.symm x = e.symm y
    · simp [q, Function.comp_def, hxy]
    · by_cases hab' : e.symm x = a ∧ e.symm y = b
      · simpa [q, Function.comp_def, hab'.1, hab'.2] using hpClose
      · by_cases hba' : e.symm x = b ∧ e.symm y = a
        · simpa [q, Function.comp_def, hba'.1, hba'.2, _root_.dist_comm] using hpClose
        · change Dist.dist (p (e.symm x)) (p (e.symm y)) < 2
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
  have htail : #tail ≤ 3 := by
    simp only [edgeFinset_card, Set.fintypeCard_eq_ncard] at hpartition
    omega
  have hqTriple : ∀ x y z : ↥(s : Set V), x ≠ y → y ≠ z → x ≠ z →
      {p | Dist.dist p (q x) = 1 ∧ Dist.dist p (q y) = 1 ∧ Dist.dist p (q z) = 1}.Infinite := by
    intro x y z hxy hyz hxz
    exact infinite_common_unit_sphere_twoSimplices hd p hab hpDist hpApex
      (e.symm x) (e.symm y) (e.symm z) (e.symm.injective.ne hxy)
      (e.symm.injective.ne hyz) (e.symm.injective.ne hxz)
  apply UnitDistEmbeddable.extend_tail_three hd q (hpInj.comp e.symm.injective)
    hqDist hqClose hqTriple
  refine ⟨tail, htail, ?_⟩
  intro x y hxy hnot
  have hsub : (s(x, y)).toFinset ⊆ s := by
    by_contra h
    exact hnot (mem_filter.mpr ⟨mem_edgeFinset.mpr hxy, h⟩)
  exact ⟨hsub (by simp), hsub (by simp)⟩


/-- A clique core with a vertex having no outside neighbour admits the off-sphere apex
construction, independently of the number of tail edges. -/
theorem UnitDistEmbeddable.of_core_clique_without_external_neighbor
    {V : Type*} [Finite V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hd : 2 ≤ d) {s : Finset V}
    (hK : G.IsNClique (d + 1) s)
    (hmax : ∀ t : Finset V, (∀ v ∈ t, d - 2 < (t.filter (G.Adj v)).card) → t ⊆ s)
    {v : V} (hv : v ∈ s) (hN : ∀ w, G.Adj v w → w ∈ s) :
    G.UnitDistEmbeddable d := by
  classical
  let _ := Fintype.ofFinite V
  have hsCard : (s.erase v).card = d := by rw [card_erase_of_mem hv, hK.card_eq]; omega
  have hK' : G.IsNClique d (s.erase v) :=
    ⟨fun _ ha _ hb hab => hK.isClique (mem_erase.mp ha).2 (mem_erase.mp hb).2 hab, hsCard⟩
  apply UnitDistEmbeddable.of_spherical_delete_clique (by omega) hK' (by simp)
    (fun w hw => mem_erase.mpr ⟨hw.ne.symm, hN w hw⟩)
  obtain ⟨c, hct, hc, hext⟩ := SphereEmbeddable.exists_core_subset (G := G) hd (univ.erase v)
  have hcs : c ⊆ s.erase v := by
    intro w hw
    exact mem_erase.mpr ⟨(mem_erase.mp (hct hw)).1, hmax c hc hw⟩
  have hcard : Fintype.card ↥(c : Set V) ≤ d := by
    calc
      Fintype.card ↥(c : Set V) = c.card := Fintype.card_coe c
      _ ≤ (s.erase v).card := card_le_card hcs
      _ = d := hsCard
  have hplace := hext (SphereEmbeddable.of_card_le hcard)
  have heq : ((univ.erase v : Finset V) : Set V) = {w | w ≠ v} := by ext; simp
  rwa [heq] at hplace


/-- At most `d + 1` edges outside a maximal `(d + 1)`-clique still admit a placement.
If every clique vertex meets the outside, these edges exhaust the tail; each outside
neighbourhood is then a small clique. -/
theorem UnitDistEmbeddable.of_core_clique_le_choose {V : Type*} [Finite V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ} (hd : 2 ≤ d) {s : Finset V}
    (hK : G.IsNClique (d + 1) s)
    (hmax : ∀ t : Finset V, (∀ v ∈ t, d - 2 < (t.filter (G.Adj v)).card) → t ⊆ s)
    (hbudget : G.edgeSet.ncard ≤ (d + 1).choose 2 + (d + 1)) :
    G.UnitDistEmbeddable d := by
  classical
  let _ := Fintype.ofFinite V
  by_cases hfree : ∃ v ∈ s, ∀ w, G.Adj v w → w ∈ s
  · obtain ⟨v, hv, hN⟩ := hfree
    exact UnitDistEmbeddable.of_core_clique_without_external_neighbor hd hK hmax hv hN
  push Not at hfree
  choose w hwadj hwout using fun v : s => hfree v v.property
  let edges : s → Sym2 V := fun v => s(v.val, w v)
  have hinj : Function.Injective edges := by
    intro v v' he
    rcases Sym2.eq_iff.mp he with ⟨hvv', -⟩ | ⟨hvw, -⟩
    · exact Subtype.ext hvv'
    · exact (hwout v' (hvw ▸ v.property)).elim
  let tail := G.edgeFinset.filter fun e => ¬ e.toFinset ⊆ s
  have hsub : univ.image edges ⊆ tail := by
    intro e he
    obtain ⟨v, -, rfl⟩ := mem_image.mp he
    refine mem_filter.mpr ⟨mem_edgeFinset.mpr (hwadj v), ?_⟩
    intro hsub
    exact hwout v (hsub (by simp [edges]))
  have hinside : #(G.edgeFinset.filter (fun e => e.toFinset ⊆ s)) = (d + 1).choose 2 := by
    rw [card_filter_edgeFinset_toFinset_subset]
    rw [edgeFinset_card, Set.fintypeCard_eq_ncard, G.induce_eq_top.mpr hK.isClique,
      ← Set.fintypeCard_eq_ncard, ← edgeFinset_card,
      card_edgeFinset_top_eq_card_choose_two]
    exact congrArg (fun n => n.choose 2) ((Fintype.card_coe s).trans hK.card_eq)
  have hpart := card_filter_add_card_filter_not (s := G.edgeFinset)
    (fun e => e.toFinset ⊆ s)
  have htail : #tail ≤ d + 1 := by
    rw [hinside, edgeFinset_card, Set.fintypeCard_eq_ncard] at hpart
    change (d + 1).choose 2 + #tail = G.edgeSet.ncard at hpart
    omega
  have heq : univ.image edges = tail := eq_of_subset_of_card_le hsub (by
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_coe, hK.card_eq]
    exact htail)
  have hN : ∀ u, u ∉ s → ∀ v, G.Adj u v → v ∈ s := by
    intro u hu v huv
    have hmem : s(u, v) ∈ tail := mem_filter.mpr ⟨mem_edgeFinset.mpr huv,
      fun h => hu (h (by simp))⟩
    rw [← heq] at hmem
    obtain ⟨x, -, hx⟩ := mem_image.mp hmem
    rcases Sym2.eq_iff.mp hx with ⟨hxu, -⟩ | ⟨hxv, -⟩
    · exact (hu (hxu ▸ x.property)).elim
    · exact hxv ▸ x.property
  have hsmall : ∀ u, u ∉ s → (G.neighborSet u).ncard + 1 ≤ d := by
    intro u hu
    by_contra hlarge
    have hlarge' : d - 2 < (G.neighborFinset u).card := by
      simpa only [card_neighborFinset_eq_degree, ← card_neighborSet_eq_degree,
        Set.fintypeCard_eq_ncard] using (show d - 2 < (G.neighborSet u).ncard by omega)
    have hcore : ∀ v ∈ insert u s, d - 2 < ((insert u s).filter (G.Adj v)).card := by
      intro v hv
      rcases mem_insert.mp hv with hv | hv
      · subst v
        have he : (insert u s).filter (G.Adj u) = G.neighborFinset u := by
          ext v
          simp only [mem_filter, mem_insert, mem_neighborFinset]
          exact ⟨And.right, fun hv => ⟨Or.inr (hN u hu v hv), hv⟩⟩
        rwa [he]
      · have hsub' : s.erase v ⊆ (insert u s).filter (G.Adj v) := by
          intro x hx
          obtain ⟨hxv, hxs⟩ := mem_erase.mp hx
          exact mem_filter.mpr ⟨mem_insert_of_mem hxs, hK.isClique hv hxs hxv.symm⟩
        have hc := card_le_card hsub'
        rw [card_erase_of_mem hv, hK.card_eq] at hc
        omega
    exact hu (hmax (insert u s) hcore (mem_insert_self _ _))
  have hs : (G.induce (s : Set V)).UnitDistEmbeddable d := by
    let e : s ≃ Fin (d + 1) := equivFinOfCardEq hK.card_eq
    have hp := unitDistEmbeddable_completeGraph (d + 1)
    rw [Nat.add_sub_cancel] at hp
    exact hp.comap
      { toFun := e, map_rel' := fun h => e.injective.ne h.ne } e.injective
  exact UnitDistEmbeddable.extend_of_clique_neighbors (s : Set V) hs
    (fun u hu a ha b hb hab => hK.isClique (hN u hu a ha) (hN u hu b hb) hab) hsmall

/-- The clique-containing branch at an explicit complete-graph budget. -/
theorem UnitDistEmbeddable.of_core_containing_clique_le_choose {V : Type*} [Finite V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ} (hd : 3 ≤ d) {s : Finset V}
    (hdeg : ∀ v : (s : Set V), d - 1 ≤ ((G.induce ↑s).neighborSet v).ncard)
    (hmax : ∀ t : Finset V, (∀ v ∈ t, d - 2 < (t.filter (G.Adj v)).card) → t ⊆ s)
    (hK : ¬ (G.induce (s : Set V)).CliqueFree (d + 1))
    (hT : (completeMinusTriangle (d + 2)).Free (G.induce (s : Set V)))
    (hbudget : G.edgeSet.ncard ≤ (d + 2).choose 2)
    (hcount : G.edgeSet.ncard < (d + 2).choose 2 + d - 4) :
    G.UnitDistEmbeddable d := by
  classical
  let _ := Fintype.ofFinite V
  let H := G.induce (s : Set V)
  obtain ⟨K, hK⟩ := not_forall.mp hK
  have hK' : H.IsNClique (d + 1) K := by simpa using hK
  have hdegree : ∀ v, d - 1 ≤ H.degree v := by
    intro v
    simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hdeg v
  have hbudgetH : H.edgeSet.ncard < (d + 2).choose 2 + d - 4 :=
    (ncard_edgeSet_induce_le G ↑s).trans_lt hcount
  have hKuniv := eq_univ_of_clique_of_edgeSet_ncard_lt hd hdegree hbudgetH hT hK'
  have htop : H = ⊤ := isClique_univ.mp (by simpa only [hKuniv, coe_univ] using hK'.isClique)
  have hs : G.IsNClique (d + 1) s := by
    refine ⟨G.induce_eq_top.mp htop, ?_⟩
    have hcard := hK'.card_eq
    rw [hKuniv, card_univ] at hcard
    exact (Fintype.card_coe s).symm.trans hcard
  apply UnitDistEmbeddable.of_core_clique_le_choose (by omega) hs hmax
  rwa [show d + 2 = (d + 1) + 1 by omega, Nat.choose_succ_succ,
    Nat.choose_one_right, Nat.add_comm] at hbudget

end SimpleGraph

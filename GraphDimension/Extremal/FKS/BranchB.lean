/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.FKS.Counting
public import GraphDimension.Geometry.BasisApex
public import GraphDimension.Sphere.Extend
public import GraphDimension.Extremal.FKS.CoreAssembly
public import GraphDimension.Extremal.FKS.BranchC

/-!
# FKS Branch B

The clique in a core avoiding `K_{d+2} − K₃` exhausts its vertices. A strict tail budget
then supplies a clique vertex with no neighbour outside the clique.
-/

@[expose] public section

namespace SimpleGraph

open Finset

/-- Branch B's core is exactly its `(d + 1)`-clique. -/
theorem eq_univ_of_clique_of_edgeSet_ncard_lt {V : Type*} [Fintype V]
    {H : SimpleGraph V} [DecidableRel H.Adj] {d : ℕ} (hd : 3 ≤ d)
    (hdeg : ∀ v, d - 1 ≤ H.degree v)
    (hbudget : H.edgeSet.ncard < (d + 2).choose 2 + d - 4)
    (hfree : (completeMinusTriangle (d + 2)).Free H)
    {K : Finset V} (hK : H.IsNClique (d + 1) K) : K = univ := by
  classical
  have hrec : (d + 2).choose 2 = (d + 1).choose 2 + (d + 1) := by
    rw [show d + 2 = (d + 1) + 1 by omega, Nat.choose_succ_succ,
      Nat.choose_one_right, Nat.add_comm]
  apply eq_univ_of_forall
  intro u
  by_contra hu
  have honly : ∀ w, w ∉ K → w = u := by
    intro w hw
    by_contra hwu
    have := card_edgeSet_ge_of_two_outside_clique (by omega) hK hu hw (Ne.symm hwu)
      (hdeg u) (hdeg w)
    omega
  have hN : H.neighborFinset u = K.filter (H.Adj u) := by
    ext w
    simp only [mem_neighborFinset, mem_filter]
    constructor
    · intro huw
      refine ⟨?_, huw⟩
      by_contra hw
      exact huw.ne (honly w hw).symm
    · exact And.right
  apply hfree
  apply completeMinusTriangle_isContained_of_one_outside_clique (by omega) hK hu
  rw [← hN, card_neighborFinset_eq_degree]
  exact hdeg u

/-- Fewer than `|K|` edges outside a clique leave a clique vertex with no outside neighbour. -/
theorem exists_vertex_without_external_neighbor {V : Type*} [Finite V] {G : SimpleGraph V}
    {K : Finset V} (hK : G.IsClique (K : Set V))
    (hbudget : G.edgeSet.ncard < K.card.choose 2 + K.card) :
    ∃ v ∈ K, ∀ w, G.Adj v w → w ∈ K := by
  classical
  let _ := Fintype.ofFinite V
  by_contra! h
  choose w hwadj hwout using fun v : K => h v v.property
  let edges : K → Sym2 V := fun v => s(v.val, w v)
  have hinj : Function.Injective edges := by
    intro v v' he
    rcases Sym2.eq_iff.mp he with ⟨hvv', -⟩ | ⟨hvw, -⟩
    · exact Subtype.ext hvv'
    · exact (hwout v' (hvw ▸ v.property)).elim
  have hsub : univ.image edges ⊆ G.edgeFinset.filter (fun e => ¬ e.toFinset ⊆ K) := by
    intro e he
    obtain ⟨v, -, rfl⟩ := mem_image.mp he
    refine mem_filter.mpr ⟨mem_edgeFinset.mpr (hwadj v), ?_⟩
    intro hsub
    exact hwout v (hsub (by simp [edges]))
  have htail := card_le_card hsub
  rw [card_image_of_injective _ hinj, card_univ, Fintype.card_coe] at htail
  have hpart := card_filter_add_card_filter_not (s := G.edgeFinset)
    (fun e => e.toFinset ⊆ K)
  have htop : G.induce (K : Set V) = ⊤ := G.induce_eq_top.mpr hK
  have hinside : #(G.edgeFinset.filter (fun e => e.toFinset ⊆ K)) = K.card.choose 2 := by
    rw [card_filter_edgeFinset_toFinset_subset]
    rw [edgeFinset_card, Set.fintypeCard_eq_ncard, htop, ← Set.fintypeCard_eq_ncard,
      ← edgeFinset_card, card_edgeFinset_top_eq_card_choose_two]
    exact congrArg (fun n => n.choose 2) (Fintype.card_coe K)
  rw [hinside, edgeFinset_card, Set.fintypeCard_eq_ncard] at hpart
  omega

/-- Reinsert a vertex whose neighbours lie in a `d`-clique, off a spherical placement of
the deleted graph. The off-sphere norm ensures injectivity with every deleted-graph vertex. -/
theorem UnitDistEmbeddable.of_spherical_delete_clique {V : Type*} {G : SimpleGraph V}
    {d : ℕ} (hd : 1 ≤ d) {v : V} {K : Finset V} (hK : G.IsNClique d K) (hv : v ∉ K)
    (hN : ∀ w, G.Adj v w → w ∈ K)
    (h : (G.induce {w | w ≠ v}).SphereEmbeddable d) : G.UnitDistEmbeddable d := by
  classical
  obtain ⟨f, hfInj, hfNorm, hfDist⟩ := h
  let e : Fin d ≃ K := (equivFinOfCardEq hK.card_eq).symm
  let q (i : Fin d) : {w : V // w ≠ v} :=
    ⟨(e i).val, fun he => hv (he ▸ (e i).property)⟩
  have horth : ∀ i j, i ≠ j → inner ℝ (f (q i)) (f (q j)) = 0 := by
    intro i j hij
    apply (EuclideanGeometry.dist_eq_one_iff_inner_eq_zero_of_norm_sq_half (hfNorm _) (hfNorm _)).mp
    apply hfDist
    apply hK.isClique (e i).property (e j).property
    exact fun he => hij (e.injective (Subtype.ext he))
  obtain ⟨x, hxDist, hxNorm⟩ := EuclideanGeometry.exists_unit_dist_of_orthogonal_basis hd
    (f ∘ q) horth (fun i => hfNorm (q i))
  have hxne (w) : x ≠ f w := by
    intro he
    exact hxNorm (he ▸ hfNorm w)
  have hnew (w : V) (hw : w ≠ v) (hvw : G.Adj v w) : dist x (f ⟨w, hw⟩) = 1 := by
    have he := hxDist (e.symm ⟨w, hN w hvw⟩)
    simpa only [Function.comp_apply, q, e.apply_symm_apply] using he
  let p (w : V) := if hw : w = v then x else f ⟨w, hw⟩
  refine ⟨p, ?_, ?_⟩
  · intro a b he
    by_cases ha : a = v <;> by_cases hb : b = v
    · exact ha.trans hb.symm
    · exact (hxne ⟨b, hb⟩ (by simpa only [p, dite_eq_left ha, dite_eq_right hb] using he)).elim
    · exact (hxne ⟨a, ha⟩ (by simpa only [p, dite_eq_left hb, dite_eq_right ha] using he.symm)).elim
    · exact congrArg Subtype.val
        (hfInj (by simpa only [p, dite_eq_right ha, dite_eq_right hb] using he))
  · intro a b hab
    by_cases ha : a = v <;> by_cases hb : b = v
    · exact (hab.ne (ha.trans hb.symm)).elim
    · subst a
      simpa only [p, dite_eq_left rfl, dite_eq_right hb] using hnew b hb hab
    · subst b
      simpa only [p, dite_eq_left rfl, dite_eq_right ha, dist_comm] using hnew a ha hab.symm
    · simpa only [p, dite_eq_right ha, dite_eq_right hb] using hfDist ⟨a, ha⟩ ⟨b, hb⟩ hab

/-- Branch B's placement: a maximal core that is a `(d + 1)`-clique, with fewer than
`d + 1` tail edges, is Euclidean embeddable together with all pruned vertices. -/
theorem UnitDistEmbeddable.of_core_clique {V : Type*} [Finite V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hd : 2 ≤ d) {s : Finset V}
    (hK : G.IsNClique (d + 1) s)
    (hmax : ∀ t : Finset V, (∀ v ∈ t, d - 2 < (t.filter (G.Adj v)).card) → t ⊆ s)
    (hbudget : G.edgeSet.ncard < (d + 1).choose 2 + (d + 1)) :
    G.UnitDistEmbeddable d := by
  classical
  let _ := Fintype.ofFinite V
  obtain ⟨v, hv, hN⟩ := exists_vertex_without_external_neighbor hK.isClique
    (by simpa only [hK.card_eq] using hbudget)
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

/-- Branch B with the original FKS budget: a maximal core containing `K_{d+1}` and
avoiding `K_{d+2} − K₃` has a Euclidean placement together with its pruned vertices. -/
theorem UnitDistEmbeddable.of_core_containing_clique {V : Type*} [Finite V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ} (hd : 3 ≤ d) {s : Finset V}
    (hdeg : ∀ v : (s : Set V), d - 1 ≤ ((G.induce ↑s).neighborSet v).ncard)
    (hmax : ∀ t : Finset V, (∀ v ∈ t, d - 2 < (t.filter (G.Adj v)).card) → t ⊆ s)
    (hK : ¬ (G.induce (s : Set V)).CliqueFree (d + 1))
    (hT : (completeMinusTriangle (d + 2)).Free (G.induce (s : Set V)))
    (hbudget : G.edgeSet.ncard ≤ fksBudget d) : G.UnitDistEmbeddable d := by
  classical
  let _ := Fintype.ofFinite V
  let H := G.induce (s : Set V)
  obtain ⟨K, hK⟩ := not_forall.mp hK
  have hK' : H.IsNClique (d + 1) K := by simpa using hK
  have hdegree : ∀ v, d - 1 ≤ H.degree v := by
    intro v
    simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hdeg v
  have hbudgetH : H.edgeSet.ncard < (d + 2).choose 2 + d - 4 :=
    (ncard_edgeSet_induce_le G ↑s).trans_lt
      (hbudget.trans_lt (fksBudget_lt_branch_count hd))
  have hKuniv := eq_univ_of_clique_of_edgeSet_ncard_lt hd hdegree hbudgetH hT hK'
  have htop : H = ⊤ := isClique_univ.mp (by simpa only [hKuniv, coe_univ] using hK'.isClique)
  have hs : G.IsNClique (d + 1) s := by
    refine ⟨G.induce_eq_top.mp htop, ?_⟩
    have hcard := hK'.card_eq
    rw [hKuniv, card_univ] at hcard
    exact (Fintype.card_coe s).symm.trans hcard
  apply UnitDistEmbeddable.of_core_clique (by omega) hs hmax
  have := fksBudget_le_choose_add hd
  omega

end SimpleGraph

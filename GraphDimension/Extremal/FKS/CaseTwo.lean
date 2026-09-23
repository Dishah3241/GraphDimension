/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Sphere.CrossPolytope
public import GraphDimension.Sphere.OrthogonalSum
public import Mathlib.Combinatorics.SimpleGraph.Finite

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The equality configuration in FKS Case 2

The five vertices consisting of the missing triangle and the two deleted vertices either fit
on a circle, or the complement contains three disjoint edges. This proves the spherical
placement in Case 2 of Frankl–Kupavskii–Swanepoel, *Embedding graphs in Euclidean space*,
Theorem 3 (arXiv:1802.03092, lines 404–412), for every `d ≥ 3`.
-/

open scoped InnerProductSpace

namespace SimpleGraph

/-- Two circle templates: a four-cycle with an isolated vertex, or a two-edge path and
a disjoint edge. The latter edge is rotated using the rational unit vector `(3/5, 4/5)`. -/
private lemma caseTwo_circle {G : SimpleGraph (Fin 5)}
    (h01 : ¬ G.Adj 0 1) (h02 : ¬ G.Adj 0 2)
    (h23 : ¬ G.Adj 2 3) (h24 : ¬ G.Adj 2 4) (h34 : ¬ G.Adj 3 4)
    (hw : ¬ G.Adj 1 2 ∨ (¬ G.Adj 1 3 ∧ ¬ G.Adj 1 4)) :
    G.SphereEmbeddable 2 := by
  classical
  let p : Bool → Fin 5 → Fin 2 → ℝ := fun b =>
    if b then ![![1, 0], ![3 / 5, 4 / 5], ![-4 / 5, 3 / 5], ![0, 1], ![0, -1]]
    else ![![1, 0], ![-1, 0], ![3 / 5, 4 / 5], ![0, 1], ![0, -1]]
  have hp_inj : ∀ b, Function.Injective (p b) := by
    intro b i j hij
    have h0 := congrFun hij 0
    have h1 := congrFun hij 1
    cases b <;> fin_cases i <;> fin_cases j <;> norm_num [p] at *
  have hp_norm : ∀ b i, (p b i 0) ^ 2 + (p b i 1) ^ 2 = 1 := by
    intro b i
    cases b <;> fin_cases i <;> norm_num [p]
  obtain ⟨b, hb⟩ : ∃ b, ∀ i j, G.Adj i j →
      p b j 0 * p b i 0 + p b j 1 * p b i 1 = 0 := by
    rcases hw with hw | ⟨hw3, hw4⟩
    · refine ⟨false, ?_⟩
      intro i j hij
      have hji := hij.symm
      have hne := hij.ne
      fin_cases i <;> fin_cases j <;> norm_num [p] <;> tauto
    · refine ⟨true, ?_⟩
      intro i j hij
      have hji := hij.symm
      have hne := hij.ne
      fin_cases i <;> fin_cases j <;> norm_num [p] <;> tauto
  let r : ℝ := (Real.sqrt 2)⁻¹
  have hr : r ≠ 0 := by dsimp [r]; positivity
  have hr2 : r ^ 2 = 1 / 2 := by
    dsimp [r]
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  refine SphereEmbeddable.iff_orthogonal.mpr
    ⟨fun i => r • WithLp.toLp 2 (p b i), ?_, ?_, ?_⟩
  · intro i j hij
    apply hp_inj b
    funext k
    have h := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x k) hij
    exact mul_left_cancel₀ hr h
  · intro i
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    change (r * p b i 0) ^ 2 + (r * p b i 1) ^ 2 = _
    rw [mul_pow, mul_pow, ← mul_add, hp_norm, mul_one, hr2]
  · intro i j hij
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    change (r * p b j 0) * (r * p b i 0) + (r * p b j 1) * (r * p b i 1) = 0
    calc
      _ = r ^ 2 * (p b j 0 * p b i 0 + p b j 1 * p b i 1) := by ring
      _ = 0 := by rw [hb i j hij, mul_zero]

/-- The degree counts supply one missing base neighbour of `v` and two distinct missing
base neighbours of `w`. -/
private lemma caseTwo_missing {V : Type*} [Fintype V]
    {H : SimpleGraph V} [DecidableRel H.Adj] {d : ℕ} (hd : 3 ≤ d)
    {v w : V} (hvw : v ≠ w) (hnadj : ¬ H.Adj v w)
    (hcard : Fintype.card V = d + 3) (hdv : H.degree v = d)
    (hdw : H.degree w = d - 1) :
    ∃ a b c : V, a ≠ v ∧ a ≠ w ∧ b ≠ v ∧ b ≠ w ∧ c ≠ v ∧ c ≠ w ∧ b ≠ c ∧
      ¬ H.Adj v a ∧ ¬ H.Adj w b ∧ ¬ H.Adj w c := by
  classical
  have hw : w ∈ Hᶜ.neighborFinset v := by simp [hvw, hnadj]
  have hv : v ∈ Hᶜ.neighborFinset w := by simp [hvw.symm, H.adj_comm, hnadj]
  have hvc : ((Hᶜ.neighborFinset v).erase w).card = 1 := by
    rw [Finset.card_erase_of_mem hw, card_neighborFinset_eq_degree, degree_compl, hcard, hdv]
    omega
  have hwc : ((Hᶜ.neighborFinset w).erase v).card = 2 := by
    rw [Finset.card_erase_of_mem hv, card_neighborFinset_eq_degree, degree_compl, hcard, hdw]
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hvc
  obtain ⟨b, c, hbc, hbcset⟩ := Finset.card_eq_two.mp hwc
  have ha' : a ∈ (Hᶜ.neighborFinset v).erase w := by rw [ha]; simp
  have hb' : b ∈ (Hᶜ.neighborFinset w).erase v := by rw [hbcset]; simp
  have hc' : c ∈ (Hᶜ.neighborFinset w).erase v := by rw [hbcset]; simp
  simp only [Finset.mem_erase, mem_neighborFinset, compl_adj] at ha' hb' hc'
  exact ⟨a, b, c, ha'.2.1.symm, ha'.1, hb'.1, hb'.2.1.symm,
    hc'.1, hc'.2.1.symm, hbc, ha'.2.2, hb'.2.2, hc'.2.2⟩

/-- When the three chosen missing neighbours lie in the triangle, its five-vertex extension
is a subgraph of one of the two circle templates. -/
private lemma caseTwo_circle_induce {V : Type*} [DecidableEq V] {H : SimpleGraph V}
    {v w a b c : V} (hvw : v ≠ w) (T : Finset V) (hT : T.card = 3)
    (hTvw : v ∉ T ∧ w ∉ T)
    (htriangle : ∀ x ∈ T, ∀ y ∈ T, ¬ H.Adj x y)
    (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hbc : b ≠ c)
    (hvw' : ¬ H.Adj v w) (hva : ¬ H.Adj v a)
    (hwb : ¬ H.Adj w b) (hwc : ¬ H.Adj w c) :
    (H.induce (↑(insert v (insert w T)) : Set V)).SphereEmbeddable 2 := by
  classical
  obtain ⟨p, q, hpq, hpqset⟩ := Finset.card_eq_two.mp
    (show (T.erase a).card = 2 by rw [Finset.card_erase_of_mem ha, hT])
  have hp : p ≠ a ∧ p ∈ T := by
    have : p ∈ T.erase a := by rw [hpqset]; simp
    simpa using this
  have hq : q ≠ a ∧ q ∈ T := by
    have : q ∈ T.erase a := by rw [hpqset]; simp
    simpa using this
  have hTset : T = {a, p, q} := by rw [← Finset.insert_erase ha, hpqset]
  have hav : a ≠ v := fun h => hTvw.1 (h ▸ ha)
  have haw : a ≠ w := fun h => hTvw.2 (h ▸ ha)
  have hpv : p ≠ v := fun h => hTvw.1 (h ▸ hp.2)
  have hpw : p ≠ w := fun h => hTvw.2 (h ▸ hp.2)
  have hqv : q ≠ v := fun h => hTvw.1 (h ▸ hq.2)
  have hqw : q ≠ w := fun h => hTvw.2 (h ▸ hq.2)
  let S : Finset V := insert v (insert w T)
  let f : Fin 5 → V := ![v, w, a, p, q]
  have hf : ∀ i, f i ∈ S := by
    intro i
    fin_cases i <;> simp [f, S, ha, hp.2, hq.2]
  have hf_inj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  let e : Fin 5 ≃ (↑S : Set V) := Equiv.ofBijective (fun i => ⟨f i, hf i⟩) (by
    constructor
    · intro i j hij
      exact hf_inj (congrArg Subtype.val hij)
    · rintro ⟨x, hx⟩
      have hx' : x = v ∨ x = w ∨ x = a ∨ x = p ∨ x = q := by
        simpa [S, hTset] using hx
      rcases hx' with rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩)
  apply (SphereEmbeddable.of_iso (Iso.comap e (H.induce (↑S : Set V)))).mp
  apply caseTwo_circle
  · exact hvw'
  · exact hva
  · exact htriangle a ha p hp.2
  · exact htriangle a ha q hq.2
  · exact htriangle p hp.2 q hq.2
  · change ¬ H.Adj w a ∨ (¬ H.Adj w p ∧ ¬ H.Adj w q)
    have hb' : b = a ∨ b = p ∨ b = q := by simpa [hTset] using hb
    have hc' : c = a ∨ c = p ∨ c = q := by simpa [hTset] using hc
    rcases hb' with rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl <;> tauto

/-- Two vertices of a triangle remain after avoiding a pair with at most one vertex in it. -/
private lemma caseTwo_triangle {V : Type*} (T : Finset V)
    (hT : T.card = 3) {a y : V} (h : a ∉ T ∨ y ∉ T) :
    ∃ p ∈ T, ∃ q ∈ T, p ≠ q ∧ p ≠ a ∧ p ≠ y ∧ q ≠ a ∧ q ≠ y := by
  classical
  have he : ∀ z, 1 < (T.erase z).card := by
    intro z
    have := Finset.pred_card_le_card_erase (a := z) (s := T)
    omega
  rcases h with ha | hy
  · obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (he y)
    simp only [Finset.mem_erase] at hp hq
    exact ⟨p, hp.2, q, hq.2, hpq, fun h => ha (h ▸ hp.2), hp.1,
      fun h => ha (h ▸ hq.2), hq.1⟩
  · obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (he a)
    simp only [Finset.mem_erase] at hp hq
    exact ⟨p, hp.2, q, hq.2, hpq, hp.1, fun h => hy (h ▸ hp.2), hq.1,
      fun h => hy (h ▸ hq.2)⟩

/-- Package the three disjoint missing edges for the cross-polytope lemma. -/
private lemma caseTwo_matching {V : Type*} [Fintype V] {H : SimpleGraph V}
    {d : ℕ} (hd : 3 ≤ d) (hcard : Fintype.card V = d + 3)
    {v w a y p q : V}
    (hvw : v ≠ w) (hav : a ≠ v) (haw : a ≠ w) (hyv : y ≠ v) (hyw : y ≠ w)
    (hya : a ≠ y) (hpv : p ≠ v) (hpw : p ≠ w) (hqv : q ≠ v) (hqw : q ≠ w)
    (hpq : p ≠ q) (hpa : p ≠ a) (hpy : p ≠ y) (hqa : q ≠ a) (hqy : q ≠ y)
    (hva : ¬ H.Adj v a) (hwy : ¬ H.Adj w y) (hpq' : ¬ H.Adj p q) :
    H.SphereEmbeddable d := by
  apply SphereEmbeddable.of_compl_matching hd (by omega) ![v, w, p] ![a, y, q]
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
  · intro i
    fin_cases i <;> assumption

@[expose] public section

/-- The equality configuration in Case 2 of FKS Theorem 3 has a spherical placement in
dimension `d`, for every `d ≥ 3`. The missing triangle and the two exceptional vertices fit
on a circle unless three disjoint missing edges give a cross-polytope placement. -/
theorem SphereEmbeddable.of_case_two {V : Type*} [Fintype V]
    {H : SimpleGraph V} [DecidableRel H.Adj] {d : ℕ} (hd : 3 ≤ d) {v w : V} (hvw : v ≠ w)
    (hnadj : ¬ H.Adj v w) (hcard : Fintype.card V = d + 3) (T : Finset V) (hT : T.card = 3)
    (hTvw : v ∉ T ∧ w ∉ T)
    (hbase : ∀ x y, x ≠ y → x ≠ v → x ≠ w → y ≠ v → y ≠ w →
      (H.Adj x y ↔ ¬ (x ∈ T ∧ y ∈ T)))
    (hdv : H.degree v = d) (hdw : H.degree w = d - 1) : H.SphereEmbeddable d := by
  classical
  have htriangle : ∀ x ∈ T, ∀ y ∈ T, ¬ H.Adj x y := by
    intro x hx y hy hxy
    exact ((hbase x y hxy.ne (fun h => hTvw.1 (h ▸ hx))
      (fun h => hTvw.2 (h ▸ hx)) (fun h => hTvw.1 (h ▸ hy))
      (fun h => hTvw.2 (h ▸ hy))).mp hxy) ⟨hx, hy⟩
  obtain ⟨a, b, c, hav, haw, hbv, hbw, hcv, hcw, hbc, hva, hwb, hwc⟩ :=
    caseTwo_missing hd hvw hnadj hcard hdv hdw
  by_cases hcircle : a ∈ T ∧ b ∈ T ∧ c ∈ T
  · let S : Finset V := insert v (insert w T)
    have hS : S.card = 5 := by simp [S, hTvw.1, hTvw.2, hvw, hT]
    have hcircle' : (H.induce (↑S : Set V)).SphereEmbeddable 2 :=
      caseTwo_circle_induce hvw T hT hTvw htriangle hcircle.1 hcircle.2.1 hcircle.2.2
        hbc hnadj hva hwb hwc
    have hrest : (H.induce (↑S : Set V)ᶜ).SphereEmbeddable (d - 2) := by
      have hrestcard : Fintype.card ↥((↑S : Set V)ᶜ) ≤ d - 2 + 0 := by
        rw [Fintype.card_compl_set]
        change Fintype.card V - Fintype.card S ≤ d - 2 + 0
        rw [Fintype.card_coe, hcard, hS]
        omega
      exact SphereEmbeddable.of_compl_matching (k := 0) (Nat.zero_le _) hrestcard
        Fin.elim0 Fin.elim0 (by rintro (i | i) <;> exact Fin.elim0 i)
        (by intro i; exact Fin.elim0 i)
    have hsum := hcircle'.orthogonalSum hrest
    simpa [Nat.add_sub_of_le (show 2 ≤ d by omega)] using hsum
  · obtain ⟨y, hyv, hyw, hay, hwy, hyT⟩ :
        ∃ y, y ≠ v ∧ y ≠ w ∧ a ≠ y ∧ ¬ H.Adj w y ∧ (a ∉ T ∨ y ∉ T) := by
      by_cases ha : a ∈ T
      · by_cases hb : b ∈ T
        · have hc : c ∉ T := by tauto
          exact ⟨c, hcv, hcw, fun h => hc (h ▸ ha), hwc, Or.inr hc⟩
        · exact ⟨b, hbv, hbw, fun h => hb (h ▸ ha), hwb, Or.inr hb⟩
      · by_cases hab : a = b
        · exact ⟨c, hcv, hcw, hab ▸ hbc, hwc, Or.inl ha⟩
        · exact ⟨b, hbv, hbw, hab, hwb, Or.inl ha⟩
    obtain ⟨p, hp, q, hq, hpq, hpa, hpy, hqa, hqy⟩ := caseTwo_triangle T hT hyT
    exact caseTwo_matching hd hcard hvw hav haw hyv hyw hay
      (fun h => hTvw.1 (h ▸ hp)) (fun h => hTvw.2 (h ▸ hp))
      (fun h => hTvw.1 (h ▸ hq)) (fun h => hTvw.2 (h ▸ hq))
      hpq hpa hpy hqa hqy hva hwy (htriangle p hp q hq)

end

end SimpleGraph

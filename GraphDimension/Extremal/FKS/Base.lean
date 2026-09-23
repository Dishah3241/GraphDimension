/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.FKS.Defs

import GraphDimension.Combinatorics.SimpleGraph.Core
import GraphDimension.Geometry.CompleteGraph
import GraphDimension.Geometry.Extend
import GraphDimension.Geometry.UnitDistanceComap
import GraphDimension.Sphere.DegreeOne
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The base of FKS's induction

`S(2)`: a finite graph with at most three edges has a unit-distance placement in `ℝ²`. If it also
contains neither `K₃` nor `K₄ − K₃`, the same graph lies on the circle of radius `1/√2`.

## References

Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, J. Combin. Theory Ser. A
**171** (2020), 105146, arXiv 1802.03092, proof of Theorem 3 (`main.tex` line 345).
-/

open scoped InnerProductSpace RealInnerProductSpace

namespace SimpleGraph

open Finset

noncomputable section

variable {V : Type*}

private def planeVec (x y : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun i => if i.val = 0 then x else y

private lemma planeVec_zero (x y : ℝ) : planeVec x y 0 = x := by
  simp [planeVec, PiLp.toLp_apply]

private lemma planeVec_one (x y : ℝ) : planeVec x y 1 = y := by
  simp [planeVec, PiLp.toLp_apply]

private lemma norm_sq_planeVec {x y : ℝ} (h : x ^ 2 + y ^ 2 = 1 / 2) :
    ‖planeVec x y‖ ^ 2 = 1 / 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, planeVec_zero, planeVec_one]
  exact h

private lemma inner_planeVec (x y x' y' : ℝ) :
    ⟪planeVec x y, planeVec x' y'⟫_ℝ = x * x' + y * y' := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, planeVec_zero, planeVec_one, planeVec_zero, planeVec_one]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

private lemma planeVec_inj {x y x' y' : ℝ} (h : planeVec x y = planeVec x' y') :
    x = x' ∧ y = y' := by
  constructor
  · have := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h
    simpa [planeVec_zero] using this
  · have := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) h
    simpa [planeVec_one] using this

private lemma planeVec_ne_of_zero {x y x' y' : ℝ} (h : x ≠ x') :
    planeVec x y ≠ planeVec x' y' := by
  intro h'
  exact h (planeVec_inj h').1

private lemma planeVec_ne_of_one {x y y' : ℝ} (h : y ≠ y') :
    planeVec x y ≠ planeVec x y' := by
  intro h'
  exact h (planeVec_inj h').2

private lemma sqrt_two_inv_sq : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private lemma sqrt_two_inv_pos : (0 : ℝ) < (Real.sqrt 2)⁻¹ := by
  positivity

private lemma half_lt_sqrt_two_inv : (1 / 2 : ℝ) < (Real.sqrt 2)⁻¹ := by
  by_contra h
  push Not at h
  have hsq : ((Real.sqrt 2)⁻¹) ^ 2 ≤ (1 / 2) ^ 2 :=
    sq_le_sq' (by linarith [sqrt_two_inv_pos]) h
  rw [sqrt_two_inv_sq] at hsq
  norm_num at hsq

private def upperVec (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  planeVec t (Real.sqrt (1 / 2 - t ^ 2))

private lemma upperVec_zero (t : ℝ) : upperVec t 0 = t := by
  simp [upperVec, planeVec_zero]

private lemma norm_sq_upperVec {t : ℝ} (ht : t ^ 2 ≤ 1 / 2) : ‖upperVec t‖ ^ 2 = 1 / 2 := by
  have hs : 0 ≤ 1 / 2 - t ^ 2 := sub_nonneg.mpr ht
  exact norm_sq_planeVec (by rw [Real.sq_sqrt hs]; ring)

private lemma isolate_coord_bounds {n k : ℕ} (hk : k < n) :
    0 < (k + 1 : ℝ) / (n + 2) * (1 / 4) ∧
      (k + 1 : ℝ) / (n + 2) * (1 / 4) < 1 / 4 ∧
      ((k + 1 : ℝ) / (n + 2) * (1 / 4)) ^ 2 ≤ 1 / 2 := by
  have hden : (0 : ℝ) < n + 2 := by exact_mod_cast (show 0 < n + 2 by omega)
  have hnum : (0 : ℝ) < (k + 1 : ℝ) := by exact_mod_cast (show 0 < k + 1 by omega)
  have hlt : (k + 1 : ℝ) < n + 2 := by exact_mod_cast (show k + 1 < n + 2 by omega)
  have hfrac : (k + 1 : ℝ) / (n + 2) < 1 := (div_lt_one hden).mpr hlt
  have ht : 0 < (k + 1 : ℝ) / (n + 2) * (1 / 4) := by positivity
  have htlt : (k + 1 : ℝ) / (n + 2) * (1 / 4) < 1 / 4 := by
    calc
      (k + 1 : ℝ) / (n + 2) * (1 / 4) < 1 * (1 / 4) :=
        mul_lt_mul_of_pos_right hfrac (by norm_num)
      _ = 1 / 4 := by ring
  refine ⟨ht, htlt, ?_⟩
  have hsq : ((k + 1 : ℝ) / (n + 2) * (1 / 4)) ^ 2 ≤ (1 / 4) ^ 2 :=
    sq_le_sq' (by linarith) htlt.le
  calc
    _ ≤ (1 / 4) ^ 2 := hsq
    _ ≤ 1 / 2 := by norm_num

private lemma not_open_quarter {x : ℝ} (h : x ≤ 0 ∨ 1 / 4 ≤ x) :
    ¬ (0 < x ∧ x < 1 / 4) := by
  rintro ⟨hx, hy⟩
  rcases h with h | h <;> linarith

private lemma upperVec_ne_of_coord {t x y : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 4)
    (hx : x ≤ 0 ∨ 1 / 4 ≤ x) : upperVec t ≠ planeVec x y := by
  intro h
  have h0 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h
  rw [upperVec_zero, planeVec_zero] at h0
  exact not_open_quarter hx ⟨by simpa [h0] using ht0, by simpa [h0] using ht1⟩

private lemma edgeSet_ncard_eq {V : Type*} (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeSet.ncard = #G.edgeFinset := by
  rw [edgeFinset_card, Set.fintypeCard_eq_ncard]

private lemma isClique_of_ncard_le_one {V : Type*} {G : SimpleGraph V} {s : Set V}
    (hs : s.Finite) (hcard : s.ncard ≤ 1) : G.IsClique s := by
  intro a ha b hb hab
  have htwo : ({a, b} : Set V).ncard = 2 := Set.ncard_pair hab
  have hsub : ({a, b} : Set V) ⊆ s := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have : 2 ≤ s.ncard := by
    rw [← htwo]
    exact Set.ncard_le_ncard hsub hs
  omega

private lemma ncard_neighbor_induce_insert_le [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {s : Finset V} {x : V}
    (xH : {v // v ∈ ↑(insert x s)}) (hxH : xH.1 = x) :
    ((G.induce ↑(insert x s)).neighborSet xH).ncard ≤ #(s.filter (G.Adj x)) := by
  let H := G.induce ↑(insert x s)
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn (fun w : {v // v ∈ ↑(insert x s)} => w.1)
      (s := H.neighborSet xH) (t := (s.filter (G.Adj x) : Set V)) ?_ ?_
      (Finset.finite_toSet _)
  · intro w hw
    have hadjH : H.Adj xH w := by simpa [mem_neighborSet] using hw
    have hadj : G.Adj x w.1 := by
      rw [induce_adj] at hadjH
      simpa [hxH] using hadjH
    have hne : w.1 ≠ x := by
      intro hwx
      exact hadjH.ne (Subtype.ext (hwx.trans hxH.symm)).symm
    have hmem : w.1 ∈ insert x s := Finset.mem_coe.mp w.2
    rcases Finset.mem_insert.mp hmem with hwx | hs
    · exact absurd hwx hne
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hs, hadj⟩)
  · intro a _ b _ hab
    exact Subtype.ext hab

private lemma unitDist_induce_erase_insert [DecidableEq V] {G : SimpleGraph V}
    {s : Finset V} {x : V}
    (xH : {v // v ∈ ↑(insert x s)}) (hxH : xH.1 = x)
    (h : (G.induce ↑s).UnitDistEmbeddable 2) :
    ((G.induce ↑(insert x s)).induce {v | v ≠ xH}).UnitDistEmbeddable 2 := by
  let H := G.induce ↑(insert x s)
  let φ : (H.induce {v | v ≠ xH}) →g G.induce ↑s := {
    toFun := fun v => ⟨v.1.1, by
      have hmem : v.1.1 ∈ insert x s := Finset.mem_coe.mp v.1.2
      have hne : v.1.1 ≠ x := by
        intro hxv
        exact v.2 (Subtype.ext (hxv.trans hxH.symm))
      rcases Finset.mem_insert.mp hmem with hxv | hs
      · exact absurd hxv hne
      · exact Finset.mem_coe.mpr hs⟩
    map_rel' := fun {a b} hab => by
      apply induce_adj.mpr
      exact induce_adj.mp (induce_adj.mp hab)
  }
  have hφ : Function.Injective φ := by
    intro a b hab
    have hval : (φ a).1 = (φ b).1 :=
      congrArg (fun z : {v // v ∈ ↑s} => (z : V)) hab
    exact Subtype.ext (Subtype.ext hval)
  exact h.comap φ hφ

private lemma unitDist_extend_insert [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {s : Finset V} {x : V} (hdeg : #(s.filter (G.Adj x)) ≤ 1)
    (h : (G.induce ↑s).UnitDistEmbeddable 2) :
    (G.induce ↑(insert x s)).UnitDistEmbeddable 2 := by
  have : Finite {v // v ∈ ↑(insert x s)} := (Finset.finite_toSet (insert x s)).to_subtype
  let H := G.induce ↑(insert x s)
  let xH : {v // v ∈ ↑(insert x s)} := ⟨x, Finset.mem_coe.mpr (Finset.mem_insert_self x s)⟩
  have hncard : (H.neighborSet xH).ncard ≤ 1 :=
    (ncard_neighbor_induce_insert_le xH rfl).trans hdeg
  have hclique : H.IsClique (H.neighborSet xH) :=
    isClique_of_ncard_le_one (Set.toFinite _) hncard
  have hk : (H.neighborSet xH).ncard + 1 ≤ 2 := by omega
  exact UnitDistEmbeddable.extend hclique hk (unitDist_induce_erase_insert xH rfl h)

private lemma unitDist_induce_empty {V : Type*} (G : SimpleGraph V) :
    (G.induce (∅ : Set V)).UnitDistEmbeddable 2 := by
  have : IsEmpty {v // v ∈ (∅ : Set V)} := ⟨fun v => v.2.elim⟩
  exact ⟨fun v => isEmptyElim v, fun a b _ => isEmptyElim a, fun a b _ => isEmptyElim a⟩

private lemma degree_induce_eq_filter {G : SimpleGraph V} [Finite V] [DecidableRel G.Adj]
    (c : Finset V) (v : {x // x ∈ (↑c : Set V)}) :
    (G.induce (↑c : Set V)).degree v = #(c.filter (G.Adj v.1)) := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  let H := G.induce (↑c : Set V)
  rw [← card_neighborFinset_eq_degree]
  exact Finset.card_bij (fun (w : {x // x ∈ (↑c : Set V)}) (_ : w ∈ H.neighborFinset v) => (w : V))
    (fun w hw => by
      rw [mem_neighborFinset] at hw
      exact mem_filter.mpr ⟨Finset.mem_coe.mp w.2, induce_adj.mp hw⟩)
    (fun w _ w' _ h => Subtype.ext h)
    (fun b hb => by
      obtain ⟨hbC, hbA⟩ := mem_filter.mp hb
      refine ⟨⟨b, Finset.mem_coe.mpr hbC⟩, ?_, rfl⟩
      rw [mem_neighborFinset, induce_adj]
      exact hbA)

private lemma ncard_induce_edgeSet_le {G : SimpleGraph V} [Finite V] (c : Finset V) :
    (G.induce (↑c : Set V)).edgeSet.ncard ≤ G.edgeSet.ncard := by
  classical
  let H := G.induce (↑c : Set V)
  let emb : {x // x ∈ (↑c : Set V)} ↪ V := Function.Embedding.subtype (· ∈ (↑c : Set V))
  let f : Sym2 {x // x ∈ (↑c : Set V)} → Sym2 V := fun e => e.map emb
  have hinj : Set.InjOn f H.edgeSet := fun _ _ _ _ h => emb.sym2Map.injective h
  have himg : f '' H.edgeSet ⊆ G.edgeSet := by
    intro e he
    obtain ⟨e', he', rfl⟩ := he
    induction e' using Sym2.inductionOn with
    | hf x y =>
      have hxy : H.Adj x y := by simpa [mem_edgeSet] using he'
      have hg : G.Adj x.1 y.1 := induce_adj.mp hxy
      simpa [f, emb, mem_edgeSet] using hg
  rw [← hinj.ncard_image]
  exact Set.ncard_le_ncard himg

private lemma unitDist_of_core {G : SimpleGraph V} [Finite V] [DecidableRel G.Adj] {c : Finset V}
    (hcore : ∀ v ∈ c, 1 < #(c.filter (G.Adj v))) (hE : G.edgeSet.ncard ≤ 3) :
    (G.induce (↑c : Set V)).UnitDistEmbeddable 2 := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  let H := G.induce (↑c : Set V)
  have hmin : ∀ v, 2 ≤ H.degree v := by
    intro v
    rw [degree_induce_eq_filter]
    have hv : v.1 ∈ c := Finset.mem_coe.mp v.2
    exact Nat.succ_le_of_lt (hcore v.1 hv)
  have hcardV : Fintype.card {v // v ∈ (↑c : Set V)} = #c :=
    Fintype.card_of_subtype c fun x => (Finset.mem_coe).symm
  have hedge : #H.edgeFinset ≤ 3 := by
    have hle := ncard_induce_edgeSet_le (G := G) c
    rw [edgeSet_ncard_eq (G := H)] at hle
    omega
  have hsum := H.sum_degrees_eq_twice_card_edges
  have hlower : 2 * Fintype.card {v // v ∈ (↑c : Set V)} ≤ ∑ v, H.degree v := by
    calc
      2 * Fintype.card {v // v ∈ (↑c : Set V)} = ∑ _ : {v // v ∈ (↑c : Set V)}, 2 := by
        simp [sum_const, mul_comm]
      _ ≤ ∑ v, H.degree v := sum_le_sum fun v _ => hmin v
  rw [hsum] at hlower
  have hverts : #c ≤ #H.edgeFinset := by
    rw [← hcardV]
    omega
  have hc : #c ≤ 3 := hverts.trans hedge
  by_cases h3 : #c = 3
  · have hdeg2 : ∀ v, H.degree v = 2 := by
      intro v
      have hge := hmin v
      have hlt := H.degree_lt_card_verts v
      rw [hcardV, h3] at hlt
      omega
    have htop : H = ⊤ := by
      ext a b
      simp only [top_adj]
      constructor
      · exact fun h => h.ne
      · intro hne
        have hsub : H.neighborFinset a ⊆ univ.erase a := by
          intro w hw
          refine mem_erase.mpr ⟨?_, mem_univ _⟩
          have hadj : H.Adj a w := by simpa [mem_neighborFinset] using hw
          exact hadj.ne.symm
        have hcardErase : #(univ.erase a) = 2 := by
          rw [card_erase_of_mem (mem_univ _), card_univ, hcardV, h3]
        have hEq : H.neighborFinset a = univ.erase a :=
          eq_of_subset_of_card_le hsub (by
            rw [hcardErase, card_neighborFinset_eq_degree, hdeg2 a])
        have hb : b ∈ univ.erase a := mem_erase.mpr ⟨hne.symm, mem_univ _⟩
        rw [← hEq] at hb
        exact (by simpa [mem_neighborFinset] using hb)
    have htop' : G.induce (↑c : Set V) = ⊤ := htop
    rw [htop']
    exact (UnitDistEmbeddable.of_iso
      (Iso.completeGraph (Fintype.equivFinOfCardEq (hcardV.trans h3)))).mpr
      (unitDistEmbeddable_completeGraph 3)
  · have hlt : #c < 3 := by omega
    by_cases h0 : #c = 0
    · have hc0 : c = ∅ := card_eq_zero.mp h0
      rw [hc0, Finset.coe_empty]
      exact unitDist_induce_empty G
    · have hpos : 0 < Fintype.card {v // v ∈ (↑c : Set V)} := by
        rw [hcardV]
        omega
      obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpos
      have hltDeg := H.degree_lt_card_verts v
      rw [hcardV] at hltDeg
      have hge := hmin v
      omega

private lemma unitDistEmbeddable_two_of_ncard_edgeSet_le {V : Type*} [Finite V]
    (G : SimpleGraph V) (hE : G.edgeSet.ncard ≤ 3) : G.UnitDistEmbeddable 2 := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  obtain ⟨c, hcore, hP⟩ := exists_core G 1
    (fun s => (G.induce (s : Set V)).UnitDistEmbeddable 2)
    (fun _s _x _hx hdeg hEmb => unitDist_extend_insert hdeg hEmb)
  have hcoreEmb : (G.induce (↑c : Set V)).UnitDistEmbeddable 2 := unitDist_of_core hcore hE
  have hUniv : (G.induce (Set.univ : Set V)).UnitDistEmbeddable 2 := by
    rw [← Finset.coe_univ]
    exact hP hcoreEmb
  exact (UnitDistEmbeddable.of_iso (induceUnivIso G)).mp hUniv

private lemma completeMinusTriangle_four_adj {i j : Fin 4} :
    (completeMinusTriangle 4).Adj i j ↔ i ≠ j ∧ (i = 3 ∨ j = 3) := by
  fin_cases i <;> fin_cases j <;> simp [completeMinusTriangle]

private lemma degree_le_two_of_free_completeMinusTriangle_four [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hFree : (completeMinusTriangle 4).Free G) (v : V) : G.degree v ≤ 2 := by
  classical
  by_contra hgt
  have h3 : 3 ≤ G.degree v := by omega
  rw [← card_neighborFinset_eq_degree] at h3
  obtain ⟨t, ht, ht3⟩ := Finset.exists_subset_card_eq h3
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp ht3
  have ha : G.Adj v a := by
    have : a ∈ G.neighborFinset v := ht (by simp [hset])
    simpa [mem_neighborFinset] using this
  have hb : G.Adj v b := by
    have : b ∈ G.neighborFinset v := ht (by simp [hset])
    simpa [mem_neighborFinset] using this
  have hc : G.Adj v c := by
    have : c ∈ G.neighborFinset v := ht (by simp [hset])
    simpa [mem_neighborFinset] using this
  let f : Fin 4 → V := fun i =>
    if i = 0 then a else if i = 1 then b else if i = 2 then c else v
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [f] at hij <;>
      first
        | rfl
        | exact absurd hij hab | exact absurd hij hab.symm
        | exact absurd hij hac | exact absurd hij hac.symm
        | exact absurd hij hbc | exact absurd hij hbc.symm
        | exact absurd hij ha.ne | exact absurd hij ha.ne.symm
        | exact absurd hij hb.ne | exact absurd hij hb.ne.symm
        | exact absurd hij hc.ne | exact absurd hij hc.ne.symm
  let hom : completeMinusTriangle 4 →g G := ⟨f, fun {i j} hij => by
    rw [completeMinusTriangle_four_adj] at hij
    rcases hij with ⟨hne, hi | hj⟩
    · subst hi
      fin_cases j
      · simpa [f] using ha
      · simpa [f] using hb
      · simpa [f] using hc
      · exact (hne rfl).elim
    · subst hj
      fin_cases i
      · simpa [f] using ha.symm
      · simpa [f] using hb.symm
      · simpa [f] using hc.symm
      · exact (hne rfl).elim⟩
  exact hFree ⟨hom.toCopy hinj⟩

private lemma not_adj_triangle {G : SimpleGraph V} (hK : G.CliqueFree 3) {v a b : V}
    (hva : G.Adj v a) (hvb : G.Adj v b) (hab : a ≠ b) : ¬ G.Adj a b := by
  classical
  intro hab'
  have hvab : v ∉ ({a, b} : Finset V) := by simp [hva.ne, hvb.ne]
  have habm : a ∉ ({b} : Finset V) := by simpa using hab
  have hcard : #{v, a, b} = 3 := by
    rw [card_insert_of_notMem hvab, card_insert_of_notMem habm, card_singleton]
  exact hK {v, a, b} ⟨by
    intro x hx y hy hxy
    rw [mem_coe, mem_insert, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact (hxy rfl).elim
    · exact hva
    · exact hvb
    · exact hva.symm
    · exact (hxy rfl).elim
    · exact hab'
    · exact hvb.symm
    · exact hab'.symm
    · exact (hxy rfl).elim, hcard⟩

private lemma exists_two_neighbors [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {v : V} (hdeg : G.degree v = 2) :
    ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b ∧ G.neighborFinset v = {a, b} := by
  have hcard : #(G.neighborFinset v) = 2 := by rw [card_neighborFinset_eq_degree, hdeg]
  obtain ⟨a, b, hab, hN⟩ := card_eq_two.mp hcard
  have ha : G.Adj v a := by
    have : a ∈ G.neighborFinset v := by simp [hN]
    simpa [mem_neighborFinset] using this
  have hb : G.Adj v b := by
    have : b ∈ G.neighborFinset v := by simp [hN]
    simpa [mem_neighborFinset] using this
  exact ⟨a, b, hab, ha, hb, hN⟩

private lemma exists_other_neighbor [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {a v : V} (hdeg : G.degree a = 2) (hv : G.Adj a v) :
    ∃ w, w ≠ v ∧ G.Adj a w ∧ G.neighborFinset a = {v, w} := by
  have hcard : #(G.neighborFinset a) = 2 := by rw [card_neighborFinset_eq_degree, hdeg]
  obtain ⟨x, y, hxy, hN⟩ := card_eq_two.mp hcard
  have hvmem : v ∈ G.neighborFinset a := by simpa [mem_neighborFinset] using hv
  have hvxy : v = x ∨ v = y := by
    have : v ∈ ({x, y} : Finset V) := by rwa [← hN]
    simpa [hxy] using this
  rcases hvxy with rfl | rfl
  · exact ⟨y, hxy.symm,
      by simpa [mem_neighborFinset] using (show y ∈ G.neighborFinset a by simp [hN]), hN⟩
  · exact ⟨x, hxy,
      by simpa [mem_neighborFinset] using (show x ∈ G.neighborFinset a by simp [hN]),
      hN.trans (pair_comm x v)⟩

private lemma eq_of_isolate_upper [Fintype V] (e : V ≃ Fin (Fintype.card V)) {x y : V}
    (h : upperVec (((e x).val + 1 : ℝ) / ((Fintype.card V : ℝ) + 2) * (1 / 4)) =
      upperVec (((e y).val + 1 : ℝ) / ((Fintype.card V : ℝ) + 2) * (1 / 4))) : x = y := by
  have h0 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h
  rw [upperVec_zero, upperVec_zero] at h0
  have hden : (Fintype.card V : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
  have hnum : ((e x).val + 1 : ℝ) = (e y).val + 1 :=
    (div_left_inj' hden).mp (mul_right_cancel₀ (by norm_num : (1 / 4 : ℝ) ≠ 0) h0)
  have hval : (e x).val = (e y).val := by
    have hsucc : (e x).val + 1 = (e y).val + 1 := by exact_mod_cast hnum
    omega
  exact e.injective (Fin.ext hval)

private lemma axis_not_open_quarter (x : ℝ) (hx : x = (Real.sqrt 2)⁻¹ ∨ x = 0 ∨
    x = -(Real.sqrt 2)⁻¹ ∨ x = 1 / 2 ∨ x = -(1 / 2)) :
    x ≤ 0 ∨ 1 / 4 ≤ x := by
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · right
    exact (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2).trans half_lt_sqrt_two_inv.le
  · left
    exact le_rfl
  · left
    linarith [sqrt_two_inv_pos]
  · right
    norm_num
  · left
    norm_num

private lemma sphere_of_path3 [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {a v b : V} (hav : a ≠ v) (hvb : v ≠ b) (hab : a ≠ b)
    (hE : G.edgeFinset = {s(a, v), s(v, b)}) : G.SphereEmbeddable 2 := by
  let e := Fintype.equivFin V
  let r : ℝ := (Real.sqrt 2)⁻¹
  let pA := planeVec r 0
  let pV := planeVec 0 r
  let pB := planeVec (-r) 0
  let t (x : V) : ℝ := ((e x).val + 1 : ℝ) / (Fintype.card V + 2) * (1 / 4)
  let place (x : V) : EuclideanSpace ℝ (Fin 2) :=
    if x = a then pA else if x = v then pV else if x = b then pB else upperVec (t x)
  have ht (x : V) : 0 < t x ∧ t x < 1 / 4 ∧ (t x) ^ 2 ≤ 1 / 2 := by
    simpa [t, e] using isolate_coord_bounds (e x).isLt
  have place_a : place a = pA := by simp [place]
  have place_v : place v = pV := by simp [place, Ne.symm hav]
  have place_b : place b = pB := by simp [place, Ne.symm hab, Ne.symm hvb]
  have hneAV : pA ≠ pV := planeVec_ne_of_zero sqrt_two_inv_pos.ne'
  have hneAB : pA ≠ pB := planeVec_ne_of_zero (by
    intro h; exact sqrt_two_inv_pos.ne' (by linarith : (Real.sqrt 2)⁻¹ = 0))
  have hneVB : pV ≠ pB := planeVec_ne_of_zero (by
    intro h; exact sqrt_two_inv_pos.ne' (by linarith : (Real.sqrt 2)⁻¹ = 0))
  have hAiso (z : V) : pA ≠ upperVec (t z) :=
    (upperVec_ne_of_coord (ht z).1 (ht z).2.1 (axis_not_open_quarter r (Or.inl rfl))).symm
  have hViso (z : V) : pV ≠ upperVec (t z) :=
    (upperVec_ne_of_coord (ht z).1 (ht z).2.1 (axis_not_open_quarter 0 (Or.inr (Or.inl rfl)))).symm
  have hBiso (z : V) : pB ≠ upperVec (t z) :=
    (upperVec_ne_of_coord (ht z).1 (ht z).2.1
      (axis_not_open_quarter (-r) (Or.inr (Or.inr (Or.inl rfl))))).symm
  have hnormA : ‖pA‖ ^ 2 = 1 / 2 :=
    norm_sq_planeVec (by simp only [r]; rw [sqrt_two_inv_sq]; ring)
  have hnormV : ‖pV‖ ^ 2 = 1 / 2 :=
    norm_sq_planeVec (by simp only [r]; rw [sqrt_two_inv_sq]; ring)
  have hnormB : ‖pB‖ ^ 2 = 1 / 2 :=
    norm_sq_planeVec (by rw [neg_sq]; simp only [r]; rw [sqrt_two_inv_sq]; ring)
  have horthAV : ⟪pA, pV⟫_ℝ = 0 := by rw [inner_planeVec]; ring
  have horthVB : ⟪pV, pB⟫_ℝ = 0 := by rw [inner_planeVec]; ring
  rw [SphereEmbeddable.iff_orthogonal]
  refine ⟨place, ?_, ?_, ?_⟩
  · intro x y h
    simp only [place] at h
    split_ifs at h
    all_goals
      first
      | (subst_eqs; rfl)
      | exact (hneAV h).elim | exact (hneAV h.symm).elim
      | exact (hneAB h).elim | exact (hneAB h.symm).elim
      | exact (hneVB h).elim | exact (hneVB h.symm).elim
      | exact (hAiso y h).elim | exact ((hAiso x).symm h).elim
      | exact (hViso y h).elim | exact ((hViso x).symm h).elim
      | exact (hBiso y h).elim | exact ((hBiso x).symm h).elim
      | exact eq_of_isolate_upper e (by simpa [t] using h)
  · intro x
    by_cases hxa : x = a
    · rw [hxa, place_a]; exact hnormA
    · by_cases hxv : x = v
      · rw [hxv, place_v]; exact hnormV
      · by_cases hxb : x = b
        · rw [hxb, place_b]; exact hnormB
        · rw [show place x = upperVec (t x) by simp [place, hxa, hxv, hxb]]
          exact norm_sq_upperVec (ht x).2.2
  · intro x y hxy
    have he : s(x, y) ∈ ({s(a, v), s(v, b)} : Finset (Sym2 V)) := by
      rw [← hE]; exact mem_edgeFinset.mpr hxy
    simp only [mem_insert, mem_singleton] at he
    rcases he with he | he
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [place_a, place_v]; exact horthAV
      · rw [place_v, place_a, real_inner_comm]; exact horthAV
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [place_v, place_b]; exact horthVB
      · rw [place_b, place_v, real_inner_comm]; exact horthVB

private lemma sphere_of_path4 [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {w a v b : V} (hwa : w ≠ a) (hav : a ≠ v) (hvb : v ≠ b) (hwv : w ≠ v) (hwb : w ≠ b)
    (hab : a ≠ b) (hE : G.edgeFinset = {s(w, a), s(a, v), s(v, b)}) : G.SphereEmbeddable 2 := by
  let e := Fintype.equivFin V
  let r : ℝ := (Real.sqrt 2)⁻¹
  let pW := planeVec r 0
  let pA := planeVec 0 r
  let pV := planeVec (-r) 0
  let pB := planeVec 0 (-r)
  let t (x : V) : ℝ := ((e x).val + 1 : ℝ) / (Fintype.card V + 2) * (1 / 4)
  let place (x : V) : EuclideanSpace ℝ (Fin 2) :=
    if x = w then pW else if x = a then pA else if x = v then pV else if x = b then pB else
      upperVec (t x)
  have ht (x : V) : 0 < t x ∧ t x < 1 / 4 ∧ (t x) ^ 2 ≤ 1 / 2 := by
    simpa [t, e] using isolate_coord_bounds (e x).isLt
  have place_w : place w = pW := by simp [place]
  have place_a : place a = pA := by simp [place, Ne.symm hwa]
  have place_v : place v = pV := by simp [place, Ne.symm hwv, Ne.symm hav]
  have place_b : place b = pB := by simp [place, Ne.symm hwb, Ne.symm hab, Ne.symm hvb]
  have hneWA : pW ≠ pA := planeVec_ne_of_zero sqrt_two_inv_pos.ne'
  have hneWV : pW ≠ pV := planeVec_ne_of_zero (by
    intro h; exact (ne_of_gt sqrt_two_inv_pos) (by linarith))
  have hneWB : pW ≠ pB := planeVec_ne_of_zero sqrt_two_inv_pos.ne'
  have hneAV : pA ≠ pV := planeVec_ne_of_zero (by
    intro h; exact sqrt_two_inv_pos.ne' (by linarith))
  have hneAB : pA ≠ pB := planeVec_ne_of_one (by
    intro h; exact (ne_of_gt sqrt_two_inv_pos) (by linarith))
  have hneVB : pV ≠ pB := planeVec_ne_of_zero (by
    intro h; exact sqrt_two_inv_pos.ne' (by linarith))
  have hWiso (z : V) : pW ≠ upperVec (t z) :=
    (upperVec_ne_of_coord (ht z).1 (ht z).2.1 (axis_not_open_quarter r (Or.inl rfl))).symm
  have hAiso (z : V) : pA ≠ upperVec (t z) :=
    (upperVec_ne_of_coord (ht z).1 (ht z).2.1 (axis_not_open_quarter 0 (Or.inr (Or.inl rfl)))).symm
  have hViso (z : V) : pV ≠ upperVec (t z) :=
    (upperVec_ne_of_coord (ht z).1 (ht z).2.1
      (axis_not_open_quarter (-r) (Or.inr (Or.inr (Or.inl rfl))))).symm
  have hBiso (z : V) : pB ≠ upperVec (t z) :=
    (upperVec_ne_of_coord (ht z).1 (ht z).2.1
      (axis_not_open_quarter 0 (Or.inr (Or.inl rfl)))).symm
  have hnormW : ‖pW‖ ^ 2 = 1 / 2 :=
    norm_sq_planeVec (by simp only [r]; rw [sqrt_two_inv_sq]; ring)
  have hnormA : ‖pA‖ ^ 2 = 1 / 2 := norm_sq_planeVec (by simp only [r]; rw [sqrt_two_inv_sq]; ring)
  have hnormV : ‖pV‖ ^ 2 = 1 / 2 :=
    norm_sq_planeVec (by rw [neg_sq]; simp only [r]; rw [sqrt_two_inv_sq]; ring)
  have hnormB : ‖pB‖ ^ 2 = 1 / 2 :=
    norm_sq_planeVec (by rw [neg_sq]; simp only [r]; rw [sqrt_two_inv_sq]; ring)
  have horthWA : ⟪pW, pA⟫_ℝ = 0 := by rw [inner_planeVec]; ring
  have horthAV : ⟪pA, pV⟫_ℝ = 0 := by rw [inner_planeVec]; ring
  have horthVB : ⟪pV, pB⟫_ℝ = 0 := by rw [inner_planeVec]; ring
  rw [SphereEmbeddable.iff_orthogonal]
  refine ⟨place, ?_, ?_, ?_⟩
  · intro x y h
    simp only [place] at h
    split_ifs at h
    all_goals
      first
      | (subst_eqs; rfl)
      | exact (hneWA h).elim | exact (hneWA h.symm).elim
      | exact (hneWV h).elim | exact (hneWV h.symm).elim
      | exact (hneWB h).elim | exact (hneWB h.symm).elim
      | exact (hneAV h).elim | exact (hneAV h.symm).elim
      | exact (hneAB h).elim | exact (hneAB h.symm).elim
      | exact (hneVB h).elim | exact (hneVB h.symm).elim
      | exact (hWiso y h).elim | exact ((hWiso x).symm h).elim
      | exact (hAiso y h).elim | exact ((hAiso x).symm h).elim
      | exact (hViso y h).elim | exact ((hViso x).symm h).elim
      | exact (hBiso y h).elim | exact ((hBiso x).symm h).elim
      | exact eq_of_isolate_upper e (by simpa [t] using h)
  · intro x
    by_cases hxw : x = w
    · rw [hxw, place_w]; exact hnormW
    · by_cases hxa : x = a
      · rw [hxa, place_a]; exact hnormA
      · by_cases hxv : x = v
        · rw [hxv, place_v]; exact hnormV
        · by_cases hxb : x = b
          · rw [hxb, place_b]; exact hnormB
          · rw [show place x = upperVec (t x) by simp [place, hxw, hxa, hxv, hxb]]
            exact norm_sq_upperVec (ht x).2.2
  · intro x y hxy
    have he : s(x, y) ∈ ({s(w, a), s(a, v), s(v, b)} : Finset (Sym2 V)) := by
      rw [← hE]; exact mem_edgeFinset.mpr hxy
    simp only [mem_insert, mem_singleton] at he
    rcases he with he | he | he
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [place_w, place_a]; exact horthWA
      · rw [place_a, place_w, real_inner_comm]; exact horthWA
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [place_a, place_v]; exact horthAV
      · rw [place_v, place_a, real_inner_comm]; exact horthAV
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [place_v, place_b]; exact horthVB
      · rw [place_b, place_v, real_inner_comm]; exact horthVB

private lemma sphere_of_path3_edge [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {a v b u w : V}
    (hav : a ≠ v) (hvb : v ≠ b) (hab : a ≠ b) (huw : u ≠ w)
    (hua : u ≠ a) (huv : u ≠ v) (hub : u ≠ b) (hwa : w ≠ a) (hwv : w ≠ v) (hwb : w ≠ b)
    (hE : G.edgeFinset = {s(a, v), s(v, b), s(u, w)}) : G.SphereEmbeddable 2 := by
  let e := Fintype.equivFin V
  let r : ℝ := (Real.sqrt 2)⁻¹
  let pA := planeVec r 0
  let pV := planeVec 0 r
  let pB := planeVec (-r) 0
  let pU := planeVec (1 / 2) (1 / 2)
  let pW := planeVec (-(1 / 2)) (1 / 2)
  let t (x : V) : ℝ := ((e x).val + 1 : ℝ) / (Fintype.card V + 2) * (1 / 4)
  let place (x : V) : EuclideanSpace ℝ (Fin 2) :=
    if x = a then pA else if x = v then pV else if x = b then pB else
      if x = u then pU else if x = w then pW else upperVec (t x)
  have ht (x : V) : 0 < t x ∧ t x < 1 / 4 ∧ (t x) ^ 2 ≤ 1 / 2 := by
    simpa [t, e] using isolate_coord_bounds (e x).isLt
  have place_a : place a = pA := by simp [place]
  have place_v : place v = pV := by simp [place, Ne.symm hav]
  have place_b : place b = pB := by simp [place, Ne.symm hab, Ne.symm hvb]
  have place_u : place u = pU := by simp [place, hua, huv, hub]
  have place_w : place w = pW := by simp [place, hwa, hwv, hwb, Ne.symm huw]
  have hne (x x' y y' : ℝ) (h : x ≠ x') : planeVec x y ≠ planeVec x' y' :=
    planeVec_ne_of_zero h
  have hAV : pA ≠ pV := hne _ _ _ _ sqrt_two_inv_pos.ne'
  have hAB : pA ≠ pB := hne _ _ _ _ (by intro h; linarith [sqrt_two_inv_pos])
  have hr_ne_half : r ≠ 1 / 2 := by
    intro h
    simp only [r] at h
    linarith [half_lt_sqrt_two_inv]
  have hAU : pA ≠ pU := hne _ _ _ _ hr_ne_half
  have hAW : pA ≠ pW := hne _ _ _ _ (by intro h; linarith [sqrt_two_inv_pos])
  have hVB : pV ≠ pB := hne _ _ _ _ (by intro h; linarith [sqrt_two_inv_pos])
  have hVU : pV ≠ pU := hne _ _ _ _ (by norm_num)
  have hVW : pV ≠ pW := hne _ _ _ _ (by norm_num)
  have hBU : pB ≠ pU := hne _ _ _ _ (by intro h; linarith [sqrt_two_inv_pos])
  have hBW : pB ≠ pW := hne _ _ _ _ (by
    intro h
    have : r = 1 / 2 := by linarith
    exact hr_ne_half this)
  have hUW : pU ≠ pW := hne _ _ _ _ (by norm_num)
  have hAiso (z : V) : pA ≠ upperVec (t z) :=
    (upperVec_ne_of_coord (ht z).1 (ht z).2.1 (axis_not_open_quarter r (Or.inl rfl))).symm
  have hViso (z : V) : pV ≠ upperVec (t z) :=
    (upperVec_ne_of_coord (ht z).1 (ht z).2.1 (axis_not_open_quarter 0 (Or.inr (Or.inl rfl)))).symm
  have hBiso (z : V) : pB ≠ upperVec (t z) :=
    (upperVec_ne_of_coord (ht z).1 (ht z).2.1
      (axis_not_open_quarter (-r) (Or.inr (Or.inr (Or.inl rfl))))).symm
  have hUiso (z : V) : pU ≠ upperVec (t z) :=
    (upperVec_ne_of_coord (ht z).1 (ht z).2.1
      (axis_not_open_quarter (1 / 2) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).symm
  have hWiso (z : V) : pW ≠ upperVec (t z) :=
    (upperVec_ne_of_coord (ht z).1 (ht z).2.1
      (axis_not_open_quarter (-(1 / 2)) (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))).symm
  have hnormA : ‖pA‖ ^ 2 = 1 / 2 :=
    norm_sq_planeVec (by simp only [r]; rw [sqrt_two_inv_sq]; ring)
  have hnormV : ‖pV‖ ^ 2 = 1 / 2 :=
    norm_sq_planeVec (by simp only [r]; rw [sqrt_two_inv_sq]; ring)
  have hnormB : ‖pB‖ ^ 2 = 1 / 2 :=
    norm_sq_planeVec (by rw [neg_sq]; simp only [r]; rw [sqrt_two_inv_sq]; ring)
  have hnormU : ‖pU‖ ^ 2 = 1 / 2 := norm_sq_planeVec (by norm_num)
  have hnormW : ‖pW‖ ^ 2 = 1 / 2 := norm_sq_planeVec (by norm_num)
  have horthAV : ⟪pA, pV⟫_ℝ = 0 := by rw [inner_planeVec]; ring
  have horthVB : ⟪pV, pB⟫_ℝ = 0 := by rw [inner_planeVec]; ring
  have horthUW : ⟪pU, pW⟫_ℝ = 0 := by rw [inner_planeVec]; norm_num
  rw [SphereEmbeddable.iff_orthogonal]
  refine ⟨place, ?_, ?_, ?_⟩
  · intro x y h
    simp only [place] at h
    split_ifs at h
    all_goals
      first
      | (subst_eqs; rfl)
      | exact (hAV h).elim | exact (hAV h.symm).elim
      | exact (hAB h).elim | exact (hAB h.symm).elim
      | exact (hAU h).elim | exact (hAU h.symm).elim
      | exact (hAW h).elim | exact (hAW h.symm).elim
      | exact (hVB h).elim | exact (hVB h.symm).elim
      | exact (hVU h).elim | exact (hVU h.symm).elim
      | exact (hVW h).elim | exact (hVW h.symm).elim
      | exact (hBU h).elim | exact (hBU h.symm).elim
      | exact (hBW h).elim | exact (hBW h.symm).elim
      | exact (hUW h).elim | exact (hUW h.symm).elim
      | exact (hAiso y h).elim | exact ((hAiso x).symm h).elim
      | exact (hViso y h).elim | exact ((hViso x).symm h).elim
      | exact (hBiso y h).elim | exact ((hBiso x).symm h).elim
      | exact (hUiso y h).elim | exact ((hUiso x).symm h).elim
      | exact (hWiso y h).elim | exact ((hWiso x).symm h).elim
      | exact eq_of_isolate_upper e (by simpa [t] using h)
  · intro x
    by_cases hxa : x = a
    · rw [hxa, place_a]; exact hnormA
    · by_cases hxv : x = v
      · rw [hxv, place_v]; exact hnormV
      · by_cases hxb : x = b
        · rw [hxb, place_b]; exact hnormB
        · by_cases hxu : x = u
          · rw [hxu, place_u]; exact hnormU
          · by_cases hxw : x = w
            · rw [hxw, place_w]; exact hnormW
            · rw [show place x = upperVec (t x) by simp [place, hxa, hxv, hxb, hxu, hxw]]
              exact norm_sq_upperVec (ht x).2.2
  · intro x y hxy
    have he : s(x, y) ∈ ({s(a, v), s(v, b), s(u, w)} : Finset (Sym2 V)) := by
      rw [← hE]; exact mem_edgeFinset.mpr hxy
    simp only [mem_insert, mem_singleton] at he
    rcases he with he | he | he
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [place_a, place_v]; exact horthAV
      · rw [place_v, place_a, real_inner_comm]; exact horthAV
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [place_v, place_b]; exact horthVB
      · rw [place_b, place_v, real_inner_comm]; exact horthVB
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [place_u, place_w]; exact horthUW
      · rw [place_w, place_u, real_inner_comm]; exact horthUW

private lemma sym2_ne_of_not_pairs {a v b w : V} (hwv : w ≠ v) (hwa : w ≠ a) (hav : a ≠ v)
    (hab : a ≠ b) (hwb : w ≠ b) :
    s(w, a) ≠ s(a, v) ∧ s(w, a) ≠ s(v, b) ∧ s(a, v) ≠ s(v, b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hwa h1
    · exact hwv h1
  · intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hwv h1
    · exact hwb h1
  · intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hav h1
    · exact hab h1

private lemma sphereEmbeddable_two_of_ncard_edgeSet_le {V : Type*} [Finite V]
    (G : SimpleGraph V) (hE : G.edgeSet.ncard ≤ 3) (hK : G.CliqueFree 3)
    (hFree : (completeMinusTriangle 4).Free G) : G.SphereEmbeddable 2 := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  by_cases hdeg1 : ∀ v, G.degree v ≤ 1
  · exact SphereEmbeddable.of_degree_le_two hdeg1
  · push Not at hdeg1
    obtain ⟨v, hv⟩ := hdeg1
    have hvle : G.degree v ≤ 2 := degree_le_two_of_free_completeMinusTriangle_four hFree v
    have hv2 : G.degree v = 2 := by omega
    obtain ⟨a, b, hab, hva, hvb, hN⟩ := exists_two_neighbors hv2
    have hnab : ¬ G.Adj a b := not_adj_triangle hK hva hvb hab
    have hda : G.degree a ≤ 2 := degree_le_two_of_free_completeMinusTriangle_four hFree a
    have hdb : G.degree b ≤ 2 := degree_le_two_of_free_completeMinusTriangle_four hFree b
    have hda0 : 1 ≤ G.degree a := by
      have hpos : 0 < G.degree a := by
        rw [degree_pos_iff_exists_adj]
        exact ⟨v, hva.symm⟩
      omega
    have hdb0 : 1 ≤ G.degree b := by
      have hpos : 0 < G.degree b := by
        rw [degree_pos_iff_exists_adj]
        exact ⟨v, hvb.symm⟩
      omega
    have hEn : #G.edgeFinset ≤ 3 := by
      rw [← edgeSet_ncard_eq]
      exact hE
    by_cases ha2 : G.degree a = 2
    · obtain ⟨w, hwv, hwa_adj, hNa⟩ := exists_other_neighbor ha2 hva.symm
      have hwb_ne : w ≠ b := by
        intro h
        exact hnab (h ▸ hwa_adj)
      have hwa_ne : w ≠ a := hwa_adj.ne.symm
      have hnes := sym2_ne_of_not_pairs hwv hwa_ne hva.ne.symm hab hwb_ne
      have hsub : ({s(w, a), s(a, v), s(v, b)} : Finset (Sym2 V)) ⊆ G.edgeFinset := by
        intro e he
        simp only [mem_insert, mem_singleton] at he
        rw [mem_edgeFinset]
        rcases he with rfl | rfl | rfl
        · simpa [mem_edgeSet] using hwa_adj.symm
        · simpa [mem_edgeSet] using hva.symm
        · simpa [mem_edgeSet] using hvb
      have hthree : #({s(w, a), s(a, v), s(v, b)} : Finset (Sym2 V)) = 3 := by
        simp [hnes.1, hnes.2.1, hnes.2.2]
      have heq : G.edgeFinset = {s(w, a), s(a, v), s(v, b)} :=
        (eq_of_subset_of_card_le hsub (by rw [← hthree] at hEn; exact hEn)).symm
      exact sphere_of_path4 hwa_ne hva.ne.symm hvb.ne hwv hwb_ne hab heq
    · by_cases hb2 : G.degree b = 2
      · obtain ⟨w, hwv, hwb_adj, _⟩ := exists_other_neighbor hb2 hvb.symm
        have hwa_ne_b : w ≠ a := by
          intro h
          exact hnab (h ▸ hwb_adj.symm)
        have hwb_ne : w ≠ b := hwb_adj.ne.symm
        have hnes := sym2_ne_of_not_pairs hwv hwb_ne hvb.ne.symm (Ne.symm hab) hwa_ne_b
        have hsub : ({s(w, b), s(b, v), s(v, a)} : Finset (Sym2 V)) ⊆ G.edgeFinset := by
          intro e he
          simp only [mem_insert, mem_singleton] at he
          rw [mem_edgeFinset]
          rcases he with rfl | rfl | rfl
          · simpa [mem_edgeSet] using hwb_adj.symm
          · simpa [mem_edgeSet] using hvb.symm
          · simpa [mem_edgeSet] using hva
        have hthree : #({s(w, b), s(b, v), s(v, a)} : Finset (Sym2 V)) = 3 := by
          simp [hnes.1, hnes.2.1, hnes.2.2]
        have heq : G.edgeFinset = {s(w, b), s(b, v), s(v, a)} :=
          (eq_of_subset_of_card_le hsub (by rw [← hthree] at hEn; exact hEn)).symm
        exact sphere_of_path4 hwb_ne hvb.ne.symm hva.ne hwv hwa_ne_b (Ne.symm hab) heq
      · have ha1 : G.degree a = 1 := by omega
        have hb1 : G.degree b = 1 := by omega
        have hNa : G.neighborFinset a = {v} := by
          have hcardA : #(G.neighborFinset a) = 1 := by
            rw [card_neighborFinset_eq_degree, ha1]
          obtain ⟨z, hz⟩ := card_eq_one.mp hcardA
          have hvmem : v ∈ G.neighborFinset a := by simpa [mem_neighborFinset] using hva.symm
          have hzv : z = v := by
            rw [hz] at hvmem
            simp at hvmem
            exact hvmem.symm
          simp [hz, hzv]
        have hNb : G.neighborFinset b = {v} := by
          have hcardB : #(G.neighborFinset b) = 1 := by
            rw [card_neighborFinset_eq_degree, hb1]
          obtain ⟨z, hz⟩ := card_eq_one.mp hcardB
          have hvmem : v ∈ G.neighborFinset b := by simpa [mem_neighborFinset] using hvb.symm
          have hzv : z = v := by
            rw [hz] at hvmem
            simp at hvmem
            exact hvmem.symm
          simp [hz, hzv]
        have hpair_ne : s(a, v) ≠ s(v, b) := by
          intro h
          rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hva.ne h1.symm
          · exact hab h1
        have hpair : ({s(a, v), s(v, b)} : Finset (Sym2 V)) ⊆ G.edgeFinset := by
          intro e he
          simp only [mem_insert, mem_singleton] at he
          rw [mem_edgeFinset]
          rcases he with rfl | rfl
          · simpa [mem_edgeSet] using hva.symm
          · simpa [mem_edgeSet] using hvb
        have hpairCard : #({s(a, v), s(v, b)} : Finset (Sym2 V)) = 2 := by
          simp [hpair_ne]
        have hge : 2 ≤ #G.edgeFinset := by
          rw [← hpairCard]
          exact card_le_card hpair
        by_cases honly : #G.edgeFinset = 2
        · have heq : G.edgeFinset = {s(a, v), s(v, b)} :=
            (eq_of_subset_of_card_le hpair (by rw [honly, hpairCard])).symm
          exact sphere_of_path3 hva.ne.symm hvb.ne hab heq
        · have h3 : #G.edgeFinset = 3 := by omega
          have hdiff : #(G.edgeFinset \ {s(a, v), s(v, b)}) = 1 := by
            rw [card_sdiff_of_subset hpair, hpairCard, h3]
          obtain ⟨e, he⟩ := card_eq_one.mp hdiff
          have hemem : e ∈ G.edgeFinset \ {s(a, v), s(v, b)} := by
            rw [he]
            simp
          induction e using Sym2.inductionOn with
          | hf u w =>
            have huw : G.Adj u w := by
              simpa [mem_edgeFinset, mem_edgeSet] using (mem_sdiff.mp hemem).1
            have hnot : s(u, w) ∉ ({s(a, v), s(v, b)} : Finset _) := (mem_sdiff.mp hemem).2
            have hu_a : u ≠ a := by
              intro hua
              have hwv' : w = v := by
                have : w ∈ G.neighborFinset a := by
                  simpa [mem_neighborFinset, hua] using huw
                simpa [hNa] using this
              apply hnot
              simp [hua, hwv']
            have hw_a : w ≠ a := by
              intro hwa
              have huv' : u = v := by
                have : u ∈ G.neighborFinset a := by
                  simpa [mem_neighborFinset, hwa] using huw.symm
                simpa [hNa] using this
              apply hnot
              simp [hwa, huv']
            have hu_b : u ≠ b := by
              intro hub
              have hwv' : w = v := by
                have : w ∈ G.neighborFinset b := by
                  simpa [mem_neighborFinset, hub] using huw
                simpa [hNb] using this
              apply hnot
              simp [hub, hwv']
            have hw_b : w ≠ b := by
              intro hwb
              have huv' : u = v := by
                have : u ∈ G.neighborFinset b := by
                  simpa [mem_neighborFinset, hwb] using huw.symm
                simpa [hNb] using this
              apply hnot
              simp [hwb, huv']
            have hu_v : u ≠ v := by
              intro huv
              have hwab : w = a ∨ w = b := by
                have : w ∈ G.neighborFinset v := by
                  simpa [mem_neighborFinset, huv] using huw
                simpa [hN] using this
              rcases hwab with hwa | hwb
              · apply hnot
                simp [huv, hwa]
              · apply hnot
                simp [huv, hwb]
            have hw_v : w ≠ v := by
              intro hwv
              have huab : u = a ∨ u = b := by
                have : u ∈ G.neighborFinset v := by
                  simpa [mem_neighborFinset, hwv] using huw.symm
                simpa [hN] using this
              rcases huab with hua | hub
              · apply hnot
                simp [hwv, hua]
              · apply hnot
                simp [hwv, hub]
            have hsub : ({s(a, v), s(v, b), s(u, w)} : Finset (Sym2 V)) ⊆ G.edgeFinset := by
              intro e' he'
              simp only [mem_insert, mem_singleton] at he'
              rw [mem_edgeFinset]
              rcases he' with rfl | rfl | rfl
              · simpa [mem_edgeSet] using hva.symm
              · simpa [mem_edgeSet] using hvb
              · simpa [mem_edgeSet] using huw
            have hne1 : s(a, v) ≠ s(u, w) := by
              intro h
              rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
              · exact hu_a h1.symm
              · exact hw_a h1.symm
            have hne2 : s(v, b) ≠ s(u, w) := by
              intro h
              rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
              · exact hu_v h1.symm
              · exact hw_v h1.symm
            have hthree : #({s(a, v), s(v, b), s(u, w)} : Finset (Sym2 V)) = 3 := by
              simp [hpair_ne, hne1, hne2]
            have heq : G.edgeFinset = {s(a, v), s(v, b), s(u, w)} :=
              (eq_of_subset_of_card_le hsub (by rw [← hthree] at hEn; exact hEn)).symm
            exact sphere_of_path3_edge hva.ne.symm hvb.ne hab huw.ne
              hu_a hu_v hu_b hw_a hw_v hw_b heq

@[expose] public section

/-- **FKS `S(2)`.** A finite graph with at most three edges has a unit-distance placement in
`ℝ²`. If it contains neither `K₃` nor `K₄ − K₃`, it also lies on the circle of radius `1/√2`. -/
theorem fksStatement_two : FKSStatement 2 := by
  intro V _ G hE
  rw [fksBudget_two] at hE
  refine ⟨unitDistEmbeddable_two_of_ncard_edgeSet_le G hE, ?_⟩
  intro hK hFree
  exact sphereEmbeddable_two_of_ncard_edgeSet_le G hE hK hFree

end

end

end SimpleGraph

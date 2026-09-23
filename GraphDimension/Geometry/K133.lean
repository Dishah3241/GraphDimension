/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps

import GraphDimension.Geometry.FinLe
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `K₁,₃,₃` has dimension 5

The complete tripartite graph with part sizes `1, 3, 3`, written
`completeMultipartiteGraph fun i : Fin 3 => Fin (![1, 3, 3] i)`.

The lower bound is that this graph has no unit-distance placement in `ℝ⁴`. Both parts of size
three lie on the sphere centred at the apex. Translating the apex to the origin makes the six
points unit vectors whose cross inner products are all `1/2`, so each difference of one part is
orthogonal to the span of the other. A collinear part admits no equidistant point. Otherwise that
span has dimension 3 and the difference span has dimension 2, which cannot fit in the orthogonal
of a 3-dimensional subspace of `ℝ⁴`.

The upper bound is an explicit placement in `ℝ⁵`: the two triples sit in orthogonal coordinate
2-planes, at equal height along the fifth axis, and the apex sits at the origin.

## References

Chaffee and Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J.
Combin. **64(2)** (2016), 327–333, Theorem 8. Their upper bound is the inclusion in `K₇ − e`;
the witness here is written in coordinates. Their lower bound rotates one part into a coordinate
plane; the argument here is the orthogonal-complement count above.
-/

namespace SimpleGraph

noncomputable section

open Module Submodule Matrix
open scoped RealInnerProductSpace

private abbrev Vertex := Σ i : Fin 3, Fin (![1, 3, 3] i)

private lemma inner_eq_neg_half {x y : EuclideanSpace ℝ (Fin 4)} (h : ‖x‖ = ‖y‖) :
    ⟪y, x - y⟫ = -‖x - y‖ ^ 2 / 2 := by
  have hexp := norm_add_sq_real y (x - y)
  rw [add_sub_cancel, h] at hexp
  have h2 : 2 * ⟪y, x - y⟫ = -‖x - y‖ ^ 2 := by linarith
  rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
  linarith

/-- Three distinct points at equal distance from the origin are not collinear. The common
distance forces the coefficient of the second difference, along the first, to be `0` or `1`. -/
private lemma false_of_dependent (p : Fin 3 → EuclideanSpace ℝ (Fin 4))
    (hp : Function.Injective p) (hnorm : ∀ i, ‖p i‖ = ‖p 0‖)
    (hdep : ¬ LinearIndependent ℝ ![p 1 - p 0, p 2 - p 0]) : False := by
  set d := p 1 - p 0
  have hd : d ≠ 0 := by
    intro h
    exact hp.ne (by decide : (1 : Fin 3) ≠ 0) (sub_eq_zero.mp h)
  rw [LinearIndependent.pair_iff' hd] at hdep
  push Not at hdep
  obtain ⟨r, hr⟩ := hdep
  have hx := inner_eq_neg_half (hnorm 1)
  have hy := inner_eq_neg_half (hnorm 2)
  rw [← hr] at hy
  have hmul : ⟪p 0, r • d⟫ = r * ⟪p 0, d⟫ := inner_smul_right _ _ _
  have hnorm_smul : ‖r • d‖ ^ 2 = r ^ 2 * ‖d‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hx2 : ⟪p 0, d⟫ * 2 = -‖d‖ ^ 2 := by
    rw [hx, div_mul_cancel₀ _ (by norm_num)]
  have hy2 : ⟪p 0, r • d⟫ * 2 = -‖r • d‖ ^ 2 := by
    rw [hy, div_mul_cancel₀ _ (by norm_num)]
  have hrN : r * ‖d‖ ^ 2 = r ^ 2 * ‖d‖ ^ 2 := by
    have hneg : -(r * ‖d‖ ^ 2) = -(r ^ 2 * ‖d‖ ^ 2) := by
      calc
        -(r * ‖d‖ ^ 2) = r * (-‖d‖ ^ 2) := by ring
        _ = r * (⟪p 0, d⟫ * 2) := by rw [hx2]
        _ = (r * ⟪p 0, d⟫) * 2 := by ring
        _ = ⟪p 0, r • d⟫ * 2 := by rw [hmul]
        _ = -‖r • d‖ ^ 2 := hy2
        _ = -(r ^ 2 * ‖d‖ ^ 2) := by rw [hnorm_smul]
    exact neg_inj.mp hneg
  have hdiff : (r - r ^ 2) * ‖d‖ ^ 2 = 0 := by
    rw [sub_mul, sub_eq_zero]
    exact hrN
  have hd2 : ‖d‖ ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hd))
  have hrsub : r - r ^ 2 = 0 := (mul_eq_zero.mp hdiff).resolve_right hd2
  have hfac : r * (1 - r) = 0 := by
    have : r - r ^ 2 = r * (1 - r) := by ring
    rw [← this]
    exact hrsub
  rcases mul_eq_zero.mp hfac with rfl | hr1
  · rw [zero_smul] at hr
    exact hp.ne (by decide : (2 : Fin 3) ≠ 0) (sub_eq_zero.mp hr.symm)
  · have hr1' : r = 1 := (sub_eq_zero.mp hr1).symm
    rw [hr1', one_smul] at hr
    have hp12 : p 1 = p 2 := by
      have hr' : p 1 - p 0 = p 2 - p 0 := by simpa [d] using hr
      have := congrArg (fun z => z + p 0) hr'
      simpa using this
    exact hp.ne (by decide : (1 : Fin 3) ≠ 2) hp12

/-- In `ℝ⁴`, two injective triples of unit vectors with all cross inner products equal to `1/2`
are impossible once neither triple is collinear. The differences of the first are orthogonal to
the span of the second, and those dimensions add to 5. -/
private lemma false_of_independent
    (A B : Fin 3 → EuclideanSpace ℝ (Fin 4))
    (hA : LinearIndependent ℝ ![A 1 - A 0, A 2 - A 0])
    (hB : LinearIndependent ℝ ![B 1 - B 0, B 2 - B 0])
    (hinner : ∀ i j, ⟪A i, B j⟫ = 1 / 2) : False := by
  have hB3 : LinearIndependent ℝ ![B 0, B 1, B 2] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg3 : g 0 • B 0 + g 1 • B 1 + g 2 • B 2 = 0 := by
      simpa [Fin.sum_univ_three] using hg
    have hsumg : g 0 + g 1 + g 2 = 0 := by
      have h0 : ⟪A 0, g 0 • B 0 + g 1 • B 1 + g 2 • B 2⟫ = 0 := by
        rw [hg3, inner_zero_right]
      rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
        inner_smul_right, hinner, hinner, hinner] at h0
      linarith
    have hrest : g 1 • (B 1 - B 0) + g 2 • (B 2 - B 0) = 0 := by
      have hcomb :
          g 0 • B 0 + g 1 • B 1 + g 2 • B 2 =
            (g 0 + g 1 + g 2) • B 0 + g 1 • (B 1 - B 0) + g 2 • (B 2 - B 0) := by
        module
      rw [hcomb, hsumg, zero_smul, zero_add] at hg3
      exact hg3
    have hpair := (Fintype.linearIndependent_iff).mp hB
    have hg1 : g 1 = 0 := by
      have := hpair ![g 1, g 2]
      simpa [Fin.sum_univ_two] using this (by simpa [Fin.sum_univ_two] using hrest) 0
    have hg2 : g 2 = 0 := by
      have := hpair ![g 1, g 2]
      simpa [Fin.sum_univ_two] using this (by simpa [Fin.sum_univ_two] using hrest) 1
    have hg0 : g 0 = 0 := by
      rw [hg1, hg2, add_zero, add_zero] at hsumg
      exact hsumg
    fin_cases i <;> assumption
  let KA : Submodule ℝ (EuclideanSpace ℝ (Fin 4)) :=
    span ℝ (Set.range ![A 1 - A 0, A 2 - A 0])
  let SB : Submodule ℝ (EuclideanSpace ℝ (Fin 4)) :=
    span ℝ (Set.range ![B 0, B 1, B 2])
  have hKAfin : finrank ℝ KA = 2 := by
    rw [finrank_span_eq_card hA, Fintype.card_fin]
  have hSBfin : finrank ℝ SB = 3 := by
    rw [finrank_span_eq_card hB3, Fintype.card_fin]
  have horth (k : Fin 2) (j : Fin 3) :
      ⟪![A 1 - A 0, A 2 - A 0] k, B j⟫ = 0 := by
    fin_cases k <;> simp [inner_sub_left, hinner]
  have hBapply (j : Fin 3) : ![B 0, B 1, B 2] j = B j := by
    fin_cases j <;> rfl
  have hle : KA ≤ SBᗮ := by
    rw [span_le]
    rintro _ ⟨k, rfl⟩
    refine (mem_orthogonal' SB (![A 1 - A 0, A 2 - A 0] k)).mpr ?_
    intro y hy
    obtain ⟨c, hc⟩ :=
      (mem_span_range_iff_exists_fun (R := ℝ) (v := ![B 0, B 1, B 2]) (x := y)).mp hy
    rw [← hc, inner_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [inner_smul_right, hBapply j, horth k j, mul_zero]
  have hsum := finrank_add_finrank_orthogonal SB
  rw [finrank_euclideanSpace_fin] at hsum
  have hmono : finrank ℝ KA ≤ finrank ℝ SBᗮ := finrank_mono hle
  have : 5 ≤ 4 := by
    calc
      (5 : ℕ) = 2 + 3 := by norm_num
      _ = finrank ℝ KA + finrank ℝ SB := by rw [hKAfin, hSBfin]
      _ ≤ finrank ℝ SBᗮ + finrank ℝ SB := Nat.add_le_add_right hmono _
      _ = 4 := by rw [Nat.add_comm, hsum]
  exact absurd this (by decide)

/-- No two injective triples of unit vectors in `ℝ⁴` have every cross inner product equal to
`1/2`. -/
private lemma false_of_unit_constant_inner
    (A B : Fin 3 → EuclideanSpace ℝ (Fin 4))
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hAn : ∀ i, ‖A i‖ = 1) (hBn : ∀ j, ‖B j‖ = 1)
    (hinner : ∀ i j, ⟪A i, B j⟫ = 1 / 2) : False := by
  have hAnorm : ∀ i, ‖A i‖ = ‖A 0‖ := by
    intro i
    rw [hAn i, hAn 0]
  have hBnorm : ∀ j, ‖B j‖ = ‖B 0‖ := by
    intro j
    rw [hBn j, hBn 0]
  by_cases hAli : LinearIndependent ℝ ![A 1 - A 0, A 2 - A 0]
  · by_cases hBli : LinearIndependent ℝ ![B 1 - B 0, B 2 - B 0]
    · exact false_of_independent A B hAli hBli hinner
    · exact false_of_dependent B hB hBnorm hBli
  · exact false_of_dependent A hA hAnorm hAli

/-! ### A placement in `ℝ⁵` -/

private def halfSqrt2 : ℝ := Real.sqrt 2 / 2

private def quarterSqrt2 : ℝ := Real.sqrt 2 / 4

private def quarterSqrt6 : ℝ := Real.sqrt 6 / 4

private lemma halfSqrt2_sq : halfSqrt2 ^ 2 = 1 / 2 := by
  unfold halfSqrt2
  rw [div_pow, Real.sq_sqrt (by positivity)]
  norm_num

private lemma quarter_norm_sq : quarterSqrt2 ^ 2 + quarterSqrt6 ^ 2 = 1 / 2 := by
  unfold quarterSqrt2 quarterSqrt6
  rw [div_pow, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  norm_num

private lemma halfSqrt2_pos : 0 < halfSqrt2 := by
  unfold halfSqrt2
  positivity

private lemma quarterSqrt2_pos : 0 < quarterSqrt2 := by
  unfold quarterSqrt2
  positivity

private lemma quarterSqrt6_pos : 0 < quarterSqrt6 := by
  unfold quarterSqrt6
  positivity

private lemma halfSqrt2_ne_neg_quarter : halfSqrt2 ≠ -quarterSqrt2 := by
  linarith [halfSqrt2_pos, quarterSqrt2_pos]

private lemma quarterSqrt6_ne_neg : quarterSqrt6 ≠ -quarterSqrt6 := by
  linarith [quarterSqrt6_pos]

/-- First coordinate of the model triangle in a coordinate 2-plane. -/
private def triX : Fin 3 → ℝ
  | 0 => halfSqrt2
  | 1 => -quarterSqrt2
  | 2 => -quarterSqrt2

/-- Second coordinate of the model triangle. -/
private def triY : Fin 3 → ℝ
  | 0 => 0
  | 1 => quarterSqrt6
  | 2 => -quarterSqrt6

private lemma triX_ne_zero (j : Fin 3) : triX j ≠ 0 := by
  fin_cases j <;> simp only [triX]
  · exact halfSqrt2_pos.ne'
  · exact neg_ne_zero.mpr quarterSqrt2_pos.ne'
  · exact neg_ne_zero.mpr quarterSqrt2_pos.ne'

private lemma tri_norm_sq (j : Fin 3) : triX j ^ 2 + triY j ^ 2 = 1 / 2 := by
  fin_cases j
  · simp only [triX, triY, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
    exact halfSqrt2_sq
  · simp only [triX, triY, neg_sq]
    exact quarter_norm_sq
  · simp only [triX, triY, neg_sq]
    exact quarter_norm_sq

private lemma triX_zero : triX 0 = halfSqrt2 := rfl

private lemma triX_one : triX 1 = -quarterSqrt2 := rfl

private lemma triX_two : triX 2 = -quarterSqrt2 := rfl

private lemma triY_one : triY 1 = quarterSqrt6 := rfl

private lemma triY_two : triY 2 = -quarterSqrt6 := rfl

private lemma tri_injective : Function.Injective fun j : Fin 3 => (triX j, triY j) := by
  intro i j hij
  have hx : triX i = triX j := (Prod.ext_iff.mp hij).1
  have hy : triY i = triY j := (Prod.ext_iff.mp hij).2
  match i, j with
  | 0, 0 => rfl
  | 0, 1 =>
      rw [triX_zero, triX_one] at hx
      exact absurd hx halfSqrt2_ne_neg_quarter
  | 0, 2 =>
      rw [triX_zero, triX_two] at hx
      exact absurd hx halfSqrt2_ne_neg_quarter
  | 1, 0 =>
      rw [triX_one, triX_zero] at hx
      exact absurd hx.symm halfSqrt2_ne_neg_quarter
  | 1, 1 => rfl
  | 1, 2 =>
      rw [triY_one, triY_two] at hy
      exact absurd hy quarterSqrt6_ne_neg
  | 2, 0 =>
      rw [triX_two, triX_zero] at hx
      exact absurd hx.symm halfSqrt2_ne_neg_quarter
  | 2, 1 =>
      rw [triY_two, triY_one] at hy
      exact absurd hy.symm quarterSqrt6_ne_neg
  | 2, 2 => rfl

private def aPt (j : Fin 3) : EuclideanSpace ℝ (Fin 5) :=
  !₂[triX j, triY j, 0, 0, halfSqrt2]

private def bPt (j : Fin 3) : EuclideanSpace ℝ (Fin 5) :=
  !₂[0, 0, triX j, triY j, halfSqrt2]

private def place : Vertex → EuclideanSpace ℝ (Fin 5)
  | ⟨0, _⟩ => 0
  | ⟨1, j⟩ => aPt j
  | ⟨2, j⟩ => bPt j

private lemma norm_sq_aPt (j : Fin 3) : ‖aPt j‖ ^ 2 = 1 := by
  rw [aPt, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_five]
  simp only [cons_val_zero, cons_val_one, cons_val_two, cons_val_three, cons_val_four, head_cons,
    tail_cons, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
  rw [tri_norm_sq j, halfSqrt2_sq]
  norm_num

private lemma norm_sq_bPt (j : Fin 3) : ‖bPt j‖ ^ 2 = 1 := by
  rw [bPt, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_five]
  simp only [cons_val_zero, cons_val_one, cons_val_two, cons_val_three, cons_val_four, head_cons,
    tail_cons, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, add_zero]
  rw [tri_norm_sq j, halfSqrt2_sq]
  norm_num

private lemma dist_zero_aPt (j : Fin 3) : dist (0 : EuclideanSpace ℝ (Fin 5)) (aPt j) = 1 := by
  have hsq : ‖aPt j‖ ^ 2 = 1 := norm_sq_aPt j
  have hdist : dist (0 : EuclideanSpace ℝ (Fin 5)) (aPt j) = ‖aPt j‖ := by
    rw [dist_eq_norm, zero_sub, norm_neg]
  rw [← Real.sqrt_sq (dist_nonneg (x := (0 : EuclideanSpace ℝ (Fin 5))) (y := aPt j)), hdist, hsq,
    Real.sqrt_one]

private lemma dist_zero_bPt (j : Fin 3) : dist (0 : EuclideanSpace ℝ (Fin 5)) (bPt j) = 1 := by
  have hsq : ‖bPt j‖ ^ 2 = 1 := norm_sq_bPt j
  have hdist : dist (0 : EuclideanSpace ℝ (Fin 5)) (bPt j) = ‖bPt j‖ := by
    rw [dist_eq_norm, zero_sub, norm_neg]
  rw [← Real.sqrt_sq (dist_nonneg (x := (0 : EuclideanSpace ℝ (Fin 5))) (y := bPt j)), hdist, hsq,
    Real.sqrt_one]

private lemma dist_aPt_bPt (i j : Fin 3) : dist (aPt i) (bPt j) = 1 := by
  have hsq : dist (aPt i) (bPt j) ^ 2 = 1 := by
    rw [aPt, bPt, EuclideanSpace.dist_sq_eq, Fin.sum_univ_five]
    simp only [Real.dist_eq, sq_abs, cons_val_zero, cons_val_one, cons_val_two, cons_val_three,
      cons_val_four, head_cons, tail_cons, sub_zero, zero_sub, neg_sq, sub_self,
      zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
    rw [tri_norm_sq i, add_assoc, tri_norm_sq j]
    norm_num
  rw [← Real.sqrt_sq (dist_nonneg (x := aPt i) (y := bPt j)), hsq, Real.sqrt_one]

private lemma aPt_injective : Function.Injective aPt := by
  intro i j hij
  have hx : triX i = triX j := by
    have := congrArg (fun z : EuclideanSpace ℝ (Fin 5) => z.ofLp 0) hij
    simpa [aPt, cons_val_zero] using this
  have hy : triY i = triY j := by
    have := congrArg (fun z : EuclideanSpace ℝ (Fin 5) => z.ofLp 1) hij
    simpa [aPt, cons_val_one] using this
  exact tri_injective (Prod.ext hx hy)

private lemma bPt_injective : Function.Injective bPt := by
  intro i j hij
  have hx : triX i = triX j := by
    have := congrArg (fun z : EuclideanSpace ℝ (Fin 5) => z.ofLp 2) hij
    simpa [bPt, cons_val_two] using this
  have hy : triY i = triY j := by
    have := congrArg (fun z : EuclideanSpace ℝ (Fin 5) => z.ofLp 3) hij
    simpa [bPt, cons_val_three] using this
  exact tri_injective (Prod.ext hx hy)

private lemma fin1_unique (a b : Fin (![1, 3, 3] 0)) : a = b := by
  apply Fin.ext
  have hsize : ![1, 3, 3] (0 : Fin 3) = 1 := rfl
  have ha : a.val = 0 := Nat.lt_one_iff.mp (by simpa [hsize] using a.isLt)
  have hb : b.val = 0 := Nat.lt_one_iff.mp (by simpa [hsize] using b.isLt)
  rw [ha, hb]

private lemma place_injective : Function.Injective place := by
  intro u v huv
  match u, v with
  | ⟨0, a⟩, ⟨0, b⟩ =>
      cases fin1_unique a b
      rfl
  | ⟨0, _⟩, ⟨1, j⟩ =>
      have hx : (0 : ℝ) = triX j := by
        have := congrArg (fun z : EuclideanSpace ℝ (Fin 5) => z.ofLp 0) huv
        simpa [place, aPt, cons_val_zero] using this
      exact absurd hx.symm (triX_ne_zero j)
  | ⟨0, _⟩, ⟨2, j⟩ =>
      have hz : (0 : ℝ) = triX j := by
        have := congrArg (fun z : EuclideanSpace ℝ (Fin 5) => z.ofLp 2) huv
        simpa [place, bPt, cons_val_two] using this
      exact absurd hz.symm (triX_ne_zero j)
  | ⟨1, j⟩, ⟨0, _⟩ =>
      have hx : triX j = 0 := by
        have := congrArg (fun z : EuclideanSpace ℝ (Fin 5) => z.ofLp 0) huv
        simpa [place, aPt, cons_val_zero] using this
      exact absurd hx (triX_ne_zero j)
  | ⟨1, i⟩, ⟨1, j⟩ =>
      cases aPt_injective (by simpa [place] using huv)
      rfl
  | ⟨1, i⟩, ⟨2, _⟩ =>
      have hx : triX i = 0 := by
        have := congrArg (fun z : EuclideanSpace ℝ (Fin 5) => z.ofLp 0) huv
        simpa [place, aPt, bPt, cons_val_zero] using this
      exact absurd hx (triX_ne_zero i)
  | ⟨2, j⟩, ⟨0, _⟩ =>
      have hz : triX j = 0 := by
        have := congrArg (fun z : EuclideanSpace ℝ (Fin 5) => z.ofLp 2) huv
        simpa [place, bPt, cons_val_two] using this
      exact absurd hz (triX_ne_zero j)
  | ⟨2, _⟩, ⟨1, i⟩ =>
      have hx : (0 : ℝ) = triX i := by
        have := congrArg (fun z : EuclideanSpace ℝ (Fin 5) => z.ofLp 0) huv
        simpa [place, aPt, bPt, cons_val_zero] using this
      exact absurd hx.symm (triX_ne_zero i)
  | ⟨2, i⟩, ⟨2, j⟩ =>
      cases bPt_injective (by simpa [place] using huv)
      rfl

private lemma dist_apex_part1 (j : Fin 3) :
    dist (place ⟨0, (0 : Fin 1)⟩) (place ⟨1, j⟩) = 1 := by
  simpa [place] using dist_zero_aPt j

private lemma dist_apex_part2 (j : Fin 3) :
    dist (place ⟨0, (0 : Fin 1)⟩) (place ⟨2, j⟩) = 1 := by
  simpa [place] using dist_zero_bPt j

private lemma dist_part1_part2 (i j : Fin 3) :
    dist (place ⟨1, i⟩) (place ⟨2, j⟩) = 1 := by
  simpa [place] using dist_aPt_bPt i j

@[expose] public section

/-- **Lower bound** for the dimension of `K₁,₃,₃`: the complete tripartite graph with part sizes
`1, 3, 3` admits no injective placement in `ℝ⁴` realising every edge as a unit segment
(Chaffee–Noble Theorem 8). -/
theorem not_unitDistEmbeddable_completeMultipartiteGraph_one_three_three :
    ¬ (completeMultipartiteGraph fun i : Fin 3 => Fin (![1, 3, 3] i)).UnitDistEmbeddable 4 := by
  intro h
  obtain ⟨f, hfInj, hfDist⟩ := h
  let apex : EuclideanSpace ℝ (Fin 4) := f ⟨0, (0 : Fin 1)⟩
  let a : Fin 3 → EuclideanSpace ℝ (Fin 4) := fun j => f ⟨1, j⟩
  let b : Fin 3 → EuclideanSpace ℝ (Fin 4) := fun j => f ⟨2, j⟩
  have ha : Function.Injective a := by
    intro i j hij
    obtain ⟨-, hsnd⟩ := Sigma.mk.inj_iff.mp (hfInj hij)
    exact eq_of_heq hsnd
  have hb : Function.Injective b := by
    intro i j hij
    obtain ⟨-, hsnd⟩ := Sigma.mk.inj_iff.mp (hfInj hij)
    exact eq_of_heq hsnd
  have hpa : ∀ i, dist apex (a i) = 1 := by
    intro i
    exact hfDist ⟨0, (0 : Fin 1)⟩ ⟨1, i⟩
      (by simp [completeMultipartiteGraph, comap_adj, top_adj])
  have hpb : ∀ j, dist apex (b j) = 1 := by
    intro j
    exact hfDist ⟨0, (0 : Fin 1)⟩ ⟨2, j⟩
      (by simp [completeMultipartiteGraph, comap_adj, top_adj])
  have hcross : ∀ i j, dist (a i) (b j) = 1 := by
    intro i j
    exact hfDist ⟨1, i⟩ ⟨2, j⟩
      (by simp [completeMultipartiteGraph, comap_adj, top_adj])
  let A : Fin 3 → EuclideanSpace ℝ (Fin 4) := fun i => a i - apex
  let B : Fin 3 → EuclideanSpace ℝ (Fin 4) := fun j => b j - apex
  have hAinj : Function.Injective A := by
    intro i j hij
    apply ha
    have := congrArg (fun z => z + apex) hij
    simpa [A] using this
  have hBinj : Function.Injective B := by
    intro i j hij
    apply hb
    have := congrArg (fun z => z + apex) hij
    simpa [B] using this
  have hAnorm : ∀ i, ‖A i‖ = 1 := by
    intro i
    calc
      ‖A i‖ = ‖a i - apex‖ := by simp [A]
      _ = dist (a i) apex := by rw [dist_eq_norm]
      _ = dist apex (a i) := dist_comm _ _
      _ = 1 := hpa i
  have hBnorm : ∀ j, ‖B j‖ = 1 := by
    intro j
    calc
      ‖B j‖ = ‖b j - apex‖ := by simp [B]
      _ = dist (b j) apex := by rw [dist_eq_norm]
      _ = dist apex (b j) := dist_comm _ _
      _ = 1 := hpb j
  have hinner : ∀ i j, ⟪A i, B j⟫ = 1 / 2 := by
    intro i j
    have hdiff : ‖A i - B j‖ = 1 := by
      calc
        ‖A i - B j‖ = ‖a i - b j‖ := by simp [A, B, sub_sub_sub_cancel_right]
        _ = dist (a i) (b j) := by rw [dist_eq_norm]
        _ = 1 := hcross i j
    have hexp := norm_sub_sq_real (A i) (B j)
    rw [hdiff, hAnorm i, hBnorm j] at hexp
    linarith
  exact false_of_unit_constant_inner A B hAinj hBinj hAnorm hBnorm hinner

/-- **Upper bound** for the dimension of `K₁,₃,₃`: the complete tripartite graph with part sizes
`1, 3, 3` admits an injective placement in `ℝ⁵` realising every edge as a unit segment
(Chaffee–Noble Theorem 8).

With `r = √2 / 2`, `u = √2 / 4` and `t = √6 / 4`, the apex is the origin, one part of size three
is `(r, 0, 0, 0, r)`, `(-u, t, 0, 0, r)`, `(-u, -t, 0, 0, r)`, and the other is
`(0, 0, r, 0, r)`, `(0, 0, -u, t, r)`, `(0, 0, -u, -t, r)`. -/
theorem unitDistEmbeddable_completeMultipartiteGraph_one_three_three :
    (completeMultipartiteGraph fun i : Fin 3 => Fin (![1, 3, 3] i)).UnitDistEmbeddable 5 := by
  refine ⟨place, place_injective, ?_⟩
  intro u v huv
  simp only [completeMultipartiteGraph, comap_adj, top_adj] at huv
  match u, v with
  | ⟨0, _⟩, ⟨0, _⟩ => exact (huv rfl).elim
  | ⟨0, _⟩, ⟨1, j⟩ => exact dist_apex_part1 j
  | ⟨0, _⟩, ⟨2, j⟩ => exact dist_apex_part2 j
  | ⟨1, j⟩, ⟨0, _⟩ =>
      rw [dist_comm]
      exact dist_apex_part1 j
  | ⟨1, _⟩, ⟨1, _⟩ => exact (huv rfl).elim
  | ⟨1, i⟩, ⟨2, j⟩ => exact dist_part1_part2 i j
  | ⟨2, j⟩, ⟨0, _⟩ =>
      rw [dist_comm]
      exact dist_apex_part2 j
  | ⟨2, j⟩, ⟨1, i⟩ =>
      rw [dist_comm]
      exact dist_part1_part2 i j
  | ⟨2, _⟩, ⟨2, _⟩ => exact (huv rfl).elim

/-- `K₁,₃,₃` has dimension five: it embeds in `ℝ⁵`, and in no smaller Euclidean space.

Chaffee–Noble Theorem 8. The lower bound is the absence of a placement in `ℝ⁴`;
`UnitDistEmbeddable.mono` carries that absence down to every smaller dimension. -/
theorem hasDimension_K133 :
    (completeMultipartiteGraph fun i : Fin 3 => Fin (![1, 3, 3] i)).HasDimension 5 := by
  refine ⟨unitDistEmbeddable_completeMultipartiteGraph_one_three_three, ?_⟩
  rw [mem_lowerBounds]
  intro m hm
  have hmle : ¬ m ≤ 4 := fun hle =>
    not_unitDistEmbeddable_completeMultipartiteGraph_one_three_three (hm.mono hle)
  exact Nat.succ_le_of_lt (Nat.gt_of_not_le hmle)

end

end

end SimpleGraph

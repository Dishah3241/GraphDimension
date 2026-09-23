/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A point at unit distance from a scaled orthonormal basis

Branch B of the induction in Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean
space* (arXiv:1802.03092, proof of Theorem 3, l. 363–369). A clique placed as the scaled
orthonormal basis `(1 / √2) • EuclideanSpace.single i 1` sits on the sphere `‖x‖ ^ 2 = 1 / 2`,
and a vertex joined to all of it still fits in `ℝᵈ`: the apex `t • ∑ i, e i`, for a root `t` of
`d * t ^ 2 - 2 * t - 1 = 0`, is at distance exactly `1` from every basis vector, and its squared
norm is not `1 / 2`, so it differs from every point already placed on that sphere.

## References

Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, arXiv:1802.03092.
-/

open scoped InnerProductSpace

@[expose] public section

namespace EuclideanGeometry

/-- The apex of a scaled orthonormal basis: pairwise orthogonal vectors of squared norm `1 / 2`
in `EuclideanSpace ℝ (Fin d)`, `1 ≤ d`, admit a common point at distance `1` from all of them
whose squared norm is not `1 / 2`. The `‖x‖ ^ 2 ≠ 1 / 2` conclusion is what makes the apex
differ from every vertex already placed on the sphere of radius `1 / √2`. -/
theorem exists_unit_dist_of_orthogonal_basis {d : ℕ} (hd : 1 ≤ d)
    (e : Fin d → EuclideanSpace ℝ (Fin d)) (horth : ∀ i j, i ≠ j → ⟪e i, e j⟫_ℝ = 0)
    (hnorm : ∀ i, ‖e i‖ ^ 2 = 1 / 2) :
    ∃ x : EuclideanSpace ℝ (Fin d), (∀ i, dist x (e i) = 1) ∧ ‖x‖ ^ 2 ≠ 1 / 2 := by
  -- the scalar: a root `t` of `d * t ^ 2 - 2 * t - 1 = 0`
  obtain ⟨t, ht⟩ : ∃ t : ℝ, (d : ℝ) * (t * t) + (-2 : ℝ) * t + (-1 : ℝ) = 0 := by
    have hsq : discrim (d : ℝ) (-2) (-1)
        = 2 * Real.sqrt (1 + (d : ℝ)) * (2 * Real.sqrt (1 + (d : ℝ))) := by
      change (-2 : ℝ) ^ 2 - 4 * (d : ℝ) * (-1)
        = 2 * Real.sqrt (1 + (d : ℝ)) * (2 * Real.sqrt (1 + (d : ℝ)))
      rw [← sq, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + (d : ℝ))]
      ring
    exact exists_quadratic_eq_zero (a := (d : ℝ)) (b := -2) (c := -1)
      (Nat.cast_ne_zero.mpr (by omega)) ⟨2 * Real.sqrt (1 + (d : ℝ)), hsq⟩
  have h1 : t ^ 2 * (d : ℝ) = 2 * t + 1 := by linear_combination ht
  have ht0 : t ≠ 0 := by
    intro hc
    rw [hc] at h1
    norm_num at h1
  set s : EuclideanSpace ℝ (Fin d) := ∑ i, e i with hs_def
  -- the sum has inner product `1 / 2` with each `e i`, and squared norm `d / 2`
  have hs_inner : ∀ i, ⟪s, e i⟫_ℝ = 1 / 2 := by
    intro i
    rw [hs_def, sum_inner, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · rw [real_inner_self_eq_norm_sq, hnorm i]
    · intro j _ hj
      exact horth j i hj
  have hs_norm : ‖s‖ ^ 2 = d / 2 := by
    rw [← real_inner_self_eq_norm_sq, hs_def, sum_inner]
    have hall : ∀ j, ⟪e j, ∑ i, e i⟫_ℝ = 1 / 2 := by
      intro j
      rw [inner_sum, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
      · rw [real_inner_self_eq_norm_sq, hnorm j]
      · intro i _ hij
        exact horth j i (Ne.symm hij)
    simp only [hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  have hx : ‖t • s‖ ^ 2 = t ^ 2 * (d / 2) := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hs_norm]
  have ht2d : t ^ 2 * (d / 2) = t + 1 / 2 := by
    calc t ^ 2 * (d / 2) = t ^ 2 * (d : ℝ) / 2 := by ring
      _ = (2 * t + 1) / 2 := by rw [h1]
      _ = t + 1 / 2 := by ring
  refine ⟨t • s, fun i => ?_, ?_⟩
  · -- the apex is at distance one from every `e i`
    rw [dist_eq_norm]
    have hsq1 : ‖t • s - e i‖ ^ 2 = 1 := by
      rw [norm_sub_sq_real, hx, real_inner_smul_left, hs_inner i, hnorm i, ht2d]
      ring
    refine (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp ?_
    rw [hsq1, one_pow]
  · -- and it is off the sphere `‖x‖ ^ 2 = 1 / 2`
    intro hc
    rw [hx, ht2d] at hc
    exact ht0 (by linarith)

/-- The concrete instance used to place `K_d`: the scaled standard basis
`e i = (1 / √2) • EuclideanSpace.single i 1` admits an apex at distance `1` from every `e i`
whose squared norm is not `1 / 2`. -/
theorem exists_unit_dist_std_orthonormal_basis (d : ℕ) (hd : 1 ≤ d) :
    ∃ x : EuclideanSpace ℝ (Fin d),
      (∀ i, dist x ((1 / Real.sqrt 2) • EuclideanSpace.single i 1) = 1) ∧
      ‖x‖ ^ 2 ≠ 1 / 2 := by
  have hsq2 : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [one_div, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), inv_eq_one_div]
  have hortho : Orthonormal ℝ fun i : Fin d =>
      (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin d)) :=
    EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin d)
  refine exists_unit_dist_of_orthogonal_basis hd
    (fun i => (1 / Real.sqrt 2) •
      (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin d))) ?_ ?_
  · intro i j hij
    have h0 : ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)⟫_ℝ = 0 :=
      hortho.inner_eq_zero hij
    rw [real_inner_smul_left, real_inner_smul_right, h0]
    ring
  · intro i
    have h1 : ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin d))‖ = 1 := hortho.1 i
    have h2 : ‖(1 / Real.sqrt 2) •
        (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin d))‖ ^ 2
        = (1 / Real.sqrt 2) ^ 2
          * ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [h2, hsq2, h1]
    norm_num

end EuclideanGeometry

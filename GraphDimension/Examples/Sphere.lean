/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Sphere.Basic

import GraphDimension.Geometry.CompleteGraph
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The complete graph on the sphere

`Kₙ` sits on the sphere of radius `1/√2` in `ℝⁿ` at the scaled standard basis. The same graph on
three vertices is a unit-distance graph in `ℝ²`, but not a spherical one: a spherical placement of
`K₃` would be three pairwise orthogonal nonzero vectors in `ℝ²`.
-/

open scoped InnerProductSpace

namespace SimpleGraph

@[expose] public section

/-- `Kₙ` has a spherical placement in `ℝⁿ`: the vertex `i` goes to `(1/√2) eᵢ`.

Adjacent vertices land on distinct axes, so their position vectors are orthogonal and the edge has
length one. This is `Kₙ` on `𝕊ⁿ⁻¹`. -/
theorem sphereEmbeddable_completeGraph (n : ℕ) :
    (⊤ : SimpleGraph (Fin n)).SphereEmbeddable n := by
  rw [SphereEmbeddable.iff_orthogonal]
  let r : ℝ := (Real.sqrt 2)⁻¹
  have hr : r ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hr0 : r ≠ 0 := by positivity
  refine ⟨fun i => r • EuclideanSpace.single i (1 : ℝ), ?_, ?_, ?_⟩
  · intro i j hij
    by_contra hne
    have hcoord := congr_arg (fun p : EuclideanSpace ℝ (Fin n) => p i) hij
    rw [PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul, PiLp.single_apply,
      PiLp.single_apply, if_pos rfl, if_neg hne, mul_one, mul_zero] at hcoord
    exact hr0 hcoord
  · intro i
    have hnorm : ‖r • EuclideanSpace.single i (1 : ℝ)‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ r), PiLp.norm_single,
        Real.norm_eq_abs, abs_one, mul_one]
    rw [hnorm, hr]
  · intro u v huv
    rw [top_adj] at huv
    rw [real_inner_smul_left, real_inner_smul_right, EuclideanSpace.inner_single_left,
      PiLp.single_apply, if_neg huv, map_one]
    simp only [mul_zero]

/-- `K₃` is a unit-distance graph in `ℝ²` and is not spherical there.

A spherical placement would give three pairwise orthogonal vectors of norm `1/√2`. A pairwise
orthogonal family of nonzero vectors is linearly independent, and `ℝ²` has dimension two. -/
theorem completeGraph_fin_three_unitDistEmbeddable_two_not_sphereEmbeddable :
    (⊤ : SimpleGraph (Fin 3)).UnitDistEmbeddable 2 ∧
      ¬(⊤ : SimpleGraph (Fin 3)).SphereEmbeddable 2 := by
  refine ⟨?_, ?_⟩
  · exact unitDistEmbeddable_completeGraph 3
  · intro h
    rw [SphereEmbeddable.iff_orthogonal] at h
    obtain ⟨f, _, hfNorm, hfOrth⟩ := h
    have hne : ∀ i, f i ≠ 0 := by
      intro i hi
      have := hfNorm i
      rw [hi, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at this
      norm_num at this
    have ho : Pairwise fun i j : Fin 3 => ⟪f i, f j⟫_ℝ = 0 := by
      intro i j hij
      exact hfOrth i j (by rwa [top_adj])
    have hli := linearIndependent_of_ne_zero_of_inner_eq_zero hne ho
    have hcard := hli.fintype_card_le_finrank
    simp only [finrank_euclideanSpace_fin, Fintype.card_fin] at hcard
    exact absurd hcard (by decide : ¬(3 : ℕ) ≤ 2)

end

end SimpleGraph

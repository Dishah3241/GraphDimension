/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Equilateral sets span an affine simplex

Points at mutual distance one are affinely independent. The Gram matrix of the difference vectors
from one of them is `½(I + J)`, with `J` the all-ones matrix, and that matrix is positive definite.
An affinely independent set in `ℝᵈ` has at most `d + 1` points.

## References

Erdős, Harary and Tutte, *On the dimension of a graph*, Mathematika **12** (1965), 118–122.
-/

open Matrix Module
open scoped Matrix RealInnerProductSpace

namespace EuclideanGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `½(I + J)` is positive definite: its quadratic form is `½ (∑ xᵢ² + (∑ xᵢ)²)`. -/
private lemma posDef_half_one_add_allOnes {ν : Type*} [Finite ν] [DecidableEq ν] :
    ((2⁻¹ : ℝ) • ((1 : Matrix ν ν ℝ) + Matrix.of fun _ _ : ν => (1 : ℝ))).PosDef := by
  have := Fintype.ofFinite ν
  have hJ : (Matrix.vecMulVec (fun _ : ν => (1 : ℝ)) (fun _ => (1 : ℝ))).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star (fun _ : ν => (1 : ℝ))
  have hJ' : (Matrix.of fun _ _ : ν => (1 : ℝ)).PosSemidef := by
    rw [show Matrix.of (fun _ _ : ν => (1 : ℝ)) =
        Matrix.vecMulVec (fun _ : ν => (1 : ℝ)) (fun _ => (1 : ℝ)) by
      ext i j
      simp [Matrix.vecMulVec_apply, of_apply]]
    exact hJ
  exact ((PosDef.one : (1 : Matrix ν ν ℝ).PosDef).add_posSemidef hJ').smul
    (by norm_num : (0 : ℝ) < 2⁻¹)

/-- Two vectors of norm one at distance one have inner product `½`. -/
private lemma inner_eq_half_of_unit_diff {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ‖x - y‖ = 1) : ⟪x, y⟫ = 2⁻¹ := by
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two, hx, hy, hxy]
  norm_num

/-- Unit vectors with unit differences have Gram matrix `½(I + J)`. -/
private lemma gram_eq_half_one_add_allOnes {ν : Type*} [DecidableEq ν] {v : ν → E}
    (hnorm : ∀ i, ‖v i‖ = 1) (hdiff : Pairwise fun i j => ‖v i - v j‖ = 1) :
    gram ℝ v = (2⁻¹ : ℝ) • ((1 : Matrix ν ν ℝ) + Matrix.of fun _ _ : ν => (1 : ℝ)) := by
  ext i j
  rw [gram_apply]
  by_cases hij : i = j
  · subst hij
    rw [real_inner_self_eq_norm_sq, hnorm i]
    simp [Matrix.smul_apply, Matrix.add_apply, one_apply, of_apply]
    norm_num
  · rw [inner_eq_half_of_unit_diff (hnorm i) (hnorm j) (hdiff hij)]
    simp [Matrix.smul_apply, Matrix.add_apply, one_apply, of_apply, hij]

@[expose] public section

/-- Points at mutual distance one are affinely independent.

The differences from one point have Gram matrix `½(I + J)`. That matrix is positive definite, so
the differences are linearly independent, and the points are affinely independent. -/
theorem affineIndependent_of_pairwise_dist_eq_one {ι : Type*} {p : ι → E}
    (h : Pairwise fun i j => dist (p i) (p j) = 1) : AffineIndependent ℝ p := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl _ => exact affineIndependent_of_subsingleton ℝ p
  | inr hι =>
    let i0 := Classical.choice hι
    rw [affineIndependent_iff_linearIndependent_vsub ℝ p i0]
    let v : {x // x ≠ i0} → E := fun i => p i -ᵥ p i0
    have hnorm : ∀ i, ‖v i‖ = 1 := fun i => by
      simpa [v, dist_eq_norm_vsub] using h i.2
    have hdiff : Pairwise fun i j => ‖v i - v j‖ = 1 := fun i j hij => by
      have hsub : v i - v j = p i -ᵥ p j := by
        simp [v, vsub_eq_sub, sub_sub_sub_cancel_right]
      simpa [hsub, dist_eq_norm_vsub, vsub_eq_sub] using h (Subtype.coe_injective.ne hij)
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    have hli : LinearIndependent ℝ (fun i : s => v i.1) := by
      refine linearIndependent_of_posDef_gram ?_
      rw [gram_eq_half_one_add_allOnes (fun i => hnorm i.1) fun i j hij =>
        hdiff (i := i.1) (j := j.1) (fun h => hij (Subtype.ext h))]
      exact posDef_half_one_add_allOnes
    simpa [v, Function.comp_def] using hli

/-- `k` points of `ℝᵈ` at mutual distance one satisfy `k ≤ d + 1`.

The points are affinely independent, and an affinely independent set in a `d`-dimensional real
vector space has cardinality at most `d + 1`. -/
theorem card_le_of_equilateral {ι : Type*} [Fintype ι] {d : ℕ}
    {p : ι → EuclideanSpace ℝ (Fin d)}
    (h : Pairwise fun i j => dist (p i) (p j) = 1) : Fintype.card ι ≤ d + 1 := by
  have hcard := (affineIndependent_of_pairwise_dist_eq_one h).card_le_finrank_succ
  have hle : finrank ℝ (vectorSpan ℝ (Set.range p)) ≤ d := by
    simpa [finrank_euclideanSpace_fin] using Submodule.finrank_le (vectorSpan ℝ (Set.range p))
  exact hcard.trans (Nat.add_le_add_right hle 1)

end

end EuclideanGeometry

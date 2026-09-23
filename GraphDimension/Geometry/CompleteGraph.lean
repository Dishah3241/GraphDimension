/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic

import GraphDimension.Geometry.Equilateral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Data.Fin.SuccPred
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Order.Bounds.Basic

/-!
# The complete graph has dimension `n - 1`

`Kₙ` embeds in `ℝⁿ⁻¹` and in no smaller Euclidean space. The upper bound places the vertices at
the scaled basis vectors `(1/√2) eᵢ` of `ℝⁿ`. Those points lie on the hyperplane `∑ xᵢ = 1/√2`.
An orthonormal basis of that hyperplane's direction, from `stdOrthonormalBasis`, carries them
isometrically into `ℝⁿ⁻¹`. The lower bound is `card_le_of_equilateral`: `n` points at mutual
distance one need dimension at least `n - 1`.

## References

* Erdős, Harary and Tutte, *On the dimension of a graph*, Mathematika **12** (1965), 118–122.
* Chaffee and Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J.
  Combin. **64(2)** (2016), 327–333, Lemma 1.
-/

open Module
open scoped RealInnerProductSpace

namespace SimpleGraph

noncomputable section

/-- Sum of coordinates, as a linear form on `ℝⁿ`. -/
private def coordSum (n : ℕ) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ :=
  ∑ i : Fin n, EuclideanSpace.projₗ i

@[simp]
private lemma coordSum_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    coordSum n x = ∑ i, x i := by
  simp [coordSum, LinearMap.sum_apply]

/-- A scaled basis vector has coordinate sum equal to its scale. -/
private lemma coordSum_scaled {n : ℕ} (i : Fin n) (c : ℝ) :
    coordSum n (c • EuclideanSpace.single i 1) = c := by
  simp [PiLp.single_apply, smul_eq_mul, mul_one, Finset.mem_univ]

/-- The coordinate sum on `ℝⁿ` is nonzero for `n ≥ 1`. -/
private lemma coordSum_ne_zero {n : ℕ} (hn : 0 < n) : coordSum n ≠ 0 := by
  intro h
  have hsum := coordSum_scaled (⟨0, hn⟩ : Fin n) (1 : ℝ)
  rw [one_smul] at hsum
  rw [h, LinearMap.zero_apply] at hsum
  exact one_ne_zero hsum.symm

/-- The direction of `∑ xᵢ = constant` in `ℝⁿ` has dimension `n - 1`. -/
private lemma finrank_ker_coordSum {n : ℕ} (hn : 0 < n) :
    finrank ℝ (LinearMap.ker (coordSum n)) = n - 1 := by
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero (coordSum_ne_zero hn)
  rw [finrank_euclideanSpace_fin] at hker
  exact Nat.eq_sub_of_add_eq hker

/-- Scaled basis vectors on distinct axes are at distance one. -/
private lemma dist_scaledBasis {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    dist ((Real.sqrt 2)⁻¹ • EuclideanSpace.single i (1 : ℝ))
      ((Real.sqrt 2)⁻¹ • EuclideanSpace.single j (1 : ℝ)) = 1 := by
  set r : ℝ := (Real.sqrt 2)⁻¹
  have hr0 : 0 ≤ r := by positivity
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
  have horth :
      ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)⟫ = 0 := by
    rw [EuclideanSpace.inner_single_left]
    simp [hij]
  have hsq :
      ‖EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ)‖ ^ 2 = 2 := by
    rw [norm_sub_sq_real, horth]
    simp [PiLp.norm_single]
    norm_num
  have hnorm :
      ‖EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ)‖ = Real.sqrt 2 := by
    refine (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp ?_
    rw [hsq, Real.sq_sqrt (by positivity)]
  rw [hnorm, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num))]

@[expose] public section

/-- `Kₙ` has a unit-distance representation in `ℝⁿ⁻¹`.

The scaled basis vectors `(1/√2) eᵢ` of `ℝⁿ` are pairwise at distance one and lie on the
hyperplane `∑ xᵢ = 1/√2`. `stdOrthonormalBasis` identifies the direction of that hyperplane with
`ℝⁿ⁻¹`. -/
theorem unitDistEmbeddable_completeGraph (n : ℕ) :
    (⊤ : SimpleGraph (Fin n)).UnitDistEmbeddable (n - 1) := by
  cases n with
  | zero => exact ⟨isEmptyElim, isEmptyElim, isEmptyElim⟩
  | succ n =>
    classical
    let r : ℝ := (Real.sqrt 2)⁻¹
    let p : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) :=
      fun i => r • EuclideanSpace.single i 1
    let V := LinearMap.ker (coordSum (n + 1))
    have hfin : finrank ℝ V = n := by
      simpa using finrank_ker_coordSum (Nat.succ_pos n)
    let b := (stdOrthonormalBasis ℝ V).reindex (finCongr hfin)
    let i0 : Fin (n + 1) := 0
    have hmem (i : Fin (n + 1)) : p i - p i0 ∈ V := by
      rw [LinearMap.mem_ker, map_sub]
      simp [p, sub_self]
    let v : Fin (n + 1) → V := fun i => ⟨p i - p i0, hmem i⟩
    let f : Fin (n + 1) → EuclideanSpace ℝ (Fin n) := fun i => b.repr (v i)
    refine ⟨f, ?_, ?_⟩
    · intro i j hij
      have hv : v i = v j := b.repr.injective hij
      have hp : p i = p j := by
        have hsub : p i - p i0 = p j - p i0 := by
          simpa [v] using congrArg Subtype.val hv
        rw [sub_eq_add_neg] at hsub
        exact add_right_cancel hsub
      have hi : p i i = r := by
        simp [p, PiLp.smul_apply, smul_eq_mul, mul_one]
      have hj : p j i = if j = i then r else 0 := by
        simp [p, PiLp.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, eq_comm]
      have hr : r ≠ 0 := by positivity
      by_cases hij' : i = j
      · exact hij'
      · have hcoord : p i i = p j i := congrArg (fun x => x i) hp
        rw [hi, hj, if_neg (Ne.symm hij')] at hcoord
        exact absurd hcoord hr
    · intro i j hij
      have hcoe : ((v i - v j : V) : EuclideanSpace ℝ (Fin (n + 1))) = p i - p j := by
        simp [v, sub_sub_sub_cancel_right]
      calc
        dist (f i) (f j) = dist (v i) (v j) := by simp [f]
        _ = ‖(v i - v j : V)‖ := by rw [dist_eq_norm]
        _ = ‖p i - p j‖ := by rw [← Submodule.norm_coe, hcoe]
        _ = dist (p i) (p j) := by rw [dist_eq_norm]
        _ = 1 := by simpa [p] using dist_scaledBasis hij

/-- The complete graph on `n` vertices has dimension `n - 1`.

Chaffee–Noble Lemma 1, attributed there to Erdős–Harary–Tutte. The upper bound is
`unitDistEmbeddable_completeGraph`, and the lower bound is `card_le_of_equilateral`. -/
theorem hasDimension_completeGraph (n : ℕ) :
    (⊤ : SimpleGraph (Fin n)).HasDimension (n - 1) := by
  refine ⟨unitDistEmbeddable_completeGraph n, ?_⟩
  rw [mem_lowerBounds]
  intro m hm
  obtain ⟨g, -, hg⟩ := hm
  have hle : n ≤ m + 1 := by
    simpa [Fintype.card_fin] using
      EuclideanGeometry.card_le_of_equilateral (p := g) fun i j hij =>
        hg i j (by simpa [top_adj] using hij)
  exact (Nat.sub_le_iff_le_add).2 hle

end

end

end SimpleGraph

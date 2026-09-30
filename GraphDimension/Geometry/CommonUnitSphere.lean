/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Set.Finite.Basic

import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Common unit spheres of points on a small sphere

For `k` points on the sphere of squared radius `1/2` in `ℝᵈ`, with `k + 1 ≤ d`,
the set of points at distance one from all of them is infinite. The centres need not be
distinct or pairwise at unit distance.

For nonempty centres, let `K` be the direction of their affine span and let `c` be the
projection of the origin onto that affine span. Then `p i - c ∈ K`, `c ∈ Kᗮ`, and
`‖p i - c‖² = 1/2 - ‖c‖²`. Translating the sphere of squared radius `1/2 + ‖c‖²`
in `Kᗮ` by `c` gives common unit-distance points. Since `dim K ≤ k - 1`, that sphere
contains a semicircle.

This is the geometric extension step in the Euclidean upper bound of Frankl, Kupavskii
and Swanepoel, *Embedding graphs in Euclidean space*, Theorem 4.
-/

namespace EuclideanGeometry

open Module Submodule
open scoped RealInnerProductSpace

/-- A positive squared-radius sphere in a subspace of dimension at least two is infinite. -/
private lemma infinite_sphere_sq_in_submodule {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {W : Submodule ℝ E} (hW : 2 ≤ finrank ℝ W)
    {r : ℝ} (hr : 0 < r) : {v : E | v ∈ W ∧ ‖v‖ ^ 2 = r}.Infinite := by
  have : FiniteDimensional ℝ W := FiniteDimensional.of_finrank_pos (by omega)
  let b := stdOrthonormalBasis ℝ W
  let i₀ : Fin (finrank ℝ W) := ⟨0, by omega⟩
  let i₁ : Fin (finrank ℝ W) := ⟨1, by omega⟩
  let e₀ : E := b i₀
  let e₁ : E := b i₁
  have he₀ : ‖e₀‖ = 1 := b.norm_eq_one i₀
  have he₁ : ‖e₁‖ = 1 := b.norm_eq_one i₁
  have horth : ⟪e₀, e₁⟫ = 0 := b.inner_eq_zero (by
    intro h
    have := congrArg Fin.val h
    simp [i₀, i₁] at this)
  let f : ℝ → E := fun t => t • e₀ + Real.sqrt (r - t ^ 2) • e₁
  have hcoord (t : ℝ) : ⟪f t, e₀⟫ = t := by
    simp [f, inner_add_left, real_inner_smul_left,
      he₀, inner_eq_zero_symm.mp horth]
  have hinj : Function.Injective f := by
    intro t u h
    have := congrArg (fun v => ⟪v, e₀⟫) h
    simpa only [hcoord] using this
  have hinf := (Set.Icc_infinite (Real.sqrt_pos.mpr hr)).image hinj.injOn
  refine hinf.mono ?_
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨W.add_mem (W.smul_mem t (b i₀).property)
    (W.smul_mem _ (b i₁).property), ?_⟩
  have ht2 : 0 ≤ r - t ^ 2 := by
    have := sq_le_sq' (by linarith [Real.sqrt_nonneg r, ht.1]) ht.2
    rw [Real.sq_sqrt hr.le] at this
    linarith
  dsimp [f]
  rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, horth,
    norm_smul, norm_smul, he₀, he₁, mul_one, mul_one, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs, Real.sq_sqrt ht2]
  ring

@[expose] public section

/-- If `k` points in `ℝᵈ` have squared norm `1/2` and `k + 1 ≤ d`, infinitely many
points are at distance one from all of them. No independence or pairwise-distance
condition on the centres is needed. The dimension bound also implies `1 ≤ d`, including
when there are no centres. -/
theorem infinite_common_unit_sphere_of_norm_sq_eq_half {d k : ℕ}
    {p : Fin k → EuclideanSpace ℝ (Fin d)} (hk : k + 1 ≤ d)
    (hp : ∀ i, ‖p i‖ ^ 2 = 1 / 2) :
    {x : EuclideanSpace ℝ (Fin d) | ∀ i, dist x (p i) = 1}.Infinite := by
  classical
  cases k with
  | zero =>
    have : Infinite (EuclideanSpace ℝ (Fin d)) := by
      refine Infinite.of_injective
        (fun t : ℝ => EuclideanSpace.single (⟨0, by omega⟩ : Fin d) t) ?_
      intro t u h
      have := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v.ofLp ⟨0, by omega⟩) h
      simpa using this
    simpa using (Set.infinite_univ : (Set.univ : Set (EuclideanSpace ℝ (Fin d))).Infinite)
  | succ n =>
    let K := vectorSpan ℝ (Set.range p)
    have hK : finrank ℝ K ≤ n := finrank_vectorSpan_range_le ℝ p (Fintype.card_fin _)
    have hKo : 2 ≤ finrank ℝ Kᗮ := by
      have hsum := K.finrank_add_finrank_orthogonal
      rw [finrank_euclideanSpace_fin] at hsum
      omega
    let c := p 0 - K.starProjection (p 0)
    have hc : c ∈ Kᗮ := K.sub_starProjection_mem_orthogonal (p 0)
    have hpc (i : Fin (n + 1)) : p i - c ∈ K := by
      have hdiff : p i - p 0 ∈ K :=
        vsub_mem_vectorSpan ℝ (Set.mem_range_self i) (Set.mem_range_self 0)
      have heq : p i - c = (p i - p 0) + K.starProjection (p 0) := by
        dsimp [c]
        abel
      rw [heq]
      exact K.add_mem hdiff (K.starProjection_apply_mem _)
    have hnorm (i : Fin (n + 1)) : ‖p i - c‖ ^ 2 = 1 / 2 - ‖c‖ ^ 2 := by
      have horth := inner_right_of_mem_orthogonal (hpc i) hc
      rw [inner_sub_left, real_inner_self_eq_norm_sq] at horth
      rw [norm_sub_sq_real, hp i]
      linarith
    have hr : 0 < 1 / 2 + ‖c‖ ^ 2 := by positivity
    have hinf := infinite_sphere_sq_in_submodule hKo hr
    have hinj : Function.Injective (fun v : EuclideanSpace ℝ (Fin d) => c + v) :=
      add_right_injective c
    refine (hinf.image hinj.injOn).mono ?_
    rintro _ ⟨v, ⟨hvK, hvnorm⟩, rfl⟩ i
    have horth : ⟪v, p i - c⟫ = 0 := inner_left_of_mem_orthogonal (hpc i) hvK
    have heq : c + v - p i = v - (p i - c) := by abel
    rw [dist_eq_norm, heq]
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [norm_sub_sq_real, horth, hvnorm, hnorm i]
    ring

end

end EuclideanGeometry

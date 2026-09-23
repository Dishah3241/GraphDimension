/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Finite.Basic

import GraphDimension.Geometry.Equilateral
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Points at unit distance from a regular simplex

The set of points at distance one from every vertex of a unit regular simplex on `k` vertices in
`ℝᵈ`, with `k + 1 ≤ d`, is a sphere of positive radius in the orthogonal complement of the
simplex's affine span. That complement has dimension `d - k + 1 ≥ 2`, so the sphere is infinite.

## References

Chaffee and Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J.
Combin. **64(2)** (2016), 327–333, the sphere argument in the proofs of Theorems 6 and 10.
-/

namespace EuclideanGeometry

open Module Submodule Affine AffineSubspace Finset
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The squared norm of a vector in the plane of an orthonormal pair is the sum of the squared
coefficients. -/
private lemma norm_sq_orthonormal {e₀ e₁ : E} (he₀ : ‖e₀‖ = 1) (he₁ : ‖e₁‖ = 1)
    (horth : ⟪e₀, e₁⟫ = 0) (t s : ℝ) : ‖t • e₀ + s • e₁‖ ^ 2 = t ^ 2 + s ^ 2 := by
  have hcross : ⟪t • e₀, s • e₁⟫ = 0 := by
    simp [real_inner_smul_left, real_inner_smul_right, horth]
  rw [norm_add_sq_real, hcross, mul_zero, add_zero, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, he₀, he₁, mul_one, mul_one, sq_abs, sq_abs]

/-- The inner product against the first vector of an orthonormal pair recovers its coefficient. -/
private lemma inner_coord_orthonormal {e₀ e₁ : E} (he₀ : ‖e₀‖ = 1) (horth : ⟪e₀, e₁⟫ = 0)
    (t s : ℝ) : ⟪t • e₀ + s • e₁, e₀⟫ = t := by
  have h10 : ⟪e₁, e₀⟫ = 0 := inner_eq_zero_symm.mp horth
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, h10, real_inner_self_eq_norm_sq,
    he₀]
  ring

omit [InnerProductSpace ℝ E] in
/-- A nonnegative radius and a square of that radius determine the norm. -/
private lemma norm_eq_of_norm_sq_eq {x : E} {r : ℝ} (hr : 0 ≤ r) (hx : ‖x‖ ^ 2 = r ^ 2) :
    ‖x‖ = r :=
  (sq_eq_sq₀ (norm_nonneg _) hr).mp hx

/-- The semicircle `t ↦ c + t • e₀ + √(r² − t²) • e₁`, for `t ∈ [0, r]` and an orthonormal pair,
is infinite. -/
private lemma infinite_semicircle (c e₀ e₁ : E) (he₀ : ‖e₀‖ = 1) (horth : ⟪e₀, e₁⟫ = 0)
    {r : ℝ} (hr : 0 < r) :
    ((fun t : ℝ => c + t • e₀ + Real.sqrt (r ^ 2 - t ^ 2) • e₁) '' Set.Icc 0 r).Infinite := by
  refine (Set.infinite_image_iff ?_).2 (Set.Icc_infinite hr)
  intro t _ t' _ h
  have hcoord : ∀ u : ℝ, ⟪c + u • e₀ + Real.sqrt (r ^ 2 - u ^ 2) • e₁ - c, e₀⟫ = u := by
    intro u
    have hshift : c + u • e₀ + Real.sqrt (r ^ 2 - u ^ 2) • e₁ - c =
        u • e₀ + Real.sqrt (r ^ 2 - u ^ 2) • e₁ := by
      abel
    rw [hshift]
    exact inner_coord_orthonormal he₀ horth _ _
  have hinner := congrArg (fun p => ⟪p - c, e₀⟫) h
  rw [hcoord, hcoord] at hinner
  exact hinner

/-- A subspace of dimension at least two contains an orthonormal pair. -/
private lemma exists_orthonormal_pair_of_finrank_ge_two {W : Submodule ℝ E}
    (hW : 2 ≤ finrank ℝ W) :
    ∃ e₀ e₁ : E, ‖e₀‖ = 1 ∧ ‖e₁‖ = 1 ∧ ⟪e₀, e₁⟫ = 0 ∧ e₀ ∈ W ∧ e₁ ∈ W := by
  have : FiniteDimensional ℝ W := FiniteDimensional.of_finrank_pos (by omega)
  let b := stdOrthonormalBasis ℝ W
  let i₀ : Fin (finrank ℝ W) := ⟨0, by omega⟩
  let i₁ : Fin (finrank ℝ W) := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := by
    intro h
    apply_fun Fin.val at h
    simp at h
  refine ⟨b i₀, b i₁, ?_, ?_, ?_, ?_, ?_⟩
  · rw [norm_coe]
    exact b.norm_eq_one i₀
  · rw [norm_coe]
    exact b.norm_eq_one i₁
  · rw [← Submodule.coe_inner]
    exact b.inner_eq_zero hne
  · exact (b i₀).property
  · exact (b i₁).property

/-- `n • (1 + ((n − 1) / 2)) = (n + 1) n / 2`. -/
private lemma card_mul_half_sum (n : ℕ) :
    (n : ℝ) * (1 + ((n - 1 : ℕ) : ℝ) * (2 : ℝ)⁻¹) = (n + 1 : ℝ) * n / 2 := by
  cases n with
  | zero => norm_num
  | succ m =>
    have hm : ((Nat.succ m - 1 : ℕ) : ℝ) = (m : ℝ) := by simp
    rw [hm]
    field_simp
    rw [Nat.cast_add]
    ring

/-- For a unit regular simplex, `‖∑ (p x − p i)‖² = (n + 1) n / 2`. -/
private lemma norm_sq_sum_vsub_of_side_one {n : ℕ} {p : Fin (n + 1) → E}
    (hdist : Pairwise fun i j => dist (p i) (p j) = 1) (i : Fin (n + 1)) :
    ‖∑ x, (p x -ᵥ p i)‖ ^ 2 = (n + 1 : ℝ) * n / 2 := by
  let v : Fin (n + 1) → E := fun x => p x -ᵥ p i
  have hv0 : v i = 0 := by simp [v]
  have hnorm_ne {x : Fin (n + 1)} (hx : x ≠ i) : ‖v x‖ = 1 := by
    rw [show ‖v x‖ = dist (p x) (p i) by simp [v, dist_eq_norm_vsub E]]
    exact hdist hx
  have hinner_ne {x y : Fin (n + 1)} (hx : x ≠ i) (hy : y ≠ i) (hxy : x ≠ y) :
      ⟪v x, v y⟫ = 2⁻¹ := by
    rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
    have hsub : v x - v y = p x -ᵥ p y := by
      simp [v, vsub_eq_sub, sub_sub_sub_cancel_right]
    have hdiff : ‖v x - v y‖ = 1 := by
      rw [hsub, ← dist_eq_norm_vsub E]
      exact hdist hxy
    rw [hnorm_ne hx, hnorm_ne hy, hdiff]
    norm_num
  have hterm0 (x : Fin (n + 1)) : ⟪v x, v i⟫ = 0 := by
    rw [hv0]
    simp
  have hdrop (x : Fin (n + 1)) :
      ∑ y ∈ univ.erase i, ⟪v x, v y⟫ = ∑ y, ⟪v x, v y⟫ :=
    Finset.sum_erase univ (hterm0 x)
  have hrow0 : ∑ y, ⟪v i, v y⟫ = 0 := by
    simp [hv0]
  have hstep1 : ∑ x ∈ univ.erase i, ∑ y, ⟪v x, v y⟫ = ∑ x, ∑ y, ⟪v x, v y⟫ :=
    Finset.sum_erase univ hrow0
  have hstep2 :
      ∑ x ∈ univ.erase i, ∑ y ∈ univ.erase i, ⟪v x, v y⟫ =
        ∑ x ∈ univ.erase i, ∑ y, ⟪v x, v y⟫ := by
    refine Finset.sum_congr rfl ?_
    intro x _
    exact hdrop x
  rw [← real_inner_self_eq_norm_sq]
  change ⟪∑ x, v x, ∑ y, v y⟫ = (n + 1 : ℝ) * n / 2
  rw [sum_inner]
  simp_rw [inner_sum]
  rw [← hstep1, ← hstep2]
  have hrow : ∑ x ∈ univ.erase i, ∑ y ∈ univ.erase i, ⟪v x, v y⟫ =
      ∑ x ∈ univ.erase i, (1 + ((n - 1 : ℕ) : ℝ) * 2⁻¹) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxne : x ≠ i := (mem_erase.mp hx).1
    rw [← Finset.add_sum_erase (univ.erase i) (fun y => ⟪v x, v y⟫) hx]
    have hdiag : ⟪v x, v x⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hnorm_ne hxne]
      norm_num
    have hoff : ∀ y ∈ (univ.erase i).erase x, ⟪v x, v y⟫ = 2⁻¹ := by
      intro y hy
      have hyx : y ≠ x := (mem_erase.mp hy).1
      have hyi : y ≠ i := (mem_erase.mp (mem_of_mem_erase hy)).1
      exact hinner_ne hxne hyi hyx.symm
    rw [hdiag, Finset.sum_congr rfl hoff, Finset.sum_const, nsmul_eq_mul]
    have hcard : #((univ.erase i).erase x) = n - 1 := by
      rw [card_erase_of_mem hx, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
      omega
    simp [hcard]
  rw [hrow, Finset.sum_const, nsmul_eq_mul, card_erase_of_mem (mem_univ i), card_univ,
    Fintype.card_fin]
  have hcard : ((n + 1 - 1 : ℕ) : ℝ) = (n : ℝ) := by
    simp
  rw [hcard]
  exact card_mul_half_sum n

/-- The squared distance from the centroid of a unit regular simplex to any vertex is
`n / (2 (n + 1))`, which is `(k − 1) / (2 k)` for `k = n + 1` vertices. -/
private lemma dist_sq_centroid_of_side_one {n : ℕ} (s : Affine.Simplex ℝ E n)
    (hdist : Pairwise fun i j => dist (s.points i) (s.points j) = 1) (i : Fin (n + 1)) :
    dist s.centroid (s.points i) ^ 2 = (n : ℝ) / (2 * ((n : ℝ) + 1)) := by
  rw [dist_eq_norm_vsub E, s.centroid_vsub_eq (s.points i)]
  have hsum := norm_sq_sum_vsub_of_side_one hdist i
  rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤
    ((n + 1 : ℝ)⁻¹)), hsum]
  field_simp

/-- `ℝᵈ` is infinite for `d ≥ 1`: the first coordinate axis is a copy of `ℝ`. -/
private lemma infinite_euclideanSpace {d : ℕ} (hd : 0 < d) :
    Infinite (EuclideanSpace ℝ (Fin d)) := by
  refine Infinite.of_injective
    (fun t : ℝ => EuclideanSpace.single (⟨0, hd⟩ : Fin d) t) ?_
  intro t s hts
  have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v.ofLp ⟨0, hd⟩) hts
  simp only [PiLp.single_apply] at hcoord
  exact hcoord

/-- In `ℝᵈ`, the points at distance one from every vertex of a unit regular `n`-simplex form an
infinite set when `n + 2 ≤ d`. -/
private lemma infinite_sphere_inter_fin {d n : ℕ}
    {p : Fin (n + 1) → EuclideanSpace ℝ (Fin d)}
    (hdist : Pairwise fun i j => dist (p i) (p j) = 1) (hk : n + 2 ≤ d) :
    {x | ∀ i, dist x (p i) = 1}.Infinite := by
  let s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) n :=
    ⟨p, affineIndependent_of_pairwise_dist_eq_one hdist⟩
  have hdist_s : Pairwise fun i j => dist (s.points i) (s.points j) = 1 := by
    simpa [s] using hdist
  let c : EuclideanSpace ℝ (Fin d) := s.centroid
  let R2 : ℝ := (n : ℝ) / (2 * ((n : ℝ) + 1))
  let rho2 : ℝ := ((n : ℝ) + 2) / (2 * ((n : ℝ) + 1))
  have hR (i : Fin (n + 1)) : dist c (s.points i) ^ 2 = R2 :=
    dist_sq_centroid_of_side_one s hdist_s i
  have hsum : R2 + rho2 = 1 := by
    simp only [R2, rho2]
    field_simp
    ring
  have hrho2 : 0 < rho2 := by
    simp only [rho2]
    positivity
  let ρ : ℝ := Real.sqrt rho2
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hrho2
  have hρsq : ρ ^ 2 = rho2 := Real.sq_sqrt hrho2.le
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := vectorSpan ℝ (Set.range s.points)
  have hK : finrank ℝ K + 1 = n + 1 := by
    simpa [s, Fintype.card_fin] using s.independent.finrank_vectorSpan_add_one
  have hKo : 2 ≤ finrank ℝ Kᗮ := by
    have hsumK := K.finrank_add_finrank_orthogonal
    rw [finrank_euclideanSpace_fin] at hsumK
    omega
  obtain ⟨e₀, e₁, he₀, he₁, horth, he₀K, he₁K⟩ :=
    exists_orthonormal_pair_of_finrank_ge_two (W := Kᗮ) hKo
  have hc : c ∈ affineSpan ℝ (Set.range s.points) := s.centroid_mem_affineSpan
  refine Set.Infinite.mono ?_ (infinite_semicircle c e₀ e₁ he₀ horth hρ)
  rintro _ ⟨t, ht, rfl⟩
  have hs : 0 ≤ ρ ^ 2 - t ^ 2 :=
    sub_nonneg.mpr <| sq_le_sq' (by linarith [ht.1, hρ.le]) ht.2
  set u : ℝ := Real.sqrt (ρ ^ 2 - t ^ 2)
  let v : EuclideanSpace ℝ (Fin d) := t • e₀ + u • e₁
  have hvK : v ∈ Kᗮ :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ he₀K) (Submodule.smul_mem _ _ he₁K)
  have hvnorm : ‖v‖ ^ 2 = rho2 := by
    rw [show v = t • e₀ + u • e₁ from rfl, norm_sq_orthonormal he₀ he₁ horth, Real.sq_sqrt hs,
      hρsq]
    ring
  intro j
  have hmem : s.points j -ᵥ c ∈ K := by
    have hdir : (affineSpan ℝ (Set.range s.points)).direction = K := by
      simpa [K] using direction_affineSpan (k := ℝ) (Set.range s.points)
    rw [← hdir]
    exact vsub_mem_direction ((subset_affineSpan ℝ _) (Set.mem_range_self j)) hc
  have horthv : ⟪s.points j - c, v⟫ = 0 := by
    have hmem' : s.points j - c ∈ K := by simpa [vsub_eq_sub] using hmem
    exact inner_right_of_mem_orthogonal hmem' hvK
  rw [dist_eq_norm]
  apply norm_eq_of_norm_sq_eq zero_le_one
  have hshift : c + t • e₀ + u • e₁ - s.points j = v - (s.points j - c) := by
    simp only [v]
    abel
  rw [hshift]
  have hsq : ‖v - (s.points j - c)‖ ^ 2 = ‖v‖ ^ 2 + ‖s.points j - c‖ ^ 2 := by
    rw [sub_eq_add_neg, norm_add_sq_real, inner_neg_right, norm_neg, real_inner_comm, horthv]
    ring
  have hpoint : ‖s.points j - c‖ ^ 2 = R2 := by
    rw [← dist_eq_norm, dist_comm]
    exact hR j
  rw [hsq, hvnorm, hpoint, add_comm, hsum, one_pow]

@[expose] public section

/-- In `ℝᵈ`, if `k` points are pairwise at distance one and `k + 1 ≤ d`, then the set of points
at distance one from all of them is infinite.

The hypothesis `Nat.card ι + 1 ≤ d` is the truncation-free form of `k ≤ d − 1`. The
circumcentre is the centroid. Its squared distance to each vertex is `(k − 1) / (2 k) < 1`, so
the solution set contains a sphere of positive radius in the orthogonal complement of the affine
span. That complement has dimension `d − k + 1 ≥ 2`.

Chaffee–Noble use the cases `k ≤ 2` in `ℝ³` (Theorem 6) and `k = 3` in `ℝ⁴` (Theorem 10). -/
theorem infinite_sphere_inter_of_regular_simplex {d : ℕ} {ι : Type*} [Finite ι]
    {p : ι → EuclideanSpace ℝ (Fin d)}
    (hdist : Pairwise fun i j => dist (p i) (p j) = 1) (hk : Nat.card ι + 1 ≤ d) :
    {x | ∀ i, dist x (p i) = 1}.Infinite := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hkF : Fintype.card ι + 1 ≤ d := by rwa [← Nat.card_eq_fintype_card]
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
    have hd : 0 < d := by
      have hcard : Fintype.card ι = 0 := @Fintype.card_eq_zero _ _ hempty
      omega
    have hset : {x | ∀ i, dist x (p i) = 1} = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro x i
      exact hempty.elim i
    rw [hset, Set.infinite_univ_iff]
    exact infinite_euclideanSpace hd
  | inr hι =>
    let n := Fintype.card ι - 1
    have hle : 1 ≤ Fintype.card ι := Nat.one_le_of_lt Fintype.card_pos
    have hn : n + 1 = Fintype.card ι := Nat.sub_add_cancel hle
    have hk' : n + 2 ≤ d := by omega
    let e : ι ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hn.symm
    let q : Fin (n + 1) → EuclideanSpace ℝ (Fin d) := fun i => p (e.symm i)
    have hq : Pairwise fun i j => dist (q i) (q j) = 1 :=
      fun i j hij => hdist (e.symm.injective.ne hij)
    have hinf := infinite_sphere_inter_fin hq hk'
    have hEq : {x | ∀ i, dist x (p i) = 1} = {x | ∀ i, dist x (q i) = 1} := by
      ext x
      constructor
      · intro hx i
        simpa [q] using hx (e.symm i)
      · intro hx i
        simpa [q] using hx (e i)
    rw [hEq]
    exact hinf

end

end EuclideanGeometry

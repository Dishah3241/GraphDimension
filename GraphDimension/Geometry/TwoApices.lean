/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Fintype.Card

import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Two apexes and a facet vertex of the two-simplex placement

Blueprint `lem:circumradius` of `docs/design/rung3-blueprint.tex` (Lemma R, repaired; findings
A36 and A37). In `ℝᵈ`, let `a` and `b` be the two apexes of the two unit regular `d`-simplices
sharing a facet, so `dist a b ^ 2 = 2 + 2 / d`, and let `c` be a vertex of their shared facet, so
`dist a c = dist b c = 1`. The triangle has sides `1, 1, √(2 + 2/d)`, hence is not degenerate,
and its squared circumradius is `d / (2 (d - 1)) < 1`. The points at distance one from all three
are the circumcentre plus a sphere of radius `√(1 - R²) > 0` in the orthogonal complement of the
triangle's plane. That complement has dimension `d - 2 ≥ 2` for `d ≥ 4`, so the solution set is
infinite. At `d = 3` it would be two points, which is why `4 ≤ d`.

The sketch's general Lemma R (pairwise distances at most `D`, `D ^ 2 < 3`, circumradius below
one) is false: `(-3/4, 0), (3/4, 0), (0, 1/10)` has circumradius `229/80` (finding A36). Only
the special case needed by the tail lemma is stated here.

## References

Chaffee and Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J.
Combin. **64(2)** (2016), 327–333, the sphere argument in the proofs of Theorems 6 and 10.
-/

namespace EuclideanGeometry

open Module Submodule Finset Set
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

@[expose] public section

/-- In `ℝᵈ` with `d ≥ 4`, two apexes `a`, `b` of the two-simplex placement (the two unit regular
`d`-simplices sharing a facet, so `dist a b ^ 2 = 2 + 2 / d`) and a vertex `c` of their shared
facet (`dist a c = dist b c = 1`) have an infinite set of common unit-sphere points.

The triangle's squared circumradius is `d / (2 (d - 1)) < 1`: with `u = a - c`, `v = b - c` and
`X = u + v`, one has `⟪X, u⟫ = ⟪X, v⟫ = 1 - 1/d` and `‖X‖² = 2 (1 - 1/d)`, so `o = c + s • X`
with `s = (2 (1 - 1/d))⁻¹` satisfies `‖o - a‖² = ‖o - b‖² = ‖o - c‖² = s`. The remaining freedom
is a sphere of squared radius `1 - s > 0` in `(span {u, v})ᗮ`, whose dimension is `d - 2 ≥ 2`,
so it contains an orthonormal pair and the solution set is infinite.

The general form suggested by the sketch (pairwise distances at most `D`, `D ^ 2 < 3`, implying
circumradius below one) is false: `(-3/4, 0), (3/4, 0), (0, 1/10)` has circumradius `229/80`. -/
theorem infinite_common_unit_sphere_two_apices {d : ℕ} (hd : 4 ≤ d)
    {a b c : EuclideanSpace ℝ (Fin d)}
    (hab : dist a b ^ 2 = 2 + 2 / (d : ℝ)) (hac : dist a c = 1) (hbc : dist b c = 1) :
    {x | dist x a = 1 ∧ dist x b = 1 ∧ dist x c = 1}.Infinite := by
  have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have h4 : (4 : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr hd
  set q : ℝ := 1 / (d : ℝ) with hq_def
  have hqp : (0 : ℝ) < q := by
    rw [hq_def]
    exact div_pos zero_lt_one hdpos
  have hq4 : q ≤ 1 / 4 := by
    rw [hq_def]
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) h4
  -- the three side lengths, as vectors relative to `c`
  have hnorm_ac : ‖a - c‖ = 1 := by
    rw [← dist_eq_norm]
    exact hac
  have hnorm_bc : ‖b - c‖ = 1 := by
    rw [← dist_eq_norm]
    exact hbc
  have huvsub : a - c - (b - c) = a - b := by abel
  have hnorm_ab2 : ‖a - b‖ * ‖a - b‖ = 2 + 2 * q := by
    have h1 : dist a b * dist a b = 2 + 2 / (d : ℝ) := by
      rw [← sq]
      exact hab
    rw [dist_eq_norm] at h1
    rw [h1, hq_def]
    ring
  have huu : ⟪a - c, a - c⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hnorm_ac]
    norm_num
  have hvv : ⟪b - c, b - c⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hnorm_bc]
    norm_num
  have huv : ⟪a - c, b - c⟫ = -q := by
    rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two, hnorm_ac,
      hnorm_bc, huvsub, hnorm_ab2]
    rw [div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  -- the sum vector `X = u + v`
  have hwu : ⟪(a - c) + (b - c), a - c⟫ = 1 - q := by
    rw [inner_add_left, huu, real_inner_comm (a - c) (b - c), huv]
    ring
  have hwv : ⟪(a - c) + (b - c), b - c⟫ = 1 - q := by
    rw [inner_add_left, huv, hvv]
    ring
  have hwnorm : ‖(a - c) + (b - c)‖ ^ 2 = 2 * (1 - q) := by
    rw [norm_add_sq_real, hnorm_ac, huv, hnorm_bc]
    ring
  -- the circumcentre `o` and its squared circumradius `s`
  set s : ℝ := (2 * (1 - q))⁻¹ with hs_def
  have h2p : (0 : ℝ) < 2 * (1 - q) := by linarith
  have hsk : s * (2 * (1 - q)) = 1 := by
    rw [hs_def]
    exact inv_mul_cancel₀ (ne_of_gt h2p)
  have hsp : (0 : ℝ) < s := by
    rw [hs_def]
    exact inv_pos.mpr h2p
  have hslt : s < 1 := by
    rw [hs_def, inv_lt_one₀ h2p]
    linarith
  set o : EuclideanSpace ℝ (Fin d) := c + s • ((a - c) + (b - c)) with ho_def
  have hao : a - o = (a - c) - s • ((a - c) + (b - c)) := by
    rw [ho_def]
    abel
  have hbo : b - o = (b - c) - s • ((a - c) + (b - c)) := by
    rw [ho_def]
    abel
  have hco : c - o = -(s • ((a - c) + (b - c))) := by
    rw [ho_def]
    abel
  have hRa2 : ‖a - o‖ ^ 2 = s := by
    rw [hao, norm_sub_sq_real, hnorm_ac, real_inner_smul_right,
      real_inner_comm ((a - c) + (b - c)) (a - c), hwu, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hsp.le, mul_pow, hwnorm]
    linear_combination (s - 1) * hsk
  have hRb2 : ‖b - o‖ ^ 2 = s := by
    rw [hbo, norm_sub_sq_real, hnorm_bc, real_inner_smul_right,
      real_inner_comm ((a - c) + (b - c)) (b - c), hwv, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hsp.le, mul_pow, hwnorm]
    linear_combination (s - 1) * hsk
  have hRc2 : ‖c - o‖ ^ 2 = s := by
    rw [hco, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsp.le, mul_pow, hwnorm]
    linear_combination s * hsk
  -- the plane of the triangle and its orthogonal complement
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
    Submodule.span ℝ (Set.range ![a - c, b - c]) with hK_def
  have hind : LinearIndependent ℝ ![a - c, b - c] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : ⟪∑ i : Fin 2, g i • (![a - c, b - c] i), a - c⟫ = 0 := by
      rw [hg]
      simp
    have h1 : ⟪∑ i : Fin 2, g i • (![a - c, b - c] i), b - c⟫ = 0 := by
      rw [hg]
      simp
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, inner_add_left,
      real_inner_smul_left, huu, hvv, mul_one, real_inner_comm (a - c) (b - c), huv] at h0 h1
    have hq2lt : (0 : ℝ) < 1 - q * q := by
      have hle : q * q ≤ q := by nlinarith [hq4, hqp]
      linarith
    have hgy : g 1 * (1 - q * q) = 0 := by
      linear_combination q * h0 + h1
    have hg1 : g 1 = 0 := by
      rcases mul_eq_zero.mp hgy with h | h
      · exact h
      · exact absurd h (ne_of_gt hq2lt)
    have hg0 : g 0 = 0 := by
      have h0' := h0
      rw [hg1] at h0'
      linarith
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
  have hK2 : finrank ℝ K = 2 := by
    have h := finrank_span_eq_card (R := ℝ) hind
    rw [Fintype.card_fin, ← hK_def] at h
    exact h
  have hKo : 2 ≤ finrank ℝ Kᗮ := by
    have hsum := K.finrank_add_finrank_orthogonal
    rw [finrank_euclideanSpace_fin] at hsum
    omega
  obtain ⟨e₀, e₁, he₀, he₁, horth, he₀K, he₁K⟩ :=
    exists_orthonormal_pair_of_finrank_ge_two (W := Kᗮ) hKo
  -- the sphere of free directions about the circumcentre
  set ρ : ℝ := Real.sqrt (1 - s) with hρ_def
  have hρ : (0 : ℝ) < ρ := by
    rw [hρ_def]
    exact Real.sqrt_pos.mpr (by linarith)
  have hρsq : ρ ^ 2 = 1 - s := by
    rw [hρ_def]
    exact Real.sq_sqrt (by linarith)
  have key : ∀ p : EuclideanSpace ℝ (Fin d), p - o ∈ K → ‖p - o‖ ^ 2 = s →
      ∀ t ∈ Set.Icc 0 ρ,
        dist (o + t • e₀ + Real.sqrt (ρ ^ 2 - t ^ 2) • e₁) p = 1 := by
    intro p hmem hpo t ht
    rw [dist_eq_norm]
    apply norm_eq_of_norm_sq_eq zero_le_one
    have hs2 : (0 : ℝ) ≤ ρ ^ 2 - t ^ 2 :=
      sub_nonneg.mpr <| sq_le_sq' (by linarith [ht.1, hρ.le]) ht.2
    have hqK : t • e₀ + Real.sqrt (ρ ^ 2 - t ^ 2) • e₁ ∈ Kᗮ :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ he₀K) (Submodule.smul_mem _ _ he₁K)
    have hq2 : ‖t • e₀ + Real.sqrt (ρ ^ 2 - t ^ 2) • e₁‖ ^ 2 = 1 - s := by
      rw [norm_sq_orthonormal he₀ he₁ horth, Real.sq_sqrt hs2, hρsq]
      ring
    have hortho : ⟪p - o, t • e₀ + Real.sqrt (ρ ^ 2 - t ^ 2) • e₁⟫ = 0 :=
      inner_right_of_mem_orthogonal hmem hqK
    have hshift : o + t • e₀ + Real.sqrt (ρ ^ 2 - t ^ 2) • e₁ - p =
        t • e₀ + Real.sqrt (ρ ^ 2 - t ^ 2) • e₁ - (p - o) := by
      abel
    rw [hshift]
    have hsq : ‖t • e₀ + Real.sqrt (ρ ^ 2 - t ^ 2) • e₁ - (p - o)‖ ^ 2 =
        ‖t • e₀ + Real.sqrt (ρ ^ 2 - t ^ 2) • e₁‖ ^ 2 + ‖p - o‖ ^ 2 := by
      rw [sub_eq_add_neg, norm_add_sq_real, inner_neg_right, norm_neg, real_inner_comm, hortho]
      ring
    rw [hsq, hq2, hpo]
    ring
  have huK : a - c ∈ K := Submodule.subset_span (Set.mem_range_self 0)
  have hvK : b - c ∈ K := Submodule.subset_span (Set.mem_range_self 1)
  have hXK : (a - c) + (b - c) ∈ K := Submodule.add_mem _ huK hvK
  have hmem_a : a - o ∈ K := by
    rw [hao]
    exact Submodule.sub_mem _ huK (Submodule.smul_mem _ _ hXK)
  have hmem_b : b - o ∈ K := by
    rw [hbo]
    exact Submodule.sub_mem _ hvK (Submodule.smul_mem _ _ hXK)
  have hmem_c : c - o ∈ K := by
    rw [hco]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hXK)
  refine Set.Infinite.mono ?_ (infinite_semicircle o e₀ e₁ he₀ horth hρ)
  rintro x ⟨t, ht, rfl⟩
  exact ⟨key a hmem_a hRa2 t ht, key b hmem_b hRb2 t ht, key c hmem_c hRc2 t ht⟩

end

end EuclideanGeometry

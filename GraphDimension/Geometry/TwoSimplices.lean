/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Finset.Card

import all GraphDimension.Geometry.CompleteMinusEdgeDimension
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.LinearAlgebra.AffineSpace.Midpoint
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Two simplices on a facet, and a tail of at most two edges

`K_{d+2} − e` sits in `ℝᵈ` as two unit regular `d`-simplices sharing a facet. The apexes are
`√(2 + 2/d)` apart, which is strictly less than `2` once `d ≥ 2`. A graph that keeps an injective
placement of a vertex set `s` in which every pair is at distance less than `2`, and that has at
most two edges not contained in `s`, is then unit-distance embeddable in `ℝᵈ` for `d ≥ 3`: each
new vertex meets the placed set in at most two neighbours, and every solution set is infinite.

## References

Frankl, Kupavskii, and Swanepoel, *Embedding graphs in Euclidean space*, arXiv:1802.03092, the
argument of Theorem 3 at `main.tex` lines 355–359.
-/

namespace EuclideanGeometry

open Module Submodule Metric
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma norm_sq_orthonormal {e₀ e₁ : E} (he₀ : ‖e₀‖ = 1) (he₁ : ‖e₁‖ = 1)
    (horth : ⟪e₀, e₁⟫ = 0) (t s : ℝ) : ‖t • e₀ + s • e₁‖ ^ 2 = t ^ 2 + s ^ 2 := by
  have hcross : ⟪t • e₀, s • e₁⟫ = 0 := by
    simp [real_inner_smul_left, real_inner_smul_right, horth]
  rw [norm_add_sq_real, hcross, mul_zero, add_zero, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, he₀, he₁, mul_one, mul_one, sq_abs, sq_abs]

private lemma inner_coord_orthonormal {e₀ e₁ : E} (he₀ : ‖e₀‖ = 1) (horth : ⟪e₀, e₁⟫ = 0)
    (t s : ℝ) : ⟪t • e₀ + s • e₁, e₀⟫ = t := by
  have h10 : ⟪e₁, e₀⟫ = 0 := inner_eq_zero_symm.mp horth
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, h10, real_inner_self_eq_norm_sq,
    he₀]
  ring

omit [InnerProductSpace ℝ E] in
private lemma norm_eq_of_norm_sq_eq {x : E} {r : ℝ} (hr : 0 ≤ r) (hx : ‖x‖ ^ 2 = r ^ 2) :
    ‖x‖ = r :=
  (sq_eq_sq₀ (norm_nonneg _) hr).mp hx

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

private lemma infinite_euclideanSpace {d : ℕ} (hd : 0 < d) :
    Infinite (EuclideanSpace ℝ (Fin d)) := by
  refine Infinite.of_injective
    (fun t : ℝ => EuclideanSpace.single (⟨0, hd⟩ : Fin d) t) ?_
  intro t s hts
  have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v.ofLp ⟨0, hd⟩) hts
  simp only [PiLp.single_apply] at hcoord
  exact hcoord

private lemma exists_fresh {d : ℕ} (hd : 0 < d) {ι : Type*} [Finite ι]
    (g : ι → EuclideanSpace ℝ (Fin d)) : ∃ p, ∀ i, p ≠ g i := by
  have hinf : (Set.univ : Set (EuclideanSpace ℝ (Fin d))).Infinite := by
    rw [Set.infinite_univ_iff]
    exact infinite_euclideanSpace hd
  obtain ⟨p, -, hp⟩ := hinf.exists_notMem_finite (Set.finite_range g)
  refine ⟨p, ?_⟩
  intro i hpi
  exact hp ⟨i, hpi.symm⟩

private lemma infinite_unitSphere {d : ℕ} (hd : 2 ≤ d) (c : EuclideanSpace ℝ (Fin d)) :
    (sphere c 1).Infinite := by
  have htop : 2 ≤ finrank ℝ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) := by
    rw [finrank_top, finrank_euclideanSpace_fin]
    exact hd
  obtain ⟨e₀, e₁, he₀, he₁, horth, -, -⟩ := exists_orthonormal_pair_of_finrank_ge_two htop
  refine Set.Infinite.mono ?_ (infinite_semicircle c e₀ e₁ he₀ horth one_pos)
  rintro _ ⟨t, ht, rfl⟩
  rw [mem_sphere, dist_eq_norm]
  have hshift : c + t • e₀ + Real.sqrt ((1 : ℝ) ^ 2 - t ^ 2) • e₁ - c =
      t • e₀ + Real.sqrt ((1 : ℝ) ^ 2 - t ^ 2) • e₁ := by
    abel
  rw [hshift]
  refine norm_eq_of_norm_sq_eq zero_le_one ?_
  have hs : 0 ≤ (1 : ℝ) ^ 2 - t ^ 2 :=
    sub_nonneg.mpr <| sq_le_sq' (by linarith [ht.1]) ht.2
  rw [norm_sq_orthonormal he₀ he₁ horth, Real.sq_sqrt hs]
  ring

/-- Unit spheres about two centres less than `2` apart meet in an infinite set once `d ≥ 3`.
Equal centres leave the whole unit sphere. Distinct centres leave a sphere of radius
`√(1 − δ²/4) > 0` in the orthogonal complement of the line through them, and that complement has
dimension `d − 1 ≥ 2`. -/
private lemma infinite_unitSphere_inter_of_dist_lt_two {d : ℕ} (hd : 3 ≤ d)
    {c₁ c₂ : EuclideanSpace ℝ (Fin d)} (hdist : dist c₁ c₂ < 2) :
    (sphere c₁ 1 ∩ sphere c₂ 1).Infinite := by
  by_cases hEq : c₁ = c₂
  · subst hEq
    rw [Set.inter_self]
    exact infinite_unitSphere (by omega) c₁
  · let v := c₂ - c₁
    have hv : v ≠ 0 := fun h => hEq (sub_eq_zero.mp h).symm
    have hδ : ‖v‖ < 2 := by
      rw [dist_comm] at hdist
      simpa [v, dist_eq_norm] using hdist
    have hδpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let ρ2 : ℝ := 1 - (‖v‖ / 2) ^ 2
    have hρ2 : 0 < ρ2 := by
      have hhalf : ‖v‖ / 2 < 1 := (div_lt_one₀ (by norm_num : (0 : ℝ) < 2)).mpr hδ
      have hsq : (‖v‖ / 2) ^ 2 < 1 := by
        have : (‖v‖ / 2) ^ 2 < 1 ^ 2 := (sq_lt_sq).2 <| by
          rw [abs_of_nonneg (by positivity), abs_one]
          exact hhalf
        simpa using this
      exact sub_pos.mpr hsq
    let ρ : ℝ := Real.sqrt ρ2
    have hρ : 0 < ρ := Real.sqrt_pos.mpr hρ2
    have hρsq : ρ ^ 2 = ρ2 := Real.sq_sqrt hρ2.le
    let K : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := ℝ ∙ v
    have hK : finrank ℝ K = 1 := finrank_span_singleton hv
    have hKo : 2 ≤ finrank ℝ Kᗮ := by
      have hsum := K.finrank_add_finrank_orthogonal
      rw [finrank_euclideanSpace_fin, hK] at hsum
      omega
    obtain ⟨e₀, e₁, he₀, he₁, horth, he₀K, he₁K⟩ :=
      exists_orthonormal_pair_of_finrank_ge_two (W := Kᗮ) hKo
    have he₀v : ⟪v, e₀⟫ = 0 := mem_orthogonal_singleton_iff_inner_right.mp he₀K
    have he₁v : ⟪v, e₁⟫ = 0 := mem_orthogonal_singleton_iff_inner_right.mp he₁K
    have hhalfScalar : (⅟2 : ℝ) = 1 / 2 := by rw [invOf_eq_inv, inv_eq_one_div]
    let m := midpoint ℝ c₁ c₂
    have hleft : m - c₁ = (1 / 2 : ℝ) • v := by
      unfold m v
      rw [← vsub_eq_sub, midpoint_vsub_left, hhalfScalar, vsub_eq_sub]
    have hright : m - c₂ = -((1 / 2 : ℝ) • v) := by
      unfold m v
      rw [← vsub_eq_sub, midpoint_vsub_right, hhalfScalar, vsub_eq_sub, ← neg_sub c₂ c₁, smul_neg]
    have hhalf : ‖(1 / 2 : ℝ) • v‖ ^ 2 = (‖v‖ / 2) ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      ring
    have hsumρ : (‖v‖ / 2) ^ 2 + ρ2 = 1 := by
      simp only [ρ2]
      ring
    refine Set.Infinite.mono ?_ (infinite_semicircle m e₀ e₁ he₀ horth hρ)
    rintro _ ⟨t, ht, rfl⟩
    have hs : 0 ≤ ρ ^ 2 - t ^ 2 :=
      sub_nonneg.mpr <| sq_le_sq' (by linarith [ht.1, hρ.le]) ht.2
    set u : ℝ := Real.sqrt (ρ ^ 2 - t ^ 2)
    have hplan : ‖t • e₀ + u • e₁‖ ^ 2 = ρ2 := by
      rw [norm_sq_orthonormal he₀ he₁ horth, Real.sq_sqrt hs, hρsq]
      ring
    have hcross : ⟪(1 / 2 : ℝ) • v, t • e₀ + u • e₁⟫ = 0 := by
      simp [real_inner_smul_left, real_inner_smul_right, inner_add_right, he₀v, he₁v]
    have hφ₁ : m + t • e₀ + u • e₁ - c₁ = (1 / 2 : ℝ) • v + (t • e₀ + u • e₁) := by
      have : m + t • e₀ + u • e₁ - c₁ = (m - c₁) + (t • e₀ + u • e₁) := by
        abel
      rw [this, hleft]
    have hφ₂ : m + t • e₀ + u • e₁ - c₂ = -((1 / 2 : ℝ) • v) + (t • e₀ + u • e₁) := by
      have : m + t • e₀ + u • e₁ - c₂ = (m - c₂) + (t • e₀ + u • e₁) := by
        abel
      rw [this, hright]
    refine ⟨?_, ?_⟩
    · rw [mem_sphere, dist_eq_norm, hφ₁]
      refine norm_eq_of_norm_sq_eq zero_le_one ?_
      rw [norm_add_sq_real, hcross, mul_zero, add_zero, hhalf, hplan, hsumρ, one_pow]
    · have hcross' : ⟪-((1 / 2 : ℝ) • v), t • e₀ + u • e₁⟫ = 0 := by
        rw [inner_neg_left, hcross, neg_zero]
      rw [mem_sphere, dist_eq_norm, hφ₂]
      refine norm_eq_of_norm_sq_eq zero_le_one ?_
      rw [norm_add_sq_real, hcross', mul_zero, add_zero, norm_neg, hhalf, hplan, hsumρ, one_pow]

end EuclideanGeometry

namespace SimpleGraph

open EuclideanGeometry Metric

noncomputable section

private lemma dist_sq_apexP_apexM {d : ℕ} (hd : 0 < d) :
    dist (apexP d) (apexM d) ^ 2 = 2 + 2 / (d : ℝ) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [EuclideanSpace.dist_sq_eq]
  have hterm : ∀ j : Fin d,
      dist (apexP d j) (apexM d j) ^ 2 = 4 * (apexOffset d * apexOffset d) := by
    intro j
    rw [Real.dist_eq, apexP_apply, apexM_apply]
    have hdiff :
        (baseScale / (d : ℝ) + apexOffset d) - (baseScale / (d : ℝ) - apexOffset d) =
          2 * apexOffset d := by
      ring
    rw [hdiff, sq_abs]
    ring
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [apexOffset_sq hd]
  field_simp
  ring

private lemma dist_apexP_apexM {d : ℕ} (hd : 0 < d) :
    dist (apexP d) (apexM d) = Real.sqrt (2 + 2 / (d : ℝ)) := by
  have hsq := dist_sq_apexP_apexM hd
  rw [← Real.sqrt_sq (dist_nonneg (x := apexP d) (y := apexM d)), hsq]

private lemma sqrt_apex_lt_two {d : ℕ} (hd : 1 < d) :
    Real.sqrt (2 + 2 / (d : ℝ)) < 2 := by
  have hdR : (1 : ℝ) < d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := lt_trans zero_lt_one hdR
  have hfrac : 2 / (d : ℝ) < 2 := by
    rw [div_lt_iff₀ hd0]
    linarith
  have hlt : 2 + 2 / (d : ℝ) < 4 := by linarith
  calc
    Real.sqrt (2 + 2 / (d : ℝ)) < Real.sqrt 4 := Real.sqrt_lt_sqrt (by positivity) hlt
    _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private lemma exists_twoSimplices_data {d : ℕ} (hd : 0 < d) {u v : Fin (d + 2)} (huv : u ≠ v) :
    ∃ f : Fin (d + 2) → EuclideanSpace ℝ (Fin d), Function.Injective f ∧
      (∀ i j, i ≠ j → ¬ (i = u ∧ j = v) → ¬ (i = v ∧ j = u) → dist (f i) (f j) = 1) ∧
      dist (f u) (f v) = Real.sqrt (2 + 2 / (d : ℝ)) := by
  obtain ⟨κ, hκinj⟩ := exists_axis_labelling hd huv
  set S : Finset (Fin (d + 2)) := (Finset.univ.erase u).erase v with hSdef
  have hSmem : ∀ w : Fin (d + 2), w ∈ S ↔ (w ≠ u ∧ w ≠ v) := by
    intro w
    simp only [hSdef, Finset.mem_erase, Finset.mem_univ, and_true]
    exact and_comm
  set f : Fin (d + 2) → EuclideanSpace ℝ (Fin d) := fun w =>
    if w = u then apexP d else if w = v then apexM d
      else baseScale • EuclideanSpace.single (κ w) (1 : ℝ) with hfdef
  have hclass : ∀ w : Fin (d + 2),
      (w = u ∧ f w = apexP d) ∨ (w = v ∧ f w = apexM d) ∨
        (w ∈ S ∧ f w = baseScale • EuclideanSpace.single (κ w) (1 : ℝ)) := by
    intro w
    by_cases hwu : w = u
    · subst hwu
      exact Or.inl ⟨rfl, by simp [hfdef]⟩
    by_cases hwv : w = v
    · subst hwv
      exact Or.inr (Or.inl ⟨rfl, by simp [hfdef, hwu]⟩)
    exact Or.inr (Or.inr ⟨(hSmem w).mpr ⟨hwu, hwv⟩, by simp [hfdef, hwu, hwv]⟩)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a b hab
    rcases hclass a with (⟨ha, hfa⟩ | ⟨ha, hfa⟩ | ⟨ha, hfa⟩) <;>
      rcases hclass b with (⟨hb, hfb⟩ | ⟨hb, hfb⟩ | ⟨hb, hfb⟩)
    · exact ha.trans hb.symm
    · exact absurd (hfa.symm.trans (hab.trans hfb)) (apexP_ne_apexM hd)
    · exact absurd (hfa.symm.trans (hab.trans hfb)) (apexP_ne_single hd _)
    · exact absurd (hfa.symm.trans (hab.trans hfb)) (Ne.symm (apexP_ne_apexM hd))
    · exact ha.trans hb.symm
    · exact absurd (hfa.symm.trans (hab.trans hfb)) (apexM_ne_single hd _)
    · exact absurd (hfa.symm.trans (hab.trans hfb)) (Ne.symm (apexP_ne_single hd _))
    · exact absurd (hfa.symm.trans (hab.trans hfb)) (Ne.symm (apexM_ne_single hd _))
    · by_contra hne
      have haUV : a ∉ ({u, v} : Set (Fin (d + 2))) := by simp [(hSmem a).mp ha]
      have hbUV : b ∉ ({u, v} : Set (Fin (d + 2))) := by simp [(hSmem b).mp hb]
      rw [hfa, hfb] at hab
      exact absurd (single_inj hab) (hκinj a b hne haUV hbUV)
  · intro x y hxy hnab hnba
    rcases hclass x with (⟨hx, hfx⟩ | ⟨hx, hfx⟩ | ⟨hx, hfx⟩) <;>
      rcases hclass y with (⟨hy, hfy⟩ | ⟨hy, hfy⟩ | ⟨hy, hfy⟩)
    · exact (hxy (hx.trans hy.symm)).elim
    · exact (hnab ⟨hx, hy⟩).elim
    · rw [hfx, hfy]; exact dist_apexP_base hd _
    · exact (hnba ⟨hx, hy⟩).elim
    · exact (hxy (hx.trans hy.symm)).elim
    · rw [hfx, hfy]; exact dist_apexM_base hd _
    · rw [hfx, hfy, dist_comm]; exact dist_apexP_base hd _
    · rw [hfx, hfy, dist_comm]; exact dist_apexM_base hd _
    · have hxUV : x ∉ ({u, v} : Set (Fin (d + 2))) := by simp [(hSmem x).mp hx]
      have hyUV : y ∉ ({u, v} : Set (Fin (d + 2))) := by simp [(hSmem y).mp hy]
      rw [hfx, hfy]
      exact dist_single_single (hκinj x y hxy hxUV hyUV)
  · rw [show f u = apexP d from by simp [hfdef],
      show f v = apexM d from by simp [hfdef, huv.symm]]
    exact dist_apexP_apexM hd

section Tail

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- An injective placement of `dom` in which every edge of `G` with both ends in `dom` has
length one. -/
private structure PartialPlacement where
  g : V → EuclideanSpace ℝ (Fin d)
  dom : Finset V
  inj : ∀ {x y}, x ∈ dom → y ∈ dom → g x = g y → x = y
  edge : ∀ {x y}, G.Adj x y → x ∈ dom → y ∈ dom → dist (g x) (g y) = 1

private def PartialPlacement.extend_point (P : @PartialPlacement V G d) {v : V}
    (_hv : v ∉ P.dom) {p : EuclideanSpace ℝ (Fin d)} (hp : ∀ x, x ∈ P.dom → p ≠ P.g x)
    (hpNbr : ∀ {w : V}, G.Adj v w → w ∈ P.dom → dist p (P.g w) = 1) :
    @PartialPlacement V G d where
  g := fun x => if x = v then p else P.g x
  dom := insert v P.dom
  inj := by
    intro x y hx hy hxy
    by_cases hxV : x = v <;> by_cases hyV : y = v
    · exact hxV.trans hyV.symm
    · have hyD : y ∈ P.dom := (Finset.mem_insert.mp hy).resolve_left hyV
      have : p = P.g y := by simpa [hxV, hyV] using hxy
      exact (hp y hyD this).elim
    · have hxD : x ∈ P.dom := (Finset.mem_insert.mp hx).resolve_left hxV
      have : P.g x = p := by simpa [hxV, hyV] using hxy
      exact (hp x hxD this.symm).elim
    · have hxD : x ∈ P.dom := (Finset.mem_insert.mp hx).resolve_left hxV
      have hyD : y ∈ P.dom := (Finset.mem_insert.mp hy).resolve_left hyV
      exact P.inj hxD hyD (by simpa [hxV, hyV] using hxy)
  edge := by
    intro x y hxy hx hy
    by_cases hxV : x = v <;> by_cases hyV : y = v
    · exact (hxy.ne (hxV.trans hyV.symm)).elim
    · have hyD : y ∈ P.dom := (Finset.mem_insert.mp hy).resolve_left hyV
      change dist (if x = v then p else P.g x) (if y = v then p else P.g y) = 1
      rw [if_pos hxV, if_neg hyV]
      exact hpNbr (hxV ▸ hxy) hyD
    · have hxD : x ∈ P.dom := (Finset.mem_insert.mp hx).resolve_left hxV
      change dist (if x = v then p else P.g x) (if y = v then p else P.g y) = 1
      rw [if_neg hxV, if_pos hyV, dist_comm]
      exact hpNbr (hyV ▸ hxy.symm) hxD
    · have hxD : x ∈ P.dom := (Finset.mem_insert.mp hx).resolve_left hxV
      have hyD : y ∈ P.dom := (Finset.mem_insert.mp hy).resolve_left hyV
      change dist (if x = v then p else P.g x) (if y = v then p else P.g y) = 1
      rw [if_neg hxV, if_neg hyV]
      exact P.edge hxy hxD hyD

/-- Any two placed neighbours of an unplaced vertex are strictly less than `2` apart. -/
private abbrev distClosed (P : @PartialPlacement V G d) : Prop :=
  ∀ {u n1 n2 : V}, u ∉ P.dom → n1 ∈ P.dom → n2 ∈ P.dom → n1 ≠ n2 →
    G.Adj u n1 → G.Adj u n2 → dist (P.g n1) (P.g n2) < 2

private lemma distClosed_extend (P : @PartialPlacement V G d) (hD : distClosed P) {v : V}
    (hv : v ∉ P.dom) {p : EuclideanSpace ℝ (Fin d)} (hp : ∀ x, x ∈ P.dom → p ≠ P.g x)
    (hpNbr : ∀ {w : V}, G.Adj v w → w ∈ P.dom → dist p (P.g w) = 1)
    (hsafe : ∀ {u n : V}, G.Adj u v → u ∉ P.dom → n ∈ P.dom → ¬ G.Adj u n) :
    distClosed (P.extend_point hv hp hpNbr) := by
  intro u n1 n2 hu hn1 hn2 hne hu1 hu2
  have hu0 : u ∉ P.dom := fun h => hu (Finset.mem_insert_of_mem h)
  by_cases hn1v : n1 = v <;> by_cases hn2v : n2 = v
  · exact (hne (hn1v.trans hn2v.symm)).elim
  · have hn2d : n2 ∈ P.dom := (Finset.mem_insert.mp hn2).resolve_left hn2v
    exact False.elim ((hsafe (by simpa [hn1v] using hu1) hu0 hn2d) hu2)
  · have hn1d : n1 ∈ P.dom := (Finset.mem_insert.mp hn1).resolve_left hn1v
    exact False.elim ((hsafe (by simpa [hn2v] using hu2) hu0 hn1d) hu1)
  · have hn1d : n1 ∈ P.dom := (Finset.mem_insert.mp hn1).resolve_left hn1v
    have hn2d : n2 ∈ P.dom := (Finset.mem_insert.mp hn2).resolve_left hn2v
    have hlt := hD hu0 hn1d hn2d hne (by simpa [hn1v] using hu1) (by simpa [hn2v] using hu2)
    change dist (if n1 = v then p else P.g n1) (if n2 = v then p else P.g n2) < 2
    rw [if_neg hn1v, if_neg hn2v]
    exact hlt

private def of_subset {s : Finset V} (f : {v : V // v ∈ s} → EuclideanSpace ℝ (Fin d))
    (hfInj : Function.Injective f)
    (hfDist : ∀ a b : {v : V // v ∈ s}, G.Adj a.1 b.1 → dist (f a) (f b) = 1) :
    @PartialPlacement V G d where
  g := fun v => if hv : v ∈ s then f ⟨v, hv⟩ else 0
  dom := s
  inj := by
    intro x y hx hy hxy
    have hxy' : f ⟨x, hx⟩ = f ⟨y, hy⟩ := by simpa [dif_pos hx, dif_pos hy] using hxy
    exact congrArg Subtype.val (hfInj hxy')
  edge := by
    intro x y hxy hx hy
    simpa [dif_pos hx, dif_pos hy] using hfDist ⟨x, hx⟩ ⟨y, hy⟩ hxy

private lemma distClosed_of_subset {s : Finset V}
    (f : {v : V // v ∈ s} → EuclideanSpace ℝ (Fin d)) (hfInj : Function.Injective f)
    (hfDist : ∀ a b : {v : V // v ∈ s}, G.Adj a.1 b.1 → dist (f a) (f b) = 1)
    (hClose : ∀ a b : {v : V // v ∈ s}, dist (f a) (f b) < 2) :
    distClosed (of_subset f hfInj hfDist) := by
  intro u n1 n2 hu hn1 hn2 hne _ _
  have hn1s : n1 ∈ s := by simpa [of_subset] using hn1
  have hn2s : n2 ∈ s := by simpa [of_subset] using hn2
  change dist (if hv : n1 ∈ s then f ⟨n1, hv⟩ else 0) (if hv : n2 ∈ s then f ⟨n2, hv⟩ else 0) < 2
  rw [dif_pos hn1s, dif_pos hn2s]
  exact hClose ⟨n1, hn1s⟩ ⟨n2, hn2s⟩

private lemma extend_tail_aux (hd : 3 ≤ d) {s : Finset V} (bad : Finset (Sym2 V))
    (hbad_card : bad.card ≤ 2)
    (hbad_iff : ∀ {x y : V}, s(x, y) ∈ bad ↔ G.Adj x y ∧ (x ∉ s ∨ y ∉ s))
    (f : {v : V // v ∈ s} → EuclideanSpace ℝ (Fin d)) (hfInj : Function.Injective f)
    (hfDist : ∀ a b : {v : V // v ∈ s}, G.Adj a.1 b.1 → dist (f a) (f b) = 1)
    (hClose : ∀ a b : {v : V // v ∈ s}, dist (f a) (f b) < 2) : G.UnitDistEmbeddable d := by
  suffices ∀ n (P : @PartialPlacement V G d), s ⊆ P.dom → distClosed P →
      (Finset.univ \ P.dom).card = n → G.UnitDistEmbeddable d from
    this (Finset.univ \ s).card (of_subset f hfInj hfDist) (Finset.Subset.refl _)
      (distClosed_of_subset f hfInj hfDist hClose) (by simp [of_subset])
  intro n
  induction n with
  | zero =>
    intro P _ _ hcard
    have hdom : ∀ x, x ∈ P.dom := by
      intro x
      have hempty : Finset.univ \ P.dom = ∅ := Finset.card_eq_zero.mp hcard
      exact Finset.sdiff_eq_empty_iff_subset.mp hempty (Finset.mem_univ x)
    refine ⟨P.g, ?_, ?_⟩
    · intro x y hxy
      exact P.inj (hdom x) (hdom y) hxy
    · intro x y hxy
      exact P.edge hxy (hdom x) (hdom y)
  | succ n ih =>
    intro P hs hD hcard
    let nbrIn : V → Finset V := fun u =>
      Finset.univ.filter fun w => G.Adj u w ∧ w ∈ P.dom
    let pending := (Finset.univ \ P.dom).filter fun v =>
      (bad.filter fun e => v ∈ e).Nonempty
    have mem_nbr {u w : V} : w ∈ nbrIn u ↔ G.Adj u w ∧ w ∈ P.dom := by
      simp [nbrIn, Finset.mem_filter]
    have hstep (v : V) (hv : v ∉ P.dom) (p : EuclideanSpace ℝ (Fin d))
        (hp : ∀ x, x ∈ P.dom → p ≠ P.g x)
        (hpNbr : ∀ {w : V}, G.Adj v w → w ∈ P.dom → dist p (P.g w) = 1)
        (hsafe : ∀ {u n : V}, G.Adj u v → u ∉ P.dom → n ∈ P.dom → ¬ G.Adj u n) :
        G.UnitDistEmbeddable d := by
      let P' := P.extend_point hv hp hpNbr
      have hs' : s ⊆ P'.dom := fun x hx => Finset.mem_insert_of_mem (hs hx)
      have hD' : distClosed P' := distClosed_extend P hD hv hp hpNbr hsafe
      have hcard' : (Finset.univ \ P'.dom).card = n := by
        have hvU : v ∈ Finset.univ \ P.dom := Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩
        have hdom : P'.dom = insert v P.dom := rfl
        rw [hdom, Finset.sdiff_insert, Finset.card_erase_of_mem hvU, hcard]
        omega
      exact ih P' hs' hD' hcard'
    by_cases hpen : pending.Nonempty
    · obtain ⟨v, hvP, hvMax⟩ := Finset.exists_max_image pending (fun u => (nbrIn u).card) hpen
      have hvSdiff : v ∈ Finset.univ \ P.dom := (Finset.mem_filter.mp hvP).1
      have hv : v ∉ P.dom := (Finset.mem_sdiff.mp hvSdiff).2
      have hv_not_s : v ∉ s := fun h => hv (hs h)
      have hk : (nbrIn v).card ≤ 2 := by
        have hle : (nbrIn v).card ≤ bad.card := by
          refine Finset.card_le_card_of_injOn (fun w => s(v, w)) ?_ ?_
          · intro w hw
            exact hbad_iff.mpr ⟨(mem_nbr.mp hw).1, Or.inl hv_not_s⟩
          · intro w1 hw1 w2 hw2 heq
            have hw1Adj : G.Adj v w1 := (mem_nbr.mp hw1).1
            rcases Sym2.eq_iff.mp heq with ⟨-, hw⟩ | ⟨-, hw1v⟩
            · exact hw
            · exact (hw1Adj.ne hw1v.symm).elim
        exact hle.trans hbad_card
      have hsafe : ∀ {u n0 : V}, G.Adj u v → u ∉ P.dom → n0 ∈ P.dom → ¬ G.Adj u n0 := by
        intro u n0 huAdj huOut hnDom hunAdj
        have hu_not_s : u ∉ s := fun h => huOut (hs h)
        have he1 : s(v, u) ∈ bad := hbad_iff.mpr ⟨huAdj.symm, Or.inl hv_not_s⟩
        have he2 : s(u, n0) ∈ bad := hbad_iff.mpr ⟨hunAdj, Or.inl hu_not_s⟩
        have hne_e : s(v, u) ≠ s(u, n0) := by
          intro h
          rcases Sym2.eq_iff.mp h with ⟨hvu, -⟩ | ⟨hvn, -⟩
          · exact huAdj.symm.ne hvu
          · exact hv (hvn ▸ hnDom)
        have hnot : s(v, u) ∉ ({s(u, n0)} : Finset (Sym2 V)) := by simpa using hne_e
        have hpair : ({s(v, u), s(u, n0)} : Finset (Sym2 V)).card = 2 := by
          rw [Finset.card_insert_of_notMem hnot, Finset.card_singleton]
        have hsub : ({s(v, u), s(u, n0)} : Finset (Sym2 V)) ⊆ bad := by
          intro e he
          simp only [Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl
          · exact he1
          · exact he2
        have hbad_eq : bad = {s(v, u), s(u, n0)} :=
          (Finset.eq_of_subset_of_card_le hsub (by rw [hpair]; exact hbad_card)).symm
        have hcard_v : (nbrIn v).card = 0 := by
          rw [Finset.card_eq_zero]
          ext w
          simp only [Finset.notMem_empty, iff_false]
          intro hw
          obtain ⟨hwAdj, hwDom⟩ := mem_nbr.mp hw
          have hwE : s(v, w) ∈ bad := hbad_iff.mpr ⟨hwAdj, Or.inl hv_not_s⟩
          rw [hbad_eq] at hwE
          simp only [Finset.mem_insert, Finset.mem_singleton] at hwE
          rcases hwE with hwE | hwE
          · rcases Sym2.eq_iff.mp hwE with ⟨-, hw⟩ | ⟨hvu, -⟩
            · exact huOut (hw ▸ hwDom)
            · exact huAdj.symm.ne hvu
          · rcases Sym2.eq_iff.mp hwE with ⟨hvu, -⟩ | ⟨hvn, -⟩
            · exact huAdj.symm.ne hvu
            · exact hv (hvn ▸ hnDom)
        have huPending : u ∈ pending := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huOut⟩, ?_⟩
          refine ⟨s(u, n0), ?_⟩
          exact Finset.mem_filter.mpr ⟨he2, Sym2.mem_mk_left u n0⟩
        have hcard_u : 1 ≤ (nbrIn u).card := by
          refine Finset.card_pos.mpr ⟨n0, ?_⟩
          simp [nbrIn, hunAdj, hnDom]
        have hle_max : (nbrIn u).card ≤ (nbrIn v).card := hvMax u huPending
        omega
      match hcardN : (nbrIn v).card with
      | 0 =>
        obtain ⟨p, hpFresh⟩ := exists_fresh (by omega : 0 < d)
          (fun x : {x // x ∈ P.dom} => P.g x.1)
        have hp : ∀ x, x ∈ P.dom → p ≠ P.g x := fun x hx => hpFresh ⟨x, hx⟩
        have hempty : nbrIn v = ∅ := Finset.card_eq_zero.mp hcardN
        have hpNbr : ∀ {w : V}, G.Adj v w → w ∈ P.dom → dist p (P.g w) = 1 := by
          intro w hw hwd
          have : w ∈ nbrIn v := by simp [nbrIn, hw, hwd]
          simp [hempty] at this
        exact hstep v hv p hp hpNbr hsafe
      | 1 =>
        obtain ⟨n1, hn1⟩ := Finset.card_eq_one.mp hcardN
        have hn1mem : n1 ∈ nbrIn v := by simp [hn1]
        have hn1adj : G.Adj v n1 := (mem_nbr.mp hn1mem).1
        have hn1d : n1 ∈ P.dom := (mem_nbr.mp hn1mem).2
        have hUsed : (Set.range fun x : {x // x ∈ P.dom} => P.g x.1).Finite := Set.finite_range _
        obtain ⟨p, hpSphere, hpOut⟩ :=
          (infinite_unitSphere (by omega) (P.g n1)).exists_notMem_finite hUsed
        have hp : ∀ x, x ∈ P.dom → p ≠ P.g x := by
          intro x hx hpeq
          exact hpOut ⟨⟨x, hx⟩, hpeq.symm⟩
        have hpNbr : ∀ {w : V}, G.Adj v w → w ∈ P.dom → dist p (P.g w) = 1 := by
          intro w hw hwd
          have hwmem : w ∈ nbrIn v := by simp [nbrIn, hw, hwd]
          have hwEq : w = n1 := by simpa [hn1] using hwmem
          subst hwEq
          exact mem_sphere.mp hpSphere
        exact hstep v hv p hp hpNbr hsafe
      | 2 =>
        obtain ⟨n1, n2, hne12, hpair⟩ := Finset.card_eq_two.mp hcardN
        have hn1mem : n1 ∈ nbrIn v := by simp [hpair]
        have hn2mem : n2 ∈ nbrIn v := by simp [hpair]
        have hn1adj : G.Adj v n1 := (mem_nbr.mp hn1mem).1
        have hn2adj : G.Adj v n2 := (mem_nbr.mp hn2mem).1
        have hn1d : n1 ∈ P.dom := (mem_nbr.mp hn1mem).2
        have hn2d : n2 ∈ P.dom := (mem_nbr.mp hn2mem).2
        have hlt : dist (P.g n1) (P.g n2) < 2 :=
          hD hv hn1d hn2d hne12 hn1adj hn2adj
        have hUsed : (Set.range fun x : {x // x ∈ P.dom} => P.g x.1).Finite := Set.finite_range _
        obtain ⟨p, hpInt, hpOut⟩ :=
          (infinite_unitSphere_inter_of_dist_lt_two hd hlt).exists_notMem_finite hUsed
        have hp : ∀ x, x ∈ P.dom → p ≠ P.g x := by
          intro x hx hpeq
          exact hpOut ⟨⟨x, hx⟩, hpeq.symm⟩
        have hpNbr : ∀ {w : V}, G.Adj v w → w ∈ P.dom → dist p (P.g w) = 1 := by
          intro w hw hwd
          have hwmem : w ∈ nbrIn v := by simp [nbrIn, hw, hwd]
          have hwEq : w = n1 ∨ w = n2 := by
            have : w ∈ ({n1, n2} : Finset V) := by simpa [hpair] using hwmem
            simpa using this
          rcases hwEq with rfl | rfl
          · exact mem_sphere.mp hpInt.1
          · exact mem_sphere.mp hpInt.2
        exact hstep v hv p hp hpNbr hsafe
      | k + 3 =>
        exfalso
        rw [hcardN] at hk
        omega
    · have hpend_empty : pending = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpen
      have hcompl : (Finset.univ \ P.dom).Nonempty :=
        Finset.card_pos.mp (by rw [hcard]; exact Nat.succ_pos n)
      obtain ⟨v, hvU⟩ := hcompl
      have hv : v ∉ P.dom := (Finset.mem_sdiff.mp hvU).2
      have hv_not_s : v ∉ s := fun h => hv (hs h)
      have hiso : ∀ w, ¬ G.Adj v w := by
        intro w hw
        have he : s(v, w) ∈ bad := hbad_iff.mpr ⟨hw, Or.inl hv_not_s⟩
        have hvPending : v ∈ pending := by
          refine Finset.mem_filter.mpr ⟨hvU, ?_⟩
          refine ⟨s(v, w), ?_⟩
          exact Finset.mem_filter.mpr ⟨he, Sym2.mem_mk_left v w⟩
        simp [hpend_empty] at hvPending
      obtain ⟨p, hpFresh⟩ := exists_fresh (by omega : 0 < d)
        (fun x : {x // x ∈ P.dom} => P.g x.1)
      have hp : ∀ x, x ∈ P.dom → p ≠ P.g x := fun x hx => hpFresh ⟨x, hx⟩
      have hpNbr : ∀ {w : V}, G.Adj v w → w ∈ P.dom → dist p (P.g w) = 1 := by
        intro w hw _
        exact (hiso w hw).elim
      have hsafe : ∀ {u n0 : V}, G.Adj u v → u ∉ P.dom → n0 ∈ P.dom → ¬ G.Adj u n0 := by
        intro u n0 huAdj _ _
        exact (hiso u huAdj.symm).elim
      exact hstep v hv p hp hpNbr hsafe

end Tail

@[expose] public section

/-- On `d + 2` vertices, every pair except a fixed pair `{a, b}` can be placed at distance one in
`ℝᵈ`, and the exceptional pair sits at distance `√(2 + 2/d)`.

The `d` vertices other than `a` and `b` are the scaled basis vectors `baseScale • eᵢ`, and `a`, `b`
are the two constant apexes of `CompleteMinusEdgeDimension`. For `d = 1` that distance equals `2`,
so the strict inequality needs `d ≥ 2`. FKS, `main.tex` lines 355–356. -/
theorem exists_twoSimplices_placement {d : ℕ} (hd : 1 < d) {a b : Fin (d + 2)} (hab : a ≠ b) :
    ∃ f : Fin (d + 2) → EuclideanSpace ℝ (Fin d), Function.Injective f ∧
      (∀ i j, i ≠ j → ¬ (i = a ∧ j = b) → ¬ (i = b ∧ j = a) → dist (f i) (f j) = 1) ∧
      dist (f a) (f b) = Real.sqrt (2 + 2 / (d : ℝ)) ∧
      dist (f a) (f b) < 2 := by
  have hd0 : 0 < d := by omega
  obtain ⟨f, hfInj, hfDist, hfEq⟩ := exists_twoSimplices_data hd0 hab
  exact ⟨f, hfInj, hfDist, hfEq, by rw [hfEq]; exact sqrt_apex_lt_two hd⟩

/-- Attach a tail of at most two edges to a placed set whose pairs are less than `2` apart.

`t` is a set of at most two unordered pairs that covers every edge of `G` with an end outside
`s`: an edge not in `t` has both ends in `s`. That is the witness form of "at most two edges fail
to have both ends in `s`". It does not ask `G` to decide adjacency in the statement. The proof
places vertices outside `s` by always extending a pending vertex with the greatest number of
already placed neighbours, so a vertex is asked to meet two placed neighbours only when both
already lie in `s`. For `d ≥ 3` the resulting unit spheres meet in an infinite set, and the
finitely many used points can be avoided. FKS, `main.tex` lines 358–359. -/
theorem UnitDistEmbeddable.extend_tail {V : Type*} [Finite V] {G : SimpleGraph V} {d : ℕ}
    (hd : 3 ≤ d) {s : Finset V} (f : {v : V // v ∈ s} → EuclideanSpace ℝ (Fin d))
    (hfInj : Function.Injective f)
    (hfDist : ∀ a b, (G.induce (s : Set V)).Adj a b → dist (f a) (f b) = 1)
    (hClose : ∀ a b, dist (f a) (f b) < 2)
    (hTail : ∃ t : Finset (Sym2 V), t.card ≤ 2 ∧
      ∀ ⦃x y : V⦄, G.Adj x y → s(x, y) ∉ t → x ∈ s ∧ y ∈ s) : G.UnitDistEmbeddable d := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have : DecidableEq V := Classical.decEq V
  have : DecidableRel G.Adj := Classical.decRel G.Adj
  obtain ⟨tCover, htCard, hcov⟩ := hTail
  let bad := G.edgeFinset.filter fun e => ¬ e ∈ s.sym2
  have hsub : bad ⊆ tCover := by
    intro e he
    rw [e.out_eq.symm] at he ⊢
    obtain ⟨heE, hnot⟩ := Finset.mem_filter.mp he
    have hadj : G.Adj e.out.1 e.out.2 := by
      rw [← mem_edgeSet]
      exact mem_edgeFinset.mp heE
    by_contra hnin
    have hin : e.out.1 ∈ s ∧ e.out.2 ∈ s := hcov hadj hnin
    exact hnot <| by
      rw [Finset.mem_sym2_iff]
      intro a ha
      rcases Sym2.mem_iff.mp ha with rfl | rfl
      · exact hin.1
      · exact hin.2
  have hbad_card : bad.card ≤ 2 := (Finset.card_le_card hsub).trans htCard
  have hbad_iff : ∀ {x y : V}, s(x, y) ∈ bad ↔ G.Adj x y ∧ (x ∉ s ∨ y ∉ s) := by
    intro x y
    constructor
    · intro h
      obtain ⟨heE, hnot⟩ := Finset.mem_filter.mp h
      have hadj : G.Adj x y := by
        rw [← mem_edgeSet]
        exact mem_edgeFinset.mp heE
      refine ⟨hadj, ?_⟩
      by_contra hboth
      simp only [not_or, not_not] at hboth
      exact hnot <| by
        rw [Finset.mem_sym2_iff]
        intro a ha
        rcases Sym2.mem_iff.mp ha with rfl | rfl
        · exact hboth.1
        · exact hboth.2
    · intro ⟨hadj, hnot⟩
      refine Finset.mem_filter.mpr ⟨mem_edgeFinset.mpr hadj, ?_⟩
      intro hsym
      rw [Finset.mem_sym2_iff] at hsym
      rcases hnot with hx | hy
      · exact hx (hsym x (Sym2.mem_mk_left x y))
      · exact hy (hsym y (Sym2.mem_mk_right x y))
  have hfDist' : ∀ a b : {v : V // v ∈ s}, G.Adj a.1 b.1 → dist (f a) (f b) = 1 :=
    fun a b h => hfDist a b (induce_adj.mpr h)
  exact extend_tail_aux hd bad hbad_card hbad_iff f hfInj hfDist' hClose

end

end

end SimpleGraph

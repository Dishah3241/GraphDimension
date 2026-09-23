/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Sphere.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Spherical placement in `ℝ²` for maximum degree one

A graph of maximum degree at most one is a matching together with isolated vertices. On the circle
of radius `1/√2`, a matched pair sits a quarter turn apart, and distinct components sit at angles
`2π a / (2|V| + 1)`. Those angles are unique modulo `2π`, and a quarter turn is never one of them.

## References

Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, J. Combin. Theory Ser. A
**171** (2020), 105146, arXiv 1802.03092, Proposition 2, the case `d = 2` (`main.tex` line 123).
-/

open scoped InnerProductSpace

namespace SimpleGraph

noncomputable section

private def onCircle (θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun i =>
    if i.val = 0 then (Real.sqrt 2)⁻¹ * Real.cos θ else (Real.sqrt 2)⁻¹ * Real.sin θ

private lemma sqrt_two_inv_sq : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private lemma sqrt_two_inv_ne_zero : ((Real.sqrt 2)⁻¹ : ℝ) ≠ 0 := by
  positivity

private lemma onCircle_zero (θ : ℝ) : onCircle θ 0 = (Real.sqrt 2)⁻¹ * Real.cos θ := by
  simp [onCircle, PiLp.toLp_apply]

private lemma onCircle_one (θ : ℝ) : onCircle θ 1 = (Real.sqrt 2)⁻¹ * Real.sin θ := by
  simp [onCircle, PiLp.toLp_apply]

private lemma norm_sq_onCircle (θ : ℝ) : ‖onCircle θ‖ ^ 2 = 1 / 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, onCircle_zero, onCircle_one,
    mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one, sqrt_two_inv_sq]

private lemma inner_onCircle_add_pi_div_two (θ : ℝ) :
    ⟪onCircle θ, onCircle (θ + Real.pi / 2)⟫_ℝ = 0 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, onCircle_zero, onCircle_one, onCircle_zero, onCircle_one,
    Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

private lemma exists_int_of_onCircle_eq {θ φ : ℝ} (h : onCircle θ = onCircle φ) :
    ∃ k : ℤ, θ - φ = k * (2 * Real.pi) := by
  have h0 := congr_arg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h
  have h1 := congr_arg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) h
  rw [onCircle_zero, onCircle_zero, mul_right_inj' sqrt_two_inv_ne_zero] at h0
  rw [onCircle_one, onCircle_one, mul_right_inj' sqrt_two_inv_ne_zero] at h1
  have hcos : Real.cos (θ - φ) = 1 := by
    rw [Real.cos_sub, h0, h1]
    have hsq : Real.cos φ * Real.cos φ + Real.sin φ * Real.sin φ =
        Real.cos φ ^ 2 + Real.sin φ ^ 2 := by ring
    rw [hsq, Real.cos_sq_add_sin_sq]
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff (θ - φ)).1 hcos
  exact ⟨k, by rw [← hk, mul_comm]⟩

/-- Angles `2π a / M` and `2π b / M`, with `a, b < M`, agree modulo `2π` only when `a = b`. -/
private lemma eq_of_base_angle {a b M : ℕ} {k : ℤ} (ha : a < M) (hb : b < M)
    (h : 2 * Real.pi * (a : ℝ) / M - 2 * Real.pi * (b : ℝ) / M = k * (2 * Real.pi)) :
    a = b := by
  have hM : (0 : ℤ) < M := by omega
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hπ : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have hsub : ((a : ℝ) - b) / M = k := by
    have h' : 2 * Real.pi * (((a : ℝ) - b) / M) = k * (2 * Real.pi) := by
      rw [mul_div_assoc']
      convert h using 1
      ring
    exact mul_left_cancel₀ hπ (by simpa [mul_comm] using h')
  have hint : ((a : ℤ) - b) = k * M := by
    have : ((a : ℝ) - b) = k * M := by
      rw [← hsub, div_mul_cancel₀ _ hMr]
    exact_mod_cast this
  have habs : |(a : ℤ) - b| < M := by
    rw [abs_lt]
    constructor <;> omega
  have hkabs : |k| * M < M := by
    calc
      |k| * M = |k * M| := by rw [abs_mul, abs_of_pos hM]
      _ = |(a : ℤ) - b| := by rw [← hint]
      _ < M := habs
  have hklt : |k| < 1 := by
    have hlt : |k| * M < 1 * M := by simpa using hkabs
    exact (mul_lt_mul_iff_of_pos_right hM).mp hlt
  have hk : k = 0 := by
    have hbound : -1 < k ∧ k < 1 := abs_lt.mp hklt
    omega
  have : ((a : ℤ) - b) = 0 := by simpa [hk] using hint
  omega

/-- A base angle and a base angle shifted by `π/2` never agree modulo `2π` when the denominator
is an odd number `2N + 1`. -/
private lemma false_of_quarter_shift {a b N : ℕ} {k : ℤ}
    (h : 2 * Real.pi * (a : ℝ) / (2 * N + 1) -
        (2 * Real.pi * (b : ℝ) / (2 * N + 1) + Real.pi / 2) = k * (2 * Real.pi)) :
    False := by
  set M : ℕ := 2 * N + 1
  have hM0 : (0 : ℕ) < M := by
    dsimp [M]
    omega
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have h1 : 2 * Real.pi * ((a : ℝ) - b) / M - Real.pi / 2 = k * (2 * Real.pi) := by
    have hMdef : (M : ℝ) = 2 * (N : ℝ) + 1 := by
      dsimp [M]
      simp
    rw [hMdef]
    convert h using 1
    ring
  have h2 : 2 * Real.pi * ((a : ℝ) - b) - Real.pi / 2 * M = k * (2 * Real.pi) * M := by
    have hmul := congrArg (fun t : ℝ => t * M) h1
    rw [sub_mul, div_mul_cancel₀ _ hMr] at hmul
    simpa [mul_assoc] using hmul
  have h3 : (2 : ℝ) * ((a : ℝ) - b) - (M : ℝ) / 2 = (k : ℝ) * 2 * M := by
    have hdiv := congrArg (fun t : ℝ => t / Real.pi) h2
    field_simp [hπ] at hdiv
    linarith
  have h4 : (4 : ℝ) * ((a : ℝ) - b) = (M : ℝ) * ((4 : ℝ) * k + 1) := by
    linarith
  have hint : (4 : ℤ) * ((a : ℤ) - b) = (M : ℤ) * (4 * k + 1) := by
    exact_mod_cast h4
  have hL : ((4 : ℤ) * ((a : ℤ) - b)) % 2 = 0 := by
    have : (4 : ℤ) * ((a : ℤ) - b) = 2 * (2 * ((a : ℤ) - b)) := by ring
    rw [this, Int.mul_emod_right]
  have hMmod : (M : ℤ) % 2 = 1 := by
    have : (M : ℤ) = 2 * (N : ℤ) + 1 := by
      dsimp [M]
    rw [this, Int.add_emod, Int.mul_emod_right]
    norm_num
  have hkmod : (4 * k + 1) % 2 = 1 := by
    have : (4 : ℤ) * k = 2 * (2 * k) := by ring
    rw [this, Int.add_emod, Int.mul_emod_right]
    norm_num
  have hR : ((M : ℤ) * (4 * k + 1)) % 2 = 1 := by
    rw [Int.mul_emod, hMmod, hkmod]
    norm_num
  have hmod : ((4 : ℤ) * ((a : ℤ) - b)) % 2 = ((M : ℤ) * (4 * k + 1)) % 2 := by
    rw [hint]
  rw [hL, hR] at hmod
  exact absurd hmod (by norm_num)

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private def anchor (e : V ≃ Fin (Fintype.card V)) (v : V) : V :=
  if h : ∃ w, G.neighborFinset v = {w} then
    let w := Classical.choose h
    if e w < e v then w else v
  else
    v

omit [DecidableEq V] in
private lemma neighborFinset_card_le_one (h : ∀ v, G.degree v ≤ 1) (v : V) :
    (G.neighborFinset v).card ≤ 1 := by
  rw [card_neighborFinset_eq_degree]
  exact h v

omit [DecidableEq V] in
private lemma neighborFinset_eq_singleton_of_adj (h : ∀ v, G.degree v ≤ 1) {v w : V}
    (hvw : G.Adj v w) : G.neighborFinset v = {w} := by
  have hmem : w ∈ G.neighborFinset v := (G.mem_neighborFinset v w).2 hvw
  have hcard : (G.neighborFinset v).card = 1 := by
    have hle := neighborFinset_card_le_one h v
    have hpos : 0 < (G.neighborFinset v).card := Finset.card_pos.mpr ⟨w, hmem⟩
    omega
  obtain ⟨u, hu⟩ := (Finset.card_eq_one).1 hcard
  have : w = u := by
    rw [hu] at hmem
    exact Finset.mem_singleton.1 hmem
  simpa [this] using hu

omit [DecidableEq V] in
private lemma anchor_choose_spec {v : V}
    (h : ∃ w, G.neighborFinset v = {w}) :
    G.neighborFinset v = {Classical.choose h} :=
  Classical.choose_spec h

private lemma anchor_eq_self_of_not_singleton (e : V ≃ Fin (Fintype.card V)) {v : V}
    (h : ¬∃ w, G.neighborFinset v = {w}) : anchor (G := G) e v = v := by
  simp [anchor, h]

private lemma adj_anchor_of_ne (e : V ≃ Fin (Fintype.card V))
    {v : V} (hne : v ≠ anchor (G := G) e v) :
    G.Adj v (anchor (G := G) e v) ∧ e (anchor (G := G) e v) < e v := by
  have hs : ∃ w, G.neighborFinset v = {w} := by
    by_contra h
    exact hne (anchor_eq_self_of_not_singleton e h).symm
  let w := Classical.choose hs
  have hw : G.neighborFinset v = {w} := anchor_choose_spec hs
  have hlt : e w < e v := by
    by_contra hnot
    have : anchor (G := G) e v = v := by simp [anchor, hs, w, hnot]
    exact hne this.symm
  have hadj : G.Adj v w :=
    (G.mem_neighborFinset v w).1 (by rw [hw]; exact Finset.mem_singleton_self w)
  have hanchor : anchor (G := G) e v = w := by simp [anchor, hs, w, hlt]
  exact ⟨hanchor ▸ hadj, hanchor ▸ hlt⟩

private lemma anchor_eq_of_adj (hdeg : ∀ v, G.degree v ≤ 1) (e : V ≃ Fin (Fintype.card V))
    {v w : V} (hvw : G.Adj v w) : anchor (G := G) e v = anchor (G := G) e w := by
  have hv : G.neighborFinset v = {w} := neighborFinset_eq_singleton_of_adj hdeg hvw
  have hw : G.neighborFinset w = {v} := neighborFinset_eq_singleton_of_adj hdeg hvw.symm
  have hne : v ≠ w := hvw.ne
  have hlt : e v ≠ e w := by
    intro h
    exact hne (e.injective h)
  rcases lt_or_gt_of_ne hlt with hlt | hgt
  · have hanchv : anchor (G := G) e v = v := by
      have hs : ∃ u, G.neighborFinset v = {u} := ⟨w, hv⟩
      have hchoose : Classical.choose hs = w :=
        Finset.singleton_inj.mp ((anchor_choose_spec hs).symm.trans hv)
      simp [anchor, hs, hchoose, not_lt.mpr hlt.le]
    have hanchw : anchor (G := G) e w = v := by
      have hs : ∃ u, G.neighborFinset w = {u} := ⟨v, hw⟩
      have hchoose : Classical.choose hs = v :=
        Finset.singleton_inj.mp ((anchor_choose_spec hs).symm.trans hw)
      simp [anchor, hs, hchoose, hlt]
    rw [hanchv, hanchw]
  · have hanchw : anchor (G := G) e w = w := by
      have hs : ∃ u, G.neighborFinset w = {u} := ⟨v, hw⟩
      have hchoose : Classical.choose hs = v :=
        Finset.singleton_inj.mp ((anchor_choose_spec hs).symm.trans hw)
      simp [anchor, hs, hchoose, not_lt.mpr hgt.le]
    have hanchv : anchor (G := G) e v = w := by
      have hs : ∃ u, G.neighborFinset v = {u} := ⟨w, hv⟩
      have hchoose : Classical.choose hs = w :=
        Finset.singleton_inj.mp ((anchor_choose_spec hs).symm.trans hv)
      simp [anchor, hs, hchoose, hgt]
    rw [hanchv, hanchw]

private lemma unique_partner (hdeg : ∀ v, G.degree v ≤ 1) (e : V ≃ Fin (Fintype.card V))
    {v w : V} (hv : v ≠ anchor (G := G) e v) (hw : w ≠ anchor (G := G) e w)
    (hanch : anchor (G := G) e v = anchor (G := G) e w) : v = w := by
  have hva := adj_anchor_of_ne e hv
  have hwa := adj_anchor_of_ne e hw
  have hvmem : v ∈ G.neighborFinset (anchor (G := G) e v) :=
    (G.mem_neighborFinset (anchor (G := G) e v) v).2 hva.1.symm
  have hwmem : w ∈ G.neighborFinset (anchor (G := G) e v) := by
    rw [hanch]
    exact (G.mem_neighborFinset (anchor (G := G) e w) w).2 hwa.1.symm
  by_contra hne
  have htwo : 2 ≤ (G.neighborFinset (anchor (G := G) e v)).card := by
    refine Finset.one_lt_card.mpr ?_
    exact ⟨v, hvmem, w, hwmem, hne⟩
  have hle := neighborFinset_card_le_one hdeg (anchor (G := G) e v)
  omega

private def baseDenom : ℕ := 2 * Fintype.card V + 1

private def baseAngle (e : V ≃ Fin (Fintype.card V)) (v : V) : ℝ :=
  2 * Real.pi * ((e (anchor (G := G) e v)).val : ℝ) / baseDenom (V := V)

private def vertexAngle (e : V ≃ Fin (Fintype.card V)) (v : V) : ℝ :=
  if v = anchor (G := G) e v then baseAngle (G := G) e v else baseAngle (G := G) e v + Real.pi / 2

private lemma baseAngle_eq_of_anchor_eq (e : V ≃ Fin (Fintype.card V)) {v w : V}
    (h : anchor (G := G) e v = anchor (G := G) e w) :
    baseAngle (G := G) e v = baseAngle (G := G) e w := by
  simp [baseAngle, h]

omit [DecidableEq V] in
private lemma baseDenom_eq : baseDenom (V := V) = 2 * Fintype.card V + 1 := rfl

omit [DecidableEq V] in
private lemma cast_baseDenom :
    ((2 * Fintype.card V + 1 : ℕ) : ℝ) = 2 * (Fintype.card V : ℝ) + 1 := by
  simp

omit [DecidableEq V] in
private lemma val_lt_denom (e : V ≃ Fin (Fintype.card V)) (v : V) :
    (e v).val < baseDenom (V := V) := by
  rw [baseDenom_eq]
  have : (e v).val < Fintype.card V := (e v).isLt
  omega

private lemma vertexAngle_eq_base (e : V ≃ Fin (Fintype.card V)) {v : V}
    (h : v = anchor (G := G) e v) :
    vertexAngle (G := G) e v = baseAngle (G := G) e v := by
  rw [vertexAngle, if_pos h]

private lemma vertexAngle_eq_shift (e : V ≃ Fin (Fintype.card V)) {v : V}
    (h : v ≠ anchor (G := G) e v) :
    vertexAngle (G := G) e v = baseAngle (G := G) e v + Real.pi / 2 := by
  rw [vertexAngle, if_neg h]

private lemma place_injective (hdeg : ∀ v, G.degree v ≤ 1) (e : V ≃ Fin (Fintype.card V)) :
    Function.Injective fun v => onCircle (vertexAngle (G := G) e v) := by
  intro v w hxy
  obtain ⟨k, hk⟩ := exists_int_of_onCircle_eq hxy
  by_cases hv : v = anchor (G := G) e v
  · by_cases hw : w = anchor (G := G) e w
    · rw [vertexAngle_eq_base e hv, vertexAngle_eq_base e hw, baseAngle, baseAngle] at hk
      have hval : (e (anchor (G := G) e v)).val = (e (anchor (G := G) e w)).val :=
        eq_of_base_angle (val_lt_denom e _) (val_lt_denom e _) hk
      have hanch : anchor (G := G) e v = anchor (G := G) e w := e.injective (Fin.ext hval)
      rw [hv, hw, hanch]
    · rw [vertexAngle_eq_base e hv, vertexAngle_eq_shift e hw, baseAngle, baseAngle] at hk
      rw [baseDenom_eq, cast_baseDenom] at hk
      exact False.elim (false_of_quarter_shift (N := Fintype.card V)
        (a := (e (anchor (G := G) e v)).val) (b := (e (anchor (G := G) e w)).val) hk)
  · by_cases hw : w = anchor (G := G) e w
    · have hk' : vertexAngle (G := G) e w - vertexAngle (G := G) e v =
          (-k) * (2 * Real.pi) := by
        linarith
      rw [vertexAngle_eq_base e hw, vertexAngle_eq_shift e hv, baseAngle, baseAngle,
        baseDenom_eq, cast_baseDenom, ← Int.cast_neg] at hk'
      exact False.elim (false_of_quarter_shift (N := Fintype.card V)
        (a := (e (anchor (G := G) e w)).val) (b := (e (anchor (G := G) e v)).val) hk')
    · rw [vertexAngle_eq_shift e hv, vertexAngle_eq_shift e hw, baseAngle, baseAngle] at hk
      have hdiff : 2 * Real.pi * ((e (anchor (G := G) e v)).val : ℝ) / baseDenom (V := V) -
          2 * Real.pi * ((e (anchor (G := G) e w)).val : ℝ) / baseDenom (V := V) =
          k * (2 * Real.pi) := by
        linarith
      have hval : (e (anchor (G := G) e v)).val = (e (anchor (G := G) e w)).val :=
        eq_of_base_angle (val_lt_denom e _) (val_lt_denom e _) hdiff
      exact unique_partner hdeg e hv hw (e.injective (Fin.ext hval))

@[expose] public section

/-- A graph of maximum degree at most one has a spherical placement in `ℝ²`.

Matched vertices go to a pair of orthogonal points on the circle of radius `1/√2`, and the pairs
are rotated so that every vertex lands on a distinct point. -/
theorem SphereEmbeddable.of_degree_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (h : ∀ v, G.degree v ≤ 1) : G.SphereEmbeddable 2 := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  rw [SphereEmbeddable.iff_orthogonal]
  refine ⟨fun v => onCircle (vertexAngle (G := G) e v), place_injective h e,
      fun v => norm_sq_onCircle _, ?_⟩
  intro u v huv
  have hanch : anchor (G := G) e u = anchor (G := G) e v := anchor_eq_of_adj h e huv
  have hne_u : u ≠ anchor (G := G) e u ∨ v ≠ anchor (G := G) e v := by
    by_contra hboth
    have hnot := not_or.mp hboth
    have hu : u = anchor (G := G) e u := by simpa using hnot.1
    have hv : v = anchor (G := G) e v := by simpa using hnot.2
    exact huv.ne (hu.trans (hanch.trans hv.symm))
  rcases hne_u with hu | hv
  · have hvself : v = anchor (G := G) e v := by
      by_contra hvne
      exact huv.ne (unique_partner h e hu hvne hanch)
    dsimp
    rw [vertexAngle_eq_shift e hu, vertexAngle_eq_base e hvself,
      baseAngle_eq_of_anchor_eq e hanch, real_inner_comm]
    exact inner_onCircle_add_pi_div_two _
  · have huself : u = anchor (G := G) e u := by
      by_contra hune
      exact huv.ne (unique_partner h e hune hv hanch)
    dsimp
    rw [vertexAngle_eq_base e huself, vertexAngle_eq_shift e hv,
      baseAngle_eq_of_anchor_eq e hanch]
    exact inner_onCircle_add_pi_div_two _

end

end

end SimpleGraph

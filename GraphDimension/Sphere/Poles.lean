/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Sphere.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Poles of a spherical placement

A spherical placement of an induced subgraph on a coordinate hyperplane extends to the whole graph
by sending one new vertex, or two non-adjacent new vertices, to the poles
`±(1/√2) eₙ` of the sphere in `ℝⁿ⁺¹`. Every pole is orthogonal to the section, hence at distance
one from every section vertex, whether or not the pair is an edge. The two poles are `√2` apart,
so the construction requires that they not be adjacent.

## References

Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, J. Combin. Theory Ser. A
**171** (2020), 105146, arXiv 1802.03092, proof of Theorem 3.
-/

open scoped InnerProductSpace

namespace SimpleGraph

noncomputable section

/-- The scale `1/√2` of the sphere. -/
private def sphereScale : ℝ := (Real.sqrt 2)⁻¹

private lemma sphereScale_sq : sphereScale ^ 2 = 1 / 2 := by
  unfold sphereScale
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private lemma sphereScale_ne_zero : sphereScale ≠ 0 := by
  unfold sphereScale
  positivity

private lemma sphereScale_ne_neg : sphereScale ≠ -sphereScale := by
  intro h
  exact sphereScale_ne_zero (by linarith)

/-- The copy of a vector of `ℝⁿ` in the first `n` coordinates of `ℝⁿ⁺¹`. -/
private def includeFin {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.lastCases (motive := fun _ => ℝ) 0 (fun i => x i))

private lemma includeFin_castSucc {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    includeFin x i.castSucc = x i := by
  simp [includeFin, PiLp.toLp_apply]

private lemma includeFin_last {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    includeFin x (Fin.last n) = 0 := by
  simp [includeFin, PiLp.toLp_apply]

private lemma norm_sq_includeFin {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖includeFin x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc,
    includeFin_last]
  simp [includeFin_castSucc, zero_pow (by decide : (2 : ℕ) ≠ 0)]

private lemma dist_includeFin {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    dist (includeFin x) (includeFin y) = dist x y := by
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc]
  simp [includeFin_castSucc, includeFin_last, dist_self, zero_pow (by decide : (2 : ℕ) ≠ 0)]

private lemma includeFin_injective {n : ℕ} :
    Function.Injective
      (includeFin : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1))) := by
  intro x y h
  ext i
  have hcoord := congr_arg (fun z => z i.castSucc) h
  simpa [includeFin_castSucc] using hcoord

private lemma inner_includeFin_single_last {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    ⟪includeFin x, EuclideanSpace.single (Fin.last n) a⟫_ℝ = 0 := by
  rw [EuclideanSpace.inner_single_right, includeFin_last]
  simp

private lemma norm_sq_single_last {n : ℕ} (a : ℝ) (ha : a ^ 2 = 1 / 2) :
    ‖(EuclideanSpace.single (Fin.last n) a : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 = 1 / 2 := by
  rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs, ha]

private lemma dist_includeFin_single_last {n : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ ^ 2 = 1 / 2) {a : ℝ} (ha : a ^ 2 = 1 / 2) :
    dist (includeFin x) (EuclideanSpace.single (Fin.last n) a) = 1 :=
  (EuclideanGeometry.dist_eq_one_iff_inner_eq_zero_of_norm_sq_half
      (by rw [norm_sq_includeFin, hx]) (norm_sq_single_last a ha)).mpr
    (inner_includeFin_single_last x a)

-- Place the section in the first `n` coordinates and `v` at the positive pole.
open Classical in
private def embedPole {V : Type*} {n : ℕ} (v : V)
    (f : {x : V // x ≠ v} → EuclideanSpace ℝ (Fin n)) (x : V) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  if hx : x ≠ v then includeFin (f ⟨x, hx⟩)
  else EuclideanSpace.single (Fin.last n) sphereScale

private lemma embedPole_of_ne {V : Type*} {n : ℕ} {v : V}
    {f : {x : V // x ≠ v} → EuclideanSpace ℝ (Fin n)} {x : V} (hx : x ≠ v) :
    embedPole v f x = includeFin (f ⟨x, hx⟩) := by
  unfold embedPole
  split_ifs
  exact congr_arg includeFin (congr_arg f (Subtype.ext rfl))

private lemma embedPole_self {V : Type*} {n : ℕ} (v : V)
    (f : {x : V // x ≠ v} → EuclideanSpace ℝ (Fin n)) :
    embedPole v f v = EuclideanSpace.single (Fin.last n) sphereScale := by
  unfold embedPole
  split_ifs with h
  · exact absurd rfl h
  · rfl

private lemma norm_sq_embedPole {V : Type*} {n : ℕ} {v : V}
    {f : {x : V // x ≠ v} → EuclideanSpace ℝ (Fin n)}
    (hfNorm : ∀ x, ‖f x‖ ^ 2 = 1 / 2) (x : V) :
    ‖embedPole v f x‖ ^ 2 = 1 / 2 := by
  classical
  by_cases hx : x = v
  · subst hx
    rw [embedPole_self, norm_sq_single_last _ sphereScale_sq]
  · rw [embedPole_of_ne hx, norm_sq_includeFin, hfNorm]

private lemma embedPole_injective {V : Type*} {n : ℕ} {v : V}
    {f : {x : V // x ≠ v} → EuclideanSpace ℝ (Fin n)} (hfInj : Function.Injective f) :
    Function.Injective (embedPole v f) := by
  classical
  intro x y hxy
  by_cases hx : x = v
  · by_cases hy : y = v
    · exact hx.trans hy.symm
    · subst hx
      have hlast := congr_arg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z (Fin.last n)) hxy
      rw [embedPole_self, PiLp.single_eq_same, embedPole_of_ne hy, includeFin_last] at hlast
      exact absurd hlast sphereScale_ne_zero
  · by_cases hy : y = v
    · subst hy
      have hlast := congr_arg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z (Fin.last n)) hxy
      rw [embedPole_of_ne hx, includeFin_last, embedPole_self, PiLp.single_eq_same] at hlast
      exact absurd hlast.symm sphereScale_ne_zero
    · rw [embedPole_of_ne hx, embedPole_of_ne hy] at hxy
      exact congrArg Subtype.val (hfInj (includeFin_injective hxy))

-- Place the section in the first `n` coordinates, `v` at the positive pole, and `w` at the
-- negative pole.
open Classical in
private def embedPoles {V : Type*} {n : ℕ} (v w : V)
    (f : {x : V // x ≠ v ∧ x ≠ w} → EuclideanSpace ℝ (Fin n)) (x : V) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  if hx : x ≠ v ∧ x ≠ w then includeFin (f ⟨x, hx⟩)
  else if x = v then EuclideanSpace.single (Fin.last n) sphereScale
  else EuclideanSpace.single (Fin.last n) (-sphereScale)

private lemma embedPoles_of_mem {V : Type*} {n : ℕ} {v w : V}
    {f : {x : V // x ≠ v ∧ x ≠ w} → EuclideanSpace ℝ (Fin n)} {x : V}
    (hx : x ≠ v ∧ x ≠ w) :
    embedPoles v w f x = includeFin (f ⟨x, hx⟩) := by
  unfold embedPoles
  split_ifs
  exact congr_arg includeFin (congr_arg f (Subtype.ext rfl))

private lemma embedPoles_left {V : Type*} {n : ℕ} {v w : V}
    (f : {x : V // x ≠ v ∧ x ≠ w} → EuclideanSpace ℝ (Fin n)) :
    embedPoles v w f v = EuclideanSpace.single (Fin.last n) sphereScale := by
  unfold embedPoles
  split_ifs with hmem heq
  · exact absurd rfl hmem.1
  · rfl
  · exact absurd rfl heq

private lemma embedPoles_right {V : Type*} {n : ℕ} {v w : V} (hvw : v ≠ w)
    (f : {x : V // x ≠ v ∧ x ≠ w} → EuclideanSpace ℝ (Fin n)) :
    embedPoles v w f w = EuclideanSpace.single (Fin.last n) (-sphereScale) := by
  unfold embedPoles
  split_ifs with hmem heq
  · exact absurd rfl hmem.2
  · exact absurd heq hvw.symm
  · rfl

private lemma eq_or_eq_of_not_deleted {V : Type*} {v w x : V}
    (hx : ¬(x ≠ v ∧ x ≠ w)) : x = v ∨ x = w := by
  classical
  by_cases hxv : x = v
  · exact Or.inl hxv
  · refine Or.inr ?_
    by_contra hxw
    exact hx ⟨hxv, hxw⟩

private lemma neg_sphereScale_sq : (-sphereScale) ^ 2 = 1 / 2 := by
  rw [neg_sq, sphereScale_sq]

@[expose] public section

/-- A vertex deleted from a spherical placement in `ℝⁿ` can be restored at the pole
`(1/√2) · eₙ` of `ℝⁿ⁺¹`.

The section keeps its first `n` coordinates. The new vertex is orthogonal to every section
vector, so it lies at distance one from each of them. Adjacency to the new vertex is
unconstrained: non-edges may have length one. -/
theorem SphereEmbeddable.pole {V : Type*} {G : SimpleGraph V} {n : ℕ} {v : V}
    (h : (G.induce {x | x ≠ v}).SphereEmbeddable n) : G.SphereEmbeddable (n + 1) := by
  obtain ⟨f, hfInj, hfNorm, hfDist⟩ := h
  refine ⟨embedPole v f, embedPole_injective hfInj, norm_sq_embedPole hfNorm, ?_⟩
  intro a b hab
  classical
  by_cases ha : a = v
  · by_cases hb : b = v
    · exact absurd (ha.trans hb.symm) hab.ne
    · subst ha
      rw [embedPole_self, embedPole_of_ne hb, dist_comm]
      exact dist_includeFin_single_last (hfNorm ⟨b, hb⟩) sphereScale_sq
  · by_cases hb : b = v
    · subst hb
      rw [embedPole_of_ne ha, embedPole_self]
      exact dist_includeFin_single_last (hfNorm ⟨a, ha⟩) sphereScale_sq
    · rw [embedPole_of_ne ha, embedPole_of_ne hb, dist_includeFin]
      exact hfDist ⟨a, ha⟩ ⟨b, hb⟩ (induce_adj.mpr hab)

/-- Two non-adjacent vertices deleted from a spherical placement in `ℝⁿ` can be restored at the
poles `±(1/√2) · eₙ` of `ℝⁿ⁺¹`.

The section sits in the first `n` coordinates. Each pole is orthogonal to the section, so every
pair consisting of a pole and a section vertex has distance one, whether or not it is an edge.
The poles themselves are `√2` apart, and the missing edge between them is what makes the
placement legal. -/
theorem SphereEmbeddable.poles {V : Type*} {G : SimpleGraph V} {n : ℕ} {v w : V}
    (hvw : v ≠ w) (hnadj : ¬G.Adj v w)
    (h : (G.induce {x | x ≠ v ∧ x ≠ w}).SphereEmbeddable n) : G.SphereEmbeddable (n + 1) := by
  obtain ⟨f, hfInj, hfNorm, hfDist⟩ := h
  refine ⟨embedPoles v w f, ?_, ?_, ?_⟩
  · classical
    intro x y hxy
    by_cases hx : x ≠ v ∧ x ≠ w
    · by_cases hy : y ≠ v ∧ y ≠ w
      · rw [embedPoles_of_mem hx, embedPoles_of_mem hy] at hxy
        exact congrArg Subtype.val (hfInj (includeFin_injective hxy))
      · rcases eq_or_eq_of_not_deleted hy with rfl | rfl
        · have hlast :=
            congr_arg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z (Fin.last n)) hxy
          rw [embedPoles_of_mem hx, includeFin_last, embedPoles_left,
            PiLp.single_eq_same] at hlast
          exact absurd hlast.symm sphereScale_ne_zero
        · have hlast :=
            congr_arg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z (Fin.last n)) hxy
          rw [embedPoles_of_mem hx, includeFin_last, embedPoles_right hvw,
            PiLp.single_eq_same] at hlast
          exact absurd (neg_eq_zero.mp hlast.symm) sphereScale_ne_zero
    · by_cases hy : y ≠ v ∧ y ≠ w
      · rcases eq_or_eq_of_not_deleted hx with rfl | rfl
        · have hlast :=
            congr_arg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z (Fin.last n)) hxy
          rw [embedPoles_left, PiLp.single_eq_same, embedPoles_of_mem hy,
            includeFin_last] at hlast
          exact absurd hlast sphereScale_ne_zero
        · have hlast :=
            congr_arg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z (Fin.last n)) hxy
          rw [embedPoles_right hvw, PiLp.single_eq_same, embedPoles_of_mem hy,
            includeFin_last] at hlast
          exact absurd (neg_eq_zero.mp hlast) sphereScale_ne_zero
      · rcases eq_or_eq_of_not_deleted hx with rfl | rfl
        · rcases eq_or_eq_of_not_deleted hy with rfl | rfl
          · rfl
          · have hlast :=
              congr_arg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z (Fin.last n)) hxy
            rw [embedPoles_left, embedPoles_right hvw, PiLp.single_eq_same,
              PiLp.single_eq_same] at hlast
            exact absurd hlast sphereScale_ne_neg
        · rcases eq_or_eq_of_not_deleted hy with rfl | rfl
          · have hlast :=
              congr_arg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z (Fin.last n)) hxy
            rw [embedPoles_right hvw, embedPoles_left, PiLp.single_eq_same,
              PiLp.single_eq_same] at hlast
            exact absurd hlast.symm sphereScale_ne_neg
          · rfl
  · intro x
    classical
    by_cases hx : x ≠ v ∧ x ≠ w
    · rw [embedPoles_of_mem hx, norm_sq_includeFin, hfNorm]
    · rcases eq_or_eq_of_not_deleted hx with rfl | rfl
      · rw [embedPoles_left, norm_sq_single_last _ sphereScale_sq]
      · rw [embedPoles_right hvw, norm_sq_single_last _ neg_sphereScale_sq]
  · intro a b hab
    classical
    by_cases ha : a ≠ v ∧ a ≠ w
    · by_cases hb : b ≠ v ∧ b ≠ w
      · rw [embedPoles_of_mem ha, embedPoles_of_mem hb, dist_includeFin]
        exact hfDist ⟨a, ha⟩ ⟨b, hb⟩ (induce_adj.mpr hab)
      · rcases eq_or_eq_of_not_deleted hb with rfl | rfl
        · rw [embedPoles_of_mem ha, embedPoles_left]
          exact dist_includeFin_single_last (hfNorm ⟨a, ha⟩) sphereScale_sq
        · rw [embedPoles_of_mem ha, embedPoles_right hvw]
          exact dist_includeFin_single_last (hfNorm ⟨a, ha⟩) neg_sphereScale_sq
    · by_cases hb : b ≠ v ∧ b ≠ w
      · rcases eq_or_eq_of_not_deleted ha with rfl | rfl
        · rw [embedPoles_left, embedPoles_of_mem hb, dist_comm]
          exact dist_includeFin_single_last (hfNorm ⟨b, hb⟩) sphereScale_sq
        · rw [embedPoles_right hvw, embedPoles_of_mem hb, dist_comm]
          exact dist_includeFin_single_last (hfNorm ⟨b, hb⟩) neg_sphereScale_sq
      · rcases eq_or_eq_of_not_deleted ha with rfl | rfl
        · rcases eq_or_eq_of_not_deleted hb with rfl | rfl
          · exact absurd rfl hab.ne
          · exact absurd hab hnadj
        · rcases eq_or_eq_of_not_deleted hb with rfl | rfl
          · exact absurd hab.symm hnadj
          · exact absurd rfl hab.ne

end

end

end SimpleGraph

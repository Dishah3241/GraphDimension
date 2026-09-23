/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Set.Operations
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Spherical placements

An injective placement on the sphere of radius `1/√2` about the origin of `ℝⁿ` in which every edge
has length one. On that sphere, `‖x - y‖² = 1 - 2⟪x, y⟫`, so an edge has length one exactly when
the position vectors are orthogonal. A spherical placement is in particular a unit-distance
placement, and it remains one in every larger dimension and along injective homomorphisms.

## References

Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, J. Combin. Theory Ser. A
**171** (2020), 105146, arXiv 1802.03092, Definition 2.
-/

open scoped InnerProductSpace

namespace EuclideanGeometry

@[expose] public section

/-- On the sphere of radius `1/√2`, `‖x - y‖² = 1 - 2⟪x, y⟫`. -/
theorem norm_sub_sq_of_norm_sq_half {n : ℕ} {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ ^ 2 = 1 / 2) (hy : ‖y‖ ^ 2 = 1 / 2) :
    ‖x - y‖ ^ 2 = 1 - 2 * ⟪x, y⟫_ℝ := by
  rw [norm_sub_sq_real, hx, hy]
  ring

/-- On the sphere of radius `1/√2`, distance one is orthogonality of position vectors. -/
theorem dist_eq_one_iff_inner_eq_zero_of_norm_sq_half {n : ℕ} {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ ^ 2 = 1 / 2) (hy : ‖y‖ ^ 2 = 1 / 2) :
    dist x y = 1 ↔ ⟪x, y⟫_ℝ = 0 := by
  rw [dist_eq_norm]
  constructor
  · intro h
    have hsq : ‖x - y‖ ^ 2 = 1 := by rw [h, one_pow]
    rw [norm_sub_sq_of_norm_sq_half hx hy] at hsq
    linarith
  · intro h
    have hsq : ‖x - y‖ ^ 2 = 1 := by
      rw [norm_sub_sq_of_norm_sq_half hx hy, h]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by rw [hsq, one_pow])

end

end EuclideanGeometry

namespace SimpleGraph

noncomputable section

/-- The vector in `ℝᵐ` obtained by appending zero coordinates to a vector of `ℝⁿ`. -/
private def appendZero {n m : ℕ} (h : n ≤ m) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (Function.extend (Fin.castLE h) (fun i => x i) (fun _ => (0 : ℝ)))

/-- A coordinate in the image of `Fin.castLE` is copied from the original vector. -/
private lemma appendZero_castLE {n m : ℕ} (h : n ≤ m) (x : EuclideanSpace ℝ (Fin n))
    (i : Fin n) : appendZero h x (Fin.castLE h i) = x i := by
  simp only [appendZero]
  exact (Fin.castLE_injective h).extend_apply (fun i => x i) (fun _ => (0 : ℝ)) i

/-- A coordinate outside the image of `Fin.castLE` is an appended zero. -/
private lemma appendZero_eq_zero {n m : ℕ} (h : n ≤ m) (x : EuclideanSpace ℝ (Fin n))
    {j : Fin m} (hj : j ∉ Set.range (Fin.castLE h)) : appendZero h x j = 0 := by
  simp only [appendZero]
  exact Function.extend_apply' (fun i => x i) (fun _ => (0 : ℝ)) j hj

/-- Appending the same zero coordinates preserves Euclidean distance. -/
private lemma dist_appendZero {n m : ℕ} (h : n ≤ m) (x y : EuclideanSpace ℝ (Fin n)) :
    dist (appendZero h x) (appendZero h y) = dist x y := by
  have hsum :
      (∑ j : Fin m, dist (appendZero h x j) (appendZero h y j) ^ 2) =
        ∑ i : Fin n, dist (x i) (y i) ^ 2 := by
    refine (Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h)
        (fun i => dist (x i) (y i) ^ 2)
        (fun j => dist (appendZero h x j) (appendZero h y j) ^ 2) ?_ ?_).symm
    · intro j hj
      rw [appendZero_eq_zero h x hj, appendZero_eq_zero h y hj, dist_self,
        zero_pow (by decide : (2 : ℕ) ≠ 0)]
    · intro i
      rw [appendZero_castLE, appendZero_castLE]
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, hsum]

/-- The zero vector stays zero when zero coordinates are appended. -/
private lemma appendZero_zero {n m : ℕ} (h : n ≤ m) :
    appendZero h (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
  ext j
  by_cases hj : j ∈ Set.range (Fin.castLE h)
  · obtain ⟨i, rfl⟩ := hj
    rw [appendZero_castLE]
    rfl
  · rw [appendZero_eq_zero h 0 hj]
    simp

/-- Appending zero coordinates preserves the Euclidean norm. -/
private lemma norm_appendZero {n m : ℕ} (h : n ≤ m) (x : EuclideanSpace ℝ (Fin n)) :
    ‖appendZero h x‖ = ‖x‖ := by
  rw [← dist_zero_right, ← dist_zero_right, ← appendZero_zero h]
  exact dist_appendZero h x 0

/-- Appending zero coordinates is an injective map of Euclidean spaces. -/
private lemma appendZero_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (appendZero h) := by
  intro x y hxy
  ext i
  simpa [appendZero_castLE] using
    congr_arg (fun z : EuclideanSpace ℝ (Fin m) => z (Fin.castLE h i)) hxy

@[expose] public section

section

variable {V : Type*} (G : SimpleGraph V)

/-- An injective placement on the sphere of radius `1/√2` about the origin of `ℝⁿ` that puts every
edge at distance one (Frankl–Kupavskii–Swanepoel 2020, Definition 2).
Non-edges are unconstrained. -/
def SphereEmbeddable (n : ℕ) : Prop :=
  ∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧ (∀ v, ‖f v‖ ^ 2 = 1 / 2) ∧
    ∀ u v, G.Adj u v → dist (f u) (f v) = 1

end

open EuclideanGeometry

/-- On the sphere of radius `1/√2`, a placement puts edges at distance one exactly when adjacent
vertices land on orthogonal position vectors. -/
theorem SphereEmbeddable.iff_orthogonal {V : Type*} {G : SimpleGraph V} {n : ℕ} :
    G.SphereEmbeddable n ↔
      ∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧ (∀ v, ‖f v‖ ^ 2 = 1 / 2) ∧
        ∀ u v, G.Adj u v → ⟪f u, f v⟫_ℝ = 0 := by
  constructor
  · rintro ⟨f, hfInj, hfNorm, hfDist⟩
    refine ⟨f, hfInj, hfNorm, fun u v huv => ?_⟩
    exact (dist_eq_one_iff_inner_eq_zero_of_norm_sq_half (hfNorm u) (hfNorm v)).mp
      (hfDist u v huv)
  · rintro ⟨f, hfInj, hfNorm, hfOrth⟩
    refine ⟨f, hfInj, hfNorm, fun u v huv => ?_⟩
    exact (dist_eq_one_iff_inner_eq_zero_of_norm_sq_half (hfNorm u) (hfNorm v)).mpr
      (hfOrth u v huv)

/-- A spherical placement is a unit-distance placement in the same Euclidean space. -/
theorem SphereEmbeddable.toUnitDist {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (hG : G.SphereEmbeddable n) : G.UnitDistEmbeddable n := by
  obtain ⟨f, hfInj, _, hfDist⟩ := hG
  exact ⟨f, hfInj, hfDist⟩

/-- A spherical placement in `ℝⁿ` yields one in `ℝᵐ` whenever `n ≤ m`, by appending zero
coordinates. Norms and distances are unchanged. -/
theorem SphereEmbeddable.mono {V : Type*} {G : SimpleGraph V} {n m : ℕ}
    (hG : G.SphereEmbeddable n) (h : n ≤ m) : G.SphereEmbeddable m := by
  obtain ⟨f, hfInj, hfNorm, hfDist⟩ := hG
  refine ⟨appendZero h ∘ f, appendZero_injective h |>.comp hfInj, ?_, ?_⟩
  · intro v
    rw [Function.comp_apply, norm_appendZero, hfNorm v]
  · intro u v huv
    rw [Function.comp_apply, Function.comp_apply, dist_appendZero h, hfDist u v huv]

/-- A spherical placement of `G` pulls back along an injective homomorphism `φ : H →g G`. -/
theorem SphereEmbeddable.comap {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ}
    (φ : H →g G) (hφ : Function.Injective φ) (hG : G.SphereEmbeddable n) :
    H.SphereEmbeddable n := by
  obtain ⟨f, hfInj, hfNorm, hfDist⟩ := hG
  refine ⟨fun w => f (φ w), hfInj.comp hφ, fun v => hfNorm (φ v), ?_⟩
  intro u v huv
  exact hfDist (φ u) (φ v) (φ.map_adj huv)

/-- A spherical placement of `G` restricts to any spanning subgraph `H ≤ G`. -/
theorem SphereEmbeddable.of_le {V : Type*} {G H : SimpleGraph V} {n : ℕ} (hHG : H ≤ G)
    (hG : G.SphereEmbeddable n) : H.SphereEmbeddable n :=
  hG.comap (Hom.ofLE hHG) Function.injective_id

/-- Spherical embeddability is invariant under graph isomorphism. -/
theorem SphereEmbeddable.of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ}
    (e : G ≃g H) : G.SphereEmbeddable n ↔ H.SphereEmbeddable n :=
  ⟨fun h => h.comap e.symm.toEmbedding.toHom e.symm.toEmbedding.injective,
    fun h => h.comap e.toEmbedding.toHom e.toEmbedding.injective⟩

end

end

end SimpleGraph

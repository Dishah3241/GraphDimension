/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Geometry.Equilateral

import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Geometry.Euclidean.Sphere.Basic

/-!
# Common unit-distance neighbors of an equilateral set

In `ℝᵈ`, an equilateral set of `d` points has no three distinct common unit-distance neighbors.
The differences of the neighbors are orthogonal to the differences of the centres. The latter
span a hyperplane, whereas three distinct cospherical points span an affine plane.
-/

@[expose] public section

namespace EuclideanGeometry

open Module Submodule
open scoped RealInnerProductSpace

/-- In positive dimension `d`, three points at distance one from each of `d` pairwise
unit-distance points cannot be distinct. -/
theorem not_injective_common_unit_neighbors {d : ℕ} (hd : 1 ≤ d)
    {a : Fin d → EuclideanSpace ℝ (Fin d)} {b : Fin 3 → EuclideanSpace ℝ (Fin d)}
    (ha : Pairwise fun i j => dist (a i) (a j) = 1)
    (hb : Function.Injective b) (hab : ∀ i j, dist (a i) (b j) = 1) : False := by
  let i₀ : Fin d := ⟨0, hd⟩
  let : Nonempty (Fin d) := ⟨i₀⟩
  let A := vectorSpan ℝ (Set.range a)
  let B := vectorSpan ℝ (Set.range b)
  have hA : finrank ℝ A + 1 = d := by
    simpa [A] using (affineIndependent_of_pairwise_dist_eq_one ha).finrank_vectorSpan_add_one
  have hs : Cospherical (Set.range b) := by
    refine ⟨a i₀, 1, ?_⟩
    rintro _ ⟨j, rfl⟩
    rw [dist_comm, hab]
  have hB : finrank ℝ B = 2 :=
    (hs.affineIndependent Set.Subset.rfl hb).finrank_vectorSpan (Fintype.card_fin 3)
  have horth : B ≤ Aᗮ := by
    dsimp only [A, B]
    rw [vectorSpan_range_eq_span_range_vsub_right ℝ b 0, span_le]
    rintro _ ⟨j, rfl⟩
    apply (Submodule.mem_orthogonal _ _).mpr
    rw [vectorSpan_range_eq_span_range_vsub_right ℝ a i₀]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      apply inner_vsub_vsub_of_dist_eq_of_dist_eq <;>
        rw [dist_comm (b 0), dist_comm (b j), hab, hab]
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul r x _ hx => rw [inner_smul_left, hx, mul_zero]
  have hle := finrank_mono horth
  have hsum := finrank_add_finrank_orthogonal A
  rw [finrank_euclideanSpace_fin] at hsum
  omega

end EuclideanGeometry

/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic
public import GraphDimension.Combinatorics.SimpleGraph.SmallGraphsThree

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The cone over two triangles in `ℝ³`

The upper bound for the cone `K₁ ∨ (K₃ ⊔ K₃)` (`coneTwoTrianglesGraph`, triangles `012` and
`345`, hub `6`): an explicit unit-distance representation in `ℝ³`. The triangles sit on two
opposite triangle faces of the cuboctahedron — the integer points `(1, 1, 0)`, `(0, 1, 1)`,
`(1, 0, 1)` and their negatives `(-1, -1, 0)`, `(0, -1, -1)`, `(-1, 0, -1)` — with the hub at
their common centre `(0, 0, 0)`, all scaled by `1/√2`. Every triangle edge and every spoke to
the hub has integer squared distance `2`, so each scaled edge has length one.
-/

namespace SimpleGraph

noncomputable section

/-! ### Two opposite cuboctahedron triangles and their centre, scaled by `1/√2` -/

private def coordX : Fin 7 → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => -1
  | 4 => 0
  | 5 => -1
  | 6 => 0

private def coordY : Fin 7 → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 0
  | 3 => -1
  | 4 => -1
  | 5 => 0
  | 6 => 0

private def coordZ : Fin 7 → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 0
  | 4 => -1
  | 5 => -1
  | 6 => 0

private def pt (i : Fin 7) : EuclideanSpace ℝ (Fin 3) :=
  !₂[coordX i / Real.sqrt 2, coordY i / Real.sqrt 2, coordZ i / Real.sqrt 2]

/-- Scaling by `1/√2` halves squared distances. -/
private lemma sq_scaled (a b : ℝ) :
    (a / Real.sqrt 2 - b / Real.sqrt 2) ^ 2 = (a - b) ^ 2 / 2 := by
  have h : a / Real.sqrt 2 - b / Real.sqrt 2 = (a - b) / Real.sqrt 2 := by ring
  rw [h, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma dist_sq (u v : Fin 7) :
    Dist.dist (pt u) (pt v) ^ 2 =
      ((coordX u - coordX v) ^ 2 + (coordY u - coordY v) ^ 2 +
        (coordZ u - coordZ v) ^ 2) / 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
  simp [pt, Real.dist_eq, sq_abs, sq_scaled]
  ring

/-- The shared scaling fact: integer squared distance `2` means scaled distance `1`. -/
private lemma dist_of_sq {u v : Fin 7}
    (h : (coordX u - coordX v) ^ 2 + (coordY u - coordY v) ^ 2 +
      (coordZ u - coordZ v) ^ 2 = 2) :
    Dist.dist (pt u) (pt v) = 1 := by
  have hsq : Dist.dist (pt u) (pt v) ^ 2 = 1 := by rw [dist_sq, h]; norm_num
  rw [← Real.sqrt_sq (dist_nonneg (x := pt u) (y := pt v)), hsq, Real.sqrt_one]

private lemma sq_comm (u v : Fin 7) :
    (coordX u - coordX v) ^ 2 + (coordY u - coordY v) ^ 2 + (coordZ u - coordZ v) ^ 2 =
      (coordX v - coordX u) ^ 2 + (coordY v - coordY u) ^ 2 + (coordZ v - coordZ u) ^ 2 := by
  ring

private lemma sq_01 :
    (coordX 0 - coordX 1) ^ 2 + (coordY 0 - coordY 1) ^ 2 + (coordZ 0 - coordZ 1) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_02 :
    (coordX 0 - coordX 2) ^ 2 + (coordY 0 - coordY 2) ^ 2 + (coordZ 0 - coordZ 2) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_12 :
    (coordX 1 - coordX 2) ^ 2 + (coordY 1 - coordY 2) ^ 2 + (coordZ 1 - coordZ 2) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_34 :
    (coordX 3 - coordX 4) ^ 2 + (coordY 3 - coordY 4) ^ 2 + (coordZ 3 - coordZ 4) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_35 :
    (coordX 3 - coordX 5) ^ 2 + (coordY 3 - coordY 5) ^ 2 + (coordZ 3 - coordZ 5) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_45 :
    (coordX 4 - coordX 5) ^ 2 + (coordY 4 - coordY 5) ^ 2 + (coordZ 4 - coordZ 5) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_06 :
    (coordX 0 - coordX 6) ^ 2 + (coordY 0 - coordY 6) ^ 2 + (coordZ 0 - coordZ 6) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_16 :
    (coordX 1 - coordX 6) ^ 2 + (coordY 1 - coordY 6) ^ 2 + (coordZ 1 - coordZ 6) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_26 :
    (coordX 2 - coordX 6) ^ 2 + (coordY 2 - coordY 6) ^ 2 + (coordZ 2 - coordZ 6) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_36 :
    (coordX 3 - coordX 6) ^ 2 + (coordY 3 - coordY 6) ^ 2 + (coordZ 3 - coordZ 6) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_46 :
    (coordX 4 - coordX 6) ^ 2 + (coordY 4 - coordY 6) ^ 2 + (coordZ 4 - coordZ 6) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_56 :
    (coordX 5 - coordX 6) ^ 2 + (coordY 5 - coordY 6) ^ 2 + (coordZ 5 - coordZ 6) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma pt_injective : Function.Injective pt := by
  intro u v h
  have hx : coordX u = coordX v := by
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 0) h
  have hy : coordY u = coordY v := by
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 1) h
  have hz : coordZ u = coordZ v := by
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 2) h
  have hxyz : coordX u = coordX v ∧ coordY u = coordY v ∧ coordZ u = coordZ v :=
    ⟨hx, hy, hz⟩
  fin_cases u <;> fin_cases v <;> simp_all <;>
    norm_num [coordX, coordY, coordZ] at *

@[expose] public section

/-- **Upper bound** for the dimension of the cone over two triangles: `coneTwoTrianglesGraph`
admits a unit-distance representation in `ℝ³`.

The triangles `012` and `345` sit on two opposite triangle faces of the cuboctahedron and the
hub `6` at their common centre; the integer squared distance of every triangle edge and spoke
is `2`, so scaling by `1/√2` puts each edge at distance one. -/
theorem unitDistEmbeddable_coneTwoTrianglesGraph :
    coneTwoTrianglesGraph.UnitDistEmbeddable 3 := by
  refine ⟨pt, pt_injective, ?_⟩
  intro u v huv
  -- `fin_cases` walks pairs `(u, v)` in lexicographic order.
  fin_cases u <;> fin_cases v
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_01
  · exact dist_of_sq sq_02
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_06
  · exact dist_of_sq ((sq_comm 0 1).symm.trans sq_01)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_12
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_16
  · exact dist_of_sq ((sq_comm 0 2).symm.trans sq_02)
  · exact dist_of_sq ((sq_comm 1 2).symm.trans sq_12)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_26
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_34
  · exact dist_of_sq sq_35
  · exact dist_of_sq sq_36
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq ((sq_comm 3 4).symm.trans sq_34)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_45
  · exact dist_of_sq sq_46
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq ((sq_comm 3 5).symm.trans sq_35)
  · exact dist_of_sq ((sq_comm 4 5).symm.trans sq_45)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_56
  · exact dist_of_sq ((sq_comm 0 6).symm.trans sq_06)
  · exact dist_of_sq ((sq_comm 1 6).symm.trans sq_16)
  · exact dist_of_sq ((sq_comm 2 6).symm.trans sq_26)
  · exact dist_of_sq ((sq_comm 3 6).symm.trans sq_36)
  · exact dist_of_sq ((sq_comm 4 6).symm.trans sq_46)
  · exact dist_of_sq ((sq_comm 5 6).symm.trans sq_56)
  · exact absurd huv (by decide)

end

end

end SimpleGraph

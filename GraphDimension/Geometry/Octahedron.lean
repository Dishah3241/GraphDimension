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
# The octahedron `K₂,₂,₂` in `ℝ³`

The upper bound for the octahedron `octahedronGraph` (`K₂,₂,₂` on `Fin 6`, opposite pairs
`01`, `23`, `45`): an explicit unit-distance representation in `ℝ³`. The vertices sit on the
coordinate axes — the integer points `(1, 0, 0)`, `(-1, 0, 0)`, `(0, 1, 0)`, `(0, -1, 0)`,
`(0, 0, 1)`, `(0, 0, -1)`, scaled by `1/√2`. Non-opposite pairs have integer squared distance
`2`, so each scaled edge has length one; each opposite pair is the antipodal pair of an axis
of the cuboctahedron's vertex figure.
-/

namespace SimpleGraph

noncomputable section

/-! ### The regular octahedron on the coordinate axes, scaled by `1/√2` -/

private def coordX : Fin 6 → ℝ
  | 0 => 1
  | 1 => -1
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0

private def coordY : Fin 6 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => -1
  | 4 => 0
  | 5 => 0

private def coordZ : Fin 6 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | 5 => -1

private def pt (i : Fin 6) : EuclideanSpace ℝ (Fin 3) :=
  !₂[coordX i / Real.sqrt 2, coordY i / Real.sqrt 2, coordZ i / Real.sqrt 2]

/-- Scaling by `1/√2` halves squared distances. -/
private lemma sq_scaled (a b : ℝ) :
    (a / Real.sqrt 2 - b / Real.sqrt 2) ^ 2 = (a - b) ^ 2 / 2 := by
  have h : a / Real.sqrt 2 - b / Real.sqrt 2 = (a - b) / Real.sqrt 2 := by ring
  rw [h, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma dist_sq (u v : Fin 6) :
    Dist.dist (pt u) (pt v) ^ 2 =
      ((coordX u - coordX v) ^ 2 + (coordY u - coordY v) ^ 2 +
        (coordZ u - coordZ v) ^ 2) / 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
  simp [pt, Real.dist_eq, sq_abs, sq_scaled]
  ring

/-- The shared scaling fact: integer squared distance `2` means scaled distance `1`. -/
private lemma dist_of_sq {u v : Fin 6}
    (h : (coordX u - coordX v) ^ 2 + (coordY u - coordY v) ^ 2 +
      (coordZ u - coordZ v) ^ 2 = 2) :
    Dist.dist (pt u) (pt v) = 1 := by
  have hsq : Dist.dist (pt u) (pt v) ^ 2 = 1 := by rw [dist_sq, h]; norm_num
  rw [← Real.sqrt_sq (dist_nonneg (x := pt u) (y := pt v)), hsq, Real.sqrt_one]

private lemma sq_comm (u v : Fin 6) :
    (coordX u - coordX v) ^ 2 + (coordY u - coordY v) ^ 2 + (coordZ u - coordZ v) ^ 2 =
      (coordX v - coordX u) ^ 2 + (coordY v - coordY u) ^ 2 + (coordZ v - coordZ u) ^ 2 := by
  ring

private lemma sq_02 :
    (coordX 0 - coordX 2) ^ 2 + (coordY 0 - coordY 2) ^ 2 + (coordZ 0 - coordZ 2) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_03 :
    (coordX 0 - coordX 3) ^ 2 + (coordY 0 - coordY 3) ^ 2 + (coordZ 0 - coordZ 3) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_04 :
    (coordX 0 - coordX 4) ^ 2 + (coordY 0 - coordY 4) ^ 2 + (coordZ 0 - coordZ 4) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_05 :
    (coordX 0 - coordX 5) ^ 2 + (coordY 0 - coordY 5) ^ 2 + (coordZ 0 - coordZ 5) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_12 :
    (coordX 1 - coordX 2) ^ 2 + (coordY 1 - coordY 2) ^ 2 + (coordZ 1 - coordZ 2) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_13 :
    (coordX 1 - coordX 3) ^ 2 + (coordY 1 - coordY 3) ^ 2 + (coordZ 1 - coordZ 3) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_14 :
    (coordX 1 - coordX 4) ^ 2 + (coordY 1 - coordY 4) ^ 2 + (coordZ 1 - coordZ 4) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_15 :
    (coordX 1 - coordX 5) ^ 2 + (coordY 1 - coordY 5) ^ 2 + (coordZ 1 - coordZ 5) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_24 :
    (coordX 2 - coordX 4) ^ 2 + (coordY 2 - coordY 4) ^ 2 + (coordZ 2 - coordZ 4) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_25 :
    (coordX 2 - coordX 5) ^ 2 + (coordY 2 - coordY 5) ^ 2 + (coordZ 2 - coordZ 5) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_34 :
    (coordX 3 - coordX 4) ^ 2 + (coordY 3 - coordY 4) ^ 2 + (coordZ 3 - coordZ 4) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma sq_35 :
    (coordX 3 - coordX 5) ^ 2 + (coordY 3 - coordY 5) ^ 2 + (coordZ 3 - coordZ 5) ^ 2 = 2 := by
  simp only [coordX, coordY, coordZ]; norm_num

private lemma pt_injective : Function.Injective pt := by
  intro u v h
  have hx : coordX u = coordX v := by
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 0) h
  have hy : coordY u = coordY v := by
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 1) h
  have hz : coordZ u = coordZ v := by
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 2) h
  fin_cases u <;> fin_cases v <;> simp_all [coordX, coordY, coordZ] <;> norm_num at *

@[expose] public section

/-- **Upper bound** for the dimension of the octahedron `K₂,₂,₂`: `octahedronGraph` admits a
unit-distance representation in `ℝ³`.

The vertices sit at `±1/√2` on the three coordinate axes, so opposite pairs `01`, `23`, `45`
are antipodal and every other pair has squared distance one. -/
theorem unitDistEmbeddable_octahedronGraph :
    octahedronGraph.UnitDistEmbeddable 3 := by
  refine ⟨pt, pt_injective, ?_⟩
  intro u v huv
  -- `fin_cases` walks pairs `(u, v)` in lexicographic order.
  fin_cases u <;> fin_cases v
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_02
  · exact dist_of_sq sq_03
  · exact dist_of_sq sq_04
  · exact dist_of_sq sq_05
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_12
  · exact dist_of_sq sq_13
  · exact dist_of_sq sq_14
  · exact dist_of_sq sq_15
  · exact dist_of_sq ((sq_comm 0 2).symm.trans sq_02)
  · exact dist_of_sq ((sq_comm 1 2).symm.trans sq_12)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_24
  · exact dist_of_sq sq_25
  · exact dist_of_sq ((sq_comm 0 3).symm.trans sq_03)
  · exact dist_of_sq ((sq_comm 1 3).symm.trans sq_13)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq sq_34
  · exact dist_of_sq sq_35
  · exact dist_of_sq ((sq_comm 0 4).symm.trans sq_04)
  · exact dist_of_sq ((sq_comm 1 4).symm.trans sq_14)
  · exact dist_of_sq ((sq_comm 2 4).symm.trans sq_24)
  · exact dist_of_sq ((sq_comm 3 4).symm.trans sq_34)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)
  · exact dist_of_sq ((sq_comm 0 5).symm.trans sq_05)
  · exact dist_of_sq ((sq_comm 1 5).symm.trans sq_15)
  · exact dist_of_sq ((sq_comm 2 5).symm.trans sq_25)
  · exact dist_of_sq ((sq_comm 3 5).symm.trans sq_35)
  · exact absurd huv (by decide)
  · exact absurd huv (by decide)

end

end

end SimpleGraph

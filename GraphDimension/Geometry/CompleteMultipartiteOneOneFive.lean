/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic
public import GraphDimension.Combinatorics.SimpleGraph.SmallGraphsThree

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The complete multipartite graph `K₁,₁,₅` in `ℝ³`

An explicit unit-distance placement of `SimpleGraph.completeMultipartiteGraphOneOneFive` in
`ℝ³`: the graph on `Fin 7` whose singleton parts are `0` and `1` and whose large part is the
independent set `2, …, 6`.

Place the two singleton vertices at the poles `(0, 0, ±1/2)`, one unit apart, and the five
remaining vertices on the equator circle of radius `√3/2` using the rational circle
parametrization `t ↦ ((1 - t²)/(1 + t²), 2t/(1 + t²))` for `t = 0, …, 4`: for `t = k - 2`,

```text
k ↦ (√3/2) · ((1 - t²)/(1 + t²), 2t/(1 + t²), 0)
```

Each equator point has squared distance `(√3/2)² + (1/2)² = 1` from both poles, and the five
equator points are distinct. The design (`2026-09-24-p9-d1-blueprint-design.md` §1, placement
P5) chose the rational parameters to avoid trigonometry.

## References

Frankl, Kupavskii and Swanepoel, FKS Problem 2 at `d = 3` (design
`2026-09-24-p9-d1-blueprint-design.md` §1, placement P5).
-/

namespace SimpleGraph

noncomputable section

private def xCoord : Fin 7 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => Real.sqrt 3 / 2 * 1
  | 3 => Real.sqrt 3 / 2 * 0
  | 4 => Real.sqrt 3 / 2 * (-3 / 5)
  | 5 => Real.sqrt 3 / 2 * (-4 / 5)
  | 6 => Real.sqrt 3 / 2 * (-15 / 17)

private def yCoord : Fin 7 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => Real.sqrt 3 / 2 * 0
  | 3 => Real.sqrt 3 / 2 * 1
  | 4 => Real.sqrt 3 / 2 * (4 / 5)
  | 5 => Real.sqrt 3 / 2 * (3 / 5)
  | 6 => Real.sqrt 3 / 2 * (8 / 17)

private def zCoord : Fin 7 → ℝ
  | 0 => 1 / 2
  | 1 => -1 / 2
  | _ => 0

private def pt (i : Fin 7) : EuclideanSpace ℝ (Fin 3) := !₂[xCoord i, yCoord i, zCoord i]

private lemma dist_sq (u v : Fin 7) :
    Dist.dist (pt u) (pt v) ^ 2 =
      (xCoord u - xCoord v) ^ 2 + (yCoord u - yCoord v) ^ 2 + (zCoord u - zCoord v) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
  simp [pt, Real.dist_eq, sq_abs]

private lemma dist_of_sq {u v : Fin 7}
    (h : (xCoord u - xCoord v) ^ 2 + (yCoord u - yCoord v) ^ 2 +
      (zCoord u - zCoord v) ^ 2 = 1) :
    Dist.dist (pt u) (pt v) = 1 := by
  have hsq : Dist.dist (pt u) (pt v) ^ 2 = 1 := by rw [dist_sq, h]
  rw [← Real.sqrt_sq (dist_nonneg (x := pt u) (y := pt v)), hsq, Real.sqrt_one]

private lemma sq_comm (u v : Fin 7) :
    (xCoord u - xCoord v) ^ 2 + (yCoord u - yCoord v) ^ 2 + (zCoord u - zCoord v) ^ 2 =
      (xCoord v - xCoord u) ^ 2 + (yCoord v - yCoord u) ^ 2 + (zCoord v - zCoord u) ^ 2 := by
  ring

/-- A pole and an equator point `(√3/2) · (a, b, 0)` with `a² + b² = 1` are at squared
distance one from the upper pole `(0, 0, 1/2)`. -/
private lemma pole_rim_sq (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    (0 - Real.sqrt 3 / 2 * a) ^ 2 + (0 - Real.sqrt 3 / 2 * b) ^ 2 + (1 / 2 - 0) ^ 2 = 1 := by
  have h3 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have key : (0 - Real.sqrt 3 / 2 * a) ^ 2 + (0 - Real.sqrt 3 / 2 * b) ^ 2 + (1 / 2 - 0) ^ 2
      = Real.sqrt 3 ^ 2 / 4 * a ^ 2 + Real.sqrt 3 ^ 2 / 4 * b ^ 2 + 1 / 4 := by ring
  rw [key, h3]
  linarith

/-- A pole and an equator point `(√3/2) · (a, b, 0)` with `a² + b² = 1` are at squared
distance one from the lower pole `(0, 0, -1/2)`. -/
private lemma pole_rim_sq' (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    (0 - Real.sqrt 3 / 2 * a) ^ 2 + (0 - Real.sqrt 3 / 2 * b) ^ 2 + (-1 / 2 - 0) ^ 2 = 1 := by
  have h3 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have key : (0 - Real.sqrt 3 / 2 * a) ^ 2 + (0 - Real.sqrt 3 / 2 * b) ^ 2 + (-1 / 2 - 0) ^ 2
      = Real.sqrt 3 ^ 2 / 4 * a ^ 2 + Real.sqrt 3 ^ 2 / 4 * b ^ 2 + 1 / 4 := by ring
  rw [key, h3]
  linarith

private lemma sq_01 :
    (xCoord 0 - xCoord 1) ^ 2 + (yCoord 0 - yCoord 1) ^ 2 + (zCoord 0 - zCoord 1) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  norm_num

private lemma sq_02 :
    (xCoord 0 - xCoord 2) ^ 2 + (yCoord 0 - yCoord 2) ^ 2 + (zCoord 0 - zCoord 2) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  exact pole_rim_sq 1 0 (by norm_num)

private lemma sq_03 :
    (xCoord 0 - xCoord 3) ^ 2 + (yCoord 0 - yCoord 3) ^ 2 + (zCoord 0 - zCoord 3) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  exact pole_rim_sq 0 1 (by norm_num)

private lemma sq_04 :
    (xCoord 0 - xCoord 4) ^ 2 + (yCoord 0 - yCoord 4) ^ 2 + (zCoord 0 - zCoord 4) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  exact pole_rim_sq (-3 / 5) (4 / 5) (by norm_num)

private lemma sq_05 :
    (xCoord 0 - xCoord 5) ^ 2 + (yCoord 0 - yCoord 5) ^ 2 + (zCoord 0 - zCoord 5) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  exact pole_rim_sq (-4 / 5) (3 / 5) (by norm_num)

private lemma sq_06 :
    (xCoord 0 - xCoord 6) ^ 2 + (yCoord 0 - yCoord 6) ^ 2 + (zCoord 0 - zCoord 6) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  exact pole_rim_sq (-15 / 17) (8 / 17) (by norm_num)

private lemma sq_12 :
    (xCoord 1 - xCoord 2) ^ 2 + (yCoord 1 - yCoord 2) ^ 2 + (zCoord 1 - zCoord 2) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  exact pole_rim_sq' 1 0 (by norm_num)

private lemma sq_13 :
    (xCoord 1 - xCoord 3) ^ 2 + (yCoord 1 - yCoord 3) ^ 2 + (zCoord 1 - zCoord 3) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  exact pole_rim_sq' 0 1 (by norm_num)

private lemma sq_14 :
    (xCoord 1 - xCoord 4) ^ 2 + (yCoord 1 - yCoord 4) ^ 2 + (zCoord 1 - zCoord 4) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  exact pole_rim_sq' (-3 / 5) (4 / 5) (by norm_num)

private lemma sq_15 :
    (xCoord 1 - xCoord 5) ^ 2 + (yCoord 1 - yCoord 5) ^ 2 + (zCoord 1 - zCoord 5) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  exact pole_rim_sq' (-4 / 5) (3 / 5) (by norm_num)

private lemma sq_16 :
    (xCoord 1 - xCoord 6) ^ 2 + (yCoord 1 - yCoord 6) ^ 2 + (zCoord 1 - zCoord 6) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  exact pole_rim_sq' (-15 / 17) (8 / 17) (by norm_num)

private lemma pt_injective : Function.Injective pt := by
  intro u v h
  have hx : xCoord u = xCoord v := by
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 0) h
  have hy : yCoord u = yCoord v := by
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 1) h
  have hz : zCoord u = zCoord v := by
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 2) h
  fin_cases u <;> fin_cases v
  · rfl
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hz
  · rfl
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hz
  · rfl
  · norm_num [xCoord, yCoord, zCoord] at hx
  · norm_num [xCoord, yCoord, zCoord] at hy
  · norm_num [xCoord, yCoord, zCoord] at hy
  · norm_num [xCoord, yCoord, zCoord] at hy
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hy
  · rfl
  · norm_num [xCoord, yCoord, zCoord] at hy
  · norm_num [xCoord, yCoord, zCoord] at hy
  · norm_num [xCoord, yCoord, zCoord] at hy
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hy
  · norm_num [xCoord, yCoord, zCoord] at hy
  · rfl
  · norm_num [xCoord, yCoord, zCoord] at hy
  · norm_num [xCoord, yCoord, zCoord] at hy
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hy
  · norm_num [xCoord, yCoord, zCoord] at hy
  · norm_num [xCoord, yCoord, zCoord] at hy
  · rfl
  · norm_num [xCoord, yCoord, zCoord] at hy
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hz
  · norm_num [xCoord, yCoord, zCoord] at hy
  · norm_num [xCoord, yCoord, zCoord] at hy
  · norm_num [xCoord, yCoord, zCoord] at hy
  · norm_num [xCoord, yCoord, zCoord] at hy
  · rfl

@[expose] public section

/-- **Upper bound** for the dimension of `K₁,₁,₅`: the complete multipartite graph with
singleton parts `0`, `1` and independent part `2, …, 6` admits a unit-distance representation
in `ℝ³`.

The singletons sit at the poles `(0, 0, ±1/2)`, one unit apart; the independent part sits on
the equator circle of radius `√3/2` at the rational points `t = 0, …, 4` of the unit circle,
each at squared distance `(√3/2)² + (1/2)² = 1` from both poles. -/
theorem unitDistEmbeddable_completeMultipartiteGraph_one_one_five :
    completeMultipartiteGraphOneOneFive.UnitDistEmbeddable 3 := by
  refine ⟨pt, pt_injective, ?_⟩
  intro u v huv
  -- `fin_cases` walks pairs `(u, v)` in lexicographic order. The edges join each pole to
  -- every other vertex, plus the pole-pole edge `01`.
  fin_cases u <;> fin_cases v
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact dist_of_sq sq_01
  · exact dist_of_sq sq_02
  · exact dist_of_sq sq_03
  · exact dist_of_sq sq_04
  · exact dist_of_sq sq_05
  · exact dist_of_sq sq_06
  · exact dist_of_sq ((sq_comm 0 1).symm.trans sq_01)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact dist_of_sq sq_12
  · exact dist_of_sq sq_13
  · exact dist_of_sq sq_14
  · exact dist_of_sq sq_15
  · exact dist_of_sq sq_16
  · exact dist_of_sq ((sq_comm 0 2).symm.trans sq_02)
  · exact dist_of_sq ((sq_comm 1 2).symm.trans sq_12)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact dist_of_sq ((sq_comm 0 3).symm.trans sq_03)
  · exact dist_of_sq ((sq_comm 1 3).symm.trans sq_13)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact dist_of_sq ((sq_comm 0 4).symm.trans sq_04)
  · exact dist_of_sq ((sq_comm 1 4).symm.trans sq_14)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact dist_of_sq ((sq_comm 0 5).symm.trans sq_05)
  · exact dist_of_sq ((sq_comm 1 5).symm.trans sq_15)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact dist_of_sq ((sq_comm 0 6).symm.trans sq_06)
  · exact dist_of_sq ((sq_comm 1 6).symm.trans sq_16)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)
  · exact absurd huv (by rw [completeMultipartiteGraphOneOneFive_adj_iff]; decide)

end

end

end SimpleGraph

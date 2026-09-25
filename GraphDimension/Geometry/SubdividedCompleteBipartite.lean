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
# The subdivided `K₃,₃` in `ℝ³`

An explicit unit-distance placement of `SimpleGraph.subdividedCompleteBipartiteGraphThreeThree`
in `ℝ³`: the subdivision of `K₃,₃` with parts `0, 1, 2` and `3, 4, 5`, the edge `03` replaced by
the two edges `06` and `63` through the new vertex `6`.

With `s = √3` the seven placed points are

```text
0 ↦ (1/2, s/2, 0)        1 ↦ (1/2, 1/2, 1/√2)   2 ↦ (1/2, 1/2, −1/√2)
3 ↦ (0, 1, 0)            4 ↦ (0, 0, 0)          5 ↦ (1, 0, 0)
6 ↦ (1/4, (2 + s)/4, √(2 + s)/2)
```

The nine cross edges `04 05 13 14 15 23 24 25` have squared length one by direct computation, and
so do the two subdivision edges `06` and `36`, using `(√(2 + √3))² = 2 + √3` and `(√3)² = 3`.
Together with `GraphDimension.Geometry.CompleteBipartite`'s lower bound this says
`dim(subdivided K₃,₃) = 3`: no unit-distance placement of `K₃,₃` in `ℝ³` exists, and subdividing
one edge drops the dimension.

## References

Frankl, Kupavskii and Swanepoel, FKS Problem 2 at `d = 3` (design
`2026-09-24-p9-d1-blueprint-design.md` §1, placement P1). The subdivided `K₃,₃` is one of the six
graphs on at most eleven edges placed in `ℝ³` by that proof.
-/

namespace SimpleGraph

noncomputable section

private def xCoord : Fin 7 → ℝ
  | 0 => 1 / 2
  | 1 => 1 / 2
  | 2 => 1 / 2
  | 3 => 0
  | 4 => 0
  | 5 => 1
  | 6 => 1 / 4

private def yCoord : Fin 7 → ℝ
  | 0 => Real.sqrt 3 / 2
  | 1 => 1 / 2
  | 2 => 1 / 2
  | 3 => 1
  | 4 => 0
  | 5 => 0
  | 6 => (2 + Real.sqrt 3) / 4

private def zCoord : Fin 7 → ℝ
  | 0 => 0
  | 1 => Real.sqrt 2 / 2
  | 2 => -(Real.sqrt 2 / 2)
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => Real.sqrt (2 + Real.sqrt 3) / 2

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

private lemma equil : (1 / 2 : ℝ) ^ 2 + (Real.sqrt 3 / 2) ^ 2 = 1 := by
  rw [div_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  norm_num

private lemma sq_sqrt_two_div_two : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

private lemma sqrt_two_div_two_ne_neg : Real.sqrt 2 / 2 ≠ -(Real.sqrt 2 / 2) := by
  have hsq : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := sq_sqrt_two_div_two
  intro h
  have h0 : (Real.sqrt 2 / 2 : ℝ) = 0 := by linarith
  have h1 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 0 := by rw [h0]; ring
  rw [hsq] at h1
  norm_num at h1

private lemma sq_04 :
    (xCoord 0 - xCoord 4) ^ 2 + (yCoord 0 - yCoord 4) ^ 2 + (zCoord 0 - zCoord 4) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  convert equil using 1
  ring

private lemma sq_05 :
    (xCoord 0 - xCoord 5) ^ 2 + (yCoord 0 - yCoord 5) ^ 2 + (zCoord 0 - zCoord 5) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  convert equil using 1
  ring

private lemma sq_13 :
    (xCoord 1 - xCoord 3) ^ 2 + (yCoord 1 - yCoord 3) ^ 2 + (zCoord 1 - zCoord 3) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  nlinarith [sq_sqrt_two_div_two]

private lemma sq_14 :
    (xCoord 1 - xCoord 4) ^ 2 + (yCoord 1 - yCoord 4) ^ 2 + (zCoord 1 - zCoord 4) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  nlinarith [sq_sqrt_two_div_two]

private lemma sq_15 :
    (xCoord 1 - xCoord 5) ^ 2 + (yCoord 1 - yCoord 5) ^ 2 + (zCoord 1 - zCoord 5) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  nlinarith [sq_sqrt_two_div_two]

private lemma sq_23 :
    (xCoord 2 - xCoord 3) ^ 2 + (yCoord 2 - yCoord 3) ^ 2 + (zCoord 2 - zCoord 3) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  nlinarith [sq_sqrt_two_div_two]

private lemma sq_24 :
    (xCoord 2 - xCoord 4) ^ 2 + (yCoord 2 - yCoord 4) ^ 2 + (zCoord 2 - zCoord 4) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  nlinarith [sq_sqrt_two_div_two]

private lemma sq_25 :
    (xCoord 2 - xCoord 5) ^ 2 + (yCoord 2 - yCoord 5) ^ 2 + (zCoord 2 - zCoord 5) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  nlinarith [sq_sqrt_two_div_two]

private lemma sq_06 :
    (xCoord 0 - xCoord 6) ^ 2 + (yCoord 0 - yCoord 6) ^ 2 + (zCoord 0 - zCoord 6) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  have h3 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : (Real.sqrt (2 + Real.sqrt 3) : ℝ) ^ 2 = 2 + Real.sqrt 3 :=
    Real.sq_sqrt (by positivity)
  nlinarith [h3, hs]

private lemma sq_36 :
    (xCoord 3 - xCoord 6) ^ 2 + (yCoord 3 - yCoord 6) ^ 2 + (zCoord 3 - zCoord 6) ^ 2 = 1 := by
  simp only [xCoord, yCoord, zCoord]
  have h3 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : (Real.sqrt (2 + Real.sqrt 3) : ℝ) ^ 2 = 2 + Real.sqrt 3 :=
    Real.sq_sqrt (by positivity)
  nlinarith [h3, hs]

private lemma pt_injective : Function.Injective pt := by
  intro u v h
  have hx : xCoord u = xCoord v := by
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 0) h
  have hy : yCoord u = yCoord v := by
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 1) h
  have hz : zCoord u = zCoord v := by
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 2) h
  fin_cases u <;> fin_cases v <;>
    simp only [xCoord, yCoord, zCoord] at hx hy hz <;>
    first
      | rfl
      | exact absurd hz sqrt_two_div_two_ne_neg
      | exact absurd hz sqrt_two_div_two_ne_neg.symm
      | norm_num at hx <;> norm_num at hy <;> norm_num at hz

@[expose] public section

/-- **Upper bound** for the dimension of the subdivided `K₃,₃`: the subdivision of `K₃,₃` with
parts `0, 1, 2` and `3, 4, 5` and the edge `03` replaced by `06` and `63` admits a
unit-distance representation in `ℝ³`.

The points `0, 4, 5` and `1, 2, 3` are two unit equilateral triangles, placed so that `0` sits
above the edge `45` and `1`, `2` above and below the midpoint of `34`; the subdivision vertex `6`
completes two unit equilateral triangles `0 4 6` and `3 4 6` sharing the edge `46`. With
`dim K₃,₃ = 4` (`GraphDimension.Geometry.CompleteBipartite`) this is sharp. -/
theorem unitDistEmbeddable_subdividedCompleteBipartiteGraph_three_three :
    subdividedCompleteBipartiteGraphThreeThree.UnitDistEmbeddable 3 := by
  refine ⟨pt, pt_injective, ?_⟩
  intro u v huv
  -- `fin_cases` walks pairs `(u, v)` in lexicographic order. The edges are
  -- `04 05 13 14 15 23 24 25 06 36`.
  fin_cases u <;> fin_cases v
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact dist_of_sq sq_04
  · exact dist_of_sq sq_05
  · exact dist_of_sq sq_06
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact dist_of_sq sq_13
  · exact dist_of_sq sq_14
  · exact dist_of_sq sq_15
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact dist_of_sq sq_23
  · exact dist_of_sq sq_24
  · exact dist_of_sq sq_25
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact dist_of_sq ((sq_comm 1 3).symm.trans sq_13)
  · exact dist_of_sq ((sq_comm 2 3).symm.trans sq_23)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact dist_of_sq sq_36
  · exact dist_of_sq ((sq_comm 0 4).symm.trans sq_04)
  · exact dist_of_sq ((sq_comm 1 4).symm.trans sq_14)
  · exact dist_of_sq ((sq_comm 2 4).symm.trans sq_24)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact dist_of_sq ((sq_comm 0 5).symm.trans sq_05)
  · exact dist_of_sq ((sq_comm 1 5).symm.trans sq_15)
  · exact dist_of_sq ((sq_comm 2 5).symm.trans sq_25)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact dist_of_sq ((sq_comm 0 6).symm.trans sq_06)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact dist_of_sq ((sq_comm 3 6).symm.trans sq_36)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
  · exact absurd huv (by rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]; decide)
end

end

end SimpleGraph

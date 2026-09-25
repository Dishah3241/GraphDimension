/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic
public import Mathlib.Combinatorics.SimpleGraph.Hasse

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The complement of the path `P₆` in `ℝ³`

An explicit unit-distance placement of `(SimpleGraph.pathGraph 6)ᶜ` in `ℝ³`: the complement of
Mathlib's path `0–1–2–3–4–5`, whose ten edges are the pairs `i, j` with `|i - j| ≥ 2`.

With `q` the integer certificate

```text
q₀ = ( -9,   9,  -9)   q₁ = (-15, -15, -15)   q₂ = (  9,   9,   9)
q₃ = (-31,  -1,  -1)   q₄ = (  9,  -9,  -9)    q₅ = ( -9,  -9,   9)
```

the placement sends `i ↦ q_i / (18√2)`. Every edge has integer squared distance `648`, and
`(18√2)² = 648`, so every edge lands at squared length one. The design
(`2026-09-24-p9-d1-blueprint-design.md` §1, placement P3) checked `q` and its distance table in
Lean; this module supplies the real scaling and the `EuclideanSpace` distances.

## References

Frankl, Kupavskii and Swanepoel, FKS Problem 2 at `d = 3` (design
`2026-09-24-p9-d1-blueprint-design.md` §1, placement P3).
-/

namespace SimpleGraph

noncomputable section

private def ix : Fin 6 → ℝ
  | 0 => -9
  | 1 => -15
  | 2 => 9
  | 3 => -31
  | 4 => 9
  | 5 => -9

private def iy : Fin 6 → ℝ
  | 0 => 9
  | 1 => -15
  | 2 => 9
  | 3 => -1
  | 4 => -9
  | 5 => -9

private def iz : Fin 6 → ℝ
  | 0 => -9
  | 1 => -15
  | 2 => 9
  | 3 => -1
  | 4 => -9
  | 5 => 9

/-- The common denominator of the placement. -/
private def den : ℝ := 18 * Real.sqrt 2

private lemma den_pos : (0:ℝ) < den := by
  rw [den]
  positivity

private lemma den_ne_zero : den ≠ 0 := ne_of_gt den_pos

private lemma den_sq : den ^ 2 = 648 := by
  rw [den, mul_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- The reciprocal scale factor: coordinates are `q_i` components times `c`. -/
private def c : ℝ := 1 / den

private lemma c_ne_zero : c ≠ 0 := by
  intro hc
  rw [c] at hc
  exact one_div_ne_zero den_ne_zero hc

private lemma c_sq : c ^ 2 = 1 / 648 := by
  rw [c, div_pow, one_pow, den_sq]

private def pt (i : Fin 6) : EuclideanSpace ℝ (Fin 3) := !₂[ix i * c, iy i * c, iz i * c]

private lemma dist_sq (u v : Fin 6) :
    Dist.dist (pt u) (pt v) ^ 2 =
      c ^ 2 * ((ix u - ix v) ^ 2 + (iy u - iy v) ^ 2 + (iz u - iz v) ^ 2) := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
  simp [pt, Real.dist_eq, sq_abs]
  ring

private lemma dist_of_int_sq {u v : Fin 6}
    (h : (ix u - ix v) ^ 2 + (iy u - iy v) ^ 2 + (iz u - iz v) ^ 2 = 648) :
    Dist.dist (pt u) (pt v) = 1 := by
  have hsq : Dist.dist (pt u) (pt v) ^ 2 = 1 := by
    rw [dist_sq, h, c_sq]
    norm_num
  rw [← Real.sqrt_sq (dist_nonneg (x := pt u) (y := pt v)), hsq, Real.sqrt_one]

private lemma sq_comm (u v : Fin 6) :
    (ix u - ix v) ^ 2 + (iy u - iy v) ^ 2 + (iz u - iz v) ^ 2 =
      (ix v - ix u) ^ 2 + (iy v - iy u) ^ 2 + (iz v - iz u) ^ 2 := by
  ring

private lemma sq_02 :
    (ix 0 - ix 2) ^ 2 + (iy 0 - iy 2) ^ 2 + (iz 0 - iz 2) ^ 2 = 648 := by
  simp only [ix, iy, iz]; norm_num

private lemma sq_03 :
    (ix 0 - ix 3) ^ 2 + (iy 0 - iy 3) ^ 2 + (iz 0 - iz 3) ^ 2 = 648 := by
  simp only [ix, iy, iz]; norm_num

private lemma sq_04 :
    (ix 0 - ix 4) ^ 2 + (iy 0 - iy 4) ^ 2 + (iz 0 - iz 4) ^ 2 = 648 := by
  simp only [ix, iy, iz]; norm_num

private lemma sq_05 :
    (ix 0 - ix 5) ^ 2 + (iy 0 - iy 5) ^ 2 + (iz 0 - iz 5) ^ 2 = 648 := by
  simp only [ix, iy, iz]; norm_num

private lemma sq_13 :
    (ix 1 - ix 3) ^ 2 + (iy 1 - iy 3) ^ 2 + (iz 1 - iz 3) ^ 2 = 648 := by
  simp only [ix, iy, iz]; norm_num

private lemma sq_14 :
    (ix 1 - ix 4) ^ 2 + (iy 1 - iy 4) ^ 2 + (iz 1 - iz 4) ^ 2 = 648 := by
  simp only [ix, iy, iz]; norm_num

private lemma sq_15 :
    (ix 1 - ix 5) ^ 2 + (iy 1 - iy 5) ^ 2 + (iz 1 - iz 5) ^ 2 = 648 := by
  simp only [ix, iy, iz]; norm_num

private lemma sq_24 :
    (ix 2 - ix 4) ^ 2 + (iy 2 - iy 4) ^ 2 + (iz 2 - iz 4) ^ 2 = 648 := by
  simp only [ix, iy, iz]; norm_num

private lemma sq_25 :
    (ix 2 - ix 5) ^ 2 + (iy 2 - iy 5) ^ 2 + (iz 2 - iz 5) ^ 2 = 648 := by
  simp only [ix, iy, iz]; norm_num

private lemma sq_35 :
    (ix 3 - ix 5) ^ 2 + (iy 3 - iy 5) ^ 2 + (iz 3 - iz 5) ^ 2 = 648 := by
  simp only [ix, iy, iz]; norm_num

private lemma pt_injective : Function.Injective pt := by
  intro u v h
  have hx : ix u = ix v := by
    refine mul_right_cancel₀ c_ne_zero ?_
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 0) h
  have hy : iy u = iy v := by
    refine mul_right_cancel₀ c_ne_zero ?_
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 1) h
  have hz : iz u = iz v := by
    refine mul_right_cancel₀ c_ne_zero ?_
    simpa [pt] using congr_arg (fun p : EuclideanSpace ℝ (Fin 3) => p.ofLp 2) h
  fin_cases u <;> fin_cases v
  · rfl
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [iy] at hy; exact absurd hy (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · rfl
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · rfl
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [iy] at hy; exact absurd hy (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · rfl
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [iy] at hy; exact absurd hy (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · rfl
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [iy] at hy; exact absurd hy (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · simp only [ix] at hx; exact absurd hx (by norm_num)
  · rfl

@[expose] public section

/-- **Upper bound** for the dimension of the complement of the path `P₆`: the ten pairs
`i, j` of `Fin 6` with `|i - j| ≥ 2` admit a unit-distance representation in `ℝ³`.

The placement scales the integer certificate `q₀ = (-9, 9, -9), …, q₅ = (-9, -9, 9)` by
`1/(18√2)`: each edge pair has integer squared distance `648 = (18√2)²`. -/
theorem unitDistEmbeddable_compl_pathGraph_six :
    (pathGraph 6)ᶜ.UnitDistEmbeddable 3 := by
  refine ⟨pt, pt_injective, ?_⟩
  intro u v huv
  -- `fin_cases` walks pairs `(u, v)` in lexicographic order. The edges are the pairs with
  -- `|i - j| ≥ 2`; the consecutive pairs are non-edges of the complement.
  fin_cases u <;> fin_cases v
  · exact absurd huv (by rw [SimpleGraph.compl_adj, pathGraph_adj]; decide)
  · exact absurd huv (by rw [SimpleGraph.compl_adj, pathGraph_adj]; decide)
  · exact dist_of_int_sq sq_02
  · exact dist_of_int_sq sq_03
  · exact dist_of_int_sq sq_04
  · exact dist_of_int_sq sq_05
  · exact absurd huv (by rw [SimpleGraph.compl_adj, pathGraph_adj]; decide)
  · exact absurd huv (by rw [SimpleGraph.compl_adj, pathGraph_adj]; decide)
  · exact absurd huv (by rw [SimpleGraph.compl_adj, pathGraph_adj]; decide)
  · exact dist_of_int_sq sq_13
  · exact dist_of_int_sq sq_14
  · exact dist_of_int_sq sq_15
  · exact dist_of_int_sq ((sq_comm 0 2).symm.trans sq_02)
  · exact absurd huv (by rw [SimpleGraph.compl_adj, pathGraph_adj]; decide)
  · exact absurd huv (by rw [SimpleGraph.compl_adj, pathGraph_adj]; decide)
  · exact absurd huv (by rw [SimpleGraph.compl_adj, pathGraph_adj]; decide)
  · exact dist_of_int_sq sq_24
  · exact dist_of_int_sq sq_25
  · exact dist_of_int_sq ((sq_comm 0 3).symm.trans sq_03)
  · exact dist_of_int_sq ((sq_comm 1 3).symm.trans sq_13)
  · exact absurd huv (by rw [SimpleGraph.compl_adj, pathGraph_adj]; decide)
  · exact absurd huv (by rw [SimpleGraph.compl_adj, pathGraph_adj]; decide)
  · exact absurd huv (by rw [SimpleGraph.compl_adj, pathGraph_adj]; decide)
  · exact dist_of_int_sq sq_35
  · exact dist_of_int_sq ((sq_comm 0 4).symm.trans sq_04)
  · exact dist_of_int_sq ((sq_comm 1 4).symm.trans sq_14)
  · exact dist_of_int_sq ((sq_comm 2 4).symm.trans sq_24)
  · exact absurd huv (by rw [SimpleGraph.compl_adj, pathGraph_adj]; decide)
  · exact absurd huv (by rw [SimpleGraph.compl_adj, pathGraph_adj]; decide)
  · exact absurd huv (by rw [SimpleGraph.compl_adj, pathGraph_adj]; decide)
  · exact dist_of_int_sq ((sq_comm 0 5).symm.trans sq_05)
  · exact dist_of_int_sq ((sq_comm 1 5).symm.trans sq_15)
  · exact dist_of_int_sq ((sq_comm 2 5).symm.trans sq_25)
  · exact dist_of_int_sq ((sq_comm 3 5).symm.trans sq_35)
  · exact absurd huv (by rw [SimpleGraph.compl_adj, pathGraph_adj]; decide)
  · exact absurd huv (by rw [SimpleGraph.compl_adj, pathGraph_adj]; decide)

end

end

end SimpleGraph

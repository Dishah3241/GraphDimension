/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.VecNotation

import GraphDimension.Geometry.CompleteBipartiteLowerBound
import GraphDimension.Geometry.FinLe
import GraphDimension.Geometry.UnitDistanceComap
import Mathlib.Order.Bounds.Basic

/-!
# The cocktail-party graphs `K₁,₂,₂,₂` and `K₂,₂,₂,₂` have dimension four

The complete multipartite graphs with part sizes `1, 2, 2, 2` and `2, 2, 2, 2` are `K₇` and `K₈`
with three and four independent edges removed. Both have dimension four.

The upper bound is the cross polytope: with `a = 1/√2`, part `i` sits on its own coordinate axis
at `± a e`, and every pair of vertices from different parts differs on two axes, so their squared
distance is `a² + a² = 1`. Vertices in the same part are antipodal, hence distinct, and the
singleton part of `K₁,₂,₂,₂` sits on the one axis its neighbours leave free.

The lower bound goes through a `K₃,₃`: parts `0` and `1` make one side and parts `2` and `3` the
other, so a placement of either cocktail-party graph in `ℝ³` would restrict to one of `K₃,₃` in
`ℝ³`, which does not exist. Chaffee and Noble reach the same conclusion through the larger
subgraphs `K₃,₄ ⊆ K₁,₂,₂,₂` and `K₄,₄ ⊆ K₂,₂,₂,₂`.

## References

Chaffee and Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J.
Combin. **64(2)** (2016), 327–333, Lemma 9.
-/

namespace SimpleGraph

noncomputable section

/-- The signed axis vector: `a` in coordinate `i` of `ℝ⁴`, zero in the other three coordinates. -/
private def svec (i : Fin 4) (a : ℝ) : EuclideanSpace ℝ (Fin 4) := PiLp.single 2 i a

/-- The axis carrying part `i` of the cross-polytope placement: parts `1, 2, 3` occupy axes
`0, 1, 2`, and part `0` occupies the remaining axis `3`. -/
private def prev (i : Fin 4) : Fin 4 := ![3, 0, 1, 2] i

private theorem prev_inj : Function.Injective prev := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [prev]

/-- The cross-polytope placement: part `i` sits on axis `prev i`, its vertex `j` at `+a` when
`j` is the first vertex of the part and `-a` otherwise. -/
private def cktPt {s : Fin 4 → ℕ} (a : ℝ) (v : Σ i : Fin 4, Fin (s i)) :
    EuclideanSpace ℝ (Fin 4) :=
  svec (prev v.1) (if v.2.val = 0 then a else -a)

/-- The squared coordinate-distance sum for two signed axis vectors on distinct axes: only the
two occupied coordinates contribute, one `a²` and one `b²`. -/
private theorem sq_dist_svec {a b : ℝ} {i j : Fin 4} (h : i ≠ j) :
    ∑ k : Fin 4, dist ((svec i a).ofLp k) ((svec j b).ofLp k) ^ 2 = a ^ 2 + b ^ 2 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [svec, PiLp.single_apply, Fin.sum_univ_four, Real.dist_eq, sq_abs] <;> ring

/-- Two signed axis vectors on distinct axes are at distance one when their entries are the two
legs of a unit right triangle. -/
private theorem dist_svec_of_ne {a b : ℝ} {i j : Fin 4} (h : i ≠ j) (hab : a ^ 2 + b ^ 2 = 1) :
    dist (svec i a) (svec j b) = 1 := by
  rw [EuclideanSpace.dist_eq, sq_dist_svec h, hab]
  exact Real.sqrt_one

/-- Two signed axis vectors with a nonzero entry agree only on the same axis with the same
entry. -/
private theorem svec_eq {a b : ℝ} {i j : Fin 4} (ha : a ≠ 0) (h : svec i a = svec j b) :
    i = j ∧ a = b := by
  have h1 : a = if i = j then b else 0 := by
    have h2 : (svec i a).ofLp i = (svec j b).ofLp i := by rw [h]
    simp only [svec, PiLp.single_eq_same, PiLp.single_apply] at h2
    exact h2
  rcases eq_or_ne i j with rfl | hij
  · rw [ite_eq_left rfl] at h1
    exact ⟨rfl, h1⟩
  · rw [ite_eq_right hij] at h1
    exact absurd h1 ha

/-- Two vertices of either cocktail-party graph are adjacent exactly when they come from
different parts. -/
private theorem adj_iff {s : Fin 4 → ℕ} (v w : Σ i : Fin 4, Fin (s i)) :
    (completeMultipartiteGraph fun i : Fin 4 => Fin (s i)).Adj v w ↔ v.1 ≠ w.1 := by
  simp [completeMultipartiteGraph, top_adj]

/-- A part of a cocktail-party graph has at most two vertices, so a vertex other than the first
has value one. -/
private theorem eq_one_of_val_ne_zero {n : ℕ} (hn : n ≤ 2) {j : Fin n} (hj : j.val ≠ 0) :
    j.val = 1 := by
  have := j.isLt
  omega

/-- The cross-polytope placement is injective: the axis recovers the part, the sign recovers
whether the vertex is the first of its part, and a part has at most two vertices. -/
private theorem cktPt_injective {s : Fin 4 → ℕ} (hs : ∀ i : Fin 4, s i ≤ 2) {a : ℝ}
    (ha : a ≠ 0) : Function.Injective (cktPt (s := s) a) := by
  intro v w hvw
  obtain ⟨i, j⟩ := v
  obtain ⟨k, l⟩ := w
  simp only [cktPt] at hvw
  have hne : (if j.val = 0 then a else -a) ≠ 0 := by
    by_cases hj : j.val = 0
    · rw [ite_eq_left hj]; exact ha
    · rw [ite_eq_right hj]
      intro h0
      exact ha (by linarith)
  obtain ⟨hik, hsign⟩ := svec_eq hne hvw
  have hij : i = k := prev_inj hik
  subst hij
  by_cases hj0 : j.val = 0
  · by_cases hl0 : l.val = 0
    · have hjl : j.val = l.val := by rw [hj0, hl0]
      exact congrArg (Sigma.mk i) (Fin.eq_of_val_eq hjl)
    · rw [hj0, ite_eq_left rfl, ite_eq_right hl0] at hsign
      have h0 : a = 0 := by linarith
      exact absurd h0 ha
  · by_cases hl0 : l.val = 0
    · rw [ite_eq_right hj0, ite_eq_left hl0] at hsign
      have h0 : a = 0 := by linarith
      exact absurd h0 ha
    · have hjl : j.val = l.val :=
        by rw [eq_one_of_val_ne_zero (hs i) hj0, eq_one_of_val_ne_zero (hs i) hl0]
      exact congrArg (Sigma.mk i) (Fin.eq_of_val_eq hjl)

/-- Vertices from different parts sit on distinct axes at entries `±a` with `a² = 1/2`, so
their distance is one, whatever the signs. -/
private theorem dist_adj {s : Fin 4 → ℕ} {a : ℝ} (ha2 : a ^ 2 = 1 / 2)
    {v w : Σ i : Fin 4, Fin (s i)} (hvw : v.1 ≠ w.1) :
    dist (cktPt a v) (cktPt a w) = 1 := by
  have hv : cktPt a v = svec (prev v.1) (if v.2.val = 0 then a else -a) := rfl
  have hw : cktPt a w = svec (prev w.1) (if w.2.val = 0 then a else -a) := rfl
  rw [hv, hw]
  refine dist_svec_of_ne (prev_inj.ne hvw) ?_
  by_cases hj : v.2.val = 0 <;> by_cases hl : w.2.val = 0
  · rw [ite_eq_left hj, ite_eq_left hl, ha2]
    linarith
  · rw [ite_eq_left hj, ite_eq_right hl]
    have h : (-a) ^ 2 = a ^ 2 := by ring
    rw [h, ha2]
    linarith
  · rw [ite_eq_right hj, ite_eq_left hl]
    have h : (-a) ^ 2 = a ^ 2 := by ring
    rw [h, ha2]
    linarith
  · rw [ite_eq_right hj, ite_eq_right hl]
    have h : (-a) ^ 2 = a ^ 2 := by ring
    rw [h, ha2]
    linarith

/-- Every part of a cocktail-party graph has at most two vertices, so the cross polytope
represents it in `ℝ⁴`. -/
private theorem unitDistEmbeddable_of_parts_le_two {s : Fin 4 → ℕ} (hs : ∀ i : Fin 4, s i ≤ 2) :
    (completeMultipartiteGraph fun i : Fin 4 => Fin (s i)).UnitDistEmbeddable 4 := by
  obtain ⟨a, ha2, ha0⟩ : ∃ a : ℝ, a ^ 2 = 1 / 2 ∧ a ≠ 0 :=
    ⟨1 / Real.sqrt 2, by rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)], by positivity⟩
  refine ⟨cktPt a, cktPt_injective hs ha0, fun v w hvw => dist_adj ha2 ((adj_iff v w).mp hvw)⟩

/-- The six vertices spanning a `K₃,₃` in either cocktail-party graph: parts `0` and `1`
contribute all their vertices to one side, parts `2` and `3` all of theirs to the other. -/
private def k33Map {s : Fin 4 → ℕ} (hs0 : 1 ≤ s 0) (hs : ∀ i : Fin 4, 1 ≤ i → s i = 2) :
    Fin 3 ⊕ Fin 3 → Σ i : Fin 4, Fin (s i) := fun v =>
  match v with
  | Sum.inl 0 => ⟨(0 : Fin 4), ⟨0, by omega⟩⟩
  | Sum.inl 1 => ⟨1, ⟨0, by have := hs 1 (by decide); omega⟩⟩
  | Sum.inl 2 => ⟨1, ⟨1, by have := hs 1 (by decide); omega⟩⟩
  | Sum.inr 0 => ⟨2, ⟨0, by have := hs 2 (by decide); omega⟩⟩
  | Sum.inr 1 => ⟨2, ⟨1, by have := hs 2 (by decide); omega⟩⟩
  | Sum.inr 2 => ⟨3, ⟨0, by have := hs 3 (by decide); omega⟩⟩

private theorem k33Map_injective {s : Fin 4 → ℕ} (hs0 : 1 ≤ s 0)
    (hs : ∀ i : Fin 4, 1 ≤ i → s i = 2) : Function.Injective (k33Map hs0 hs) := by
  intro u v huv
  rcases u with k | k <;> rcases v with l | l
  · fin_cases k <;> fin_cases l <;> simp_all [k33Map]
  · exact absurd (congrArg (fun w : Σ i : Fin 4, Fin (s i) => w.1) huv) (by
      fin_cases k <;> fin_cases l <;> simp [k33Map])
  · exact absurd (congrArg (fun w : Σ i : Fin 4, Fin (s i) => w.1) huv) (by
      fin_cases k <;> fin_cases l <;> simp [k33Map])
  · fin_cases k <;> fin_cases l <;> simp_all [k33Map]

/-- The `K₃,₃` inside either cocktail-party graph: its left side spans parts `0` and `1`, its
right side parts `2` and `3`. -/
private def k33Hom {s : Fin 4 → ℕ} (hs0 : 1 ≤ s 0) (hs : ∀ i : Fin 4, 1 ≤ i → s i = 2) :
    completeBipartiteGraph (Fin 3) (Fin 3) →g
      completeMultipartiteGraph (fun i : Fin 4 => Fin (s i)) where
  toFun := k33Map hs0 hs
  map_rel' := by
    intro u v huv
    rcases u with k | k <;> rcases v with l | l
    · simp [completeBipartiteGraph] at huv
    · refine (adj_iff _ _).mpr ?_
      fin_cases k <;> fin_cases l <;> simp [k33Map]
    · refine (adj_iff _ _).mpr ?_
      fin_cases k <;> fin_cases l <;> simp [k33Map]
    · simp [completeBipartiteGraph] at huv

/-- Neither cocktail-party graph has a unit-distance representation in `ℝᵐ` for `m ≤ 3`: the
`K₃,₃` inside it would have one too, and `K₃,₃` does not. -/
private theorem not_unitDistEmbeddable_le_three {s : Fin 4 → ℕ} (hs0 : 1 ≤ s 0)
    (hs : ∀ i : Fin 4, 1 ≤ i → s i = 2) {m : ℕ} (hm : m ≤ 3)
    (h : (completeMultipartiteGraph fun i : Fin 4 => Fin (s i)).UnitDistEmbeddable m) : False :=
  not_unitDistEmbeddable_completeBipartiteGraph_three_three
    (UnitDistEmbeddable.comap (k33Hom hs0 hs) (k33Map_injective hs0 hs) (h.mono hm))

@[expose] public section

/-- **Upper bound** for the dimension of `K₁,₂,₂,₂`: the seven vertices sit at
`(±a, 0, 0, 0)`, `(0, ±a, 0, 0)`, `(0, 0, ±a, 0)` and `(0, 0, 0, a)` with `a = 1/√2`
(Chaffee–Noble Lemma 9). Two vertices from different parts differ on two coordinate axes, so
their squared distance is `a² + a² = 1`; the two vertices of a two-point part are antipodal. -/
theorem unitDistEmbeddable_completeMultipartiteGraph_one_two_two_two :
    (completeMultipartiteGraph fun i : Fin 4 => Fin (![1, 2, 2, 2] i)).UnitDistEmbeddable 4 :=
  unitDistEmbeddable_of_parts_le_two (s := ![1, 2, 2, 2])
    (by intro i; fin_cases i <;> simp)

/-- **Upper bound** for the dimension of `K₂,₂,₂,₂`: the eight vertices of the cross polytope
sit at `(±a, 0, 0, 0)`, `(0, ±a, 0, 0)`, `(0, 0, ±a, 0)` and `(0, 0, 0, ±a)` with `a = 1/√2`
(Chaffee–Noble Lemma 9). Two vertices from different parts differ on two coordinate axes, so
their squared distance is `a² + a² = 1`; antipodal vertices share a part. -/
theorem unitDistEmbeddable_completeMultipartiteGraph_two_two_two_two :
    (completeMultipartiteGraph fun i : Fin 4 => Fin (![2, 2, 2, 2] i)).UnitDistEmbeddable 4 :=
  unitDistEmbeddable_of_parts_le_two (s := ![2, 2, 2, 2])
    (by intro i; fin_cases i <;> simp)

/-- `K₁,₂,₂,₂` has dimension four: it embeds in `ℝ⁴`, and in no smaller Euclidean space
(Chaffee–Noble Lemma 9). The lower bound goes through the `K₃,₃` spanned by parts `0, 1`
against parts `2, 3`, whose dimension is already four. -/
theorem hasUnitDistDim_completeMultipartiteGraph_one_two_two_two :
    (completeMultipartiteGraph fun i : Fin 4 => Fin (![1, 2, 2, 2] i)).HasUnitDistDim 4 := by
  refine ⟨unitDistEmbeddable_completeMultipartiteGraph_one_two_two_two, ?_⟩
  rw [mem_lowerBounds]
  intro m hm
  have hmle : ¬ m ≤ 3 := fun hle =>
    not_unitDistEmbeddable_le_three (s := ![1, 2, 2, 2]) (by simp)
      (by intro i hi; fin_cases i <;> simp_all) hle hm
  exact Nat.succ_le_of_lt (Nat.gt_of_not_le hmle)

/-- `K₂,₂,₂,₂` has dimension four: it embeds in `ℝ⁴`, and in no smaller Euclidean space
(Chaffee–Noble Lemma 9). The lower bound goes through the `K₃,₃` spanned by parts `0, 1`
against parts `2, 3`, whose dimension is already four. -/
theorem hasUnitDistDim_completeMultipartiteGraph_two_two_two_two :
    (completeMultipartiteGraph fun i : Fin 4 => Fin (![2, 2, 2, 2] i)).HasUnitDistDim 4 := by
  refine ⟨unitDistEmbeddable_completeMultipartiteGraph_two_two_two_two, ?_⟩
  rw [mem_lowerBounds]
  intro m hm
  have hmle : ¬ m ≤ 3 := fun hle =>
    not_unitDistEmbeddable_le_three (s := ![2, 2, 2, 2]) (by simp)
      (by intro i hi; fin_cases i <;> simp_all) hle hm
  exact Nat.succ_le_of_lt (Nat.gt_of_not_le hmle)

end

end

end SimpleGraph

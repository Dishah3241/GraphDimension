/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic

import Mathlib.Algebra.CharZero.Defs
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Separating examples for the dimension definitions

`UnitDistEmbeddable` does not constrain non-edges: a placement may put a non-edge at distance
one. `HasDimension` is leastness, not mere representability: `K₂` embeds in `ℝ⁴` and does not
have dimension four.
-/

namespace SimpleGraph

private lemma dist_single_axis {n : ℕ} (i : Fin n) (a b : ℝ) :
    dist (EuclideanSpace.single i a) (EuclideanSpace.single i b) = |a - b| := by
  rw [PiLp.dist_single_same, Real.dist_eq]

@[expose] public section

/-- `K₂` plus an isolated vertex, placed at `0`, `1` and `2` in `ℝ¹`, has a non-edge at
distance one.

The edge is the segment from `0` to `1`. The pair `{1, 2}` is not an edge, and it is also a unit
segment, so a unit-distance representation does not force non-adjacent vertices apart. -/
theorem UnitDistEmbeddable.exists_unit_nonedge :
    ∃ (V : Type) (G : SimpleGraph V) (n : ℕ) (f : V → EuclideanSpace ℝ (Fin n)),
      G.UnitDistEmbeddable n ∧ Function.Injective f ∧
        (∀ u v, G.Adj u v → dist (f u) (f v) = 1) ∧
          ∃ u v, u ≠ v ∧ ¬ G.Adj u v ∧ dist (f u) (f v) = 1 := by
  have inj : Function.Injective (fun j : Fin 3 =>
      EuclideanSpace.single (0 : Fin 1) (j : ℝ)) := by
    intro u v h
    have hcoord := congr_arg (fun p : EuclideanSpace ℝ (Fin 1) => p 0) h
    simp only [PiLp.single_eq_same] at hcoord
    exact Fin.ext (Nat.cast_inj.mp hcoord)
  let f : Fin 3 → EuclideanSpace ℝ (Fin 1) := fun j => EuclideanSpace.single 0 (j : ℝ)
  refine ⟨Fin 3, fromEdgeSet {s(0, 1)}, 1, f, ⟨f, inj, ?_⟩, inj, ?_, 1, 2, ?_, ?_, ?_⟩
  · intro u v huv
    rw [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at huv
    rcases huv with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩
    · rw [dist_single_axis]
      norm_num
    · rw [dist_single_axis]
      norm_num
  · intro u v huv
    rw [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at huv
    rcases huv with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩
    · rw [dist_single_axis]
      norm_num
    · rw [dist_single_axis]
      norm_num
  · decide
  · rw [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff]
    decide
  · rw [dist_single_axis]
    norm_num

/-- `K₂` has an edge, embeds in `ℝ⁴`, and does not have dimension four.

Placing the two vertices at `0` and `1` on a coordinate axis is a unit-distance representation in
every positive dimension, including `ℝ¹`, so four is not least. -/
theorem completeGraph_fin_two_unitDistEmbeddable_four_not_hasDimension :
    (∃ u v : Fin 2, (completeGraph (Fin 2)).Adj u v) ∧
      (completeGraph (Fin 2)).UnitDistEmbeddable 4 ∧
      ¬ (completeGraph (Fin 2)).HasDimension 4 := by
  have k2 (n : ℕ) (i : Fin n) : (completeGraph (Fin 2)).UnitDistEmbeddable n := by
    refine ⟨fun j => EuclideanSpace.single i (j : ℝ), ?_, ?_⟩
    · intro u v h
      have hcoord := congr_arg (fun p : EuclideanSpace ℝ (Fin n) => p i) h
      simp only [PiLp.single_eq_same] at hcoord
      exact Fin.ext (Nat.cast_inj.mp hcoord)
    · intro u v huv
      fin_cases u <;> fin_cases v <;> rw [top_adj] at huv
      · exact (huv rfl).elim
      · rw [dist_single_axis]
        norm_num
      · rw [dist_single_axis]
        norm_num
      · exact (huv rfl).elim
  refine ⟨⟨0, 1, ?_⟩, k2 4 0, ?_⟩
  · rw [top_adj]
    decide
  · intro h
    have hle : (4 : ℕ) ≤ 1 := (mem_lowerBounds.mp h.2) 1 (k2 1 0)
    exact absurd hle (by decide : ¬ (4 : ℕ) ≤ 1)

end

end SimpleGraph

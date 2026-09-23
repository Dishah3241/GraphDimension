/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.FKS.Counting

import Mathlib.Tactic.FinCases

/-!
# A graph attaining the two-vertex clique bound

At `d = 3`, `K₄` plus two vertices of degree `2`, joined to each other and to one clique vertex
each, has exactly `C(4, 2) + 2 · 3 − 3 = 9` edges. That is the lower bound of
`card_edgeSet_ge_of_two_outside_clique`.
-/

namespace SimpleGraph

open Finset

@[expose] public section

/-- The nine edges: `K₄` on `{0, 1, 2, 3}`, together with `4—0`, `5—1`, and `4—5`. -/
def branchBTwoOutsideEdges : Finset (Sym2 (Fin 6)) :=
  {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(2, 3), s(0, 4), s(1, 5), s(4, 5)}

/-- `K₄` plus two degree-`2` vertices that meet the bound of
`card_edgeSet_ge_of_two_outside_clique` at `d = 3`. -/
def branchBTwoOutside : SimpleGraph (Fin 6) :=
  fromEdgeSet branchBTwoOutsideEdges

instance : DecidableRel branchBTwoOutside.Adj := by
  unfold branchBTwoOutside
  infer_instance

lemma card_branchBTwoOutsideEdges : #branchBTwoOutsideEdges = 9 := by
  decide

lemma not_isDiag_branchBTwoOutsideEdges {e : Sym2 (Fin 6)} (he : e ∈ branchBTwoOutsideEdges) :
    ¬ e.IsDiag := by
  simp only [branchBTwoOutsideEdges, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Sym2.mk_isDiag_iff]

lemma edgeSet_branchBTwoOutside :
    branchBTwoOutside.edgeSet = (branchBTwoOutsideEdges : Set (Sym2 (Fin 6))) := by
  rw [branchBTwoOutside, edgeSet_fromEdgeSet]
  ext e
  rw [Set.mem_sdiff, Sym2.mem_diagSet]
  constructor
  · rintro ⟨he, _⟩
    exact he
  · intro he
    exact ⟨he, not_isDiag_branchBTwoOutsideEdges (mem_coe.mp he)⟩

/-- The four clique vertices. -/
def branchBTwoOutsideClique : Finset (Fin 6) := {0, 1, 2, 3}

lemma branchBTwoOutside_isNClique : branchBTwoOutside.IsNClique 4 branchBTwoOutsideClique := by
  refine ⟨?_, by decide⟩
  intro a ha b hb hab
  rw [branchBTwoOutside, fromEdgeSet_adj]
  refine ⟨?_, hab⟩
  fin_cases a <;> fin_cases b <;> simp_all [branchBTwoOutsideClique, branchBTwoOutsideEdges]

lemma branchBTwoOutside_degree_four : branchBTwoOutside.degree 4 = 2 := by
  have hN : branchBTwoOutside.neighborFinset 4 = {0, 5} := by
    ext i
    fin_cases i <;> rw [mem_neighborFinset, branchBTwoOutside, fromEdgeSet_adj] <;> decide
  simp [degree, hN]

lemma branchBTwoOutside_degree_five : branchBTwoOutside.degree 5 = 2 := by
  have hN : branchBTwoOutside.neighborFinset 5 = {1, 4} := by
    ext i
    fin_cases i <;> rw [mem_neighborFinset, branchBTwoOutside, fromEdgeSet_adj] <;> decide
  simp [degree, hN]

/-- The bound `(d + 1).choose 2 + 2d − 3` at `d = 3` is the number of edges of this graph. -/
theorem card_edgeSet_branchBTwoOutside :
    branchBTwoOutside.edgeSet.ncard = (3 + 1).choose 2 + 2 * 3 - 3 := by
  rw [edgeSet_branchBTwoOutside, Set.ncard_coe_finset, card_branchBTwoOutsideEdges]
  decide

/-- Those nine edges are exactly the lower bound from `card_edgeSet_ge_of_two_outside_clique`. -/
theorem card_edgeSet_ge_of_two_outside_clique_attained :
    (3 + 1).choose 2 + 2 * 3 - 3 ≤ branchBTwoOutside.edgeSet.ncard := by
  have h4 : (4 : Fin 6) ∉ branchBTwoOutsideClique := by decide
  have h5 : (5 : Fin 6) ∉ branchBTwoOutsideClique := by decide
  have hdeg4 : 3 - 1 ≤ branchBTwoOutside.degree 4 := by
    rw [branchBTwoOutside_degree_four]
  have hdeg5 : 3 - 1 ≤ branchBTwoOutside.degree 5 := by
    rw [branchBTwoOutside_degree_five]
  exact card_edgeSet_ge_of_two_outside_clique (by decide) branchBTwoOutside_isNClique
    h4 h5 (by decide) hdeg4 hdeg5

end

end SimpleGraph

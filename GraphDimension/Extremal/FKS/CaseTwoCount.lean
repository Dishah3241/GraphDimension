/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.FKS.Deletion

/-!
# Saturation of the Case 2 edge budget

The almost-complete copy after deleting a nonadjacent pair forces dimension at most four.
The degrees and edge counts are determined, but the vertex count is a separate obligation;
`CaseTwoBoundary` exhibits why it does not follow in dimension three.
-/

@[expose] public section

namespace SimpleGraph

/-- Under the FKS budget, Case 2 is possible only in dimensions three and four, with
both deleted degrees and the remaining edge count at their lower bounds. -/
theorem fks_case_two_degrees {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hd : 3 ≤ d) {v w : V} (hvw : v ≠ w)
    (hnadj : ¬ G.Adj v w) (hdv : d ≤ G.degree v) (hdw : d - 1 ≤ G.degree w)
    (hbudget : G.edgeSet.ncard ≤ fksBudget d)
    (hcopy : completeMinusTriangle (d + 1) ⊑ G.induce {x | x ≠ v ∧ x ≠ w}) :
    d ≤ 4 ∧ G.degree v = d ∧ G.degree w = d - 1 ∧
      (G.induce {x | x ≠ v ∧ x ≠ w}).edgeSet.ncard = (d + 1).choose 2 - 3 ∧
      G.edgeSet.ncard = fksBudget d := by
  classical
  obtain ⟨f⟩ := hcopy
  have hlow := ncard_edgeSet_le_of_copy f
  rw [card_edgeFinset_completeMinusTriangle (by omega)] at hlow
  have hdelete := ncard_edgeSet_induce_ne_pair G hvw hnadj
  have hchoose : 6 ≤ (d + 1).choose 2 :=
    (by decide : 6 ≤ (4 : ℕ).choose 2).trans (Nat.choose_le_choose 2 (by omega))
  have hrec : (d + 2).choose 2 = (d + 1).choose 2 + (d + 1) := by
    rw [show d + 2 = (d + 1) + 1 by omega, Nat.choose_succ_succ,
      Nat.choose_one_right, Nat.add_comm]
  have hd4 : d ≤ 4 := by
    by_contra hn
    rw [fksBudget_of_four_le (by omega)] at hbudget
    omega
  have hbudgetEq : fksBudget d = (d + 1).choose 2 - 3 + d + (d - 1) := by
    interval_cases d <;> decide
  refine ⟨hd4, ?_, ?_, ?_, ?_⟩ <;> omega

end SimpleGraph

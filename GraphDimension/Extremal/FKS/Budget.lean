/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.FKS.Defs

/-!
# Budget inequalities for FKS's induction

The additive bounds avoid truncated subtraction when counting edges removed from a core.
The exceptional budgets in dimensions two and three are included explicitly.
-/

@[expose] public section

namespace SimpleGraph

/-- The FKS budget is strictly below the complete graph on `d + 2` vertices. -/
theorem fksBudget_lt_choose {d : ℕ} (hd : 3 ≤ d) :
    fksBudget d < (d + 2).choose 2 := by
  by_cases h3 : d = 3
  · subst d; decide
  · rw [fksBudget_of_four_le (by omega)]
    have hpos := Nat.choose_pos (show 2 ≤ d + 2 by omega)
    omega

/-- The complete `(d + 1)`-clique leaves room for at most `d` further edges. -/
theorem fksBudget_le_choose_add {d : ℕ} (hd : 3 ≤ d) :
    fksBudget d ≤ (d + 1).choose 2 + d := by
  have h := fksBudget_lt_choose hd
  rw [show d + 2 = (d + 1) + 1 by omega, Nat.choose_succ_succ, Nat.choose_one_right] at h
  change fksBudget d < d + 1 + (d + 1).choose 2 at h
  omega

/-- The extra-vertex and two-clique counts exceed the FKS budget. -/
theorem fksBudget_lt_branch_count {d : ℕ} (hd : 3 ≤ d) :
    fksBudget d < (d + 2).choose 2 + d - 4 := by
  by_cases h3 : d = 3
  · subst d; decide
  · have := fksBudget_lt_choose hd
    omega

/-- Removing at least `d + 2` edges makes the previous-dimensional budget available. -/
theorem fksBudget_le_pred_add {d : ℕ} (hd : 3 ≤ d) :
    fksBudget d ≤ fksBudget (d - 1) + (d + 2) := by
  by_cases hsmall : d ≤ 4
  · interval_cases d <;> decide
  · rw [fksBudget_of_four_le (by omega), fksBudget_of_four_le (by omega)]
    rw [show d - 1 + 2 = d + 1 by omega]
    have hrec : (d + 2).choose 2 = (d + 1).choose 2 + (d + 1) := by
      rw [show d + 2 = (d + 1) + 1 by omega, Nat.choose_succ_succ,
        Nat.choose_one_right, Nat.add_comm]
    have hpos := Nat.choose_pos (show 2 ≤ d + 1 by omega)
    omega

/-- Removing a nonadjacent pair of degrees at least `d` and `d - 1` suffices. -/
theorem fksBudget_le_pred_add_two_mul {d : ℕ} (hd : 3 ≤ d) :
    fksBudget d ≤ fksBudget (d - 1) + (2 * d - 1) := by
  have := fksBudget_le_pred_add hd
  omega

/-- Subtraction form of the universal-vertex budget. -/
theorem fksBudget_sub_add_two_le {d : ℕ} (hd : 3 ≤ d) :
    fksBudget d - (d + 2) ≤ fksBudget (d - 1) := by
  have := fksBudget_le_pred_add hd
  omega

/-- Subtraction form of the two-pole budget. -/
theorem fksBudget_sub_two_mul_le {d : ℕ} (hd : 3 ≤ d) :
    fksBudget d - (2 * d - 1) ≤ fksBudget (d - 1) := by
  have := fksBudget_le_pred_add_two_mul hd
  omega

/-- Subtraction form of the clique-tail budget. -/
theorem fksBudget_sub_choose_le {d : ℕ} (hd : 3 ≤ d) :
    fksBudget d - (d + 1).choose 2 ≤ d := by
  have := fksBudget_le_choose_add hd
  omega

end SimpleGraph

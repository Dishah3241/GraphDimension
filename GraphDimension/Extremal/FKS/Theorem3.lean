/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.FKS.Base
public import GraphDimension.Extremal.FKS.Step

/-!
# Frankl–Kupavskii–Swanepoel, Theorem 3

Induction from `S(2)` gives the simultaneous Euclidean and spherical statement.
For dimension at least four its budget is one less than `C(d + 2, 2)`, giving the
strict edge-count bound of Theorem 3.
-/

@[expose] public section

namespace SimpleGraph

/-- FKS's simultaneous Euclidean and spherical statement in every dimension at least two. -/
theorem fksStatement {d : ℕ} (hd : 2 ≤ d) : FKSStatement d := by
  revert hd
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    by_cases he : d = 2
    · subst d
      exact fksStatement_two
    exact fksStatement_succ (by omega) (ih (d - 1) (by omega) (by omega))

/-- Frankl–Kupavskii–Swanepoel 2020, Theorem 3. -/
theorem unitDistEmbeddable_of_ncard_edgeSet_lt {V : Type} [Finite V] (G : SimpleGraph V)
    {d : ℕ} (hd : 4 ≤ d) (h : G.edgeSet.ncard < (d + 2).choose 2) :
    G.UnitDistEmbeddable d := by
  apply (fksStatement (by omega) V G ?_).1
  rw [fksBudget_of_four_le hd]
  omega

end SimpleGraph

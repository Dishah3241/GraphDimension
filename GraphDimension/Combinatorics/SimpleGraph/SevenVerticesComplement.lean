/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Set.Card

import Mathlib.Data.Sym.NatCard
import Mathlib.Data.Set.Basic

/-!
# The complementary edge count on seven vertices

Leaf T3 of the FKS leaf plan (design `2026-09-24-p9-d1-blueprint-design.md`, §1): a graph and
its complement on seven vertices have `7.choose 2 = 21` edges between them, since every
non-loop pair is an edge of exactly one of `G` and `Gᶜ`. The seven-vertex disjunction reads
this as: one of the two graphs has at most ten edges.
-/

@[expose] public section

namespace SimpleGraph

/-- On seven vertices, a graph and its complement together have `21 = 7.choose 2` edges:
every non-loop pair is an edge of exactly one of `G` and `Gᶜ`. -/
theorem edgeSet_ncard_add_compl_fin_seven (G : SimpleGraph (Fin 7)) :
    G.edgeSet.ncard + Gᶜ.edgeSet.ncard = 21 := by
  have hunion : (G.edgeSet ∪ Gᶜ.edgeSet : Set (Sym2 (Fin 7))) =
      (Sym2.diagSetᶜ : Set (Sym2 (Fin 7))) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ v w =>
      constructor
      · intro h
        rcases Set.mem_union s(v, w) G.edgeSet Gᶜ.edgeSet |>.mp h with h | h
        · exact edgeSet_subset_compl_diagSet G h
        · exact edgeSet_subset_compl_diagSet Gᶜ h
      · intro h
        simp only [Set.mem_union, mem_edgeSet, compl_adj]
        simp only [Set.mem_compl_iff, Sym2.mem_diagSet, Sym2.mk_isDiag_iff] at h
        by_cases hG : G.Adj v w
        · exact Or.inl hG
        · exact Or.inr ⟨h, hG⟩
  have hdisj : Disjoint G.edgeSet Gᶜ.edgeSet := by
    rw [disjoint_edgeSet]
    exact disjoint_iff_inf_le.mpr (by rw [inf_compl_eq_bot])
  rw [← Set.ncard_union_eq hdisj, hunion, Sym2.ncard_diagSet_compl]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

end SimpleGraph

/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.FKS.BranchA
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Edge budgets after deleting vertices

These identities count the edges removed in the one-pole and two-pole branches of FKS.
-/

@[expose] public section

namespace SimpleGraph

open Finset

/-- Deleting a vertex removes precisely its degree many edges. -/
theorem ncard_edgeSet_induce_ne {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    (G.induce {x | x ≠ v}).edgeSet.ncard = G.edgeSet.ncard - G.degree v := by
  classical
  have h := G.card_edgeFinset_induce_compl_singleton v
  rw [G.card_edgeFinset_deleteIncidenceSet] at h
  have hset : ({v}ᶜ : Set V) = {x | x ≠ v} := by ext; simp
  simp only [edgeFinset_card, Set.fintypeCard_eq_ncard] at h
  rwa [hset] at h

/-- For distinct nonadjacent vertices the removed stars are disjoint. -/
theorem ncard_edgeSet_induce_ne_pair {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v w : V} (hvw : v ≠ w) (hnadj : ¬ G.Adj v w) :
    (G.induce {x | x ≠ v ∧ x ≠ w}).edgeSet.ncard =
      G.edgeSet.ncard - G.degree v - G.degree w := by
  classical
  let H := G.induce {x | x ≠ v}
  let w' : {x : V // x ≠ v} := ⟨w, hvw.symm⟩
  have hdeg : H.degree w' = G.degree w := by
    apply degree_induce_of_neighborSet_subset
    intro x hx
    exact fun he => hnadj (he ▸ hx.symm)
  let J := H.induce {x | x ≠ w'}
  let L := G.induce {x | x ≠ v ∧ x ≠ w}
  let f : J.Copy L :=
    { toHom :=
        { toFun := fun x => ⟨x.val.val, x.val.property,
            fun he => x.property (Subtype.ext he)⟩
          map_rel' := fun h => h }
      injective' := fun x y h => Subtype.ext (Subtype.ext
        (congrArg (fun z : {x : V // x ≠ v ∧ x ≠ w} => z.val) h)) }
  let g : L.Copy J :=
    { toHom :=
        { toFun := fun x => ⟨⟨x.val, x.property.1⟩,
            fun he => x.property.2 (congrArg Subtype.val he)⟩
          map_rel' := fun h => h }
      injective' := fun x y h => Subtype.ext (congrArg (fun z => z.val.val) h) }
  have heq : L.edgeSet.ncard = J.edgeSet.ncard :=
    Nat.le_antisymm (ncard_edgeSet_le_of_copy g) (ncard_edgeSet_le_of_copy f)
  have hJ := ncard_edgeSet_induce_ne H w'
  rw [hdeg] at hJ
  change J.edgeSet.ncard = H.edgeSet.ncard - G.degree w at hJ
  have hH := ncard_edgeSet_induce_ne G v
  change H.edgeSet.ncard = G.edgeSet.ncard - G.degree v at hH
  exact heq.trans (hJ.trans (congrArg (fun n => n - G.degree w) hH))

end SimpleGraph

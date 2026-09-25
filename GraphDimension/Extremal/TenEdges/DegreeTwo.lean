/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Data.Fintype.Card

import GraphDimension.Combinatorics.SimpleGraph.SubdividedCompleteBipartite
import GraphDimension.Extremal.EightEdges
import GraphDimension.Extremal.NineEdges
import GraphDimension.Geometry.Reattach
import GraphDimension.Geometry.SubdividedCompleteBipartite
import GraphDimension.Geometry.UnitDistanceComap
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith

/-!
# A degree-two vertex is no obstruction in `ℝ³`

A graph on at most seven vertices with at most ten edges and no `K₃,₃` copy places in `ℝ³`
as soon as it has a vertex of degree two. Write `G' = G.induce {x | x ≠ v}` for the graph
without the vertex `v`, whose two neighbours are `a` and `b`, and complete `G'` by the edge
`ab`: the completion `C = G' ⊔ fromEdgeSet {s(a,b)}` has at most nine edges
(`edgeSet_ncard_completion_le`).

If `a` and `b` are adjacent, `G'` has at most eight edges and places by the eight-edge
theorem; otherwise `C` has at most nine edges. If `C` places, its placement already puts
`a` and `b` one apart, so `v` is reattached by
`UnitDistEmbeddable.extend_degree_le_two_fin_three`. If it does not place, the nine-edge
theorem gives a `K₃,₃` copy in `C`, the completion classification
`nonempty_iso_subdividedCompleteBipartiteGraph_of_completion` identifies `G` with the
subdivided `K₃,₃`, and the explicit placement of that graph transfers along the isomorphism.

This is leaf C4 of the `d = 3` phase of FKS Problem 2: rows L2a, L2b and L2c of the case
table in `docs/research/2026-09-24-p9-crosscheck-d3.md`.

## References

Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, J. Combin. Theory
Ser. A **171** (2020), 105146, Problem 2 at `d = 3`; Chaffee and Noble, *Dimension 4 and
dimension 5 graphs with minimum edge set*, Australas. J. Combin. **64(2)** (2016), 327–333,
Theorems 6 and 7.
-/

namespace SimpleGraph

open Finset

/-- `G.edgeSet.ncard` agrees with the cardinality of `G.edgeFinset`. -/
private lemma ncard_eq_edgeFinset_card {V : Type*} (G : SimpleGraph V)
    [Fintype G.edgeSet] : G.edgeSet.ncard = #G.edgeFinset := by
  rw [edgeFinset_card, Set.fintypeCard_eq_ncard]

/-- Deleting a degree-two vertex deletes its two incident edges. -/
private lemma edgeSet_ncard_induce_compl_singleton {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} (hv : G.degree v = 2) :
    (G.induce {x | x ≠ v}).edgeSet.ncard ≤ G.edgeSet.ncard - 2 := by
  classical
  have hdel : #(G.induce {x | x ≠ v}).edgeFinset = #G.edgeFinset - 2 := by
    rw [← hv, ← G.card_edgeFinset_deleteIncidenceSet v,
      ← G.card_edgeFinset_induce_compl_singleton v]
    rfl
  rw [ncard_eq_edgeFinset_card (G := G.induce {x | x ≠ v}), ncard_eq_edgeFinset_card (G := G)]
  omega

/-- The two neighbours of `v`, in either order. -/
private lemma pair_eq_of_mem_neighborSet {V : Type*} {G : SimpleGraph V} {v : V}
    {a b : {x : V // x ≠ v}}
    (hn : ∀ x : V, G.Adj v x ↔ x = a.val ∨ x = b.val)
    {x y : {x : V // x ≠ v}} (hxN : x.val ∈ G.neighborSet v)
    (hyN : y.val ∈ G.neighborSet v) (hxy : x ≠ y) :
    (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  have hxp : x.val = a.val ∨ x.val = b.val :=
    (hn x.val).mp ((G.mem_neighborSet v x.val).mp hxN)
  have hyb : y.val = a.val ∨ y.val = b.val :=
    (hn y.val).mp ((G.mem_neighborSet v y.val).mp hyN)
  rcases hxp with hxp | hxp <;> rcases hyb with hyb | hyb
  · exact absurd (Subtype.ext (hxp.trans hyb.symm)) hxy
  · exact Or.inl ⟨Subtype.ext hxp, Subtype.ext hyb⟩
  · exact Or.inr ⟨Subtype.ext hxp, Subtype.ext hyb⟩
  · exact absurd (Subtype.ext (hxp.trans hyb.symm)) hxy

/-- If the two neighbours of a degree-two vertex are adjacent, the graph with the vertex
deleted has at most eight edges, places by the eight-edge theorem with the two neighbours
one apart, and the vertex is reattached. -/
private theorem unitDistEmbeddable_three_of_degree_eq_two_of_adj
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hE : G.edgeSet.ncard ≤ 10) (hv : G.degree v = 2)
    (a b : {x : V // x ≠ v})
    (hn : ∀ x : V, G.Adj v x ↔ x = a.val ∨ x = b.val)
    (habadj : G.Adj a.val b.val) :
    G.UnitDistEmbeddable 3 := by
  classical
  have hle : (G.induce {x | x ≠ v}).edgeSet.ncard ≤ 8 :=
    (edgeSet_ncard_induce_compl_singleton hv).trans (by omega)
  obtain ⟨f, hfInj, hfDist⟩ := unitDistEmbeddable_three_of_ncard_edgeSet_le
    (G.induce {x | x ≠ v}) hle
  refine UnitDistEmbeddable.extend_degree_le_two_fin_three hv.le ⟨f, hfInj, ?_⟩
  rintro x y (hadj | ⟨_, hxN, hyN, hxy⟩)
  · exact hfDist x y hadj
  · rcases pair_eq_of_mem_neighborSet hn hxN hyN hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hx, hy]
      exact hfDist _ _ (induce_adj.mpr habadj)
    · rw [hx, hy]
      exact hfDist _ _ (induce_adj.mpr habadj.symm)

@[expose] public section

/-- **A degree-two vertex is no obstruction.** A graph on at most seven vertices with at
most ten edges and no `K₃,₃` copy places in `ℝ³` as soon as it has a vertex of degree two.

Let `a` and `b` be the neighbours of `v` and complete `G' = G.induce {x | x ≠ v}` by the
edge `ab`. If `a` and `b` are adjacent, `G'` has at most eight edges and places, with `a`
and `b` one apart. Otherwise the completion has at most nine edges
(`edgeSet_ncard_completion_le`): either it places, again with `a`, `b` one apart, or the
nine-edge theorem gives a `K₃,₃` copy in it, in which case `G` is the subdivided `K₃,₃`
(`nonempty_iso_subdividedCompleteBipartiteGraph_of_completion`) and that graph places
explicitly. In every case the two neighbours of `v` land one apart, and
`UnitDistEmbeddable.extend_degree_le_two_fin_three` reattaches `v`.

This covers rows L2a, L2b and L2c of the `d = 3` case table of FKS Problem 2. Chaffee and
Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J. Combin.
**64(2)** (2016), 327–333, Theorems 6 and 7. -/
theorem unitDistEmbeddable_three_of_degree_eq_two
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V)
    (hV : Fintype.card V ≤ 7)
    (hE : G.edgeSet.ncard ≤ 10)
    (hK33 : ¬ ((completeBipartiteGraph (Fin 3) (Fin 3)) ⊑ G))
    (hv : G.degree v = 2) :
    G.UnitDistEmbeddable 3 := by
  classical
  have hcard : #(G.neighborFinset v) = 2 := by
    rw [G.card_neighborFinset_eq_degree v, hv]
  obtain ⟨p, q, hpq, hN⟩ := Finset.card_eq_two.mp hcard
  have hp : G.Adj v p := (G.mem_neighborFinset v p).mp (by rw [hN]; simp)
  have hq : G.Adj v q := (G.mem_neighborFinset v q).mp (by rw [hN]; simp)
  obtain ⟨a, b, hab, haP, hbP⟩ :
      ∃ a b : {x : V // x ≠ v}, a ≠ b ∧ a.val = p ∧ b.val = q :=
    ⟨⟨p, hp.ne'⟩, ⟨q, hq.ne'⟩, fun h => hpq (congrArg Subtype.val h), rfl, rfl⟩
  have hn : ∀ x : V, G.Adj v x ↔ x = a.val ∨ x = b.val := by
    intro x
    rw [← G.mem_neighborFinset, hN]
    simp [haP, hbP]
  rcases Classical.em (G.Adj p q) with hpqadj | -
  · -- L2a: the neighbours are adjacent; delete `v`, place, reattach.
    exact unitDistEmbeddable_three_of_degree_eq_two_of_adj G v hE hv a b hn
      (by rw [haP, hbP]; exact hpqadj)
  · -- The completion `C` of `G'` by the edge `ab`.
    have hCle : ((G.induce {x | x ≠ v}) ⊔ fromEdgeSet {s(a, b)}).edgeSet.ncard ≤ 9 :=
      edgeSet_ncard_completion_le G v a b hE hv
    rcases Classical.em (((G.induce {x | x ≠ v}) ⊔ fromEdgeSet {s(a, b)}).UnitDistEmbeddable 3) with
      hC | hC
    · -- L2b: the completion places, so `a` and `b` land one apart.
      obtain ⟨f, hfInj, hfDist⟩ := hC
      refine UnitDistEmbeddable.extend_degree_le_two_fin_three hv.le ⟨f, hfInj, ?_⟩
      rintro x y (hadj | ⟨_, hxN, hyN, hxy⟩)
      · exact hfDist x y (Or.inl hadj)
      · rcases pair_eq_of_mem_neighborSet hn hxN hyN hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · rw [hx, hy]
          refine hfDist _ _ (Or.inr ?_)
          simp only [fromEdgeSet_adj, Set.mem_singleton_iff]
          exact ⟨rfl, hab⟩
        · rw [hx, hy]
          refine hfDist _ _ (Or.inr ?_)
          simp only [fromEdgeSet_adj, Set.mem_singleton_iff]
          exact ⟨Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩), hab.symm⟩
    · -- L2c: the completion fails, so `G` is the subdivided `K₃,₃`.
      have hK33C : (completeBipartiteGraph (Fin 3) (Fin 3)) ⊑
          ((G.induce {x | x ≠ v}) ⊔ fromEdgeSet {s(a, b)}) :=
        completeBipartiteGraph_three_three_isContained_of_not_unitDistEmbeddable_three
          _ hCle hC
      obtain ⟨e⟩ := nonempty_iso_subdividedCompleteBipartiteGraph_of_completion
        G v a b hV hE hK33 hv hab hn hK33C
      exact (UnitDistEmbeddable.of_iso e).mpr
        unitDistEmbeddable_subdividedCompleteBipartiteGraph_three_three

end

end SimpleGraph

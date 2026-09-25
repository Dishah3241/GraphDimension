/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic
public import GraphDimension.Combinatorics.SimpleGraph.FiveVertices
public import GraphDimension.Combinatorics.SimpleGraph.SixVertices
public import GraphDimension.Extremal.EightEdges
public import GraphDimension.Geometry.CompleteMinusEdge
public import GraphDimension.Geometry.FinLe
public import GraphDimension.Geometry.Prism
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite

import GraphDimension.Geometry.Extend
import GraphDimension.Geometry.Reattach
import GraphDimension.Geometry.UnitDistanceComap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Range
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Nine edges: only `K₃,₃` fails in `ℝ³`

A finite graph with at most nine edges and no unit-distance representation in `ℝ³` contains
`K₃,₃` as a (not necessarily induced) subgraph. Together with the `g(3) = 8` bound of
`GraphDimension.Extremal.EightEdges` this says `f_D(7) = 3`: `K₃,₃`, with nine edges, is the
smallest graph that is not unit-distance embeddable in `ℝ³`.

If the graph has an isolated vertex, the rest still has nine edges and no placement, and the
induction carries the containment over. Otherwise every degree is at least three: a vertex of
degree one or two is deleted, placed with `GraphDimension.Extremal.EightEdges`, and reattached
by `UnitDistEmbeddable.extend_degree_le_two_fin_three`. Then `3|V| ≤ 2·9 = 18` bounds the
number of vertices by six, and nine edges bound it below by five. Five vertices force `K₅ − e`,
which embeds. On six vertices the graph is three-regular, its complement is two-regular, hence
`C₆` or `K₃ ⊔ K₃`; the complement of `C₆` is the triangular prism, which embeds in the plane,
and the complement of `K₃ ⊔ K₃` is `K₃,₃` itself.

## References

House of Graphs / Chaffee and Noble, *Dimension 4 and dimension 5 graphs with minimum edge
set*, Australas. J. Combin. **64(2)** (2016), 327–333, Theorem 7.
-/

namespace SimpleGraph

open Finset Metric

noncomputable section

/-! ### Counting and transport helpers -/

/-- `G.edgeSet.ncard` agrees with the cardinality of `G.edgeFinset`. -/
private lemma edgeSet_ncard_eq {V : Type*} (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeSet.ncard = #G.edgeFinset := by
  rw [edgeFinset_card, Set.fintypeCard_eq_ncard]

/-- Deleting `u` removes exactly `G.degree u` edges. -/
private lemma card_edgeFinset_induce_ne {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (u : V) :
    (G.induce {v | v ≠ u}).edgeFinset.card = G.edgeFinset.card - G.degree u := by
  rw [← G.card_edgeFinset_deleteIncidenceSet u,
    ← G.card_edgeFinset_induce_compl_singleton u]
  rfl

/-- A simple graph on at most four vertices has at most six edges. -/
private lemma edgeFinset_card_le_six_of_card_le_four {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hV : Fintype.card V ≤ 4) :
    #G.edgeFinset ≤ 6 := by
  calc
    #G.edgeFinset ≤ (Fintype.card V).choose 2 := G.card_edgeFinset_le_card_choose_two
    _ ≤ Nat.choose 4 2 := Nat.choose_le_choose 2 hV
    _ = 6 := by decide

/-- Edge counts transport along `SimpleGraph.overFin`. -/
private lemma edgeSet_ncard_overFin {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (hV : Fintype.card V = n) : (G.overFin hV).edgeSet.ncard = G.edgeSet.ncard := by
  classical
  rw [edgeSet_ncard_eq, edgeSet_ncard_eq (G := G), (G.overFinIso hV).card_edgeFinset_eq]

/-- A placement of `Hᶜ` pulls back along an isomorphism `Gᶜ ≃g H` to a placement of `G`. -/
private lemma unitDistEmbeddable_of_compl_iso {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} {n : ℕ} (e : Gᶜ ≃g H) (h : (Hᶜ).UnitDistEmbeddable n) :
    G.UnitDistEmbeddable n := by
  have h' : ((Gᶜ)ᶜ).UnitDistEmbeddable n :=
    h.of_embedding (Embedding.complEquiv e.toEmbedding)
  rwa [compl_compl] at h'

/-- `K₅` with any chosen edge deleted admits a unit-distance representation in `ℝ³`, by moving
the deleted edge of the reference placement onto `{a, b}` along a permutation of `Fin 5`. -/
private theorem unitDistEmbeddable_deleteEdges_pair {a b : Fin 5} (hab : a ≠ b) :
    ((⊤ : SimpleGraph (Fin 5)).deleteEdges {s(a, b)}).UnitDistEmbeddable 3 := by
  classical
  obtain ⟨e, hea, heb⟩ := exists_equiv_sending_pair (V := Fin 5) (by simp) hab
  refine UnitDistEmbeddable.comap
    (show (⊤ : SimpleGraph (Fin 5)).deleteEdges {s(a, b)} →g
        (⊤ : SimpleGraph (Fin 5)).deleteEdges {s(3, 4)} from
      ⟨e, fun {x y} hxy => by
        rw [deleteEdges_adj, top_adj] at hxy
        rw [deleteEdges_adj, top_adj]
        obtain ⟨hxy1, hxy2⟩ := hxy
        refine ⟨e.injective.ne hxy1, ?_⟩
        intro hmem
        rw [Set.mem_singleton_iff] at hmem
        rcases Sym2.eq_iff.mp hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hx : x = a := e.injective (h1.trans hea.symm)
          have hy : y = b := e.injective (h2.trans heb.symm)
          exact hxy2 (by rw [hx, hy, Set.mem_singleton_iff])
        · have hx : x = b := e.injective (h1.trans heb.symm)
          have hy : y = a := e.injective (h2.trans hea.symm)
          exact hxy2 (by rw [hx, hy, Set.mem_singleton_iff]; exact Sym2.eq_swap)⟩)
    e.injective unitDistEmbeddable_completeGraph_five_deleteEdge

-- The sup-specific finiteness instance is not the one used for an abstract graph, and the
-- two `edgeFinset` instances are not definitionally equal.
attribute [-instance] SimpleGraph.fintypeEdgeSetSup in
/-- A finite graph with nine edges and a vertex of degree one or two admits a unit-distance
representation in `ℝ³`.

The induced subgraph on `V \ {u}` has `9 - G.degree u` edges. Degree one leaves eight. Degree
two leaves seven, and the edge between the two neighbours brings the count to at most eight.
`unitDistEmbeddable_three_of_ncard_edgeSet_le` places that graph, and
`UnitDistEmbeddable.extend_degree_le_two_fin_three` restores `u`. The hypothesis
`0 < G.degree u` keeps the degree equal to one or two: an isolated vertex leaves all nine edges
on `V \ {u}`.

Chaffee and Noble, the argument of their Theorem 7. -/
private theorem unitDistEmbeddable_three_of_nine_edges_of_degree_le_two
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hE : #G.edgeFinset = 9) {u : V} (hdeg : G.degree u ≤ 2)
    (hpos : 0 < G.degree u) :
    G.UnitDistEmbeddable 3 := by
  classical
  have glue (H : SimpleGraph {v // v ≠ u}) [DecidableRel H.Adj]
      (hsub : ∀ ⦃a b : {v // v ≠ u}⦄,
        (G.induce {v | v ≠ u}).Adj a b → H.Adj a b)
      (hextra : ∀ ⦃a b : {v // v ≠ u}⦄, G.degree u = 2 → a.1 ∈ G.neighborSet u →
        b.1 ∈ G.neighborSet u → a ≠ b → H.Adj a b)
      (hEle : #H.edgeFinset ≤ 8) :
      G.UnitDistEmbeddable 3 := by
    obtain ⟨f, hfInj, hfDist⟩ := unitDistEmbeddable_three_of_ncard_edgeSet_le H
      (by rw [edgeSet_ncard_eq H]; exact hEle)
    refine UnitDistEmbeddable.extend_degree_le_two_fin_three hdeg ⟨f, hfInj, ?_⟩
    intro a b hcond
    rcases hcond with hadj | ⟨h2, ha, hb, hab⟩
    · exact hfDist a b (hsub hadj)
    · exact hfDist a b (hextra h2 ha hb hab)
  obtain h1 | h2 : G.degree u = 1 ∨ G.degree u = 2 := by omega
  · let H : SimpleGraph {v // v ≠ u} := G.induce {v | v ≠ u}
    have hEle : #H.edgeFinset ≤ 8 := by
      rw [card_edgeFinset_induce_ne u, h1]
      omega
    exact glue H (fun _ _ h => h) (fun _ _ h2 _ _ _ => by omega) hEle
  · let G' : SimpleGraph {v // v ≠ u} := G.induce {v | v ≠ u}
    have hNcard : (G.neighborFinset u).card = 2 := by
      rw [G.card_neighborFinset_eq_degree, h2]
    obtain ⟨a, b, _, hN⟩ := Finset.card_eq_two.mp hNcard
    have ha : G.Adj u a := (G.mem_neighborFinset u a).mp (by simp [hN])
    have hb : G.Adj u b := (G.mem_neighborFinset u b).mp (by simp [hN])
    let a' : {v // v ≠ u} := ⟨a, ha.ne'⟩
    let b' : {v // v ≠ u} := ⟨b, hb.ne'⟩
    let E : SimpleGraph {v // v ≠ u} := fromRel fun x y => x = a' ∧ y = b'
    let H : SimpleGraph {v // v ≠ u} := G' ⊔ E
    have hHcard : #H.edgeFinset ≤ #G'.edgeFinset + 1 := by
      have hsub : H.edgeFinset ⊆ G'.edgeFinset ∪ {s(a', b')} := by
        intro e he
        have heSet : e ∈ H.edgeSet := (mem_edgeFinset (G := H)).mp he
        induction e using Sym2.ind with
        | h x y =>
          have hadj : H.Adj x y := (mem_edgeSet (G := H)).mp heSet
          simp only [H, sup_adj] at hadj
          rcases hadj with hG | ⟨_, hpair⟩
          · exact Finset.mem_union_left _ ((mem_edgeFinset (G := G')).mpr
              ((mem_edgeSet (G := G')).mpr hG))
          · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
            · rw [Sym2.eq_swap]
              exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      have hunion : (G'.edgeFinset ∪ {s(a', b')}).card ≤ #G'.edgeFinset + 1 := by
        exact (Finset.card_union_le _ _).trans (by simp)
      exact (Finset.card_le_card hsub).trans hunion
    have hG' : #G'.edgeFinset = #G.edgeFinset - 2 := by
      rw [card_edgeFinset_induce_ne u, h2]
    have hEle : #H.edgeFinset ≤ 8 := by omega
    obtain ⟨f, hfInj, hfDist⟩ := unitDistEmbeddable_three_of_ncard_edgeSet_le H
      (by rw [edgeSet_ncard_eq H]; omega)
    refine UnitDistEmbeddable.extend_degree_le_two_fin_three hdeg ⟨f, hfInj, ?_⟩
    intro x y hcond
    rcases hcond with hadj | ⟨_, hxN, hyN, hxy⟩
    · exact hfDist x y ((le_sup_left : G' ≤ H) hadj)
    · have hxab : x.1 = a ∨ x.1 = b := by
        have hxFin : x.1 ∈ G.neighborFinset u :=
          (G.mem_neighborFinset u x.1).mpr ((G.mem_neighborSet u x.1).mp hxN)
        rw [hN] at hxFin
        simpa using hxFin
      have hyab : y.1 = a ∨ y.1 = b := by
        have hyFin : y.1 ∈ G.neighborFinset u :=
          (G.mem_neighborFinset u y.1).mpr ((G.mem_neighborSet u y.1).mp hyN)
        rw [hN] at hyFin
        simpa using hyFin
      have hEadj : E.Adj x y := by
        rw [fromRel_adj]
        refine ⟨hxy, ?_⟩
        rcases hxab with hxa | hxb <;> rcases hyab with hya | hyb
        · exact absurd (Subtype.ext (hxa.trans hya.symm)) hxy
        · exact Or.inl ⟨Subtype.ext hxa, Subtype.ext hyb⟩
        · exact Or.inr ⟨Subtype.ext hya, Subtype.ext hxb⟩
        · exact absurd (Subtype.ext (hxb.trans hyb.symm)) hxy
      exact hfDist x y ((le_sup_right : E ≤ H) hEadj)

/-- On at most five vertices, minimum degree three, nine edges and no placement in `ℝ³` force
an isomorphism with `K₃,₃` on six vertices.

Nine edges bound the vertex count below by five, and `3|V| ≤ 2·9 = 18` above by six. Five
vertices force `K₅ − e`, which embeds in `ℝ³`, a contradiction. On six vertices the graph is
three-regular, its complement is two-regular, hence `C₆` or `K₃ ⊔ K₃`; the complement of `C₆`
is the triangular prism, which embeds in the plane, and the complement of `K₃ ⊔ K₃` is
`K₃,₃`. -/
private theorem exists_iso_of_not_embeddable_of_minDegree_three {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hE9 : #G.edgeFinset = 9)
    (hdeg3 : ∀ v, 3 ≤ G.degree v) (hG : ¬ G.UnitDistEmbeddable 3) :
    Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
  classical
  have h5 : 5 ≤ Fintype.card V := by
    by_contra hlt
    have hle : #G.edgeFinset ≤ 6 :=
      edgeFinset_card_le_six_of_card_le_four (G := G) (by omega)
    omega
  have h6 : Fintype.card V ≤ 6 := by
    have hsum : ∑ v, G.degree v = 2 * #G.edgeFinset := G.sum_degrees_eq_twice_card_edges
    have hlow : 3 * Fintype.card V ≤ ∑ v, G.degree v := by
      calc 3 * Fintype.card V = ∑ _v : V, 3 := by
            rw [Nat.mul_comm, ← Finset.card_univ, ← Finset.sum_const_nat fun _ _ => rfl]
          _ ≤ ∑ v, G.degree v := Finset.sum_le_sum fun v _ => hdeg3 v
    have h18 : 3 * Fintype.card V ≤ 18 := by rw [hsum, hE9] at hlow; omega
    omega
  have h56 : Fintype.card V = 5 ∨ Fintype.card V = 6 := by omega
  rcases h56 with h5c | h6c
  · have hE5 : #((G.overFin h5c).edgeFinset) = 9 := by
      have h1 := edgeSet_ncard_overFin (G := G) h5c
      rw [edgeSet_ncard_eq, edgeSet_ncard_eq (G := G)] at h1
      omega
    obtain ⟨a, b, hab, ⟨φ⟩⟩ := nine_edges_iso_deleteEdge hE5
    exact absurd ((UnitDistEmbeddable.of_iso (G.overFinIso h5c)).mpr
      ((UnitDistEmbeddable.of_iso φ).mpr (unitDistEmbeddable_deleteEdges_pair hab))) hG
  · have hE6 : #((G.overFin h6c).edgeFinset) = 9 := by
      have h1 := edgeSet_ncard_overFin (G := G) h6c
      rw [edgeSet_ncard_eq, edgeSet_ncard_eq (G := G)] at h1
      omega
    have hdeg6 : ∀ v, 3 ≤ (G.overFin h6c).degree v := by
      intro v
      have hdeg := (G.overFinIso h6c).degree_eq ((G.overFinIso h6c).symm v)
      rw [(G.overFinIso h6c).apply_symm_apply] at hdeg
      rw [hdeg]
      exact hdeg3 _
    rcases nine_edges_six_minDegree_three hE6 hdeg6 with hK | hC
    · exact ⟨Iso.comp hK.some (G.overFinIso h6c)⟩
    · obtain ⟨ψ⟩ := hC
      have hemb : ((cycleGraph 6)ᶜ).UnitDistEmbeddable 3 :=
        unitDistEmbeddable_compl_cycleGraph_six.mono (by decide)
      exact absurd ((UnitDistEmbeddable.of_iso (G.overFinIso h6c)).mpr
        (unitDistEmbeddable_of_compl_iso ψ hemb)) hG

/-- Induction on the number of vertices for the `K₃,₃` containment. An isolated vertex carries
no edges and no placement constraint: deleting it preserves both the edge count and
non-embeddability, and the copy of `K₃,₃` in the deletion sits in `G`. -/
private theorem isContained_aux (n : ℕ) {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hV : Fintype.card V ≤ n) (hE : #G.edgeFinset ≤ 9)
    (hG : ¬ G.UnitDistEmbeddable 3) :
    completeBipartiteGraph (Fin 3) (Fin 3) ⊑ G := by
  induction n generalizing V with
  | zero =>
    have hV0 : Fintype.card V = 0 := Nat.le_zero.mp hV
    have hEmpty : IsEmpty V := Fintype.card_eq_zero_iff.mp hV0
    have hncard : G.edgeSet.ncard ≤ 8 := by
      have hset : G.edgeSet = ∅ := by
        ext e
        induction e using Sym2.ind with
        | h a b =>
          simp only [mem_edgeSet, Set.mem_empty_iff_false, iff_false]
          exact isEmptyElim a
      rw [hset, Set.ncard_empty]
      exact Nat.zero_le 8
    exact absurd (unitDistEmbeddable_three_of_ncard_edgeSet_le G hncard) hG
  | succ n ih =>
    classical
    by_cases hiso : ∃ u : V, G.degree u = 0
    · obtain ⟨u, hu⟩ := hiso
      have hcard' : Fintype.card {v : V // v ≠ u} ≤ n := by
        rw [Fintype.card_subtype_compl (p := (· = u)), Fintype.card_subtype_eq u]
        have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
        omega
      have hE' : #((G.induce {v | v ≠ u}).edgeFinset) ≤ 9 := by
        rw [card_edgeFinset_induce_ne u, hu]
        omega
      have hN : G.neighborSet u = ∅ := by
        ext v
        simp only [mem_neighborSet, Set.mem_empty_iff_false, iff_false]
        exact (G.degree_eq_zero u).mp hu v
      have hclique : G.IsClique (G.neighborSet u) := by
        rw [hN]
        exact fun a ha _ _ => absurd ha (Set.notMem_empty a)
      have hG' : ¬(G.induce {v | v ≠ u}).UnitDistEmbeddable 3 := fun h' =>
        hG (UnitDistEmbeddable.extend (G := G) (u := u) hclique (by rw [hN]; simp) h')
      exact (ih _ hcard' hE' hG').trans ⟨Copy.induce G {v | v ≠ u}⟩
    · have hdeg1 : ∀ v, 0 < G.degree v := fun v =>
        Nat.pos_of_ne_zero (fun h0 => hiso ⟨v, h0⟩)
      have hE9 : #G.edgeFinset = 9 := by
        by_contra hne
        have hle8 : #G.edgeFinset ≤ 8 := by omega
        exact hG (unitDistEmbeddable_three_of_ncard_edgeSet_le G
          (by rw [edgeSet_ncard_eq G]; exact hle8))
      have hdeg3 : ∀ v, 3 ≤ G.degree v := by
        intro v
        rcases Nat.lt_or_ge (G.degree v) 3 with hlt | hge
        · exact absurd (unitDistEmbeddable_three_of_nine_edges_of_degree_le_two hE9
            (Nat.lt_succ_iff.mp hlt) (hdeg1 v)) hG
        · exact hge
      exact ⟨(exists_iso_of_not_embeddable_of_minDegree_three G hE9 hdeg3 hG).some.symm.toCopy⟩

@[expose] public section

/-- **Nine edges: only `K₃,₃` fails in `ℝ³`.** A finite graph with exactly nine edges and no
unit-distance representation in `ℝ³`, and with no isolated vertex, is isomorphic to the
complete bipartite graph `K₃,₃`.

No vertex has degree one or two, since such a vertex can be deleted, the remaining eight or
seven edges placed by `GraphDimension.Extremal.EightEdges`, and the vertex reattached by
`UnitDistEmbeddable.extend_degree_le_two_fin_three`. Then `3|V| ≤ 2·9 = 18` bounds the vertex
count above by six, and nine edges bound it below by five. Five vertices force `K₅ − e`, which
embeds. On six vertices the graph is three-regular, its complement is two-regular, hence `C₆`
or `K₃ ⊔ K₃`; the complement of `C₆` is the triangular prism, which embeds in the plane, and
the complement of `K₃ ⊔ K₃` is `K₃,₃`.

Chaffee and Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J.
Combin. **64(2)** (2016), 327–333, Theorem 7; House (2013). -/
theorem nonempty_iso_completeBipartiteGraph_three_three_of_not_unitDistEmbeddable_three
    {V : Type*} [Finite V] (G : SimpleGraph V) (hE : G.edgeSet.ncard = 9)
    (hnbr : ∀ v : V, ∃ w : V, G.Adj v w) (hG : ¬ G.UnitDistEmbeddable 3) :
    Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
  classical
  have := Fintype.ofFinite V
  have hE' : #G.edgeFinset = 9 := by rw [← edgeSet_ncard_eq G]; exact hE
  have hdeg3 : ∀ v, 3 ≤ G.degree v := by
    intro v
    rcases Nat.lt_or_ge (G.degree v) 3 with hlt | hge
    · obtain ⟨w, hw⟩ := hnbr v
      exact absurd (unitDistEmbeddable_three_of_nine_edges_of_degree_le_two hE'
        (Nat.lt_succ_iff.mp hlt) ((G.degree_pos_iff_exists_adj v).mpr ⟨w, hw⟩)) hG
    · exact hge
  exact exists_iso_of_not_embeddable_of_minDegree_three G hE' hdeg3 hG

/-- **At most nine edges: only `K₃,₃` fails in `ℝ³`.** A finite graph with at most nine edges
and no unit-distance representation in `ℝ³` contains `K₃,₃` (`⊑`, an injective homomorphism,
not an induced copy).

Graphs with at most eight edges embed by `unitDistEmbeddable_three_of_ncard_edgeSet_le`, so a
counterexample has exactly nine edges. If it has an isolated vertex, the rest still has nine
edges and no placement, and the induction carries the containment over. Otherwise every degree
is at least three, and the classification
`nonempty_iso_completeBipartiteGraph_three_three_of_not_unitDistEmbeddable_three` applies.

This is the `d = 3` base of FKS Problem 2: `g(3) = 8` and `f_D(7) = 3`. Chaffee and Noble,
*Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J. Combin. **64(2)**
(2016), 327–333, Theorem 7. -/
theorem completeBipartiteGraph_three_three_isContained_of_not_unitDistEmbeddable_three
    {V : Type*} [Finite V] (G : SimpleGraph V) (h : G.edgeSet.ncard ≤ 9)
    (hG : ¬ G.UnitDistEmbeddable 3) :
    completeBipartiteGraph (Fin 3) (Fin 3) ⊑ G := by
  classical
  have := Fintype.ofFinite V
  have hE : #G.edgeFinset ≤ 9 := by
    rw [← edgeSet_ncard_eq G]
    exact h
  exact isContained_aux (Fintype.card V) G le_rfl hE hG

end

end

end SimpleGraph

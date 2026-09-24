/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Combinatorics.SimpleGraph.SmallGraphsThree
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Operations

import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Recovering a subdivided complete bipartite graph

Deleting a degree-two vertex and joining its neighbours can create a `K₃,₃` copy.
With at most seven vertices and ten edges, the copy exhausts the completion, and
the original graph is the subdivision of one edge of `K₃,₃`.
-/

namespace SimpleGraph

open Finset

/-- An injective homomorphism exhausts both vertices and edges when neither target
cardinality is larger than the corresponding source cardinality. -/
private lemma iso_of_copy_of_card_le {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : Copy G H)
    (hV : Fintype.card W ≤ Fintype.card V)
    (hE : H.edgeSet.ncard ≤ G.edgeSet.ncard) :
    ∃ e : G ≃g H, ∀ x, e x = f x := by
  classical
  have hcard : Fintype.card V = Fintype.card W :=
    Nat.le_antisymm (Fintype.card_le_of_injective f f.injective) hV
  have hsurj : Function.Surjective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, hcard⟩ |>.surjective
  have hmap : G.map f = H := by
    apply edgeFinset_inj.mp
    apply Finset.eq_of_subset_of_card_le (edgeFinset_mono f.toHom.map_le)
    change H.edgeFinset.card ≤ (G.map f.toEmbedding).edgeFinset.card
    rw [card_edgeFinset_map]
    simpa only [edgeFinset_card, Set.fintypeCard_eq_ncard] using hE
  refine ⟨{ Equiv.ofBijective f ⟨f.injective, hsurj⟩ with map_rel_iff' := ?_ }, fun _ => rfl⟩
  intro x y
  change H.Adj (f x) (f y) ↔ G.Adj x y
  have hc := congrArg (fun K => K.Adj x y) (comap_map_eq f.toEmbedding G)
  change (G.map f).Adj (f x) (f y) = G.Adj x y at hc
  rw [hmap] at hc
  exact iff_of_eq hc

private lemma completeBipartiteGraph_three_three_ncard :
    (completeBipartiteGraph (Fin 3) (Fin 3)).edgeSet.ncard = 9 := by
  let : DecidableRel (completeBipartiteGraph (Fin 3) (Fin 3)).Adj :=
    fun x y => inferInstanceAs (Decidable
      (x.isLeft ∧ y.isRight ∨ x.isRight ∧ y.isLeft))
  rw [← Set.fintypeCard_eq_ncard, ← edgeFinset_card]
  decide

/-- Permuting the two parts sends any specified edge to the distinguished cross edge,
with either orientation. -/
private lemma exists_iso_completeBipartiteGraph_sending_edge {W : Type*}
    {H : SimpleGraph W} (e : completeBipartiteGraph (Fin 3) (Fin 3) ≃g H)
    {a b : W} (hab : H.Adj a b) :
    ∃ f : completeBipartiteGraph (Fin 3) (Fin 3) ≃g H,
      (f (.inl 0) = a ∧ f (.inr 0) = b) ∨
      (f (.inl 0) = b ∧ f (.inr 0) = a) := by
  obtain ⟨x, hx⟩ := e.surjective a
  obtain ⟨y, hy⟩ := e.surjective b
  have hxy : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj x y :=
    e.map_rel_iff.mp (by simpa only [hx, hy] using hab)
  cases x with
  | inl i =>
    cases y with
    | inl j => simp [completeBipartiteGraph_adj] at hxy
    | inr j =>
      refine ⟨e.comp (completeBipartiteGraphCongr (Equiv.swap 0 i) (Equiv.swap 0 j)),
        Or.inl ?_⟩
      simpa using And.intro hx hy
  | inr i =>
    cases y with
    | inl j =>
      refine ⟨e.comp (completeBipartiteGraphCongr (Equiv.swap 0 j) (Equiv.swap 0 i)),
        Or.inr ?_⟩
      simpa using And.intro hy hx
    | inr j => simp [completeBipartiteGraph_adj] at hxy

@[expose] public section

/-- Completing the neighbours of a degree-two vertex adds at most one edge after
deleting its two incident edges. -/
lemma edgeSet_ncard_completion_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (a b : {x : V // x ≠ v})
    (hE : G.edgeSet.ncard ≤ 10) (hv : G.degree v = 2) :
    ((G.induce {x | x ≠ v}) ⊔ fromEdgeSet {s(a,b)}).edgeSet.ncard ≤ 9 := by
  classical
  have hdel : (G.induce {x | x ≠ v}).edgeFinset.card = G.edgeFinset.card - 2 := by
    rw [← hv, ← G.card_edgeFinset_deleteIncidenceSet v,
      ← G.card_edgeFinset_induce_compl_singleton v]
    rfl
  have hsingle : (fromEdgeSet {s(a,b)} : SimpleGraph {x : V // x ≠ v}).edgeFinset.card ≤ 1 := by
    apply le_trans (Finset.card_le_card (t := {s(a,b)}) ?_) (by simp)
    intro e he
    have he' := mem_edgeFinset.mp he
    rw [edgeSet_fromEdgeSet] at he'
    simpa only [Set.mem_singleton_iff, Finset.mem_singleton] using he'.1
  have hu := Finset.card_union_le (G.induce {x | x ≠ v}).edgeFinset
    (fromEdgeSet {s(a,b)}).edgeFinset
  rw [← edgeFinset_sup] at hu
  simp only [← Set.fintypeCard_eq_ncard, ← edgeFinset_card] at hE ⊢
  omega

/-- A `K₃,₃` copy exhausts a degree-two completion on at most six remaining vertices
and at most nine edges. In particular the copy is an induced, surjective copy. -/
lemma nonempty_iso_completeBipartiteGraph_completion {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (a b : {x : V // x ≠ v})
    (hV : Fintype.card V ≤ 7) (hE : G.edgeSet.ncard ≤ 10) (hv : G.degree v = 2)
    (hH : (completeBipartiteGraph (Fin 3) (Fin 3)) ⊑
      ((G.induce {x | x ≠ v}) ⊔ fromEdgeSet {s(a,b)})) :
    Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)) ≃g
      ((G.induce {x | x ≠ v}) ⊔ fromEdgeSet {s(a,b)})) := by
  classical
  obtain ⟨f⟩ := hH
  obtain ⟨e, -⟩ := iso_of_copy_of_card_le f (by
    simp only [Fintype.card_sum, Fintype.card_fin]
    change Fintype.card {x : V // x ≠ v} ≤ 3 + 3
    rw [Fintype.card_subtype_compl (fun x => x = v), Fintype.card_subtype_eq]
    omega) (by
    rw [completeBipartiteGraph_three_three_ncard]
    exact edgeSet_ncard_completion_le G v a b hE hv)
  exact ⟨e⟩

/-- If completion creates a forbidden copy, the completed edge was absent before
completion. This implication needs no cardinality hypotheses. -/
lemma not_adj_of_completeBipartiteGraph_completion {V : Type*} (G : SimpleGraph V)
    (v : V) (a b : {x : V // x ≠ v})
    (hK33 : ¬ ((completeBipartiteGraph (Fin 3) (Fin 3)) ⊑ G))
    (hH : (completeBipartiteGraph (Fin 3) (Fin 3)) ⊑
      ((G.induce {x | x ≠ v}) ⊔ fromEdgeSet {s(a,b)})) : ¬ G.Adj a.val b.val := by
  intro hab
  obtain ⟨f⟩ := hH
  apply hK33
  refine ⟨⟨{ toFun := fun x => (f x).val, map_rel' := ?_ },
    Subtype.val_injective.comp f.injective⟩⟩
  intro x y hxy
  have hf := f.toHom.map_rel' hxy
  rcases hf with h | h
  · exact h
  · simp only [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at h
    obtain ⟨he, -⟩ := h
    rcases he with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · change f x = a at hx
      change f y = b at hy
      simpa only [hx, hy] using hab
    · change f x = b at hx
      change f y = a at hy
      simpa only [hx, hy] using hab.symm

/-- Recover the subdivision from a completion isomorphism whose distinguished edge
has the prescribed endpoints. -/
private lemma nonempty_iso_subdivision_of_completion_iso {V : Type*}
    (G : SimpleGraph V) (v : V) (a b : {x : V // x ≠ v})
    (e : completeBipartiteGraph (Fin 3) (Fin 3) ≃g
      ((G.induce {x | x ≠ v}) ⊔ fromEdgeSet {s(a,b)}))
    (ha : e (.inl 0) = a) (hb : e (.inr 0) = b)
    (hn : ∀ x : V, G.Adj v x ↔ x = a.val ∨ x = b.val)
    (hab : ¬ G.Adj a.val b.val) :
    Nonempty (G ≃g subdividedCompleteBipartiteGraphThreeThree) := by
  classical
  have hinj (x y : Fin 3 ⊕ Fin 3) : (e x).val = (e y).val ↔ x = y :=
    ⟨fun h => e.injective (Subtype.ext h), fun h => congrArg (fun z => (e z).val) h⟩
  have hnv (x : Fin 3 ⊕ Fin 3) : (e x).val ≠ v := (e x).property
  have hbase (x y : Fin 3 ⊕ Fin 3) :
      G.Adj (e x).val (e y).val ↔
        (completeBipartiteGraph (Fin 3) (Fin 3)).Adj x y ∧
          ¬ (x = .inl 0 ∧ y = .inr 0 ∨ x = .inr 0 ∧ y = .inl 0) := by
    constructor
    · intro h
      refine ⟨e.map_rel_iff.mp (Or.inl h), ?_⟩
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hab (by simpa only [ha, hb] using h)
      · exact hab (by simpa only [ha, hb] using h.symm)
    · rintro ⟨hxy, hne⟩
      have h := e.map_rel_iff.mpr hxy
      rcases h with h | h
      · exact h
      · simp only [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at h
        apply False.elim (hne ?_)
        simpa only [← ha, ← hb, e.injective.eq_iff] using h.1
  have hvbase (x : Fin 3 ⊕ Fin 3) :
      G.Adj v (e x).val ↔ x = .inl 0 ∨ x = .inr 0 := by
    rw [hn]
    simp only [← ha, ← hb, hinj]
  let f : Fin 7 → V := ![(e (.inl 0)).val, (e (.inl 1)).val,
    (e (.inl 2)).val, (e (.inr 0)).val, (e (.inr 1)).val, (e (.inr 2)).val, v]
  have hfi : Function.Injective f := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [f, hinj, hnv, Ne.symm (hnv _)]
  have hfs : Function.Surjective f := by
    intro x
    by_cases hx : x = v
    · exact ⟨6, hx.symm⟩
    · obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
      have hy' : (e y).val = x := congrArg Subtype.val hy
      cases y with
      | inl i =>
        fin_cases i
        · exact ⟨0, hy'⟩
        · exact ⟨1, hy'⟩
        · exact ⟨2, hy'⟩
      | inr i =>
        fin_cases i
        · exact ⟨3, hy'⟩
        · exact ⟨4, hy'⟩
        · exact ⟨5, hy'⟩
  have hvbase' (x : Fin 3 ⊕ Fin 3) :
      G.Adj (e x).val v ↔ x = .inl 0 ∨ x = .inr 0 :=
    (G.adj_comm _ _).trans (hvbase x)
  have hrel (i j : Fin 7) : G.Adj (f i) (f j) ↔
      subdividedCompleteBipartiteGraphThreeThree.Adj i j := by
    fin_cases i <;> fin_cases j <;>
      simp [f, hbase, hvbase, hvbase',
        completeBipartiteGraph_adj, subdividedCompleteBipartiteGraphThreeThree_adj_iff]
  exact ⟨({ Equiv.ofBijective f ⟨hfi, hfs⟩ with map_rel_iff' := fun {i j} => hrel i j } :
    subdividedCompleteBipartiteGraphThreeThree ≃g G).symm⟩

/-- If completing a degree-two vertex creates a `K₃,₃` in a graph with at most seven
vertices and ten edges which had no `K₃,₃`, the graph is exactly a subdivided `K₃,₃`. -/
theorem nonempty_iso_subdividedCompleteBipartiteGraph_of_completion
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (a b : {x : V // x ≠ v})
    (hV : Fintype.card V ≤ 7)
    (hE : G.edgeSet.ncard ≤ 10)
    (hK33 : ¬ ((completeBipartiteGraph (Fin 3) (Fin 3)) ⊑ G))
    (hv : G.degree v = 2)
    (hab : a ≠ b)
    (hn : ∀ x : V, G.Adj v x ↔ x = a.val ∨ x = b.val)
    (hH : (completeBipartiteGraph (Fin 3) (Fin 3)) ⊑
      ((G.induce {x | x ≠ v}) ⊔ fromEdgeSet {s(a,b)})) :
    Nonempty (G ≃g subdividedCompleteBipartiteGraphThreeThree) := by
  have hnot := not_adj_of_completeBipartiteGraph_completion G v a b hK33 hH
  obtain ⟨e⟩ := nonempty_iso_completeBipartiteGraph_completion G v a b hV hE hv hH
  have habC : ((G.induce {x | x ≠ v}) ⊔ fromEdgeSet {s(a,b)}).Adj a b := by
    exact Or.inr (by simp only [fromEdgeSet_adj, Set.mem_singleton_iff]; exact ⟨rfl, hab⟩)
  obtain ⟨f, h | h⟩ := exists_iso_completeBipartiteGraph_sending_edge e habC
  · exact nonempty_iso_subdivision_of_completion_iso G v a b f h.1 h.2 hn hnot
  · let swap : completeBipartiteGraph (Fin 3) (Fin 3) ≃g
        completeBipartiteGraph (Fin 3) (Fin 3) :=
      { Equiv.sumComm (Fin 3) (Fin 3) with
        map_rel_iff' := by
          intro x y
          cases x <;> cases y <;> simp [completeBipartiteGraph_adj] }
    exact nonempty_iso_subdivision_of_completion_iso G v a b (f.comp swap) h.2 h.1 hn hnot

end

end SimpleGraph

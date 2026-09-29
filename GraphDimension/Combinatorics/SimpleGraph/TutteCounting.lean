/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Tutte
public import GraphDimension.Combinatorics.SimpleGraph.ComponentCardinality

/-!
# Component sizes and Tutte counts after deleting vertices

Deletion uses the subgraph's `coe`, whose vertex type contains only the surviving vertices.
-/

@[expose] public section

namespace SimpleGraph

/-- A lower bound on closed neighbourhood sizes gives an additive lower bound on every
component size after deleting vertices. -/
theorem le_ncard_add_ncard_deleteVerts_component
    {V : Type*} [Finite V] (H : SimpleGraph V) (S : Set V) {d : ℕ}
    (hmin : ∀ v, d ≤ (H.neighborSet v).ncard + 1) :
    ∀ c : ((⊤ : H.Subgraph).deleteVerts S).coe.ConnectedComponent,
      d ≤ S.ncard + c.supp.ncard := by
  intro c
  obtain ⟨v, hv⟩ := c.nonempty_supp
  have hsub : insert v.val (H.neighborSet v.val) ⊆ S ∪ Subtype.val '' c.supp := by
    intro w hw
    rcases hw with rfl | hw
    · exact Or.inr ⟨v, hv, rfl⟩
    · by_cases hwS : w ∈ S
      · exact Or.inl hwS
      · have hwverts : w ∈ ((⊤ : H.Subgraph).deleteVerts S).verts := by
          simpa using hwS
        have hadj : ((⊤ : H.Subgraph).deleteVerts S).coe.Adj v ⟨w, hwverts⟩ := by
          exact ⟨v.property, hwverts, hw⟩
        exact Or.inr ⟨⟨w, hwverts⟩, (c.mem_supp_congr_adj hadj).mp hv, rfl⟩
  have hcount := Set.ncard_le_ncard hsub
  rw [Set.ncard_insert_of_notMem H.notMem_neighborSet_self] at hcount
  have hunion := Set.ncard_union_le S (Subtype.val '' c.supp)
  rw [Set.ncard_image_of_injective _ Subtype.val_injective] at hunion
  exact (hmin v.val).trans (hcount.trans hunion)

/-- In an even-order graph, a Tutte violating set leaves at least two more odd components
than deleted vertices; the deleted vertices and odd components together fit in the order. -/
theorem IsTutteViolator.card_bounds
    {V : Type*} [Finite V] {H : SimpleGraph V} {S : Set V}
    (hS : H.IsTutteViolator S) (heven : Even (Nat.card V)) :
    S.ncard + 2 ≤
        ((⊤ : H.Subgraph).deleteVerts S).coe.oddComponents.ncard ∧
      S.ncard +
        ((⊤ : H.Subgraph).deleteVerts S).coe.oddComponents.ncard ≤ Nat.card V := by
  have hcard : S.ncard + Nat.card ((⊤ : H.Subgraph).deleteVerts S).verts = Nat.card V := by
    rw [Nat.card_coe_set_eq, Subgraph.deleteVerts_verts,
      Subgraph.verts_top, ← Set.compl_eq_univ_sdiff]
    exact Set.ncard_add_ncard_compl S
  have hpar : Odd ((⊤ : H.Subgraph).deleteVerts S).coe.oddComponents.ncard ↔
      Odd S.ncard := by
    rw [odd_ncard_oddComponents, Nat.card_coe_set_eq, Subgraph.deleteVerts_verts,
      Subgraph.verts_top, ← Set.compl_eq_univ_sdiff]
    exact Set.odd_ncard_compl_iff heven S
  have hcount := mul_ncard_le_card_of_le_ncard_connectedComponent
    ((⊤ : H.Subgraph).deleteVerts S).coe
    ((⊤ : H.Subgraph).deleteVerts S).coe.oddComponents 1
    (fun c _ => c.nonempty_supp.ncard_pos)
  simp only [one_mul] at hcount
  rw [Nat.odd_iff, Nat.odd_iff] at hpar
  unfold IsTutteViolator at hS
  omega

end SimpleGraph

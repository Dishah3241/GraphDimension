/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Combinatorics.SimpleGraph.TutteCounting
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# The empty Tutte violating set at twice the minimum closed neighbourhood size

Two odd components exhaust the graph. Each has half the vertices and is complete.
-/

@[expose] public section

namespace SimpleGraph

/-- If the empty set violates Tutte's condition in a graph on `2 * d` vertices whose
closed neighbourhoods have at least `d` vertices, the graph consists of two disjoint
cliques of odd order `d`. -/
theorem exists_two_cliques_of_isTutteViolator_empty
    {V : Type*} [Finite V] (H : SimpleGraph V) {d : ℕ}
    (hd : 0 < d) (hcard : Nat.card V = 2 * d)
    (hmin : ∀ v, d ≤ (H.neighborSet v).ncard + 1)
    (hviol : H.IsTutteViolator ∅) :
    Odd d ∧ ∃ s : Set V,
      s.ncard = d ∧ sᶜ.ncard = d ∧
      H.IsClique s ∧ H.IsClique sᶜ ∧
      ∀ u ∈ s, ∀ v ∈ sᶜ, ¬ H.Adj u v := by
  have hbounds := hviol.card_bounds (hcard ▸ even_two_mul d)
  rw [Subgraph.deleteVerts_empty] at hbounds
  simp only [Set.ncard_empty, zero_add] at hbounds
  have hcomponent := H.le_ncard_add_ncard_deleteVerts_component ∅ hmin
  rw [Subgraph.deleteVerts_empty] at hcomponent
  simp only [Set.ncard_empty, zero_add] at hcomponent
  have hcount := mul_ncard_le_card_of_le_ncard_connectedComponent
    (⊤ : H.Subgraph).coe (⊤ : H.Subgraph).coe.oddComponents d
    (fun C _ => hcomponent C)
  rw [Nat.card_congr (Subgraph.topIso (G := H)).toEquiv, hcard] at hcount
  have htwo : (⊤ : H.Subgraph).coe.oddComponents.ncard = 2 := by
    have hle := Nat.le_of_mul_le_mul_left (hcount.trans_eq (Nat.mul_comm 2 d)) hd
    omega
  obtain ⟨a, ha, b, _, hab⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp (by rw [htwo]; decide :
    1 < (⊤ : H.Subgraph).coe.oddComponents.ncard)
  let e : (⊤ : H.Subgraph).coe ≃g H := Subgraph.topIso
  let c := e.connectedComponentEquiv a
  let c' := e.connectedComponentEquiv b
  have hne : c ≠ c' := fun h => hab (e.connectedComponentEquiv.injective h)
  have hodd : Odd c.supp.ncard := by
    have heq := Nat.card_congr (a.isoEquivSupp e)
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at heq
    exact heq ▸ ha
  have hclosed (C : H.ConnectedComponent) {v : V} (hv : v ∈ C.supp) :
      insert v (H.neighborSet v) ⊆ C.supp := by
    intro w hw
    rcases hw with rfl | hw
    · exact hv
    · exact (C.mem_supp_congr_adj hw).mp hv
  have hsize (C : H.ConnectedComponent) : d ≤ C.supp.ncard := by
    obtain ⟨v, hv⟩ := C.nonempty_supp
    have hle := Set.ncard_le_ncard (hclosed C hv)
    rw [Set.ncard_insert_of_notMem H.notMem_neighborSet_self] at hle
    exact (hmin v).trans hle
  have hdisj := H.pairwise_disjoint_supp_connectedComponent hne
  have hsum : c.supp.ncard + c'.supp.ncard ≤ 2 * d := by
    rw [← Set.ncard_union_eq hdisj, ← hcard]
    exact Set.ncard_le_card _
  have hc : c.supp.ncard = d := by have := hsize c; have := hsize c'; omega
  have hc' : c'.supp.ncard = d := by have := hsize c; have := hsize c'; omega
  have hcompl : c'.supp = c.suppᶜ := by
    apply Set.eq_of_subset_of_ncard_le (ht := Set.toFinite _)
    · intro v hv hv'
      exact Set.disjoint_left.mp hdisj hv' hv
    · have := Set.ncard_add_ncard_compl c.supp
      omega
  have hclique (C : H.ConnectedComponent) (hC : C.supp.ncard = d) :
      H.IsClique C.supp := by
    intro v hv w hw hvw
    have heq : insert v (H.neighborSet v) = C.supp := by
      apply Set.eq_of_subset_of_ncard_le (hclosed C hv)
      rw [Set.ncard_insert_of_notMem H.notMem_neighborSet_self, hC]
      exact hmin v
    have hw' : w ∈ insert v (H.neighborSet v) := heq ▸ hw
    rcases hw' with rfl | hw'
    · exact (hvw rfl).elim
    · exact hw'
  refine ⟨hc ▸ hodd, c.supp, hc, ?_, hclique c hc, ?_, ?_⟩
  · rw [← hcompl, hc']
  · rw [← hcompl]
    exact hclique c' hc'
  · intro u hu v hv hadj
    exact hv ((c.mem_supp_congr_adj hadj).mp hu)

end SimpleGraph

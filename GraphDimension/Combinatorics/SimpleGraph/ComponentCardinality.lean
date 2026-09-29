/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Represents
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting vertices in connected components

Disjoint component supports bound the number of selected components. Equality in the bound
for odd components forces the graph to be edgeless.
-/

@[expose] public section

namespace SimpleGraph

/-- If each selected component has at least `k` vertices, their total size is at most the
order of the graph. -/
theorem mul_ncard_le_card_of_le_ncard_connectedComponent
    {V : Type*} [Finite V] (H : SimpleGraph V)
    (C : Set H.ConnectedComponent) (k : ℕ)
    (hk : ∀ c ∈ C, k ≤ c.supp.ncard) :
    k * C.ncard ≤ Nat.card V := by
  classical
  let := Fintype.ofFinite V
  calc
    k * C.ncard = ∑ _c ∈ C.toFinset, k := by
      rw [Finset.sum_const, ← Set.ncard_eq_toFinset_card', smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ c ∈ C.toFinset, c.supp.toFinset.card := by
      apply Finset.sum_le_sum
      intro c hc
      rw [← Set.ncard_eq_toFinset_card']
      exact hk c (Set.mem_toFinset.mp hc)
    _ = (C.toFinset.biUnion fun c => c.supp.toFinset).card := by
      symm
      apply Finset.card_biUnion
      intro c _ c' _ hne
      exact Set.disjoint_toFinset.mpr (H.pairwise_disjoint_supp_connectedComponent hne)
    _ ≤ Nat.card V := by simpa using Finset.card_le_univ _

/-- A finite graph with at least as many odd components as vertices is edgeless. -/
theorem eq_bot_of_card_le_ncard_oddComponents
    {V : Type*} [Finite V] (H : SimpleGraph V)
    (h : Nat.card V ≤ H.oddComponents.ncard) :
    H = ⊥ := by
  have hrep := ConnectedComponent.Represents.image_out H.oddComponents
  have huniv : Quot.out '' H.oddComponents = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    simpa only [Set.ncard_univ, hrep.ncard_eq] using h
  apply bot_unique
  intro v w hvw
  have heq : v = w := hrep.2.1 (by rw [huniv]; trivial) (by rw [huniv]; trivial)
    (ConnectedComponent.eq.mpr hvw.reachable)
  exact (hvw.ne heq).elim

end SimpleGraph

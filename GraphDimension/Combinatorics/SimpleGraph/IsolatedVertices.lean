/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# Padding a graph with isolated vertices

Adjoining isolated vertices to a finite graph raises the order to any prescribed `N` while
preserving a degree bound and the exclusion of a clique of order at least two. In the graph sum
with an edgeless summand, the neighbour set of a left vertex is the image of its old neighbour
set, the neighbour set of a right vertex is empty, and a clique containing a right vertex cannot
have two vertices because no edge touches a right vertex.

This is the padding half of ROADMAP P10 (FKS Problem 1 for graphs on at most twice the
dimension); its consumers reduce the bounded statement to the exact-order one.
-/

@[expose] public section

namespace SimpleGraph

/-- If `G` has at most `N` vertices and `d ≥ 1`, adjoining `N - |V|` isolated vertices gives a
graph of order exactly `N` that still has every neighbour set of size at most `d` and still has
no clique of order `d + 1`. -/
theorem card_degree_cliqueFree_sum_bot
    {V : Type*} [Finite V] (G : SimpleGraph V) {N d : ℕ}
    (hcard : Nat.card V ≤ N) (hd : 1 ≤ d)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ d)
    (hK : G.CliqueFree (d + 1)) :
    let H := G ⊕g (⊥ : SimpleGraph (Fin (N - Nat.card V)))
    Nat.card (V ⊕ Fin (N - Nat.card V)) = N ∧
      (∀ v, (H.neighborSet v).ncard ≤ d) ∧ H.CliqueFree (d + 1) := by
  classical
  have := Fintype.ofFinite V
  have hcard' : Nat.card (V ⊕ Fin (N - Nat.card V)) = N := by
    rw [Nat.card_sum, Nat.card_fin]
    omega
  have hdeg' : ∀ v : V ⊕ Fin (N - Nat.card V),
      ((G ⊕g (⊥ : SimpleGraph (Fin (N - Nat.card V)))).neighborSet v).ncard ≤ d := by
    rintro (x | w)
    · have hset : (G ⊕g (⊥ : SimpleGraph (Fin (N - Nat.card V)))).neighborSet (Sum.inl x) =
          Sum.inl '' (G.neighborSet x) := by
        ext u
        simp only [mem_neighborSet, Set.mem_image]
        cases u <;> simp
      rw [hset, Set.ncard_image_of_injective _ Sum.inl_injective]
      exact hdeg x
    · have hset : (G ⊕g (⊥ : SimpleGraph (Fin (N - Nat.card V)))).neighborSet (Sum.inr w) = ∅ := by
        ext u
        simp only [mem_neighborSet]
        cases u <;> simp
      rw [hset, Set.ncard_empty]
      exact Nat.zero_le d
  have hK' : (G ⊕g (⊥ : SimpleGraph (Fin (N - Nat.card V)))).CliqueFree (d + 1) := by
    intro t ht
    obtain ⟨hc, hcCard⟩ := ht
    have hnoright : ∀ w : Fin (N - Nat.card V), Sum.inr w ∉ t := by
      intro w hw
      have htwo : 2 ≤ t.card := by rw [hcCard]; omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
      by_cases ha' : a = Sum.inr w
      · have hneb : Sum.inr w ≠ b := fun h' => hab (ha'.trans h')
        cases b with
        | inl y => simpa using hc hw hb hneb
        | inr w' => simpa using hc hw hb hneb
      · have hnea : Sum.inr w ≠ a := fun h' => ha' h'.symm
        cases a with
        | inl y => simpa using hc hw ha hnea
        | inr w' => simpa using hc hw ha hnea
    have hall : ∀ b ∈ t, ∃ a : V, Sum.inl a = b := by
      intro b hb
      cases b with
      | inl x => exact ⟨x, rfl⟩
      | inr w => exact absurd hb (hnoright w)
    have hinj : Set.InjOn (Sum.inl : V → V ⊕ Fin (N - Nat.card V))
        (Sum.inl ⁻¹' (t : Set (V ⊕ Fin (N - Nat.card V)))) :=
      fun a _ b _ h => Sum.inl_injective h
    have hsCard : (t.preimage Sum.inl hinj).card = d + 1 := by
      rw [Finset.card_preimage t Sum.inl hinj]
      have hfilt :
          t.filter (fun x => x ∈ Set.range (Sum.inl : V → V ⊕ Fin (N - Nat.card V))) = t := by
        ext x
        simp only [Finset.mem_filter, Set.mem_range]
        refine ⟨fun hx => hx.1, fun hx => ⟨hx, hall x hx⟩⟩
      rw [hfilt, hcCard]
    have hclique : G.IsNClique (d + 1) (t.preimage Sum.inl hinj) := by
      refine ⟨?_, hsCard⟩
      intro x hx y hy hxy
      have hx' : Sum.inl x ∈ t := Finset.mem_preimage.mp hx
      have hy' : Sum.inl y ∈ t := Finset.mem_preimage.mp hy
      have hadj : (G ⊕g (⊥ : SimpleGraph (Fin (N - Nat.card V)))).Adj (Sum.inl x) (Sum.inl y) :=
        hc hx' hy' (Sum.inl_injective.ne hxy)
      simpa using hadj
    exact hK _ hclique
  exact ⟨hcard', hdeg', hK'⟩

end SimpleGraph

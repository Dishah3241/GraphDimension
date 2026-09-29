/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# A saturated clique is a connected component

In a graph of maximum degree at most `d`, a clique on `d + 1` vertices uses every neighbour
of each of its vertices. No edge leaves the clique, so reachability from any of its vertices
stays inside it, and the clique is the support of a connected component.
-/

@[expose] public section

namespace SimpleGraph

-- L1
/-- **Saturated clique is a component.**

If every vertex has at most `d` neighbours and `s` is a clique of order `d + 1`, then `s` is
the support of a connected component. Each vertex of `s` is already adjacent to the other `d`
vertices of `s`, so it has no neighbour outside `s`. -/
theorem IsNClique.exists_connectedComponent_supp_eq
    {V : Type*} [Finite V] {G : SimpleGraph V} {d : ℕ}
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ d)
    {s : Finset V} (hs : G.IsNClique (d + 1) s) :
    ∃ c : G.ConnectedComponent, c.supp = (s : Set V) := by
  classical
  -- Neighbours of a clique vertex are exactly the other vertices of the clique.
  have hnbhd {v : V} (hv : v ∈ s) : G.neighborSet v = ↑(s.erase v) := by
    have hsub : (↑(s.erase v) : Set V) ⊆ G.neighborSet v := by
      intro w hw
      simp only [Finset.mem_coe, Finset.mem_erase] at hw
      exact hs.isClique (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hw.2) hw.1.symm
    have hcard : (↑(s.erase v) : Set V).ncard = d := by
      rw [Set.ncard_coe_finset, Finset.card_erase_of_mem hv, hs.card_eq, Nat.add_sub_cancel]
    have hle : (G.neighborSet v).ncard ≤ (↑(s.erase v) : Set V).ncard := by
      rw [hcard]
      exact hdeg v
    exact (Set.eq_of_subset_of_ncard_le hsub hle).symm
  have hclosed {v w : V} (hv : v ∈ s) (hadj : G.Adj v w) : w ∈ s := by
    have hw : w ∈ G.neighborSet v := hadj
    rw [hnbhd hv] at hw
    exact Finset.mem_of_mem_erase (Finset.mem_coe.mp hw)
  -- A walk that starts in `s` cannot leave it.
  have hreach {u w : V} (hu : u ∈ s) (h : G.Reachable u w) : w ∈ s := by
    rw [reachable_eq_reflTransGen] at h
    induction h with
    | refl => exact hu
    | tail _ hadj ih => exact hclosed ih hadj
  have hspos : 0 < s.card := by rw [hs.card_eq]; omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hspos
  refine ⟨G.connectedComponentMk v, ?_⟩
  ext w
  constructor
  · intro hw
    rw [ConnectedComponent.mem_supp_iff] at hw
    exact Finset.mem_coe.mpr (hreach hv (ConnectedComponent.exact hw.symm))
  · intro hw
    rw [ConnectedComponent.mem_supp_iff, eq_comm, ConnectedComponent.eq]
    obtain rfl | hne := eq_or_ne v w
    · exact Reachable.rfl
    · exact (hs.isClique (Finset.mem_coe.mpr hv) hw hne).reachable

end SimpleGraph

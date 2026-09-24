/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Sphere.Extend
import Mathlib.Data.Finset.Max

/-!
# A maximal core for simultaneous deletion and reattachment

Taking a core containing every induced subgraph of the required minimum degree lets the
same core control reattachment after deleting one of its vertices, as required in Branch B.
-/

@[expose] public section

namespace SimpleGraph

open Finset

/-- There is a core containing every vertex set of minimum degree greater than `k`. -/
theorem exists_core_maximal {V : Type*} [Finite V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (k : ℕ) :
    ∃ s : Finset V, (∀ v ∈ s, k < (s.filter (G.Adj v)).card) ∧
      ∀ t : Finset V, (∀ v ∈ t, k < (t.filter (G.Adj v)).card) → t ⊆ s := by
  classical
  let _ := Fintype.ofFinite V
  let C := (univ : Finset (Finset V)).filter fun t =>
    ∀ v ∈ t, k < (t.filter (G.Adj v)).card
  have hC : C.Nonempty := ⟨∅, by simp [C]⟩
  obtain ⟨s, hs, hmax⟩ := C.exists_max_image card hC
  have hsdeg := (mem_filter.mp hs).2
  refine ⟨s, hsdeg, ?_⟩
  intro t ht
  have hU : s ∪ t ∈ C := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact (hsdeg v hv).trans_le (card_le_card (filter_subset_filter _ subset_union_left))
    · exact (ht v hv).trans_le (card_le_card (filter_subset_filter _ subset_union_right))
  have heq : s = s ∪ t := eq_of_subset_of_card_le subset_union_left (hmax _ hU)
  rw [heq]
  exact subset_union_right

/-- A placement of a maximal core extends inside any vertex set that contains it. -/
theorem SphereEmbeddable.of_core_maximal {V : Type*} [Finite V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hd : 2 ≤ d) {s : Finset V}
    (hmax : ∀ t : Finset V, (∀ v ∈ t, d - 2 < (t.filter (G.Adj v)).card) → t ⊆ s)
    (h : (G.induce (s : Set V)).SphereEmbeddable d) : G.SphereEmbeddable d := by
  classical
  obtain ⟨c, hc, hext⟩ := SphereEmbeddable.exists_core (G := G) hd
  apply hext
  let f : G.induce (c : Set V) →g G.induce (s : Set V) :=
    { toFun := fun v => ⟨v.val, hmax c hc v.property⟩
      map_rel' := fun h => h }
  exact h.comap f (fun _ _ he => Subtype.ext
    (congrArg (fun z : ↥(s : Set V) => z.val) he))

end SimpleGraph

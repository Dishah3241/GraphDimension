/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Combinatorics.SimpleGraph.Core

import Mathlib.Tactic.FinCases

/-!
# The core of `K₄` with a pendant vertex

`K₄` on vertices `{0, 1, 2, 3}` with vertex `4` pendant at `0`, at level `k = 2`: the core is
exactly the `K₄`. Every `c` satisfying the core property of `SimpleGraph.exists_core` contains
the four `K₄` vertices — a set missing one of them cannot re-attach it, because a missing `K₄`
vertex still has three neighbours present, more than `k` — and no core contains the pendant,
whose single neighbour cannot exceed `k`. The `K₄` itself satisfies the core property and is a
proper subset of the vertex set, so the example is nondegenerate: the core is neither empty nor
everything. This separates `exists_core` from its two degenerate readings, `c = ∅` and
`c = Finset.univ`.
-/

@[expose] public section

namespace SimpleGraph

open Finset

/-- The four `K₄` vertices. -/
def k4Vertices : Finset (Fin 5) := {0, 1, 2, 3}

/-- `K₄` on vertices `0, 1, 2, 3` with vertex `4` pendant at `0`. -/
def k4Pendant : SimpleGraph (Fin 5) where
  Adj i j := (i ≠ 4 ∧ j ≠ 4 ∧ i ≠ j) ∨ (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0)
  symm := ⟨fun _ _ h => by
    rcases h with (⟨hi, hj, hij⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨hj, hi, Ne.symm hij⟩
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  loopless := ⟨fun _ h => by
    rcases h with (⟨-, -, hij⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hij rfl
    · subst h1
      exact absurd h2 (by decide)
    · subst h1
      exact absurd h2 (by decide)⟩

instance : DecidableRel k4Pendant.Adj := fun _ _ =>
  inferInstanceAs (Decidable
    ((_ ≠ 4 ∧ _ ≠ 4 ∧ _ ≠ _) ∨ (_ = 0 ∧ _ = 4) ∨ (_ = 4 ∧ _ = 0)))

@[simp] lemma mem_k4Vertices {j : Fin 5} : j ∈ k4Vertices ↔ j ≠ 4 := by
  fin_cases j <;> simp [k4Vertices]

lemma k4Pendant_adj (i j : Fin 5) :
    k4Pendant.Adj i j ↔ (i ≠ 4 ∧ j ≠ 4 ∧ i ≠ j) ∨ (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) :=
  Iff.rfl

lemma adj_of_mem_k4Vertices {i j : Fin 5} (hi : i ∈ k4Vertices) (hj : j ∈ k4Vertices)
    (hne : i ≠ j) : k4Pendant.Adj i j := by
  rw [k4Pendant_adj]
  exact Or.inl ⟨mem_k4Vertices.mp hi, mem_k4Vertices.mp hj, hne⟩

/-- Every set containing the other three `K₄` vertices gives a `K₄` vertex at least three
neighbours inside it. -/
lemma three_le_card_filter_adj {s : Finset (Fin 5)} {i : Fin 5} (hi : i ∈ k4Vertices)
    (hs : k4Vertices.erase i ⊆ s) : 3 ≤ (s.filter (k4Pendant.Adj i)).card := by
  have hcard : (k4Vertices.erase i).card = 3 := by
    rw [card_erase_of_mem hi]
    simp [k4Vertices]
  calc 3 = (k4Vertices.erase i).card := hcard.symm
    _ ≤ (s.filter (k4Pendant.Adj i)).card := by
        refine card_le_card ?_
        intro y hy
        obtain ⟨hy1, hy2⟩ := mem_erase.mp hy
        exact mem_filter.mpr ⟨hs hy, adj_of_mem_k4Vertices hi hy2 (Ne.symm hy1)⟩

/-- No core contains the pendant vertex: it has only the one neighbour `0`, so it can never
have more than `k = 2` neighbours inside any set. -/
lemma four_notMem_of_core {c : Finset (Fin 5)}
    (hcore : ∀ v ∈ c, 2 < (c.filter (k4Pendant.Adj v)).card) : (4 : Fin 5) ∉ c := by
  intro h4
  have hsub : (c.filter (k4Pendant.Adj 4)).card ≤ ({0} : Finset (Fin 5)).card :=
    card_le_card (by
      intro y hy
      obtain ⟨-, hyadj⟩ := mem_filter.mp hy
      rw [k4Pendant_adj] at hyadj
      rcases hyadj with (⟨h, -, -⟩ | ⟨h1, -⟩ | ⟨-, h⟩)
      · exact absurd rfl h
      · exact absurd h1 (by decide)
      · rw [Finset.mem_singleton]
        exact h)
  have hbig := hcore 4 h4
  have h1 : (c.filter (k4Pendant.Adj 4)).card ≤ 1 := by simpa using hsub
  omega

/-- The re-attachment step for `P s := ¬(k4Vertices ⊆ s)`: re-inserting a vertex with at most
two neighbours present cannot make the set contain all four `K₄` vertices. -/
lemma step_not_subset_k4 (s : Finset (Fin 5)) (x : Fin 5) (hxs : x ∉ s)
    (hle : (s.filter (k4Pendant.Adj x)).card ≤ 2) (hsub : ¬(k4Vertices ⊆ s)) :
    ¬(k4Vertices ⊆ insert x s) := by
  intro hins
  rcases eq_or_ne x 4 with rfl | hx4
  · -- `x` is the pendant: the four `K₄` vertices were already in `s`
    refine hsub (fun y hy => ?_)
    rcases Finset.mem_insert.mp (hins hy) with h' | h'
    · exact absurd h' (mem_k4Vertices.mp hy)
    · exact h'
  · -- `x` is a `K₄` vertex: the other three are in `s`, giving `x` three neighbours there
    have hxK : x ∈ k4Vertices := by
      by_contra hx
      refine hsub (fun y hy => ?_)
      rcases Finset.mem_insert.mp (hins hy) with h' | h'
      · subst h'
        exact absurd hy hx
      · exact h'
    have h3 : 3 ≤ (s.filter (k4Pendant.Adj x)).card :=
      three_le_card_filter_adj hxK (by
        intro y hy
        obtain ⟨hy1, hy2⟩ := mem_erase.mp hy
        rcases Finset.mem_insert.mp (hins hy2) with h' | h'
        · exact absurd h' hy1
        · exact h')
    omega

/-- **The core of `K₄` with a pendant vertex is the `K₄`.** Every `c` satisfying the core
property of `SimpleGraph.exists_core` at `k = 2` — every vertex of `c` with more than two
neighbours inside `c`, together with the re-attachment conclusion for every admissible `P` —
equals the four `K₄` vertices. -/
theorem core_eq_k4Vertices (c : Finset (Fin 5))
    (hcore : ∀ v ∈ c, 2 < (c.filter (k4Pendant.Adj v)).card)
    (hattach : ∀ ⦃P : Finset (Fin 5) → Prop⦄,
      (∀ s x, x ∉ s → (s.filter (k4Pendant.Adj x)).card ≤ 2 → P s → P (insert x s)) →
        P c → P Finset.univ) :
    c = k4Vertices := by
  have h4 : (4 : Fin 5) ∉ c := four_notMem_of_core hcore
  have hKsub : k4Vertices ⊆ c := by
    by_contra hyC
    exact (hattach (P := fun s => ¬(k4Vertices ⊆ s)) step_not_subset_k4 hyC) (subset_univ _)
  refine subset_antisymm ?_ hKsub
  intro y hy
  refine mem_k4Vertices.mpr ?_
  rcases eq_or_ne y 4 with rfl | hy4
  · exact absurd hy h4
  · exact hy4

/-- Applying `SimpleGraph.exists_core` to `k4Pendant` at `k = 2` with
`P s := ¬(k4Vertices ⊆ s)`: the core it returns contains all four `K₄` vertices and excludes
the pendant vertex. -/
theorem exists_core_k4Pendant :
    ∃ c : Finset (Fin 5),
      (∀ v ∈ c, 2 < (c.filter (k4Pendant.Adj v)).card) ∧
        k4Vertices ⊆ c ∧ (4 : Fin 5) ∉ c := by
  obtain ⟨c, hcore, hP⟩ :=
    k4Pendant.exists_core 2 (fun s => ¬(k4Vertices ⊆ s)) step_not_subset_k4
  refine ⟨c, hcore, ?_, four_notMem_of_core hcore⟩
  by_contra h
  exact (hP h) (subset_univ k4Vertices)

/-- The `K₄` itself satisfies the core property at `k = 2`, and it is a proper subset of the
vertex set: the core in this example is neither empty nor everything. -/
theorem k4Vertices_is_core :
    (∀ v ∈ k4Vertices, 2 < (k4Vertices.filter (k4Pendant.Adj v)).card) ∧
      k4Vertices ≠ Finset.univ := by
  refine ⟨fun v hv => ?_, ?_⟩
  · have h3 : 3 ≤ (k4Vertices.filter (k4Pendant.Adj v)).card :=
      three_le_card_filter_adj hv (erase_subset v k4Vertices)
    omega
  · intro h
    have h4 : (4 : Fin 5) ∈ k4Vertices := by
      rw [h]
      exact Finset.mem_univ 4
    exact absurd h4 (by simp [k4Vertices])

end SimpleGraph

/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Card

/-!
# The `(k + 1)`-core as a re-attachment principle

Repeatedly delete a vertex with at most `k` neighbours among those not yet deleted. What
remains, the `(k + 1)`-core, has every vertex with more than `k` neighbours inside it, and the
deleted vertices re-attach one at a time in reverse order: any hypothesis `P` preserved by
re-inserting a vertex with at most `k` already-present neighbours propagates from the core to
all vertices (`SimpleGraph.exists_core`).

The construction is relative to a starting vertex set (`SimpleGraph.exists_core_subset`,
proved by strong induction on the starting set), and the absolute version applies it to
`Finset.univ`.

Two facts the consumers use about any core `c`: the subgraph induced by `c` has no more edges
than `G` (`SimpleGraph.induce_edgeFinset_card_le`), and when `G` is `k`-degenerate the core is
forced to be empty, so `P` propagates from `∅` to all vertices
(`SimpleGraph.exists_core_of_degenerate`).

## Source

Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, proof of Theorem 3,
first paragraph (`main.tex` lines 346–348): remove vertices of degree at most `d - 2` one by
one; if nothing remains the graph is `(d - 2)`-degenerate, otherwise a subgraph of minimum
degree at least `d - 1` remains and the deleted vertices re-attach one at a time.
-/

@[expose] public section

namespace SimpleGraph

open Finset

variable {V : Type*} [DecidableEq V]

/-- **Relative core.** Inside any vertex set `t` there is a subset `c` in which every vertex
has more than `k` neighbours, and any `P` preserved by re-inserting a vertex with at most `k`
neighbours among those already present propagates from `c` to `t`: run the deletion inside `t`
until it stops, then re-attach in reverse order. -/
theorem exists_core_subset {G : SimpleGraph V} [DecidableRel G.Adj] (k : ℕ)
    (P : Finset V → Prop)
    (hstep : ∀ s x, x ∉ s → (s.filter (G.Adj x)).card ≤ k → P s → P (insert x s))
    (t : Finset V) :
    ∃ c ⊆ t, (∀ v ∈ c, k < (c.filter (G.Adj v)).card) ∧ (P c → P t) := by
  induction t using Finset.strongInductionOn with
  | _ t ih =>
    by_cases hex : ∃ x ∈ t, (t.filter (G.Adj x)).card ≤ k
    · obtain ⟨x, hx, hdeg⟩ := hex
      have hdeg' : ((t.erase x).filter (G.Adj x)).card ≤ k := by
        refine le_trans (card_le_card (filter_subset_filter (G.Adj x) (erase_subset x t))) hdeg
      obtain ⟨c, hcsub, hcore, hP⟩ := ih (t.erase x) (erase_ssubset hx)
      refine ⟨c, subset_trans hcsub (erase_subset x t), hcore, ?_⟩
      intro hcP
      rw [← insert_erase hx]
      exact hstep _ x (notMem_erase x t) hdeg' (hP hcP)
    · refine ⟨t, subset_rfl, ?_, id⟩
      intro v hv
      by_contra hlt
      exact hex ⟨v, hv, Nat.not_lt.mp hlt⟩

/-- **The `(k + 1)`-core.** Some vertex set `c` has every vertex with more than `k` neighbours
inside `c`, and any `P` preserved by re-inserting a vertex with at most `k` present neighbours
propagates from `c` to all vertices: the deleted vertices re-attach one at a time in reverse
order. -/
theorem exists_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (P : Finset V → Prop)
    (hstep : ∀ s x, x ∉ s → (s.filter (G.Adj x)).card ≤ k → P s → P (insert x s)) :
    ∃ c : Finset V, (∀ v ∈ c, k < (c.filter (G.Adj v)).card) ∧ (P c → P Finset.univ) := by
  obtain ⟨c, -, hcore, hP⟩ := exists_core_subset k P hstep Finset.univ
  exact ⟨c, hcore, hP⟩

/-- The edges with both ends in `c` are among all the edges: the induced subgraph `G.induce c`,
coarsened back to a graph on all of `V` by `spanningCoe`, has at most `e(G)` edges. The two
edge counts `e(G.induce c)` and `e((G.induce c).spanningCoe)` agree, since coarsening maps each
induced edge to the same unordered pair in `Sym2 V`. -/
theorem induce_edgeFinset_card_le {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype V]
    (c : Finset V) :
    (G.induce (c : Set V)).spanningCoe.edgeFinset.card ≤ G.edgeFinset.card := by
  classical
  refine card_le_card ?_
  intro e he
  rw [mem_edgeFinset] at he ⊢
  rw [edgeSet_map, Set.mem_image] at he
  obtain ⟨e', he', rfl⟩ := he
  rw [Function.Embedding.sym2Map_apply]
  induction e' using Sym2.inductionOn with
  | _ u w =>
    rw [Sym2.map_mk, mem_edgeSet]
    rw [mem_edgeSet] at he'
    exact induce_adj.mp he'

omit [DecidableEq V] in
/-- `k`-degeneracy of `G`, in the form the deletion process uses: every nonempty vertex set
contains a vertex with at most `k` neighbours inside it. Then no vertex set has all its
vertices with more than `k` neighbours inside, i.e. the core is empty. -/
theorem eq_empty_of_degenerate {G : SimpleGraph V} [DecidableRel G.Adj] (k : ℕ)
    (hdeg : ∀ s : Finset V, s.Nonempty → ∃ x ∈ s, (s.filter (G.Adj x)).card ≤ k)
    {c : Finset V} (hcore : ∀ v ∈ c, k < (c.filter (G.Adj v)).card) :
    c = ∅ := by
  rcases eq_empty_or_nonempty c with hc | hc
  · exact hc
  · obtain ⟨x, hx, hle⟩ := hdeg c hc
    exact absurd hle (Nat.not_le.mpr (hcore x hx))

/-- **Degenerate case.** If `G` is `k`-degenerate, the core is empty, so any `P` as above
propagates from `∅` to all vertices: the deleted vertices re-attach one at a time, starting
from nothing. -/
theorem exists_core_of_degenerate {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] (k : ℕ)
    (P : Finset V → Prop)
    (hstep : ∀ s x, x ∉ s → (s.filter (G.Adj x)).card ≤ k → P s → P (insert x s))
    (hP0 : P ∅)
    (hdeg : ∀ s : Finset V, s.Nonempty → ∃ x ∈ s, (s.filter (G.Adj x)).card ≤ k) :
    P Finset.univ := by
  obtain ⟨c, -, hcore, hP⟩ := exists_core_subset k P hstep Finset.univ
  have hPc : P c := by rw [eq_empty_of_degenerate k hdeg hcore]; exact hP0
  exact hP hPc

end SimpleGraph

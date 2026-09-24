/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Geometry.CompleteGraph
public import GraphDimension.Geometry.Extend
public import GraphDimension.Geometry.UnitDistanceComap

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith

/-!
# Attaching vertices over cliques (Lemma P)

If each vertex outside `s` has a clique for its
neighbourhood, and each has at most `d − 1` neighbours, then a unit-distance placement of
`G.induce s` in `ℝᵈ` extends to one of `G` (`UnitDistEmbeddable.extend_of_clique_neighbors`).

The outside vertices re-attach one at a time. When a vertex `u` joins the placed set `t`, the
neighbours of `u` that lie in `insert u t` still form a clique — a subset of `G.neighborSet u`,
which is a clique because `u ∉ s` — and still have cardinality at most `d − 1`; deleting `u`
from `G.induce (insert u t)` leaves exactly `G.induce t`, so `UnitDistEmbeddable.extend`
applies. The neighbour sets of different outside vertices may overlap (the A37 correction to
the Stage 0 sketch): each re-attachment constrains only the new point, so nothing is lost.
Rung 4 uses this for Branch B's second case, where the core is `K_{d+1}`, every clique vertex
has exactly one outside neighbour, and every outside vertex's neighbours all lie in the clique.

The example `k4TwoApex` is the least nondegenerate instance: `K₄` in `ℝ³`, with two outside
vertices each joined to the same two clique vertices.
-/

namespace SimpleGraph

/-- The empty vertex set induces a graph whose vertex type is empty, which has a unit-distance
placement in every dimension. -/
private lemma unitDist_induce_empty {V : Type*} (G : SimpleGraph V) (d : ℕ) :
    (G.induce (∅ : Set V)).UnitDistEmbeddable d := by
  have : IsEmpty {v // v ∈ (∅ : Set V)} := ⟨fun v => Set.notMem_empty v.1 v.2⟩
  exact ⟨fun v => isEmptyElim v, fun a b _ => isEmptyElim a, fun a b _ => isEmptyElim a⟩

/-- One re-attachment step: a vertex `u` outside the placed set `t` joins it, where `s ⊆ t` is
the seed of the induction.

The neighbours of `u` inside `insert u t` form a clique — a subset of `G.neighborSet u`, which
is a clique because `u ∉ s` — and their cardinality is at most `(G.neighborSet u).ncard`, so
`UnitDistEmbeddable.extend` re-attaches `u`. Deleting `u` from `G.induce (insert u t)` leaves a
graph isomorphic to `G.induce t`, via the injective homomorphism forgetting the `insert u t`
membership component. -/
private lemma extend_step_of_clique_neighbors {V : Type*} [Finite V] {G : SimpleGraph V} {d : ℕ}
    {s t : Set V} {u : V} (hst : s ⊆ t) (hu : u ∉ t)
    (hclique : ∀ a, a ∉ s → G.IsClique (G.neighborSet a))
    (hdeg : ∀ a, a ∉ s → (G.neighborSet a).ncard + 1 ≤ d)
    (h : (G.induce t).UnitDistEmbeddable d) :
    (G.induce (insert u t)).UnitDistEmbeddable d := by
  classical
  have hus : u ∉ s := fun hmem => hu (hst hmem)
  have hfinst : (insert u t).Finite := Set.toFinite _
  have : Finite {v : V // v ∈ insert u t} := hfinst.to_subtype
  let H := G.induce (insert u t)
  let x : {v : V // v ∈ insert u t} := ⟨u, (Set.mem_insert_iff).mpr (Or.inl rfl)⟩
  have hclique' : H.IsClique (H.neighborSet x) := by
    intro v hv w hw hvw
    rw [mem_neighborSet] at hv hw
    have hxb : ↑x = u := rfl
    have hxv : G.Adj u v.1 := by
      have := induce_adj.mp hv
      rwa [hxb] at this
    have hxw : G.Adj u w.1 := by
      have := induce_adj.mp hw
      rwa [hxb] at this
    have hv' : v.1 ∈ G.neighborSet u := (mem_neighborSet G u v.1).mpr hxv
    have hw' : w.1 ∈ G.neighborSet u := (mem_neighborSet G u w.1).mpr hxw
    exact hclique u hus hv' hw' fun hxy => hvw (Subtype.ext hxy)
  have hncard : (H.neighborSet x).ncard ≤ (G.neighborSet u).ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun w : {v : V // v ∈ insert u t} => (w : V))
      (s := H.neighborSet x) (t := G.neighborSet u) ?_ ?_ (Set.toFinite _)
    · intro y hy
      rw [mem_neighborSet] at hy
      exact (mem_neighborSet G u ↑y).mpr (induce_adj.mp hy)
    · intro a _ b _ hab
      exact Subtype.ext hab
  have hk : (H.neighborSet x).ncard + 1 ≤ d := by
    have h1 := hdeg u hus
    omega
  have herase : (H.induce {v : {w : V // w ∈ insert u t} | v ≠ x}).UnitDistEmbeddable d := by
    let φ : (H.induce {v | v ≠ x}) →g G.induce t := {
      toFun := fun v => ⟨v.1.1, by
        rcases Set.mem_insert_iff.mp v.1.2 with hv | hv
        · exact absurd (Subtype.ext hv) v.2
        · exact hv⟩
      map_rel' := fun {a b} hab => by
        have h1 : G.Adj a.1.1 b.1.1 := induce_adj.mp (induce_adj.mp hab)
        exact h1
    }
    have hφ : Function.Injective φ := by
      intro a b hab
      have hval : (φ a).1 = (φ b).1 := congrArg (fun z : {w : V // w ∈ t} => (z : V)) hab
      exact Subtype.ext (Subtype.ext hval)
    exact h.comap φ hφ
  exact UnitDistEmbeddable.extend hclique' hk herase

/-- The finite set `r` of not-yet-placed vertices shrinks; placed vertices are `univ \ r`.
Every vertex of `r` is outside `s` (the sets are disjoint), so each deleted vertex re-attaches
over the placement of the set it joins. -/
private lemma extend_clique_neighbors_rec {V : Type*} [Finite V] {G : SimpleGraph V} {d : ℕ}
    {s : Set V} (hclique : ∀ a, a ∉ s → G.IsClique (G.neighborSet a))
    (hdeg : ∀ a, a ∉ s → (G.neighborSet a).ncard + 1 ≤ d)
    (r : Set V) (hr : r.Finite) :
    s ∩ r = ∅ →
    (G.induce (Set.univ \ r)).UnitDistEmbeddable d →
      (G.induce Set.univ).UnitDistEmbeddable d := by
  refine Set.Finite.induction_on (motive := fun r _ => s ∩ r = ∅ →
    (G.induce (Set.univ \ r)).UnitDistEmbeddable d →
      (G.induce Set.univ).UnitDistEmbeddable d) r hr ?_ ?_
  · intro _ h
    have hEq : (Set.univ \ (∅ : Set V)) = Set.univ := by
      ext x
      simp
    rwa [hEq] at h
  · intro a r har _ ih hdisj h
    have hnotMem : ∀ x ∈ s ∩ insert a r, False := fun x hx => by
      rw [hdisj] at hx
      exact hx
    have hdisjr : s ∩ r = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx =>
        hnotMem x ⟨hx.1, Set.mem_insert_of_mem _ hx.2⟩
    have harS : a ∉ s := fun ha =>
      hnotMem a ⟨ha, (Set.mem_insert_iff).mpr (Or.inl rfl)⟩
    -- the placed set before `a` joins it
    have hst : s ⊆ Set.univ \ insert a r := by
      intro x hx
      refine ⟨Set.mem_univ x, fun hxin => ?_⟩
      rcases Set.mem_insert_iff.mp hxin with hxv | hxv
      · subst hxv
        exact harS hx
      · exact hnotMem x ⟨hx, Set.mem_insert_of_mem _ hxv⟩
    have hu : a ∉ Set.univ \ insert a r := fun hmem =>
      ((Set.mem_sdiff _).mp hmem).2 ((Set.mem_insert_iff).mpr (Or.inl rfl))
    have hstep := extend_step_of_clique_neighbors (V := V) (G := G) (d := d) (s := s)
      (t := Set.univ \ insert a r) (u := a) hst hu hclique hdeg h
    have hins : insert a (Set.univ \ insert a r) = Set.univ \ r := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_univ, true_and]
      refine ⟨fun hor => ?_, fun hx => ?_⟩
      · rcases hor with rfl | h
        · exact har
        · exact fun hx' => h (Or.inr hx')
      · by_cases hxa : x = a
        · exact Or.inl hxa
        · refine Or.inr fun hor => ?_
          rcases hor with h1 | h1
          · exact hxa h1
          · exact hx h1
    rw [hins] at hstep
    exact ih hdisjr hstep

@[expose] public section

/-- **Lemma P.** New vertices, each joined to at most `d − 1` vertices
of the placed part, which are pairwise adjacent, re-attach in `ℝᵈ`.

The seed `s` has a unit-distance placement in `ℝᵈ` (`hs`). Each outside vertex `u ∉ s` has a
clique neighbourhood (`hclique`) and at most `d − 1` of them (`hdeg`, in the truncation-free
form `ncard + 1 ≤ d`). The neighbour sets may overlap, and outside vertices may even be
adjacent to each other. Blueprint node `lem:simplex-attach`, as revised by A37; design row
`UnitDistEmbeddable.extend_simplex`.

The proof re-attaches one vertex at a time with `UnitDistEmbeddable.extend`; the clique
condition is read inside the graph where the vertex is added. The brief also assumed the outside
vertices pairwise non-adjacent; the proof does not need it, so the statement omits it. -/
theorem UnitDistEmbeddable.extend_of_clique_neighbors {V : Type*} [Finite V] {G : SimpleGraph V}
    {d : ℕ} (s : Set V) (hs : (G.induce s).UnitDistEmbeddable d)
    (hclique : ∀ u, u ∉ s → G.IsClique (G.neighborSet u))
    (hdeg : ∀ u, u ∉ s → (G.neighborSet u).ncard + 1 ≤ d) : G.UnitDistEmbeddable d := by
  classical
  have hdisj0 : s ∩ (Set.univ \ s) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_univ, true_and, Set.notMem_empty]
    tauto
  have hEq : Set.univ \ (Set.univ \ s) = s := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_univ, true_and]
    tauto
  have hplace : (G.induce (Set.univ \ (Set.univ \ s))).UnitDistEmbeddable d := by
    rw [hEq]
    exact hs
  exact (UnitDistEmbeddable.of_iso (induceUnivIso G)).mp
    (extend_clique_neighbors_rec hclique hdeg (Set.univ \ s) (Set.toFinite _) hdisj0 hplace)

section Example

/-! ### The example: `K₄` in `ℝ³` with two outside vertices over the same edge -/

/-- Adjacency of the example graph: `K₄` on `0, 1, 2, 3`, with `4` and `5` each joined to
exactly `0` and `1`, and `4, 5` not adjacent to each other. -/
private def k4TwoApexAdj (i j : Fin 6) : Prop :=
  (i < 4 ∧ j < 4 ∧ i ≠ j) ∨ (i ≤ 1 ∧ 4 ≤ j) ∨ (4 ≤ i ∧ j ≤ 1)

private lemma k4TwoApexAdj_symm {i j : Fin 6} (h : k4TwoApexAdj i j) : k4TwoApexAdj j i := by
  rcases h with ⟨h1, h2, h3⟩ | h | h
  · exact Or.inl ⟨h2, h1, Ne.symm h3⟩
  · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
  · exact Or.inr (Or.inl ⟨h.2, h.1⟩)

private lemma k4TwoApexAdj_loopless {i : Fin 6} : ¬ k4TwoApexAdj i i := by
  rintro (⟨-, -, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact h3 rfl
  · omega
  · omega

/-- `K₄` on vertices `0, 1, 2, 3`, with `4` and `5` each joined to exactly `0` and `1`.
The two outside vertices share their neighbour set, which is the overlap case of A37. -/
private def k4TwoApex : SimpleGraph (Fin 6) where
  Adj := k4TwoApexAdj
  symm := ⟨fun _ _ h => k4TwoApexAdj_symm h⟩
  loopless := ⟨fun _ h => k4TwoApexAdj_loopless h⟩

private lemma k4TwoApex_adj (i j : Fin 6) :
    k4TwoApex.Adj i j ↔ (i < 4 ∧ j < 4 ∧ i ≠ j) ∨ (i ≤ 1 ∧ 4 ≤ j) ∨ (4 ≤ i ∧ j ≤ 1) :=
  Iff.rfl

/-- The `K₄` vertices. -/
private def k4TwoApexClique : Set (Fin 6) := {0, 1, 2, 3}

@[simp] private lemma mem_k4TwoApexClique {j : Fin 6} :
    j ∈ k4TwoApexClique ↔ j ≠ 4 ∧ j ≠ 5 := by
  fin_cases j <;> simp [k4TwoApexClique]

private lemma notMem_k4TwoApexClique {u : Fin 6} (hu : u ∉ k4TwoApexClique) :
    u = 4 ∨ u = 5 := by
  fin_cases u <;> simp [mem_k4TwoApexClique] at hu ⊢

private lemma k4TwoApex_out_edge {u a : Fin 6} (hu : u ∉ k4TwoApexClique)
    (h : k4TwoApex.Adj u a) : a ≤ 1 ∧ 4 ≤ u := by
  rw [k4TwoApex_adj] at h
  rcases h with ⟨h1, -, -⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases notMem_k4TwoApexClique hu with hh | hh <;> rw [hh] at h1 <;> omega
  · rcases notMem_k4TwoApexClique hu with hh | hh <;> rw [hh] at h1 <;> omega
  · exact ⟨h2, h1⟩

/-- The induced subgraph on the `K₄` vertices is complete, hence has a unit-distance placement
in `ℝ³`, pulled back from `unitDistEmbeddable_completeGraph` along the relabelling. -/
private lemma unitDist_induce_k4TwoApexClique :
    (k4TwoApex.induce k4TwoApexClique).UnitDistEmbeddable 3 := by
  let φ : (k4TwoApex.induce k4TwoApexClique) →g (⊤ : SimpleGraph (Fin 4)) := {
    toFun := fun v => ⟨(v.1.1 : ℕ), by
      have hv := mem_k4TwoApexClique.mp v.2
      omega⟩
    map_rel' := fun {a b} hab => by
      refine Iff.mpr (top_adj _ _) fun hcon => hab.ne ?_
      exact Subtype.ext (Fin.ext (congrArg (fun z : Fin 4 => (z : ℕ)) hcon))
  }
  have hφ : Function.Injective φ := by
    intro a b hab
    have hval : (φ a : ℕ) = (φ b : ℕ) := congrArg (fun z : Fin 4 => (z : ℕ)) hab
    exact Subtype.ext (Fin.ext hval)
  exact (unitDistEmbeddable_completeGraph 4).comap φ hφ

/-- The outside vertices of `k4TwoApex` are pairwise non-adjacent. -/
private lemma k4TwoApex_out_not_adj (u v : Fin 6) (hu : u ∉ k4TwoApexClique)
    (hv : v ∉ k4TwoApexClique) : ¬ k4TwoApex.Adj u v := by
  intro h
  obtain ⟨ha, hua⟩ := k4TwoApex_out_edge hu h
  obtain ⟨hb, hvb⟩ := k4TwoApex_out_edge hv h.symm
  omega

/-- Each outside vertex's neighbours are exactly `0` and `1`, a clique. -/
private lemma k4TwoApex_clique_neighbors (u : Fin 6) (hu : u ∉ k4TwoApexClique) :
    k4TwoApex.IsClique (k4TwoApex.neighborSet u) := by
  intro a ha b hb hab
  rw [mem_neighborSet] at ha hb
  obtain ⟨ha1, -⟩ := k4TwoApex_out_edge hu ha
  obtain ⟨hb1, -⟩ := k4TwoApex_out_edge hu hb
  rw [k4TwoApex_adj]
  refine Or.inl ⟨Fin.lt_def.mpr ?_, Fin.lt_def.mpr ?_, hab⟩
  · have h1 : (a : ℕ) ≤ 1 := Fin.le_def.mp ha1
    omega
  · have h1 : (b : ℕ) ≤ 1 := Fin.le_def.mp hb1
    omega

/-- Each outside vertex has exactly the two neighbours `0` and `1`, so `2 + 1 ≤ 3`. -/
private lemma k4TwoApex_deg (u : Fin 6) (hu : u ∉ k4TwoApexClique) :
    (k4TwoApex.neighborSet u).ncard + 1 ≤ 3 := by
  have hsub : k4TwoApex.neighborSet u ⊆ ({0, 1} : Set (Fin 6)) := by
    intro v hv
    rw [mem_neighborSet] at hv
    obtain ⟨h1, -⟩ := k4TwoApex_out_edge hu hv
    have hv1 : (v : ℕ) ≤ 1 := Fin.le_def.mp h1
    have hv0 : v = 0 ∨ v = 1 := by
      have h2 : (v : ℕ) = 0 ∨ (v : ℕ) = 1 := by omega
      rcases h2 with h | h
      · exact Or.inl (Fin.eq_of_val_eq h)
      · exact Or.inr (Fin.eq_of_val_eq h)
    rcases hv0 with h | h
    · rw [h]
      exact Set.mem_insert 0 {1}
    · rw [h]
      exact Set.mem_insert_of_mem 0 rfl
  have hcard : (k4TwoApex.neighborSet u).ncard ≤ ({0, 1} : Set (Fin 6)).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have htwo : ({0, 1} : Set (Fin 6)).ncard = 2 := Set.ncard_pair (by decide)
  omega

/-- **The example.** `K₄` in `ℝ³` plus two outside vertices, each joined to the same two clique
vertices, is `UnitDistEmbeddable 3`: the neighbour sets of the two outside vertices overlap, so
this exercises the A37 correction, and each outside vertex has exactly `d − 1 = 2` neighbours,
so the degree bound is tight. -/
private theorem unitDistEmbeddable_k4_twoApex : k4TwoApex.UnitDistEmbeddable 3 :=
  UnitDistEmbeddable.extend_of_clique_neighbors k4TwoApexClique
    unitDist_induce_k4TwoApexClique k4TwoApex_clique_neighbors
    k4TwoApex_deg

end Example

end

end SimpleGraph

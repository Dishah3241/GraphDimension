/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Set.Card

import GraphDimension.Geometry.SimplexSphere
import Mathlib.Data.Set.Finite.Range

/-!
# Re-attaching a vertex over a clique

If the neighbours of a vertex `u` form a clique of size `k` with `k + 1 ≤ d`, and the induced
subgraph on the remaining vertices has a unit-distance placement in `ℝᵈ`, then so does `G`,
provided `V` is finite. The new point is chosen from the infinite set of points at distance one
from every neighbour, outside the finite image of the given placement.

## References

Chaffee and Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J.
Combin. **64(2)** (2016), 327–333, Theorems 6 and 10.
-/

namespace SimpleGraph

open EuclideanGeometry

/-- Extend a unit-distance placement of `V \ {u}` by a fresh point at distance one from every
neighbour of `u`. -/
private lemma extend_unitDistance {V : Type*} {G : SimpleGraph V} {u : V} {d : ℕ}
    (f : {v : V // v ≠ u} → EuclideanSpace ℝ (Fin d)) (hfInj : Function.Injective f)
    (hfDist : ∀ a b : {v : V // v ≠ u},
      (G.induce {v | v ≠ u}).Adj a b → dist (f a) (f b) = 1)
    (q : EuclideanSpace ℝ (Fin d)) (hqOut : q ∉ Set.range f)
    (hqNbr : ∀ ⦃v : V⦄ (hv : G.Adj u v), dist q (f ⟨v, hv.ne'⟩) = 1) :
    ∃ g : V → EuclideanSpace ℝ (Fin d), Function.Injective g ∧
      ∀ a b, G.Adj a b → dist (g a) (g b) = 1 := by
  classical
  let g : V → EuclideanSpace ℝ (Fin d) := fun x => if hx : x = u then q else f ⟨x, hx⟩
  refine ⟨g, ?_, ?_⟩
  · intro a b hab
    by_cases ha : a = u <;> by_cases hb : b = u
    · exact ha.trans hb.symm
    · have hga : g a = q := dif_pos ha
      have hgb : g b = f ⟨b, hb⟩ := dif_neg hb
      exact (hqOut ⟨⟨b, hb⟩, hgb.symm.trans (hab.symm.trans hga)⟩).elim
    · have hga : g a = f ⟨a, ha⟩ := dif_neg ha
      have hgb : g b = q := dif_pos hb
      exact (hqOut ⟨⟨a, ha⟩, hga.symm.trans (hab.trans hgb)⟩).elim
    · have hga : g a = f ⟨a, ha⟩ := dif_neg ha
      have hgb : g b = f ⟨b, hb⟩ := dif_neg hb
      exact congrArg Subtype.val <| hfInj <| hga.symm.trans (hab.trans hgb)
  · intro a b hab
    by_cases ha : a = u <;> by_cases hb : b = u
    · exact (hab.ne (ha.trans hb.symm)).elim
    · have hbu : G.Adj u b := by simpa [ha] using hab
      rw [show g a = q from dif_pos ha, show g b = f ⟨b, hb⟩ from dif_neg hb]
      exact hqNbr hbu
    · have hau : G.Adj u a := by simpa [hb] using hab.symm
      rw [show g a = f ⟨a, ha⟩ from dif_neg ha, show g b = q from dif_pos hb, dist_comm]
      exact hqNbr hau
    · rw [show g a = f ⟨a, ha⟩ from dif_neg ha, show g b = f ⟨b, hb⟩ from dif_neg hb]
      exact hfDist ⟨a, ha⟩ ⟨b, hb⟩ hab

@[expose] public section

/-- Re-attach a vertex whose neighbours form a clique of size `k` with `k + 1 ≤ d`.

`G.neighborSet u` is a clique and `(G.neighborSet u).ncard + 1 ≤ d`. The induced subgraph on
`V \ {u}` has a unit-distance placement in `ℝᵈ`, so the neighbour images are pairwise at distance
one. That set of centres meets the unit spheres in an infinite set, and finiteness of `V` leaves
a point of the set outside the image. Edges away from `u` are edges of the induced subgraph, and
each edge at `u` meets the new point at distance one.

The hypothesis `ncard + 1 ≤ d` is the truncation-free form of `k ≤ d − 1`. Chaffee–Noble prove the
cases of at most two neighbours in `ℝ³` (Theorem 6) and three neighbours in `ℝ⁴` (Theorem 10).

`UnitDistEmbeddable.extend_degree_le_two_fin_three` is the case `d = 3` with at most two
neighbours. When those neighbours are already adjacent it is this theorem. When they are not, the
degree-two lemma supplies a placement of `V \ {u}` in which they are still at distance one, which
is a unit-distance placement of `(G - u)` plus that edge. The neighbours then form a clique, this
theorem re-attaches `u`, and `UnitDistEmbeddable.of_le` deletes the extra edge. -/
theorem UnitDistEmbeddable.extend {V : Type*} [Finite V] {G : SimpleGraph V} {u : V} {d : ℕ}
    (hClique : G.IsClique (G.neighborSet u)) (hk : (G.neighborSet u).ncard + 1 ≤ d)
    (hGu : (G.induce {v | v ≠ u}).UnitDistEmbeddable d) : G.UnitDistEmbeddable d := by
  obtain ⟨f, hfInj, hfDist⟩ := hGu
  let N := {v : V // v ∈ G.neighborSet u}
  let p : N → EuclideanSpace ℝ (Fin d) := fun i => f ⟨i.1, i.2.ne'⟩
  have hpair : Pairwise fun a b : N => dist (p a) (p b) = 1 := by
    intro a b hab
    have hne : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
    have hadj : G.Adj ↑a ↑b := hClique a.2 b.2 hne
    exact hfDist ⟨a.1, a.2.ne'⟩ ⟨b.1, b.2.ne'⟩ hadj
  have hk' : Nat.card N + 1 ≤ d := by
    rw [Nat.card_coe_set_eq]
    exact hk
  obtain ⟨q, hq, hqOut⟩ :=
    (infinite_sphere_inter_of_regular_simplex hpair hk').exists_notMem_finite (Set.finite_range f)
  refine extend_unitDistance f hfInj hfDist q hqOut ?_
  intro v hv
  simpa [p] using hq ⟨v, hv⟩

end

end SimpleGraph

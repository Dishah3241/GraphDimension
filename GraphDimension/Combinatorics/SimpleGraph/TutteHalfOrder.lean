/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Degree bounds in the complement of a graph of twice the order

A graph on `2 * d` vertices whose neighbour sets all have at most `d` vertices has, in the
complement, at least `d - 1` neighbours at every vertex: the complementary degrees satisfy
`deg_G v + deg_(Gᶜ) v + 1 = 2 * d`.

This is the degree half of ROADMAP P10 (FKS Problem 1 for graphs on at most twice the dimension);
its consumers combine the bound with Tutte's theorem.
-/

@[expose] public section

namespace SimpleGraph

/-- If `G` has order `2 * d` and every neighbour set of `G` has at most `d` vertices, then every
vertex of `Gᶜ` satisfies `deg_(Gᶜ) v + 1 ≥ d`. -/
theorem le_compl_neighborSet_ncard_add_one {V : Type*} [Finite V] (G : SimpleGraph V) {d : ℕ}
    (hcard : Nat.card V = 2 * d)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ d) :
    ∀ v, d ≤ (Gᶜ.neighborSet v).ncard + 1 := by
  classical
  have := Fintype.ofFinite V
  intro v
  have h2 := hdeg v
  rw [ncard_neighborSet] at h2
  have h1 : Gᶜ.degree v = Fintype.card V - 1 - G.degree v := degree_compl G v
  rw [← ncard_neighborSet, ← Nat.card_eq_fintype_card, hcard] at h1
  omega

end SimpleGraph

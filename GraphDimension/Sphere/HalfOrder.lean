/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Combinatorics.SimpleGraph.IsolatedVertices
public import GraphDimension.Combinatorics.SimpleGraph.TutteHalfOrder
public import GraphDimension.Sphere.Bipartite
public import GraphDimension.Sphere.PerfectMatching

/-!
# FKS Problem 1 for graphs on twice the dimension

Every finite graph on at most `2 * d` vertices whose neighbour sets all have at most `d` vertices
and which has no clique of order `d + 1` sits on the sphere of radius `1/√2` in `ℝᵈ` for `d ≥ 4`.

At exact order `2 * d` the dichotomy decides the placement: a perfect matching in the complement
puts the vertices on the cross-polytope, and a bipartite graph fits on two orthogonal circles in
`ℝ⁴`. For smaller orders, pad with isolated vertices to `2 * d`, place the padded graph, and
restrict along the first summand.

This is ROADMAP P10 (FKS Problem 1 for graphs on at most twice the dimension); the target
repository consumes it through the statement bridges.
-/

@[expose] public section

namespace SimpleGraph

/-- **FKS Problem 1 for graphs of order exactly twice the dimension.**

Every graph on `2 * d` vertices whose neighbour sets all have at most `d` vertices and which has
no clique of order `d + 1` has a spherical placement in `ℝᵈ` for `d ≥ 4`. -/
theorem SphereEmbeddable.of_card_eq_two_mul
    {V : Type*} [Finite V] {G : SimpleGraph V} {d : ℕ}
    (hd : 4 ≤ d) (hcard : Nat.card V = 2 * d)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ d)
    (hK : G.CliqueFree (d + 1)) :
    G.SphereEmbeddable d := by
  rcases exists_compl_perfectMatching_or_isBipartite G (by omega : 1 ≤ d) hcard hdeg hK with
    hM | hb
  · exact SphereEmbeddable.of_compl_perfectMatching hcard hM
  · exact (SphereEmbeddable.of_isBipartite hb).mono hd

/-- **FKS Problem 1 for graphs of order at most twice the dimension.**

Every graph on at most `2 * d` vertices whose neighbour sets all have at most `d` vertices and
which has no clique of order `d + 1` has a spherical placement in `ℝᵈ` for `d ≥ 4`: pad with
isolated vertices to order `2 * d`, place the padded graph, and restrict along the first
summand. -/
theorem SphereEmbeddable.of_card_le_two_mul
    {V : Type*} [Finite V] {G : SimpleGraph V} {d : ℕ}
    (hd : 4 ≤ d) (hcard : Nat.card V ≤ 2 * d)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ d)
    (hK : G.CliqueFree (d + 1)) :
    G.SphereEmbeddable d := by
  obtain ⟨hcardN, hdegN, hKN⟩ :=
    card_degree_cliqueFree_sum_bot G hcard (by omega : 1 ≤ d) hdeg hK
  have h := SphereEmbeddable.of_card_eq_two_mul hd hcardN hdegN hKN
  let e : G ↪g (G ⊕g (⊥ : SimpleGraph (Fin (2 * d - Nat.card V)))) := Embedding.sumInl
  exact h.comap e.toHom e.injective

end SimpleGraph

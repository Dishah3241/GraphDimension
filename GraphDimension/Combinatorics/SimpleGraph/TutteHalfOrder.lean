/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Combinatorics.SimpleGraph.TutteHalfOrder.Empty
public import GraphDimension.Combinatorics.SimpleGraph.TutteHalfOrder.Nonempty
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Tutte

/-!
# Degree bounds and the matching-or-bipartite dichotomy at twice the order

A graph on `2 * d` vertices whose neighbour sets all have at most `d` vertices has, in the
complement, at least `d - 1` neighbours at every vertex: the complementary degrees satisfy
`deg_G v + deg_(Gᶜ) v + 1 = 2 * d`.

The same hypotheses, plus exclusion of a clique of order `d + 1`, give the Tutte dichotomy: the
complement carries a perfect matching, or the graph is bipartite. Tutte's theorem produces a
violating set; the nonempty ones are impossible or force a forbidden clique, and the empty one
splits the graph into two cliques of order `d` with no cross edges.

These are the degree half and the dichotomy of ROADMAP P10 (FKS Problem 1 for graphs on at most
twice the dimension); their consumers combine them with the sphere placements.
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

/-- **Matching or bipartiteness at twice the order** (the Tutte dichotomy of FKS Problem 1).

Every graph on `2 * d` vertices whose neighbour sets all have at most `d` vertices and which has
no clique of order `d + 1` either has a perfect matching in its complement or is bipartite. -/
theorem exists_compl_perfectMatching_or_isBipartite
    {V : Type*} [Finite V] (G : SimpleGraph V) {d : ℕ}
    (hd : 1 ≤ d) (hcard : Nat.card V = 2 * d)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ d)
    (hK : G.CliqueFree (d + 1)) :
    (∃ M : Gᶜ.Subgraph, M.IsPerfectMatching) ∨ G.IsBipartite := by
  classical
  by_contra h
  have hM : ¬ ∃ M : Gᶜ.Subgraph, M.IsPerfectMatching := fun hm => h (Or.inl hm)
  have hnb : ¬ G.IsBipartite := fun hb => h (Or.inr hb)
  have hmin := le_compl_neighborSet_ncard_add_one G hcard hdeg
  obtain ⟨S, hviol⟩ : ∃ S : Set V, (Gᶜ).IsTutteViolator S := by
    by_contra hall
    exact hM ((tutte (G := Gᶜ)).mpr fun S hS => hall ⟨S, hS⟩)
  rcases Set.eq_empty_or_nonempty S with rfl | hne
  · obtain ⟨-, s, -, -, hcl, hcl', -⟩ :=
      exists_two_cliques_of_isTutteViolator_empty Gᶜ (by omega) hcard hmin hviol
    have hbip : G.IsBipartiteWith s sᶜ := by
      refine IsBipartiteWith.mk disjoint_compl_right ?_
      intro v w hvw
      have hnew : v ≠ w := G.ne_of_adj hvw
      by_cases hv : v ∈ s
      · refine Or.inl ⟨hv, ?_⟩
        intro hw
        exact ((G.compl_adj v w).mp (hcl hv hw hnew)).2 hvw
      · refine Or.inr ⟨(Set.mem_compl_iff s v).mpr hv, ?_⟩
        by_contra hw0
        exact ((G.compl_adj v w).mp
          (hcl' ((Set.mem_compl_iff s v).mpr hv) ((Set.mem_compl_iff s w).mpr hw0) hnew)).2 hvw
    exact absurd hbip.isBipartite hnb
  · have hpos : 1 ≤ S.ncard := Set.ncard_pos (Set.toFinite S) |>.mpr hne
    by_cases h1 : S.ncard + 2 ≤ d
    · exact (not_isTutteViolator_of_card_between Gᶜ S hcard hmin hpos h1) hviol
    by_cases h2 : d ≤ S.ncard
    · exact (not_isTutteViolator_of_half_card_le Gᶜ S hcard h2) hviol
    obtain ⟨t, ht⟩ :=
      exists_isNClique_compl_of_isTutteViolator_card_add_one Gᶜ S hcard (by omega) hviol
    exact hK t (by rw [compl_compl] at ht; exact ht)

end SimpleGraph

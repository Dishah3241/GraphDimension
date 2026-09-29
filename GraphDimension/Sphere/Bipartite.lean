/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Sphere.DegreeOne
public import GraphDimension.Sphere.OrthogonalSum
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Bipartite graphs on the sphere

A finite bipartite graph has a spherical placement in `ℝ⁴`: take a bipartition, put each side on
a radius-`1/√2` circle in one of two orthogonal coordinate planes. Both induced graphs are
edgeless, so the degree-one circle placement applies to each, and the orthogonal sum makes every
cross pair an edge, whether or not it is one. Every finite complete bipartite graph therefore has
a spherical placement in `ℝᵈ` for every `d ≥ 4`.

This is the two-circle placement of ROADMAP P10 (FKS Problem 1 for graphs on at most twice the
dimension); its consumers combine it with the cross-polytope placement through a dichotomy.
-/

open scoped InnerProductSpace

namespace SimpleGraph

noncomputable section

@[expose] public section

/-- A finite bipartite graph has a spherical placement in `ℝ⁴`.

Place one side of a bipartition on the radius-`1/√2` circle in the first coordinate plane and the
remaining vertices on the circle in the second plane. Edges cross the bipartition, so every edge
joins orthogonal position vectors and hence has length one. -/
theorem SphereEmbeddable.of_isBipartite {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : G.IsBipartite) :
    G.SphereEmbeddable 4 := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨s, t, hst⟩ := hG.exists_isBipartiteWith
  have hnoS : ∀ v w : V, v ∈ s → w ∈ s → ¬ G.Adj v w := by
    intro v w hv hw hadj
    rcases hst.mem_of_adj hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Set.disjoint_left.mp hst.disjoint hw h2
    · exact Set.disjoint_left.mp hst.disjoint hv h1
  have hnoSc : ∀ v w : V, v ∈ sᶜ → w ∈ sᶜ → ¬ G.Adj v w := by
    intro v w hv hw hadj
    rcases hst.mem_of_adj hadj with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hv h1
    · exact hw h2
  have hleft : (G.induce s).SphereEmbeddable 2 :=
    SphereEmbeddable.of_degree_le_two fun v => by
      by_contra hdeg
      have hpos : 0 < (G.induce s).degree v := by omega
      obtain ⟨w, hw⟩ := (degree_pos_iff_exists_adj _ _).mp hpos
      exact hnoS _ _ v.prop w.prop (induce_adj.mp hw)
  have hright : (G.induce sᶜ).SphereEmbeddable 2 :=
    SphereEmbeddable.of_degree_le_two fun v => by
      by_contra hdeg
      have hpos : 0 < (G.induce sᶜ).degree v := by omega
      obtain ⟨w, hw⟩ := (degree_pos_iff_exists_adj _ _).mp hpos
      exact hnoSc _ _ v.prop w.prop (induce_adj.mp hw)
  exact hleft.orthogonalSum hright

/-- Every finite complete bipartite graph has a spherical placement in `ℝᵈ` for `d ≥ 4`. -/
theorem sphereEmbeddable_completeBipartiteGraph {U W : Type*} [Finite U] [Finite W] {d : ℕ}
    (hd : 4 ≤ d) :
    (completeBipartiteGraph U W).SphereEmbeddable d :=
  (SphereEmbeddable.of_isBipartite (IsBipartite.completeBipartiteGraph U W)).mono hd

end

end

end SimpleGraph

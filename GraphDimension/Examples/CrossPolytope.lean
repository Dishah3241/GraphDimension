/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Sphere.CrossPolytope

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.NormNum

/-!
# The octahedron and the cross-polytope lemma at `d = 3`

The graph of the 3-dimensional cross-polytope — the octahedron `K₂,₂,₂` — is on `𝕊²` in `ℝ³`:
the three pairs of opposite vertices are sent to `±eᵢ/√2` by
`SphereEmbeddable.of_compl_matching` with `k = d = 3`, the antipodal pairs being exactly the
three missing edges. This is the nondegenerate case `k = 3` of the lemma, with no unmatched
vertices.

The `hnadj` hypothesis is load-bearing: `K₄` satisfies every other hypothesis of
`of_compl_matching` at `d = 3` with `k = 1`, but is not on `𝕊²` — a spherical placement would
give four pairwise orthogonal nonzero vectors in `ℝ³`, which would be linearly independent in a
three-dimensional space.
-/

open scoped InnerProductSpace

namespace SimpleGraph

@[expose] public section

/-- The octahedral graph `K₂,₂,₂` — the 1-skeleton of the 3-dimensional cross-polytope — is on
`𝕊²` in `ℝ³`.

`K₂,₂,₂` is the complete multipartite graph on three parts of size two; the antipodal pairs are
the two vertices of each part, which are exactly the non-edges of the complement matching. The
matched vertices `⟨i, 0⟩`, `⟨i, 1⟩` go to `±eᵢ/√2`. -/
theorem sphereEmbeddable_octahedron :
    (completeMultipartiteGraph fun _ : Fin 3 => Fin 2).SphereEmbeddable 3 := by
  refine SphereEmbeddable.of_compl_matching (k := 3) (d := 3) le_rfl
    (by simp) (fun i => ⟨i, 0⟩) (fun i => ⟨i, 1⟩) ?_ ?_
  · -- The six vertices are pairwise distinct.
    rintro (i | i) (j | j) h
    · exact congrArg Sum.inl (congrArg Sigma.fst h)
    · exfalso
      have h2 : i = j := congrArg Sigma.fst h
      subst h2
      have h3 : (0 : Fin 2) = (1 : Fin 2) := congrArg Sigma.snd h
      exact absurd h3 (by decide)
    · exfalso
      have h2 : i = j := congrArg Sigma.fst h
      subst h2
      have h3 : (1 : Fin 2) = (0 : Fin 2) := congrArg Sigma.snd h
      exact absurd h3 (by decide)
    · exact congrArg Sum.inr (congrArg Sigma.fst h)
  -- Vertices in the same part are not adjacent.
  · intro i h
    exact h rfl

/-- `K₄` is not on `𝕊²`: a spherical placement in `ℝ³` would give four pairwise orthogonal
nonzero vectors, linearly independent in a space of dimension three. -/
theorem completeGraph_fin_four_not_sphereEmbeddable_three :
    ¬ (⊤ : SimpleGraph (Fin 4)).SphereEmbeddable 3 := by
  intro h
  rw [SphereEmbeddable.iff_orthogonal] at h
  obtain ⟨f, -, hfNorm, hfOrth⟩ := h
  have hne : ∀ i, f i ≠ 0 := by
    intro i hi
    have h2 := hfNorm i
    rw [hi, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h2
    norm_num at h2
  have ho : Pairwise fun i j : Fin 4 => ⟪f i, f j⟫_ℝ = 0 := fun i j hij =>
    hfOrth i j (by rwa [top_adj])
  have hli := linearIndependent_of_ne_zero_of_inner_eq_zero hne ho
  have hcard := hli.fintype_card_le_finrank
  simp only [finrank_euclideanSpace_fin, Fintype.card_fin] at hcard
  exact absurd hcard (by decide : ¬ (4 : ℕ) ≤ 3)

end

end SimpleGraph

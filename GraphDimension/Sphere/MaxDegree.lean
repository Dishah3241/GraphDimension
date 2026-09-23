/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Sphere.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite

import GraphDimension.Combinatorics.SimpleGraph.Lovasz
import GraphDimension.Sphere.DegreeOne
import GraphDimension.Sphere.OrthogonalSum
import Mathlib.Tactic.Linarith

/-!
# Inductive step of FKS Proposition 2

For `d ≥ 4`, Lovász's partition with `k₁ = ⌊(d - 2) / 2⌋` and `k₂ = d - 2 - k₁` splits a graph of
maximum degree at most `d - 1` into induced subgraphs of maximum degree at most `k₁` and `k₂`.
The inductive hypothesis places those subgraphs on spheres in `ℝ^{k₁+1}` and `ℝ^{k₂+1}`, and the
orthogonal sum places `G` in `ℝᵈ`.

The case `d = 3` is not proved here. Closing `SphereEmbeddable.of_degree_le` needs that base.

## References

Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, J. Combin. Theory Ser. A
**171** (2020), 105146, arXiv 1802.03092, proof of Proposition 2 (`main.tex` lines 122–125).
-/

namespace SimpleGraph

universe u

@[expose] public section

/-- **Inductive step of FKS Proposition 2.** For `d ≥ 4`, a graph of maximum degree at most
`d - 1` is spherically embeddable in `ℝᵈ` whenever every graph of maximum degree at most `d' - 1`
is spherically embeddable in `ℝᵈ'` for all `2 ≤ d' < d`.

`k₁ = (d - 2) / 2` and `k₂ = d - 2 - k₁` are at least one, and
`k₁ + k₂ + 1 = d - 1`. Lovász's partition (`exists_partition_maxDegree_le`) produces parts whose
induced subgraphs fall under the inductive hypothesis in dimensions `k₁ + 1` and `k₂ + 1`. The
orthogonal sum (`SphereEmbeddable.orthogonalSum`) adds those dimensions to `d`. -/
theorem SphereEmbeddable.of_degree_le_ge_four {V : Type u} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hd : 4 ≤ d)
    (ih : ∀ {d' : ℕ} {W : Type u} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
      d' < d → 2 ≤ d' → (∀ w, H.degree w + 1 ≤ d') → H.SphereEmbeddable d')
    (h : ∀ v, G.degree v + 1 ≤ d) : G.SphereEmbeddable d := by
  classical
  let k₁ : ℕ := (d - 2) / 2
  let k₂ : ℕ := d - 2 - k₁
  have hk₁ : 1 ≤ k₁ := by
    dsimp [k₁]
    omega
  have hk₂ : 1 ≤ k₂ := by
    dsimp [k₁, k₂]
    omega
  have hsum : k₁ + k₂ + 1 = d - 1 := by
    dsimp [k₁, k₂]
    omega
  have hdim : k₁ + 1 + (k₂ + 1) = d := by
    dsimp [k₁, k₂]
    omega
  have hΔ : G.maxDegree ≤ k₁ + k₂ + 1 := by
    rw [hsum]
    refine G.maxDegree_le_of_forall_degree_le (d - 1) fun v => ?_
    have hv := h v
    omega
  obtain ⟨s, hs, hsc⟩ := exists_partition_maxDegree_le G k₁ k₂ hΔ
  have hlt₁ : k₁ + 1 < d := by
    dsimp [k₁]
    omega
  have hlt₂ : k₂ + 1 < d := by
    dsimp [k₁, k₂]
    omega
  let W₁ := {v // v ∈ (s : Set V)}
  let H₁ : SimpleGraph W₁ := G.induce (s : Set V)
  have hdeg₁ : ∀ x : W₁, H₁.degree x + 1 ≤ k₁ + 1 := by
    intro x
    have hdeg : H₁.degree x ≤ k₁ := (H₁.degree_le_maxDegree x).trans hs
    omega
  have h₁ : H₁.SphereEmbeddable (k₁ + 1) :=
    @ih (k₁ + 1) W₁ _ H₁ _ hlt₁ (by omega) hdeg₁
  let W₂ := {v // v ∈ ((sᶜ : Finset V) : Set V)}
  let H₂ : SimpleGraph W₂ := G.induce ((sᶜ : Finset V) : Set V)
  have hdeg₂ : ∀ x : W₂, H₂.degree x + 1 ≤ k₂ + 1 := by
    intro x
    have hdeg : H₂.degree x ≤ k₂ := (H₂.degree_le_maxDegree x).trans hsc
    omega
  have h₂ : H₂.SphereEmbeddable (k₂ + 1) :=
    @ih (k₂ + 1) W₂ _ H₂ _ hlt₂ (by omega) hdeg₂
  have h₂' : (G.induce ((s : Set V)ᶜ)).SphereEmbeddable (k₂ + 1) := by
    rw [show (s : Set V)ᶜ = ((sᶜ : Finset V) : Set V) from (Finset.coe_compl s).symm]
    simpa [H₂] using h₂
  have hsumEmb := SphereEmbeddable.orthogonalSum h₁ h₂'
  rw [hdim] at hsumEmb
  exact hsumEmb

end

end SimpleGraph

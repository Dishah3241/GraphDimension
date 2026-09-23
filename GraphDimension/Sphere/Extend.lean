/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Sphere.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Card

import GraphDimension.Combinatorics.SimpleGraph.Core
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Set.Finite.Range
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Re-attaching a low-degree vertex on the sphere

A vertex with at most `d − 2` neighbours re-attaches to a spherical placement in `ℝᵈ`: the placed
neighbours span a subspace of dimension at most `d − 2`, so the orthogonal complement has dimension
at least two and meets the sphere of radius `1/√2` in an infinite set. A point of that set outside
the finite image is orthogonal to every neighbour, hence at distance one.

`SphereEmbeddable.extend_insert` is that step on an induced subgraph, in the shape
`SimpleGraph.exists_core` consumes. `SphereEmbeddable.exists_core` is the resulting
`(d − 1)`-core: spherical embeddability of the core implies spherical embeddability of `G`.
`SphereEmbeddable.exists_core_subset` is the same propagation inside an arbitrary vertex set, so a
later branch can re-attach onto `G − v` by taking the ground set `univ.erase v`.
`SphereEmbeddable.of_degenerate` is the empty-core case. Its hypothesis is this library's
`(d − 2)`-degeneracy condition, the hypothesis under which every core is empty.

## References

Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, J. Combin. Theory Ser. A
**171** (2020), 105146, arXiv 1802.03092, Lemma 11 and Corollary 12 (`main.tex` lines 317–328).
-/

open scoped InnerProductSpace RealInnerProductSpace

namespace SimpleGraph

open Module Submodule Finset

noncomputable section

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The squared norm of a vector in the plane of an orthonormal pair is the sum of the squared
coefficients. -/
private lemma norm_sq_orthonormal {e₀ e₁ : E} (he₀ : ‖e₀‖ = 1) (he₁ : ‖e₁‖ = 1)
    (horth : ⟪e₀, e₁⟫_ℝ = 0) (t s : ℝ) : ‖t • e₀ + s • e₁‖ ^ 2 = t ^ 2 + s ^ 2 := by
  have hcross : ⟪t • e₀, s • e₁⟫_ℝ = 0 := by
    simp [real_inner_smul_left, real_inner_smul_right, horth]
  rw [norm_add_sq_real, hcross, mul_zero, add_zero, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, he₀, he₁, mul_one, mul_one, sq_abs, sq_abs]

/-- The inner product against the first vector of an orthonormal pair recovers its coefficient. -/
private lemma inner_coord_orthonormal {e₀ e₁ : E} (he₀ : ‖e₀‖ = 1) (horth : ⟪e₀, e₁⟫_ℝ = 0)
    (t s : ℝ) : ⟪t • e₀ + s • e₁, e₀⟫_ℝ = t := by
  have h10 : ⟪e₁, e₀⟫_ℝ = 0 := inner_eq_zero_symm.mp horth
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, h10,
    real_inner_self_eq_norm_sq, he₀]
  ring

/-- The semicircle `t ↦ t • e₀ + √(r² − t²) • e₁`, for `t ∈ [0, r]` and an orthonormal pair,
is infinite. -/
private lemma infinite_origin_semicircle (e₀ e₁ : E) (he₀ : ‖e₀‖ = 1) (horth : ⟪e₀, e₁⟫_ℝ = 0)
    {r : ℝ} (hr : 0 < r) :
    ((fun t : ℝ => t • e₀ + Real.sqrt (r ^ 2 - t ^ 2) • e₁) '' Set.Icc 0 r).Infinite := by
  refine (Set.infinite_image_iff ?_).2 (Set.Icc_infinite hr)
  intro t _ t' _ h
  have hcoord : ∀ u : ℝ,
      ⟪u • e₀ + Real.sqrt (r ^ 2 - u ^ 2) • e₁, e₀⟫_ℝ = u :=
    fun u => inner_coord_orthonormal he₀ horth u (Real.sqrt (r ^ 2 - u ^ 2))
  have hinner := congrArg (fun p => ⟪p, e₀⟫_ℝ) h
  rw [hcoord, hcoord] at hinner
  exact hinner

/-- A subspace of dimension at least two contains an orthonormal pair. -/
private lemma exists_orthonormal_pair_of_finrank_ge_two {W : Submodule ℝ E}
    (hW : 2 ≤ finrank ℝ W) :
    ∃ e₀ e₁ : E, ‖e₀‖ = 1 ∧ ‖e₁‖ = 1 ∧ ⟪e₀, e₁⟫_ℝ = 0 ∧ e₀ ∈ W ∧ e₁ ∈ W := by
  have : FiniteDimensional ℝ W := FiniteDimensional.of_finrank_pos (by omega)
  let b := stdOrthonormalBasis ℝ W
  let i₀ : Fin (finrank ℝ W) := ⟨0, by omega⟩
  let i₁ : Fin (finrank ℝ W) := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := by
    intro h
    apply_fun Fin.val at h
    simp at h
  refine ⟨b i₀, b i₁, ?_, ?_, ?_, ?_, ?_⟩
  · rw [norm_coe]
    exact b.norm_eq_one i₀
  · rw [norm_coe]
    exact b.norm_eq_one i₁
  · rw [← Submodule.coe_inner]
    exact b.inner_eq_zero hne
  · exact (b i₀).2
  · exact (b i₁).2

/-- In a subspace of dimension at least two, the sphere of radius `1/√2` about the origin is
infinite: it contains a semicircle in the plane of an orthonormal pair. -/
private lemma infinite_sphere_in_submodule {W : Submodule ℝ E} (hW : 2 ≤ finrank ℝ W) :
    {v : E | v ∈ W ∧ ‖v‖ ^ 2 = 1 / 2}.Infinite := by
  obtain ⟨e₀, e₁, he₀, he₁, horth, he₀W, he₁W⟩ :=
    exists_orthonormal_pair_of_finrank_ge_two hW
  let r : ℝ := Real.sqrt (1 / 2)
  have hr0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hr : 0 < r := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 1 / 2)
  have hr2 : r ^ 2 = 1 / 2 := Real.sq_sqrt hr0
  refine Set.Infinite.mono ?_ (infinite_origin_semicircle e₀ e₁ he₀ horth hr)
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨?_, ?_⟩
  · exact add_mem (smul_mem _ t he₀W) (smul_mem _ _ he₁W)
  · have hs : 0 ≤ r ^ 2 - t ^ 2 :=
      sub_nonneg.mpr (sq_le_sq' (by linarith [ht.1, hr.le]) ht.2)
    rw [norm_sq_orthonormal he₀ he₁ horth, Real.sq_sqrt hs, hr2]
    ring

end Geometry

variable {V : Type*}

/-- The subgraph induced by the empty vertex set has an empty vertex type, so the unique
placement is a spherical placement in every dimension. -/
private lemma induce_empty (G : SimpleGraph V) (d : ℕ) :
    (G.induce (∅ : Set V)).SphereEmbeddable d := by
  have : IsEmpty {v // v ∈ (∅ : Set V)} := ⟨fun v => Set.notMem_empty v.1 v.2⟩
  exact ⟨fun v => isEmptyElim v, fun a b _ => isEmptyElim a, fun v => isEmptyElim v,
    fun u v _ => isEmptyElim u⟩

/-- Neighbours of `x` inside `insert x s` are neighbours of `x` that already lie in `s`. -/
private lemma ncard_neighbor_induce_insert_le [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {s : Finset V} {x : V}
    (xH : {v // v ∈ ↑(insert x s)}) (hxH : xH.1 = x) :
    ((G.induce ↑(insert x s)).neighborSet xH).ncard ≤ (s.filter (G.Adj x)).card := by
  let H := G.induce ↑(insert x s)
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn (fun w : {v // v ∈ ↑(insert x s)} => w.1)
      (s := H.neighborSet xH) (t := (s.filter (G.Adj x) : Set V)) ?_ ?_
      (Finset.finite_toSet _)
  · intro w hw
    have hadjH : H.Adj xH w := by simpa [mem_neighborSet] using hw
    have hadj : G.Adj x w.1 := by
      rw [induce_adj] at hadjH
      simpa [hxH] using hadjH
    have hne : w.1 ≠ x := by
      intro hwx
      exact hadjH.ne (Subtype.ext (hwx.trans hxH.symm)).symm
    have hmem : w.1 ∈ insert x s := Finset.mem_coe.mp w.2
    rcases Finset.mem_insert.mp hmem with hwx | hs
    · exact absurd hwx hne
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hs, hadj⟩)
  · intro a _ b _ hab
    exact Subtype.ext hab

/-- A spherical placement of `G.induce ↑s` is one of the induced subgraph of
`G.induce ↑(insert x s)` on the vertices other than `x`. -/
private lemma sphereEmbeddable_induce_erase_insert [DecidableEq V] {G : SimpleGraph V}
    {s : Finset V} {x : V} {d : ℕ}
    (xH : {v // v ∈ ↑(insert x s)}) (hxH : xH.1 = x)
    (h : (G.induce ↑s).SphereEmbeddable d) :
    ((G.induce ↑(insert x s)).induce {v | v ≠ xH}).SphereEmbeddable d := by
  let H := G.induce ↑(insert x s)
  let φ : (H.induce {v | v ≠ xH}) →g G.induce ↑s := {
    toFun := fun v => ⟨v.1.1, by
      have hmem : v.1.1 ∈ insert x s := Finset.mem_coe.mp v.1.2
      have hne : v.1.1 ≠ x := by
        intro hxv
        exact v.2 (Subtype.ext (hxv.trans hxH.symm))
      rcases Finset.mem_insert.mp hmem with hxv | hs
      · exact absurd hxv hne
      · exact Finset.mem_coe.mpr hs⟩
    map_rel' := fun {a b} hab => by
      apply induce_adj.mpr
      exact induce_adj.mp (induce_adj.mp hab)
  }
  have hφ : Function.Injective φ := by
    intro a b hab
    have hval : (φ a).1 = (φ b).1 :=
      congrArg (fun z : {v // v ∈ ↑s} => (z : V)) hab
    exact Subtype.ext (Subtype.ext hval)
  exact h.comap φ hφ

@[expose] public section

/-- **FKS Lemma 11.** A vertex with at most `d − 2` neighbours re-attaches on the sphere.

`(G.neighborSet x).ncard + 2 ≤ d` is the truncation-free form of degree at most `d − 2`; it forces
`d ≥ 2`. The placed neighbours span a subspace of dimension at most `d − 2`
(`finrank_span_le_card`). Its orthogonal complement therefore has dimension at least two
(`Submodule.finrank_add_finrank_orthogonal`), so the complement meets the sphere of radius `1/√2`
in an infinite set. That set avoids the finitely many placed points
(`Set.Infinite.exists_notMem_finite`). The chosen point is orthogonal to each neighbour, hence at
distance one (`SphereEmbeddable.iff_orthogonal`). -/
theorem SphereEmbeddable.extend {V : Type*} [Finite V] {G : SimpleGraph V} {x : V} {d : ℕ}
    (hdeg : (G.neighborSet x).ncard + 2 ≤ d)
    (h : (G.induce {v | v ≠ x}).SphereEmbeddable d) : G.SphereEmbeddable d := by
  classical
  rw [SphereEmbeddable.iff_orthogonal] at h ⊢
  obtain ⟨f, hfInj, hfNorm, hfOrth⟩ := h
  let : Fintype (G.neighborSet x) := Fintype.ofFinite _
  let p : G.neighborSet x → EuclideanSpace ℝ (Fin d) := fun i => f ⟨i.1, i.2.ne'⟩
  have : Finite (Set.range p) := (Set.finite_range p).to_subtype
  let : Fintype (Set.range p) := Fintype.ofFinite _
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := span ℝ (Set.range p)
  have hspan : finrank ℝ K ≤ (G.neighborSet x).ncard := by
    refine (finrank_span_le_card (Set.range p)).trans ?_
    rw [Set.toFinset_range (f := p)]
    calc (Finset.univ.image p).card
        ≤ Finset.univ.card := Finset.card_image_le
      _ = Fintype.card (G.neighborSet x) := Finset.card_univ
      _ = (G.neighborSet x).ncard := by
          rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have horth : 2 ≤ finrank ℝ Kᗮ := by
    have hsum : finrank ℝ K + finrank ℝ Kᗮ = d := by
      simpa [finrank_euclideanSpace_fin] using finrank_add_finrank_orthogonal K
    have hle : finrank ℝ K + 2 ≤ d :=
      (Nat.add_le_add_right hspan 2).trans hdeg
    omega
  obtain ⟨q, hq, hqOut⟩ :=
    (infinite_sphere_in_submodule (W := Kᗮ) horth).exists_notMem_finite (Set.finite_range f)
  obtain ⟨hqK, hqNorm⟩ := hq
  let g : V → EuclideanSpace ℝ (Fin d) := fun y => if hy : y = x then q else f ⟨y, hy⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · intro a b hab
    by_cases ha : a = x <;> by_cases hb : b = x
    · exact ha.trans hb.symm
    · have hga : g a = q := dite_eq_left ha
      have hgb : g b = f ⟨b, hb⟩ := dite_eq_right hb
      exact (hqOut ⟨⟨b, hb⟩, hgb.symm.trans (hab.symm.trans hga)⟩).elim
    · have hga : g a = f ⟨a, ha⟩ := dite_eq_right ha
      have hgb : g b = q := dite_eq_left hb
      exact (hqOut ⟨⟨a, ha⟩, hga.symm.trans (hab.trans hgb)⟩).elim
    · have hga : g a = f ⟨a, ha⟩ := dite_eq_right ha
      have hgb : g b = f ⟨b, hb⟩ := dite_eq_right hb
      exact congrArg Subtype.val <| hfInj <| hga.symm.trans (hab.trans hgb)
  · intro y
    by_cases hy : y = x
    · rw [show g y = q from dite_eq_left hy]
      exact hqNorm
    · rw [show g y = f ⟨y, hy⟩ from dite_eq_right hy]
      exact hfNorm _
  · intro a b hab
    by_cases ha : a = x <;> by_cases hb : b = x
    · exact (hab.ne (ha.trans hb.symm)).elim
    · have hbu : G.Adj x b := ha ▸ hab
      have horthb : ⟪q, p ⟨b, hbu⟩⟫_ℝ = 0 :=
        inner_left_of_mem_orthogonal (subset_span (Set.mem_range_self _)) hqK
      have hp : p ⟨b, hbu⟩ = f ⟨b, hb⟩ := by
        dsimp [p]
      rw [show g a = q from dite_eq_left ha, show g b = f ⟨b, hb⟩ from dite_eq_right hb, ← hp]
      exact horthb
    · have hau : G.Adj x a := hb ▸ hab.symm
      have hortha : ⟪q, p ⟨a, hau⟩⟫_ℝ = 0 :=
        inner_left_of_mem_orthogonal (subset_span (Set.mem_range_self _)) hqK
      have hp : p ⟨a, hau⟩ = f ⟨a, ha⟩ := by
        dsimp [p]
      rw [show g a = f ⟨a, ha⟩ from dite_eq_right ha, show g b = q from dite_eq_left hb,
        real_inner_comm,
        ← hp]
      exact hortha
    · rw [show g a = f ⟨a, ha⟩ from dite_eq_right ha, show g b = f ⟨b, hb⟩ from dite_eq_right hb]
      exact hfOrth ⟨a, ha⟩ ⟨b, hb⟩ hab

/-- **The re-attachment step `exists_core` consumes.** If `x` has at most `d − 2` neighbours in
`s`, a spherical placement of `G.induce ↑s` yields one of `G.induce ↑(insert x s)`.

`exists_core` calls this with `x ∉ s`. That side condition is not required: when `x ∈ s`,
`insert x s = s`. -/
theorem SphereEmbeddable.extend_insert {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {s : Finset V} {x : V} {d : ℕ}
    (hdeg : (s.filter (G.Adj x)).card + 2 ≤ d)
    (h : (G.induce ↑s).SphereEmbeddable d) :
    (G.induce ↑(insert x s)).SphereEmbeddable d := by
  have : Finite {v // v ∈ ↑(insert x s)} := (Finset.finite_toSet (insert x s)).to_subtype
  let xH : {v // v ∈ ↑(insert x s)} := ⟨x, Finset.mem_coe.mpr (Finset.mem_insert_self x s)⟩
  have hxH : xH.1 = x := rfl
  have hdeg' : ((G.induce ↑(insert x s)).neighborSet xH).ncard + 2 ≤ d :=
    (Nat.add_le_add_right (ncard_neighbor_induce_insert_le xH hxH) 2).trans hdeg
  exact SphereEmbeddable.extend hdeg' (sphereEmbeddable_induce_erase_insert xH hxH h)

private lemma extend_insert_of_le [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {s : Finset V} {x : V} {d : ℕ} (hd : 2 ≤ d)
    (hdeg : (s.filter (G.Adj x)).card ≤ d - 2)
    (h : (G.induce ↑s).SphereEmbeddable d) :
    (G.induce ↑(insert x s)).SphereEmbeddable d :=
  SphereEmbeddable.extend_insert (by omega) h

/-- **Re-attachment inside a vertex set.** Some `c ⊆ t` has every vertex of degree more than
`d − 2` in `c`, and spherical embeddability of `G.induce ↑c` implies spherical embeddability of
`G.induce ↑t`.

This is the form a branch uses for `G − v`: take `t = univ.erase v`. The deleted vertices
re-attach one at a time by `SphereEmbeddable.extend_insert`. -/
theorem SphereEmbeddable.exists_core_subset {V : Type*} {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hd : 2 ≤ d) (t : Finset V) :
    ∃ c ⊆ t,
      (∀ v ∈ c, d - 2 < (c.filter (G.Adj v)).card) ∧
        ((G.induce ↑c).SphereEmbeddable d → (G.induce ↑t).SphereEmbeddable d) := by
  classical
  exact SimpleGraph.exists_core_subset (d - 2) (fun s => (G.induce ↑s).SphereEmbeddable d)
    (fun _s _x _hx hdeg hP => extend_insert_of_le hd hdeg hP) t

/-- **FKS Corollary 12, the core.** For `2 ≤ d` there is a vertex set `c` in which every vertex
has more than `d − 2` neighbours, such that a spherical placement of `G.induce ↑c` in `ℝᵈ`
yields one of `G`. The set `c` is a `(d − 1)`-core of `G`: it is what remains after deleting
vertices of degree at most `d − 2`, and the deleted vertices re-attach in reverse order. -/
theorem SphereEmbeddable.exists_core {V : Type*} [Finite V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hd : 2 ≤ d) :
    ∃ c : Finset V,
      (∀ v ∈ c, d - 2 < (c.filter (G.Adj v)).card) ∧
        ((G.induce ↑c).SphereEmbeddable d → G.SphereEmbeddable d) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨c, -, hcore, hP⟩ :=
    SphereEmbeddable.exists_core_subset (G := G) hd (Finset.univ : Finset V)
  refine ⟨c, hcore, fun hc => ?_⟩
  have hUniv : (G.induce Set.univ).SphereEmbeddable d := by
    rw [← Finset.coe_univ]
    exact hP hc
  exact (SphereEmbeddable.of_iso (induceUnivIso G)).mp hUniv

/-- **FKS Corollary 12, the degenerate case.** A `(d − 2)`-degenerate graph is spherically
embeddable in `ℝᵈ`.

The hypothesis is the deletion condition from `SimpleGraph.exists_core_of_degenerate`: every
nonempty vertex set has a vertex with at most `d − 2` neighbours inside it. By
`SimpleGraph.eq_empty_of_degenerate` that is exactly the condition under which every core is
empty, so the empty induced subgraph, which is spherically embeddable, propagates to `G`. -/
theorem SphereEmbeddable.of_degenerate {V : Type*} [Finite V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hdeg : ∀ s : Finset V, s.Nonempty → ∃ x ∈ s, (s.filter (G.Adj x)).card ≤ d - 2) :
    G.SphereEmbeddable d := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hP0 : (G.induce ↑(∅ : Finset V)).SphereEmbeddable d := by
    rw [Finset.coe_empty]
    exact induce_empty G d
  have hUniv := exists_core_of_degenerate (d - 2) (fun s => (G.induce ↑s).SphereEmbeddable d)
    (fun _s _x _hx hcard hP => extend_insert_of_le hd hcard hP) hP0 hdeg
  have hUniv' : (G.induce Set.univ).SphereEmbeddable d := by
    rw [← Finset.coe_univ]
    exact hUniv
  exact (SphereEmbeddable.of_iso (induceUnivIso G)).mp hUniv'

end

end

end SimpleGraph

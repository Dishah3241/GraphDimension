/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Sphere.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.NormNum

/-!
# Orthogonal sum of spherical placements

Placements of the two sides of a vertex partition, sitting in the first `m` and the last `n`
coordinates of `ℝᵐ⁺ⁿ`, give a spherical placement of the whole graph. Every cross pair is
orthogonal, hence at distance one, whether or not the pair is an edge.

## References

Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, J. Combin. Theory Ser. A
**171** (2020), 105146, arXiv 1802.03092, proof of Proposition 2 (`main.tex` lines 122–125).
-/

open scoped InnerProductSpace

namespace SimpleGraph

noncomputable section

variable {m n : ℕ}

/-- A vector of `ℝᵐ` placed in the first `m` coordinates of `ℝᵐ⁺ⁿ`, with zeros after. -/
private def padLeft (x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin (m + n)) :=
  WithLp.toLp 2 (Fin.append (fun i => x i) fun _ => (0 : ℝ))

/-- A vector of `ℝⁿ` placed in the last `n` coordinates of `ℝᵐ⁺ⁿ`, with zeros before. -/
private def padRight (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (m + n)) :=
  WithLp.toLp 2 (Fin.append (fun _ : Fin m => (0 : ℝ)) fun j => y j)

private lemma padLeft_castAdd (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    padLeft (n := n) x (Fin.castAdd n i) = x i := by
  simp [padLeft, PiLp.toLp_apply, Fin.append_left]

private lemma padLeft_natAdd (x : EuclideanSpace ℝ (Fin m)) (j : Fin n) :
    padLeft (n := n) x (Fin.natAdd m j) = 0 := by
  simp [padLeft, PiLp.toLp_apply, Fin.append_right]

private lemma padRight_castAdd (y : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    padRight (m := m) y (Fin.castAdd n i) = 0 := by
  simp [padRight, PiLp.toLp_apply, Fin.append_left]

private lemma padRight_natAdd (y : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    padRight (m := m) y (Fin.natAdd m j) = y j := by
  simp [padRight, PiLp.toLp_apply, Fin.append_right]

private lemma inner_padLeft (x y : EuclideanSpace ℝ (Fin m)) :
    ⟪padLeft (n := n) x, padLeft (n := n) y⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_add]
  simp [padLeft_castAdd, padLeft_natAdd]

private lemma inner_padRight (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪padRight (m := m) x, padRight (m := m) y⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_add]
  simp [padRight_castAdd, padRight_natAdd]

private lemma inner_padLeft_padRight (x : EuclideanSpace ℝ (Fin m))
    (y : EuclideanSpace ℝ (Fin n)) :
    ⟪padLeft (n := n) x, padRight (m := m) y⟫_ℝ = 0 := by
  rw [PiLp.inner_apply, Fin.sum_univ_add]
  simp [padLeft_castAdd, padLeft_natAdd, padRight_castAdd, padRight_natAdd]

private lemma norm_sq_padLeft (x : EuclideanSpace ℝ (Fin m)) :
    ‖padLeft (n := n) x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_padLeft]

private lemma norm_sq_padRight (y : EuclideanSpace ℝ (Fin n)) :
    ‖padRight (m := m) y‖ ^ 2 = ‖y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_padRight]

private lemma padLeft_injective (m n : ℕ) : Function.Injective (padLeft (m := m) (n := n)) := by
  intro x y hxy
  ext i
  simpa [padLeft_castAdd] using congr_arg (fun z => z (Fin.castAdd n i)) hxy

private lemma padRight_injective (m n : ℕ) :
    Function.Injective (padRight (m := m) (n := n)) := by
  intro x y hxy
  ext j
  simpa [padRight_natAdd] using congr_arg (fun z => z (Fin.natAdd m j)) hxy

@[expose] public section

/-- **Orthogonal sum.** A spherical placement of `G.induce s` in `ℝᵐ` and one of `G.induce sᶜ` in
`ℝⁿ` yield a spherical placement of `G` in `ℝᵐ⁺ⁿ`.

The first part keeps its coordinates and is followed by zeros; the second part is preceded by
zeros. An edge inside either part keeps its inner product. A pair with one vertex in each part
has inner product zero, so the edge has length one. -/
theorem SphereEmbeddable.orthogonalSum {V : Type*} {G : SimpleGraph V} {s : Set V} {m n : ℕ}
    (hm : (G.induce s).SphereEmbeddable m) (hn : (G.induce sᶜ).SphereEmbeddable n) :
    G.SphereEmbeddable (m + n) := by
  classical
  rw [SphereEmbeddable.iff_orthogonal] at hm hn ⊢
  obtain ⟨f, hfInj, hfNorm, hfOrth⟩ := hm
  obtain ⟨g, hgInj, hgNorm, hgOrth⟩ := hn
  let φ : V → EuclideanSpace ℝ (Fin (m + n)) := fun v =>
    if hv : v ∈ s then padLeft (n := n) (f ⟨v, hv⟩)
    else padRight (m := m) (g ⟨v, hv⟩)
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro a b hab
    by_cases ha : a ∈ s
    · by_cases hb : b ∈ s
      · have hφa : φ a = padLeft (f ⟨a, ha⟩) := dite_eq_left ha
        have hφb : φ b = padLeft (f ⟨b, hb⟩) := dite_eq_left hb
        have hfeq := padLeft_injective m n (hφa ▸ hφb ▸ hab)
        exact congrArg Subtype.val (hfInj hfeq)
      · have hφa : φ a = padLeft (f ⟨a, ha⟩) := dite_eq_left ha
        have hφb : φ b = padRight (g ⟨b, hb⟩) := dite_eq_right hb
        have hzero : f ⟨a, ha⟩ = 0 := by
          ext i
          have hcoord := congr_arg (fun z => z (Fin.castAdd n i)) hab
          rw [hφa, hφb, padLeft_castAdd, padRight_castAdd] at hcoord
          exact hcoord
        have hnorm := hfNorm ⟨a, ha⟩
        rw [hzero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hnorm
        norm_num at hnorm
    · by_cases hb : b ∈ s
      · have hφa : φ a = padRight (g ⟨a, ha⟩) := dite_eq_right ha
        have hφb : φ b = padLeft (f ⟨b, hb⟩) := dite_eq_left hb
        have hzero : f ⟨b, hb⟩ = 0 := by
          ext i
          have hcoord := congr_arg (fun z => z (Fin.castAdd n i)) hab
          rw [hφa, hφb, padRight_castAdd, padLeft_castAdd] at hcoord
          exact hcoord.symm
        have hnorm := hfNorm ⟨b, hb⟩
        rw [hzero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hnorm
        norm_num at hnorm
      · have hφa : φ a = padRight (g ⟨a, ha⟩) := dite_eq_right ha
        have hφb : φ b = padRight (g ⟨b, hb⟩) := dite_eq_right hb
        have hgeq := padRight_injective m n (hφa ▸ hφb ▸ hab)
        exact congrArg Subtype.val (hgInj hgeq)
  · intro v
    by_cases hv : v ∈ s
    · rw [show φ v = padLeft (f ⟨v, hv⟩) from dite_eq_left hv, norm_sq_padLeft, hfNorm]
    · rw [show φ v = padRight (g ⟨v, hv⟩) from dite_eq_right hv, norm_sq_padRight, hgNorm]
  · intro u v huv
    by_cases hu : u ∈ s
    · by_cases hv : v ∈ s
      · rw [show φ u = padLeft (f ⟨u, hu⟩) from dite_eq_left hu,
          show φ v = padLeft (f ⟨v, hv⟩) from dite_eq_left hv, inner_padLeft]
        exact hfOrth ⟨u, hu⟩ ⟨v, hv⟩ (by simpa [induce_adj] using huv)
      · rw [show φ u = padLeft (f ⟨u, hu⟩) from dite_eq_left hu,
          show φ v = padRight (g ⟨v, hv⟩) from dite_eq_right hv]
        exact inner_padLeft_padRight _ _
    · by_cases hv : v ∈ s
      · rw [show φ u = padRight (g ⟨u, hu⟩) from dite_eq_right hu,
          show φ v = padLeft (f ⟨v, hv⟩) from dite_eq_left hv, real_inner_comm]
        exact inner_padLeft_padRight _ _
      · rw [show φ u = padRight (g ⟨u, hu⟩) from dite_eq_right hu,
          show φ v = padRight (g ⟨v, hv⟩) from dite_eq_right hv, inner_padRight]
        exact hgOrth ⟨u, hu⟩ ⟨v, hv⟩ (by simpa [induce_adj] using huv)

end

end

end SimpleGraph

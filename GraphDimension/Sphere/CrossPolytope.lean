/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Sphere.Basic

import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The cross-polytope lemma

If `k ≤ d` and a graph on at most `d + k` vertices has `k` disjoint missing edges, given
explicitly as the pairs `a i`, `b i`, then it is on the sphere of radius `1/√2` in `ℝᵈ`: send
`a i ↦ eᵢ/√2` and `b i ↦ -eᵢ/√2` along the first `k` axes, and the remaining vertices injectively
to the unused axes `eⱼ`, `k ≤ j < d`. Distinct points are then orthogonal unless they form a
matched pair, and matched pairs are not edges, so every edge has length one.

This is Frankl–Kupavskii–Swanepoel, Lemma 13: the written proof treats only a matching of size
`d` (the cross-polytope graph itself), while the uses of the lemma need `k = 1, 2, 3`, so the
statement here allows any `k ≤ d`.

## References

Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, J. Combin. Theory Ser. A
**171** (2020), 105146, arXiv 1802.03092, Lemma 13 (l. 332–339).
-/

open scoped InnerProductSpace

namespace SimpleGraph

/-- The unused axis `eⱼ` with `k ≤ j < d` carrying an unmatched vertex. -/
private def crossAxis {d k : ℕ} (hk : k ≤ d) (i : Fin (d - k)) : Fin d :=
  ⟨k + i.val, by have := i.isLt; omega⟩

@[expose] public section

/-- **The cross-polytope lemma** (Frankl–Kupavskii–Swanepoel, Lemma 13, repaired for `k ≤ d`).

If `k ≤ d`, the vertex set has at most `d + k` elements, and `a`, `b` give `k` pairwise distinct
pairs of vertices that are not edges of `G`, then `G` has a spherical placement in `ℝᵈ`: the
matched vertices go to `±eᵢ/√2` and the rest, of which there are at most `d - k`, to the unused
basis vectors. -/
theorem SphereEmbeddable.of_compl_matching {V : Type*} [Fintype V] {G : SimpleGraph V}
    {d k : ℕ} (hk : k ≤ d) (hcard : Fintype.card V ≤ d + k) (a b : Fin k → V)
    (hinj : Function.Injective (Sum.elim a b)) (hnadj : ∀ i, ¬ G.Adj (a i) (b i)) :
    G.SphereEmbeddable d := by
  classical
  set r : ℝ := (Real.sqrt 2)⁻¹ with hr_def
  have hr2 : r ^ 2 = 1 / 2 := by
    rw [hr_def, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hrpos : 0 ≤ r := by rw [hr_def]; positivity
  have hr0 : r ≠ 0 := by rw [hr_def]; positivity
  -- The matched vertices are pairwise distinct.
  have haa : ∀ i j : Fin k, a i = a j → i = j := fun i j h =>
    Sum.inl.inj (hinj (show Sum.elim a b (Sum.inl i) = Sum.elim a b (Sum.inl j) from h))
  have hbb : ∀ i j : Fin k, b i = b j → i = j := fun i j h =>
    Sum.inr.inj (hinj (show Sum.elim a b (Sum.inr i) = Sum.elim a b (Sum.inr j) from h))
  have hab : ∀ i j : Fin k, a i ≠ b j := fun i j h =>
    Sum.inl_ne_inr (hinj (show Sum.elim a b (Sum.inl i) = Sum.elim a b (Sum.inr j) from h))
  -- The matched image, and the vertices left unmatched.
  set M : Finset V := Finset.univ.image (Sum.elim a b) with hM_def
  have hMcard : M.card = 2 * k := by
    rw [hM_def, Finset.card_image_of_injective Finset.univ hinj, Finset.card_univ,
      Fintype.card_sum, Fintype.card_fin]
    ring
  set U : Finset V := Mᶜ with hU_def
  have hUcard : U.card = Fintype.card V - 2 * k := by rw [hU_def, Finset.card_compl, hMcard]
  -- There are at most `d - k` unmatched vertices, so they fit injectively on the unused axes.
  obtain ⟨ψ, hψinj⟩ : ∃ ψ : {x : V // x ∈ U} → Fin (d - k), Function.Injective ψ := by
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (α := {x : V // x ∈ U}) (β := Fin (d - k)) (by rw [Fintype.card_coe, Fintype.card_fin]; omega)
    exact ⟨e, e.injective⟩
  have hposk : ∀ i : Fin (d - k), k ≤ (crossAxis hk i).val := by
    intro i
    change k ≤ k + i.val
    exact Nat.le_add_right k i.val
  have hposinj : Function.Injective (crossAxis hk) := by
    intro i j hij
    have h : k + i.val = k + j.val := congrArg Fin.val hij
    refine Fin.ext ?_
    omega
  -- Membership bookkeeping for the unmatched set.
  have hUma : ∀ (x : V), x ∈ U → ∀ i, a i ≠ x := by
    intro x hx i hi
    rw [hU_def, hM_def, Finset.mem_compl] at hx
    exact hx (Finset.mem_image.mpr ⟨Sum.inl i, Finset.mem_univ _, hi⟩)
  have hUmb : ∀ (x : V), x ∈ U → ∀ i, b i ≠ x := by
    intro x hx i hi
    rw [hU_def, hM_def, Finset.mem_compl] at hx
    exact hx (Finset.mem_image.mpr ⟨Sum.inr i, Finset.mem_univ _, hi⟩)
  have huU : ∀ x : V, (∀ i, ¬ a i = x) → (∀ i, ¬ b i = x) → x ∈ U := by
    intro x ha hb
    rw [hU_def, hM_def, Finset.mem_compl, Finset.mem_image]
    rintro ⟨i, -, hi⟩
    cases i with
    | inl i => exact ha i hi
    | inr i => exact hb i hi
  -- The placement: `a i ↦ eᵢ/√2`, `b i ↦ -eᵢ/√2`, the rest to the unused axes.
  let f : V → EuclideanSpace ℝ (Fin d) := fun x =>
    if h1 : ∃ i : Fin k, a i = x then r • EuclideanSpace.single (Fin.castLE hk h1.choose) (1 : ℝ)
    else if h2 : ∃ i : Fin k, b i = x then
      r • EuclideanSpace.single (Fin.castLE hk h2.choose) (-1 : ℝ)
    else
      r • EuclideanSpace.single
        (crossAxis hk (ψ ⟨x, huU x (not_exists.mp h1) (not_exists.mp h2)⟩)) (1 : ℝ)
  have hfa : ∀ i : Fin k, f (a i) = r • EuclideanSpace.single (Fin.castLE hk i) (1 : ℝ) := by
    intro i
    have hc : ∃ i', a i' = a i := ⟨i, rfl⟩
    change (if h1 : ∃ i', a i' = a i then
        r • EuclideanSpace.single (Fin.castLE hk h1.choose) (1 : ℝ)
      else
        if h2 : ∃ i', b i' = a i then
          r • EuclideanSpace.single (Fin.castLE hk h2.choose) (-1 : ℝ)
        else
          r • EuclideanSpace.single
            (crossAxis hk (ψ ⟨a i, huU (a i) (not_exists.mp h1) (not_exists.mp h2)⟩)) (1 : ℝ)) = _
    exact (dif_pos hc).trans (congrArg
      (fun j : Fin k => r • EuclideanSpace.single (Fin.castLE hk j) (1 : ℝ))
      (haa _ _ hc.choose_spec))
  have hfb : ∀ i : Fin k, f (b i) = r • EuclideanSpace.single (Fin.castLE hk i) (-1 : ℝ) := by
    intro i
    have hna : ¬ ∃ i', a i' = b i := fun h => hab h.choose i h.choose_spec
    have hc : ∃ i', b i' = b i := ⟨i, rfl⟩
    change (if h1 : ∃ i', a i' = b i then
        r • EuclideanSpace.single (Fin.castLE hk h1.choose) (1 : ℝ)
      else
        if h2 : ∃ i', b i' = b i then
          r • EuclideanSpace.single (Fin.castLE hk h2.choose) (-1 : ℝ)
        else
          r • EuclideanSpace.single
            (crossAxis hk (ψ ⟨b i, huU (b i) (not_exists.mp h1) (not_exists.mp h2)⟩)) (1 : ℝ)) = _
    rw [dif_neg hna, dif_pos hc]
    exact congrArg
      (fun j : Fin k => r • EuclideanSpace.single (Fin.castLE hk j) (-1 : ℝ))
      (hbb _ _ hc.choose_spec)
  have hfU : ∀ (x : V) (hx : x ∈ U),
      f x = r • EuclideanSpace.single (crossAxis hk (ψ ⟨x, hx⟩)) (1 : ℝ) := by
    intro x hx
    have hna : ¬ ∃ i', a i' = x := fun h => hUma x hx h.choose h.choose_spec
    have hnb : ¬ ∃ i', b i' = x := fun h => hUmb x hx h.choose h.choose_spec
    change (if h1 : ∃ i', a i' = x then
        r • EuclideanSpace.single (Fin.castLE hk h1.choose) (1 : ℝ)
      else
        if h2 : ∃ i', b i' = x then
          r • EuclideanSpace.single (Fin.castLE hk h2.choose) (-1 : ℝ)
        else
          r • EuclideanSpace.single
            (crossAxis hk (ψ ⟨x, huU x (not_exists.mp h1) (not_exists.mp h2)⟩)) (1 : ℝ)) = _
    rw [dif_neg hna, dif_neg hnb]
  -- Every vertex is matched, or one of the unmatched ones.
  have htri : ∀ x : V, (∃ i : Fin k, a i = x) ∨ (∃ i : Fin k, b i = x) ∨ x ∈ U := by
    intro x
    by_cases h1 : ∃ i, a i = x
    · exact Or.inl h1
    by_cases h2 : ∃ i, b i = x
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (huU x (not_exists.mp h1) (not_exists.mp h2)))
  have hlow : ∀ (i m : Fin d), i.val < k → k ≤ m.val → i ≠ m := by
    intro i m h1 h2 heq
    have h3 : i.val = m.val := congrArg Fin.val heq
    omega
  have hnorm_single : ∀ (ν : Fin d) (c : ℝ), c = 1 ∨ c = -1 →
      ‖(r • EuclideanSpace.single ν c : EuclideanSpace ℝ (Fin d))‖ ^ 2 = 1 / 2 := by
    intro ν c hc
    have hc2 : c ^ 2 = 1 := by rcases hc with h | h <;> rw [h] <;> norm_num
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hrpos, PiLp.norm_single, Real.norm_eq_abs,
      mul_pow, sq_abs, hc2, hr2, mul_one]
  have haxis : ∀ (ν₁ ν₂ : Fin d) (c₁ c₂ : ℝ), c₁ ≠ 0 →
      (r • EuclideanSpace.single ν₁ c₁ : EuclideanSpace ℝ (Fin d)) =
        r • EuclideanSpace.single ν₂ c₂ → ν₁ = ν₂ ∧ c₁ = c₂ := by
    intro ν₁ ν₂ c₁ c₂ hc₁ h
    have h1 := congr_arg (fun z : EuclideanSpace ℝ (Fin d) => z ν₁) h
    rw [PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul, PiLp.single_apply,
      PiLp.single_apply, if_pos rfl] at h1
    by_cases hν : ν₁ = ν₂
    · subst hν
      rw [if_pos rfl] at h1
      exact ⟨rfl, mul_left_cancel₀ hr0 h1⟩
    · rw [if_neg hν, mul_zero] at h1
      rcases mul_eq_zero.mp h1 with h' | h'
      · exact absurd h' hr0
      · exact absurd h' hc₁
  have hinner : ∀ (ν₁ ν₂ : Fin d) (c₁ c₂ : ℝ), ν₁ ≠ ν₂ →
      ⟪(r • EuclideanSpace.single ν₁ c₁ : EuclideanSpace ℝ (Fin d)),
        r • EuclideanSpace.single ν₂ c₂⟫_ℝ = 0 := by
    intro ν₁ ν₂ c₁ c₂ hν
    rw [real_inner_smul_left, real_inner_smul_right, EuclideanSpace.inner_single_left,
      PiLp.single_apply, if_neg hν]
    norm_num
  rw [SphereEmbeddable.iff_orthogonal]
  refine ⟨f, ?_, ?_, ?_⟩
  · -- Injectivity.
    intro x y hxy
    rcases htri x with (⟨i, rfl⟩ | ⟨i, rfl⟩ | hx) <;>
      rcases htri y with (⟨j, rfl⟩ | ⟨j, rfl⟩ | hy)
    · rw [hfa i, hfa j] at hxy
      exact congrArg a (Fin.castLE_injective hk (haxis _ _ 1 1 one_ne_zero hxy).1)
    · rw [hfa i, hfb j] at hxy
      exact absurd (haxis _ _ 1 (-1) one_ne_zero hxy).2 (by norm_num : ¬((1:ℝ) = -1))
    · rw [hfa i, hfU y hy] at hxy
      exact absurd (haxis _ _ 1 1 one_ne_zero hxy).1
        (hlow (Fin.castLE hk i) _ i.isLt (hposk _))
    · rw [hfb i, hfa j] at hxy
      exact absurd (haxis _ _ 1 (-1) one_ne_zero hxy.symm).2 (by norm_num : ¬((1:ℝ) = -1))
    · rw [hfb i, hfb j] at hxy
      exact congrArg b (Fin.castLE_injective hk (haxis _ _ (-1) (-1)
        (by norm_num : (-1:ℝ) ≠ 0) hxy).1)
    · rw [hfb i, hfU y hy] at hxy
      exact absurd (haxis _ _ (-1) 1 (by norm_num : (-1:ℝ) ≠ 0) hxy).1
        (hlow (Fin.castLE hk i) _ i.isLt (hposk _))
    · rw [hfU x hx, hfa j] at hxy
      exact absurd (haxis _ _ 1 1 one_ne_zero hxy).1
        (Ne.symm (hlow (Fin.castLE hk j) _ j.isLt (hposk _)))
    · rw [hfU x hx, hfb j] at hxy
      exact absurd (haxis _ _ 1 (-1) one_ne_zero hxy).2 (by norm_num : ¬((1:ℝ) = -1))
    · rw [hfU x hx, hfU y hy] at hxy
      have h1 : crossAxis hk (ψ ⟨x, hx⟩) = crossAxis hk (ψ ⟨y, hy⟩) :=
        (haxis (crossAxis hk (ψ ⟨x, hx⟩)) (crossAxis hk (ψ ⟨y, hy⟩)) 1 1 one_ne_zero hxy).1
      have h2 : ψ ⟨x, hx⟩ = ψ ⟨y, hy⟩ := hposinj h1
      exact congrArg Subtype.val (hψinj h2)
  · -- Every point lies on the sphere.
    intro x
    rcases htri x with (⟨i, rfl⟩ | ⟨i, rfl⟩ | hx)
    · rw [hfa i]
      exact hnorm_single (Fin.castLE hk i) 1 (Or.inl rfl)
    · rw [hfb i]
      exact hnorm_single (Fin.castLE hk i) (-1) (Or.inr rfl)
    · rw [hfU x hx]
      exact hnorm_single _ 1 (Or.inl rfl)
  · -- Adjacent vertices land on distinct axes, hence on orthogonal points.
    intro u v huv
    rcases htri u with (⟨i, rfl⟩ | ⟨i, rfl⟩ | hu) <;>
      rcases htri v with (⟨j, rfl⟩ | ⟨j, rfl⟩ | hv)
    · rw [hfa i, hfa j]
      exact hinner _ _ 1 1 fun h => huv.ne (by rw [Fin.castLE_injective hk h])
    · rw [hfa i, hfb j]
      exact hinner _ _ 1 (-1) fun h => hnadj i (by
        have h2 := Fin.castLE_injective hk h
        subst h2
        exact huv)
    · rw [hfa i, hfU v hv]
      exact hinner _ _ 1 1 (hlow (Fin.castLE hk i) _ i.isLt (hposk _))
    · rw [hfb i, hfa j]
      exact hinner _ _ (-1) 1 fun h => hnadj i (by
        have h2 := Fin.castLE_injective hk h
        subst h2
        exact huv.symm)
    · rw [hfb i, hfb j]
      exact hinner _ _ (-1) (-1) fun h => huv.ne (by rw [Fin.castLE_injective hk h])
    · rw [hfb i, hfU v hv]
      exact hinner _ _ (-1) 1 (hlow (Fin.castLE hk i) _ i.isLt (hposk _))
    · rw [hfU u hu, hfa j]
      exact hinner _ _ 1 1 (Ne.symm (hlow (Fin.castLE hk j) _ j.isLt (hposk _)))
    · rw [hfU u hu, hfb j]
      exact hinner _ _ 1 (-1) (Ne.symm (hlow (Fin.castLE hk j) _ j.isLt (hposk _)))
    · rw [hfU u hu, hfU v hv]
      have hu' : u ≠ v := huv.ne
      have hne : crossAxis hk (ψ ⟨u, hu⟩) ≠ crossAxis hk (ψ ⟨v, hv⟩) := by
        intro h
        have h2 : ψ ⟨u, hu⟩ = ψ ⟨v, hv⟩ := hposinj h
        exact hu' (congrArg Subtype.val (hψinj h2))
      exact hinner _ _ 1 1 hne

end

end SimpleGraph

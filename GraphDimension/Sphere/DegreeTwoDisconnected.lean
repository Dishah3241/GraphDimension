/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Sphere.Proposition2
public import GraphDimension.Sphere.Cycles

import Mathlib.Tactic

/-!
# Placing disconnected two-regular graphs

A finite collection of component placements can be assembled when each component admits an
offset family with only finitely many collisions against any fixed point. The component families
come from rotating each finite placement after moving its points off the rotation axis.
-/

namespace SimpleGraph

open scoped InnerProductSpace

noncomputable section

private def align (t : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  let q := Real.sqrt (1 + t ^ 2)
  WithLp.toLp 2 fun i =>
    if i.val = 0 then (p 0 + t * p 1) / q else
    if i.val = 1 then (p 1 - t * p 0) / q else p 2

private lemma align_zero (t : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    align t p 0 = (p 0 + t * p 1) / Real.sqrt (1 + t ^ 2) := by
  simp [align, PiLp.toLp_apply]

private lemma align_one (t : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    align t p 1 = (p 1 - t * p 0) / Real.sqrt (1 + t ^ 2) := by
  simp [align, PiLp.toLp_apply]

private lemma align_two (t : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    align t p 2 = p 2 := by
  simp [align, PiLp.toLp_apply]

private def rotationCos (t : ℝ) : ℝ := (1 - t ^ 2) / (1 + t ^ 2)
private def rotationSin (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)

private def rotate (t : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun i =>
    if i.val = 0 then p 0 else
    if i.val = 1 then rotationCos t * p 1 - rotationSin t * p 2 else
      rotationSin t * p 1 + rotationCos t * p 2

private lemma rotate_zero (t : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    rotate t p 0 = p 0 := by simp [rotate, PiLp.toLp_apply]

private lemma rotate_one (t : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    rotate t p 1 = rotationCos t * p 1 - rotationSin t * p 2 := by
  simp [rotate, PiLp.toLp_apply]

private lemma rotate_two (t : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    rotate t p 2 = rotationSin t * p 1 + rotationCos t * p 2 := by
  simp [rotate, PiLp.toLp_apply]

private lemma rotation_sq (t : ℝ) : rotationCos t ^ 2 + rotationSin t ^ 2 = 1 := by
  have h : 1 + t ^ 2 ≠ 0 := by positivity
  unfold rotationCos rotationSin
  field_simp
  ring

private lemma align_inner (t : ℝ) (p q : EuclideanSpace ℝ (Fin 3)) :
    ⟪align t p, align t q⟫_ℝ = ⟪p, q⟫_ℝ := by
  have hsq : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hne : Real.sqrt (1 + t ^ 2) ≠ 0 := by positivity
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [align_zero, align_one, align_two, RCLike.inner_apply, conj_trivial]
  field_simp
  rw [hsq]
  ring

private lemma rotate_inner (t : ℝ) (p q : EuclideanSpace ℝ (Fin 3)) :
    ⟪rotate t p, rotate t q⟫_ℝ = ⟪p, q⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [rotate_zero, rotate_one, rotate_two, RCLike.inner_apply, conj_trivial]
  calc
    _ = p 0 * q 0 + (rotationCos t ^ 2 + rotationSin t ^ 2) *
        (p 1 * q 1 + p 2 * q 2) := by ring
    _ = _ := by rw [rotation_sq]; ring

private lemma align_norm_sq (t : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    ‖align t p‖ ^ 2 = ‖p‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_three, Fin.sum_univ_three, align_zero, align_one, align_two]
  have hsq : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hne : Real.sqrt (1 + t ^ 2) ≠ 0 := by positivity
  field_simp
  rw [hsq]
  ring

private lemma rotate_norm_sq (t : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    ‖rotate t p‖ ^ 2 = ‖p‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_three, Fin.sum_univ_three, rotate_zero, rotate_one, rotate_two]
  calc
    _ = p 0 ^ 2 + (rotationCos t ^ 2 + rotationSin t ^ 2) *
        (p 1 ^ 2 + p 2 ^ 2) := by ring
    _ = _ := by rw [rotation_sq]; ring

private lemma injective_of_norm_inner
    (T : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hnorm : ∀ p, ‖T p‖ ^ 2 = ‖p‖ ^ 2)
    (hinner : ∀ p q, ⟪T p, T q⟫_ℝ = ⟪p, q⟫_ℝ) : Function.Injective T := by
  intro p q hpq
  have hdist : ‖p - q‖ ^ 2 = 0 := by
    calc
      ‖p - q‖ ^ 2 = ‖T p - T q‖ ^ 2 := by
        rw [norm_sub_sq_real, norm_sub_sq_real, hnorm, hnorm, hinner]
      _ = 0 := by rw [hpq, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  exact sub_eq_zero.mp ((norm_eq_zero.mp (sq_eq_zero_iff.mp hdist)))

private lemma align_injective (t : ℝ) : Function.Injective (align t) :=
  injective_of_norm_inner (align t) (align_norm_sq t) (align_inner t)

private lemma rotate_injective (t : ℝ) : Function.Injective (rotate t) :=
  injective_of_norm_inner (rotate t) (rotate_norm_sq t) (rotate_inner t)

private lemma rotationCos_injOn : Set.InjOn rotationCos (Set.Ioo (0 : ℝ) 1) := by
  intro s hs t ht heq
  have hsden : 1 + s ^ 2 ≠ 0 := by positivity
  have htden : 1 + t ^ 2 ≠ 0 := by positivity
  unfold rotationCos at heq
  have hsq : s ^ 2 = t ^ 2 := by
    apply (div_eq_div_iff hsden htden).mp at heq
    nlinarith [heq]
  rcases lt_trichotomy s t with hlt | hst | hgt
  · have hm : 0 < (t - s) * (t + s) :=
      mul_pos (sub_pos.mpr hlt) (by linarith [hs.1, ht.1])
    nlinarith
  · exact hst
  · have hm : 0 < (s - t) * (s + t) :=
      mul_pos (sub_pos.mpr hgt) (by linarith [hs.1, ht.1])
    nlinarith

private lemma rotate_injOn_of_off_axis (p : EuclideanSpace ℝ (Fin 3))
    (hp : p 1 ≠ 0 ∨ p 2 ≠ 0) :
    Set.InjOn (fun t : ℝ => rotate t p) (Set.Ioo 0 1) := by
  intro s hs t ht heq
  have h1 := congrArg (fun q : EuclideanSpace ℝ (Fin 3) => q 1) heq
  have h2 := congrArg (fun q : EuclideanSpace ℝ (Fin 3) => q 2) heq
  rw [rotate_one, rotate_one] at h1
  rw [rotate_two, rotate_two] at h2
  have hcos : (rotationCos s - rotationCos t) * (p 1 ^ 2 + p 2 ^ 2) = 0 := by
    linear_combination p 1 * h1 + p 2 * h2
  have hn : p 1 ^ 2 + p 2 ^ 2 ≠ 0 := by
    rcases hp with hp | hp <;> nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_pos_of_ne_zero hp]
  exact rotationCos_injOn hs ht (sub_eq_zero.mp ((mul_eq_zero.mp hcos).resolve_right hn))

private lemma exists_align_off_axis {V : Type*} [Finite V]
    (b : V → EuclideanSpace ℝ (Fin 3)) (hnorm : ∀ x, ‖b x‖ ^ 2 = 1 / 2) :
    ∃ t : ℝ, ∀ x, (align t (b x)) 1 ≠ 0 ∨ (align t (b x)) 2 ≠ 0 := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  let bad : Finset ℝ := Finset.univ.image fun x : V => b x 1 / b x 0
  obtain ⟨t, _, htbad⟩ :=
    (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).exists_notMem_finite
      (Set.toFinite bad)
  refine ⟨t, fun x => ?_⟩
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hz : b x 2 = 0 := by simpa only [align_two] using h2
  have hq : Real.sqrt (1 + t ^ 2) ≠ 0 := by positivity
  have hxy : b x 1 - t * b x 0 = 0 := by
    rw [align_one] at h1
    exact (div_eq_zero_iff).mp h1 |>.resolve_right hq
  have hx0 : b x 0 ≠ 0 := by
    intro hx0
    have hx1 : b x 1 = 0 := by simpa [hx0] using hxy
    have hn := hnorm x
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] at hn
    simp [hx0, hx1, hz] at hn
  have ht : t = b x 1 / b x 0 := by
    apply (eq_div_iff hx0).2
    nlinarith [hxy]
  apply htbad
  rw [ht]
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

@[expose] public section

/-- A finite spherical placement in three-space can be rotated through a one-parameter family
whose collisions with any fixed point occur at only finitely many offsets in `(0, 1)`. -/
theorem SphereEmbeddable.exists_finite_collision_family
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.SphereEmbeddable 3) :
    ∃ f : ℝ → V → EuclideanSpace ℝ (Fin 3),
      (∀ φ, Function.Injective (f φ) ∧
        (∀ x, ‖f φ x‖ ^ 2 = 1 / 2) ∧
        (∀ x y, G.Adj x y → ⟪f φ x, f φ y⟫_ℝ = 0)) ∧
      ∀ p, {φ : ℝ | φ ∈ Set.Ioo 0 1 ∧ ∃ x, f φ x = p}.Finite := by
  classical
  obtain ⟨b, hb, hnorm, horth⟩ := SphereEmbeddable.iff_orthogonal.mp hG
  obtain ⟨t, hoff⟩ := exists_align_off_axis b hnorm
  let f (φ : ℝ) (x : V) := rotate φ (align t (b x))
  refine ⟨f, ?_, ?_⟩
  · intro φ
    refine ⟨(rotate_injective φ).comp ((align_injective t).comp hb), ?_, ?_⟩
    · intro x
      simpa only [f, rotate_norm_sq, align_norm_sq] using hnorm x
    · intro x y hxy
      simpa only [f, rotate_inner, align_inner] using horth x y hxy
  · intro p
    let fiber (x : V) : Set ℝ := {φ | φ ∈ Set.Ioo 0 1 ∧ f φ x = p}
    have hfiber (x : V) : (fiber x).Finite := by
      apply Set.Subsingleton.finite
      intro a ha a' ha'
      exact rotate_injOn_of_off_axis (align t (b x)) (hoff x) ha.1 ha'.1
        (ha.2.trans ha'.2.symm)
    have hunion : (⋃ x : V, fiber x).Finite := Set.finite_iUnion hfiber
    convert hunion using 1
    ext φ
    simp [fiber]

/-- Assemble placements of the connected components using offsets that avoid the finitely many
points already used. -/
theorem SphereEmbeddable.of_connectedComponents_with_finite_collisions
    {V : Type*} [Finite V] {G : SimpleGraph V}
    (f : (c : G.ConnectedComponent) → ℝ → c → EuclideanSpace ℝ (Fin 3))
    (hf : ∀ c φ, Function.Injective (f c φ) ∧
      (∀ x, ‖f c φ x‖ ^ 2 = 1 / 2) ∧
      (∀ x y, c.toSimpleGraph.Adj x y → ⟪f c φ x, f c φ y⟫_ℝ = 0))
    (hfinite : ∀ (c : G.ConnectedComponent) (p : EuclideanSpace ℝ (Fin 3)),
      {φ : ℝ | φ ∈ Set.Ioo 0 1 ∧ ∃ x : c, f c φ x = p}.Finite) :
    G.SphereEmbeddable 3 := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  let F (φ : G.ConnectedComponent → ℝ) (v : V) : EuclideanSpace ℝ (Fin 3) :=
    f (G.connectedComponentMk v) (φ (G.connectedComponentMk v)) ⟨v, rfl⟩
  have hchoose : ∀ s : Finset G.ConnectedComponent,
      ∃ φ : G.ConnectedComponent → ℝ,
        ∀ u v : V, G.connectedComponentMk u ∈ s → G.connectedComponentMk v ∈ s →
          G.connectedComponentMk u ≠ G.connectedComponentMk v → F φ u ≠ F φ v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨fun _ => 0, ?_⟩
        simp
    | @insert c s hc ih =>
        obtain ⟨φ, hφ⟩ := ih
        let prior : Finset (EuclideanSpace ℝ (Fin 3)) :=
          (Finset.univ.filter fun v : V => G.connectedComponentMk v ∈ s).image (F φ)
        let bad : Finset ℝ := prior.biUnion fun p => (hfinite c p).toFinset
        obtain ⟨t, ht, htbad⟩ :=
          (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).exists_notMem_finite
            (Set.toFinite bad)
        let ψ (d : G.ConnectedComponent) : ℝ := if d = c then t else φ d
        refine ⟨ψ, ?_⟩
        intro u v hu hv hne heq
        simp only [Finset.mem_insert] at hu hv
        have hψc : ψ c = t := by simp [ψ]
        have hψs (d : G.ConnectedComponent) (hd : d ∈ s) : ψ d = φ d := by
          simp [ψ, ne_of_mem_of_not_mem hd hc]
        rcases hu with huc | hus
        · rcases hv with hvc | hvs
          · exact hne (huc.trans hvc.symm)
          · have hpoint : F φ v ∈ prior := by
              simp only [prior, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
                true_and]
              exact ⟨v, hvs, rfl⟩
            have hnot : t ∉ (hfinite c (F φ v)).toFinset := by
              intro hmem
              exact htbad (Finset.mem_biUnion.mpr ⟨F φ v, hpoint, hmem⟩)
            rw [← huc] at hnot
            have htv : f (G.connectedComponentMk u) t ⟨u, rfl⟩ ≠ F φ v := by
              intro h
              apply hnot
              exact (Set.Finite.mem_toFinset (hfinite _ _)).2 ⟨ht, ⟨⟨u, rfl⟩, h⟩⟩
            apply htv
            simpa only [F, huc, hψc, hψs _ hvs] using heq
        · rcases hv with hvc | hvs
          · have hpoint : F φ u ∈ prior := by
              simp only [prior, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
                true_and]
              exact ⟨u, hus, rfl⟩
            have hnot : t ∉ (hfinite c (F φ u)).toFinset := by
              intro hmem
              exact htbad (Finset.mem_biUnion.mpr ⟨F φ u, hpoint, hmem⟩)
            rw [← hvc] at hnot
            have htv : f (G.connectedComponentMk v) t ⟨v, rfl⟩ ≠ F φ u := by
              intro h
              apply hnot
              exact (Set.Finite.mem_toFinset (hfinite _ _)).2 ⟨ht, ⟨⟨v, rfl⟩, h⟩⟩
            apply htv
            simpa only [F, hvc, hψc, hψs _ hus] using heq.symm
          · have hφuv := hφ u v hus hvs hne
            apply hφuv
            simpa only [F, hψs _ hus, hψs _ hvs] using heq
  obtain ⟨φ, hφ⟩ := hchoose Finset.univ
  have hcomponent (v : V) (c : G.ConnectedComponent) (hv : v ∈ c.supp) :
      f c (φ c) ⟨v, hv⟩ = F φ v := by
    have hvc : G.connectedComponentMk v = c := hv
    subst c
    rfl
  rw [SphereEmbeddable.iff_orthogonal]
  refine ⟨F φ, ?_, ?_, ?_⟩
  · intro u v huv
    by_cases hc : G.connectedComponentMk u = G.connectedComponentMk v
    · have hu : (⟨u, rfl⟩ : G.connectedComponentMk u) =
          ⟨v, hc.symm⟩ := by
          apply (hf (G.connectedComponentMk u) (φ (G.connectedComponentMk u))).1
          rw [hcomponent v _ hc.symm]
          exact huv
      exact congrArg Subtype.val hu
    · exact False.elim ((hφ u v (Finset.mem_univ _) (Finset.mem_univ _) hc) huv)
  · intro v
    exact (hf (G.connectedComponentMk v) (φ (G.connectedComponentMk v))).2.1 _
  · intro u v huv
    have hc := ConnectedComponent.connectedComponentMk_eq_of_adj huv
    have hcomm : (G.connectedComponentMk u).toSimpleGraph.Adj
        ⟨u, rfl⟩ ⟨v, hc.symm⟩ := huv
    change ⟪F φ u, F φ v⟫_ℝ = 0
    rw [← hcomponent v _ hc.symm]
    exact (hf (G.connectedComponentMk u) (φ (G.connectedComponentMk u))).2.2 _ _ hcomm

/-- If every connected component of a finite graph has a spherical placement in three-space,
the whole graph has one. -/
theorem SphereEmbeddable.of_connectedComponents
    {V : Type*} [Finite V] {G : SimpleGraph V}
    (h : ∀ c : G.ConnectedComponent, c.toSimpleGraph.SphereEmbeddable 3) :
    G.SphereEmbeddable 3 := by
  classical
  let family (c : G.ConnectedComponent) :=
    Classical.choose (SphereEmbeddable.exists_finite_collision_family (h c))
  have hfamily (c : G.ConnectedComponent) :=
    Classical.choose_spec (SphereEmbeddable.exists_finite_collision_family (h c))
  exact SphereEmbeddable.of_connectedComponents_with_finite_collisions family
    (fun c φ => (hfamily c).1 φ) (fun c p => (hfamily c).2 p)

/-- Every finite two-regular graph has a spherical placement in three-space. -/
theorem SphereEmbeddable.of_degree_two_regular
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hregular : ∀ v, G.degree v = 2) : G.SphereEmbeddable 3 := by
  classical
  apply SphereEmbeddable.of_connectedComponents
  intro c
  apply SphereEmbeddable.of_connected_degree_two c.connected_toSimpleGraph
  intro x
  have hs : G.neighborSet x.1 ⊆ c.supp := by
    intro y hy
    exact c.mem_supp_of_adj_mem_supp x.property hy
  have heq := (G.degree_induce_of_neighborSet_subset hs).trans (hregular x.1)
  rw [← c.toSimpleGraph.ncard_neighborSet]
  rw [← ncard_neighborSet] at heq
  change ((G.induce c.supp).neighborSet x).ncard = 2 at heq
  exact heq

/-- The degree-three base of FKS Proposition 2. -/
theorem SphereEmbeddable.of_degree_le_three
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : ∀ v, G.degree v ≤ 2) : G.SphereEmbeddable 3 :=
  SphereEmbeddable.of_degree_le_three_of_regular
    (fun _H _ hreg => SphereEmbeddable.of_degree_two_regular hreg) h

/-- FKS Proposition 2: every finite graph of maximum degree at most `d - 1` embeds on the
sphere of radius `1 / √2` in `ℝᵈ`. -/
theorem SphereEmbeddable.of_degree_le
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} (hd : 2 ≤ d) (h : ∀ v, G.degree v + 1 ≤ d) : G.SphereEmbeddable d :=
  SphereEmbeddable.of_degree_le_of_regular
    (fun _H _ hreg => SphereEmbeddable.of_degree_two_regular hreg) hd h

end

end

end SimpleGraph

/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Sphere.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Matching

import Mathlib.Tactic

/-!
# Orthogonal placements of cycles on the two-sphere

The coordinate calculations for the umbrella and zigzag placements of cycles are separated from
their finite cyclic indexing. The radius is `1 / √2`, so squared norm is `1 / 2`.
-/

open scoped InnerProductSpace

namespace SimpleGraph

noncomputable section

private instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- A point with cylindrical coordinates `(ρ, θ, h)` in three-space. -/
private def cyclePoint (ρ h : ℝ) (θ : Real.Angle) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun i => if i.val = 0 then ρ * Real.Angle.cos θ else
    if i.val = 1 then ρ * Real.Angle.sin θ else h

private lemma cyclePoint_zero (ρ h : ℝ) (θ : Real.Angle) :
    cyclePoint ρ h θ 0 = ρ * Real.Angle.cos θ := by
  simp [cyclePoint, PiLp.toLp_apply]

private lemma cyclePoint_one (ρ h : ℝ) (θ : Real.Angle) :
    cyclePoint ρ h θ 1 = ρ * Real.Angle.sin θ := by
  simp [cyclePoint, PiLp.toLp_apply]

private lemma cyclePoint_two (ρ h : ℝ) (θ : Real.Angle) :
    cyclePoint ρ h θ 2 = h := by
  simp [cyclePoint, PiLp.toLp_apply]

private lemma cyclePoint_norm_sq (ρ h : ℝ) (θ : Real.Angle) :
    ‖cyclePoint ρ h θ‖ ^ 2 = ρ ^ 2 + h ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
    cyclePoint_zero, cyclePoint_one, cyclePoint_two]
  nlinarith [Real.Angle.cos_sq_add_sin_sq θ]

private lemma cyclePoint_inner_add (ρ h h' : ℝ) (θ δ : Real.Angle) :
    ⟪cyclePoint ρ h θ, cyclePoint ρ h' (θ + δ)⟫_ℝ =
      ρ ^ 2 * Real.Angle.cos δ + h * h' := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [cyclePoint_zero, cyclePoint_one, cyclePoint_two,
    RCLike.inner_apply, conj_trivial]
  rw [Real.Angle.cos_add, Real.Angle.sin_add]
  calc
    _ = ρ ^ 2 * (Real.Angle.cos θ ^ 2 + Real.Angle.sin θ ^ 2) *
        Real.Angle.cos δ + h * h' := by ring
    _ = _ := by rw [Real.Angle.cos_sq_add_sin_sq]; ring

private lemma cyclePoint_angle_eq {ρ h h' : ℝ} {θ ψ : Real.Angle} (hρ : ρ ≠ 0)
    (hEq : cyclePoint ρ h θ = cyclePoint ρ h' ψ) : θ = ψ := by
  have hcos := congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 0) hEq
  have hsin := congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 1) hEq
  rw [cyclePoint_zero, cyclePoint_zero] at hcos
  rw [cyclePoint_one, cyclePoint_one] at hsin
  have hcos' := mul_left_cancel₀ hρ hcos
  have hsin' := mul_left_cancel₀ hρ hsin
  induction θ using Real.Angle.induction_on with
  | h θ =>
    induction ψ using Real.Angle.induction_on with
    | h ψ =>
      exact Real.Angle.cos_sin_inj (by simpa using hcos') (by simpa using hsin')

/-- One full turn, divided into `n` equal angles. -/
private def cycleStep (n : ℕ) : Real.Angle := ((2 * Real.pi / n : ℝ) : Real.Angle)

private lemma cycleStep_nsmul (n : ℕ) (hn : 0 < n) : n • cycleStep n = 0 := by
  rw [cycleStep, ← Real.Angle.natCast_mul_eq_nsmul]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq : (n : ℝ) * (2 * Real.pi / n) = 2 * Real.pi := by
    field_simp
  rw [heq, Real.Angle.coe_two_pi]

private lemma cycleStep_mod (n m : ℕ) (hn : 0 < n) :
    (m % n) • cycleStep n = m • cycleStep n := by
  conv_rhs => rw [← Nat.mod_add_div m n]
  rw [add_nsmul, mul_nsmul, cycleStep_nsmul n hn, smul_zero, add_zero]

private lemma cycleStep_smul (n m : ℕ) :
    m • cycleStep n = ((2 * Real.pi * m / n : ℝ) : Real.Angle) := by
  rw [cycleStep, ← Real.Angle.natCast_mul_eq_nsmul]
  congr 1
  ring

/-- The basic `n` angles are distinct in the angle quotient. -/
private lemma cycleStep_inj (n : ℕ) (hn : 0 < n) {a b : ℕ}
    (ha : a < n) (hb : b < n)
    (h : a • cycleStep n = b • cycleStep n) : a = b := by
  rw [cycleStep_smul, cycleStep_smul] at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hπ : 0 < 2 * Real.pi := by positivity
  have hI (c : ℕ) (hc : c < n) :
      (2 * Real.pi * c / n : ℝ) ∈ Set.Ico 0 (0 + 2 * Real.pi) := by
    constructor
    · positivity
    · rw [zero_add, div_lt_iff₀ hn']
      have hc' : (c : ℝ) < n := by exact_mod_cast hc
      nlinarith [mul_pos hπ (sub_pos.mpr hc')]
  have heq : (2 * Real.pi * a / n : ℝ) = 2 * Real.pi * b / n :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico (hI a ha) (hI b hb)).mp h
  have hab : (a : ℝ) = b := by
    have hprod : (2 * Real.pi) * (a : ℝ) = (2 * Real.pi) * (b : ℝ) :=
      (div_left_inj' hn'.ne').mp heq
    exact mul_left_cancel₀ hπ.ne' hprod
  exact_mod_cast hab

private lemma cycleStep_mul_inj (n k : ℕ) (hn : 0 < n) (hk : Nat.Coprime k n) :
    Function.Injective (fun j : Fin n => (j.val * k) • cycleStep n) := by
  intro i j hij
  change (i.val * k) • cycleStep n = (j.val * k) • cycleStep n at hij
  rw [← cycleStep_mod n (i.val * k) hn,
    ← cycleStep_mod n (j.val * k) hn] at hij
  have hrem : (i.val * k) % n = (j.val * k) % n :=
    cycleStep_inj n hn (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) hij
  have hm : Nat.ModEq n (i.val * k) (j.val * k) := hrem
  have hc : Nat.ModEq n i.val j.val :=
    Nat.ModEq.cancel_right_of_coprime hk.symm hm
  apply Fin.ext
  simpa [Nat.ModEq, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hc

private lemma cycleStep_mod_mul (n m k : ℕ) (hn : 0 < n) :
    ((m % n) * k) • cycleStep n = (m * k) • cycleStep n := by
  calc
    _ = k • ((m % n) • cycleStep n) := by rw [← mul_nsmul, Nat.mul_comm]
    _ = k • (m • cycleStep n) := by rw [cycleStep_mod n m hn]
    _ = _ := by rw [← mul_nsmul, Nat.mul_comm]

private lemma cycleStep_succ (n k : ℕ) (hn : 2 ≤ n) (j : Fin n) :
    (((j + ⟨1, by omega⟩ : Fin n).val) * k) • cycleStep n =
      (j.val * k) • cycleStep n + k • cycleStep n := by
  have hnpos : 0 < n := by omega
  have hval : (j + ⟨1, by omega⟩ : Fin n).val = (j.val + 1) % n := by
    rw [Fin.val_add]
  rw [hval, cycleStep_mod_mul n (j.val + 1) k hnpos,
    Nat.add_mul, one_mul, add_nsmul]

private lemma angle_nsmul_mod (n m : ℕ) (θ : Real.Angle) (hn : n • θ = 0) :
    (m % n) • θ = m • θ := by
  conv_rhs => rw [← Nat.mod_add_div m n]
  rw [add_nsmul, mul_nsmul, hn, smul_zero, add_zero]

private lemma angle_nsmul_succ (n : ℕ) (hn : 2 ≤ n) (θ : Real.Angle)
    (hθ : n • θ = 0) (j : Fin n) :
    (j + ⟨1, by omega⟩ : Fin n).val • θ = j.val • θ + θ := by
  have hval : (j + ⟨1, by omega⟩ : Fin n).val = (j.val + 1) % n := by
    rw [Fin.val_add]
  rw [hval, angle_nsmul_mod n (j.val + 1) θ hθ, add_nsmul, one_nsmul]

private lemma cos_nsmul_pi_sq (j : ℕ) :
    Real.Angle.cos (j • (Real.pi : Real.Angle)) ^ 2 = 1 := by
  rw [← Real.Angle.natCast_mul_eq_nsmul, Real.Angle.cos_coe, Real.cos_nat_mul_pi]
  rcases neg_one_pow_eq_or ℝ j with h | h <;> rw [h] <;> ring

@[expose] public section

/-- An umbrella placement with a coprime angular step whose cosine is negative. -/
theorem SphereEmbeddable.exists_cycle_placement_of_negative_cos (n k : ℕ)
    (hn : 3 ≤ n) (hk : Nat.Coprime k n)
    (hc : Real.Angle.cos (k • ((2 * Real.pi / n : ℝ) : Real.Angle)) < 0) (φ : ℝ) :
    ∃ v : Fin n → EuclideanSpace ℝ (Fin 3), Function.Injective v ∧
      (∀ j, ‖v j‖ ^ 2 = 1 / 2) ∧
      (∀ j, ⟪v j, v (j + ⟨1, by omega⟩)⟫_ℝ = 0) := by
  let c := Real.Angle.cos (k • cycleStep n)
  let q : ℝ := 2 * (1 - c)
  let ρ : ℝ := Real.sqrt (1 / q)
  let h : ℝ := Real.sqrt (-c / q)
  have hc' : c < 0 := hc
  have hq : 0 < q := by dsimp [q]; linarith
  have hρsq : ρ ^ 2 = 1 / q := by
    dsimp [ρ]
    rw [Real.sq_sqrt (by positivity)]
  have hhsq : h ^ 2 = -c / q := by
    dsimp [h]
    rw [Real.sq_sqrt (div_nonneg (by linarith) hq.le)]
  have hρ : ρ ≠ 0 := by
    intro hz
    have : 0 < ρ ^ 2 := by rw [hρsq]; positivity
    simp [hz] at this
  let v : Fin n → EuclideanSpace ℝ (Fin 3) := fun j =>
    cyclePoint ρ h ((φ : Real.Angle) + (j.val * k) • cycleStep n)
  have hinj : Function.Injective v := by
    intro i j hij
    have hangle : (φ : Real.Angle) + (i.val * k) • cycleStep n =
        (φ : Real.Angle) + (j.val * k) • cycleStep n :=
      cyclePoint_angle_eq hρ hij
    exact cycleStep_mul_inj n k (by omega) hk (add_left_cancel hangle)
  have hnorm : ∀ j, ‖v j‖ ^ 2 = 1 / 2 := by
    intro j
    change ‖cyclePoint ρ h _‖ ^ 2 = 1 / 2
    rw [cyclePoint_norm_sq, hρsq, hhsq]
    dsimp [q]
    have hden : 1 - c ≠ 0 := by linarith
    field_simp
    ring
  have horth : ∀ j, ⟪v j, v (j + ⟨1, by omega⟩)⟫_ℝ = 0 := by
    intro j
    have hphase : (φ : Real.Angle) + (((j + ⟨1, by omega⟩ : Fin n).val) * k) •
        cycleStep n = ((φ : Real.Angle) + (j.val * k) • cycleStep n) +
        k • cycleStep n := by
      rw [cycleStep_succ n k (by omega) j]
      abel
    change ⟪cyclePoint ρ h _, cyclePoint ρ h _⟫_ℝ = 0
    rw [hphase, cyclePoint_inner_add, hρsq, ← pow_two h, hhsq]
    dsimp [c, q]
    have hden : 1 - Real.Angle.cos (k • cycleStep n) ≠ 0 := by linarith
    field_simp
    ring
  exact ⟨v, hinj, hnorm, horth⟩

/-- Every odd cycle has an umbrella placement, with arbitrary azimuthal offset. -/
theorem SphereEmbeddable.exists_odd_cycle_placement (n : ℕ) (hn : 3 ≤ n)
    (hodd : Odd n) (φ : ℝ) :
    ∃ v : Fin n → EuclideanSpace ℝ (Fin 3), Function.Injective v ∧
      (∀ j, ‖v j‖ ^ 2 = 1 / 2) ∧
      (∀ j, ⟪v j, v (j + ⟨1, by omega⟩)⟫_ℝ = 0) := by
  obtain ⟨k, hkdef⟩ := hodd
  have hcop : Nat.Coprime k n := by
    rw [hkdef]
    have h := (Nat.coprime_add_mul_left_right k 1 2).2 (by simp)
    simpa only [Nat.mul_comm, Nat.add_comm] using h
  have hnreal : (n : ℝ) = 2 * k + 1 := by exact_mod_cast hkdef
  have hangle : 2 * Real.pi * (k : ℝ) / n = Real.pi - Real.pi / n := by
    rw [hnreal]
    have hden : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
  have hxpos : 0 < Real.pi / n := div_pos Real.pi_pos hnpos
  have hxlt : Real.pi / n < Real.pi / 2 := by
    apply (div_lt_div_iff₀ hnpos (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [mul_lt_mul_of_pos_left hn2 Real.pi_pos]
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxlt⟩
  have hc : Real.Angle.cos (k • ((2 * Real.pi / n : ℝ) : Real.Angle)) < 0 := by
    change Real.Angle.cos (k • cycleStep n) < 0
    rw [cycleStep_smul n k, Real.Angle.cos_coe, hangle, Real.cos_pi_sub]
    linarith
  exact SphereEmbeddable.exists_cycle_placement_of_negative_cos n k hn hcop hc φ

/-- Every even cycle has a zigzag placement, with arbitrary azimuthal offset. -/
theorem SphereEmbeddable.exists_even_cycle_placement (n : ℕ) (hn : 4 ≤ n)
    (heven : Even n) (φ : ℝ) :
    ∃ v : Fin n → EuclideanSpace ℝ (Fin 3), Function.Injective v ∧
      (∀ j, ‖v j‖ ^ 2 = 1 / 2) ∧
      (∀ j, ⟪v j, v (j + ⟨1, by omega⟩)⟫_ℝ = 0) := by
  let c := Real.Angle.cos (cycleStep n)
  let q : ℝ := 2 * (1 + c)
  let ρ : ℝ := Real.sqrt (1 / q)
  let h : ℝ := Real.sqrt (c / q)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hangle : 2 * Real.pi / (n : ℝ) ≤ Real.pi / 2 := by
    apply (div_le_div_iff₀ hnreal (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [mul_le_mul_of_nonneg_left hn4 Real.pi_pos.le]
  have hc : 0 ≤ c := by
    change 0 ≤ Real.cos (2 * Real.pi / n)
    have hxnonneg : (0 : ℝ) ≤ 2 * Real.pi / n := by positivity
    have hminus : -(Real.pi / 2) ≤ (0 : ℝ) := by linarith [Real.pi_pos]
    exact Real.cos_nonneg_of_mem_Icc ⟨hminus.trans hxnonneg, hangle⟩
  have hq : 0 < q := by dsimp [q]; linarith
  have hρsq : ρ ^ 2 = 1 / q := by
    dsimp [ρ]
    rw [Real.sq_sqrt (by positivity)]
  have hhsq : h ^ 2 = c / q := by
    dsimp [h]
    rw [Real.sq_sqrt (div_nonneg hc hq.le)]
  have hρ : ρ ≠ 0 := by
    intro hz
    have : 0 < ρ ^ 2 := by rw [hρsq]; positivity
    simp [hz] at this
  have hπN : n • (Real.pi : Real.Angle) = 0 := by
    obtain ⟨m, rfl⟩ := heven.two_dvd
    rw [mul_nsmul, Real.Angle.two_nsmul_coe_pi, smul_zero]
  let v : Fin n → EuclideanSpace ℝ (Fin 3) := fun j =>
    cyclePoint ρ (h * Real.Angle.cos (j.val • (Real.pi : Real.Angle)))
      ((φ : Real.Angle) + j.val • cycleStep n)
  have hinj : Function.Injective v := by
    intro i j hij
    have hangle' : (φ : Real.Angle) + i.val • cycleStep n =
        (φ : Real.Angle) + j.val • cycleStep n := cyclePoint_angle_eq hρ hij
    exact cycleStep_mul_inj n 1 (by omega) (by simp) (by simpa using add_left_cancel hangle')
  have hnorm : ∀ j, ‖v j‖ ^ 2 = 1 / 2 := by
    intro j
    change ‖cyclePoint ρ (h * Real.Angle.cos (j.val • (Real.pi : Real.Angle))) _‖ ^ 2 = 1 / 2
    rw [cyclePoint_norm_sq, mul_pow, cos_nsmul_pi_sq, mul_one, hρsq, hhsq]
    dsimp [q]
    have hden : 1 + c ≠ 0 := by linarith
    field_simp
  have horth : ∀ j, ⟪v j, v (j + ⟨1, by omega⟩)⟫_ℝ = 0 := by
    intro j
    have hphase : (φ : Real.Angle) + (j + ⟨1, by omega⟩ : Fin n).val • cycleStep n =
        ((φ : Real.Angle) + j.val • cycleStep n) + cycleStep n := by
      rw [angle_nsmul_succ n (by omega) (cycleStep n) (cycleStep_nsmul n (by omega)) j]
      abel
    have hsign : Real.Angle.cos ((j + ⟨1, by omega⟩ : Fin n).val •
        (Real.pi : Real.Angle)) = -Real.Angle.cos (j.val • (Real.pi : Real.Angle)) := by
      rw [angle_nsmul_succ n (by omega) _ hπN j, Real.Angle.cos_add_pi]
    change ⟪cyclePoint ρ (h * Real.Angle.cos (j.val • (Real.pi : Real.Angle))) _,
      cyclePoint ρ (h * Real.Angle.cos ((j + ⟨1, by omega⟩ : Fin n).val •
        (Real.pi : Real.Angle))) _⟫_ℝ = 0
    rw [hphase, hsign, cyclePoint_inner_add]
    calc
      _ = ρ ^ 2 * c - h ^ 2 *
          Real.Angle.cos (j.val • (Real.pi : Real.Angle)) ^ 2 := by ring
      _ = 0 := by rw [cos_nsmul_pi_sq, hρsq, hhsq]; ring
  exact ⟨v, hinj, hnorm, horth⟩

/-- A cycle of any length at least three has an injective orthogonal placement on the sphere,
with an arbitrary azimuthal offset. -/
theorem SphereEmbeddable.exists_cycle_placement (n : ℕ) (hn : 3 ≤ n) (φ : ℝ) :
    ∃ v : Fin n → EuclideanSpace ℝ (Fin 3), Function.Injective v ∧
      (∀ j, ‖v j‖ ^ 2 = 1 / 2) ∧
      (∀ j, ⟪v j, v (j + ⟨1, by omega⟩)⟫_ℝ = 0) := by
  rcases n.even_or_odd with heven | hodd
  · have hn4 : 4 ≤ n := by
      obtain ⟨m, hm⟩ := heven
      omega
    exact SphereEmbeddable.exists_even_cycle_placement n hn4 heven φ
  · exact SphereEmbeddable.exists_odd_cycle_placement n hn hodd φ

/-- The cycle graph on at least three vertices is spherically embeddable in `ℝ³`. -/
theorem SphereEmbeddable.cycleGraph (n : ℕ) (hn : 3 ≤ n) :
    (SimpleGraph.cycleGraph n).SphereEmbeddable 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨v, hvInj, hvNorm, hvOrth⟩ :=
    SphereEmbeddable.exists_cycle_placement (m + 2) (by omega) 0
  rw [SphereEmbeddable.iff_orthogonal]
  refine ⟨v, hvInj, hvNorm, ?_⟩
  intro u w huw
  rcases (SimpleGraph.cycleGraph_adj.mp huw) with h | h
  · have hu : u = w + 1 := (sub_eq_iff_eq_add').mp h
    subst u
    rw [real_inner_comm]
    exact hvOrth w
  · have hw : w = u + 1 := (sub_eq_iff_eq_add').mp h
    subst w
    exact hvOrth u

/-- An injective homomorphism from a cycle to a two-regular graph reflects adjacency. -/
private lemma cycle_copy_reflects_adj {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hregular : ∀ v, G.degree v = 2)
    {n : ℕ} (hn : 3 ≤ n) (f : (SimpleGraph.cycleGraph n).Copy G)
    {u v : Fin n} (huv : G.Adj (f u) (f v)) :
    (SimpleGraph.cycleGraph n).Adj u v := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hcard : Fintype.card ((SimpleGraph.cycleGraph (m + 3)).neighborSet u) =
      Fintype.card (G.neighborSet (f u)) := by
    rw [SimpleGraph.card_neighborSet_eq_degree,
      SimpleGraph.card_neighborSet_eq_degree,
      SimpleGraph.cycleGraph_degree_three_le, hregular]
  have hsurj : Function.Surjective (f.mapNeighborSet u) :=
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨
      (f.mapNeighborSet u).injective, hcard⟩).2
  obtain ⟨w, hw⟩ := hsurj ⟨f v, huv⟩
  have hwv : w.val = v := f.injective (congrArg Subtype.val hw)
  exact hwv ▸ w.property

private lemma cycle_support_card {V : Type*} {G : SimpleGraph V} {v : V}
    {p : G.Walk v v} (hp : p.IsCycle) [DecidableEq V] :
    p.support.toFinset.card = p.length := by
  have hv : v ∈ p.support := by
    have h := p.getVert_mem_support p.length
    rwa [p.getVert_length] at h
  have hsplit : p.support.dropLast ++ [v] = p.support := by
    have h := List.dropLast_append_getLast (l := p.support)
      (List.ne_nil_of_length_pos (by rw [p.length_support]; omega))
    rwa [p.getLast_support] at h
  have hcount : p.support.dropLast.count v = 1 := by
    have htwo := hp.count_support
    rw [← hsplit, List.count_append, List.count_singleton_self] at htwo
    omega
  have hmem : v ∈ p.support.dropLast := List.count_pos_iff.mp (by omega)
  have hfin : (p.support.dropLast ++ [v]).toFinset = p.support.dropLast.toFinset := by
    ext x
    simp only [List.mem_toFinset, List.mem_append]
    constructor
    · rintro (h | hx)
      · exact h
      · rcases List.mem_singleton.mp hx with rfl
        exact hmem
    · exact fun h => Or.inl h
  rw [← hsplit, hfin, List.toFinset_card_of_nodup hp.nodup_dropLast_support,
    List.length_dropLast, p.length_support]
  omega

/-- A connected finite two-regular graph is a cycle and therefore has a spherical placement. -/
theorem SphereEmbeddable.of_connected_degree_two {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected)
    (hregular : ∀ v, G.degree v = 2) : G.SphereEmbeddable 3 := by
  classical
  have hcycles : G.IsCycles := by
    intro w _
    rw [Set.ncard_eq_toFinset_card',
      show (G.neighborSet w).toFinset = G.neighborFinset w from rfl,
      card_neighborFinset_eq_degree, hregular]
  have hnb : ∀ w : V, (G.neighborSet w).Nonempty := by
    intro w
    have hw : (G.neighborFinset w).card = 2 := by
      rw [card_neighborFinset_eq_degree, hregular]
    obtain ⟨x, y, hx, -, -⟩ := Finset.one_lt_card_iff.mp (by rw [hw]; decide)
    exact ⟨x, by simpa using hx⟩
  obtain ⟨v, hvall⟩ := G.connected_iff_exists_forall_reachable.mp hconn
  let c := G.connectedComponentMk v
  have hv : v ∈ c.supp := (c.mem_supp_iff v).mpr rfl
  obtain ⟨p, hp, hpverts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv (hnb v)
  have hsupport : p.support.toFinset = Finset.univ := by
    ext w
    rw [List.mem_toFinset, ← Walk.mem_verts_toSubgraph, hpverts]
    constructor
    · intro _
      exact Finset.mem_univ w
    · intro _
      exact (SimpleGraph.ConnectedComponent.sound (hvall w)).symm
  have hcard : p.length = Fintype.card V := by
    have h := cycle_support_card hp
    rw [hsupport, Finset.card_univ] at h
    exact h.symm
  have hn : 3 ≤ p.length := hp.three_le_length
  have hcopy : SimpleGraph.cycleGraph p.length ⊑ G :=
    (SimpleGraph.cycleGraph_isContained_iff (by omega)).2 ⟨v, p, hp, rfl⟩
  obtain ⟨f⟩ := hcopy
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨f.injective, by simp [hcard]⟩
  let e : SimpleGraph.cycleGraph p.length ≃g G := {
    toEquiv := Equiv.ofBijective f hbij
    map_rel_iff' := by
      intro a b
      constructor
      · exact cycle_copy_reflects_adj hregular hn f
      · exact f.toHom.map_adj
  }
  exact (SphereEmbeddable.of_iso e).mp (SphereEmbeddable.cycleGraph p.length hn)

end

end

end SimpleGraph

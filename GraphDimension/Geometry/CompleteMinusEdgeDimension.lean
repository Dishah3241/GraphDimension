/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

import GraphDimension.Geometry.Equilateral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The dimension of a complete graph with one edge deleted

`Kₙ − e` has dimension `n - 2` for `n ≥ 3`. The upper bound places the `n - 2` vertices other
than the deleted edge's endpoints `u, v` on the scaled basis vectors `(1/√2) eᵢ` of `ℝⁿ⁻²`, and
`u, v` at the two constant points `c ± s · 𝟙` of `ℝⁿ⁻²` that sit at distance one from all of
them, where `c` is the centroid of the scaled axes and `s² = (n - 1)/(2(n - 2))`. Every
remaining edge has length one; the edge between the two apexes is the deleted one, so its length
is unconstrained beyond injectivity.

The lower bound is `card_le_of_equilateral`: deleting `u` leaves `n - 1` vertices that are still
pairwise adjacent, so any unit-distance representation of `Kₙ − e` in `ℝᵐ` has `n - 1 ≤ m + 1`,
that is `n - 2 ≤ m`.

## References

Chaffee and Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J.
Combin. **64(2)** (2016), 327–333, Lemma 2, attributed there to Erdős, Harary and Tutte, *On the
dimension of a graph*, Mathematika **12** (1965), 118–122.
-/

open scoped RealInnerProductSpace

namespace SimpleGraph

noncomputable section

/-- The scale putting two distinct scaled basis vectors at distance one: `(1/√2)² = 1/2`. -/
def baseScale : ℝ := (Real.sqrt 2)⁻¹

/-- The apex half-offset: the two constant points `c ± apexOffset d · 𝟙` sit at distance one
from every scaled basis vector `baseScale • single k 1` of `ℝᵈ`, where `c` is their centroid. -/
def apexOffset (d : ℕ) : ℝ := Real.sqrt ((↑d + 1) / (2 * (d : ℝ) * (d : ℝ)))

/-- The upper apex of the two-apex construction in `ℝᵈ`: a constant vector. -/
def apexP (d : ℕ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun _ => baseScale / (d : ℝ) + apexOffset d

/-- The lower apex of the two-apex construction in `ℝᵈ`: a constant vector. -/
def apexM (d : ℕ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun _ => baseScale / (d : ℝ) - apexOffset d

private lemma baseScale_pos : 0 < baseScale := by
  unfold baseScale
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))

private lemma baseScale_ne_zero : baseScale ≠ 0 := ne_of_gt baseScale_pos

private lemma baseScale_sq : baseScale * baseScale = 1 / 2 := by
  have h2 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold baseScale
  rw [← pow_two, inv_pow, h2, inv_eq_one_div]

private lemma frac_pos {d : ℕ} (hd : 0 < d) : 0 < (↑d + 1) / (2 * (d : ℝ) * (d : ℝ)) := by
  have h1 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  exact div_pos (by linarith) (mul_pos (by linarith) h1)

lemma apexOffset_sq {d : ℕ} (hd : 0 < d) :
    apexOffset d * apexOffset d = (↑d + 1) / (2 * (d : ℝ) * (d : ℝ)) := by
  unfold apexOffset
  rw [← pow_two]
  exact Real.sq_sqrt (le_of_lt (frac_pos hd))

private lemma apexOffset_ne_zero {d : ℕ} (hd : 0 < d) : apexOffset d ≠ 0 := by
  unfold apexOffset
  exact Real.sqrt_ne_zero'.mpr (frac_pos hd)

lemma apexP_apply (d : ℕ) (j : Fin d) :
    apexP d j = baseScale / (d : ℝ) + apexOffset d := rfl

lemma apexM_apply (d : ℕ) (j : Fin d) :
    apexM d j = baseScale / (d : ℝ) - apexOffset d := rfl

private lemma dist_of_sq {d : ℕ} {x y : EuclideanSpace ℝ (Fin d)} (h : dist x y ^ 2 = 1) :
    dist x y = 1 := by
  rw [← Real.sqrt_sq (dist_nonneg (x := x) (y := y)), h, Real.sqrt_one]

/-- Distinct scaled basis vectors carry the `baseScale` to distance one. -/
lemma dist_single_single {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    dist (baseScale • EuclideanSpace.single i (1 : ℝ))
        (baseScale • EuclideanSpace.single j (1 : ℝ)) = 1 := by
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg baseScale_pos.le]
  have horth : ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)⟫ = 0 := by
    rw [EuclideanSpace.inner_single_left]
    simp [hij]
  have hsq : ‖EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ)‖ ^ 2 = 2 := by
    rw [norm_sub_sq_real, horth]
    simp [PiLp.norm_single]
    norm_num
  have hnorm : ‖EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ)‖
      = Real.sqrt 2 := by
    refine (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp ?_
    rw [hsq, Real.sq_sqrt (by positivity)]
  rw [hnorm]
  change (Real.sqrt 2)⁻¹ * Real.sqrt 2 = 1
  exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num))

private lemma single_ne_single {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    baseScale • EuclideanSpace.single i (1 : ℝ) ≠ baseScale • EuclideanSpace.single j (1 : ℝ) := by
  intro hab
  have h := congrArg (fun p : EuclideanSpace ℝ (Fin d) => p i) hab
  simp [hij, baseScale_ne_zero] at h

lemma single_inj {d : ℕ} {i j : Fin d}
    (h : baseScale • EuclideanSpace.single i (1 : ℝ)
      = baseScale • EuclideanSpace.single j (1 : ℝ)) : i = j := by
  by_contra hij
  exact single_ne_single hij h

/-- The distance-one identity for the apex offset: for `x = r/d + s` with `r² = 1/2` and
`s² = (d+1)/(2d)`, the constant point `x 𝟙` is at squared distance one from `r e_k`.

Indeed `(x - r)² + (d-1)x² = d·x² - 2rx + r²`, and the `2rs` cross terms cancel. -/
private lemma apex_coord_sq {d : ℕ} (hd : 0 < d) {r s : ℝ} (hr : r * r = 1 / 2)
    (hs : s * s = (↑d + 1) / (2 * (d : ℝ) * (d : ℝ))) :
    (r / (d : ℝ) + s - r) ^ 2 + ((d : ℝ) - 1) * (r / (d : ℝ) + s) ^ 2 = 1 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have key : (r / (d : ℝ) + s - r) ^ 2 + ((d : ℝ) - 1) * (r / (d : ℝ) + s) ^ 2
      = r * r - r * r / (d : ℝ) + (d : ℝ) * (s * s) := by
    field_simp
    ring
  rw [key, hr, hs]
  field_simp
  ring

/-- Sum over `Fin d` of the squared distance from the constant point `a + b` to the scaled
basis vector `r e_k`: the `k`-coordinate contributes `(a + b - r)²`, the other `d - 1`
coordinates contribute `(a + b)²` each. -/
private lemma sum_split {d : ℕ} (k : Fin d) (a b r : ℝ) :
    ∑ i : Fin d, (a + b - if i = k then r else 0) ^ 2
      = (a + b - r) ^ 2 + ((d : ℝ) - 1) * (a + b) ^ 2 := by
  rw [← Finset.insert_erase (Finset.mem_univ k),
    Finset.sum_insert (Finset.notMem_erase k Finset.univ), ite_eq_left rfl]
  have hle : (1 : ℕ) ≤ d := by
    have hk := k.isLt
    omega
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    have hnat : (d - 1 : ℕ) + 1 = d := by omega
    conv_rhs => rw [← hnat, Nat.cast_add, Nat.cast_one]
    ring
  have hcard : ((Finset.univ.erase k).card : ℝ) = (d : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin, hcast]
  rw [Finset.sum_congr rfl fun i hi => by
      rw [ite_eq_right (Finset.ne_of_mem_erase hi), sub_zero],
    Finset.sum_const, nsmul_eq_mul, hcard]

lemma dist_apexP_base {d : ℕ} (hd : 0 < d) (k : Fin d) :
    dist (apexP d) (baseScale • EuclideanSpace.single k (1 : ℝ)) = 1 := by
  refine dist_of_sq ?_
  rw [EuclideanSpace.dist_sq_eq]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
    (Eq.trans (sum_split k (baseScale / (d : ℝ)) (apexOffset d) baseScale)
      (apex_coord_sq hd baseScale_sq (apexOffset_sq hd)))
  change |apexP d i - (baseScale • EuclideanSpace.single k (1 : ℝ)) i| ^ 2 = _
  rw [sq_abs, apexP_apply]
  simp [smul_eq_mul, PiLp.single_apply, mul_ite, mul_one, mul_zero]

lemma dist_apexM_base {d : ℕ} (hd : 0 < d) (k : Fin d) :
    dist (apexM d) (baseScale • EuclideanSpace.single k (1 : ℝ)) = 1 := by
  refine dist_of_sq ?_
  rw [EuclideanSpace.dist_sq_eq]
  have hsm : (-apexOffset d) * (-apexOffset d) = (↑d + 1) / (2 * (d : ℝ) * (d : ℝ)) := by
    rw [neg_mul_neg]
    exact apexOffset_sq hd
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
    (Eq.trans (sum_split k (baseScale / (d : ℝ)) (-apexOffset d) baseScale)
      (apex_coord_sq hd baseScale_sq hsm))
  change |apexM d i - (baseScale • EuclideanSpace.single k (1 : ℝ)) i| ^ 2 = _
  rw [sq_abs, apexM_apply]
  simp [smul_eq_mul, PiLp.single_apply, mul_ite, mul_one, mul_zero, ← sub_eq_add_neg]

/-- A constant vector of `ℝᵈ` cannot be a scaled basis vector unless its constant value times
`d` equals the scale: summing coordinates makes the collision uniform in `d`. -/
private lemma constVec_ne_single {d : ℕ} {c : ℝ} {z : EuclideanSpace ℝ (Fin d)}
    (hz : ∀ j : Fin d, z j = c) (k : Fin d) (hc : (d : ℝ) * c ≠ baseScale) :
    z ≠ baseScale • EuclideanSpace.single k (1 : ℝ) := by
  intro hab
  refine hc ?_
  have hsum := congrArg (fun p : EuclideanSpace ℝ (Fin d) => ∑ j : Fin d, p j) hab
  simp only [PiLp.smul_apply, smul_eq_mul, hz, PiLp.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at hsum
  exact hsum

lemma apexP_ne_single {d : ℕ} (hd : 0 < d) (k : Fin d) :
    apexP d ≠ baseScale • EuclideanSpace.single k (1 : ℝ) := by
  refine constVec_ne_single (fun j => apexP_apply d j) k ?_
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  intro hcon
  have hexp : (d : ℝ) * (baseScale / (d : ℝ) + apexOffset d)
      = baseScale + (d : ℝ) * apexOffset d := by
    field_simp
  rw [hexp] at hcon
  rcases mul_eq_zero.mp (by linarith : (d : ℝ) * apexOffset d = 0) with h | h
  · exact absurd h hd0
  · exact apexOffset_ne_zero hd h

lemma apexM_ne_single {d : ℕ} (hd : 0 < d) (k : Fin d) :
    apexM d ≠ baseScale • EuclideanSpace.single k (1 : ℝ) := by
  refine constVec_ne_single (fun j => apexM_apply d j) k ?_
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  intro hcon
  have hexp : (d : ℝ) * (baseScale / (d : ℝ) - apexOffset d)
      = baseScale - (d : ℝ) * apexOffset d := by
    field_simp
  rw [hexp] at hcon
  rcases mul_eq_zero.mp (by linarith : (d : ℝ) * apexOffset d = 0) with h | h
  · exact absurd h hd0
  · exact apexOffset_ne_zero hd h

lemma apexP_ne_apexM {d : ℕ} (hd : 0 < d) : apexP d ≠ apexM d := by
  intro hab
  have h := congrArg (fun p : EuclideanSpace ℝ (Fin d) => p (⟨0, hd⟩ : Fin d)) hab
  rw [apexP_apply, apexM_apply] at h
  exact (apexOffset_ne_zero hd) (by linarith)

/-- The `d` vertices other than `u, v` of `Fin (d + 2)` admit an injective labelling by `Fin d`. -/
lemma exists_axis_labelling {d : ℕ} (hd : 0 < d) {u v : Fin (d + 2)} (huv : u ≠ v) :
    ∃ κ : Fin (d + 2) → Fin d, ∀ x y : Fin (d + 2), x ≠ y →
      x ∉ ({u, v} : Set (Fin (d + 2))) → y ∉ ({u, v} : Set (Fin (d + 2))) → κ x ≠ κ y := by
  set S : Finset (Fin (d + 2)) := (Finset.univ.erase u).erase v with hSdef
  have hcard : S.card = d := by
    rw [hSdef, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm huv, Finset.mem_univ v⟩),
      Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]
    omega
  have hfin : Fintype.card ↥S = d := by rw [Fintype.card_coe, hcard]
  refine ⟨fun w => if hw : w ∈ S then Fintype.equivFinOfCardEq hfin ⟨w, hw⟩ else ⟨0, hd⟩, ?_⟩
  intro x y hxy hxS hyS
  have hxu : x ≠ u := fun h => hxS (by rw [h]; simp)
  have hxv : x ≠ v := fun h => hxS (by rw [h]; simp)
  have hyu : y ≠ u := fun h => hyS (by rw [h]; simp)
  have hyv : y ≠ v := fun h => hyS (by rw [h]; simp)
  have hx : x ∈ S := by
    simp only [hSdef, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨hxv, hxu⟩
  have hy : y ∈ S := by
    simp only [hSdef, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨hyv, hyu⟩
  by_contra hcon
  simp only [dite_eq_left hx, dite_eq_left hy] at hcon
  exact hxy (congrArg Subtype.val ((Fintype.equivFinOfCardEq hfin).injective hcon))

/-- **Upper bound** for the dimension of `Kₙ − e`: the complete graph on `d + 2` vertices with
one edge between distinct vertices deleted admits a unit-distance representation in `ℝᵈ`.

The `d` vertices other than the deleted edge's endpoints sit on the scaled basis vectors
`baseScale • single k 1`, and the endpoints sit at the two apex points `c ± apexOffset d · 𝟙`
over them. Erdős–Harary–Tutte; Chaffee–Noble Lemma 2. -/
private theorem upperBound {d : ℕ} (hd : 0 < d) {u v : Fin (d + 2)} (huv : u ≠ v) :
    ((⊤ : SimpleGraph (Fin (d + 2))).deleteEdges {s(u, v)}).UnitDistEmbeddable d := by
  obtain ⟨κ, hκinj⟩ := exists_axis_labelling hd huv
  set S : Finset (Fin (d + 2)) := (Finset.univ.erase u).erase v with hSdef
  have hSmem : ∀ w : Fin (d + 2), w ∈ S ↔ (w ≠ u ∧ w ≠ v) := by
    intro w
    simp only [hSdef, Finset.mem_erase, Finset.mem_univ, and_true]
    exact and_comm
  set f : Fin (d + 2) → EuclideanSpace ℝ (Fin d) := fun w =>
    if w = u then apexP d else if w = v then apexM d
      else baseScale • EuclideanSpace.single (κ w) (1 : ℝ) with hfdef
  have hclass : ∀ w : Fin (d + 2),
      (w = u ∧ f w = apexP d) ∨ (w = v ∧ f w = apexM d) ∨
        (w ∈ S ∧ f w = baseScale • EuclideanSpace.single (κ w) (1 : ℝ)) := by
    intro w
    by_cases hwu : w = u
    · subst hwu
      exact Or.inl ⟨rfl, by simp [hfdef]⟩
    by_cases hwv : w = v
    · subst hwv
      exact Or.inr (Or.inl ⟨rfl, by simp [hfdef, hwu]⟩)
    exact Or.inr (Or.inr ⟨(hSmem w).mpr ⟨hwu, hwv⟩, by simp [hfdef, hwu, hwv]⟩)
  refine ⟨f, ?_, ?_⟩
  · intro a b hab
    rcases hclass a with (⟨ha, hfa⟩ | ⟨ha, hfa⟩ | ⟨ha, hfa⟩) <;>
      rcases hclass b with (⟨hb, hfb⟩ | ⟨hb, hfb⟩ | ⟨hb, hfb⟩)
    · exact ha.trans hb.symm
    · exact absurd (hfa.symm.trans (hab.trans hfb)) (apexP_ne_apexM hd)
    · exact absurd (hfa.symm.trans (hab.trans hfb)) (apexP_ne_single hd _)
    · exact absurd (hfa.symm.trans (hab.trans hfb)) (Ne.symm (apexP_ne_apexM hd))
    · exact ha.trans hb.symm
    · exact absurd (hfa.symm.trans (hab.trans hfb)) (apexM_ne_single hd _)
    · exact absurd (hfa.symm.trans (hab.trans hfb)) (Ne.symm (apexP_ne_single hd _))
    · exact absurd (hfa.symm.trans (hab.trans hfb)) (Ne.symm (apexM_ne_single hd _))
    · by_contra hne
      have haUV : a ∉ ({u, v} : Set (Fin (d + 2))) := by simp [(hSmem a).mp ha]
      have hbUV : b ∉ ({u, v} : Set (Fin (d + 2))) := by simp [(hSmem b).mp hb]
      rw [hfa, hfb] at hab
      exact absurd (single_inj hab) (hκinj a b hne haUV hbUV)
  · intro a b hab
    simp only [deleteEdges_adj, top_adj, Set.mem_singleton_iff] at hab
    obtain ⟨hab, hsym⟩ := hab
    rcases hclass a with (⟨ha, hfa⟩ | ⟨ha, hfa⟩ | ⟨ha, hfa⟩) <;>
      rcases hclass b with (⟨hb, hfb⟩ | ⟨hb, hfb⟩ | ⟨hb, hfb⟩)
    · exact absurd (ha.trans hb.symm) hab
    · rw [ha, hb] at hsym; exact absurd rfl hsym
    · rw [hfa, hfb]; exact dist_apexP_base hd _
    · rw [ha, hb] at hsym
      exact absurd (show s(v, u) = s(u, v) from by rw [Sym2.eq_iff]; simp) hsym
    · exact absurd (ha.trans hb.symm) hab
    · rw [hfa, hfb]; exact dist_apexM_base hd _
    · rw [hfa, hfb, dist_comm]; exact dist_apexP_base hd _
    · rw [hfa, hfb, dist_comm]; exact dist_apexM_base hd _
    · have haUV : a ∉ ({u, v} : Set (Fin (d + 2))) := by simp [(hSmem a).mp ha]
      have hbUV : b ∉ ({u, v} : Set (Fin (d + 2))) := by simp [(hSmem b).mp hb]
      rw [hfa, hfb]
      exact dist_single_single (hκinj a b hab haUV hbUV)

@[expose] public section

/-- The complete graph on `n` vertices with one edge between distinct vertices deleted has
dimension `n - 2`.

The upper bound is `upperBound`: two constant apexes `c ± s · 𝟙` over the scaled basis vectors
of `ℝⁿ⁻²`. The lower bound is `card_le_of_equilateral`: deleting one endpoint of the deleted
edge leaves `n - 1` pairwise-adjacent vertices. Erdős–Harary–Tutte; Chaffee–Noble Lemma 2. -/
theorem hasUnitDistDim_completeGraph_deleteEdge {n : ℕ} (hn : 3 ≤ n) {u v : Fin n} (huv : u ≠ v) :
    ((⊤ : SimpleGraph (Fin n)).deleteEdges {s(u, v)}).HasUnitDistDim (n - 2) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by omega⟩
  have hd : 0 < d := by omega
  have hdd : d + 2 - 2 = d := by omega
  rw [hdd]
  refine ⟨upperBound hd huv, ?_⟩
  rw [mem_lowerBounds]
  intro m hm
  obtain ⟨g, -, hg⟩ := hm
  have hcard : Fintype.card {w : Fin (d + 2) // w ≠ u} = d + 1 := by
    have h1 : Fintype.card {w : Fin (d + 2) // w ∈ (Finset.univ.erase u : Finset (Fin (d + 2)))}
        = d + 1 := by
      rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ,
        Fintype.card_fin]
      omega
    exact (Fintype.card_congr (Equiv.subtypeEquivRight (p := fun w : Fin (d + 2) => w ≠ u)
      (q := fun w : Fin (d + 2) => w ∈ Finset.univ.erase u) (fun w => by simp))).trans h1
  have hle := EuclideanGeometry.card_le_of_equilateral
    (p := fun w : {w : Fin (d + 2) // w ≠ u} => g w)
    fun i j hij =>
      hg i j (by
        rw [deleteEdges_adj, top_adj]
        refine ⟨fun h => hij (Subtype.ext h), fun heq => ?_⟩
        rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
        rcases heq with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact i.2 h1
        · exact j.2 h2)
  rw [hcard] at hle
  omega

end

end

end SimpleGraph

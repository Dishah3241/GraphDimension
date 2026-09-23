/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Ring

/-!
# Lovász's partition lemma

If `Δ(G) ≤ k₁ + k₂ + 1`, the vertices split into `s` and `sᶜ` so that every vertex of `s` has at
most `k₁` neighbours in `s`, and every vertex of `sᶜ` has at most `k₂` neighbours in `sᶜ`. That is
the maximum degree of the two induced subgraphs.

Lovász minimises `(k₂ + 1) · e(s) + (k₁ + 1) · e(sᶜ)`, where `e(t)` is the number of edges with
both ends in `t`. The argument below minimises the same expression with each edge counted twice,
namely the sum of the internal neighbour counts: a positive multiple has the same minimisers, and
moving a vertex that violates a part's degree bound strictly decreases it. A vertex of `s` with at
least `k₁ + 1` neighbours in `s` has at most `k₂` neighbours in `sᶜ`, because the two counts add up
to its degree.

## Source

Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, Lemma 5
(`main.tex` lines 115–117), citing Lovász, *On decomposition of graphs*, Studia Sci. Math. Hungar.
**1** (1966), 237–238. Only the case of two parts is proved; that is the case used for their
Proposition 2.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

open Finset

section Lovasz

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Sum, over vertices of `s`, of the number of neighbours in `s`. Each edge inside `s` is
counted twice. -/
private def internalDegreeSum (s : Finset V) : ℕ :=
  ∑ w ∈ s, (s.filter (G.Adj w)).card

omit [Fintype V] [DecidableEq V] in
private lemma filter_card_eq_sum_ite (s : Finset V) (v : V) :
    (s.filter (G.Adj v)).card = ∑ w ∈ s, if G.Adj v w then 1 else 0 := by
  rw [card_eq_sum_ones, sum_filter]

omit [Fintype V] in
private lemma internalDegreeSum_insert {s : Finset V} {v : V} (hv : v ∉ s) :
    internalDegreeSum (G := G) (insert v s) =
      internalDegreeSum (G := G) s + 2 * (s.filter (G.Adj v)).card := by
  unfold internalDegreeSum
  rw [sum_insert hv]
  have hself : ((insert v s).filter (G.Adj v)).card = (s.filter (G.Adj v)).card := by
    rw [filter_insert, ite_eq_right G.irrefl]
  have hterms : ∀ w ∈ s, ((insert v s).filter (G.Adj w)).card =
      (s.filter (G.Adj w)).card + if G.Adj v w then 1 else 0 := by
    intro w _
    rw [filter_insert]
    by_cases h : G.Adj v w
    · rw [ite_eq_left h.symm, card_insert_of_notMem (fun hmem => hv (mem_filter.mp hmem).1),
        ite_eq_left h]
    · rw [ite_eq_right (fun h' => h h'.symm), ite_eq_right h, add_zero]
  calc
    ((insert v s).filter (G.Adj v)).card + ∑ w ∈ s, ((insert v s).filter (G.Adj w)).card
      = (s.filter (G.Adj v)).card + ∑ w ∈ s,
          ((s.filter (G.Adj w)).card + if G.Adj v w then 1 else 0) := by
        rw [hself, sum_congr rfl hterms]
    _ = (s.filter (G.Adj v)).card + (∑ w ∈ s, (s.filter (G.Adj w)).card +
          ∑ w ∈ s, if G.Adj v w then 1 else 0) := by
        rw [sum_add_distrib]
    _ = (s.filter (G.Adj v)).card + (∑ w ∈ s, (s.filter (G.Adj w)).card +
          (s.filter (G.Adj v)).card) := by
        rw [← filter_card_eq_sum_ite]
    _ = ∑ w ∈ s, (s.filter (G.Adj w)).card + 2 * (s.filter (G.Adj v)).card := by
        rw [Nat.two_mul]
        ac_rfl

omit [Fintype V] in
private lemma internalDegreeSum_erase {s : Finset V} {v : V} (hv : v ∈ s) :
    internalDegreeSum (G := G) s =
      internalDegreeSum (G := G) (s.erase v) + 2 * (s.filter (G.Adj v)).card := by
  have hfilter : ((s.erase v).filter (G.Adj v)).card = (s.filter (G.Adj v)).card := by
    rw [filter_erase, erase_eq_of_notMem]
    intro hmem
    exact G.irrefl (mem_filter.mp hmem).2
  conv_lhs => rw [← insert_erase hv]
  rw [internalDegreeSum_insert (notMem_erase v s), hfilter]

/-- `(k₂ + 1)` times the doubled edge count of `s`, plus `(k₁ + 1)` times that of `sᶜ`. -/
private def lovaszPhi (k₁ k₂ : ℕ) (s : Finset V) : ℕ :=
  (k₂ + 1) * internalDegreeSum (G := G) s + (k₁ + 1) * internalDegreeSum (G := G) sᶜ

private lemma eraseBound (k₁ k₂ A B : ℕ) :
    (k₂ + 1) * A + (k₁ + 1) * (B + 2 * k₂) + 2 * (k₁ + 1) =
      (k₂ + 1) * (A + 2 * (k₁ + 1)) + (k₁ + 1) * B := by
  ring

private lemma insertBound (k₁ k₂ A B : ℕ) :
    (k₂ + 1) * (A + 2 * k₁) + (k₁ + 1) * B + 2 * (k₂ + 1) =
      (k₂ + 1) * A + (k₁ + 1) * (B + 2 * (k₂ + 1)) := by
  ring

private lemma compl_card_le_of_ge {k₁ k₂ d d' : ℕ} (hd : k₁ + 1 ≤ d)
    (hdeg : d + d' ≤ k₁ + k₂ + 1) : d' ≤ k₂ := by
  have h : d' + (k₁ + 1) ≤ k₁ + k₂ + 1 := by
    calc
      d' + (k₁ + 1) ≤ d' + d := Nat.add_le_add_left hd _
      _ = d + d' := Nat.add_comm _ _
      _ ≤ k₁ + k₂ + 1 := hdeg
  have hk : k₁ + k₂ + 1 = (k₁ + 1) + k₂ := by
    calc
      k₁ + k₂ + 1 = k₁ + (k₂ + 1) := Nat.add_assoc _ _ _
      _ = k₁ + (1 + k₂) := by rw [Nat.add_comm k₂ 1]
      _ = k₁ + 1 + k₂ := (Nat.add_assoc k₁ 1 k₂).symm
  rw [hk, Nat.add_comm d'] at h
  exact Nat.le_of_add_le_add_left h

private lemma card_le_of_compl_ge {k₁ k₂ d d' : ℕ} (hd' : k₂ + 1 ≤ d')
    (hdeg : d + d' ≤ k₁ + k₂ + 1) : d ≤ k₁ := by
  have h : d + (k₂ + 1) ≤ k₁ + (k₂ + 1) := by
    calc
      d + (k₂ + 1) ≤ d + d' := Nat.add_le_add_left hd' _
      _ ≤ k₁ + k₂ + 1 := hdeg
      _ = k₁ + (k₂ + 1) := Nat.add_assoc _ _ _
  exact Nat.le_of_add_le_add_right h

private lemma degree_eq_filter_add_filter_compl (s : Finset V) (v : V) :
    G.degree v = (s.filter (G.Adj v)).card + (sᶜ.filter (G.Adj v)).card := by
  rw [← card_neighborFinset_eq_degree]
  have hdisj : Disjoint (s.filter (G.Adj v)) (sᶜ.filter (G.Adj v)) :=
    disjoint_filter_filter disjoint_compl_right
  rw [← card_union_of_disjoint hdisj]
  congr 1
  ext w
  simp only [mem_neighborFinset, mem_union, mem_filter, mem_compl]
  constructor
  · intro h
    by_cases hw : w ∈ s
    · exact Or.inl ⟨hw, h⟩
    · exact Or.inr ⟨hw, h⟩
  · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h

private lemma lovaszPhi_erase_lt {k₁ k₂ : ℕ} {s : Finset V} {v : V} (hv : v ∈ s)
    (hd : k₁ + 1 ≤ (s.filter (G.Adj v)).card)
    (hdeg : (s.filter (G.Adj v)).card + (sᶜ.filter (G.Adj v)).card ≤ k₁ + k₂ + 1) :
    lovaszPhi (G := G) k₁ k₂ (s.erase v) < lovaszPhi (G := G) k₁ k₂ s := by
  let d := (s.filter (G.Adj v)).card
  let d' := (sᶜ.filter (G.Adj v)).card
  have hd' : d' ≤ k₂ := compl_card_le_of_ge hd hdeg
  have hv' : v ∉ sᶜ := fun h => (mem_compl.mp h) hv
  have hA : internalDegreeSum (G := G) s =
      internalDegreeSum (G := G) (s.erase v) + 2 * d :=
    internalDegreeSum_erase hv
  have hB : internalDegreeSum (G := G) (s.erase v)ᶜ =
      internalDegreeSum (G := G) sᶜ + 2 * d' := by
    rw [compl_erase]
    exact internalDegreeSum_insert hv'
  let A := internalDegreeSum (G := G) (s.erase v)
  let B := internalDegreeSum (G := G) sᶜ
  have hle₁ : internalDegreeSum (G := G) (s.erase v)ᶜ ≤ B + 2 * k₂ := by
    rw [hB]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hd') B
  have hinner : A + 2 * (k₁ + 1) ≤ A + 2 * d :=
    Nat.add_le_add_left (Nat.mul_le_mul_left 2 hd) A
  have hchain : lovaszPhi (G := G) k₁ k₂ (s.erase v) + 2 * (k₁ + 1) ≤
      lovaszPhi (G := G) k₁ k₂ s := by
    calc
      lovaszPhi (G := G) k₁ k₂ (s.erase v) + 2 * (k₁ + 1)
        = (k₂ + 1) * A + (k₁ + 1) * internalDegreeSum (G := G) (s.erase v)ᶜ +
            2 * (k₁ + 1) := by
          rw [lovaszPhi]
      _ ≤ (k₂ + 1) * A + (k₁ + 1) * (B + 2 * k₂) + 2 * (k₁ + 1) := by
        exact Nat.add_le_add_right
          (Nat.add_le_add_left (Nat.mul_le_mul_left (k₁ + 1) hle₁) ((k₂ + 1) * A)) _
      _ = (k₂ + 1) * (A + 2 * (k₁ + 1)) + (k₁ + 1) * B := eraseBound k₁ k₂ A B
      _ ≤ (k₂ + 1) * (A + 2 * d) + (k₁ + 1) * B :=
        Nat.add_le_add_right (Nat.mul_le_mul_left (k₂ + 1) hinner) _
      _ = lovaszPhi (G := G) k₁ k₂ s := by
        rw [← hA, lovaszPhi]
  exact lt_of_lt_of_le (Nat.lt_add_of_pos_right (by omega)) hchain

private lemma lovaszPhi_insert_lt {k₁ k₂ : ℕ} {s : Finset V} {v : V} (hv : v ∉ s)
    (hd' : k₂ + 1 ≤ (sᶜ.filter (G.Adj v)).card)
    (hdeg : (s.filter (G.Adj v)).card + (sᶜ.filter (G.Adj v)).card ≤ k₁ + k₂ + 1) :
    lovaszPhi (G := G) k₁ k₂ (insert v s) < lovaszPhi (G := G) k₁ k₂ s := by
  let d := (s.filter (G.Adj v)).card
  let d' := (sᶜ.filter (G.Adj v)).card
  have hd : d ≤ k₁ := card_le_of_compl_ge hd' hdeg
  have hv' : v ∈ sᶜ := mem_compl.mpr hv
  have hA : internalDegreeSum (G := G) (insert v s) =
      internalDegreeSum (G := G) s + 2 * d :=
    internalDegreeSum_insert hv
  have hB : internalDegreeSum (G := G) sᶜ =
      internalDegreeSum (G := G) (insert v s)ᶜ + 2 * d' := by
    rw [compl_insert]
    exact internalDegreeSum_erase hv'
  let A := internalDegreeSum (G := G) s
  let B := internalDegreeSum (G := G) (insert v s)ᶜ
  have hinner : internalDegreeSum (G := G) (insert v s) ≤ A + 2 * k₁ := by
    rw [hA]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hd) A
  have hcompl : B + 2 * (k₂ + 1) ≤ B + 2 * d' :=
    Nat.add_le_add_left (Nat.mul_le_mul_left 2 hd') B
  have hchain : lovaszPhi (G := G) k₁ k₂ (insert v s) + 2 * (k₂ + 1) ≤
      lovaszPhi (G := G) k₁ k₂ s := by
    calc
      lovaszPhi (G := G) k₁ k₂ (insert v s) + 2 * (k₂ + 1)
        = (k₂ + 1) * internalDegreeSum (G := G) (insert v s) + (k₁ + 1) * B +
            2 * (k₂ + 1) := by
          rw [lovaszPhi]
      _ ≤ (k₂ + 1) * (A + 2 * k₁) + (k₁ + 1) * B + 2 * (k₂ + 1) := by
        exact Nat.add_le_add_right
          (Nat.add_le_add_right (Nat.mul_le_mul_left (k₂ + 1) hinner) _) _
      _ = (k₂ + 1) * A + (k₁ + 1) * (B + 2 * (k₂ + 1)) := insertBound k₁ k₂ A B
      _ ≤ (k₂ + 1) * A + (k₁ + 1) * (B + 2 * d') :=
        Nat.add_le_add_left (Nat.mul_le_mul_left (k₁ + 1) hcompl) _
      _ = (k₂ + 1) * A + (k₁ + 1) * internalDegreeSum (G := G) sᶜ := by
        rw [← hB]
      _ = lovaszPhi (G := G) k₁ k₂ s := by
        rw [lovaszPhi]
  exact lt_of_lt_of_le (Nat.lt_add_of_pos_right (by omega)) hchain

/-- **Lovász's partition lemma** (two parts). If every degree is at most `k₁ + k₂ + 1`, some
finset `s` has each of its vertices adjacent to at most `k₁` vertices of `s`, and each vertex
outside `s` adjacent to at most `k₂` vertices of `sᶜ`. -/
theorem exists_partition_degree_le (G : SimpleGraph V) [DecidableRel G.Adj] (k₁ k₂ : ℕ)
    (h : ∀ v, G.degree v ≤ k₁ + k₂ + 1) :
    ∃ s : Finset V, (∀ v ∈ s, (s.filter (G.Adj v)).card ≤ k₁) ∧
      (∀ v ∉ s, (sᶜ.filter (G.Adj v)).card ≤ k₂) := by
  obtain ⟨s, _, hmin⟩ :=
    exists_min_image univ.powerset (lovaszPhi (G := G) k₁ k₂) (powerset_nonempty _)
  refine ⟨s, ?_, ?_⟩
  · intro v hv
    rcases Nat.lt_or_ge k₁ ((s.filter (G.Adj v)).card) with hlt | hle
    · have hdec := lovaszPhi_erase_lt hv (Nat.succ_le_of_lt hlt) <| by
        rw [← degree_eq_filter_add_filter_compl]
        exact h v
      have hmem : s.erase v ∈ univ.powerset := mem_powerset.mpr (subset_univ _)
      exact False.elim (lt_irrefl _ (lt_of_lt_of_le hdec (hmin _ hmem)))
    · exact hle
  · intro v hv
    rcases Nat.lt_or_ge k₂ ((sᶜ.filter (G.Adj v)).card) with hlt | hle
    · have hdec := lovaszPhi_insert_lt hv (Nat.succ_le_of_lt hlt) <| by
        rw [← degree_eq_filter_add_filter_compl]
        exact h v
      have hmem : insert v s ∈ univ.powerset := mem_powerset.mpr (subset_univ _)
      exact False.elim (lt_irrefl _ (lt_of_lt_of_le hdec (hmin _ hmem)))
    · exact hle

/-- **Lovász's partition lemma**, in maximum-degree form: `Δ(G) ≤ k₁ + k₂ + 1` yields parts whose
induced subgraphs have maximum degree at most `k₁` and `k₂`. -/
theorem exists_partition_maxDegree_le (G : SimpleGraph V) [DecidableRel G.Adj] (k₁ k₂ : ℕ)
    (h : G.maxDegree ≤ k₁ + k₂ + 1) :
    ∃ s : Finset V,
      (G.induce ((s : Finset V) : Set V)).maxDegree ≤ k₁ ∧
        (G.induce ((sᶜ : Finset V) : Set V)).maxDegree ≤ k₂ := by
  obtain ⟨s, hs, hsc⟩ :=
    exists_partition_degree_le G k₁ k₂ fun v => (G.degree_le_maxDegree v).trans h
  have induce_degree {t : Finset V} (x : (t : Set V)) :
      (G.induce (t : Set V)).degree x = (t.filter (G.Adj (x : V))).card := by
    rw [← card_neighborFinset_eq_degree]
    refine card_bij (fun w _ => (w : V)) ?_ ?_ ?_
    · intro w hw
      rw [mem_neighborFinset, induce_adj] at hw
      exact mem_filter.mpr ⟨mem_coe.mp w.prop, hw⟩
    · intro w₁ _ w₂ _ h
      exact Subtype.ext h
    · intro b hb
      have hb' := mem_filter.mp hb
      refine ⟨⟨b, mem_coe.mpr hb'.1⟩, ?_, rfl⟩
      rw [mem_neighborFinset, induce_adj]
      exact hb'.2
  refine ⟨s, ?_, ?_⟩
  · exact (G.induce ((s : Finset V) : Set V)).maxDegree_le_of_forall_degree_le k₁ fun v => by
      rw [induce_degree]
      exact hs _ (mem_coe.mp v.prop)
  · exact (G.induce ((sᶜ : Finset V) : Set V)).maxDegree_le_of_forall_degree_le k₂ fun v => by
      rw [induce_degree]
      exact hsc _ (mem_compl.mp (mem_coe.mp v.prop))

end Lovasz

end SimpleGraph

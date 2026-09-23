/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Sphere.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Set.Card

import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.IntervalCases

/-!
# FKS's inductive statement

`S(k)` is the statement Frankl–Kupavskii–Swanepoel induct on: at most `g(k)` edges gives a
unit-distance placement in `ℝᵏ`, and avoiding `K_{k+1}` and `K_{k+2} − K₃` as ordinary
subgraphs gives a placement on the sphere of radius `1/√2`.

## References

Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, J. Combin. Theory Ser. A
**171** (2020), 105146, arXiv 1802.03092, proof of Theorem 3 (`main.tex` lines 342–344).
-/

namespace SimpleGraph

open Finset

@[expose] public section

/-- `Kₙ` with the three edges among the vertices `0, 1, 2` removed: FKS's `K_n − K₃`. -/
def completeMinusTriangle (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ ¬ (i.val < 3 ∧ j.val < 3)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun h' => h.2 ⟨h'.2, h'.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- FKS's edge budget `g`: `g(2) = 3`, `g(3) = 8`, and `g(k) = C(k + 2, 2) − 1` for `k ≥ 4`. -/
def fksBudget : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 3
  | 3 => 8
  | k + 4 => (k + 6).choose 2 - 1

/-- FKS's inductive statement `S(k)`: a graph with at most `g(k)` edges has a unit-distance
placement in `ℝᵏ`, and if it contains neither `K_{k+1}` nor `K_{k+2} − K₃` (as ordinary
subgraphs), a placement on the sphere of radius `1/√2`. -/
def FKSStatement (k : ℕ) : Prop :=
  ∀ (V : Type) [Finite V] (G : SimpleGraph V), G.edgeSet.ncard ≤ fksBudget k →
    G.UnitDistEmbeddable k ∧
      (G.CliqueFree (k + 1) → (completeMinusTriangle (k + 2)).Free G → G.SphereEmbeddable k)

/-- `g(2) = 3`. -/
theorem fksBudget_two : fksBudget 2 = 3 := rfl

/-- `g(3) = 8`. -/
theorem fksBudget_three : fksBudget 3 = 8 := rfl

/-- For `k ≥ 4`, the budget is one less than the number of edges of `K_{k+2}`. -/
theorem fksBudget_of_four_le {k : ℕ} (hk : 4 ≤ k) :
    fksBudget k = (k + 2).choose 2 - 1 := by
  match k with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | k + 4 =>
    rw [fksBudget]

private lemma edgeSet_ncard_eq {V : Type*} (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeSet.ncard = #G.edgeFinset := by
  rw [edgeFinset_card, Set.fintypeCard_eq_ncard]

/-- `Kₙ − K₃` has `C(n, 2) − 3` edges once `n` is large enough to contain the triangle. -/
theorem card_edgeFinset_completeMinusTriangle {n : ℕ} (hn : 3 ≤ n) :
    (completeMinusTriangle n).edgeSet.ncard = n.choose 2 - 3 := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let T : Finset (Sym2 (Fin n)) := {s(i0, i1), s(i0, i2), s(i1, i2)}
  have hi0 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  have hi2 : i0 ≠ i2 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i2] at this
  have hi12 : i1 ≠ i2 := by
    intro h
    have := congrArg Fin.val h
    simp [i1, i2] at this
  have hne01 : s(i0, i1) ≠ s(i0, i2) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨_, h12⟩ | ⟨h02, _⟩
    · exact hi12 h12
    · exact hi2 h02
  have hne02 : s(i0, i1) ≠ s(i1, i2) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h01, _⟩ | ⟨h02, _⟩
    · exact hi0 h01
    · exact hi2 h02
  have hne12 : s(i0, i2) ≠ s(i1, i2) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h01, _⟩ | ⟨_, h21⟩
    · exact hi0 h01
    · exact hi12 h21.symm
  have hTcard : #T = 3 := by
    simp [T, hne01, hne02, hne12, Finset.card_singleton]
  have hval (i : Fin n) (hi : i.val < 3) : i = i0 ∨ i = i1 ∨ i = i2 := by
    rcases i with ⟨val, hltn⟩
    interval_cases val
    · exact Or.inl (Fin.ext rfl)
    · exact Or.inr (Or.inl (Fin.ext rfl))
    · exact Or.inr (Or.inr (Fin.ext rfl))
  have hgraph : completeMinusTriangle n =
      (⊤ : SimpleGraph (Fin n)).deleteEdges (T : Set (Sym2 (Fin n))) := by
    ext i j
    simp only [deleteEdges_adj, top_adj]
    constructor
    · rintro ⟨hij, hnot⟩
      refine ⟨hij, ?_⟩
      intro hmem
      simp only [Finset.mem_coe, T, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h
      · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hnot ⟨by simp [i0], by simp [i1]⟩
        · exact hnot ⟨by simp [i1], by simp [i0]⟩
      · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hnot ⟨by simp [i0], by simp [i2]⟩
        · exact hnot ⟨by simp [i2], by simp [i0]⟩
      · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hnot ⟨by simp [i1], by simp [i2]⟩
        · exact hnot ⟨by simp [i2], by simp [i1]⟩
    · rintro ⟨hij, hmem⟩
      refine ⟨hij, ?_⟩
      intro ⟨hi, hj⟩
      apply hmem
      have hi' := hval i hi
      have hj' := hval j hj
      rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl
      · exact (hij rfl).elim
      · simp [T]
      · simp [T]
      · simp [T]
      · exact (hij rfl).elim
      · simp [T]
      · simp [T]
      · simp [T]
      · exact (hij rfl).elim
  have hsub : T ⊆ (⊤ : SimpleGraph (Fin n)).edgeFinset := by
    intro e he
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at he
    rw [mem_edgeFinset, edgeSet_top, Set.mem_compl_iff, Sym2.mem_diagSet]
    rcases he with rfl | rfl | rfl
    · simpa [Sym2.mk_isDiag_iff] using hi0
    · simpa [Sym2.mk_isDiag_iff] using hi2
    · simpa [Sym2.mk_isDiag_iff] using hi12
  have hfin : (completeMinusTriangle n).edgeFinset =
      (⊤ : SimpleGraph (Fin n)).edgeFinset \ T := by
    rw [hgraph, edgeFinset_deleteEdges]
  rw [edgeSet_ncard_eq, hfin, Finset.card_sdiff_of_subset hsub,
    card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin, hTcard]

end

end SimpleGraph

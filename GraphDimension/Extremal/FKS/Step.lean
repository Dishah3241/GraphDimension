/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.FKS.CaseTwoBridge
public import GraphDimension.Extremal.FKS.CaseOne
public import GraphDimension.Extremal.FKS.BranchB
public import GraphDimension.Extremal.FKS.SmallCore
public import GraphDimension.Sphere.DegreeTwoDisconnected

/-!
# The induction step for FKS Theorem 3

A maximal core supplies both the pruning extension and Branch B's deletion extension.
For a core avoiding the two obstructions, Case 1 supplies a clique-free deletion;
the remaining alternatives are the poles construction and the repaired Case 2 bridge.
-/

@[expose] public section

namespace SimpleGraph

open Finset

/-- The spherical branch for a core avoiding both FKS obstructions. -/
theorem SphereEmbeddable.of_fks_core {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hd : 3 ≤ d) (ih : FKSStatement (d - 1))
    (hdeg : ∀ x, d - 1 ≤ G.degree x) (hbudget : G.edgeSet.ncard ≤ fksBudget d)
    (hK : G.CliqueFree (d + 1)) (hT : (completeMinusTriangle (d + 2)).Free G) :
    G.SphereEmbeddable d := by
  classical
  by_cases hsmall : Fintype.card V ≤ d + 2
  · exact SphereEmbeddable.of_fks_small_core (by omega) hsmall hdeg hK hT
  have hcard : d + 3 ≤ Fintype.card V := by omega
  by_cases hlow : ∀ x, G.degree x + 1 ≤ d
  · exact SphereEmbeddable.of_degree_le (by omega) hlow
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hmax (x : V) : G.degree x ≤ G.degree v := hv ▸ G.degree_le_maxDegree x
  have hdv : d ≤ G.degree v := by
    push Not at hlow
    obtain ⟨x, hx⟩ := hlow
    have := hmax x
    omega
  by_cases huni : ∀ x, x ≠ v → G.Adj v x
  · have hvdeg : G.degree v = Fintype.card V - 1 :=
      (G.degree_eq_card_sub_one v).mpr (fun _ hx => huni _ hx.symm)
    exact SphereEmbeddable.of_fks_pole hd ih huni (by omega)
      (hbudget.trans (fksBudget_le_pred_add hd)) hK hT
  push Not at huni
  obtain ⟨w, hwv, hn⟩ := huni
  obtain ⟨x, hxv, hnx, hKx⟩ := exists_cliqueFree_pair_of_edgeSet_ncard_lt hd hcard hdeg
    (hbudget.trans_lt (fksBudget_lt_branch_count hd)) hK hwv.symm hn hdv
  by_cases hTx : (completeMinusTriangle (d + 1)).Free
      (G.induce {y | y ≠ v ∧ y ≠ x})
  · exact SphereEmbeddable.of_fks_poles hd ih hxv.symm hnx hdv (hdeg x)
      (hbudget.trans (fksBudget_le_pred_add_two_mul hd)) hKx hTx
  · exact SphereEmbeddable.of_fks_case_two hd ih hxv.symm hnx hmax hdv hdeg hbudget
      (not_not.mp hTx)

/-- The degree of a vertex in an induced finite vertex set counts its neighbours there. -/
private lemma fks_degree_induce_finset {V : Type*} [Finite V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (s : Finset V) (v : (s : Set V)) :
    (G.induce (s : Set V)).degree v = (s.filter (G.Adj v.val)).card := by
  classical
  let _ := Fintype.ofFinite V
  rw [← card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun w _ => w.val)
  · intro w hw
    exact mem_filter.mpr ⟨w.property,
      ((G.induce (s : Set V)).mem_neighborFinset _ _).mp hw⟩
  · intro w _ w' _ he
    exact Subtype.ext he
  · intro x hx
    obtain ⟨hxs, hAdj⟩ := mem_filter.mp hx
    exact ⟨⟨x, hxs⟩, (mem_neighborFinset _ _ _).mpr hAdj, rfl⟩

/-- The induction step in Frankl–Kupavskii–Swanepoel's simultaneous Euclidean and
spherical statement. -/
theorem fksStatement_succ {d : ℕ} (hd : 3 ≤ d) (ih : FKSStatement (d - 1)) :
    FKSStatement d := by
  classical
  intro V _ G hbudget
  let _ := Fintype.ofFinite V
  obtain ⟨s, hsdeg, hsmax⟩ := exists_core_maximal (G := G) (d - 2)
  let H := G.induce (s : Set V)
  have hdeg (v : (s : Set V)) : d - 1 ≤ H.degree v := by
    have := hsdeg v.val v.property
    change d - 1 ≤ (G.induce (s : Set V)).degree v
    rw [fks_degree_induce_finset]
    omega
  have hdegSet (v : (s : Set V)) : d - 1 ≤ (H.neighborSet v).ncard := by
    simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hdeg v
  have hinc : H ⊑ G := ⟨Copy.induce G (s : Set V)⟩
  by_cases hT : (completeMinusTriangle (d + 2)).Free H
  · by_cases hK : H.CliqueFree (d + 1)
    · have hH := SphereEmbeddable.of_fks_core hd ih hdeg
        ((ncard_edgeSet_induce_le G (s : Set V)).trans hbudget) hK hT
      have hG := SphereEmbeddable.of_core_maximal (by omega) hsmax hH
      exact ⟨hG.toUnitDist, fun _ _ => hG⟩
    · refine ⟨UnitDistEmbeddable.of_core_containing_clique hd hdegSet hsmax hK hT hbudget,
        ?_⟩
      intro hKG _
      exact (hK (hKG.comap hinc)).elim
  · have hcopy : completeMinusTriangle (d + 2) ⊑ H := not_not.mp hT
    refine ⟨UnitDistEmbeddable.of_core_completeMinusTriangle hd s hdegSet hcopy
      (hbudget.trans_lt (fksBudget_lt_choose hd))
      (hbudget.trans_lt (fksBudget_lt_branch_count hd)), ?_⟩
    intro _ hTG
    exact (hTG (hcopy.trans hinc)).elim

end SimpleGraph

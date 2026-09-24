/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.FKS.Budget
public import GraphDimension.Sphere.CrossPolytope
public import GraphDimension.Sphere.Poles
public import GraphDimension.Extremal.FKS.Deletion

/-!
# Spherical branches of FKS's induction

The small-core placement uses at most one antipodal pair. The induction lemmas use the
spherical half of `FKSStatement`, retaining both ordinary-subgraph avoidance hypotheses.
-/

@[expose] public section

namespace SimpleGraph

open Finset

/-- At most `d` vertices can be placed on distinct coordinate axes. -/
theorem SphereEmbeddable.of_card_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    {d : ℕ} (hcard : Fintype.card V ≤ d) : G.SphereEmbeddable d := by
  apply SphereEmbeddable.of_compl_matching (k := 0) (by omega) (by omega)
    Fin.elim0 Fin.elim0
  · intro i
    cases i with
    | inl i => exact Fin.elim0 i
    | inr i => exact Fin.elim0 i
  · intro i; exact Fin.elim0 i

/-- A graph on at most `d + 1` vertices avoiding `K_{d+1}` fits in a cross-polytope. -/
theorem SphereEmbeddable.of_cliqueFree_card_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    {d : ℕ} (hd : 1 ≤ d) (hcard : Fintype.card V ≤ d + 1) (hfree : G.CliqueFree (d + 1)) :
    G.SphereEmbeddable d := by
  classical
  by_cases hsmall : Fintype.card V ≤ d
  · exact SphereEmbeddable.of_card_le hsmall
  have hcard' : Fintype.card V = d + 1 := by omega
  have hmissing : ∃ a b : V, a ≠ b ∧ ¬ G.Adj a b := by
    by_contra! h
    apply hfree univ
    refine ⟨?_, by simpa using hcard'⟩
    intro a _ b _ hab
    exact h a b hab
  obtain ⟨a, b, hab, hnab⟩ := hmissing
  apply SphereEmbeddable.of_compl_matching hd hcard (fun _ : Fin 1 => a) (fun _ => b)
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => congr 1; exact Subsingleton.elim _ _
      | inr j => exact (hab hij).elim
    | inr i =>
      cases j with
      | inl j => exact (hab hij.symm).elim
      | inr j => congr 1; exact Subsingleton.elim _ _
  · exact fun _ => hnab

/-- A universal vertex enlarges an ordinary copy of `K_n − K₃` by one vertex. -/
theorem completeMinusTriangle_isContained_of_universal_vertex {V : Type*}
    {G : SimpleGraph V} {n : ℕ} {v : V} (huni : ∀ x, x ≠ v → G.Adj v x)
    (hcopy : completeMinusTriangle n ⊑ G.induce {x | x ≠ v}) :
    completeMinusTriangle (n + 1) ⊑ G := by
  classical
  obtain ⟨f⟩ := hcopy
  let p : Fin (n + 1) → V := Fin.lastCases v (fun i => (f i).val)
  refine ⟨{ toHom := { toFun := p, map_rel' := ?_ }, injective' := ?_ }⟩
  · intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact (hij.1 rfl).elim
      | cast j =>
        simpa only [p, Fin.lastCases_last, Fin.lastCases_castSucc] using (huni _ (f j).property)
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simpa only [p, Fin.lastCases_last, Fin.lastCases_castSucc] using
          (huni _ (f i).property).symm
      | cast j =>
        simp only [p, Fin.lastCases_castSucc]
        apply f.toHom.map_rel'
        exact ⟨fun he => hij.1 (congrArg Fin.castSucc he), hij.2⟩
  · intro i j he
    change p i = p j at he
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rfl
      | cast j =>
        simp only [p, Fin.lastCases_last, Fin.lastCases_castSucc] at he
        exact ((f j).property he.symm).elim
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [p, Fin.lastCases_last, Fin.lastCases_castSucc] at he
        exact ((f i).property he).elim
      | cast j =>
        simp only [p, Fin.lastCases_castSucc] at he
        exact congrArg Fin.castSucc (f.injective (Subtype.ext he))

/-- A universal vertex extends every clique of its deletion by one vertex. -/
theorem cliqueFree_induce_ne_of_universal_vertex {V : Type*} {G : SimpleGraph V}
    {n : ℕ} {v : V} (huni : ∀ x, x ≠ v → G.Adj v x) (hfree : G.CliqueFree (n + 1)) :
    (G.induce {x | x ≠ v}).CliqueFree n := by
  classical
  intro K hK
  have hmap := (isNClique_induce_iff _ _ _).mp hK
  apply hfree _ (hmap.insert (a := v) ?_)
  intro w hw
  obtain ⟨x, -, rfl⟩ := mem_map.mp hw
  exact huni x x.property

/-- The universal-vertex branch of FKS, with an additive budget hypothesis. -/
theorem SphereEmbeddable.of_fks_pole {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hd : 3 ≤ d) (ih : FKSStatement (d - 1)) {v : V}
    (huni : ∀ x, x ≠ v → G.Adj v x) (hdeg : d + 2 ≤ G.degree v)
    (hbudget : G.edgeSet.ncard ≤ fksBudget (d - 1) + (d + 2))
    (hK : G.CliqueFree (d + 1)) (hT : (completeMinusTriangle (d + 2)).Free G) :
    G.SphereEmbeddable d := by
  classical
  have hE : (G.induce {x | x ≠ v}).edgeSet.ncard ≤ fksBudget (d - 1) := by
    rw [ncard_edgeSet_induce_ne]; omega
  have hK' : (G.induce {x | x ≠ v}).CliqueFree ((d - 1) + 1) := by
    have := cliqueFree_induce_ne_of_universal_vertex huni hK
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ d)] using this
  have hT' : (completeMinusTriangle ((d - 1) + 2)).Free (G.induce {x | x ≠ v}) := by
    intro hcopy
    have hc := completeMinusTriangle_isContained_of_universal_vertex huni hcopy
    have heq : (d - 1) + 2 + 1 = d + 2 := by omega
    exact hT (heq ▸ hc)
  have hs := (ih _ _ hE).2 hK' hT'
  have hp := hs.pole
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ d)] using hp

/-- The two-pole branch when a distinct nonadjacent pair leaves neither smaller obstruction. -/
theorem SphereEmbeddable.of_fks_poles {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hd : 3 ≤ d) (ih : FKSStatement (d - 1)) {v w : V}
    (hvw : v ≠ w) (hnadj : ¬ G.Adj v w) (hdv : d ≤ G.degree v)
    (hdw : d - 1 ≤ G.degree w)
    (hbudget : G.edgeSet.ncard ≤ fksBudget (d - 1) + (2 * d - 1))
    (hK : (G.induce {x | x ≠ v ∧ x ≠ w}).CliqueFree d)
    (hT : (completeMinusTriangle (d + 1)).Free (G.induce {x | x ≠ v ∧ x ≠ w})) :
    G.SphereEmbeddable d := by
  classical
  have hE : (G.induce {x | x ≠ v ∧ x ≠ w}).edgeSet.ncard ≤ fksBudget (d - 1) := by
    rw [ncard_edgeSet_induce_ne_pair G hvw hnadj]; omega
  have hK' : (G.induce {x | x ≠ v ∧ x ≠ w}).CliqueFree ((d - 1) + 1) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ d)] using hK
  have hT' : (completeMinusTriangle ((d - 1) + 2)).Free
      (G.induce {x | x ≠ v ∧ x ≠ w}) := by
    convert hT using 1 <;> congr 1 <;> omega
  have hs := (ih _ _ hE).2 hK' hT'
  have hp := hs.poles hvw hnadj
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ d)] using hp

end SimpleGraph

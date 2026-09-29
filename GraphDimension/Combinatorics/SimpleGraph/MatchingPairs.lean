/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Matching

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Sum.Basic

/-!
# Indexed pairs of a perfect matching

A perfect matching on `2d` vertices pairs each vertex with a unique mate. That mate map is a
fixed-point-free involution. Ordering the vertices and keeping the smaller endpoint of each
pair enumerates the `d` edges by maps `Fin d → V` whose joint map on `Fin d ⊕ Fin d` is
injective.
-/

@[expose] public section

namespace SimpleGraph

-- M1
/-- **Indexed matching pairs.**

A perfect matching on a vertex set of cardinality `2d` consists of `d` edges that can be
indexed by `Fin d` so that the `2d` endpoints are pairwise distinct. -/
theorem Subgraph.IsPerfectMatching.exists_indexed_edges
    {V : Type*} [Finite V] {H : SimpleGraph V} {d : ℕ}
    {M : H.Subgraph} (hM : M.IsPerfectMatching)
    (hcard : Nat.card V = 2 * d) :
    ∃ a b : Fin d → V, Function.Injective (Sum.elim a b) ∧
      ∀ i, M.Adj (a i) (b i) := by
  classical
  have := Fintype.ofFinite V
  have huniq (v : V) : ∃! w, M.Adj v w :=
    (Subgraph.isPerfectMatching_iff.mp hM) v
  -- The unique mate is a fixed-point-free involution.
  let mate : V → V := fun v => (huniq v).choose
  have hmate_adj (v : V) : M.Adj v (mate v) := (huniq v).choose_spec.1
  have hmate_invol (v : V) : mate (mate v) = v :=
    ((huniq (mate v)).unique (hmate_adj v).symm (hmate_adj (mate v))).symm
  have hmate_ne (v : V) : mate v ≠ v := (hmate_adj v).ne.symm
  have hmate_inj : Function.Injective mate :=
    Function.LeftInverse.injective hmate_invol
  let ι : V ≃ Fin (2 * d) := Finite.equivFinOfCardEq hcard
  -- One representative from each pair: the endpoint with the smaller index.
  let reps : Finset V := Finset.univ.filter fun v => ι v < ι (mate v)
  have himage : reps.image mate =
      Finset.univ.filter (fun v => ι (mate v) < ι v) := by
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      have hlt : ι w < ι (mate w) := (Finset.mem_filter.mp hw).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hmate_invol]; exact hlt⟩
    · intro hv
      have hlt : ι (mate v) < ι v := (Finset.mem_filter.mp hv).2
      exact Finset.mem_image.mpr ⟨mate v,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hmate_invol]; exact hlt⟩,
        hmate_invol v⟩
  have hdisj : Disjoint reps (reps.image mate) := by
    rw [himage, Finset.disjoint_filter]
    intro v _ hlt hgt
    exact lt_asymm hlt hgt
  have hunion : reps ∪ reps.image mate = Finset.univ := by
    rw [himage]
    ext v
    constructor
    · intro _
      exact Finset.mem_univ v
    · intro _
      have hne : ι v ≠ ι (mate v) := ι.injective.ne (hmate_ne v).symm
      obtain hlt | hgt := hne.lt_or_gt
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hlt⟩))
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hgt⟩))
  have hreps : reps.card = d := by
    have himg : (reps.image mate).card = reps.card :=
      Finset.card_image_of_injective reps hmate_inj
    have hsum : (reps ∪ reps.image mate).card =
        reps.card + (reps.image mate).card :=
      Finset.card_union_of_disjoint hdisj
    have hvu : (Finset.univ : Finset V).card = 2 * d := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
    have htwo : 2 * reps.card = 2 * d := by
      calc
        2 * reps.card = reps.card + reps.card := by omega
        _ = reps.card + (reps.image mate).card := by rw [himg]
        _ = (reps ∪ reps.image mate).card := by rw [← hsum]
        _ = (Finset.univ : Finset V).card := by rw [hunion]
        _ = 2 * d := hvu
    omega
  let ε : reps ≃ Fin d := reps.equivFinOfCardEq hreps
  let a : Fin d → V := fun i => (ε.symm i).val
  let b : Fin d → V := fun i => mate (a i)
  have hinja : Function.Injective a := by
    intro i j hij
    exact ε.symm.injective (Subtype.ext hij)
  have hinjb : Function.Injective b := hmate_inj.comp hinja
  have hends (i j) : a i ≠ b j := by
    intro hij
    have hltj : ι (a j) < ι (mate (a j)) :=
      (Finset.mem_filter.mp (ε.symm j).property).2
    have hlti : ι (a i) < ι (mate (a i)) :=
      (Finset.mem_filter.mp (ε.symm i).property).2
    have hcontra : ι (mate (a j)) < ι (a j) := by
      calc
        ι (mate (a j)) = ι (a i) := by rw [hij]
        _ < ι (mate (a i)) := hlti
        _ = ι (mate (mate (a j))) := by rw [hij]
        _ = ι (a j) := by rw [hmate_invol]
    exact lt_asymm hltj hcontra
  exact ⟨a, b, hinja.sumElim hinjb hends, fun i => hmate_adj (a i)⟩

end SimpleGraph

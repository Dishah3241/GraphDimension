/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Set.Card

import GraphDimension.Combinatorics.SimpleGraph.TwoRegularSeven
import GraphDimension.Geometry.Cocktail
import GraphDimension.Geometry.CompleteGraph
import GraphDimension.Geometry.CompleteMinusEdgeDimension
import GraphDimension.Geometry.Extend
import GraphDimension.Geometry.UnitDistanceComap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Order.Bounds.Basic

/-!
# Graphs with at most fourteen edges embed in `ℝ⁴`

The lower-bound half of Chaffee–Noble Theorem 10: a finite graph with at most fourteen edges has a
unit-distance representation in `ℝ⁴`.

## References

Chaffee and Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J.
Combin. **64(2)** (2016), 327–333, Theorem 10.
-/

namespace SimpleGraph

noncomputable section

open Finset Function

variable {V : Type*}

private lemma choose_two_le_of_le_three {k : ℕ} (hk : k ≤ 3) : k.choose 2 ≤ k := by
  rcases k with _ | _ | _ | _ | _
  · decide
  · decide
  · decide
  · decide
  · omega

/-- `G` with every edge among the neighbours of `u` filled in. Edges at `u` are unchanged. -/
private def addNeighborClique (G : SimpleGraph V) (u : V) : SimpleGraph V where
  Adj v w := G.Adj v w ∨ (G.Adj u v ∧ G.Adj u w ∧ v ≠ w)
  symm := ⟨fun v w h => by
    rcases h with h | ⟨huv, huw, hne⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨huw, huv, hne.symm⟩⟩
  loopless := ⟨fun v h => by
    rcases h with h | ⟨-, -, hne⟩
    · exact G.irrefl h
    · exact hne rfl⟩

@[simp] private lemma addNeighborClique_adj (G : SimpleGraph V) (u v w : V) :
    (addNeighborClique G u).Adj v w ↔ G.Adj v w ∨ (G.Adj u v ∧ G.Adj u w ∧ v ≠ w) := Iff.rfl

private lemma le_addNeighborClique (G : SimpleGraph V) (u : V) : G ≤ addNeighborClique G u := by
  intro v w h
  rw [addNeighborClique_adj]
  exact Or.inl h

private lemma neighborSet_addNeighborClique (G : SimpleGraph V) (u : V) :
    (addNeighborClique G u).neighborSet u = G.neighborSet u := by
  ext v
  simp only [mem_neighborSet, addNeighborClique_adj]
  constructor
  · rintro (h | ⟨h, -, -⟩)
    · exact h
    · exact (G.irrefl h).elim
  · exact Or.inl

private lemma isClique_addNeighborClique (G : SimpleGraph V) (u : V) :
    (addNeighborClique G u).IsClique ((addNeighborClique G u).neighborSet u) := by
  intro v hv w hw hvw
  rw [neighborSet_addNeighborClique] at hv hw
  rw [addNeighborClique_adj]
  exact Or.inr ⟨hv, hw, hvw⟩

private lemma edgeSet_ncard_eq (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeSet.ncard = #G.edgeFinset := by
  rw [edgeFinset_card, Set.fintypeCard_eq_ncard]

/-- Deleting a vertex of degree at most three and filling the clique on its neighbours does not
raise the number of edges: at most `C(k, 2) ≤ k` edges are added and `k` edges are removed. -/
private theorem ncard_induce_addNeighborClique_le [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {u : V} (hu : G.degree u ≤ 3) :
    ((addNeighborClique G u).induce {v | v ≠ u}).edgeSet.ncard ≤ G.edgeSet.ncard := by
  classical
  let G' := addNeighborClique G u
  let s : Set V := {v | v ≠ u}
  let A : Finset (Sym2 V) := G.edgeFinset.filter fun e => u ∉ e
  let B : Finset (Sym2 V) := (G.neighborFinset u).offDiag.image Sym2.mk.uncurry
  have hA : A = (G.deleteIncidenceSet u).edgeFinset := by
    rw [edgeFinset_deleteIncidenceSet_eq_filter]
  have hAcard : #A = #G.edgeFinset - G.degree u := by
    rw [hA, card_edgeFinset_deleteIncidenceSet]
  have hBcard : #B = (G.degree u).choose 2 := by
    rw [Sym2.card_image_offDiag, card_neighborFinset_eq_degree]
  have hsub : G'.edgeFinset ∩ s.toFinset.sym2 ⊆ A ∪ B := by
    intro e he
    obtain ⟨heG', hesym⟩ := Finset.mem_inter.mp he
    induction e using Sym2.ind with
    | h v w =>
      rw [mem_edgeFinset, mem_edgeSet, addNeighborClique_adj] at heG'
      rw [Finset.mk_mem_sym2_iff, Set.mem_toFinset, Set.mem_toFinset, Set.mem_ofPred_eq,
        Set.mem_ofPred_eq] at hesym
      rcases heG' with hG | ⟨huv, huw, hvw⟩
      · refine Finset.mem_union.mpr (Or.inl ?_)
        rw [Finset.mem_filter, mem_edgeFinset, mem_edgeSet]
        refine ⟨hG, ?_⟩
        intro hu
        rcases Sym2.mem_iff.mp hu with rfl | rfl
        · exact hesym.1 rfl
        · exact hesym.2 rfl
      · refine Finset.mem_union.mpr (Or.inr ?_)
        refine Finset.mem_image.mpr ⟨(v, w), ?_, rfl⟩
        rw [Finset.mem_offDiag, mem_neighborFinset, mem_neighborFinset]
        exact ⟨huv, huw, hvw⟩
  have hdegE : G.degree u ≤ #G.edgeFinset := G.degree_le_card_edgeFinset u
  have hchoose : (G.degree u).choose 2 ≤ G.degree u := choose_two_le_of_le_three hu
  have hinduce :
      #((G'.induce s).edgeFinset) ≤ #G.edgeFinset := by
    calc
      #((G'.induce s).edgeFinset)
          = #(((G'.induce s).edgeFinset).map (Embedding.subtype (· ∈ s)).sym2Map) := by
            rw [Finset.card_map]
        _ = #(G'.edgeFinset ∩ s.toFinset.sym2) := by rw [map_edgeFinset_induce]
        _ ≤ #(A ∪ B) := Finset.card_le_card hsub
        _ ≤ #A + #B := Finset.card_union_le _ _
        _ = #G.edgeFinset - G.degree u + (G.degree u).choose 2 := by rw [hAcard, hBcard]
        _ ≤ #G.edgeFinset - G.degree u + G.degree u := Nat.add_le_add_left hchoose _
        _ = #G.edgeFinset := Nat.sub_add_cancel hdegE
  rw [edgeSet_ncard_eq, edgeSet_ncard_eq]
  exact hinduce

private theorem unitDistEmbeddable_four_of_card_le_five [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V ≤ 5) : G.UnitDistEmbeddable 4 := by
  classical
  let f : V ↪ Fin 5 :=
    (Embedding.nonempty_of_card_le (by simpa [Fintype.card_fin] using hV)).some
  exact UnitDistEmbeddable.comap
    (show G →g (⊤ : SimpleGraph (Fin 5)) from ⟨f, fun huv => by
      rw [top_adj]
      exact f.injective.ne huv.ne⟩)
    f.injective (hasUnitDistDim_completeGraph 5).1

private theorem unitDistEmbeddable_four_fin_six (G : SimpleGraph (Fin 6))
    (hE : G.edgeSet.ncard ≤ 14) : G.UnitDistEmbeddable 4 := by
  classical
  have htop : #(⊤ : SimpleGraph (Fin 6)).edgeFinset = 15 := by
    rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
    decide
  have htopN : (⊤ : SimpleGraph (Fin 6)).edgeSet.ncard = 15 := by
    rw [edgeSet_ncard_eq, htop]
  have hne : G ≠ ⊤ := by
    intro hEq
    subst hEq
    rw [htopN] at hE
    omega
  obtain ⟨u, v, huv, hna⟩ := ne_top_iff_exists_not_adj.mp hne
  have hle : G ≤ (⊤ : SimpleGraph (Fin 6)).deleteEdges {s(u, v)} := by
    intro a b hab
    rw [deleteEdges_adj, top_adj]
    refine ⟨hab.ne, ?_⟩
    intro hmem
    rcases Sym2.eq_iff.mp (by simpa using hmem) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hna hab
    · exact hna hab.symm
  exact UnitDistEmbeddable.of_le hle
    (hasUnitDistDim_completeGraph_deleteEdge (by decide : 3 ≤ 6) huv).1

private inductive Tag
  | g | a | b | c | d | e | f
  deriving DecidableEq

private def tag (g a b c d e fv x : Fin 7) : Tag :=
  if x = g then .g else if x = a then .a else if x = b then .b else if x = c then .c
  else if x = d then .d else if x = e then .e else if x = fv then .f else .g

private def part (g a b c d e fv x : Fin 7) : Σ i : Fin 4, Fin (![1, 2, 2, 2] i) :=
  match tag g a b c d e fv x with
  | .g => ⟨0, (finCongr (by decide : ![1, 2, 2, 2] (0 : Fin 4) = 1)).symm 0⟩
  | .a => ⟨1, (finCongr (by decide : ![1, 2, 2, 2] (1 : Fin 4) = 2)).symm 0⟩
  | .b => ⟨1, (finCongr (by decide : ![1, 2, 2, 2] (1 : Fin 4) = 2)).symm 1⟩
  | .c => ⟨2, (finCongr (by decide : ![1, 2, 2, 2] (2 : Fin 4) = 2)).symm 0⟩
  | .d => ⟨2, (finCongr (by decide : ![1, 2, 2, 2] (2 : Fin 4) = 2)).symm 1⟩
  | .e => ⟨3, (finCongr (by decide : ![1, 2, 2, 2] (3 : Fin 4) = 2)).symm 0⟩
  | .f => ⟨3, (finCongr (by decide : ![1, 2, 2, 2] (3 : Fin 4) = 2)).symm 1⟩

private theorem tag_cases {g a b c d e fv : Fin 7} (hn : List.Nodup [g, a, b, c, d, e, fv])
    (x : Fin 7) :
    tag g a b c d e fv x = .g ∧ x = g ∨ tag g a b c d e fv x = .a ∧ x = a ∨
      tag g a b c d e fv x = .b ∧ x = b ∨ tag g a b c d e fv x = .c ∧ x = c ∨
      tag g a b c d e fv x = .d ∧ x = d ∨ tag g a b c d e fv x = .e ∧ x = e ∨
      tag g a b c d e fv x = .f ∧ x = fv := by
  have hineq :
      g ≠ a ∧ g ≠ b ∧ g ≠ c ∧ g ≠ d ∧ g ≠ e ∧ g ≠ fv ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ fv ∧
      b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ fv ∧
      c ≠ d ∧ c ≠ e ∧ c ≠ fv ∧
      d ≠ e ∧ d ≠ fv ∧
      e ≠ fv := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hn
    tauto
  obtain ⟨hga, hgb, hgc, hgd, hge, hgf, hab, hac, had, hae, haf, hbc, hbd, hbe, hbf, hcd, hce,
      hcf, hde, hdf, hef⟩ := hineq
  have hcov : x = g ∨ x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e ∨ x = fv := by
    have hcard : ([g, a, b, c, d, e, fv].toFinset).card = 7 := by
      simpa using List.toFinset_card_of_nodup hn
    have huniv : [g, a, b, c, d, e, fv].toFinset = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [hcard, Fintype.card_fin])
    have hx : x ∈ [g, a, b, c, d, e, fv].toFinset := by simp [huniv]
    simpa [List.mem_toFinset, List.mem_cons, List.mem_nil_iff, or_false] using hx
  rcases hcov with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨by simp [tag], rfl⟩
  · exact Or.inr <| Or.inl ⟨by simp only [tag, ite_eq_right hga.symm, ite_true], rfl⟩
  · exact Or.inr <| Or.inr <| Or.inl
      ⟨by simp only [tag, ite_eq_right hgb.symm, ite_eq_right hab.symm, ite_true], rfl⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨by simp only [tag, ite_eq_right hgc.symm, ite_eq_right hac.symm,
          ite_eq_right hbc.symm, ite_true], rfl⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨by simp only [tag, ite_eq_right hgd.symm, ite_eq_right had.symm,
          ite_eq_right hbd.symm, ite_eq_right hcd.symm, ite_true], rfl⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨by simp only [tag, ite_eq_right hge.symm, ite_eq_right hae.symm,
          ite_eq_right hbe.symm, ite_eq_right hce.symm, ite_eq_right hde.symm, ite_true], rfl⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      ⟨by simp only [tag, ite_eq_right hgf.symm, ite_eq_right haf.symm,
          ite_eq_right hbf.symm, ite_eq_right hcf.symm, ite_eq_right hdf.symm,
          ite_eq_right hef.symm, ite_true], rfl⟩

private theorem part_injective {g a b c d e fv : Fin 7} (hn : List.Nodup [g, a, b, c, d, e, fv]) :
    Function.Injective (part g a b c d e fv) := by
  intro x y hxy
  rcases tag_cases hn x with
    ⟨hx, rfl⟩ | ⟨hx, rfl⟩ | ⟨hx, rfl⟩ | ⟨hx, rfl⟩ | ⟨hx, rfl⟩ | ⟨hx, rfl⟩ | ⟨hx, rfl⟩
  <;> rcases tag_cases hn y with
    ⟨hy, rfl⟩ | ⟨hy, rfl⟩ | ⟨hy, rfl⟩ | ⟨hy, rfl⟩ | ⟨hy, rfl⟩ | ⟨hy, rfl⟩ | ⟨hy, rfl⟩
  <;> first
    | rfl
    | (simp only [part, hx, hy] at hxy; injection hxy; contradiction)

private theorem part_map_rel {g a b c d e fv : Fin 7} {G : SimpleGraph (Fin 7)}
    (hn : List.Nodup [g, a, b, c, d, e, fv]) (hnab : ¬G.Adj a b) (hncd : ¬G.Adj c d)
    (hnef : ¬G.Adj e fv) :
    ∀ ⦃x y : Fin 7⦄, G.Adj x y → (part g a b c d e fv x).1 ≠ (part g a b c d e fv y).1 := by
  intro x y hxy hsame
  rcases tag_cases hn x with
    ⟨hx, rfl⟩ | ⟨hx, rfl⟩ | ⟨hx, rfl⟩ | ⟨hx, rfl⟩ | ⟨hx, rfl⟩ | ⟨hx, rfl⟩ | ⟨hx, rfl⟩
  <;> rcases tag_cases hn y with
    ⟨hy, rfl⟩ | ⟨hy, rfl⟩ | ⟨hy, rfl⟩ | ⟨hy, rfl⟩ | ⟨hy, rfl⟩ | ⟨hy, rfl⟩ | ⟨hy, rfl⟩
  <;> first
    | exact hxy.ne rfl
    | exact hnab hxy
    | exact hnab hxy.symm
    | exact hncd hxy
    | exact hncd hxy.symm
    | exact hnef hxy
    | exact hnef hxy.symm
    | (simp only [part, hx, hy] at hsame; exact absurd hsame (by decide))

private theorem unitDistEmbeddable_four_fin_seven (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    (hδ : ∀ v, 4 ≤ G.degree v) (hE : G.edgeSet.ncard ≤ 14) : G.UnitDistEmbeddable 4 := by
  classical
  have hcardE : #G.edgeFinset ≤ 14 := by
    rw [← edgeSet_ncard_eq]
    exact hE
  have hsum : ∑ v, G.degree v = 2 * #G.edgeFinset := G.sum_degrees_eq_twice_card_edges
  have hlower : ∑ v : Fin 7, (4 : ℕ) ≤ ∑ v, G.degree v :=
    Finset.sum_le_sum fun v _ => hδ v
  have hfour : ∑ v : Fin 7, (4 : ℕ) = 28 := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hsum28 : ∑ v, G.degree v = 28 := by
    apply le_antisymm
    · rw [hsum]
      omega
    · simpa [hfour] using hlower
  have hreg : G.IsRegularOfDegree 4 := by
    intro v
    have herase : ∑ w ∈ Finset.univ.erase v, (4 : ℕ) = 24 := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
        Fintype.card_fin]
      norm_num
    have hrest : 24 ≤ ∑ w ∈ Finset.univ.erase v, G.degree w := by
      rw [← herase]
      exact Finset.sum_le_sum fun w _ => hδ w
    have hsplit :
        (∑ w ∈ Finset.univ.erase v, G.degree w) + G.degree v = 28 := by
      simpa [hsum28] using
        Finset.sum_erase_add Finset.univ (fun w => G.degree w) (Finset.mem_univ v)
    have hle : G.degree v ≤ 4 := by omega
    exact le_antisymm hle (hδ v)
  obtain ⟨a, b, c, d, e, f, hab, hcd, hef, hnodup⟩ :=
    exists_three_pairwise_disjoint_edges_compl G hreg
  have hnab : ¬G.Adj a b := ((compl_adj G a b).mp hab).2
  have hncd : ¬G.Adj c d := ((compl_adj G c d).mp hcd).2
  have hnef : ¬G.Adj e f := ((compl_adj G e f).mp hef).2
  let six : Finset (Fin 7) := [a, b, c, d, e, f].toFinset
  have hsix : #six = 6 := by simpa [six] using List.toFinset_card_of_nodup hnodup
  have hrest : #(Finset.univ \ six) = 1 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hsix]
  obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hrest
  have hg_out : g ∉ six := by
    have hgmem : g ∈ Finset.univ \ six := by
      rw [hg]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_sdiff.mp hgmem).2
  have hnodup7 : List.Nodup [g, a, b, c, d, e, f] := by
    rw [List.nodup_cons]
    refine ⟨?_, hnodup⟩
    intro hx
    exact hg_out (by simpa [six, List.mem_toFinset] using hx)
  exact UnitDistEmbeddable.comap
    (show G →g completeMultipartiteGraph (fun i : Fin 4 => Fin (![1, 2, 2, 2] i)) from
      ⟨part g a b c d e f, fun hxy => by
        rw [comap_adj, top_adj]
        exact part_map_rel hnodup7 hnab hncd hnef hxy⟩)
    (part_injective hnodup7) (hasUnitDistDim_completeMultipartiteGraph_one_two_two_two).1

private theorem edgeSet_ncard_overFin [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (hV : Fintype.card V = n) : (G.overFin hV).edgeSet.ncard = G.edgeSet.ncard := by
  classical
  rw [edgeSet_ncard_eq, edgeSet_ncard_eq (G := G), (G.overFinIso hV).card_edgeFinset_eq]

private theorem unitDistEmbeddable_four_of_minDegree_ge_four [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hδ : ∀ v, 4 ≤ G.degree v) (hE : G.edgeSet.ncard ≤ 14) :
    G.UnitDistEmbeddable 4 := by
  classical
  have hcardE : #G.edgeFinset ≤ 14 := by
    rw [← edgeSet_ncard_eq]
    exact hE
  have hsum : ∑ v, G.degree v = 2 * #G.edgeFinset := G.sum_degrees_eq_twice_card_edges
  have hlower : 4 * Fintype.card V ≤ ∑ v, G.degree v := by
    have hs : ∑ v : V, (4 : ℕ) ≤ ∑ v, G.degree v :=
      Finset.sum_le_sum fun v _ => hδ v
    have hconst : ∑ v : V, (4 : ℕ) = 4 * Fintype.card V := by
      rw [Finset.sum_const, Finset.card_univ]
      simp [mul_comm]
    simpa [hconst] using hs
  have hle7 : Fintype.card V ≤ 7 := by
    have : 4 * Fintype.card V ≤ 28 := by
      have htwice : ∑ v, G.degree v ≤ 28 := by
        rw [hsum]
        omega
      exact hlower.trans htwice
    omega
  by_cases h5 : Fintype.card V ≤ 5
  · exact unitDistEmbeddable_four_of_card_le_five G h5
  · by_cases h6 : Fintype.card V = 6
    · have hE' : (G.overFin h6).edgeSet.ncard ≤ 14 := by
        rw [edgeSet_ncard_overFin h6]
        exact hE
      exact (UnitDistEmbeddable.of_iso (G.overFinIso h6)).mpr
        (unitDistEmbeddable_four_fin_six (G.overFin h6) hE')
    · have h7 : Fintype.card V = 7 := by omega
      have hE' : (G.overFin h7).edgeSet.ncard ≤ 14 := by
        rw [edgeSet_ncard_overFin h7]
        exact hE
      have hδ' : ∀ v, 4 ≤ (G.overFin h7).degree v := by
        intro v
        have hdeg := (G.overFinIso h7).degree_eq ((G.overFinIso h7).symm v)
        rw [(G.overFinIso h7).apply_symm_apply] at hdeg
        rw [hdeg]
        exact hδ _
      exact (UnitDistEmbeddable.of_iso (G.overFinIso h7)).mpr
        (unitDistEmbeddable_four_fin_seven (G.overFin h7) hδ' hE')

private theorem unitDistEmbeddable_four_aux (n : ℕ) {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V ≤ n) (hE : G.edgeSet.ncard ≤ 14) : G.UnitDistEmbeddable 4 := by
  induction n generalizing V with
  | zero =>
    have : IsEmpty V := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hV)
    exact ⟨isEmptyElim, isEmptyElim, isEmptyElim⟩
  | succ n ih =>
    classical
    by_cases hlt : Fintype.card V ≤ n
    · exact ih G hlt hE
    · have hcard : Fintype.card V = n + 1 := by omega
      by_cases hlow : ∃ u, G.degree u ≤ 3
      · obtain ⟨u, hu⟩ := hlow
        have hEH :
            ((addNeighborClique G u).induce {v | v ≠ u}).edgeSet.ncard ≤ 14 :=
          (ncard_induce_addNeighborClique_le hu).trans hE
        have hcardH : Fintype.card {v : V // v ≠ u} ≤ n := by
          rw [Fintype.card_subtype_compl (p := (· = u)), Fintype.card_subtype_eq u, hcard]
          omega
        have hInd := ih ((addNeighborClique G u).induce {v | v ≠ u}) hcardH hEH
        have hk : ((addNeighborClique G u).neighborSet u).ncard + 1 ≤ 4 := by
          rw [neighborSet_addNeighborClique, ← Set.fintypeCard_eq_ncard, card_neighborSet_eq_degree]
          omega
        exact UnitDistEmbeddable.of_le (le_addNeighborClique G u)
          (UnitDistEmbeddable.extend (isClique_addNeighborClique G u) hk hInd)
      · have hδ : ∀ v, 4 ≤ G.degree v := by
          intro v
          have hv : ¬G.degree v ≤ 3 := by
            intro hvle
            exact hlow ⟨v, hvle⟩
          omega
        exact unitDistEmbeddable_four_of_minDegree_ge_four hδ hE

@[expose] public section

/-- Every finite graph with at most fourteen edges has a unit-distance representation in `ℝ⁴`.

This is the lower-bound half of Chaffee–Noble Theorem 10. Induction is on the number of vertices.
A vertex of degree at most three is deleted and the missing edges among its neighbours are added;
for degree `k ≤ 3` one has `C(k, 2) ≤ k`, so the smaller graph has no more edges and embeds by
induction. `UnitDistEmbeddable.extend` re-attaches the vertex, and `UnitDistEmbeddable.of_le`
deletes the added edges. If every degree is at least four, then `4|V| ≤ 2|E| ≤ 28`, so `|V| ≤ 7`.
At most five vertices, the graph maps injectively into `K₅`. On six vertices it misses an edge of
`K₆`. On seven vertices the degree sum forces a four-regular graph, so the complement has three
pairwise disjoint edges and the graph maps by an injective homomorphism into `K₁,₂,₂,₂`. -/
theorem unitDistEmbeddable_four_of_ncard_edgeSet_le {V : Type*} [Finite V] (G : SimpleGraph V)
    (h : G.edgeSet.ncard ≤ 14) : G.UnitDistEmbeddable 4 := by
  classical
  have := Fintype.ofFinite V
  exact unitDistEmbeddable_four_aux (Fintype.card V) G le_rfl h

end

end

end SimpleGraph

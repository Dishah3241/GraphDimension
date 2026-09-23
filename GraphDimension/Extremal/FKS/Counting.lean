/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.FKS.Defs
public import Mathlib.Combinatorics.SimpleGraph.Finite

import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Sym.Card
import Mathlib.Tactic.Ring

/-!
# Edge counts in the branches of FKS's Theorem 3

The case split on a core of minimum degree `d − 1` compares six lower bounds on `e(H)` with the
budget. Each bound is pure counting: a copy or a clique contributes its edges, and edges incident
to vertices outside that set are disjoint from them. `m(d)` is `(d + 2).choose 2`.

## References

Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, J. Combin. Theory Ser. A
**171** (2020), 105146, arXiv 1802.03092, proof of Theorem 3 (`main.tex` lines 352–406).
-/

namespace SimpleGraph

open Finset

@[expose] public section

variable {V : Type*} [Fintype V] [DecidableEq V]

private instance decidableRel_completeMinusTriangle (n : ℕ) :
    DecidableRel (completeMinusTriangle n).Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ ¬ (i.val < 3 ∧ j.val < 3)))

variable {H : SimpleGraph V} [DecidableRel H.Adj]

omit [DecidableEq V] in
private lemma edgeFinset_card_eq_edgeSet_ncard :
    #H.edgeFinset = H.edgeSet.ncard := by
  rw [edgeFinset_card, Set.fintypeCard_eq_ncard]

private lemma choose_two_mul_two (n : ℕ) : n.choose 2 * 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)

/-- If `a + k = b + c`, with `b ≤ a` and `k ≤ c`, then `a − b = c − k`. -/
private lemma sub_eq_of_add_eq {a b c k : ℕ} (hb : b ≤ a) (_hk : k ≤ c)
    (h : a + k = b + c) : a - b = c - k := by
  have h1 : a - b + k = c := by
    calc
      a - b + k = a + k - b := (Nat.sub_add_comm hb).symm
      _ = b + c - b := by rw [h]
      _ = c := Nat.add_sub_cancel_left _ _
  rw [← h1, Nat.add_sub_cancel]

private lemma two_mul_sub_poly {d : ℕ} (hd : 2 ≤ d) :
    2 * (d * (d - 1)) + 8 = (d - 2) * (d - 3) + (d + 2) * (d + 1) := by
  rcases eq_or_lt_of_le hd with rfl | hd'
  · decide
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hd')
    rw [show (3 + n) - 1 = 2 + n by omega, show (3 + n) - 2 = 1 + n by omega,
      show (3 + n) - 3 = n by omega]
    ring

private lemma two_mul_sub_poly_one {d : ℕ} (hd : 1 ≤ d) :
    2 * (d * (d - 1)) + 2 = (d - 1) * (d - 2) + (d + 1) * d := by
  rcases eq_or_lt_of_le hd with rfl | hd'
  · decide
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hd')
    rw [show (2 + n) - 1 = 1 + n by omega, show (2 + n) - 2 = n by omega]
    ring

private lemma two_choose_add_four {d : ℕ} (hd : 2 ≤ d) :
    2 * d.choose 2 + 4 = (d - 2).choose 2 + (d + 2).choose 2 := by
  have h2 := choose_two_mul_two
  have hdouble :
      2 * (2 * d.choose 2 + 4) = 2 * ((d - 2).choose 2 + (d + 2).choose 2) := by
    calc
      2 * (2 * d.choose 2 + 4) = 2 * (2 * d.choose 2) + 8 := by ring
      _ = 2 * (d.choose 2 * 2) + 8 := by ring
      _ = 2 * (d * (d - 1)) + 8 := by rw [h2 d]
      _ = (d - 2) * (d - 3) + (d + 2) * (d + 1) := two_mul_sub_poly hd
      _ = (d - 2) * ((d - 2) - 1) + (d + 2) * ((d + 2) - 1) := by
        rw [show d - 3 = (d - 2) - 1 by omega]
        conv_lhs =>
          arg 2
          arg 2
          rw [show d + 1 = (d + 2) - 1 by omega]
      _ = (d - 2).choose 2 * 2 + (d + 2).choose 2 * 2 := by
        rw [← h2 (d - 2), ← h2 (d + 2)]
      _ = 2 * ((d - 2).choose 2 + (d + 2).choose 2) := by ring
  omega

private lemma two_choose_sub_choose_sub_two (d : ℕ) (hd : 2 ≤ d) :
    2 * d.choose 2 - (d - 2).choose 2 = (d + 2).choose 2 - 4 := by
  have hB : (d - 2).choose 2 ≤ 2 * d.choose 2 := by
    have hle : (d - 2).choose 2 ≤ d.choose 2 := Nat.choose_le_choose 2 (Nat.sub_le d 2)
    omega
  have hC : 4 ≤ (d + 2).choose 2 := by
    calc
      4 ≤ (4 : ℕ).choose 2 := by decide
      _ ≤ (d + 2).choose 2 := Nat.choose_le_choose 2 (by omega)
  exact sub_eq_of_add_eq hB hC (two_choose_add_four hd)

private lemma two_choose_sub_choose_ge {d i : ℕ} (hd : 2 ≤ d) (hi : i ≤ d - 2) :
    (d + 2).choose 2 - 4 ≤ 2 * d.choose 2 - i.choose 2 := by
  calc
    (d + 2).choose 2 - 4 = 2 * d.choose 2 - (d - 2).choose 2 :=
      (two_choose_sub_choose_sub_two d hd).symm
    _ ≤ 2 * d.choose 2 - i.choose 2 :=
      Nat.sub_le_sub_left (Nat.choose_le_choose 2 hi) _

private lemma two_choose_add_one {d : ℕ} (hd : 1 ≤ d) :
    2 * d.choose 2 + 1 = (d - 1).choose 2 + (d + 1).choose 2 := by
  have h2 := choose_two_mul_two
  have hdouble :
      2 * (2 * d.choose 2 + 1) = 2 * ((d - 1).choose 2 + (d + 1).choose 2) := by
    calc
      2 * (2 * d.choose 2 + 1) = 2 * (2 * d.choose 2) + 2 := by ring
      _ = 2 * (d.choose 2 * 2) + 2 := by ring
      _ = 2 * (d * (d - 1)) + 2 := by rw [h2 d]
      _ = (d - 1) * (d - 2) + (d + 1) * d := two_mul_sub_poly_one hd
      _ = (d - 1) * ((d - 1) - 1) + (d + 1) * ((d + 1) - 1) := by
        rw [show d - 2 = (d - 1) - 1 by omega]
        conv_lhs =>
          arg 2
          arg 2
          rw [show d = (d + 1) - 1 by omega]
      _ = (d - 1).choose 2 * 2 + (d + 1).choose 2 * 2 := by
        rw [← h2 (d - 1), ← h2 (d + 1)]
      _ = 2 * ((d - 1).choose 2 + (d + 1).choose 2) := by ring
  omega

private lemma two_choose_sub_choose_pred (d : ℕ) (hd : 1 ≤ d) :
    2 * d.choose 2 - (d - 1).choose 2 = (d + 1).choose 2 - 1 := by
  have hB : (d - 1).choose 2 ≤ 2 * d.choose 2 := by
    have hle : (d - 1).choose 2 ≤ d.choose 2 := Nat.choose_le_choose 2 (Nat.sub_le d 1)
    omega
  have hC : 1 ≤ (d + 1).choose 2 := by
    calc
      1 ≤ (2 : ℕ).choose 2 := by decide
      _ ≤ (d + 1).choose 2 := Nat.choose_le_choose 2 (by omega)
  exact sub_eq_of_add_eq hB hC (two_choose_add_one hd)

private lemma edgeFinset_card_completeMinusTriangle {n : ℕ} (hn : 3 ≤ n) :
    #(completeMinusTriangle n).edgeFinset = n.choose 2 - 3 := by
  rw [edgeFinset_card_eq_edgeSet_ncard, card_edgeFinset_completeMinusTriangle hn]

/-- The unordered edges with both ends in `K`. -/
private def cliqueEdges (K : Finset V) : Finset (Sym2 V) :=
  K.offDiag.image Sym2.mk.uncurry

omit [Fintype V] in
private lemma card_cliqueEdges (K : Finset V) : #(cliqueEdges K) = (#K).choose 2 :=
  Sym2.card_image_offDiag K

omit [Fintype V] in
private lemma mem_cliqueEdges {K : Finset V} {e : Sym2 V} :
    e ∈ cliqueEdges K ↔ ∃ a b, a ∈ K ∧ b ∈ K ∧ a ≠ b ∧ e = s(a, b) := by
  constructor
  · intro he
    obtain ⟨p, hp, rfl⟩ := mem_image.mp he
    rw [mem_offDiag] at hp
    refine ⟨p.1, p.2, hp.1, hp.2.1, hp.2.2, rfl⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine mem_image.mpr ⟨(a, b), ?_, rfl⟩
    exact mem_offDiag.mpr ⟨ha, hb, hab⟩

private lemma cliqueEdges_subset_edgeFinset {K : Finset V} (hK : H.IsClique (K : Set V)) :
    cliqueEdges K ⊆ H.edgeFinset := by
  intro e he
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := mem_cliqueEdges.mp he
  rw [mem_edgeFinset, mem_edgeSet]
  exact hK (by simpa using ha) (by simpa using hb) hab

omit [Fintype V] in
private lemma cliqueEdges_inter (K K' : Finset V) :
    cliqueEdges K ∩ cliqueEdges K' = cliqueEdges (K ∩ K') := by
  ext e
  constructor
  · intro he
    obtain ⟨heK, heK'⟩ := mem_inter.mp he
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := mem_cliqueEdges.mp heK
    obtain ⟨a', b', ha', hb', hab', heq⟩ := mem_cliqueEdges.mp heK'
    have hends : a ∈ K' ∧ b ∈ K' := by
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨ha', hb'⟩
      · exact ⟨hb', ha'⟩
    exact mem_cliqueEdges.mpr ⟨a, b, mem_inter.mpr ⟨ha, hends.1⟩, mem_inter.mpr ⟨hb, hends.2⟩,
      hab, rfl⟩
  · intro he
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := mem_cliqueEdges.mp he
    rw [mem_inter]
    exact ⟨mem_cliqueEdges.mpr ⟨a, b, (mem_inter.mp ha).1, (mem_inter.mp hb).1, hab, rfl⟩,
      mem_cliqueEdges.mpr ⟨a, b, (mem_inter.mp ha).2, (mem_inter.mp hb).2, hab, rfl⟩⟩

omit [Fintype V] in
private lemma card_cliqueEdges_union (K K' : Finset V) :
    #(cliqueEdges K ∪ cliqueEdges K') =
      (#K).choose 2 + (#K').choose 2 - (#(K ∩ K')).choose 2 := by
  have hcard := card_union_add_card_inter (cliqueEdges K) (cliqueEdges K')
  rw [cliqueEdges_inter, card_cliqueEdges, card_cliqueEdges, card_cliqueEdges] at hcard
  omega

private lemma disjoint_cliqueEdges_incidence {K : Finset V} {u : V} (hu : u ∉ K) :
    Disjoint (cliqueEdges K) (H.incidenceFinset u) := by
  rw [Finset.disjoint_left]
  intro e he huinc
  obtain ⟨a, b, ha, hb, -, rfl⟩ := mem_cliqueEdges.mp he
  rw [mem_incidenceFinset, mk'_mem_incidenceSet_iff] at huinc
  rcases huinc.2 with rfl | rfl
  · exact hu ha
  · exact hu hb

omit [DecidableEq V] in
private lemma eq_pair_of_mem_incidence_inter {u u' : V} (hne : u ≠ u') {e : Sym2 V}
    (he : e ∈ H.incidenceFinset u) (he' : e ∈ H.incidenceFinset u') : e = s(u, u') := by
  rw [mem_incidenceFinset] at he he'
  induction e using Sym2.inductionOn with
  | hf a b =>
    rw [mk'_mem_incidenceSet_iff] at he he'
    rcases he.2 with rfl | rfl <;> rcases he'.2 with rfl | rfl
    · exact (hne rfl).elim
    · rfl
    · exact Sym2.eq_swap
    · exact (hne rfl).elim

private lemma card_inter_incidence_le_one {u u' : V} (hne : u ≠ u') :
    #(H.incidenceFinset u ∩ H.incidenceFinset u') ≤ 1 := by
  have hsub : H.incidenceFinset u ∩ H.incidenceFinset u' ⊆ {s(u, u')} := by
    intro e he
    obtain ⟨hu, hu'⟩ := mem_inter.mp he
    simpa using eq_pair_of_mem_incidence_inter hne hu hu'
  simpa using card_le_card hsub

private lemma card_incidence_union_ge {u u' : V} (hne : u ≠ u') :
    H.degree u + H.degree u' - 1 ≤ #(H.incidenceFinset u ∪ H.incidenceFinset u') := by
  have hinter := card_inter_incidence_le_one (H := H) hne
  have hcard := card_union_add_card_inter (H.incidenceFinset u) (H.incidenceFinset u')
  rw [card_incidenceFinset_eq_degree, card_incidenceFinset_eq_degree] at hcard
  omega

omit [DecidableEq V] in
private lemma disjoint_incidence_of_not_adj {u u' : V} (hne : u ≠ u') (hnadj : ¬ H.Adj u u') :
    Disjoint (H.incidenceFinset u) (H.incidenceFinset u') := by
  rw [Finset.disjoint_left]
  intro e he he'
  rw [eq_pair_of_mem_incidence_inter hne he he', mem_incidenceFinset, mem_incidenceSet] at he
  exact hnadj he

omit [DecidableEq V] in
private lemma edgeSet_ncard_ge_of_disjoint {A B : Finset (Sym2 V)}
    (hA : A ⊆ H.edgeFinset) (hB : B ⊆ H.edgeFinset) (hd : Disjoint A B) :
    #A + #B ≤ H.edgeSet.ncard := by
  classical
  calc
    #A + #B = #(A ∪ B) := (card_union_of_disjoint hd).symm
    _ ≤ #H.edgeFinset := card_le_card (union_subset hA hB)
    _ = H.edgeSet.ncard := edgeFinset_card_eq_edgeSet_ncard

private def copyEdges {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph W}
    [DecidableRel G.Adj] (f : G.Copy H) : Finset (Sym2 V) :=
  G.edgeFinset.image (Sym2.map (⇑f))

omit [Fintype V] [DecidableRel H.Adj] in
private lemma card_copyEdges {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph W}
    [DecidableRel G.Adj] (f : G.Copy H) : #(copyEdges (H := H) f) = #G.edgeFinset := by
  have hinj : Function.Injective (⇑f) := by
    intro a b h
    exact f.injective (by simpa using h)
  simpa [copyEdges] using card_image_of_injective _ (Sym2.map.injective hinj)

private lemma copyEdges_subset {W : Type*} [Fintype W] [DecidableEq W] {G : SimpleGraph W}
    [DecidableRel G.Adj] (f : G.Copy H) : copyEdges (H := H) f ⊆ H.edgeFinset := by
  intro e he
  obtain ⟨e', he', rfl⟩ := mem_image.mp he
  rw [mem_edgeFinset] at he' ⊢
  exact f.toHom.map_mem_edgeSet he'

private lemma disjoint_copyEdges_incidence {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph W} [DecidableRel G.Adj] (f : G.Copy H) {u : V}
    (hu : u ∉ Set.range (⇑f)) : Disjoint (copyEdges (H := H) f) (H.incidenceFinset u) := by
  rw [Finset.disjoint_left]
  intro e he huinc
  obtain ⟨e', -, rfl⟩ := mem_image.mp he
  induction e' using Sym2.inductionOn with
  | hf a b =>
    rw [Sym2.map_mk, mem_incidenceFinset, mk'_mem_incidenceSet_iff] at huinc
    rcases huinc.2 with rfl | rfl
    · exact hu ⟨a, rfl⟩
    · exact hu ⟨b, rfl⟩

omit [DecidableEq V] in
/-- Branch A. One vertex outside a copy of `K_{d+2} − K₃` contributes at least `d − 1` new edges,
so `H` has at least `(d + 2).choose 2 − 3 + (d − 1)` edges. -/
theorem card_edgeSet_ge_of_copy_add_vertex {d : ℕ} (hd : 3 ≤ d)
    (f : (completeMinusTriangle (d + 2)).Copy H) {u : V} (hu : u ∉ Set.range (⇑f))
    (hdeg : d - 1 ≤ H.degree u) :
    (d + 2).choose 2 - 3 + (d - 1) ≤ H.edgeSet.ncard := by
  classical
  have hcopy : #(copyEdges (H := H) f) = (d + 2).choose 2 - 3 := by
    rw [card_copyEdges, edgeFinset_card_completeMinusTriangle (by omega)]
  have hdisj : Disjoint (copyEdges (H := H) f) (H.incidenceFinset u) :=
    disjoint_copyEdges_incidence f hu
  calc
    (d + 2).choose 2 - 3 + (d - 1) = #(copyEdges (H := H) f) + (d - 1) := by rw [hcopy]
    _ ≤ #(copyEdges (H := H) f) + H.degree u := Nat.add_le_add_left hdeg _
    _ = #(copyEdges (H := H) f) + #(H.incidenceFinset u) := by
      rw [card_incidenceFinset_eq_degree]
    _ ≤ H.edgeSet.ncard :=
      edgeSet_ncard_ge_of_disjoint (copyEdges_subset f) (H.incidenceFinset_subset u) hdisj

omit [DecidableEq V] in
/-- Branch B. Two vertices outside a `(d + 1)`-clique contribute at least `2d − 3` further edges:
their incident edges meet in at most the single edge joining them. -/
theorem card_edgeSet_ge_of_two_outside_clique {d : ℕ} (hd : 2 ≤ d) {K : Finset V}
    (hK : H.IsNClique (d + 1) K) {u u' : V} (hu : u ∉ K) (hu' : u' ∉ K) (hne : u ≠ u')
    (hdeg : d - 1 ≤ H.degree u) (hdeg' : d - 1 ≤ H.degree u') :
    (d + 1).choose 2 + 2 * d - 3 ≤ H.edgeSet.ncard := by
  classical
  have hE : #(cliqueEdges K) = (d + 1).choose 2 := by rw [card_cliqueEdges, hK.card_eq]
  have hI : (d - 1) + (d - 1) - 1 ≤ #(H.incidenceFinset u ∪ H.incidenceFinset u') := by
    calc
      (d - 1) + (d - 1) - 1 ≤ H.degree u + H.degree u' - 1 :=
        Nat.sub_le_sub_right (Nat.add_le_add hdeg hdeg') 1
      _ ≤ #(H.incidenceFinset u ∪ H.incidenceFinset u') := card_incidence_union_ge hne
  have hrest : (d - 1) + (d - 1) - 1 = 2 * d - 3 := by omega
  have hdisj : Disjoint (cliqueEdges K) (H.incidenceFinset u ∪ H.incidenceFinset u') :=
    disjoint_union_right.mpr ⟨disjoint_cliqueEdges_incidence hu, disjoint_cliqueEdges_incidence hu'⟩
  calc
    (d + 1).choose 2 + 2 * d - 3 = (d + 1).choose 2 + (2 * d - 3) :=
      Nat.add_sub_assoc (by omega) _
    _ = #(cliqueEdges K) + ((d - 1) + (d - 1) - 1) := by rw [hE, hrest]
    _ ≤ #(cliqueEdges K) + #(H.incidenceFinset u ∪ H.incidenceFinset u') :=
      Nat.add_le_add_left hI _
    _ ≤ H.edgeSet.ncard :=
      edgeSet_ncard_ge_of_disjoint (cliqueEdges_subset_edgeFinset hK.isClique)
        (union_subset (H.incidenceFinset_subset u) (H.incidenceFinset_subset u')) hdisj

omit [Fintype V] [DecidableEq V] in
/-- Branch B. A vertex outside a `(d + 1)`-clique, adjacent to at least `d − 1` of its vertices,
misses at most two clique vertices. Sending `0, 1, 2` to that vertex and to two clique vertices
that cover the misses embeds `K_{d+2} − K₃`. -/
theorem completeMinusTriangle_isContained_of_one_outside_clique {d : ℕ} (hd : 1 ≤ d)
    {K : Finset V} (hK : H.IsNClique (d + 1) K) {u : V} (hu : u ∉ K)
    (hdeg : d - 1 ≤ #(K.filter (H.Adj u))) :
    completeMinusTriangle (d + 2) ⊑ H := by
  classical
  let missed := K.filter fun v => ¬ H.Adj u v
  have hmiss_le : #missed ≤ 2 := by
    have hpart : #(K.filter (H.Adj u)) + #missed = d + 1 := by
      simpa [missed, hK.card_eq] using
        card_filter_add_card_filter_not (s := K) (fun v => H.Adj u v)
    omega
  obtain ⟨S, hmissS, hSK, hScard⟩ :=
    exists_subsuperset_card_eq (filter_subset _ K) hmiss_le (by rw [hK.card_eq]; omega)
  obtain ⟨x, y, hxy, hSxy⟩ := card_eq_two.mp hScard
  have hxK : x ∈ K := hSK (by simp [hSxy])
  have hyK : y ∈ K := hSK (by simp [hSxy])
  have hpair_sub : ({x, y} : Finset V) ⊆ K := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxK
    · exact hyK
  let R := K \ ({x, y} : Finset V)
  have hRcard : #R = d - 1 := by
    rw [card_sdiff_of_subset hpair_sub, (card_pair_eq_two_iff).mpr hxy, hK.card_eq]
    omega
  let e : Fin (d - 1) ≃ {v // v ∈ R} := (equivFinOfCardEq hRcard).symm
  have hlt (i : Fin (d + 2)) (h0 : i.val ≠ 0) (h1 : i.val ≠ 1) (h2 : i.val ≠ 2) :
      i.val - 3 < d - 1 := by omega
  let f : Fin (d + 2) → V := fun i =>
    if h0 : i.val = 0 then u
    else if h1 : i.val = 1 then x
    else if h2 : i.val = 2 then y
    else (e ⟨i.val - 3, hlt i h0 h1 h2⟩).1
  have hf_low (i : Fin (d + 2)) :
      (i.val = 0 → f i = u) ∧ (i.val = 1 → f i = x) ∧ (i.val = 2 → f i = y) := by
    unfold f
    split_ifs with h0 h1 h2
    · exact ⟨fun _ => rfl, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    · exact ⟨fun h => absurd h h0, fun _ => rfl, fun h => absurd h (by omega)⟩
    · exact ⟨fun h => absurd h h0, fun h => absurd h h1, fun _ => rfl⟩
    · exact ⟨fun h => absurd h h0, fun h => absurd h h1, fun h => absurd h h2⟩
  have hf0 (i : Fin (d + 2)) (hi : i.val = 0) : f i = u := (hf_low i).1 hi
  have hf1 (i : Fin (d + 2)) (hi : i.val = 1) : f i = x := (hf_low i).2.1 hi
  have hf2 (i : Fin (d + 2)) (hi : i.val = 2) : f i = y := (hf_low i).2.2 hi
  have hf_high (i : Fin (d + 2)) (hi : 3 ≤ i.val) :
      f i = (e ⟨i.val - 3, hlt i (by omega) (by omega) (by omega)⟩).1 := by
    simp only [f]
    split_ifs with h0 h1 h2
    · omega
    · omega
    · omega
    · refine congrArg (fun z : Fin (d - 1) => (e z).1) (Fin.ext ?_)
      rfl
  have hhigh_mem (i : Fin (d + 2)) (hi : 3 ≤ i.val) : f i ∈ R := by
    rw [hf_high i hi]
    exact Subtype.mem _
  have hR_spec {z : V} (hz : z ∈ R) : z ∈ K ∧ z ≠ x ∧ z ≠ y ∧ z ≠ u := by
    refine ⟨(mem_sdiff.mp hz).1, ?_, ?_, ?_⟩
    · intro hzx
      exact (mem_sdiff.mp hz).2 (by simp [hzx])
    · intro hzy
      exact (mem_sdiff.mp hz).2 (by simp [hzy])
    · intro hzu
      exact hu (hzu ▸ (mem_sdiff.mp hz).1)
  have hmiss_pair : missed ⊆ {x, y} := by rwa [← hSxy]
  have hadj_rest {z : V} (hz : z ∈ R) : H.Adj u z := by
    by_contra hna
    have hzm : z ∈ missed := mem_filter.mpr ⟨(mem_sdiff.mp hz).1, hna⟩
    have hzxy : z ∈ ({x, y} : Finset V) := hmiss_pair hzm
    exact (mem_sdiff.mp hz).2 hzxy
  have hinj : Function.Injective f := by
    intro i j hij
    by_cases hi : 3 ≤ i.val <;> by_cases hj : 3 ≤ j.val
    · rw [hf_high i hi, hf_high j hj] at hij
      have hsub :
          e ⟨i.val - 3, hlt i (by omega) (by omega) (by omega)⟩ =
            e ⟨j.val - 3, hlt j (by omega) (by omega) (by omega)⟩ :=
        Subtype.ext hij
      have hval : i.val - 3 = j.val - 3 := congrArg Fin.val (e.injective hsub)
      exact Fin.ext (by have := hval; omega)
    · have hspec := hR_spec (hhigh_mem i hi)
      have hju : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
      rcases hju with hj0 | hj1 | hj2
      · rw [hf0 j hj0] at hij
        exact (hspec.2.2.2 hij).elim
      · rw [hf1 j hj1] at hij
        exact (hspec.2.1 hij).elim
      · rw [hf2 j hj2] at hij
        exact (hspec.2.2.1 hij).elim
    · have hspec := hR_spec (hhigh_mem j hj)
      have hiu : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
      rcases hiu with hi0 | hi1 | hi2
      · rw [hf0 i hi0] at hij
        exact (hspec.2.2.2 hij.symm).elim
      · rw [hf1 i hi1] at hij
        exact (hspec.2.1 hij.symm).elim
      · rw [hf2 i hi2] at hij
        exact (hspec.2.2.1 hij.symm).elim
    · have hiu : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
      have hju : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
      rcases hiu with hi0 | hi1 | hi2 <;> rcases hju with hj0 | hj1 | hj2
      · exact Fin.ext (hi0.trans hj0.symm)
      · rw [hf0 i hi0, hf1 j hj1] at hij
        exact (hu (hij ▸ hxK)).elim
      · rw [hf0 i hi0, hf2 j hj2] at hij
        exact (hu (hij ▸ hyK)).elim
      · rw [hf1 i hi1, hf0 j hj0] at hij
        exact (hu (hij.symm ▸ hxK)).elim
      · exact Fin.ext (hi1.trans hj1.symm)
      · rw [hf1 i hi1, hf2 j hj2] at hij
        exact (hxy hij).elim
      · rw [hf2 i hi2, hf0 j hj0] at hij
        exact (hu (hij.symm ▸ hyK)).elim
      · rw [hf2 i hi2, hf1 j hj1] at hij
        exact (hxy hij.symm).elim
      · exact Fin.ext (hi2.trans hj2.symm)
  have hmap {i j : Fin (d + 2)} (hadj : (completeMinusTriangle (d + 2)).Adj i j) :
      H.Adj (f i) (f j) := by
    obtain ⟨hne, hnot⟩ := hadj
    by_cases hi : 3 ≤ i.val <;> by_cases hj : 3 ≤ j.val
    · exact hK.isClique (by simpa using (hR_spec (hhigh_mem i hi)).1)
        (by simpa using (hR_spec (hhigh_mem j hj)).1) (hinj.ne hne)
    · have hju : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
      rcases hju with hj0 | hj1 | hj2
      · rw [hf0 j hj0]
        exact (hadj_rest (hhigh_mem i hi)).symm
      · rw [hf1 j hj1]
        exact hK.isClique (by simpa using (hR_spec (hhigh_mem i hi)).1) (by simpa using hxK)
          (hR_spec (hhigh_mem i hi)).2.1
      · rw [hf2 j hj2]
        exact hK.isClique (by simpa using (hR_spec (hhigh_mem i hi)).1) (by simpa using hyK)
          (hR_spec (hhigh_mem i hi)).2.2.1
    · have hiu : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
      rcases hiu with hi0 | hi1 | hi2
      · rw [hf0 i hi0]
        exact hadj_rest (hhigh_mem j hj)
      · rw [hf1 i hi1]
        exact hK.isClique (by simpa using hxK) (by simpa using (hR_spec (hhigh_mem j hj)).1)
          ((hR_spec (hhigh_mem j hj)).2.1).symm
      · rw [hf2 i hi2]
        exact hK.isClique (by simpa using hyK) (by simpa using (hR_spec (hhigh_mem j hj)).1)
          ((hR_spec (hhigh_mem j hj)).2.2.1).symm
    · exact (hnot ⟨by omega, by omega⟩).elim
  exact ⟨⟨⟨f, fun hadj => hmap hadj⟩, hinj⟩⟩

/-- Case 1, small overlap. Two `d`-cliques meeting in `i ≤ d − 2` vertices span at least
`m(d) − 4` edges, and a vertex outside both contributes `d` more. -/
theorem card_edgeSet_ge_of_cliques_small_inter {d : ℕ} (hd : 2 ≤ d) {K K' : Finset V}
    (hK : H.IsNClique d K) (hK' : H.IsNClique d K') (hinter : #(K ∩ K') ≤ d - 2) {v : V}
    (hv : v ∉ K ∪ K') (hdeg : d ≤ H.degree v) :
    (d + 2).choose 2 - 4 + d ≤ H.edgeSet.ncard := by
  let E := cliqueEdges K ∪ cliqueEdges K'
  have hE : #E = 2 * d.choose 2 - (#(K ∩ K')).choose 2 := by
    rw [card_cliqueEdges_union, hK.card_eq, hK'.card_eq, ← two_mul]
  have hge : (d + 2).choose 2 - 4 ≤ #E := by
    rw [hE]
    exact two_choose_sub_choose_ge hd hinter
  have hdisj : Disjoint E (H.incidenceFinset v) := by
    rw [disjoint_union_left]
    exact ⟨disjoint_cliqueEdges_incidence (fun h => hv (mem_union.mpr (Or.inl h))),
      disjoint_cliqueEdges_incidence (fun h => hv (mem_union.mpr (Or.inr h)))⟩
  have hEsub : E ⊆ H.edgeFinset :=
    union_subset (cliqueEdges_subset_edgeFinset hK.isClique)
      (cliqueEdges_subset_edgeFinset hK'.isClique)
  calc
    (d + 2).choose 2 - 4 + d ≤ #E + d := Nat.add_le_add_right hge _
    _ ≤ #E + H.degree v := Nat.add_le_add_left hdeg _
    _ = #E + #(H.incidenceFinset v) := by rw [card_incidenceFinset_eq_degree]
    _ ≤ H.edgeSet.ncard :=
      edgeSet_ncard_ge_of_disjoint hEsub (H.incidenceFinset_subset v) hdisj

/-- Case 1, overlap `d − 1`. The two cliques span at least `(d + 1).choose 2 − 1` edges, and two
vertices outside both contribute at least `d + (d − 1) − 1` more. -/
theorem card_edgeSet_ge_of_cliques_inter_pred {d : ℕ} (hd : 2 ≤ d) {K K' : Finset V}
    (hK : H.IsNClique d K) (hK' : H.IsNClique d K') (hinter : #(K ∩ K') = d - 1) {v y : V}
    (hv : v ∉ K ∪ K') (hy : y ∉ K ∪ K') (hvy : v ≠ y) (hdegv : d ≤ H.degree v)
    (hdegy : d - 1 ≤ H.degree y) :
    (d + 1).choose 2 - 1 + d + (d - 1) - 1 ≤ H.edgeSet.ncard := by
  let E := cliqueEdges K ∪ cliqueEdges K'
  have hE : #E = (d + 1).choose 2 - 1 := by
    rw [card_cliqueEdges_union, hK.card_eq, hK'.card_eq, hinter, ← two_mul,
      two_choose_sub_choose_pred d (by omega)]
  have hI : d + (d - 1) - 1 ≤ #(H.incidenceFinset v ∪ H.incidenceFinset y) := by
    calc
      d + (d - 1) - 1 ≤ H.degree v + H.degree y - 1 :=
        Nat.sub_le_sub_right (Nat.add_le_add hdegv hdegy) 1
      _ ≤ #(H.incidenceFinset v ∪ H.incidenceFinset y) := card_incidence_union_ge hvy
  have hdisj : Disjoint E (H.incidenceFinset v ∪ H.incidenceFinset y) := by
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    exact ⟨⟨disjoint_cliqueEdges_incidence (fun h => hv (mem_union.mpr (Or.inl h))),
        disjoint_cliqueEdges_incidence (fun h => hy (mem_union.mpr (Or.inl h)))⟩,
      ⟨disjoint_cliqueEdges_incidence (fun h => hv (mem_union.mpr (Or.inr h))),
        disjoint_cliqueEdges_incidence (fun h => hy (mem_union.mpr (Or.inr h)))⟩⟩
  have hEsub : E ⊆ H.edgeFinset :=
    union_subset (cliqueEdges_subset_edgeFinset hK.isClique)
      (cliqueEdges_subset_edgeFinset hK'.isClique)
  have hIsub : H.incidenceFinset v ∪ H.incidenceFinset y ⊆ H.edgeFinset :=
    union_subset (H.incidenceFinset_subset v) (H.incidenceFinset_subset y)
  calc
    (d + 1).choose 2 - 1 + d + (d - 1) - 1
      = #E + d + (d - 1) - 1 := by rw [hE]
    _ = #E + (d + (d - 1)) - 1 := by rw [Nat.add_assoc]
    _ = #E + (d + (d - 1) - 1) := Nat.add_sub_assoc (by omega) _
    _ ≤ #E + #(H.incidenceFinset v ∪ H.incidenceFinset y) := Nat.add_le_add_left hI _
    _ ≤ H.edgeSet.ncard := edgeSet_ncard_ge_of_disjoint hEsub hIsub hdisj

omit [DecidableEq V] in
/-- Case 2. A copy of `K_{d+1} − K₃` avoiding two non-adjacent vertices `v` and `w` is disjoint from
both stars, and those stars are disjoint from each other. -/
theorem card_edgeSet_ge_of_copy_two_external {d : ℕ} (hd : 3 ≤ d) {v w : V} (hvw : v ≠ w)
    (hnadj : ¬ H.Adj v w) (hdegv : d ≤ H.degree v) (hdegw : d - 1 ≤ H.degree w)
    (f : (completeMinusTriangle (d + 1)).Copy H) (havoid : ∀ i, f i ≠ v ∧ f i ≠ w) :
    (d + 1).choose 2 - 3 + d + (d - 1) ≤ H.edgeSet.ncard := by
  classical
  have hcopy : #(copyEdges (H := H) f) = (d + 1).choose 2 - 3 := by
    rw [card_copyEdges, edgeFinset_card_completeMinusTriangle (by omega)]
  have hv_out : v ∉ Set.range (⇑f) := by
    intro ⟨i, hi⟩
    exact (havoid i).1 hi
  have hw_out : w ∉ Set.range (⇑f) := by
    intro ⟨i, hi⟩
    exact (havoid i).2 hi
  let I := H.incidenceFinset v ∪ H.incidenceFinset w
  have hI : #I = H.degree v + H.degree w := by
    rw [card_union_of_disjoint (disjoint_incidence_of_not_adj hvw hnadj),
      card_incidenceFinset_eq_degree, card_incidenceFinset_eq_degree]
  have hdisj : Disjoint (copyEdges (H := H) f) I :=
    disjoint_union_right.mpr
      ⟨disjoint_copyEdges_incidence f hv_out, disjoint_copyEdges_incidence f hw_out⟩
  have hIsub : I ⊆ H.edgeFinset :=
    union_subset (H.incidenceFinset_subset v) (H.incidenceFinset_subset w)
  calc
    (d + 1).choose 2 - 3 + d + (d - 1) = #(copyEdges (H := H) f) + d + (d - 1) := by rw [hcopy]
    _ = #(copyEdges (H := H) f) + (d + (d - 1)) := Nat.add_assoc _ _ _
    _ ≤ #(copyEdges (H := H) f) + (H.degree v + H.degree w) :=
      Nat.add_le_add_left (Nat.add_le_add hdegv hdegw) _
    _ = #(copyEdges (H := H) f) + #I := by rw [hI]
    _ ≤ H.edgeSet.ncard :=
      edgeSet_ncard_ge_of_disjoint (copyEdges_subset f) hIsub hdisj

end

end SimpleGraph

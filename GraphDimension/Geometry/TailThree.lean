/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Geometry.TwoSimplices
public import GraphDimension.Geometry.SimplexSphere
public import GraphDimension.Geometry.TwoApices

import all GraphDimension.Geometry.TwoSimplices
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Tactic.FinCases

/-!
# Tails of three edges

`SimpleGraph.UnitDistEmbeddable.extend_tail_three` attaches a tail of at most three edges to a
finite placement. The proof maintains the placed vertices that still meet unplaced vertices,
choosing each new point in their common unit locus outside the finite set of occupied points.

`SimpleGraph.infinite_common_unit_sphere_twoSimplices` supplies the three-point unit-sphere
condition for two simplices sharing a facet. There are two possible triangle shapes: an
equilateral triangle, or the two apexes and one facet vertex.
-/

namespace EuclideanGeometry

private lemma infinite_common_unit_sphere_equilateral_triple {d : ℕ} (hd : 4 ≤ d)
    {a b c : EuclideanSpace ℝ (Fin d)}
    (hab : dist a b = 1) (hbc : dist b c = 1) (hac : dist a c = 1) :
    {x | dist x a = 1 ∧ dist x b = 1 ∧ dist x c = 1}.Infinite := by
  have hp : Pairwise fun i j : Fin 3 => dist (![a, b, c] i) (![a, b, c] j) = 1 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [dist_comm]
  have hi := infinite_sphere_inter_of_regular_simplex hp (by simpa using hd)
  simpa [Fin.forall_fin_succ] using hi

end EuclideanGeometry

namespace SimpleGraph

open EuclideanGeometry Metric

noncomputable section

/-- Placed vertices that still have an unplaced neighbour. -/
private def tailBoundary {V : Type*} {G : SimpleGraph V} {d : ℕ}
    (P : @PartialPlacement V G d) : Finset V := by
  classical
  exact P.dom.filter fun w => ∃ u, u ∉ P.dom ∧ G.Adj u w

private lemma mem_tailBoundary {V : Type*} {G : SimpleGraph V} {d : ℕ}
    (P : @PartialPlacement V G d) {w : V} :
    w ∈ tailBoundary P ↔ w ∈ P.dom ∧ ∃ u, u ∉ P.dom ∧ G.Adj u w := by
  classical
  simp [tailBoundary]

-- A placed isolated vertex is absent from the boundary; the placed endpoint of an edge to an
-- unplaced vertex is present. Thus the boundary is neither the domain nor the unplaced set.
example : ∃ P : @PartialPlacement (Fin 3) (edge 1 2) 1,
    P.dom = {0, 1} ∧ tailBoundary P = {1} := by
  classical
  let P : @PartialPlacement (Fin 3) (edge 1 2) 1 := {
    g := fun v => EuclideanSpace.single 0 (v.val : ℝ)
    dom := {0, 1}
    inj := by
      intro x y _ _ h
      have hval : (x.val : ℝ) = (y.val : ℝ) := by
        simpa using congrArg (fun p : EuclideanSpace ℝ (Fin 1) => p 0) h
      exact Fin.ext (Nat.cast_injective hval)
    edge := by
      intro x y hxy hx hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        norm_num [edge_adj] at hxy }
  refine ⟨P, rfl, ?_⟩
  ext w
  fin_cases w <;> norm_num [mem_tailBoundary, P, edge_adj, Fin.exists_fin_succ]

private lemma card_tailBoundary_le {V : Type*} {G : SimpleGraph V} {d : ℕ}
    (P : @PartialPlacement V G d) (t : Finset (Sym2 V))
    (hcov : ∀ u w, u ∉ P.dom → w ∈ P.dom → G.Adj u w → s(u, w) ∈ t) :
    (tailBoundary P).card ≤ t.card := by
  classical
  have hwit : ∀ w : {w // w ∈ tailBoundary P}, ∃ u, u ∉ P.dom ∧ G.Adj u w :=
    fun w => (Finset.mem_filter.mp w.property).2
  choose u hu using hwit
  let e : {w // w ∈ tailBoundary P} → {e // e ∈ t} := fun w =>
    ⟨s(u w, w.val), hcov _ _ (hu w).1 (Finset.mem_filter.mp w.property).1 (hu w).2⟩
  have he : Function.Injective e := by
    intro w z h
    have hh : s(u w, w.val) = s(u z, z.val) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp hh with ⟨_, hwz⟩ | ⟨huz, _⟩
    · exact Subtype.ext hwz
    · exact ((hu w).1 (huz ▸ (Finset.mem_filter.mp z.property).1)).elim
  simpa using Fintype.card_le_of_injective e he

private lemma infinite_common_unit_sphere_of_card_le_three {V : Type*} {d : ℕ}
    (hd : 4 ≤ d) (s : Finset V) (g : V → EuclideanSpace ℝ (Fin d)) (hs : s.card ≤ 3)
    (hClose : ∀ a ∈ s, ∀ b ∈ s, dist (g a) (g b) < 2)
    (hTriple : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a ≠ b → b ≠ c → a ≠ c →
      {x | dist x (g a) = 1 ∧ dist x (g b) = 1 ∧ dist x (g c) = 1}.Infinite) :
    {x | ∀ a ∈ s, dist x (g a) = 1}.Infinite := by
  classical
  match hcard : s.card with
  | 0 =>
    have hz := Finset.card_eq_zero.mp hcard
    simp only [hz, Finset.notMem_empty, IsEmpty.forall_iff, implies_true, Set.ofPred_true]
    exact Set.infinite_univ_iff.mpr (infinite_euclideanSpace (by omega))
  | 1 =>
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
    simpa only [Finset.mem_singleton, forall_eq, sphere] using
      infinite_unitSphere (by omega) (g a)
  | 2 =>
    obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp hcard
    have hab : dist (g a) (g b) < 2 := hClose a (by simp) b (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
      Set.ofPred_and, sphere] using
      infinite_unitSphere_inter_of_dist_lt_two (by omega) hab
  | 3 =>
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
    simpa only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] using
      hTriple a (by simp) b (by simp) c (by simp) hab hbc hac
  | n + 4 => omega

private lemma extend_tail_three_aux {V : Type*} [Finite V] {G : SimpleGraph V} {d : ℕ}
    (hd : 4 ≤ d) (t : Finset (Sym2 V)) (ht : t.card ≤ 3)
    (P : @PartialPlacement V G d)
    (hcov : ∀ u w, G.Adj u w → u ∉ P.dom → s(u, w) ∈ t)
    (hClose : ∀ a ∈ tailBoundary P, ∀ b ∈ tailBoundary P, dist (P.g a) (P.g b) < 2)
    (hTriple : ∀ a ∈ tailBoundary P, ∀ b ∈ tailBoundary P, ∀ c ∈ tailBoundary P,
      a ≠ b → b ≠ c → a ≠ c →
      {x | dist x (P.g a) = 1 ∧ dist x (P.g b) = 1 ∧ dist x (P.g c) = 1}.Infinite) :
    G.UnitDistEmbeddable d := by
  classical
  let _ := Fintype.ofFinite V
  suffices ∀ n (P : @PartialPlacement V G d),
      (∀ u w, G.Adj u w → u ∉ P.dom → s(u, w) ∈ t) →
      (∀ a ∈ tailBoundary P, ∀ b ∈ tailBoundary P, dist (P.g a) (P.g b) < 2) →
      (∀ a ∈ tailBoundary P, ∀ b ∈ tailBoundary P, ∀ c ∈ tailBoundary P,
        a ≠ b → b ≠ c → a ≠ c →
        {x | dist x (P.g a) = 1 ∧ dist x (P.g b) = 1 ∧ dist x (P.g c) = 1}.Infinite) →
      (Finset.univ \ P.dom).card = n → G.UnitDistEmbeddable d from
    this _ P hcov hClose hTriple rfl
  intro n
  induction n with
  | zero =>
    intro P _ _ _ hcard
    have hdom : ∀ x, x ∈ P.dom := by
      have hempty := Finset.card_eq_zero.mp hcard
      exact fun x => Finset.sdiff_eq_empty_iff_subset.mp hempty (Finset.mem_univ x)
    exact ⟨P.g, fun _ _ h => P.inj (hdom _) (hdom _) h,
      fun _ _ h => P.edge h (hdom _) (hdom _)⟩
  | succ n ih =>
    intro P hcov hClose hTriple hcard
    -- Consume a crossing edge whenever there is one. Otherwise every placed vertex has
    -- finished its constraints, and any unplaced vertex can be chosen.
    obtain ⟨v, hv, hchoose⟩ : ∃ v, v ∉ P.dom ∧
        (tailBoundary P = ∅ ∨ ∃ w, w ∈ P.dom ∧ G.Adj v w) := by
      by_cases hb : tailBoundary P = ∅
      · obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < (Finset.univ \ P.dom).card by omega)
        exact ⟨v, (Finset.mem_sdiff.mp hv).2, Or.inl hb⟩
      · obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hb
        obtain ⟨hwd, v, hv, hvw⟩ := (mem_tailBoundary P).mp hw
        exact ⟨v, hv, Or.inr ⟨w, hwd, hvw⟩⟩
    have hBcard : (tailBoundary P).card ≤ 3 :=
      (card_tailBoundary_le P t (fun u w hu _ hadj => hcov u w hadj hu)).trans ht
    obtain ⟨p, hpUnit, hpOut⟩ :=
      (infinite_common_unit_sphere_of_card_le_three hd (tailBoundary P) P.g hBcard
        hClose hTriple).exists_notMem_finite
        (Set.finite_range fun x : {x // x ∈ P.dom} => P.g x.val)
    have hpFresh : ∀ x, x ∈ P.dom → p ≠ P.g x := by
      intro x hx h
      exact hpOut ⟨⟨x, hx⟩, h.symm⟩
    have hpNbr : ∀ {w}, G.Adj v w → w ∈ P.dom → dist p (P.g w) = 1 := by
      intro w hadj hw
      exact hpUnit w ((mem_tailBoundary P).mpr ⟨hw, v, hv, hadj⟩)
    let P' := P.extend_point hv hpFresh hpNbr
    have hdom : P'.dom = insert v P.dom := rfl
    have hout {u} (hu : u ∉ P'.dom) : u ∉ P.dom :=
      fun h => hu (Finset.mem_insert_of_mem h)
    have hboundary {w} (hw : w ∈ tailBoundary P') (hwv : w ≠ v) :
        w ∈ tailBoundary P := by
      obtain ⟨hwd, u, hu, hadj⟩ := (mem_tailBoundary P').mp hw
      exact (mem_tailBoundary P).mpr
        ⟨(Finset.mem_insert.mp hwd).resolve_left hwv, u, hout hu, hadj⟩
    have hcov' : ∀ u w, G.Adj u w → u ∉ P'.dom → s(u, w) ∈ t :=
      fun u w hadj hu => hcov u w hadj (hout hu)
    have hClose' : ∀ a ∈ tailBoundary P', ∀ b ∈ tailBoundary P',
        dist (P'.g a) (P'.g b) < 2 := by
      intro a ha b hb
      change dist (if a = v then p else P.g a) (if b = v then p else P.g b) < 2
      by_cases hav : a = v <;> by_cases hbv : b = v
      · simp [hav, hbv]
      · rw [ite_eq_left hav, ite_eq_right hbv, hpUnit b (hboundary hb hbv)]
        norm_num
      · rw [ite_eq_right hav, ite_eq_left hbv, dist_comm, hpUnit a (hboundary ha hav)]
        norm_num
      · rw [ite_eq_right hav, ite_eq_right hbv]
        exact hClose a (hboundary ha hav) b (hboundary hb hbv)
    -- Once a crossing edge has been consumed, at most two edges can still meet unplaced
    -- vertices. If there was no crossing edge, only the new vertex can enter the boundary.
    have hBcard' : (tailBoundary P').card ≤ 2 := by
      rcases hchoose with hempty | ⟨w, hw, hvw⟩
      · have hsub : tailBoundary P' ⊆ {v} := by
          intro z hz
          by_cases hzv : z = v
          · simp [hzv]
          · have hzold := hboundary hz hzv
            simp [hempty] at hzold
        have hle := Finset.card_le_card hsub
        simpa using hle.trans (by simp : ({v} : Finset V).card ≤ 2)
      · have he : s(v, w) ∈ t := hcov v w hvw hv
        have hle : (tailBoundary P').card ≤ (t.erase s(v, w)).card := by
          apply card_tailBoundary_le
          intro u z hu _ huz
          apply Finset.mem_erase.mpr
          refine ⟨?_, hcov' u z huz hu⟩
          intro h
          rcases Sym2.eq_iff.mp h with ⟨huv, _⟩ | ⟨huw, _⟩
          · exact hu (huv ▸ Finset.mem_insert_self v P.dom)
          · exact hu (huw ▸ Finset.mem_insert_of_mem hw)
        rw [Finset.card_erase_of_mem he] at hle
        omega
    have hTriple' : ∀ a ∈ tailBoundary P', ∀ b ∈ tailBoundary P', ∀ c ∈ tailBoundary P',
        a ≠ b → b ≠ c → a ≠ c →
        {x | dist x (P'.g a) = 1 ∧ dist x (P'.g b) = 1 ∧ dist x (P'.g c) = 1}.Infinite := by
      intro a ha b hb c hc hab hbc hac
      have hlt := Finset.two_lt_card_iff.mpr ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
      omega
    have hcard' : (Finset.univ \ P'.dom).card = n := by
      have hvU : v ∈ Finset.univ \ P.dom := Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩
      rw [hdom, Finset.sdiff_insert, Finset.card_erase_of_mem hvU, hcard]
      omega
    exact ih P' hcov' hClose' hTriple' hcard'

@[expose] public section

/-- Attach at most three edges to a placed set with pairwise distances less than two and
infinite common unit loci for triples of distinct points.

At each step, place the new vertex at unit distance from every placed vertex that still has an
unplaced neighbour. There are at most three such vertices. Whenever this boundary is nonempty,
choose a new vertex that consumes a crossing edge; the next boundary then has size at most two.
This includes the path `p–u–v–q`: choose `u` at unit distance from both `p` and `q`, so that `v`
can subsequently be chosen at unit distance from `u` and `q`. Extra unit distances are allowed.
All choices avoid the finite set of points already used. -/
theorem UnitDistEmbeddable.extend_tail_three {V : Type*} [Finite V] {G : SimpleGraph V} {d : ℕ}
    (hd : 4 ≤ d) {s : Finset V} (f : {v : V // v ∈ s} → EuclideanSpace ℝ (Fin d))
    (hfInj : Function.Injective f)
    (hfDist : ∀ a b, (G.induce (s : Set V)).Adj a b → dist (f a) (f b) = 1)
    (hClose : ∀ a b, dist (f a) (f b) < 2)
    (hTriple : ∀ a b c, a ≠ b → b ≠ c → a ≠ c →
      {x | dist x (f a) = 1 ∧ dist x (f b) = 1 ∧ dist x (f c) = 1}.Infinite)
    (hTail : ∃ t : Finset (Sym2 V), t.card ≤ 3 ∧
      ∀ ⦃x y : V⦄, G.Adj x y → s(x, y) ∉ t → x ∈ s ∧ y ∈ s) : G.UnitDistEmbeddable d := by
  classical
  have hfDist' : ∀ a b : {v : V // v ∈ s}, G.Adj a.val b.val → dist (f a) (f b) = 1 :=
    fun a b h => hfDist a b (induce_adj.mpr h)
  let P := of_subset f hfInj hfDist'
  obtain ⟨t, ht, hcov⟩ := hTail
  apply extend_tail_three_aux hd t ht P
  · intro u w huw hu
    by_contra h
    exact hu (hcov huw h).1
  · intro a ha b hb
    have haD : a ∈ s := ((mem_tailBoundary P).mp ha).1
    have hbD : b ∈ s := ((mem_tailBoundary P).mp hb).1
    simpa [P, of_subset, haD, hbD] using hClose ⟨a, haD⟩ ⟨b, hbD⟩
  · intro a ha b hb c hc hab hbc hac
    have haD : a ∈ s := ((mem_tailBoundary P).mp ha).1
    have hbD : b ∈ s := ((mem_tailBoundary P).mp hb).1
    have hcD : c ∈ s := ((mem_tailBoundary P).mp hc).1
    simpa [P, of_subset, haD, hbD, hcD] using
      hTriple ⟨a, haD⟩ ⟨b, hbD⟩ ⟨c, hcD⟩
        (fun h => hab (congrArg Subtype.val h)) (fun h => hbc (congrArg Subtype.val h))
        (fun h => hac (congrArg Subtype.val h))

/-- Every triple of distinct vertices in the two-simplex distance pattern has infinitely many
common unit-sphere points in dimension at least four. Injectivity need not be assumed separately:
only the prescribed distances are used. -/
theorem infinite_common_unit_sphere_twoSimplices {d : ℕ} (hd : 4 ≤ d)
    (f : Fin (d + 2) → EuclideanSpace ℝ (Fin d)) {a b : Fin (d + 2)} (hab : a ≠ b)
    (hfDist : ∀ i j, i ≠ j → ¬ (i = a ∧ j = b) → ¬ (i = b ∧ j = a) →
      dist (f i) (f j) = 1)
    (hfApex : dist (f a) (f b) = Real.sqrt (2 + 2 / (d : ℝ)))
    (i j k : Fin (d + 2)) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    {x | dist x (f i) = 1 ∧ dist x (f j) = 1 ∧ dist x (f k) = 1}.Infinite := by
  have hapex (v : Fin (d + 2)) (hva : v ≠ a) (hvb : v ≠ b) :
      {x | dist x (f a) = 1 ∧ dist x (f b) = 1 ∧ dist x (f v) = 1}.Infinite := by
    apply EuclideanGeometry.infinite_common_unit_sphere_two_apices hd
    · rw [hfApex, Real.sq_sqrt (by positivity)]
    · exact hfDist a v hva.symm (by simp [hvb]) (by simp [hab])
    · exact hfDist b v hvb.symm (by simp [hab.symm]) (by simp [hva])
  by_cases h₁ : (i = a ∧ j = b) ∨ (i = b ∧ j = a)
  · rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hapex k hik.symm hjk.symm
    · simpa [and_comm, and_left_comm, and_assoc] using hapex k hjk.symm hik.symm
  by_cases h₂ : (j = a ∧ k = b) ∨ (j = b ∧ k = a)
  · rcases h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [and_comm, and_left_comm, and_assoc] using hapex i hij hik
    · simpa [and_comm, and_left_comm, and_assoc] using hapex i hik hij
  by_cases h₃ : (i = a ∧ k = b) ∨ (i = b ∧ k = a)
  · rcases h₃ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [and_comm, and_left_comm, and_assoc] using hapex j hij.symm hjk
    · simpa [and_comm, and_left_comm, and_assoc] using hapex j hjk hij.symm
  exact EuclideanGeometry.infinite_common_unit_sphere_equilateral_triple hd
    (hfDist i j hij (fun h => h₁ (Or.inl h)) (fun h => h₁ (Or.inr h)))
    (hfDist j k hjk (fun h => h₂ (Or.inl h)) (fun h => h₂ (Or.inr h)))
    (hfDist i k hik (fun h => h₃ (Or.inl h)) (fun h => h₃ (Or.inr h)))

end

end

end SimpleGraph

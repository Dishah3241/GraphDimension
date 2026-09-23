/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Three pairwise disjoint edges in a two-regular graph on seven vertices

Every connected component of a two-regular simple graph is a cycle: the component supports are
exactly the vertex sets of cycle walks
(`SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp`). The first
`2k` vertices of a cycle walk of length at least `2k + 1`, taken in consecutive pairs, form `k`
pairwise vertex-disjoint edges.

For a two-regular graph on seven vertices the component sizes are all at least three (a cycle
has length at least three) and sum to seven. If some component's cycle walk has length at least
six, its first six vertices already give three disjoint edges. Otherwise it has three, four or
five vertices, so some vertex lies outside it, and that vertex's component has a cycle walk of
length three or four: together with the edges of the first component this again gives three
pairwise vertex-disjoint edges. The only way to fall short would be a triangle next to a
triangle, but then the seventh vertex would need a third component of at least three vertices,
which does not fit. So the classification into `C₇` and `C₃ ⊔ C₄` is never needed as such: the
count over components carries the argument.

## Source

Chaffee and Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J.
Combin. **64(2)** (2016), 327–333, use this in the proof of their Theorem 10: a four-regular
graph on seven vertices has a two-regular complement, so the complement has three pairwise
vertex-disjoint edges, and the graph embeds in `K₇` minus a matching of size three, which is
`K_{1,2,2,2}`.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {v : V} {p : G.Walk v v}

section CycleWalkLemmas

/-- The vertices of a cycle walk at distinct positions below its length are distinct. -/
private lemma Walk.IsCycle.getVert_ne (hp : p.IsCycle) {i j : ℕ} (hi : i + 1 ≤ p.length)
    (hj : j + 1 ≤ p.length) (hij : i ≠ j) : p.getVert i ≠ p.getVert j := by
  intro h
  have hi' : i ≤ p.length - 1 := by omega
  have hj' : j ≤ p.length - 1 := by omega
  exact hij (hp.getVert_injOn' hi' hj' h)

/-- The support of a cycle walk has as many distinct vertices as its length: the first and last
vertex coincide, and no other repetition occurs. -/
private lemma Walk.IsCycle.support_toFinset_card [DecidableEq V] (hp : p.IsCycle) :
    p.support.toFinset.card = p.length := by
  classical
  have hv : v ∈ p.support := by
    have h0 := Walk.getVert_mem_support p p.length
    rwa [Walk.getVert_length p] at h0
  have hsplit : p.support.dropLast ++ [v] = p.support := by
    have h1 := List.dropLast_append_getLast (l := p.support)
      (List.ne_nil_of_length_pos (by rw [Walk.length_support]; omega))
    rwa [Walk.getLast_support p] at h1
  have h2 : p.support.count v = 2 := hp.count_support
  have hcount : p.support.dropLast.count v = 1 := by
    rw [← hsplit, List.count_append, List.count_singleton_self] at h2
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
    List.length_dropLast, Walk.length_support]
  omega

/-- The first and second vertices of a cycle walk are adjacent and distinct. -/
private lemma Walk.IsCycle.first_edge (hp : p.IsCycle) :
    p.getVert 0 ≠ p.getVert 1 ∧ G.Adj (p.getVert 0) (p.getVert 1) := by
  have h3 := hp.three_le_length
  exact ⟨hp.getVert_ne (by omega) (by omega) (by omega),
    Walk.adj_getVert_succ p (by omega)⟩

/-- A cycle walk of length at least four has two disjoint edges: the first two and the next two
vertices, taken in pairs. -/
private lemma Walk.IsCycle.first_two_disjoint_edges (hp : p.IsCycle) (h4 : 4 ≤ p.length) :
    List.Nodup [p.getVert 0, p.getVert 1, p.getVert 2, p.getVert 3] ∧
      G.Adj (p.getVert 0) (p.getVert 1) ∧ G.Adj (p.getVert 2) (p.getVert 3) := by
  refine ⟨?_, Walk.adj_getVert_succ p (by omega), Walk.adj_getVert_succ p (by omega)⟩
  change List.Pairwise (· ≠ ·) [p.getVert 0, p.getVert 1, p.getVert 2, p.getVert 3]
  have h01 : p.getVert 0 ≠ p.getVert 1 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h02 : p.getVert 0 ≠ p.getVert 2 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h03 : p.getVert 0 ≠ p.getVert 3 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h12 : p.getVert 1 ≠ p.getVert 2 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h13 : p.getVert 1 ≠ p.getVert 3 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h23 : p.getVert 2 ≠ p.getVert 3 := hp.getVert_ne (by omega) (by omega) (by omega)
  refine List.Pairwise.cons ?_ ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h01
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h02
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h03
    exact absurd hx List.not_mem_nil
  · refine List.Pairwise.cons ?_ ?_
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h12
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h13
      exact absurd hx List.not_mem_nil
    · refine List.Pairwise.cons ?_ ?_
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h23
        exact absurd hx List.not_mem_nil
      · simp

/-- A cycle walk of length at least six has three disjoint edges: its first six vertices, taken
in consecutive pairs. -/
private lemma Walk.IsCycle.first_three_disjoint_edges (hp : p.IsCycle) (h6 : 6 ≤ p.length) :
    List.Nodup [p.getVert 0, p.getVert 1, p.getVert 2, p.getVert 3, p.getVert 4, p.getVert 5] ∧
      G.Adj (p.getVert 0) (p.getVert 1) ∧ G.Adj (p.getVert 2) (p.getVert 3) ∧
      G.Adj (p.getVert 4) (p.getVert 5) := by
  refine ⟨?_, Walk.adj_getVert_succ p (by omega), Walk.adj_getVert_succ p (by omega),
    Walk.adj_getVert_succ p (by omega)⟩
  change List.Pairwise (· ≠ ·) [p.getVert 0, p.getVert 1, p.getVert 2, p.getVert 3, p.getVert 4,
    p.getVert 5]
  have h01 : p.getVert 0 ≠ p.getVert 1 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h02 : p.getVert 0 ≠ p.getVert 2 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h03 : p.getVert 0 ≠ p.getVert 3 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h04 : p.getVert 0 ≠ p.getVert 4 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h05 : p.getVert 0 ≠ p.getVert 5 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h12 : p.getVert 1 ≠ p.getVert 2 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h13 : p.getVert 1 ≠ p.getVert 3 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h14 : p.getVert 1 ≠ p.getVert 4 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h15 : p.getVert 1 ≠ p.getVert 5 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h23 : p.getVert 2 ≠ p.getVert 3 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h24 : p.getVert 2 ≠ p.getVert 4 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h25 : p.getVert 2 ≠ p.getVert 5 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h34 : p.getVert 3 ≠ p.getVert 4 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h35 : p.getVert 3 ≠ p.getVert 5 := hp.getVert_ne (by omega) (by omega) (by omega)
  have h45 : p.getVert 4 ≠ p.getVert 5 := hp.getVert_ne (by omega) (by omega) (by omega)
  refine List.Pairwise.cons ?_ ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h01
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h02
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h03
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h04
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h05
    exact absurd hx List.not_mem_nil
  · refine List.Pairwise.cons ?_ ?_
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h12
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h13
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h14
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h15
      exact absurd hx List.not_mem_nil
    · refine List.Pairwise.cons ?_ ?_
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h23
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h24
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h25
        exact absurd hx List.not_mem_nil
      · refine List.Pairwise.cons ?_ ?_
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact h34
          rcases List.mem_cons.mp hx with rfl | hx
          · exact h35
          exact absurd hx List.not_mem_nil
        · refine List.Pairwise.cons ?_ ?_
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact h45
            exact absurd hx List.not_mem_nil
          · simp

/-- A vertex distinct from four given vertices is not one of them. -/
private lemma notMem_four_of_ne {α : Type*} {x a b c d : α} (h₁ : x ≠ a) (h₂ : x ≠ b)
    (h₃ : x ≠ c) (h₄ : x ≠ d) : x ∉ [a, b, c, d] := by
  intro hx
  rcases List.mem_cons.mp hx with h | hx
  · exact h₁ h
  rcases List.mem_cons.mp hx with h | hx
  · exact h₂ h
  rcases List.mem_cons.mp hx with h | hx
  · exact h₃ h
  rcases List.mem_cons.mp hx with h | hx
  · exact h₄ h
  exact List.not_mem_nil hx

/-- A nodup list of four vertices stays nodup when two further vertices are appended, provided
neither of the two is among the first four and they differ from each other. -/
private lemma nodup_four_append_pair {α : Type*} {a b c d x y : α}
    (h : List.Nodup [a, b, c, d]) (hx : x ∉ [a, b, c, d]) (hy : y ∉ [a, b, c, d])
    (hxy : x ≠ y) : List.Nodup [a, b, c, d, x, y] := by
  change List.Nodup ([a, b, c, d] ++ [x, y])
  rw [List.nodup_append]
  refine ⟨h, ?_, ?_⟩
  · exact List.Pairwise.cons (fun z hz heq => hxy (heq.trans (by simpa using hz)))
      (List.Pairwise.cons (fun z hz => False.elim (List.not_mem_nil hz)) List.Pairwise.nil)
  intro u hu v hv huv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hx (by rw [← huv]; exact hu)
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hy (by rw [← huv]; exact hu)
  exact absurd hv List.not_mem_nil

end CycleWalkLemmas

/-- **Three pairwise disjoint edges in a two-regular graph on seven vertices.** A two-regular
simple graph on `Fin 7` has three pairwise vertex-disjoint edges: it is the heptagon `C₇` or the
disjoint sum `C₃ ⊔ C₄`, and either contains a matching of size three. The proof argues by the
count over cycle components rather than by naming the two models. -/
theorem exists_three_pairwise_disjoint_edges (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    (h : G.IsRegularOfDegree 2) :
    ∃ a b c d e f : Fin 7, G.Adj a b ∧ G.Adj c d ∧ G.Adj e f ∧
      List.Nodup [a, b, c, d, e, f] := by
  classical
  -- every vertex has two neighbours
  have hnb : ∀ w : Fin 7, (G.neighborSet w).Nonempty := by
    intro w
    have hw : (G.neighborFinset w).card = 2 := by
      rw [card_neighborFinset_eq_degree]; exact h.degree_eq w
    obtain ⟨x, y, hx, -, -⟩ := Finset.one_lt_card_iff.mp (by rw [hw]; decide)
    exact ⟨x, by simpa using hx⟩
  -- a two-regular graph is a graph of cycles
  have hcycles : G.IsCycles := by
    intro w _
    rw [Set.ncard_eq_toFinset_card',
      show (G.neighborSet w).toFinset = G.neighborFinset w from rfl,
      card_neighborFinset_eq_degree, h.degree_eq w]
  -- the cycle through vertex `0`
  have h0mem : (0 : Fin 7) ∈ (G.connectedComponentMk 0).supp :=
    (G.connectedComponentMk 0).mem_supp_iff 0 |>.mpr rfl
  obtain ⟨p, hpcyc, hpverts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp h0mem (hnb 0)
  have hplen : 3 ≤ p.length := hpcyc.three_le_length
  have hcard : (G.connectedComponentMk 0).supp.toFinset.card = p.length := by
    have heq : (G.connectedComponentMk 0).supp.toFinset = p.support.toFinset := by
      ext x
      rw [Set.mem_toFinset, ← hpverts, Walk.verts_toSubgraph p, Set.mem_ofPred_eq,
        List.mem_toFinset]
    rw [heq, hpcyc.support_toFinset_card]
  have mem0 : ∀ i : ℕ, p.getVert i ∈ (G.connectedComponentMk 0).supp := by
    intro i
    rw [← hpverts, Walk.verts_toSubgraph p]
    exact Walk.getVert_mem_support p i
  by_cases h6 : 6 ≤ p.length
  · -- a long cycle through `0` provides the three edges on its own
    obtain ⟨hnd, ha, hb, hc⟩ := hpcyc.first_three_disjoint_edges h6
    exact ⟨p.getVert 0, p.getVert 1, p.getVert 2, p.getVert 3, p.getVert 4, p.getVert 5,
      ha, hb, hc, hnd⟩
  · -- the component of `0` has three to five vertices, so a vertex lies outside it
    have houtside : ((Finset.univ \
        (G.connectedComponentMk 0).supp.toFinset : Finset (Fin 7))).card ≥ 2 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, hcard]
      omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (show
        0 < (Finset.univ \ (G.connectedComponentMk 0).supp.toFinset : Finset (Fin 7)).card by
        omega)
    obtain ⟨-, hw₂⟩ := Finset.mem_sdiff.mp hw
    have hwC₀ : w ∉ (G.connectedComponentMk 0).supp := fun hm => hw₂ (Set.mem_toFinset.mpr hm)
    have hwC₁ : w ∈ (G.connectedComponentMk w).supp :=
      (G.connectedComponentMk w).mem_supp_iff w |>.mpr rfl
    have hne : G.connectedComponentMk w ≠ G.connectedComponentMk 0 := by
      intro heq
      exact hwC₀ (by rw [← heq]; exact hwC₁)
    -- the cycle through `w`
    obtain ⟨q, hqcyc, hqverts⟩ :=
      hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hwC₁ (hnb w)
    have hqlen : 3 ≤ q.length := hqcyc.three_le_length
    have hcardq : (G.connectedComponentMk w).supp.toFinset.card = q.length := by
      have heq : (G.connectedComponentMk w).supp.toFinset = q.support.toFinset := by
        ext x
        rw [Set.mem_toFinset, ← hqverts, Walk.verts_toSubgraph q, Set.mem_ofPred_eq,
          List.mem_toFinset]
      rw [heq, hqcyc.support_toFinset_card]
    have memq : ∀ i : ℕ, q.getVert i ∈ (G.connectedComponentMk w).supp := by
      intro i
      rw [← hqverts, Walk.verts_toSubgraph q]
      exact Walk.getVert_mem_support q i
    -- distinct components are vertex-disjoint
    have hsub : (G.connectedComponentMk w).supp.toFinset ⊆
        Finset.univ \ (G.connectedComponentMk 0).supp.toFinset := by
      intro x hx
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, fun hx0 => ?_⟩
      exact hne (ConnectedComponent.eq_of_common_vertex (Set.mem_toFinset.mp hx)
        (Set.mem_toFinset.mp hx0))
    by_cases h4 : 4 ≤ p.length
    · -- two edges from the cycle through `0`, one from the cycle through `w`
      obtain ⟨hnd4, ha, hb⟩ := hpcyc.first_two_disjoint_edges h4
      obtain ⟨hw01, hq1⟩ := hqcyc.first_edge
      have hneq0 : ∀ i : ℕ, q.getVert 0 ≠ p.getVert i := by
        intro i hij
        exact hne (ConnectedComponent.eq_of_common_vertex (hij ▸ memq 0) (mem0 i))
      have hneq1 : ∀ i : ℕ, q.getVert 1 ≠ p.getVert i := by
        intro i hij
        exact hne (ConnectedComponent.eq_of_common_vertex (hij ▸ memq 1) (mem0 i))
      exact ⟨p.getVert 0, p.getVert 1, p.getVert 2, p.getVert 3, q.getVert 0, q.getVert 1,
        ha, hb, hq1, nodup_four_append_pair hnd4 (notMem_four_of_ne (hneq0 0) (hneq0 1)
          (hneq0 2) (hneq0 3)) (notMem_four_of_ne (hneq1 0) (hneq1 1) (hneq1 2) (hneq1 3))
          hw01⟩
    · -- the cycle through `0` is a triangle, so the cycle through `w` has four vertices
      have hp3 : p.length = 3 := by omega
      by_cases hq4 : 4 ≤ q.length
      · -- two edges from the cycle through `w`, one from the triangle through `0`
        obtain ⟨hnd4, ha, hb⟩ := hqcyc.first_two_disjoint_edges hq4
        obtain ⟨hv01, hp1⟩ := hpcyc.first_edge
        have hneq0 : ∀ i : ℕ, p.getVert 0 ≠ q.getVert i := by
          intro i hij
          exact hne.symm (ConnectedComponent.eq_of_common_vertex (hij ▸ mem0 0) (memq i))
        have hneq1 : ∀ i : ℕ, p.getVert 1 ≠ q.getVert i := by
          intro i hij
          exact hne.symm (ConnectedComponent.eq_of_common_vertex (hij ▸ mem0 1) (memq i))
        exact ⟨q.getVert 0, q.getVert 1, q.getVert 2, q.getVert 3, p.getVert 0, p.getVert 1,
          ha, hb, hp1, nodup_four_append_pair hnd4 (notMem_four_of_ne (hneq0 0) (hneq0 1)
            (hneq0 2) (hneq0 3)) (notMem_four_of_ne (hneq1 0) (hneq1 1) (hneq1 2) (hneq1 3))
            hv01⟩
      · -- two adjacent triangles would leave the seventh vertex without a component of its own
        exfalso
        have hdisj : Disjoint (G.connectedComponentMk 0).supp.toFinset
          (G.connectedComponentMk w).supp.toFinset := by
          rw [Finset.disjoint_left]
          intro x hx hxw
          exact hne (ConnectedComponent.eq_of_common_vertex (Set.mem_toFinset.mp hxw)
            (Set.mem_toFinset.mp hx))
        have hcardU : ((G.connectedComponentMk 0).supp.toFinset ∪
            (G.connectedComponentMk w).supp.toFinset : Finset (Fin 7)).card = 6 := by
          rw [Finset.card_union_of_disjoint hdisj, hcard, hcardq]
          omega
        have houtside2 : ((Finset.univ \ ((G.connectedComponentMk 0).supp.toFinset ∪
            (G.connectedComponentMk w).supp.toFinset : Finset (Fin 7)))).card ≥ 1 := by
          rw [Finset.card_sdiff_of_subset
            (Finset.union_subset (Finset.subset_univ _) (Finset.subset_univ _)),
            Finset.card_univ, Fintype.card_fin, hcardU]
        obtain ⟨u, hu⟩ := Finset.card_pos.mp (show
            0 < (Finset.univ \ ((G.connectedComponentMk 0).supp.toFinset ∪
              (G.connectedComponentMk w).supp.toFinset : Finset (Fin 7))).card by
            omega)
        obtain ⟨-, hu₂⟩ := Finset.mem_sdiff.mp hu
        have huC₀ : u ∉ (G.connectedComponentMk 0).supp := fun hm =>
          hu₂ (Finset.mem_union_left _ (Set.mem_toFinset.mpr hm))
        have huC₁ : u ∉ (G.connectedComponentMk w).supp := fun hm =>
          hu₂ (Finset.mem_union_right _ (Set.mem_toFinset.mpr hm))
        have huC₂ : u ∈ (G.connectedComponentMk u).supp :=
          (G.connectedComponentMk u).mem_supp_iff u |>.mpr rfl
        have hne₀ : G.connectedComponentMk u ≠ G.connectedComponentMk 0 := by
          intro heq
          exact huC₀ (by rw [← heq]; exact huC₂)
        have hne₁ : G.connectedComponentMk u ≠ G.connectedComponentMk w := by
          intro heq
          exact huC₁ (by rw [← heq]; exact huC₂)
        obtain ⟨r, hrcyc, hrverts⟩ :=
          hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp huC₂ (hnb u)
        have hcardr : (G.connectedComponentMk u).supp.toFinset.card = r.length := by
          have heq : (G.connectedComponentMk u).supp.toFinset = r.support.toFinset := by
            ext x
            rw [Set.mem_toFinset, ← hrverts, Walk.verts_toSubgraph r, Set.mem_ofPred_eq,
              List.mem_toFinset]
          rw [heq, hrcyc.support_toFinset_card]
        have hsubr : (G.connectedComponentMk u).supp.toFinset ⊆ Finset.univ \
            ((G.connectedComponentMk 0).supp.toFinset ∪
              (G.connectedComponentMk w).supp.toFinset) := by
          intro x hx
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, fun hxy => ?_⟩
          rcases Finset.mem_union.mp hxy with h0 | h1
          · exact hne₀ (ConnectedComponent.eq_of_common_vertex (Set.mem_toFinset.mp hx)
              (Set.mem_toFinset.mp h0))
          · exact hne₁ (ConnectedComponent.eq_of_common_vertex (Set.mem_toFinset.mp hx)
              (Set.mem_toFinset.mp h1))
        have hle := Finset.card_le_card hsubr
        rw [Finset.card_sdiff_of_subset
          (Finset.union_subset (Finset.subset_univ _) (Finset.subset_univ _)),
          Finset.card_univ, Fintype.card_fin, hcardU, hcardr] at hle
        have hr3 := hrcyc.three_le_length
        omega

/-- **The form used by Chaffee--Noble's Theorem 10.** A four-regular graph on `Fin 7` has a
two-regular complement, which therefore has three pairwise vertex-disjoint edges: the graph is a
subgraph of `K₇` minus a matching of size three, which is `K_{1,2,2,2}`. -/
theorem exists_three_pairwise_disjoint_edges_compl (G : SimpleGraph (Fin 7))
    [DecidableRel G.Adj] (h : G.IsRegularOfDegree 4) :
    ∃ a b c d e f : Fin 7, Gᶜ.Adj a b ∧ Gᶜ.Adj c d ∧ Gᶜ.Adj e f ∧
      List.Nodup [a, b, c, d, e, f] :=
  exists_three_pairwise_disjoint_edges Gᶜ (by simpa [Fintype.card_fin] using h.compl)

end SimpleGraph

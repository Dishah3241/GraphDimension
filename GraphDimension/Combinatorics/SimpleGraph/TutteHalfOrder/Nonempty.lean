/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Combinatorics.SimpleGraph.TutteCounting
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Tactic.Linarith

/-!
# Nonempty Tutte violating sets in graphs of twice a prescribed order

For a graph on `2 * d` vertices whose closed neighbourhoods have at least `d` vertices,
a nonempty Tutte violating set must have size `d - 1`. At that size, its complement
is a clique in the complementary graph.
-/

@[expose] public section

namespace SimpleGraph

/-- A nonempty set of size at most `d - 2` cannot violate Tutte's condition when the graph
has order `2 * d` and every closed neighbourhood has at least `d` vertices. -/
theorem not_isTutteViolator_of_card_between
    {V : Type*} [Finite V] (H : SimpleGraph V) {d : ℕ} (S : Set V)
    (hcard : Nat.card V = 2 * d)
    (hmin : ∀ v, d ≤ (H.neighborSet v).ncard + 1)
    (hpos : 1 ≤ S.ncard) (hsmall : S.ncard + 2 ≤ d) :
    ¬ H.IsTutteViolator S := by
  intro hviol
  have hbounds := hviol.card_bounds (hcard ▸ even_two_mul d)
  have hremaining :
      S.ncard + Nat.card ((⊤ : H.Subgraph).deleteVerts S).verts = 2 * d := by
    rw [Nat.card_coe_set_eq, Subgraph.deleteVerts_verts,
      Subgraph.verts_top, ← Set.compl_eq_univ_sdiff, Set.ncard_add_ncard_compl, hcard]
  have hle : S.ncard ≤ d := by omega
  have hcount := mul_ncard_le_card_of_le_ncard_connectedComponent
    ((⊤ : H.Subgraph).deleteVerts S).coe
    ((⊤ : H.Subgraph).deleteVerts S).coe.oddComponents (d - S.ncard)
    (fun c _ => by
      have := H.le_ncard_add_ncard_deleteVerts_component S hmin c
      omega)
  have hsub := Nat.sub_add_cancel hle
  have hgap : 2 ≤ d - S.ncard := by omega
  have hmul := Nat.mul_le_mul_left (d - S.ncard) hbounds.1
  have hstrict := Nat.mul_le_mul_left S.ncard hgap
  nlinarith

/-- A set containing at least half the vertices cannot violate Tutte's condition. -/
theorem not_isTutteViolator_of_half_card_le
    {V : Type*} [Finite V] (H : SimpleGraph V) {d : ℕ} (S : Set V)
    (hcard : Nat.card V = 2 * d) (hlarge : d ≤ S.ncard) :
    ¬ H.IsTutteViolator S := by
  intro hviol
  have := hviol.card_bounds (hcard ▸ even_two_mul d)
  omega

/-- A Tutte violating set of size `d - 1` in a graph of order `2 * d` leaves a clique of
order `d + 1` in the complementary graph. -/
theorem exists_isNClique_compl_of_isTutteViolator_card_add_one
    {V : Type*} [Finite V] (H : SimpleGraph V) {d : ℕ} (S : Set V)
    (hcard : Nat.card V = 2 * d) (hS : S.ncard + 1 = d)
    (hviol : H.IsTutteViolator S) :
    ∃ t : Finset V, Hᶜ.IsNClique (d + 1) t := by
  classical
  let := Fintype.ofFinite V
  have hbounds := hviol.card_bounds (hcard ▸ even_two_mul d)
  have hremaining :
      S.ncard + Nat.card ((⊤ : H.Subgraph).deleteVerts S).verts = 2 * d := by
    rw [Nat.card_coe_set_eq, Subgraph.deleteVerts_verts,
      Subgraph.verts_top, ← Set.compl_eq_univ_sdiff, Set.ncard_add_ncard_compl, hcard]
  have hbot := eq_bot_of_card_le_ncard_oddComponents
    ((⊤ : H.Subgraph).deleteVerts S).coe (by omega)
  refine ⟨Sᶜ.toFinset, ?_, ?_⟩
  · intro v hv w hw hvw
    have hvS : v ∉ S := Set.mem_toFinset.mp hv
    have hwS : w ∉ S := Set.mem_toFinset.mp hw
    refine ⟨hvw, ?_⟩
    intro hadj
    have hvverts : v ∈ ((⊤ : H.Subgraph).deleteVerts S).verts := by simpa using hvS
    have hwverts : w ∈ ((⊤ : H.Subgraph).deleteVerts S).verts := by simpa using hwS
    have hcoe : ((⊤ : H.Subgraph).deleteVerts S).coe.Adj
        ⟨v, hvverts⟩ ⟨w, hwverts⟩ := ⟨hvverts, hwverts, hadj⟩
    simp [hbot] at hcoe
  · rw [← Set.ncard_eq_toFinset_card']
    have := Set.ncard_add_ncard_compl S
    omega

end SimpleGraph

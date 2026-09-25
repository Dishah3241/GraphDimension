/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic
public import Mathlib.Combinatorics.SimpleGraph.Copy

import GraphDimension.Combinatorics.SimpleGraph.SixVertices
import GraphDimension.Combinatorics.SimpleGraph.SixVerticesTenEdges
import GraphDimension.Geometry.Wheel
import GraphDimension.Geometry.PathComplement
import GraphDimension.Geometry.Octahedron
import GraphDimension.Geometry.Prism
import GraphDimension.Geometry.FinLe
import GraphDimension.Geometry.UnitDistanceComap
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fin.VecNotation

/-!
# Six vertices with minimum degree three and at most ten edges

The degree sum forces nine or ten edges. The nine-edge classification leaves the planar
prism after excluding `K₃,₃`. For ten edges, the complement classification gives a wheel,
the complement of a path, a subgraph of the octahedron, or another forbidden `K₃,₃` copy.
-/

namespace SimpleGraph

private instance (n : ℕ) : DecidableRel (pathGraph n).Adj :=
  fun _ _ => decidable_of_iff _ pathGraph_adj.symm

private instance {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (G ⊕g H).Adj := by
  intro a b
  cases a <;> cases b <;> dsimp only [SimpleGraph.sum] <;> infer_instance

/-- Complement an isomorphism out of a complement, keeping its vertex equivalence. -/
private def sixVerticesComplIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : Gᶜ ≃g H) : G ≃g Hᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' {a b} := by
    rw [compl_adj, e.toEquiv.injective.ne_iff, not_congr e.map_rel_iff', ← compl_adj,
      compl_compl]

/-- Relabel the complementary pentagon in the rim order, keeping the isolate as the hub. -/
private def complCycleFiveIsoWheel :
    (cycleGraph 5 ⊕g (⊥ : SimpleGraph (Fin 1)))ᶜ ≃g wheelGraphFive where
  toEquiv := (finSumFinEquiv : Fin 5 ⊕ Fin 1 ≃ Fin 6).trans
    { toFun := ![0, 2, 4, 1, 3, 5]
      invFun := ![0, 3, 1, 4, 2, 5]
      left_inv := by decide
      right_inv := by decide }
  map_rel_iff' := by
    change ∀ a b, _
    simp only [wheelGraphFive_adj_iff]
    decide

/-- Edges `01`, `23` of the four-cycle and the path edge become opposite pairs. -/
private lemma complCycleFourPathTwoContainedOctahedron :
    (cycleGraph 4 ⊕g pathGraph 2)ᶜ ⊑ octahedronGraph := by
  refine ⟨{
    toHom := { toFun := (finSumFinEquiv : Fin 4 ⊕ Fin 2 ≃ Fin 6), map_rel' := ?_ }
    injective' := finSumFinEquiv.injective }⟩
  change ∀ a b, _
  simp only [octahedronGraph_adj_iff]
  decide

/-- All edges between the two triples are present in the complement of their disjoint sum. -/
private lemma completeBipartiteContainedComplCycleThreePathThree :
    completeBipartiteGraph (Fin 3) (Fin 3) ⊑ (cycleGraph 3 ⊕g pathGraph 3)ᶜ := by
  refine ⟨{
    toHom := { toFun := id, map_rel' := ?_ }
    injective' := Function.injective_id }⟩
  change ∀ a b, _
  simp only [completeBipartiteGraph_adj]
  decide

@[expose] public section

/-- A six-vertex graph with at most ten edges and minimum degree at least three has a
unit-distance placement in three dimensions if it contains no `K₃,₃`. -/
theorem unitDistEmbeddable_three_fin_six_of_minDegree_ge_three
    (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (hE : G.edgeSet.ncard ≤ 10)
    (hδ : ∀ v, 3 ≤ G.degree v)
    (hK33 : ¬ ((completeBipartiteGraph (Fin 3) (Fin 3)) ⊑ G)) :
    G.UnitDistEmbeddable 3 := by
  have hsum : 18 ≤ ∑ v, G.degree v := by
    calc
      18 = ∑ _ : Fin 6, (3 : ℕ) := by decide
      _ ≤ ∑ v, G.degree v := Finset.sum_le_sum fun v _ => hδ v
  rw [G.sum_degrees_eq_twice_card_edges, edgeFinset_card,
    Set.fintypeCard_eq_ncard] at hsum
  have hcases : G.edgeSet.ncard = 9 ∨ G.edgeSet.ncard = 10 := by omega
  rcases hcases with h9 | h10
  · have h9' : G.edgeFinset.card = 9 := by
      rw [edgeFinset_card, Set.fintypeCard_eq_ncard, h9]
    rcases nine_edges_six_minDegree_three h9' hδ with h | h
    · obtain ⟨e⟩ := h
      exact (hK33 e.symm.isContained).elim
    · obtain ⟨e⟩ := h
      exact (UnitDistEmbeddable.of_iso (sixVerticesComplIso e)).mpr
        (unitDistEmbeddable_compl_cycleGraph_six.mono (by decide))
  · rcases compl_classification_fin_six_of_ten_edges G h10 hδ with
      h | h | h | h
    · obtain ⟨e⟩ := h
      exact (UnitDistEmbeddable.of_iso
        (Iso.comp complCycleFiveIsoWheel (sixVerticesComplIso e))).mpr
        unitDistEmbeddable_wheelGraph_five
    · obtain ⟨e⟩ := h
      exact (UnitDistEmbeddable.of_iso (sixVerticesComplIso e)).mpr
        unitDistEmbeddable_compl_pathGraph_six
    · obtain ⟨e⟩ := h
      obtain ⟨f⟩ := complCycleFourPathTwoContainedOctahedron
      exact (UnitDistEmbeddable.of_iso (sixVerticesComplIso e)).mpr
        (UnitDistEmbeddable.comap f.toHom f.injective unitDistEmbeddable_octahedronGraph)
    · obtain ⟨e⟩ := h
      exact (hK33 (completeBipartiteContainedComplCycleThreePathThree.trans
        (sixVerticesComplIso e).symm.isContained)).elim

end

end SimpleGraph

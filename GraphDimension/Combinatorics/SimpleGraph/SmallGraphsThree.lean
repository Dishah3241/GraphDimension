/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The five small graphs placed in `ℝ³` by the FKS proof

The five small graphs that the Frankl–Kupavskii–Swanepoel proof at `d = 3` places in `ℝ³`
(design `2026-09-24-p9-d1-blueprint-design.md`, §1): a subdivision of `K₃,₃`, the five-rim
wheel, the octahedron `K₂,₂,₂`, the complete multipartite graph `K₁,₁,₅`, and the cone
`K₁ ∨ (K₃ ⊔ K₃)` over two triangles. Each has a decidable adjacency instance and a `@[simp]`
characteristic adjacency lemma `…_adj_iff` exposing its edges as a disjunction of vertex pairs
in the form `decide`, `simp` and `omega` use downstream.

Labels: the subdivided `K₃,₃` has parts `0, 1, 2` and `3, 4, 5`, with the edge `03` replaced
by `06` and `63`; the wheel has rim `0, 1, 2, 3, 4` and hub `5`; the octahedron has opposite
pairs `01, 23, 45`; `K₁,₁,₅` has singleton parts `0` and `1` and remaining part `2, …, 6`;
the cone has triangles `012` and `345` and hub `6`.
-/

@[expose] public section

namespace SimpleGraph

/-- The subdivision of `K₃,₃`: parts `0, 1, 2` and `3, 4, 5`, with the edge `03` replaced by
the two edges `06` and `63` through the new vertex `6`. -/
def subdividedCompleteBipartiteGraphThreeThree : SimpleGraph (Fin 7) :=
  fromEdgeSet {
    s(0,4), s(0,5), s(1,3), s(1,4), s(1,5),
    s(2,3), s(2,4), s(2,5), s(0,6), s(3,6)
  }

instance : DecidableRel subdividedCompleteBipartiteGraphThreeThree.Adj := by
  unfold subdividedCompleteBipartiteGraphThreeThree
  infer_instance

/-- Characteristic adjacency of the subdivided `K₃,₃`: the nine cross edges of `K₃,₃` for
parts `0, 1, 2` and `3, 4, 5`, with `03` replaced by `06` and `63`. -/
@[simp] lemma subdividedCompleteBipartiteGraphThreeThree_adj_iff (i j : Fin 7) :
    subdividedCompleteBipartiteGraphThreeThree.Adj i j ↔
      ((i = 0 ∧ j = 4 ∨ i = 4 ∧ j = 0) ∨
        (i = 0 ∧ j = 5 ∨ i = 5 ∧ j = 0) ∨
        (i = 1 ∧ j = 3 ∨ i = 3 ∧ j = 1) ∨
        (i = 1 ∧ j = 4 ∨ i = 4 ∧ j = 1) ∨
        (i = 1 ∧ j = 5 ∨ i = 5 ∧ j = 1) ∨
        (i = 2 ∧ j = 3 ∨ i = 3 ∧ j = 2) ∨
        (i = 2 ∧ j = 4 ∨ i = 4 ∧ j = 2) ∨
        (i = 2 ∧ j = 5 ∨ i = 5 ∧ j = 2) ∨
        (i = 0 ∧ j = 6 ∨ i = 6 ∧ j = 0) ∨
        (i = 3 ∧ j = 6 ∨ i = 6 ∧ j = 3)) ∧ i ≠ j := by
  simp only [subdividedCompleteBipartiteGraphThreeThree, fromEdgeSet_adj, Set.mem_insert_iff,
    Set.mem_singleton_iff, Sym2.eq_iff]

/-- The wheel with five-rim `0, 1, 2, 3, 4` and hub `5`. -/
def wheelGraphFive : SimpleGraph (Fin 6) :=
  fromEdgeSet {
    s(0,1), s(1,2), s(2,3), s(3,4), s(0,4),
    s(0,5), s(1,5), s(2,5), s(3,5), s(4,5)
  }

instance : DecidableRel wheelGraphFive.Adj := by
  unfold wheelGraphFive
  infer_instance

/-- Characteristic adjacency of the five-rim wheel: the rim cycle `0—1—2—3—4—0` and the hub
`5` joined to every rim vertex. -/
@[simp] lemma wheelGraphFive_adj_iff (i j : Fin 6) :
    wheelGraphFive.Adj i j ↔
      ((i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0) ∨
        (i = 1 ∧ j = 2 ∨ i = 2 ∧ j = 1) ∨
        (i = 2 ∧ j = 3 ∨ i = 3 ∧ j = 2) ∨
        (i = 3 ∧ j = 4 ∨ i = 4 ∧ j = 3) ∨
        (i = 0 ∧ j = 4 ∨ i = 4 ∧ j = 0) ∨
        (i = 0 ∧ j = 5 ∨ i = 5 ∧ j = 0) ∨
        (i = 1 ∧ j = 5 ∨ i = 5 ∧ j = 1) ∨
        (i = 2 ∧ j = 5 ∨ i = 5 ∧ j = 2) ∨
        (i = 3 ∧ j = 5 ∨ i = 5 ∧ j = 3) ∨
        (i = 4 ∧ j = 5 ∨ i = 5 ∧ j = 4)) ∧ i ≠ j := by
  simp only [wheelGraphFive, fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff,
    Sym2.eq_iff]

/-- The octahedron `K₂,₂,₂` on `Fin 6`: the opposite pairs are `01`, `23` and `45`. -/
def octahedronGraph : SimpleGraph (Fin 6) :=
  fromRel (fun i j => i.val / 2 ≠ j.val / 2)

instance : DecidableRel octahedronGraph.Adj := by
  unfold octahedronGraph
  infer_instance

/-- Characteristic adjacency of the octahedron: two vertices are adjacent iff they do not
lie in the same opposite pair `{0, 1}`, `{2, 3}`, `{4, 5}`. -/
@[simp] lemma octahedronGraph_adj_iff (i j : Fin 6) :
    octahedronGraph.Adj i j ↔ i.val / 2 ≠ j.val / 2 := by
  simp only [octahedronGraph, fromRel_adj, ne_eq]
  omega

/-- The complete multipartite graph `K₁,₁,₅`: singleton parts `0` and `1` and remaining part
`2, …, 6`. -/
def completeMultipartiteGraphOneOneFive : SimpleGraph (Fin 7) :=
  fromRel (fun i j => i.val < 2 ∨ j.val < 2)

instance : DecidableRel completeMultipartiteGraphOneOneFive.Adj := by
  unfold completeMultipartiteGraphOneOneFive
  infer_instance

/-- Characteristic adjacency of `K₁,₁,₅`: a vertex of part `{0} ∪ {1}` meets every vertex
except itself, and the part `2, …, 6` is independent. -/
@[simp] lemma completeMultipartiteGraphOneOneFive_adj_iff (i j : Fin 7) :
    completeMultipartiteGraphOneOneFive.Adj i j ↔ i ≠ j ∧ (i.val < 2 ∨ j.val < 2) := by
  simp only [completeMultipartiteGraphOneOneFive, fromRel_adj, ne_eq]
  omega

/-- The cone `K₁ ∨ (K₃ ⊔ K₃)` over two triangles: triangles `012` and `345` with universal
hub `6`. -/
def coneTwoTrianglesGraph : SimpleGraph (Fin 7) :=
  fromRel (fun i j => i = 6 ∨ j = 6 ∨ i.val / 3 = j.val / 3)

instance : DecidableRel coneTwoTrianglesGraph.Adj := by
  unfold coneTwoTrianglesGraph
  infer_instance

/-- Characteristic adjacency of the cone over two triangles: the hub `6` meets every vertex
except itself, and the triangles `012` and `345` are joined only inside themselves. -/
@[simp] lemma coneTwoTrianglesGraph_adj_iff (i j : Fin 7) :
    coneTwoTrianglesGraph.Adj i j ↔ i ≠ j ∧ (i = 6 ∨ j = 6 ∨ i.val / 3 = j.val / 3) := by
  simp only [coneTwoTrianglesGraph, fromRel_adj, ne_eq]
  omega

end SimpleGraph

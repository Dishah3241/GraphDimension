/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Combinatorics.SimpleGraph.SmallGraphsThree
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Set.Card

import Mathlib.Tactic.FinCases

/-!
# Sanity checks for the five small `ℝ³` graphs

The design's kernel-checked checks for the graphs of
`GraphDimension.Combinatorics.SimpleGraph.SmallGraphsThree`: their edge counts, one present
and one absent edge each, and the property that separates each graph from its degenerate
look-alike — in the subdivided `K₃,₃` both subdivision edges `06` and `63` are present while
`03` is absent; the wheel's hub `5` is adjacent to everything while `02` is absent; the
octahedron is `4`-regular, `01` is absent and `02` is present; in `K₁,₁,₅` the edges `01` and
`02` are present while `23` is absent; in the cone the hub `6` is universal and `03` is
absent.
-/

@[expose] public section

namespace SimpleGraph

/-! ### The subdivided `K₃,₃` -/

/-- The subdivided `K₃,₃` has ten edges. -/
theorem card_edgeSet_subdividedCompleteBipartiteGraphThreeThree :
    subdividedCompleteBipartiteGraphThreeThree.edgeSet.ncard = 10 := by
  rw [Set.ncard_eq_toFinset_card']
  decide

/-- The subdivision edge `06` is present. -/
theorem subdividedCompleteBipartiteGraphThreeThree_adj_zero_six :
    subdividedCompleteBipartiteGraphThreeThree.Adj 0 6 := by
  rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]
  decide

/-- The subdivision edge `36` is present: the new vertex `6` meets both `0` and `3`, so this
is a subdivision of `K₃,₃`, not `K₃,₃` with a pendant vertex. -/
theorem subdividedCompleteBipartiteGraphThreeThree_adj_three_six :
    subdividedCompleteBipartiteGraphThreeThree.Adj 3 6 := by
  rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]
  decide

/-- The subdivided edge `03` is absent. -/
theorem subdividedCompleteBipartiteGraphThreeThree_not_adj_zero_three :
    ¬ subdividedCompleteBipartiteGraphThreeThree.Adj 0 3 := by
  rw [subdividedCompleteBipartiteGraphThreeThree_adj_iff]
  decide

/-! ### The five-rim wheel -/

/-- The five-rim wheel has ten edges. -/
theorem card_edgeSet_wheelGraphFive :
    wheelGraphFive.edgeSet.ncard = 10 := by
  rw [Set.ncard_eq_toFinset_card']
  decide

/-- The hub `5` is adjacent to every other vertex. -/
theorem wheelGraphFive_hub_adj (j : Fin 6) (hj : j ≠ 5) :
    wheelGraphFive.Adj 5 j := by
  rw [wheelGraphFive_adj_iff]
  fin_cases j
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact absurd rfl hj

/-- The rim edge `01` is present. -/
theorem wheelGraphFive_adj_zero_one :
    wheelGraphFive.Adj 0 1 := by
  rw [wheelGraphFive_adj_iff]
  decide

/-- The skip-one chord `02` is absent. -/
theorem wheelGraphFive_not_adj_zero_two :
    ¬ wheelGraphFive.Adj 0 2 := by
  rw [wheelGraphFive_adj_iff]
  decide

/-! ### The octahedron -/

/-- The octahedron has twelve edges. -/
theorem card_edgeSet_octahedronGraph :
    octahedronGraph.edgeSet.ncard = 12 := by
  rw [Set.ncard_eq_toFinset_card']
  decide

/-- The octahedron is `4`-regular: this is the octahedron, not `K₆`. -/
theorem octahedronGraph_isRegularOfDegree_four :
    octahedronGraph.IsRegularOfDegree 4 := by
  intro v
  fin_cases v <;> decide

/-- The edge `02` is present. -/
theorem octahedronGraph_adj_zero_two :
    octahedronGraph.Adj 0 2 := by
  rw [octahedronGraph_adj_iff]
  decide

/-- The opposite pair `01` is a nonedge. -/
theorem octahedronGraph_not_adj_zero_one :
    ¬ octahedronGraph.Adj 0 1 := by
  rw [octahedronGraph_adj_iff]
  decide

/-! ### `K₁,₁,₅` -/

/-- `K₁,₁,₅` has eleven edges. -/
theorem card_edgeSet_completeMultipartiteGraphOneOneFive :
    completeMultipartiteGraphOneOneFive.edgeSet.ncard = 11 := by
  rw [Set.ncard_eq_toFinset_card']
  decide

/-- The edge `01` between the two singleton parts is present. -/
theorem completeMultipartiteGraphOneOneFive_adj_zero_one :
    completeMultipartiteGraphOneOneFive.Adj 0 1 := by
  rw [completeMultipartiteGraphOneOneFive_adj_iff]
  decide

/-- The edge `02` is present: this is `K₁,₁,₅`, not `K₂,₅`. -/
theorem completeMultipartiteGraphOneOneFive_adj_zero_two :
    completeMultipartiteGraphOneOneFive.Adj 0 2 := by
  rw [completeMultipartiteGraphOneOneFive_adj_iff]
  decide

/-- The edge `23` inside the large part is absent. -/
theorem completeMultipartiteGraphOneOneFive_not_adj_two_three :
    ¬ completeMultipartiteGraphOneOneFive.Adj 2 3 := by
  rw [completeMultipartiteGraphOneOneFive_adj_iff]
  decide

/-! ### The cone over two triangles -/

/-- The cone over two triangles has twelve edges. -/
theorem card_edgeSet_coneTwoTrianglesGraph :
    coneTwoTrianglesGraph.edgeSet.ncard = 12 := by
  rw [Set.ncard_eq_toFinset_card']
  decide

/-- The hub `6` is adjacent to every other vertex. -/
theorem coneTwoTrianglesGraph_hub_adj (j : Fin 7) (hj : j ≠ 6) :
    coneTwoTrianglesGraph.Adj 6 j := by
  rw [coneTwoTrianglesGraph_adj_iff]
  fin_cases j
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact absurd rfl hj

/-- The triangle edge `01` is present. -/
theorem coneTwoTrianglesGraph_adj_zero_one :
    coneTwoTrianglesGraph.Adj 0 1 := by
  rw [coneTwoTrianglesGraph_adj_iff]
  decide

/-- The triangle edge `34` is present. -/
theorem coneTwoTrianglesGraph_adj_three_four :
    coneTwoTrianglesGraph.Adj 3 4 := by
  rw [coneTwoTrianglesGraph_adj_iff]
  decide

/-- The cross edge `03` between the two triangles is absent. -/
theorem coneTwoTrianglesGraph_not_adj_zero_three :
    ¬ coneTwoTrianglesGraph.Adj 0 3 := by
  rw [coneTwoTrianglesGraph_adj_iff]
  decide

end SimpleGraph

# GraphDimension status

One row per lemma in `docs/design/graph-dimension-library.md` §3. A name is the library
declaration. "not yet" means that row has no declaration in this library.

| Lemma | Declaration |
|---|---|
| `UnitDistEmbeddable.mono` | `SimpleGraph.UnitDistEmbeddable.mono` |
| `UnitDistEmbeddable.comap` / `of_le` / `of_embedding` / `of_iso` | `SimpleGraph.UnitDistEmbeddable.comap`, `.of_le`, `.of_embedding`, `.of_iso` |
| `dim_le_of_le_compl` | `SimpleGraph.dim_le_of_le_compl`, and `UnitDistEmbeddable.of_le_compl` |
| `UnitDistEmbeddable.extend` | `SimpleGraph.UnitDistEmbeddable.extend`: the neighbours of `u` form a clique of size `k` in `G`, with `k + 1 ≤ d`. Chaffee–Noble first add the missing neighbour edges; apply `extend` to that supergraph and restrict with `of_le`. The ℝ³ degree-two case `extend_degree_le_two_fin_three` stays |
| `infinite_sphere_inter_of_regular_simplex` | `EuclideanGeometry.infinite_sphere_inter_of_regular_simplex` (`k + 1 ≤ d` points) |
| `card_le_of_equilateral` | `EuclideanGeometry.card_le_of_equilateral` (geometry, not graphs, so outside `SimpleGraph`) |
| `hasUnitDistDim_completeGraph` | `SimpleGraph.hasUnitDistDim_completeGraph` (every `n`), `unitDistEmbeddable_completeGraph` |
| `hasUnitDistDim_completeGraph_deleteEdge` | `SimpleGraph.hasUnitDistDim_completeGraph_deleteEdge` (`n ≥ 3`, `u ≠ v`); the `n = 5` placement `unitDistEmbeddable_completeGraph_five_deleteEdge` stays |
| `hasUnitDistDim_completeBipartite` | `SimpleGraph.hasUnitDistDim_completeBipartiteGraph_three_three` (`K₃,₃`); the statement for `m, n ≥ 3` is not yet |
| `hasUnitDistDim_K133` | `SimpleGraph.hasUnitDistDim_K133`: no placement in `ℝ⁴` (orthogonal-complement count), explicit placement in `ℝ⁵` |
| `hasUnitDistDim_cocktail` | `SimpleGraph.hasUnitDistDim_completeMultipartiteGraph_one_two_two_two`, `..._two_two_two_two` (lower bound via a `K₃,₃` homomorphism) |
| `regular_two_classification` | six vertices: `SimpleGraph.isRegularOfDegree_two_fin_six`. Seven vertices, in the form Theorem 10 uses: `exists_three_pairwise_disjoint_edges` and `..._compl` (through Mathlib's `IsCycles`) |
| `hasUnitDistDim_completeMultipartite` | not yet |
| `SphereEmbeddable` | `SimpleGraph.SphereEmbeddable` (`Sphere/Basic.lean`); examples `Examples/Sphere.lean`: `Kₙ` on the sphere of `ℝⁿ`, `K₃` in `ℝ²` but not on its sphere |
| `SphereEmbeddable.iff_orthogonal` | `SimpleGraph.SphereEmbeddable.iff_orthogonal`; also `.mono`, `.comap`, `.of_le`, `.of_iso` |
| `SphereEmbeddable.toUnitDist` | `SimpleGraph.SphereEmbeddable.toUnitDist` |
| `SphereEmbeddable.extend` | `SimpleGraph.SphereEmbeddable.extend` (FKS Lemma 11: at most `d − 2` neighbours), `.extend_insert` (`Sphere/Extend.lean`) |
| `SphereEmbeddable.of_degenerate` | `SimpleGraph.SphereEmbeddable.of_degenerate` (FKS Cor. 12), with `.exists_core` and `.exists_core_subset` (a spherical placement of the core extends to `G`, or to `t ⊇ c`) |
| `SphereEmbeddable.of_compl_matching` | `SimpleGraph.SphereEmbeddable.of_compl_matching` (FKS Lemma 13 for any `k ≤ d`, `card V ≤ d + k`: the repaired Lemma M), `Sphere/CrossPolytope.lean`; examples `Examples/CrossPolytope.lean`: the octahedron on `𝕊²`, `K₄` not |
| `not_embeddable_complete` | not yet |
| `exists_partition_maxDegree_le` (Lovász 1966, FKS Lemma 5) | `SimpleGraph.exists_partition_degree_le` (neighbour counts in each part) and `SimpleGraph.exists_partition_maxDegree_le` (induced maximum degree); two parts only |
| `SphereEmbeddable.of_maxDegree_le` (FKS Proposition 2) | **`SimpleGraph.SphereEmbeddable.of_degree_le`** (`2 ≤ d`, every degree `+ 1 ≤ d`) and the base `of_degree_le_three` (`Sphere/DegreeTwoDisconnected.lean`), built from `of_degree_le_two`, `of_degree_le_ge_four`, the cycle placements in `Sphere/Cycles.lean` and the reduction in `Sphere/DegreeTwo.lean` |
| `SphereEmbeddable.orthogonalSum` | `SimpleGraph.SphereEmbeddable.orthogonalSum` (`Sphere/OrthogonalSum.lean`) |
| `SphereEmbeddable.pole` | `SimpleGraph.SphereEmbeddable.pole` (one vertex, any neighbours) and `.poles` (two distinct non-adjacent vertices) (`Sphere/Poles.lean`) |
| `coreDelete`, the `(d − 1)`-core | `SimpleGraph.exists_core` (re-attachment principle: a core `c` whose vertices have more than `k` neighbours in `c`, and `P c → P univ` for any `P` closed under adding a vertex with at most `k` placed neighbours), `exists_core_subset`, `induce_edgeFinset_card_le`, `exists_core_of_degenerate`; example `Examples/K4Pendant.lean` |
| `UnitDistEmbeddable.extend_tail`, `t ≤ 2` (rung 3) | `SimpleGraph.UnitDistEmbeddable.extend_tail` (`3 ≤ d`, placed pairs `< 2` apart, at most two edges leave `s`); `t = 3` (Lemma T) not yet |
| `unitDistEmbeddable_three_of_card_edges_le_eight` (`g(3) = 8`) | not yet; seed is Erdos1007 `Geometry/EightEdges.lean` |
| The induction's statement | `SimpleGraph.FKSStatement k` (`S(k)`), with `completeMinusTriangle` (`K_n − K₃`) and `fksBudget` (`g`), `Extremal/FKS/Defs.lean`; examples `Examples/FKSDefs.lean` |
| `S(2)` (both halves) | `SimpleGraph.fksStatement_two` (`Extremal/FKS/Base.lean`). `S(3)` needs no separate base: FKS's step runs from `d = 3` |
| FKS Thm 3, edge counts (blueprint `lem:branch-A`, `lem:branch-B`, `lem:case1`, `lem:case2-count`) | `Extremal/FKS/Counting.lean`: `card_edgeSet_ge_of_copy_add_vertex`, `card_edgeSet_ge_of_two_outside_clique`, `completeMinusTriangle_isContained_of_one_outside_clique`, `card_edgeSet_ge_of_cliques_small_inter`, `card_edgeSet_ge_of_cliques_inter_pred`, `card_edgeSet_ge_of_copy_two_external`; example `Examples/FKSCounting.lean` |
| FKS Thm 3, Case 2 equality configuration (blueprint `lem:case2-place`) | `SimpleGraph.SphereEmbeddable.of_case_two` (every `d ≥ 3`), `Extremal/FKS/CaseTwo.lean` |
| `unitDistEmbeddable_of_card_edges_lt` | `d = 4` only: `SimpleGraph.unitDistEmbeddable_four_of_ncard_edgeSet_le` (CN Theorem 10, at most 14 edges). General `d` is rung 3 |
| Case B's point off the sphere (blueprint `lem:basis-apex`) | `EuclideanGeometry.exists_unit_dist_of_orthogonal_basis`, `…_std_orthonormal_basis` (`Geometry/BasisApex.lean`) |
| `unitDistEmbeddable_twoSimplices` (Lemma S) | `SimpleGraph.exists_twoSimplices_placement` (`1 < d`; apex distance `√(2 + 2/d) < 2`) |
| `infinite_common_unit_sphere_two_apices` (Lemma R, repaired; A36) | `EuclideanGeometry.infinite_common_unit_sphere_two_apices` (`Geometry/TwoApices.lean`; `d ≥ 4`) |
| `UnitDistEmbeddable.extend_tail` (Lemma T) | not yet |
| `UnitDistEmbeddable.extend_simplex` (Lemma P) | not yet |
| `unitDistEmbeddable_of_card_edges_eq` (rung 4) | not yet; statement not frozen |
| bridge to Mathlib | `SimpleGraph.unitDistEmbeddable_iff_nonempty_unitDistEmbedding`: `UnitDistEmbeddable n` iff Mathlib's `UnitDistEmbedding` into `EuclideanSpace ℝ (Fin n)` is nonempty |

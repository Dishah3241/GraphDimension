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
| `UnitDistEmbeddable.extend_tail`, `t ≤ 2` (rung 3) | `SimpleGraph.UnitDistEmbeddable.extend_tail` (`3 ≤ d`, placed pairs `< 2` apart, at most two edges leave `s`); `t ≤ 3` (Lemma T, rung 4): `SimpleGraph.UnitDistEmbeddable.extend_tail_three` (`4 ≤ d`, every placed triple has an infinite common unit sphere) and `infinite_common_unit_sphere_twoSimplices`, `Geometry/TailThree.lean` |
| `unitDistEmbeddable_three_of_card_edges_le_eight` (`g(3) = 8`) | **`SimpleGraph.unitDistEmbeddable_three_of_ncard_edgeSet_le`** (at most 8 edges, `[Finite V]`), `Extremal/EightEdges.lean`, ported from Erdos1007 with `FiveVertices.lean` (`nine_edges_iso_deleteEdge`) and `SixVertices.lean` (`nine_edges_six_minDegree_three`) |
| Nine edges in `ℝ³` (House 2013; Chaffee–Noble Thm 7; ROADMAP P9) | `SimpleGraph.completeBipartiteGraph_three_three_isContained_of_not_unitDistEmbeddable_three` (at most 9 edges, no placement → `K₃,₃ ⊑ G`) and `nonempty_iso_completeBipartiteGraph_three_three_of_not_unitDistEmbeddable_three` (exactly 9 edges, no isolated vertex → `G ≃g K₃,₃`), `Extremal/NineEdges.lean` |
| P9's small graphs for `d = 3` | `SimpleGraph.subdividedCompleteBipartiteGraphThreeThree`, `wheelGraphFive`, `octahedronGraph`, `completeMultipartiteGraphOneOneFive`, `coneTwoTrianglesGraph`, with `@[simp]` `…_adj_iff` (`Combinatorics/SimpleGraph/SmallGraphsThree.lean`); examples `Examples/SmallGraphsThree.lean` |
| Complementary edge count on 7 vertices (P9 T3) | `SimpleGraph.edgeSet_ncard_add_compl_fin_seven` (`Combinatorics/SimpleGraph/SevenVerticesComplement.lean`) |
| Complement classification, 6 vertices and 10 edges (P9 C1) | `SimpleGraph.compl_classification_fin_six_of_ten_edges` (minimum degree 3 → `Gᶜ` is `C₅ ⊔ K₁`, `P₆`, `C₄ ⊔ P₂` or `C₃ ⊔ P₃`) and the standalone `classification_fin_six_of_five_edges`, `Combinatorics/SimpleGraph/SixVerticesTenEdges.lean` (kernel-checked certificate over all graphs on `Fin 6`) |
| Degree-2 completion creating `K₃,₃` (P9 C3) | `SimpleGraph.nonempty_iso_subdividedCompleteBipartiteGraph_of_completion` (`Combinatorics/SimpleGraph/SubdividedCompleteBipartite.lean`) |
| Complement containment on 7 vertices (P9 T1, T2) | `SimpleGraph.compl_isContained_completeMultipartiteGraph_one_one_five` (`K₅ ⊑ G`), `compl_isContained_coneTwoTrianglesGraph` (`K₃,₃ ⊑ G`), `Combinatorics/SimpleGraph/SevenVerticesContainment.lean` |
| P9 placements in `ℝ³` (P1–P6) | `SimpleGraph.unitDistEmbeddable_subdividedCompleteBipartiteGraph_three_three` (`Geometry/SubdividedCompleteBipartite.lean`), `unitDistEmbeddable_wheelGraph_five` (`Geometry/Wheel.lean`), `unitDistEmbeddable_compl_pathGraph_six` (`Geometry/PathComplement.lean`), `unitDistEmbeddable_octahedronGraph` (`Geometry/Octahedron.lean`), `unitDistEmbeddable_completeMultipartiteGraph_one_one_five` (`Geometry/CompleteMultipartiteOneOneFive.lean`), `unitDistEmbeddable_coneTwoTrianglesGraph` (`Geometry/ConeTwoTriangles.lean`) |
| Triangular prism in the plane (P9 P7) | `SimpleGraph.unitDistEmbeddable_compl_cycleGraph_six` (`(C₆)ᶜ` in `ℝ²`), `Geometry/Prism.lean` |
| At most five vertices, no `K₅` (P9 C2) | `SimpleGraph.isContained_completeGraph_five_deleteEdge_of_card_le_five` (`Combinatorics/SimpleGraph/FiveVerticesContainment.lean`) |
| Degree-2 reduction, ≤ 7 vertices and ≤ 10 edges (P9 C4) | `SimpleGraph.unitDistEmbeddable_three_of_degree_eq_two` (`Extremal/TenEdges/DegreeTwo.lean`) |
| Six vertices, minimum degree 3 (P9 C5) | `SimpleGraph.unitDistEmbeddable_three_fin_six_of_minDegree_ge_three` (`Extremal/TenEdges/SixVertices.lean`) |
| Ten-edge lemma (P9 E) | **`SimpleGraph.unitDistEmbeddable_three_of_ncard_edgeSet_le_ten`** (≤ 7 vertices, ≤ 10 edges, no `K₅`, no `K₃,₃`), `Extremal/TenEdges.lean` |
| The induction's statement | `SimpleGraph.FKSStatement k` (`S(k)`), with `completeMinusTriangle` (`K_n − K₃`) and `fksBudget` (`g`), `Extremal/FKS/Defs.lean`; examples `Examples/FKSDefs.lean` |
| `S(2)` (both halves) | `SimpleGraph.fksStatement_two` (`Extremal/FKS/Base.lean`). `S(3)` needs no separate base: FKS's step runs from `d = 3` |
| FKS Thm 3, edge counts (blueprint `lem:branch-A`, `lem:branch-B`, `lem:case1`, `lem:case2-count`) | `Extremal/FKS/Counting.lean`: `card_edgeSet_ge_of_copy_add_vertex`, `card_edgeSet_ge_of_two_outside_clique`, `completeMinusTriangle_isContained_of_one_outside_clique`, `card_edgeSet_ge_of_cliques_small_inter`, `card_edgeSet_ge_of_cliques_inter_pred`, `card_edgeSet_ge_of_copy_two_external`; example `Examples/FKSCounting.lean` |
| FKS Thm 3, Case 2 equality configuration (blueprint `lem:case2-place`) | `SimpleGraph.SphereEmbeddable.of_case_two` (every `d ≥ 3`), `Extremal/FKS/CaseTwo.lean` |
| FKS Thm 3, the step's branches (`Extremal/FKS/`) | budget facts (`Budget.lean`); deletion counts (`Deletion.lean`); maximal core (`CoreAssembly.lean`: `exists_core_maximal`, `SphereEmbeddable.of_core_maximal`); Branch A (`UnitDistEmbeddable.of_core_completeMinusTriangle`); Branch B (`UnitDistEmbeddable.of_core_clique`, `.of_core_containing_clique`); small cores (`SphereEmbeddable.of_fks_small_core`); Branch C (`SphereEmbeddable.of_fks_pole`, `.of_fks_poles`); Case 1 excluded (`not_forall_clique_of_edgeSet_ncard_lt`, `exists_cliqueFree_pair_of_edgeSet_ncard_lt`); Case 2 count (`fks_case_two_degrees`); counterexample to FKS's Case 2 deduction at `d = 3` (`exists_fks_case_two_extra_vertex`, Math finding A38). the Case 2 bridge with the A38 repair (`CaseTwoBridge.lean`); the step `fksStatement_succ` (`Step.lean`) |
| `unitDistEmbeddable_of_card_edges_lt` | **`SimpleGraph.unitDistEmbeddable_of_ncard_edgeSet_lt`** (FKS 2020 Theorem 3: `d ≥ 4`, fewer than `C(d + 2, 2)` edges, `V : Type`), from `SimpleGraph.fksStatement` (`S(d)` for every `d ≥ 2`), `Extremal/FKS/Theorem3.lean`. The `d = 4` case also has CN Theorem 10: `unitDistEmbeddable_four_of_ncard_edgeSet_le` |
| Case B's point off the sphere (blueprint `lem:basis-apex`) | `EuclideanGeometry.exists_unit_dist_of_orthogonal_basis`, `…_std_orthonormal_basis` (`Geometry/BasisApex.lean`) |
| `unitDistEmbeddable_twoSimplices` (Lemma S) | `SimpleGraph.exists_twoSimplices_placement` (`1 < d`; apex distance `√(2 + 2/d) < 2`) |
| `infinite_common_unit_sphere_two_apices` (Lemma R, repaired; A36) | `EuclideanGeometry.infinite_common_unit_sphere_two_apices` (`Geometry/TwoApices.lean`; `d ≥ 4`) |
| `UnitDistEmbeddable.extend_tail` (Lemma T) | see the `t ≤ 2` row: `extend_tail_three` |
| `UnitDistEmbeddable.extend_simplex` (Lemma P) | `SimpleGraph.UnitDistEmbeddable.extend_of_clique_neighbors` (`Geometry/ExtendClique.lean`): clique neighbourhoods of size at most `d − 1`, overlaps allowed, no non-adjacency needed |
| `unitDistEmbeddable_of_card_edges_eq` (rung 4) | **`SimpleGraph.nonempty_iso_completeGraph_of_not_unitDistEmbeddable`** (`d ≥ 6`, `C(d + 2, 2)` edges, no isolated vertex, no placement in `ℝᵈ` → `G ≃g K_{d+2}`), `Extremal/FKS/Uniqueness.lean`, with the equality-budget branches in `EqualityBranches.lean`. Statement as the owner chose it; frozen by the owner's Compass sign-off on 2026-09-24 (EdgeThresholdUniqueness `docs/compass.md`) |
| bridge to Mathlib | `SimpleGraph.unitDistEmbeddable_iff_nonempty_unitDistEmbedding`: `UnitDistEmbeddable n` iff Mathlib's `UnitDistEmbedding` into `EuclideanSpace ℝ (Fin n)` is nonempty |

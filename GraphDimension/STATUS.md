# GraphDimension status

One row per lemma in `docs/design/graph-dimension-library.md` §3. A name is the library
declaration. "not yet" means that row has no declaration in this library.

| Lemma | Declaration |
|---|---|
| `UnitDistEmbeddable.mono` | `SimpleGraph.UnitDistEmbeddable.mono` |
| `UnitDistEmbeddable.comap` / `of_le` / `of_embedding` / `of_iso` | `SimpleGraph.UnitDistEmbeddable.comap`, `.of_le`, `.of_embedding`, `.of_iso` |
| `dim_le_of_le_compl` | `SimpleGraph.dim_le_of_le_compl`, and `UnitDistEmbeddable.of_le_compl` |
| `UnitDistEmbeddable.extend` | `SimpleGraph.UnitDistEmbeddable.extend_degree_le_two_fin_three` (degree at most 2 in `ℝ³`); the general statement is not yet |
| `infinite_sphere_inter_of_regular_simplex` | not yet |
| `card_le_of_equilateral` | not yet |
| `hasDimension_completeGraph` | not yet |
| `hasDimension_completeGraph_deleteEdge` | `SimpleGraph.unitDistEmbeddable_completeGraph_five_deleteEdge` (`n = 5` upper bound); the dimension statement is not yet |
| `hasDimension_completeBipartite` | `SimpleGraph.hasDimension_completeBipartiteGraph_three_three` (`K₃,₃`); the statement for `m, n ≥ 3` is not yet |
| `hasDimension_K133` | not yet |
| `hasDimension_cocktail` | not yet |
| `regular_two_classification` | `SimpleGraph.isRegularOfDegree_two_fin_six` (six vertices). For seven vertices, use Mathlib's `SimpleGraph.IsCycles` (`IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp`) rather than a new leaf |
| `hasDimension_completeMultipartite` | not yet |
| `SphereEmbeddable` | not yet |
| `SphereEmbeddable.iff_orthogonal` | not yet |
| `SphereEmbeddable.toUnitDist` | not yet |
| `SphereEmbeddable.extend` | not yet |
| `SphereEmbeddable.of_degenerate` | not yet |
| `SphereEmbeddable.of_compl_matching` | not yet |
| `not_embeddable_complete` | not yet |
| `unitDistEmbeddable_of_card_edges_lt` | not yet |
| bridge to Mathlib | `SimpleGraph.unitDistEmbeddable_iff_nonempty_unitDistEmbedding`: `UnitDistEmbeddable n` iff Mathlib's `UnitDistEmbedding` into `EuclideanSpace ℝ (Fin n)` is nonempty |

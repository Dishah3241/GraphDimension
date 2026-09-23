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
| `hasDimension_completeGraph` | `SimpleGraph.hasDimension_completeGraph` (every `n`), `unitDistEmbeddable_completeGraph` |
| `hasDimension_completeGraph_deleteEdge` | `SimpleGraph.hasDimension_completeGraph_deleteEdge` (`n ≥ 3`, `u ≠ v`); the `n = 5` placement `unitDistEmbeddable_completeGraph_five_deleteEdge` stays |
| `hasDimension_completeBipartite` | `SimpleGraph.hasDimension_completeBipartiteGraph_three_three` (`K₃,₃`); the statement for `m, n ≥ 3` is not yet |
| `hasDimension_K133` | `SimpleGraph.hasDimension_K133`: no placement in `ℝ⁴` (orthogonal-complement count), explicit placement in `ℝ⁵` |
| `hasDimension_cocktail` | `SimpleGraph.hasDimension_completeMultipartiteGraph_one_two_two_two`, `..._two_two_two_two` (lower bound via a `K₃,₃` homomorphism) |
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

/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Unit-distance representations pull back along injective homomorphisms

A unit-distance representation of a graph in `ℝⁿ` is an injective placement of its vertices in
which every edge is a segment of length one. Precomposing such a placement with an injective graph
homomorphism represents the domain graph. The same conclusion for a spanning subgraph `H ≤ G`,
and for a graph embedding `H ↪g G`, follows at once.

A representation of `G` in `ℝⁿ` yields one of any graph mapped injectively into `G`, so dimension
is monotone under injective homomorphisms and under taking subgraphs.

## References

Chaffee and Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J.
Combin. **64(2)** (2016), 327–333, Lemma 4, attributed there to Erdős, Harary and Tutte, *On the
dimension of a graph*, Mathematika **12** (1965), 118–122.
-/

namespace SimpleGraph

open SimpleGraph

@[expose] public section

/-- A unit-distance representation of `G` in `ℝⁿ` pulls back along an injective homomorphism
`φ : H →g G`.

The placement of `H` is the placement of `G` precomposed with `φ`. Injectivity of both maps keeps
the placement injective, and `φ` sends edges of `H` to edges of `G`. Chaffee–Noble Lemma 4,
attributed there to Erdős–Harary–Tutte. -/
theorem UnitDistEmbeddable.comap {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ}
    (φ : H →g G) (hφ : Function.Injective φ) (hG : G.UnitDistEmbeddable n) :
    H.UnitDistEmbeddable n := by
  obtain ⟨f, hfInj, hfDist⟩ := hG
  refine ⟨fun w => f (φ w), hfInj.comp hφ, ?_⟩
  intro u v huv
  exact hfDist (φ u) (φ v) (φ.map_adj huv)

/-- A unit-distance representation of `G` restricts to any spanning subgraph `H ≤ G` on the same
vertex type (Chaffee–Noble Lemma 4). -/
theorem UnitDistEmbeddable.of_le {V : Type*} {G H : SimpleGraph V} {n : ℕ} (hHG : H ≤ G)
    (hG : G.UnitDistEmbeddable n) : H.UnitDistEmbeddable n :=
  hG.comap (Hom.ofLE hHG) Function.injective_id

/-- A unit-distance representation of `G` pulls back along a graph embedding `H ↪g G`
(Chaffee–Noble Lemma 4). -/
theorem UnitDistEmbeddable.of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {n : ℕ} (φ : H ↪g G) (hG : G.UnitDistEmbeddable n) : H.UnitDistEmbeddable n :=
  hG.comap φ.toHom φ.injective

/-- Unit-distance embeddability is invariant under graph isomorphism. -/
theorem UnitDistEmbeddable.of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ}
    (e : G ≃g H) : G.UnitDistEmbeddable n ↔ H.UnitDistEmbeddable n :=
  ⟨fun h => h.of_embedding e.symm.toEmbedding, fun h => h.of_embedding e.toEmbedding⟩

end

end SimpleGraph

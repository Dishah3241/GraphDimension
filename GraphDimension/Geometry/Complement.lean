/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Basic
public import GraphDimension.Geometry.UnitDistanceComap

import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.Bounds.Basic

/-!
# Complementary graphs and unit-distance dimension

On one vertex set, the sparser graph has the smaller unit-distance dimension bound: if `Gᶜ ≤ Hᶜ`,
which on a common vertex type says exactly that `H ≤ G`, then every unit-distance representation
of `G` in `ℝⁿ` represents `H`, and the least representing dimension of `H` is at most that of
`G`.

## References

Chaffee and Noble, *Dimension 4 and dimension 5 graphs with minimum edge set*, Australas. J.
Combin. **64(2)** (2016), 327–333, Corollary 5, derived there from Lemma 4, attributed to
Erdős, Harary and Tutte, *On the dimension of a graph*, Mathematika **12** (1965), 118–122.
-/

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {m n : ℕ}

@[expose] public section

/-- Chaffee–Noble Corollary 5, as a representability implication: if `Gᶜ ≤ Hᶜ` on one vertex
type — which is to say `H ≤ G`, since complement is antitone — then a unit-distance
representation of `G` in `ℝⁿ` is one of `H`. -/
theorem UnitDistEmbeddable.of_le_compl (h : Gᶜ ≤ Hᶜ) (hG : G.UnitDistEmbeddable n) :
    H.UnitDistEmbeddable n :=
  hG.of_le (compl_le_compl_iff_le.mp h)

/-- Chaffee–Noble Corollary 5: if `Gᶜ ≤ Hᶜ` on one vertex type, then `dim H ≤ dim G`.

Stated through `HasDimension`: if `n` is the least dimension representing `G` and `m` the least
dimension representing `H`, then `m ≤ n`. -/
theorem dim_le_of_le_compl (h : Gᶜ ≤ Hᶜ) (hG : G.HasDimension n) (hH : H.HasDimension m) :
    m ≤ n :=
  IsLeast.mono hG hH fun _k hk => hk.of_le_compl h

end

end SimpleGraph

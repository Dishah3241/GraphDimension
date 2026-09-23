/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.FKS.Defs
public import Mathlib.Combinatorics.SimpleGraph.Star

import Mathlib.Tactic.FinCases

/-!
# Small cases of `Kₙ − K₃`

`completeMinusTriangle 4` is the star with centre `3` and leaves `0, 1, 2`, so FKS's forbidden
subgraph `K₄ − K₃` is `K₁,₃`. On five vertices the same construction still contains a
triangle `{0, 3, 4}`, so it is not `K₃`-free.
-/

namespace SimpleGraph

open Finset

@[expose] public section

/-- `K₄ − K₃` is the star with centre `3` joined to `0, 1, 2`. -/
theorem completeMinusTriangle_four_eq_starGraph :
    completeMinusTriangle 4 = starGraph (3 : Fin 4) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [completeMinusTriangle, starGraph_adj]

/-- The identity on `Fin 4` is a graph isomorphism onto that star. -/
def completeMinusTriangle_four_iso_starGraph :
    completeMinusTriangle 4 ≃g starGraph (3 : Fin 4) :=
  completeMinusTriangle_four_eq_starGraph ▸
    (Iso.refl : completeMinusTriangle 4 ≃g completeMinusTriangle 4)

/-- `K₅ − K₃` contains a triangle on `{0, 3, 4}`. -/
theorem not_cliqueFree_completeMinusTriangle_five :
    ¬ (completeMinusTriangle 5).CliqueFree 3 := by
  classical
  refine IsNClique.not_cliqueFree (s := {0, 3, 4}) ?_
  refine ⟨?_, by decide⟩
  intro a ha b hb hab
  rw [Finset.mem_coe, mem_insert, mem_insert, mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp_all [completeMinusTriangle]

end

end SimpleGraph

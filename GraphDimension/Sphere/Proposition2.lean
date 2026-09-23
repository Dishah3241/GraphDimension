/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Sphere.DegreeTwo
public import GraphDimension.Sphere.MaxDegree

import GraphDimension.Sphere.DegreeOne
import Mathlib.Tactic.Linarith

/-!
# Induction for FKS Proposition 2

The degree-two base and the Lovász partition step already prove the proposition in every
dimension once the degree-three base is available. This file packages that strong induction
with its missing base explicit.
-/

namespace SimpleGraph

universe u

@[expose] public section

/-- The induction in FKS Proposition 2, conditional on its degree-three base. The cases `d = 2`
and `d ≥ 4` use the established base and the Lovász partition step respectively. -/
theorem SphereEmbeddable.of_degree_le_of_three
    (hthree : ∀ {W : Type u} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (∀ w, H.degree w ≤ 2) → H.SphereEmbeddable 3)
    {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} (hd : 2 ≤ d) (h : ∀ v, G.degree v + 1 ≤ d) : G.SphereEmbeddable d := by
  suffices hs : ∀ n : ℕ, ∀ {W : Type u} [Fintype W] (H : SimpleGraph W)
      [DecidableRel H.Adj], 2 ≤ n → (∀ w, H.degree w + 1 ≤ n) → H.SphereEmbeddable n from
    hs d G hd h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ H _ hn hdeg
    by_cases htwo : n = 2
    · subst n
      exact SphereEmbeddable.of_degree_le_two (G := H) (by
        intro w
        have hw := hdeg w
        omega)
    by_cases hthree_dim : n = 3
    · subst n
      exact hthree H (by
        intro w
        have hw := hdeg w
        omega)
    have hfour : 4 ≤ n := by omega
    exact SphereEmbeddable.of_degree_le_ge_four hfour
      (fun {d'} {W'} _ H' _ hlt htwo' hdeg' => ih d' hlt H' htwo' hdeg') hdeg

/-- FKS Proposition 2 reduces entirely to spherical placements of finite two-regular graphs.
The core reduction supplies the degree-three base, and the induction then covers every `d ≥ 2`.
-/
theorem SphereEmbeddable.of_degree_le_of_regular
    (hregular : ∀ {W : Type u} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (∀ w, H.degree w = 2) → H.SphereEmbeddable 3)
    {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} (hd : 2 ≤ d) (h : ∀ v, G.degree v + 1 ≤ d) : G.SphereEmbeddable d :=
  SphereEmbeddable.of_degree_le_of_three
    (fun _ _ hdegree => SphereEmbeddable.of_degree_le_three_of_regular hregular hdegree) hd h

end

end SimpleGraph

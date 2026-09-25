/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Extremal.EightEdges
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# At most five vertices without `K₅` sit in `K₅ − e`

Leaf C2 of the FKS leaf plan (design `2026-09-24-p9-d1-blueprint-design.md`, §1): a graph on at
most five vertices that does not contain `K₅` is contained in the reference graph
`K₅ − e`, the complete graph on `Fin 5` with the edge `s(3, 4)` deleted.

On fewer than five vertices an injection into `Fin 5` below `4` cannot land an edge on the
deleted pair. On exactly five vertices a missing edge is relabelled onto the deleted pair by
`SimpleGraph.exists_equiv_sending_pair`. A complete graph on five vertices would contain `K₅`,
which the hypothesis forbids. The empty and smaller vertex types are included in the first
case.
-/

@[expose] public section

namespace SimpleGraph

/-- **C2**: a graph on at most five vertices with no copy of `K₅` is contained in `K₅ − e`
(`⊑`, an injective homomorphism, not an induced copy), the complete graph on `Fin 5` with the
edge `s(3, 4)` deleted. -/
theorem isContained_completeGraph_five_deleteEdge_of_card_le_five
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V ≤ 5)
    (hK5 : ¬ ((⊤ : SimpleGraph (Fin 5)) ⊑ G)) :
    G ⊑ ((⊤ : SimpleGraph (Fin 5)).deleteEdges {s(3, 4)}) := by
  classical
  rcases Nat.lt_or_ge (Fintype.card V) 5 with hlt | heq
  · -- Fewer than five vertices: inject `V` into `Fin 5` below `4`, so no edge can land on
    -- the deleted pair `s(3, 4)`.
    obtain ⟨f, hf4⟩ : ∃ f : V ↪ Fin 5, ∀ x : V, f x ≠ 4 := by
      refine ⟨(Fintype.equivFinOfCardEq rfl).toEmbedding.trans (Fin.castLEEmb hV), fun x => ?_⟩
      intro hcon
      have hval : (((Fintype.equivFinOfCardEq rfl).toEmbedding.trans (Fin.castLEEmb hV)) x : ℕ)
          = (Fintype.equivFinOfCardEq rfl x : ℕ) := rfl
      rw [hcon] at hval
      have hx := (Fintype.equivFinOfCardEq rfl x).isLt
      have h4 : (Fintype.equivFinOfCardEq rfl x : ℕ) = 4 := by rw [← hval]; rfl
      omega
    exact ⟨Hom.toCopy
      (show G →g (⊤ : SimpleGraph (Fin 5)).deleteEdges {s(3, 4)} from
        ⟨f, fun {x y} hxy => by
          rw [deleteEdges_adj, top_adj]
          refine ⟨f.injective.ne (G.ne_of_adj hxy), fun hs => ?_⟩
          rw [Set.mem_singleton_iff] at hs
          rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact absurd h2 (hf4 y)
          · exact absurd h1 (hf4 x)⟩)
      f.injective⟩
  · -- Exactly five vertices: if `G` were complete it would contain `K₅`.
    have heq5 : Fintype.card V = 5 := Nat.le_antisymm hV heq
    have hne : G ≠ ⊤ := by
      intro htop
      exact hK5 ⟨Hom.toCopy
        (show (⊤ : SimpleGraph (Fin 5)) →g G from
          ⟨(Fintype.equivFinOfCardEq heq5).symm, fun {a b} hab => by
            rw [top_adj] at hab
            rw [htop, top_adj]
            exact (Fintype.equivFinOfCardEq heq5).symm.injective.ne hab⟩)
        (Fintype.equivFinOfCardEq heq5).symm.injective⟩
    -- a missing edge, relabelled onto the deleted pair
    obtain ⟨u, v, huv, hnadj⟩ := ne_top_iff_exists_not_adj.mp hne
    obtain ⟨e, he3, he4⟩ := exists_equiv_sending_pair heq5 huv
    exact ⟨Hom.toCopy
      (show G →g (⊤ : SimpleGraph (Fin 5)).deleteEdges {s(3, 4)} from
        ⟨e, fun {x y} hxy => by
          rw [deleteEdges_adj, top_adj]
          refine ⟨e.injective.ne (G.ne_of_adj hxy), fun hs => ?_⟩
          rw [Set.mem_singleton_iff] at hs
          rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have hx : x = u := e.injective (h1.trans he3.symm)
            have hy : y = v := e.injective (h2.trans he4.symm)
            rw [hx, hy] at hxy
            exact hnadj hxy
          · have hx : x = v := e.injective (h1.trans he4.symm)
            have hy : y = u := e.injective (h2.trans he3.symm)
            rw [hx, hy] at hxy
            exact hnadj (G.adj_symm hxy)⟩)
      e.injective⟩

end SimpleGraph

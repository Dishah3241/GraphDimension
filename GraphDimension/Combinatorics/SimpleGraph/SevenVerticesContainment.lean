/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import GraphDimension.Combinatorics.SimpleGraph.SmallGraphsThree
public import Mathlib.Combinatorics.SimpleGraph.Copy

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Sum

/-!
# Complement containment on seven vertices from a forbidden copy

Leaves T1 and T2 of the FKS leaf plan (design `2026-09-24-p9-d1-blueprint-design.md`, §1).
If a graph `G` on seven vertices contains a `K₅`, its copy is a clique, so every edge of
`Gᶜ` touches one of the two vertices outside the copy; labelling those two vertices `0` and
`1` and the copy `2, …, 6` embeds `Gᶜ` in `K₁,₁,₅`. If `G` contains a `K₃,₃`, no edge of
`Gᶜ` joins the two sides of the copy; labelling the sides `0, 1, 2` and `3, 4, 5` and the
seventh vertex `6` embeds `Gᶜ` in the cone `K₁ ∨ (K₃ ⊔ K₃)`. Both proofs extend the vertex
injection of the forbidden copy to a labelling of all seven vertices and read adjacency
preservation off the `@[simp]` adjacency lemmas of `SmallGraphsThree`.
-/

@[expose] public section

namespace SimpleGraph

/-- **T1**: if `G` on seven vertices contains a `K₅`, then `Gᶜ` is contained in the complete
multipartite graph `K₁,₁,₅` with singleton parts `0`, `1` and remaining part `2, …, 6`. -/
theorem compl_isContained_completeMultipartiteGraph_one_one_five (G : SimpleGraph (Fin 7))
    (hK5 : (⊤ : SimpleGraph (Fin 5)) ⊑ G) :
    Gᶜ ⊑ completeMultipartiteGraphOneOneFive := by
  classical
  obtain ⟨c⟩ := hK5
  -- the five vertices of the copy of `K₅`, and the two vertices outside it
  have hcard5 : Fintype.card { a // a ∈ Finset.image c.toEmbedding Finset.univ } = 5 := by
    rw [Fintype.card_coe, Finset.card_image_of_injective _ c.toEmbedding.injective,
      Finset.card_univ, Fintype.card_fin]
  have hcard2 : Fintype.card { a // a ∉ Finset.image c.toEmbedding Finset.univ } = 2 := by
    have h := Fintype.card_subtype_compl fun a => a ∈ Finset.image c.toEmbedding Finset.univ
    rw [hcard5, Fintype.card_fin] at h
    omega
  -- a labelling of all seven vertices: the two vertices outside the copy go to `0, 1`
  obtain ⟨e, hvalC⟩ : ∃ e : Fin 7 ≃ Fin 7, ∀ a : Fin 7,
      a ∉ Finset.image c.toEmbedding Finset.univ → (e a : ℕ) < 2 := by
    refine ⟨(Equiv.sumCompl (· ∈ Finset.image c.toEmbedding Finset.univ)).symm.trans
      ((Equiv.sumCongr (Fintype.equivFinOfCardEq hcard5) (Fintype.equivFinOfCardEq hcard2)).trans
        ((Equiv.sumComm (Fin 5) (Fin 2)).trans (finSumFinEquiv (m := 2) (n := 5)))),
      ?_⟩
    intro a ha
    have key : (Equiv.sumCompl (· ∈ Finset.image c.toEmbedding Finset.univ)).symm a =
        Sum.inr ⟨a, ha⟩ := Equiv.sumCompl_symm_apply_of_neg ha
    rw [Equiv.trans_apply, key, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inr, finSumFinEquiv_apply_left,
      Fin.val_castAdd]
    omega
  refine ⟨Hom.toCopy ⟨e, fun {a b} hab => ?_⟩ e.injective⟩
  rw [compl_adj] at hab
  obtain ⟨hne, hnadj⟩ := hab
  simp only [completeMultipartiteGraphOneOneFive_adj_iff]
  refine ⟨show e a ≠ e b from fun h => hne (e.injective h), ?_⟩
  by_cases h2a : (e a : ℕ) < 2
  · exact Or.inl h2a
  by_cases h2b : (e b : ℕ) < 2
  · exact Or.inr h2b
  -- both labels lie in `2, …, 6`, so both vertices lie in the copy of `K₅`, which is a clique
  exfalso
  have haS : a ∈ Finset.image c.toEmbedding Finset.univ := by
    by_contra hcon
    exact h2a (hvalC a hcon)
  have hbS : b ∈ Finset.image c.toEmbedding Finset.univ := by
    by_contra hcon
    exact h2b (hvalC b hcon)
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp haS
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hbS
  have hxy : x ≠ y := by
    intro h
    subst h
    exact hne (hx.symm.trans hy)
  refine hnadj ?_
  have hadj : G.Adj (c.toEmbedding x) (c.toEmbedding y) :=
    c.toHom.map_adj ((top_adj x y).mpr hxy)
  rwa [hx, hy] at hadj

/-- **T2**: if `G` on seven vertices contains a `K₃,₃`, then `Gᶜ` is contained in the cone
`K₁ ∨ (K₃ ⊔ K₃)` with triangles `012`, `345` and hub `6`. -/
theorem compl_isContained_coneTwoTrianglesGraph (G : SimpleGraph (Fin 7))
    (hK33 : (completeBipartiteGraph (Fin 3) (Fin 3)) ⊑ G) :
    Gᶜ ⊑ coneTwoTrianglesGraph := by
  classical
  obtain ⟨c⟩ := hK33
  have hcard6 : Fintype.card { a // a ∈ Finset.image c.toEmbedding Finset.univ } = 6 := by
    rw [Fintype.card_coe, Finset.card_image_of_injective _ c.toEmbedding.injective,
      Finset.card_univ, Fintype.card_sum, Fintype.card_fin]
  have hcard1 : Fintype.card { a // a ∉ Finset.image c.toEmbedding Finset.univ } = 1 := by
    have h := Fintype.card_subtype_compl fun a => a ∈ Finset.image c.toEmbedding Finset.univ
    rw [hcard6, Fintype.card_fin] at h
    omega
  have hmem : ∀ a ∈ Finset.image c.toEmbedding Finset.univ,
      ∃ x : Fin 3 ⊕ Fin 3, c.toEmbedding x = a := fun a ha => by
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp ha
    exact ⟨x, hx⟩
  -- the side labelling: a copied vertex is sent to `finSumFinEquiv` of its preimage
  obtain ⟨ψf, hψ⟩ : ∃ ψf : { a // a ∈ Finset.image c.toEmbedding Finset.univ } → Fin 3 ⊕ Fin 3,
      ∀ u, c.toEmbedding (ψf u) = u.1 :=
    ⟨fun u => Classical.choose (hmem u.1 u.2), fun u => Classical.choose_spec (hmem u.1 u.2)⟩
  have hψinj : Function.Injective ψf := by
    intro u v huv
    apply Subtype.ext
    rw [← hψ u, ← hψ v, huv]
  have hψsurj : Function.Surjective ψf := by
    intro x
    refine ⟨⟨c.toEmbedding x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩, ?_⟩
    exact c.toEmbedding.injective (hψ _)
  -- a labelling of all seven vertices: the two sides of the copy go to `0, 1, 2` and
  -- `3, 4, 5`, the seventh vertex goes to `6`
  obtain ⟨e, hvalS, hvalC⟩ : ∃ e : Fin 7 ≃ Fin 7,
      (∀ a : Fin 7, a ∈ Finset.image c.toEmbedding Finset.univ → ∃ x : Fin 3 ⊕ Fin 3,
          c.toEmbedding x = a ∧ (e a : ℕ) = (finSumFinEquiv x : Fin 6).val) ∧
      (∀ a : Fin 7, a ∉ Finset.image c.toEmbedding Finset.univ → (e a : ℕ) = 6) := by
    refine ⟨(Equiv.sumCompl (· ∈ Finset.image c.toEmbedding Finset.univ)).symm.trans
      ((Equiv.sumCongr (Equiv.ofBijective ψf ⟨hψinj, hψsurj⟩)
          (Fintype.equivFinOfCardEq hcard1)).trans
        ((Equiv.sumCongr (finSumFinEquiv (m := 3) (n := 3)) (Equiv.refl (Fin 1))).trans
          (finSumFinEquiv (m := 6) (n := 1)))), ?_, ?_⟩
    · intro a ha
      obtain ⟨x, hx⟩ := hmem a ha
      refine ⟨x, hx, ?_⟩
      have hgx : Equiv.ofBijective ψf ⟨hψinj, hψsurj⟩ ⟨a, ha⟩ = x :=
        c.toEmbedding.injective ((hψ ⟨a, ha⟩).trans hx.symm)
      rw [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos ha, Equiv.trans_apply,
        Equiv.sumCongr_apply, Sum.map_inl, Equiv.trans_apply, Equiv.sumCongr_apply,
        Sum.map_inl, hgx, finSumFinEquiv_apply_left, Fin.val_castAdd]
    · intro a ha
      have key : (Equiv.sumCompl (· ∈ Finset.image c.toEmbedding Finset.univ)).symm a =
          Sum.inr ⟨a, ha⟩ := Equiv.sumCompl_symm_apply_of_neg ha
      rw [Equiv.trans_apply, key, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
        Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply,
        finSumFinEquiv_apply_right, Fin.val_natAdd]
      omega
  refine ⟨Hom.toCopy ⟨e, fun {a b} hab => ?_⟩ e.injective⟩
  rw [compl_adj] at hab
  obtain ⟨hne, hnadj⟩ := hab
  simp only [coneTwoTrianglesGraph_adj_iff]
  refine ⟨show e a ≠ e b from fun h => hne (e.injective h), ?_⟩
  by_cases haS : a ∈ Finset.image c.toEmbedding Finset.univ
  · by_cases hbS : b ∈ Finset.image c.toEmbedding Finset.univ
    · -- both vertices are copied; they lie on the same side of the `K₃,₃`, since every
      -- cross pair is an edge of `G`
      obtain ⟨x, hx, hvalx⟩ := hvalS a haS
      obtain ⟨y, hy, hvaly⟩ := hvalS b hbS
      have hxy : x ≠ y := by
        intro h
        subst h
        exact hne (hx.symm.trans hy)
      have hnot : ¬ (completeBipartiteGraph (Fin 3) (Fin 3)).Adj x y := by
        intro h
        refine hnadj ?_
        rw [← hx, ← hy]
        exact c.toHom.map_adj h
      rcases x with i | i <;> rcases y with j | j
      · rw [hvalx, hvaly]
        simp only [finSumFinEquiv_apply_left, Fin.val_castAdd]
        omega
      · exact absurd (show (completeBipartiteGraph (Fin 3) (Fin 3)).Adj (Sum.inl i) (Sum.inr j)
          from by simp) hnot
      · exact absurd (show (completeBipartiteGraph (Fin 3) (Fin 3)).Adj (Sum.inr i) (Sum.inl j)
          from by simp) hnot
      · rw [hvalx, hvaly]
        simp only [finSumFinEquiv_apply_right, Fin.val_natAdd]
        omega
    · exact Or.inr (Or.inl (Fin.val_injective (hvalC b hbS)))
  · exact Or.inl (Fin.val_injective (hvalC a haS))

end SimpleGraph

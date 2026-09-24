/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Sum

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.BitVec
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Six vertices, ten edges, minimum degree three

The complement has five edges and maximum degree at most two. We classify all such graphs
as `C₅ ⊔ K₁`, `P₆`, `C₄ ⊔ P₂`, or `C₃ ⊔ P₃`.

The finite certificate uses the fifteen upper-triangular adjacency bits in lexicographic
order: `01, 02, 03, 04, 05, 12, 13, 14, 15, 23, 24, 25, 34, 35, 45`. The encoding lemma proves
that these bits recover any graph on `Fin 6`. Six explicit sums compute its degrees.

The balanced lookup table records a target and a vertex permutation for each of the 537
admissible labeled graphs. It is obtained by relabeling the four displayed target graphs
by permutations of `Fin 6`, retaining one inverse permutation per distinct adjacency mask.
The target masks are respectively `4649`, `21025`, `16933`, and `20515`.

Thirty-two kernel `decide` checks, each on 1024 masks, verify that every admissible mask
receives a bijection preserving and reflecting adjacency. The checked coverage theorem
joins these intervals. Thus neither the construction of the table nor an external graph
classification is trusted. Each check has an explicit heartbeat and recursion bound.
-/

namespace SimpleGraph

-- Index of an unordered pair in the fifteen upper-triangular positions.
private def sixIndex (i j : Fin 6) : Nat :=
  let a := min i.val j.val
  let b := max i.val j.val
  a * (11 - a) / 2 + b - a - 1

private def sixGraph (n : Nat) : SimpleGraph (Fin 6) :=
  fromRel fun i j => n.testBit (sixIndex i j) = true

private instance (n : Nat) : DecidableRel (sixGraph n).Adj := by
  unfold sixGraph
  infer_instance

private def sixDegrees (n : Nat) : Fin 6 → Nat :=
  ![(n.testBit 0).toNat + (n.testBit 1).toNat +
      (n.testBit 2).toNat + (n.testBit 3).toNat + (n.testBit 4).toNat,
    (n.testBit 0).toNat + (n.testBit 5).toNat +
      (n.testBit 6).toNat + (n.testBit 7).toNat + (n.testBit 8).toNat,
    (n.testBit 1).toNat + (n.testBit 5).toNat +
      (n.testBit 9).toNat + (n.testBit 10).toNat + (n.testBit 11).toNat,
    (n.testBit 2).toNat + (n.testBit 6).toNat +
      (n.testBit 9).toNat + (n.testBit 12).toNat + (n.testBit 13).toNat,
    (n.testBit 3).toNat + (n.testBit 7).toNat +
      (n.testBit 10).toNat + (n.testBit 12).toNat + (n.testBit 14).toNat,
    (n.testBit 4).toNat + (n.testBit 8).toNat +
      (n.testBit 11).toNat + (n.testBit 13).toNat + (n.testBit 14).toNat]

private theorem sixDegrees_eq (n : Nat) (i : Fin 6) :
    sixDegrees n i = (sixGraph n).degree i := by
  rw [degree, neighborFinset_eq_filter]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Fin.sum_univ_succ]
  fin_cases i <;>
    simp [sixDegrees, sixGraph, sixIndex, fromRel_adj,
      Bool.toNat, Nat.add_assoc]

private def sixValid (n : Nat) : Prop :=
  (sixDegrees n 0 + sixDegrees n 1 + sixDegrees n 2 +
    sixDegrees n 3 + sixDegrees n 4 + sixDegrees n 5) = 10 ∧
    ∀ i, sixDegrees n i ≤ 2

private instance (n : Nat) : Decidable (sixValid n) := by unfold sixValid; infer_instance

-- Encode only off-diagonal adjacency; symmetry supplies the other triangle.
private def sixEncode (H : SimpleGraph (Fin 6)) [DecidableRel H.Adj] : BitVec 15 :=
  BitVec.ofBoolListLE [
    decide (H.Adj 0 1), decide (H.Adj 0 2), decide (H.Adj 0 3),
    decide (H.Adj 0 4), decide (H.Adj 0 5), decide (H.Adj 1 2),
    decide (H.Adj 1 3), decide (H.Adj 1 4), decide (H.Adj 1 5),
    decide (H.Adj 2 3), decide (H.Adj 2 4), decide (H.Adj 2 5),
    decide (H.Adj 3 4), decide (H.Adj 3 5), decide (H.Adj 4 5)]

private theorem sixGraph_encode (H : SimpleGraph (Fin 6)) [DecidableRel H.Adj] :
    sixGraph (sixEncode H).toNat = H := by
  have hbit (b : BitVec 15) (k : Nat) : b.toNat.testBit k = b.getLsbD k := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [sixGraph, sixEncode, Fin.isValue, sixIndex, hbit, BitVec.getLsbD_ofBoolListLE,
      List.getD_eq_getElem?_getD, Fin.zero_eta, SimpleGraph.irrefl, Fin.mk_one, fromRel_adj,
      ne_eq, zero_ne_one, not_false_eq_true, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.one_mod,
      zero_le, inf_of_le_left, tsub_zero, zero_mul, Nat.zero_div, sup_of_le_right, zero_add,
      tsub_self, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos,
      List.getElem_cons_zero, Option.getD_some, decide_eq_true_eq, inf_of_le_right,
      sup_of_le_left, or_self, true_and, H.adj_comm, Fin.reduceFinMk, Fin.reduceEq, Nat.reduceMod,
      Nat.add_one_sub_one, Nat.one_lt_ofNat, List.getElem_cons_succ, Nat.reduceLT, Nat.mod_succ,
      one_ne_zero, Nat.one_le_ofNat, one_mul, Nat.reduceDiv, Nat.reduceLeDiff, Nat.reduceSub,
      Nat.reduceMul, Nat.lt_add_one] <;> exact H.adj_comm _ _

private def sixTarget (k : Fin 4) : SimpleGraph (Fin 6) :=
  sixGraph (![4649, 21025, 16933, 20515] k)

private instance (k : Fin 4) : DecidableRel (sixTarget k).Adj := by
  unfold sixTarget
  infer_instance
-- The entries give the target and a permutation from the labeled graph to it.
private def sixWitness (n : Nat) : Fin 4 × (Fin 6 → Fin 6) :=
  if n < 9350 then
    if n < 4867 then
      if n < 2348 then
        if n < 1364 then
          if n < 914 then
            if n < 820 then
              if n < 714 then
                if n < 692 then
                  if n < 684 then (3, ![4, 0, 1, 2, 3, 5]) else (0, ![0, 3, 2, 1, 4, 5])
                else
                  if n < 696 then (1, ![4, 1, 2, 3, 0, 5]) else (1, ![4, 2, 1, 0, 3, 5])
              else
                if n < 728 then
                  if n < 722 then (0, ![0, 3, 1, 2, 4, 5]) else (1, ![4, 1, 3, 2, 0, 5])
                else
                  if n < 812 then (1, ![4, 2, 0, 1, 3, 5]) else (1, ![1, 4, 3, 2, 0, 5])
            else
              if n < 856 then
                if n < 842 then
                  if n < 824 then (0, ![0, 3, 2, 1, 5, 4]) else (1, ![4, 2, 1, 0, 5, 3])
                else
                  if n < 850 then (1, ![1, 4, 2, 3, 0, 5]) else (0, ![0, 3, 1, 2, 5, 4])
              else
                if n < 906 then
                  if n < 902 then (1, ![4, 2, 0, 1, 5, 3]) else (3, ![0, 4, 1, 2, 3, 5])
                else
                  if n < 908 then (1, ![2, 4, 1, 0, 3, 5]) else (1, ![2, 4, 0, 1, 3, 5])
          else
            if n < 1234 then
              if n < 1140 then
                if n < 920 then
                  if n < 916 then (1, ![2, 4, 1, 0, 5, 3]) else (1, ![2, 4, 0, 1, 5, 3])
                else
                  if n < 1132 then (2, ![0, 2, 4, 5, 1, 3]) else (0, ![0, 2, 3, 1, 4, 5])
              else
                if n < 1204 then
                  if n < 1144 then (1, ![4, 2, 1, 3, 0, 5]) else (1, ![4, 1, 2, 0, 3, 5])
                else
                  if n < 1222 then (3, ![4, 0, 1, 3, 2, 5]) else (0, ![0, 3, 1, 4, 2, 5])
            else
              if n < 1336 then
                if n < 1324 then
                  if n < 1236 then (1, ![4, 1, 3, 0, 2, 5]) else (1, ![4, 2, 0, 3, 1, 5])
                else
                  if n < 1332 then (1, ![1, 4, 3, 0, 2, 5]) else (1, ![1, 3, 4, 0, 5, 2])
              else
                if n < 1354 then
                  if n < 1350 then (0, ![0, 3, 2, 5, 1, 4]) else (1, ![2, 4, 1, 3, 0, 5])
                else
                  if n < 1356 then
                    (3, ![0, 4, 1, 3, 2, 5])
                  else
                    if n < 1362 then (1, ![2, 4, 0, 3, 1, 5]) else (1, ![3, 1, 4, 0, 5, 2])
        else
          if n < 1816 then
            if n < 1669 then
              if n < 1428 then
                if n < 1414 then
                  if n < 1368 then (2, ![0, 2, 4, 1, 5, 3]) else (1, ![2, 4, 0, 5, 1, 3])
                else
                  if n < 1426 then (1, ![1, 4, 2, 0, 3, 5]) else (0, ![0, 3, 1, 5, 2, 4])
              else
                if n < 1617 then
                  if n < 1609 then (1, ![4, 2, 0, 5, 1, 3]) else (0, ![0, 1, 3, 2, 4, 5])
                else
                  if n < 1624 then (1, ![4, 3, 1, 2, 0, 5]) else (1, ![4, 0, 2, 1, 3, 5])
            else
              if n < 1797 then
                if n < 1684 then
                  if n < 1681 then (0, ![0, 1, 3, 4, 2, 5]) else (1, ![4, 3, 1, 0, 2, 5])
                else
                  if n < 1744 then (1, ![4, 0, 2, 3, 1, 5]) else (2, ![4, 0, 2, 1, 3, 5])
              else
                if n < 1804 then
                  if n < 1801 then (1, ![3, 4, 1, 2, 0, 5]) else (1, ![3, 4, 1, 0, 2, 5])
                else
                  if n < 1809 then
                    (2, ![0, 4, 2, 1, 3, 5])
                  else
                    if n < 1812 then (3, ![0, 1, 4, 3, 5, 2]) else (1, ![2, 0, 4, 3, 5, 1])
          else
            if n < 2220 then
              if n < 1936 then
                if n < 1872 then
                  if n < 1864 then (1, ![2, 0, 4, 5, 3, 1]) else (1, ![0, 4, 2, 3, 1, 5])
                else
                  if n < 1924 then (1, ![0, 2, 4, 3, 5, 1]) else (1, ![0, 4, 2, 1, 3, 5])
              else
                if n < 2164 then
                  if n < 2156 then (1, ![0, 2, 4, 5, 3, 1]) else (1, ![1, 3, 4, 2, 0, 5])
                else
                  if n < 2168 then (0, ![0, 2, 3, 1, 5, 4]) else (1, ![4, 1, 2, 0, 5, 3])
            else
              if n < 2250 then
                if n < 2232 then
                  if n < 2228 then (1, ![1, 3, 4, 0, 2, 5]) else (1, ![1, 4, 3, 0, 5, 2])
                else
                  if n < 2246 then (0, ![0, 2, 3, 5, 1, 4]) else (1, ![3, 1, 4, 2, 0, 5])
              else
                if n < 2258 then
                  if n < 2252 then (1, ![3, 1, 4, 0, 2, 5]) else (2, ![0, 2, 4, 1, 3, 5])
                else
                  if n < 2260 then
                    (3, ![0, 4, 1, 3, 5, 2])
                  else
                    if n < 2264 then (1, ![2, 4, 0, 3, 5, 1]) else (1, ![2, 4, 0, 5, 3, 1])
      else
        if n < 3268 then
          if n < 2760 then
            if n < 2641 then
              if n < 2438 then
                if n < 2378 then
                  if n < 2374 then (3, ![4, 0, 1, 3, 5, 2]) else (0, ![0, 3, 1, 4, 5, 2])
                else
                  if n < 2380 then (1, ![4, 1, 3, 0, 5, 2]) else (1, ![4, 2, 0, 3, 5, 1])
              else
                if n < 2444 then
                  if n < 2442 then (1, ![1, 4, 2, 0, 5, 3]) else (0, ![0, 3, 1, 5, 4, 2])
                else
                  if n < 2633 then (1, ![4, 2, 0, 5, 3, 1]) else (1, ![1, 2, 4, 3, 0, 5])
            else
              if n < 2700 then
                if n < 2693 then
                  if n < 2648 then (0, ![0, 1, 3, 2, 5, 4]) else (1, ![4, 0, 2, 1, 5, 3])
                else
                  if n < 2697 then (1, ![2, 1, 4, 3, 0, 5]) else (3, ![0, 1, 4, 3, 2, 5])
              else
                if n < 2708 then
                  if n < 2705 then (1, ![2, 0, 4, 3, 1, 5]) else (1, ![3, 4, 1, 0, 5, 2])
                else
                  if n < 2712 then (2, ![0, 4, 2, 1, 5, 3]) else (1, ![2, 0, 4, 5, 1, 3])
          else
            if n < 3141 then
              if n < 2828 then
                if n < 2821 then
                  if n < 2768 then (1, ![0, 2, 4, 3, 1, 5]) else (1, ![0, 4, 2, 3, 5, 1])
                else
                  if n < 2825 then (0, ![0, 1, 3, 4, 5, 2]) else (1, ![4, 3, 1, 0, 5, 2])
              else
                if n < 2948 then
                  if n < 2888 then (1, ![4, 0, 2, 3, 5, 1]) else (2, ![4, 0, 2, 1, 5, 3])
                else
                  if n < 2952 then (1, ![0, 4, 2, 1, 5, 3]) else (1, ![0, 2, 4, 5, 1, 3])
            else
              if n < 3156 then
                if n < 3148 then
                  if n < 3145 then (3, ![0, 1, 4, 2, 3, 5]) else (1, ![2, 1, 4, 0, 3, 5])
                else
                  if n < 3153 then (1, ![2, 0, 4, 1, 3, 5]) else (1, ![2, 1, 4, 0, 5, 3])
              else
                if n < 3205 then
                  if n < 3160 then (1, ![2, 0, 4, 1, 5, 3]) else (2, ![0, 4, 2, 5, 1, 3])
                else
                  if n < 3217 then
                    (1, ![1, 2, 4, 0, 3, 5])
                  else
                    if n < 3220 then (0, ![0, 1, 3, 5, 2, 4]) else (1, ![4, 0, 2, 5, 1, 3])
        else
          if n < 4396 then
            if n < 4202 then
              if n < 3340 then
                if n < 3333 then
                  if n < 3280 then (1, ![0, 2, 4, 1, 3, 5]) else (1, ![0, 4, 2, 5, 3, 1])
                else
                  if n < 3337 then (1, ![1, 2, 4, 0, 5, 3]) else (0, ![0, 1, 3, 5, 4, 2])
              else
                if n < 3400 then
                  if n < 3396 then (1, ![4, 0, 2, 5, 3, 1]) else (1, ![0, 2, 4, 1, 5, 3])
                else
                  if n < 3460 then (1, ![0, 4, 2, 5, 1, 3]) else (2, ![4, 0, 2, 5, 1, 3])
            else
              if n < 4274 then
                if n < 4216 then
                  if n < 4210 then (0, ![0, 2, 1, 3, 4, 5]) else (1, ![4, 2, 3, 1, 0, 5])
                else
                  if n < 4262 then (1, ![4, 1, 0, 2, 3, 5]) else (0, ![0, 2, 1, 4, 3, 5])
              else
                if n < 4306 then
                  if n < 4276 then (1, ![4, 2, 3, 0, 1, 5]) else (1, ![4, 1, 0, 3, 2, 5])
                else
                  if n < 4390 then
                    (3, ![4, 0, 3, 1, 2, 5])
                  else
                    if n < 4394 then (1, ![2, 4, 3, 1, 0, 5]) else (1, ![2, 4, 3, 0, 1, 5])
          else
            if n < 4498 then
              if n < 4426 then
                if n < 4404 then
                  if n < 4402 then (3, ![0, 4, 3, 1, 2, 5]) else (2, ![0, 2, 1, 4, 5, 3])
                else
                  if n < 4408 then (1, ![3, 1, 0, 4, 5, 2]) else (1, ![3, 1, 0, 5, 4, 2])
              else
                if n < 4440 then
                  if n < 4434 then (1, ![1, 4, 0, 3, 2, 5]) else (1, ![1, 3, 0, 4, 5, 2])
                else
                  if n < 4486 then (0, ![0, 3, 5, 2, 1, 4]) else (1, ![1, 4, 0, 2, 3, 5])
            else
              if n < 4664 then
                if n < 4649 then
                  if n < 4500 then (1, ![1, 3, 0, 5, 4, 2]) else (0, ![0, 3, 5, 1, 2, 4])
                else
                  if n < 4657 then (0, ![0, 1, 2, 3, 4, 5]) else (1, ![4, 3, 2, 1, 0, 5])
              else
                if n < 4753 then
                  if n < 4739 then (1, ![4, 0, 1, 2, 3, 5]) else (0, ![0, 1, 4, 3, 2, 5])
                else
                  if n < 4754 then
                    (1, ![4, 3, 0, 1, 2, 5])
                  else
                    if n < 4784 then (1, ![4, 0, 3, 2, 1, 5]) else (2, ![4, 0, 1, 2, 3, 5])
    else
      if n < 6673 then
        if n < 6193 then
          if n < 5232 then
            if n < 4994 then
              if n < 4882 then
                if n < 4874 then
                  if n < 4873 then (1, ![3, 4, 2, 1, 0, 5]) else (1, ![3, 4, 0, 1, 2, 5])
                else
                  if n < 4881 then (2, ![0, 4, 1, 2, 3, 5]) else (3, ![0, 1, 3, 4, 5, 2])
              else
                if n < 4904 then
                  if n < 4888 then (1, ![2, 0, 3, 4, 5, 1]) else (1, ![2, 0, 5, 4, 3, 1])
                else
                  if n < 4912 then (1, ![0, 4, 3, 2, 1, 5]) else (1, ![0, 2, 3, 4, 5, 1])
            else
              if n < 5172 then
                if n < 5157 then
                  if n < 5008 then (1, ![0, 4, 1, 2, 3, 5]) else (1, ![0, 2, 5, 4, 3, 1])
                else
                  if n < 5169 then (0, ![0, 1, 2, 4, 3, 5]) else (1, ![4, 3, 2, 0, 1, 5])
              else
                if n < 5201 then
                  if n < 5187 then (1, ![4, 0, 1, 3, 2, 5]) else (0, ![0, 1, 4, 2, 3, 5])
                else
                  if n < 5202 then (1, ![4, 3, 0, 2, 1, 5]) else (1, ![4, 0, 3, 1, 2, 5])
          else
            if n < 5424 then
              if n < 5393 then
                if n < 5381 then
                  if n < 5379 then (2, ![4, 0, 1, 3, 2, 5]) else (1, ![3, 4, 2, 0, 1, 5])
                else
                  if n < 5382 then (1, ![3, 4, 0, 2, 1, 5]) else (2, ![0, 4, 1, 3, 2, 5])
              else
                if n < 5396 then
                  if n < 5394 then (3, ![0, 1, 3, 5, 4, 2]) else (1, ![2, 0, 3, 5, 4, 1])
                else
                  if n < 5412 then (1, ![2, 0, 5, 3, 4, 1]) else (1, ![0, 4, 3, 1, 2, 5])
            else
              if n < 5889 then
                if n < 5456 then
                  if n < 5442 then (1, ![0, 2, 3, 5, 4, 1]) else (1, ![0, 4, 1, 3, 2, 5])
                else
                  if n < 5649 then (1, ![0, 2, 5, 3, 4, 1]) else (3, ![4, 3, 0, 1, 2, 5])
              else
                if n < 6181 then
                  if n < 5904 then (3, ![3, 4, 0, 1, 2, 5]) else (3, ![3, 5, 0, 1, 2, 4])
                else
                  if n < 6185 then
                    (1, ![2, 3, 4, 1, 0, 5])
                  else
                    if n < 6188 then (1, ![2, 3, 4, 0, 1, 5]) else (3, ![0, 3, 4, 1, 2, 5])
        else
          if n < 6308 then
            if n < 6232 then
              if n < 6217 then
                if n < 6200 then
                  if n < 6196 then (2, ![0, 1, 2, 4, 5, 3]) else (1, ![3, 0, 1, 4, 5, 2])
                else
                  if n < 6211 then (1, ![3, 0, 1, 5, 4, 2]) else (1, ![3, 2, 4, 1, 0, 5])
              else
                if n < 6225 then
                  if n < 6218 then (2, ![0, 1, 4, 2, 3, 5]) else (1, ![3, 0, 4, 1, 2, 5])
                else
                  if n < 6226 then (1, ![2, 3, 0, 4, 5, 1]) else (3, ![0, 3, 1, 4, 5, 2])
            else
              if n < 6277 then
                if n < 6256 then
                  if n < 6248 then (1, ![3, 0, 5, 1, 2, 4]) else (1, ![0, 3, 4, 2, 1, 5])
                else
                  if n < 6275 then (1, ![0, 3, 2, 4, 5, 1]) else (1, ![3, 2, 4, 0, 1, 5])
              else
                if n < 6289 then
                  if n < 6278 then (2, ![0, 1, 4, 3, 2, 5]) else (1, ![3, 0, 4, 2, 1, 5])
                else
                  if n < 6290 then
                    (1, ![2, 3, 0, 5, 4, 1])
                  else
                    if n < 6292 then (3, ![0, 3, 1, 5, 4, 2]) else (1, ![3, 0, 5, 2, 1, 4])
          else
            if n < 6410 then
              if n < 6403 then
                if n < 6338 then
                  if n < 6320 then (1, ![0, 3, 4, 1, 2, 5]) else (1, ![0, 3, 2, 5, 4, 1])
                else
                  if n < 6352 then (3, ![3, 0, 4, 1, 2, 5]) else (3, ![3, 0, 5, 1, 2, 4])
              else
                if n < 6406 then
                  if n < 6405 then (2, ![0, 1, 3, 4, 5, 2]) else (1, ![3, 2, 0, 4, 5, 1])
                else
                  if n < 6409 then (1, ![3, 0, 2, 4, 5, 1]) else (1, ![3, 2, 0, 5, 4, 1])
            else
              if n < 6466 then
                if n < 6436 then
                  if n < 6412 then (1, ![3, 0, 2, 5, 4, 1]) else (3, ![0, 3, 5, 1, 2, 4])
                else
                  if n < 6440 then (3, ![3, 0, 1, 4, 5, 2]) else (3, ![3, 0, 1, 5, 4, 2])
              else
                if n < 6530 then
                  if n < 6472 then (1, ![0, 3, 1, 4, 5, 2]) else (1, ![0, 3, 5, 2, 1, 4])
                else
                  if n < 6532 then
                    (1, ![0, 3, 1, 5, 4, 2])
                  else
                    if n < 6665 then (1, ![0, 3, 5, 1, 2, 4]) else (1, ![1, 0, 4, 3, 2, 5])
      else
        if n < 8588 then
          if n < 8306 then
            if n < 7185 then
              if n < 6913 then
                if n < 6785 then
                  if n < 6680 then (1, ![1, 0, 3, 4, 5, 2]) else (0, ![0, 5, 3, 2, 1, 4])
                else
                  if n < 6800 then (1, ![0, 1, 4, 3, 2, 5]) else (1, ![0, 5, 2, 3, 4, 1])
              else
                if n < 7040 then
                  if n < 6920 then (1, ![0, 1, 3, 4, 5, 2]) else (1, ![0, 5, 3, 2, 1, 4])
                else
                  if n < 7173 then (0, ![5, 0, 3, 2, 1, 4]) else (1, ![1, 0, 4, 2, 3, 5])
            else
              if n < 7425 then
                if n < 7233 then
                  if n < 7188 then (1, ![1, 0, 3, 5, 4, 2]) else (0, ![0, 5, 3, 1, 2, 4])
                else
                  if n < 7248 then (1, ![0, 1, 4, 2, 3, 5]) else (1, ![0, 5, 2, 4, 3, 1])
              else
                if n < 7488 then
                  if n < 7428 then (1, ![0, 1, 3, 5, 4, 2]) else (1, ![0, 5, 3, 1, 2, 4])
                else
                  if n < 8298 then (0, ![5, 0, 3, 1, 2, 4]) else (1, ![1, 3, 2, 4, 0, 5])
          else
            if n < 8394 then
              if n < 8364 then
                if n < 8358 then
                  if n < 8312 then (0, ![0, 2, 1, 3, 5, 4]) else (1, ![4, 1, 0, 2, 5, 3])
                else
                  if n < 8362 then (1, ![3, 1, 2, 4, 0, 5]) else (2, ![0, 2, 1, 4, 3, 5])
              else
                if n < 8372 then
                  if n < 8370 then (1, ![3, 1, 0, 4, 2, 5]) else (1, ![2, 4, 3, 0, 5, 1])
                else
                  if n < 8376 then (3, ![0, 4, 3, 1, 5, 2]) else (1, ![3, 1, 0, 5, 2, 4])
            else
              if n < 8490 then
                if n < 8408 then
                  if n < 8402 then (1, ![1, 3, 0, 4, 2, 5]) else (1, ![1, 4, 0, 3, 5, 2])
                else
                  if n < 8486 then (0, ![0, 2, 5, 3, 1, 4]) else (0, ![0, 2, 1, 4, 5, 3])
              else
                if n < 8522 then
                  if n < 8492 then (1, ![4, 2, 3, 0, 5, 1]) else (1, ![4, 1, 0, 3, 5, 2])
                else
                  if n < 8582 then
                    (3, ![4, 0, 3, 1, 5, 2])
                  else
                    if n < 8586 then (1, ![1, 4, 0, 2, 5, 3]) else (1, ![1, 3, 0, 5, 2, 4])
        else
          if n < 9096 then
            if n < 8850 then
              if n < 8835 then
                if n < 8753 then
                  if n < 8745 then (0, ![0, 3, 5, 1, 4, 2]) else (1, ![1, 2, 3, 4, 0, 5])
                else
                  if n < 8760 then (0, ![0, 1, 2, 3, 5, 4]) else (1, ![4, 0, 1, 2, 5, 3])
              else
                if n < 8842 then
                  if n < 8841 then (1, ![2, 1, 3, 4, 0, 5]) else (3, ![0, 1, 3, 4, 2, 5])
                else
                  if n < 8849 then (1, ![2, 0, 3, 4, 1, 5]) else (1, ![3, 4, 0, 1, 5, 2])
            else
              if n < 8963 then
                if n < 8872 then
                  if n < 8856 then (2, ![0, 4, 1, 2, 5, 3]) else (1, ![2, 0, 5, 4, 1, 3])
                else
                  if n < 8880 then (1, ![0, 2, 3, 4, 1, 5]) else (1, ![0, 4, 3, 2, 5, 1])
              else
                if n < 8970 then
                  if n < 8969 then (0, ![0, 1, 4, 3, 5, 2]) else (1, ![4, 3, 0, 1, 5, 2])
                else
                  if n < 9000 then
                    (1, ![4, 0, 3, 2, 5, 1])
                  else
                    if n < 9090 then (2, ![4, 0, 1, 2, 5, 3]) else (1, ![0, 4, 1, 2, 5, 3])
          else
            if n < 9289 then
              if n < 9265 then
                if n < 9257 then
                  if n < 9253 then (1, ![0, 2, 5, 4, 1, 3]) else (1, ![3, 2, 1, 4, 0, 5])
                else
                  if n < 9260 then (2, ![0, 1, 2, 4, 3, 5]) else (1, ![3, 0, 1, 4, 2, 5])
              else
                if n < 9272 then
                  if n < 9268 then (1, ![2, 3, 4, 0, 5, 1]) else (3, ![0, 3, 4, 1, 5, 2])
                else
                  if n < 9283 then (1, ![3, 0, 1, 5, 2, 4]) else (1, ![2, 3, 1, 4, 0, 5])
            else
              if n < 9304 then
                if n < 9297 then
                  if n < 9290 then (1, ![2, 3, 0, 4, 1, 5]) else (3, ![0, 3, 1, 4, 2, 5])
                else
                  if n < 9298 then (2, ![0, 1, 4, 2, 5, 3]) else (1, ![3, 0, 4, 1, 5, 2])
              else
                if n < 9328 then
                  if n < 9320 then (1, ![3, 0, 5, 1, 4, 2]) else (1, ![0, 3, 2, 4, 1, 5])
                else
                  if n < 9347 then
                    (1, ![0, 3, 4, 2, 5, 1])
                  else
                    if n < 9349 then (2, ![0, 1, 3, 4, 2, 5]) else (1, ![3, 2, 0, 4, 1, 5])
  else
    if n < 17157 then
      if n < 12547 then
        if n < 10314 then
          if n < 9538 then
            if n < 9475 then
              if n < 9380 then
                if n < 9362 then
                  if n < 9361 then (1, ![3, 0, 2, 4, 1, 5]) else (1, ![3, 2, 0, 5, 1, 4])
                else
                  if n < 9364 then (1, ![3, 0, 2, 5, 1, 4]) else (3, ![0, 3, 5, 1, 4, 2])
              else
                if n < 9410 then
                  if n < 9392 then (3, ![3, 0, 1, 4, 2, 5]) else (3, ![3, 0, 1, 5, 2, 4])
                else
                  if n < 9424 then (1, ![0, 3, 1, 4, 2, 5]) else (1, ![0, 3, 5, 2, 4, 1])
            else
              if n < 9482 then
                if n < 9478 then
                  if n < 9477 then (1, ![3, 2, 4, 0, 5, 1]) else (2, ![0, 1, 4, 3, 5, 2])
                else
                  if n < 9481 then (1, ![3, 0, 4, 2, 5, 1]) else (1, ![2, 3, 0, 5, 1, 4])
              else
                if n < 9508 then
                  if n < 9484 then (3, ![0, 3, 1, 5, 2, 4]) else (1, ![3, 0, 5, 2, 4, 1])
                else
                  if n < 9512 then (1, ![0, 3, 4, 1, 5, 2]) else (1, ![0, 3, 2, 5, 1, 4])
          else
            if n < 9872 then
              if n < 9737 then
                if n < 9602 then
                  if n < 9544 then (3, ![3, 0, 4, 1, 5, 2]) else (3, ![3, 0, 5, 1, 4, 2])
                else
                  if n < 9604 then (1, ![0, 3, 1, 5, 2, 4]) else (1, ![0, 3, 5, 1, 4, 2])
              else
                if n < 9752 then
                  if n < 9745 then (1, ![1, 0, 3, 4, 2, 5]) else (1, ![1, 0, 4, 3, 5, 2])
                else
                  if n < 9857 then (0, ![0, 5, 2, 3, 1, 4]) else (1, ![0, 1, 3, 4, 2, 5])
            else
              if n < 10277 then
                if n < 9992 then
                  if n < 9985 then (1, ![0, 5, 3, 2, 4, 1]) else (1, ![0, 1, 4, 3, 5, 2])
                else
                  if n < 10112 then (1, ![0, 5, 2, 3, 1, 4]) else (0, ![5, 0, 2, 3, 1, 4])
              else
                if n < 10284 then
                  if n < 10281 then (0, ![0, 1, 2, 4, 5, 3]) else (1, ![4, 3, 2, 0, 5, 1])
                else
                  if n < 10307 then
                    (1, ![4, 0, 1, 3, 5, 2])
                  else
                    if n < 10313 then (0, ![0, 1, 4, 2, 5, 3]) else (1, ![4, 3, 0, 2, 5, 1])
        else
          if n < 11276 then
            if n < 10404 then
              if n < 10374 then
                if n < 10371 then
                  if n < 10344 then (1, ![4, 0, 3, 1, 5, 2]) else (2, ![4, 0, 1, 3, 5, 2])
                else
                  if n < 10373 then (1, ![3, 4, 2, 0, 5, 1]) else (1, ![3, 4, 0, 2, 5, 1])
              else
                if n < 10378 then
                  if n < 10377 then (2, ![0, 4, 1, 3, 5, 2]) else (3, ![0, 1, 3, 5, 2, 4])
                else
                  if n < 10380 then (1, ![2, 0, 3, 5, 1, 4]) else (1, ![2, 0, 5, 3, 1, 4])
            else
              if n < 10761 then
                if n < 10434 then
                  if n < 10408 then (1, ![0, 4, 3, 1, 5, 2]) else (1, ![0, 2, 3, 5, 1, 4])
                else
                  if n < 10440 then (1, ![0, 4, 1, 3, 5, 2]) else (1, ![0, 2, 5, 3, 1, 4])
              else
                if n < 10888 then
                  if n < 10881 then (3, ![4, 3, 0, 1, 5, 2]) else (3, ![3, 4, 0, 1, 5, 2])
                else
                  if n < 11269 then
                    (3, ![3, 5, 0, 1, 4, 2])
                  else
                    if n < 11273 then (1, ![1, 0, 4, 2, 5, 3]) else (1, ![1, 0, 3, 5, 2, 4])
          else
            if n < 12330 then
              if n < 11396 then
                if n < 11336 then
                  if n < 11329 then (0, ![0, 5, 3, 1, 4, 2]) else (1, ![0, 1, 4, 2, 5, 3])
                else
                  if n < 11393 then (1, ![0, 5, 2, 4, 1, 3]) else (1, ![0, 1, 3, 5, 2, 4])
              else
                if n < 12323 then
                  if n < 11456 then (1, ![0, 5, 3, 1, 4, 2]) else (0, ![5, 0, 3, 1, 4, 2])
                else
                  if n < 12329 then (3, ![0, 1, 2, 4, 3, 5]) else (1, ![2, 1, 0, 4, 3, 5])
            else
              if n < 12419 then
                if n < 12338 then
                  if n < 12337 then (1, ![2, 0, 1, 4, 3, 5]) else (1, ![2, 1, 0, 4, 5, 3])
                else
                  if n < 12344 then (1, ![2, 0, 1, 4, 5, 3]) else (2, ![0, 4, 5, 2, 1, 3])
              else
                if n < 12434 then
                  if n < 12433 then (1, ![1, 2, 0, 4, 3, 5]) else (0, ![0, 1, 5, 3, 2, 4])
                else
                  if n < 12450 then
                    (1, ![4, 0, 5, 2, 1, 3])
                  else
                    if n < 12464 then (1, ![0, 2, 1, 4, 3, 5]) else (1, ![0, 4, 5, 2, 3, 1])
      else
        if n < 16594 then
          if n < 14346 then
            if n < 13330 then
              if n < 12584 then
                if n < 12554 then
                  if n < 12553 then (1, ![1, 2, 0, 4, 5, 3]) else (0, ![0, 1, 5, 3, 4, 2])
                else
                  if n < 12578 then (1, ![4, 0, 5, 2, 3, 1]) else (1, ![0, 2, 1, 4, 5, 3])
              else
                if n < 13315 then
                  if n < 12674 then (1, ![0, 4, 5, 2, 1, 3]) else (2, ![4, 0, 5, 2, 1, 3])
                else
                  if n < 13329 then (1, ![1, 0, 2, 4, 3, 5]) else (1, ![1, 0, 5, 3, 4, 2])
            else
              if n < 13570 then
                if n < 13360 then
                  if n < 13345 then (0, ![0, 5, 1, 3, 2, 4]) else (1, ![0, 1, 2, 4, 3, 5])
                else
                  if n < 13569 then (1, ![0, 5, 4, 2, 3, 1]) else (1, ![0, 1, 5, 3, 4, 2])
              else
                if n < 14339 then
                  if n < 13600 then (1, ![0, 5, 1, 3, 2, 4]) else (0, ![5, 0, 1, 3, 2, 4])
                else
                  if n < 14345 then (1, ![1, 0, 2, 4, 5, 3]) else (1, ![1, 0, 5, 3, 2, 4])
          else
            if n < 16490 then
              if n < 14466 then
                if n < 14376 then
                  if n < 14369 then (0, ![0, 5, 1, 3, 4, 2]) else (1, ![0, 1, 2, 4, 5, 3])
                else
                  if n < 14465 then (1, ![0, 5, 4, 2, 1, 3]) else (1, ![0, 1, 5, 3, 2, 4])
              else
                if n < 15361 then
                  if n < 14496 then (1, ![0, 5, 1, 3, 4, 2]) else (0, ![5, 0, 1, 3, 4, 2])
                else
                  if n < 16486 then (2, ![4, 5, 0, 2, 1, 3]) else (2, ![0, 2, 1, 3, 4, 5])
            else
              if n < 16504 then
                if n < 16498 then
                  if n < 16492 then (1, ![3, 1, 2, 0, 4, 5]) else (1, ![3, 1, 0, 2, 4, 5])
                else
                  if n < 16500 then (1, ![3, 1, 2, 0, 5, 4]) else (1, ![3, 1, 0, 2, 5, 4])
              else
                if n < 16562 then
                  if n < 16550 then (3, ![0, 4, 3, 5, 1, 2]) else (1, ![1, 3, 2, 0, 4, 5])
                else
                  if n < 16564 then
                    (0, ![0, 2, 1, 5, 3, 4])
                  else
                    if n < 16582 then (1, ![4, 1, 0, 5, 2, 3]) else (1, ![1, 3, 0, 2, 4, 5])
        else
          if n < 16970 then
            if n < 16774 then
              if n < 16684 then
                if n < 16678 then
                  if n < 16596 then (1, ![1, 4, 0, 5, 3, 2]) else (0, ![0, 2, 5, 1, 3, 4])
                else
                  if n < 16682 then (1, ![1, 3, 2, 0, 5, 4]) else (0, ![0, 2, 1, 5, 4, 3])
              else
                if n < 16714 then
                  if n < 16710 then (1, ![4, 1, 0, 5, 3, 2]) else (1, ![1, 3, 0, 2, 5, 4])
                else
                  if n < 16716 then (1, ![1, 4, 0, 5, 2, 3]) else (0, ![0, 2, 5, 1, 4, 3])
            else
              if n < 16945 then
                if n < 16937 then
                  if n < 16933 then (3, ![4, 0, 3, 5, 1, 2]) else (2, ![0, 1, 2, 3, 4, 5])
                else
                  if n < 16940 then (1, ![3, 2, 1, 0, 4, 5]) else (1, ![3, 0, 1, 2, 4, 5])
              else
                if n < 16952 then
                  if n < 16948 then (1, ![3, 2, 1, 0, 5, 4]) else (1, ![3, 0, 1, 2, 5, 4])
                else
                  if n < 16963 then
                    (3, ![0, 3, 4, 5, 1, 2])
                  else
                    if n < 16969 then (2, ![0, 1, 3, 2, 4, 5]) else (1, ![3, 2, 0, 1, 4, 5])
          else
            if n < 17030 then
              if n < 17000 then
                if n < 16978 then
                  if n < 16977 then (1, ![3, 0, 2, 1, 4, 5]) else (1, ![3, 2, 0, 1, 5, 4])
                else
                  if n < 16984 then (1, ![3, 0, 2, 1, 5, 4]) else (3, ![0, 3, 5, 4, 1, 2])
              else
                if n < 17027 then
                  if n < 17008 then (3, ![3, 0, 1, 2, 4, 5]) else (3, ![3, 0, 1, 2, 5, 4])
                else
                  if n < 17029 then (1, ![2, 3, 1, 0, 4, 5]) else (1, ![2, 3, 0, 1, 4, 5])
            else
              if n < 17060 then
                if n < 17042 then
                  if n < 17041 then (3, ![0, 3, 1, 2, 4, 5]) else (2, ![0, 1, 4, 5, 2, 3])
                else
                  if n < 17044 then (1, ![3, 0, 4, 5, 1, 2]) else (1, ![3, 0, 5, 4, 1, 2])
              else
                if n < 17090 then
                  if n < 17072 then (1, ![0, 3, 2, 1, 4, 5]) else (1, ![0, 3, 4, 5, 2, 1])
                else
                  if n < 17104 then
                    (1, ![0, 3, 1, 2, 4, 5])
                  else
                    if n < 17155 then (1, ![0, 3, 5, 4, 2, 1]) else (1, ![2, 3, 1, 0, 5, 4])
    else
      if n < 20529 then
        if n < 18177 then
          if n < 17478 then
            if n < 17224 then
              if n < 17164 then
                if n < 17161 then
                  if n < 17158 then (1, ![2, 3, 0, 1, 5, 4]) else (3, ![0, 3, 1, 2, 5, 4])
                else
                  if n < 17162 then (2, ![0, 1, 4, 5, 3, 2]) else (1, ![3, 0, 4, 5, 2, 1])
              else
                if n < 17192 then
                  if n < 17188 then (1, ![3, 0, 5, 4, 2, 1]) else (1, ![0, 3, 2, 1, 5, 4])
                else
                  if n < 17218 then (1, ![0, 3, 4, 5, 1, 2]) else (1, ![0, 3, 1, 2, 5, 4])
            else
              if n < 17457 then
                if n < 17284 then
                  if n < 17282 then (1, ![0, 3, 5, 4, 1, 2]) else (3, ![3, 0, 4, 5, 1, 2])
                else
                  if n < 17445 then (3, ![3, 0, 5, 4, 1, 2]) else (1, ![1, 2, 3, 0, 4, 5])
              else
                if n < 17475 then
                  if n < 17460 then (0, ![0, 1, 2, 5, 3, 4]) else (1, ![4, 0, 1, 5, 2, 3])
                else
                  if n < 17477 then (1, ![2, 1, 3, 0, 4, 5]) else (3, ![0, 1, 3, 2, 4, 5])
          else
            if n < 17670 then
              if n < 17508 then
                if n < 17490 then
                  if n < 17489 then (1, ![2, 0, 3, 1, 4, 5]) else (1, ![3, 4, 0, 5, 1, 2])
                else
                  if n < 17492 then (2, ![0, 4, 1, 5, 2, 3]) else (1, ![2, 0, 5, 1, 4, 3])
              else
                if n < 17667 then
                  if n < 17520 then (1, ![0, 2, 3, 1, 4, 5]) else (1, ![0, 4, 3, 5, 2, 1])
                else
                  if n < 17669 then (0, ![0, 1, 4, 5, 3, 2]) else (1, ![4, 3, 0, 5, 1, 2])
            else
              if n < 17925 then
                if n < 17730 then
                  if n < 17700 then (1, ![4, 0, 3, 5, 2, 1]) else (2, ![4, 0, 1, 5, 2, 3])
                else
                  if n < 17732 then (1, ![0, 4, 1, 5, 2, 3]) else (1, ![0, 2, 5, 1, 4, 3])
              else
                if n < 17940 then
                  if n < 17937 then (1, ![1, 0, 3, 2, 4, 5]) else (1, ![1, 0, 4, 5, 3, 2])
                else
                  if n < 17985 then
                    (0, ![0, 5, 2, 1, 3, 4])
                  else
                    if n < 18000 then (1, ![0, 1, 3, 2, 4, 5]) else (1, ![0, 5, 3, 4, 2, 1])
        else
          if n < 18596 then
            if n < 18502 then
              if n < 18473 then
                if n < 18240 then
                  if n < 18180 then (1, ![0, 1, 4, 5, 3, 2]) else (1, ![0, 5, 2, 1, 3, 4])
                else
                  if n < 18469 then (0, ![5, 0, 2, 1, 3, 4]) else (1, ![1, 2, 3, 0, 5, 4])
              else
                if n < 18499 then
                  if n < 18476 then (0, ![0, 1, 2, 5, 4, 3]) else (1, ![4, 0, 1, 5, 3, 2])
                else
                  if n < 18501 then (1, ![2, 1, 3, 0, 5, 4]) else (3, ![0, 1, 3, 2, 5, 4])
            else
              if n < 18532 then
                if n < 18506 then
                  if n < 18505 then (1, ![2, 0, 3, 1, 5, 4]) else (1, ![3, 4, 0, 5, 2, 1])
                else
                  if n < 18508 then (2, ![0, 4, 1, 5, 3, 2]) else (1, ![2, 0, 5, 1, 3, 4])
              else
                if n < 18563 then
                  if n < 18536 then (1, ![0, 2, 3, 1, 5, 4]) else (1, ![0, 4, 3, 5, 1, 2])
                else
                  if n < 18565 then
                    (0, ![0, 1, 4, 5, 2, 3])
                  else
                    if n < 18566 then (1, ![4, 3, 0, 5, 2, 1]) else (1, ![4, 0, 3, 5, 1, 2])
          else
            if n < 19073 then
              if n < 18953 then
                if n < 18628 then
                  if n < 18626 then (2, ![4, 0, 1, 5, 3, 2]) else (1, ![0, 4, 1, 5, 3, 2])
                else
                  if n < 18949 then (1, ![0, 2, 5, 1, 3, 4]) else (1, ![1, 0, 3, 2, 5, 4])
              else
                if n < 19009 then
                  if n < 18956 then (1, ![1, 0, 4, 5, 2, 3]) else (0, ![0, 5, 2, 1, 4, 3])
                else
                  if n < 19016 then (1, ![0, 1, 3, 2, 5, 4]) else (1, ![0, 5, 3, 4, 1, 2])
            else
              if n < 19521 then
                if n < 19136 then
                  if n < 19076 then (1, ![0, 1, 4, 5, 2, 3]) else (1, ![0, 5, 2, 1, 4, 3])
                else
                  if n < 19461 then (0, ![5, 0, 2, 1, 4, 3]) else (3, ![4, 3, 0, 5, 1, 2])
              else
                if n < 20515 then
                  if n < 19524 then (3, ![3, 4, 0, 5, 1, 2]) else (3, ![3, 5, 0, 4, 1, 2])
                else
                  if n < 20517 then
                    (3, ![0, 1, 2, 3, 4, 5])
                  else
                    if n < 20518 then (1, ![2, 1, 0, 3, 4, 5]) else (1, ![2, 0, 1, 3, 4, 5])
      else
        if n < 24617 then
          if n < 21025 then
            if n < 20739 then
              if n < 20561 then
                if n < 20532 then
                  if n < 20530 then (1, ![2, 1, 0, 5, 4, 3]) else (1, ![2, 0, 1, 5, 4, 3])
                else
                  if n < 20547 then (2, ![0, 4, 5, 1, 2, 3]) else (1, ![1, 2, 0, 3, 4, 5])
              else
                if n < 20578 then
                  if n < 20562 then (0, ![0, 1, 5, 2, 3, 4]) else (1, ![4, 0, 5, 1, 2, 3])
                else
                  if n < 20592 then (1, ![0, 2, 1, 3, 4, 5]) else (1, ![0, 4, 5, 3, 2, 1])
            else
              if n < 20772 then
                if n < 20742 then
                  if n < 20741 then (1, ![1, 2, 0, 5, 4, 3]) else (0, ![0, 1, 5, 4, 3, 2])
                else
                  if n < 20770 then (1, ![4, 0, 5, 3, 2, 1]) else (1, ![0, 2, 1, 5, 4, 3])
              else
                if n < 20995 then
                  if n < 20802 then (1, ![0, 4, 5, 1, 2, 3]) else (2, ![4, 0, 5, 1, 2, 3])
                else
                  if n < 21009 then
                    (1, ![1, 0, 2, 3, 4, 5])
                  else
                    if n < 21010 then (1, ![1, 0, 5, 4, 3, 2]) else (0, ![0, 5, 1, 2, 3, 4])
          else
            if n < 22561 then
              if n < 21280 then
                if n < 21249 then
                  if n < 21040 then (1, ![0, 1, 2, 3, 4, 5]) else (1, ![0, 5, 4, 3, 2, 1])
                else
                  if n < 21250 then (1, ![0, 1, 5, 4, 3, 2]) else (1, ![0, 5, 1, 2, 3, 4])
              else
                if n < 22533 then
                  if n < 22531 then (0, ![5, 0, 1, 2, 3, 4]) else (1, ![1, 0, 2, 5, 4, 3])
                else
                  if n < 22534 then (1, ![1, 0, 5, 2, 3, 4]) else (0, ![0, 5, 1, 4, 3, 2])
            else
              if n < 22624 then
                if n < 22593 then
                  if n < 22564 then (1, ![0, 1, 2, 5, 4, 3]) else (1, ![0, 5, 4, 1, 2, 3])
                else
                  if n < 22594 then (1, ![0, 1, 5, 2, 3, 4]) else (1, ![0, 5, 1, 4, 3, 2])
              else
                if n < 24611 then
                  if n < 23041 then (0, ![5, 0, 1, 4, 3, 2]) else (2, ![4, 5, 0, 1, 2, 3])
                else
                  if n < 24613 then
                    (3, ![0, 1, 2, 3, 5, 4])
                  else
                    if n < 24614 then (1, ![2, 1, 0, 3, 5, 4]) else (1, ![2, 0, 1, 3, 5, 4])
        else
          if n < 25121 then
            if n < 24707 then
              if n < 24649 then
                if n < 24620 then
                  if n < 24618 then (1, ![2, 1, 0, 5, 3, 4]) else (1, ![2, 0, 1, 5, 3, 4])
                else
                  if n < 24643 then (2, ![0, 4, 5, 1, 3, 2]) else (1, ![1, 2, 0, 3, 5, 4])
              else
                if n < 24674 then
                  if n < 24650 then (0, ![0, 1, 5, 2, 4, 3]) else (1, ![4, 0, 5, 1, 3, 2])
                else
                  if n < 24680 then (1, ![0, 2, 1, 3, 5, 4]) else (1, ![0, 4, 5, 3, 1, 2])
            else
              if n < 24740 then
                if n < 24710 then
                  if n < 24709 then (1, ![1, 2, 0, 5, 3, 4]) else (0, ![0, 1, 5, 4, 2, 3])
                else
                  if n < 24738 then (1, ![4, 0, 5, 3, 1, 2]) else (1, ![0, 2, 1, 5, 3, 4])
              else
                if n < 25091 then
                  if n < 24770 then (1, ![0, 4, 5, 1, 3, 2]) else (2, ![4, 0, 5, 1, 3, 2])
                else
                  if n < 25097 then
                    (1, ![1, 0, 2, 3, 5, 4])
                  else
                    if n < 25098 then (1, ![1, 0, 5, 4, 2, 3]) else (0, ![0, 5, 1, 2, 4, 3])
          else
            if n < 25633 then
              if n < 25248 then
                if n < 25217 then
                  if n < 25128 then (1, ![0, 1, 2, 3, 5, 4]) else (1, ![0, 5, 4, 3, 1, 2])
                else
                  if n < 25218 then (1, ![0, 1, 5, 4, 2, 3]) else (1, ![0, 5, 1, 2, 4, 3])
              else
                if n < 25605 then
                  if n < 25603 then (0, ![5, 0, 1, 2, 4, 3]) else (1, ![1, 0, 2, 5, 3, 4])
                else
                  if n < 25606 then (1, ![1, 0, 5, 2, 4, 3]) else (0, ![0, 5, 1, 4, 2, 3])
            else
              if n < 25696 then
                if n < 25665 then
                  if n < 25636 then (1, ![0, 1, 2, 5, 3, 4]) else (1, ![0, 5, 4, 1, 3, 2])
                else
                  if n < 25666 then (1, ![0, 1, 5, 2, 4, 3]) else (1, ![0, 5, 1, 4, 2, 3])
              else
                if n < 28675 then
                  if n < 26113 then (0, ![5, 0, 1, 4, 2, 3]) else (2, ![4, 5, 0, 1, 3, 2])
                else
                  if n < 28705 then
                    (3, ![4, 3, 5, 0, 1, 2])
                  else
                    if n < 28706 then (3, ![3, 4, 5, 0, 1, 2]) else (3, ![3, 5, 4, 0, 1, 2])

private def sixCertificate (n : Nat) : Prop :=
  let w := sixWitness n
  Function.Bijective w.2 ∧
    ∀ i j, (sixTarget w.1).Adj (w.2 i) (w.2 j) ↔ (sixGraph n).Adj i j

private instance (n : Nat) : Decidable (sixCertificate n) := by
  unfold sixCertificate Function.Bijective Function.Injective Function.Surjective
  infer_instance

-- Exhaustive checks use kernel reduction only.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck0 :
    ∀ n : Fin 1024, sixValid (0 + n.val) → sixCertificate (0 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck1 :
    ∀ n : Fin 1024, sixValid (1024 + n.val) → sixCertificate (1024 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck2 :
    ∀ n : Fin 1024, sixValid (2048 + n.val) → sixCertificate (2048 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck3 :
    ∀ n : Fin 1024, sixValid (3072 + n.val) → sixCertificate (3072 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck4 :
    ∀ n : Fin 1024, sixValid (4096 + n.val) → sixCertificate (4096 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck5 :
    ∀ n : Fin 1024, sixValid (5120 + n.val) → sixCertificate (5120 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck6 :
    ∀ n : Fin 1024, sixValid (6144 + n.val) → sixCertificate (6144 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck7 :
    ∀ n : Fin 1024, sixValid (7168 + n.val) → sixCertificate (7168 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck8 :
    ∀ n : Fin 1024, sixValid (8192 + n.val) → sixCertificate (8192 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck9 :
    ∀ n : Fin 1024, sixValid (9216 + n.val) → sixCertificate (9216 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck10 :
    ∀ n : Fin 1024, sixValid (10240 + n.val) → sixCertificate (10240 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck11 :
    ∀ n : Fin 1024, sixValid (11264 + n.val) → sixCertificate (11264 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck12 :
    ∀ n : Fin 1024, sixValid (12288 + n.val) → sixCertificate (12288 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck13 :
    ∀ n : Fin 1024, sixValid (13312 + n.val) → sixCertificate (13312 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck14 :
    ∀ n : Fin 1024, sixValid (14336 + n.val) → sixCertificate (14336 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck15 :
    ∀ n : Fin 1024, sixValid (15360 + n.val) → sixCertificate (15360 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck16 :
    ∀ n : Fin 1024, sixValid (16384 + n.val) → sixCertificate (16384 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck17 :
    ∀ n : Fin 1024, sixValid (17408 + n.val) → sixCertificate (17408 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck18 :
    ∀ n : Fin 1024, sixValid (18432 + n.val) → sixCertificate (18432 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck19 :
    ∀ n : Fin 1024, sixValid (19456 + n.val) → sixCertificate (19456 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck20 :
    ∀ n : Fin 1024, sixValid (20480 + n.val) → sixCertificate (20480 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck21 :
    ∀ n : Fin 1024, sixValid (21504 + n.val) → sixCertificate (21504 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck22 :
    ∀ n : Fin 1024, sixValid (22528 + n.val) → sixCertificate (22528 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck23 :
    ∀ n : Fin 1024, sixValid (23552 + n.val) → sixCertificate (23552 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck24 :
    ∀ n : Fin 1024, sixValid (24576 + n.val) → sixCertificate (24576 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck25 :
    ∀ n : Fin 1024, sixValid (25600 + n.val) → sixCertificate (25600 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck26 :
    ∀ n : Fin 1024, sixValid (26624 + n.val) → sixCertificate (26624 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck27 :
    ∀ n : Fin 1024, sixValid (27648 + n.val) → sixCertificate (27648 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck28 :
    ∀ n : Fin 1024, sixValid (28672 + n.val) → sixCertificate (28672 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck29 :
    ∀ n : Fin 1024, sixValid (29696 + n.val) → sixCertificate (29696 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck30 :
    ∀ n : Fin 1024, sixValid (30720 + n.val) → sixCertificate (30720 + n.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the degree bounds and relabeling for 1024 adjacency masks.
private theorem sixCheck31 :
    ∀ n : Fin 1024, sixValid (31744 + n.val) → sixCertificate (31744 + n.val) := by
  decide

private theorem sixCertificate_all (n : Nat) (hn : n < 32768) :
    sixValid n → sixCertificate n := by
  have hall : ∀ k : Fin 32, ∀ r : Fin 1024,
      sixValid (1024 * k.val + r.val) → sixCertificate (1024 * k.val + r.val) := by
    intro k r
    fin_cases k
    · exact sixCheck0 r
    · exact sixCheck1 r
    · exact sixCheck2 r
    · exact sixCheck3 r
    · exact sixCheck4 r
    · exact sixCheck5 r
    · exact sixCheck6 r
    · exact sixCheck7 r
    · exact sixCheck8 r
    · exact sixCheck9 r
    · exact sixCheck10 r
    · exact sixCheck11 r
    · exact sixCheck12 r
    · exact sixCheck13 r
    · exact sixCheck14 r
    · exact sixCheck15 r
    · exact sixCheck16 r
    · exact sixCheck17 r
    · exact sixCheck18 r
    · exact sixCheck19 r
    · exact sixCheck20 r
    · exact sixCheck21 r
    · exact sixCheck22 r
    · exact sixCheck23 r
    · exact sixCheck24 r
    · exact sixCheck25 r
    · exact sixCheck26 r
    · exact sixCheck27 r
    · exact sixCheck28 r
    · exact sixCheck29 r
    · exact sixCheck30 r
    · exact sixCheck31 r
  let k : Fin 32 := ⟨n / 1024, by omega⟩
  let r : Fin 1024 := ⟨n % 1024, Nat.mod_lt _ (by decide)⟩
  have h : n = 1024 * k.val + r.val := by dsimp [k, r]; omega
  simpa only [← h] using hall k r


private instance (n : Nat) : DecidableRel (pathGraph n).Adj :=
  fun _ _ => decidable_of_iff _ pathGraph_adj.symm


private instance {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (G ⊕g H).Adj := by
  intro a b
  cases a <;> cases b <;> dsimp only [SimpleGraph.sum] <;> infer_instance

private def sixTargetCycleFive :
    sixTarget 0 ≃g (cycleGraph 5 ⊕g (⊥ : SimpleGraph (Fin 1))) where
  toEquiv := (finSumFinEquiv : Fin 5 ⊕ Fin 1 ≃ Fin 6).symm
  map_rel_iff' := by
    change ∀ a b, _
    decide

private def sixTargetPathSix : sixTarget 1 ≃g pathGraph 6 where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    change ∀ a b, _
    decide

private def sixTargetCycleFour : sixTarget 2 ≃g (cycleGraph 4 ⊕g pathGraph 2) where
  toEquiv := (finSumFinEquiv : Fin 4 ⊕ Fin 2 ≃ Fin 6).symm
  map_rel_iff' := by
    change ∀ a b, _
    decide

private def sixTargetCycleThree : sixTarget 3 ≃g (cycleGraph 3 ⊕g pathGraph 3) where
  toEquiv := (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm
  map_rel_iff' := by
    change ∀ a b, _
    decide

-- Transfer the checked certificate back to an arbitrary graph.
private theorem sixGraph_classification
    (H : SimpleGraph (Fin 6)) [DecidableRel H.Adj]
    (hSum : ∑ i, H.degree i = 10) (hδ : ∀ i, H.degree i ≤ 2) :
    Nonempty (H ≃g (cycleGraph 5 ⊕g (⊥ : SimpleGraph (Fin 1)))) ∨
      Nonempty (H ≃g pathGraph 6) ∨
      Nonempty (H ≃g (cycleGraph 4 ⊕g pathGraph 2)) ∨
      Nonempty (H ≃g (cycleGraph 3 ⊕g pathGraph 3)) := by
  let n := (sixEncode H).toNat
  have hn : n < 32768 := (sixEncode H).isLt
  have hG : sixGraph n = H := sixGraph_encode H
  let eH : sixGraph n ≃g H :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro a b
        change H.Adj a b ↔ (sixGraph n).Adj a b
        rw [hG] }
  have hd (i : Fin 6) : sixDegrees n i = H.degree i := by
    rw [sixDegrees_eq]
    exact (eH.degree_eq i).symm
  have hv : sixValid n := by
    constructor
    · simp only [hd]
      simpa [Fin.sum_univ_succ, Nat.add_assoc] using hSum
    · simpa only [hd] using hδ
  have hw := sixCertificate_all n hn hv
  obtain ⟨k, ⟨e⟩⟩ : ∃ k, Nonempty (sixGraph n ≃g sixTarget k) :=
    ⟨(sixWitness n).1, ⟨{
      toEquiv := Equiv.ofBijective (sixWitness n).2 hw.1
      map_rel_iff' := fun {a b} => hw.2 a b }⟩⟩
  rw [hG] at e
  fin_cases k
  · exact Or.inl ⟨sixTargetCycleFive.comp e⟩
  · exact Or.inr (Or.inl ⟨sixTargetPathSix.comp e⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨sixTargetCycleFour.comp e⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨sixTargetCycleThree.comp e⟩))

@[expose] public section

/-- A graph on six vertices with five edges and maximum degree at most two is a five-cycle
and an isolated vertex, a six-vertex path, a four-cycle and an edge, or a triangle and a
three-vertex path. -/
theorem classification_fin_six_of_five_edges
    (H : SimpleGraph (Fin 6)) [DecidableRel H.Adj]
    (hE : H.edgeSet.ncard = 5) (hδ : ∀ v, H.degree v ≤ 2) :
    Nonempty (H ≃g (cycleGraph 5 ⊕g (⊥ : SimpleGraph (Fin 1)))) ∨
      Nonempty (H ≃g pathGraph 6) ∨
      Nonempty (H ≃g (cycleGraph 4 ⊕g pathGraph 2)) ∨
      Nonempty (H ≃g (cycleGraph 3 ⊕g pathGraph 3)) := by
  apply sixGraph_classification H _ hδ
  rw [H.sum_degrees_eq_twice_card_edges, edgeFinset_card, Set.fintypeCard_eq_ncard, hE]

/-- The complement of a six-vertex graph with ten edges and minimum degree at least three
is one of the four path-and-cycle graphs in the classification of five-edge graphs. -/
theorem compl_classification_fin_six_of_ten_edges
    (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (hE : G.edgeSet.ncard = 10)
    (hδ : ∀ v, 3 ≤ G.degree v) :
    Nonempty (Gᶜ ≃g (cycleGraph 5 ⊕g (⊥ : SimpleGraph (Fin 1)))) ∨
      Nonempty (Gᶜ ≃g pathGraph 6) ∨
      Nonempty (Gᶜ ≃g (cycleGraph 4 ⊕g pathGraph 2)) ∨
      Nonempty (Gᶜ ≃g (cycleGraph 3 ⊕g pathGraph 3)) := by
  have hdeg (v : Fin 6) : Gᶜ.degree v + G.degree v = 5 := by
    have hlt := G.degree_lt_card_verts v
    rw [degree_compl, Fintype.card_fin]
    simp only [Fintype.card_fin] at hlt
    omega
  have hSumG : ∑ v, G.degree v = 20 := by
    rw [G.sum_degrees_eq_twice_card_edges, edgeFinset_card, Set.fintypeCard_eq_ncard, hE]
  have hSum : (∑ v, Gᶜ.degree v) + ∑ v, G.degree v = 30 := by
    rw [← Finset.sum_add_distrib]
    simp only [hdeg]
    decide
  have hSumCompl : ∑ v, Gᶜ.degree v = 10 := by omega
  have hECompl : Gᶜ.edgeSet.ncard = 5 := by
    rw [Gᶜ.sum_degrees_eq_twice_card_edges, edgeFinset_card,
      Set.fintypeCard_eq_ncard] at hSumCompl
    omega
  apply classification_fin_six_of_five_edges Gᶜ hECompl
  intro v
  have := hdeg v
  have := hδ v
  omega
end

end SimpleGraph

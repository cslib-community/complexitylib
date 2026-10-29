/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ThreeCNF.Exact
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import Mathlib.Data.List.GetD
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time count-preserving clause splitting

The recursive OR-gate chain agrees with an indexed traversal of the input clause, with three
clauses per gate. The certificate charges every lookup, fresh variable, copied literal and list
delimiter. Original variables keep their supplied encoding; gate variables use their unary clause
and gate indices. This mirrors the certificate for `Cslib.Logic.PL.CNF.to3CNF`.

## Main results

* `Cslib.Logic.PL.Clause.isPolyTime_orChainAux`: efficient OR-gate chains of clause tails.
* `Cslib.Logic.PL.Clause.isPolyTime_orSplit3`: efficient chains with a certified fresh-variable
  routine, retaining its captured input.
* `Cslib.Logic.PL.CNF.isPolyTime_toExact3CNF`: a uniform certificate for the count-preserving
  3CNF reduction.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Turing.MultiTapeTM ComputableInPolyTime

variable {V W Input : Type}

/-- The three clauses of the gate `z ↔ u ∨ v`. -/
private def gateClauses (u v : Literal W) (z : W) : CNF W :=
  [[(u.1, !u.2), (z, true)], [(v.1, !v.2), (z, true)], [u, v, (z, false)]]

private theorem orChainAux_eq_flatMap (fresh : ℕ → W) (j : ℕ) (carry : Literal W)
    (rest : Clause W) :
    Clause.orChainAux fresh j carry rest =
      (List.range (rest.length - 2)).flatMap (fun i =>
        gateClauses (if i = 0 then carry else (fresh (j + (i - 1)), true)) (rest.getD i carry)
          (fresh (j + i))) ++
      [(if rest.length - 2 = 0 then carry else (fresh (j + (rest.length - 2 - 1)), true)) ::
        rest.drop (rest.length - 2)] := by
  induction j, carry, rest using Clause.orChainAux.induct fresh with
  | case1 j carry b c d rest ih =>
    rw [Clause.orChainAux, ih]
    have htwo : (c :: d :: rest).length - 2 = rest.length := by
      simp [Nat.add_assoc]
    have hthree : (b :: c :: d :: rest).length - 2 = rest.length + 1 := by
      simp [Nat.add_assoc]
    simp only [htwo, hthree, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      ite_true, List.getD_cons_zero, Nat.add_zero, List.cons_append, List.drop_succ_cons,
      Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one, gateClauses,
      List.nil_append]
    have hcarry (i : ℕ) :
        (if i = 0 then (fresh j, true) else (fresh (j + 1 + (i - 1)), true)) =
          ((fresh (j + i), true) : Literal W) := by
      cases i <;> simp [Nat.add_comm, Nat.add_left_comm]
    congr 3
    apply congrArg₂ List.append
    · apply List.flatMap_congr
      intro i hi
      have hi' : i < (c :: d :: rest).length := by
        simp only [List.mem_range] at hi
        simp only [List.length_cons]
        lia
      rw [hcarry i, List.getD_cons_succ, List.getD_eq_getElem _ _ hi',
        List.getD_eq_getElem _ _ hi']
      simp [Nat.add_right_comm, Nat.add_assoc, Nat.succ_eq_add_one]
    · cases rest <;> simp [Nat.add_assoc, Nat.add_comm 1]
  | case2 j carry rest hrest =>
    match rest, hrest with
    | [], _ | [_], _ | [_, _], _ => simp [Clause.orChainAux]
    | _ :: _ :: _ :: _, hrest => exact absurd rfl (hrest _ _ _ _)

private theorem gateClauses_polyTime {In : Type} {encIn : In ↪ List Bool} {enc : W ↪ List Bool}
    {u v : In → Literal W} {z : In → W}
    (hu : ComputableInPolyTime u encIn (encPair enc encBool))
    (hv : ComputableInPolyTime v encIn (encPair enc encBool))
    (hz : ComputableInPolyTime z encIn enc) :
    ComputableInPolyTime (fun x => gateClauses (u x) (v x) (z x)) encIn
      (encList (encList (encPair enc encBool))) := by
  unfold gateClauses
  fun_prop

/-- The OR-gate chain of a clause tail, with a certified fresh-variable routine and runtime gate
index. -/
@[fun_prop]
theorem Clause.isPolyTime_orChainAux {input : Input ↪ List Bool} {enc : W ↪ List Bool}
    {fresh : Input → ℕ → W} {index : Input → ℕ} {carry : Input → Literal W}
    {rest : Input → Clause W}
    (hrest : ComputableInPolyTime rest input (encList (encPair enc encBool)))
    (hcarry : ComputableInPolyTime carry input (encPair enc encBool))
    (hindex : ComputableInPolyTime index input encUnary)
    (hfresh : ComputableInPolyTime (fun p : Input × ℕ => fresh p.1 p.2)
      (encPair input encUnary) enc) :
    ComputableInPolyTime (fun x => Clause.orChainAux (fresh x) (index x) (carry x) (rest x))
      input (encList (encList (encPair enc encBool))) := by
  have hdrop : ComputableInPolyTime (fun x => (rest x).drop ((rest x).length - 2))
      input (encList (encPair enc encBool)) :=
    (dropUnary (encA := encPair enc encBool)).comp (hrest.prod (by fun_prop))
  have hu : ComputableInPolyTime (fun p : Input × ℕ =>
      if p.2 = 0 then carry p.1 else ((fresh p.1 (index p.1 + (p.2 - 1)), true) : Literal W))
      (encPair input encUnary) (encPair enc encBool) := by
    fun_prop
  have hv : ComputableInPolyTime (fun p : Input × ℕ => ((rest p.1)[p.2]?).getD (carry p.1))
      (encPair input encUnary) (encPair enc encBool) := by
    fun_prop
  have hz : ComputableInPolyTime (fun p : Input × ℕ => fresh p.1 (index p.1 + p.2))
      (encPair input encUnary) enc := by
    fun_prop
  have hflat := ComputableInPolyTime.flatMapWithInput
    (list := fun x => List.range ((rest x).length - 2))
    (f := fun x i => gateClauses
      (if i = 0 then carry x else ((fresh x (index x + (i - 1)), true) : Literal W))
      (((rest x)[i]?).getD (carry x)) (fresh x (index x + i)))
    (by fun_prop) (gateClauses_polyTime hu hv hz)
  simp_rw [orChainAux_eq_flatMap, List.getD_eq_getElem?_getD]
  fun_prop

/-- The OR-gate chain of a computed clause retains the input captured by its fresh-variable
routine. -/
@[fun_prop]
theorem Clause.isPolyTime_orSplit3 {input : Input ↪ List Bool} {enc : W ↪ List Bool}
    {fresh : Input → ℕ → W} {index : Input → ℕ} {clause : Input → Clause W}
    (hclause : ComputableInPolyTime clause input (encList (encPair enc encBool)))
    (hindex : ComputableInPolyTime index input encUnary)
    (hfresh : ComputableInPolyTime (fun p : Input × ℕ => fresh p.1 p.2)
      (encPair input encUnary) enc) :
    ComputableInPolyTime (fun x => Clause.orSplit3 (fresh x) (index x) (clause x))
      input (encList (encList (encPair enc encBool))) := by
  have heq (f : ℕ → W) (j : ℕ) (c : Clause W) : Clause.orSplit3 f j c =
      c.head?.elim [[]] (fun carry => Clause.orChainAux f j carry c.tail) := by
    cases c <;> rfl
  simp_rw [heq]
  apply optionElimWithInput (encB := encPair enc encBool) (by fun_prop) (by fun_prop)
  exact Clause.isPolyTime_orChainAux (input := encPair input (encPair enc encBool))
    (fresh := fun p => fresh p.1) (index := fun p => index p.1) (carry := fun p => p.2)
    (rest := fun p => (clause p.1).tail) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop)

/-- Convert an arbitrary CNF formula to 3CNF with the same number of models, encoding gate
variables by unary clause and gate indices. The certificate includes relabelling, clause
traversal and all output copying. -/
@[fun_prop]
theorem CNF.isPolyTime_toExact3CNF (enc : V ↪ List Bool) :
    ComputableInPolyTime (CNF.toExact3CNF (V := V))
      (encList (encList (encPair enc encBool)))
      (encList (encList (encPair (encSum enc (encPair encUnary encUnary)) encBool))) := by
  have hsplit : ComputableInPolyTime
      (fun p : CNF V × (Clause V × ℕ) => Clause.orSplit3 (fun j => Sum.inr (p.2.2, j)) 0
        (Clause.relabel Sum.inl p.2.1))
      (encPair (encList (encList (encPair enc encBool)))
        (encPair (encList (encPair enc encBool)) encUnary))
      (encList (encList (encPair (encSum enc (encPair encUnary encUnary)) encBool))) :=
    Clause.isPolyTime_orSplit3
      ((Clause.computableInPolyTime_relabel (by fun_prop)).comp
        (by fun_prop)) (by fun_prop) (by fun_prop)
  unfold CNF.toExact3CNF
  fun_prop

end Cslib.Logic.PL

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ThreeCNF
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
# Polynomial-time clause splitting

The existing recursive splitter agrees with an indexed traversal of the input clause. The
certificate charges every lookup, fresh variable, copied literal, and list delimiter. Original
variables keep their supplied encoding; fresh variables use their unary clause and chain indices.

## Main results

* `Cslib.Logic.PL.Clause.isPolyTime_splitAux`: efficient splitting of clause tails.
* `Cslib.Logic.PL.Clause.isPolyTime_split3`: efficient splitting with a certified fresh-variable
  routine, retaining its captured input.
* `Cslib.Logic.PL.CNF.isPolyTime_to3CNF`: a uniform certificate for the existing 3CNF reduction.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.3.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Turing.MultiTapeTM ComputableInPolyTime

variable {V W Input : Type}

private theorem splitAux_eq_map (fresh : ℕ → W) (j : ℕ) (carry : Literal W)
    (rest : Clause W) :
    Clause.splitAux fresh j carry rest =
      (List.range (rest.length - 2)).map (fun i =>
        [if i = 0 then carry else (fresh (j + (i - 1)), false), rest.getD i carry,
          (fresh (j + i), true)]) ++
      [(if rest.length - 2 = 0 then carry else (fresh (j + (rest.length - 2 - 1)), false)) ::
        rest.drop (rest.length - 2)] := by
  induction j, carry, rest using Clause.splitAux.induct fresh with
  | case1 j carry b c d rest ih =>
    rw [Clause.splitAux, ih]
    have htwo : (c :: d :: rest).length - 2 = rest.length := by
      simp [Nat.add_assoc]
    have hthree : (b :: c :: d :: rest).length - 2 = rest.length + 1 := by
      simp [Nat.add_assoc]
    simp only [htwo, hthree, List.range_succ_eq_map, List.map_cons, List.map_map,
      Function.comp_def, ite_true, List.getD_cons_zero, Nat.add_zero, List.cons_append,
      List.drop_succ_cons, Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one]
    congr 1
    have hcarry (i : ℕ) :
        (if i = 0 then (fresh j, false) else (fresh (j + 1 + (i - 1)), false)) =
          (fresh (j + i), false) := by
      cases i <;> simp [Nat.add_comm, Nat.add_left_comm]
    apply congrArg₂ List.append
    · apply List.map_congr_left
      intro i hi
      have hi' : i < (c :: d :: rest).length := by
        simp only [List.mem_range] at hi
        simp only [List.length_cons]
        lia
      rw [hcarry i, List.getD_cons_succ, List.getD_eq_getElem _ _ hi',
        List.getD_eq_getElem _ _ hi']
      simp [Nat.add_right_comm, Nat.add_assoc]
    · rw [hcarry]
  | case2 j carry rest hrest =>
    match rest, hrest with
    | [], _ | [_], _ | [_, _], _ => simp [Clause.splitAux]
    | _ :: _ :: _ :: _, hrest => exact absurd rfl (hrest _ _ _ _)

/-- Split a clause tail with a certified fresh-variable routine and runtime chain index. -/
@[fun_prop]
theorem Clause.isPolyTime_splitAux {input : Input ↪ List Bool} {enc : W ↪ List Bool}
    {fresh : Input → ℕ → W} {index : Input → ℕ} {carry : Input → Literal W}
    {rest : Input → Clause W}
    (hrest : ComputableInPolyTime rest input (encList (encPair enc encBool)))
    (hcarry : ComputableInPolyTime carry input (encPair enc encBool))
    (hindex : ComputableInPolyTime index input encUnary)
    (hfresh : ComputableInPolyTime (fun p : Input × ℕ => fresh p.1 p.2)
      (encPair input encUnary) enc) :
    ComputableInPolyTime (fun x => Clause.splitAux (fresh x) (index x) (carry x) (rest x))
      input (encList (encList (encPair enc encBool))) := by
  have hdrop : ComputableInPolyTime (fun x => (rest x).drop ((rest x).length - 2))
      input (encList (encPair enc encBool)) :=
    (dropUnary (encA := encPair enc encBool)).comp (hrest.prod (by fun_prop))
  simp_rw [splitAux_eq_map, List.getD_eq_getElem?_getD]
  fun_prop

/-- Splitting a computed clause retains the input captured by its fresh-variable routine. -/
@[fun_prop]
theorem Clause.isPolyTime_split3 {input : Input ↪ List Bool} {enc : W ↪ List Bool}
    {fresh : Input → ℕ → W} {index : Input → ℕ} {clause : Input → Clause W}
    (hclause : ComputableInPolyTime clause input (encList (encPair enc encBool)))
    (hindex : ComputableInPolyTime index input encUnary)
    (hfresh : ComputableInPolyTime (fun p : Input × ℕ => fresh p.1 p.2)
      (encPair input encUnary) enc) :
    ComputableInPolyTime (fun x => Clause.split3 (fresh x) (index x) (clause x))
      input (encList (encList (encPair enc encBool))) := by
  have heq (f : ℕ → W) (j : ℕ) (c : Clause W) : Clause.split3 f j c =
      c.head?.elim [[]] (fun carry => Clause.splitAux f j carry c.tail) := by
    cases c <;> rfl
  simp_rw [heq]
  apply optionElimWithInput (encB := encPair enc encBool) (by fun_prop) (by fun_prop)
  exact Clause.isPolyTime_splitAux (input := encPair input (encPair enc encBool))
    (fresh := fun p => fresh p.1) (index := fun p => index p.1) (carry := fun p => p.2)
    (rest := fun p => (clause p.1).tail) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop)

/-- Convert an arbitrary CNF formula to 3CNF, encoding fresh variables by unary clause and
chain indices. The certificate includes relabelling, clause traversal, and all output copying. -/
@[fun_prop]
theorem CNF.isPolyTime_to3CNF (enc : V ↪ List Bool) :
    ComputableInPolyTime (CNF.to3CNF (V := V))
      (encList (encList (encPair enc encBool)))
      (encList (encList (encPair (encSum enc (encPair encUnary encUnary)) encBool))) := by
  have hsplit : ComputableInPolyTime
      (fun p : CNF V × (Clause V × ℕ) => Clause.split3 (fun j => Sum.inr (p.2.2, j)) 0
        (Clause.relabel Sum.inl p.2.1))
      (encPair (encList (encList (encPair enc encBool)))
        (encPair (encList (encPair enc encBool)) encUnary))
      (encList (encList (encPair (encSum enc (encPair encUnary encUnary)) encBool))) :=
    Clause.isPolyTime_split3
      ((Clause.computableInPolyTime_relabel (by fun_prop)).comp
        (by fun_prop)) (by fun_prop) (by fun_prop)
  unfold CNF.to3CNF
  fun_prop

end Cslib.Logic.PL

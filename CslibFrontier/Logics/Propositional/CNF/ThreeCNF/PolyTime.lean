/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ThreeCNF
public import CslibFrontier.Logics.Propositional.CNF.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Foundations.Data.List.EmitChain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

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

public section

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
  have h := List.eq_flatMap_range_of_emit (Clause.splitAux fresh)
    (fun j => (fresh j, false)) (fun j u v => [[u, v, (fresh j, true)]])
    (fun carry rest => [carry :: rest]) 2
    (fun j carry rest hs => by
      match rest with
      | [] | [_] | [_, _] => rfl
      | _ :: _ :: _ :: _ => simp only [List.length_cons] at hs; omega)
    (fun j carry b rest hs => by
      match rest with
      | [] | [_] => simp only [List.length_cons, List.length_nil] at hs; omega
      | _ :: _ :: _ => rfl) j carry rest
  simpa only [← List.map_eq_flatMap] using h

/-- Split a clause tail with a certified fresh-variable routine and runtime chain index. -/
@[fun_prop]
theorem Clause.isPolyTime_splitAux {input : Input ↪ List Bool} {enc : W ↪ List Bool}
    {fresh : Input → ℕ → W} {index : Input → ℕ} {carry : Input → Literal W}
    {rest : Input → Clause W}
    (hrest : ComputableInPolyTime rest input (encClause enc))
    (hcarry : ComputableInPolyTime carry input (encPair enc encBool))
    (hindex : ComputableInPolyTime index input encUnary)
    (hfresh : ComputableInPolyTime (fun p : Input × ℕ => fresh p.1 p.2)
      (encPair input encUnary) enc) :
    ComputableInPolyTime (fun x => Clause.splitAux (fresh x) (index x) (carry x) (rest x))
      input (encCNFOver enc) := by
  have hdrop : ComputableInPolyTime (fun x => (rest x).drop ((rest x).length - 2))
      input (encList (encPair enc encBool)) :=
    (dropUnary (encA := encPair enc encBool)).comp (hrest.prod (by fun_prop))
  simp_rw [splitAux_eq_map, List.getD_eq_getElem?_getD]
  fun_prop

/-- Splitting a computed clause retains the input captured by its fresh-variable routine. -/
@[fun_prop]
theorem Clause.isPolyTime_split3 {input : Input ↪ List Bool} {enc : W ↪ List Bool}
    {fresh : Input → ℕ → W} {index : Input → ℕ} {clause : Input → Clause W}
    (hclause : ComputableInPolyTime clause input (encClause enc))
    (hindex : ComputableInPolyTime index input encUnary)
    (hfresh : ComputableInPolyTime (fun p : Input × ℕ => fresh p.1 p.2)
      (encPair input encUnary) enc) :
    ComputableInPolyTime (fun x => Clause.split3 (fresh x) (index x) (clause x))
      input (encCNFOver enc) := by
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
      (encCNFOver enc) (encCNFOver (encSum enc (encPair encUnary encUnary))) := by
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

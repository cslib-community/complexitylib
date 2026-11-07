/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.CookLevin.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Window
import Complexity.Tactic.PolyTime

/-!
# Cook–Levin construction tests

The constructor certificates must compose through the reduction's actual parameters and emit
the binary encoding of SAT. A concrete zero-work-tape machine checks that the machine parameters
are inhabited; certificate variables remain available even for an empty control-state type.
-/

namespace ComplexityTests.CookLevinPolyTime

open Turing.MultiTapeTM Cslib.Complexity Cslib.Complexity.CookLevin

example {k : ℕ} {State : Type} [Fintype State] (tm : Turing.MultiTapeTM k Bool State) :
    ComputableInPolyTime
      (fun T => (initClauses tm T ++ sitClauses T ++ acceptClauses T).relabel Var.index)
      encUnary encCNF := by
  have hinit := computableInPolyTime_initClauses tm
  have hsit := computableInPolyTime_sitClauses (k := k) (State := State)
  have haccept := computableInPolyTime_acceptClauses (k := k) (State := State)
  polytime

-- Fixed tape/symbol traversals combine with input-dependent windows and nested lists.
example {k : ℕ} {State : Type} [Fintype State] :
    ComputableInPolyTime
      (fun p : ℕ × ℕ => Feature.groups (k := k) (State := State) p.1 p.2)
      (encPair encUnary encUnary) (encList (encList encFeature)) := by
  fun_prop

-- Exactly-one constraints compose with the existing binary variable numbering.
example {k : ℕ} {State : Type} [Fintype State] [DecidableEq State] :
    ComputableInPolyTime
      (fun p : ((List Bool × ℕ) × ℕ) × ℕ =>
        (oneHotClauses (k := k) (State := State) p.1.1.1 p.1.1.2 p.1.2 p.2).relabel Var.index)
      (encPair (encPair (encPair encBits encUnary) encUnary) encUnary) encCNF := by
  fun_prop

-- The full reducible tuple composes without a specialized `Prod.mk` search rule.
example {α : Type} (enc : α ↪ List Bool) (p : Polynomial ℕ) (c d : ℕ) :
    ComputableInPolyTime (parameters p c d enc)
      enc (encPair encBits (encPair encUnary encUnary)) := by
  fun_prop

-- The input encoding, polynomial and machine are fixed parameters of the reduction.
example {k : ℕ} {State α : Type} [Fintype State]
    (tm : Turing.MultiTapeTM k Bool State) (enc : α ↪ List Bool)
    (p : Polynomial ℕ) (c d : ℕ) :
    ComputableInPolyTime
      (fun a => (initClauses tm (parameters p c d enc a).2.2).relabel Var.index)
      enc encCNF := by
  fun_prop

private def finish : Turing.MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ _ _ => ⟨0, Fin.elim0, some true, none⟩

-- Concrete machine parameterizations and complete reduction witnesses.
example :
    ComputableInPolyTime (fun T => (initClauses finish T).relabel Var.index) encUnary encCNF ∧
    ComputableInPolyTime
      (fun n => (oneHotClauses (k := 0) (State := Unit) [] n n n).relabel Var.index)
      encUnary encCNF ∧
    ComputableInPolyTime
      (fun j => (Var.cert (k := 0) (State := Empty) j).index) encUnary encNat ∧
    ComputableInPolyTime (reduce finish (Polynomial.X + 1) 3 2 encBits) encBits encCNF :=
  ⟨by fun_prop, by fun_prop [oneHotClauses], by fun_prop, by fun_prop⟩

-- A computed tableau and the same computation through a tuple or generic list encoding all emit
-- binary SAT instances.
example :
    ComputableInPolyTime (fun word : List Bool =>
      (tableau finish word (word.length + 1) (word.length ^ 2 + 2)).relabel Var.index)
      encBits encCNF ∧
    ComputableInPolyTime (fun word : List Bool =>
      (tableau finish word (word.length + 1) (word.length ^ 2 + 2)).relabel Var.index)
      (encList encBool) encCNF ∧
    ComputableInPolyTime (fun q : List Bool × ℕ × ℕ =>
      (tableau finish q.1 q.2.1 q.2.2).relabel Var.index)
      (encPair encBits (encPair encUnary encUnary)) encCNF :=
  ⟨by polytime, by polytime, by fun_prop⟩

-- Fixed parameter lists need no encoding or finiteness instance for their element type, whether
-- selected via `filter` or `flatMap`; plain automation supplies both certificates directly.
example {ι : Type} (parameters : List ι) (weight : ι → ℕ) :
    ComputableInPolyTime (fun n =>
      (parameters.filter (fun i => decide (weight i ≤ n))).map
        (fun i => List.replicate (n + weight i) true))
      encUnary (encList encBits) ∧
    ComputableInPolyTime (fun n => parameters.flatMap fun i =>
      if weight i ≤ n then [List.replicate (n + weight i) true] else [])
      encUnary (encList encBits) :=
  ⟨by fun_prop, by fun_prop⟩

-- Total input-head movement clips even an out-of-range starting position.
example : Turing.moveInputPosNat 0 9 .neg = 1 ∧
    Turing.moveInputPosNat 0 9 .zero = 1 ∧ Turing.moveInputPosNat 0 9 .pos = 1 ∧
    Turing.moveInputPosNat 3 0 .neg = 0 := by decide

example :
    ComputableInPolyTime
      (fun p : ℕ × ℤ => decide (|p.2 - (-1 : SignType)| ≤ (p.1 : ℤ)))
      (encPair encUnary encInt) encBool ∧
    PolyTimeReducible encBits encCNF {w : List Bool | w.headD false = true} SAT ∧
    PolyTimeReducible encBits encCNF {w : List Bool | w.headD false = true} UNSAT :=
  ⟨by fun_prop,
   SAT_npComplete.2 encBits _
     (P_subset_NP ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩),
   UNSAT_coNPComplete.2 encBits _
     (P_subset_coNP ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩)⟩

end ComplexityTests.CookLevinPolyTime

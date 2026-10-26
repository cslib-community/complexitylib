/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.CNF.ThreeCNF.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
import Complexity.Tactic.PolyTime

/-! Efficient exact clause splitting with captured fresh variables and arbitrary encodings. -/

namespace ComplexityTests.ThreeCNFPolyTime

open Cslib.Logic.PL Turing.MultiTapeTM

-- The empty formula and the empty clause retain their different meanings.
example : CNF.to3CNF ([] : CNF ℕ) = [] := rfl
example : CNF.to3CNF ([[]] : CNF ℕ) = [[]] := rfl

-- The first nontrivial split starts its fresh-variable counter at the supplied runtime index.
example : Clause.split3 (fun i : ℕ => i + 100) 7
    [(0, true), (1, false), (2, true), (3, false)] =
      [[(0, true), (1, false), (107, true)], [(107, false), (2, true), (3, false)]] := rfl

example : ComputableInPolyTime
    (fun p : ℕ × Clause ℕ => Clause.split3 (fun i => p.1 + i) p.1 p.2)
    (encPair encUnary (encList (encPair encUnary encBool)))
    (encList (encList (encPair encUnary encBool))) := by fun_prop

-- Binary original names coexist with unary fresh clause and chain indices.
example : ComputableInPolyTime (CNF.to3CNF (V := ℕ))
    (encList (encList (encPair encNat encBool)))
    (encList (encList (encPair (encSum encNat (encPair encUnary encUnary)) encBool))) := by
  fun_prop

-- No inhabitant of the original variable type is required.
example (empty : Empty ↪ List Bool) : ComputableInPolyTime (CNF.to3CNF (V := Empty))
    (encList (encList (encPair empty encBool)))
    (encList (encList (encPair (encSum empty (encPair encUnary encUnary)) encBool))) := by
  fun_prop

section Captured

variable {W Input : Type} (input : Input ↪ List Bool) (enc : W ↪ List Bool)
  (fresh : Input → ℕ → W) (index : Input → ℕ) (clause : Input → Clause W)
  (hclause : ComputableInPolyTime clause input (encList (encPair enc encBool)))
  (hindex : ComputableInPolyTime index input encUnary)
  (hfresh : ComputableInPolyTime (fun p : Input × ℕ => fresh p.1 p.2)
    (encPair input encUnary) enc)

example : ComputableInPolyTime
    (fun x => Clause.split3 (fresh x) (index x) (clause x))
    input (encList (encList (encPair enc encBool))) := by
  fail_if_success (clear hclause; fun_prop)
  fail_if_success (clear hindex; fun_prop)
  fail_if_success (clear hfresh; fun_prop)
  fun_prop

example : ComputableInPolyTime
    (fun x => let c := clause x; let start := index x; Clause.split3 (fresh x) start (c ++ c))
    input (encList (encList (encPair enc encBool))) := by fun_prop

end Captured

example {V Input : Type} (enc : V ↪ List Bool) (input : Input ↪ List Bool)
    (formula : Input → CNF V)
    (hformula : ComputableInPolyTime formula input
      (encList (encList (encPair enc encBool)))) :
    ComputableInPolyTime (fun x => let φ := formula x; φ.to3CNF)
      input (encList (encList (encPair (encSum enc (encPair encUnary encUnary)) encBool))) := by
  fail_if_success (clear hformula; fun_prop)
  fun_prop

example (φ : CNF ℕ) : φ.to3CNF.Satisfiable ↔ φ.Satisfiable := CNF.satisfiable_to3CNF φ

end ComplexityTests.ThreeCNFPolyTime

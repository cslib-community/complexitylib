/-
Copyright (c) 2026 Anton Kovsharov, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Logics.Propositional.CNF.ModelCount.Declared
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time declared-input check

The declared-input guard `Cslib.Logic.PL.CNF.validDeclaredInput k N φ` checks that every clause
of `φ` has width at most `k` and every variable of `φ` is below the declared bound `N`. This
module shows that the guard is polynomial-time computable on `encPair encP encCNF` when the
declared bound is computed from the parameter in unary. Both the native sparse leaf counter and the
uniform counting-sparsification resources use it.

## Main results

* `Cslib.Logic.PL.CNF.computableInPolyTime_validDeclaredInput`: the declared-input check is
  `ComputableInPolyTime` when the declared variable bound is.
-/

public section

namespace Cslib.Logic.PL.CNF

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

variable {P : Type} {encP : P ↪ List Bool} {NOf : P → ℕ}

/-- The declared-input check `validDeclaredInput k (NOf p) φ` is computable in polynomial time
when the declared variable bound `NOf` is. -/
theorem computableInPolyTime_validDeclaredInput (k : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) :
    ComputableInPolyTime (fun x : P × CNF ℕ => validDeclaredInput k (NOf x.1) x.2)
      (encPair encP encCNF) encBool := by
  have hN_nat := unary_to_binary.comp' (hNOf.comp' (fst encP encCNF))
  have h1 := allWithEncoding
    (unary_le' (SAT.computableInPolyTime_clause_length
      (snd (encPair encP encCNF) (encList (encPair encNat encBool)))) (.const k))
    id' (snd encP (encList (encList (encPair encNat encBool))))
  have h2 := allWithEncoding
    (binary_lt' (snd (encPair encP encCNF) encNat)
      (hN_nat.comp' (fst (encPair encP encCNF) encNat)))
    id' (SAT.computableInPolyTime_vars.comp' (snd encP encCNF))
  exact h1.bool_and' h2

end Cslib.Logic.PL.CNF

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Replacement

/-! The logical replacement API is available through its ordinary import without native runtime. -/

namespace CslibFrontierTests.PPGadgetReplacement

open Cslib.Logic.PL Cslib.Logic.PL.CSP

example : instantiate 3 2 [2 ^ 250, 2 ^ 250]
    ([⟨(), [(false, 1), (true, 2), (false, 0)]⟩] : CSP Unit (Bool × ℕ)) =
    [⟨(), [2 * 2 ^ 250, 17, 2 * 2 ^ 250]⟩] := by decide +kernel

example : replaceGadgets 3
    (fun (_ : Unit) => ([⟨(), [(false, 0), (true, 1)]⟩] : CSP Unit (Bool × ℕ)))
    [⟨(), [7]⟩, ⟨(), [7]⟩] = [⟨(), [14, 3]⟩, ⟨(), [14, 9]⟩] := by decide

example : replaceGadgets 0 (Empty.elim : Empty → CSP Empty (Bool × ℕ)) [] = [] := rfl

example {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ)
    (hF : WellFormed srcArity F) :
    (replaceGadgets B (fun r => (gadgets r).template) F).Satisfiable sem ↔
      F.Satisfiable srcSem :=
  satisfiable_replaceGadgets_iff gadgets B hB F hF

/-- info: Unknown identifier `Cslib.Complexity.CSP.computableInPolyTime_instantiate` -/
#guard_msgs in
#check_failure Cslib.Complexity.CSP.computableInPolyTime_instantiate

end CslibFrontierTests.PPGadgetReplacement

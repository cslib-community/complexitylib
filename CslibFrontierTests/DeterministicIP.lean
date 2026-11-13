/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.IP.Deterministic
import CslibFrontier.Computability.Complexity.Reduction

/-!
# Deterministic interactive proofs and perfect soundness: clients

* The replaying prover on an explicit one-message program: replaying an accepting history
  accepts with probability `1`. The history must answer the message that the program actually
  sends; a history with another message is invalid.
* `dIP` is not vacuous: every problem in `P` is in `dIP`, through `dIP_eq_NP`, and so in `IP`.
-/

public section

namespace CslibFrontierTests.DeterministicIP

open Cslib Cslib.Complexity Cslib.Complexity.Interaction Turing.MultiTapeTM

/-- A one-message program: send `[true]` and accept when the reply is `[false]`. -/
def askOnce : WordQueryComp Unit Bool :=
  (fun y => decide (y = [false])) <$> OracleComp.query ((), [true])

/-- The accepting history of `askOnce`. -/
example : outcome askOnce [([true], [false])] = .done true := by
  decide +kernel

/-- A history that replies with the wrong word is followed but rejects. -/
example : outcome askOnce [([true], [true])] = .done false := by
  decide +kernel

/-- A history that records another message is invalid: the program sends `[true]`. -/
example : outcome askOnce [([false], [false])] = .invalid := by
  decide +kernel

/-- Replaying the accepting history makes `askOnce` accept with probability one. -/
example : acceptFrom (historyProver []) [([true], [false])] (some askOnce) = 1 :=
  acceptFrom_historyProver [] (by decide +kernel)

/-- `dIP` is not vacuous: problems in `P` have deterministic interactive proofs. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} (hA : A ∈ P enc) : A ∈ dIP enc :=
  (dIP_eq_NP enc).symm ▸ P_subset_NP hA

/-- Every Boolean-valued polynomial-time property is in `dIP`, hence in `IP`. -/
example : {w : List Bool | w.headD false = true} ∈ IP encBits :=
  dIP_subset_IP encBits <| (dIP_eq_NP encBits).symm ▸ P_subset_NP
    ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

end CslibFrontierTests.DeterministicIP

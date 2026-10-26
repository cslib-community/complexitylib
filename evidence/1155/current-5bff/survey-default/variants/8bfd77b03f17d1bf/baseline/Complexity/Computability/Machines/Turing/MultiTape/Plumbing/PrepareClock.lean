/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
import Complexity.Computability.Machines.Turing.MultiTape.Run

/-!
# Preparing a polynomial clock with the tidy calculus

The budget is an ordinary functional program: compute a fixed polynomial in the input length
and write that many true bits. Its efficiency follows from `fun_prop`; the existing output
redirection and rewind compiler puts the result on a work tape. The resulting finite machine
starts with blank tapes, halts, restores the input and all heads, leaves its scratch tapes blank,
and emits nothing. Its polynomial bound charges both generation and rewinding.

## Main definitions

* `Turing.MultiTapeTM.PolynomialClock.budget`: a unary monomial execution budget.

## Main results

* `Turing.MultiTapeTM.PolynomialClock.computableTidilyInPolyTime_budget`: the functional generator
  has a uniform polynomial-time TM certificate.
* `Turing.MultiTapeTM.PolynomialClock.exists_prepare`: a finite machine prepares the budget on
  its last work tape, within one polynomial bound for every input.

## References

This serves the role of MultiTape/Plumbing/PrepareClock.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing Christian Reitwiessner's tidy calculus and
the existing output-to-word compiler instead of a separate polynomial generator.
-/

@[expose] public section

namespace Turing.MultiTapeTM.PolynomialClock

/-- Unary execution budget, with coefficient and degree fixed independently of the input. -/
def budget (coefficient degree : ℕ) (input : List Bool) : List Bool :=
  List.replicate (coefficient * (input.length + 1) ^ degree) true

/-- Generate the budget using the existing functional polynomial-time calculus. -/
@[fun_prop] theorem computableTidilyInPolyTime_budget (coefficient degree : ℕ) :
    ComputableTidilyInPolyTime (budget coefficient degree) encBits encBits := by
  have h : ComputableTidilyInPolyTime
      (fun input : List Bool => coefficient * (input.length + 1) ^ degree)
      encBits encUnary := by fun_prop
  exact h.of_enc_eq (fun _ => rfl)

/-- Prepare and rewind a budget from blank tapes, restoring every scratch tape and emitting
nothing. The finite machine and its polynomial bound are uniform over all input words. -/
theorem exists_prepare (coefficient degree : ℕ) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeTM (k + 1) Bool State)
      (c d : ℕ), ∀ input,
      machine.runFrom (machine.initCfg input) (c * (input.length + 1) ^ d) =
        wordsCfg input none (Function.update (fun _ => []) (Fin.last k)
          (budget coefficient degree input)) [] := by
  obtain ⟨t, s, ht, _, k, State, hfinite, machine, hmachine⟩ :=
    computableTidilyInPolyTime_budget coefficient degree
  have hlength : PolyBounded List.length (fun input => (budget coefficient degree input).length) :=
    .of_forall_le coefficient degree (fun _ => by simp [budget])
  obtain ⟨c, d, hbound⟩ := ((ht.add hlength).add (PolyBounded.const 2)).exists_le
  refine ⟨k, State ⊕ RewindWorkState, inferInstance, machine.outputToWord, c, d, fun input => ?_⟩
  have hcompute : machine.ComputesTidilyInTimeAndSpace input (budget coefficient degree input)
      (t input) (s input) := hmachine input
  have hwrite := hcompute.outputToWord.mono (hbound input) le_rfl
  obtain ⟨_, _, hrun, ⟨rfl, rfl⟩, _⟩ :=
    transformsTapes_iff_runFrom.mp hwrite input (fun _ => []) [] ⟨rfl, rfl⟩
  simpa only [initCfg_eq_wordsCfg, encBits_apply, List.nil_append] using hrun

end Turing.MultiTapeTM.PolynomialClock

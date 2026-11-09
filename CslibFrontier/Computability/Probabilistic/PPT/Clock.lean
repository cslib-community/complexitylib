/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.PolynomialClock

/-!
# Intrinsically halting PPT realizations

Every strict clocked PPT certificate admits a finite machine that actually halts in polynomial
time with the same output distribution. The clock compiler starts with blank tapes and charges
preparation of its unary budget. Its bound and finite control are uniform over all inputs.

## Main results

* `Turing.MultiTapePTM.exists_halting_clock`: compile a polynomial cutoff under fair-coin semantics.
* `Cslib.Probability.IsPPTOn.exists_halting_machine`: choose an intrinsically halting PPT witness.

## References

Adapts Computability/Probabilistic/Clock.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the common machine compilers and existing
tidy functional budget generation.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib

/-- A polynomial cutoff can be implemented by a finite machine that halts under fair-coin
semantics, with one polynomial bound on all inputs and every supported execution. -/
theorem exists_halting_clock {k : ℕ} {State : Type} [Finite State]
    (machine : MultiTapePTM k Bool State) (coefficient degree : ℕ) :
    ∃ (k' : ℕ) (State' : Type) (_ : Finite State') (target : MultiTapePTM k' Bool State')
      (c d : ℕ), ∀ input,
      ProbComp.eval (target.runClosed (c * (input.length + 1) ^ d) input) =
        ProbComp.eval (machine.runClosed (coefficient * (input.length + 1) ^ degree) input) ∧
      ∀ final ∈ (ProbComp.eval (target.runConfigFrom (ProbComp.uniform Bool) Empty.elim
        (c * (input.length + 1) ^ d) (target.initialConfig input))).support,
        final.tapes.state = none := by
  obtain ⟨k', State', hfinite, target, c, d, htarget⟩ :=
    machine.exists_polynomialClock coefficient degree
  refine ⟨k', State', hfinite, target, c, d, fun input => ?_⟩
  obtain ⟨hout, hhalt⟩ := htarget input ℕ Unit unifSpec (ProbComp.uniform Bool) Empty.elim
    (fun q (s : Unit) => (fun a => (a, s)) <$> ProbComp.unifOracle q)
    (Probability.PMF.uniformOfFintype Bool)
    (fun s => by
      rw [OracleComp.run_interpret_stateless]
      exact congrArg (PMF.map (fun bit => (bit, s))) (ProbComp.eval_uniform Bool)) ()
  simp only [OracleComp.run_interpret_stateless] at hout
  constructor
  · have h := congrArg (PMF.map Prod.fst) hout
    simp only [PMF.monad_map_eq_map, PMF.map_comp] at h
    change PMF.map id _ = PMF.map id _ at h
    simp only [PMF.map_id] at h
    exact h
  · intro final hfinal
    apply hhalt (final, ())
    rw [OracleComp.run_interpret_stateless, PMF.monad_map_eq_map]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, hfinal, rfl⟩

end Turing.MultiTapePTM

namespace Cslib.Probability

/-- Replace a strict clocked certificate by an intrinsically halting finite realization.
The new machine and bound are fixed before choosing an input. It halts on every raw word,
including words outside the declared input encoding. -/
theorem IsPPTOn.exists_halting_machine {α β : Type} {input : α ↪ List Bool}
    {output : β ↪ List Bool} {program : α → ProbComp β} (h : IsPPTOn input output program) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : Turing.MultiTapePTM k Bool State)
      (c d : ℕ),
      (∀ a, (ProbComp.eval (program a)).map output =
        ProbComp.eval (machine.runClosed (c * ((input a).length + 1) ^ d) (input a))) ∧
      ∀ word,
      ∀ final ∈ (ProbComp.eval (machine.runConfigFrom (ProbComp.uniform Bool) Empty.elim
        (c * (word.length + 1) ^ d) (machine.initialConfig word))).support,
        final.tapes.state = none := by
  obtain ⟨k, State, hfinite, machine, c, d, hmachine⟩ := h
  obtain ⟨k', State', hfinite', target, c', d', htarget⟩ := machine.exists_halting_clock c d
  exact ⟨k', State', hfinite', target, c', d',
    fun a => (hmachine a).trans (htarget (input a)).1.symm, fun word => (htarget word).2⟩

end Cslib.Probability

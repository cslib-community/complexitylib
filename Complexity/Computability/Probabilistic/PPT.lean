/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Deterministic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Probability.PMF.Bool
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Run

/-!
# Uniform strict probabilistic polynomial time

`IsPPTOn input output program` identifies the encoded result distribution with one finite-control
fair-coin machine, clocked by a polynomial in the encoded input length. The machine and polynomial
are fixed before quantifying over inputs. Only fair bits are supplied to the machine, and it has
no oracle channels. Thus arbitrary Lean computation, nonuniform advice, and arbitrary distribution
samplers are not free operations.

The clock bounds every execution, rather than its expectation. The witness is forcibly stopped
at its clock; this definition does not require that its control state has already halted.
`PPT.Clock` compiles every such witness to an intrinsically halting finite machine, charging
preparation and consumption of a unary budget to its polynomial bound.
In particular, this definition does not certify exact uniform sampling from every finite type.

The public input and output encodings reuse the tidy calculus. A deterministic certificate lifts
directly to `IsPPTOn` without another deterministic computability predicate. `PPT.Composition`
certifies monadic `bind`, deterministic preprocessing and postprocessing. `PPT.Capture` permits
captured inputs and efficient conditionals. `Adaptive` certifies bounded probabilistic loops from
supported state-size invariants. `Tactic.PPT` automates the closed program rules and constant-growth
loops; oracle PPT requires further certified constructions.

Adapted from the cslib `crypto` branch's Computability/Probabilistic/PPT.lean at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`. The witness uses the common machine and any finite
control type, as the upstream tidy calculus does, instead of imposing a separate `Fin` presentation.

## Main definitions

* `Cslib.Probability.IsPPTOn`: uniform strict PPT on encoded types.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.isPPTOn`: deterministic certificates lift to PPT.
* `Cslib.Probability.IsPPTOn.length_le`: every supported encoded output is polynomially bounded.
-/

@[expose] public section

namespace Cslib.Probability

/-- Complementing a Boolean program's answer replaces the real probability of `true` by its
complement. -/
theorem _root_.Cslib.ProbComp.probability_not (program : ProbComp Bool) :
    (ProbComp.eval (Bool.not <$> program) true).toReal =
      1 - (ProbComp.eval program true).toReal := by
  simpa [ProbComp.eval_map, PMF.map_apply] using
    PMF.toReal_false_eq_one_sub (ProbComp.eval program)

variable {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
  {program program' : α → ProbComp β}

/-- One finite fair-coin machine realizes the program, with a uniform polynomial clock.
The clock is strict on every execution and includes the cost of writing the encoded output. -/
@[fun_prop]
def IsPPTOn {α β : Type} (input : α ↪ List Bool) (output : β ↪ List Bool)
    (program : α → ProbComp β) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : Turing.MultiTapePTM k Bool State)
    (c d : ℕ), ∀ a, (ProbComp.eval (program a)).map output =
      ProbComp.eval (machine.runClosed (c * ((input a).length + 1) ^ d) (input a))

/-- Distributional equality reuses the same finite machine and clock. -/
theorem IsPPTOn.congr (h : IsPPTOn input output program)
    (heq : ∀ a, ProbComp.eval (program a) = ProbComp.eval (program' a)) :
    IsPPTOn input output program' := by
  obtain ⟨k, State, hfinite, machine, c, d, h⟩ := h
  exact ⟨k, State, hfinite, machine, c, d, fun a =>
    (congrArg (PMF.map output) (heq a)).symm.trans (h a)⟩

/-- A typed certificate bounds the encoded length of every supported result. -/
theorem IsPPTOn.length_le (h : IsPPTOn input output program) :
    ∃ c d : ℕ, ∀ a result, result ∈ (ProbComp.eval (program a)).support →
      (output result).length ≤ c * ((input a).length + 1) ^ d := by
  obtain ⟨k, State, hfinite, machine, c, d, h⟩ := h
  refine ⟨c, d, fun a result hresult => ?_⟩
  have hmap := (PMF.mem_support_map_iff output (ProbComp.eval (program a))
    (output result)).mpr ⟨result, hresult, rfl⟩
  rw [h a] at hmap
  exact machine.length_output_eval_runClosed_le _ _ _ hmap

/-- A program returning its declared encoding has the same machine-level contract. -/
theorem isPPTOn_iff_encoded : IsPPTOn input output program ↔
    IsPPTOn input Turing.MultiTapeTM.encBits (fun a => output <$> program a) := by
  simp only [IsPPTOn, ProbComp.eval_map, Turing.MultiTapeTM.encBits,
    Function.Embedding.coe_refl, PMF.map_id]

end Cslib.Probability

/-- Reuse a tidy deterministic machine as a fair-coin machine that ignores its sampled bits. -/
@[fun_prop]
theorem Turing.MultiTapeTM.ComputableTidilyInPolyTime.isPPTOn {α β : Type}
    {input : α ↪ List Bool} {output : β ↪ List Bool} {f : α → β}
    (h : ComputableTidilyInPolyTime f input output) :
    Cslib.Probability.IsPPTOn input output (fun a => pure (f a)) := by
  obtain ⟨t, s, ht, _, k, State, hfinite, machine, hmachine⟩ := h
  obtain ⟨c, d, ht⟩ := ht.exists_le
  refine ⟨k, State, hfinite, Turing.MultiTapePTM.ofDeterministic machine, c, d, fun a => ?_⟩
  rw [Cslib.ProbComp.eval_pure, PMF.pure_map, Turing.MultiTapePTM.eval_runClosed_ofDeterministic]
  exact congrArg PMF.pure ((hmachine a).mono (ht a) le_rfl).runFrom_initCfg.2.symm

/-- A plain deterministic polynomial-time certificate gives a fair-coin machine that ignores
its sampled bits, with the same encoded result distribution. -/
@[fun_prop]
theorem Turing.MultiTapeTM.ComputableInPolyTime.isPPTOn {α β : Type}
    {input : α ↪ List Bool} {output : β ↪ List Bool} {f : α → β}
    (h : ComputableInPolyTime f input output) :
    Cslib.Probability.IsPPTOn input output (fun a => pure (f a)) :=
  h.tidy.isPPTOn

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Run
import Complexity.Computability.Machines.Turing.MultiTape.Internal.NormalForm

/-!
# Uniform strict PPT with external word oracles

`IsOraclePPTOn` uses one finite-control fair-coin machine and one polynomial clock for all inputs
and all shared stateful oracle handlers. The certificate preserves the joint output and final
oracle state. Finite operation names are separate from unbounded word requests and replies.
The clock charges writing queries, reading replies and writing output, while the oracle's own
computation is external.
Clock exhaustion may cut off a still-live machine; the certificate does not assert that its
control state has already halted.

Typed query encodings are not hidden inside this contract: any translation must separately
account for its computation. In particular, an unbounded oracle reply cannot be returned for
free. The machine clock bounds every supported output even when the handler returns a longer word.

`Oracle.Normalization` shows that every certificate also has a clean, intrinsically halting
realization with the same joint law, and `Oracle.Composition` composes certificates.

## Main definitions

* `Cslib.Probability.WordOracleComp`: private randomness and named word requests/replies.
* `Cslib.Probability.IsOraclePPTOn`: joint stateful realization by a strict polynomial clock.

## Main results

* `Cslib.Probability.IsOraclePPTOn.length_le`: uniform bounds on supported encoded output lengths.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.isOraclePPTOn`,
  `Turing.MultiTapeTM.ComputableInPolyTime.isOraclePPTOn`: deterministic functional programs
  are uniform oracle-PPT programs; the plain bridge first normalizes its machine.

## References

Adapted from Computability/Probabilistic/Oracle.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the current encodings and `ProbOracleComp`.
-/

@[expose] public section

namespace Cslib.Probability

/-- Private randomness and named external operations on word payloads. -/
abbrev WordOracleComp (Operation α : Type) :=
  ProbOracleComp (fun _ : Operation × List Bool => List Bool) α

/-- One finite machine and polynomial clock preserve the full interaction with every shared
stateful oracle. The oracle's computation is external; request construction and reply access are
ordinary machine work. -/
@[fun_prop]
def IsOraclePPTOn {Operation α β : Type} [DecidableEq Operation]
    (input : α ↪ List Bool) (output : β ↪ List Bool)
    (program : α → WordOracleComp Operation β) : Prop :=
  Finite Operation ∧ ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : Turing.MultiTapePTM k Bool Control Operation) (c d : ℕ),
    ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (output <$> program a)).run s =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (machine.runOracle (c * ((input a).length + 1) ^ d) (input a))).run s

namespace IsOraclePPTOn

variable {Operation α β : Type} [DecidableEq Operation]
  {input : α ↪ List Bool} {output : β ↪ List Bool}

/-- A fixed finite-control machine and polynomial clock supply a certificate directly. -/
theorem of_machine [Finite Operation] {k : ℕ} {Control : Type} [Finite Control]
    (machine : Turing.MultiTapePTM k Bool Control Operation) (c d : ℕ) :
    IsOraclePPTOn input Turing.MultiTapeTM.encBits
      (fun a => machine.runOracle (c * ((input a).length + 1) ^ d) (input a)) := by
  refine ⟨inferInstance, k, Control, inferInstance, machine, c, d, ?_⟩
  intro a State oracle s
  simp only [Turing.MultiTapeTM.encBits, Function.Embedding.coe_refl, id_map]

/-- Finiteness of the operation names is part of the certificate. -/
theorem finite_operations {program : α → WordOracleComp Operation β}
    (h : IsOraclePPTOn input output program) : Finite Operation := h.1

/-- Equality of the complete stateful semantics preserves the same clock. Output marginals
alone do not suffice, since later calls may observe the oracle's state. -/
theorem congr {program program' : α → WordOracleComp Operation β}
    (h : IsOraclePPTOn input output program)
    (heq : ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (program a)).run s =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (program' a)).run s) : IsOraclePPTOn input output program' := by
  obtain ⟨hops, k, Control, hfinite, machine, c, d, h⟩ := h
  refine ⟨hops, k, Control, hfinite, machine, c, d, fun a State oracle s => ?_⟩
  simpa only [OracleComp.interpret_map, StateT.run_map, heq] using h a State oracle s

/-- A program returning its declared encoding has the same strict oracle PPT certificates. -/
theorem iff_encoded {program : α → WordOracleComp Operation β} :
    IsOraclePPTOn input output program ↔
      IsOraclePPTOn input Turing.MultiTapeTM.encBits (fun a => output <$> program a) := by
  simp only [IsOraclePPTOn, Turing.MultiTapeTM.encBits, Function.Embedding.coe_refl, id_map]

/-- Every supported encoded output has polynomial length, independently of all oracle replies. -/
theorem length_le {program : α → WordOracleComp Operation β}
    (h : IsOraclePPTOn input output program) :
    ∃ c d : ℕ, ∀ a (State : Type)
      (oracle : Operation × List Bool → StateT State PMF (List Bool)) s s' result,
      (result, s') ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (program a)).run s).support →
      (output result).length ≤ c * ((input a).length + 1) ^ d := by
  obtain ⟨_, k, Control, _, machine, c, d, h⟩ := h
  refine ⟨c, d, fun a State oracle s s' result hresult => ?_⟩
  have hmap : (output result, s') ∈ ((OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (output <$> program a)).run s).support := by
    rw [OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(result, s'), hresult, rfl⟩
  rw [h a State oracle s] at hmap
  exact machine.length_output_runOracle_le oracle _ _ _ s s' hmap

end IsOraclePPTOn

end Cslib.Probability

/-- A tidy deterministic certificate also works in the presence of arbitrary external oracles. -/
@[fun_prop]
theorem Turing.MultiTapeTM.ComputableTidilyInPolyTime.isOraclePPTOn
    {Operation α β : Type} [DecidableEq Operation] [Finite Operation]
    {input : α ↪ List Bool} {output : β ↪ List Bool} {f : α → β}
    (h : ComputableTidilyInPolyTime f input output) :
    Cslib.Probability.IsOraclePPTOn (Operation := Operation) input output
      (fun a => pure (f a)) := by
  obtain ⟨t, s, ht, _, k, State, hfinite, machine, hmachine⟩ := h
  obtain ⟨c, d, ht⟩ := ht.exists_le
  refine ⟨inferInstance, k, State, hfinite,
    Turing.MultiTapePTM.ofDeterministic machine, c, d, fun a OracleState oracle state => ?_⟩
  rw [map_pure, Cslib.OracleComp.interpret_pure,
    Turing.MultiTapePTM.run_interpret_runOracle_ofDeterministic]
  exact congrArg (fun word => PMF.pure (word, state))
    ((hmachine a).mono (ht a) le_rfl).runFrom_initCfg.2.symm

/-- A plain deterministic certificate also works in the presence of arbitrary external oracles. -/
@[fun_prop]
theorem Turing.MultiTapeTM.ComputableInPolyTime.isOraclePPTOn
    {Operation α β : Type} [DecidableEq Operation] [Finite Operation]
    {input : α ↪ List Bool} {output : β ↪ List Bool} {f : α → β}
    (h : ComputableInPolyTime f input output) :
    Cslib.Probability.IsOraclePPTOn (Operation := Operation) input output
      (fun a => pure (f a)) := by
  obtain ⟨c, d, k, State, hfinite, machine, hmachine⟩ := Internal.NormalForm.polyTime h
  refine ⟨inferInstance, k, State, hfinite,
    Turing.MultiTapePTM.ofDeterministic machine, c, d, fun a OracleState oracle state => ?_⟩
  rw [map_pure, Cslib.OracleComp.interpret_pure,
    Turing.MultiTapePTM.run_interpret_runOracle_ofDeterministic]
  exact congrArg (fun word => PMF.pure (word, state)) (hmachine a).runFrom_initCfg.2.symm

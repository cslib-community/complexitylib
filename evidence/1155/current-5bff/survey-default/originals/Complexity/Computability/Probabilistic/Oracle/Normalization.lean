/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Oracle.Iteration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.QueryBounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Clean realizations of arbitrary oracle PPT certificates

A strict `IsOraclePPTOn` witness may be cut off by its clock while still live, leave partial
requests in its query buffers, read stale answer tapes and leave arbitrary storage behind. It is
nevertheless equivalent to a clean phase. During `fuel` instructions from blank storage, a machine
reads at most `fuel` symbols of any reply. The native run is therefore exactly the finite
interpreter loop in which every external call returns its `fuel`-symbol prefix. Each interpreter
step is certified by the clean calculus: a fair bit, a fixed table lookup, and at most one
bounded-prefix query. The loop makes the same adaptive external calls in the same order, with
identical requests, and preserves the complete joint law of the output and external oracle state.

## Main results

* `Cslib.Probability.IsTidyOraclePPTOn.finiteStep`: one truncated interpreter step is clean.
* `Cslib.Probability.IsTidyOraclePPTOn.runOracle`: every clocked oracle machine run is clean.
* `Cslib.Probability.IsOraclePPTOn.isTidyOraclePPTOn`,
  `Cslib.Probability.isOraclePPTOn_iff_isTidyOraclePPTOn`: every strict oracle PPT certificate
  has a clean realization with the same joint output and external-state law.

## References

Adapts the closed interpreter Computability/Probabilistic/Realization/OracleSimulation.lean of
the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8` to open oracles, using the
reply truncation lemma `Turing.MultiTapePTM.finiteRunFrom_take_runOracle`.
-/

@[expose] public section

namespace Cslib.Probability

open _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapeTM
  _root_.Turing.MultiTapePTM

variable {k : ℕ} {Control Operation : Type} [DecidableEq Operation]

/-- One native instruction on finite storage, with each external reply truncated to the first
`limit` symbols, is a clean phase. A query copies only the charged reply prefix. -/
theorem IsTidyOraclePPTOn.finiteStep [Fintype Operation] [Finite Control]
    (machine : _root_.Turing.MultiTapePTM k Bool Control Operation) :
    IsTidyOraclePPTOn (encPair encUnary encFiniteConfig) encFiniteConfig
      (fun pair : ℕ × FiniteConfig k Bool Control Operation =>
        machine.finiteStep
          (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
          (fun op word => List.take pair.1 <$> ProbOracleComp.query (op, word)) pair.2) := by
  let branch (control : Option Control) (pair : ℕ × FiniteConfig k Bool Control Operation) :
      WordOracleComp Operation (FiniteConfig k Bool Control Operation) :=
    match control with
    | none => pure pair.2
    | some control => do
      let bit ← ProbOracleComp.sample (ProbComp.uniform Bool)
      match machine.tr control pair.2.tapes.inputSymbol pair.2.tapes.workTapeSymbols
          pair.2.answerSymbols bit with
      | .step action symbol move => pure (pair.2.step action symbol move)
      | .query channel next => do
        let answer ← ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool)
          (channel, (pair.2.channels channel).1)
        pure (pair.2.receive channel next (List.take pair.1 answer))
  have hprogram (pair : ℕ × FiniteConfig k Bool Control Operation) :
      branch pair.2.tapes.state pair = machine.finiteStep
        (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
        (fun op word => List.take pair.1 <$> ProbOracleComp.query (op, word)) pair.2 := by
    rcases pair with ⟨limit, cfg⟩
    cases hstate : cfg.tapes.state with
    | none => simp only [branch, MultiTapeMachine.finiteStep, hstate]
    | some control =>
      simp only [branch, MultiTapeMachine.finiteStep, hstate, bind_map_left]
      congr 1
      funext bit
      cases machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols
          bit with
      | step action symbol move => rfl
      | query channel next => rfl
  refine (IsTidyOraclePPTOn.finite_cases (tagEncoding := encFinite (Option Control))
    (tag := fun pair : ℕ × FiniteConfig k Bool Control Operation => pair.2.tapes.state)
    (branch := branch) (by fun_prop) fun control => ?_).congr
      fun pair State oracle s => by rw [hprogram]
  cases control with
  | none => exact IsTidyOraclePPTOn.of_computableInPolyTime (by fun_prop)
  | some control =>
    apply (IsTidyOraclePPTOn.uniform_bool (encPair encUnary encFiniteConfig)).bind_with
    apply IsTidyOraclePPTOn.finite_cases
      (tag := fun pair : (ℕ × FiniteConfig k Bool Control Operation) × Bool =>
        (pair.1.2.tapes.inputSymbol, pair.1.2.tapes.workTapeSymbols,
          pair.1.2.answerSymbols, pair.2))
      (tagEncoding := encPair (encFinEnum (Option Bool))
        (encPair (encFinEnum (Fin k → Option Bool))
          (encPair (encFinite (Operation → Option Bool)) encBool)))
      (branch := fun symbols (pair : (ℕ × FiniteConfig k Bool Control Operation) × Bool) =>
        match machine.tr control symbols.1 symbols.2.1 symbols.2.2.1 symbols.2.2.2 with
        | .step action symbol move => pure (pair.1.2.step action symbol move)
        | .query channel next => do
          let answer ← ProbOracleComp.query
            (spec := fun _ : Operation × List Bool => List Bool)
            (channel, (pair.1.2.channels channel).1)
          pure (pair.1.2.receive channel next (List.take pair.1.1 answer)))
    · fun_prop
    · rintro ⟨inputSymbol, workSymbols, answerSymbols, bit⟩
      cases machine.tr control inputSymbol workSymbols answerSymbols bit with
      | step action symbol move =>
        exact IsTidyOraclePPTOn.of_computableInPolyTime (by fun_prop)
      | query channel next =>
        have hreply := ((IsTidyOraclePPTOn.query_take channel).preprocess
          (input := encPair (encPair encUnary encFiniteConfig) encBool)
          (prepare := fun pair : (ℕ × FiniteConfig k Bool Control Operation) × Bool =>
            ((pair.1.2.channels channel).1, pair.1.1)) (by fun_prop)).map_with
          (f := fun pair answer => pair.1.2.receive channel next answer) (by fun_prop)
        simpa only [Functor.map_map, bind_pure_comp] using hreply

/-- Every clocked run of a finite-control oracle machine is a clean phase. The interpreter loop
retains finite storage, runs exactly as many steps as the clock, and copies each reply only up to
the clock, which bounds every reply position the original run can read. -/
theorem IsTidyOraclePPTOn.runOracle [Finite Operation] [Finite Control]
    (machine : _root_.Turing.MultiTapePTM k Bool Control Operation) (c d : ℕ) :
    IsTidyOraclePPTOn encBits encBits
      (fun word : List Bool => machine.runOracle (c * (word.length + 1) ^ d) word) := by
  let _ := Fintype.ofFinite Operation
  obtain ⟨cf, hconfigurationSize⟩ :=
    length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Operation)
  let clock (word : List Bool) : ℕ := c * (word.length + 1) ^ d
  have hclock : ComputableInPolyTime clock encBits encUnary := by
    dsimp only [clock]
    fun_prop
  have hclockPoly : PolyBounded (fun word => (encBits word).length) clock := by
    simpa only [encUnary_apply, List.length_replicate] using hclock.polyBounded_length
  have hstart : ComputableInPolyTime
      (fun word => FiniteConfig.init (k := k) (Oracle := Operation) machine.initial word)
      encBits encFiniteConfig := by fun_prop
  let step (word : List Bool) (cfg : FiniteConfig k Bool Control Operation) :
      WordOracleComp Operation (FiniteConfig k Bool Control Operation) :=
    machine.finiteStep (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun op query => List.take (clock word) <$> ProbOracleComp.query (op, query)) cfg
  have hstep : IsTidyOraclePPTOn (encPair encBits encFiniteConfig) encFiniteConfig
      (fun pair => step pair.1 pair.2) :=
    (IsTidyOraclePPTOn.finiteStep machine).preprocess
      (prepare := fun pair : List Bool × FiniteConfig k Bool Control Operation =>
        (clock pair.1, pair.2)) (by fun_prop)
  have hloop := (IsTidyOraclePPTOn.iterateWith_spec hclock hstart hstep
    (fun word i cfg => FiniteConfig.SpaceBound word.length i (clock word) cfg)
    (fun word => FiniteConfig.spaceBound_init _ _ _)
    (by
      intro word i cfg _ hcfg next hnext
      cases hstate : cfg.tapes.state with
      | none =>
        simp only [step, MultiTapeMachine.finiteStep, hstate] at hnext
        exact (OracleComp.eq_of_mem_supportWith_pure hnext) ▸
          hcfg.mono le_rfl (Nat.le_succ i) le_rfl
      | some control =>
        simp only [step, MultiTapeMachine.finiteStep, hstate] at hnext
        obtain ⟨action, _, hnext⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
        cases action with
        | step action symbol move =>
          exact (OracleComp.eq_of_mem_supportWith_pure hnext) ▸ hcfg.step action symbol move
        | query channel control =>
          obtain ⟨answer, hanswer, hnext⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
          obtain ⟨reply, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hanswer
          exact (OracleComp.eq_of_mem_supportWith_pure hnext) ▸
            hcfg.receive channel control _ (List.length_take_le _ _))
    (size := fun word => cf * (word.length + clock word + clock word + 1))
    ((PolyBounded.const cf).mul
      (((PolyBounded.self.add hclockPoly).add hclockPoly).add (.const 1)))
    (fun word i cfg hi hcfg => (hconfigurationSize _ _ _ cfg hcfg).trans
      (Nat.mul_le_mul_left cf (by lia)))).1
  refine (hloop.map (by fun_prop : ComputableInPolyTime
    (fun cfg : FiniteConfig k Bool Control Operation => cfg.tapes.output)
    encFiniteConfig encBits)).congr fun word State oracle s => ?_
  rw [← finiteRunFrom_take_runOracle]
  rfl

/-- Every strict oracle PPT certificate has a clean realization. The realization makes the same
adaptive external calls with the same requests in the same order, and has the same joint law of
output and external oracle state, for every stateful handler and arbitrarily long replies. -/
theorem IsOraclePPTOn.isTidyOraclePPTOn {α β : Type} {input : α ↪ List Bool}
    {output : β ↪ List Bool} {program : α → WordOracleComp Operation β}
    (h : IsOraclePPTOn input output program) : IsTidyOraclePPTOn input output program := by
  obtain ⟨_, k, Control, _, machine, c, d, h⟩ := h
  exact IsTidyOraclePPTOn.iff_encoded.mpr
    (((IsTidyOraclePPTOn.runOracle machine c d).preprocess
      (ComputableInPolyTime.of_eq (encOut := encBits) (f := input) fun _ => rfl)).congr
        fun a State oracle s =>
        (h a State oracle s).symm)

/-- Strict oracle PPT certificates are exactly the clean polynomial-time realizations. -/
theorem isOraclePPTOn_iff_isTidyOraclePPTOn {α β : Type} {input : α ↪ List Bool}
    {output : β ↪ List Bool} {program : α → WordOracleComp Operation β} :
    IsOraclePPTOn input output program ↔ IsTidyOraclePPTOn input output program :=
  ⟨IsOraclePPTOn.isTidyOraclePPTOn, IsTidyOraclePPTOn.isOraclePPTOn⟩

end Cslib.Probability

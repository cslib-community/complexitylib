/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Oracle
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.WithOracleInput

/-!
# Efficient saved-coin replay of oracle-PPT programs

A native machine's replay receives its coins and ordinary input as one encoded pair. Its native
certificate charges decoding, tape preparation, and all replay instructions. Oracle requests and
replies retain their original channels and costs.

Every `IsOraclePPTOn` program consequently has a polynomial-length saved-coin representation whose
replay itself satisfies `IsOraclePPTOn`. Averaging those fixed-coin interactions recovers the joint
encoded output and external state for every stateful handler. This is a replay certificate; a
signature ROM reduction must still implement its query encodings, cache, signing, and freshness.

## Main results

* `Turing.MultiTapePTM.isOraclePPTOn_runCoins`: efficient replay from the full encoded input pair.
* `Cslib.Probability.IsOraclePPTOn.exists_savedCoins`: an actual oracle-PPT program has efficient
  polynomial-coin replay with equality of its full stateful semantics.

## References

An original application of the native saved-coin compiler and the existing pre-sampling law
`MultiTapePTM.run_interpret_runConfigFrom_eq_coins`.
-/

public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeTM

/-- Saved-coin replay is oracle-PPT in the complete encoded pair, including preparation. -/
@[fun_prop] theorem isOraclePPTOn_runCoins {k : ℕ} {Control Operation : Type}
    [Finite Control] [Finite Operation] [DecidableEq Operation]
    (machine : MultiTapePTM k Bool Control Operation) :
    IsOraclePPTOn (encPair encBits encBits) encBits
      (fun p : List Bool × List Bool =>
        machine.runCoins (fun op word => ProbOracleComp.query (op, word)) p.1 p.2) := by
  obtain ⟨k', Control', hfinite, target, c, ht⟩ := machine.exists_oracleReplay
  refine ⟨inferInstance, k', Control', hfinite, target, c, 1, ?_⟩
  intro p Store oracle s
  simp only [encBits, Function.Embedding.coe_refl, id_map, pow_one]
  exact (ht p.1 p.2 _ _ _ (ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun op word => ProbOracleComp.query (op, word))
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
    (PMF.uniformOfFintype Bool)
    (fun _ => by simp only [ProbOracleComp.run_interpret_sample, ProbComp.eval_uniform]) s).1.symm

end Turing.MultiTapePTM

namespace Cslib.Probability

open Turing Turing.MultiTapeTM Turing.MultiTapePTM

/-- Every certified oracle-PPT program has an efficient saved-coin realization. The coin tape has
polynomial length in the original encoded input. Replay fixes one coin per native instruction and
performs only the original external requests; averaging retains both output and handler state. -/
theorem IsOraclePPTOn.exists_savedCoins {Operation α β : Type} [DecidableEq Operation]
    {input : α ↪ List Bool} {output : β ↪ List Bool}
    {program : α → WordOracleComp Operation β} (h : IsOraclePPTOn input output program) :
    ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM k Bool Control Operation) (c d : ℕ),
      IsOraclePPTOn (encPair encBits encBits) encBits
        (fun p : List Bool × List Bool =>
          machine.runCoins (fun op word => ProbOracleComp.query (op, word)) p.1 p.2) ∧
      ∀ a (Store : Type) (oracle : Operation × List Bool → StateT Store PMF (List Bool)) s,
        ProbOracleComp.runWith oracle (output <$> program a) s =
          (BitString.uniformList (c * ((input a).length + 1) ^ d)).bind (fun coins =>
            ProbOracleComp.runWith oracle
                (machine.runCoins (fun op word => ProbOracleComp.query (op, word)) coins (input a))
                s) := by
  obtain ⟨hops, k, Control, hfinite, machine, c, d, hrun⟩ := h
  let := hops
  let := hfinite
  refine ⟨k, Control, inferInstance, machine, c, d, machine.isOraclePPTOn_runCoins, ?_⟩
  intro a Store oracle s
  rw [hrun a Store oracle s]
  have hc := machine.run_interpret_runConfigFrom_eq_coins
    (ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun op word => ProbOracleComp.query (op, word))
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
    (fun _ => by simp only [ProbOracleComp.run_interpret_sample, ProbComp.eval_uniform])
    (c * ((input a).length + 1) ^ d) (machine.initialConfig (input a)) s
  have hout := congrArg (PMF.map (fun result => (result.1.tapes.output, result.2))) hc
  simpa only [ProbOracleComp.runWith, OracleComp.runWith, MultiTapePTM.runOracle,
    MultiTapePTM.run, MultiTapePTM.runFrom, runCoins, runFromCoins, OracleComp.interpret_map,
    StateT.run_map, PMF.monad_map_eq_map, PMF.map_bind] using hout

end Cslib.Probability

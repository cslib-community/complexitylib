/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Oracle
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.SingleOracle

/-!
# Routing a single-channel oracle program

Route every query of a single-channel word-oracle program to one named channel, preserving the
complete stateful interaction and its strict polynomial-time realization.

## Main definitions

* `Cslib.Probability.WordOracleComp.singleOracle`: route queries to a selected channel.

## Main results

* `Cslib.Probability.WordOracleComp.run_interpret_singleOracle`: interpretation after routing.
* `Cslib.Probability.IsOraclePPTOn.singleOracle`: routing preserves strict oracle PPT.
-/

@[expose] public section

namespace Cslib.Probability

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM

variable {ι α β : Type}

/-- Route all word-oracle queries of a single-channel program to channel `i₀ : ι`. -/
def WordOracleComp.singleOracle (i₀ : ι) (p : WordOracleComp Unit α) :
    WordOracleComp ι α :=
  OracleComp.interpret
    (OracleComp.sumHandler
      (fun n => OracleComp.query
        (spec := probOracleSpec (fun _ : ι × List Bool => List Bool)) (Sum.inl n))
      (fun q : Unit × List Bool =>
        ProbOracleComp.query (spec := fun _ : ι × List Bool => List Bool) (i₀, q.2)))
    p

theorem WordOracleComp.singleOracle_map (i₀ : ι) (f : α → β) (p : WordOracleComp Unit α) :
    WordOracleComp.singleOracle i₀ (f <$> p) = f <$> WordOracleComp.singleOracle i₀ p :=
  OracleComp.interpret_map _ _ _

/-- Interpreting `WordOracleComp.singleOracle i₀ p` against `oracle` is equivalent to interpreting
`p` against `fun q => oracle (i₀, q.2)`. -/
theorem WordOracleComp.run_interpret_singleOracle {State : Type} (i₀ : ι)
    (oracle : ι × List Bool → StateT State PMF (List Bool)) (p : WordOracleComp Unit α)
    (s : State) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (WordOracleComp.singleOracle i₀ p)).run s =
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
        (fun q : Unit × List Bool => oracle (i₀, q.2))) p).run s := by
  rw [WordOracleComp.singleOracle, OracleComp.interpret_interpret]
  congr 2
  funext q
  cases q <;> simp only [OracleComp.sumHandler, ProbOracleComp.query, OracleComp.interpret_query]

/-- Routing a strict oracle-PPT single-channel program to channel `i₀ : ι` preserves
`IsOraclePPTOn`. -/
theorem IsOraclePPTOn.singleOracle [DecidableEq ι] [Finite ι] (i₀ : ι)
    {input : α ↪ List Bool} {output : β ↪ List Bool} {program : α → WordOracleComp Unit β}
    (h : IsOraclePPTOn input output program) :
    IsOraclePPTOn input output (fun a => WordOracleComp.singleOracle i₀ (program a)) := by
  obtain ⟨_, k, Control, hfinite, machine, c, d, h⟩ := h
  refine ⟨inferInstance, k, Control, hfinite, machine.singleOracle i₀, c, d,
    fun a State oracle s => ?_⟩
  rw [← WordOracleComp.singleOracle_map, WordOracleComp.run_interpret_singleOracle,
    MultiTapePTM.runOracle_singleOracle, ← WordOracleComp.singleOracle,
    WordOracleComp.run_interpret_singleOracle]
  exact h a State (fun q => oracle (i₀, q.2)) s

end Cslib.Probability

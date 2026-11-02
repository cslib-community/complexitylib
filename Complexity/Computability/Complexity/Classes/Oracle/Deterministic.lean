/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Deterministic

/-!
# Deterministic machines behind polynomial time relative to an oracle

A certificate of `Cslib.Complexity.ComputableInPolyTimeWithOracle` is a fair-coin machine that
reproduces a deterministic program against every stateful oracle. Fixing all of its coins to
`false` gives a deterministic run of the same machine, itself a word-query program
(`Turing.MultiTapePTM.run` with the coin program `pure false`). Its result against every
answer function is the program's (`Cslib.Probability.IsOraclePPTOn.exists_run_pure_false`): the
coin-fixed run is one of the supported runs of the certificate, whose result is determined
(`Turing.MultiTapePTM.mem_support_runConfigFrom_pure`). The run makes at most one request per
instruction (`Turing.MultiTapeMachine.length_queriesWith_runConfigFrom_le`).

Relabelling the finite control states to `Fin m` (`Turing.MultiTapePTM.relabel`,
`Turing.MultiTapePTM.runFrom_relabel`) shows that the deterministic runs behind all certificates
come from countably many machines with control `Fin m`
(`Cslib.Probability.IsOraclePPTOn.exists_fin_run_pure_false`), as oracle diagonalizations need.

## Main results

* `Turing.MultiTapeMachine.length_queriesWith_runConfigFrom_le`: a deterministic run makes at most
  one request per instruction.
* `Cslib.Probability.IsOraclePPTOn.exists_run_pure_false`,
  `Cslib.Probability.IsOraclePPTOn.exists_fin_run_pure_false`: certificates of deterministic
  programs are deterministic runs of finite machines with a polynomial clock.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 3.4
  (oracle Turing machines).
-/

@[expose] public section

namespace Turing.MultiTapeMachine

open Cslib

variable {k : ℕ} {Symbol State Oracle : Type} {input : List Symbol}

/-- **A deterministic run makes at most one request per instruction**, under every answer
function. -/
theorem length_queriesWith_runConfigFrom_le {Choose : Type → Type} [DecidableEq Oracle]
    (machine : MultiTapeMachine k Symbol State Oracle Choose)
    (pick : Choose (Action k Symbol State Oracle) → Action k Symbol State Oracle)
    (answer : Oracle × List Symbol → List Symbol) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) :
    (OracleComp.queriesWith answer (machine.runConfigFrom (fun choices => pure (pick choices))
      (fun oracle word => OracleComp.query (oracle, word)) fuel cfg)).length ≤ fuel := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => simp [runConfigFrom, hs]
    | some state =>
      simp only [runConfigFrom, hs, pure_bind]
      cases pick (machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols) with
      | step action symbol move => exact (ih _).trans (Nat.le_succ _)
      | query oracle next =>
        rw [OracleComp.queriesWith_query_bind, List.length_cons]
        exact Nat.succ_le_succ (ih _)

end Turing.MultiTapeMachine

namespace Cslib.Probability.IsOraclePPTOn

open Turing Complexity

variable {Operation α β : Type} [DecidableEq Operation] {input : α ↪ List Bool}
  {output : β ↪ List Bool}

omit [DecidableEq Operation] in
/-- A deterministic program against a deterministic oracle returns a point mass and keeps the
oracle's state. -/
private theorem run_interpret_interpret_query {σ : Type}
    (answer : Operation × List Bool → List Bool)
    (program : WordQueryComp Operation β) (s : σ) :
    (OracleComp.interpret (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
        (fun q s => PMF.pure (answer q, s)))
      (OracleComp.interpret ProbOracleComp.query program)).run s =
      PMF.pure (OracleComp.interpret (m := Id) answer program, s) := by
  rw [OracleComp.interpret_interpret]
  simp only [ProbOracleComp.interpret_query]
  induction program using PFunctor.FreeM.induction generalizing s with
  | pure b => rfl
  | lift_bind q cont ih =>
    rw [show (PFunctor.FreeM.lift q).bind cont = OracleComp.query q >>= cont from rfl,
      OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind]
    exact (PMF.pure_bind _ _).trans (ih _ s)

/-- **Certificates are deterministic runs.** A certificate for a deterministic program yields a
finite machine and a polynomial clock whose run with every coin fixed to `false` returns, against
every answer function, the encoded result of the program. -/
theorem exists_run_pure_false {program : α → WordQueryComp Operation β}
    (h : IsOraclePPTOn input output
      (fun a => OracleComp.interpret ProbOracleComp.query (program a))) :
    ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM k Bool Control Operation) (c d : ℕ),
      ∀ a (answer : Operation × List Bool → List Bool),
        OracleComp.interpret (m := Id) answer (machine.run (pure false)
            (fun op word => OracleComp.query (op, word)) (c * ((input a).length + 1) ^ d)
            (input a)) =
          output (OracleComp.interpret (m := Id) answer (program a)) := by
  obtain ⟨-, k, Control, hfinite, machine, c, d, h⟩ := h
  refine ⟨k, Control, hfinite, machine, c, d, fun a answer => ?_⟩
  have hcert := h a Unit (fun q s => PMF.pure (answer q, s)) ()
  rw [OracleComp.interpret_map, StateT.run_map, run_interpret_interpret_query,
    PMF.monad_map_eq_map, PMF.pure_map] at hcert
  have hmem := MultiTapePTM.mem_support_runConfigFrom_pure machine false answer ()
    (c * ((input a).length + 1) ^ d) (machine.initialConfig (input a))
  have hmem' : (OracleComp.interpret (m := Id) answer (machine.run (pure false)
      (fun op word => OracleComp.query (op, word)) (c * ((input a).length + 1) ^ d) (input a)),
      ()) ∈ ((OracleComp.interpret (OracleComp.sumHandler
        (fun n => StateT.lift (ProbComp.unifOracle n)) (fun q s => PMF.pure (answer q, s)))
        (machine.runOracle (c * ((input a).length + 1) ^ d) (input a))).run ()).support := by
    simp only [MultiTapePTM.runOracle, MultiTapePTM.run, MultiTapePTM.runFrom,
      OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map, PMF.mem_support_map_iff]
    exact ⟨_, hmem, rfl⟩
  rw [← hcert, PMF.mem_support_pure_iff] at hmem'
  exact (Prod.mk.inj hmem').1

/-- **Certificates are deterministic runs of countably many machines.** As
`exists_run_pure_false`, with control states `Fin m`. -/
theorem exists_fin_run_pure_false {program : α → WordQueryComp Operation β}
    (h : IsOraclePPTOn input output
      (fun a => OracleComp.interpret ProbOracleComp.query (program a))) :
    ∃ (k m : ℕ) (machine : MultiTapePTM k Bool (Fin m) Operation) (c d : ℕ),
      ∀ a (answer : Operation × List Bool → List Bool),
        OracleComp.interpret (m := Id) answer (machine.run (pure false)
            (fun op word => OracleComp.query (op, word)) (c * ((input a).length + 1) ^ d)
            (input a)) =
          output (OracleComp.interpret (m := Id) answer (program a)) := by
  obtain ⟨k, Control, hfinite, machine, c, d, h⟩ := exists_run_pure_false h
  have := Fintype.ofFinite Control
  refine ⟨k, Fintype.card Control, machine.relabel (Fintype.equivFin Control), c, d,
    fun a answer => ?_⟩
  rw [MultiTapePTM.run, MultiTapePTM.initialConfig_relabel, MultiTapePTM.runFrom_relabel,
    ← MultiTapePTM.run]
  exact h a answer

end Cslib.Probability.IsOraclePPTOn

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Probabilistic.Oracle.Replay

/-! Full-input replay and a saved-coin witness for an actual random oracle-aware program. -/

namespace CslibFrontierTests.OracleReplayInput

open Cslib Cslib.Probability Turing Turing.MultiTapeTM Turing.MultiTapePTM

private def machine : MultiTapePTM 0 Bool Bool Bool where
  initial := false
  tr state _ _ answer bit := if state then
    .step { inputTape := 0, workTapes := Fin.elim0, output := answer true, state := none }
      (fun _ => none) (fun _ => 0)
    else .query bit true

private def query (op : Bool) (word : List Bool) :
    OracleComp (fun _ : Bool × List Bool => List Bool) (List Bool) :=
  OracleComp.query (op, word)

private def record (q : Bool × List Bool) : StateT ℕ Id (List Bool) :=
  fun s => ([q.1], s + 1)

-- A private coin directly selects the query channel; the handler state advances once.
example : (OracleComp.interpret record (machine.runCoins query [true, false] [])).run 4 =
    ([true], 5) := rfl

-- The same saved second coin reads a different channel when the first coin selected false.
example : (OracleComp.interpret record (machine.runCoins query [false, false] [])).run 4 =
    ([], 5) := rfl

-- Exhaustion before the first query has a different observable external state.
example : (OracleComp.interpret record (machine.runCoins query [] [])).run 4 ≠
    (OracleComp.interpret record (machine.runCoins query [false, false] [])).run 4 := by
  change (([], 4) : List Bool × ℕ) ≠ ([], 5)
  decide

-- The certificate measures the full encoded pair, including arbitrarily long supplied input.
example : IsOraclePPTOn (encPair encBits encBits) encBits
    (fun p : List Bool × List Bool =>
      machine.runCoins (fun op word => ProbOracleComp.query (op, word)) p.1 p.2) := by
  fun_prop

private noncomputable def handler (q : Bool × List Bool) : StateT ℕ PMF (List Bool) :=
  fun s => PMF.pure ([q.1], s + 1)

private noncomputable def observe (p : WordOracleComp Bool (List Bool)) (s : ℕ) :=
  (OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) handler) p).run s

-- An actual uniform two-step oracle machine has a certified replay and a joint-law decomposition.
-- The empty ordinary input still permits a query and a stateful reply.
example : ∃ (fuel : ℕ) (replay : List Bool × List Bool → WordOracleComp Bool (List Bool)),
    IsOraclePPTOn (encPair encBits encBits) encBits replay ∧
    ∀ s, observe (machine.runOracle 2 []) s =
      (BitString.uniformList fuel).bind (fun coins => observe (replay (coins, [])) s) := by
  have h : IsOraclePPTOn encBits encBits (fun input => machine.runOracle 2 input) := by
    simpa only [encBits_apply, pow_zero, mul_one] using
      (IsOraclePPTOn.of_machine (input := encBits) machine 2 0)
  obtain ⟨_, _, _, native, c, _, hefficient, heq⟩ := h.exists_savedCoins
  refine ⟨c, (fun p => native.runCoins (fun op word => ProbOracleComp.query (op, word)) p.1 p.2),
    hefficient, ?_⟩
  intro s
  simpa only [encBits, Function.Embedding.coe_refl, id_map, id_eq, List.length_nil,
    zero_add, one_pow,
    mul_one, observe] using heq [] ℕ handler s

end CslibFrontierTests.OracleReplayInput

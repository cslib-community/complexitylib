/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Probabilistic.Oracle.ReplayParameter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape.QueryBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape.Substitution
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Protocols.Signature.RandomOracle.Simulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! Varying generated key lengths, stateful oracle replay, and shared-world mixture replacement. -/

namespace ComplexityTests.SavedCoinReplacement

open Cslib Cslib.Probability Turing Turing.MultiTapeTM Turing.MultiTapePTM
open Cslib.Crypto.Protocols.ROMSignature

private def machine : MultiTapePTM 0 Bool Bool Bool where
  initial := false
  tr state _ _ answer bit := if state then
    .step { inputTape := 0, workTapes := Fin.elim0, output := answer true, state := none }
      (fun _ => none) (fun _ => 0)
    else .query bit true

private def query (op : Bool) (word : List Bool) :
    OracleComp (fun _ : Bool × List Bool => List Bool) (List Bool) :=
  OracleComp.query (op, word)

-- This bound holds on every tape, including empty and arbitrarily overlong tapes.
example (coins input : List Bool) :
    OracleComp.IsQueryBounded (machine.runCoins query coins input) coins.length := by
  simpa only [Nat.mul_one] using machine.isCostBounded_runCoins query 1
    (fun op word => OracleComp.IsCostBounded.query (op, word)) coins input

private def record (q : Bool × List Bool) : StateT ℕ Id (List Bool) :=
  fun s => ([q.1], s + 1)

-- Channel substitution preserves the saved tape before any stateful world is selected.
example (coins input : List Bool) :
    OracleComp.interpret (fun request => query (!request.1) request.2)
      (machine.runCoins query coins input) =
    machine.runCoins (fun op word => query (!op) word) coins input := by
  simpa only [query, OracleComp.interpret_query] using
    machine.interpret_runCoins query (fun request => query (!request.1) request.2) coins input

-- Selecting another saved first coin changes the output channel, while both runs change state.
example : (OracleComp.interpret record (machine.runCoins query [true, false] [])).run 4 =
    ([true], 5) := rfl

example : (OracleComp.interpret record (machine.runCoins query [false, false] [])).run 4 =
    ([], 5) := rfl

private noncomputable def gen (n : ℕ) : ProbComp (List Bool × List Bool) :=
  (fun bit => (List.replicate n true ++ if bit then [false] else [], [])) <$>
    ProbComp.uniform Bool

private theorem gen_ppt : IsPPTOn encUnary (encPair encBits encBits) gen := by
  apply (isPPTOn_uniform_bool encUnary).map_with
  fun_prop

-- Two supported keys at one security parameter have different lengths.
example (n : ℕ) : (List.replicate n true, []) ∈ (ProbComp.eval (gen n)).support := by
  simp only [gen, ProbComp.eval_map, ProbComp.eval_uniform, PMF.mem_support_map_iff]
  exact ⟨false, by simp, by simp⟩

example (n : ℕ) : (List.replicate n true ++ [false], []) ∈ (ProbComp.eval (gen n)).support := by
  simp only [gen, ProbComp.eval_map, ProbComp.eval_uniform, PMF.mem_support_map_iff]
  exact ⟨true, by simp, by simp⟩

private noncomputable def handler (q : Bool × List Bool) : StateT ℕ PMF (List Bool) :=
  fun s => PMF.pure ([q.1], s + 1)

private noncomputable def observe (program : WordOracleComp Bool (List Bool)) (s : ℕ) :=
  (OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) handler) program).run s

-- One polynomial tape law works for both key lengths; the query counter is retained jointly.
example : ∃ (budget : ℕ → ℕ)
    (replay : ℕ → List Bool → List Bool → WordOracleComp Bool (List Bool)),
    PolynomiallyBounded budget ∧ ∀ n keys, keys ∈ (ProbComp.eval (gen n)).support → ∀ s,
      observe (machine.runOracle 2 keys.1) s =
        (BitString.uniformList (budget n)).bind
          (fun coins => observe (replay n keys.1 coins) s) := by
  have hsource : IsOraclePPT encBits (fun _ pk => machine.runOracle 2 pk) := by
    have h : IsOraclePPTOn encBits encBits (fun input => machine.runOracle 2 input) := by
      simpa only [encBits_apply, pow_zero, mul_one] using
        (IsOraclePPTOn.of_machine (input := encBits) machine 2 0)
    exact h.preprocess' (prepare := fun p : ℕ × List Bool => p.2) (by fun_prop)
  obtain ⟨_, _, _, native, c, d, keyC, keyD, hkeys, _, _, heq⟩ :=
    hsource.exists_savedCoins_of_keyGen gen_ppt
  refine ⟨fun n => c * (2 * n + 2 + keyC * (n + 1) ^ keyD) ^ d,
    fun n pk coins => native.runCoins (fun op word => ProbOracleComp.query (op, word))
      (coins.take (c * ((encPair encUnary encBits (n, pk)).length + 1) ^ d))
      (encPair encUnary encBits (n, pk)), by fun_prop, ?_⟩
  intro n keys hmem s
  simpa only [encBits, Function.Embedding.coe_refl, id_map, observe] using
    heq n keys.1 (hkeys n keys hmem) ℕ handler s

private def fixedForger (bit : Bool) :
    OracleComp (ForgerSpec Bool Bool Unit Bool) (Bool × Unit) := do
  let _ ← OracleComp.query (spec := ForgerSpec Bool Bool Unit Bool) (.inl false)
  let _ ← OracleComp.query (spec := ForgerSpec Bool Bool Unit Bool) (.inl false)
  let _ ← OracleComp.query (spec := ForgerSpec Bool Bool Unit Bool) (.inr bit)
  let _ ← OracleComp.query (spec := ForgerSpec Bool Bool Unit Bool) (.inr bit)
  return (bit, ())

private noncomputable def randomizedForger :
    ProbOracleComp (ForgerSpec Bool Bool Unit Bool) (Bool × Unit) := do
  let bit ← ProbOracleComp.sample (ProbComp.uniform Bool)
  liftOracleForger (fixedForger bit)

-- The mixture transport allows repeated signing and hashing. For bit=false final-message
-- freshness fails; for bit=true it succeeds if verification does. No Nodup premise is used.
example (scheme : Scheme Unit Unit Bool Unit Bool Bool) :
    (world scheme ()).eval (worldRealize scheme () randomizedForger
      (fun verified ⟨msg, _⟩ pairs => verified && !(pairs.map Prod.fst).contains msg)) =
    (PMF.uniformOfFintype Bool).bind (fun bit =>
      (world scheme ()).eval (worldRealize scheme () (liftOracleForger (fixedForger bit))
        (fun verified ⟨msg, _⟩ pairs => verified && !(pairs.map Prod.fst).contains msg))) := by
  apply eval_worldRealize_eq_bind
  intro Store oracle s
  simp only [randomizedForger, OracleComp.interpret_bind, StateT.run_bind,
    ProbOracleComp.run_interpret_sample, ProbComp.eval_uniform, PMF.monad_bind_eq_bind,
    PMF.bind_map, Function.comp_def]

end ComplexityTests.SavedCoinReplacement

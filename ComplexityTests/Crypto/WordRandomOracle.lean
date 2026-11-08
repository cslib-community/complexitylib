/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Signature.WordRandomOracle
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Probability.PMF.Bind

/-! Actual native word forgers, shared signing/hash caches, freshness, and off-support tapes. -/

namespace ComplexityTests.Crypto.WordRandomOracle

open Cslib Cslib.Probability Cslib.Crypto.Protocols.ROMSignature
open Turing Turing.MultiTapeTM Turing.MultiTapePTM

private def machine : MultiTapePTM 0 Bool Bool Bool where
  initial := false
  tr state _ _ answer bit := if state then
    .step { inputTape := 0, workTapes := Fin.elim0, output := answer true, state := none }
      (fun _ => none) (fun _ => 0)
    else .query bit true

private def audit : (q : List Bool ⊕ List Bool) →
    StateT (List (List Bool ⊕ List Bool)) Id
      (ForgerSpec (List Bool) (List Bool) (List Bool) Bool q)
  | .inl word, log => (word, log ++ [.inl word])
  | .inr word, log => (word.headD false, log ++ [.inr word])

-- A short word that is not a canonical pair encoding remains a distinct hash payload.
example : (OracleComp.interpret audit (do
    let _ ← wordQuery encBool true [true]
    let _ ← wordQuery encBool true []
    wordQuery encBool false [true])).run [] =
      ([true], [.inr [true], .inr [], .inl [true]]) := rfl

-- Oversized public keys make no calls, even with an arbitrarily overlong tape.
example (coins : List Bool) :
    (OracleComp.interpret audit
      ((savedCoinForger machine encBool 2 0 0 0 0).forge [true] coins)).run [] =
      (([], []), []) := rfl

-- An empty tape has no output. The existing total decoder handles that malformed pair word.
example : (OracleComp.interpret audit
    ((savedCoinForger machine encBool 2 0 0 0 0).forge [] [])).run [] =
      (([], []), []) := rfl

-- Extra saved bits are ignored at the original two-step cutoff; the selected query is retained.
example (more : List Bool) :
    (OracleComp.interpret audit
      ((savedCoinForger machine encBool 2 0 0 0 0).forge [] ([true, false] ++ more))).run [] =
      (([], []), [.inr []]) := rfl

example : (savedCoinForger machine encBool 2 0 0 0 0).CallBounded 2 2 :=
  callBounded_savedCoinForger machine encBool 2 0 0 0 0

-- The guarded, truncated and decoded replay has a certificate on the entire supplied triple.
example : IsOraclePPTOn (encPair encUnary (encPair encBits encBits)) (encPair encBits encBits)
    (savedWordReplay machine (fun op word => ProbOracleComp.query (op, word)) 2 0 0 0) := by
  fun_prop

private def interaction (fresh : Bool) :
    OracleComp (fun _ : Bool × List Bool => List Bool) (List Bool × List Bool) := do
  let signed ← List.take 1 <$> OracleComp.query (false, [])
  let signedAgain ← List.take 1 <$> OracleComp.query (false, [])
  let signedHash ← List.take 1 <$> OracleComp.query (true, [])
  let newHash ← List.take 1 <$> OracleComp.query (true, [true])
  let newHashAgain ← List.take 1 <$> OracleComp.query (true, [true])
  let stable := signed == signedAgain && signed == signedHash && newHash == newHashAgain
  return if stable then (if fresh then [true] else [], if fresh then newHash else signed)
    else ([], [])

private def nativeForger (fresh : Bool) (_ : ℕ) (_ : List Bool) :
    WordOracleComp Bool (List Bool × List Bool) := OracleComp.liftRight (interaction fresh)

private theorem nativeForger_ppt (fresh : Bool) :
    IsOraclePPT (encPair encBits encBits) (nativeForger fresh) := by
  unfold IsOraclePPT nativeForger interaction
  simp only [OracleComp.liftRight, OracleComp.interpret_bind, OracleComp.interpret_map,
    OracleComp.interpret_query, OracleComp.interpret_pure]
  change IsOraclePPTOn _ _ (fun _ => do
    let signed ← List.take 1 <$> ProbOracleComp.query (false, [])
    let signedAgain ← List.take 1 <$> ProbOracleComp.query (false, [])
    let signedHash ← List.take 1 <$> ProbOracleComp.query (true, [])
    let newHash ← List.take 1 <$> ProbOracleComp.query (true, [true])
    let newHashAgain ← List.take 1 <$> ProbOracleComp.query (true, [true])
    let stable := signed == signedAgain && signed == signedHash && newHash == newHashAgain
    return if stable then (if fresh then [true] else [], if fresh then newHash else signed)
      else ([], []))
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · fun_prop
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · fun_prop
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · fun_prop
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · fun_prop
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · fun_prop
  cases fresh <;> dsimp only <;> fun_prop

private noncomputable def scheme :
    Scheme (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) Bool where
  keyGen := PMF.pure ([], [])
  SignCoins := Unit
  signCoins _ _ := PMF.pure ()
  sign _ msg _ := do
    let digest ← OracleComp.query msg
    return encBool digest
  verify _ msg sig := do
    let digest ← OracleComp.query msg
    return sig == encBool digest

private noncomputable def explicitForger (fresh : Bool) :
    Forger (List Bool) (List Bool) (List Bool) (List Bool) Bool where
  Coins := Unit
  coins := PMF.pure ()
  forge _ _ := OracleComp.interpret (fun q => wordQuery encBool q.1 q.2) (interaction fresh)

-- Signing and hashing share the cache, including after repeated signing and hash queries.
-- The fresh forgery succeeds; replaying a signed message is rejected despite valid verification.
example (fresh : Bool) : eufCmaGame scheme (explicitForger fresh) = PMF.pure fresh := by
  simp only [eufCmaGame, scheme, explicitForger, interaction, wordQuery,
    OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_map,
    OracleComp.interpret_pure, StateT.run_bind, StateT.run_pure, StateT.run_map,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.monad_map_eq_map, PMF.pure_bind]
  simp only [handler, oracle, OracleComp.interpret_bind, OracleComp.interpret_query,
    OracleComp.interpret_pure, StateT.run_bind, StateT.run_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind, PMF.bind_bind]
  cases fresh <;> simp [memoize, StateT.run, encBool_apply, PMF.bind_bind, List.lookup_cons,
    Bool.beq_eq_decide_eq]

-- The actual native program is routed into that same existing typed game.
example (fresh : Bool) (n : ℕ) :
    worldGame scheme (fun pk => routeWordProgram encBool (nativeForger fresh n pk))
      (fun verified ⟨msg, _⟩ pairs => verified && !(pairs.map Prod.fst).contains msg) =
    eufCmaGame scheme (explicitForger fresh) := by
  rw [eufCmaGame_eq_worldGame]
  simp only [worldGame, scheme, explicitForger, PMF.monad_bind_eq_bind, PMF.pure_bind]
  congr 2 with verified msig pairs : 3
  simp only [List.contains_eq_mem]
  congr 2
  exact decide_eq_decide.mpr Iff.rfl

-- The final bridge applies to actual key generation and an actual efficient oracle forger.
example (fresh : Bool) : ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (replay : MultiTapePTM k Bool Control Bool) (c d keyC keyD : ℕ),
    ∀ n,
      worldGame scheme (fun pk => routeWordProgram encBool (nativeForger fresh n pk))
        (fun verified ⟨msg, _⟩ pairs => verified && !(pairs.map Prod.fst).contains msg) =
      eufCmaGame scheme (savedCoinForger replay encBool c d keyC keyD n) := by
  have hgen : IsPPTOn encUnary (encPair encBits encBits)
      (fun _ => (pure ([], []) : ProbComp (List Bool × List Bool))) := by fun_prop
  obtain ⟨k, Control, hfinite, replay, c, d, keyC, keyD, _, hgame⟩ :=
    exists_eufCmaGame_savedCoinForger hgen (nativeForger_ppt fresh)
  exact ⟨k, Control, hfinite, replay, c, d, keyC, keyD, fun n =>
    (hgame n Bool encBool scheme rfl).2⟩

end ComplexityTests.Crypto.WordRandomOracle

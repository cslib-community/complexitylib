/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Signature
public import Complexity.Crypto.Computational.WordSignature
public import Complexity.Crypto.Protocols.Signature.RandomOracle
import Complexity.Languages.Probabilistic.Oracle.Simulation
import Complexity.Probability.PMF
import Complexity.Probability.PMF.Bind

/-!
# Bridge between typed `ROMSignature` and computational word signature schemes

`Cslib.Crypto.Protocols.ROMSignature.Scheme` models signatures in the random-oracle model with
typed key and coin laws and shared oracle access to `H : Query → Digest`, whereas
`Cslib.Crypto.SignatureScheme` and `Cslib.Crypto.WordSignatureScheme` model standard-model
computational bit-string signature schemes (`List Bool`) with strict PPT certificates.

This module bridges the two layers by specializing the random oracle to the trivial unit oracle
(`Query := Empty`, `Digest := Unit`) and routing signing coins through the word-level signing
distribution `ProbComp.eval (S.sign sk msg)`:

* **Fixed-length `SignatureScheme` bridge (`SignatureScheme.toROMSignatureScheme`,
  `SignatureScheme.correctOn_toROMSignatureScheme`, `SignatureScheme.liftWordForger`,
  `SignatureScheme.romEufCmaGame`, `SignatureScheme.eval_eufCmaGame_eq_romEufCmaGame`)**:
  at security parameter `n`, `S.toROMSignatureScheme n` is a closed `ROMSignature.Scheme` on
  `List Bool` messages satisfying `ROMSignature.Scheme.CorrectOn (fun msg => msg.length = n)`.
  Evaluating `S.eufCmaGame adversary n` is equal to `ROMSignature.worldGame` on
  `S.toROMSignatureScheme n` and `liftWordForger adversary n` with the final-message admissibility
  guard `msg.length == n` and final-message freshness `!(pairs.map Prod.fst).contains msg`.
* **Unrestricted-length `WordSignatureScheme` bridge (`WordSignatureScheme.toROMSignatureScheme`,
  `WordSignatureScheme.correct_toROMSignatureScheme`, `WordSignatureScheme.romEufCmaGame`,
  `WordSignatureScheme.eval_eufCmaGame_eq_romEufCmaGame`)**:
  because `WordSignatureScheme.verify_sign` holds for all `msg : List Bool`,
  `S.toROMSignatureScheme n` satisfies unrestricted `ROMSignature.Scheme.Correct`, and
  `ProbComp.eval (S.eufCmaGame adversary n)` equals the unguarded `ROMSignature.worldGame` on
  `S.toROMSignatureScheme n`.

## Main definitions

* `Cslib.Crypto.SignatureScheme.toROMSignatureScheme`: view a `SignatureScheme` at parameter `n` as
  a closed typed `ROMSignature.Scheme`.
* `Cslib.Crypto.SignatureScheme.liftWordForger`: lift a computational `Forger` at parameter `n` into
  the `ProbOracleComp (ROMSignature.ForgerSpec ...)` interface.
* `Cslib.Crypto.SignatureScheme.romEufCmaGame`: the typed `ROMSignature.worldGame` realization of
  `SignatureScheme.eufCmaGame`.
* `Cslib.Crypto.WordSignatureScheme.toROMSignatureScheme`: view a `WordSignatureScheme` at parameter
  `n` as a closed typed `ROMSignature.Scheme`.
* `Cslib.Crypto.WordSignatureScheme.romEufCmaGame`: the typed `ROMSignature.worldGame` realization
  of `WordSignatureScheme.eufCmaGame`.

## Main results

* `Cslib.Crypto.SignatureScheme.correctOn_toROMSignatureScheme`: `S.toROMSignatureScheme n` is
  correct on `n`-bit messages (`msg.length = n`).
* `Cslib.Crypto.SignatureScheme.runWith_forgerWorldImpl_runLoggedForger_liftWordForger`,
  `Cslib.Crypto.SignatureScheme.eval_eufCmaGame_eq_romEufCmaGame`,
  `Cslib.Crypto.SignatureScheme.succProbability_eufCmaGame_eq_romEufCmaGame`: exact execution and
  game-law equivalence between `SignatureScheme.eufCmaGame` and `SignatureScheme.romEufCmaGame`.
* `Cslib.Crypto.WordSignatureScheme.correct_toROMSignatureScheme`: `S.toROMSignatureScheme n`
  satisfies unrestricted `ROMSignature.Scheme.Correct`.
* `Cslib.Crypto.WordSignatureScheme.runWith_forgerWorldImpl_runLoggedForger_liftWordForger`,
  `Cslib.Crypto.WordSignatureScheme.eval_eufCmaGame_eq_romEufCmaGame`,
  `Cslib.Crypto.WordSignatureScheme.succProbability_eufCmaGame_eq_romEufCmaGame`: exact execution
  and game-law equivalence between `WordSignatureScheme.eufCmaGame` and
  `WordSignatureScheme.romEufCmaGame`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 13.1 and 13.2.1.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability OracleComp Protocols

namespace SignatureScheme

/-- View a computational `SignatureScheme` at security parameter `n` as a closed typed
random-oracle signature scheme (`Query = Empty`, `Digest = Unit`) whose signer coins are the
signature distribution `ProbComp.eval (S.sign sk msg)`. -/
noncomputable def toROMSignatureScheme (S : SignatureScheme) (n : ℕ) :
    ROMSignature.Scheme (List Bool) (List Bool) (List Bool) (List Bool) Empty Unit where
  keyGen := ProbComp.eval (S.keyGen n)
  SignCoins := List Bool
  signCoins sk msg := ProbComp.eval (S.sign sk msg)
  sign _ _ sig := pure sig
  verify pk msg sig := pure (S.verify pk msg sig)

@[simp]
theorem toROMSignatureScheme_keyGen (S : SignatureScheme) (n : ℕ) :
    (S.toROMSignatureScheme n).keyGen = ProbComp.eval (S.keyGen n) := rfl

@[simp]
theorem toROMSignatureScheme_SignCoins (S : SignatureScheme) (n : ℕ) :
    (S.toROMSignatureScheme n).SignCoins = List Bool := rfl

@[simp]
theorem toROMSignatureScheme_signCoins (S : SignatureScheme) (n : ℕ) (sk msg : List Bool) :
    (S.toROMSignatureScheme n).signCoins sk msg = ProbComp.eval (S.sign sk msg) := rfl

@[simp]
theorem toROMSignatureScheme_sign (S : SignatureScheme) (n : ℕ) (sk msg sig : List Bool) :
    (S.toROMSignatureScheme n).sign sk msg sig = pure sig := rfl

@[simp]
theorem toROMSignatureScheme_verify (S : SignatureScheme) (n : ℕ) (pk msg sig : List Bool) :
    (S.toROMSignatureScheme n).verify pk msg sig = pure (S.verify pk msg sig) := rfl

/-- The typed ROM view `S.toROMSignatureScheme n` satisfies `ROMSignature.Scheme.CorrectOn` on
`n`-bit messages (`msg.length = n`). -/
theorem correctOn_toROMSignatureScheme (S : SignatureScheme) (n : ℕ) :
    (S.toROMSignatureScheme n).CorrectOn (fun msg => msg.length = n) := by
  dsimp only [ROMSignature.Scheme.CorrectOn, toROMSignatureScheme,
    ProbOracleComp.runWith, OracleComp.runWith]
  intro keys hkeys msg hmsg sig hsig cache signed hsigned verified hverified
  simp only [OracleComp.interpret_pure, StateT.run_pure,
    PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hsigned hverified
  subst hsigned hverified
  exact S.verify_sign n keys hkeys msg hmsg sig hsig

/-- Lift a computational `Forger` (`ℕ → List Bool → WordOracleComp Unit (List Bool × List Bool)`)
at security parameter `n` into the `ProbOracleComp (ROMSignature.ForgerSpec ...)` interface of
`S.toROMSignatureScheme n`, forwarding private fair-coin samples and routing signing calls
`((), msg)` to `.inl msg`. -/
def liftWordForger (adversary : Forger) (n : ℕ) (pk : List Bool) :
    ProbOracleComp
      (ROMSignature.ForgerSpec (List Bool) Empty (List Bool) Unit)
      (List Bool × List Bool) :=
  OracleComp.interpret
    (OracleComp.sumHandler
      (fun k =>
        ProbOracleComp.sample
          (spec := ROMSignature.ForgerSpec (List Bool) Empty (List Bool) Unit)
          (ProbComp.unifFin k))
      (fun ⟨_, msg⟩ =>
        ProbOracleComp.query
          (spec := ROMSignature.ForgerSpec (List Bool) Empty (List Bool) Unit)
          (.inl msg)))
    (adversary n pk)

/-- Running `liftWordForger adversary n pk` with `ROMSignature.runLoggedForger` in
`ROMSignature.forgerWorldImpl (S.toROMSignatureScheme n) sk` and projecting the logged
`(message, signature)` pairs to their messages reproduces `S.signingOracle sk`. -/
theorem runWith_forgerWorldImpl_runLoggedForger_liftWordForger
    (S : SignatureScheme) (adversary : Forger) (n : ℕ) (pk sk : List Bool) :
    (ProbOracleComp.runWith
      (ROMSignature.forgerWorldImpl (S.toROMSignatureScheme n) sk)
      (ROMSignature.runLoggedForger (liftWordForger adversary n pk)) []).map
        (fun ⟨⟨msig, pairs⟩, _⟩ => (msig, pairs.map Prod.fst)) =
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (S.signingOracle sk)) (adversary n pk)).run []) := by
  rw [ProbOracleComp.eval_run_interpret]
  unfold ProbOracleComp.runWith OracleComp.runWith ROMSignature.runLoggedForger liftWordForger
  have hcomp :
      OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => StateT.lift
            (ProbOracleComp.sample
              (spec := ROMSignature.ForgerSpec (List Bool) Empty (List Bool) Unit)
              (ProbComp.unifFin k)))
          ROMSignature.logSigning)
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun k =>
              ProbOracleComp.sample
                (spec := ROMSignature.ForgerSpec (List Bool) Empty (List Bool) Unit)
                (ProbComp.unifFin k))
            (fun ⟨_, msg⟩ =>
              ProbOracleComp.query
                (spec := ROMSignature.ForgerSpec (List Bool) Empty (List Bool) Unit)
                (.inl msg)))
          (adversary n pk)) =
      OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => StateT.lift
            (ProbOracleComp.sample
              (spec := ROMSignature.ForgerSpec (List Bool) Empty (List Bool) Unit)
              (ProbComp.unifFin k)))
          (fun ⟨_, msg⟩ => ROMSignature.logSigning (.inl msg)))
        (adversary n pk) := by
    rw [OracleComp.interpret_interpret]
    congr 1
    funext q
    cases q with
    | inl k =>
      simp [OracleComp.sumHandler, ProbOracleComp.sample, ProbComp.unifFin,
        OracleComp.interpret_query]
    | inr req =>
      simp [OracleComp.sumHandler, ProbOracleComp.query, OracleComp.interpret_query]
  rw [hcomp, ProbOracleComp.run_interpret_run_interpret, PMF.map_comp]
  have hsim := ProbOracleComp.run_interpret_map_state
    (oracle := fun (q : Unit × List Bool)
        (state : List (List Bool × List Bool) × List (Empty × Unit)) =>
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (ROMSignature.forgerWorldImpl (S.toROMSignatureScheme n) sk))
        ((ROMSignature.logSigning (.inl q.2)).run state.1)).run state.2).map
          (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)))
    (oracle' := fun q s => ProbComp.eval (S.signingOracle sk q s))
    (represent := fun (state : List (List Bool × List Bool) × List (Empty × Unit)) =>
      state.1.map Prod.fst)
    (step := by
      intro ⟨⟨⟩, msg⟩ ⟨pairs, curCache⟩
      change (((OracleComp.interpret (m := StateT (List (Empty × Unit)) PMF)
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (ROMSignature.forgerWorldImpl (S.toROMSignatureScheme n) sk))
        (ROMSignature.logSigning (.inl msg) pairs)).run curCache).map
          (fun ⟨⟨a, b⟩, c⟩ => (a, b, c))).map
            (fun ⟨a, s'⟩ => (a, s'.1.map Prod.fst)) =
        ProbComp.eval (S.signingOracle sk ((), msg) (pairs.map Prod.fst))
      simp only [ROMSignature.logSigning, ROMSignature.forgerWorldImpl, toROMSignatureScheme,
        signingOracle, OracleComp.sumHandler, ProbOracleComp.query, OracleComp.interpret_bind,
        OracleComp.interpret_pure, OracleComp.interpret_query, StateT.run_bind, StateT.run_pure,
        ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        PMF.map_bind, PMF.pure_map, List.map_cons]
      rw [StateT.run, PMF.bind_bind]
      refine PMF.bind_congr_on_support _ _ _ fun sig _ => ?_
      simp)
    (adversary n pk) ([], [])
  exact hsim

/-- The typed `ROMSignature.worldGame` realization of `S.eufCmaGame adversary n`:
evaluate `S.toROMSignatureScheme n` in `ROMSignature.world` against `liftWordForger adversary n`
with the `n`-bit final-message admissibility guard `msg.length == n` and final-message
freshness `!(pairs.map Prod.fst).contains msg`. -/
noncomputable def romEufCmaGame (S : SignatureScheme) (adversary : Forger) (n : ℕ) :
    PMF Bool :=
  ROMSignature.worldGame (S.toROMSignatureScheme n) (liftWordForger adversary n)
    (fun verified ⟨msg, _⟩ pairs =>
      (msg.length == n) && !(pairs.map Prod.fst).contains msg && verified)

/-- Exact game-law correspondence: `ProbComp.eval (S.eufCmaGame adversary n)` is equal to the
typed `ROMSignature` game `S.romEufCmaGame adversary n`. -/
theorem eval_eufCmaGame_eq_romEufCmaGame (S : SignatureScheme) (adversary : Forger) (n : ℕ) :
    ProbComp.eval (S.eufCmaGame adversary n) = S.romEufCmaGame adversary n := by
  unfold eufCmaGame romEufCmaGame ROMSignature.worldGame
  simp only [toROMSignatureScheme_keyGen, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun keys _ => ?_
  rw [ROMSignature.eval_world_worldRealize,
    ← S.runWith_forgerWorldImpl_runLoggedForger_liftWordForger adversary n keys.1 keys.2]
  simp only [toROMSignatureScheme_verify, OracleComp.interpret_pure, StateT.run_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map, PMF.pure_bind]
  rfl

/-- The success probability of any computational forger in `S.eufCmaGame adversary n` equals its
success probability in `S.romEufCmaGame adversary n`. -/
@[simp]
theorem succProbability_eufCmaGame_eq_romEufCmaGame
    (S : SignatureScheme) (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (S.eufCmaGame adversary n)) =
      Game.succProbability (S.romEufCmaGame adversary n) := by
  rw [S.eval_eufCmaGame_eq_romEufCmaGame adversary n]

end SignatureScheme

namespace WordSignatureScheme

/-- View a computational `WordSignatureScheme` at security parameter `n` as a closed typed
random-oracle signature scheme (`Query = Empty`, `Digest = Unit`). -/
noncomputable abbrev toROMSignatureScheme (S : WordSignatureScheme) (n : ℕ) :
    ROMSignature.Scheme (List Bool) (List Bool) (List Bool) (List Bool) Empty Unit :=
  S.toSignatureScheme.toROMSignatureScheme n

/-- Because `WordSignatureScheme.verify_sign` holds for all `msg : List Bool`, the typed ROM view
`S.toROMSignatureScheme n` satisfies unrestricted `ROMSignature.Scheme.Correct`. -/
theorem correct_toROMSignatureScheme (S : WordSignatureScheme) (n : ℕ) :
    (S.toROMSignatureScheme n).Correct := by
  dsimp only [ROMSignature.Scheme.Correct, toROMSignatureScheme,
    SignatureScheme.toROMSignatureScheme, toSignatureScheme_keyGen, toSignatureScheme_sign,
    toSignatureScheme_verify, ProbOracleComp.runWith, OracleComp.runWith]
  intro keys hkeys msg sig hsig cache signed hsigned verified hverified
  simp only [OracleComp.interpret_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
    PMF.mem_support_pure_iff] at hsigned hverified
  subst hsigned hverified
  exact S.verify_sign n keys.1 keys.2 hkeys msg sig hsig

/-- Running `SignatureScheme.liftWordForger adversary n pk` in
`ROMSignature.forgerWorldImpl (S.toROMSignatureScheme n) sk` and projecting the logged pairs to
their messages reproduces `S.signingOracle sk`. -/
theorem runWith_forgerWorldImpl_runLoggedForger_liftWordForger
    (S : WordSignatureScheme) (adversary : Forger) (n : ℕ) (pk sk : List Bool) :
    (ProbOracleComp.runWith
      (ROMSignature.forgerWorldImpl (S.toROMSignatureScheme n) sk)
      (ROMSignature.runLoggedForger (SignatureScheme.liftWordForger adversary n pk)) []).map
        (fun ⟨⟨msig, pairs⟩, _⟩ => (msig, pairs.map Prod.fst)) =
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (S.signingOracle sk)) (adversary n pk)).run []) :=
  S.toSignatureScheme.runWith_forgerWorldImpl_runLoggedForger_liftWordForger adversary n pk sk

/-- The typed `ROMSignature.worldGame` realization of `WordSignatureScheme.eufCmaGame`:
evaluate `S.toROMSignatureScheme n` in `ROMSignature.world` against
`SignatureScheme.liftWordForger adversary n` with unrestricted final-message freshness
`!(pairs.map Prod.fst).contains msg`. -/
noncomputable def romEufCmaGame (S : WordSignatureScheme) (adversary : Forger) (n : ℕ) :
    PMF Bool :=
  ROMSignature.worldGame (S.toROMSignatureScheme n) (SignatureScheme.liftWordForger adversary n)
    (fun verified ⟨msg, _⟩ pairs => !(pairs.map Prod.fst).contains msg && verified)

/-- Exact game-law correspondence for unrestricted-length word signature schemes:
`ProbComp.eval (S.eufCmaGame adversary n)` is equal to `S.romEufCmaGame adversary n`. -/
theorem eval_eufCmaGame_eq_romEufCmaGame (S : WordSignatureScheme) (adversary : Forger) (n : ℕ) :
    ProbComp.eval (S.eufCmaGame adversary n) = S.romEufCmaGame adversary n := by
  unfold eufCmaGame romEufCmaGame ROMSignature.worldGame
  simp only [toROMSignatureScheme, SignatureScheme.toROMSignatureScheme_keyGen,
    toSignatureScheme_keyGen, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun keys _ => ?_
  rw [ROMSignature.eval_world_worldRealize,
    ← S.runWith_forgerWorldImpl_runLoggedForger_liftWordForger adversary n keys.1 keys.2]
  simp only [toROMSignatureScheme, SignatureScheme.toROMSignatureScheme_verify,
    toSignatureScheme_verify, OracleComp.interpret_pure, StateT.run_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map, PMF.pure_bind]
  rfl

/-- The success probability of any computational forger in `S.eufCmaGame adversary n` equals its
success probability in `S.romEufCmaGame adversary n`. -/
@[simp]
theorem succProbability_eufCmaGame_eq_romEufCmaGame
    (S : WordSignatureScheme) (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (S.eufCmaGame adversary n)) =
      Game.succProbability (S.romEufCmaGame adversary n) := by
  rw [S.eval_eufCmaGame_eq_romEufCmaGame adversary n]

end WordSignatureScheme

end Cslib.Crypto

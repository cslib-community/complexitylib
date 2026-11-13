/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Signature
public import CslibFrontier.Crypto.Computational.Signature.Scheme
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation

/-!
# Word-level signature games as typed forgery experiments

At each security parameter `n`, the word-level experiments `SignatureScheme.eufCmaGame` and
`SignatureScheme.eufOneTimeGame` are the typed experiments `eufCmaExperiment` and
`oneTimeEufCmaExperiment` of one fixed scheme. That scheme is `S.toScheme n`: the scheme with the
same algorithms at parameter `n` whose verification accepts only `n`-bit messages. The forger is
`adversary.toTyped n`: the word forger with the unit operation tag dropped from its queries. The
word game keeps the list of queried messages, newest first; the typed experiment keeps the log of
answered pairs, oldest first, and the two agree up to that representation.

## Main definitions

* `Cslib.Crypto.SignatureScheme.toScheme`: the typed scheme of a word-level scheme at parameter `n`.
* `Cslib.Crypto.Forger.toTyped`: the typed forger of a word-level forger at parameter `n`.

## Main results

* `Cslib.Crypto.SignatureScheme.eufCmaGame_eq_eufCmaExperiment`,
  `Cslib.Crypto.SignatureScheme.eufOneTimeGame_eq_oneTimeEufCmaExperiment`: the word games have
  the distributions of the typed experiments.
* `Cslib.Crypto.SignatureScheme.succProbability_eufCmaGame`,
  `Cslib.Crypto.SignatureScheme.succProbability_eufOneTimeGame`: the same statements for the
  success probabilities.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability
open OracleComp (sumHandler)

/-- The typed forger played by the word forger `adversary` at parameter `n` on the public key
`pk`: each signing request `((), m)` becomes the query `m`, and private sampling is unchanged. -/
def Forger.toTyped (adversary : Forger) (n : ℕ) : Signature.Forger (List Bool) (List Bool)
    (List Bool) := fun pk =>
  OracleComp.interpret
    (sumHandler (fun k => OracleComp.query (spec := probOracleSpec fun _ : List Bool => List Bool)
      (.inl k)) (fun request => ProbOracleComp.query request.2))
    (adversary n pk)

namespace SignatureScheme

/-- The typed scheme of `S` at parameter `n`: the same algorithms at `n`, restricted to `n`-bit
messages, as in the word-level games. -/
def toScheme (S : SignatureScheme) (n : ℕ) :
    Signature.Scheme (List Bool) (List Bool) (List Bool) (List Bool) :=
  Signature.Scheme.restrict ⟨S.keyGen n, S.sign, S.verify⟩ (·.length == n)

@[simp] theorem toScheme_keyGen (S : SignatureScheme) (n : ℕ) :
    (S.toScheme n).keyGen = S.keyGen n := rfl

@[simp] theorem toScheme_sign (S : SignatureScheme) (n : ℕ) : (S.toScheme n).sign = S.sign := rfl

@[simp] theorem toScheme_verify (S : SignatureScheme) (n : ℕ) (pk msg sig : List Bool) :
    (S.toScheme n).verify pk msg sig = (msg.length == n && S.verify pk msg sig) := rfl

/-- Running the typed forger against a logging signer and dropping the signatures from the log
is running the word forger against the word oracle that keeps the queried messages, newest
first, whenever each oracle call agrees under that representation. -/
private theorem eval_runLogWith_toTyped (adversary : Forger) (n : ℕ) (pk : List Bool)
    (signer : List (List Bool × List Bool) → List Bool → Option (ProbComp (List Bool)))
    (oracle : Unit × List Bool → StateT (List (List Bool)) ProbComp (List Bool))
    (step : ∀ (request : Unit × List Bool) (log : List (List Bool × List Bool)),
      (ProbComp.eval (ProbOracleComp.logOracle signer request.2 log)).map
          (fun (a, log') => (a, (log'.map Prod.fst).reverse)) =
        ProbComp.eval (oracle request ((log.map Prod.fst).reverse))) :
    (ProbComp.eval ((adversary.toTyped n pk).runLogWith signer)).map
        (fun (a, log) => (a, (log.map Prod.fst).reverse)) =
      ProbComp.eval ((OracleComp.interpret
        (sumHandler (fun k => StateT.lift (ProbComp.unifFin k)) oracle) (adversary n pk)).run
          []) := by
  have hhandler : (fun q => OracleComp.interpret
      (sumHandler (fun k => StateT.lift (ProbComp.unifFin k)) (ProbOracleComp.logOracle signer))
      (sumHandler (fun k => OracleComp.query (spec := probOracleSpec fun _ : List Bool =>
          List Bool) (.inl k)) (fun request : Unit × List Bool => ProbOracleComp.query request.2)
        q)) =
      sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (fun request : Unit × List Bool => ProbOracleComp.logOracle signer request.2) := by
    funext q
    cases q <;> simp [ProbOracleComp.query]
  rw [ProbOracleComp.runLogWith, ProbOracleComp.runState, Forger.toTyped,
    OracleComp.interpret_interpret, hhandler,
    ProbOracleComp.eval_run_interpret, ProbOracleComp.eval_run_interpret]
  exact ProbOracleComp.run_interpret_map_state
    (fun request log => ProbComp.eval (ProbOracleComp.logOracle signer request.2 log))
    (fun request queried => ProbComp.eval (oracle request queried))
    (fun log => (log.map Prod.fst).reverse) step (adversary n pk) []

/-- The word post-processing `msg.length = n`, `msg` not queried, valid signature is the typed
post-processing on the represented log. -/
private theorem post_eq (S : SignatureScheme) (n : ℕ) (pk msg sig : List Bool)
    (log : List (List Bool × List Bool)) :
    ((msg.length == n) && !((log.map Prod.fst).reverse.contains msg) && S.verify pk msg sig) =
      ((S.toScheme n).verify pk msg sig && freshMessage msg sig log) := by
  simp only [toScheme_verify, freshMessage, List.contains_reverse]
  cases msg.length == n <;> cases S.verify pk msg sig <;> simp

/-- At each parameter `n`, the word-level EUF-CMA game is the typed EUF-CMA experiment of
`S.toScheme n` played by `adversary.toTyped n`. -/
theorem eufCmaGame_eq_eufCmaExperiment (S : SignatureScheme) (adversary : Forger) (n : ℕ) :
    ProbComp.eval (S.eufCmaGame adversary n) =
      ProbComp.eval ((S.toScheme n).eufCmaExperiment (adversary.toTyped n)) := by
  simp only [eufCmaGame, forgeExperiment, toScheme_keyGen, ProbComp.eval_bind,
    ProbComp.eval_pure]
  congr 1
  funext keys
  obtain ⟨pk, sk⟩ := keys
  dsimp only
  rw [← eval_runLogWith_toTyped adversary n pk (Signer.ofSign (S.toScheme n).sign sk)
    (S.signingOracle sk) fun request log => by
      simp [ProbOracleComp.logOracle, signingOracle, ProbComp.eval_map, PMF.map_comp,
        Function.comp_def]]
  rw [PMF.bind_map]
  congr 1
  funext x
  obtain ⟨⟨msg, sig⟩, log⟩ := x
  simp only [Function.comp_apply, post_eq]

/-- At each parameter `n`, the word-level one-time EUF-CMA game is the typed one-time EUF-CMA
experiment of `S.toScheme n` played by `adversary.toTyped n`. -/
theorem eufOneTimeGame_eq_oneTimeEufCmaExperiment (S : SignatureScheme) (adversary : Forger)
    (n : ℕ) :
    ProbComp.eval (S.eufOneTimeGame adversary n) =
      ProbComp.eval ((S.toScheme n).oneTimeEufCmaExperiment (adversary.toTyped n)) := by
  simp only [eufOneTimeGame, forgeExperiment, toScheme_keyGen, ProbComp.eval_bind,
    ProbComp.eval_pure]
  congr 1
  funext keys
  obtain ⟨pk, sk⟩ := keys
  dsimp only
  rw [← eval_runLogWith_toTyped adversary n pk ((Signer.ofSign (S.toScheme n).sign).oneTime sk)
    (S.oneTimeSigningOracle sk) fun request log => by
      cases log with
      | nil =>
        simp [ProbOracleComp.logOracle, oneTimeSigningOracle, oneTimeSigningOracleOf,
          ProbComp.eval_map, PMF.map_comp, Function.comp_def]
      | cons p log =>
        simp only [ProbOracleComp.logOracle, toScheme_sign, Signer.oneTime_cons, ProbComp.eval_pure,
          PMF.pure_map, List.map_cons, List.reverse_cons, oneTimeSigningOracle,
          oneTimeSigningOracleOf, List.isEmpty_iff, List.append_eq_nil_iff, List.reverse_eq_nil_iff,
          List.map_eq_nil_iff, List.cons_ne_self, and_false, ↓reduceIte]
        rfl]
  rw [PMF.bind_map]
  congr 1
  funext x
  obtain ⟨⟨msg, sig⟩, log⟩ := x
  simp only [Function.comp_apply, post_eq]

/-- The success probability of the word-level EUF-CMA game at `n` is that of the typed
experiment. -/
theorem succProbability_eufCmaGame (S : SignatureScheme) (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (S.eufCmaGame adversary n)) =
      ((S.toScheme n).eufCmaExperiment (adversary.toTyped n)).succProbability := by
  rw [Experiment.succProbability, eufCmaGame_eq_eufCmaExperiment]

/-- The success probability of the word-level one-time EUF-CMA game at `n` is that of the typed
experiment. -/
theorem succProbability_eufOneTimeGame (S : SignatureScheme) (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (S.eufOneTimeGame adversary n)) =
      ((S.toScheme n).oneTimeEufCmaExperiment (adversary.toTyped n)).succProbability := by
  rw [Experiment.succProbability, eufOneTimeGame_eq_oneTimeEufCmaExperiment]

end SignatureScheme

end Cslib.Crypto

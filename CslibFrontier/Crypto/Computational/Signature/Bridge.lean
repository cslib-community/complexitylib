/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.IndexedSignature.Counter
public import CslibFrontier.Crypto.Computational.Signature
public import CslibFrontier.Crypto.Computational.Signature.Scheme
public import CslibFrontier.Crypto.Computational.WordSignature
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation

/-!
# Word-level signature games as typed forgery experiments

At each security parameter `n`, every word-level signature game is a typed forgery experiment of
one fixed scheme, played by the word forger with its requests decoded.

* `SignatureScheme.eufCmaGame` and `SignatureScheme.eufOneTimeGame` are `eufCmaExperiment` and
  `oneTimeEufCmaExperiment` of `S.toScheme n`: the scheme with the same algorithms at parameter
  `n` whose verification accepts only `n`-bit messages.
* `WordSignatureScheme.eufCmaGame` is `eufCmaExperiment` of `S.toScheme n`, with no restriction.
* `IndexedSignatureScheme.indexedEufCmaGame` is the indexed experiment of `S.toScheme n`. The word
  oracle reads every request with the total decoder `requestDecoder`, so the typed forger
  queries the decoded pair.
* `IndexedSignatureScheme.counterEufCmaGame` is the counter experiment of `S.toScheme n`. The word
  oracle answers the encoded pair `(j, σ)` and the empty word once the capacity is used up. The
  typed forger `adversary.toCounter (S.capacity n) n` counts its own queries to tell the two
  apart, so it encodes every answer exactly as the word oracle does.

The word games keep the list of queried messages, newest first; the typed experiment keeps the log
of answered pairs, oldest first, and the two agree up to that representation.

## Main definitions

* `Cslib.Crypto.SignatureScheme.toScheme`, `Cslib.Crypto.WordSignatureScheme.toScheme`,
  `Cslib.Crypto.IndexedSignatureScheme.toScheme`: the typed scheme of a word-level scheme at
  parameter `n`.
* `Cslib.Crypto.Forger.toTyped`, `Cslib.Crypto.IndexedForger.toTyped`,
  `Cslib.Crypto.Forger.toCounter`: the typed forger of a word-level forger at parameter `n`.

## Main results

* `Cslib.Crypto.Forger.eval_eufCmaExperiment_toTyped`,
  `Cslib.Crypto.Forger.eval_eufCmaExperiment_restrict_toTyped`: the EUF-CMA experiment of any typed
  scheme on words, restricted or not, played by a word forger, is the word-level game against the
  signing oracle that records the queried messages.
* `Cslib.Crypto.SignatureScheme.eufCmaGame_eq_eufCmaExperiment`,
  `Cslib.Crypto.SignatureScheme.eufOneTimeGame_eq_oneTimeEufCmaExperiment`,
  `Cslib.Crypto.WordSignatureScheme.eufCmaGame_eq_eufCmaExperiment`,
  `Cslib.Crypto.IndexedSignatureScheme.indexedEufCmaGame_eq_eufCmaExperiment`,
  `Cslib.Crypto.IndexedSignatureScheme.counterEufCmaGame_eq_counterEufCmaExperiment`: the word games
  have the distributions of the typed experiments.
* `Cslib.Crypto.SignatureScheme.succProbability_eufCmaGame`,
  `Cslib.Crypto.SignatureScheme.succProbability_eufOneTimeGame`: the same statements for the
  success probabilities.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open OracleComp (sumHandler)

/-- The typed forger played by the word forger `adversary` at parameter `n` on the public key
`pk`: each signing request `((), m)` becomes the query `m`, and private sampling is unchanged. -/
def Forger.toTyped (adversary : Forger) (n : ℕ) : Signature.Forger (List Bool) (List Bool)
    (List Bool) := fun pk =>
  OracleComp.interpret
    (sumHandler (fun k => OracleComp.query (spec := probOracleSpec fun _ : List Bool => List Bool)
      (.inl k)) (fun request => ProbOracleComp.query request.2))
    (adversary n pk)

/-- The typed indexed forger played by the word forger `adversary` at parameter `n`: each request
word is decoded to the pair `(u, m)` that the word oracle reads from it, and the candidate
`(u, m, σ)` becomes `((u, m), σ)`. -/
def IndexedForger.toTyped (adversary : IndexedForger) (n : ℕ) :
    Signature.Forger (List Bool) (ℕ × List Bool) (List Bool) := fun pk =>
  (fun (u, m, σ) => ((u, m), σ)) <$> OracleComp.interpret
    (sumHandler (fun k => OracleComp.query (spec := probOracleSpec fun _ : ℕ × List Bool =>
      List Bool) (.inl k))
      (fun request => ProbOracleComp.query (IndexedSignatureScheme.requestDecoder.decode
        request.2)))
    (adversary n pk)

/-- One signing request of `Forger.toCounter` against a signer of capacity `cap`, with the number
`j` of answered requests as state: while `j < cap` it forwards the message and returns the answer
`(j, σ)` as the word `encPair encUnary encBits (j, σ)`; afterwards it returns the empty word without
querying. These are the replies of the word counter oracle. -/
def Forger.counterRelay (cap : ℕ) (request : Unit × List Bool) :
    StateT ℕ (ProbOracleComp (fun _ : List Bool => ℕ × List Bool)) (List Bool) := fun j =>
  if j < cap then
    (fun r => (encPair encUnary encBits r, j + 1)) <$> ProbOracleComp.query request.2
  else pure ([], j)

theorem Forger.counterRelay_run (cap : ℕ) (request : Unit × List Bool) (j : ℕ) :
    (Forger.counterRelay cap request).run j =
      if j < cap then
        (fun r => (encPair encUnary encBits r, j + 1)) <$> ProbOracleComp.query request.2
      else pure ([], j) := rfl

/-- The typed counter forger played by the word forger `adversary` at parameter `n` against a
signer of capacity `cap`: it answers the word forger's requests with `counterRelay cap`, counting
them, and decodes its candidate signature word to `(u, σ)`, as the word counter game does. -/
noncomputable def Forger.toCounter (adversary : Forger) (cap n : ℕ) :
    Signature.Forger (List Bool) (List Bool) (ℕ × List Bool) := fun pk =>
  (fun ((m, sig), _) => (m, IndexedSignatureScheme.requestDecoder.decode sig)) <$>
    (OracleComp.interpret
      (sumHandler (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (Forger.counterRelay cap))
      (adversary n pk)).run 0

/-- Running a word forger with renamed requests against a logging signer, and keeping only the
queries of the log, newest first, is running it against the word oracle whose state is the list of
queries, whenever each oracle call agrees under that representation. -/
private theorem eval_runLogWith_rename {Q α : Type} (program : WordOracleComp Unit α)
    (decode : List Bool → Q) (signer : List (Q × List Bool) → Q → Option (ProbComp (List Bool)))
    (oracle : Unit × List Bool → StateT (List Q) ProbComp (List Bool))
    (step : ∀ (request : Unit × List Bool) (log : List (Q × List Bool)),
      (ProbComp.eval (ProbOracleComp.logOracle signer (decode request.2) log)).map
          (fun (a, log') => (a, (log'.map Prod.fst).reverse)) =
        ProbComp.eval (oracle request ((log.map Prod.fst).reverse))) :
    (ProbComp.eval (ProbOracleComp.runLogWith (OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (spec := probOracleSpec fun _ : Q => List Bool)
          (.inl k)) (fun request => ProbOracleComp.query (decode request.2)))
        program) signer)).map
        (fun (a, log) => (a, (log.map Prod.fst).reverse)) =
      ProbComp.eval ((OracleComp.interpret
        (sumHandler (fun k => StateT.lift (ProbComp.unifFin k)) oracle) program).run []) := by
  have hhandler : (fun q => OracleComp.interpret
      (sumHandler (fun k => StateT.lift (ProbComp.unifFin k)) (ProbOracleComp.logOracle signer))
      (sumHandler (fun k => OracleComp.query (spec := probOracleSpec fun _ : Q => List Bool)
          (.inl k)) (fun request : Unit × List Bool => ProbOracleComp.query (decode request.2))
        q)) =
      sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (fun request : Unit × List Bool => ProbOracleComp.logOracle signer (decode request.2)) := by
    funext q
    cases q <;> simp [ProbOracleComp.query]
  rw [ProbOracleComp.runLogWith, ProbOracleComp.runState, OracleComp.interpret_interpret,
    hhandler, ProbOracleComp.eval_run_interpret, ProbOracleComp.eval_run_interpret]
  exact ProbOracleComp.run_interpret_map_state
    (fun request log => ProbComp.eval (ProbOracleComp.logOracle signer (decode request.2) log))
    (fun request queried => ProbComp.eval (oracle request queried))
    (fun log => (log.map Prod.fst).reverse) step program []

/-- The EUF-CMA experiment of a typed scheme on words, played by `adversary.toTyped n`, is the
word-level game: run the word forger against the signing oracle that records the queried messages,
newest first, and accept a valid signature on a message that was never queried. -/
theorem Forger.eval_eufCmaExperiment_toTyped
    (S : Signature.Scheme (List Bool) (List Bool) (List Bool) (List Bool)) (adversary : Forger)
    (n : ℕ) :
    ProbComp.eval (S.eufCmaExperiment (adversary.toTyped n)) = ProbComp.eval (do
      let (pk, sk) ← S.keyGen
      let ((msg, sig), queried) ← (OracleComp.interpret
        (sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
          (SignatureScheme.signingOracleOf S.sign sk)) (adversary n pk)).run []
      return !queried.contains msg && S.verify pk msg sig) := by
  simp only [forgeExperiment, ProbComp.eval_bind, ProbComp.eval_pure]
  congr 1
  funext keys
  obtain ⟨pk, sk⟩ := keys
  dsimp only
  rw [← eval_runLogWith_rename (adversary n pk) (fun w => w) (Signer.ofSign S.sign sk)
    (SignatureScheme.signingOracleOf S.sign sk) fun request log => by
      simp [ProbOracleComp.logOracle, SignatureScheme.signingOracleOf, ProbComp.eval_map,
        PMF.map_comp, Function.comp_def]]
  rw [PMF.bind_map]
  congr 1
  funext x
  obtain ⟨⟨msg, sig⟩, log⟩ := x
  simp only [Function.comp_apply, freshMessage, List.contains_reverse]
  cases S.verify pk msg sig <;> simp

/-- The EUF-CMA experiment of a scheme on words restricted to the messages accepted by `adm`,
played by `adversary.toTyped n`, is the word-level game that also requires the forged message to
be admissible. -/
theorem Forger.eval_eufCmaExperiment_restrict_toTyped
    (S : Signature.Scheme (List Bool) (List Bool) (List Bool) (List Bool)) (adm : List Bool → Bool)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval ((S.restrict adm).eufCmaExperiment (adversary.toTyped n)) = ProbComp.eval (do
      let (pk, sk) ← S.keyGen
      let ((msg, sig), queried) ← (OracleComp.interpret
        (sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
          (SignatureScheme.signingOracleOf S.sign sk)) (adversary n pk)).run []
      return adm msg && !queried.contains msg && S.verify pk msg sig) := by
  rw [Forger.eval_eufCmaExperiment_toTyped]
  simp only [Signature.Scheme.restrict_keyGen, Signature.Scheme.restrict_sign,
    Signature.Scheme.restrict_verify, ProbComp.eval_bind, ProbComp.eval_pure]
  refine congrArg _ (funext fun ⟨pk, sk⟩ => congrArg _ (funext fun ⟨⟨msg, sig⟩, queried⟩ => ?_))
  cases adm msg <;> simp

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
      ProbComp.eval ((S.toScheme n).eufCmaExperiment (adversary.toTyped n)) :=
  (Forger.eval_eufCmaExperiment_restrict_toTyped ⟨S.keyGen n, S.sign, S.verify⟩ (·.length == n)
    adversary n).symm

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
  rw [← eval_runLogWith_rename (adversary n pk) (fun w => w)
    ((Signer.ofSign (S.toScheme n).sign).oneTime sk) (S.oneTimeSigningOracle sk)
    fun request log => by
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

namespace WordSignatureScheme

/-- The typed scheme of `S` at parameter `n`: the same algorithms at `n`, on all messages. -/
def toScheme (S : WordSignatureScheme) (n : ℕ) :
    Signature.Scheme (List Bool) (List Bool) (List Bool) (List Bool) :=
  ⟨S.keyGen n, S.sign, S.verify⟩

@[simp] theorem toScheme_keyGen (S : WordSignatureScheme) (n : ℕ) :
    (S.toScheme n).keyGen = S.keyGen n := rfl

@[simp] theorem toScheme_sign (S : WordSignatureScheme) (n : ℕ) :
    (S.toScheme n).sign = S.sign := rfl

@[simp] theorem toScheme_verify (S : WordSignatureScheme) (n : ℕ) :
    (S.toScheme n).verify = S.verify := rfl

/-- At each parameter `n`, the unrestricted word-level EUF-CMA game is the typed EUF-CMA
experiment of `S.toScheme n` played by `adversary.toTyped n`. -/
theorem eufCmaGame_eq_eufCmaExperiment (S : WordSignatureScheme) (adversary : Forger) (n : ℕ) :
    ProbComp.eval (S.eufCmaGame adversary n) =
      ProbComp.eval ((S.toScheme n).eufCmaExperiment (adversary.toTyped n)) :=
  (Forger.eval_eufCmaExperiment_toTyped (S.toScheme n) adversary n).symm

end WordSignatureScheme

namespace IndexedSignatureScheme

/-- The typed indexed scheme of `S` at parameter `n`: the same algorithms and the capacity at
`n`. -/
def toScheme (S : IndexedSignatureScheme) (n : ℕ) :
    Signature.IndexedScheme (List Bool) (List Bool) (List Bool) (List Bool) :=
  ⟨S.keyGen n, S.capacity n, S.sign, S.verify⟩

@[simp] theorem toScheme_keyGen (S : IndexedSignatureScheme) (n : ℕ) :
    (S.toScheme n).keyGen = S.keyGen n := rfl

@[simp] theorem toScheme_capacity (S : IndexedSignatureScheme) (n : ℕ) :
    (S.toScheme n).capacity = S.capacity n := rfl

@[simp] theorem toScheme_sign (S : IndexedSignatureScheme) (n : ℕ) :
    (S.toScheme n).sign = S.sign := rfl

@[simp] theorem toScheme_verify (S : IndexedSignatureScheme) (n : ℕ) :
    (S.toScheme n).verify = S.verify := rfl

/-- At each parameter `n`, the word-level indexed EUF-CMA game is the typed indexed experiment of
`S.toScheme n` played by `adversary.toTyped n`. -/
theorem indexedEufCmaGame_eq_eufCmaExperiment (S : IndexedSignatureScheme)
    (adversary : IndexedForger) (n : ℕ) :
    ProbComp.eval (S.indexedEufCmaGame adversary n) =
      ProbComp.eval ((S.toScheme n).eufCmaExperiment (adversary.toTyped n)) := by
  simp only [indexedEufCmaGame, forgeExperiment, toScheme_keyGen, ProbComp.eval_bind,
    ProbComp.eval_pure]
  congr 1
  funext keys
  obtain ⟨pk, sk⟩ := keys
  dsimp only
  rw [IndexedForger.toTyped, ProbOracleComp.runLogWith_map, ProbComp.eval_map, PMF.bind_map,
    ← eval_runLogWith_rename (adversary n pk) requestDecoder.decode
      (Signer.indexed (S.capacity n) S.sign sk) (S.indexedSigningOracle n sk) fun request log => by
        simp only [indexedSigningOracle]
        generalize requestDecoder.decode request.2 = r
        obtain ⟨u, m⟩ := r
        have hmem : u ∈ List.map Prod.fst (List.map Prod.fst log).reverse ↔
            u ∈ log.map (fun p => p.1.1) := by
          simp [List.map_reverse, List.map_map, Function.comp_def]
        by_cases h : u < S.capacity n ∧ u ∉ log.map (fun p => p.1.1)
        · rw [ite_eq_left ⟨h.1, fun hu => h.2 (hmem.mp hu)⟩]
          simp only [ProbOracleComp.logOracle, Signer.indexed]
          rw [ite_eq_left h]
          simp [ProbComp.eval_map, PMF.map_comp, Function.comp_def]
        · rw [ite_eq_right fun hu => h ⟨hu.1, fun hu' => hu.2 (hmem.mpr hu')⟩]
          simp only [ProbOracleComp.logOracle, Signer.indexed]
          rw [ite_eq_right h]
          simp only [ProbComp.eval_pure, PMF.pure_map]
          rfl]
  rw [PMF.bind_map]
  congr 1
  funext x
  obtain ⟨⟨u, msg, sig⟩, log⟩ := x
  simp only [Function.comp_apply, Prod.map, id, toScheme_verify, freshMessage,
    List.contains_reverse]
  cases S.verify pk u msg sig <;> simp

/-- Running the typed counter forger against the logging counter signer, and keeping only the
messages of the log, newest first, is running the word forger against the word counter oracle,
with its candidate signature word decoded. The forger's query count, the length of the log and
the word oracle's counter agree throughout. -/
private theorem eval_runLogWith_toCounter (S : IndexedSignatureScheme) (adversary : Forger)
    (n : ℕ) (pk sk : List Bool) :
    (ProbComp.eval (ProbOracleComp.runLogWith (adversary.toCounter (S.capacity n) n pk)
        (Signer.counter (S.capacity n) S.sign sk))).map
        (fun (a, log) => (a, (log.map Prod.fst).reverse)) =
      (ProbComp.eval ((OracleComp.interpret
        (sumHandler (fun k => StateT.lift (ProbComp.unifFin k)) (S.counterSigningOracle n sk))
        (adversary n pk)).run (0, []))).map
        (fun ((m, sig), (_, signed)) => ((m, requestDecoder.decode sig), signed)) := by
  rw [Forger.toCounter, ProbOracleComp.runLogWith, ProbOracleComp.runState,
    OracleComp.run_interpret_map,
    ProbComp.eval_map, PMF.map_comp, ProbOracleComp.eval_run_interpret,
    ProbOracleComp.eval_run_interpret, ProbOracleComp.run_interpret_run_interpret, PMF.map_comp]
  have key := ProbOracleComp.run_interpret_map_state_of_invariant
    (fun q (state : ℕ × List (List Bool × ℕ × List Bool)) =>
      PMF.map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)) ((OracleComp.interpret
        (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
          (fun q state => ProbComp.eval (ProbOracleComp.logOracle
            (Signer.counter (S.capacity n) S.sign sk) q state)))
        ((Forger.counterRelay (S.capacity n) q).run state.1)).run state.2))
    (fun q s => ProbComp.eval (S.counterSigningOracle n sk q s))
    (fun state => (state.2.length, (state.2.map Prod.fst).reverse))
    (fun state => state.1 = state.2.length) ?preserve ?step (adversary n pk) (0, []) rfl
  · refine Eq.trans ?_ (congrArg
      (PMF.map fun ((m, sig), (_, signed)) => ((m, requestDecoder.decode sig), signed)) key)
    rw [PMF.map_comp]
    congr 1
  case preserve =>
    rintro q ⟨j, log⟩ (rfl : j = log.length) a ⟨j', log'⟩ h
    dsimp only at h ⊢
    rw [Forger.counterRelay_run] at h
    by_cases hcap : log.length < S.capacity n
    · rw [ite_eq_left hcap] at h
      simp only [OracleComp.interpret_map, StateT.run_map, ProbOracleComp.query,
        OracleComp.interpret_query] at h
      dsimp only [OracleComp.sumHandler, StateT.run] at h
      simp only [ProbOracleComp.logOracle, Signer.counter, hcap, ite_true, ProbComp.eval_map,
        PMF.monad_map_eq_map, PMF.map_comp, PMF.mem_support_map_iff, Function.comp_apply] at h
      obtain ⟨σ, -, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      simp
    · rw [ite_eq_right hcap] at h
      simp only [OracleComp.interpret_pure, StateT.run_pure] at h
      simp_all [PMF.monad_pure_eq_pure]
  case step =>
    rintro q ⟨j, log⟩ (rfl : j = log.length)
    dsimp only
    rw [Forger.counterRelay_run]
    by_cases hcap : log.length < S.capacity n
    · rw [ite_eq_left hcap]
      simp only [OracleComp.interpret_map, StateT.run_map, ProbOracleComp.query,
        OracleComp.interpret_query, counterSigningOracle, hcap, ite_true]
      dsimp only [OracleComp.sumHandler, StateT.run]
      simp only [ProbOracleComp.logOracle, Signer.counter, hcap, ite_true, ProbComp.eval_map,
        ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_map_eq_map, PMF.map_comp]
      congr 1
      funext σ
      simp [List.map_append]
    · rw [ite_eq_right hcap]
      simp [counterSigningOracle, hcap, PMF.monad_pure_eq_pure]

/-- At each parameter `n`, the word-level counter EUF-CMA game is the typed counter experiment of
`S.toScheme n` played by `adversary.toCounter (S.capacity n) n`. -/
theorem counterEufCmaGame_eq_counterEufCmaExperiment (S : IndexedSignatureScheme)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval (S.counterEufCmaGame adversary n) =
      ProbComp.eval ((S.toScheme n).counterEufCmaExperiment
        (adversary.toCounter (S.capacity n) n)) := by
  simp only [counterEufCmaGame, forgeExperiment, toScheme_keyGen, ProbComp.eval_bind,
    ProbComp.eval_pure]
  congr 1
  funext keys
  obtain ⟨pk, sk⟩ := keys
  dsimp only
  let post : (List Bool × ℕ × List Bool) × List (List Bool) → PMF Bool :=
    fun ((m, u, σ), signed) => PMF.pure (!signed.contains m && S.verify pk u m σ)
  symm
  calc _ = ((ProbComp.eval (ProbOracleComp.runLogWith (adversary.toCounter (S.capacity n) n pk)
          (Signer.counter (S.capacity n) S.sign sk))).map
          (fun (a, log) => (a, (log.map Prod.fst).reverse))).bind post := by
        rw [PMF.bind_map]
        congr 1
        funext ⟨⟨m, u, σ⟩, log⟩
        simp only [Function.comp_apply, post, toScheme_verify, freshMessage,
          List.contains_reverse]
        cases S.verify pk u m σ <;> simp
    _ = _ := by
        rw [eval_runLogWith_toCounter, PMF.bind_map]
        congr 1

end IndexedSignatureScheme

end Cslib.Crypto

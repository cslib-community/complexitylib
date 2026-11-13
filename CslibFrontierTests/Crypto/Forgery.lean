/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Signature.Bridge

/-! Clients of the forgery experiment (`forgeExperiment`, `Signer`), typed signature schemes
(`Signature.Scheme`, `Signature.IndexedScheme`) and the word-level bridges
(`SignatureScheme.toScheme`, `Forger.toTyped`, `IndexedForger.toTyped`, `Forger.toCounter`). -/

namespace CslibFrontierTests.Forgery

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-! ### Signing policies -/

-- The one-time policy answers the first query and refuses every later one.
example (sign : Unit → Bool → ProbComp Bool) (m : Bool) :
    (Signer.ofSign sign).oneTime () [] m = some (sign () m) := by simp

example (sign : Unit → Bool → ProbComp Bool) (p : Bool × Bool) (m : Bool) :
    (Signer.ofSign sign).oneTime () [p] m = none := by simp

-- The indexed policy refuses a used index and signs a fresh one below the capacity.
example (sign : Unit → ℕ → Bool → ProbComp Bool) :
    Signer.indexed 2 sign () [((0, true), false)] (0, false) = none := by simp [Signer.indexed]

example (sign : Unit → ℕ → Bool → ProbComp Bool) :
    Signer.indexed 2 sign () [((0, true), false)] (1, false) = some (sign () 1 false) := by
  simp [Signer.indexed]

-- The counter policy signs the second query with index `1` and tags the signature with it, and
-- refuses every query beyond its capacity.
example (sign : Unit → ℕ → Bool → ProbComp Bool) (σ : ℕ × Bool) :
    Signer.counter 2 sign () [(true, σ)] false = some ((1, ·) <$> sign () 1 false) := by
  simp [Signer.counter]

example (sign : Unit → ℕ → Bool → ProbComp Bool) (σ : ℕ × Bool) :
    Signer.counter 1 sign () [(true, σ)] false = none := by
  simp [Signer.counter]

/-! ### A toy scheme -/

/-- The insecure scheme whose signature on `m` is `m` itself. -/
def echo : Signature.Scheme Unit Unit Bool Bool where
  keyGen := pure ((), ())
  sign _ m := pure m
  verify _ m σ := σ == m

-- A forger that outputs a valid pair without querying wins the existential experiment.
example : ProbComp.eval (echo.eufCmaExperiment fun _ => pure (true, true)) = PMF.pure true := by
  simp [forgeExperiment, ProbOracleComp.runLogWith, ProbOracleComp.runState, echo, freshMessage]

-- Replaying the answer to a query is not an existential forgery.
example : ProbComp.eval (echo.eufCmaExperiment fun _ => do
    let σ ← ProbOracleComp.query true
    return (true, σ)) = PMF.pure false := by
  simp [forgeExperiment, ProbOracleComp.runLogWith, ProbOracleComp.runState, echo, freshMessage]

-- The echo scheme is correct and has unique signatures, so its strong and existential
-- experiments coincide for every forger.
example (A : Signature.Forger Unit Bool Bool) :
    ProbComp.eval (echo.sufCmaExperiment A) = ProbComp.eval (echo.eufCmaExperiment A) := by
  refine Signature.Scheme.sufCmaExperiment_eq_eufCmaExperiment ?_ ?_ A
  · intro _ _ m σ hσ
    simp only [echo, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hσ
    simp [echo, hσ]
  · intro _ _ m σ σ' h h'
    simp only [echo, beq_iff_eq] at h h'
    rw [h, h']

/-! ### Word-level schemes -/

-- At parameter `n`, the typed scheme of a word-level scheme rejects messages of other lengths.
example (S : SignatureScheme) (pk sig : List Bool) : (S.toScheme 2).verify pk [true] sig = false :=
  by simp

-- The typed forger asks the message of each word request.
example (pk msg : List Bool) :
    Forger.toTyped (fun _ _ => do
      let sig ← ProbOracleComp.query ((), msg)
      return (msg, sig)) 0 pk =
      (do
        let sig ← ProbOracleComp.query msg
        return (msg, sig)) := by
  simp [Forger.toTyped, ProbOracleComp.query]

-- The typed indexed forger queries the pair that the word oracle decodes from its request.
example (pk w : List Bool) :
    IndexedForger.toTyped (fun _ _ => do
      let sig ← ProbOracleComp.query ((), w)
      return (0, w, sig)) 0 pk =
      (do
        let sig ← ProbOracleComp.query (IndexedSignatureScheme.requestDecoder.decode w)
        return ((0, w), sig)) := by
  simp [IndexedForger.toTyped, ProbOracleComp.query]

-- The counter relay forwards a request while the capacity lasts, and answers the empty word
-- without querying afterwards.
example (m : List Bool) :
    (Forger.counterRelay 1 ((), m)).run 1 = pure ([], 1) := by
  rw [Forger.counterRelay_run, ite_eq_right (lt_irrefl 1)]

example (m : List Bool) :
    (Forger.counterRelay 1 ((), m)).run 0 =
      (fun r => (encPair encUnary encBits r, 1)) <$> ProbOracleComp.query m := by
  rw [Forger.counterRelay_run, ite_eq_left Nat.zero_lt_one]

-- The typed indexed scheme keeps the capacity at the parameter.
example (S : IndexedSignatureScheme) (n : ℕ) : (S.toScheme n).capacity = S.capacity n := by simp

end CslibFrontierTests.Forgery

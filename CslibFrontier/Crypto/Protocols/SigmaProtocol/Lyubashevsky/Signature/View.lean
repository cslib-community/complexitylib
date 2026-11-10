/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature
import CslibFrontier.Crypto.Protocols.SigmaProtocol.Abort.View

/-!
# Full-view witness invariance for box lattice signatures

Two bounded secrets with the same public key give the same full commitment/optional-response
law, including aborted commitments. The challenge may be any common deterministic function of
the commitment. Independent finite attempt histories retain all hash inputs and responses.

These are equalities of single-execution laws. They do not assert equality of paired runs that
reuse private coins, efficient secret-free simulation, or adaptive random-oracle cache simulation.

## Main results

* `lyubashevsky_transcript_eq`: full fixed-challenge witness invariance.
* `lyubashevsky_attempt_view_eq`: commitment-dependent challenges preserve that equality.
* `lyubashevsky_sign_attempts_view_eq`: equality of independent full attempt histories.
* `lyubashevskySignBounded_eq_attempts_view`: project the existing signer from a full history.
* `lyubashevskySignBounded_witness_eq`: exact bounded signing is witness-invariant.

## References

The exact statements for box secrets and binary challenges are original. The witness-independence
role is motivated by [Lyubashevsky2009], Section 3.1. No full CMA theorem is claimed.
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Probability.PMF
open scoped _root_.Matrix

variable {n m k q η γ β : ℕ}
  {S S' : Matrix (Fin m) (Fin k) ℤ}
  {y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)}

/-- Bounded witnesses of the same public key have identical full fixed-challenge transcript
laws. In particular, the commitment remains visible when the prover aborts. -/
theorem lyubashevsky_transcript_eq (hβ : β ≤ γ) (hη : k * η ≤ β)
    (hS : lyubashevskyRelation η S y) (hS' : lyubashevskyRelation η S' y) (c : BitString k) :
    (lyubashevsky n m k q γ β).transcript S y c =
      (lyubashevsky n m k q γ β).transcript S' y c := by
  apply transcript_eq_of_acceptedTranscript_eq
  · rfl
  · exact ((lyubashevsky_nonAbortSpecialHVZK hβ hη).acceptedTranscript_eq S y hS c).symm.trans
      ((lyubashevsky_nonAbortSpecialHVZK hβ hη).acceptedTranscript_eq S' y hS' c)

/-- The full attempt law is witness-invariant even when the challenge is selected from the
commitment, provided both experiments use the same challenge function and public key. -/
theorem lyubashevsky_attempt_view_eq (hβ : β ≤ γ) (hη : k * η ≤ β)
    (hS : lyubashevskyRelation η S y) (hS' : lyubashevskyRelation η S' y)
    (challenge : (Fin n → ZMod q) → BitString k) :
    (((lyubashevsky n m k q γ β).commit S y).map fun ts =>
      (ts.1, (lyubashevsky n m k q γ β).respond S y ts.2 (challenge ts.1))) =
    ((lyubashevsky n m k q γ β).commit S' y).map fun ts =>
      (ts.1, (lyubashevsky n m k q γ β).respond S' y ts.2 (challenge ts.1)) :=
  map_respond_challenge_eq_of_transcript_eq _
    (lyubashevsky_transcript_eq hβ hη hS hS') challenge

/-- The full history of `K` independent exact attempts is witness-invariant. Every attempt
retains its hash input, challenge and optional response, including aborted commitments. This
history evaluates all `K` attempts; it is not a stopped or adaptive random-oracle trace. -/
theorem lyubashevsky_sign_attempts_view_eq {M : Type} (hβ : β ≤ γ) (hη : k * η ≤ β)
    (hS : lyubashevskyRelation η S y) (hS' : lyubashevskyRelation η S' y)
    (hash : M × (Fin n → ZMod q) → BitString k) (msg : M) (K : ℕ) :
    iid (((lyubashevsky n m k q γ β).commit S y).map fun ts =>
      ((msg, ts.1), hash (msg, ts.1),
        (lyubashevsky n m k q γ β).respond S y ts.2 (hash (msg, ts.1)))) K =
    iid (((lyubashevsky n m k q γ β).commit S' y).map fun ts =>
      ((msg, ts.1), hash (msg, ts.1),
        (lyubashevsky n m k q γ β).respond S' y ts.2 (hash (msg, ts.1)))) K := by
  have h := congrArg (PMF.map fun pair => ((msg, pair.1), hash (msg, pair.1), pair.2))
    (lyubashevsky_attempt_view_eq hβ hη hS hS' (fun w => hash (msg, w)))
  simp only [PMF.map_comp, Function.comp_def] at h
  exact congrArg (fun law => iid law K) h

/-- Selecting the first successful response from the full independent attempt history gives
exactly the existing bounded signer. Its output hides aborted commitments; the history does not. -/
theorem lyubashevskySignBounded_eq_attempts_view {M : Type}
    (hash : M × (Fin n → ZMod q) → BitString k) (msg : M) (K : ℕ) :
    fsAbortSignBounded (lyubashevsky n m k q γ β) hash K S y msg =
    (iid (((lyubashevsky n m k q γ β).commit S y).map fun ts =>
      ((msg, ts.1), hash (msg, ts.1),
        (lyubashevsky n m k q γ β).respond S y ts.2 (hash (msg, ts.1)))) K).map fun views =>
      (((List.ofFn views).map fun view => view.2.2.map fun z => (view.1.2, z)).find?
        Option.isSome).getD none := by
  simpa only [Option.map_id, PMF.map_id, fsAbortSignAttempt, fsAbortSignStep, iid_map,
    PMF.map_comp, Function.comp_def, List.map_ofFn, List.map_map, id_eq] using
      fsAbortSignBounded_map_eq_iid (lyubashevsky n m k q γ β) hash id K S y msg

/-- The existing bounded signer has the same exact law for two bounded secrets of one public
key, for any common deterministic hash. This follows from the complete attempt-history law. -/
theorem lyubashevskySignBounded_witness_eq {M : Type} (hβ : β ≤ γ) (hη : k * η ≤ β)
    (hS : lyubashevskyRelation η S y) (hS' : lyubashevskyRelation η S' y)
    (hash : M × (Fin n → ZMod q) → BitString k) (msg : M) (K : ℕ) :
    fsAbortSignBounded (lyubashevsky n m k q γ β) hash K S y msg =
      fsAbortSignBounded (lyubashevsky n m k q γ β) hash K S' y msg := by
  rw [lyubashevskySignBounded_eq_attempts_view, lyubashevskySignBounded_eq_attempts_view,
    lyubashevsky_sign_attempts_view_eq hβ hη hS hS']

end Cslib.Crypto.Protocols.SigmaProtocol

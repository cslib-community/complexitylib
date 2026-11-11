/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature.View
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Abort.RandomOracle

/-!
# Bounded lattice signatures in the canonical random-oracle game

`lyubashevskyROMSignature` is an all-attempt ROM variant of the bounded box signer whose signature
is optional. Signing runs all `K` attempts against the same memoizing cache even after an earlier
attempt succeeds. By contrast, the repeat-until-success signer of [Lyubashevsky2009] and
`fsAbortSignBounded` stop at the first success, so the two agree only in output law for a fixed
hash (`fiatShamirAbort_sign_fixedHash`), not in stopped ROM cache trace. Aborted commitments
remain in that cache, repeated points reuse their digest, and failed signing requests enter the
canonical queried-message log.

For valid bounded witnesses of the same public key, the actual signing/cache law and every
common adaptive forger's full output/cache/log law agree. This does not construct an efficient
secret-free simulator, a paired fork with common private coins, or an EUF-CMA reduction.

## Main definitions

* `lyubashevskyROMSignature`: all-attempt ROM variant of the bounded box signer using the original
  key generator and masks.

## Main results

* `lyubashevskyROMSignature_sign_run_eq`: same-key signing and final-cache equality.
* `lyubashevskyROMSignature_forger_run_eq`: adaptive full-view witness invariance.
* `lyubashevskyROMSignature_worldRealize_eq`: the canonical world and final verification.

## References

These exact box-signer statements are original. The aborting transformation is motivated by
[Lyubashevsky2009], Section 3.1; no full signature-security theorem is claimed.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability OracleComp ROMSignature
open scoped _root_.Matrix

/-- All-attempt ROM variant of the bounded box signer as a canonical `ROMSignature.Scheme`.
Unlike `fsAbortSignBounded` and the repeat-until-success signer of [Lyubashevsky2009], which stop
at the first success, signing executes all `K` attempts against the shared cache and agrees with
`fsAbortSignBounded` only in output law for a fixed hash (`fiatShamirAbort_sign_fixedHash`). The
secret key contains its public key as in `fiatShamir`; `none` is an abort, and verification
rejects it. -/
noncomputable def lyubashevskyROMSignature (M : Type) (n m k q η γ β K : ℕ) [NeZero q] :
    Scheme
      (Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q))
      (Matrix (Fin m) (Fin k) ℤ ×
        (Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)))
      M (Option ((Fin n → ZMod q) × (Fin m → ℤ)))
      (M × (Fin n → ZMod q)) (BitString k) :=
  fiatShamirAbort (lyubashevsky n m k q γ β) (lyubashevskyKeyGen n m k q η) K

variable {M : Type} [DecidableEq M] {n m k q η γ β K : ℕ} [NeZero q]
  {S S' : Matrix (Fin m) (Fin k) ℤ}
  {y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)}

/-- The joint signature and final cache law is independent of the bounded witness for a
fixed public key. All attempted hash points, including aborts, contribute to that cache. -/
theorem lyubashevskyROMSignature_sign_run_eq (hβ : β ≤ γ) (hη : k * η ≤ β)
    (hS : lyubashevskyRelation η S y) (hS' : lyubashevskyRelation η S' y)
    (msg : M) (cache : List ((M × (Fin n → ZMod q)) × BitString k)) :
    let scheme := lyubashevskyROMSignature M n m k q η γ β K
    ((scheme.signCoins (S, y) msg).bind fun coins =>
      (interpret (oracle (BitString k)) (scheme.sign (S, y) msg coins)).run cache) =
    (scheme.signCoins (S', y) msg).bind fun coins =>
      (interpret (oracle (BitString k)) (scheme.sign (S', y) msg coins)).run cache :=
  fiatShamirAbortSign_run_eq_of_transcript_eq _ _
    (lyubashevsky_transcript_eq hβ hη hS hS') msg K cache

/-- Any common adaptive forger has identical output, final hash cache and queried-message log
for valid bounded witnesses of one public key. The program may depend on that public key. -/
theorem lyubashevskyROMSignature_forger_run_eq (hβ : β ≤ γ) (hη : k * η ≤ β)
    (hS : lyubashevskyRelation η S y) (hS' : lyubashevskyRelation η S' y)
    {α : Type}
    (program : OracleComp (ForgerSpec M (M × (Fin n → ZMod q))
      (Option ((Fin n → ZMod q) × (Fin m → ℤ))) (BitString k)) α)
    (state : List ((M × (Fin n → ZMod q)) × BitString k) × List M) :
    (interpret (handler (lyubashevskyROMSignature M n m k q η γ β K) (S, y)) program).run state =
    (interpret (handler (lyubashevskyROMSignature M n m k q η γ β K) (S', y)) program).run state :=
  fiatShamirAbort_forger_run_eq_of_transcript_eq _ _ K
    (lyubashevsky_transcript_eq hβ hη hS hS') program state

/-- The canonical randomized forger also has the same full view after averaging its explicit
coins. Its program receives the common public key, not the chosen witness. -/
theorem lyubashevskyROMSignature_forger_eq (hβ : β ≤ γ) (hη : k * η ≤ β)
    (hS : lyubashevskyRelation η S y) (hS' : lyubashevskyRelation η S' y)
    (A : Forger
      (Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)) M
      (Option ((Fin n → ZMod q) × (Fin m → ℤ))) (M × (Fin n → ZMod q)) (BitString k))
    (state : List ((M × (Fin n → ZMod q)) × BitString k) × List M) :
    (do
      let coins ← A.coins
      (interpret (handler (lyubashevskyROMSignature M n m k q η γ β K) (S, y))
        (A.forge y coins)).run state) = (do
      let coins ← A.coins
      (interpret (handler (lyubashevskyROMSignature M n m k q η γ β K) (S', y))
        (A.forge y coins)).run state) := by
  congr 1
  funext coins
  exact lyubashevskyROMSignature_forger_run_eq hβ hη hS hS' (A.forge y coins) state

/-- A probabilistic forger and final verification in the canonical world have the same law
for either bounded witness. Verification uses the common public key and the forger's final
cache. The acceptance rule may inspect the complete signing log, including aborted replies. -/
theorem lyubashevskyROMSignature_worldRealize_eq (hβ : β ≤ γ) (hη : k * η ≤ β)
    (hS : lyubashevskyRelation η S y) (hS' : lyubashevskyRelation η S' y)
    (forger : ProbOracleComp (ForgerSpec M (M × (Fin n → ZMod q))
      (Option ((Fin n → ZMod q) × (Fin m → ℤ))) (BitString k))
      (M × Option ((Fin n → ZMod q) × (Fin m → ℤ))))
    (accept : Bool → (M × Option ((Fin n → ZMod q) × (Fin m → ℤ))) →
      List (M × Option ((Fin n → ZMod q) × (Fin m → ℤ))) → Bool) :
    let scheme := lyubashevskyROMSignature M n m k q η γ β K
    Interactive.World.eval (world scheme (S, y)) (worldRealize scheme y forger accept) =
      Interactive.World.eval (world scheme (S', y)) (worldRealize scheme y forger accept) := by
  dsimp only [lyubashevskyROMSignature]
  rw [fiatShamirAbort_world_eq_of_transcript_eq _ _ K
    (lyubashevsky_transcript_eq hβ hη hS hS')]

end Cslib.Crypto.Protocols.SigmaProtocol

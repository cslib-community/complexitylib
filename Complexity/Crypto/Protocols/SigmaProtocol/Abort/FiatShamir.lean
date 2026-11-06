/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.SigmaProtocol.Abort
public import Complexity.Probability.IID

/-!
# Fiat–Shamir signing with aborts

Generic deterministic-hash operations for an aborting Sigma protocol. The signature output
forgets aborted commitments; this API alone makes no claim about an adaptive oracle cache.

## Main definitions

* `fsAbortSignStep`, `fsAbortSignAttempt`, `fsAbortSignBounded`: single and bounded signing.
* `fsAbortVerify`: verification with a fixed hash function.
* `FiatShamirWithAborts`, `fiatShamirWithAborts`: bundled signing and verification operations.

## Main results

* `fsAbortVerify_of_fsAbortSignBounded_eq_some`: every produced signature verifies.
* `fsAbortSignBounded_apply_none`: exact bounded retry failure probability.
* `fsAbortSignBounded_map_eq_iid`: all-attempt first-success output law.
* `fsAbortForkExtract`: special soundness extracts from accepting distinct-challenge forks.

## References

[V. Lyubashevsky, *Fiat-Shamir with Aborts: Applications to Lattice and Factoring-Based
Signatures*][Lyubashevsky2009] motivates the aborting transformation. These generic operations
and elementary finite-retry laws are not a full signature-security reduction.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Probability.PMF
open scoped ENNReal

universe u
variable {X Y T C Z M : Type u}

/-- A Sigma protocol whose responses are `Option Z`, where `none` represents an abort. -/
abbrev AbortSigmaProtocol (X Y T C Z : Type u) := SigmaProtocol X Y T C (Option Z)

/-- One deterministic Fiat–Shamir-with-aborts signing step from sampled commitment/state coins
`ts : T × P.State`: query the hash oracle `h` at `(msg, ts.1)` and return `some (ts.1, z)` when
the prover does not abort, or `none` when it aborts. -/
def fsAbortSignStep (P : SigmaProtocol X Y T C (Option Z))
    (h : M × T → C) (x : X) (y : Y) (msg : M) (ts : T × P.State) : Option (T × Z) :=
  (P.respond x y ts.2 (h (msg, ts.1))).map fun z => (ts.1, z)

/-- A single probabilistic Fiat–Shamir-with-aborts signing attempt: draw commitment and state
from `P.commit x y`, hash `(msg, t)` to obtain the challenge, and return `some (t, z)` if the
prover responds without aborting, or `none` if it aborts. -/
noncomputable def fsAbortSignAttempt (P : SigmaProtocol X Y T C (Option Z))
    (h : M × T → C) (x : X) (y : Y) (msg : M) : PMF (Option (T × Z)) :=
  (P.commit x y).map (fsAbortSignStep P h x y msg)

/-- Bounded `K`-attempt Fiat–Shamir-with-aborts signing: repeat `fsAbortSignAttempt` up to `K`
independent times, returning the first non-aborted signature `some (t, z)` or `none` if all `K`
attempts abort. -/
noncomputable def fsAbortSignBounded (P : SigmaProtocol X Y T C (Option Z))
    (h : M × T → C) : ℕ → X → Y → M → PMF (Option (T × Z))
  | 0, _, _, _ => PMF.pure none
  | K + 1, x, y, msg => do
    let attempt ← fsAbortSignAttempt P h x y msg
    match attempt with
    | some sig => return some sig
    | none => fsAbortSignBounded P h K x y msg

/-- Verification of a Fiat–Shamir-with-aborts signature `sig = (t, z)` on `msg` under random
oracle `h`: check that `(t, h (msg, t), some z)` is accepted by `P.verify`. -/
def fsAbortVerify (P : SigmaProtocol X Y T C (Option Z))
    (h : M × T → C) (y : Y) (msg : M) (sig : T × Z) : Bool :=
  P.verify y sig.1 (h (msg, sig.1)) (some sig.2)

/-- Bundled Fiat–Shamir-with-aborts signature operations for an aborting Sigma protocol `P` and
hash oracle `h`. -/
structure FiatShamirWithAborts (X Y T C Z M : Type u) where
  /-- Single probabilistic signing attempt. -/
  signAttempt : X → Y → M → PMF (Option (T × Z))
  /-- Bounded `K`-attempt signing loop. -/
  signBounded : ℕ → X → Y → M → PMF (Option (T × Z))
  /-- Deterministic signature verification given the hash oracle. -/
  verify : Y → M → T × Z → Bool

/-- Construct the `FiatShamirWithAborts` bundle for an aborting Sigma protocol `P` and hash
function `h`. -/
noncomputable def fiatShamirWithAborts (P : SigmaProtocol X Y T C (Option Z))
    (h : M × T → C) : FiatShamirWithAborts X Y T C Z M where
  signAttempt := fsAbortSignAttempt P h
  signBounded := fsAbortSignBounded P h
  verify := fsAbortVerify P h

/-- **Completeness of a deterministic signing step.** If `P` is complete up to aborts for `R` and
`R x y` holds, any commitment/state `ts` in the support of `P.commit x y` for which
`fsAbortSignStep` returns `some sig` produces a valid signature. -/
theorem fsAbortVerify_of_fsAbortSignStep_eq_some {P : SigmaProtocol X Y T C (Option Z)}
    {R : X → Y → Prop} (hP : P.NonAbortComplete R) (h : M × T → C)
    {x : X} {y : Y} (hxy : R x y) {msg : M} {ts : T × P.State}
    (hts : ts ∈ (P.commit x y).support) {sig : T × Z}
    (hsig : fsAbortSignStep P h x y msg ts = some sig) :
    fsAbortVerify P h y msg sig = true := by
  unfold fsAbortSignStep at hsig
  cases hresp : P.respond x y ts.2 (h (msg, ts.1)) with
  | none => simp [hresp] at hsig
  | some z =>
    simp only [hresp, Option.map_some, Option.some.injEq] at hsig
    subst hsig
    refine hP x y hxy (h (msg, ts.1)) ts.1 z ?_
    simp only [acceptedTranscript, transcript, PMF.map_comp, PMF.mem_support_map_iff]
    exact ⟨ts, hts, by simp [hresp]⟩

/-- **Completeness of each non-aborting signing attempt.** If `P` is complete up to aborts for `R`
and `R x y` holds, every signature `sig` in the support of `fsAbortSignAttempt` is accepted by
`fsAbortVerify`. -/
theorem fsAbortVerify_of_fsAbortSignAttempt_eq_some {P : SigmaProtocol X Y T C (Option Z)}
    {R : X → Y → Prop} (hP : P.NonAbortComplete R) (h : M × T → C)
    {x : X} {y : Y} (hxy : R x y) {msg : M} {sig : T × Z}
    (hsig : some sig ∈ (fsAbortSignAttempt P h x y msg).support) :
    fsAbortVerify P h y msg sig = true := by
  obtain ⟨ts, hts, hstep⟩ := (PMF.mem_support_map_iff _ _ _).mp hsig
  exact fsAbortVerify_of_fsAbortSignStep_eq_some hP h hxy hts hstep

/-- **Completeness of bounded `K`-attempt signing.** If `P` is complete up to aborts for `R` and
`R x y` holds, every signature `sig` produced by `fsAbortSignBounded P h K x y msg` verifies. -/
theorem fsAbortVerify_of_fsAbortSignBounded_eq_some {P : SigmaProtocol X Y T C (Option Z)}
    {R : X → Y → Prop} (hP : P.NonAbortComplete R) (h : M × T → C)
    {K : ℕ} {x : X} {y : Y} (hxy : R x y) {msg : M} {sig : T × Z}
    (hsig : some sig ∈ (fsAbortSignBounded P h K x y msg).support) :
    fsAbortVerify P h y msg sig = true := by
  induction K with
  | zero => simp [fsAbortSignBounded] at hsig
  | succ K ih =>
    simp only [fsAbortSignBounded, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.mem_support_bind_iff] at hsig
    rcases hsig with ⟨attempt, hattempt, hrest⟩
    cases attempt with
    | some sig' =>
      simp only [PMF.mem_support_pure_iff, Option.some.injEq] at hrest
      subst hrest
      exact fsAbortVerify_of_fsAbortSignAttempt_eq_some hP h hxy hattempt
    | none => exact ih hrest

/-- **Abort probability after `K` independent attempts.** `fsAbortSignBounded` aborts only when all
`K` attempts abort, so its abort probability is the `K`-th power of a single attempt's abort
probability. -/
theorem fsAbortSignBounded_apply_none (P : SigmaProtocol X Y T C (Option Z))
    (h : M × T → C) (K : ℕ) (x : X) (y : Y) (msg : M) :
    fsAbortSignBounded P h K x y msg none = (fsAbortSignAttempt P h x y msg none) ^ K := by
  induction K with
  | zero => simp [fsAbortSignBounded]
  | succ K ih =>
    simp only [fsAbortSignBounded, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.bind_apply]
    rw [tsum_eq_single none]
    · simp only [ih, pow_succ']
    · rintro (_ | sig) hne
      · exact absurd rfl hne
      · simp

/-- Exact bounded signing is independent sampling followed by selection of the first success,
including after a deterministic serialization of each successful signature. -/
theorem fsAbortSignBounded_map_eq_iid {W : Type u}
    (P : SigmaProtocol X Y T C (Option Z)) (hash : M × T → C)
    (encode : T × Z → W) (K : ℕ) (x : X) (y : Y) (msg : M) :
    (fsAbortSignBounded P hash K x y msg).map (Option.map encode) =
      (PMF.iid ((fsAbortSignAttempt P hash x y msg).map (Option.map encode)) K).map
        (fun attempts => ((List.ofFn attempts).find? Option.isSome).getD none) := by
  induction K with
  | zero => simp [fsAbortSignBounded, PMF.iid]
  | succ K ih =>
    simp only [fsAbortSignBounded, PMF.iid, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.map_bind, PMF.bind_map]
    congr 1
    funext attempt
    cases attempt with
    | none => simpa [PMF.map_comp, Function.comp_def, List.ofFn_cons] using ih
    | some sig =>
      simp only [Function.comp_apply, Option.map_some, PMF.pure_map, PMF.map_comp]
      have hf : ((fun attempts : Fin (K + 1) → Option W =>
          ((List.ofFn attempts).find? Option.isSome).getD none) ∘
          Fin.cons (some (encode sig))) =
          Function.const (Fin K → Option W) (some (encode sig)) := by
        funext attempts
        simp
      rw [hf]
      exact (PMF.map_const _ _).symm

/-- **Forking extraction for Fiat–Shamir with aborts.** Two valid signatures `(t, z₁)` and
`(t, z₂)` sharing a commitment `t` on points mapped to distinct challenges `h₁ (msg₁, t) ≠
h₂ (msg₂, t)` yield a witness in `R · y` via `P`'s special soundness extractor. -/
theorem fsAbortForkExtract {P : SigmaProtocol X Y T C (Option Z)} {W : Type*}
    {R : W → Y → Prop} {extract : Y → T → C → Option Z → C → Option Z → W}
    (hP : P.SpecialSoundness R extract)
    {h₁ h₂ : M × T → C} {y : Y} {msg₁ msg₂ : M} {t : T} {z₁ z₂ : Z}
    (hc : h₁ (msg₁, t) ≠ h₂ (msg₂, t))
    (hv₁ : fsAbortVerify P h₁ y msg₁ (t, z₁) = true)
    (hv₂ : fsAbortVerify P h₂ y msg₂ (t, z₂) = true) :
    R (extract y t (h₁ (msg₁, t)) (some z₁) (h₂ (msg₂, t)) (some z₂)) y :=
  hP y t (h₁ (msg₁, t)) (some z₁) (h₂ (msg₂, t)) (some z₂) hc hv₁ hv₂

end Cslib.Crypto.Protocols.SigmaProtocol

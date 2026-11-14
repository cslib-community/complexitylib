/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.CompressedKeyOnly
public import CslibFrontier.Probability.IID
import CslibFrontier.Probability.IID.FirstSome
import Batteries.Data.Fin.Lemmas

/-!
# Bounded ML-DSA signing

FIPS 204 Algorithm 7 signs by rejection sampling. After the response and low-bits checks on
line 23, line 28 performs a second rejection check: `‖c t₀‖∞ < γ₂`, and the hint has at most
`ω` set coefficients. This module adds that complete two-stage acceptance predicate to the
existing semantic ML-DSA surface and gives executable bounded-loop semantics.

The source-shaped loop takes an explicit mask schedule. Attempt `i` uses the counter
`κ + i ℓ`, matching Algorithm 7 line 31. Exhausting the supplied attempt limit returns `none`.
This pure result represents the standard's single error result, but does not model destruction
of intermediate state or side-channel behavior. A separate IID interface samples independent
masks and proves its exact failure mass; no theorem identifies that model with FIPS 204's seeded
`ExpandMask` before its distribution and counter behavior are formalized.

Appendix C, Table 3 of the published FIPS 204 gives `814` as the minimum permitted bounded
signing limit under its stated hash/XOF distribution assumptions. NIST's potential-updates
workbook, Sheet1 row 27 (2026-07-31), proposes `821` after accounting for line 28. The inspected
workbook has SHA-256 `5bc93ce63bc647e6d1d456cb2d3a171426c15aca4a7a0e0edd40d08b7a34c793`.
The two values have deliberately different declaration names: the latter is not part of the
published standard.

## Main definitions

* `Cslib.Crypto.MLDSA.hintWeight`: number of set hint coefficients.
* `Cslib.Crypto.MLDSA.compressedSignAttempt`: one semantic Algorithm 7 attempt, including
  both rejection stages.
* `Cslib.Crypto.MLDSA.compressedSignBoundedFrom`,
  `Cslib.Crypto.MLDSA.compressedSignBounded`: first successful attempt in a bounded mask
  schedule, with an explicit starting counter or counter zero.
* `Cslib.Crypto.MLDSA.compressedSignIID`: bounded first-success signing with IID masks.
* `Cslib.Crypto.MLDSA.fips204PublishedSigningLoopLimit`,
  `Cslib.Crypto.MLDSA.fips204Proposed20260731SigningLoopLimit`: the published and proposed
  limits, kept separate.

## Main results

* `Cslib.Crypto.MLDSA.compressedSignBoundedFrom_eq_none_iff`: exhaustion is exactly rejection
  of every scheduled attempt.
* `Cslib.Crypto.MLDSA.compressedSignBoundedFrom_eq_some_iff`: a result is exactly the first
  successful scheduled attempt.
* `Cslib.Crypto.MLDSA.compressedSignIID_apply_none`: under IID masks, bounded failure is the
  single-attempt failure mass raised to the number of attempts.

## References

* [National Institute of Standards and Technology, *Module-Lattice-Based Digital Signature
  Standard*, Section 6.2, Algorithm 7 and Appendix C][NISTFIPS204]
* [National Institute of Standards and Technology, *FIPS 204 Errata (Potential Updates)*,
  Sheet1 row 27 (2026-07-31)](https://csrc.nist.gov/pubs/fips/204/final)
-/

public section

namespace Cslib.Crypto.MLDSA

open Cslib.Probability

variable (P : Params)

/-- Number of set coefficients in an ML-DSA hint vector. This is the quantity compared with
`ω` on line 28 of FIPS 204 Algorithm 7. -/
@[expose] def hintWeight (h : Fin P.k → Fin P.n → Bool) : ℕ :=
  ∑ i, Fin.countP (h i)

/-- The line-28 norm check `‖c t₀‖∞ < γ₂`, stated for the already-computed product. -/
@[expose] def LowProductShort (ct₀ : Fin P.k → Fin P.n → ZMod P.q) : Prop :=
  ∀ i j, |(ct₀ i j).valMinAbs| < P.γ₂

@[expose] instance (ct₀ : Fin P.k → Fin P.n → ZMod P.q) :
    Decidable (LowProductShort P ct₀) :=
  inferInstanceAs (Decidable (∀ _ _, _))

/-- One semantic execution of FIPS 204 Algorithm 7 lines 11--30.

The hash and mask are still the abstract values used by `Basic.lean`; seed expansion, the message
representative, byte encodings and malformed-input behavior are not modeled here. Unlike
`signAttempt`, this compressed attempt constructs the FIPS hint and includes both line-28 checks. -/
@[expose] def compressedSignAttempt (d ω : ℕ) (H : Hash P) (sk : SecretKey P)
    (msg : List Bool) (y : Fin P.ℓ → Fin P.n → ZMod P.q) : Option (CompressedSignature P) :=
  let w := moduleSISMap sk.A y
  let c := H (highBitsVec P w, msg)
  let z := y + fun j => negacyclicMul c (sk.s₁ j)
  let r₀ := w - fun i => negacyclicMul c (sk.s₂ i)
  if ResponseShort P z ∧ LowBitsShort P r₀ then
    let ct₀ := fun i => negacyclicMul c (publicKeyLowPart P d sk.publicKey i)
    let h := fun i => makeHintVec P.q P.γ₂ (-ct₀ i) (r₀ i + ct₀ i)
    if LowProductShort P ct₀ ∧ hintWeight P h ≤ ω then
      some ⟨z, h, c⟩
    else none
  else none

/-- Counter supplied to the `i`-th scheduled attempt. Algorithm 7 starts at `κ` and advances it
by `ℓ` after every rejection. -/
@[expose] def signingAttemptCounter {K : ℕ} (κ : ℕ) (i : Fin K) : ℕ :=
  κ + (i : ℕ) * P.ℓ

/-- The `K` scheduled Algorithm 7 attempts starting from counter `κ`, with line 31's
counter progression built into each mask lookup. -/
@[expose] def compressedSignAttempts (d ω : ℕ) (H : Hash P) (sk : SecretKey P) (msg : List Bool)
    (maskAt : ℕ → Fin P.ℓ → Fin P.n → ZMod P.q) (κ K : ℕ) :
    Fin K → Option (CompressedSignature P) :=
  fun i => compressedSignAttempt P d ω H sk msg (maskAt (signingAttemptCounter P κ i))

/-- Bounded Algorithm 7 signing from counter `κ`: return the first accepted signature among
`K` scheduled attempts, or `none` if every attempt rejects. This is the pure semantics of the
bounded-implementation paragraph immediately before Algorithm 7 and of its lines 10--32. -/
@[expose] def compressedSignBoundedFrom (d ω : ℕ) (H : Hash P) (sk : SecretKey P)
    (msg : List Bool) (maskAt : ℕ → Fin P.ℓ → Fin P.n → ZMod P.q) (κ K : ℕ) :
    Option (CompressedSignature P) :=
  Fin.findSome? (compressedSignAttempts P d ω H sk msg maskAt κ K)

/-- Bounded Algorithm 7 signing with the initial counter `κ = 0` from Algorithm 7 line 10. -/
@[expose] def compressedSignBounded (d ω : ℕ) (H : Hash P) (sk : SecretKey P)
    (msg : List Bool) (maskAt : ℕ → Fin P.ℓ → Fin P.n → ZMod P.q) (K : ℕ) :
    Option (CompressedSignature P) :=
  compressedSignBoundedFrom P d ω H sk msg maskAt 0 K

/-- The bounded-error obligation from the paragraph before Algorithm 7: the single failure result
is returned exactly when every scheduled execution of lines 11--30 rejects. -/
theorem compressedSignBoundedFrom_eq_none_iff (d ω : ℕ) (H : Hash P) (sk : SecretKey P)
    (msg : List Bool) (maskAt : ℕ → Fin P.ℓ → Fin P.n → ZMod P.q) (κ K : ℕ) :
    compressedSignBoundedFrom P d ω H sk msg maskAt κ K = none ↔
      ∀ i, compressedSignAttempts P d ω H sk msg maskAt κ K i = none := by
  simpa only [compressedSignBoundedFrom] using
    (Fin.findSome?_eq_none_iff
      (f := compressedSignAttempts P d ω H sk msg maskAt κ K))

/-- Algorithm 7's loop returns the first accepting scheduled attempt; all smaller indices reject. -/
theorem compressedSignBoundedFrom_eq_some_iff (d ω : ℕ) (H : Hash P) (sk : SecretKey P)
    (msg : List Bool) (maskAt : ℕ → Fin P.ℓ → Fin P.n → ZMod P.q) (κ K : ℕ)
    (σ : CompressedSignature P) :
    compressedSignBoundedFrom P d ω H sk msg maskAt κ K = some σ ↔
      ∃ i, compressedSignAttempts P d ω H sk msg maskAt κ K i = some σ ∧
        ∀ j < i, compressedSignAttempts P d ω H sk msg maskAt κ K j = none := by
  simpa only [compressedSignBoundedFrom] using
    (Fin.findSome?_eq_some_iff
      (f := compressedSignAttempts P d ω H sk msg maskAt κ K) (a := σ))

/-- The law of one semantic compressed signing attempt under a supplied mask distribution.
This is a convenience definition, not FIPS 204's seeded `ExpandMask` distribution. -/
noncomputable def compressedSignAttemptLaw (d ω : ℕ) (H : Hash P) (sk : SecretKey P)
    (msg : List Bool) (mask : PMF (Fin P.ℓ → Fin P.n → ZMod P.q)) :
    PMF (Option (CompressedSignature P)) :=
  mask.map (compressedSignAttempt P d ω H sk msg)

/-- IID bounded signing: draw `K` independent masks, run the complete compressed attempt on each,
and return the first success. This convenience model is not a separate FIPS 204 algorithm and is
not identified with seeded `ExpandMask`. -/
noncomputable def compressedSignIID (d ω : ℕ) (H : Hash P) (sk : SecretKey P)
    (msg : List Bool) (mask : PMF (Fin P.ℓ → Fin P.n → ZMod P.q)) (K : ℕ) :
    PMF (Option (CompressedSignature P)) :=
  (PMF.iid (compressedSignAttemptLaw P d ω H sk msg mask) K).map Fin.findSome?

/-- Exact IID failure probability: all `K` independent attempts must reject. This is a formal
consequence of the convenience IID model, not FIPS 204 Appendix C's distribution analysis. -/
theorem compressedSignIID_apply_none (d ω : ℕ) (H : Hash P) (sk : SecretKey P)
    (msg : List Bool) (mask : PMF (Fin P.ℓ → Fin P.n → ZMod P.q)) (K : ℕ) :
    compressedSignIID P d ω H sk msg mask K none =
      (compressedSignAttemptLaw P d ω H sk msg mask none) ^ K := by
  simpa only [compressedSignIID] using
    PMF.map_findSome_iid_apply_none (compressedSignAttemptLaw P d ω H sk msg mask) K

/-- A supplied one-attempt failure estimate raises to the `K`-th power under the IID model.
This monotonicity consequence supplies no one-attempt estimate itself. -/
theorem compressedSignIID_apply_none_le (d ω : ℕ) (H : Hash P) (sk : SecretKey P)
    (msg : List Bool) (mask : PMF (Fin P.ℓ → Fin P.n → ZMod P.q)) (K : ℕ)
    {ε : ℝ≥0∞} (hε : compressedSignAttemptLaw P d ω H sk msg mask none ≤ ε) :
    compressedSignIID P d ω H sk msg mask K none ≤ ε ^ K := by
  rw [compressedSignIID_apply_none]
  exact pow_le_pow_left' hε K

/-- Published FIPS 204 Appendix C, Table 3 minimum bounded-signing limit.

The published analysis uses expected repetition values `4.25`, `5.1` and `3.85` and the
standard's stated hash/XOF distribution assumptions. This declaration alone proves no failure
bound. -/
@[expose] def fips204PublishedSigningLoopLimit : ℕ := 814

/-- Limit proposed by NIST's FIPS 204 potential-updates workbook, Sheet1 row 27 (2026-07-31).

This proposed `821` accounts for Algorithm 7 line 28 and is deliberately not named as a
published FIPS limit. The workbook says a future revision will update Table 3. -/
@[expose] def fips204Proposed20260731SigningLoopLimit : ℕ := 821

end Cslib.Crypto.MLDSA

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.Basic
public import CslibFrontier.Foundations.Algebra.Negacyclic
import Mathlib.Tactic.Abel

/-!
# Falcon v1.2 verification algebra

This module formalizes the algebraic core of verification in the NIST-selected Falcon Round 3
submission, version 1.2 ([Falcon2020], Section 3.10, Algorithm 16). For public key
`h ∈ ℤ_q[x]/(x^n + 1)`, hash point `c` and decoded integer polynomial `s₂`, the verifier computes
`s₁ = c - s₂h mod q`, takes centered coefficient representatives, and accepts exactly when the
squared Euclidean norm of `(s₁, s₂)` is at most `⌊β²⌋`. `verify_of_signingRelation` is the
corresponding deterministic correctness boundary from Section 2.3.2: a centered integer pair
satisfying `s₁ + s₂h = c mod q` and the norm bound is accepted.

The two recommended parameter fragments are from [Falcon2020], Section 3.13, Table 3.3. This is
the Falcon v1.2 algebra *after successful signature decompression and hashing*. It does not define
byte encodings, the salt, `HashToPoint`, key generation, FFT/NTT algorithms, the trapdoor sampler,
its Gaussian law or rejection analysis, an NTRU-SIS assumption, a ROM/QROM reduction, or an
efficiency theorem. NIST lists FN-DSA / FIPS 206 as still under development as of 13 November 2026
([NISTPQC2026]); this module does not claim agreement with that future standard.

## Main definitions

* `Cslib.Crypto.Falcon.VerificationParams`: the ring degree, modulus and squared-norm bound used
  by verification.
* `Cslib.Crypto.Falcon.VerificationParams.falcon512`,
  `Cslib.Crypto.Falcon.VerificationParams.falcon1024`: the Falcon v1.2 recommended verification
  parameters.
* `Cslib.Crypto.Falcon.reduce`, `Cslib.Crypto.Falcon.reconstructResidue`,
  `Cslib.Crypto.Falcon.reconstructFirst`: coefficient reduction and Algorithm 16 reconstruction.
* `Cslib.Crypto.Falcon.pairSquaredNorm`, `Cslib.Crypto.Falcon.SigningRelation`,
  `Cslib.Crypto.Falcon.IsCentered`, `Cslib.Crypto.Falcon.verify`: the exact algebraic acceptance
  boundary after decoding.

## Main results

* `Cslib.Crypto.Falcon.verify_eq_true_iff`: verification accepts exactly the reconstructed pair
  satisfying the squared-norm bound.
* `Cslib.Crypto.Falcon.reconstructFirst_eq_of_signingRelation`: a centered first component
  satisfying the signing relation is reconstructed exactly.
* `Cslib.Crypto.Falcon.verify_of_signingRelation`: deterministic correctness of the verification
  layer for any centered relation witness within the norm bound.

## References

* [Falcon team, *Falcon: Fast-Fourier Lattice-based Compact Signatures over NTRU*, Round 3
  submission, version 1.2][Falcon2020], Sections 2.3.2, 3.10 and 3.13.
* [National Institute of Standards and Technology, *Post-Quantum Cryptography
  Standardization*][NISTPQC2026].
-/

public section

namespace Cslib.Crypto.Falcon

/-- The part of a Falcon v1.2 parameter set used by Algorithm 16: ring degree `n`, positive
modulus `q`, and the maximal signature squared norm `⌊β²⌋`. -/
structure VerificationParams where
  /-- Degree of the negacyclic ring `ℤ_q[x]/(x^n + 1)`. -/
  n : ℕ
  /-- Positive coefficient modulus. -/
  q : ℕ
  /-- Maximal accepted squared Euclidean norm `⌊β²⌋`. -/
  squaredNormBound : ℕ
  /-- The modulus is positive. -/
  q_pos : 0 < q

instance (P : VerificationParams) : NeZero P.q := ⟨P.q_pos.ne'⟩

namespace VerificationParams

/-- Falcon-512 verification parameters ([Falcon2020], Section 3.13, Table 3.3). -/
@[expose] def falcon512 : VerificationParams where
  n := 512
  q := 12289
  squaredNormBound := 34034726
  q_pos := by decide

/-- Falcon-1024 verification parameters ([Falcon2020], Section 3.13, Table 3.3). -/
@[expose] def falcon1024 : VerificationParams where
  n := 1024
  q := 12289
  squaredNormBound := 70265242
  q_pos := by decide

end VerificationParams

variable (P : VerificationParams)

/-- The coefficient representation of `ℤ_q[x]/(x^n + 1)` used by Falcon v1.2. -/
abbrev Polynomial := Negacyclic (ZMod P.q) P.n

/-- Integer coefficient representation of a polynomial in `ℤ[x]/(x^n + 1)`. -/
abbrev IntegerPolynomial := Fin P.n → ℤ

/-- Reduce every integer coefficient modulo `q`. -/
@[expose] def reduce (s : IntegerPolynomial P) : Polynomial P :=
  Negacyclic.ofCoeffs (Int.cast ∘ s)

@[simp] theorem reduce_coeffs (s : IntegerPolynomial P) (i : Fin P.n) :
    (reduce P s).coeffs i = (s i : ZMod P.q) :=
  rfl

/-- The verifier's residue-class first component `c - s₂h mod (x^n + 1, q)` from
[Falcon2020], Algorithm 16, line 5. -/
@[expose] def reconstructResidue (h c : Polynomial P) (s₂ : IntegerPolynomial P) : Polynomial P :=
  c - reduce P s₂ * h

/-- The verifier's normalized integer first component, using centered representatives in
`(-q/2, q/2]`, from [Falcon2020], Section 3.10.2. -/
@[expose] def reconstructFirst (h c : Polynomial P)
    (s₂ : IntegerPolynomial P) : IntegerPolynomial P :=
  SIS.liftCentered (reconstructResidue P h c s₂).coeffs

/-- The squared Euclidean norm `‖(s₁, s₂)‖²`, computed over integer coefficients as in
[Falcon2020], Algorithm 16, line 6. -/
@[expose] def pairSquaredNorm (s₁ s₂ : IntegerPolynomial P) : ℕ :=
  (∑ i, (s₁ i).natAbs ^ 2) + ∑ i, (s₂ i).natAbs ^ 2

/-- The Falcon signing relation `s₁ + s₂h = c mod (x^n + 1, q)` from [Falcon2020],
Section 2.3.2. -/
@[expose] def SigningRelation (h c : Polynomial P) (s₁ s₂ : IntegerPolynomial P) : Prop :=
  reduce P s₁ + reduce P s₂ * h = c

instance (h c : Polynomial P) (s₁ s₂ : IntegerPolynomial P) :
    Decidable (SigningRelation P h c s₁ s₂) := by
  unfold SigningRelation
  infer_instance

/-- Every coefficient of `s` is already the centered representative of its residue modulo `q`.
This is the exact normalization premise needed to identify the signer's integer `s₁` with the
verifier's reconstructed integer polynomial. -/
@[expose] def IsCentered (s : IntegerPolynomial P) : Prop :=
  ∀ i, ((s i : ZMod P.q).valMinAbs) = s i

instance (s : IntegerPolynomial P) : Decidable (IsCentered P s) := by
  unfold IsCentered
  infer_instance

/-- Falcon v1.2 Algorithm 16 acceptance after `s₂` has been successfully decompressed and
`c = HashToPoint(r ‖ m, q, n)` has been computed. -/
@[expose] def verify (h c : Polynomial P) (s₂ : IntegerPolynomial P) : Bool :=
  decide (pairSquaredNorm P (reconstructFirst P h c s₂) s₂ ≤ P.squaredNormBound)

/-- Algorithm 16 accepts exactly when the reconstructed centered pair satisfies the configured
squared-norm bound. -/
theorem verify_eq_true_iff (h c : Polynomial P) (s₂ : IntegerPolynomial P) :
    verify P h c s₂ = true ↔
      pairSquaredNorm P (reconstructFirst P h c s₂) s₂ ≤ P.squaredNormBound := by
  simp only [verify, decide_eq_true_eq]

/-- The residue reconstructed by verification equals the reduction of `s₁` whenever the signing
relation holds. This step needs no norm or distribution hypothesis. -/
theorem reconstructResidue_eq_reduce {h c : Polynomial P} {s₁ s₂ : IntegerPolynomial P}
    (hrel : SigningRelation P h c s₁ s₂) :
    reconstructResidue P h c s₂ = reduce P s₁ := by
  unfold SigningRelation at hrel
  unfold reconstructResidue
  rw [← hrel]
  abel

/-- A centered integer first component satisfying the signing relation is exactly the verifier's
reconstructed first component. -/
theorem reconstructFirst_eq_of_signingRelation {h c : Polynomial P}
    {s₁ s₂ : IntegerPolynomial P} (hrel : SigningRelation P h c s₁ s₂)
    (hcenter : IsCentered P s₁) :
    reconstructFirst P h c s₂ = s₁ := by
  funext i
  rw [reconstructFirst, reconstructResidue_eq_reduce P hrel, SIS.liftCentered, reduce_coeffs]
  exact hcenter i

/-- **Falcon v1.2 verification correctness boundary.** If an integer pair satisfies the signing
relation, its first component is centered, and its squared norm is within `⌊β²⌋`, then Algorithm
16 accepts its transmitted second component. This theorem does not establish that key generation
or the trapdoor sampler produces such a pair. -/
theorem verify_of_signingRelation {h c : Polynomial P} {s₁ s₂ : IntegerPolynomial P}
    (hrel : SigningRelation P h c s₁ s₂) (hcenter : IsCentered P s₁)
    (hnorm : pairSquaredNorm P s₁ s₂ ≤ P.squaredNormBound) :
    verify P h c s₂ = true := by
  rw [verify_eq_true_iff, reconstructFirst_eq_of_signingRelation P hrel hcenter]
  exact hnorm

end Cslib.Crypto.Falcon

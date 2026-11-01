/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.TruncatedResources

/-!
# Tests for the resources of the truncation-order reduction

Around a polynomial-time contraction over `A_P`, the reduction is polynomial-time: the calls are
polynomially long (`length_encCore_coreInput_le`), so the loop bound (`engineCertificate_le`) is a
polynomial. Specialized entries of a polynomial-time entry certificate are polynomial-time in the
input and the entry (`specEntryCertificate_le`).
-/

@[expose] public section

namespace ComplexityTests.TensorNetworkTruncatedResources

open Cslib Cslib.GenericRAM Cslib.Circuits.Frontier Turing.MultiTapeTM

/-- A contraction over `A_P` that returns the zero coefficient list. -/
def zeroCore (_ : ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc (List ℕ))) : List ℕ := []

/-- Its polynomial-time certificate. -/
noncomputable def zeroCoreCert :
    NativeCertificate zeroCore (encCore (encList encNat)) (encList encNat) :=
  NativeCertificate.ofPolyTime (ComputableInPolyTime.const [])

/-- **A polynomial-time core gives a polynomial-time reduction.** -/
example : ∃ c d : ℕ, ∀ y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork (List ℕ),
    (engineCertificate zeroCore zeroCoreCert).time y ≤
      c * ((encEngine (encList encNat) y).length + 1) ^ d := by
  obtain ⟨p, hp, hm, hb⟩ := exists_mono_poly_cert
    (ComputableInPolyTime.const (encIn := encCore (encList encNat)) (encOut := encList encNat)
      ([] : List ℕ))
  obtain ⟨K, hK⟩ := engineCertificate_le zeroCore zeroCoreCert
  let L := fun y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork (List ℕ) =>
    (encEngine (encList encNat) y).length
  have hpoly : PolyBounded L fun y => (L y * L y + 2) *
      (K * (L y + 0 + 1) ^ K + p (9 * (L y + 1) ^ 2)) :=
    ((PolyBounded.self.mul PolyBounded.self).add (PolyBounded.const 2)).mul
      (((PolyBounded.const K).mul ((PolyBounded.self.add (PolyBounded.const 0)).add
        (PolyBounded.const 1) |>.pow K)).add
        ((PolyBounded.of_polynomiallyBounded id hp).comp
          ((PolyBounded.const 9).mul ((PolyBounded.self.add (PolyBounded.const 1)).pow 2))))
  obtain ⟨c, d, hcd⟩ := hpoly.exists_le
  refine ⟨c, d, fun ⟨fl, P, ℓ, r, G⟩ => ?_⟩
  have h := (hK fl P ℓ r G (p (9 * (L (fl, P, ℓ, r, G) + 1) ^ 2))
    (p (9 * (L (fl, P, ℓ, r, G) + 1) ^ 2)) 0 fun k _ =>
      ⟨(hb _).1.trans (hm (length_encCore_coreInput_le (fl, P, ℓ, r, G) k)),
        (hb _).2.trans (hm (length_encCore_coreInput_le (fl, P, ℓ, r, G) k)),
        by simp [zeroCore]⟩).1
  have hN := pointCount_le (encT := encList encNat) fl P ℓ r G
  have hmul := Nat.mul_le_mul_right
    (K * (L (fl, P, ℓ, r, G) + 0 + 1) ^ K + p (9 * (L (fl, P, ℓ, r, G) + 1) ^ 2))
    (show DescribedNetwork.pointCount ℓ G + 1 ≤ L (fl, P, ℓ, r, G) * L (fl, P, ℓ, r, G) + 2 by
      simp only [L]
      omega)
  exact h.trans (hmul.trans (hcd (fl, P, ℓ, r, G)))

/-- The entry certificate of descriptors that are their own entry. -/
noncomputable def constCert :
    NativeCertificate (fun q : List ℕ × List Bool => q.1) (encPair (encList encNat) encBits)
      (encList encNat) :=
  NativeCertificate.ofPolyTime (ComputableInPolyTime.fst _ _)

-- Specialized entries cost the original entry plus a polynomial in the input and the entry.
example : ∃ K : ℕ, ∀ (t : List ℕ) (P ℓ : ℕ) (fl ζ : List ℕ) (bs : List Bool),
    (specEntryCertificate (fun t _ => t) constCert).time ((t, P, ℓ, fl, ζ), bs) ≤
      constCert.time (t, bs) +
        K * ((encPair (encSpecDesc (encList encNat)) encBits ((t, P, ℓ, fl, ζ), bs)).length +
          (encList encNat t).length + 1) ^ K := by
  obtain ⟨K, hK⟩ := specEntryCertificate_le (encT := encList encNat)
  exact ⟨K, fun t P ℓ fl ζ bs => (hK (fun t _ => t) constCert t P ℓ fl ζ bs).1⟩

end ComplexityTests.TensorNetworkTruncatedResources

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.TruncatedPolyTime

/-!
# Tests for the native machine of truncation order `ℓ`

Descriptors that are their own entry (a constant list of `V`-coefficients) have a polynomial-time
entry certificate, so direct summation through the reduction is a native machine for their
truncated contraction on every input. The loop's values after `j` rounds are the contractions at
the first `j` digit points.
-/

@[expose] public section

namespace ComplexityTests.TensorNetworkTruncatedPolyTime

open Cslib Cslib.GenericRAM Cslib.Circuits.Frontier Turing.MultiTapeTM

/-- A descriptor is its own entry, whatever the bits. -/
def constEntry (t : List ℕ) (_ : List Bool) : List ℕ := t

/-- The entry certificate of constant descriptors. -/
noncomputable def constCert :
    NativeCertificate (fun q : List ℕ × List Bool => constEntry q.1 q.2)
      (encPair (encList encNat) encBits) (encList encNat) :=
  NativeCertificate.ofPolyTime (ComputableInPolyTime.fst _ _)

/-- **A native machine for the truncated contraction** of constant-entry networks, on every
input `(P, ℓ, r, G)` with `P` and `ℓ` in unary. -/
noncomputable def truncConstCert :
    NativeCertificate
      (fun x : ℕ × ℕ × ℕ × DescribedNetwork (List ℕ) =>
        x.2.2.2.truncContraction constEntry x.1 x.2.1)
      (encTrunc (encList encNat)) (encList encNat) :=
  truncDirectCertificate constEntry constCert

-- The loop's values are the contractions at the digit points, in order.
example (core : ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc (List ℕ)) → List ℕ)
    (y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork (List ℕ)) :
    (IndexFold.run (engineStep core) 2 (y, [])).2.2 =
      [core (coreInput y 0), core (coreInput y 1)] := by
  rw [run_engineStep]
  rfl

-- `FastContraction.modulus n` has at least `n` residues.
example : 100 ≤ 2 ^ (FastContraction.modulus 100).length := le_two_pow_length_modulus 100

end ComplexityTests.TensorNetworkTruncatedPolyTime

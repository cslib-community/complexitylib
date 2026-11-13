/-
Copyright (c) 2026 Samuel Schlesinger, Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Mayank Rathee
-/

module
-- upstream: candidate

public import Cslib.Crypto.Protocols.SecretSharing.Shamir
public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF
import CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Linear
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product

/-!
# Unauthorized-Coalition Joint Uniformity for Independent Shamir Sharings

Sharing a vector `secret : κ → F` entrywise with independent uniform Shamir randomness vectors
produces a uniform joint view on `I → κ → F` for every unauthorized coalition `I`
(`I.card ≤ params.threshold`). The proof lifts single-secret coalition uniformity
(`Shamir.uniformOfFintype_map_restrict_share`) across `κ` via `PMF.pi` and swaps coordinates with
`Equiv.piComm`.

## Main results

* `Cslib.Crypto.Protocols.SecretSharing.Shamir.uniformOfFintype_map_restrict_share_pi`: independent
  Shamir sharings of `secret : κ → F` restrict to a uniform distribution on `I → κ → F` whenever
  `I.card ≤ params.threshold`.

## References

* [A. Shamir, *How to Share a Secret*][Shamir1979]
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing.Shamir

open Cslib.Probability

/-- **Vector Unauthorized-Coalition Marginal Uniformity** ([Shamir1979]): for any coalition `I`
with `I.card ≤ params.threshold` and any vector of secrets `secret : κ → F`, sharing each
coordinate independently with uniform Shamir randomness induces the uniform distribution on
`I → κ → F`. -/
theorem uniformOfFintype_map_restrict_share_pi {F Party κ : Type*} [Field F] [Fintype F]
    [Fintype Party] [DecidableEq Party] [Fintype κ] [DecidableEq κ]
    (params : Params F Party) (I : Finset Party) (hI : I.card ≤ params.threshold)
    (secret : κ → F) :
    (PMF.uniformOfFintype (κ → Randomness params)).map
        (fun r (i : I) k => share params (r k) (secret k) i) =
      PMF.uniformOfFintype (I → κ → F) := by
  have hpi :
      (PMF.uniformOfFintype (κ → Randomness params)).map
          (fun r k (i : I) => share params (r k) (secret k) i) =
        PMF.uniformOfFintype (κ → I → F) := by
    rw [← PMF.pi_uniformOfFintype,
      ← PMF.pi_map
        (fun _ : κ => PMF.uniformOfFintype (Randomness params))
        (fun k coeffs (i : I) => share params coeffs (secret k) i)]
    simp only [uniformOfFintype_map_restrict_share params I hI, PMF.pi_uniformOfFintype]
  have hcomp :
      (fun (r : κ → Randomness params) (i : I) k => share params (r k) (secret k) i) =
        (Equiv.piComm fun (_ : κ) (_ : I) => F) ∘
          fun (r : κ → Randomness params) k (i : I) => share params (r k) (secret k) i := rfl
  rw [hcomp, ← PMF.map_comp, hpi]
  exact PMF.uniformOfFintype_map_equiv (Equiv.piComm fun (_ : κ) (_ : I) => F)

end Cslib.Crypto.Protocols.SecretSharing.Shamir

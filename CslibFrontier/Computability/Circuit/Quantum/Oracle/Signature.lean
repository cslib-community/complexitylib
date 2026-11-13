/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Uniform

/-!
# A shared oracle signature for uniform quantum circuits

`UniformOracleCircuitFamily.HasOracleSignature` fixes the argument and response widths at each
security parameter, uniformly over the permitted classical input lengths. It is a property of
the existing family, not a second circuit model. Its `oracle` equivalence transports one common
function to each generated description, for use with the existing `run` and `output`.

For a finite random-oracle experiment, draw the common function once with
`Cslib.Probability.PMF.uniformOfFintype`, outside all executions that share it. The existing
uniform-equivalence and finite-product restriction laws apply to this equivalence. No new
sampler is needed, and drawing a complete table is not asserted to be computationally efficient.
These definitions and bounds are original infrastructure. They do not establish an unbounded
random oracle, equivalence across message caps, or interactive QROM security.

## Main definitions

* `Cslib.Quantum.UniformOracleCircuitFamily.HasOracleSignature`: compatible query widths.
* `Cslib.Quantum.UniformOracleCircuitFamily.HasOracleSignature.oracle`: transport a shared table.

## Main results

* `Cslib.Quantum.UniformOracleCircuitFamily.HasOracleSignature.oracle_apply`: pointwise transport.
* `Cslib.Quantum.UniformOracleCircuitFamily.HasOracleSignature.polynomiallyBounded_widths`:
  the common argument and response widths are polynomially bounded by native generation.
-/

public section

namespace Cslib.Quantum.UniformOracleCircuitFamily

open Turing.MultiTapeTM

/-- The family uses the same argument and response widths at each security parameter for every
classical input length up to `inputLength`. The length bound need not be computable or polynomial
to express this compatibility condition. -/
structure HasOracleSignature (F : UniformOracleCircuitFamily)
    (queryWidth responseWidth inputLength : ℕ → ℕ) : Prop where
  /-- Every permitted description has the common argument width. -/
  queryWidth_eq : ∀ n ℓ, ℓ ≤ inputLength n → (F.description n ℓ).queryWidth = queryWidth n
  /-- Every permitted description has the common response width. -/
  responseWidth_eq : ∀ n ℓ, ℓ ≤ inputLength n → (F.description n ℓ).responseWidth = responseWidth n

namespace HasOracleSignature

variable {F : UniformOracleCircuitFamily} {a b L : ℕ → ℕ}

/-- Relabel the common function's bit indices to those of a generated description. Applying this
equivalence at different input lengths retains the same function; it performs no sampling. -/
def oracle (h : F.HasOracleSignature a b L) (n ℓ : ℕ) (hℓ : ℓ ≤ L n) :
    ((Fin (a n) → Bool) → Fin (b n) → Bool) ≃
      ((Fin (F.description n ℓ).queryWidth → Bool) →
        Fin (F.description n ℓ).responseWidth → Bool) :=
  Equiv.arrowCongr
    (Equiv.arrowCongr (finCongr (h.queryWidth_eq n ℓ hℓ)).symm (Equiv.refl Bool))
    (Equiv.arrowCongr (finCongr (h.responseWidth_eq n ℓ hℓ)).symm (Equiv.refl Bool))

/-- Transport changes only the finite-index types, retaining every table entry. -/
theorem oracle_apply (h : F.HasOracleSignature a b L) (n ℓ : ℕ) (hℓ : ℓ ≤ L n)
    (H : (Fin (a n) → Bool) → Fin (b n) → Bool)
    (q : Fin (F.description n ℓ).queryWidth → Bool)
    (j : Fin (F.description n ℓ).responseWidth) :
    h.oracle n ℓ hℓ H q j =
      H (q ∘ (finCongr (h.queryWidth_eq n ℓ hℓ)).symm)
        (finCongr (h.responseWidth_eq n ℓ hℓ) j) := by
  unfold oracle
  rfl

/-- The shared signature has polynomial width because the native generator must write a valid
description even for the empty classical input. No separate size bound is assumed. -/
theorem polynomiallyBounded_widths (h : F.HasOracleSignature a b L) :
    PolynomiallyBounded (fun n => a n + b n) := by
  obtain ⟨c, d, hbound⟩ := F.exists_resource_bound
  refine polynomiallyBounded_iff_le.mpr ⟨c * 2 ^ d, d, fun n => ?_⟩
  have hfit := (F.wellFormed n 0).query_le
  rw [h.queryWidth_eq n 0 (Nat.zero_le _), h.responseWidth_eq n 0 (Nat.zero_le _)] at hfit
  calc
    a n + b n ≤ c * (2 * n + 0 + 2) ^ d := by have := hbound n 0; omega
    _ = (c * 2 ^ d) * (n + 1) ^ d := by rw [show 2 * n + 0 + 2 = 2 * (n + 1) by omega,
        mul_pow, Nat.mul_assoc]

end HasOracleSignature

end Cslib.Quantum.UniformOracleCircuitFamily

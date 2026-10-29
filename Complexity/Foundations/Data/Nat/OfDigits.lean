/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.Radix

/-!
# Finite-function digit numbering

## Main results

* `Nat.ofDigits_finFunctionFinEquiv`: agreement with Mathlib's finite-function numbering.

The weighted-digit identity is the existing `Nat.ofDigits_ofFn_eq_sum` from fixed-length radix
arithmetic; this module supplies only its bridge to Mathlib's finite-function enumeration.
-/

@[expose] public section

namespace Nat

/-- `finFunctionFinEquiv` uses exactly `ofDigits`'s least-significant-first convention. -/
theorem ofDigits_finFunctionFinEquiv {b L : ℕ} (f : Fin L → Fin b) :
    ofDigits b (List.ofFn fun i => (f i).val) = (finFunctionFinEquiv f).val :=
  ofDigits_ofFn_eq_sum b _

end Nat

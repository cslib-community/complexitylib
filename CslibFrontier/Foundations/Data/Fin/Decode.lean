/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Partial decoding into a finite type

`Fin.ofNat? n x` decodes `x` as an element of `Fin n` when it is in range and returns `none`
otherwise.

## Main definitions

* `Fin.ofNat?`: the partial decoder from natural numbers to `Fin`.

## Main results

* `Fin.ofNat?_eq_some_of_lt`, `Fin.ofNat?_eq_none_of_not_lt`: exact success and failure laws.

## References

This elementary decoder is original to this module.
-/

public section

namespace Fin

/-- Decode a natural number as an element of `Fin n`, rejecting out-of-range values. -/
@[expose] def ofNat? (n x : ℕ) : Option (Fin n) :=
  if h : x < n then some ⟨x, h⟩ else none

@[simp] theorem ofNat?_eq_some_of_lt (n x : ℕ) (h : x < n) :
    ofNat? n x = some ⟨x, h⟩ := by
  simp only [ofNat?, h, dite_true]

@[simp] theorem ofNat?_eq_none_of_not_lt (n x : ℕ) (h : ¬ x < n) :
    ofNat? n x = none := by
  simp only [ofNat?, h, dite_false]

end Fin

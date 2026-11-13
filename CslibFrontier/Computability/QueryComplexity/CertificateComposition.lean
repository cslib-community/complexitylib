/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Cslib.Computability.QueryComplexity.Measures
import Mathlib.Data.Finset.Card

/-!
# Composing certificates

The union of certificates for two functions certifies any binary combination of their outputs.
Consequently the certificate complexity at an input is subadditive under binary composition.
These elementary rules are used to construct accepted-input formal complexity measures.

## Main results

* `Cslib.QueryComplexity.IsCertificate.comp₂`: union certificates for a binary operation.
* `Cslib.QueryComplexity.certificateComplexityAt_comp₂_le`: subadditivity at a fixed input.
-/

public section

namespace Cslib.QueryComplexity

open Finset

variable {n : ℕ} {f g : BooleanFunction n} {a : BitString n} {S T : Finset (Fin n)}

/-- Certificates for both arguments certify any binary operation on their values. -/
theorem IsCertificate.comp₂ (hS : IsCertificate f a S) (hT : IsCertificate g a T)
    (op : Bool → Bool → Bool) : IsCertificate (fun x => op (f x) (g x)) a (S ∪ T) := by
  intro y hy
  exact congrArg₂ op (hS y (fun i hi => hy i (mem_union_left T hi)))
    (hT y (fun i hi => hy i (mem_union_right S hi)))

/-- Certificate complexity at an input is subadditive under any binary Boolean operation. -/
theorem certificateComplexityAt_comp₂_le (op : Bool → Bool → Bool)
    (f g : BooleanFunction n) (a : BitString n) :
    certificateComplexityAt (fun x => op (f x) (g x)) a ≤
      certificateComplexityAt f a + certificateComplexityAt g a := by
  obtain ⟨S, hS, eS⟩ := exists_isCertificate_card_eq f a
  obtain ⟨T, hT, eT⟩ := exists_isCertificate_card_eq g a
  exact (certificateComplexityAt_le (hS.comp₂ hT op)).trans
    ((card_union_le S T).trans_eq (by rw [eS, eT]))

end Cslib.QueryComplexity

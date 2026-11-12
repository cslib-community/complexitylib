/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: candidate
import CslibFrontier.Computability.Circuit.Boolean.FormalComplexityMeasure.Certificate

/-! # Accepted-input certificate measures

Concrete AND/OR clients check the accepted-only convention and certificate minimization.
The singleton family witnesses growing measure, while the zero-measure density is at least half.
-/

open Cslib Cslib.Circuits.Boolean Cslib.QueryComplexity

private def allTrue : BitString 2 := fun _ => true
private def allFalse : BitString 2 := fun _ => false

example : (acceptedCertificateMeasure allTrue).measure (fun x => x 0 && x 1) = 2 := by
  decide

example : (acceptedCertificateMeasure allTrue).measure (fun x => x 0 || x 1) = 1 := by
  decide

-- Rejecting inputs have measure zero even when their ordinary certificate size is nonzero.
example : certificateComplexityAt (fun x : BitString 2 => x 0 || x 1) allFalse = 2 ∧
    (acceptedCertificateMeasure allFalse).measure (fun x => x 0 || x 1) = 0 := by
  decide

-- Constants and the zero-input truth tables do not have positive certificate size.
example : (acceptedCertificateMeasure (fun _ : Fin 0 => false)).measure (fun _ => true) = 0 := by
  decide

example : (acceptedCertificateMeasure allTrue).measure (fun x => x 0 && x 1) ≠
    (acceptedCertificateMeasure allTrue).measure (fun x => !(x 0 && x 1)) := by
  decide

example : Cslib.QueryComplexity.IsCertificate (fun x : BitString 2 => x 0 ^^ x 1) allFalse
    ({0} ∪ {1}) :=
  (show IsCertificate (fun x => x 0) allFalse {0} from
    fun _ hy => hy 0 (by simp)).comp₂
    (show IsCertificate (fun x => x 1) allFalse {1} from
      fun _ hy => hy 1 (by simp)) Bool.xor

-- The witness measure grows with n, so merely asking for a large witness does not repair
-- an unconditional positive near-total-density statement.
example (n : ℕ) :
    n < (acceptedCertificateMeasure (fun _ : Fin (n + 1) => false)).measure
      (fun x => decide (x = fun _ => false)) := by
  rw [acceptedCertificateMeasure_singleton]
  omega

example (n : ℕ) : ∃ μ : FormalComplexityMeasure (n + 1),
    (∃ f, n < μ.measure f) ∧
      Fintype.card (BooleanFunction (n + 1)) ≤
        2 * (Finset.univ.filter fun g => μ.measure g = 0).card := by
  refine ⟨acceptedCertificateMeasure (fun _ => false), ⟨fun x => decide (x = fun _ => false), ?_⟩,
    card_le_two_mul_card_zero_acceptedCertificateMeasure _⟩
  rw [acceptedCertificateMeasure_singleton]
  omega

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.FormalComplexityMeasure
public import CslibFrontier.Computability.QueryComplexity.CertificateComposition

/-!
# Certificate measures and the additive loss in density amplification

At a fixed input `a`, take the certificate complexity when the function accepts `a`, and zero
otherwise. This is a formal complexity measure. A singleton indicator has measure `n`, yet at
least half of all truth tables have measure zero. Thus even an unbounded sequence of positive
witness measures does not imply a positive lower bound on a fraction tending to one.

This is an original example explaining a source discrepancy: [Arora–Barak, web draft
2007-01-08, Theorem 22.3, printed p. 438, PDF p. 454][AroraBarak07] omits the additive `-n`
in [Razborov–Rudich, Theorem 5.1(b), printed p. 33][RazborovRudich1997]. The latter asserts a
bound of the form `Ω(t / (n + log (1 / ε))²) - n`. This module does not prove the corrected
amplification theorem.

## Main definitions

* `Cslib.Circuits.Boolean.acceptedCertificateMeasure`: certificate size on accepted inputs only.

## Main results

* `Cslib.Circuits.Boolean.acceptedCertificateMeasure_singleton`: a singleton has measure `n`.
* `Cslib.Circuits.Boolean.card_le_two_mul_card_zero_acceptedCertificateMeasure`: at least half
  of all truth tables have zero measure.
-/

public section

namespace Cslib.Circuits.Boolean

open QueryComplexity Finset

variable {n : ℕ}

/-- The certificate complexity at `a` when `f a` is true, and zero otherwise. This is an
original instance of the formal complexity measure axioms, without complement invariance. -/
@[expose] def acceptedCertificateMeasure (a : BitString n) : FormalComplexityMeasure n where
  measure f := if f a then certificateComplexityAt f a else 0
  input_le i := by
    split
    · exact (certificateComplexityAt_le (S := {i}) fun y hy => hy i (mem_singleton_self i)).trans
        (by simp)
    · omega
  not_input_le i := by
    split
    · exact (certificateComplexityAt_le (S := {i}) fun y hy =>
        congrArg Bool.not (hy i (mem_singleton_self i))).trans (by simp)
    · omega
  and_le f g := by
    by_cases hf : f a = true <;> by_cases hg : g a = true
    · simpa only [hf, hg, Bool.true_and, ite_true] using
        certificateComplexityAt_comp₂_le Bool.and f g a
    all_goals simp [hf, hg]
  or_le f g := by
    by_cases hf : f a = true
    · obtain ⟨S, hS, eS⟩ := exists_isCertificate_card_eq f a
      have h : IsCertificate (fun x => f x || g x) a S := by
        intro y hy
        simp [hS y hy, hf]
      have hb := (certificateComplexityAt_le h).trans_eq eS
      simp only [hf, Bool.true_or, ite_true]
      omega
    · by_cases hg : g a = true
      · obtain ⟨S, hS, eS⟩ := exists_isCertificate_card_eq g a
        have h : IsCertificate (fun x => f x || g x) a S := by
          intro y hy
          simp [hS y hy, hg]
        have hb := (certificateComplexityAt_le h).trans_eq eS
        simpa [hf, hg] using hb
      · simp [hf, hg]

/-- Rejecting the distinguished input makes the certificate measure zero. -/
@[simp] theorem acceptedCertificateMeasure_of_false (a : BitString n) {f : BooleanFunction n}
    (hf : f a = false) : (acceptedCertificateMeasure a).measure f = 0 := by
  simp [acceptedCertificateMeasure, hf]

/-- The singleton indicator at `a` needs all `n` coordinates to certify acceptance. -/
@[simp] theorem acceptedCertificateMeasure_singleton (a : BitString n) :
    (acceptedCertificateMeasure a).measure (fun x => decide (x = a)) = n := by
  simp only [acceptedCertificateMeasure, decide_true, ite_true]
  apply le_antisymm (certificateComplexityAt_le_card _ _)
  apply le_certificateComplexityAt
  intro S hS
  have he : S = univ := by
    apply eq_univ_of_forall
    intro i
    by_contra hi
    have h := hS (Function.update a i (!(a i))) (fun j hj => by
      exact Function.update_of_ne (ne_of_mem_of_not_mem hj hi) _ _)
    have hx : Function.update a i (!(a i)) = a := of_decide_eq_true (h.trans (by simp))
    have hb := congrFun hx i
    simp at hb
  simp [he]

/-- At least half of all truth tables have zero accepted-certificate measure, at every arity.
Together with `acceptedCertificateMeasure_singleton`, this rules out an unconditional positive
near-total-density bound, even for witness measures growing with the arity. -/
theorem card_le_two_mul_card_zero_acceptedCertificateMeasure (a : BitString n) :
    Fintype.card (BooleanFunction n) ≤
      2 * (univ.filter fun f : BooleanFunction n =>
        (acceptedCertificateMeasure a).measure f = 0).card := by
  classical
  let rejecting : Finset (BooleanFunction n) := univ.filter fun f => f a = false
  let accepting : Finset (BooleanFunction n) := univ.filter fun f => f a = true
  have he : rejecting.card = accepting.card := by
    apply Finset.card_bijective (fun f x => !(f x))
      (show Function.Involutive (fun (f : BooleanFunction n) x => !(f x)) from
        fun f => funext fun x => Bool.not_not (f x)).bijective
    intro f
    simp [rejecting, accepting]
  have hs := card_filter_add_card_filter_not (s := (univ : Finset (BooleanFunction n)))
    (fun f => f a = false)
  have hn : (univ.filter fun f : BooleanFunction n => ¬f a = false) = accepting := by
    ext f
    simp [accepting]
  rw [hn, card_univ] at hs
  have hsub : rejecting ⊆ univ.filter fun f =>
      (acceptedCertificateMeasure a).measure f = 0 := by
    intro f hf
    exact mem_filter.mpr ⟨mem_univ _, acceptedCertificateMeasure_of_false a (mem_filter.mp hf).2⟩
  have hb := card_le_card hsub
  change rejecting.card + accepting.card = _ at hs
  omega

end Cslib.Circuits.Boolean

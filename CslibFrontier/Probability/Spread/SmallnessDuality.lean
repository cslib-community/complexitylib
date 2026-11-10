/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Spread.Basic
import CslibFrontier.Probability.Minimax
import CslibFrontier.Probability.PMF.Expect

/-!
# A spread law from failure of weak smallness

Finite minimax supplies a probability law supported on the given family. Its normalized
containment moments are less than two, giving spread parameter 2p for every nonempty test set;
the empty test uses total mass one. No fractional-cover duality is assumed.

## Main results

* `exists_spread_of_not_isWeaklySmall`: Talagrand's Proposition 6.7(a), including actual support.

## References

[Talagrand2010Small], Propositions 6.5 and 6.7(a), author PDF p.7.
-/

public section
namespace Cslib.Probability.Spread
open Finset
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A non-weakly-small family carries an actual 2p-spread probability law. The factor two is
essential in the source reduction; the empty-set constraint is supplied by probability mass one. -/
theorem exists_spread_of_not_isWeaklySmall {p : ℝ} (hp : 0 < p) {A : Set (Finset ι)}
    (hA : ¬ IsWeaklySmall p A) :
    ∃ ν : PMF (Finset ι), IsSpreadLaw (2 * p) ν ∧ ∀ J ∈ ν.support, J ∈ A := by
  classical
  have hne : A.Nonempty := by
    by_contra hh
    have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hh
    exact hA ⟨PMF.pure ∅, by simp [he]⟩
  let B := {J : Finset ι // J ∈ A}
  have : Nonempty B := by obtain ⟨J, hJ⟩ := hne; exact ⟨⟨J, hJ⟩⟩
  have hn : ¬ ∀ ν : PMF B, ∃ I : Finset ι,
      (∑ J : B, (ν J).toReal * (-upperKernel p I J.val)) ≤ -2 := by
    intro hh
    obtain ⟨η, hη⟩ := PMF.exists_forall_sum_mul_le
      (fun (I : Finset ι) (J : B) => -upperKernel p I J.val) hh
    apply hA
    refine ⟨η, fun J hJ => ?_⟩
    have ht := hη ⟨J, hJ⟩
    have he : (∑ I, (η I).toReal * (-upperKernel p I J)) = -coverScore p η J := by
      simp only [coverScore, mul_neg, sum_neg_distrib]
    rw [he] at ht
    linarith
  push Not at hn
  obtain ⟨ν, hν⟩ := hn
  let μ := ν.map Subtype.val
  have hm (I : Finset ι) : (∑ J, (μ J).toReal * upperKernel p I J) < 2 := by
    rw [PMF.sum_map_mul]
    have ht := hν I
    have he : (∑ J : B, (ν J).toReal * (-upperKernel p I J.val)) =
        -(∑ J : B, (ν J).toReal * upperKernel p I J.val) := by
      simp only [mul_neg, sum_neg_distrib]
    rw [he] at ht
    linarith
  refine ⟨μ, ?_, ?_⟩
  · intro I
    by_cases hI : I = ∅
    · subst I
      simpa using (PMF.sum_toReal μ).le
    · have hpI : 0 < p ^ I.card := pow_pos hp _
      have ht := hm I
      rw [kernel_average_eq] at ht
      have hc : 1 ≤ I.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hI)
      have htwo : (2 : ℝ) ≤ 2 ^ I.card := by
        simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hc
      calc _ ≤ 2 * p ^ I.card := ((div_lt_iff₀ hpI).mp ht).le
        _ ≤ 2 ^ I.card * p ^ I.card := mul_le_mul_of_nonneg_right htwo hpI.le
        _ = (2 * p) ^ I.card := (mul_pow _ _ _).symm
  · intro J hJ
    obtain ⟨x, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hJ
    exact x.property

end Cslib.Probability.Spread

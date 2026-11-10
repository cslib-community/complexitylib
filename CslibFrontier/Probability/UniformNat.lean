/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Probability.BitString
public import Cslib.Foundations.Data.Nat.PolynomialBound
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Bounded binary indices

A uniform binary word decodes to a uniform finite index. Capping it puts all excess mass at
one sentinel. A power-of-two range above any bound is at most twice the bound plus two,
including the zero case.

## Main definitions

* `Cslib.Probability.dyadicSize`: a power-of-two sampling range strictly above a bound.

## Main results

* `Cslib.BitString.uniformList_binaryValue`: exact uniformity of binary decoding.
* `Cslib.BitString.uniformList_boundedBinaryValue`: the capped distribution.
* `Cslib.Probability.uniformFin_decide_lt`: the exact probability of an index threshold.

## References

Adapted from Probability/UniformNat.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Probability

/-- A power-of-two sampling range strictly larger than the supplied bound. -/
def dyadicSize (bound : ℕ) : ℕ := 2 ^ (Nat.log 2 bound + 1)

/-- The sampling range is positive, including at zero. -/
theorem dyadicSize_pos (bound : ℕ) : 0 < dyadicSize bound := by
  unfold dyadicSize
  positivity

/-- Even at zero, the sampler draws at least one fair bit. -/
theorem two_le_dyadicSize (bound : ℕ) : 2 ≤ dyadicSize bound := by
  unfold dyadicSize
  rw [pow_succ]
  have h : 0 < 2 ^ Nat.log 2 bound := by positivity
  lia

/-- The sampling range `dyadicSize bound` is nonzero. -/
instance (bound : ℕ) : NeZero (dyadicSize bound) := ⟨(dyadicSize_pos bound).ne'⟩

/-- Every index at most the original bound lies in the dyadic range. -/
theorem lt_dyadicSize (bound : ℕ) : bound < dyadicSize bound :=
  Nat.lt_pow_succ_log_self (by decide) bound

/-- Rounding up to a power of two increases the range by at most a factor of two. -/
theorem dyadicSize_le (bound : ℕ) : dyadicSize bound ≤ 2 * (bound + 1) := by
  by_cases h : bound = 0
  · simp [h, dyadicSize]
  · have hpow := Nat.pow_log_le_self 2 h
    unfold dyadicSize
    rw [pow_succ]
    lia

/-- Applying the rounding operation to a power-of-two range doubles it. -/
@[simp] theorem dyadicSize_dyadicSize (bound : ℕ) :
    dyadicSize (dyadicSize bound) = 2 * dyadicSize bound := by
  simp only [dyadicSize]
  rw [Nat.log_pow Nat.one_lt_two, pow_succ, Nat.mul_comm]

/-- The sampling range is polynomially bounded as a function of its bound. The linear bound is
`dyadicSize_le`. -/
@[fun_prop] theorem dyadicSize_polynomiallyBounded : PolynomiallyBounded dyadicSize := by
  change PolynomiallyBounded (fun n => 2 ^ (Nat.log 2 n + 1))
  simpa only [one_mul] using polynomiallyBounded_two_pow_mul_log 1

/-- The dyadic range has a bounded unary implementation via the binary decoder. -/
theorem dyadicSize_eq_boundedBinaryValue (bound : ℕ) :
    dyadicSize bound =
      BitString.boundedBinaryValue (2 * bound + 1)
        (List.replicate (Nat.log 2 bound + 1) true) + 1 := by
  rw [BitString.boundedBinaryValue_eq]
  have h := BitString.binaryValue_replicate_true (Nat.log 2 bound + 1)
  have hle := dyadicSize_le bound
  change _ = dyadicSize bound at h
  rw [Nat.min_eq_right (by lia)]
  exact h.symm

/-- Comparing a uniform finite index with a threshold samples the corresponding capped fraction. -/
theorem uniformFin_decide_lt (size threshold : ℕ) [NeZero size] :
    ((PMF.uniformOfFintype (Fin size)).map (fun i => decide (i.val < threshold))) true =
      (↑(min size threshold) : ENNReal) / size := by
  simp [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply, ← Finset.sum_filter,
    Fin.card_filter_val_lt, div_eq_mul_inv]

end Cslib.Probability

namespace Cslib.BitString

open Probability

/-- Binary decoding identifies fair bit strings with uniform finite indices. -/
theorem uniformList_binaryValue (k : ℕ) :
    (uniformList k).map binaryValue = (PMF.uniformOfFintype (Fin (2 ^ k))).map Fin.val := by
  induction k with
  | zero => simp [binaryValue, PMF.map, Function.comp_def]
  | succ k ih =>
    let e : Fin (2 ^ k) × Bool ≃ Fin (2 ^ (k + 1)) :=
      (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans
        (finProdFinEquiv.trans (finCongr (pow_succ 2 k).symm))
    have he (i : Fin (2 ^ k)) (bit : Bool) : (e (i, bit)).val = 2 * i.val + bit.toNat := by
      cases bit <;> simp [e, finProdFinEquiv, finTwoEquiv, Nat.add_comm]
    calc
      (uniformList (k + 1)).map binaryValue =
          ((uniformList k).map binaryValue).bind (fun value =>
            (PMF.uniformOfFintype Bool).map (fun bit => 2 * value + bit.toNat)) := by
        simp [uniformList_snoc, PMF.map_bind, PMF.map_comp, PMF.bind_map,
          Function.comp_def, binaryValue_snoc]
      _ = (PMF.uniformOfFintype (Fin (2 ^ k) × Bool)).map (fun pair => (e pair).val) := by
        rw [ih, PMF.bind_map, ← PMF.uniformOfFintype_prod, PMF.map_bind]
        simp [PMF.map_comp, Function.comp_def, he]
      _ = ((PMF.uniformOfFintype (Fin (2 ^ k) × Bool)).map e).map Fin.val := by
        rw [PMF.map_comp]; rfl
      _ = _ := by rw [PMF.uniformOfFintype_map_equiv]

/-- A capped uniform index can be sampled using exactly `k` fair bits. -/
theorem uniformList_boundedBinaryValue (bound k : ℕ) :
    (uniformList k).map (boundedBinaryValue bound) =
      (PMF.uniformOfFintype (Fin (2 ^ k))).map (fun i => min bound i.val) := by
  rw [show boundedBinaryValue bound = (min bound ·) ∘ binaryValue by
    funext word; exact boundedBinaryValue_eq bound word]
  rw [← PMF.map_comp, uniformList_binaryValue, PMF.map_comp]
  rfl

end Cslib.BitString

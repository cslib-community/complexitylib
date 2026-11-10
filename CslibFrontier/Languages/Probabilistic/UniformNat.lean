/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.BitString
public import CslibFrontier.Probability.UniformNat
public import CslibFrontier.Probability.StatisticalDistance.UniformMod

/-!
# Sampling bounded indices

`sampleBinaryNat width` interprets exactly `width` fair bits as a natural number, giving the
uniform distribution below `2 ^ width`. Its runtime certificate uses binary output.

`sampleBoundedIndex bound` uses `log₂ bound + 1` fair bits. Each index strictly below `bound`
has the same probability; the remaining probability is assigned to the sentinel `bound`.
There is no unbounded rejection loop.

`sampleModNat width modulus` reduces such a value modulo `modulus`. Read in `ZMod q`, it is within
statistical distance `q / 2 ^ width` of uniform (`dist_map_natCast_eval_sampleModNat_le`): strict
PPT machines sample `ZMod q` only approximately, and enough extra bits make the error small.

`sampleDyadicIndex bound` instead samples exactly uniformly below the next power of two, whose
range is at most `2 * (bound + 1)`. `sampleDyadicCoin bound numerator` compares such an index with
`numerator`, sampling the exact capped fraction `numerator / dyadicSize bound`.

## Main definitions

* `Cslib.ProbComp.sampleBinaryNat`: exact uniform sampling from a specified bit width.
* `Cslib.ProbComp.sampleModNat`: approximately uniform sampling of residues modulo a given modulus.
* `Cslib.ProbComp.sampleDyadicIndex`: exact uniform sampling in the power-of-two range.
* `Cslib.ProbComp.sampleBoundedIndex`: a capped uniform index with a rejection sentinel.
* `Cslib.ProbComp.sampleDyadicCoin`: an exact capped dyadic acceptance probability.

## Main results

* `Cslib.ProbComp.eval_sampleBinaryNat`, `Cslib.ProbComp.mem_support_sampleBinaryNat_iff`:
  the exact law and support.
* `Cslib.ProbComp.eval_sampleModNat`, `Cslib.ProbComp.dist_map_natCast_eval_sampleModNat_le`:
  the law of the residue sampler and its distance from uniform on `ZMod q`.
* `Cslib.ProbComp.eval_sampleDyadicIndex`, `Cslib.ProbComp.eval_sampleBoundedIndex`:
  exact distribution laws.
* `Cslib.ProbComp.eval_sampleDyadicCoin_true`: exact acceptance mass, including zero and one.

## References

Adapted from Languages/Probabilistic/UniformNat.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.ProbComp

open BitString Probability

/-- Interpret exactly `width` independent fair bits as a binary natural number. -/
noncomputable def sampleBinaryNat (width : ℕ) : ProbComp ℕ :=
  binaryValue <$> BitString.sampleList width

/-- With width zero the sampler returns `0` without sampling. -/
@[simp] theorem sampleBinaryNat_zero : sampleBinaryNat 0 = pure 0 := rfl

/-- The sampled value is exactly uniform below `2 ^ width`, including width zero. -/
theorem eval_sampleBinaryNat (width : ℕ) :
    ProbComp.eval (sampleBinaryNat width) =
      (PMF.uniformOfFintype (Fin (2 ^ width))).map Fin.val := by
  simp only [sampleBinaryNat, ProbComp.eval_map, BitString.eval_sampleList,
    uniformList_binaryValue]

/-- Reduce `width` fair bits, read as a binary natural number, modulo `modulus`. -/
noncomputable def sampleModNat (width modulus : ℕ) : ProbComp ℕ :=
  (· % modulus) <$> sampleBinaryNat width

/-- The residue sampler reduces a uniform value below `2 ^ width`. -/
theorem eval_sampleModNat (width modulus : ℕ) :
    ProbComp.eval (sampleModNat width modulus) =
      (PMF.uniformOfFintype (Fin (2 ^ width))).map fun x => x.val % modulus := by
  simp only [sampleModNat, ProbComp.eval_map, eval_sampleBinaryNat, PMF.map_comp]
  rfl

open scoped Cslib.Probability.PMF in
/-- **Approximately uniform residues.** Read in `ZMod q`, the residue of `width` fair bits is
within statistical distance `q / 2 ^ width` of the uniform distribution on `ZMod q`. -/
theorem dist_map_natCast_eval_sampleModNat_le (width q : ℕ) [NeZero q] :
    dist ((ProbComp.eval (sampleModNat width q)).map (Nat.cast : ℕ → ZMod q))
      (PMF.uniformOfFintype (ZMod q)) ≤ q / 2 ^ width := by
  rw [eval_sampleModNat, PMF.map_comp]
  have hcast : ((Nat.cast : ℕ → ZMod q) ∘ fun x : Fin (2 ^ width) => x.val % q) =
      fun x => (x.val : ZMod q) := funext fun x => ZMod.natCast_mod _ _
  rw [hcast]
  exact_mod_cast PMF.dist_map_natCast_uniformOfFintype_le_div (2 ^ width) q

/-- Every value below `2 ^ width` can occur, and no other value can occur. -/
theorem mem_support_sampleBinaryNat_iff (width value : ℕ) :
    value ∈ (ProbComp.eval (sampleBinaryNat width)).support ↔ value < 2 ^ width := by
  rw [eval_sampleBinaryNat, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact i.isLt
  · intro hvalue
    exact ⟨⟨value, hvalue⟩, by simp, rfl⟩

/-- An exact uniform index in a power-of-two range, using a fixed number of fair bits. -/
noncomputable def sampleDyadicIndex (bound : ℕ) : ProbComp ℕ :=
  boundedBinaryValue (dyadicSize bound) <$> BitString.sampleList (Nat.log 2 bound + 1)

/-- The dyadic sampler has no rejection or approximation error. -/
theorem eval_sampleDyadicIndex (bound : ℕ) :
    ProbComp.eval (sampleDyadicIndex bound) =
      (PMF.uniformOfFintype (Fin (dyadicSize bound))).map Fin.val := by
  simp only [sampleDyadicIndex, ProbComp.eval_map, BitString.eval_sampleList,
    uniformList_boundedBinaryValue]
  congr 1
  funext i
  exact Nat.min_eq_right i.isLt.le

/-- Move an independent source inside a uniform index choice, with a fixed fallback for padding
indices. This exposes the finite average used by random-coordinate reductions. -/
theorem eval_bind_sampleDyadicIndex_guard {α β : Type} (source : ProbComp α) (bound : ℕ)
    (test : ℕ → α → ProbComp β) (fallback : β) :
    ProbComp.eval (do
      let value ← source
      let index ← sampleDyadicIndex bound
      if index < bound then test index value else pure fallback) =
      (do
        let i ← PMF.uniformOfFintype (Fin (dyadicSize bound))
        if i.val < bound then ProbComp.eval (do
          let value ← source
          test i.val value)
        else PMF.pure fallback) := by
  simp only [ProbComp.eval_bind, eval_sampleDyadicIndex]
  simp only [PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  congr 1
  funext i
  by_cases hi : i.val < bound <;>
    simp only [hi, ite_true, ite_false, ProbComp.eval_pure, PMF.bind_const]

/-- An exact dyadic coin, saturated at probability one when the numerator exceeds the range. -/
noncomputable def sampleDyadicCoin (bound numerator : ℕ) : ProbComp Bool := do
  let index ← sampleDyadicIndex bound
  return decide (index < numerator)

/-- The dyadic coin's exact acceptance probability, including the endpoints zero and one. -/
theorem eval_sampleDyadicCoin_true (bound numerator : ℕ) :
    ProbComp.eval (sampleDyadicCoin bound numerator) true =
      (↑(min (dyadicSize bound) numerator) : ENNReal) / dyadicSize bound := by
  simp only [sampleDyadicCoin, ProbComp.eval_bind, ProbComp.eval_pure,
    eval_sampleDyadicIndex, PMF.bind_map]
  exact uniformFin_decide_lt _ _

/-- The real-valued acceptance probability of the exact dyadic sampler. -/
theorem eval_sampleDyadicCoin_true_toReal (bound numerator : ℕ) :
    (ProbComp.eval (sampleDyadicCoin bound numerator) true).toReal =
      (↑(min (dyadicSize bound) numerator) : ℝ) / dyadicSize bound := by
  rw [eval_sampleDyadicCoin_true, ENNReal.toReal_div]
  simp

/-- Every positive dyadic acceptance probability is at least one over its sampling range. -/
theorem inv_dyadicSize_le_eval_sampleDyadicCoin (bound numerator : ℕ)
    (hpositive : 0 < (ProbComp.eval (sampleDyadicCoin bound numerator) true).toReal) :
    (1 : ℝ) / dyadicSize bound ≤
      (ProbComp.eval (sampleDyadicCoin bound numerator) true).toReal := by
  rw [eval_sampleDyadicCoin_true_toReal] at hpositive ⊢
  have hdenominator : (0 : ℝ) < dyadicSize bound := by exact_mod_cast dyadicSize_pos bound
  have hnum : 0 < min (dyadicSize bound) numerator := by
    exact_mod_cast (div_pos_iff_of_pos_right hdenominator).mp hpositive
  apply div_le_div_of_nonneg_right _ hdenominator.le
  exact_mod_cast Nat.succ_le_of_lt hnum

/-- A capped fair-bit index, with `bound` denoting rejection. -/
noncomputable def sampleBoundedIndex (bound : ℕ) : ProbComp ℕ :=
  boundedBinaryValue bound <$> BitString.sampleList (Nat.log 2 bound + 1)

/-- The sampler's exact distribution, including its rejection mass. -/
theorem eval_sampleBoundedIndex (bound : ℕ) :
    ProbComp.eval (sampleBoundedIndex bound) =
      (PMF.uniformOfFintype (Fin (2 ^ (Nat.log 2 bound + 1)))).map (fun i => min bound i.val) := by
  simp [sampleBoundedIndex, ProbComp.eval_map, BitString.eval_sampleList,
    uniformList_boundedBinaryValue]

end Cslib.ProbComp

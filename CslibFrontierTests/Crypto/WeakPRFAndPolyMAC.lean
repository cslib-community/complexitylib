/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Computational.WeakPRF
import CslibFrontier.Crypto.Protocols.MAC.PolynomialEvaluation
import Mathlib.Algebra.Field.ZMod

/-!
# Tests for weak pseudorandom functions and polynomial-evaluation hashes

The zero patch is evaluated on small inputs, the forger is run against the MAC built from a
patched toy family, and the zero-patch bound is instantiated for an adversary making one call.
The polynomial-evaluation hashes are evaluated over `ZMod 5` with messages of length below `2`.
One length code is injective and never zero, so all three positive results apply; another is
injective but codes length one as zero, so the two counterexamples apply, and the resulting
key-independent collision is checked directly.
-/

namespace CslibFrontierTests.Crypto.WeakPRFAndPolyMAC

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-! ### Zero patching -/

/-- Bitwise negation of the query, ignoring the key. -/
def negate (_ query : List Bool) : List Bool := query.map not

example : zeroPatch negate [true, true] [false, false] = [false, false] := by decide

example : zeroPatch negate [true, true] [true, false] = [false, true] := by decide

/-- The key, answered on every query. -/
def keyFamily (key _ : List Bool) : List Bool := key

theorem computableInPolyTime_keyFamily :
    ComputableInPolyTime (fun pair : List Bool × List Bool => keyFamily pair.1 pair.2)
      (encPair encBits encBits) encBits := by
  unfold keyFamily
  fun_prop

/-- The forger wins outright against the MAC built from the patched key family. -/
example (n : ℕ) :
    ProbComp.eval ((prfMAC (zeroPatch keyFamily)
      (computableInPolyTime_zeroPatch computableInPolyTime_keyFamily)).eufCmaGame
        zeroForger n) = PMF.pure true :=
  eval_eufCmaGame_prfMAC_zeroPatch_zeroForger _ n

example : ¬ (prfMAC (zeroPatch keyFamily)
    (computableInPolyTime_zeroPatch computableInPolyTime_keyFamily)).EUFCMA :=
  not_eufCma_prfMAC_zeroPatch _

example : ¬ PseudorandomFunction (zeroPatch keyFamily) :=
  not_pseudorandomFunction_zeroPatch keyFamily

/-- Ask for one weak sample and accept when it is all-zero. -/
noncomputable def zeroSampleTest : OracleDistinguisher := fun n _ => do
  let sample ← ProbOracleComp.query ((), [])
  return sample == List.replicate (2 * n) false

theorem isQueryBounded_zeroSampleTest (n : ℕ) : (zeroSampleTest n []).IsQueryBounded 1 := by
  simpa only [zeroSampleTest, Nat.add_zero] using
    (ProbOracleComp.IsQueryBounded.query ((), [])).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0

/-- Against one call, zero patching moves the weak real game by at most `2⁻ⁿ`. -/
example (n : ℕ) :
    (Game.advantage (ProbComp.eval (weakPrfRealGame (zeroPatch negate) zeroSampleTest n))
      (ProbComp.eval (weakPrfRealGame negate zeroSampleTest n)) : ℝ) ≤ 1 / 2 ^ n := by
  simpa only [Nat.cast_one] using
    advantage_weakPrfRealGame_zeroPatch_le negate zeroSampleTest n 1
      (isQueryBounded_zeroSampleTest n)

example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    WeakPseudorandomFunction (zeroPatch family) :=
  hprf.weakPseudorandomFunction.zeroPatch

/-! ### Polynomial-evaluation hashes over `ZMod 5` -/

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

open PolynomialEvaluation

/-- Length code `d ↦ d + 1`: injective and never zero. -/
def shiftedLength (d : Fin 2) : ZMod 5 := d.val + 1

/-- Length code `d ↦ 1 - d`: injective, but codes length one as zero. -/
def flippedLength (d : Fin 2) : ZMod 5 := ((1 - d.val : ℕ) : ZMod 5)

theorem shiftedLength_injective : Function.Injective shiftedLength := by decide

theorem shiftedLength_ne_zero (d : Fin 2) (hd : d.val ≠ 0) : shiftedLength d ≠ 0 := by
  revert d; decide

theorem flippedLength_injective : Function.Injective flippedLength := by decide

theorem flippedLength_one : flippedLength ⟨1, by norm_num⟩ = 0 := by decide

/-- The empty message. -/
def empty : Message (ZMod 5) 2 := ⟨[], by simp⟩

/-- A one-letter message. -/
def letter (c : ZMod 5) : Message (ZMod 5) 2 := ⟨[c], by simp⟩

-- With `shiftedLength`, `letter 3` has coefficients `[3, 2]`; at `k = 2` the four hashes are
-- `3·4 + 2·2`, `2⁰·(3·4 + 2·2)`, `3·2 + 2` and `3·2 + 2·4`.
example : PolynomialEvaluation.hash shiftedLength 2 (letter 3) = 1 := by decide
example : fixedTopHash shiftedLength 2 (letter 3) = 1 := by decide
example : constantTermHash shiftedLength 2 (letter 3) = 3 := by decide
example : ascendingHash shiftedLength 2 (letter 3) = 4 := by decide

example : IsDeltaUniversalHash (PMF.uniformOfFintype (ZMod 5))
    (PolynomialEvaluation.hash shiftedLength) (2 / 5) := by
  simpa [ZMod.card] using isDeltaUniversalHash_hash shiftedLength_injective

example : IsDeltaUniversalHash (PMF.uniformOfFintype (ZMod 5)) (fixedTopHash shiftedLength)
    (2 / 5) := by
  simpa [ZMod.card] using isDeltaUniversalHash_fixedTopHash shiftedLength_ne_zero

example : IsDeltaUniversalHash (PMF.uniformOfFintype (ZMod 5)) (ascendingHash shiftedLength)
    (2 / 5) := by
  simpa [ZMod.card] using isDeltaUniversalHash_ascendingHash shiftedLength_ne_zero

/-- With `flippedLength`, the empty message and `letter 1` collide under every key. -/
example : ∀ k : ZMod 5, ascendingHash flippedLength k empty =
    ascendingHash flippedLength k (letter 1) := by decide

theorem two_fifths_lt_one : (2 / 5 : ENNReal) < 1 :=
  (ENNReal.div_lt_iff (by norm_num) (by norm_num)).2 (by norm_num)

example : ¬ IsDeltaUniversalHash (PMF.uniformOfFintype (ZMod 5)) (fixedTopHash flippedLength)
    (2 / 5) :=
  not_isDeltaUniversalHash_fixedTopHash (by norm_num) flippedLength_one two_fifths_lt_one

example : ¬ IsDeltaUniversalHash (PMF.uniformOfFintype (ZMod 5)) (ascendingHash flippedLength)
    (2 / 5) :=
  not_isDeltaUniversalHash_ascendingHash (by norm_num) flippedLength_one two_fifths_lt_one

example : ¬ IsDeltaUniversalHash (PMF.uniformOfFintype (ZMod 5))
    (constantTermHash shiftedLength) (2 / 5) :=
  not_isDeltaUniversalHash_constantTermHash shiftedLength (by norm_num) two_fifths_lt_one

end CslibFrontierTests.Crypto.WeakPRFAndPolyMAC

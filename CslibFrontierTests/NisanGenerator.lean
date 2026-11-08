/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Primitives.PRG.Nisan.Bits

/-! Nisan's generator: block order, read-once tests at widths `1` and `2`, and the bounds. -/

namespace ComplexityTests.NisanGenerator

open Cslib Cslib.BranchingPrograms Cslib.Crypto.PRG Cslib.Crypto.PRG.Nisan

/-- Parity of `L` bits as a read-once branching program of width `2`. -/
private def parity (L : ℕ) : ReadOnceProgram L (Fin 2) Bool where
  start := 0
  step _ s a := if a then s + 1 else s
  accept s := s = 1

example : (parity 3).eval ![true, false, true] = false := by decide

example : (parity 4).eval ![true, true, false, true] = true := by decide

-- The `i`-th instruction from the end of the monoid program reads position `i`.
example : (parity 3).toMonoidProgram.eval ![true, false, false] (parity 3).start = 1 := by
  rw [ReadOnceProgram.eval_toMonoidProgram]
  decide

-- Regrouping `2 * 2` bits into two blocks of two bits keeps the output.
example : (parity (2 * 2)).blocks.eval ![![true, false], ![true, true]] = true := by
  rw [ReadOnceProgram.eval_blocks]
  decide

-- Parity is a read-once test of width `2`: the admissibility predicate is inhabited.
example (L : ℕ) : IsReadOnceTest 2 (fun x : Fin L → Bool => PMF.pure ((parity L).eval x)) :=
  ⟨parity L, rfl⟩

-- A program of width `1` has a constant output, so the test reading one bit is not a read-once
-- test of width `1`: the admissibility predicate is not trivial.
example : ¬IsReadOnceTest 1 (fun x : Fin 1 → Bool => PMF.pure (x 0)) := by
  rintro ⟨P, hP⟩
  have hconst : P.eval ![true] = P.eval ![false] := by
    simp only [ReadOnceProgram.eval,
      Subsingleton.elim (P.finalState ![true]) (P.finalState ![false])]
  have h := congrArg (fun p : PMF Bool => p true)
    ((congrFun hP ![true]).trans ((congrArg PMF.pure hconst).trans (congrFun hP ![false]).symm))
  simp at h

-- The first seed acts first and chooses the most significant bit of the block index:
-- the blocks for the seeds `(1, 2)` are `x`, `h 2 x`, `h 1 x`, `h 2 (h 1 x)`.
example : blocks (fun i x : ℕ => 10 * x + i) 2 0 ![1, 2] = ![0, 2, 1, 12] := by decide

-- With no hash seeds the generator outputs its block: the error bound is `0`.
example : (bitGenerator 3 0).Secure (IsReadOnceTest 5) 0 := by
  simpa using secure_bitGenerator 3 0 5

-- The generator on bit strings stretches: `48` seed bits into `64` output bits.
example : Fintype.card (BitSeed 4 4) = 2 ^ 48 ∧ 2 ^ 4 * 4 = 64 := by
  rw [card_bitSeed]
  decide

-- The parameters of Nisan's theorem: width up to `2 ^ 1` and error `1 / 2` with `k = 10` and
-- `n = 2 (10 + 1 + 1) = 24`. The generator stretches `734` seed bits into `24576` output bits.
example : (bitGenerator 24 10).Secure (IsReadOnceTest 2) 2⁻¹ ∧
    Fintype.card (BitSeed 24 10) = 2 ^ 734 ∧ 2 ^ 10 * 24 = 24576 := by
  refine ⟨?_, ?_, by norm_num⟩
  · have h := secure_bitGenerator_of_le 10 1 1 2 (by norm_num)
    rwa [pow_one] at h
  · rw [card_bitSeed]

end ComplexityTests.NisanGenerator

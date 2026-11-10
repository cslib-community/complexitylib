/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow

/-!
# Padding to exponential length in `EXP`

Polynomial-time computation on an instance `b` paired with unary padding `2 ^ L b`, for an exponent
`L b` computable in unary in polynomial time, gives a problem in `EXP`
(`Cslib.Complexity.setOf_mem_EXP_of_computableInPolyTime_pad`). Writing the padding and running
the polynomial-time procedure takes time `C 2 ^ (D L b) (|b| + 1) ^ D`
(`Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO_pad`), which is `2 ^ poly(|b|)`
because `L b` is polynomial in `|b|`. This is the `EXP` counterpart of
`Cslib.Complexity.setOf_mem_E_of_computableInPolyTime_pad`, whose padding is `2 ^ |y|`.

A typical use is a polynomial-time algorithm in the size of an exponentially large object, such as
the configuration graph of a polynomial-space machine, stated as an exponential-time decision
procedure on the original instances.

## Main results

* `Cslib.Complexity.setOf_mem_EXP_of_computableInPolyTime_pad`: polynomial time on instances
  padded by `2 ^ L b`, for a polynomial-time unary exponent `L`, gives `EXP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

/-- **Padding to exponential length in `EXP`.** If `Ψ` is polynomial-time on pairs of an instance
and a unary number, and the exponent `L` is polynomial-time in unary, then the instances `b` with
`Ψ (b, 2 ^ L b)` form a problem in `EXP`: writing the padding `2 ^ L b` and running `Ψ` takes
time `C 2 ^ (D L b) (|b| + 1) ^ D`
(`Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO_pad`), with `L b` polynomial in
`|b|`. -/
theorem setOf_mem_EXP_of_computableInPolyTime_pad {β : Type} {encB : β ↪ List Bool}
    {Ψ : β × ℕ → Bool} (hΨ : ComputableInPolyTime Ψ (encPair encB encUnary) encBool)
    {L : β → ℕ} (hL : ComputableInPolyTime L encB encUnary) :
    {b | Ψ (b, 2 ^ L b) = true} ∈ EXP encB := by
  -- write the padding `2 ^ L b`, then run `Ψ`
  obtain ⟨C, D, h⟩ := hΨ.exists_computableInO_pad hL
  obtain ⟨cL, dL, hLle⟩ := hL.polyBounded.exists_le
  -- the time bound is `2 ^ h n` with a polynomial exponent `h`
  refine DTIME_two_pow_subset_EXP (h := fun n => C + D * (cL * (n + 1) ^ dL) + D * (n + 1))
    (by fun_prop) (setOf_mem_DTIME_of_computableInO h fun b => ?_)
  calc C * 2 ^ (D * L b) * ((encB b).length + 1) ^ D
      ≤ 2 ^ C * 2 ^ (D * (cL * ((encB b).length + 1) ^ dL)) * (2 ^ ((encB b).length + 1)) ^ D := by
        gcongr
        · exact Nat.lt_two_pow_self.le
        · exact hLle b
        · exact Nat.lt_two_pow_self.le
    _ = _ := by ring

end Cslib.Complexity

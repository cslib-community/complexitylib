/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.EXP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Padding to exponential length in `EXP`

Polynomial-time computation on an instance `b` paired with unary padding `2 ^ L b`, for an exponent
`L b` computable in unary in polynomial time, gives a problem in `EXP`
(`Cslib.Complexity.setOf_mem_EXP_of_computableInPolyTime_pad`). The padding is written within
exponential time (`Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO_unary_two_pow`),
and the timed-reduction API (`Cslib.Complexity.preimage_mem_DTIME`) composes it with the
polynomial-time procedure. This is the `EXP` counterpart of
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

open Turing Turing.MultiTapeTM Filter

/-- **Padding to exponential length in `EXP`.** If `Ψ` is polynomial-time on pairs of an instance
and a unary number, and the exponent `L` is polynomial-time in unary, then the instances `b` with
`Ψ (b, 2 ^ L b)` form a problem in `EXP`: the padding `b ↦ (b, 2 ^ L b)` is written within time
`O(2 ^ |b| + 4 ^ L b)`
(`Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO_unary_two_pow`), and `Ψ` then runs
in time polynomial in `2 ^ L b`, with `L b` polynomial in `|b|`. -/
theorem setOf_mem_EXP_of_computableInPolyTime_pad {β : Type} {encB : β ↪ List Bool}
    {Ψ : β × ℕ → Bool} (hΨ : ComputableInPolyTime Ψ (encPair encB encUnary) encBool)
    {L : β → ℕ} (hL : ComputableInPolyTime L encB encUnary) :
    {b | Ψ (b, 2 ^ L b) = true} ∈ EXP encB := by
  obtain ⟨t, s, ht, hs, h⟩ := hΨ
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.mp (ht.add hs)
  -- the problem decided by `Ψ`, within polynomial time
  have hB : {x | Ψ x = true} ∈ DTIME (encPair encB encUnary) fun n => c * (n + 1) ^ d :=
    setOf_mem_DTIME_of_computableInO
      (T := fun x => t (encPair encB encUnary x).length + s (encPair encB encUnary x).length)
      (S := fun x => t (encPair encB encUnary x).length + s (encPair encB encUnary x).length)
      (.of_bounds h 1 (fun _ => by omega) (fun _ => by omega)
        fun x => (h.length_le x).trans (by omega)) fun x => hcd _
  -- the padding `b ↦ (b, 2 ^ L b)`
  obtain ⟨C, hpad⟩ := hL.exists_computableInO_unary_two_pow
  have hgO := (ComputableInO.of_eq (f := fun b : β => b) (encIn := encB) (encMid := encB)
    fun _ => rfl).prod hpad
  obtain ⟨cL, dL, hLle⟩ := hL.polyBounded.exists_le
  -- the time bound `2 ^ M n`
  set M : ℕ → ℕ := fun n => (d + 2) * (n + cL * (n + 1) ^ dL + 2)
  have hpre : {b | Ψ (b, 2 ^ L b) = true} ∈ DTIME encB fun n => 2 ^ M n := by
    refine preimage_mem_DTIME (C := 2 + C + c) hB hgO fun b => ?_
    set n := (encB b).length
    set P := cL * (n + 1) ^ dL
    have hLb : L b ≤ P := hLle b
    have hMn : M n = (d + 2) * (n + P + 2) := rfl
    have hQ : n + P + 2 ≤ M n := by grind
    have hlen : (encPair encB encUnary (b, 2 ^ L b)).length = 2 * n + 1 + 2 ^ L b := by
      simp only [length_encPair, encUnary_apply, List.length_replicate, n]
    have hn : n < 2 ^ n := Nat.lt_two_pow_self
    -- each term is at most `2 ^ M n`
    have hM1 : 2 ^ n ≤ 2 ^ M n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hM2 : 4 ^ L b ≤ 2 ^ M n := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      refine Nat.pow_le_pow_right (by norm_num) ?_
      have : 2 * (n + P + 2) ≤ M n := by grind
      omega
    have hM3 : (2 * n + 1 + 2 ^ L b + 1) ^ d ≤ 2 ^ M n := by
      have hbase : 2 * n + 1 + 2 ^ L b + 1 ≤ 2 ^ (n + P + 2) := by
        have h2L : 2 ^ L b ≤ 2 ^ P := Nat.pow_le_pow_right (by norm_num) hLb
        rw [pow_add, pow_add]
        have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        have h2 : 1 ≤ 2 ^ P := Nat.one_le_two_pow
        nlinarith
      calc (2 * n + 1 + 2 ^ L b + 1) ^ d ≤ (2 ^ (n + P + 2)) ^ d := Nat.pow_le_pow_left hbase d
        _ = 2 ^ ((n + P + 2) * d) := by rw [← pow_mul]
        _ ≤ 2 ^ M n := by
          refine Nat.pow_le_pow_right (by norm_num) ?_
          rw [hMn, mul_comm]
          exact Nat.mul_le_mul_right _ (by omega)
    rw [hlen]
    calc n + (C * 2 ^ n + 4 ^ L b) + c * (2 * n + 1 + 2 ^ L b + 1) ^ d
        ≤ 2 ^ M n + (C * 2 ^ M n + 2 ^ M n) + c * 2 ^ M n := by
          gcongr
          exact hn.le.trans hM1
      _ ≤ (2 + C + c) * 2 ^ M n + (2 + C + c) := by ring_nf; omega
  -- `M n` is polynomial in `n`
  have hpoly : PolynomiallyBounded fun n => M n + 1 := by
    simp only [M]
    fun_prop
  obtain ⟨D, hD⟩ := hpoly
  refine mem_EXP_iff.mpr ⟨D, DTIME_mono_of_eventually_le ?_ hpre⟩
  filter_upwards [hD] with n hn
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end Cslib.Complexity

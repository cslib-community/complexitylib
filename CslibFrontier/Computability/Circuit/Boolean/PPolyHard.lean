/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.PPoly
public import Cslib.Computability.Circuit.Boolean.Shannon
import Cslib.Foundations.Data.Nat.Asymptotics

/-!
# A language outside P/poly

Shannon's counting argument gives, for every large `n`, a Boolean function on `n` bits whose
circuit complexity exceeds `2 ^ n / n` (`Cslib.Circuits.Boolean.Shannon.lt_complexity`). A
language whose slices are such functions is not in `P/poly`, since `2 ^ n / n` outgrows every
polynomial [Arora and Barak, Theorem 6.21][AroraBarak09].

## Main results

* `Cslib.Circuits.Boolean.PPoly.exists_not_mem`: some language over `Bool` is not in `P/poly`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.4][AroraBarak09]
* [C. E. Shannon, *The synthesis of two-terminal switching circuits*][Shannon1949]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Filter

/-- **P/poly is not every language.** Some language over `Bool` has slices whose circuit
complexity is not polynomially bounded. -/
theorem PPoly.exists_not_mem : ∃ L : Language Bool, L ∉ PPoly := by
  classical
  obtain ⟨N, hN⟩ := Shannon.lt_complexity
  let hard : ∀ n, (Fin n → Bool) → Bool := fun n =>
    if h : N ≤ n then Classical.choose (hN n h) else fun _ => false
  refine ⟨Language.ofSlices hard, fun hL => ?_⟩
  obtain ⟨d, hd⟩ := hL
  obtain ⟨n, hnN, hn1, hnd, hpow⟩ := ((eventually_ge_atTop N).and ((eventually_ge_atTop 1).and
    (hd.and (Nat.eventually_mul_pow_le_pow 2 (d + 1) one_lt_two)))).exists
  have hhard : (2 : ℝ) ^ n / n < complexity interpretation (single (hard n)) := by grind
  have hslice : (Language.ofSlices hard).slice n = hard n := Language.slice_ofSlices hard n
  simp only [hslice] at hnd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlt : (2 : ℝ) ^ n < n * n ^ d := by
    have : (2 : ℝ) ^ n / n < n ^ d :=
      hhard.trans_le (by exact_mod_cast hnd)
    rwa [div_lt_iff₀ hn0, mul_comm] at this
  have hlt' : 2 ^ n < n ^ (d + 1) := by
    rw [pow_succ', show (n : ℝ) * n ^ d = ((n * n ^ d : ℕ) : ℝ) by push_cast; ring] at *
    exact_mod_cast hlt
  have hpos : 1 ≤ n ^ (d + 1) := Nat.one_le_pow _ _ hn1
  omega

end Cslib.Circuits.Boolean

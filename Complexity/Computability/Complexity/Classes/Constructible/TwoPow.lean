/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Constructible
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.NatPolynomial
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Exponentials of constructible clocks

If `T` is time-constructible, so is `n ↦ 2 ^ (T n / k)` for every `k ≥ 1`. The machine computes
`T n` in binary within `O(T n)` steps and divides it by `k`. It then counts the quotient `m` down
to unary within `O((m + 1) ^ 2)` steps (`Turing.MultiTapeTM.ComputableInO.natToUnary`) and writes
`2 ^ m` in binary, as `m` zeros followed by a one. Since `T n < k * (m + 1)`, every stage is
polynomial in `m`, hence `O(2 ^ m)`.

Such clocks separate time classes at exponential scale. The clocked diagonal with clock
`2 ^ (T n / 4)` is decidable within time `O(2 ^ T n)`, which separates `DTIME[2 ^ T]` from the
classes of the counting simulation in `CountingSimulation.Separation`.

## Main results

* `Cslib.Complexity.TimeConstructible.two_pow_div`: `n ↦ 2 ^ (T n / k)` is time-constructible.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- **Exponentials of constructible clocks.** If `T` is time-constructible and `0 < k`, then so
is `n ↦ 2 ^ (T n / k)`. -/
theorem TimeConstructible.two_pow_div {T : ℕ → ℕ} (hT : TimeConstructible T) {k : ℕ}
    (hk : 0 < k) : TimeConstructible fun n => 2 ^ (T n / k) := by
  have hdiv : ComputableInPolyTime (fun m : ℕ => m / k) encNat encNat :=
    ComputableInPolyTime.binary_div.comp
      (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const k))
  have h₁ := ComputableInO.natToUnary.comp (hdiv.nat_inO.comp hT.computableInO)
  have h₂ := ((ComputableInDegree.two_pow_length encUnary).inO_one.comp h₁).of_enc_eq
    (encC := encNat) (g := fun x : List Bool => 2 ^ (T x.length / k)) fun x => by
      simp only [Function.comp_apply, encUnary_apply, List.length_replicate]
  obtain ⟨C, hC⟩ := PolynomiallyBounded.exists_le_mul_two_pow
    (p := fun m => 2 * (k * m + k) + (m + 1) ^ 2 + m) (by fun_prop)
  refine TimeConstructible.of_computableInO C h₂
    (s := fun n => T n + T n + T n / k + T n / k) (fun x => ?_) fun x => ?_
  · have hlt : T x.length < k * (T x.length / k + 1) := by
      rw [Nat.mul_add_one]
      exact Nat.lt_div_mul_add hk |>.trans_eq (by ring)
    have := hC (T x.length / k)
    simp only [Function.comp_apply, encUnary_apply, List.length_replicate]
    nlinarith
  · simp only [Function.comp_apply, encUnary_apply, List.length_replicate]
    exact le_rfl

end Cslib.Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.Primes.MillerRabin
import CslibFrontier.Foundations.NumberTheory.Primality.EulerLiars
import CslibFrontier.Foundations.NumberTheory.Primality.RabinMonier
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime

/-! Checked instances for the Euler-liar, strong-liar and Rabin–Monier bounds and for the
Miller–Rabin verifier: witnesses and liars for small composites, including the Carmichael number
`561` and the strong pseudoprime `2047` to base `2`, moduli where the Rabin–Monier bound is attained
or fails, and the verifier accepting and rejecting concrete random words. -/

namespace ComplexityTests.Primality

open Cslib.Complexity Turing.MultiTapeTM

/-! ### Rounds -/

-- `2` is a Miller–Rabin witness for `9`: `8 = 2 ^ 3 * 1` and `2 ^ 1, 2 ^ 2, 2 ^ 4 ≢ ±1 (mod 9)`.
example : MillerRabin.passes 8 2 = false := by decide

-- `8 ≡ -1 (mod 9)` is a strong liar for `9`.
example : MillerRabin.passes 8 8 = true := by decide

-- For `15`, `14 = 2 * 7`: `2 ^ 7 ≡ 8 (mod 15)`, so `2` is a witness, and `14 ≡ -1` is a liar.
example : MillerRabin.passes 14 2 = false ∧ MillerRabin.passes 14 14 = true := by decide

-- `561 = 3 * 11 * 17` is a Carmichael number, but `2` is a Miller–Rabin witness for it. The
-- unreduced powers are large, so these are checked by the kernel alone.
example : MillerRabin.passes 560 2 = false := by decide +kernel

-- `2047 = 23 * 89` is a strong pseudoprime to base `2`, and `3` is a witness for it.
example : MillerRabin.passes 2046 2 = true ∧ MillerRabin.passes 2046 3 = false := by
  decide +kernel

-- Every nonzero residue modulo the prime `13` passes.
example : ∀ a : Fin 12, MillerRabin.passes 12 (a + 1) = true := by decide

/-! ### Strong liars -/

-- `passes_eq_true_iff` transfers the computations to `ZMod.IsStrongLiar`.
example : ¬ ZMod.IsStrongLiar 9 2 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, show (2 : ZMod (8 + 1)) = ((2 : ℕ) : ZMod (8 + 1)) from rfl,
    ← MillerRabin.passes_eq_true_iff (by norm_num)]
  decide

example : ZMod.IsStrongLiar 9 8 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, show (8 : ZMod (8 + 1)) = ((8 : ℕ) : ZMod (8 + 1)) from rfl,
    ← MillerRabin.passes_eq_true_iff (by norm_num)]
  decide

-- The hypotheses of the Miller–Rabin and Solovay–Strassen bounds hold together for `n = 9`.
example : 2 * (Finset.univ.filter (ZMod.IsStrongLiar 9)).card ≤ Nat.totient 9 :=
  ZMod.two_mul_card_isStrongLiar_le (by decide) (by norm_num) (by norm_num)

example : 2 * Nat.card (ZMod.eulerLiars 9) ≤ Nat.totient 9 :=
  ZMod.two_mul_card_eulerLiars_le (by decide) (by norm_num) (by norm_num)

-- Modulo the odd prime `7` every unit is an Euler liar.
example : ZMod.eulerLiars 7 = ⊤ :=
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  ZMod.eulerLiars_eq_top (by norm_num)

-- Modulo `9`, the unit `-1 = 8` is an Euler liar: `8 ^ 4 = 1 = J(8 | 9)`.
example : (-1 : (ZMod 9)ˣ) ∈ ZMod.eulerLiars 9 := by
  rw [ZMod.mem_eulerLiars, Units.val_neg, Units.val_one,
    show ((-1 : ZMod 9)).val = 8 from rfl]
  norm_num

-- The unit `2` is not: `2 ^ 4 = 7`, while `J(2 | 9) = 1`.
example : ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 9) ∉ ZMod.eulerLiars 9 := by
  rw [ZMod.mem_eulerLiars, ZMod.coe_unitOfCoprime,
    show ((2 : ℕ) : ZMod 9).val = 2 from rfl]
  norm_num
  decide

/-! ### The Rabin–Monier bound -/

/-- Strong liars modulo `m + 1` are the residues that pass a Miller–Rabin round, so that counts of
strong liars can be computed. -/
theorem isStrongLiar_iff_passes {m : ℕ} (hm : 0 < m) (a : ZMod (m + 1)) :
    ZMod.IsStrongLiar (m + 1) a ↔ MillerRabin.passes m a.val = true := by
  rw [MillerRabin.passes_eq_true_iff hm, ZMod.natCast_zmod_val]

-- The bound applies to `15 = 3 * 5`.
example : 4 * (Finset.univ.filter (ZMod.IsStrongLiar 15)).card ≤ Nat.totient 15 :=
  ZMod.four_mul_card_isStrongLiar_le (by decide) (by norm_num) (by norm_num) (by norm_num)

-- It is attained there: `14 = 2 * 7`, the strong liars are `±1`, and `φ(15) = 8`. The bases `4` and
-- `11` have `a ^ 14 = 1` but `a ^ 7 = a`, so they are Fermat liars and not strong liars.
example : (Finset.univ.filter (ZMod.IsStrongLiar 15)).card = 2 ∧ Nat.totient 15 = 8 := by
  rw [Finset.filter_congr fun a _ => isStrongLiar_iff_passes (m := 14) (by norm_num) a]
  decide

example : ¬ ZMod.IsStrongLiar 15 4 ∧ (4 : ZMod 15) ^ 14 = 1 := by
  rw [isStrongLiar_iff_passes (m := 14) (by norm_num)]
  decide

-- It is attained by `91 = 7 * 13` as well: `18` strong liars and `φ(91) = 72`.
example : (Finset.univ.filter (ZMod.IsStrongLiar 91)).card = 18 ∧ Nat.totient 91 = 72 := by
  rw [Finset.filter_congr fun a _ => isStrongLiar_iff_passes (m := 90) (by norm_num) a]
  decide +kernel

-- The hypothesis `n ≠ 9` is needed: modulo `9` the strong liars are `±1`, and `4 * 2 > φ(9) = 6`.
example : ¬ 4 * (Finset.univ.filter (ZMod.IsStrongLiar 9)).card ≤ Nat.totient 9 := by
  rw [Finset.filter_congr fun a _ => isStrongLiar_iff_passes (m := 8) (by norm_num) a]
  decide

/-! ### The verifier -/

-- On `9` the verifier reads `8` random bits. The word with value `1` gives the base
-- `1 + 1 % 8 = 2`, a witness, and is accepted; the word with value `7` gives the base `8`, a liar,
-- and is rejected.
example : MillerRabin.verifier (9, [true, false, false, false, false, false, false, false]) =
    true := by decide

example : MillerRabin.verifier (9, [true, true, true, false, false, false, false, false]) =
    false := by decide

-- Primes are never accepted, and composites below `2` or even are always accepted.
example (r : List Bool) : MillerRabin.verifier (2, r) = false := by
  simp [MillerRabin.verifier]

example (r : List Bool) : MillerRabin.verifier (10, r) = true := by
  simp [MillerRabin.verifier]

example (r : Fin 6 → Bool) : MillerRabin.verifier (7, List.ofFn r) = false := by
  have h := (MillerRabin.decidesWithOneSidedError 7).2 (by norm_num)
  have hlen : (2 * Polynomial.X : Polynomial ℕ).eval (encNat 7).length = 6 := by
    rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat, encNat_apply]
    decide
  rw [hlen] at h
  exact h r

end ComplexityTests.Primality

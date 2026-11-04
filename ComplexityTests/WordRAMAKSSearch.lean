/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.WordRAM.AKS.CongruenceLoop
import Complexity.Algorithms.WordRAM.AKS.GcdTotient
import Complexity.Algorithms.WordRAM.AKS.OrderSearch
import Complexity.Foundations.NumberTheory.AKS.IntegerVariant

/-!
# The order search, step 3 and the integer thresholds of the AKS test

Concrete runs of the search for `r`, of the step-3 and totient loop and of the step-5 loop,
instances of their correctness theorems, and checked instances of the integer-threshold
conditions.
-/

namespace ComplexityTests.WordRAMAKSSearch

open Cslib.WordRAM Cslib.Algorithms.WordRAM

/-! ## The search for `r` -/

private def searchInput (n L : ℕ) : Data 13 :=
  (Data.init []).set AKS.OrderSearch.n n |>.set AKS.OrderSearch.L L

/-- For `n = 5` and `L = 2`: `r = 2` fails (`5 ≡ 1`), `r = 3` fails (`5² ≡ 1`), `r = 4` fails
(`5 ≡ 1`), and `r = 5` fails (`gcd = 5`); `r = 6` fails (`5² ≡ 1`), and `r = 7` is accepted. -/
example : (Code.eval 16 16 AKS.OrderSearch.program (searchInput 5 2)).map
      (·.1.regs AKS.OrderSearch.r) = some 7 := by
  decide +kernel

/-- `Good 5 2 7`: `5` is coprime to `7`, and `5 ≡ 5`, `5² ≡ 4` modulo `7`. -/
theorem good_5_2_7 : AKS.OrderSearch.Good 5 2 7 := by
  refine ⟨by decide, fun k hk1 hk2 => ?_⟩
  interval_cases k <;> decide

/-- The correctness theorem with `r₀ = 7`: the search stops at a good `2 ≤ r ≤ 7`. -/
example : ∃ y, ExecWithin 16 AKS.OrderSearch.program (searchInput 5 2) y
    (AKS.OrderSearch.time 2 7) ∧ AKS.OrderSearch.Good 5 2 (y.regs AKS.OrderSearch.r) := by
  obtain ⟨y, hy, -, -, hgood, -⟩ := AKS.OrderSearch.exec (w := 16) (searchInput 5 2)
    (by decide) (by decide) (by decide) good_5_2_7 (by decide) (by decide) (by decide)
  exact ⟨y, hy, hgood⟩

/-- `Good` is the order condition: `ord₇(5) = 6 > 2`. -/
example : 2 < orderOf ((5 : ℕ) : ZMod 7) :=
  (Cslib.AKS.lt_orderOf_iff (by norm_num)).mpr good_5_2_7

/-! ## Step 3 and the totient -/

private def gcdInput (n r : ℕ) : Data 11 :=
  (Data.init []).set AKS.GcdTotient.n n |>.set AKS.GcdTotient.r r

/-- For `n = 15` and `r = 4`, `gcd(3, 15) = 3` fails step 3; for `n = 7` it passes; `φ(4) = 2`. -/
example : (Code.eval 16 8 AKS.GcdTotient.program (gcdInput 15 4)).map
      (fun yn => (yn.1.regs AKS.GcdTotient.ok, yn.1.regs AKS.GcdTotient.phi)) = some (0, 2) ∧
    (Code.eval 16 8 AKS.GcdTotient.program (gcdInput 7 4)).map
      (fun yn => (yn.1.regs AKS.GcdTotient.ok, yn.1.regs AKS.GcdTotient.phi)) = some (1, 2) := by
  decide +kernel

/-- The correctness theorem computes `φ(4) = 2`. -/
example : ∃ y, ExecWithin 16 AKS.GcdTotient.program (gcdInput 7 4) y (AKS.GcdTotient.time 4) ∧
    y.regs AKS.GcdTotient.phi = 2 := by
  obtain ⟨y, hy, -, -, hphi, -⟩ := AKS.GcdTotient.exec (w := 16) (gcdInput 7 4) (N := 7) (R := 4)
    (by decide)
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨y, hy, hphi.trans (by decide)⟩

/-! ## Step 5 -/

/-- Blocks at `0`, `r` and `2r`, with `r`, `n` and the last tested value `A` in their registers. -/
private def loopInput (r n A : ℕ) : Data 29 :=
  ⟨fun j => if j = AKS.CongruenceLoop.B then r else if j = AKS.CongruenceLoop.T then 2 * r else
      if j = AKS.CongruenceLoop.rr then r else if j = AKS.CongruenceLoop.nn then n else
      if j = AKS.CongruenceLoop.A then A else 0,
    fun _ => 0⟩

/-- Modulo `X - 1`, `4` fails at `a = 1` (`2⁴ ≡ 0 ≢ 2`), so the flag is cleared. -/
example : (Code.eval 16 4 AKS.CongruenceLoop.program (loopInput 1 4 1)).map
      (·.1.regs AKS.CongruenceLoop.ok) = some 0 := by
  decide +kernel

/-- The correctness theorem: for the prime `5`, every `a ≤ 3` passes modulo `X² - 1`. -/
example : ∃ y, ExecWithin 16 AKS.CongruenceLoop.program (loopInput 2 5 3) y
    (AKS.CongruenceLoop.time 2 5 3) ∧ y.regs AKS.CongruenceLoop.ok = 1 := by
  obtain ⟨y, hy, -, hiff, -⟩ := AKS.CongruenceLoop.exec (w := 16) (loopInput 2 5 3) (a := 0)
    (b := 2) (t := 4) (r := 2) (n := 5) (A₀ := 3) rfl rfl rfl rfl rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  exact ⟨y, hy, hiff.mpr fun v _ _ => Cslib.AKS.congruence_of_prime (by decide) 2 v⟩

/-! ## Integer thresholds -/

/-- Step 3 rejects `15` with `r = 3`, since `gcd(3, 15) = 3`. -/
example (A : ℕ) : ¬ Cslib.AKS.PassesUpTo 15 3 A := by
  rintro ⟨-, h3, -⟩
  have := h3 3 (by norm_num) le_rfl
  revert this
  decide

end ComplexityTests.WordRAMAKSSearch

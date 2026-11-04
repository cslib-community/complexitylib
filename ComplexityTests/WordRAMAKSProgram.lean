/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.Primes

/-!
# The AKS program and PRIMES in `P`

Concrete runs of the top-level AKS program on small inputs, through each early exit, instances of
its correctness theorem on a prime and on a composite, and the membership of the primes in `P`.
-/

namespace ComplexityTests.WordRAMAKSProgram

open Cslib.WordRAM Cslib.Algorithms.WordRAM

/-- The answer of the program on `n` at word size `w`, allowing each loop `16` iterations. -/
private def run (w n : ℕ) : Option ℕ :=
  (Code.eval w 16 AKS.program (Data.init [n])).map (·.1.regs AKS.ans)

/-- `0` and `1` are not prime (step 0). -/
example : run 8 0 = some 0 ∧ run 8 1 = some 0 := by decide +kernel

/-- `4 = 2²` is a perfect power (step 1). -/
example : run 24 4 = some 0 := by decide +kernel

/-- `2` is prime: the search stops at `r = 3 ≥ 2` (step 4). -/
example : run 24 2 = some 1 := by decide +kernel

/-- `6` is composite: the search stops at `r = 11`, and `gcd(2, 6) = 2` (step 3). -/
example : run 32 6 = some 0 := by decide +kernel

/-- The correctness theorem on the prime `7`, at the width `8 (size 7 + 1) = 32`. -/
example : ∃ y, ExecWithin 32 AKS.program (.init [7]) y (AKS.time (Nat.size 7)) ∧
    y.regs AKS.ans = 1 := by
  obtain ⟨y, hy, -, hiff⟩ := AKS.answers (w := 32) 7 (by decide)
  exact ⟨y, hy, hiff.mpr (by decide)⟩

/-- The correctness theorem on the composite `91 = 7 · 13`, at the width `8 (size 91 + 1) = 64`. -/
example : ∃ y, ExecWithin 64 AKS.program (.init [91]) y (AKS.time (Nat.size 91)) ∧
    y.regs AKS.ans = 0 := by
  obtain ⟨y, hy, hle, hiff⟩ := AKS.answers (w := 64) 91 (by decide)
  refine ⟨y, hy, ?_⟩
  have : ¬ y.regs AKS.ans = 1 := fun h => (by decide : ¬ Nat.Prime 91) (hiff.mp h)
  omega

/-- **PRIMES is in `P`**, for the binary encoding of naturals. -/
example : {n : ℕ | n.Prime} ∈ Cslib.Complexity.P Turing.MultiTapeTM.encNat :=
  Cslib.Complexity.primes_mem_P

end ComplexityTests.WordRAMAKSProgram

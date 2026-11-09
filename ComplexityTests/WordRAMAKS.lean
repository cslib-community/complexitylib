/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.WordRAM.NatGcd
import Complexity.Algorithms.WordRAM.AKS.PerfectPower
import Complexity.Algorithms.WordRAM.AKS.PolyMul
import Complexity.Algorithms.WordRAM.AKS.PolyArray

/-!
# Word-RAM subroutines of the AKS primality test

Concrete runs of Euclid's algorithm, the integer `k`-th root, the perfect-power test,
multiplication modulo `X^r - 1` and `n`, and writing and comparing coefficient arrays, and
instances of their correctness theorems.
-/

namespace ComplexityTests.WordRAMAKS

open Cslib.WordRAM Cslib.Algorithms.WordRAM

/-! ## Greatest common divisors -/

private def gcdInput (a b : ℕ) : Data 4 := (Data.init []).set NatGcd.a a |>.set NatGcd.b b

/-- Euclid's algorithm on `(12, 18)`, `(17, 5)` and `(7, 0)`. -/
example : (Code.eval 8 8 NatGcd.program (gcdInput 12 18)).map (·.1.regs NatGcd.a) = some 6 ∧
    (Code.eval 8 8 NatGcd.program (gcdInput 17 5)).map (·.1.regs NatGcd.a) = some 1 ∧
    (Code.eval 8 8 NatGcd.program (gcdInput 7 0)).map (·.1.regs NatGcd.a) = some 7 := by
  decide

/-- The correctness theorem at width `8`: `gcd(12, 18) = 6` within `93` instructions. -/
example : ∃ y, ExecWithin 8 NatGcd.program (gcdInput 12 18) y 93 ∧ y.regs NatGcd.a = 6 := by
  obtain ⟨y, hy, ha, -⟩ := NatGcd.exec (w := 8) (gcdInput 12 18) (by decide) (by decide)
  exact ⟨y, hy, ha.trans (by decide)⟩

/-! ## Integer roots -/

private def rootInput (n k : ℕ) : Data 10 :=
  (Data.init []).set NatNthRoot.n n |>.set NatNthRoot.k k

/-- `⌊√30⌋ = 5`, `⌊∛64⌋ = 4` and `⌊∛63⌋ = 3`, by binary search. -/
example : (Code.eval 16 16 NatNthRoot.program (rootInput 30 2)).map (·.1.regs NatNthRoot.lo) =
      some 5 ∧
    (Code.eval 16 16 NatNthRoot.program (rootInput 64 3)).map (·.1.regs NatNthRoot.lo) = some 4 ∧
    (Code.eval 16 16 NatNthRoot.program (rootInput 63 3)).map (·.1.regs NatNthRoot.lo) =
      some 3 := by
  decide

/-- The correctness theorem: the search returns `Nat.nthRoot 3 63`. -/
example : ∃ y, ExecWithin 16 NatNthRoot.program (rootInput 63 3) y 193 ∧
    y.regs NatNthRoot.lo = Nat.nthRoot 3 63 := by
  obtain ⟨y, hy, hlo, -⟩ := NatNthRoot.exec (w := 16) (rootInput 63 3) (by decide) (by decide)
    (by decide)
  exact ⟨y, hy.mono (by decide), hlo⟩

/-! ## Perfect powers -/

private def ppInput (n : ℕ) : Data 14 := (Data.init []).set AKS.PerfectPower.n n

/-- `8 = 2³` and `9 = 3²` are perfect powers; `10` and `12` are not. -/
example : (Code.eval 16 16 AKS.PerfectPower.program (ppInput 8)).map
      (·.1.regs AKS.PerfectPower.flag) = some 1 ∧
    (Code.eval 16 16 AKS.PerfectPower.program (ppInput 9)).map
      (·.1.regs AKS.PerfectPower.flag) = some 1 ∧
    (Code.eval 16 16 AKS.PerfectPower.program (ppInput 10)).map
      (·.1.regs AKS.PerfectPower.flag) = some 0 ∧
    (Code.eval 16 16 AKS.PerfectPower.program (ppInput 12)).map
      (·.1.regs AKS.PerfectPower.flag) = some 0 := by
  decide

/-- The decision procedure for `IsPerfectPower` agrees. -/
example : Cslib.AKS.IsPerfectPower 27 ∧ ¬Cslib.AKS.IsPerfectPower 12 := by decide

/-- The correctness theorem on `27 = 3³`. -/
example : ∃ y, ExecWithin 16 AKS.PerfectPower.program (ppInput 27) y
      (AKS.PerfectPower.time 27) ∧ y.regs AKS.PerfectPower.flag = 1 := by
  obtain ⟨y, hy, hf, -⟩ := AKS.PerfectPower.exec (w := 16) (ppInput 27) (by decide) (by decide)
  exact ⟨y, hy, hf.trans (by decide)⟩

/-! ## Multiplication modulo `X^r - 1` and `n` -/

/-- Factors at `10` and `13`, product at `20`, `r = 3`, `n = 5`: `p = X + 1`, `q = 4X² + 3`. -/
private def mulInput (pa pb : ℕ) : Data 14 :=
  ⟨fun j => if j = AKS.PolyMul.pa then pa else if j = AKS.PolyMul.pb then pb else
      if j = AKS.PolyMul.pt then 20 else if j = AKS.PolyMul.rr then 3 else
      if j = AKS.PolyMul.nn then 5 else 0,
    fun a => if a = 10 ∨ a = 11 then 1 else if a = 13 then 3 else if a = 15 then 4 else
      if a = 23 then 99 else 0⟩

/-- `(X + 1)² = X² + 2X + 1` and `(X + 1)(4X² + 3) = 4X³ + 4X² + 3X + 3 ≡ 4X² + 3X + 2`
modulo `X³ - 1` and `5`. -/
example : (Code.eval 16 4 AKS.PolyMul.program (mulInput 10 10)).map
      (fun yn => [yn.1.mem 20, yn.1.mem 21, yn.1.mem 22]) = some [1, 2, 1] ∧
    (Code.eval 16 4 AKS.PolyMul.program (mulInput 10 13)).map
      (fun yn => [yn.1.mem 20, yn.1.mem 21, yn.1.mem 22]) = some [2, 3, 4] := by
  decide +kernel

/-- The correctness theorem computes the same square through `Cslib.AKS.mulCoeff`. -/
example : ∃ y, ExecWithin 16 AKS.PolyMul.program (mulInput 10 10) y 224 ∧ y.mem 21 = 2 ∧
    y.mem 23 = 99 := by
  obtain ⟨y, hy, hcoeff, hout, -⟩ := AKS.PolyMul.exec (w := 16) (mulInput 10 10)
    (a := 10) (b := 10) (t := 20) (r := 3) (n := 5) rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  refine ⟨y, hy, ?_, hout 23 (by decide)⟩
  rw [show (21 : ℕ) = 20 + 1 from rfl, hcoeff 1 (by decide)]
  decide

/-! ## Writing and comparing coefficient arrays -/

private def fillInput (e a : ℕ) : Data 10 :=
  ⟨fun j => if j = AKS.Fill.base then 20 else if j = AKS.Fill.rr then 3 else
      if j = AKS.Fill.nn then 5 else if j = AKS.Fill.er then e % 3 else
      if j = AKS.Fill.aa then a else 0,
    fun a => if a = 23 then 99 else 7⟩

/-- `X^4 + 7 ≡ X + 2` and `X^3 + 4 ≡ 0` modulo `X³ - 1` and `5`, over dirty memory. -/
example : (Code.eval 16 4 AKS.Fill.program (fillInput 4 7)).map
      (fun yn => [yn.1.mem 20, yn.1.mem 21, yn.1.mem 22, yn.1.mem 23]) = some [2, 1, 0, 99] ∧
    (Code.eval 16 4 AKS.Fill.program (fillInput 3 4)).map
      (fun yn => [yn.1.mem 20, yn.1.mem 21, yn.1.mem 22]) = some [0, 0, 0] := by
  decide +kernel

/-- The correctness theorem agrees with `Cslib.AKS.powAddCoeff`. -/
example : ∃ y, ExecWithin 16 AKS.Fill.program (fillInput 4 7) y 28 ∧ y.mem 20 = 2 := by
  obtain ⟨y, hy, hc, -⟩ := AKS.Fill.exec (w := 16) (fillInput 4 7) (b := 20) (r := 3) (n := 5)
    (e := 4) (a := 7) rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
    (by decide)
  exact ⟨y, hy, (hc 0 (by decide)).trans (by decide)⟩

private def cmpInput : Data 9 :=
  ⟨fun j => if j = AKS.Compare.p then 10 else if j = AKS.Compare.q then 20 else
      if j = AKS.Compare.rr then 3 else 0,
    fun a => if a = 12 then 5 else if a = 22 then 6 else 1⟩

/-- Blocks agreeing on two cells but not the third compare unequal; shorter prefixes agree. -/
example : (Code.eval 16 4 AKS.Compare.program cmpInput).map (·.1.regs AKS.Compare.flag) =
      some 0 ∧
    (Code.eval 16 4 AKS.Compare.program (cmpInput.set AKS.Compare.rr 2)).map
      (·.1.regs AKS.Compare.flag) = some 1 := by
  decide

end ComplexityTests.WordRAMAKS

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Modulus

/-! # Complete native two-prime modulus computations -/

namespace ComplexityTests.WordRAMChanHeModulus

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.WordRAM.ThreeSum.ChanHe

private def input (n digits : ℕ) (values : ℕ → ℤ) : Data 64 :=
  ⟨fun i => if i.val = 28 ∨ i.val = 30 ∨ i.val = 32 then n
    else if i.val = 29 ∨ i.val = 31 ∨ i.val = 33 then 1
    else if i.val = 34 then 20 else if i.val = 35 then 30
    else if i.val = 40 then 2 else if i.val = 41 then 10
    else if i.val = 42 ∨ i.val = 59 then (if i.val = 42 then 1 else digits) else 71,
    fun a => if 1 ≤ a ∧ a < 1 + n then encode (values (a - 1))
      else if 10 ≤ a ∧ a ≤ 12 then (if a = 12 then 1 else 0) else 79⟩

-- Each execution includes two complete prime scans and three baseline counting calls.
set_option maxRecDepth 8192 in
/-- Empty sets still compute the exact minimum/default specification, returning `2*2`. -/
example : (Code.eval 8 6 Modulus.program (input 0 1 (fun i => i))).map
    (fun yn => [yn.1.regs Modulus.first, yn.1.regs Modulus.output,
      yn.1.regs Modulus.digits, yn.1.mem 12]) = some [2, 4, 1, 1] := by decide

/-- A target word too small for the very first scalar setup is rejected. -/
example : (Code.eval 1 1 Modulus.program (input 0 1 (fun i => i))).map
    (fun yn => yn.1.regs Modulus.output) = none := by decide

/-- The native execution contract is admissible at every small array length, including all
fits, the complete bitmap, preserved input and injective enumeration. -/
example (n : Fin 3) : ∃ y,
    ExecWithin 10 Modulus.program (input n 1 (fun i => i)) y (714 * (n : ℕ) + 1111) ∧
      y.regs Modulus.output = 4 := by
  let x := input n 1 (fun i => i)
  have hn (j : Fin 3) : x.regs (CountCall.length j) = n := by fin_cases j <;> rfl
  have hs (j : Fin 3) : x.regs (CountCall.source j) = 1 := by fin_cases j <;> rfl
  have hN : (n : ℕ) ≤ 2 := by omega
  have hlimit : x.regs Search.limit = 2 := rfl
  obtain ⟨y, he, hr, hm, hp, hv⟩ := Modulus.exec (w := 8) x (fun _ i => (i : ℤ))
    (by change 2 ≤ 2; decide)
    (by change Cslib.GenericRAM.Signed.Fits 8 (4 : ℤ); decide)
    (by fin_cases n <;> decide) (by change 1 = (Nat.primesLE 2).card; decide)
    (by change 10 + (2 + 1) ≤ 20; decide)
    (by intro q hq; change q ≤ 2 at hq; fin_cases n <;> interval_cases q <;> decide)
    (by intro j i hi; rw [hn] at hi; have hi1 : i ≤ 1 := by omega
        interval_cases i <;> decide)
    (by intro j; rw [hs, hn]; change 1 + (n : ℕ) ≤ 20; omega)
    (by intro j; rw [hn]; change 20 + (n : ℕ) ≤ 30; omega)
    (by
      intro j i hi
      rw [hn] at hi
      rw [hs]
      change (if 1 ≤ 1 + i ∧ 1 + i < 1 + (n : ℕ) then encode ((1 + i - 1 : ℕ) : ℤ)
        else if 10 ≤ 1 + i ∧ 1 + i ≤ 12 then (if 1 + i = 12 then 1 else 0) else 79) = _
      simp only [show 1 ≤ 1 + i ∧ 1 + i < 1 + (n : ℕ) by omega,
        and_self, ↓reduceIte, show 1 + i - 1 = i by omega])
    (by intro j a _ b _ hab; change (a : ℤ) = (b : ℤ) at hab; exact_mod_cast hab)
  have hcost : Modulus.cost x = 714 * (n : ℕ) + 1111 := by
    simp only [Modulus.cost, Modulus.searchTime, hn, hlimit]
    omega
  refine ⟨y, by simpa only [hcost] using he, ?_⟩
  have hvalue : Cslib.Algorithms.ThreeSum.ChanHe.modulus (Nat.primesLE 2) 1
      ((Finset.range (n : ℕ)).image fun i : ℕ => (i : ℤ))
      ((Finset.range (n : ℕ)).image fun i : ℕ => (i : ℤ))
      ((Finset.range (n : ℕ)).image fun i : ℕ => (i : ℤ)) = 4 := by fin_cases n <;> decide
  simp only [hn] at hv
  exact hv.trans hvalue

/-- A zero divisor bound and negative colliding values reject the only prime twice. The full
native theorem returns the exact default product one, with admissible input and resource bounds. -/
example : ∃ y, ExecWithin 10 Modulus.program
      (input 2 0 (fun i => if i = 0 then -2 else 0)) y
      (Modulus.cost (input 2 0 (fun i => if i = 0 then -2 else 0))) ∧
    y.regs Modulus.first = 1 ∧ y.regs Modulus.output = 1 := by
  let values (i : ℕ) : ℤ := if i = 0 then -2 else 0
  let x := input 2 0 values
  have hn (j : Fin 3) : x.regs (CountCall.length j) = 2 := by fin_cases j <;> rfl
  obtain ⟨y, he, hr, hm, hp, hv⟩ := Modulus.exec (w := 8) x (fun _ => values)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro q hq; change q ≤ 2 at hq; interval_cases q <;> decide)
    (by intro j i hi; rw [hn] at hi; interval_cases i <;> decide)
    (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide)
    (by intro j i hi; rw [hn] at hi; fin_cases j <;> interval_cases i <;> decide)
    (by
      intro j a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_range, hn] at ha hb
      interval_cases a <;> interval_cases b <;> norm_num [values] at *)
  refine ⟨y, he, ?_, ?_⟩
  · have hvalue : Cslib.Algorithms.ThreeSum.ChanHe.firstP (Nat.primesLE 2) 0
        ((Finset.range 2).image values) ((Finset.range 2).image values)
        ((Finset.range 2).image values) = 1 := by decide
    simp only [hn] at hp
    exact hp.trans hvalue
  · have hvalue : Cslib.Algorithms.ThreeSum.ChanHe.modulus (Nat.primesLE 2) 0
        ((Finset.range 2).image values) ((Finset.range 2).image values)
        ((Finset.range 2).image values) = 1 := by decide
    simp only [hn] at hv
    exact hv.trans hvalue

end ComplexityTests.WordRAMChanHeModulus

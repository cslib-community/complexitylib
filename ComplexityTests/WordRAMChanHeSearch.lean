/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Search

/-! # Executed least-prime collision searches -/

namespace ComplexityTests.WordRAMChanHeSearch

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe
open Cslib.Algorithms.WordRAM.ThreeSum.ChanHe

private def emptyInput (m : ℕ) : Data 64 :=
  ⟨fun i => if i.val = 28 ∨ i.val = 30 ∨ i.val = 32 then 0
    else if i.val = 29 ∨ i.val = 31 ∨ i.val = 33 then 1
    else if i.val = 34 then 20 else if i.val = 35 then 30
    else if i.val = 40 then m else if i.val = 41 then 10
    else if i.val = 42 then 1 else if i.val = 43 then 1
    else if i.val = 44 ∨ i.val = 45 ∨ i.val = 46 then 0 else 71,
    fun a => if a = 12 ∨ a = 13 then 1 else 0⟩

/-- Zero candidates return the specified default, without running a collision query. -/
example : (Code.eval 8 2 Search.program (emptyInput 0)).map
    (fun yn => yn.1.regs Search.answer) = some 1 := by decide

/-- The nonprime boundary one still returns the default. -/
example : (Code.eval 8 3 Search.program (emptyInput 1)).map
    (fun yn => yn.1.regs Search.answer) = some 1 := by decide

-- The positive case reduces the full renamed three-set query inside the search loop.
set_option maxRecDepth 8192 in
/-- The first prime is accepted at three zero thresholds for three empty sets. -/
example : (Code.eval 8 4 Search.program (emptyInput 2)).map
    (fun yn => [yn.1.regs Search.answer, yn.1.regs Search.found, yn.1.mem 12]) =
      some [2, 1, 1] := by decide

-- After accepting two, the search executes only the charged skip branch for three.
set_option maxRecDepth 8192 in
/-- Later accepted primes cannot overwrite the minimum or rerun the collision query. -/
example : (Code.eval 8 5 Search.program (emptyInput 3)).map
    (fun yn => [yn.1.regs Search.answer, yn.1.regs CountCall.modulus]) =
      some [2, 4] := by decide

-- The rejected prime still runs all three native collision-counting calls.
set_option maxRecDepth 8192 in
/-- The only prime fails because zero and two collide, so the answer is the default one. -/
example : (Code.eval 8 4 Search.program
    ⟨Function.update (emptyInput 2).regs (CountCall.length 0) 2,
      Function.update (emptyInput 2).mem 2 4⟩).map
    (fun yn => [yn.1.regs Search.answer, yn.1.regs Search.found]) =
      some [1, 0] := by decide

/-- The full execution contract has an admissible initialized instance, including every fit,
bitmap cell and input frame. -/
example : ∃ y, ExecWithin 8 Search.program (emptyInput 2) y (3 * 132 + 9) ∧
    y.regs Search.answer = 2 := by
  have hlen (j : Fin 3) : (emptyInput 2).regs (CountCall.length j) = 0 := by
    fin_cases j <;> decide
  have hcut (j : Fin 3) : (emptyInput 2).regs (CollisionTest.threshold j) = 0 := by
    fin_cases j <;> decide
  obtain ⟨y, he, hregs, hmem, ha⟩ := Search.exec (w := 6) (emptyInput 2) (fun _ _ => 0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro q hq; change q ≤ 2 at hq; interval_cases q <;> decide)
    (by intros; decide)
    (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide)
    (by decide) (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide)
    (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide)
    (by intro j i hi; rw [hlen] at hi; omega)
    (by
      intro j a ha
      simp only [hlen, Finset.range_zero, Finset.coe_empty, Set.mem_empty_iff_false] at ha)
  refine ⟨y, he, ?_⟩
  simp only [hlen, hcut, Finset.range_zero, Finset.image_empty, coll, Finset.offDiag_empty,
    Finset.filter_empty, Finset.card_empty, Nat.zero_mul, Nat.le_refl, implies_true,
    Finset.filter_true] at ha
  have hselect : minOrOne (Nat.primesLE 2) = 2 := by decide
  change y.regs Search.answer = minOrOne (Nat.primesLE 2) at ha
  exact ha.trans hselect

private def laterInput : Data 64 :=
  ⟨Function.update (Function.update (emptyInput 3).regs (CountCall.length 0) 2) Search.factor 2,
    Function.update (emptyInput 3).mem 2 8⟩

private def laterValues (j : Fin 3) (i : ℕ) : ℤ := if j = 0 then if i = 0 then 0 else 4 else 0

-- Factor two queries moduli four and six. The first collides on {0,4}; the second does not.
-- The actual answer, accepted flag, encoded modulus and charged bound are all observed.
/-- info: true -/
#guard_msgs in
#eval decide ((Code.eval 8 8 Search.program laterInput).map (fun yn =>
  ([yn.1.regs Search.answer, yn.1.regs Search.found, yn.1.regs CountCall.modulus],
    decide (yn.2 ≤ 1049))) = some ([3, 1, 12], true))

-- The same nonempty factor-two case discharges every fit, array and bitmap premise of the
-- complete native execution theorem; its output witness is the actual executed state.
example : ∃ y, ExecWithin 8 Search.program laterInput y 1049 ∧ y.regs Search.answer = 3 := by
  obtain ⟨y, he, _, _, ha⟩ := Search.exec (w := 6) laterInput laterValues
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro q hq; change q ≤ 3 at hq; interval_cases q <;> decide)
    (by intro j i _; unfold laterValues; split; split <;> decide; decide)
    (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide)
    (by decide) (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide)
    (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide)
    (by
      intro j i hi
      fin_cases j
      · have hi' : i < 2 := hi
        interval_cases i <;> decide
      · have hi' : i < 0 := hi
        omega
      · have hi' : i < 0 := hi
        omega)
    (by
      intro j i hi k hk he
      fin_cases j
      · have hi' : i < 2 := Finset.mem_range.mp hi
        have hk' : k < 2 := Finset.mem_range.mp hk
        interval_cases i <;> interval_cases k <;> simp [laterValues] at he ⊢
      · have hi' : i < 0 := Finset.mem_range.mp hi
        omega
      · have hi' : i < 0 := Finset.mem_range.mp hi
        omega)
  refine ⟨y, ?_, ha.trans (by decide)⟩
  convert he using 1
  decide

end ComplexityTests.WordRAMChanHeSearch

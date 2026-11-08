/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import all Complexity.Cryptanalysis.AddXNORNativeDissection
import all Complexity.Cryptanalysis.AddXNORNativeCounterPair
import all Complexity.Cryptanalysis.AddXNORNativeSelectedClass
import all Complexity.Cryptanalysis.AddXNORNativeOrientedSearch
import Mathlib.Tactic.IntervalCases

/-! # Original-array computed-orientation and all-class clients -/

set_option linter.privateModule false

open Cslib.WordRAM Cslib.Cryptanalysis.AddXNOR
open Cslib.Cryptanalysis.AddXNOR.Native.Quarter
open Cslib.Cryptanalysis.AddXNOR.Native.Driver

private def first : List (BitVec 3) := [1#3, 2#3, 4#3]
private def middle : List (BitVec 3) := [1#3]

private def layout :
    SearchLayout 16 3 2 first.length middle.length middle.length middle.length where
  b₁ := 5
  b₂ := 10
  b₃ := 15
  b₄ := 20
  q₂ := 128
  q₃ := 144
  h := 160
  f := 168
  h₄ := 240
  f₄ := 248
  D := 320
  input₁ := by decide
  input₂ := by decide
  input₃ := by decide
  input₄ := by decide
  project₂ := by decide
  project₃ := by decide
  positive := by decide
  heads := by decide
  arena := by decide
  heads₄ := by decide
  boundary := by decide
  capacity := by decide

private def counters : CounterLayout layout where
  prefixBase := 30
  suffixBase := 40
  q := 64
  B := 80
  r := 96
  C := 112
  prefixEnd := by decide
  suffixEnd := by decide
  firstEnd := by decide
  secondEnd := by decide
  thirdEnd := by decide
  fourthEnd := by decide
  projection := by decide
  separation := by decide
  projectionBack := by decide
  below := by decide
  capacityForward := by decide
  capacityBackward := by decide
  capacityScan := by decide

private def input : Data 40 :=
  { regs := fun _ => 99
    mem := fun a => if a = 5 ∨ a = 10 ∨ a = 15 ∨ a = 20 ∨ a = 30 ∨ a = 33 ∨
      a = 40 ∨ a = 41
      then 1 else if a = 6 ∨ a = 31 then 2 else if a = 7 ∨ a = 32 then 4
      else if a < 320 then 17 else 0 }

private theorem raw : layout.Raw first middle middle middle (input.comap bank) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; change i < 3 at hi; interval_cases i <;> decide +revert
  · intro i hi; change i < 1 at hi; interval_cases i; decide +revert
  · intro i hi; change i < 1 at hi; interval_cases i; decide +revert
  · intro i hi; change i < 1 at hi; interval_cases i; decide +revert
  · intro a ha
    change 320 ≤ a at ha
    simp [input, show ¬a = 5 by omega, show ¬a = 10 by omega, show ¬a = 15 by omega,
      show ¬a = 20 by omega, show ¬a = 30 by omega, show ¬a = 33 by omega,
      show ¬a = 40 by omega, show ¬a = 41 by omega, show ¬a = 6 by omega,
      show ¬a = 31 by omega, show ¬a = 7 by omega, show ¬a = 32 by omega,
      show ¬a < 320 by omega]

/-- All raw premises of the general theorem, with unequal quarter lengths,
non-self-inverse addition, initially dirty scratch and colliding low keys. -/
private theorem checked (t : BitVec 3) :
    ∃ y, ExecWithin 16 (dissection layout counters 1#3 t) input y
        (prepareTime 2 4 2 + (5 + loopTime (p := 2) first middle middle middle 1#3 t 0 4)) ∧
      (y.regs tag ≠ 0 ↔
        ∃ g : BitVec 2, PackedClassSolution first middle middle middle 1#3 t g) ∧
      (y.regs tag = 0 ↔
        ¬∃ g : BitVec 2, PackedClassSolution first middle middle middle 1#3 t g) ∧
      (y.regs tag ≠ 0 → eval (witness first middle middle middle y) 1#3 = t) ∧
      y.regs balance = computedBalance (p := 2) first middle middle middle 1#3 t ∧
      layout.Raw first middle middle middle (y.comap bank) := by
  apply dissection_exec (by decide) first middle middle middle 1#3 t layout counters input raw
  · intro i hi; change i < 4 at hi; interval_cases i <;> decide +revert
  · intro i hi; change i < 2 at hi; interval_cases i <;> decide +revert
  · decide
  · decide

/-- Class zero is a real hit. Its actual backward count is smaller, so the
native selector executes inverse retention rather than substituting forward data. -/
example : backwardCount middle middle 2#3 0#2 = 1 ∧
    forwardCount first middle 1#3 0#2 = 4 ∧
    computedBalance (p := 2) first middle middle middle 1#3 2#3 = 2 := by
  decide +kernel

example : ∃ y, ExecWithin 16 (dissection layout counters 1#3 2#3) input y
      (prepareTime 2 4 2 + (5 + loopTime (p := 2) first middle middle middle 1#3 2#3 0 4)) ∧
    y.regs tag ≠ 0 ∧ eval (witness first middle middle middle y) 1#3 = 2#3 ∧
    y.regs balance = 2 ∧ (∀ a, 320 ≤ a → y.mem a = 0) := by
  obtain ⟨y, he, hit, _, sound, mu, yr⟩ := checked 2#3
  have hh : y.regs tag ≠ 0 := hit.mpr ⟨0#2, 4, by decide, 0, by decide, 0, by decide,
    0, by decide, by decide +kernel, by decide +kernel⟩
  exact ⟨y, he, hh, sound hh, mu.trans (by decide +kernel), yr.2.2.2.2⟩

/-- Reversing the physical layout swaps unequal quarters without changing the
solution event; the returned inverse witness solves the original, not the dual. -/
example (g : BitVec 2) :
    PackedClassSolution middle.reverse middle.reverse middle.reverse first.reverse
        (~~~2#3) (~~~1#3) (~~~g) ↔
      PackedClassSolution first middle middle middle 1#3 2#3 g :=
  packedClassSolution_reverse_iff (by decide) first middle middle middle 1#3 2#3 g

/-- The other orientation is selected when its actual count is smaller. -/
example : forwardCount middle middle 2#3 0#2 = 1 ∧
    backwardCount middle first 1#3 0#2 = 6 := by decide +kernel

/-- Counter multiplicity counts all four indexed zero-width words, while a
single dictionary state suffices after replacement collisions. -/
example : forwardCount [0#0] [0#0] 0#0 0#0 = 4 ∧
    backwardCount [0#0] [0#0] 0#0 0#0 = 4 ∧
    computedBalance (p := 0) [0#0] [0#0] [0#0] [0#0] 0#0 0#0 = 4 := by decide +kernel

/-- No quarter operands: the outer composition must exhaust both low-bit classes
when the original initial and target words disagree. -/
private def emptyLayout : SearchLayout 16 1 1 0 0 0 0 where
  b₁ := 5
  b₂ := 10
  b₃ := 15
  b₄ := 20
  q₂ := 128
  q₃ := 144
  h := 160
  f := 168
  h₄ := 240
  f₄ := 248
  D := 320
  input₁ := by decide
  input₂ := by decide
  input₃ := by decide
  input₄ := by decide
  project₂ := by decide
  project₃ := by decide
  positive := by decide
  heads := by decide
  arena := by decide
  heads₄ := by decide
  boundary := by decide
  capacity := by decide

private def emptyCounters : CounterLayout emptyLayout where
  prefixBase := 30
  suffixBase := 40
  q := 64
  B := 80
  r := 96
  C := 112
  prefixEnd := by decide
  suffixEnd := by decide
  firstEnd := by decide
  secondEnd := by decide
  thirdEnd := by decide
  fourthEnd := by decide
  projection := by decide
  separation := by decide
  projectionBack := by decide
  below := by decide
  capacityForward := by decide
  capacityBackward := by decide
  capacityScan := by decide

example : ((dissection emptyLayout emptyCounters 0#1 1#1).eval 16 8
      { regs := fun _ => 99, mem := fun _ => 0 }).map
      (fun y => (y.1.regs tag, y.1.regs balance, y.1.mem 320,
        y.1.regs classIndex, y.1.regs classLimit)) = some (0, 0, 0, 2, 2) := by
  decide +kernel

/-- Width-zero multiplicity collisions take the tie/forward branch; all actual
release stores run, and the returned original witness words survive release. -/
private def collisionLayout : SearchLayout 16 0 0 1 1 1 1 where
  b₁ := 5
  b₂ := 10
  b₃ := 15
  b₄ := 20
  q₂ := 128
  q₃ := 144
  h := 160
  f := 168
  h₄ := 240
  f₄ := 248
  D := 320
  input₁ := by decide
  input₂ := by decide
  input₃ := by decide
  input₄ := by decide
  project₂ := by decide
  project₃ := by decide
  positive := by decide
  heads := by decide
  arena := by decide
  heads₄ := by decide
  boundary := by decide
  capacity := by decide

private def collisionCounters : CounterLayout collisionLayout where
  prefixBase := 30
  suffixBase := 40
  q := 64
  B := 80
  r := 96
  C := 112
  prefixEnd := by decide
  suffixEnd := by decide
  firstEnd := by decide
  secondEnd := by decide
  thirdEnd := by decide
  fourthEnd := by decide
  projection := by decide
  separation := by decide
  projectionBack := by decide
  below := by decide
  capacityForward := by decide
  capacityBackward := by decide
  capacityScan := by decide

example : ((dissection collisionLayout collisionCounters 0#0 0#0).eval 16 16
      { regs := fun _ => 99, mem := fun _ => 0 }).map
      (fun y => [y.1.regs tag, y.1.regs balance, y.1.regs orientation, y.1.mem 320,
        y.1.regs (bank Cslib.Cryptanalysis.AddXNOR.Native.Dictionary.top),
        y.1.regs (bank bits), y.1.regs classIndex,
        y.1.regs classLimit]) = some [1, 4, 0, 0, 0, 1, 1, 1] := by
  decide +kernel

/-- A smaller non-self-inverse raw instance exercises both actual strict
orientation branches without an expensive whole-instance kernel reduction. -/
private def smallLayout : SearchLayout 16 2 1 2 0 0 1 where
  b₁ := 5
  b₂ := 10
  b₃ := 15
  b₄ := 20
  q₂ := 128
  q₃ := 144
  h := 160
  f := 168
  h₄ := 240
  f₄ := 248
  D := 320
  input₁ := by decide
  input₂ := by decide
  input₃ := by decide
  input₄ := by decide
  project₂ := by decide
  project₃ := by decide
  positive := by decide
  heads := by decide
  arena := by decide
  heads₄ := by decide
  boundary := by decide
  capacity := by decide

private def smallCounters : CounterLayout smallLayout where
  prefixBase := 30
  suffixBase := 40
  q := 64
  B := 80
  r := 96
  C := 112
  prefixEnd := by decide
  suffixEnd := by decide
  firstEnd := by decide
  secondEnd := by decide
  thirdEnd := by decide
  fourthEnd := by decide
  projection := by decide
  separation := by decide
  projectionBack := by decide
  below := by decide
  capacityForward := by decide
  capacityBackward := by decide
  capacityScan := by decide

private def smallInput : Data 40 :=
  { regs := fun _ => 99
    mem := fun a => if a = 5 ∨ a = 20 ∨ a = 30 ∨ a = 40 then 1
      else if a = 6 ∨ a = 31 then 2 else 0 }

example : ((dissection smallLayout smallCounters 0#2 0#2).eval 16 8 smallInput).map
      (fun y => (y.1.regs orientation, Decidable.decide (y.1.regs tag ≠ 0),
        y.1.regs balance, y.1.mem 320, y.1.regs classIndex,
        y.1.regs classLimit)) = some (1, true, 1, 0, 2, 2) := by
  decide +kernel

private def smallDual := reverseLayout [1#2, 2#2] [] [] [1#2] smallLayout

private def smallDualCounters : CounterLayout smallDual where
  prefixBase := 40
  suffixBase := 30
  q := 64
  B := 80
  r := 96
  C := 112
  prefixEnd := by decide
  suffixEnd := by decide
  firstEnd := by decide
  secondEnd := by decide
  thirdEnd := by decide
  fourthEnd := by decide
  projection := by decide
  separation := by decide
  projectionBack := by decide
  below := by decide
  capacityForward := by decide
  capacityBackward := by decide
  capacityScan := by decide

example : ((dissection smallDual smallDualCounters 3#2 3#2).eval 16 8 smallInput).map
      (fun y => (y.1.regs orientation, Decidable.decide (y.1.regs tag ≠ 0),
        y.1.regs balance, y.1.mem 320, y.1.regs classIndex,
        y.1.regs classLimit)) = some (0, true, 1, 0, 2, 2) := by
  decide +kernel

/-- The whole compiled block has the same size at every projection width,
quarter length and admitted layout, including zero-width collision instances. -/
example {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d) (K : CounterLayout L)
    (s t : BitVec m) : (dissection L K s t).size = 960 :=
  dissection_size L K s t

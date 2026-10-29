/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.CountCall
import Mathlib.Tactic.FinCases

/-!
# Native tests of the three Chan–He collision inequalities

Each inequality multiplies a computed collision count by the number of candidate primes,
then compares it with its supplied threshold. All multiplications, branches and flag updates
are ordinary charged instructions. No predicate is executed by an oracle.

## Main definitions

* `CollisionTest.program`: test all three inequalities.

## Main results

* `CollisionTest.exec`: the exact acceptance flag in at most thirteen instructions.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.CollisionTest

open Cslib.WordRAM

/-- Number of candidate primes. -/
abbrev card : Fin 64 := 42
/-- Threshold for one of the three sets. -/
def threshold (j : Fin 3) : Fin 64 := ⟨44 + j.val, by omega⟩
/-- Constant zero. -/
abbrev zero : Fin 64 := 52
/-- Collision count times the number of candidate primes. -/
abbrev scaled : Fin 64 := 57
/-- Acceptance flag. -/
abbrev good : Fin 64 := 58

/-- One charged multiplication and comparison, retaining a previously false flag. -/
def compare (j : Fin 3) : Code .standard 64 :=
  let value := CountCall.result j
  let cutoff := threshold j
  ram[ scaled ← value * card;
    if cutoff < scaled then [ good ← zero ] else [ good ← good ] ]

/-- Initialize a true flag and test all three supplied collision counts. -/
def program : Code .standard 64 :=
  .seq (ram[ good ← #1 ]) (.seq (compare 0) (.seq (compare 1) (compare 2)))

private theorem exec_compare {w : ℕ} (j : Fin 3) (x : Data 64)
    (hz : x.regs zero = 0)
    (hfit : Fits w (x.regs (CountCall.result j) * x.regs card)) :
    ∃ y, ExecWithin w (compare j) x y 4 ∧
      y.regs good = (if x.regs (CountCall.result j) * x.regs card ≤ x.regs (threshold j)
        then x.regs good else 0) ∧ y.mem = x.mem ∧
      ∀ i, i ≠ scaled → i ≠ good → y.regs i = x.regs i := by
  let product := x.regs (CountCall.result j) * x.regs card
  let y := (x.set scaled product).set good
    (if x.regs (threshold j) < product then 0 else x.regs good)
  have hm : ExecWithin w
      (.op (.bin .mul scaled (CountCall.result j) card)) x (x.set scaled product) 1 :=
    ExecWithin.bin hfit
  have hcut : (x.set scaled product).regs (threshold j) = x.regs (threshold j) := by
    fin_cases j <;> rfl
  have hz' : (x.set scaled product).regs zero = 0 := by
    simpa +decide [zero, scaled] using hz
  have hg' : (x.set scaled product).regs good = x.regs good := rfl
  have hscaled : (x.set scaled product).regs scaled = product := rfl
  have he : ExecWithin w (compare j) x y 4 := by
    by_cases hlt : x.regs (threshold j) < product
    · have hc : (Cond.lt (threshold j) scaled).Holds (x.set scaled product) := by
        simpa only [Cond.holds_lt, hcut, hscaled] using hlt
      have hb := ExecWithin.branch_pos (B := .standard) (w := w) (pos := ram[ good ← zero ])
        (neg := ram[ good ← good ]) hc
        (ExecWithin.copy (x := x.set scaled product) (d := good) (s := zero))
      have hb' : ExecWithin (B := .standard) w
          (.branch (.lt (threshold j) scaled) (ram[ good ← zero ]) (ram[ good ← good ]))
          (x.set scaled product) y 2 := by
        simpa only [y, hlt, ↓reduceIte, hz'] using hb
      exact (hm.seq hb').mono (by decide)
    · have hc : ¬(Cond.lt (threshold j) scaled).Holds (x.set scaled product) := by
        simpa only [Cond.holds_lt, hcut, hscaled] using hlt
      have hb := ExecWithin.branch_neg (B := .standard) (w := w) (pos := ram[ good ← zero ])
        (neg := ram[ good ← good ]) hc
        (ExecWithin.copy (x := x.set scaled product) (d := good) (s := good))
      have hb' : ExecWithin (B := .standard) w
          (.branch (.lt (threshold j) scaled) (ram[ good ← zero ]) (ram[ good ← good ]))
          (x.set scaled product) y 3 := by
        simpa only [y, hlt, ↓reduceIte, hg'] using hb
      exact hm.seq hb'
  refine ⟨y, he, ?_, rfl, ?_⟩
  · change (if x.regs (threshold j) < product then 0 else x.regs good) =
      if product ≤ x.regs (threshold j) then x.regs good else 0
    by_cases hlt : x.regs (threshold j) < product
    · have hnot : ¬product ≤ x.regs (threshold j) := by omega
      simp only [hlt, hnot, ↓reduceIte]
    · have hle : product ≤ x.regs (threshold j) := by omega
      simp only [hlt, hle, ↓reduceIte]
  · intro i hs hg
    simp only [y, Data.set_regs, Function.update_of_ne hg, Function.update_of_ne hs]

/-- Test all three inequalities with a shared acceptance flag. The only written registers
are `scaled` and `good`; memory and every other caller register are unchanged. -/
theorem exec {w : ℕ} (x : Data 64) (h1 : Fits w 1) (hz : x.regs zero = 0)
    (hfit : ∀ j, Fits w (x.regs (CountCall.result j) * x.regs card)) :
    ∃ y, ExecWithin w program x y 13 ∧
      y.regs good = (if
        x.regs (CountCall.result 0) * x.regs card ≤ x.regs (threshold 0) ∧
        x.regs (CountCall.result 1) * x.regs card ≤ x.regs (threshold 1) ∧
        x.regs (CountCall.result 2) * x.regs card ≤ x.regs (threshold 2) then 1 else 0) ∧
      y.mem = x.mem ∧ ∀ i, i ≠ scaled → i ≠ good → y.regs i = x.regs i := by
  let R (y : Data 64) : Prop := y.mem = x.mem ∧
    ∀ i, i ≠ scaled → i ≠ good → y.regs i = x.regs i
  have hcall (j : Fin 3) (y : Data 64) (hy : R y) :
      ∃ z, ExecWithin w (compare j) y z 4 ∧ R z ∧
        z.regs good = (if x.regs (CountCall.result j) * x.regs card ≤ x.regs (threshold j)
          then y.regs good else 0) := by
    obtain ⟨hm, hr⟩ := hy
    have hvalue : y.regs (CountCall.result j) = x.regs (CountCall.result j) :=
      hr _ (by fin_cases j <;> decide) (by fin_cases j <;> decide)
    have hcard : y.regs card = x.regs card := hr _ (by decide) (by decide)
    have hcut : y.regs (threshold j) = x.regs (threshold j) :=
      hr _ (by fin_cases j <;> decide) (by fin_cases j <;> decide)
    obtain ⟨z, he, hf, hzm, hzr⟩ := exec_compare j y
      ((hr _ (by decide) (by decide)).trans hz)
      (by simpa only [hvalue, hcard] using hfit j)
    exact ⟨z, he, ⟨hzm.trans hm, fun i hs hg => (hzr i hs hg).trans (hr i hs hg)⟩,
      by simpa only [hvalue, hcard, hcut] using hf⟩
  let x₀ := x.set good 1
  have hx₀ : R x₀ := ⟨rfl, fun i _ hg => Function.update_of_ne hg _ _⟩
  obtain ⟨a, ha, hRa, hfa⟩ := hcall 0 x₀ hx₀
  obtain ⟨b, hb, hRb, hfb⟩ := hcall 1 a hRa
  obtain ⟨c, hc, hRc, hfc⟩ := hcall 2 b hRb
  refine ⟨c, ?_, ?_, hRc⟩
  · exact (ExecWithin.const h1).seq (ha.seq (hb.seq hc))
  · rw [hfc, hfb, hfa]
    change (if _ then (if _ then (if _ then 1 else 0) else 0) else 0) = _
    split_ifs <;> omega

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.CollisionTest

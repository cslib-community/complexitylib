/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Keep
public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Trial
public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Frame
import all Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Minimum

/-!
# Native minimum and candidate-advance steps

The actual strict-minimum update realizes the prefix-minimum invariant. The actual successor
code advances the candidate and recomputes its square in two charged instructions. The
counter must separately establish the value supplied to the minimum update; these local
rules do not assume a complete modular-counting endpoint.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

open Cslib.WordRAM

/-- Advance to the next candidate and compute its actual square. All other registers and
all memory cells survive. Numerical admission is for the new square itself. -/
theorem exec_advance {w : ℕ} (x : Data 160) (ho : x.regs Reg.one = 1)
    (hfit : Fits w ((x.regs Reg.cursor + 1) * (x.regs Reg.cursor + 1))) :
    ∃ y, ExecWithin w advance x y 2 ∧ y.regs Reg.cursor = x.regs Reg.cursor + 1 ∧
      y.regs Reg.square = (x.regs Reg.cursor + 1) * (x.regs Reg.cursor + 1) ∧
      y.mem = x.mem ∧ ∀ i, i ≠ Reg.cursor → i ≠ Reg.square → y.regs i = x.regs i := by
  have hinc : Fits w (x.regs Reg.cursor + 1) := hfit.of_le (by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left (x.regs Reg.cursor + 1) (show 1 ≤ x.regs Reg.cursor + 1 by omega))
  let y := (x.set Reg.cursor (x.regs Reg.cursor + 1)).set Reg.square
    ((x.regs Reg.cursor + 1) * (x.regs Reg.cursor + 1))
  have he : ExecWithin w advance x y 2 := by
    ram_eval [advance, y, ho, hfit, hinc, Reg.cursor, Reg.square, Reg.one, Fin.mk.injEq]
  refine ⟨y, he, ?_, ?_, rfl, ?_⟩
  · simp +decide [y, Reg.cursor, Reg.square]
  · simp +decide [y, Reg.cursor, Reg.square]
  · intro i hc hs
    simp only [y, Data.set_regs, Function.update_of_ne hs, Function.update_of_ne hc]

private theorem exec_keep_bestBefore {w D : ℕ} (score : ℕ → ℕ) (x : Data 160)
    (hz : x.regs Reg.zero = 0) (ho : x.regs Reg.one = 1)
    (hbest : BestBefore D score (x.regs Reg.cursor) (x.regs Reg.best)
      (x.regs Reg.bestCount) (x.regs Reg.found))
    (hk : x.regs Reg.cursor ∈ Nat.sqrtPrimeWindow D)
    (hscore : x.regs Reg.countResult = score (x.regs Reg.cursor)) :
    ∃ y, ExecWithin w keep x y 5 ∧
      BestBefore D score (x.regs Reg.cursor + 1) (y.regs Reg.best)
        (y.regs Reg.bestCount) (y.regs Reg.found) ∧ y.mem = x.mem ∧
      ∀ i, 131 ≤ i.val → y.regs i = x.regs i := by
  have hf : x.regs Reg.found = 0 ∨ x.regs Reg.found = 1 :=
    hbest.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  obtain ⟨y, he, hb, hv, hf, hm, hr⟩ := exec_keep x hz ho hf
  have hnext := bestBefore_take hbest hk
  rw [hscore] at hb hv
  refine ⟨y, he, ?_, hm, ?_⟩
  · rw [hb, hv, hf]
    exact hnext
  · intro i hi
    apply hr i
    all_goals intro h; subst i; simp [Reg.best, Reg.bestCount, Reg.found] at hi

private theorem exec_candidate_bestBefore {w D T : ℕ} (counter : Code .standard 128)
    (score : ℕ → ℕ) (Source : (ℕ → ℕ) → Prop) (x : Data 160)
    (hz : x.regs Reg.zero = 0) (ho : x.regs Reg.one = 1)
    (hD : x.regs Reg.window = D) (hp : 2 ≤ x.regs Reg.cursor)
    (hupper : x.regs Reg.cursor * x.regs Reg.cursor < D)
    (hfour : x.regs Reg.fourSquare = 4 * (x.regs Reg.cursor * x.regs Reg.cursor))
    (hfit : Fits w (x.regs Reg.cursor + 2)) (hSource : Source x.mem)
    (hbest : BestBefore D score (x.regs Reg.cursor) (x.regs Reg.best)
      (x.regs Reg.bestCount) (x.regs Reg.found))
    (hcount : ∀ z, Source z.mem → (∀ i, 128 ≤ i.val → z.regs i = x.regs i) →
      x.regs Reg.cursor ∈ Nat.sqrtPrimeWindow D →
      ∃ a, ExecWithin w (count counter) z a T ∧
        a.regs Reg.countResult = score (x.regs Reg.cursor) ∧ Source a.mem) :
    ∃ y, ExecWithin w (candidate counter) x y (T + 7 * x.regs Reg.cursor + 15) ∧
      BestBefore D score (x.regs Reg.cursor + 1) (y.regs Reg.best)
        (y.regs Reg.bestCount) (y.regs Reg.found) ∧ Source y.mem ∧
      ∀ i, 131 ≤ i.val → y.regs i = x.regs i := by
  by_cases hlo : 4 * (x.regs Reg.cursor * x.regs Reg.cursor) < D
  · have hnot : x.regs Reg.cursor ∉ Nat.sqrtPrimeWindow D := by
      intro hw
      have hlow := (Nat.mem_sqrtPrimeWindow_iff_sq.1 hw).2.1
      simp only [pow_two] at hlow
      omega
    refine ⟨x, ?_, bestBefore_skip hbest hnot, hSource, fun _ _ => rfl⟩
    exact (ExecWithin.branch_pos
      (by simpa only [Cond.holds_lt, hfour, hD] using hlo) (exec_nop x)).mono (by omega)
  · have hneg : ¬(Cond.lt Reg.fourSquare Reg.window).Holds x := by
      simpa only [Cond.holds_lt, hfour, hD] using hlo
    obtain ⟨z, ht, hflag, hm, hr⟩ := exec_trial x hp hfit
    have hzSource : Source z.mem := by simpa only [hm] using hSource
    have hzOne : z.regs Reg.one = 1 := (hr Reg.one (by decide)).trans ho
    have hmeta : ∀ i, 128 ≤ i.val → z.regs i = x.regs i :=
      fun i hi => hr i (by omega)
    by_cases hprime : (x.regs Reg.cursor).Prime
    · have hwindow : x.regs Reg.cursor ∈ Nat.sqrtPrimeWindow D :=
        Nat.mem_sqrtPrimeWindow_iff_sq.2 ⟨hprime,
          by simpa only [pow_two] using Nat.le_of_not_gt hlo,
          by simpa only [pow_two] using hupper⟩
      have hbit : (Cond.eq Reg.trialFlag Reg.one).Holds z := by
        simp only [Cond.holds_eq, hflag, hprime, ↓reduceIte, hzOne]
      obtain ⟨a, hc, hscore, haSource⟩ := hcount z hzSource hmeta hwindow
      have hameta : ∀ i, 128 ≤ i.val → a.regs i = x.regs i := by
        intro i hi
        exact (hc.regs_eq (count_preserves counter i hi)).trans (hmeta i hi)
      have haBest : BestBefore D score (a.regs Reg.cursor) (a.regs Reg.best)
          (a.regs Reg.bestCount) (a.regs Reg.found) := by
        simpa only [hameta Reg.cursor (by decide), hameta Reg.best (by decide),
          hameta Reg.bestCount (by decide), hameta Reg.found (by decide)] using hbest
      obtain ⟨y, hy, hybest, hym, hyr⟩ := exec_keep_bestBefore score a
        ((hameta Reg.zero (by decide)).trans hz) ((hameta Reg.one (by decide)).trans ho)
        haBest (by simpa only [hameta Reg.cursor (by decide)] using hwindow)
        (by simpa only [hameta Reg.cursor (by decide)] using hscore)
      refine ⟨y, ?_, ?_, ?_, ?_⟩
      · exact (ExecWithin.branch_neg hneg
          (ht.seq (ExecWithin.branch_pos hbit (hc.seq hy)))).mono (by omega)
      · simpa only [hameta Reg.cursor (by decide)] using hybest
      · simpa only [hym] using haSource
      · intro i hi
        exact (hyr i hi).trans (hameta i (by omega))
    · have hbit : ¬(Cond.eq Reg.trialFlag Reg.one).Holds z := by
        simp only [Cond.holds_eq, hflag, hprime, ↓reduceIte, hzOne, zero_ne_one, not_false_eq_true]
      have hnot : x.regs Reg.cursor ∉ Nat.sqrtPrimeWindow D :=
        fun hw => hprime (Nat.mem_sqrtPrimeWindow_iff_sq.1 hw).1
      refine ⟨z, ?_, ?_, hzSource, ?_⟩
      · exact (ExecWithin.branch_neg hneg
          (ht.seq (ExecWithin.branch_neg hbit (exec_nop z)))).mono (by omega)
      · simpa only [hmeta Reg.best (by decide), hmeta Reg.bestCount (by decide),
          hmeta Reg.found (by decide)] using bestBefore_skip hbest hnot
      · intro i hi
        exact hr i (by omega)

end Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

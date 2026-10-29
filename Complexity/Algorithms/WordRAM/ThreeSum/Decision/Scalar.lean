/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Program

/-!
# Charged polynomial workspace reservation

The outer controller computes its preprocessing word envelope by actual multiplication and
decrement instructions. The exponent is fixed with the input-magnitude parameter, not supplied
by an oracle. All other controls and every memory cell are preserved by the reservation loop.

## Main results

* `exec_power`: the complete native exponentiation loop and its charged frame.

These finite native reservation proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM

/-- Native exponentiation from the actual loop registers, with all multiplication work charged. -/
theorem exec_power {w B E : ℕ} (x : Data 16)
    (hB : 1 ≤ B) (hs : x.regs scale = B) (hc : x.regs remaining = E)
    (hv : x.regs envelope = 1) (ho : x.regs one = 1) (hz : x.regs zero = 0)
    (hfit : Fits w (B ^ E)) (hcount : Fits w E) :
    ∃ y, ExecWithin w power x y (4 * E + 2) ∧
      y.regs envelope = B ^ E ∧ y.regs remaining = 0 ∧
      (∀ i, i ≠ envelope → i ≠ remaining → y.regs i = x.regs i) ∧ y.mem = x.mem := by
  let I (y : Data 16) : Prop := y.regs remaining ≤ E ∧
    y.regs envelope = B ^ (E - y.regs remaining) ∧
    (∀ i, i ≠ envelope → i ≠ remaining → y.regs i = x.regs i) ∧ y.mem = x.mem
  have hbody (y : Data 16) (hy : I y) (hlt : (Cond.lt zero remaining).Holds y) :
      ∃ z, ExecWithin w powerBody y z 2 ∧ I z ∧ z.regs remaining < y.regs remaining := by
    obtain ⟨hyc, hyv, hyr, hym⟩ := hy
    have hyz : y.regs zero = 0 := (hyr _ (by decide) (by decide)).trans hz
    have hyo : y.regs one = 1 := (hyr _ (by decide) (by decide)).trans ho
    have hys : y.regs scale = B := (hyr _ (by decide) (by decide)).trans hs
    have hcpos : 0 < y.regs remaining := by simpa only [Cond.holds_lt, hyz] using hlt
    have hexp : E - y.regs remaining + 1 = E - (y.regs remaining - 1) := by omega
    have hmul : Fits w (B ^ (E - y.regs remaining) * B) := by
      rw [← pow_succ]
      exact hfit.of_le (Nat.pow_le_pow_right hB (by omega))
    have hdec : Fits w (y.regs remaining - 1) := hcount.of_le (by omega)
    let z := y.set envelope (B ^ (E - y.regs remaining) * B)
      |>.set remaining (y.regs remaining - 1)
    have he : ExecWithin w powerBody y z 2 := by
      ram_eval [powerBody, z, hyv, hys, hyo, hmul, hdec,
        envelope, scale, remaining, one, Fin.mk.injEq]
    refine ⟨z, he, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa +decide [z, envelope, remaining] using (show y.regs remaining - 1 ≤ E by omega)
    · simp +decide only [z, Data.set_regs, Function.update_apply, envelope, remaining,
        ↓reduceIte]
      rw [← pow_succ, hexp]
    · intro i hie hir
      exact (by simp only [z, Data.set_regs, Function.update_of_ne hir,
        Function.update_of_ne hie] : z.regs i = y.regs i).trans (hyr i hie hir)
    · exact hym
    · have hlt : y.regs remaining - 1 < y.regs remaining := by omega
      simpa +decide [z, envelope, remaining] using hlt
  have hx : I x := ⟨by omega, by simp only [hc, hv, Nat.sub_self, pow_zero],
    fun _ _ _ => rfl, rfl⟩
  obtain ⟨y, he, hy, hstop⟩ := ExecWithin.loop_invariant I
    (fun y => y.regs remaining) hbody hx
  obtain ⟨hyc, hyv, hyr, hym⟩ := hy
  have hyz : y.regs zero = 0 := (hyr _ (by decide) (by decide)).trans hz
  have hy0 : y.regs remaining = 0 := by
    change ¬y.regs zero < y.regs remaining at hstop
    omega
  refine ⟨y, ?_, ?_, hy0, hyr, hym⟩
  · simpa only [power, hc, Nat.reduceAdd, Nat.mul_comm] using he
  · simpa only [hy0, Nat.sub_zero] using hyv

end Cslib.Algorithms.WordRAM.ThreeSum.Decision

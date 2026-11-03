/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Structured

/-!
# Static register-bank copies on the word RAM

`copyBank` copies a finite sequence of source registers into an injective destination bank using
only native register-copy instructions, with a terminal self-copy on `idle` supplying the
zero-length code case without inspecting the word width or requiring a positive-width constant.

## Main definitions

* `copyBank`: copy `k` source registers into `k` destination registers, ending with an `idle`
  self-copy.

## Main results

* `copyBank_not_readsWidth`: copying a finite register bank does not inspect the word width.
* `copyBank_exec`: copying `k` disjoint source registers into an injective destination bank takes
  `k + 1` instructions, preserving memory and all registers outside the destination bank.
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B : Basis} {r k : ℕ}

/-- Native register copies need no word-size or arithmetic side condition. -/
def copyBank : {k : ℕ} → (Fin k → Fin r) → (Fin k → Fin r) → Fin r → Code B r
  | 0, _, _, idle => .op (.copy idle idle)
  | n + 1, src, dst, idle => .seq (.op (.copy (dst 0) (src 0)))
      (copyBank (fun i : Fin n => src i.succ) (fun i => dst i.succ) idle)

/-- Copying a finite bank does not inspect the word width. -/
theorem copyBank_not_readsWidth (src dst : Fin k → Fin r) (idle : Fin r) :
    ¬(copyBank (B := B) src dst idle).ReadsWidth := by
  induction k with
  | zero => simp [copyBank, Code.ReadsWidth, Op.ReadsWidth]
  | succ n ih => simp [copyBank, Code.ReadsWidth, Op.ReadsWidth, ih]

/-- Copy disjoint source words into an injective destination bank, leaving the entire memory and
all other registers unchanged. A neutral copy supplies the zero-length code case. -/
theorem copyBank_exec (src dst : Fin k → Fin r) (idle : Fin r)
    (hi : Function.Injective dst) (hd : ∀ i j, src i ≠ dst j) (w : ℕ) (x : Data r) :
    ∃ y, ExecWithin w (copyBank (B := B) src dst idle) x y (k + 1) ∧
      y.mem = x.mem ∧ (∀ i, y.regs (dst i) = x.regs (src i)) ∧
      ∀ j, (∀ i, dst i ≠ j) → y.regs j = x.regs j := by
  induction k generalizing x with
  | zero =>
    have he : ExecWithin (B := B) w (.op (.copy idle idle)) x x 1 := by
      convert (ExecWithin.copy (B := B) (w := w) (d := idle) (s := idle) (x := x)) using 1
      apply Data.ext <;> simp [Data.set]
    exact ⟨x, he, rfl, fun i => Fin.elim0 i, fun _ _ => rfl⟩
  | succ n ih =>
    let a := x.set (dst 0) (x.regs (src 0))
    obtain ⟨y, hy, hm, hout, hframe⟩ := ih
      (fun i : Fin n => src i.succ) (fun i => dst i.succ)
      (fun i j h => Fin.succ_injective _ (hi h))
      (fun i j => hd i.succ j.succ) a
    have he : ExecWithin (B := B) w (.op (.copy (dst 0) (src 0))) x a 1 :=
      ExecWithin.copy
    refine ⟨y, ?_, hm, ?_, ?_⟩
    · simpa only [copyBank, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using he.seq hy
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [hframe (dst 0) (fun j h => Fin.succ_ne_zero _ (hi h))]
        simp [a, Data.set]
      · rw [hout]
        exact Function.update_of_ne (hd j.succ 0) _ _
    · intro j hj
      rw [hframe j (fun i => hj i.succ)]
      exact Function.update_of_ne (hj 0).symm _ _

end Cslib.WordRAM

end

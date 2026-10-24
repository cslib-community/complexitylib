/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Multiword.Digits

/-!
# Shared workspace for multiword operations

Register zero stores an arithmetic total, register one a carry, register two the half-word
radix, and register three a preserved zero. All operand digits lie outside this workspace.
Multiplication, transfers, bitwise operations and shifts share this layout.

## Main definitions

* `Workspace.total`, `Workspace.carry`, `Workspace.base`, `Workspace.zero`: the four reserved
  workspace registers.
* `Workspace.IsDigit`: a register outside the four reserved registers.
* `Workspace.Frame`: memory and registers outside destinations and arithmetic scratch are kept.
* `Workspace.setup`, `Workspace.setupResult`: initialize the radix and zero in six checked
  instructions, and the resulting machine state.

## Main results

* `Workspace.exec_setup`: exact initialization at every physical width at least two.
* `Workspace.setup_digit`: initialization leaves operand digits unchanged.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Workspace

variable {r : ℕ}

/-- Arithmetic total and partial-sum workspace. -/
abbrev total : Fin (r + 4) := ⟨0, by omega⟩
/-- Carry workspace. -/
abbrev carry : Fin (r + 4) := ⟨1, by omega⟩
/-- Half-word radix. -/
abbrev base : Fin (r + 4) := ⟨2, by omega⟩
/-- A preserved zero, used for padding and shifts. -/
abbrev zero : Fin (r + 4) := ⟨3, by omega⟩

/-- Registers outside the four reserved workspace registers. -/
def IsDigit (i : Fin (r + 4)) : Prop := 4 ≤ i.val

/-- Digit registers are disjoint from the four reserved workspace registers. -/
theorem digit_ne {i : Fin (r + 4)} (hi : IsDigit i) :
    i ≠ total ∧ i ≠ carry ∧ i ≠ base ∧ i ≠ zero := by
  dsimp [IsDigit] at hi
  simp only [ne_eq, Fin.ext_iff, total, carry, base, zero]
  omega

/-- A routine changes only its destination digits and the total and carry workspace. -/
def Frame (x y : Data (r + 4)) (ds : List (Fin (r + 4))) : Prop :=
  y.mem = x.mem ∧ ∀ i, i ∉ ds → i ≠ total → i ≠ carry → y.regs i = x.regs i

/-- Enlarging the destination set weakens the preservation requirement. -/
theorem frame_mono {x y : Data (r + 4)} {ds es : List (Fin (r + 4))}
    (h : Frame x y ds) (hsub : ds ⊆ es) : Frame x y es :=
  ⟨h.1, fun i hi ht hc => h.2 i (fun hm => hi (hsub hm)) ht hc⟩

/-- Two routines with the same frame compose. -/
theorem frame_trans {x y z : Data (r + 4)} {ds : List (Fin (r + 4))}
    (h : Frame x y ds) (h' : Frame y z ds) : Frame x z ds :=
  ⟨h'.1.trans h.1, fun i hi ht hc => (h'.2 i hi ht hc).trans (h.2 i hi ht hc)⟩

/-- Compute the half-word radix and a preserved zero in six standard instructions. -/
def setup : Code .standard (r + 4) := ram[
  total ← width%;
  carry ← #2;
  base ← total / carry;
  carry ← #1;
  base ← carry <<< base;
  zero ← #0 ]

/-- Exact workspace contents after initialization. -/
def setupResult (w : ℕ) (x : Data (r + 4)) : Data (r + 4) :=
  let y := (((x.set total w).set carry 2).set base (w / 2)).set carry 1
  (y.set base (radix w)).set zero 0

/-- Initialization executes in exactly six instructions for every width at least two. -/
theorem exec_setup {w : ℕ} (hw : 2 ≤ w) (x : Data (r + 4)) :
    Exec w setup x (setupResult w x) 6 := by
  have h2 : Fits w 2 := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hw)
  have hhalf := (fits_self w).of_le (Nat.div_le_self w 2)
  have h1 := fits_one (w := w) (by omega)
  have hβ := radix_fits hw
  have hshift : 1 <<< (w / 2) = radix w := by rw [Nat.shiftLeft_eq, one_mul]; rfl
  ram_eval [setup, setupResult, total, carry, base, zero, Fin.mk.injEq,
    h2, hhalf, h1, hβ, hshift]

/-- Initialization preserves every register outside the reserved workspace. -/
theorem setup_digit (w : ℕ) (x : Data (r + 4)) {i : Fin (r + 4)}
    (hi : IsDigit i) : (setupResult w x).regs i = x.regs i := by
  obtain ⟨ht, hc, hb, hz⟩ := digit_ne hi
  simp only [setupResult, Data.set_regs, Function.update_apply, ht, hc, hb, hz, ↓reduceIte]

end Cslib.WordRAM.Multiword.Workspace

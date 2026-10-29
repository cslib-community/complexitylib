/-
Copyright (c) 2026 Erik Demaine, Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Machines.Turing.MultiTape.Configuration
import Mathlib.Data.List.GetD

/-!
# Raw two-stack work tapes

A work tape is stored as its current cell and two lists, nearest cell first. Blanks are retained:
moving beyond the stored interval extends it by one blank cell. Thus storage records the interval
visited by the head, independently of the number of times the machine revisits cells.
The relative read and representation proofs adapt the `BiTape` API of Bolton Bailey and
Samuel Schlesinger to raw lists.

## Main definitions

* `Turing.MultiTapeTM.ToTM2.RawTape`: the current cell and the raw left and right stacks.
* `Turing.MultiTapeTM.ToTM2.RawTape.step`: native optional writing followed by head movement.
* `Turing.MultiTapeTM.ToTM2.RawTape.Represents`: correspondence with an integer-indexed native tape.

## Main results

* `Turing.MultiTapeTM.ToTM2.RawTape.Represents.step`: preservation of native tape semantics.
-/

public section

namespace Turing.MultiTapeTM.ToTM2

/-- A work tape with raw stacks, ordered from the head outwards. Trailing blanks are retained. -/
@[ext] structure RawTape (Symbol : Type*) where
  /-- The cell under the head. -/
  head : Option Symbol
  /-- Cells strictly to the left, nearest first. -/
  left : List (Option Symbol)
  /-- Cells strictly to the right, nearest first. -/
  right : List (Option Symbol)
  deriving DecidableEq

namespace RawTape

variable {Symbol : Type*}

/-- A blank tape, initially storing just the cell at its head. -/
@[expose] def init : RawTape Symbol := ⟨none, [], []⟩

instance : Inhabited (RawTape Symbol) := ⟨init⟩

/-- Perform an optional native write: `none` preserves the cell and `some none` erases it. -/
@[expose] def write (t : RawTape Symbol) (w : Option (Option Symbol)) : RawTape Symbol :=
  { t with head := w.getD t.head }

@[simp] theorem write_none (t : RawTape Symbol) : t.write none = t := rfl

@[simp] theorem head_write (t : RawTape Symbol) (w : Option (Option Symbol)) :
    (t.write w).head = w.getD t.head := rfl

/-- Move left, extending the stored interval by a blank when the left stack is empty. -/
@[expose] def moveLeft (t : RawTape Symbol) : RawTape Symbol :=
  ⟨t.left.headD none, t.left.tail, t.head :: t.right⟩

/-- Move right, extending the stored interval by a blank when the right stack is empty. -/
@[expose] def moveRight (t : RawTape Symbol) : RawTape Symbol :=
  ⟨t.right.headD none, t.head :: t.left, t.right.tail⟩

/-- Apply a native work-tape action, writing before moving. -/
@[expose] def step (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) : RawTape Symbol :=
  match a.2 with
  | .neg => (t.write a.1).moveLeft
  | .zero => t.write a.1
  | .pos => (t.write a.1).moveRight

/-- Read at an integer offset relative to the head; unstored cells are blank. -/
def read (t : RawTape Symbol) : ℤ → Option Symbol
  | .ofNat 0 => t.head
  | .ofNat (n + 1) => t.right.getD n none
  | .negSucc n => t.left.getD n none

/-- The raw tape agrees with a native tape whose head is at `pos`. -/
def Represents (t : RawTape Symbol) (native : ℤ → Option Symbol) (pos : ℤ) : Prop :=
  ∀ z, t.read z = native (pos + z)

@[simp] theorem read_zero (t : RawTape Symbol) : t.read 0 = t.head := by simp [read]

@[simp] theorem read_init (z : ℤ) : (init : RawTape Symbol).read z = none := by
  cases z with
  | ofNat n => cases n <;> simp [read, init]
  | negSucc n => simp [read, init]

theorem read_write (t : RawTape Symbol) (w : Option (Option Symbol)) (z : ℤ) :
    (t.write w).read z = if z = 0 then w.getD t.head else t.read z := by
  cases z with
  | ofNat n => cases n <;> simp [read, write, add_eq_zero_iff_eq_neg]
  | negSucc n => simp [read, write]

theorem read_moveLeft (t : RawTape Symbol) (z : ℤ) :
    t.moveLeft.read z = t.read (z - 1) := by
  rcases t with ⟨h, l, r⟩
  cases z with
  | ofNat n =>
    cases n with
    | zero => cases l <;> rfl
    | succ n =>
      have he : (Int.ofNat (n + 1) : ℤ) - 1 = Int.ofNat n := by
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [he]
      cases n <;> rfl
  | negSucc n =>
    have he : Int.negSucc n - 1 = Int.negSucc (n + 1) := by omega
    rw [he]
    cases l <;> rfl

theorem read_moveRight (t : RawTape Symbol) (z : ℤ) :
    t.moveRight.read z = t.read (z + 1) := by
  rcases t with ⟨h, l, r⟩
  cases z with
  | ofNat n =>
    have he : (Int.ofNat n : ℤ) + 1 = Int.ofNat (n + 1) := by
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [he]
    cases n <;> cases r <;> rfl
  | negSucc n =>
    cases n with
    | zero => rfl
    | succ n =>
      have he : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
      rw [he]
      rfl

theorem Represents.head {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) : t.head = native pos := by
  simpa using h 0

theorem Represents.init : (init : RawTape Symbol).Represents (fun _ => none) 0 := by
  intro z
  exact read_init z

theorem Represents.write {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) (w : Option (Option Symbol)) :
    (t.write w).Represents (match w with
      | none => native
      | some s => Function.update native pos s) pos := by
  intro z
  rw [read_write]
  cases w with
  | none =>
    by_cases hz : z = 0
    · subst z; simpa using h 0
    · simpa [hz] using h z
  | some s =>
    by_cases hz : z = 0
    · subst z; simp
    · simpa [hz, show pos + z ≠ pos by omega] using h z

theorem Represents.moveLeft {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) : t.moveLeft.Represents native (pos - 1) := by
  intro z
  rw [read_moveLeft, h]
  congr 1
  omega

theorem Represents.moveRight {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) : t.moveRight.Represents native (pos + 1) := by
  intro z
  rw [read_moveRight, h]
  congr 1
  omega

/-- Raw execution preserves a native optional-write-and-move action, including erasing cells. -/
theorem Represents.step {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) (a : Option (Option Symbol) × SignType) :
    (t.step a).Represents (match a.1 with
      | none => native
      | some s => Function.update native pos s) (pos + a.2) := by
  rcases a with ⟨w, d⟩
  cases w <;> cases d
  · simpa only [RawTape.step, SignType.cast, add_zero] using h.write none
  · simpa only [RawTape.step, SignType.cast, sub_eq_add_neg] using (h.write none).moveLeft
  · simpa only [RawTape.step, SignType.cast] using (h.write none).moveRight
  · simpa only [RawTape.step, SignType.cast, add_zero] using h.write (some _)
  · simpa only [RawTape.step, SignType.cast, sub_eq_add_neg] using (h.write (some _)).moveLeft
  · simpa only [RawTape.step, SignType.cast] using (h.write (some _)).moveRight

@[simp] theorem left_write (t : RawTape Symbol) (w : Option (Option Symbol)) :
    (t.write w).left = t.left := rfl

@[simp] theorem right_write (t : RawTape Symbol) (w : Option (Option Symbol)) :
    (t.write w).right = t.right := rfl

@[simp] theorem length_left_moveLeft (t : RawTape Symbol) :
    t.moveLeft.left.length = t.left.length - 1 := by simp [moveLeft]

@[simp] theorem length_right_moveLeft (t : RawTape Symbol) :
    t.moveLeft.right.length = t.right.length + 1 := rfl

@[simp] theorem length_left_moveRight (t : RawTape Symbol) :
    t.moveRight.left.length = t.left.length + 1 := rfl

@[simp] theorem length_right_moveRight (t : RawTape Symbol) :
    t.moveRight.right.length = t.right.length - 1 := by simp [moveRight]

/-- The exact left-stack length after an action. -/
theorem length_left_step (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) :
    (t.step a).left.length = match a.2 with
      | .neg => t.left.length - 1
      | .zero => t.left.length
      | .pos => t.left.length + 1 := by
  rcases a with ⟨w, d⟩
  cases d <;> simp only [step, length_left_moveLeft, length_left_moveRight, left_write]

/-- The exact right-stack length after an action. -/
theorem length_right_step (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) :
    (t.step a).right.length = match a.2 with
      | .neg => t.right.length + 1
      | .zero => t.right.length
      | .pos => t.right.length - 1 := by
  rcases a with ⟨w, d⟩
  cases d <;> simp only [step, length_right_moveLeft, length_right_moveRight, right_write]

/-- The number of stored cells, including the current cell and stored blanks. -/
@[expose] def span (t : RawTape Symbol) : ℕ := t.left.length + t.right.length + 1

@[simp] theorem span_init : (init : RawTape Symbol).span = 1 := rfl

@[simp] theorem span_write (t : RawTape Symbol) (w : Option (Option Symbol)) :
    (t.write w).span = t.span := rfl

/-- Storage grows only when the head moves beyond the previously stored interval. -/
theorem span_step (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) :
    (t.step a).span = t.span +
      if (a.2 = .neg ∧ t.left = []) ∨ (a.2 = .pos ∧ t.right = []) then 1 else 0 := by
  rcases a with ⟨w, d⟩
  cases d <;> cases hl : t.left <;> cases hr : t.right <;>
    simp [span, length_left_step, length_right_step, hl, hr,
      Nat.add_comm, Nat.add_left_comm]

theorem span_step_le (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) :
    (t.step a).span ≤ t.span + 1 := by
  rw [span_step]
  split_ifs <;> omega

end RawTape

end Turing.MultiTapeTM.ToTM2

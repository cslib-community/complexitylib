/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Machines.Turing.MultiTape.Configuration

/-!
# A bounded input zipper for the TM2 compiler

The left stack is reversed and the right stack includes the symbol under the head. A separate
flag distinguishes the left boundary from the first input symbol. An empty right stack with
the flag unset represents the right boundary, including the initial position on empty input.

## Main definitions

* `Turing.MultiTapeTM.ToTM2.Input`: the two stacks and the left-boundary flag.
* `Turing.MultiTapeTM.ToTM2.Input.Represents`: agreement with a native input and head position.

## Main results

* `Turing.MultiTapeTM.ToTM2.Input.represents_init`: initialization represents native position one.
* `Turing.MultiTapeTM.ToTM2.Input.Represents.read_eq_inputSymbol`: reads agree with native reads.
* `Turing.MultiTapeTM.ToTM2.Input.Represents.move`: moves agree, including boundary clamping.
-/

public section

namespace Turing.MultiTapeTM.ToTM2

/-- A read-only input tape represented by two stacks and a left-boundary flag. -/
@[ext]
structure Input (Symbol : Type) where
  /-- Input symbols strictly to the left of the head, in reverse order. -/
  left : List Symbol
  /-- Input symbols from the head onward, in input order. -/
  right : List Symbol
  /-- Whether the head is at the blank before the input. -/
  atLeft : Bool
deriving Inhabited

namespace Input

variable {Symbol : Type}

/-- Start at native position one, also when the input is empty. -/
@[expose] def init (input : List Symbol) : Input Symbol := ⟨[], input, false⟩

/-- Read the current input symbol, or a blank at either boundary. -/
@[expose] def read (z : Input Symbol) : Option Symbol :=
  if z.atLeft then none else z.right.head?

/-- Move left, stopping at the blank before the input. -/
@[expose] def moveLeft (z : Input Symbol) : Input Symbol :=
  if z.atLeft then z else
    match z.left with
    | [] => { z with atLeft := true }
    | a :: l => ⟨l, a :: z.right, false⟩

/-- Move right, stopping at the blank after the input. -/
@[expose] def moveRight (z : Input Symbol) : Input Symbol :=
  if z.atLeft then { z with atLeft := false } else
    match z.right with
    | [] => z
    | a :: r => ⟨a :: z.left, r, false⟩

/-- Move the input head in the indicated direction. -/
@[expose] def move (z : Input Symbol) : SignType → Input Symbol
  | .neg => z.moveLeft
  | .zero => z
  | .pos => z.moveRight

/-- The stacks reconstruct the input and locate the head at the native bounded position. -/
structure Represents (z : Input Symbol) (input : List Symbol)
    (pos : Fin (input.length + 2)) : Prop where
  /-- The two stacks hold exactly the original input. -/
  contents : z.left.reverse ++ z.right = input
  /-- No symbols precede the left boundary. -/
  left_nil : z.atLeft = true → z.left = []
  /-- Native positions count the left boundary as zero. -/
  pos_eq : pos.val = if z.atLeft then 0 else z.left.length + 1

/-- Initialization agrees with the native initial head position, including on empty input. -/
theorem represents_init (input : List Symbol) :
    (init input).Represents input ⟨1, by omega⟩ := by
  constructor <;> simp [init]

namespace Represents

variable {z : Input Symbol} {input : List Symbol} {pos : Fin (input.length + 2)}

/-- The stacks retain exactly the number of input symbols. -/
theorem length_eq (h : z.Represents input pos) :
    z.left.length + z.right.length = input.length := by
  simpa only [List.length_append, List.length_reverse] using congrArg List.length h.contents

/-- A zipper read agrees with indexing the original input at the native head position. -/
theorem read_eq_getElem? (h : z.Represents input pos) :
    z.read = if pos.val = 0 then none else input[pos.val - 1]? := by
  rcases z with ⟨l, r, b⟩
  cases b with
  | false =>
    have hp : pos.val = l.length + 1 := h.pos_eq
    have hi : input = l.reverse ++ r := h.contents.symm
    simp [read, hp, hi, List.getElem?_append_right, List.head?_eq_getElem?]
  | true => simp [read, h.pos_eq]

/-- A zipper read agrees with the input symbol of any represented native configuration. -/
theorem read_eq_inputSymbol {k : ℕ} {State : Type*} {cfg : Cfg k Symbol State input}
    (h : z.Represents input cfg.inputPos) : z.read = cfg.inputSymbol := by
  rw [h.read_eq_getElem?]
  unfold Cfg.inputSymbol
  have := cfg.inputPos.isLt
  split_ifs <;> grind

/-- Moving left preserves the representation, with clamping at the left boundary. -/
theorem moveLeft (h : z.Represents input pos) :
    z.moveLeft.Represents input (moveInputPos pos .neg) := by
  have hm := val_moveInputPos_eq pos .neg
  simp only [SignType.cast] at hm
  rcases z with ⟨l, r, b⟩
  cases b with
  | true =>
    refine ⟨h.contents, h.left_nil, ?_⟩
    have hp : pos.val = 0 := h.pos_eq
    change (moveInputPos pos .neg).val = 0
    omega
  | false =>
    cases l with
    | nil =>
      refine ⟨h.contents, ?_, ?_⟩
      · simp [Input.moveLeft]
      · have hp : pos.val = 1 := h.pos_eq
        change (moveInputPos pos .neg).val = 0
        omega
    | cons a l =>
      refine ⟨?_, ?_, ?_⟩
      · simpa [Input.moveLeft, List.reverse_cons, List.append_assoc] using h.contents
      · simp [Input.moveLeft]
      · have hp : pos.val = (a :: l).length + 1 := h.pos_eq
        simp only [List.length_cons] at hp
        change (moveInputPos pos .neg).val = l.length + 1
        omega

/-- Moving right preserves the representation, with clamping at the right boundary. -/
theorem moveRight (h : z.Represents input pos) :
    z.moveRight.Represents input (moveInputPos pos .pos) := by
  have hm := val_moveInputPos_eq pos .pos
  simp only [SignType.cast] at hm
  have hlen := h.length_eq
  rcases z with ⟨l, r, b⟩
  change l.length + r.length = input.length at hlen
  cases b with
  | true =>
    have hl : l = [] := h.left_nil rfl
    subst l
    refine ⟨h.contents, ?_, ?_⟩
    · simp [Input.moveRight]
    · have hp : pos.val = 0 := h.pos_eq
      change (moveInputPos pos .pos).val = 1
      omega
  | false =>
    cases r with
    | nil =>
      refine ⟨h.contents, h.left_nil, ?_⟩
      have hp : pos.val = l.length + 1 := h.pos_eq
      simp only [List.length_nil, Nat.add_zero] at hlen
      change (moveInputPos pos .pos).val = l.length + 1
      omega
    | cons a r =>
      refine ⟨?_, ?_, ?_⟩
      · simpa [Input.moveRight, List.reverse_cons, List.append_assoc] using h.contents
      · simp [Input.moveRight]
      · have hp : pos.val = l.length + 1 := h.pos_eq
        simp only [List.length_cons] at hlen
        change (moveInputPos pos .pos).val = l.length + 1 + 1
        omega

/-- Each zipper move simulates the corresponding native bounded head move. -/
theorem move (h : z.Represents input pos) (d : SignType) :
    (z.move d).Represents input (moveInputPos pos d) := by
  cases d with
  | neg => exact h.moveLeft
  | zero =>
    change z.Represents input (moveInputPos pos 0)
    rwa [moveInputPos_zero]
  | pos => exact h.moveRight

end Represents
end Input
end Turing.MultiTapeTM.ToTM2

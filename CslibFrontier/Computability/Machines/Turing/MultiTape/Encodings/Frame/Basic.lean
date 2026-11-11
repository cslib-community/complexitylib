/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: subset of crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Cslib.Init
public import Mathlib.Data.List.Basic

/-! # Pure framed words

The original framing definitions and laws are moved unchanged below encoding-machine
capabilities so their machine implementations do not create an import cycle.
-/

namespace Turing.MultiTapeTM

/-! ### Framed words -/

/-- Each symbol `b` of `w` as `[true, b]`, followed by `[false]`. -/
@[expose] public def frame (w : List Bool) : List Bool := w.flatMap (fun b => [true, b]) ++ [false]

/-- The word framed at the start of `v`, see `Turing.MultiTapeTM.frame`. -/
@[expose] public def unframe : List Bool → List Bool
  | true :: b :: v => b :: unframe v
  | _ => []

/-- What follows the frame at the start of `v`, see `Turing.MultiTapeTM.frame`. -/
@[expose] public def dropFrame : List Bool → List Bool
  | true :: _ :: v => dropFrame v
  | false :: v => v
  | _ => []

@[simp]
public lemma frame_nil : frame [] = [false] := rfl

@[simp]
public lemma frame_cons (b : Bool) (w : List Bool) : frame (b :: w) = true :: b :: frame w := rfl

@[simp]
public lemma length_frame (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  induction w <;> simp [*]; omega

@[simp]
public lemma unframe_frame_append (w u : List Bool) : unframe (frame w ++ u) = w := by
  induction w <;> simp [unframe, *]

@[simp]
public lemma unframe_frame (w : List Bool) : unframe (frame w) = w := by
  simpa using unframe_frame_append w []

@[simp]
public lemma dropFrame_frame_append (w u : List Bool) : dropFrame (frame w ++ u) = u := by
  induction w <;> simp [dropFrame, *]

/-- A framed word followed by another word determines both. -/
public theorem frame_append_inj {w w' u u' : List Bool} (h : frame w ++ u = frame w' ++ u') :
    w = w' ∧ u = u' :=
  ⟨by simpa using congrArg unframe h, by simpa using congrArg dropFrame h⟩

/-- Framing is injective. -/
public theorem frame_injective : Function.Injective frame := fun _ _ h =>
  (frame_append_inj (u := []) (u' := []) (by simpa using h)).1

@[simp]
public lemma frame_ne_nil (w : List Bool) : frame w ≠ [] := by simp [frame]

end Turing.MultiTapeTM

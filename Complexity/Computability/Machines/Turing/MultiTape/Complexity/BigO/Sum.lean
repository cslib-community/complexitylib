/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative

/-!
# Linear resource bounds for tagged sum constructors

Prepending the fixed Boolean tag bit to the payload encoding costs linear time and space in the
encoded input length, without any finite-domain or inhabitance assumption on either summand.

## Main results

* `Turing.MultiTapeTM.ComputableInO.inl`, `.inr`: linear-time and linear-space tagged sum
  injections.
* `Turing.MultiTapeTM.ComputableInO.getLeft?`, `.getRight?`: linear-time and linear-space tagged
  sum projections.

## References

Uses Christian Reitwiessner's native degree/resource calculus (`ComputableInO.append`).
-/

@[expose] public section

attribute [fun_prop] Turing.MultiTapeTM.ComputableInO

namespace Turing.MultiTapeTM.ComputableInO

variable {α β : Type}

/-- A left sum tag has a direct native linear implementation. -/
@[fun_prop]
theorem inl (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInO (Sum.inl (α := α) (β := β)) left (encSum left right)
      (fun a => (left a).length) (fun a => (left a).length) := by
  have hid : ComputableInO (fun a : α => a) left left
      (fun a => (left a).length) (fun a => (left a).length) :=
    ComputableInDegree.id'.inO_one
  exact ((ComputableInO.const (encMid := encBool) false).append hid
    (fun _ => rfl)).mono 2 (fun _ => by omega) (fun _ => by omega)

/-- A right sum tag has a direct native linear implementation. -/
@[fun_prop]
theorem inr (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInO (Sum.inr (α := α) (β := β)) right (encSum left right)
      (fun a => (right a).length) (fun a => (right a).length) := by
  have hid : ComputableInO (fun a : β => a) right right
      (fun a => (right a).length) (fun a => (right a).length) :=
    ComputableInDegree.id'.inO_one
  exact ((ComputableInO.const (encMid := encBool) true).append hid
    (fun _ => rfl)).mono 2 (fun _ => by omega) (fun _ => by omega)

/-- Testing for a left sum tag takes linear time and constant output size. -/
@[fun_prop]
theorem isLeft_deg (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInDegree (Sum.isLeft (α := α) (β := β)) (encSum left right) encBool 1 0 := by
  have hraw : ComputableInDegree (fun s : α ⊕ β => encSum left right s)
      (encSum left right) encBits 1 1 := .of_eq fun _ => rfl
  have hhead := (ComputableInDegree.headD (enc₁ := encBool) (enc := encBits) true).comp hraw
  have hnot := (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool)
    Bool.not).comp hhead
  exact (hnot.mono (d' := 1) (e' := 0)).of_enc_eq fun s => by cases s <;> rfl

/-- Testing for a right sum tag takes linear time and constant output size. -/
@[fun_prop]
theorem isRight_deg (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInDegree (Sum.isRight (α := α) (β := β)) (encSum left right) encBool 1 0 := by
  have hraw : ComputableInDegree (fun s : α ⊕ β => encSum left right s)
      (encSum left right) encBits 1 1 := .of_eq fun _ => rfl
  have hhead := (ComputableInDegree.headD (enc₁ := encBool) (enc := encBits) false).comp hraw
  have hid := (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool)
    id).comp hhead
  exact (hid.mono (d' := 1) (e' := 0)).of_enc_eq fun s => by cases s <;> rfl

/-- Extracting the left summand as an option takes linear time and space. -/
@[fun_prop]
theorem getLeft?_deg (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInDegree (Sum.getLeft? (α := α) (β := β))
      (encSum left right) (encOption left) 1 1 := by
  have hraw : ComputableInDegree (fun s : α ⊕ β => encSum left right s)
      (encSum left right) encBits 1 1 := .of_eq fun _ => rfl
  have htail := (ComputableInDegree.tail (enc₁ := encBool) (enc := encBits)).comp hraw
  have hsome : ComputableInDegree (fun s : α ⊕ β => true :: (encSum left right s).tail)
      (encSum left right) encBits 1 1 :=
    ((ComputableInDegree.const (encMid := encBool) true).append htail
      (fun _ => rfl)).mono
  have hnone : ComputableInDegree (fun _ : α ⊕ β => ([] : List Bool))
      (encSum left right) encBits 1 1 :=
    (ComputableInDegree.const (encMid := encBits) []).mono
  exact (((isLeft_deg left right).ite (hsome.restrict _) (hnone.restrict _)).mono
    (d' := 1) (e' := 1)).of_enc_eq fun s => by cases s <;> rfl

/-- Extracting the right summand as an option takes linear time and space. -/
@[fun_prop]
theorem getRight?_deg (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInDegree (Sum.getRight? (α := α) (β := β))
      (encSum left right) (encOption right) 1 1 := by
  have hraw : ComputableInDegree (fun s : α ⊕ β => encSum left right s)
      (encSum left right) encBits 1 1 := .of_eq fun _ => rfl
  have hnone : ComputableInDegree (fun _ : α ⊕ β => ([] : List Bool))
      (encSum left right) encBits 1 1 :=
    (ComputableInDegree.const (encMid := encBits) []).mono
  exact (((isRight_deg left right).ite (hraw.restrict _) (hnone.restrict _)).mono
    (d' := 1) (e' := 1)).of_enc_eq fun s => by cases s <;> rfl

/-- Extracting the left summand as an option has linear time and space bounds. -/
@[fun_prop]
theorem getLeft? (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInO (Sum.getLeft? (α := α) (β := β))
      (encSum left right) (encOption left)
      (fun s => (encSum left right s).length) (fun s => (encSum left right s).length) :=
  (getLeft?_deg left right).inO_one

/-- Extracting the right summand as an option has linear time and space bounds. -/
@[fun_prop]
theorem getRight? (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInO (Sum.getRight? (α := α) (β := β))
      (encSum left right) (encOption right)
      (fun s => (encSum left right s).length) (fun s => (encSum left right s).length) :=
  (getRight?_deg left right).inO_one

end Turing.MultiTapeTM.ComputableInO

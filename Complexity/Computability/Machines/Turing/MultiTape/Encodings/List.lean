/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Words

/-!
# Encodings of lists

`encList enc` encodes a list as the concatenation of its framed elements
(`Turing.MultiTapeTM.frame`), for any encoding `enc` of the elements. Lists of Booleans also have
the plain encoding `encBits`, the list itself, which is the concatenation of the elements encoded by
`Turing.MultiTapeTM.encBool`. Both have the capabilities of `Turing.MultiTapeTM.ListEncoding`.

## Main definitions

* `Turing.MultiTapeTM.encList`: the concatenation of the framed elements.
* `Turing.MultiTapeTM.encBits`: lists of Booleans encoded as themselves.
-/

namespace Turing.MultiTapeTM

universe u

variable {α : Type u}

/-- Lists encoded as the concatenation of their framed elements. -/
@[expose] public def encList (enc : α ↪ List Bool) : List α ↪ List Bool :=
  ⟨fun l => l.flatMap (frame ∘ enc), fun l l' h => by
    induction l generalizing l' with
    | nil => cases l' <;> simp_all
    | cons a l ih =>
      cases l' with
      | nil => simp at h
      | cons a' l' => rw [enc.injective (frame_append_inj h).1, ih _ (frame_append_inj h).2]⟩

variable {enc : α ↪ List Bool}

@[simp]
public lemma encList_nil : encList enc [] = [] := rfl

@[simp]
public lemma encList_cons (a : α) (l : List α) :
    encList enc (a :: l) = frame (enc a) ++ encList enc l := rfl

public instance : ListEncoding enc (encList enc) where
  headD d := .of_isEmpty_ite d (fun l hl => by cases l <;> simp_all)
    (.of_unframe fun ⟨l, hl⟩ => by cases l <;> simp at hl ⊢)
  tail := .of_dropFrame fun l => by cases l <;> simp [dropFrame]
  isEmpty := .of_isEmpty fun l => by cases l <;> simp

/-- Lists of Booleans encoded as themselves. -/
@[expose] public def encBits : List Bool ↪ List Bool := Function.Embedding.refl _

@[simp]
public lemma encBits_apply (l : List Bool) : encBits l = l := rfl

public instance : ListEncoding encBool encBits where
  headD d := .of_isEmpty_ite d (fun l hl => by simp_all)
    (.of_take_one fun ⟨l, hl⟩ => by cases l; exacts [by simp at hl, rfl])
  tail := .of_tail fun _ => rfl
  isEmpty := .of_isEmpty fun _ => rfl

end Turing.MultiTapeTM

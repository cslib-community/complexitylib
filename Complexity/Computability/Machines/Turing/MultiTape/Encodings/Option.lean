/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Words

/-!
# The encoding of options

`encOption enc` encodes `none` as the empty word and `some a` as `true` followed by `enc a`. It has
the capabilities of `Turing.MultiTapeTM.OptionEncoding`.

## Main definitions

* `Turing.MultiTapeTM.encOption`: the encoding of options.
-/

namespace Turing.MultiTapeTM

universe u

variable {α : Type u}

/-- Options encoded with `none` as the empty word and `some a` as `true` followed by `enc a`. -/
@[expose] public def encOption (enc : α ↪ List Bool) : Option α ↪ List Bool :=
  ⟨fun o => o.elim [] (true :: enc ·), by rintro (_ | a) (_ | b) h <;> simp_all⟩

variable {enc : α ↪ List Bool}

@[simp]
public lemma encOption_none : encOption enc none = [] := rfl

@[simp]
public lemma encOption_some (a : α) : encOption enc (some a) = true :: enc a := rfl

public instance : OptionEncoding enc (encOption enc) where
  none_eq := rfl
  some := .of_cons_true fun _ => rfl
  getD d := .of_isEmpty_ite d (fun o ho => by cases o <;> simp_all)
    (.of_tail fun ⟨o, ho⟩ => by cases o <;> simp at ho ⊢)

end Turing.MultiTapeTM

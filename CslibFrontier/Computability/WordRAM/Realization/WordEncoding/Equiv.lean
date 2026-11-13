/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Absorb

/-!
# Word encodings transported along an equivalence

A program argument, result or loop state can be a named record instead of a nested tuple.
Its `WordEncoding` is the tuple's, transported along an equivalence that lists the fields in the
tuple's order. `realize` then works with the record's field projections and anonymous
constructors directly, and the live-word layout, glue and certificates match the tuple version.

For example, with `structure Cursor where (base : ℕ) (index : ℕ)`:

```
@[expose] def Cursor.equiv : Cursor ≃ ℕ × ℕ where
  toFun c := (c.base, c.index)
  invFun := fun (base, index) => ⟨base, index⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding Cursor := .ofEquiv Cursor.equiv
```

Write `invFun` as a pattern-matching lambda, as above. Written with projections
(`fun p => ⟨p.1, p.2.1, …⟩`), it is the same function, but it reintroduces the positional chains
that the record removes. Expose the equivalence so that importing modules can evaluate a
record's words, for example to install concrete arguments for a realized program.

## Main definitions

* `WordEncoding.ofEquiv`: the encoding of `α` given by an equivalence `α ≃ β` and the encoding of
  `β`.

## Main results

* `WordEncoding.encode_ofEquiv`: the words of `a` are the words of `e a`.
-/

public section

namespace Cslib.WordRAM.Realization.WordEncoding

variable {α β : Type}

/-- The word encoding of `α` given by an equivalence with `β`: the words of `e a`. Kept reducible
so that `realize` evaluates its width to the numeral of `β`. -/
abbrev ofEquiv [WordEncoding β] (e : α ≃ β) : WordEncoding α :=
  ⟨width β, e.toEmbedding.trans encode⟩

/-- The record's words are the words of its tuple image. -/
theorem encode_ofEquiv [WordEncoding β] (e : α ≃ β) (a : α) :
    @encode α (ofEquiv e) a = encode (e a) := rfl

end Cslib.WordRAM.Realization.WordEncoding

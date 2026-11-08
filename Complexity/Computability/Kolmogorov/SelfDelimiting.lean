/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.Bits
public import Mathlib.Data.Nat.Size
import Mathlib.Data.List.Basic

/-!
# A self-delimiting code for binary strings

A program for `x` followed by a program for `y` can only be split back into the two programs if
the end of the first one is marked. The *self-delimiting code* `selfDelimitingCode p` of a binary
string `p` is `1^{|ℓ|} 0 ℓ p`, where `ℓ` is the binary representation of the length of `p`
(`Nat.bits`, least significant digit first): the unary prefix gives the length of `ℓ`, and `ℓ`
gives the length of `p`. It costs `2 size |p| + 1` bits, that is `2 log₂ |p| + O(1)`
[Li and Vitányi, Chapter 1][LiVitanyi2019]. The decoder `decodeSelfDelimiting` splits a
self-delimiting code followed by any string back into the two
(`decodeSelfDelimiting_selfDelimitingCode_append`). It splits every string, so it is a total
function, and it only uses operations that are primitive recursive in Mathlib's sense
(`List.idxOf`, `List.take`, `List.drop`, `List.foldr`).

## Main definitions

* `Cslib.Kolmogorov.selfDelimitingCode`: a binary string prefixed by its length.
* `Cslib.Kolmogorov.decodeSelfDelimiting`: the decoder.

## Main results

* `Cslib.Kolmogorov.decodeSelfDelimiting_selfDelimitingCode_append`: the decoder inverts the code.
* `Cslib.Kolmogorov.selfDelimitingCode_append_inj`: a self-delimiting code followed by any string
  determines both.
* `Cslib.Kolmogorov.length_selfDelimitingCode`: the code of `p` has length
  `|p| + 2 size |p| + 1`.

## References

* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
-/

@[expose] public section

namespace Cslib.Kolmogorov

/-- The *self-delimiting code* `1^{|ℓ|} 0 ℓ p` of a binary string `p`, where `ℓ = Nat.bits |p|` is
the binary representation of the length of `p` [Li and Vitányi, Chapter 1][LiVitanyi2019]. -/
def selfDelimitingCode (p : List Bool) : List Bool :=
  List.replicate p.length.size true ++ false :: (p.length.bits ++ p)

/-- The decoder of the self-delimiting code: `decodeSelfDelimiting (selfDelimitingCode p ++ q)` is
`(p, q)`. It reads the number `k` of leading `true`s, the number `n` whose binary representation
follows the first `false` in `k` bits, and then splits off the next `n` bits. -/
def decodeSelfDelimiting (q : List Bool) : List Bool × List Bool :=
  let k := q.idxOf false
  let r := q.drop (k + 1)
  let n := (r.take k).foldr Nat.bit 0
  ((r.drop k).take n, (r.drop k).drop n)


/-- The extracted word and unused suffix together never exceed the raw input,
including malformed or arbitrarily large numerical length headers. -/
theorem decodeSelfDelimiting_length_le (word : List Bool) :
    (decodeSelfDelimiting word).1.length + (decodeSelfDelimiting word).2.length ≤ word.length := by
  simp only [decodeSelfDelimiting, List.length_take, List.length_drop]
  omega


/-- The decoder inverts the code: it splits `selfDelimitingCode p ++ q` back into `p` and `q`. -/
@[simp]
theorem decodeSelfDelimiting_selfDelimitingCode_append (p q : List Bool) :
    decodeSelfDelimiting (selfDelimitingCode p ++ q) = (p, q) := by
  have hidx : (selfDelimitingCode p ++ q).idxOf false = p.length.size := by
    rw [selfDelimitingCode, List.append_assoc, List.idxOf_append_of_notMem (by simp),
      List.length_replicate, List.cons_append, List.idxOf_cons_self, Nat.add_zero]
  have hdrop :
      (selfDelimitingCode p ++ q).drop (p.length.size + 1) = p.length.bits ++ (p ++ q) := by
    rw [← List.drop_drop, selfDelimitingCode, List.append_assoc,
      List.drop_left' (List.length_replicate ..), List.cons_append, List.drop_one, List.tail_cons,
      List.append_assoc]
  simp only [decodeSelfDelimiting, hidx, hdrop]
  rw [List.take_left' (Nat.size_eq_bits_len _), List.drop_left' (Nat.size_eq_bits_len _),
    Nat.foldr_bit_bits, List.take_left, List.drop_left]

/-- A self-delimiting code followed by any string determines both. -/
theorem selfDelimitingCode_append_inj {p p' q q' : List Bool}
    (h : selfDelimitingCode p ++ q = selfDelimitingCode p' ++ q') : p = p' ∧ q = q' := by
  simpa using congrArg decodeSelfDelimiting h

theorem selfDelimitingCode_injective : Function.Injective selfDelimitingCode := fun p p' h =>
  (selfDelimitingCode_append_inj (q := []) (q' := []) (by rw [h])).1

/-- The self-delimiting code of `p` costs `2 size |p| + 1` bits. -/
theorem length_selfDelimitingCode (p : List Bool) :
    (selfDelimitingCode p).length = p.length + (2 * p.length.size + 1) := by
  simp only [selfDelimitingCode, List.length_append, List.length_replicate, List.length_cons,
    Nat.size_eq_bits_len]
  omega

end Cslib.Kolmogorov

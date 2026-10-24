/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Basic
public import Complexity.Foundations.Data.BitString.List

/-!
# Self-delimiting padding of bounded words

The machine calculus's existing frame encoding makes bounded words equally long without
identifying distinct words. Words longer than the bound retain their complete frame. This
representation bridge is separate from the pure bit-string foundations and from its
polynomial-time certificate in
`Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/BitString.lean`.

## Main definitions

* `Cslib.BitString.padWord`: frame a word and pad it to a supplied width bound.

## Main results

* `Cslib.BitString.word_eq_of_padWord_eq`: injectivity even across different bounds.
* `Cslib.BitString.length_padWord`: bounded words have length `2 * bound + 1`.
* `Cslib.BitString.word_eq_of_paddedBits_eq`: bounded words embed into a fixed finite cube.

## References

Adapted from Computability/Probabilistic/BitString.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing tidy machine frame encoding.
-/

@[expose] public section

namespace Cslib.BitString

open Turing.MultiTapeTM

/-- Pad a framed word to `2 * bound + 1` bits when it fits. Longer words are not truncated. -/
def padWord (bound : ℕ) (word : List Bool) : List Bool :=
  frame word ++ List.replicate (2 * (bound - word.length)) false

/-- Padding never identifies distinct words, even when their bounds differ. -/
theorem word_eq_of_padWord_eq {bound bound' : ℕ} {word word' : List Bool}
    (h : padWord bound word = padWord bound' word') : word = word' :=
  (frame_append_inj h).1

/-- Every word within the supplied bound has the same padded length. -/
theorem length_padWord {bound : ℕ} {word : List Bool} (h : word.length ≤ bound) :
    (padWord bound word).length = 2 * bound + 1 := by
  simp only [padWord, List.length_append, length_frame, List.length_replicate]
  lia

/-- Concatenating bounded, padded words has a length determined solely by their count. -/
theorem length_flatten_padWord (bound : ℕ) (words : List (List Bool))
    (hbound : ∀ word ∈ words, word.length ≤ bound) :
    ((words.map (padWord bound)).flatten).length = words.length * (2 * bound + 1) := by
  induction words with
  | nil => simp
  | cons word rest ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hbound
    simp only [List.map_cons, List.flatten_cons, List.length_append,
      length_padWord hbound.1, ih hbound.2, List.length_cons]
    lia

/-- Padding embeds bounded words into a fixed finite bit-string space. -/
theorem word_eq_of_paddedBits_eq {bound : ℕ} {left right : List Bool}
    (hleft : left.length ≤ bound) (hright : right.length ≤ bound)
    (h : ofList (2 * bound + 1) (padWord bound left) =
      ofList (2 * bound + 1) (padWord bound right)) : left = right := by
  apply word_eq_of_padWord_eq
  simpa only [ofFn_ofList (length_padWord hleft), ofFn_ofList (length_padWord hright)] using
    congrArg List.ofFn h

end Cslib.BitString

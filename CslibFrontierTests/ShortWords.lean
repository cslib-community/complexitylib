/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Data.BitString.ShortWords

/-! The binary-word counting facts need only their foundational import. -/

example (n : ℕ) : {p : List Bool | p.length = n}.encard = 2 ^ n :=
  Cslib.BitString.encard_setOf_length_eq n

example (Q : List (List Bool)) (n : ℕ) (hQ : Q.length < 2 ^ n) :
    ∃ w : List Bool, w.length = n ∧ w ∉ Q :=
  Cslib.BitString.exists_length_eq_notMem Q n hQ

-- The empty word is counted and remains available when the query list is empty.
example : {p : List Bool | p.length = 0}.encard = 1 :=
  Cslib.BitString.encard_setOf_length_eq 0

example : ∃ w : List Bool, w.length = 0 ∧ w ∉ ([] : List (List Bool)) :=
  Cslib.BitString.exists_length_eq_notMem [] 0 (by decide)

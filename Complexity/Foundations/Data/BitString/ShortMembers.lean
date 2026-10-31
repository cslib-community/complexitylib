/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.ShortWords

/-!
# Short members of a language

`Cslib.BitString.shortMembers S n` lists, without repetition, the members of a language
`S : Set (List Bool)` of length at most `n`: the binary words of length at most `n`
(`Cslib.BitString.shortWords`) that lie in `S`.

## Main definitions

* `Cslib.BitString.shortMembers`: the members of a language of length at most `n`.

## Main results

* `Cslib.BitString.mem_shortMembers`: its members.
* `Cslib.BitString.length_shortMembers`: its length is the number of short members.
-/

@[expose] public section

namespace Cslib.BitString

open Classical in
/-- The members of `S` of length at most `n`, listed in some order without repetition. -/
noncomputable def shortMembers (S : Set (List Bool)) (n : ℕ) : List (List Bool) :=
  ((shortWords n).filter (· ∈ S)).toList

variable {S : Set (List Bool)} {n : ℕ}

/-- A word is listed exactly when it is a member of `S` of length at most `n`. -/
@[simp]
theorem mem_shortMembers {w : List Bool} : w ∈ shortMembers S n ↔ w ∈ S ∧ w.length ≤ n := by
  simp [shortMembers, and_comm]

open Classical in
/-- The listing has one entry for each member of `S` of length at most `n`. -/
theorem length_shortMembers (S : Set (List Bool)) (n : ℕ) :
    (shortMembers S n).length = ((shortWords n).filter (· ∈ S)).card := by
  rw [shortMembers, Finset.length_toList]

end Cslib.BitString

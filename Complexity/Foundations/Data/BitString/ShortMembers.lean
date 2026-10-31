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
* `Cslib.BitString.nodup_shortMembers`: it has no repetition.
* `Cslib.BitString.length_shortMembers`: its length is the number of short members.
* `Cslib.BitString.length_le_length_shortMembers`,
  `Cslib.BitString.mem_iff_of_length_eq_length_shortMembers`: the census bounds the duplicate-free
  lists of short members, and a list attaining it lists them all.
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

theorem nodup_shortMembers (S : Set (List Bool)) (n : ℕ) : (shortMembers S n).Nodup :=
  Finset.nodup_toList _

open Classical in
/-- The listing has one entry for each member of `S` of length at most `n`. -/
theorem length_shortMembers (S : Set (List Bool)) (n : ℕ) :
    (shortMembers S n).length = ((shortWords n).filter (· ∈ S)).card := by
  rw [shortMembers, Finset.length_toList]

/-- **The census bounds the lists of distinct short members.** -/
theorem length_le_length_shortMembers {ℓ : List (List Bool)} (hnd : ℓ.Nodup)
    (h : ∀ s ∈ ℓ, s ∈ S ∧ s.length ≤ n) : ℓ.length ≤ (shortMembers S n).length := by
  rw [← List.toFinset_card_of_nodup hnd, ← List.toFinset_card_of_nodup (nodup_shortMembers S n)]
  exact Finset.card_le_card fun s hs => by
    rw [List.mem_toFinset] at hs ⊢
    exact mem_shortMembers.mpr (h s hs)

/-- **A list attaining the census lists all short members.** A duplicate-free list of short
members of `S` with as many entries as there are short members agrees with `S` on every short
word. -/
theorem mem_iff_of_length_eq_length_shortMembers {ℓ : List (List Bool)} (hnd : ℓ.Nodup)
    (h : ∀ s ∈ ℓ, s ∈ S ∧ s.length ≤ n) (hlen : ℓ.length = (shortMembers S n).length)
    {s : List Bool} (hs : s.length ≤ n) : s ∈ ℓ ↔ s ∈ S := by
  have hsub : ℓ.toFinset ⊆ (shortMembers S n).toFinset := fun t ht => by
    rw [List.mem_toFinset] at ht ⊢
    exact mem_shortMembers.mpr (h t ht)
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [List.toFinset_card_of_nodup hnd, List.toFinset_card_of_nodup (nodup_shortMembers S n),
      hlen])
  refine ⟨fun hsℓ => (h s hsℓ).1, fun hsS => ?_⟩
  have hmem : s ∈ (shortMembers S n).toFinset :=
    List.mem_toFinset.mpr (mem_shortMembers.mpr ⟨hsS, hs⟩)
  rwa [← heq, List.mem_toFinset] at hmem

end Cslib.BitString

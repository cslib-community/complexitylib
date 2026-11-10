/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.List
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
import Mathlib.Data.Vector.Basic

/-!
# Counting binary words

The binary words of length at most `L` form a finite set `shortWords L` with `2 ^ (L + 1) - 1`
elements: the words of length `m` are the `2 ^ m` lists `List.ofFn r` for `r : Fin m → Bool`, and
`∑ m ≤ L, 2 ^ m = 2 ^ (L + 1) - 1`. In particular, a list of fewer than `2 ^ n` words
leaves some word of length `n` unused.

## Main definitions

* `Cslib.BitString.shortWords`: the binary words of length at most `L`.

## Main results

* `Cslib.BitString.encard_setOf_length_eq`: there are `2 ^ n` words of length `n`.
* `Cslib.BitString.encard_setOf_length_lt_add_one`: there are `2 ^ n - 1` words of length below
  `n`.
* `Cslib.BitString.exists_length_eq_notMem`: fewer than `2 ^ n` words leave a word of length `n`
  unused.
* `Cslib.BitString.mem_shortWords`: membership is the length bound.
* `Cslib.BitString.card_shortWords`: there are `2 ^ (L + 1) - 1` such words.
* `Cslib.BitString.card_shortWords_lt`: in particular fewer than `2 ^ (L + 1)`.
-/

@[expose] public section

namespace Cslib.BitString

open Finset

/-- There are `2 ^ n` binary strings of length `n`. -/
theorem encard_setOf_length_eq (n : ℕ) : {p : List Bool | p.length = n}.encard = 2 ^ n := by
  change ENat.card (List.Vector Bool n) = _
  rw [ENat.card_eq_coe_fintype_card, card_vector]
  simp

/-- There are `2 ^ n - 1` binary strings of length below `n`. -/
theorem encard_setOf_length_lt_add_one (n : ℕ) :
    {p : List Bool | p.length < n}.encard + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hunion : {p : List Bool | p.length < n + 1} =
        {p | p.length < n} ∪ {p | p.length = n} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      omega
    have hdisj : Disjoint {p : List Bool | p.length < n} {p | p.length = n} :=
      Set.disjoint_left.mpr fun _ hlt heq => Nat.ne_of_lt hlt heq
    rw [hunion, Set.encard_union_eq hdisj, add_right_comm, ih, encard_setOf_length_eq,
      pow_succ, mul_two]

/-- Fewer than `2 ^ n` words leave a word of length `n` unused. -/
theorem exists_length_eq_notMem (Q : List (List Bool)) (n : ℕ) (hQ : Q.length < 2 ^ n) :
    ∃ w : List Bool, w.length = n ∧ w ∉ Q := by
  classical
  have hcard : Q.toFinset.card <
      ((Finset.univ : Finset (Fin n → Bool)).image List.ofFn).card := by
    rw [Finset.card_image_of_injective _ List.ofFn_injective, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    exact (List.toFinset_card_le Q).trans_lt hQ
  obtain ⟨w, hw, hwQ⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hw
  exact ⟨List.ofFn f, List.length_ofFn, fun h => hwQ (List.mem_toFinset.mpr h)⟩

/-- The binary words of length at most `L`. -/
noncomputable def shortWords (L : ℕ) : Finset (List Bool) :=
  (List.finite_length_le Bool L).toFinset

/-- A word lies in `shortWords L` exactly when its length is at most `L`. -/
@[simp]
theorem mem_shortWords {L : ℕ} {w : List Bool} : w ∈ shortWords L ↔ w.length ≤ L := by
  simp [shortWords]

/-- The empty word lies in `shortWords L`. -/
theorem nil_mem_shortWords (L : ℕ) : [] ∈ shortWords L := by simp

/-- The binary words of length at most `L` are the words `List.ofFn r` for `r : Fin m → Bool` and
`m ≤ L`. -/
theorem shortWords_eq_biUnion (L : ℕ) :
    shortWords L =
      (range (L + 1)).biUnion fun m => univ.image (List.ofFn : (Fin m → Bool) → _) := by
  ext w
  simp only [mem_shortWords, mem_biUnion, mem_range, mem_image, mem_univ, true_and]
  refine ⟨fun hw => ⟨w.length, by omega, w.get, List.ofFn_get w⟩, ?_⟩
  rintro ⟨m, hm, r, rfl⟩
  rw [List.length_ofFn]
  omega

/-- There are `2 ^ (L + 1) - 1` binary words of length at most `L`. -/
theorem card_shortWords (L : ℕ) : #(shortWords L) = 2 ^ (L + 1) - 1 := by
  rw [shortWords_eq_biUnion, card_biUnion]
  · simp_rw [card_image_of_injective _ List.ofFn_injective, card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
    rw [Nat.geomSum_eq le_rfl, Nat.div_one]
  · intro m _ m' _ hmm'
    refine disjoint_left.2 fun w hw hw' => hmm' ?_
    obtain ⟨r, -, rfl⟩ := mem_image.1 hw
    obtain ⟨r', -, hr'⟩ := mem_image.1 hw'
    simpa using congrArg List.length hr'.symm

/-- There are fewer than `2 ^ (L + 1)` binary words of length at most `L`. -/
theorem card_shortWords_lt (L : ℕ) : #(shortWords L) < 2 ^ (L + 1) := by
  rw [card_shortWords]
  exact Nat.sub_lt (Nat.two_pow_pos _) one_pos

end Cslib.BitString

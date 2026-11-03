/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.UniformNat
import Complexity.Probability.PMF.Map
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Interval.Finset.Nat

/-!
# Decoding integer ranks in a binary probability tree

A prefix has a natural-number mass, equal to the sum of its two children's masses. A rank
strictly below the initial mass selects a leaf by comparing it with the left child's mass and
subtracting that mass when taking the right branch. Each leaf has exactly its mass many initial
ranks. In particular, a tree of total mass `2 ^ bits` is sampled exactly by `bits` fair bits.

The decoder is an executable deterministic function. The distribution theorems describe its
pushforward of an existing uniform source; they do not assert a machine resource bound for the
supplied mass function. Zero-mass nodes need no special case and are never reached from a valid
rank. Depth zero and a zero-bit seed are included.

## Main definitions

* `Cslib.BitString.RankDecoder.decode`: follow a rank through a fixed number of binary splits.

## Main results

* `Cslib.BitString.RankDecoder.length_decode`: decoding produces the requested number of bits.
* `Cslib.BitString.RankDecoder.mass_decode_pos`: a valid rank reaches a positive-mass leaf.
* `Cslib.BitString.RankDecoder.card_filter_decode`: each leaf has exactly its mass many ranks.
* `Cslib.BitString.RankDecoder.uniformFin_decode_apply`: the law of a uniform finite rank.
* `Cslib.BitString.RankDecoder.uniformList_decode_apply`: the exact law from a fixed fair-bit seed.
-/

public section

namespace Cslib.BitString.RankDecoder

open Probability

/-- Decode `remaining` bits after `pre`, querying only the left child's mass at each step.
The return value is the new suffix. The function is total; its probability guarantees apply to
ranks strictly below the initial mass. -/
@[expose] def decode (mass : List Bool → ℕ) : ℕ → List Bool → ℕ → List Bool
  | 0, _, _ => []
  | remaining + 1, pre, rank =>
    let left := mass (pre ++ [false])
    if rank < left then
      false :: decode mass remaining (pre ++ [false]) rank
    else
      true :: decode mass remaining (pre ++ [true]) (rank - left)

/-- Decoding always produces exactly the requested number of bits, even for an invalid rank. -/
@[simp] theorem length_decode (mass : List Bool → ℕ) (remaining : ℕ)
    (pre : List Bool) (rank : ℕ) :
    (decode mass remaining pre rank).length = remaining := by
  induction remaining generalizing pre rank with
  | zero => rfl
  | succ remaining ih =>
    simp only [decode]
    split_ifs <;> simp [ih]

/-- The first rank assigned to a leaf, relative to its initial prefix. -/
private def offset (mass : List Bool → ℕ) (pre : List Bool) : List Bool → ℕ
  | [] => 0
  | bit :: suffix =>
    (if bit then mass (pre ++ [false]) else 0) + offset mass (pre ++ [bit]) suffix

variable {mass : List Bool → ℕ} {depth : ℕ}
variable (hadd : ∀ pre, pre.length < depth →
  mass pre = mass (pre ++ [false]) + mass (pre ++ [true]))

include hadd

private theorem offset_add_mass_le (pre suffix : List Bool)
    (hdepth : pre.length + suffix.length ≤ depth) :
    offset mass pre suffix + mass (pre ++ suffix) ≤ mass pre := by
  induction suffix generalizing pre with
  | nil => simp [offset]
  | cons bit suffix ih =>
    have hprefix : pre.length < depth := by
      simp only [List.length_cons] at hdepth
      omega
    have hchild (bit : Bool) : (pre ++ [bit]).length + suffix.length ≤ depth := by
      simp only [List.length_append, List.length_cons, List.length_nil] at *
      omega
    have hsplit := hadd pre hprefix
    have hbound := ih (pre ++ [bit]) (hchild bit)
    cases bit <;>
      simp only [offset, Bool.false_eq_true, ite_false, ite_true, zero_add,
        List.append_assoc, List.singleton_append] at * <;> omega

private theorem decode_eq_iff (pre suffix : List Bool)
    (hdepth : pre.length + suffix.length ≤ depth) (rank : ℕ) :
    rank < mass pre ∧ decode mass suffix.length pre rank = suffix ↔
      offset mass pre suffix ≤ rank ∧
        rank < offset mass pre suffix + mass (pre ++ suffix) := by
  induction suffix generalizing pre rank with
  | nil => simp [decode, offset]
  | cons bit suffix ih =>
    have hprefix : pre.length < depth := by
      simp only [List.length_cons] at hdepth
      omega
    have hchild (bit : Bool) : (pre ++ [bit]).length + suffix.length ≤ depth := by
      simp only [List.length_append, List.length_cons, List.length_nil] at *
      omega
    have hsplit := hadd pre hprefix
    cases bit with
    | false =>
      have hbound := offset_add_mass_le hadd (pre ++ [false]) suffix (hchild false)
      have hi := ih (pre ++ [false]) (hchild false) rank
      simp only [List.append_assoc, List.singleton_append] at hbound hi
      by_cases hrank : rank < mass (pre ++ [false])
      · have hroot : rank < mass pre := by omega
        simpa [decode, offset, hrank, hroot] using hi
      · simp only [List.length_cons, decode, hrank, ite_false, List.cons.injEq,
          Bool.true_eq_false, false_and, and_false, offset, Bool.false_eq_true,
          zero_add]
        constructor
        · exact False.elim
        · rintro ⟨hlower, hupper⟩
          omega
    | true =>
      have hi := ih (pre ++ [true]) (hchild true) (rank - mass (pre ++ [false]))
      simp only [List.append_assoc, List.singleton_append] at hi
      by_cases hrank : rank < mass (pre ++ [false])
      · simp only [List.length_cons, decode, hrank, ite_true, List.cons.injEq,
          Bool.false_eq_true, false_and, and_false, offset]
        constructor
        · exact False.elim
        · rintro ⟨hlower, hupper⟩
          omega
      · simp only [List.length_cons, decode, hrank, ite_false, List.cons.injEq,
          true_and, offset, ite_true]
        constructor
        · rintro ⟨hroot, hdecode⟩
          have hresidual : rank - mass (pre ++ [false]) < mass (pre ++ [true]) := by
            omega
          have hinterval := hi.mp ⟨hresidual, hdecode⟩
          omega
        · intro hinterval
          have hresidual :
              offset mass (pre ++ [true]) suffix ≤ rank - mass (pre ++ [false]) ∧
                rank - mass (pre ++ [false]) <
                  offset mass (pre ++ [true]) suffix + mass (pre ++ true :: suffix) := by
            omega
          obtain ⟨hbound, hdecode⟩ := hi.mpr hresidual
          exact ⟨by omega, hdecode⟩

/-- A valid rank reaches a positive-mass leaf; zero-mass branches are not sampled. -/
theorem mass_decode_pos (remaining : ℕ) (pre : List Bool)
    (hdepth : pre.length + remaining ≤ depth) (rank : ℕ) (hrank : rank < mass pre) :
    0 < mass (pre ++ decode mass remaining pre rank) := by
  have hlength := length_decode mass remaining pre rank
  have hinterval := (decode_eq_iff hadd pre (decode mass remaining pre rank)
    (by simpa only [hlength] using hdepth) rank).mp ⟨hrank, by rw [hlength]⟩
  omega

/-- The number of valid initial ranks producing a word is its leaf mass. Words of a different
length have no preimages. This cardinality statement also permits total mass zero. -/
theorem card_filter_decode (remaining : ℕ) (pre : List Bool)
    (hdepth : pre.length + remaining ≤ depth) (word : List Bool) :
    ((Finset.range (mass pre)).filter
      (fun rank => decode mass remaining pre rank = word)).card =
      if word.length = remaining then mass (pre ++ word) else 0 := by
  by_cases hlength : word.length = remaining
  · subst remaining
    have hfiber : (Finset.range (mass pre)).filter
        (fun rank => decode mass word.length pre rank = word) =
        Finset.Ico (offset mass pre word)
          (offset mass pre word + mass (pre ++ word)) := by
      ext rank
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      exact decode_eq_iff hadd pre word hdepth rank
    rw [hfiber]
    simp
  · have hempty : (Finset.range (mass pre)).filter
        (fun rank => decode mass remaining pre rank = word) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro rank _ heq
      exact hlength ((congrArg List.length heq).symm.trans
        (length_decode mass remaining pre rank))
    simp [hlength, hempty]

/-- Decoding a uniform finite rank gives each leaf its integer mass divided by the total mass. -/
theorem uniformFin_decode_apply (remaining : ℕ) (pre : List Bool)
    (hdepth : pre.length + remaining ≤ depth) {size : ℕ} [NeZero size]
    (hroot : mass pre = size) (word : List Bool) :
    ((PMF.uniformOfFintype (Fin size)).map
      (fun rank => decode mass remaining pre rank.val)) word =
      if word.length = remaining then
        (mass (pre ++ word) : ENNReal) / size else 0 := by
  classical
  have hfiber : Nat.card {rank : Fin size //
      decode mass remaining pre rank.val = word} =
      if word.length = remaining then mass (pre ++ word) else 0 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hmap : (Finset.univ.filter
        (fun rank : Fin size => decode mass remaining pre rank.val = word)).map
          Fin.valEmbedding =
        (Finset.range size).filter
          (fun rank => decode mass remaining pre rank = word) := by
      ext rank
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_range, Fin.valEmbedding_apply]
      constructor
      · rintro ⟨index, hdecode, rfl⟩
        exact ⟨index.isLt, hdecode⟩
      · rintro ⟨hbound, hdecode⟩
        exact ⟨⟨rank, hbound⟩, hdecode, rfl⟩
    rw [← Finset.card_map (f := Fin.valEmbedding), hmap, ← hroot]
    exact card_filter_decode hadd remaining pre hdepth word
  rw [PMF.uniformOfFintype_map_apply, Fintype.card_fin, hfiber]
  split_ifs <;> simp

/-- A tree with root mass `2 ^ bits` is sampled exactly by `bits` fair bits followed by the
integer decoder. The statement includes zero bits and depth zero. -/
theorem uniformList_decode_apply (bits : ℕ) (hroot : mass [] = 2 ^ bits) (word : List Bool) :
    ((uniformList bits).map (fun seed => decode mass depth [] (binaryValue seed))) word =
      if word.length = depth then (mass word : ENNReal) / (2 ^ bits : ℕ) else 0 := by
  have hmap : (uniformList bits).map (fun seed => decode mass depth [] (binaryValue seed)) =
      (PMF.uniformOfFintype (Fin (2 ^ bits))).map
        (fun rank => decode mass depth [] rank.val) := by
    change (uniformList bits).map (decode mass depth [] ∘ binaryValue) = _
    rw [← PMF.map_comp, uniformList_binaryValue, PMF.map_comp]
    rfl
  rw [hmap]
  simpa only [List.nil_append] using
    uniformFin_decode_apply hadd depth [] (by simp) hroot word

end Cslib.BitString.RankDecoder

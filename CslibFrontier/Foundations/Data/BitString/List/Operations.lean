/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Foundations.Data.BitString.List.Single
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD

/-!
# Algebraic operations on lists of bits

Finite bit strings and ordinary lists agree under pointwise XOR, Boolean dot products, basis
vectors, subset sums and strict majority. List algorithms are total: an out-of-range basis index
produces zeros, missing selectors are false, and pointwise XOR truncates to the shorter list.
Collection XOR has a declared width and treats missing bits as false.

## Main definitions

* `Cslib.BitString.listStrictMajority`: strict majority, returning false on a tie.
* `Cslib.BitString.listNonpositiveMargin`: compare correct votes with all votes.
* `Cslib.BitString.listSingles`: the basis vectors `listSingle` (`BitString.List.Single`) in
  coordinate order.
* `Cslib.BitString.listXorSelected`: sum selected rows using an ordinary fold.
* `Cslib.BitString.listXor`: sum every row at a declared width, padding missing bits with false.

## Main results

* `Cslib.BitString.ofFn_add`, `Cslib.BitString.flatMap_ofFn_zipWith_add`,
  `Cslib.BitString.zipWith_xor_self_left`, `Cslib.BitString.zipWith_xor_self_right`,
  `Cslib.BitString.dotProduct_eq_foldl`: algebraic representation and cancellation laws.
* `Cslib.BitString.listStrictMajority_map`: a list with distinct voting indices agrees with
  finite-set strict majority.
* `Cslib.BitString.listXorSelected_eq_ofFn_sum`: the selector fold computes the finite mask sum.
* `Cslib.BitString.listXor_eq_ofFn_sum`: collection XOR computes the finite sum of padded views.
* `Cslib.BitString.listXor_pair_left_inj`, `Cslib.BitString.exists_getD_listXor_pair_of_ne`:
  two-word XOR cancels a common right word, and distinct words of the declared width have a set
  bit in their XOR.

## References

Adapted from Probability/WordBits.lean and Crypto/Computational/GoldreichLevin/WordDecoder.lean
and Crypto/Computational/Pseudoentropy/Boosting/Vote.lean and
Crypto/Computational/GeneratorXor.lean
on the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.BitString

/-- Adding finite masks is exactly coordinatewise XOR of their word representations. -/
theorem ofFn_add {n : ℕ} (left right : BitString n) :
    List.ofFn (left + right) = (List.ofFn left).zipWith Bool.xor (List.ofFn right) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [List.getElem_zipWith, Bool.add_eq_xor]

/-- The sums of two equally long lists of blocks, concatenated, are the XOR of the two
concatenations. -/
theorem flatMap_ofFn_zipWith_add {n : ℕ} :
    ∀ left right : List (BitString n), left.length = right.length →
      (List.zipWith (· + ·) left right).flatMap List.ofFn =
        List.zipWith Bool.xor (left.flatMap List.ofFn) (right.flatMap List.ofFn)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: left, y :: right, h => by
    rw [List.zipWith_cons_cons, List.flatMap_cons, List.flatMap_cons, List.flatMap_cons,
      List.zipWith_append (by simp), ofFn_add,
      flatMap_ofFn_zipWith_add left right (by simpa using h)]

/-- Pointwise XOR of equal-length bit lists is left-involutive:
`List.zipWith Bool.xor pad (List.zipWith Bool.xor pad msg) = msg`. -/
theorem zipWith_xor_self_left :
    ∀ pad msg : List Bool, pad.length = msg.length →
      List.zipWith Bool.xor pad (List.zipWith Bool.xor pad msg) = msg
  | [], [], _ => rfl
  | b :: pad, m :: msg, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.zipWith_cons_cons, zipWith_xor_self_left pad msg h]
    cases b <;> cases m <;> rfl

/-- Pointwise XOR of equal-length bit lists is right-involutive:
`List.zipWith Bool.xor (List.zipWith Bool.xor msg pad) pad = msg`. -/
theorem zipWith_xor_self_right :
    ∀ msg pad : List Bool, msg.length = pad.length →
      List.zipWith Bool.xor (List.zipWith Bool.xor msg pad) pad = msg
  | [], [], _ => rfl
  | m :: msg, b :: pad, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.zipWith_cons_cons, zipWith_xor_self_right msg pad h]
    cases m <;> cases b <;> rfl

/-- A Boolean dot product is a pointwise AND followed by a parity fold on words. -/
theorem dotProduct_eq_foldl {n : ℕ} (left right : BitString n) :
    left ⬝ᵥ right = ((List.ofFn left).zipWith Bool.and (List.ofFn right)).foldl Bool.xor false := by
  have hzip : (List.ofFn left).zipWith Bool.and (List.ofFn right) =
      List.ofFn (fun i => left i * right i) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp [List.getElem_zipWith, Bool.mul_eq_and]
  rw [hzip, dotProduct, ← List.sum_ofFn]
  simp [List.sum_eq_foldl, Bool.add_eq_xor, Bool.zero_eq_false]

/-- Strict majority of a word of votes, choosing false on a tie. -/
def listStrictMajority (votes : List Bool) : Bool :=
  decide (votes.length < 2 * (votes.filter id).length)

/-- Whether the correct votes fail to form a strict majority. This test uses natural arithmetic. -/
def listNonpositiveMargin (votes : List Bool) (truth : Bool) : Bool :=
  decide (2 * votes.count truth ≤ votes.length)

/-- The existing strict-majority operation is equivalently a comparison of vote counts. -/
theorem listStrictMajority_eq_decide_count (votes : List Bool) :
    listStrictMajority votes = decide (votes.length < 2 * votes.count true) := by
  simp only [listStrictMajority, List.count_eq_length_filter, beq_true]
  rfl

/-- Listing each voting index once gives exactly finite-set strict majority. -/
theorem listStrictMajority_map {ι : Type} [DecidableEq ι]
    (indices : List ι) (hnodup : indices.Nodup)
    (vote : ι → Bool) :
    listStrictMajority (indices.map vote) = strictMajorityOn indices.toFinset vote := by
  rw [listStrictMajority, strictMajorityOn, ← List.toFinset_filter,
    List.toFinset_card_of_nodup hnodup,
    List.toFinset_card_of_nodup (hnodup.filter vote)]
  simp [List.filter_map, Nat.div_lt_iff_lt_mul, Nat.mul_comm]

/-- The coordinate-mask program agrees with the finite basis vector. -/
theorem listSingle_eq_ofFn_single {n : ℕ} (index : Fin n) :
    listSingle n index = List.ofFn (Pi.single index true) := by
  apply List.ext_getElem (by simp [listSingle])
  intro coordinate hleft hright
  simp [listSingle, Pi.single_apply, Fin.ext_iff, Bool.zero_eq_false, eq_comm]

/-- All coordinate queries in their ordinary increasing order. -/
def listSingles (dimension : ℕ) : List (List Bool) :=
  (List.range dimension).map (listSingle dimension)

/-- The coordinate masks list the finite basis vectors in increasing index order. -/
theorem listSingles_eq_ofFn (dimension : ℕ) :
    listSingles dimension =
      List.ofFn (fun index : Fin dimension => List.ofFn (Pi.single index true)) := by
  apply List.ext_getElem (by simp [listSingles])
  intro index hleft hright
  simpa [listSingles] using
    listSingle_eq_ofFn_single (⟨index, by simpa using hright⟩ : Fin dimension)

/-- XOR the rows selected by a word of bits. Missing selector bits are false. The accumulator
starts at the requested dimension; rows of that dimension preserve its length. -/
def listXorSelected (dimension : ℕ) (selector : List Bool) (rows : List (List Bool)) : List Bool :=
  (rows.foldl (fun state row =>
    (state.1.tail, if state.1.headD false then state.2.zipWith Bool.xor row else state.2))
    (selector, List.replicate dimension false)).2

/-- On finite masks, the selector fold is exactly the sum of the selected rows. -/
theorem listXorSelected_eq_ofFn_sum {n k : ℕ} (selector : BitString k)
    (masks : Fin k → BitString n) :
    listXorSelected n (List.ofFn selector) (List.ofFn (fun i => List.ofFn (masks i))) =
      List.ofFn (∑ i, if selector i then masks i else 0) := by
  let advance (state : List Bool × List Bool) (row : List Bool) :=
    (state.1.tail, if state.1.headD false then state.2.zipWith Bool.xor row else state.2)
  have hfold (count : ℕ) (selector : BitString count) (masks : Fin count → BitString n)
      (value : BitString n) :
      (List.ofFn (fun i => List.ofFn (masks i))).foldl advance
          (List.ofFn selector, List.ofFn value) =
        ([], List.ofFn (value + ∑ i, if selector i then masks i else 0)) := by
    induction count generalizing value with
    | zero => simp
    | succ count ih =>
      cases h : selector 0 <;>
        simpa [List.ofFn_succ, advance, h, ← ofFn_add, Fin.sum_univ_succ, add_assoc] using
          ih (fun i => selector i.succ) (fun i => masks i.succ)
            (value + if selector 0 then masks 0 else 0)
  have hzero : List.ofFn (0 : BitString n) = List.replicate n false := by
    change List.ofFn (fun _ : Fin n => false) = _
    simp
  simpa [listXorSelected, advance, hzero] using
    congrArg Prod.snd (hfold k selector masks 0)

/-- Selecting the characteristic word of a finite subset computes its mask sum. -/
theorem listXorSelected_eq_ofFn_sum_subset {n k : ℕ} (indices : Finset (Fin k))
    (masks : Fin k → BitString n) :
    listXorSelected n (List.ofFn (fun i => decide (i ∈ indices)))
        (List.ofFn (fun i => List.ofFn (masks i))) = List.ofFn (∑ i ∈ indices, masks i) := by
  simpa using listXorSelected_eq_ofFn_sum (fun i => decide (i ∈ indices)) masks

/-- XOR a collection at the supplied width, treating missing bits as false. -/
def listXor (width : ℕ) (words : List (List Bool)) : List Bool :=
  (List.range width).map fun bit =>
    (words.map (fun word => word[bit]?.getD false)).foldl Bool.xor false

/-- The result has the declared width, also for an empty collection or short rows. -/
@[simp] theorem length_listXor (width : ℕ) (words : List (List Bool)) :
    (listXor width words).length = width := by simp [listXor]

/-- The list program agrees exactly with the sum of the finite bit-string views. -/
theorem listXor_eq_ofFn_sum {count : ℕ} (width : ℕ) (words : Fin count → List Bool) :
    listXor width (List.ofFn words) = List.ofFn (∑ i, ofList width (words i)) := by
  have hparity (word : List Bool) : word.foldl Bool.xor false = word.sum := by
    simp [List.sum_eq_foldl, Bool.add_eq_xor, Bool.zero_eq_false]
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [listXor, hparity, ofList, List.map_ofFn, List.sum_ofFn, Finset.sum_apply]

/-- Two-word `listXor` agrees with addition in `BitString m`. -/
theorem listXor_pair (m : ℕ) (u v : List Bool) :
    listXor m [u, v] = List.ofFn (ofList m u + ofList m v) := by
  have h := listXor_eq_ofFn_sum m ![u, v]
  simpa [List.ofFn_succ, Fin.sum_univ_two] using h

/-- Fixed-width view of a two-word `listXor`. -/
@[simp] theorem ofList_listXor_pair (m : ℕ) (u v : List Bool) :
    ofList m (listXor m [u, v]) = ofList m u + ofList m v := by
  rw [listXor_pair, ofList_ofFn]

/-- Two-word `listXor` is commutative. -/
theorem listXor_pair_comm (m : ℕ) (u v : List Bool) :
    listXor m [u, v] = listXor m [v, u] := by
  rw [listXor_pair, listXor_pair, add_comm]

/-- XORing with the same mask twice on the left recovers the fixed-width view of the right word. -/
@[simp] theorem listXor_pair_self_left (m : ℕ) (k u : List Bool) :
    listXor m [k, listXor m [k, u]] = List.ofFn (ofList m u) := by
  have hself : ofList m k + ofList m k = 0 := funext fun i => Bool.xor_self _
  rw [listXor_pair, ofList_listXor_pair, ← add_assoc, hself, zero_add]

/-- XORing with the same mask twice on the left recovers a word of the declared width `m`. -/
theorem listXor_pair_self_left_of_length {m : ℕ} (k : List Bool) {u : List Bool}
    (hu : u.length = m) :
    listXor m [k, listXor m [k, u]] = u := by
  rw [listXor_pair_self_left, ofFn_ofList hu]

/-- Below the width `m`, each bit of a two-word `listXor` is the XOR of the corresponding bits of
the words, with missing bits read as `false`. -/
theorem getD_listXor_pair (m : ℕ) (u v : List Bool) (i : ℕ) (hi : i < m) :
    (listXor m [u, v]).getD i false = (u.getD i false ^^ v.getD i false) := by
  have h := congrFun (ofList_listXor_pair m u v) ⟨i, hi⟩
  simpa [ofList, Pi.add_apply, Bool.add_eq_xor] using h

/-- Two-word `listXor` at the common width `m` of the left words cancels the right word. -/
theorem listXor_pair_left_inj {m : ℕ} {u v : List Bool} (hu : u.length = m) (hv : v.length = m)
    (w : List Bool) : listXor m [u, w] = listXor m [v, w] ↔ u = v := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have hof := congrArg (ofList m) h
  rw [ofList_listXor_pair, ofList_listXor_pair, add_left_inj] at hof
  rw [← ofFn_ofList hu, ← ofFn_ofList hv, hof]

/-- Distinct words of the declared width `m` have a set bit below `m` in their XOR. -/
theorem exists_getD_listXor_pair_of_ne {m : ℕ} {u v : List Bool}
    (hu : u.length = m) (hv : v.length = m) (hne : u ≠ v) :
    ∃ i < m, (listXor m [u, v]).getD i false = true := by
  by_contra hall
  simp only [not_exists, not_and] at hall
  apply hne (List.ext_getElem (hu.trans hv.symm) fun i hi_u hi_v => ?_)
  have hi_m : i < m := by omega
  have hzero := Bool.eq_false_iff.mpr (hall i hi_m)
  rw [getD_listXor_pair m u v i hi_m] at hzero
  have heq_bit : u.getD i false = v.getD i false := by
    cases h1 : u.getD i false <;> cases h2 : v.getD i false <;> simp_all
  simpa only [List.getD_eq_getElem _ _ hi_u, List.getD_eq_getElem _ _ hi_v] using heq_bit

/-- Below the width `m`, row `0` of a word agrees bitwise with the word itself, with missing bits
read as `false`. -/
theorem getD_listRow_zero (m : ℕ) (u : List Bool) (i : ℕ) (hi : i < m) :
    (listRow m 0 u).getD i false = u.getD i false := by
  simpa only [Nat.zero_mul, Nat.zero_add] using getD_listRow (row := 0) hi

end Cslib.BitString

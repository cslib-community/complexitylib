/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.BitIndices
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Batteries.Data.Nat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A linearly packed tree of bit sums

A balanced addition tree counts a block of bits. Its level `j` contains counts of blocks of
`2^j` bits, and each such count fits in `j+1` bits. The bit planes of every level fit together
in fewer than four times the number of leaves. Their addresses use only shifts and additions.

## Main definitions

* `Cslib.BitString.sumTree`: the sum at a node of the balanced tree.
* `Cslib.BitString.sumTreeAddress`: a bit-plane address within the packed tree.
* `Cslib.BitString.sumTreeBits`: the packed bit planes of the tree, read by address.
* `Cslib.BitString.sumTreeWords`: the packed bit planes stored in eight words of `h` bits.

## Main results

* `Cslib.BitString.sumTree_eq_sum`: the tree counts its specified block.
* `Cslib.BitString.sumTree_testBit`: the root counts the set bits of a natural number.
* `Cslib.BitString.sumTreeAddress_injective`: distinct valid node bits have distinct addresses.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Lemma 1.18 (Bit Sum Lemma).
  This balanced-tree packing is a variant of the packed running-sum construction there.
-/

@[expose] public section

namespace Cslib.BitString

open Finset

/-- The number of true bits in the block at level `j`, node `q`. -/
def sumTree (f : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, q => (f q).toNat
  | j + 1, q => sumTree f j (2 * q) + sumTree f j (2 * q + 1)

/-- A level-`j` node counts at most `2^j` bits. -/
theorem sumTree_le (f : ℕ → Bool) (j q : ℕ) : sumTree f j q ≤ 2 ^ j := by
  induction j generalizing q with
  | zero => simp only [sumTree, pow_zero]; cases f q <;> decide
  | succ j ih =>
    rw [sumTree, pow_succ]
    have := ih (2 * q)
    have := ih (2 * q + 1)
    lia

/-- Each count occupies at most `j+1` bits, including the all-one block. -/
theorem sumTree_lt (f : ℕ → Bool) (j q : ℕ) : sumTree f j q < 2 ^ (j + 1) := by
  have := sumTree_le f j q
  have := Nat.two_pow_pos j
  rw [pow_succ]
  lia

/-- The balanced tree counts its contiguous block, in increasing position order. -/
theorem sumTree_eq_sum (f : ℕ → Bool) (j q : ℕ) :
    sumTree f j q = ∑ i ∈ range (2 ^ j), (f (q * 2 ^ j + i)).toNat := by
  induction j generalizing q with
  | zero => simp [sumTree]
  | succ j ih =>
    rw [sumTree, ih, ih, pow_succ, Nat.mul_two, sum_range_add]
    congr 1
    · apply sum_congr rfl
      intro i _
      congr 2
      ring
    · apply sum_congr rfl
      intro i _
      congr 2
      ring

/-- Counting all the bit positions containing a numeral gives its number of set bits. -/
theorem _root_.Nat.sum_testBit_eq_length_bitIndices {x k : ℕ} (hx : x < 2 ^ k) :
    (∑ i ∈ range k, (x.testBit i).toNat) = x.bitIndices.length := by
  have hbits : (range k).filter (fun i => x.testBit i = true) = x.bitIndices.toFinset := by
    ext i
    simp only [mem_filter, mem_range, List.mem_toFinset, Nat.mem_bitIndices]
    constructor
    · exact And.right
    · intro hi
      refine ⟨?_, hi⟩
      have := Nat.ge_two_pow_of_testBit hi
      exact (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp (lt_of_le_of_lt this hx)
  calc
    (∑ i ∈ range k, (x.testBit i).toNat) =
        ∑ i ∈ range k, if x.testBit i = true then 1 else 0 := by
      apply sum_congr rfl
      intro i _
      cases x.testBit i <;> rfl
    _ = ((range k).filter (fun i => x.testBit i = true)).card := by simp
    _ = x.bitIndices.length := by rw [hbits, List.toFinset_card_of_nodup Nat.bitIndices_nodup]

/-- The root of a sufficiently deep tree counts every set bit of a natural number. -/
theorem sumTree_testBit {x m : ℕ} (hx : x < 2 ^ (2 ^ m)) :
    sumTree x.testBit m 0 = x.bitIndices.length := by
  rw [sumTree_eq_sum]
  simpa using Nat.sum_testBit_eq_length_bitIndices hx

/-- Bit `b` of node `q` at level `j` in a tree with `2^m` leaves. -/
def sumTreeAddress (m j b q : ℕ) : ℕ := (j + b + 3) * 2 ^ (m - j) + q

/-- All valid node bits fit in four times the number of leaves. -/
theorem sumTreeAddress_lt {m j b q : ℕ} (hj : j ≤ m) (hb : b ≤ j)
    (hq : q < 2 ^ (m - j)) : sumTreeAddress m j b q < 4 * 2 ^ m := by
  have hc : j + b + 4 ≤ 4 * 2 ^ j := by
    have h : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
    lia
  have hp : 2 ^ j * 2 ^ (m - j) = 2 ^ m := by rw [← pow_add, Nat.add_sub_of_le hj]
  have hh := Nat.mul_le_mul_right (2 ^ (m - j)) hc
  dsimp [sumTreeAddress]
  nlinarith

/-- Increasing the level moves its entire bit plane before the preceding level. -/
private theorem plane_separated {m i j : ℕ} (hij : i < j) (hj : j ≤ m) :
    (2 * j + 4) * 2 ^ (m - j) ≤ (i + 3) * 2 ^ (m - i) := by
  have hg (d : ℕ) : 2 * (i + d + 1) + 4 ≤ (i + 3) * 2 ^ (d + 1) := by
    induction d with
    | zero => simp only [Nat.add_zero]; lia
    | succ d ih =>
      rw [pow_succ]
      nlinarith
  have h := hg (j - i - 1)
  have hd : i + (j - i - 1) + 1 = j := by lia
  have he : j - i - 1 + 1 = j - i := by lia
  rw [hd, he] at h
  have hm := Nat.mul_le_mul_right (2 ^ (m - j)) h
  have hp : 2 ^ (j - i) * 2 ^ (m - j) = 2 ^ (m - i) := by
    rw [← pow_add]
    congr 1
    lia
  rwa [Nat.mul_assoc, hp] at hm

/-- Valid bits at different levels, nodes or bit positions never share an address. -/
theorem sumTreeAddress_injective {m j b q j' b' q' : ℕ}
    (hj : j ≤ m) (hb : b ≤ j) (hq : q < 2 ^ (m - j))
    (hj' : j' ≤ m) (hb' : b' ≤ j') (hq' : q' < 2 ^ (m - j'))
    (he : sumTreeAddress m j b q = sumTreeAddress m j' b' q') :
    j = j' ∧ b = b' ∧ q = q' := by
  have hlevels : j = j' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hs := plane_separated hlt hj'
      have hlo : (j + 3) * 2 ^ (m - j) ≤ sumTreeAddress m j b q := by
        dsimp [sumTreeAddress]
        nlinarith
      have hhi : sumTreeAddress m j' b' q' < (2 * j' + 4) * 2 ^ (m - j') := by
        dsimp [sumTreeAddress]
        nlinarith
      lia
    · have hs := plane_separated hlt hj
      have hlo : (j' + 3) * 2 ^ (m - j') ≤ sumTreeAddress m j' b' q' := by
        dsimp [sumTreeAddress]
        nlinarith
      have hhi : sumTreeAddress m j b q < (2 * j + 4) * 2 ^ (m - j) := by
        dsimp [sumTreeAddress]
        nlinarith
      lia
  subst j'
  have hpos := Nat.two_pow_pos (m - j)
  have hdiv := congrArg (· / 2 ^ (m - j)) he
  have hmod := congrArg (· % 2 ^ (m - j)) he
  simp only [sumTreeAddress] at hdiv
  rw [Nat.mul_comm (j + b + 3), Nat.mul_comm (j + b' + 3)] at hdiv
  simp only [Nat.mul_add_div hpos, Nat.div_eq_of_lt hq,
    Nat.div_eq_of_lt hq', Nat.add_zero] at hdiv
  simp only [sumTreeAddress, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hq,
    Nat.mod_eq_of_lt hq'] at hmod
  exact ⟨rfl, by lia, hmod⟩

/-- The packed bit planes of the actual addition tree, with unused positions set to zero. -/
def sumTreeBits (f : ℕ → Bool) (m a : ℕ) : Bool :=
  decide (∃ j : Fin (m + 1), ∃ b : Fin (j.val + 1), ∃ q : Fin (2 ^ (m - j.val)),
    sumTreeAddress m j.val b.val q.val = a ∧ (sumTree f j.val q.val).testBit b.val = true)

/-- Reading a valid tree address returns exactly the specified node bit. -/
theorem sumTreeBits_address (f : ℕ → Bool) {m j b q : ℕ}
    (hj : j ≤ m) (hb : b ≤ j) (hq : q < 2 ^ (m - j)) :
    sumTreeBits f m (sumTreeAddress m j b q) = (sumTree f j q).testBit b := by
  apply Bool.eq_iff_iff.mpr
  simp only [sumTreeBits, decide_eq_true_eq]
  constructor
  · rintro ⟨j', b', q', he, ht⟩
    obtain ⟨hj', hb', hq'⟩ := sumTreeAddress_injective
      (Nat.le_of_lt_succ j'.isLt) (Nat.le_of_lt_succ b'.isLt) q'.isLt hj hb hq he
    simpa only [hj', hb', hq'] using ht
  · intro ht
    exact ⟨⟨j, by lia⟩, ⟨b, by lia⟩, ⟨q, hq⟩, rfl, ht⟩

/-- A fixed tuple of eight `h`-bit words stores the tree's bit planes. -/
def sumTreeWords (f : ℕ → Bool) (m h : ℕ) (r : Fin 8) : ℕ :=
  Nat.ofBits (fun b : Fin h => sumTreeBits f m (r.val * h + b.val))

/-- Every packed witness is strictly less than `2^h`, independently of the tree contents. -/
theorem sumTreeWords_lt (f : ℕ → Bool) (m h : ℕ) (r : Fin 8) :
    sumTreeWords f m h r < 2 ^ h := Nat.ofBits_lt_two_pow _

/-- Bits within a packed word have the specified global addresses. -/
theorem sumTreeWords_testBit (f : ℕ → Bool) (m h : ℕ) (r : Fin 8) {b : ℕ} (hb : b < h) :
    (sumTreeWords f m h r).testBit b = sumTreeBits f m (r.val * h + b) :=
  Nat.testBit_ofBits_lt _ _ hb

/-- The eight words collectively contain every address below `8h`. -/
theorem exists_sumTreeWords_address {h a : ℕ} (ha : a < 8 * h) :
    ∃ r : Fin 8, ∃ b : Fin h, r.val * h + b.val = a := by
  have hh : 0 < h := by lia
  refine ⟨⟨a / h, (Nat.div_lt_iff_lt_mul hh).mpr ha⟩,
    ⟨a % h, Nat.mod_lt _ hh⟩, ?_⟩
  simpa only [Nat.mul_comm] using Nat.div_add_mod a h

end Cslib.BitString

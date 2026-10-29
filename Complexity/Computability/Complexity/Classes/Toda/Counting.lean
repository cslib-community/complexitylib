/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.ParityP
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Complexity.Foundations.Data.BitString.List
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.PiLex
public import Complexity.Foundations.Data.BitString.WordCount
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Mathlib.Data.List.GetD

/-!
# Counting the parities of a random string with one bit of a `#P` value

The second half of Toda's theorem [Toda][Toda1991], [Arora and Barak, Section 17.4][AroraBarak09]:
for numbers `f r` of accepted witnesses, given for the random strings `r` of length `R`, the
number `G` of random strings with `f r` odd is read off one bit of a single counting function.

## Modulus amplification by binomial coefficients

Toda's amplifier uses residues `0` modulo `2 ^ K` for even counts and `-1` for odd counts.
This module uses the opposite sign: `0` for even counts and `+1` for odd counts. Negating our
amplifier modulo `2 ^ K` recovers the `0`/`-1` convention. All subsequent counts and bit
extraction here use the `+1` convention, from the binomial expansion of `(1 - 2) ^ c`
(`Cslib.BitString.sum_range_neg_two_pow_mul_choose`):

`[c odd] = ∑ i < c, (-2) ^ i * choose c (i + 1)`,

whose terms with `i ≥ K` vanish modulo `2 ^ K`
(`Cslib.BitString.sum_range_neg_two_pow_mul_choose_zmod`). The coefficients `(-2) ^ i` are
replaced by naturals equal to them modulo `2 ^ K` (`Cslib.Complexity.Toda.parityCoeff`), and
`choose (f r) k` counts the `k`-element sets of accepted witnesses, written as strictly
increasing lists of `k` words for the lexicographic order
(`Cslib.BitString.card_filter_strictMono`, `Cslib.BitString.wordLt_ofFn_iff`). So
the words accepted by `Cslib.Complexity.Toda.countingTest` — a size `k ≤ K` in unary, one of
`parityCoeff K (k - 1)` coefficient words, a random string `r` and a strictly increasing list of
`k` accepted witnesses, padded with zero words — number
`H = ∑ i < K, parityCoeff K i * ∑ r, choose (f r) (i + 1)`
(`Cslib.Complexity.Toda.card_filter_countingTest`), and with `K = R + 1`, `H` is `G` modulo
`2 ^ (R + 1)` (`Cslib.Complexity.Toda.cast_card_filter_countingTest`).

## One bit decides the majority

`Cslib.Complexity.Toda.sharpTest` accepts `2 H + 2 ^ R - 1` words
(`Cslib.Complexity.Toda.card_filter_sharpTest`). Since `G ≤ 2 ^ R`, the bit `R + 1` of this
number says whether `2 G > 2 ^ R`, that is whether more than half of the random strings have an
odd number of accepted witnesses (`Cslib.Complexity.Toda.testBit_card_filter_sharpTest`).

## Main definitions

* `Cslib.Complexity.Toda.parityCoeff`: the coefficients of the amplification.
* `Cslib.Complexity.Toda.countingTest`, `Cslib.Complexity.Toda.sharpTest`: the word tests of the
  counting functions.

## Main results

* `Cslib.Complexity.Toda.cast_card_filter_countingTest`: the count is `G` modulo `2 ^ (R + 1)`.
* `Cslib.Complexity.Toda.testBit_card_filter_sharpTest`: one bit says whether `2 G > 2 ^ R`.

## References

* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.Toda

open Finset BitString Turing.MultiTapeTM

/-! ### Modulus amplification -/

/-- Natural coefficients equal to `(-2) ^ i` modulo `2 ^ K`, for `i ≤ K`: `2 ^ i` for even `i`
and `2 ^ K - 2 ^ i` for odd `i`. -/
def parityCoeff (K i : ℕ) : ℕ := if Even i then 2 ^ i else 2 ^ K - 2 ^ i

private theorem cast_parityCoeff {K i : ℕ} (hi : i ≤ K) :
    (parityCoeff K i : ZMod (2 ^ K)) = (-2) ^ i := by
  have h2 : ((2 ^ K : ℕ) : ZMod (2 ^ K)) = 0 := ZMod.natCast_self _
  unfold parityCoeff
  split
  · rename_i h
    rw [h.neg_pow]
    push_cast
    rfl
  · rename_i h
    rw [(Nat.not_even_iff_odd.1 h).neg_pow, Nat.cast_sub (Nat.pow_le_pow_right (by norm_num) hi),
      h2]
    push_cast
    ring

/-- **One bit decides the majority.** If `H` is `G` modulo `2 ^ (R + 1)` and `G ≤ 2 ^ R`, then the
bit `R + 1` of `2 H + (2 ^ R - 1)` says whether `2 G > 2 ^ R`. -/
private theorem testBit_two_mul_add_two_pow_sub_one {R G H : ℕ} (hG : G ≤ 2 ^ R)
    (hH : (H : ZMod (2 ^ (R + 1))) = G) :
    (2 * H + (2 ^ R - 1)).testBit (R + 1) = decide (2 ^ R < 2 * G) := by
  have hGlt : G < 2 ^ (R + 1) := by
    have : 2 ^ (R + 1) = 2 * 2 ^ R := by ring
    have := Nat.one_le_two_pow (n := R)
    omega
  have hmod : H % 2 ^ (R + 1) = G := by
    rw [← Nat.mod_eq_of_lt hGlt]
    exact (ZMod.natCast_eq_natCast_iff' H G (2 ^ (R + 1))).1 hH
  have hpos : 1 ≤ 2 ^ R := Nat.one_le_two_pow
  have hy : (2 * H + (2 ^ R - 1)) % 2 ^ (R + 2) = 2 * G + 2 ^ R - 1 := by
    have h2H : 2 * H % 2 ^ (R + 2) = 2 * G := by
      rw [pow_succ', Nat.mul_mod_mul_left, hmod]
    have h4' : 2 ^ (R + 2) = 4 * 2 ^ R := by ring
    rw [Nat.add_mod, h2H, Nat.mod_eq_of_lt (show 2 ^ R - 1 < 2 ^ (R + 2) by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  rw [← Bool.and_true ((2 * H + (2 ^ R - 1)).testBit (R + 1)),
    show true = decide (R + 1 < R + 2) by simp, Bool.and_comm, ← Nat.testBit_mod_two_pow, hy,
    Nat.testBit_eq_decide_div_mod_eq]
  have h4 : 2 ^ (R + 1) = 2 * 2 ^ R := by ring
  have hlt : 2 * G + 2 ^ R - 1 < 2 * 2 ^ (R + 1) := by omega
  by_cases hc : 2 ^ R < 2 * G
  · have hq : (2 * G + 2 ^ R - 1) / 2 ^ (R + 1) = 1 := by
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [hq, hc]
  · have hq : (2 * G + 2 ^ R - 1) / 2 ^ (R + 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp [hq, hc]

/-! ### Subsets as strictly increasing tuples -/

/-- The `k`-subset test on `K` rows of `Z` bits: the first `k` rows are accepted by `acc` and
strictly increasing, and the other rows are zero. -/
def subsetTest (acc : List Bool → Bool) (K Z k : ℕ) (zs : List Bool) : Bool :=
  ((BitString.listRows K Z zs).zipIdx.all fun p =>
      if p.2 < k then acc p.1 else !(p.1.any fun b => b)) &&
    (List.range (k - 1)).all fun i =>
      BitString.wordLt (BitString.listRow Z i zs) (BitString.listRow Z (i + 1) zs)

@[fun_prop]
theorem computableInPolyTime_subsetTest {γ : Type} {input : γ ↪ List Bool}
    {acc : γ → List Bool → Bool}
    (hacc : ComputableInPolyTime (fun p : γ × List Bool => acc p.1 p.2)
      (encPair input encBits) encBool)
    {K Z k : γ → ℕ} {zs : γ → List Bool}
    (hK : ComputableInPolyTime K input encUnary)
    (hZ : ComputableInPolyTime Z input encUnary)
    (hk : ComputableInPolyTime k input encUnary)
    (hzs : ComputableInPolyTime zs input encBits) :
    ComputableInPolyTime (fun c => subsetTest (acc c) (K c) (Z c) (k c) (zs c)) input
      encBool := by
  unfold subsetTest
  fun_prop

/-- A bit string `z` has no `true` bits in `List.ofFn z` if and only if `z = 0`. -/
private theorem not_any_ofFn_eq_true_iff {Z : ℕ} (z : Fin Z → Bool) :
    (!(List.ofFn z).any fun b => b) = true ↔ z = 0 := by
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, List.mem_ofFn,
    forall_exists_index, forall_apply_eq_imp_iff, Bool.not_eq_true]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

/-- The block-level predicate corresponding to `subsetTest`: the first `k` blocks are accepted and
strictly increasing in lexicographic order, and the remaining blocks are zero. -/
private def SubsetBlockPred (acc : List Bool → Bool) {K Z k : ℕ} (hk : k ≤ K)
    (t : Fin K → BitString Z) : Prop :=
  (∀ j : Fin K, ((j : ℕ) < k → acc (List.ofFn (t j)) = true) ∧ (k ≤ j → t j = 0)) ∧
    ∀ (i : ℕ) (h : i + 1 < k), toLex (t ⟨i, by omega⟩) < toLex (t ⟨i + 1, by omega⟩)

/-- `subsetTest` on `List.ofFn v` holds if and only if `SubsetBlockPred` holds on the blocks of
`v`. -/
private theorem subsetTest_ofFn_iff (acc : List Bool → Bool) {K k Z : ℕ} (hk : k ≤ K)
    (v : Fin (K * Z) → Bool) :
    subsetTest acc K Z k (List.ofFn v) = true ↔
      SubsetBlockPred acc hk (BitString.blocksEquiv v) := by
  -- the test on blocks
  have hrows : BitString.listRows K Z (List.ofFn v) =
      List.ofFn fun j => List.ofFn (BitString.blocksEquiv v j) := by
    rw [BitString.listRows_eq_ofFn, BitString.ofList_ofFn]
    rfl
  have hrow (i : ℕ) (hi : i < K) :
      BitString.listRow Z i (List.ofFn v) = List.ofFn (BitString.blocksEquiv v ⟨i, hi⟩) := by
    rw [BitString.listRow_eq_ofFn (count := K) Z ⟨i, hi⟩, BitString.ofList_ofFn]
    rfl
  simp only [subsetTest, Bool.and_eq_true, hrows, SubsetBlockPred]
  refine and_congr ?_ ?_
  · simp only [List.all_eq_true, Prod.forall]
    refine ⟨fun h j => ?_, fun h w j hw => ?_⟩
    · have hj := h (List.ofFn (BitString.blocksEquiv v j)) j
        (by rw [List.mem_zipIdx_iff_getElem?]; simp)
      refine ⟨fun hjk => by simpa [hjk] using hj, fun hjk => ?_⟩
      rw [ite_eq_right (by omega)] at hj
      exact (not_any_ofFn_eq_true_iff _).1 hj
    · rw [List.mem_zipIdx_iff_getElem?, List.getElem?_ofFn] at hw
      simp only at hw
      split at hw
      · rename_i hjK
        rw [← Option.some.inj hw]
        split
        · exact (h ⟨j, hjK⟩).1 (by simpa)
        · rename_i hjk
          exact (not_any_ofFn_eq_true_iff _).2 ((h ⟨j, hjK⟩).2 (Nat.le_of_not_lt hjk))
      · exact absurd hw (by simp)
  · simp only [List.all_eq_true, List.mem_range]
    refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩
    · have := h i (by omega)
      rwa [hrow i (by omega), hrow (i + 1) (by omega), BitString.wordLt_ofFn_iff] at this
    · rw [hrow i (by omega), hrow (i + 1) (by omega), BitString.wordLt_ofFn_iff]
      exact h i (by omega)

/-- **The `k`-subset test counts `k`-element sets of accepted words**, for `k ≤ K`. -/
private theorem card_filter_subsetTest (acc : List Bool → Bool) {K k : ℕ} (Z : ℕ) (hk : k ≤ K) :
    (univ.filter fun zs : Fin (K * Z) → Bool => subsetTest acc K Z k (List.ofFn zs) = true).card =
      ((univ.filter fun z : Fin Z → Bool => acc (List.ofFn z) = true).card).choose k := by
  classical
  set A := univ.filter fun z : Fin Z → Bool => acc (List.ofFn z) = true with hA
  set P := SubsetBlockPred acc (Z := Z) hk with hP
  rw [show (univ.filter fun zs : Fin (K * Z) → Bool => subsetTest acc K Z k (List.ofFn zs) = true)
      = univ.filter fun zs => P (BitString.blocksEquiv zs) by
    simp only [subsetTest_ofFn_iff _ hk, hP]]
  rw [show (univ.filter fun zs : Fin (K * Z) → Bool => P (BitString.blocksEquiv zs)).card =
      (univ.filter P).card from card_equiv BitString.blocksEquiv
        (fun v => by simp only [mem_filter, mem_univ, true_and])]
  -- restricting to the first `k` blocks
  have hrestrict : (univ.filter P).card = (univ.filter fun g : Fin k → Lex (Fin Z → Bool) =>
      StrictMono g ∧ ∀ i, g i ∈ A.map toLex.toEmbedding).card := by
    refine card_bij (fun t _ i => toLex (t (Fin.castLE hk i))) ?_ ?_ ?_
    · intro t ht
      simp only [mem_filter, mem_univ, true_and, hP, SubsetBlockPred] at ht ⊢
      refine ⟨strictMono_of_lt_succ fun i hi => ht.2 i hi, fun i => ?_⟩
      rw [mem_map]
      exact ⟨_, by rw [hA, mem_filter]; exact ⟨mem_univ _, (ht.1 _).1 i.2⟩, rfl⟩
    · intro t ht t' ht' h
      simp only [mem_filter, mem_univ, true_and, hP, SubsetBlockPred] at ht ht'
      funext j
      by_cases hj : (j : ℕ) < k
      · exact toLex.injective (congrFun h ⟨j, hj⟩)
      · rw [(ht.1 j).2 (by omega), (ht'.1 j).2 (by omega)]
    · intro g hg
      simp only [mem_filter, mem_univ, true_and] at hg
      refine ⟨fun j => if h : (j : ℕ) < k then ofLex (g ⟨j, h⟩) else 0, ?_,
        funext fun i => by simp [i.2]⟩
      simp only [mem_filter, mem_univ, true_and, hP, SubsetBlockPred]
      refine ⟨fun j => ⟨fun hj => ?_, fun hj => by simp [show ¬(j : ℕ) < k by omega]⟩,
        fun i hi => ?_⟩
      · obtain ⟨z, hz, hzg⟩ := mem_map.1 (hg.2 ⟨j, hj⟩)
        simp only [hj, ↓reduceDIte, ← hzg]
        simpa [hA] using hz
      · simp only [show i < k by omega, hi, dite_true]
        exact hg.1 (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
  rw [hrestrict, card_filter_strictMono, card_map]

/-! ### The counting test -/

/-- The unary test: `kb` is `k` bits `true` followed by `false`s, for its number `k ≥ 1` of bits
`true`. -/
def unaryTest (K : ℕ) (kb : List Bool) : Bool :=
  decide (0 < kb.count true) &&
    kb == List.replicate (kb.count true) true ++ List.replicate (K - kb.count true) false

@[fun_prop]
theorem computableInPolyTime_unaryTest {γ : Type} {input : γ ↪ List Bool}
    {K : γ → ℕ} {kb : γ → List Bool}
    (hK : ComputableInPolyTime K input encUnary)
    (hkb : ComputableInPolyTime kb input encBits) :
    ComputableInPolyTime (fun c => unaryTest (K c) (kb c)) input encBool := by
  unfold unaryTest
  fun_prop

/-- Summing over the words passing the unary test of length `K` sums over the sizes
`1, …, K`. -/
private theorem sum_unaryTest (K : ℕ) (F : ℕ → ℕ) :
    ∑ kb : Fin K → Bool, (if unaryTest K (List.ofFn kb) then F ((List.ofFn kb).count true) else 0) =
      ∑ i ∈ range K, F (i + 1) := by
  classical
  rw [← Finset.sum_filter]
  set u : ℕ → Fin K → Bool := fun k i => decide ((i : ℕ) < k) with hu
  have hcount (k : ℕ) (hk : k ≤ K) : (List.ofFn (u k)).count true = k := by
    rw [hu, BitString.ofFn_decide_lt hk]
    simp [List.count_replicate]
  have himage : (univ.filter fun kb : Fin K → Bool => unaryTest K (List.ofFn kb) = true) =
      (range K).image fun i => u (i + 1) := by
    ext kb
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_range, unaryTest, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq]
    constructor
    · rintro ⟨hpos, hkb⟩
      have hle : (List.ofFn kb).count true ≤ K := (List.count_le_length).trans (by simp)
      refine ⟨(List.ofFn kb).count true - 1, by omega, ?_⟩
      apply List.ofFn_injective
      rw [Nat.sub_add_cancel hpos, hu, BitString.ofFn_decide_lt hle, ← hkb]
    · rintro ⟨i, hi, rfl⟩
      rw [hcount _ (by omega)]
      exact ⟨by omega, by rw [hu, BitString.ofFn_decide_lt (by omega)]⟩
  rw [himage, Finset.sum_image]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [hcount _ (Nat.succ_le_of_lt (mem_range.1 hi))]
  · intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    have := congrArg (fun kb => (List.ofFn kb).count true) h
    simp only at this
    rw [hcount _ (by omega), hcount _ (by omega)] at this
    omega

/-- The coefficient test for size `k`: for odd `k`, the first `K + 1 - k` bits are `false`, and
for even `k`, they are not all `false`. -/
def coeffTest (K k : ℕ) (cb : List Bool) : Bool :=
  if k % 2 = 1 then !((cb.take (K + 1 - k)).any fun b => b)
  else (cb.take (K + 1 - k)).any fun b => b

@[fun_prop]
theorem computableInPolyTime_coeffTest {γ : Type} {input : γ ↪ List Bool}
    {K k : γ → ℕ} {cb : γ → List Bool}
    (hK : ComputableInPolyTime K input encUnary)
    (hk : ComputableInPolyTime k input encUnary)
    (hcb : ComputableInPolyTime cb input encBits) :
    ComputableInPolyTime (fun c => coeffTest (K c) (k c) (cb c)) input encBool := by
  unfold coeffTest
  fun_prop

/-- The coefficient test for size `k` accepts `parityCoeff K (k - 1)` words. -/
private theorem card_filter_coeffTest {K k : ℕ} (hk : 1 ≤ k) (hkK : k ≤ K) :
    (univ.filter fun cb : Fin K → Bool => coeffTest K k (List.ofFn cb) = true).card =
      parityCoeff K (k - 1) := by
  classical
  have hsplit := BitString.card_filter_take_drop (m := K) (a := K + 1 - k) (by omega)
    (fun u => (if k % 2 = 1 then !(u.any fun b => b) else u.any fun b => b) = true) (fun _ => True)
  simp only [and_true, filter_true, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at hsplit
  have hK : K - (K + 1 - k) = k - 1 := by omega
  rw [hK] at hsplit
  have hall := BitString.card_filter_not_any (K + 1 - k)
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin (K + 1 - k) → Bool)))
    (fun u => (!(List.ofFn u).any fun b => b) = true)
  simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hsum
  have hpow : 2 ^ (K + 1 - k) * 2 ^ (k - 1) = 2 ^ K := by
    rw [← pow_add, show K + 1 - k + (k - 1) = K by omega]
  unfold coeffTest parityCoeff
  split
  · rename_i hodd
    simp only [hodd, ite_true] at hsplit
    rw [hsplit, hall, one_mul, ite_eq_left (by rw [Nat.even_iff]; omega)]
  · rename_i heven
    simp only [heven, ite_false] at hsplit
    rw [ite_eq_right (by rw [Nat.even_iff]; omega)]
    have hnot : (univ.filter fun u : Fin (K + 1 - k) → Bool =>
        ((List.ofFn u).any fun b => b) = true).card = 2 ^ (K + 1 - k) - 1 := by
      have : (univ.filter fun u : Fin (K + 1 - k) → Bool =>
          ¬((!(List.ofFn u).any fun b => b) = true)) =
          univ.filter fun u => ((List.ofFn u).any fun b => b) = true := by
        ext u; simp
      rw [← this]
      omega
    rw [hsplit, hnot, Nat.sub_mul, hpow, one_mul]

/-- **The counting test**: a size `k` in unary in the first `K` bits, a coefficient word in the
next `K`, a random string `r` in the next `R`, and a `k`-subset of words accepted by `accept r`
in `K` rows of `Z` bits. -/
def countingTest (accept : List Bool → List Bool → Bool) (K R Z : ℕ) (w : List Bool) : Bool :=
  unaryTest K (w.take K) && coeffTest K ((w.take K).count true) ((w.drop K).take K) &&
    subsetTest (accept ((w.drop (K + K)).take R)) K Z ((w.take K).count true) (w.drop (K + K + R))

/-- For a fixed size `1 ≤ k ≤ K`, the number of words passing both `coeffTest` and `subsetTest` is
`parityCoeff K (k - 1)` times the sum over `r` of `choose (f r) k`. -/
private theorem card_filter_coeff_and_subsetTest (accept : List Bool → List Bool → Bool)
    {K R Z k : ℕ} (hk1 : 1 ≤ k) (hkK : k ≤ K) :
    (univ.filter fun w : Fin (K + (R + K * Z)) → Bool =>
      coeffTest K k ((List.ofFn w).take K) = true ∧
        subsetTest (accept (((List.ofFn w).drop K).take R)) K Z k ((List.ofFn w).drop (K + R)) =
          true).card =
      parityCoeff K (k - 1) * ∑ r : Fin R → Bool,
        ((univ.filter fun z : Fin Z → Bool =>
          accept (List.ofFn r) (List.ofFn z) = true).card).choose k := by
  classical
  -- split off the coefficient bits
  have h3 := BitString.card_filter_ofFn_add K (R + K * Z) (fun u v => coeffTest K k u = true ∧
    subsetTest (accept (v.take R)) K Z k (v.drop R) = true)
  have h3' : (univ.filter fun w : Fin (K + (R + K * Z)) → Bool =>
      coeffTest K k ((List.ofFn w).take K) = true ∧
        subsetTest (accept (((List.ofFn w).drop K).take R)) K Z k
          ((List.ofFn w).drop (K + R)) = true).card =
      ∑ u : Fin K → Bool, (univ.filter fun w : Fin (R + K * Z) → Bool =>
        coeffTest K k (List.ofFn u) = true ∧
          subsetTest (accept ((List.ofFn w).take R)) K Z k ((List.ofFn w).drop R) =
            true).card := by
    rw [← h3]
    congr 1 with w
    simp only [mem_filter, mem_univ, true_and, List.drop_drop]
  rw [h3']
  set Y := (univ.filter fun w : Fin (R + K * Z) → Bool =>
    subsetTest (accept ((List.ofFn w).take R)) K Z k ((List.ofFn w).drop R) = true).card with hY
  have hY' : Y = ∑ r : Fin R → Bool,
      ((univ.filter fun z : Fin Z → Bool => accept (List.ofFn r) (List.ofFn z) = true).card).choose
        k := by
    rw [hY, BitString.card_filter_ofFn_add R (K * Z)
      (fun u v => subsetTest (accept u) K Z k v = true)]
    exact sum_congr rfl fun r _ => card_filter_subsetTest _ Z hkK
  have hsum : ∑ u : Fin K → Bool, (univ.filter fun w : Fin (R + K * Z) → Bool =>
      coeffTest K k (List.ofFn u) = true ∧
        subsetTest (accept ((List.ofFn w).take R)) K Z k ((List.ofFn w).drop R) =
          true).card =
        ∑ u : Fin K → Bool, if coeffTest K k (List.ofFn u) = true then Y else 0 := by
    refine sum_congr rfl fun u _ => ?_
    by_cases h : coeffTest K k (List.ofFn u) = true
    · simp only [h, true_and, ↓reduceIte, hY]
    · simp [h]
  rw [hsum, ← Finset.sum_filter, sum_const, smul_eq_mul, card_filter_coeffTest hk1 hkK, hY']

/-- **The count of the counting test**: `∑ i < K, parityCoeff K i * ∑ r, choose (f r) (i + 1)`,
where `f r` counts the words accepted by `accept r`. -/
theorem card_filter_countingTest (accept : List Bool → List Bool → Bool) (K R Z : ℕ) :
    (univ.filter fun w : Fin (K + (K + (R + K * Z))) → Bool =>
      countingTest accept K R Z (List.ofFn w) = true).card =
      ∑ i ∈ range K, parityCoeff K i * ∑ r : Fin R → Bool,
        ((univ.filter fun z : Fin Z → Bool =>
          accept (List.ofFn r) (List.ofFn z) = true).card).choose (i + 1) := by
  classical
  -- the raw count after a selector of `k`
  set C : ℕ → ℕ := fun k => (univ.filter fun w : Fin (K + (R + K * Z)) → Bool =>
    coeffTest K k ((List.ofFn w).take K) = true ∧
      subsetTest (accept (((List.ofFn w).drop K).take R)) K Z k ((List.ofFn w).drop (K + R)) =
        true).card with hC
  have h1 := BitString.card_filter_ofFn_add K (K + (R + K * Z))
    (fun u v => countingTest accept K R Z (u ++ v) = true)
  simp only [List.take_append_drop] at h1
  rw [h1]
  have h2 (kb : Fin K → Bool) : (univ.filter fun w : Fin (K + (R + K * Z)) → Bool =>
      countingTest accept K R Z (List.ofFn kb ++ List.ofFn w) = true).card =
      if unaryTest K (List.ofFn kb) then C ((List.ofFn kb).count true) else 0 := by
    have hlen : (List.ofFn kb).length = K := List.length_ofFn
    have hw (w : List Bool) : countingTest accept K R Z (List.ofFn kb ++ w) =
        (unaryTest K (List.ofFn kb) && (coeffTest K ((List.ofFn kb).count true) (w.take K) &&
          subsetTest (accept ((w.drop K).take R)) K Z ((List.ofFn kb).count true)
            (w.drop (K + R)))) := by
      simp only [countingTest, List.take_left' hlen, Bool.and_assoc]
      rw [show K + K + R = K + (K + R) by omega, ← List.drop_drop, List.drop_left' hlen,
        ← List.drop_drop, List.drop_left' hlen]
    simp only [hw]
    by_cases hu : unaryTest K (List.ofFn kb) = true
    · simp only [hu, ↓reduceIte, Bool.true_and, Bool.and_eq_true, hC]
    · simp [hu]
  simp only [h2]
  rw [sum_unaryTest]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiK : i < K := by simpa using hi
  exact (card_filter_coeff_and_subsetTest accept (by omega) (by omega)).trans
    (by rw [Nat.add_sub_cancel])

/-- **The count of the counting test is the number of random strings with an odd number of
accepted words**, modulo `2 ^ (R + 1)`, with sizes up to `K = R + 1`. -/
theorem cast_card_filter_countingTest (accept : List Bool → List Bool → Bool) (R Z : ℕ) :
    ((univ.filter fun w : Fin ((R + 1) + ((R + 1) + (R + (R + 1) * Z))) → Bool =>
      countingTest accept (R + 1) R Z (List.ofFn w) = true).card : ZMod (2 ^ (R + 1))) =
      (univ.filter fun r : Fin R → Bool => Odd (univ.filter fun z : Fin Z → Bool =>
        accept (List.ofFn r) (List.ofFn z) = true).card).card := by
  classical
  rw [card_filter_countingTest, card_filter]
  push_cast
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun r _ => ?_
  rw [← sum_range_neg_two_pow_mul_choose_zmod]
  refine sum_congr rfl fun i hi => ?_
  rw [cast_parityCoeff (Nat.le_of_lt (mem_range.1 hi))]

/-- **The `#P` test**: after a bit `true`, a free bit and the counting test; after a bit
`false`, a word of `R` bits not all `true`, then `false`s. -/
def sharpTest (accept : List Bool → List Bool → Bool) (R Z : ℕ) (w : List Bool) : Bool :=
  (w.headD false && countingTest accept (R + 1) R Z (w.drop 2)) ||
    (!w.headD false && (!((w.tail.take R).all fun b => b) && !((w.tail.drop R).any fun b => b)))

/-- The `#P` test accepts `2 H + (2 ^ R - 1)` words, for the count `H` of the counting test. -/
theorem card_filter_sharpTest (accept : List Bool → List Bool → Bool) (R Z : ℕ) :
    (univ.filter fun w : Fin ((R + 1) + ((R + 1) + (R + (R + 1) * Z)) + 1 + 1) → Bool =>
      sharpTest accept R Z (List.ofFn w) = true).card =
      2 * (univ.filter fun w : Fin ((R + 1) + ((R + 1) + (R + (R + 1) * Z))) → Bool =>
        countingTest accept (R + 1) R Z (List.ofFn w) = true).card + (2 ^ R - 1) := by
  classical
  set LH := (R + 1) + ((R + 1) + (R + (R + 1) * Z))
  rw [BitString.card_filter_ofFn_succ (LH + 1) (fun l => sharpTest accept R Z l = true)]
  have h1 : (univ.filter fun w : Fin (LH + 1) → Bool =>
      sharpTest accept R Z (true :: List.ofFn w) = true).card =
      2 * (univ.filter fun w : Fin LH → Bool =>
        countingTest accept (R + 1) R Z (List.ofFn w) = true).card := by
    simp only [sharpTest, List.headD_cons, Bool.true_and, Bool.not_true, Bool.false_and,
      Bool.or_false, List.drop_succ_cons]
    rw [BitString.card_filter_ofFn_succ LH
      (fun l => countingTest accept (R + 1) R Z (l.drop 1) = true)]
    simp only [List.drop_succ_cons, List.drop_zero]
    ring
  have h2 : (univ.filter fun w : Fin (LH + 1) → Bool =>
      sharpTest accept R Z (false :: List.ofFn w) = true).card = 2 ^ R - 1 := by
    simp only [sharpTest, List.headD_cons, Bool.false_and, Bool.not_false, Bool.true_and,
      Bool.false_or, List.tail_cons]
    have := BitString.card_filter_take_drop (m := LH + 1) (a := R) (by omega)
      (fun u => (!(u.all fun b => b)) = true) (fun v => (!(v.any fun b => b)) = true)
    simp only [Bool.and_eq_true]
    rw [this, BitString.card_filter_not_any, mul_one]
    have hsum := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin R → Bool)))
      (fun u => ((List.ofFn u).all fun b => b) = true)
    simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      BitString.card_filter_all] at hsum
    have : (univ.filter fun u : Fin R → Bool => (!(List.ofFn u).all fun b => b) = true) =
        univ.filter fun u => ¬((List.ofFn u).all fun b => b) = true := by
      ext u; simp
    rw [this]
    omega
  rw [h1, h2]

/-- **One bit of the `#P` count decides the majority**: the bit `R + 1` of the number of words
accepted by the `#P` test says whether more than half of the random strings `r` of length `R`
have an odd number of words accepted by `accept r`. -/
theorem testBit_card_filter_sharpTest (accept : List Bool → List Bool → Bool) (R Z : ℕ) :
    ((univ.filter fun w : Fin ((R + 1) + ((R + 1) + (R + (R + 1) * Z)) + 1 + 1) → Bool =>
      sharpTest accept R Z (List.ofFn w) = true).card).testBit (R + 1) =
      decide (2 ^ R < 2 * (univ.filter fun r : Fin R → Bool =>
        Odd (univ.filter fun z : Fin Z → Bool =>
          accept (List.ofFn r) (List.ofFn z) = true).card).card) := by
  rw [card_filter_sharpTest]
  refine testBit_two_mul_add_two_pow_sub_one ?_ (cast_card_filter_countingTest accept R Z)
  exact (card_le_univ _).trans_eq (by simp)

/-! ### Polynomial time -/

variable {α : Type} {enc : α ↪ List Bool} {γ : Type} {input : γ ↪ List Bool}

@[fun_prop]
theorem computableInPolyTime_countingTest {V : (α × List Bool) × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair (encPair enc encBits) encBits) encBool)
    {a : γ → α} {K R Z : γ → ℕ} {w : γ → List Bool}
    (ha : ComputableInPolyTime a input enc)
    (hK : ComputableInPolyTime K input encUnary)
    (hR : ComputableInPolyTime R input encUnary)
    (hZ : ComputableInPolyTime Z input encUnary)
    (hw : ComputableInPolyTime w input encBits) :
    ComputableInPolyTime (fun c => countingTest (fun r z => V ((a c, r), z)) (K c) (R c)
      (Z c) (w c)) input encBool := by
  unfold countingTest
  fun_prop

/-- Toda's counting verifier has a plain polynomial-time certificate with the same captured
input, two unary width parameters and word encoding as its machine-construction certificate. -/
@[fun_prop]
theorem computableInPolyTime_sharpTest {V : (α × List Bool) × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair (encPair enc encBits) encBits) encBool)
    {a : γ → α} {R Z : γ → ℕ} {w : γ → List Bool}
    (ha : ComputableInPolyTime a input enc)
    (hR : ComputableInPolyTime R input encUnary)
    (hZ : ComputableInPolyTime Z input encUnary)
    (hw : ComputableInPolyTime w input encBits) :
    ComputableInPolyTime (fun c => sharpTest (fun r z => V ((a c, r), z)) (R c) (Z c) (w c))
      input encBool := by
  unfold sharpTest
  fun_prop

end Cslib.Complexity.Toda

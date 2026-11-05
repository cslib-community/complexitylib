/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.PMF.Uniform
public import Complexity.Crypto.Protocols.SecretSharing.ImperfectRandomness
import all Complexity.Crypto.Protocols.SecretSharing.ImperfectRandomness
import Mathlib.Algebra.BigOperators.ModEq

/-!
# Source classes from complementary branch sets

The common source family in [Aggarwal2026], Sections 4 and 5: at each index,
a source includes either every branch in a fixed set or every branch outside it.
These definitions specify actual uniform laws. They do not assume the extraction
or privacy conclusions of the threshold constructions.

The extraction results formalize the complete parity and matching upper-bound arguments
of STOC submission 886, November 3, 2026, Lemmas 4.4 and 5.4. The branch type is an
arbitrary odd finite type. The index type is arbitrary for the lower bound, and even
and nonempty for tightness. The two nonempty branch classes must have sizes `a` and
`a+1` for the matching upper bound; either orientation is supported. The extractor
uses a half set whose existence is proved, rather than assumed.

For Theorem 4.1 take `|B| = 2*n-1`; for Theorem 5.1 take `|B| = 2^r-1`.
Threshold schemes and their privacy are separate consumers of this source API.
The reused `bitSign` assigns `true` sign `+1`, the negative of the paper's convention;
absolute bias and statistical distance are unchanged.

## Main definitions

* `keys`: the allowed branch/index pairs for a choice of indices.
* `source`: the uniform law on those pairs.
* `indexCount`: the number of keys at a specified set of indices.

## Main results

* `no_bit_extractor`, `no_string_extractor`: actual-source lower bounds `1/(2*|B|)`.
* `balanced_index_upper`: the all-source upper bound for a balanced index bit.
* `exists_tight_index_extractor`: existence of that bit and an actual source attaining equality.
* `support_source`, `minEntropy_source`: exact support and min-entropy of each source.

## References

* [Aggarwal2026], equations (6) and (8), Lemmas 4.4 and 5.4,
  submission PDF pp. 8–11.
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness.OddSources

open Finset Cslib.Probability
open scoped Cslib.Probability.PMF

variable {B I : Type*} [Fintype B] [Fintype I] [DecidableEq B] [DecidableEq I]

/-- At indices in `T`, take the branches in `A`; at other indices, take the complement. -/
@[expose] def keys (A : Finset B) (T : Finset I) : Finset (B × I) :=
  univ.filter fun k => (k.1 ∈ A ↔ k.2 ∈ T)

/-- Membership records exactly which branch choice is used at an index. -/
@[simp] theorem mem_keys (A : Finset B) (T : Finset I) (k : B × I) :
    k ∈ keys A T ↔ (k.1 ∈ A ↔ k.2 ∈ T) := by
  simp [keys]

/-- The two source blocks are products of their branch and index choices. -/
theorem keys_eq_union_product (A : Finset B) (T : Finset I) :
    keys A T = (A ×ˢ T) ∪ ((univ \ A) ×ˢ (univ \ T)) := by
  ext k
  simp only [mem_keys, mem_union, mem_product, mem_sdiff, mem_univ, true_and]
  tauto

/-- Exact support size for an arbitrary complementary pair of branch classes. -/
theorem card_keys (A : Finset B) (T : Finset I) :
    (keys A T).card = A.card * T.card +
      (Fintype.card B - A.card) * (Fintype.card I - T.card) := by
  have hd : Disjoint A (univ \ A) := disjoint_sdiff
  rw [keys_eq_union_product,
    card_union_of_disjoint (disjoint_product.mpr (Or.inl hd)), card_product, card_product,
    card_sdiff_of_subset (subset_univ A), card_sdiff_of_subset (subset_univ T), card_univ,
    card_univ]

/-- Nonempty branch choices and index space give a nonempty source for every `T`. -/
theorem keys_nonempty [Nonempty I] (A : Finset B) (hA : A.Nonempty)
    (hAc : (univ \ A).Nonempty) (T : Finset I) : (keys A T).Nonempty := by
  obtain ⟨i⟩ := ‹Nonempty I›
  by_cases hi : i ∈ T
  · obtain ⟨b, hb⟩ := hA
    exact ⟨(b, i), by simp [hb, hi]⟩
  · obtain ⟨b, hb⟩ := hAc
    exact ⟨(b, i), by simp [(mem_sdiff.mp hb).2, hi]⟩

/-- The actual flat source indexed by `T`, with no additional dealer randomness. -/
@[expose] noncomputable def source [Nonempty I] (A : Finset B) (hA : A.Nonempty)
    (hAc : (univ \ A).Nonempty) (T : Finset I) : PMF (B × I) :=
  PMF.uniformOfFinset (keys A T) (keys_nonempty A hA hAc T)

/-- Summation over an actual source, grouped by index and branch class. -/
theorem sum_keys (A : Finset B) (T : Finset I) (f : B × I → ℝ) :
    (∑ k ∈ keys A T, f k) =
      ∑ i, if i ∈ T then ∑ b ∈ A, f (b, i) else ∑ b ∈ univ \ A, f (b, i) := by
  rw [keys_eq_union_product,
    sum_union (disjoint_product.mpr (Or.inl disjoint_sdiff)), sum_product, sum_product]
  rw [sum_comm, sum_comm (s := univ \ A)]
  conv_lhs => arg 1; rw [show T = univ.filter (· ∈ T) by ext; simp, sum_filter]
  conv_lhs => arg 2; rw [show univ \ T = univ.filter (· ∉ T) by ext; simp, sum_filter]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  split_ifs <;> simp_all

/-- The real expectation is the normalized sum over the allowed keys. -/
theorem source_expect [Nonempty I] (A : Finset B) (hA : A.Nonempty)
    (hAc : (univ \ A).Nonempty) (T : Finset I) (f : B × I → ℝ) :
    (∑ k, (source A hA hAc T k).toReal * f k) =
      (∑ k ∈ keys A T, f k) / (keys A T).card := by
  classical
  simp only [source, PMF.uniformOfFinset_apply]
  simp_rw [apply_ite ENNReal.toReal, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_zero, ite_mul, zero_mul]
  rw [← sum_filter, ← mul_sum]
  have hs : univ.filter (fun k => k ∈ keys A T) = keys A T := by ext; simp
  rw [hs]
  ring

/-- Complementary sources partition the entire key alphabet. -/
theorem card_keys_add_compl (A : Finset B) (T : Finset I) :
    (keys A T).card + (keys A (univ \ T)).card = Fintype.card B * Fintype.card I := by
  have hu : keys A T ∪ keys A (univ \ T) = univ := by ext; simp; tauto
  have hd : Disjoint (keys A T) (keys A (univ \ T)) := by
    apply disjoint_left.mpr
    intro k hk hk'
    simp only [mem_keys, mem_sdiff, mem_univ, true_and] at hk hk'
    tauto
  rw [← card_union_of_disjoint hd, hu, card_univ, Fintype.card_prod]

private theorem odd_signed_sum (A : Finset B) (hodd : Odd (Fintype.card B))
    (e : B → Bool) :
    1 ≤ |(∑ b ∈ A, bitSign (e b)) - ∑ b ∈ univ \ A, bitSign (e b)| := by
  let z : B → ℤ := fun b => if b ∈ A then (if e b then 1 else -1)
    else -(if e b then 1 else -1)
  have hz : ∀ b ∈ (univ : Finset B), z b ≡ 1 [ZMOD 2] := by
    intro b _
    dsimp [z]
    split_ifs <;> decide
  have hp := Int.ModEq.sum hz
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, Int.ModEq] at hp
  have ho : (Fintype.card B : ℤ) % 2 = 1 := by exact_mod_cast Nat.odd_iff.mp hodd
  have hn : (∑ b, z b) ≠ 0 := by omega
  have hab : (1 : ℤ) ≤ |∑ b, z b| := Int.one_le_abs hn
  have heq : ((∑ b, z b : ℤ) : ℝ) =
      (∑ b ∈ A, bitSign (e b)) - ∑ b ∈ univ \ A, bitSign (e b) := by
    rw [← sum_filter_add_sum_filter_not (s := univ) (p := fun b => b ∈ A)]
    simp only [Int.cast_add, Int.cast_sum]
    have ha : univ.filter (fun b => b ∈ A) = A := by ext; simp
    have hc : univ.filter (fun b => b ∉ A) = univ \ A := by ext; simp
    rw [ha, hc]
    have ha' : ∀ b ∈ A, (z b : ℝ) = bitSign (e b) := by
      intro b hb
      simp [z, hb, bitSign]
    have hc' : ∀ b ∈ univ \ A, (z b : ℝ) = -bitSign (e b) := by
      intro b hb
      simp [z, (mem_sdiff.mp hb).2, bitSign]
    rw [sum_congr rfl ha', sum_congr rfl hc', sum_neg_distrib, sub_eq_add_neg]
  rw [← heq]
  exact_mod_cast hab

/-- Full odd-parity obstruction, independent of the sizes of the two branch classes.
This is the common argument of [Aggarwal2026], Lemmas 4.4 and 5.4. -/
theorem exists_signed_imbalance (A : Finset B) (hodd : Odd (Fintype.card B))
    (ext : B × I → Bool) :
    ∃ T : Finset I, (keys A T).card / (Fintype.card B : ℝ) ≤
      |∑ k ∈ keys A T, bitSign (ext k)| := by
  let v : I → ℝ := fun i => (∑ b ∈ A, bitSign (ext (b, i))) -
    ∑ b ∈ univ \ A, bitSign (ext (b, i))
  let T := univ.filter fun i => 0 < v i
  let H : Finset I → ℝ := fun S => ∑ k ∈ keys A S, bitSign (ext k)
  have hdiff : H T - H (univ \ T) = ∑ i, |v i| := by
    dsimp [H]
    rw [sum_keys, sum_keys, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    by_cases hi : 0 < v i
    · have hit : i ∈ T := by simp [T, hi]
      simp only [hit, mem_sdiff, mem_univ, not_true_eq_false, and_false,
        ite_true, ite_false]
      exact (abs_of_pos hi).symm
    · have hit : i ∉ T := by simp [T, hi]
      simp only [hit, mem_sdiff, mem_univ, not_false_eq_true, and_self,
        ite_true, ite_false]
      rw [abs_of_nonpos (le_of_not_gt hi)]
      dsimp [v]
      ring
  have hlower : (Fintype.card I : ℝ) ≤ H T - H (univ \ T) := by
    rw [hdiff]
    simpa only [sum_const, card_univ, nsmul_eq_mul, mul_one, v] using
      sum_le_sum (s := univ) (fun i _ => odd_signed_sum A hodd (fun b => ext (b, i)))
  have hcards : ((keys A T).card : ℝ) + (keys A (univ \ T)).card =
      Fintype.card B * Fintype.card I := by exact_mod_cast card_keys_add_compl A T
  have hB : (0 : ℝ) < Fintype.card B := by
    exact_mod_cast hodd.pos
  by_cases hT : (keys A T).card / (Fintype.card B : ℝ) ≤ |H T|
  · exact ⟨T, hT⟩
  · refine ⟨univ \ T, ?_⟩
    have ht := (div_le_iff₀ hB).not.mp hT
    apply (div_le_iff₀ hB).mpr
    have ha := le_abs_self (H T)
    have hc := neg_abs_le (H (univ \ T))
    nlinarith

/-- Every bit extractor fails on an actual source, with error at least `1/(2*|B|)`.
Only odd branch cardinality and nonempty complementary classes are required. -/
theorem no_bit_extractor [Nonempty I] (A : Finset B) (hA : A.Nonempty)
    (hAc : (univ \ A).Nonempty) (hodd : Odd (Fintype.card B))
    (ext : B × I → Bool) :
    ∃ T : Finset I, (1 : ℝ) / (2 * Fintype.card B) ≤
      dist ((source A hA hAc T).map ext) (PMF.uniformOfFintype Bool) := by
  obtain ⟨T, hT⟩ := exists_signed_imbalance A hodd ext
  have hcard : (0 : ℝ) < (keys A T).card := by
    exact_mod_cast (keys_nonempty A hA hAc T).card_pos
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast hodd.pos
  have hbias : (1 : ℝ) / Fintype.card B ≤
      |∑ k, (source A hA hAc T k).toReal * bitSign (ext k)| := by
    rw [source_expect, abs_div, abs_of_pos hcard]
    apply (le_div_iff₀ hcard).mpr
    nlinarith [(div_le_iff₀ hB).mp hT, div_mul_cancel₀ (1 : ℝ) (ne_of_gt hB)]
  have hd := PMF.abs_sum_mul_sub_le ((source A hA hAc T).map ext)
    (PMF.uniformOfFintype Bool) bitSign (bound := 1)
    (by intro b; cases b <;> norm_num [bitSign])
  have hu : (∑ b : Bool, (PMF.uniformOfFintype Bool b).toReal * bitSign b) = 0 := by
    simp [PMF.uniformOfFintype_apply, bitSign]
  rw [hu, sub_zero, PMF.sum_map_mul] at hd
  refine ⟨T, ?_⟩
  have he : (1 : ℝ) / (2 * Fintype.card B) = (1 / Fintype.card B) / 2 := by ring
  rw [he]
  linarith

/-- The obstruction holds for every positive literal output length, by projecting a bit. -/
theorem no_string_extractor [Nonempty I] (A : Finset B) (hA : A.Nonempty)
    (hAc : (univ \ A).Nonempty) (hodd : Odd (Fintype.card B))
    (ℓ : ℕ) (hℓ : 0 < ℓ) (ext : B × I → (Fin ℓ → Bool)) :
    ∃ T : Finset I, (1 : ℝ) / (2 * Fintype.card B) ≤
      dist ((source A hA hAc T).map ext) (PMF.uniformOfFintype (Fin ℓ → Bool)) := by
  let e : (Fin ℓ → Bool) ≃ Bool × (Fin (ℓ - 1) → Bool) :=
    (Equiv.cast (congrArg (fun n => Fin n → Bool) (by omega : ℓ = (ℓ - 1) + 1))).trans
      (Fin.consEquiv (fun _ : Fin ((ℓ - 1) + 1) => Bool)).symm
  obtain ⟨T, hT⟩ := no_bit_extractor A hA hAc hodd (fun k => (e (ext k)).1)
  have hm := PMF.dist_map_le ((source A hA hAc T).map ext)
    (PMF.uniformOfFintype (Fin ℓ → Bool)) (Prod.fst ∘ e)
  have hu : (PMF.uniformOfFintype (Fin ℓ → Bool)).map (Prod.fst ∘ e) =
      PMF.uniformOfFintype Bool := by
    rw [← PMF.map_comp, PMF.uniformOfFintype_map_equiv, PMF.uniformOfFintype_prod_map_fst]
  rw [hu, PMF.map_comp] at hm
  exact ⟨T, hT.trans hm⟩

/-- Number of source keys whose index lies in `S`. -/
@[expose] def indexCount (A : Finset B) (T S : Finset I) : ℕ :=
  ∑ i ∈ S, if i ∈ T then A.card else (univ \ A).card

/-- The index counts of any partition add to the full support size. -/
theorem indexCount_add_compl (A : Finset B) (T S : Finset I) :
    indexCount A T S + indexCount A T (univ \ S) = (keys A T).card := by
  rw [add_comm, indexCount, indexCount, sum_sdiff (subset_univ S)]
  have hs := sum_keys A T (fun _ => (1 : ℝ))
  simp only [sum_const, nsmul_eq_mul, mul_one] at hs
  have he : (∑ i, if i ∈ T then (A.card : ℝ) else ((univ \ A).card : ℝ)) =
      ((∑ i, if i ∈ T then A.card else (univ \ A).card : ℕ) : ℝ) := by
    simp only [Nat.cast_sum, Nat.cast_ite]
  rw [he] at hs
  exact_mod_cast hs.symm

/-- Boolean index extractors have probability equal to a normalized index count. -/
theorem source_index_probability [Nonempty I] (A : Finset B) (hA : A.Nonempty)
    (hAc : (univ \ A).Nonempty) (T S : Finset I) :
    (((source A hA hAc T).map (fun k => decide (k.2 ∈ S))) true).toReal =
      (indexCount A T S : ℝ) / (keys A T).card := by
  rw [PMF.map_apply_toReal]
  have he : (∑ k, if true = decide (k.2 ∈ S) then
      (source A hA hAc T k).toReal else 0) =
      ∑ k, (source A hA hAc T k).toReal * (if k.2 ∈ S then 1 else 0) := by
    apply sum_congr rfl
    intro k _
    by_cases hk : k.2 ∈ S <;> simp [hk]
  rw [he, source_expect, sum_keys]
  congr 1
  rw [indexCount, Nat.cast_sum]
  conv_rhs => rw [show S = univ.filter (· ∈ S) by ext; simp, sum_filter]
  apply sum_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> by_cases ht : i ∈ T <;> simp [hi, ht]

omit [Fintype I] in
/-- Bounds on the count of source keys at a set of indices. -/
theorem indexCount_bounds (A : Finset B) (T S : Finset I) (a : ℕ)
    (ha : a ≤ A.card ∧ A.card ≤ a + 1)
    (hac : a ≤ (univ \ A).card ∧ (univ \ A).card ≤ a + 1) :
    a * S.card ≤ indexCount A T S ∧ indexCount A T S ≤ (a + 1) * S.card := by
  unfold indexCount
  constructor
  · calc
      _ = ∑ _i ∈ S, a := by simp [mul_comm]
      _ ≤ _ := sum_le_sum fun i _ => by split_ifs <;> omega
  · calc
      _ ≤ ∑ _i ∈ S, (a + 1) := sum_le_sum fun i _ => by split_ifs <;> omega
      _ = _ := by simp [mul_comm]

/-- A balanced index bit attains the matching upper bound when the branch class sizes
are `a` and `a+1`, in either orientation. -/
theorem balanced_index_upper [Nonempty I] (A : Finset B) (hA : A.Nonempty)
    (hAc : (univ \ A).Nonempty) (a : ℕ)
    (hclasses : (A.card = a ∧ (univ \ A).card = a + 1) ∨
      (A.card = a + 1 ∧ (univ \ A).card = a))
    (S : Finset I) (hS : S.card = (univ \ S).card) (T : Finset I) :
    dist ((source A hA hAc T).map (fun k => decide (k.2 ∈ S)))
      (PMF.uniformOfFintype Bool) ≤ (1 : ℝ) / (2 * Fintype.card B) := by
  have hc : A.card + (univ \ A).card = Fintype.card B := by
    rw [card_sdiff_of_subset (subset_univ A), card_univ]
    exact Nat.add_sub_of_le (card_le_univ A)
  have hb : Fintype.card B = 2 * a + 1 := by rcases hclasses with h | h <;> omega
  have ha : a ≤ A.card ∧ A.card ≤ a + 1 := by rcases hclasses with h | h <;> omega
  have hac : a ≤ (univ \ A).card ∧ (univ \ A).card ≤ a + 1 := by
    rcases hclasses with h | h <;> omega
  have hx := indexCount_bounds A T S a ha hac
  have hy := indexCount_bounds A T (univ \ S) a ha hac
  rw [← hS] at hy
  have ht := indexCount_add_compl A T S
  have hd : (0 : ℝ) < (keys A T).card := by
    exact_mod_cast (keys_nonempty A hA hAc T).card_pos
  have hbp : (0 : ℝ) < Fintype.card B := by rw [hb]; positivity
  have hxy : (indexCount A T S : ℝ) + indexCount A T (univ \ S) = (keys A T).card := by
    exact_mod_cast ht
  have hx' : (a : ℝ) * S.card ≤ indexCount A T S ∧
      (indexCount A T S : ℝ) ≤ (a + 1) * S.card := by exact_mod_cast hx
  have hy' : (a : ℝ) * S.card ≤ indexCount A T (univ \ S) ∧
      (indexCount A T (univ \ S) : ℝ) ≤ (a + 1) * S.card := by exact_mod_cast hy
  have hb' : (Fintype.card B : ℝ) = 2 * a + 1 := by exact_mod_cast hb
  rw [PMF.dist_uniformOfFintype_bool, source_index_probability]
  have hr : (indexCount A T S : ℝ) / (keys A T).card - 1 / 2 =
      (2 * indexCount A T S - (keys A T).card) / (2 * (keys A T).card) := by field_simp
  rw [hr]
  apply abs_le.mpr
  constructor
  · rw [← neg_div, div_le_div_iff₀
      (show (0 : ℝ) < 2 * Fintype.card B by positivity)
      (show (0 : ℝ) < 2 * (keys A T).card by positivity)]
    nlinarith
  · rw [div_le_div_iff₀ (show (0 : ℝ) < 2 * (keys A T).card by positivity)
      (show (0 : ℝ) < 2 * Fintype.card B by positivity)]
    nlinarith

/-- On every even nonempty index space, an actual balanced index extractor has error
at most `1/(2*|B|)` on every source and exactly this error on some source.
Together with `no_string_extractor`, this is the tightness assertion of
[Aggarwal2026], Lemmas 4.4 and 5.4, for either orientation of the two classes. -/
theorem exists_tight_index_extractor [Nonempty I] (A : Finset B) (hA : A.Nonempty)
    (hAc : (univ \ A).Nonempty) (a : ℕ)
    (hclasses : (A.card = a ∧ (univ \ A).card = a + 1) ∨
      (A.card = a + 1 ∧ (univ \ A).card = a))
    (heven : Even (Fintype.card I)) :
    ∃ g : I → Bool,
      (univ.filter fun i => g i = true).card = (univ.filter fun i => g i = false).card ∧
      (∀ T, dist ((source A hA hAc T).map (fun k => g k.2))
        (PMF.uniformOfFintype Bool) ≤ (1 : ℝ) / (2 * Fintype.card B)) ∧
      (∃ T, dist ((source A hA hAc T).map (fun k => g k.2))
        (PMF.uniformOfFintype Bool) = (1 : ℝ) / (2 * Fintype.card B)) := by
  obtain ⟨h, hh⟩ := heven
  obtain ⟨S, _, hcard⟩ := exists_subset_card_eq (s := (univ : Finset I)) (n := h) (by
    rw [card_univ, hh]; omega)
  have hS : S.card = (univ \ S).card := by
    rw [card_sdiff_of_subset (subset_univ S), card_univ, hcard, hh]
    omega
  let g : I → Bool := fun i => decide (i ∈ S)
  have hg : (univ.filter fun i => g i = true) = S := by ext; simp [g]
  have hgc : (univ.filter fun i => g i = false) = univ \ S := by ext; simp [g]
  have hup := balanced_index_upper A hA hAc a hclasses S hS
  have hb : Fintype.card B = 2 * a + 1 := by
    have hc : (univ \ A).card = Fintype.card B - A.card := by
      rw [card_sdiff_of_subset (subset_univ A), card_univ]
    have ha := card_le_univ A
    rcases hclasses with h | h <;> omega
  have hodd : Odd (Fintype.card B) := ⟨a, by omega⟩
  obtain ⟨T, hT⟩ := no_bit_extractor A hA hAc hodd (fun k => g k.2)
  exact ⟨g, by rw [hg, hgc]; exact hS, hup, T, le_antisymm (hup T) hT⟩

/-- Exact support of each source: these bounds concern the actual PMF. -/
theorem support_source [Nonempty I] (A : Finset B) (hA : A.Nonempty)
    (hAc : (univ \ A).Nonempty) (T : Finset I) :
    (source A hA hAc T).support = (keys A T : Set (B × I)) := by
  ext k
  simp [source, PMF.mem_support_iff, PMF.uniformOfFinset_apply]

/-- The source's exact min-entropy is the logarithm of its support size. -/
theorem minEntropy_source [Nonempty I] (A : Finset B) (hA : A.Nonempty)
    (hAc : (univ \ A).Nonempty) (T : Finset I) :
    PMF.minEntropy (source A hA hAc T) = Real.logb 2 (keys A T).card :=
  PMF.minEntropy_uniformOfFinset _ _

end Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness.OddSources

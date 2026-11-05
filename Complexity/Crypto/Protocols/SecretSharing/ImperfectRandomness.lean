/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Cslib.Algorithms.Lean.TimeM
public import Complexity.Probability.StatisticalDistance
public import Complexity.Probability.MinEntropy
public import Complexity.Probability.PMF.Uniform
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Map
import Mathlib.Tactic

/-!
# Secret sharing from nonextractable randomness

The three-key construction of [Aggarwal2026], Section 3, separates perfect two-party secret
sharing from deterministic extraction. Keys at each index are central, left, or right. A source
chooses either the central key or both side keys independently at every index, then samples
uniformly from the resulting set. The source choice is arbitrary, rather than randomized.

The algebraic construction below uses an arbitrary field and subtraction. In characteristic two
it is exactly equation (1) of the paper. The probability statements concern the actual uniform
finite sources, without assumptions on the candidate extractor.

The existing `SecretSharing.Scheme` bundles a fixed random generator. Here the dealer must work
with every distribution in an allowed source class, so the results quantify directly over the
sharing maps and these source PMFs. No parallel scheme interface is introduced.

## Main definitions

* `Key`, `Share`, `keys`, `source`: key/share alphabets and the flat source class.
* `first`, `second`, `reconstruct`: the algebraic sharing maps and joint reconstruction.
* `PaddedKey`, `paddedSource`: padding to the power-of-two ambient key alphabet.

## Main results

* `perfect_privacy`: each single-share distribution is independent of the secret.
* `no_bit_extractor`: every deterministic extractor has error at least `1/6` on some source.
* `shareWithFieldCost_spec`, `reconstructWithFieldCost_spec`: the concrete sharing and
  reconstruction routines use at most three and four field operations, respectively.
* `sharing_at_bit_size`: exact alphabet sizes, entropy, reconstruction, privacy and extraction
  obstruction at each admissible field cardinality.

## References

* [D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*][Aggarwal2026],
  Theorem 1.1 and Section 3, submission PDF pp. 2 and 6–7.
-/

public section

open Cslib.Probability
open scoped Cslib.Probability.PMF

namespace Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness

/-- The central, left, and right branch of the construction. -/
inductive Branch
  | central | left | right
  deriving DecidableEq

instance : Fintype Branch :=
  ⟨{.central, .left, .right}, fun b => by cases b <;> simp⟩

/-- A key records its branch and field index. -/
abbrev Key (V : Type*) := Branch × V

/-- A share is either an ordinary field element or a tagged index. -/
abbrev Share (V : Type*) := Sum V V

variable {V : Type*}

/-- The source contains the central key on `T` and both side keys outside `T`. -/
def keys [Fintype V] [DecidableEq V] (T : Finset V) : Finset (Key V) :=
  Finset.univ.filter fun k => (k.1 = Branch.central ↔ k.2 ∈ T)

@[simp] theorem mem_keys [Fintype V] [DecidableEq V] (T : Finset V) (k : Key V) :
    k ∈ keys T ↔ match k.1 with
      | .central => k.2 ∈ T
      | .left | .right => k.2 ∉ T := by
  rcases k with ⟨b, i⟩
  cases b <;> simp [keys]

/-- Sum a score over the source's one-or-two keys at every index. -/
theorem sum_keys [Fintype V] [DecidableEq V] (T : Finset V) (f : Key V → ℝ) :
    ∑ k ∈ keys T, f k =
      ∑ i, if i ∈ T then f (.central, i) else f (.left, i) + f (.right, i) := by
  classical
  rw [keys, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  rw [show (Finset.univ : Finset Branch) = {.central, .left, .right} by decide]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.sum_singleton, reduceCtorEq, or_self, not_false_eq_true]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ T <;> simp [hi]

/-- There are between one and two source keys per index. -/
theorem card_keys [Fintype V] [DecidableEq V] (T : Finset V) :
    (keys T).card = 2 * Fintype.card V - T.card := by
  classical
  have h := sum_keys T (fun _ => (1 : ℝ))
  have hsum : (∑ i : V, if i ∈ T then (1 : ℝ) else 1 + 1) =
      2 * Fintype.card V - T.card := by
    simp_rw [show ∀ i : V, (if i ∈ T then (1 : ℝ) else 1 + 1) =
      2 - (if i ∈ T then 1 else 0) by intro i; split_ifs <;> norm_num]
    simp [Finset.sum_sub_distrib, mul_comm]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [hsum] at h
  have ht := Finset.card_le_univ T
  have hnat : T.card ≤ 2 * Fintype.card V := by omega
  have hh : ((keys T).card : ℝ) = (2 * Fintype.card V - T.card : ℕ) := by
    rw [Nat.cast_sub hnat, Nat.cast_mul, Nat.cast_ofNat]
    exact h
  exact_mod_cast hh

theorem keys_nonempty [Fintype V] [DecidableEq V] [Nonempty V] (T : Finset V) :
    (keys T).Nonempty := by
  classical
  obtain ⟨i⟩ := ‹Nonempty V›
  by_cases hi : i ∈ T
  · exact ⟨(.central, i), by simp [hi]⟩
  · exact ⟨(.left, i), by simp [hi]⟩

/-- The allowed flat source indexed by `T`. -/
noncomputable def source [Fintype V] [DecidableEq V] [Nonempty V] (T : Finset V) : PMF (Key V) :=
  PMF.uniformOfFinset (keys T) (keys_nonempty T)

/-- First share of the three-key scheme. -/
@[expose] def first [Field V] (m : V) : Key V → Share V
  | (.central, i) | (.left, i) => .inl (i + m)
  | (.right, i) => .inr i

/-- Second share of the three-key scheme. -/
@[expose] def second [Field V] (α m : V) : Key V → Share V
  | (.central, i) | (.right, i) => .inl (α * i + m)
  | (.left, i) => .inr i

/-- Reconstruction; the two-tag branch never occurs under the sharing map. -/
@[expose] def reconstruct [Field V] (α : V) : Share V → Share V → V
  | .inl x, .inl y => (α * x - y) / (α - 1)
  | .inl x, .inr i => x - i
  | .inr i, .inl y => y - α * i
  | .inr _, .inr _ => 0

/-- Perfect correctness, including keys outside any particular allowed source. -/
theorem reconstruct_shares [Field V] {α : V} (hα : α ≠ 1) (m : V) (k : Key V) :
    reconstruct α (first m k) (second α m k) = m := by
  rcases k with ⟨b, i⟩
  cases b <;> simp only [first, second, reconstruct]
  · apply (div_eq_iff (sub_ne_zero.mpr hα)).mpr
    ring
  · ring
  · ring

/-- The number of source keys is at least the number of indices. -/
theorem card_le_card_keys [Fintype V] [DecidableEq V] (T : Finset V) :
    Fintype.card V ≤ (keys T).card := by
  rw [card_keys]
  have := Finset.card_le_univ T
  omega

/-- The number of source keys is at most twice the number of indices. -/
theorem card_keys_le [Fintype V] [DecidableEq V] (T : Finset V) :
    (keys T).card ≤ 2 * Fintype.card V := by
  rw [card_keys]
  omega

/-- Opposite sources partition all three keys at every index. -/
theorem card_keys_add_compl [Fintype V] [DecidableEq V] (T : Finset V) :
    (keys T).card + (keys (Finset.univ \ T)).card = 3 * Fintype.card V := by
  rw [card_keys, card_keys, Finset.card_sdiff_of_subset (Finset.subset_univ T),
    Finset.card_univ]
  have := Finset.card_le_univ T
  omega

/-- Every source has min-entropy at least the logarithm of the field size. -/
theorem source_minEntropy [Fintype V] [DecidableEq V] [Nonempty V] (T : Finset V) :
    Real.logb 2 (Fintype.card V) ≤ PMF.minEntropy (source T) := by
  rw [source, PMF.minEntropy_uniformOfFinset]
  exact Real.logb_le_logb_of_le (by norm_num)
    (by exact_mod_cast Fintype.card_pos (α := V))
    (by exact_mod_cast card_le_card_keys T)

/-- A field with at least three elements admits a valid nonzero slope different from one. -/
theorem exists_slope [Field V] [Fintype V]
    (hcard : 2 < Fintype.card V) : ∃ α : V, α ≠ 0 ∧ α ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset V) ⊆ {0, 1} := by
    intro α _
    by_cases hα : α = 0
    · simp [hα]
    · simp [h α hα]
  have hle := Finset.card_le_card hsub
  have hpair : ({0, 1} : Finset V).card = 2 := by simp
  rw [Finset.card_univ, hpair] at hle
  omega

/-- Expectation under the flat source is the normalized sum over its keys. -/
theorem source_expect [Fintype V] [DecidableEq V] [Nonempty V]
    (T : Finset V) (f : Key V → ℝ) :
    (∑ k, (source T k).toReal * f k) =
      (∑ k ∈ keys T, f k) / (keys T).card := by
  classical
  simp only [source, PMF.uniformOfFinset_apply]
  simp_rw [apply_ite ENNReal.toReal, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_zero, ite_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  have hs : Finset.univ.filter (fun k => k ∈ keys T) = keys T := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hs]
  ring

private theorem sum_first [Field V] [Fintype V] [DecidableEq V]
    (T : Finset V) (m : V) (score : Share V → ℝ) :
    (∑ k ∈ keys T, score (first m k)) =
      (∑ i : V, score (.inl i)) + ∑ i ∈ Finset.univ \ T, score (.inr i) := by
  rw [sum_keys]
  have hsum : (∑ i : V, score (.inl (i + m))) = ∑ i : V, score (.inl i) :=
    Equiv.sum_comp (Equiv.addRight m) (fun i : V => score (.inl i))
  calc
    _ = (∑ i : V, score (.inl (i + m))) +
        ∑ i ∈ Finset.univ \ T, score (.inr i) := by
      have hc : Finset.univ \ T = Finset.univ.filter (fun i : V => i ∉ T) := by
        ext i
        simp
      rw [hc, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ T <;> simp [first, hi]
    _ = _ := by rw [hsum]

private theorem sum_second [Field V] [Fintype V] [DecidableEq V]
    (T : Finset V) {α : V} (hα : α ≠ 0) (m : V) (score : Share V → ℝ) :
    (∑ k ∈ keys T, score (second α m k)) =
      (∑ i : V, score (.inl i)) + ∑ i ∈ Finset.univ \ T, score (.inr i) := by
  rw [sum_keys]
  have hsum : (∑ i : V, score (.inl (α * i + m))) = ∑ i : V, score (.inl i) :=
    Equiv.sum_comp ((Equiv.mulLeft₀ α hα).trans (Equiv.addRight m))
      (fun i : V => score (.inl i))
  calc
    _ = (∑ i : V, score (.inl (α * i + m))) +
        ∑ i ∈ Finset.univ \ T, score (.inr i) := by
      have hc : Finset.univ \ T = Finset.univ.filter (fun i : V => i ∉ T) := by
        ext i
        simp
      rw [hc, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ T <;> simp [second, hi, add_comm]
    _ = _ := by rw [hsum]

/-- A single share has exactly the same distribution for every message. -/
theorem perfect_privacy [Field V] [Fintype V] [DecidableEq V]
    (T : Finset V) {α : V} (hα : α ≠ 0) (m m' : V) :
    (source T).map (first m) = (source T).map (first m') ∧
      (source T).map (second α m) = (source T).map (second α m') := by
  classical
  have heq {f g : Key V → Share V}
      (h : ∀ score : Share V → ℝ, (∑ k ∈ keys T, score (f k)) =
        ∑ k ∈ keys T, score (g k)) : (source T).map f = (source T).map g := by
    ext x
    apply (ENNReal.toReal_eq_toReal_iff' ((source T).map f |>.apply_ne_top x)
      ((source T).map g |>.apply_ne_top x)).mp
    have h' := congrArg (fun z : ℝ => z / (keys T).card) (h (fun y => if y = x then 1 else 0))
    rw [PMF.map_apply_toReal, PMF.map_apply_toReal]
    simpa only [← source_expect, mul_ite, mul_one, mul_zero, eq_comm] using h'
  exact ⟨heq (fun score => by rw [sum_first, sum_first]),
    heq (fun score => by rw [sum_second T hα, sum_second T hα])⟩

/-- The sign score of a candidate output bit. -/
def bitSign (b : Bool) : ℝ := if b then 1 else -1

/-- No labelling of the three branches can balance both complementary source choices.
This is the parity argument in [Aggarwal2026], Lemma 3.3. -/
theorem exists_signed_imbalance [Fintype V] [DecidableEq V]
    (ext : Key V → Bool) :
    ∃ T : Finset V, (keys T).card / (3 : ℝ) ≤
      |∑ k ∈ keys T, bitSign (ext k)| := by
  classical
  let v : V → ℝ := fun i => bitSign (ext (.central, i)) -
    bitSign (ext (.left, i)) - bitSign (ext (.right, i))
  let T := Finset.univ.filter fun i => 0 < v i
  have hv (i : V) : 1 ≤ |v i| := by
    dsimp [v, bitSign]
    cases ext (.central, i) <;> cases ext (.left, i) <;>
      cases ext (.right, i) <;> norm_num
  let H : Finset V → ℝ := fun S => ∑ k ∈ keys S, bitSign (ext k)
  have hdiff : H T - H (Finset.univ \ T) = ∑ i, |v i| := by
    dsimp [H]
    rw [sum_keys, sum_keys, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 < v i
    · have hit : i ∈ T := by simp [T, hi]
      simp only [hit, Finset.mem_sdiff, Finset.mem_univ, not_true_eq_false, and_false,
        ite_true, ite_false]
      rw [abs_of_pos hi]
      dsimp [v]
      ring
    · have hit : i ∉ T := by simp [T, hi]
      simp only [hit, Finset.mem_sdiff, Finset.mem_univ, not_false_eq_true, and_self,
        ite_true, ite_false]
      rw [abs_of_nonpos (le_of_not_gt hi)]
      dsimp [v]
      ring
  have hlower : (Fintype.card V : ℝ) ≤ H T - H (Finset.univ \ T) := by
    rw [hdiff]
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hv i)
  have hcards : ((keys T).card : ℝ) + (keys (Finset.univ \ T)).card =
      3 * Fintype.card V := by exact_mod_cast card_keys_add_compl T
  by_cases hT : (keys T).card / (3 : ℝ) ≤ |H T|
  · exact ⟨T, hT⟩
  · refine ⟨Finset.univ \ T, ?_⟩
    have ht := lt_of_not_ge hT
    have habs := le_abs_self (H T)
    have habsc := neg_abs_le (H (Finset.univ \ T))
    dsimp [H] at *
    linarith

/-- Every deterministic bit extractor has error at least `1 / 6` on an allowed flat source.
This formalizes [Aggarwal2026], Lemma 3.3, using the library's statistical distance. -/
theorem no_bit_extractor [Fintype V] [DecidableEq V] [Nonempty V]
    (ext : Key V → Bool) :
    ∃ T : Finset V, (1 : ℝ) / 6 ≤
      dist ((source T).map ext) (PMF.uniformOfFintype Bool) := by
  classical
  obtain ⟨T, hT⟩ := exists_signed_imbalance ext
  have hcard : (0 : ℝ) < (keys T).card := by
    exact_mod_cast (keys_nonempty T).card_pos
  have hbias : (1 : ℝ) / 3 ≤
      |∑ k, (source T k).toReal * bitSign (ext k)| := by
    rw [source_expect, abs_div, abs_of_pos hcard]
    apply (le_div_iff₀ hcard).mpr
    linarith
  have hdist := PMF.abs_sum_mul_sub_le ((source T).map ext)
    (PMF.uniformOfFintype Bool) bitSign (bound := 1)
    (by intro b; cases b <;> norm_num [bitSign])
  have hunif : (∑ b : Bool, (PMF.uniformOfFintype Bool b).toReal * bitSign b) = 0 := by
    simp [PMF.uniformOfFintype_apply, bitSign]
  rw [hunif, sub_zero, PMF.sum_map_mul] at hdist
  exact ⟨T, by linarith⟩

/-- Failure for one output bit also rules out extraction to any nonempty product of bits. -/
theorem no_product_extractor [Fintype V] [DecidableEq V] [Nonempty V]
    {O : Type*} [Fintype O] [Nonempty O] (ext : Key V → Bool × O) :
    ∃ T : Finset V, (1 : ℝ) / 6 ≤
      dist ((source T).map ext) (PMF.uniformOfFintype (Bool × O)) := by
  obtain ⟨T, hT⟩ := no_bit_extractor (fun k => (ext k).1)
  have hmap := PMF.dist_map_le ((source T).map ext)
    (PMF.uniformOfFintype (Bool × O)) Prod.fst
  rw [PMF.map_comp, PMF.uniformOfFintype_prod_map_fst] at hmap
  exact ⟨T, hT.trans hmap⟩

/-- The source-class separation: one fixed scheme is perfectly correct and perfectly private
for every source, while each deterministic bit extractor fails on one of those sources.
The finite-field formulation is Section 3 of [Aggarwal2026], before the bit encoding in §3.2. -/
theorem sharing_without_extraction [Field V] [Fintype V] [DecidableEq V]
    (hcard : 2 < Fintype.card V) :
    ∃ α : V, (∀ m k, reconstruct α (first m k) (second α m k) = m) ∧
      (∀ T m m', (source T).map (first m) = (source T).map (first m') ∧
        (source T).map (second α m) = (source T).map (second α m')) ∧
      (∀ T : Finset V, Real.logb 2 (Fintype.card V) ≤ PMF.minEntropy (source T)) ∧
      (∀ ext : Key V → Bool, ∃ T, (1 : ℝ) / 6 ≤
        dist ((source T).map ext) (PMF.uniformOfFintype Bool)) := by
  obtain ⟨α, hα0, hα1⟩ := exists_slope hcard
  exact ⟨α, reconstruct_shares hα1, fun T m m' => perfect_privacy T hα0 m m',
    source_minEntropy, no_bit_extractor⟩

/-- A fourth, unused branch gives the ambient key alphabet of Section 3.2. -/
abbrev PaddedKey (V : Type*) := Option Branch × V

/-- Include the three used branches in the four-branch ambient key alphabet. -/
def pad (k : Key V) : PaddedKey V := (some k.1, k.2)

private theorem pad_injective : Function.Injective (pad : Key V → PaddedKey V) := by
  rintro ⟨b, i⟩ ⟨b', i'⟩ h
  simpa [pad] using h

/-- Allowed keys in the ambient four-branch alphabet; the fourth branch has zero mass. -/
def paddedKeys [Fintype V] [DecidableEq V] (T : Finset V) : Finset (PaddedKey V) :=
  (keys T).image pad

/-- A flat source on the four-branch key alphabet. -/
noncomputable def paddedSource [Fintype V] [DecidableEq V] [Nonempty V]
    (T : Finset V) : PMF (PaddedKey V) :=
  PMF.uniformOfFinset (paddedKeys T) ((keys_nonempty T).image pad)

/-- Every padded source has at least one allowed key. -/
theorem paddedKeys_nonempty [Fintype V] [DecidableEq V] [Nonempty V]
    (T : Finset V) : (paddedKeys T).Nonempty :=
  (keys_nonempty T).image pad

/-- Padding preserves the number of allowed keys. -/
theorem card_paddedKeys [Fintype V] [DecidableEq V] (T : Finset V) :
    (paddedKeys T).card = 2 * Fintype.card V - T.card := by
  rw [paddedKeys, Finset.card_image_of_injective _ pad_injective, card_keys]

open scoped Classical in
/-- The padded source is uniform on precisely its allowed keys. -/
theorem paddedSource_apply [Fintype V] [DecidableEq V] [Nonempty V]
    (T : Finset V) (k : PaddedKey V) :
    paddedSource T k = if k ∈ paddedKeys T then (↑(paddedKeys T).card : ENNReal)⁻¹ else 0 := by
  have h := PMF.uniformOfFinset_apply (paddedKeys T) ((keys_nonempty T).image pad) k
  by_cases hk : k ∈ paddedKeys T <;>
    simpa only [paddedSource, hk, ite_true, ite_false] using h

/-- Padding is an injective re-encoding of the actual uniform source. -/
theorem paddedSource_eq_map [Fintype V] [DecidableEq V] [Nonempty V]
    (T : Finset V) : paddedSource T = (source T).map pad := by
  classical
  ext x
  rw [PMF.map_apply, tsum_fintype]
  rcases x with ⟨b, i⟩
  cases b with
  | none =>
    simp [paddedSource, paddedKeys, pad, PMF.uniformOfFinset_apply]
  | some b =>
    rw [Finset.sum_eq_single (b, i)]
    · simp [paddedSource, paddedKeys, pad, source,
        Finset.card_image_of_injective _ pad_injective]
    · intro k _ hk
      have hne : (some b, i) ≠ pad k := by
        intro heq
        apply hk
        exact pad_injective heq.symm
      simp [hne]
    · simp

/-- Perfect reconstruction also holds on the unused fourth branch. -/
def paddedFirst [Field V] (m : V) (k : PaddedKey V) : Share V :=
  first m (k.1.getD .central, k.2)

/-- The fourth branch duplicates the central sharing rule. -/
def paddedSecond [Field V] (α m : V) (k : PaddedKey V) : Share V :=
  second α m (k.1.getD .central, k.2)

/-- Correctness on the complete four-branch key alphabet. -/
theorem reconstruct_paddedShares [Field V] {α : V} (hα : α ≠ 1)
    (m : V) (k : PaddedKey V) :
    reconstruct α (paddedFirst m k) (paddedSecond α m k) = m :=
  reconstruct_shares hα m _

/-- Both padded marginals are exactly message independent. -/
theorem padded_perfect_privacy [Field V] [Fintype V] [DecidableEq V]
    (T : Finset V) {α : V} (hα : α ≠ 0) (m m' : V) :
    (paddedSource T).map (paddedFirst m) = (paddedSource T).map (paddedFirst m') ∧
      (paddedSource T).map (paddedSecond α m) =
        (paddedSource T).map (paddedSecond α m') := by
  simpa only [paddedSource_eq_map, PMF.map_comp, Function.comp_def, pad,
    paddedFirst, paddedSecond, Option.getD_some] using perfect_privacy T hα m m'

/-- Padding does not change the entropy of the flat source. -/
theorem paddedSource_minEntropy [Fintype V] [DecidableEq V] [Nonempty V]
    (T : Finset V) : Real.logb 2 (Fintype.card V) ≤ PMF.minEntropy (paddedSource T) := by
  change Real.logb 2 (Fintype.card V) ≤ PMF.minEntropy
    (PMF.uniformOfFinset ((keys T).image pad) ((keys_nonempty T).image pad))
  rw [PMF.minEntropy_uniformOfFinset, Finset.card_image_of_injective _ pad_injective]
  simpa only [source, PMF.minEntropy_uniformOfFinset] using source_minEntropy T

/-- No extractor on the full ambient key alphabet can evade the lower bound. -/
theorem padded_no_bit_extractor [Fintype V] [DecidableEq V] [Nonempty V]
    (ext : PaddedKey V → Bool) :
    ∃ T : Finset V, (1 : ℝ) / 6 ≤
      dist ((paddedSource T).map ext) (PMF.uniformOfFintype Bool) := by
  obtain ⟨T, hT⟩ := no_bit_extractor (ext ∘ pad)
  exact ⟨T, by simpa only [paddedSource_eq_map, PMF.map_comp] using hT⟩

/-- The ambient key and share alphabet sizes are exactly those of Theorem 1.1. -/
theorem alphabet_cardinalities [Fintype V] {b : ℕ} (hV : Fintype.card V = 2 ^ b) :
    Fintype.card (PaddedKey V) = 2 ^ (b + 2) ∧
      Fintype.card (Share V) = 2 ^ (b + 1) := by
  have hbranch : Fintype.card Branch = 3 := by decide
  simp [PaddedKey, Share, Fintype.card_prod, Fintype.card_option, Fintype.card_sum,
    hbranch, hV, pow_add]
  constructor <;> omega

/-- The same lower bound applies to every output with at least one bit. -/
theorem padded_no_product_extractor [Fintype V] [DecidableEq V] [Nonempty V]
    {O : Type*} [Fintype O] [Nonempty O] (ext : PaddedKey V → Bool × O) :
    ∃ T : Finset V, (1 : ℝ) / 6 ≤
      dist ((paddedSource T).map ext) (PMF.uniformOfFintype (Bool × O)) := by
  obtain ⟨T, hT⟩ := no_product_extractor (ext ∘ pad)
  exact ⟨T, by simpa only [paddedSource_eq_map, PMF.map_comp] using hT⟩

/-- Exact alphabet sizes and the source-class separation of [Aggarwal2026], Theorem 1.1.
The alphabets are finite-field alphabets of the indicated cardinalities, before choosing
bijections to bit strings. No cost bound for field operations is asserted here. -/
theorem sharing_at_bit_size [Field V] [Fintype V] [DecidableEq V]
    {b : ℕ} (hb : 2 ≤ b) (hV : Fintype.card V = 2 ^ b) :
    Fintype.card (PaddedKey V) = 2 ^ (b + 2) ∧
      Fintype.card (Share V) = 2 ^ (b + 1) ∧
      ∃ α : V,
        (∀ m k, reconstruct α (paddedFirst m k) (paddedSecond α m k) = m) ∧
        (∀ T m m', (paddedSource T).map (paddedFirst m) =
          (paddedSource T).map (paddedFirst m') ∧
          (paddedSource T).map (paddedSecond α m) =
            (paddedSource T).map (paddedSecond α m')) ∧
        (∀ T : Finset V, (b : ℝ) ≤ PMF.minEntropy (paddedSource T)) ∧
        (∀ ext : PaddedKey V → Bool, ∃ T, (1 : ℝ) / 6 ≤
          dist ((paddedSource T).map ext) (PMF.uniformOfFintype Bool)) := by
  have hcard : 2 < Fintype.card V := by
    rw [hV]
    have hpow : 2 ^ 2 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb
    omega
  obtain ⟨α, hα0, hα1⟩ := exists_slope hcard
  obtain ⟨hk, hs⟩ := alphabet_cardinalities hV
  refine ⟨hk, hs, α, reconstruct_paddedShares hα1,
    fun T m m' => padded_perfect_privacy T hα0 m m', ?_, padded_no_bit_extractor⟩
  intro T
  have hent := paddedSource_minEntropy T
  rw [hV, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), mul_one] at hent
  exact hent

/-- Both shares, charging one unit for each field addition or multiplication.
Tag inspection, pairing and field-coordinate access are free, as in Theorem 1.1's
field-operation model; this is not a bit-operation count. -/
@[expose] def shareWithFieldCost [Field V] (α m : V) (k : Key V) :
    Cslib.Algorithms.Lean.TimeM ℕ (Share V × Share V) := do
  match k with
  | (.central, i) =>
    let x ← (⟨i + m, 1⟩ : Cslib.Algorithms.Lean.TimeM ℕ V)
    let y ← (⟨α * i, 1⟩ : Cslib.Algorithms.Lean.TimeM ℕ V)
    let z ← (⟨y + m, 1⟩ : Cslib.Algorithms.Lean.TimeM ℕ V)
    pure (.inl x, .inl z)
  | (.left, i) =>
    let x ← (⟨i + m, 1⟩ : Cslib.Algorithms.Lean.TimeM ℕ V)
    pure (.inl x, .inr i)
  | (.right, i) =>
    let y ← (⟨α * i, 1⟩ : Cslib.Algorithms.Lean.TimeM ℕ V)
    let z ← (⟨y + m, 1⟩ : Cslib.Algorithms.Lean.TimeM ℕ V)
    pure (.inr i, .inl z)

/-- The charged sharing routine computes the actual two shares using at most
three field operations, independently of field size and source choice. -/
theorem shareWithFieldCost_spec [Field V] (α m : V) (k : Key V) :
    (shareWithFieldCost α m k).ret = (first m k, second α m k) ∧
      (shareWithFieldCost α m k).time ≤ 3 := by
  rcases k with ⟨b, i⟩
  cases b <;> exact ⟨rfl, by norm_num [shareWithFieldCost,
    Cslib.Algorithms.Lean.TimeM.bind, Cslib.Algorithms.Lean.TimeM.pure]⟩

/-- The three-operation sharing bound also covers every key of the padded ambient alphabet. -/
theorem shareWithFieldCost_padded_spec [Field V] (α m : V) (k : PaddedKey V) :
    (shareWithFieldCost α m (k.1.getD .central, k.2)).ret =
        (paddedFirst m k, paddedSecond α m k) ∧
      (shareWithFieldCost α m (k.1.getD .central, k.2)).time ≤ 3 :=
  shareWithFieldCost_spec α m _

/-- Reconstruction with a unit charge for every field multiplication, subtraction or division.
A division is one field operation, not a constant number of bit operations. -/
@[expose] def reconstructWithFieldCost [Field V] (α : V) (s t : Share V) :
    Cslib.Algorithms.Lean.TimeM ℕ V := do
  match s, t with
  | .inl x, .inl y =>
    let a ← (⟨α * x, 1⟩ : Cslib.Algorithms.Lean.TimeM ℕ V)
    let z ← (⟨a - y, 1⟩ : Cslib.Algorithms.Lean.TimeM ℕ V)
    let d ← (⟨α - 1, 1⟩ : Cslib.Algorithms.Lean.TimeM ℕ V)
    (⟨z / d, 1⟩ : Cslib.Algorithms.Lean.TimeM ℕ V)
  | .inl x, .inr i => (⟨x - i, 1⟩ : Cslib.Algorithms.Lean.TimeM ℕ V)
  | .inr i, .inl y =>
    let z ← (⟨α * i, 1⟩ : Cslib.Algorithms.Lean.TimeM ℕ V)
    (⟨y - z, 1⟩ : Cslib.Algorithms.Lean.TimeM ℕ V)
  | .inr _, .inr _ => pure 0

/-- The charged reconstruction routine agrees everywhere with the scheme and costs
at most four field operations. -/
theorem reconstructWithFieldCost_spec [Field V] (α : V) (s t : Share V) :
    (reconstructWithFieldCost α s t).ret = reconstruct α s t ∧
      (reconstructWithFieldCost α s t).time ≤ 4 := by
  cases s <;> cases t <;> exact ⟨rfl, by norm_num [reconstructWithFieldCost,
    Cslib.Algorithms.Lean.TimeM.bind, Cslib.Algorithms.Lean.TimeM.pure]⟩

end Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness

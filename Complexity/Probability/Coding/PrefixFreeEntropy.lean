/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.List.Binary
public import Complexity.Init
public import Complexity.Probability.Entropy
public import Mathlib.InformationTheory.Coding.Kraft
import Complexity.Foundations.Data.Nat.Bits
import Complexity.Probability.Divergence
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Map

/-!
# Prefix-Free Combinators and the Kraft–Entropy Compression Bound

This module connects Mathlib's `InformationTheory.IsPrefixFree` and Kraft inequality
(`Mathlib/InformationTheory/Coding/Kraft.lean`) to finite-distribution Shannon entropy and
conditional entropy (`Complexity/Probability/Entropy.lean`, `Divergence.lean`), and supplies
reusable self-delimiting binary primitives (`finIdxBits`, `eliasGamma`) and concatenation
combinators for variable-length communication transcripts.

## Main definitions

* `Cslib.Probability.Coding.finIdxBits`: fixed-width `⌈log₂ K⌉`-bit binary encoding of `Fin K`.
* `Cslib.Probability.Coding.eliasGamma`, `Cslib.Probability.Coding.decodeEliasGamma`: Peter Elias's
  1975 prefix-free gamma code for positive integers `m ≥ 1` of length `2 * ⌊log₂ m⌋ + 1` and its
  left inverse.

## Main results

* `InformationTheory.IsPrefixFree.bind_append`,
  `Cslib.Probability.Coding.isPrefixFree_biUnion_append`,
  `Cslib.Probability.Coding.isPrefixFree_image_append`,
  `Cslib.Probability.Coding.isPrefixFree_prod_append`,
  `Cslib.Probability.Coding.injOn_append`,
  `Cslib.Probability.Coding.injOn_prod_append`: sequential dependent concatenation of prefix-free
  codes remains prefix-free and uniquely decomposable.
* `Cslib.Probability.Coding.finIdxBits_injective`,
  `Cslib.Probability.Coding.isPrefixFree_range_finIdxBits`,
  `Cslib.Probability.Coding.clog_two_lt_logb_add_one`: fixed-width index code properties and ceiling
  slack `< log₂ K + 1`.
* `Cslib.Probability.Coding.decodeEliasGamma_eliasGamma`,
  `Cslib.Probability.Coding.injOn_eliasGamma`,
  `Cslib.Probability.Coding.isPrefixFree_range_eliasGamma`,
  `Cslib.Probability.Coding.isPrefixFree_eliasGamma`: Elias gamma length, left-invertibility,
  injectivity on `{m | 1 ≤ m}`, and prefix-freeness.
* `Cslib.Probability.Coding.entropy_le_expected_length_of_isPrefixFree`,
  `Cslib.Probability.Coding.conditionalEntropy_le_expected_length_of_isPrefixFree`,
  `Cslib.Probability.Coding.conditionalEntropy_map_le_expected_length_of_isPrefixFree`: Kraft–Gibbs
  source coding lower bounds ([CoverThomas2006], Theorem 5.3.1).

## References

* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006], Section 5.2 and
  Theorem 5.3.1.
* [L. G. Kraft, *A Device for Quantizing, Grouping, and Coding Amplitude-Modulated
  Pulses*][Kraft1949].
* Peter Elias, *Universal Codeword Sets and Representations of the Integers*, IEEE Transactions on
  Information Theory 21(2):194–203, 1975.
-/

public section

open scoped BigOperators ENNReal

/-- Dependent concatenation of a prefix-free prefix set `S` with fiberwise prefix-free suffix sets
`T u` is prefix-free. -/
theorem _root_.InformationTheory.IsPrefixFree.bind_append {ι : Type*}
    {S : Set (List ι)} {T : List ι → Set (List ι)}
    (hS : InformationTheory.IsPrefixFree S)
    (hT : ∀ u ∈ S, InformationTheory.IsPrefixFree (T u)) :
    InformationTheory.IsPrefixFree {w | ∃ u ∈ S, ∃ v ∈ T u, w = u ++ v} := by
  rintro _ ⟨u₁, hu₁, v₁, hv₁, rfl⟩ _ ⟨u₂, hu₂, v₂, hv₂, rfl⟩ ⟨r, hr⟩
  rw [List.append_assoc] at hr
  have hu : u₁ = u₂ := by
    rcases List.append_eq_append_iff.mp hr with ⟨t, hu₂', -⟩ | ⟨t, hu₁', -⟩
    · exact hS u₁ hu₁ u₂ hu₂ ⟨t, hu₂'.symm⟩
    · exact (hS u₂ hu₂ u₁ hu₁ ⟨t, hu₁'.symm⟩).symm
  subst hu
  have hv_pref : v₁ <+: v₂ := ⟨r, List.append_cancel_left hr⟩
  rw [hT u₁ hu₁ v₁ hv₁ v₂ hv₂ hv_pref]

namespace Cslib.Probability.Coding

open InformationTheory Cslib.Probability.PMF

/-! ### Self-delimiting and prefix-free combinators -/

/-- Equal concatenations with prefixes drawn from a prefix-free set have equal prefix and suffix. -/
theorem append_inj_of_isPrefixFree {ι : Type*} {S : Set (List ι)}
    (hS : IsPrefixFree S) {u₁ u₂ v₁ v₂ : List ι}
    (hu₁ : u₁ ∈ S) (hu₂ : u₂ ∈ S) (heq : u₁ ++ v₁ = u₂ ++ v₂) :
    u₁ = u₂ ∧ v₁ = v₂ := by
  have hu : u₁ = u₂ := by
    rcases List.append_eq_append_iff.mp heq with ⟨t, hu₂', -⟩ | ⟨t, hu₁', -⟩
    · exact hS u₁ hu₁ u₂ hu₂ ⟨t, hu₂'.symm⟩
    · exact (hS u₂ hu₂ u₁ hu₁ ⟨t, hu₁'.symm⟩).symm
  subst hu
  exact ⟨rfl, List.append_cancel_left heq⟩

/-- Finite `Finset.biUnion` form of `IsPrefixFree.bind_append`. -/
theorem isPrefixFree_biUnion_append {ι : Type*} [DecidableEq ι]
    {S : Finset (List ι)} {T : List ι → Finset (List ι)}
    (hS : IsPrefixFree (S : Set (List ι)))
    (hT : ∀ u ∈ S, IsPrefixFree (T u : Set (List ι))) :
    IsPrefixFree ((S.biUnion fun u => (T u).image (u ++ ·) : Finset (List ι)) : Set (List ι)) := by
  refine (hS.bind_append (T := fun u => (T u : Set (List ι))) hT).anti ?_
  intro w hw
  simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image] at hw
  rcases hw with ⟨u, hu, v, hv, rfl⟩
  exact ⟨u, hu, v, hv, rfl⟩

/-- Sequential encoding `x ↦ enc₁ x ++ enc₂ x` on `D` is prefix-free whenever `enc₁ '' D` is
prefix-free and `enc₂` is prefix-free on each `enc₁`-fiber of `D`. -/
theorem isPrefixFree_image_append {γ ι : Type*} {D : Set γ}
    {enc₁ enc₂ : γ → List ι}
    (h₁ : IsPrefixFree (enc₁ '' D))
    (h₂ : ∀ x ∈ D, IsPrefixFree (enc₂ '' {y ∈ D | enc₁ y = enc₁ x})) :
    IsPrefixFree ((fun x => enc₁ x ++ enc₂ x) '' D) := by
  have hbind : IsPrefixFree
      {w | ∃ u ∈ enc₁ '' D, ∃ v ∈ enc₂ '' {y ∈ D | enc₁ y = u}, w = u ++ v} := by
    refine h₁.bind_append ?_
    rintro _ ⟨x, hx, rfl⟩
    exact h₂ x hx
  refine hbind.anti ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨enc₁ x, ⟨x, hx, rfl⟩, enc₂ x, ⟨x, ⟨hx, rfl⟩, rfl⟩, rfl⟩

/-- Sequential encoding `x ↦ enc₁ x ++ enc₂ x` is injective on `D` whenever `enc₁ '' D` is
prefix-free and the pair `(enc₁, enc₂)` is injective on `D`. -/
theorem injOn_append {γ ι : Type*} {D : Set γ} {enc₁ enc₂ : γ → List ι}
    (h₁ : IsPrefixFree (enc₁ '' D))
    (hinj : Set.InjOn (fun x => (enc₁ x, enc₂ x)) D) :
    Set.InjOn (fun x => enc₁ x ++ enc₂ x) D := by
  intro x hx y hy heq
  obtain ⟨hu, hv⟩ := append_inj_of_isPrefixFree h₁ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ heq
  exact hinj hx hy (Prod.ext hu hv)

/-- Dependent pair encoding `(a, b) ↦ enc₁ a ++ enc₂ a b` is injective on `D : Set (α × β)` when
`enc₁` is injective and prefix-free on `Prod.fst '' D` and `enc₂ a` is injective on each slice. -/
theorem injOn_prod_append {α β ι : Type*} {D : Set (α × β)}
    {enc₁ : α → List ι} {enc₂ : α → β → List ι}
    (hinj₁ : Set.InjOn enc₁ (Prod.fst '' D))
    (hpf₁ : IsPrefixFree (enc₁ '' (Prod.fst '' D)))
    (hinj₂ : ∀ a, Set.InjOn (enc₂ a) {b | (a, b) ∈ D}) :
    Set.InjOn (fun p : α × β => enc₁ p.1 ++ enc₂ p.1 p.2) D := by
  have hpf' : IsPrefixFree ((fun p : α × β => enc₁ p.1) '' D) := by
    rwa [← Set.image_image]
  refine injOn_append hpf' fun p₁ hp₁ p₂ hp₂ heq => ?_
  rcases Prod.mk.inj heq with ⟨hu, hv⟩
  have ha : p₁.1 = p₂.1 := hinj₁ ⟨p₁, hp₁, rfl⟩ ⟨p₂, hp₂, rfl⟩ hu
  rcases p₁ with ⟨a₁, b₁⟩
  rcases p₂ with ⟨a₂, b₂⟩
  dsimp only at ha hv
  subst ha
  exact Prod.ext rfl (hinj₂ a₁ hp₁ hp₂ hv)

/-- Dependent pair encoding `(a, b) ↦ enc₁ a ++ enc₂ a b` has prefix-free image on `D` when `enc₁`
is injective and prefix-free on `Prod.fst '' D` and `enc₂ a` is prefix-free on each slice. -/
theorem isPrefixFree_prod_append {α β ι : Type*} {D : Set (α × β)}
    {enc₁ : α → List ι} {enc₂ : α → β → List ι}
    (hinj₁ : Set.InjOn enc₁ (Prod.fst '' D))
    (hpf₁ : IsPrefixFree (enc₁ '' (Prod.fst '' D)))
    (hpf₂ : ∀ a, IsPrefixFree (enc₂ a '' {b | (a, b) ∈ D})) :
    IsPrefixFree ((fun p : α × β => enc₁ p.1 ++ enc₂ p.1 p.2) '' D) := by
  have hpf' : IsPrefixFree ((fun p : α × β => enc₁ p.1) '' D) := by
    rwa [← Set.image_image]
  refine isPrefixFree_image_append hpf' fun p hp => ?_
  refine (hpf₂ p.1).anti ?_
  rintro _ ⟨q, ⟨hqD, hq_eq⟩, rfl⟩
  have hqa : q.1 = p.1 := hinj₁ ⟨q, hqD, rfl⟩ ⟨p, hp, rfl⟩ hq_eq
  exact ⟨q.2, hqa ▸ hqD, by dsimp only; rw [hqa]⟩

/-- Any set of words of a common fixed length `k` is prefix-free. -/
theorem isPrefixFree_of_length_eq {ι : Type*} {S : Set (List ι)} {k : ℕ}
    (hlen : ∀ w ∈ S, w.length = k) : IsPrefixFree S := by
  intro u hu v hv ⟨r, hr⟩
  have hlen_eq : (u ++ r).length = u.length := by rw [hr, hlen v hv, hlen u hu]
  rw [List.length_append] at hlen_eq
  have hr_nil : r = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [← hr, hr_nil, List.append_nil]

/-! ### Fixed-width binary index code (`finIdxBits`) -/

/-- Fixed-width binary encoding of `i : Fin K` in `⌈log₂ K⌉` little-endian bits. -/
@[expose] def finIdxBits (K : ℕ) (i : Fin K) : List Bool :=
  Cslib.BitString.lowBits (Nat.clog 2 K) i.val

@[simp]
theorem length_finIdxBits (K : ℕ) (i : Fin K) :
    (finIdxBits K i).length = Nat.clog 2 K :=
  Cslib.BitString.length_lowBits (Nat.clog 2 K) i.val

private theorem foldr_bit_finIdxBits (K : ℕ) (i : Fin K) :
    (finIdxBits K i).foldr Nat.bit 0 = i.val := by
  have hi_lt : i.val < 2 ^ Nat.clog 2 K :=
    lt_of_lt_of_le i.isLt (Nat.le_pow_clog Nat.one_lt_two K)
  exact Nat.foldr_bit_testBit (Nat.size_le.mpr hi_lt)

/-- `finIdxBits K` is injective on `Fin K`. -/
theorem finIdxBits_injective (K : ℕ) : Function.Injective (finIdxBits K) := by
  intro i₁ i₂ h
  apply Fin.ext
  rw [← foldr_bit_finIdxBits K i₁, ← foldr_bit_finIdxBits K i₂, h]

/-- The codeword set of `finIdxBits K` has uniform length `⌈log₂ K⌉` and is prefix-free. -/
theorem isPrefixFree_range_finIdxBits (K : ℕ) :
    IsPrefixFree (Set.range (finIdxBits K)) :=
  isPrefixFree_of_length_eq (by rintro _ ⟨i, rfl⟩; exact length_finIdxBits K i)

/-- Ceiling slack bound: for `1 ≤ K`, `⌈log₂ K⌉ < log₂ K + 1`. -/
theorem clog_two_lt_logb_add_one {K : ℕ} (hK : 1 ≤ K) :
    (Nat.clog 2 K : ℝ) < Real.logb 2 K + 1 := by
  rcases eq_or_lt_of_le hK with rfl | hK_gt
  · simp
  · have hc_pos : 1 ≤ Nat.clog 2 K := Nat.clog_pos Nat.one_lt_two hK_gt
    have hpow : 2 ^ (Nat.clog 2 K - 1) < K := Nat.pow_pred_clog_lt_self Nat.one_lt_two hK_gt
    have hpowR : (2 : ℝ) ^ ((Nat.clog 2 K - 1 : ℕ) : ℝ) < (K : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast hpow
    have hK_pos : (0 : ℝ) < K := by positivity
    have hlt : ((Nat.clog 2 K - 1 : ℕ) : ℝ) < Real.logb 2 K :=
      (Real.lt_logb_iff_rpow_lt (by norm_num) hK_pos).mpr hpowR
    rw [Nat.cast_sub hc_pos, Nat.cast_one] at hlt
    linarith

/-! ### Elias gamma positive-integer code (`eliasGamma`) -/

/-- Elias gamma prefix-free encoding of a positive integer `m ≥ 1`: `⌊log₂ m⌋` leading `false`
bits, a `true` delimiter bit, and the `⌊log₂ m⌋` low-order binary bits of `m`. -/
@[expose] def eliasGamma (m : ℕ) : List Bool :=
  let k := Nat.log 2 m
  List.replicate k false ++ true :: Cslib.BitString.lowBits k m

/-- Computable decoder for `eliasGamma`: drops the unary prefix and `true` delimiter and folds the
remaining low-order bits with leading bit `1`. -/
@[expose] def decodeEliasGamma (code : List Bool) : ℕ :=
  (code.drop (code.length / 2 + 1)).foldr Nat.bit 1

@[simp]
theorem length_eliasGamma (m : ℕ) :
    (eliasGamma m).length = 2 * Nat.log 2 m + 1 := by
  simp only [eliasGamma, List.length_append, List.length_replicate, List.length_cons,
    Cslib.BitString.length_lowBits]
  ring

theorem eliasGamma_ne_nil (m : ℕ) : eliasGamma m ≠ [] := by
  simp [← List.length_pos_iff]

/-- `decodeEliasGamma` recovers every positive integer `m ≥ 1` from `eliasGamma m`. -/
@[simp]
theorem decodeEliasGamma_eliasGamma {m : ℕ} (hm : 1 ≤ m) :
    decodeEliasGamma (eliasGamma m) = m := by
  set k := Nat.log 2 m
  have hhalf : (eliasGamma m).length / 2 + 1 = k + 1 := by
    rw [length_eliasGamma]
    omega
  have hsplit : eliasGamma m =
      (List.replicate k false ++ [true]) ++ Cslib.BitString.lowBits k m := by
    simp [eliasGamma, k]
  have hdrop : (eliasGamma m).drop ((eliasGamma m).length / 2 + 1) =
      Cslib.BitString.lowBits k m := by
    rw [hhalf, hsplit, List.drop_left' (by simp)]
  have hge : 2 ^ k ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hlt : m < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two m
  have hdiv : m / 2 ^ k = 1 := by
    apply le_antisymm
    · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).mpr
        (by simpa only [Nat.pow_succ'] using hlt))
    · exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos k)).mpr (by simpa using hge)
  have hbitk : m.testBit k = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq, hdiv]
    decide
  have hsize : m.size ≤ k + 1 := Nat.size_le.mpr hlt
  have hrec := Nat.foldr_bit_testBit hsize
  rw [List.range_succ, List.map_append, List.map_singleton, List.foldr_append, hbitk] at hrec
  rw [decodeEliasGamma, hdrop]
  exact hrec

/-- `eliasGamma` is injective on positive integers `{m : ℕ | 1 ≤ m}`. -/
theorem injOn_eliasGamma : Set.InjOn eliasGamma {m : ℕ | 1 ≤ m} := by
  intro m₁ hm₁ m₂ hm₂ heq
  rw [← decodeEliasGamma_eliasGamma hm₁, ← decodeEliasGamma_eliasGamma hm₂, heq]

private theorem getElem_eliasGamma_lt (m : ℕ) {i : ℕ} (hi : i < Nat.log 2 m) :
    (eliasGamma m)[i]'(by rw [length_eliasGamma]; omega) = false := by
  simp only [eliasGamma]
  rw [List.getElem_append_left (by simp [hi]), List.getElem_replicate]

private theorem getElem_eliasGamma_self (m : ℕ) :
    (eliasGamma m)[Nat.log 2 m]'(by rw [length_eliasGamma]; omega) = true := by
  simp only [eliasGamma]
  rw [List.getElem_append_right (by simp)]
  simp

/-- The full range of `eliasGamma` is prefix-free. -/
theorem isPrefixFree_range_eliasGamma : IsPrefixFree (Set.range eliasGamma) := by
  rintro _ ⟨m₁, rfl⟩ _ ⟨m₂, rfl⟩ ⟨r, hr⟩
  have hget : ∀ (i : ℕ) (hi₁ : i < (eliasGamma m₁).length),
      (eliasGamma m₁)[i]'hi₁ =
        (eliasGamma m₂)[i]'(by rw [← hr, List.length_append]; omega) := by
    intro i hi₁
    have happ : (eliasGamma m₁ ++ r)[i]'(by rw [List.length_append]; omega) =
        (eliasGamma m₁)[i]'hi₁ := List.getElem_append_left hi₁
    simpa only [hr] using happ.symm
  rcases lt_trichotomy (Nat.log 2 m₁) (Nat.log 2 m₂) with hlt | heq | hgt
  · have h₁ := getElem_eliasGamma_self m₁
    have h₂ := getElem_eliasGamma_lt m₂ hlt
    have h_eq := hget (Nat.log 2 m₁) (by rw [length_eliasGamma]; omega)
    rw [h₁, h₂] at h_eq
    cases h_eq
  · have hlen : (eliasGamma m₁ ++ r).length = (eliasGamma m₁).length := by
      rw [hr, length_eliasGamma, length_eliasGamma, heq]
    rw [List.length_append] at hlen
    have hr_nil : r = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [← hr, hr_nil, List.append_nil]
  · have h₁ := getElem_eliasGamma_lt m₁ hgt
    have h₂ := getElem_eliasGamma_self m₂
    have h_eq := hget (Nat.log 2 m₂) (by rw [length_eliasGamma]; omega)
    rw [h₁, h₂] at h_eq
    cases h_eq

/-- `eliasGamma '' {m : ℕ | 1 ≤ m}` is prefix-free. -/
theorem isPrefixFree_eliasGamma : IsPrefixFree (eliasGamma '' {m : ℕ | 1 ≤ m}) :=
  isPrefixFree_range_eliasGamma.anti (Set.image_subset_range _ _)

/-! ### Kraft–Gibbs compression bounds for entropy and conditional entropy -/

/-- **Kraft–Gibbs source coding lower bound** ([CoverThomas2006], Theorem 5.3.1): if `enc` is
injective on `p.support` and its image on `p.support` is prefix-free, then `entropy p` is at most
the expected codeword length under `p`. -/
theorem entropy_le_expected_length_of_isPrefixFree {α : Type*} [Fintype α]
    (p : PMF α) (enc : α → List Bool)
    (hinj : Set.InjOn enc p.support)
    (hpf : IsPrefixFree (enc '' p.support)) :
    entropy p ≤ ∑ a, (p a).toReal * ((enc a).length : ℝ) := by
  classical
  let s : Finset α := Finset.univ.filter fun a => a ∈ p.support
  have hs_mem (a : α) : a ∈ s ↔ a ∈ p.support := by simp [s]
  have hs_coe : (s : Set α) = p.support := Set.ext hs_mem
  obtain ⟨a₀, ha₀⟩ := p.support_nonempty
  have hs_ne : s.Nonempty := ⟨a₀, (hs_mem a₀).mpr ha₀⟩
  let S : Finset (List Bool) := s.image enc
  have hS_pf : IsPrefixFree (S : Set (List Bool)) := by
    simpa only [S, Finset.coe_image, hs_coe] using hpf
  have hkraft_img := hS_pf.finsetSum_one_div_card_pow_length_le_one
  simp only [Fintype.card_bool, Nat.cast_ofNat, one_div] at hkraft_img
  have hinj_s : Set.InjOn enc (s : Set α) := hs_coe.symm ▸ hinj
  have hsum_eq : ∑ w ∈ S, (2⁻¹ : ℝ) ^ w.length = ∑ a ∈ s, (2⁻¹ : ℝ) ^ (enc a).length :=
    Finset.sum_image hinj_s
  set Z : ℝ := ∑ a ∈ s, (2⁻¹ : ℝ) ^ (enc a).length
  have hZ_le : Z ≤ 1 := hsum_eq ▸ hkraft_img
  have hZ_pos : 0 < Z :=
    Finset.sum_pos (fun a _ => by positivity) hs_ne
  let f : α → ℝ≥0∞ := fun a =>
    if a ∈ s then ENNReal.ofReal ((2⁻¹ : ℝ) ^ (enc a).length / Z) else 0
  have hf_sum : ∑ a, f a = 1 := by
    have hsum_real : ∑ a ∈ s, (2⁻¹ : ℝ) ^ (enc a).length / Z = 1 := by
      rw [← Finset.sum_div, div_self hZ_pos.ne']
    simp only [f, Finset.sum_ite_mem, Finset.univ_inter]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => by positivity), hsum_real, ENNReal.ofReal_one]
  let q : PMF α := PMF.ofFintype f hf_sum
  have hq_toReal (a : α) (ha : a ∈ p.support) :
      (q a).toReal = (2⁻¹ : ℝ) ^ (enc a).length / Z := by
    have has : a ∈ s := (hs_mem a).mpr ha
    change (f a).toReal = _
    simp only [f, ite_eq_left has]
    exact ENNReal.toReal_ofReal (by positivity)
  have hmass_ge (a : α) (ha : a ∈ p.support) :
      (2 : ℝ) ^ (-((enc a).length : ℝ)) ≤ (q a).toReal := by
    rw [hq_toReal a ha, Real.rpow_neg (by norm_num), Real.rpow_natCast, ← inv_pow]
    exact le_div_self (by positivity) hZ_pos hZ_le
  have hsupp : p.support ⊆ q.support := by
    intro a ha
    have hpos : 0 < (q a).toReal :=
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).trans_le (hmass_ge a ha)
    exact (PMF.mem_support_iff q a).mpr fun h0 => by simp [h0] at hpos
  refine (entropy_le_sum_mul_surprisal hsupp).trans ?_
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases ha : a ∈ p.support
  · exact mul_le_mul_of_nonneg_left (surprisal_le_of_mass_ge q a (hmass_ge a ha))
      ENNReal.toReal_nonneg
  · have hp0 : (p a).toReal = 0 := by simp [(PMF.apply_eq_zero_iff p a).mpr ha]
    simp [hp0]

/-- **Conditional Kraft–Gibbs compression bound**: if for each observable `obs`, `enc obs` is
injective on `(conditionalSnd joint obs).support` with prefix-free image, then
`conditionalEntropy joint` is at most the expected codeword length under `joint`. -/
theorem conditionalEntropy_le_expected_length_of_isPrefixFree {Obs α : Type*}
    [Fintype Obs] [Fintype α]
    (joint : PMF (Obs × α)) (enc : Obs → α → List Bool)
    (hinj : ∀ obs ∈ (joint.map Prod.fst).support,
      Set.InjOn (enc obs) (conditionalSnd joint obs).support)
    (hpf : ∀ obs ∈ (joint.map Prod.fst).support,
      IsPrefixFree (enc obs '' (conditionalSnd joint obs).support)) :
    conditionalEntropy joint ≤ ∑ oa, (joint oa).toReal * ((enc oa.1 oa.2).length : ℝ) := by
  rw [conditionalEntropy_eq_sum, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun obs _ => ?_
  by_cases hobs : obs ∈ (joint.map Prod.fst).support
  · have hbound := entropy_le_expected_length_of_isPrefixFree (conditionalSnd joint obs)
      (enc obs) (hinj obs hobs) (hpf obs hobs)
    calc ((joint.map Prod.fst) obs).toReal * entropy (conditionalSnd joint obs)
        ≤ ((joint.map Prod.fst) obs).toReal *
            ∑ a, (conditionalSnd joint obs a).toReal * ((enc obs a).length : ℝ) :=
          mul_le_mul_of_nonneg_left hbound ENNReal.toReal_nonneg
      _ = ∑ a, (joint (obs, a)).toReal * ((enc obs a).length : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← mul_assoc, ← ENNReal.toReal_mul, marginal_mul_conditionalSnd]
  · have hm0 : (joint.map Prod.fst) obs = 0 := (PMF.apply_eq_zero_iff _ _).mpr hobs
    have hj0 : ∀ a, joint (obs, a) = 0 := fun a =>
      le_antisymm (hm0 ▸ apply_le_map_fst joint obs a) bot_le
    simp [hm0, hj0]

/-- **Communication transcript compression bound**: if a message `msg ω` sent over an outcome space
`p : PMF Ω` is prefix-free on each observation fiber `{ω ∈ p.support | obs ω = o}` and uniquely
determines `target ω` given `obs ω` on `p.support`, then `H(target(ω) | obs(ω)) ≤ E[|msg(ω)|]`. -/
theorem conditionalEntropy_map_le_expected_length_of_isPrefixFree {Ω Obs α : Type*}
    [Fintype Ω] [Finite Obs] [Finite α]
    (p : PMF Ω) (obs : Ω → Obs) (target : Ω → α) (msg : Ω → List Bool)
    (hpf : ∀ o : Obs, IsPrefixFree (msg '' {ω ∈ p.support | obs ω = o}))
    (hdec : ∀ ω₁ ∈ p.support, ∀ ω₂ ∈ p.support,
      obs ω₁ = obs ω₂ → msg ω₁ = msg ω₂ → target ω₁ = target ω₂) :
    conditionalEntropy (p.map fun ω => (obs ω, target ω)) ≤
      ∑ ω, (p ω).toReal * ((msg ω).length : ℝ) := by
  classical
  let := Fintype.ofFinite Obs
  let := Fintype.ofFinite α
  let W : Finset (List Bool) := Finset.univ.image msg
  let cw : Ω → {w // w ∈ W} := fun ω => ⟨msg ω, Finset.mem_image_of_mem msg (Finset.mem_univ ω)⟩
  let joint_cw : PMF (Obs × {w // w ∈ W}) := p.map fun ω => (obs ω, cw ω)
  let joint_tgt : PMF (Obs × α) := p.map fun ω => (obs ω, target ω)
  obtain ⟨ω_def, _⟩ := p.support_nonempty
  let dec : Obs × {w // w ∈ W} → Obs × α := fun oc =>
    if h : ∃ ω ∈ p.support, obs ω = oc.1 ∧ cw ω = oc.2 then
      (oc.1, target (Classical.choose h))
    else
      (oc.1, target ω_def)
  have hmap_dec : joint_cw.map dec = joint_tgt := by
    rw [PMF.map_comp]
    refine Cslib.Probability.PMF.map_congr_on_support p _ _ fun ω hω => ?_
    have hex : ∃ ω' ∈ p.support, obs ω' = obs ω ∧ cw ω' = cw ω := ⟨ω, hω, rfl, rfl⟩
    obtain ⟨hω', hobs', hcw'⟩ := Classical.choose_spec hex
    have hmsg' : msg (Classical.choose hex) = msg ω := congrArg Subtype.val hcw'
    simp only [Function.comp_apply, dec, dite_eq_left hex]
    exact Prod.ext rfl (hdec (Classical.choose hex) hω' ω hω hobs' hmsg')
  have hent_le : conditionalEntropy joint_tgt ≤ conditionalEntropy joint_cw := by
    have hm_fst : joint_tgt.map Prod.fst = joint_cw.map Prod.fst := by
      simp only [joint_tgt, joint_cw, PMF.map_comp, Function.comp_def]
    rw [conditionalEntropy, conditionalEntropy, hm_fst, ← hmap_dec]
    exact sub_le_sub_right (entropy_map_le joint_cw dec) _
  have hcw_pf : ∀ o ∈ (joint_cw.map Prod.fst).support,
      IsPrefixFree (Subtype.val '' (conditionalSnd joint_cw o).support) := by
    intro o ho
    refine (hpf o).anti ?_
    rintro _ ⟨c, hc, rfl⟩
    have hoc : (o, c) ∈ joint_cw.support :=
      (mem_support_conditionalSnd_iff joint_cw o ho c).mp hc
    obtain ⟨ω, hω, hpair⟩ := (PMF.mem_support_map_iff _ _ _).mp hoc
    rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
    exact ⟨ω, ⟨hω, rfl⟩, rfl⟩
  have hcw_bound := conditionalEntropy_le_expected_length_of_isPrefixFree joint_cw
    (fun _ c => c.val) (fun _ _ => Subtype.val_injective.injOn) hcw_pf
  have hexp_eq : ∑ oc, (joint_cw oc).toReal * ((oc.2.val).length : ℝ) =
      ∑ ω, (p ω).toReal * ((msg ω).length : ℝ) :=
    sum_map_mul p (fun ω => (obs ω, cw ω)) (fun oc => ((oc.2.val).length : ℝ))
  exact hent_le.trans (hcw_bound.trans_eq hexp_eq)

end Cslib.Probability.Coding

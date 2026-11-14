/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.InformationTheory.Coding.PrefixFree
import CslibFrontier.Foundations.Data.Nat.Bits
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Self-Delimiting Binary Codes and Prefix-Free Concatenation Combinators

This module provides deterministic concatenation combinators for `InformationTheory.IsPrefixFree`
together with two basic binary prefix-free codes in `Cslib.BitString`:

* `Cslib.BitString.finIdxBits`: fixed-width `⌈log₂ K⌉`-bit little-endian encoding of `Fin K`.
* `Cslib.BitString.eliasGamma` and `Cslib.BitString.decodeEliasGamma`: a little-endian-suffix
  variant of Peter Elias's 1975 gamma code [Elias1975] for positive integers `m ≥ 1`. It emits
  `⌊log₂ m⌋` leading `false` bits, a `true` delimiter bit, and the `⌊log₂ m⌋` low-order binary
  bits of `m` least-significant bit first (via `Cslib.BitString.lowBits`, whereas Elias [Elias1975]
  orders the suffix bits most-significant bit first, e.g., `eliasGamma 6 = [false, false, true,
  false, true]` vs. `00110`), preserving the exact codeword length `2 * ⌊log₂ m⌋ + 1`, unique
  decodability on `{m | 1 ≤ m}`, and prefix-freeness.

## Main definitions

* `Cslib.BitString.finIdxBits`: fixed-width `⌈log₂ K⌉`-bit binary encoding of `Fin K`.
* `Cslib.BitString.eliasGamma`, `Cslib.BitString.decodeEliasGamma`: little-endian-suffix variant of
  the Elias gamma code [Elias1975] of length `2 * ⌊log₂ m⌋ + 1` and its left inverse on `m ≥ 1`.
* `Cslib.BitString.encodeFintype`, `Cslib.BitString.encodeMemFinset`,
  `Cslib.BitString.encodeRestr`: canonical binary encodings for finite types, membership, and
  restricted maps.

## Main results

* `InformationTheory.IsPrefixFree.bind_append`,
  `Cslib.BitString.prefix_append_of_length_eq`,
  `Cslib.BitString.prefix_append_of_isPrefixFree`,
  `Cslib.BitString.isPrefixFree_biUnion_append`,
  `Cslib.BitString.isPrefixFree_image_append`,
  `Cslib.BitString.isPrefixFree_prod_append`,
  `Cslib.BitString.injOn_append`,
  `Cslib.BitString.injOn_prod_append`: sequential dependent concatenation of prefix-free codes
  remains prefix-free and uniquely decomposable; equal-length or prefix-free heads preserve prefix
  relations on tails.
* `Cslib.BitString.finIdxBits_injective`,
  `Cslib.BitString.isPrefixFree_range_finIdxBits`,
  `Cslib.BitString.clog_two_lt_logb_add_one`: fixed-width index code properties and ceiling slack
  `(Nat.clog 2 K : ℝ) < Real.logb 2 K + 1`.
* `Cslib.BitString.encodeFintype`, `Cslib.BitString.encodeMemFinset`,
  `Cslib.BitString.encodeRestr`: canonical binary encodings, exact lengths, and injectivity for
  finite types, subsets, and restricted maps (`encodeFintype_injective`, `encodeMemFinset_inj`,
  `encodeRestr_inj`).
* `Cslib.BitString.decodeEliasGamma_eliasGamma`,
  `Cslib.BitString.injOn_eliasGamma`,
  `Cslib.BitString.isPrefixFree_range_eliasGamma`,
  `Cslib.BitString.isPrefixFree_eliasGamma`: codeword length, left-invertibility, injectivity on
  `{m | 1 ≤ m}`, and prefix-freeness of `eliasGamma`.

## References

* [P. Elias, *Universal Codeword Sets and Representations of the Integers*][Elias1975].
-/

public section

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

namespace Cslib.BitString

open InformationTheory

/-! ### Self-delimiting and prefix-free combinators -/

/-- Equal-length prefixes of equal or prefix-related concatenations must be equal,
leaving a prefix relation on the tails. -/
theorem prefix_append_of_length_eq {α : Type*} {u₁ u₂ v₁ v₂ : List α}
    (hlen : u₁.length = u₂.length) (hp : u₁ ++ v₁ <+: u₂ ++ v₂) : u₁ = u₂ ∧ v₁ <+: v₂ := by
  obtain ⟨w, hw⟩ := hp; rw [List.append_assoc] at hw
  obtain ⟨rfl, hw'⟩ := List.append_inj hw hlen; exact ⟨rfl, ⟨w, hw'⟩⟩

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

/-- A prefix of concatenations whose heads are drawn from a prefix-free set forces
equal heads and a prefix relation on the tails. -/
theorem prefix_append_of_isPrefixFree {α : Type*} {S : Set (List α)}
    (hpf : IsPrefixFree S) {u₁ u₂ v₁ v₂ : List α}
    (hu₁ : u₁ ∈ S) (hu₂ : u₂ ∈ S) (hp : u₁ ++ v₁ <+: u₂ ++ v₂) : u₁ = u₂ ∧ v₁ <+: v₂ := by
  obtain ⟨w, hw⟩ := hp
  rw [List.append_assoc] at hw
  obtain ⟨rfl, hw'⟩ := append_inj_of_isPrefixFree hpf hu₁ hu₂ hw
  exact ⟨rfl, ⟨w, hw'⟩⟩

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
  lowBits (Nat.clog 2 K) i.val

@[simp]
theorem length_finIdxBits (K : ℕ) (i : Fin K) :
    (finIdxBits K i).length = Nat.clog 2 K :=
  length_lowBits (Nat.clog 2 K) i.val

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
  rw [← Real.natCeil_logb_natCast]
  exact Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) (by exact_mod_cast hK))

/-! ### Elias gamma positive-integer code (`eliasGamma`) -/

/-- Little-endian-suffix variant of Peter Elias's 1975 gamma code [Elias1975] for positive integers
`m ≥ 1`: `⌊log₂ m⌋` leading `false` bits, a `true` delimiter bit, and the `⌊log₂ m⌋` low-order
binary bits of `m` in least-significant-first order (`lowBits`). Unlike Elias's most-significant-
first suffix convention (e.g., `eliasGamma 6 = [false, false, true, false, true]` vs. `00110`),
using `lowBits` composes directly with `Nat.foldr_bit_testBit` while keeping the exact codeword
length `2 * ⌊log₂ m⌋ + 1` and prefix-freeness. -/
@[expose] def eliasGamma (m : ℕ) : List Bool :=
  let k := Nat.log 2 m
  List.replicate k false ++ true :: lowBits k m

/-- Computable left inverse for `eliasGamma` on positive integers: drops the unary prefix and `true`
delimiter and folds the remaining low-order bits with leading bit `1`. -/
def decodeEliasGamma (code : List Bool) : ℕ :=
  (code.drop (code.length / 2 + 1)).foldr Nat.bit 1

@[simp]
theorem length_eliasGamma (m : ℕ) :
    (eliasGamma m).length = 2 * Nat.log 2 m + 1 := by
  simp only [eliasGamma, List.length_append, List.length_replicate, List.length_cons,
    length_lowBits]
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
      (List.replicate k false ++ [true]) ++ lowBits k m := by
    simp [eliasGamma, k]
  have hdrop : (eliasGamma m).drop ((eliasGamma m).length / 2 + 1) = lowBits k m := by
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

/-! ### Fixed-width encodings of finite structures -/

/-- Fixed-width binary encoding of a finite type `α` via `finIdxBits`. -/
noncomputable def encodeFintype {α : Type*} [Fintype α] (x : α) : List Bool :=
  finIdxBits (Fintype.card α) (Fintype.equivFin α x)

@[simp] theorem length_encodeFintype {α : Type*} [Fintype α] (x : α) :
    (encodeFintype x).length = Nat.clog 2 (Fintype.card α) := length_finIdxBits (Fintype.card α) _

theorem encodeFintype_injective {α : Type*} [Fintype α] :
    Function.Injective (encodeFintype (α := α)) :=
  (finIdxBits_injective (Fintype.card α)).comp (Fintype.equivFin α).injective

open Classical in
/-- Fixed-width encoding of an element `x ∈ F` of a bounded finite set `F` (`card F ≤ K`). -/
noncomputable def encodeMemFinset {β : Type*} (F : Finset β) (K : ℕ) (x : β) : List Bool :=
  if h : x ∈ F ∧ F.card ≤ K ∧ 0 < K then
    have ⟨_, hcard, _⟩ := h
    finIdxBits K (Fin.castLE ((Fintype.card_coe F).trans_le hcard) (Fintype.equivFin ↥F ⟨x, h.1⟩))
  else List.replicate (Nat.clog 2 K) false

@[simp] theorem length_encodeMemFinset {β : Type*} (F : Finset β) (K : ℕ) (x : β) :
    (encodeMemFinset F K x).length = Nat.clog 2 K := by
  classical simp only [encodeMemFinset]; split_ifs <;> simp

theorem encodeMemFinset_inj {β : Type*} {F : Finset β} {K : ℕ} {x₁ x₂ : β}
    (hx₁ : x₁ ∈ F) (hx₂ : x₂ ∈ F) (hcard : F.card ≤ K)
    (heq : encodeMemFinset F K x₁ = encodeMemFinset F K x₂) : x₁ = x₂ := by
  classical
  have hK : 0 < K := (Finset.card_pos.mpr ⟨x₁, hx₁⟩).trans_le hcard
  have h1 : x₁ ∈ F ∧ F.card ≤ K ∧ 0 < K := ⟨hx₁, hcard, hK⟩
  have h2 : x₂ ∈ F ∧ F.card ≤ K ∧ 0 < K := ⟨hx₂, hcard, hK⟩
  simp only [encodeMemFinset, h1, h2] at heq
  exact congrArg Subtype.val ((Fintype.equivFin ↥F).injective
    ((Fin.castLE_injective _) (finIdxBits_injective K heq)))

open Classical in
/-- Fixed-width encoding of a function on a finite subset `S : Finset α` with codomain `β`. -/
noncomputable def encodeRestr {α β : Type*} [Fintype β] (S : Finset α) (f : α → β) :
    List Bool := encodeFintype (fun x : ↥S => f x.val)

@[simp] theorem length_encodeRestr {α β : Type*} [Fintype β] (S : Finset α) (f : α → β) :
    (encodeRestr S f).length = Nat.clog 2 (Fintype.card β ^ S.card) := by
  classical rw [encodeRestr, length_encodeFintype, Fintype.card_fun, Fintype.card_coe]

theorem encodeRestr_inj {α β : Type*} [Fintype β] {S₁ S₂ : Finset α} {f₁ f₂ : α → β}
    (hS : S₁ = S₂) (heq : encodeRestr S₁ f₁ = encodeRestr S₂ f₂) : ∀ x ∈ S₁, f₁ x = f₂ x := by
  classical subst hS; intro x hx; exact congrFun (encodeFintype_injective heq) ⟨x, hx⟩

end Cslib.BitString

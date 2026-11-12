/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Linear codes, rate, puncturing, and shortening

A *linear code* is a submodule `C` of the words `ι → M`, usually with `M = F` a field
[MacWilliams and Sloane, Chapter 1][MacWilliamsSloane1977]. The Hamming distance between two words
is the Hamming weight `hammingNorm` of their difference, and the difference of two codewords is a
codeword, so the minimum distance of a linear code is the least weight of a nonzero codeword
(`Cslib.Code.le_minDist_iff_hammingNorm`, `Cslib.Code.minDist_eq_iInf_hammingNorm`).

This module also provides the finite-code `rate` (`log_|α| |C| / |ι|`, equal to `finrank F C / |ι|`
for linear codes over a finite field `F`), coordinate restriction / puncturing (`Code.puncture`,
`Code.punctureLinear`), zero-extension along an embedding (`Code.extend`, `Code.extendLinearMap`),
and shortening (`Code.shorten`, `Code.shortenLinear`), together with cardinality/rate bounds for
kernels of linear maps.

## Main definitions

* `Cslib.Code.rate`: the information rate `log_|α| |C| / |ι|` of a finite code.
* `Cslib.Code.extend`, `Cslib.Code.extendLinearMap`: zero-extension of a word along an embedding.
* `Cslib.Code.puncture`, `Cslib.Code.punctureLinear`: puncturing (coordinate restriction).
* `Cslib.Code.shorten`, `Cslib.Code.shortenLinear`: shortening a code to an embedded subset.

## Main results

* `Cslib.Code.le_minDist_iff_hammingNorm`: lower bounds on the minimum distance of a linear code
  are lower bounds on the weights of its nonzero codewords.
* `Cslib.Code.minDist_eq_iInf_hammingNorm`: the minimum distance of a linear code is the least
  weight of a nonzero codeword.
* `Cslib.Code.card_linearCode_eq_pow_finrank`, `Cslib.Code.rate_linearCode_eq_finrank_div_card`:
  cardinality and rate of linear codes over finite fields.
* `Cslib.Code.hammingNorm_extend`, `Cslib.Code.le_minDist_shorten`: shortening preserves Hamming
  weights and cannot decrease minimum distance.
* `Cslib.Code.pow_sub_le_card_ker`, `Cslib.Code.one_sub_card_div_card_le_rate_ker`: cardinality
  and rate lower bounds for kernels of linear maps over finite rings.

## References

* [F. J. MacWilliams, N. J. A. Sloane, *The Theory of Error-Correcting Codes*]
  [MacWilliamsSloane1977]
-/

public section

namespace Cslib.Code

section Distance

variable {ι R M : Type*} [Fintype ι] [Ring R] [AddCommGroup M] [Module R M] [DecidableEq M]

/-- The minimum distance of a linear code is at least `d` iff every nonzero codeword has weight at
least `d`. -/
theorem le_minDist_iff_hammingNorm (C : Submodule R (ι → M)) {d : ℕ∞} :
    d ≤ minDist (C : Set (ι → M)) ↔ ∀ x ∈ C, x ≠ 0 → d ≤ hammingNorm x := by
  rw [le_minDist_iff]
  refine ⟨fun h x hx hx0 => ?_, fun h x hx y hy hxy => ?_⟩
  · rw [← hammingDist_zero_right]
    exact h x hx 0 C.zero_mem hx0
  · rw [hammingDist_eq_hammingNorm]
    exact h _ (C.add_mem (C.neg_mem hx) hy) fun h0 => hxy (neg_add_eq_zero.1 h0)

/-- **Minimum weight.** The minimum distance of a linear code is the least weight of a nonzero
codeword, and `⊤` for the zero code. -/
theorem minDist_eq_iInf_hammingNorm (C : Submodule R (ι → M)) :
    minDist (C : Set (ι → M)) = ⨅ x ∈ C, ⨅ _ : x ≠ 0, (hammingNorm x : ℕ∞) :=
  le_antisymm
    (le_iInf₂ fun x hx => le_iInf fun hx0 => (le_minDist_iff_hammingNorm C).1 le_rfl x hx hx0)
    ((le_minDist_iff_hammingNorm C).2 fun _ hx hx0 => iInf₂_le_of_le _ hx (iInf_le _ hx0))

end Distance

section Rate

/-- The *rate* of a code `C : Set (ι → α)` over a finite alphabet `α`: `log_|α| |C| / |ι|`. -/
@[expose]
noncomputable def rate {ι α : Type*} [Fintype ι] [Fintype α] (C : Set (ι → α)) : ℝ :=
  Real.logb (Fintype.card α) (Nat.card C) / Fintype.card ι

/-- A linear code over a finite field `F` has cardinality `|F| ^ dim F C`. -/
theorem card_linearCode_eq_pow_finrank {ι F : Type*} [Finite ι] [Field F] [Fintype F]
    (C : Submodule F (ι → F)) :
    Nat.card C = Fintype.card F ^ Module.finrank F C := by
  rw [Module.natCard_eq_pow_finrank (K := F) (V := C), Nat.card_eq_fintype_card]

/-- The rate of a linear code over a finite field `F` equals `dim F C / |ι|`. -/
theorem rate_linearCode_eq_finrank_div_card {ι F : Type*} [Fintype ι] [Field F] [Fintype F]
    (C : Submodule F (ι → F)) :
    rate (C : Set (ι → F)) = Module.finrank F C / Fintype.card ι := by
  have hF : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hcard : Nat.card (C : Set (ι → F)) = Nat.card C := rfl
  rw [rate, hcard, card_linearCode_eq_pow_finrank]
  push_cast
  rw [← Real.rpow_natCast (Fintype.card F : ℝ), Real.logb_rpow (by linarith) (by linarith)]

end Rate

section KerBounds

/-- Over a finite ring `R`, `|R| ^ |ι| ≤ |ker f| * |R| ^ |κ|` for any linear map
`f : (ι → R) →ₗ[R] (κ → R)`. -/
theorem card_pow_le_card_ker_mul {ι κ R : Type*} [Fintype ι] [Fintype κ] [Ring R] [Fintype R]
    (f : (ι → R) →ₗ[R] (κ → R)) :
    Fintype.card R ^ Fintype.card ι ≤ Nat.card f.ker * Fintype.card R ^ Fintype.card κ := by
  have h := AddSubgroup.card_ker_mul_card_range f.toAddMonoidHom
  have hker : Nat.card f.toAddMonoidHom.ker = Nat.card f.ker := rfl
  have hrange : Nat.card f.toAddMonoidHom.range ≤ Fintype.card R ^ Fintype.card κ := by
    refine (Nat.card_le_card_of_injective _ Subtype.val_injective).trans ?_
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := R), Nat.card_eq_fintype_card (α := κ)]
  rw [hker, Nat.card_fun, Nat.card_eq_fintype_card (α := R),
    Nat.card_eq_fintype_card (α := ι)] at h
  rw [← h]
  exact Nat.mul_le_mul_left _ hrange

/-- Over a finite ring `R` (`|R| ≥ 1`), `|R| ^ (|ι| - |κ|) ≤ |ker f|`. -/
theorem pow_sub_le_card_ker {ι κ R : Type*} [Fintype ι] [Fintype κ] [Ring R] [Fintype R]
    (f : (ι → R) →ₗ[R] (κ → R)) :
    Fintype.card R ^ (Fintype.card ι - Fintype.card κ) ≤ Nat.card f.ker := by
  rcases le_total (Fintype.card κ) (Fintype.card ι) with hle | hle
  · have h2 : Fintype.card R ^ (Fintype.card ι - Fintype.card κ) * Fintype.card R ^ Fintype.card κ =
        Fintype.card R ^ Fintype.card ι := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    have hpos : 0 < Fintype.card R ^ Fintype.card κ := pow_pos Fintype.card_pos _
    exact le_of_mul_le_mul_right (h2.le.trans (card_pow_le_card_ker_mul f)) hpos
  · rw [Nat.sub_eq_zero_of_le hle, pow_zero]
    exact Nat.card_pos

/-- Over a finite nontrivial ring `R`, `rate (ker f) ≥ 1 - |κ| / |ι|`. -/
theorem one_sub_card_div_card_le_rate_ker {ι κ R : Type*} [Fintype ι] [Fintype κ] [Ring R]
    [Fintype R] [Nontrivial R] (hι : 0 < Fintype.card ι) (f : (ι → R) →ₗ[R] (κ → R)) :
    1 - (Fintype.card κ : ℝ) / Fintype.card ι ≤ rate (f.ker : Set (ι → R)) := by
  have hpos : (0 : ℝ) < Nat.card f.ker := by exact_mod_cast Nat.card_pos (α := f.ker)
  have hR : (1 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.one_lt_card
  have hR0 : (0 : ℝ) < Fintype.card R := by linarith
  have h : ((Fintype.card R : ℝ) ^ (Fintype.card ι : ℝ)) ≤
      (Nat.card f.ker : ℝ) * (Fintype.card R : ℝ) ^ (Fintype.card κ : ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_natCast]
    exact_mod_cast card_pow_le_card_ker_mul f
  have hlog : (Fintype.card ι : ℝ) ≤
      Real.logb (Fintype.card R) (Nat.card f.ker) + Fintype.card κ := by
    have h1 := Real.logb_le_logb_of_le hR (by positivity) h
    rw [Real.logb_mul hpos.ne' (by positivity),
      Real.logb_rpow hR0 (by linarith), Real.logb_rpow hR0 (by linarith)] at h1
    exact h1
  have hι' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hι
  have hcard : Nat.card (f.ker : Set (ι → R)) = Nat.card f.ker := rfl
  rw [rate, hcard, sub_le_iff_le_add, ← add_div, le_div_iff₀ hι', one_mul]
  linarith

end KerBounds

section ExtendAndShorten

/-- Extending a word `z : κ → M` by zero outside the image of an embedding `emb : κ ↪ ι`. -/
noncomputable def extend {κ ι M : Type*} [Zero M]
    (emb : κ ↪ ι) (z : κ → M) : ι → M :=
  Function.extend emb z 0

/-- Extension agrees with `z` on the retained coordinates. -/
@[simp]
theorem extend_emb {κ ι M : Type*} [Zero M]
    (emb : κ ↪ ι) (z : κ → M) (j : κ) : extend emb z (emb j) = z j :=
  emb.injective.extend_apply z 0 j

/-- Extension vanishes outside the image of `emb`. -/
theorem extend_of_notMem {κ ι M : Type*} [Zero M]
    (emb : κ ↪ ι) (z : κ → M) {i : ι} (hi : ∀ j, emb j ≠ i) : extend emb z i = 0 :=
  by simpa only [extend, Pi.zero_apply] using
    Function.extend_apply' (f := emb) z 0 i (not_exists.2 hi)

/-- Finite-sum representation of `extend emb z` as an indicator sum over `emb`. -/
theorem extend_eq_sum {κ ι M : Type*} [Fintype κ] [DecidableEq ι] [AddCommMonoid M]
    (emb : κ ↪ ι) (z : κ → M) (i : ι) :
    extend emb z i = ∑ j : κ, if emb j = i then z j else 0 := by
  by_cases h : ∃ j, emb j = i
  · rcases h with ⟨j, rfl⟩
    rw [extend_emb, Finset.sum_eq_single j
      (fun j' _ hj' => by simp [emb.injective.ne hj']) (by simp)]
    simp
  · push Not at h
    rw [extend_of_notMem emb z h]
    simp [h]

/-- Zero-extension along an embedding is injective. -/
theorem extend_injective {κ ι M : Type*} [Zero M]
    (emb : κ ↪ ι) : Function.Injective (extend (M := M) emb) := fun z₁ z₂ h =>
  funext fun j => by simpa only [extend_emb] using congrFun h (emb j)

/-- Zero-extension as an `R`-linear map `(κ → M) →ₗ[R] (ι → M)`. -/
noncomputable def extendLinearMap {κ ι : Type*} (R M : Type*)
    [Semiring R] [AddCommMonoid M] [Module R M] (emb : κ ↪ ι) : (κ → M) →ₗ[R] (ι → M) :=
  Function.ExtendByZero.linearMap R M emb

/-- Applying `extendLinearMap` agrees with `extend`. -/
@[simp]
theorem extendLinearMap_apply {κ ι : Type*} (R M : Type*)
    [Semiring R] [AddCommMonoid M] [Module R M] (emb : κ ↪ ι) (z : κ → M) :
    extendLinearMap R M emb z = extend emb z := by
  ext i
  exact Function.ExtendByZero.linearMap_apply R M emb z i

/-- Zero-extension preserves Hamming weight. -/
theorem hammingNorm_extend {κ ι M : Type*} [Fintype κ] [Fintype ι]
    [Zero M] [DecidableEq M] (emb : κ ↪ ι) (z : κ → M) :
    hammingNorm (extend emb z) = hammingNorm z := by
  simp only [hammingNorm]
  symm
  refine Finset.card_bij (fun j _ => emb j) (fun j hj => ?_) (fun _ _ _ _ h => emb.injective h)
    (fun i hi => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rwa [extend_emb]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_contra hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hne
    have hnone : ∀ j, emb j ≠ i := fun j he =>
      hne j (by rw [← he, extend_emb] at hi; exact hi) he
    exact hi (extend_of_notMem emb z hnone)

/-- Zero-extension preserves Hamming distance. -/
theorem hammingDist_extend {κ ι M : Type*} [Fintype κ] [Fintype ι]
    [AddCommGroup M] [DecidableEq M] (emb : κ ↪ ι) (z₁ z₂ : κ → M) :
    hammingDist (extend emb z₁) (extend emb z₂) = hammingDist z₁ z₂ := by
  rw [hammingDist_eq_hammingNorm, hammingDist_eq_hammingNorm,
    ← extendLinearMap_apply ℤ M emb z₁, ← extendLinearMap_apply ℤ M emb z₂,
    ← (extendLinearMap ℤ M emb).map_neg, ← (extendLinearMap ℤ M emb).map_add]
  exact hammingNorm_extend emb (-z₁ + z₂)

/-- Puncturing a code `C` along coordinate map `emb : κ → ι`: restricting words to `emb`. -/
def puncture {κ ι : Type*} {α : Type*} (C : Set (ι → α)) (emb : κ → ι) : Set (κ → α) :=
  (fun x => x ∘ emb) '' C

/-- Puncturing a linear code `C` along `emb : κ → ι`. -/
def punctureLinear {κ ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (C : Submodule R (ι → M)) (emb : κ → ι) : Submodule R (κ → M) :=
  C.map (LinearMap.funLeft R M emb)

/-- Membership in a punctured code `puncture C emb`. -/
@[simp]
theorem mem_puncture {κ ι α : Type*} {C : Set (ι → α)} {emb : κ → ι} {y : κ → α} :
    y ∈ puncture C emb ↔ ∃ x ∈ C, x ∘ emb = y :=
  Iff.rfl

/-- Membership in a punctured linear code `punctureLinear C emb`. -/
@[simp]
theorem mem_punctureLinear {κ ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {C : Submodule R (ι → M)} {emb : κ → ι} {y : κ → M} :
    y ∈ punctureLinear C emb ↔ ∃ x ∈ C, x ∘ emb = y :=
  Iff.rfl

/-- Coercion of `punctureLinear C emb` agrees with `puncture (C : Set _) emb`. -/
@[simp]
theorem coe_punctureLinear {κ ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (C : Submodule R (ι → M)) (emb : κ → ι) :
    (punctureLinear C emb : Set (κ → M)) = puncture (C : Set (ι → M)) emb := by
  ext y
  exact Iff.rfl

/-- Shortening a code `C` along an embedding `emb : κ ↪ ι`: words whose zero-extension lies in
`C`. -/
def shorten {κ ι M : Type*} [Zero M]
    (C : Set (ι → M)) (emb : κ ↪ ι) : Set (κ → M) :=
  {z | extend emb z ∈ C}

/-- Shortening a linear code `C` along `emb : κ ↪ ι`. -/
noncomputable def shortenLinear {κ ι R M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (C : Submodule R (ι → M)) (emb : κ ↪ ι) :
    Submodule R (κ → M) :=
  C.comap (extendLinearMap R M emb)

/-- Membership in `shorten C emb` means the zero-extension lies in `C`. -/
@[simp]
theorem mem_shorten {κ ι M : Type*} [Zero M]
    (C : Set (ι → M)) (emb : κ ↪ ι) (z : κ → M) :
    z ∈ shorten C emb ↔ extend emb z ∈ C := by
  rfl

/-- Membership in `shortenLinear C emb` means the zero-extension lies in `C`. -/
@[simp]
theorem mem_shortenLinear {κ ι R M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (C : Submodule R (ι → M)) (emb : κ ↪ ι) (z : κ → M) :
    z ∈ shortenLinear C emb ↔ extend emb z ∈ C := by
  simp only [shortenLinear, Submodule.mem_comap, extendLinearMap_apply]

/-- As a set, `shortenLinear C emb` equals `shorten (C : Set (ι → M)) emb`. -/
@[simp]
theorem coe_shortenLinear {κ ι R M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (C : Submodule R (ι → M)) (emb : κ ↪ ι) :
    ((shortenLinear C emb : Submodule R (κ → M)) : Set (κ → M)) =
      shorten (C : Set (ι → M)) emb := by
  ext z
  simp only [SetLike.mem_coe, mem_shortenLinear, mem_shorten]

/-- Shortening cannot decrease minimum distance. -/
theorem le_minDist_shorten {κ ι M : Type*} [Fintype κ] [Fintype ι]
    [AddCommGroup M] [DecidableEq M] (C : Set (ι → M)) (emb : κ ↪ ι) :
    minDist C ≤ minDist (shorten C emb) := by
  refine le_minDist_iff.2 fun z₁ hz₁ z₂ hz₂ hne => ?_
  rw [← hammingDist_extend emb z₁ z₂]
  exact minDist_le_hammingDist hz₁ hz₂ fun h => hne (extend_injective emb h)

end ExtendAndShorten

end Cslib.Code

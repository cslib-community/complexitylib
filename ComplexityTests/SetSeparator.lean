/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.Dynamic.Spec
public import Complexity.Foundations.Data.BitString.List.PrefixFree
public import Complexity.Foundations.Data.Nat.IterLog
public import Complexity.Probability.Coding.PrefixFreeEntropy
public import Complexity.Probability.Coding.SetSeparator
public import Complexity.Probability.Uniform

/-!
# Tests for `IterLog`, `BitString.PrefixFree`, `PrefixFreeEntropy`, and `SetSeparator`

Concrete evaluation checks, dependent self-delimiting code composition, Kraft–Gibbs compression
examples, and non-vacuous instantiations of `exists_prefixFree_separator_code` (strictly beating the
trivial `(S + 1)`-bit subset-indicator encoding).
-/

public section

namespace CslibTests.SetSeparator

open Nat Cslib Cslib.BitString Cslib.Probability.PMF Cslib.Probability.Coding InformationTheory
open scoped BigOperators ENNReal

/-! ### 1. `Nat.iterLog` and `Nat.floorLogStar` concrete evaluations and ceiling bridges -/

example : iterLog 0 65536 = 65536 := by decide
example : iterLog 1 65536 = 16 := by decide
example : iterLog 2 65536 = 4 := by decide
example : iterLog 3 65536 = 2 := by decide
example : iterLog 4 65536 = 1 := by decide
example : iterLog 5 65536 = 0 := by decide

example : floorLogStar 0 = 0 := by decide
example : floorLogStar 1 = 0 := by decide
example : floorLogStar 2 = 1 := by decide
example : floorLogStar 3 = 1 ∧ logStar 3 = 2 := by decide
example : floorLogStar 4 = 2 := by decide
example : floorLogStar 15 = 2 ∧ logStar 15 = 3 := by decide
example : floorLogStar 16 = 3 := by decide
example : floorLogStar 65535 = 3 := by decide
example : floorLogStar 65536 = 4 := by decide

/-- Floor/ceiling comparison and base/step equations for `Nat.floorLogStar`. -/
theorem floorLogStar_bridges (n : ℕ) :
    floorLogStar n ≤ logStar n ∧ logStar n ≤ floorLogStar n + 1 :=
  ⟨floorLogStar_le_logStar n, logStar_le_floorLogStar_add_one n⟩

/-- Bridge between `iterLog 2 (max n 4)` and `Dynamic.logLogFactor n`. -/
theorem iterLog_two_bridges_logLogFactor (n : ℕ) :
    max (iterLog 2 (max n 4)) 1 = iterLog 2 (max n 4) ∧
      iterLog 2 (max n 4) ≤ DataStructure.Dictionary.Dynamic.logLogFactor n ∧
      DataStructure.Dictionary.Dynamic.logLogFactor n ≤ 2 * iterLog 2 (max n 4) :=
  ⟨max_iterLog_two_max_four n, iterLog_two_max_four_le_clog n,
    clog_clog_max_four_le_two_mul_iterLog n⟩

/-! ### 2. `finIdxBits`, `eliasGamma`, and dependent prefix-free concatenation -/

example : finIdxBits 5 ⟨3, by decide⟩ = [true, true, false] := by decide
example : eliasGamma 1 = [true] := by decide
example : eliasGamma 2 = [false, true, false] := by decide
example : eliasGamma 3 = [false, true, true] := by decide
example : eliasGamma 6 = [false, false, true, false, true] := by decide
example : decodeEliasGamma (eliasGamma 42) = 42 := decodeEliasGamma_eliasGamma (by decide)

/-- Dependent variable-width code `(k, i) ↦ eliasGamma k ++ finIdxBits k i` on `{p | i < k}`:
the width `⌈log₂ k⌉` of the second field depends on the decoded value of the first field. -/
def depPairCode (p : ℕ × ℕ) : List Bool :=
  if h : p.2 < p.1 then eliasGamma p.1 ++ finIdxBits p.1 ⟨p.2, h⟩ else []

theorem depPairCode_prefixFree_and_injOn :
    let D : Set (ℕ × ℕ) := {p | 1 ≤ p.1 ∧ p.2 < p.1}
    Set.InjOn depPairCode D ∧ IsPrefixFree (depPairCode '' D) := by
  intro D
  let raw : ℕ × ℕ → List Bool := fun p =>
    eliasGamma p.1 ++
      (if h : p.2 < p.1 then finIdxBits p.1 ⟨p.2, h⟩ else [])
  have heq_on : Set.EqOn raw depPairCode D := by
    intro p hp
    simp only [raw, depPairCode, dite_eq_left hp.2]
  have hfst_sub : Prod.fst '' D ⊆ {m : ℕ | 1 ≤ m} := by
    rintro _ ⟨p, hp, rfl⟩
    exact hp.1
  have hinj₁ : Set.InjOn eliasGamma (Prod.fst '' D) := injOn_eliasGamma.mono hfst_sub
  have hpf₁ : IsPrefixFree (eliasGamma '' (Prod.fst '' D)) :=
    isPrefixFree_eliasGamma.anti (Set.image_mono hfst_sub)
  have hinj_raw : Set.InjOn raw D := by
    refine injOn_prod_append (D := D) (enc₁ := eliasGamma)
      (enc₂ := fun a b => if h : b < a then finIdxBits a ⟨b, h⟩ else []) hinj₁ hpf₁ ?_
    intro a b₁ hb₁ b₂ hb₂ heq
    have h₁ : b₁ < a := hb₁.2
    have h₂ : b₂ < a := hb₂.2
    simp only [dite_eq_left h₁, dite_eq_left h₂] at heq
    exact congrArg Fin.val (finIdxBits_injective a heq)
  have hpf_raw : IsPrefixFree (raw '' D) := by
    refine isPrefixFree_prod_append (D := D) (enc₁ := eliasGamma)
      (enc₂ := fun a b => if h : b < a then finIdxBits a ⟨b, h⟩ else []) hinj₁ hpf₁ ?_
    intro a
    refine (isPrefixFree_range_finIdxBits a).anti ?_
    rintro _ ⟨b, hb, rfl⟩
    have hba : b < a := hb.2
    exact ⟨⟨b, hba⟩, by simp [dite_eq_left hba]⟩
  exact ⟨hinj_raw.congr heq_on, heq_on.image_eq ▸ hpf_raw⟩

/-! ### 3. Kraft–Gibbs entropy and conditional entropy compression checks -/

/-- On `uniformOfFintype (Fin 4)`, `finIdxBits 4` achieves the exact `2`-bit entropy bound. -/
theorem uniform_fin4_kraft_tight :
    let p := uniformOfFintype (Fin 4)
    entropy p ≤ ∑ i : Fin 4, (p i).toReal * ((finIdxBits 4 i).length : ℝ) ∧
      (∑ i : Fin 4, (p i).toReal * ((finIdxBits 4 i).length : ℝ)) = 2 := by
  intro p
  refine ⟨entropy_le_expected_length_of_isPrefixFree p (finIdxBits 4)
    (finIdxBits_injective 4).injOn
    ((isPrefixFree_range_finIdxBits 4).anti (Set.image_subset_range _ _)), ?_⟩
  have hclog : (Nat.clog 2 4 : ℝ) = 2 := by
    have : Nat.clog 2 4 = 2 := by decide
    exact_mod_cast this
  simp only [length_finIdxBits, hclog, ← Finset.sum_mul, sum_toReal p, one_mul]

/-- Conditional compression bound on a joint observation-dependent variable-length code. -/
theorem conditional_kraft_nonvacuous :
    let joint : _root_.PMF (Bool × Fin 4) :=
      (uniformOfFintype Bool).bind fun b =>
        (if b then _root_.PMF.pure (0 : Fin 4) else uniformOfFintype (Fin 4)).map (b, ·)
    let enc : Bool → Fin 4 → List Bool := fun b i =>
      if b then [] else finIdxBits 4 i
    conditionalEntropy joint ≤ ∑ oa, (joint oa).toReal * ((enc oa.1 oa.2).length : ℝ) := by
  intro joint enc
  refine conditionalEntropy_le_expected_length_of_isPrefixFree joint enc ?_ ?_
  · intro obs _
    cases obs
    · simpa [enc] using (finIdxBits_injective 4).injOn
    · intro x hx y hy _
      have hfst : true ∈ (uniformOfFintype Bool).support := by
        simp [_root_.PMF.mem_support_iff]
      have hcond := conditionalSnd_bind_pair (uniformOfFintype Bool)
        (fun b => if b then _root_.PMF.pure (0 : Fin 4) else uniformOfFintype (Fin 4))
        true hfst
      rw [hcond] at hx hy
      simp only [ite_true, _root_.PMF.support_pure, Set.mem_singleton_iff] at hx hy
      exact hx.trans hy.symm
  · intro obs _
    cases obs
    · exact (isPrefixFree_range_finIdxBits 4).anti
        (by rintro _ ⟨i, _, rfl⟩; exact ⟨i, rfl⟩)
    · refine isPrefixFree_of_length_eq (k := 0) ?_
      rintro _ ⟨i, _, rfl⟩
      rfl

/-! ### 4. Non-vacuous set-separator instantiation beating the `(S + 1)`-bit trivial code -/

/-- Explicit distribution over two sparse disjoint subset pairs of `Fin 20`, verifying separation
(including `mem_sepSet`), expected bit length `≤ 15 < 20` (strictly below the `20`-bit truth table
and `21`-bit fallback encoding on `Fin 20`), and self-delimiting concatenation with a subsequent
fixed-width field. -/
theorem separator_code_nonvacuous_and_composable :
    let pair₁ : Finset (Fin 20) × Finset (Fin 20) := ({0, 1}, {2, 4})
    let pair₂ : Finset (Fin 20) × Finset (Fin 20) := ({3}, {0, 19})
    let supp : Finset (Finset (Fin 20) × Finset (Fin 20)) := {pair₁, pair₂}
    have hne : supp.Nonempty := ⟨pair₁, Finset.mem_insert_self pair₁ _⟩
    let μ : _root_.PMF (Finset (Fin 20) × Finset (Fin 20)) := uniformOfFinset supp hne
    ∃ (enc : Finset (Fin 20) × Finset (Fin 20) → List Bool)
      (sep : List Bool → Fin 20 → Bool),
      IsPrefixFree (Set.range (fun p : (Finset (Fin 20) × Finset (Fin 20)) × Fin 3 =>
        enc p.1 ++ finIdxBits 3 p.2)) ∧
      (0 : Fin 20) ∈ sepSet sep (enc pair₁) ∧ (2 : Fin 20) ∉ sepSet sep (enc pair₁) ∧
      pair₁.1 ⊆ sepSet sep (enc pair₁) ∧ Disjoint pair₁.2 (sepSet sep (enc pair₁)) ∧
      pair₂.1 ⊆ sepSet sep (enc pair₂) ∧ Disjoint pair₂.2 (sepSet sep (enc pair₂)) ∧
      ∑ ab, (μ ab).toReal * ((enc ab).length : ℝ) ≤ 15 := by
  intro pair₁ pair₂ supp hne μ
  have hdisj : ∀ ab ∈ μ.support, Disjoint ab.1 ab.2 := by
    intro ab hab
    rw [mem_support_uniformOfFinset_iff] at hab
    simp only [supp, Finset.mem_insert, Finset.mem_singleton] at hab
    rcases hab with rfl | rfl <;> decide
  obtain ⟨enc, sep, hpf, hsep, hlen⟩ := exists_prefixFree_separator_code 20 μ hdisj
  have hcard_le : ∀ ab : Finset (Fin 20) × Finset (Fin 20),
      (μ ab).toReal * ((ab.1.card + ab.2.card : ℕ) : ℝ) ≤ (μ ab).toReal * 4 := by
    intro ab
    by_cases hab : ab ∈ μ.support
    · rw [mem_support_uniformOfFinset_iff] at hab
      simp only [supp, Finset.mem_insert, Finset.mem_singleton] at hab
      have hc : ab.1.card + ab.2.card ≤ 4 := by rcases hab with rfl | rfl <;> decide
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc) ENNReal.toReal_nonneg
    · have h0 : (μ ab).toReal = 0 := by simp [(_root_.PMF.apply_eq_zero_iff μ ab).mpr hab]
      simp [h0]
  have hexp_card : ∑ ab, (μ ab).toReal * ((ab.1.card + ab.2.card : ℕ) : ℝ) ≤ 4 := by
    calc ∑ ab, (μ ab).toReal * ((ab.1.card + ab.2.card : ℕ) : ℝ)
        ≤ ∑ ab, (μ ab).toReal * 4 := Finset.sum_le_sum fun ab _ => hcard_le ab
      _ = 4 := by rw [← Finset.sum_mul, sum_toReal μ, one_mul]
  have hpf_comp : IsPrefixFree
      (Set.range fun p : (Finset (Fin 20) × Finset (Fin 20)) × Fin 3 =>
        enc p.1 ++ finIdxBits 3 p.2) := by
    refine (hpf.bind_append fun _ _ => isPrefixFree_range_finIdxBits 3).anti ?_
    rintro _ ⟨⟨ab, j⟩, rfl⟩
    exact ⟨enc ab, ⟨ab, rfl⟩, finIdxBits 3 j, ⟨j, rfl⟩, rfl⟩
  have h₁ := hsep pair₁.1 pair₁.2 (by decide)
  have hs₁ := subset_sepSet_and_disjoint h₁.1 h₁.2
  have hs₂ := subset_sepSet_and_disjoint (hsep pair₂.1 pair₂.2 (by decide)).1
    (hsep pair₂.1 pair₂.2 (by decide)).2
  have hmem0 : (0 : Fin 20) ∈ sepSet sep (enc pair₁) :=
    mem_sepSet.mpr (h₁.1 0 (by decide))
  have hnmem2 : (2 : Fin 20) ∉ sepSet sep (enc pair₁) := by
    rw [mem_sepSet, h₁.2 2 (by decide)]
    decide
  exact ⟨enc, sep, hpf_comp, hmem0, hnmem2, hs₁.1, hs₁.2, hs₂.1, hs₂.2, by linarith⟩

end CslibTests.SetSeparator

/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.Computability.WordRAM.Realization.Branch
public import CslibFrontier.Computability.WordRAM.Realization.Loop
public import CslibFrontier.Computability.WordRAM.Realization.Primitive
public import CslibFrontier.Computability.WordRAM.Realization.Reindex
public import CslibFrontier.Computability.WordRAM.Realization.Witness
public import CslibFrontier.DataStructure.Dictionary.WordRAM.BitPackedArray
public import CslibFrontier.DataStructure.HashFamily.WordRAM.DoubleTabulation
public import CslibFrontier.DataStructure.HashFamily.WordRAM.Tabulation
public import CslibFrontier.Probability.KWiseIndependent.DoubleTabulation
public import CslibFrontier.Probability.KWiseIndependent.ReducedLimbs
public import CslibFrontier.Probability.PMF.Uniform
public import CslibFrontier.Probability.Uniform
import CslibFrontier.Computability.WordRAM.Width
import CslibFrontier.Tactic.Realize

/-!
# Universe-Reduced Salted General-`q` Bit-Packed Double Tabulation (`[Thorup2013]`)

This module provides a Word-RAM implementation of universe-reduced salted general-`q` double
tabulation hashing with bit-packed lookup tables:

1. **Stage 1 (`multiplyShiftReduced` via `oddMulModWord`)**: maps any key `u : Fin U`
   (`U ≤ 2 ^ w₀`, `0 < w₀ ≤ w`) to a reduced key `rKey ∈ Fin (2 ^ min w₀ R)` without `2 * w₀ ≤ w`
   overflow, failing injectivity on a window `W_set : Finset (Fin U)` with probability at most
   `(#W_set * (#W_set - 1)) / 2 ^ R`.
2. **Stage 2 (salted general-`q` `doubleTabHash` with bit-packed tables)**: appends a salt character
   `s : Fin s_max` (`s_max ≤ 2 ^ b_char`) to the `c_tab` base-`2 ^ b_char` characters of `rKey`
   (`min w₀ R ≤ c_tab * b_char`) and evaluates `(c_tab + 1, d, b_char, M_out)` double tabulation
   with `d = 2 * q * (c_tab + 1)`. Both `T₁` (`(c_tab + 1) * d * 2 ^ b_char` entries of `b_char`
   bits) and `T₂` (`d * 2 ^ b_char` entries of `M_out` bits) are stored in `BitPackedArray`s so the
   total footprint is `≤ (((c_tab + 1) * d * b_char + d * M_out) * 2 ^ b_char + w - 1) / w + 6`
   words for every word width `w > 0` (including `w ≫ n_max`).
3. **Exact uniform resampling (`resampleCode`) and `Memory.Prog` evaluation (`evalGenProg`)**:
   `resampleCode` populates `(α, T₁, T₂)` from the exact uniform distribution in
   `O((topWords + botWords) + 1)` instructions via `Tabulation.randFillLoop`, and `evalGenProg`
   evaluates the hash in `O(c_tab * d)` deterministic instructions via `Memory.Prog` and `realize`
   (`¬ReadsWidth`, single compiled `Code .exact` independent of `(c_tab, d, b_char, M_out, U, w)`).

## Main definitions

* `Cslib.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation.space`,
  `topWords`, `botWords`, `Seed`, `saltedChars`, `evalSalted`, `GoodTop`.
* `Cslib.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation.extractSeed`, `SeedRep`,
  `resampleCode`, `resampleSteps`.
* `Cslib.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation.HashParams`, `mkHashParams`,
  `evalGenProg`, `evalProg`.

## Main results

* `space_le`: bit-packed word-space bound valid for all `w > 0`.
* `isKWiseIndependentHash_evalSalted_of_goodTop`: conditional exact `k`-wise independence on
  `Fin s_max × W_set` whenever `GoodTop` holds.
* `toOuterMeasure_not_goodTop_le`: explicit union bound on `¬ GoodTop` combining
  `toOuterMeasure_not_injOn_multiplyShiftReduced_le` and `card_not_isKUnique_le`.
* `resampleCode_execRand`, `map_extractSeed_eval_resampleComp`: exact `ExecRand` semantics and
  product uniformity of bit-packed seed resampling.
* `realizes_evalGen`, `evalProg_spec`, `validHistory_evalProg`, `memoryCost_evalProg`:
  `Realizes .exact` certificate, functional correctness, memory admissibility, and cost of
  `evalProg`.

## References

* [M. Dietzfelbinger, T. Hagerup, J. Katajainen, M. Penttonen, *A Reliable Randomized Algorithm for
  the Closest-Pair Problem*][DietzfelbingerHagerupKatajainenPenttonen1997]
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation,
  and High Independence*][Thorup2013]
-/

public section

namespace Cslib.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation

open Cslib.WordRAM Cslib.WordRAM.ExactLog Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.Probability Cslib.Probability.PMF
open Finset
open scoped BigOperators ENNReal Cslib.Probability.PMF

/-! ## Section 1: Salted double-tabulation model, conditional `k`-wise independence, and layout -/

/-- Number of entries `(c_tab + 1) * d * 2 ^ b_char` in the top-level bit-packed table `T₁`. -/
abbrev topEntries (c_tab d b_char : ℕ) : ℕ :=
  (c_tab + 1) * d * 2 ^ b_char

/-- Number of entries `d * 2 ^ b_char` in the bottom-level bit-packed table `T₂`. -/
abbrev botEntries (d b_char : ℕ) : ℕ :=
  d * 2 ^ b_char

/-- Number of `w`-bit words storing `T₁` as a `BitPackedArray` of `b_char`-bit entries. -/
@[expose] def topWords (w c_tab d b_char : ℕ) : ℕ :=
  packedWords (topEntries c_tab d b_char) b_char w

/-- Number of `w`-bit words storing `T₂` as a `BitPackedArray` of `M_out`-bit entries. -/
@[expose] def botWords (w d b_char M_out : ℕ) : ℕ :=
  packedWords (botEntries d b_char) M_out w

/-- Word offset `1 + topWords w c_tab d b_char` of the bottom-level bit-packed table `T₂`. -/
@[expose] def offBot (w c_tab d b_char : ℕ) : ℕ :=
  1 + topWords w c_tab d b_char

/-- Total footprint `1 + topWords + botWords` in `w`-bit machine words. -/
@[expose] def space (w c_tab d b_char M_out : ℕ) : ℕ :=
  1 + topWords w c_tab d b_char + botWords w d b_char M_out

theorem space_pos (w c_tab d b_char M_out : ℕ) : 0 < space w c_tab d b_char M_out := by
  unfold space
  omega

/-- Bit-packed word bound valid for every word width `w`:
`space w c_tab d b_char M_out ≤ (topEntries * b_char + botEntries * M_out + w - 1) / w + 6`. -/
theorem space_le (w c_tab d b_char M_out : ℕ) :
    space w c_tab d b_char M_out ≤
      (topEntries c_tab d b_char * b_char + botEntries d b_char * M_out + w - 1) / w + 6 := by
  unfold space topWords botWords
  have h := packedWords_add_le (topEntries c_tab d b_char) b_char (botEntries d b_char) M_out w
  omega

/-- Combined seed type `(α, T₁, T₂)` for universe-reduced salted double tabulation. -/
abbrev Seed (w₀ c_tab d b_char M_out : ℕ) : Type :=
  Fin (2 ^ (w₀ - 1)) × DoubleTabTopSeed (c_tab + 1) d b_char × DoubleTabBotSeed d b_char M_out

/-- Salted `(c_tab + 1)`-character tuple: the first `c_tab` characters extract base-`2 ^ b_char`
digits of the reduced key `rKey`, and the final character at index `c_tab` encodes the salt `s`. -/
@[expose] def saltedChars (c_tab b_char : ℕ) {R' s_max : ℕ} (s : Fin s_max) (rKey : Fin R') :
    Fin (c_tab + 1) → Fin (2 ^ b_char) :=
  Fin.snoc (charDigits c_tab b_char rKey) ⟨s.val % 2 ^ b_char, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Injectivity of `saltedChars` when `s_max ≤ 2 ^ b_char` and `R' ≤ 2 ^ (c_tab * b_char)`. -/
theorem saltedChars_injective {c_tab b_char R' s_max : ℕ}
    (hs : s_max ≤ 2 ^ b_char) (hR' : R' ≤ 2 ^ (c_tab * b_char)) :
    Function.Injective (fun p : Fin s_max × Fin R' => saltedChars c_tab b_char p.1 p.2) := by
  rintro ⟨s₁, r₁⟩ ⟨s₂, r₂⟩ heq
  have hlast := congrFun heq (Fin.last c_tab)
  simp only [saltedChars, Fin.snoc_last, Fin.mk.injEq] at hlast
  rw [Nat.mod_eq_of_lt (s₁.isLt.trans_le hs), Nat.mod_eq_of_lt (s₂.isLt.trans_le hs)] at hlast
  have hinit : charDigits c_tab b_char r₁ = charDigits c_tab b_char r₂ := by
    funext i
    have hi := congrFun heq i.castSucc
    simpa only [saltedChars, Fin.snoc_castSucc] using hi
  exact Prod.ext (Fin.ext hlast) (charDigits_injective hR' hinit)

/-- Universe-reduced salted double tabulation hash mapping `(s, u) : Fin s_max × Fin U` to
`Fin (2 ^ M_out)`. -/
@[expose] def evalSalted (U w₀ R c_tab d b_char M_out s_max : ℕ)
    (θ : Seed w₀ c_tab d b_char M_out) (p : Fin s_max × Fin U) : Fin (2 ^ M_out) :=
  simpleTabEval θ.2.2
    (simpleTabTuple θ.2.1 (saltedChars c_tab b_char p.1 (multiplyShiftReduced U w₀ R θ.1 p.2)))

/-- Good top-seed event on a key window `W_set : Finset (Fin U)`: Stage 1 `multiplyShiftReduced` is
injective on `W_set` and Stage 2 `simpleTabTuple T₁` is `k`-unique. -/
@[expose] def GoodTop (U w₀ R c_tab d b_char k : ℕ) (W_set : Finset (Fin U))
    (α : Fin (2 ^ (w₀ - 1))) (T₁ : DoubleTabTopSeed (c_tab + 1) d b_char) : Prop :=
  Set.InjOn (multiplyShiftReduced U w₀ R α) (W_set : Set (Fin U)) ∧
  IsKUnique k (simpleTabTuple T₁)

/-- **Conditional exact `k`-wise independence on `Fin s_max × W_set`**:
whenever `s_max ≤ 2 ^ b_char`, `min w₀ R ≤ c_tab * b_char`, and `GoodTop` holds for `(α, T₁)`,
the bottom-table family `T₂ ↦ evalSalted ... (α, T₁, T₂)` restricted to `Fin s_max × W_set` is
exact `k`-wise independent. -/
theorem isKWiseIndependentHash_evalSalted_of_goodTop
    {U w₀ R c_tab d b_char M_out s_max k : ℕ} {W_set : Finset (Fin U)}
    {α : Fin (2 ^ (w₀ - 1))} {T₁ : DoubleTabTopSeed (c_tab + 1) d b_char}
    (hs : s_max ≤ 2 ^ b_char) (hcov : min w₀ R ≤ c_tab * b_char)
    (hgood : GoodTop U w₀ R c_tab d b_char k W_set α T₁) :
    IsKWiseIndependentHash k (fun (T₂ : DoubleTabBotSeed d b_char M_out) (p : Fin s_max × W_set) =>
      evalSalted U w₀ R c_tab d b_char M_out s_max (α, T₁, T₂) (p.1, p.2.1)) := by
  have hR' : 2 ^ min w₀ R ≤ 2 ^ (c_tab * b_char) := Nat.pow_le_pow_right two_pos hcov
  have hinj_enc : Function.Injective (fun p : Fin s_max × W_set =>
      saltedChars c_tab b_char p.1 (multiplyShiftReduced U w₀ R α p.2.1)) := by
    rintro ⟨s₁, ⟨u₁, hu₁⟩⟩ ⟨s₂, ⟨u₂, hu₂⟩⟩ heq
    have hprod := @saltedChars_injective c_tab b_char (2 ^ min w₀ R) s_max hs hR'
      (s₁, multiplyShiftReduced U w₀ R α u₁) (s₂, multiplyShiftReduced U w₀ R α u₂) heq
    obtain ⟨rfl, hr_eq⟩ := Prod.mk.inj hprod
    have hu_eq : u₁ = u₂ := hgood.1 hu₁ hu₂ hr_eq
    subst hu_eq
    rfl
  exact isKWiseIndependentHash_of_isKUnique
    (f := fun p : Fin s_max × W_set =>
      simpleTabTuple T₁ (saltedChars c_tab b_char p.1 (multiplyShiftReduced U w₀ R α p.2.1)))
    (hgood.2.comp_injective hinj_enc)

/-- Probability bound on `¬ IsKUnique k (simpleTabTuple T₁)` under `PMF.uniformOfFintype`, lifted
from `Cslib.Probability.card_not_isKUnique_le`. -/
theorem toOuterMeasure_not_isKUnique_le {c d b q k : ℕ} (hc : 1 ≤ c) (hq : 1 ≤ q)
    (hd : d = 2 * q * c) (hbound : 2 * doubleTabCodeBound c d q k ≤ 2 ^ ((q - 1) * b)) :
    (PMF.uniformOfFintype (DoubleTabTopSeed c d b)).toOuterMeasure
      {T₁ | ¬ IsKUnique k (simpleTabTuple T₁)} ≤
      (2 * (doubleTabCodeBound c d q k : ℝ≥0∞) ^ 2) /
        ((2 : ℝ≥0∞) ^ ((q - 1) * b)) ^ 2 := by
  classical
  let Bad := Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b => ¬ IsKUnique k (simpleTabTuple T₁)
  have hset :
      {T₁ : DoubleTabTopSeed c d b | ¬ IsKUnique k (simpleTabTuple T₁)} = (Bad : Set _) := by
    ext T₁
    simp only [Set.mem_ofPred_eq, mem_coe, Bad, mem_filter, mem_univ, true_and]
  rw [hset, PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, sum_const, nsmul_eq_mul, ← div_eq_mul_inv]
  have hcard := card_not_isKUnique_le hc hq hd hbound
  have hN_pos : 0 < Fintype.card (DoubleTabTopSeed c d b) := Fintype.card_pos
  have hN_ne : (Fintype.card (DoubleTabTopSeed c d b) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hN_pos.ne'
  have hN_top : (Fintype.card (DoubleTabTopSeed c d b) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hW_ne : (((2 : ℝ≥0∞) ^ ((q - 1) * b)) ^ 2) ≠ 0 := by positivity
  have hW_top : (((2 : ℝ≥0∞) ^ ((q - 1) * b)) ^ 2) ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top 2))
  rw [ENNReal.div_le_iff_le_mul (Or.inl hN_ne) (Or.inl hN_top), div_eq_mul_inv,
    mul_right_comm _ _⁻¹, ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (Or.inl hW_ne) (Or.inl hW_top)]
  have hcast : ((#Bad : ℝ≥0∞) * (((2 : ℝ≥0∞) ^ ((q - 1) * b)) ^ 2)) =
      ((((2 ^ ((q - 1) * b)) ^ 2 * #Bad : ℕ) : ℝ≥0∞)) := by
    push_cast
    ring
  have hcast_rhs : (2 * (doubleTabCodeBound c d q k : ℝ≥0∞) ^ 2 *
      (Fintype.card (DoubleTabTopSeed c d b) : ℝ≥0∞)) =
      (((2 * (doubleTabCodeBound c d q k) ^ 2 *
        Fintype.card (DoubleTabTopSeed c d b) : ℕ) : ℝ≥0∞)) := by
    push_cast
    ring
  rw [hcast, hcast_rhs]
  exact Nat.cast_le.mpr hcard

/-- **Explicit failure-probability bound on `¬ GoodTop`**:
for a uniform seed `θ : Seed w₀ c_tab d b_char M_out`, when `0 < w₀`, `U ≤ 2 ^ w₀`, `1 ≤ q`,
`d = 2 * q * (c_tab + 1)`, and `2 * doubleTabCodeBound (c_tab + 1) d q k ≤ 2 ^ ((q - 1) * b_char)`,
the probability that `GoodTop U w₀ R c_tab d b_char k W_set θ.1 θ.2.1` fails is at most
`(#W_set * (#W_set - 1)) / 2 ^ R + 2 * (doubleTabCodeBound (c_tab + 1) d q k) ^ 2 /
(2 ^ ((q - 1) * b_char)) ^ 2`. -/
theorem toOuterMeasure_not_goodTop_le
    {U w₀ R c_tab d b_char M_out q k : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    (hq : 1 ≤ q) (hd : d = 2 * q * (c_tab + 1))
    (hbound : 2 * doubleTabCodeBound (c_tab + 1) d q k ≤ 2 ^ ((q - 1) * b_char))
    (W_set : Finset (Fin U)) :
    (PMF.uniformOfFintype (Seed w₀ c_tab d b_char M_out)).toOuterMeasure
      {θ | ¬ GoodTop U w₀ R c_tab d b_char k W_set θ.1 θ.2.1} ≤
      ((#W_set * (#W_set - 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ R +
        (2 * (doubleTabCodeBound (c_tab + 1) d q k : ℝ≥0∞) ^ 2) /
          ((2 : ℝ≥0∞) ^ ((q - 1) * b_char)) ^ 2 := by
  let S₁ : Set (Seed w₀ c_tab d b_char M_out) :=
    {θ | ¬ Set.InjOn (multiplyShiftReduced U w₀ R θ.1) (W_set : Set (Fin U))}
  let S₂ : Set (Seed w₀ c_tab d b_char M_out) :=
    {θ | ¬ IsKUnique k (simpleTabTuple θ.2.1)}
  have hsub : {θ : Seed w₀ c_tab d b_char M_out |
      ¬ GoodTop U w₀ R c_tab d b_char k W_set θ.1 θ.2.1} ⊆ S₁ ∪ S₂ := by
    intro θ hθ
    rw [Set.mem_ofPred_eq, GoodTop, not_and_or] at hθ
    exact hθ
  have hfst : (PMF.uniformOfFintype (Seed w₀ c_tab d b_char M_out)).map Prod.fst =
      PMF.uniformOfFintype (Fin (2 ^ (w₀ - 1))) := by
    dsimp only [Seed]
    exact uniformOfFintype_prod_map_fst
  have hsnd_fst : (PMF.uniformOfFintype (Seed w₀ c_tab d b_char M_out)).map (fun θ => θ.2.1) =
      PMF.uniformOfFintype (DoubleTabTopSeed (c_tab + 1) d b_char) := by
    let eSwap : Seed w₀ c_tab d b_char M_out ≃
        DoubleTabTopSeed (c_tab + 1) d b_char ×
          (Fin (2 ^ (w₀ - 1)) × DoubleTabBotSeed d b_char M_out) :=
      { toFun := fun θ => (θ.2.1, (θ.1, θ.2.2))
        invFun := fun q => (q.2.1, (q.1, q.2.2))
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    have hfn : (fun θ : Seed w₀ c_tab d b_char M_out => θ.2.1) = Prod.fst ∘ eSwap := rfl
    rw [hfn, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv eSwap]
    exact uniformOfFintype_prod_map_fst
  have hm₁ : (PMF.uniformOfFintype (Seed w₀ c_tab d b_char M_out)).toOuterMeasure S₁ =
      (PMF.uniformOfFintype (Fin (2 ^ (w₀ - 1)))).toOuterMeasure
        {α | ¬ Set.InjOn (multiplyShiftReduced U w₀ R α) (W_set : Set (Fin U))} := by
    rw [← hfst, PMF.toOuterMeasure_map_apply]
    rfl
  have hm₂ : (PMF.uniformOfFintype (Seed w₀ c_tab d b_char M_out)).toOuterMeasure S₂ =
      (PMF.uniformOfFintype (DoubleTabTopSeed (c_tab + 1) d b_char)).toOuterMeasure
        {T₁ | ¬ IsKUnique k (simpleTabTuple T₁)} := by
    rw [← hsnd_fst, PMF.toOuterMeasure_map_apply]
    rfl
  let μ := (PMF.uniformOfFintype (Seed w₀ c_tab d b_char M_out)).toOuterMeasure
  calc μ {θ | ¬ GoodTop U w₀ R c_tab d b_char k W_set θ.1 θ.2.1}
      ≤ μ (S₁ ∪ S₂) := μ.mono hsub
    _ ≤ μ S₁ + μ S₂ := MeasureTheory.measure_union_le S₁ S₂
    _ ≤ ((#W_set * (#W_set - 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ R +
          (2 * (doubleTabCodeBound (c_tab + 1) d q k : ℝ≥0∞) ^ 2) /
            ((2 : ℝ≥0∞) ^ ((q - 1) * b_char)) ^ 2 := by
          rw [hm₁, hm₂]
          exact add_le_add
            (toOuterMeasure_not_injOn_multiplyShiftReduced_le hw₀ hU W_set)
            (toOuterMeasure_not_isKUnique_le (by omega) hq hd hbound)

/-! ## Section 2: Bit-packed slice uniformity, `SeedRep`, and `resampleCode` -/

/-- For `0 < w` and `idx < N`, every bit index `idx * k + j` (`j < k`) lies in word
`(idx * k + j) / w < packedWords N k w`. -/
theorem mul_add_div_lt_packedWords {N k w idx j : ℕ} (hw : 0 < w) (hidx : idx < N) (hj : j < k) :
    (idx * k + j) / w < packedWords N k w := by
  unfold packedWords
  have hle : idx * k + j < N * k := by
    calc idx * k + j < idx * k + k := Nat.add_lt_add_left hj _
      _ = (idx + 1) * k := by ring
      _ ≤ N * k := Nat.mul_le_mul_right k hidx
  have hdiv : (idx * k + j) / w ≤ (N * k + w - 1) / w :=
    Nat.div_le_div_right (by omega)
  omega

/-- Exact bit-level characterization of `readPacked`: for `0 < w`, `k ≤ w`, and `j < k`, bit `j` of
`readPacked arrBase k w mem idx` equals bit `(idx * k + j) % w` of word
`mem (arrBase + (idx * k + j) / w)`. -/
theorem testBit_readPacked {arrBase k w : ℕ} (hw : 0 < w) (hkw : k ≤ w) (mem : ℕ → ℕ)
    (idx : ℕ) {j : ℕ} (hj : j < k) :
    (readPacked arrBase k w mem idx).testBit j =
      (mem (arrBase + (idx * k + j) / w)).testBit ((idx * k + j) % w) := by
  unfold readPacked
  dsimp only
  set wOff := wordOffset k w idx
  set bOff := bitOffset k w idx
  set k₀ := lowWidth k w idx
  set k₁ := highWidth k w idx
  have hwOff : wOff = (idx * k) / w := wordOffset_eq_mul_div hw
  have hbOff : bOff = (idx * k) % w := bitOffset_eq_mul_mod k w idx
  have hb_lt : bOff < w := bitOffset_lt hw
  have hk_sum : k₀ + k₁ = k := lowWidth_add_highWidth k w idx
  have hdecomp : idx * k = w * wOff + bOff := by
    rw [hwOff, hbOff]
    exact (Nat.div_add_mod (idx * k) w).symm
  rw [Nat.testBit_xor]
  by_cases hjk₀ : j < k₀
  · have hbj_lt : bOff + j < w := by
      have hk₀_le : k₀ ≤ w - bOff := Nat.min_le_right k (w - bOff)
      omega
    have hhigh_false : ((((mem (arrBase + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)) <<< k₀).testBit j) =
        false := by
      rw [Nat.testBit_shiftLeft]
      simp [not_le.mpr hjk₀]
    have hlow_eq : (((mem (arrBase + wOff) >>> bOff) &&& (2 ^ k₀ - 1)).testBit j) =
        (mem (arrBase + wOff)).testBit (bOff + j) := by
      rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_true hjk₀, Bool.and_true,
        Nat.testBit_shiftRight]
    have hdiv_eq : (idx * k + j) / w = wOff := by
      have heq : idx * k + j = (bOff + j) + w * wOff := by omega
      rw [heq, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hbj_lt, zero_add]
    have hmod_eq : (idx * k + j) % w = bOff + j := by
      have heq : idx * k + j = (bOff + j) + w * wOff := by omega
      rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbj_lt]
    rw [hlow_eq, hhigh_false, Bool.xor_false, hdiv_eq, hmod_eq]
  · have hk₀_le_j : k₀ ≤ j := not_lt.mp hjk₀
    have hk₀_eq : k₀ = w - bOff := by
      dsimp only [k₀, lowWidth] at hk₀_le_j ⊢
      have hlt : w - bOff < k := by omega
      exact Nat.min_eq_right hlt.le
    have hlow_lt : ((mem (arrBase + wOff) >>> bOff) &&& (2 ^ k₀ - 1)) < 2 ^ j := by
      calc ((mem (arrBase + wOff) >>> bOff) &&& (2 ^ k₀ - 1))
          < 2 ^ k₀ := by rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (by positivity)
        _ ≤ 2 ^ j := Nat.pow_le_pow_right two_pos hk₀_le_j
    have hlow_false : (((mem (arrBase + wOff) >>> bOff) &&& (2 ^ k₀ - 1)).testBit j) = false :=
      Nat.testBit_lt_two_pow hlow_lt
    have hj_sub_lt_k₁ : j - k₀ < k₁ := by omega
    have hj_sub_lt_w : j - k₀ < w := by omega
    have hhigh_eq : ((((mem (arrBase + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)) <<< k₀).testBit j) =
        (mem (arrBase + wOff + 1)).testBit (j - k₀) := by
      rw [Nat.testBit_shiftLeft, decide_eq_true hk₀_le_j, Bool.true_and, Nat.testBit_and,
        Nat.testBit_two_pow_sub_one, decide_eq_true hj_sub_lt_k₁, Bool.and_true,
        Nat.shiftRight_zero]
    have hdiv_eq : (idx * k + j) / w = wOff + 1 := by
      have heq : idx * k + j = (j - k₀) + w * (wOff + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      rw [heq, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hj_sub_lt_w, zero_add]
    have hmod_eq : (idx * k + j) % w = j - k₀ := by
      have heq : idx * k + j = (j - k₀) + w * (wOff + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj_sub_lt_w]
    rw [hlow_false, Bool.false_xor, hhigh_eq, hdiv_eq, hmod_eq, Nat.add_assoc]

/-- Extract `N` bit-packed `k`-bit entries from `mem` starting at `arrBase`. -/
@[expose] def extractPackedSlice (arrBase N k w : ℕ) (mem : ℕ → ℕ) : Fin N → Fin (2 ^ k) :=
  fun i => ⟨readPacked arrBase k w mem i.val, readPacked_lt arrBase k w mem i.val⟩

/-- Additive homomorphism projecting `packedWords N k w` `w`-bit strings onto `N` `k`-bit strings
by reading bits `[idx * k, (idx + 1) * k)`. -/
@[expose] def bitPackedProjHom (N k w : ℕ) (hw : 0 < w) :
    (Fin (packedWords N k w) → BitString w) →+ (Fin N → BitString k) where
  toFun words i j :=
    words ⟨(i.val * k + j.val) / w, mul_add_div_lt_packedWords hw i.isLt j.isLt⟩
      ⟨(i.val * k + j.val) % w, Nat.mod_lt _ hw⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem surjective_bitPackedProjHom {N k w : ℕ} (hw : 0 < w) :
    Function.Surjective (bitPackedProjHom N k w hw) := by
  intro target
  have hk_pos_of_mem : ∀ m < N * k, 0 < k := by
    intro m hm
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hm
    · exact hk
  refine ⟨fun q r =>
    if hm : q.val * w + r.val < N * k then
      let hk := hk_pos_of_mem _ hm
      target ⟨(q.val * w + r.val) / k,
        Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm k N]; exact hm)⟩
        ⟨(q.val * w + r.val) % k, Nat.mod_lt _ hk⟩
    else false, ?_⟩
  funext i j
  dsimp only [bitPackedProjHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  have hm_eq : ((i.val * k + j.val) / w) * w + (i.val * k + j.val) % w = i.val * k + j.val := by
    rw [Nat.mul_comm _ w]
    exact Nat.div_add_mod (i.val * k + j.val) w
  have hm_lt : ((i.val * k + j.val) / w) * w + (i.val * k + j.val) % w < N * k := by
    rw [hm_eq]
    calc i.val * k + j.val < i.val * k + k := Nat.add_lt_add_left j.isLt _
      _ = (i.val + 1) * k := by ring
      _ ≤ N * k := Nat.mul_le_mul_right k i.isLt
  have hk_pos : 0 < k := Nat.zero_lt_of_lt j.isLt
  rw [dite_eq_left hm_lt]
  have hdiv : (((i.val * k + j.val) / w) * w + (i.val * k + j.val) % w) / k = i.val := by
    rw [hm_eq, Nat.add_comm, Nat.mul_comm i.val k, Nat.add_mul_div_left _ _ hk_pos,
      Nat.div_eq_of_lt j.isLt, zero_add]
  have hmod : (((i.val * k + j.val) / w) * w + (i.val * k + j.val) % w) % k = j.val := by
    rw [hm_eq, Nat.add_comm, Nat.mul_comm i.val k, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt j.isLt]
  congr 1
  · exact Fin.ext hdiv
  · exact Fin.ext hmod

/-- Map from a raw `w`-bit word slice `Fin (packedWords N k w) → Fin (2 ^ w)` to
`Fin N → Fin (2 ^ k)` matching `extractPackedSlice`. -/
@[expose] def packedSliceOfWords (N k w : ℕ) (hw : 0 < w)
    (words : Fin (packedWords N k w) → Fin (2 ^ w)) : Fin N → Fin (2 ^ k) :=
  (Equiv.piCongrRight fun _ : Fin N => BitString.equivFin k)
    (bitPackedProjHom N k w hw
      ((Equiv.piCongrRight fun _ : Fin (packedWords N k w) => (BitString.equivFin w).symm) words))

theorem extractPackedSlice_eq_packedSliceOfWords {arrBase N k w : ℕ} (hw : 0 < w) (hkw : k ≤ w)
    {mem : ℕ → ℕ} (hmem : ∀ q < packedWords N k w, mem (arrBase + q) < 2 ^ w) :
    extractPackedSlice arrBase N k w mem =
      packedSliceOfWords N k w hw (Tabulation.extractSlice arrBase w (packedWords N k w) mem) := by
  funext i
  apply (BitString.equivFin k).symm.injective
  funext j
  rw [BitString.equivFin_symm_apply]
  change (readPacked arrBase k w mem i.val).testBit j.val =
    (BitString.equivFin k).symm
      (BitString.equivFin k
        (bitPackedProjHom N k w hw
          ((Equiv.piCongrRight fun _ => (BitString.equivFin w).symm)
            (Tabulation.extractSlice arrBase w (packedWords N k w) mem))
          i)) j
  rw [Equiv.symm_apply_apply, testBit_readPacked hw hkw mem i.val j.isLt]
  change _ =
    ((BitString.equivFin w).symm
      (wordOfNat w (mem (arrBase + (i.val * k + j.val) / w))))
      ⟨(i.val * k + j.val) % w, Nat.mod_lt _ hw⟩
  rw [BitString.equivFin_symm_apply,
    wordOfNat_val_of_lt (hmem _ (mul_add_div_lt_packedWords hw i.isLt j.isLt))]

/-- Pushforward of `PMF.uniformOfFintype (Fin (packedWords N k w) → Fin (2 ^ w))` along
`packedSliceOfWords` is `PMF.uniformOfFintype (Fin N → Fin (2 ^ k))`. -/
theorem uniformOfFintype_map_packedSliceOfWords (N k w : ℕ) (hw : 0 < w) :
    (PMF.uniformOfFintype (Fin (packedWords N k w) → Fin (2 ^ w))).map
      (packedSliceOfWords N k w hw) =
      PMF.uniformOfFintype (Fin N → Fin (2 ^ k)) := by
  let e_in : (Fin (packedWords N k w) → Fin (2 ^ w)) ≃ (Fin (packedWords N k w) → BitString w) :=
    Equiv.piCongrRight fun _ => (BitString.equivFin w).symm
  let e_out : (Fin N → BitString k) ≃ (Fin N → Fin (2 ^ k)) :=
    Equiv.piCongrRight fun _ => BitString.equivFin k
  have hfn : packedSliceOfWords N k w hw = e_out ∘ bitPackedProjHom N k w hw ∘ e_in := rfl
  rw [hfn, ← PMF.map_comp, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv e_in,
    PMF.uniformOfFintype_map_addHom (bitPackedProjHom N k w hw) (surjective_bitPackedProjHom hw),
    PMF.uniformOfFintype_map_equiv e_out]

/-- Extract the full seed `(α, T₁, T₂)` from `[base, base + space w c_tab d b_char M_out)`. -/
@[expose] def extractSeed (base w w₀ c_tab d b_char M_out : ℕ) (mem : ℕ → ℕ) :
    Seed w₀ c_tab d b_char M_out :=
  (wordOfNat (w₀ - 1) (mem base),
    DoubleTabulation.topSliceEquiv (c_tab + 1) d b_char
      (extractPackedSlice (base + 1) (topEntries c_tab d b_char) b_char w mem),
    DoubleTabulation.botSliceEquiv d b_char M_out
      (extractPackedSlice (base + offBot w c_tab d b_char) (botEntries d b_char) M_out w mem))

/-- Representation predicate for `(α, T₁, T₂)` in `[base, base + space w c_tab d b_char M_out)`. -/
@[expose] def SeedRep (base w w₀ c_tab d b_char M_out : ℕ)
    (θ : Seed w₀ c_tab d b_char M_out) (mem : ℕ → ℕ) : Prop :=
  mem base = θ.1.val ∧
  (∀ (i : Fin (c_tab + 1)) (j : Fin d) (ch : Fin (2 ^ b_char)),
    readPacked (base + 1) b_char w mem ((j.val * (c_tab + 1) + i.val) * 2 ^ b_char + ch.val) =
      (θ.2.1 i j ch).val) ∧
  (∀ (j : Fin d) (y : Fin (2 ^ b_char)),
    readPacked (base + offBot w c_tab d b_char) M_out w mem (j.val * 2 ^ b_char + y.val) =
      (θ.2.2 j y).val)

theorem seedRep_extractSeed {base w w₀ c_tab d b_char M_out : ℕ} {mem : ℕ → ℕ}
    (hα : mem base < 2 ^ (w₀ - 1)) :
    SeedRep base w w₀ c_tab d b_char M_out
      (extractSeed base w w₀ c_tab d b_char M_out mem) mem := by
  refine ⟨(wordOfNat_val_of_lt hα).symm, ?_, ?_⟩
  · intro i j ch
    change readPacked (base + 1) b_char w mem _ =
      readPacked (base + 1) b_char w mem
        (DoubleTabulation.topIndexEquiv (c_tab + 1) d b_char (i, j, ch)).val
    rw [DoubleTabulation.val_topIndexEquiv]
  · intro j y
    change readPacked (base + offBot w c_tab d b_char) M_out w mem _ =
      readPacked (base + offBot w c_tab d b_char) M_out w mem (finProdFinEquiv (j, y)).val
    rw [finProdFinEquiv_apply_val]
    congr 1
    dsimp only
    ring

theorem extractSeed_eq_of_seedRep {base w w₀ c_tab d b_char M_out : ℕ}
    {θ : Seed w₀ c_tab d b_char M_out} {mem : ℕ → ℕ}
    (hrep : SeedRep base w w₀ c_tab d b_char M_out θ mem) :
    extractSeed base w w₀ c_tab d b_char M_out mem = θ := by
  rcases θ with ⟨α, T₁, T₂⟩
  rcases hrep with ⟨hα, hT₁, hT₂⟩
  apply Prod.ext
  · apply Fin.ext
    dsimp only [extractSeed]
    rw [hα, wordOfNat_val_of_lt α.isLt]
  · apply Prod.ext
    · funext i j ch
      apply Fin.ext
      change readPacked (base + 1) b_char w mem
        (DoubleTabulation.topIndexEquiv (c_tab + 1) d b_char (i, j, ch)).val = (T₁ i j ch).val
      rw [DoubleTabulation.val_topIndexEquiv]
      exact hT₁ i j ch
    · funext j y
      apply Fin.ext
      change readPacked (base + offBot w c_tab d b_char) M_out w mem
        (finProdFinEquiv (j, y)).val = (T₂ j y).val
      rw [finProdFinEquiv_apply_val]
      rw [show (j, y).2.val + 2 ^ b_char * (j, y).1.val = j.val * 2 ^ b_char + y.val by
        dsimp only; ring]
      exact hT₂ j y

theorem seedRep_congr_mem {base w w₀ c_tab d b_char M_out : ℕ}
    {θ : Seed w₀ c_tab d b_char M_out} {mem mem' : ℕ → ℕ} (hw : 0 < w)
    (hrep : SeedRep base w w₀ c_tab d b_char M_out θ mem)
    (heq : ∀ a, base ≤ a → a < base + space w c_tab d b_char M_out → mem' a = mem a) :
    SeedRep base w w₀ c_tab d b_char M_out θ mem' := by
  have hsp_eq : space w c_tab d b_char M_out =
      1 + topWords w c_tab d b_char + botWords w d b_char M_out := rfl
  refine ⟨(heq base le_rfl (by omega)).trans hrep.1, ?_, ?_⟩
  · intro i j ch
    have hidx :
        (j.val * (c_tab + 1) + i.val) * 2 ^ b_char + ch.val < topEntries c_tab d b_char := by
      have h := DoubleTabulation.topAddr_lt_base_add_topWords 0 (c_tab + 1) d b_char i j ch
      dsimp only [DoubleTabulation.topAddr, DoubleTabulation.topWords, topEntries] at h ⊢
      omega
    rw [readPacked_congr hw (fun a ⟨ha1, ha2⟩ =>
      heq a (by omega) (by dsimp only [topWords] at hsp_eq; omega)) hidx]
    exact hrep.2.1 i j ch
  · intro j y
    have hidx : j.val * 2 ^ b_char + y.val < botEntries d b_char := by
      calc j.val * 2 ^ b_char + y.val
          < j.val * 2 ^ b_char + 2 ^ b_char := Nat.add_lt_add_left y.isLt _
        _ = (j.val + 1) * 2 ^ b_char := by ring
        _ ≤ d * 2 ^ b_char := Nat.mul_le_mul_right _ j.isLt
    rw [readPacked_congr hw (fun a ⟨ha1, ha2⟩ =>
      heq a (by unfold offBot at ha1; omega)
        (by dsimp only [offBot, botWords] at ha2 hsp_eq ⊢; omega)) hidx]
    exact hrep.2.2 j y

/-! ### Single-pass `randFillLoop` seed resampling (`resampleCode`) -/

/-- Combined additive homomorphism projecting `topWords + botWords` `w`-bit strings onto the pair of
bit-packed slices `(Fin topEntries → BitString b_char) × (Fin botEntries → BitString M_out)`. -/
@[expose] def bothPackedProjHom (w c_tab d b_char M_out : ℕ) (hw : 0 < w) :
    (Fin (topWords w c_tab d b_char + botWords w d b_char M_out) → BitString w) →+
      (Fin (topEntries c_tab d b_char) → BitString b_char) ×
        (Fin (botEntries d b_char) → BitString M_out) where
  toFun words :=
    (bitPackedProjHom (topEntries c_tab d b_char) b_char w hw
        (fun q => words (Fin.castAdd (botWords w d b_char M_out) q)),
      bitPackedProjHom (botEntries d b_char) M_out w hw
        (fun q => words (Fin.natAdd (topWords w c_tab d b_char) q)))
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem surjective_bothPackedProjHom {w c_tab d b_char M_out : ℕ} (hw : 0 < w) :
    Function.Surjective (bothPackedProjHom w c_tab d b_char M_out hw) := by
  rintro ⟨t₁, t₂⟩
  obtain ⟨w₁, hw₁⟩ := surjective_bitPackedProjHom (N := topEntries c_tab d b_char)
    (k := b_char) hw t₁
  obtain ⟨w₂, hw₂⟩ := surjective_bitPackedProjHom (N := botEntries d b_char)
    (k := M_out) hw t₂
  refine ⟨Fin.addCases w₁ w₂, ?_⟩
  dsimp only [bothPackedProjHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  have hl : (fun q => Fin.addCases w₁ w₂ (Fin.castAdd (botWords w d b_char M_out) q)) = w₁ :=
    funext fun q => Fin.addCases_left q
  have hr : (fun q => Fin.addCases w₁ w₂ (Fin.natAdd (topWords w c_tab d b_char) q)) = w₂ :=
    funext fun q => Fin.addCases_right q
  exact Prod.ext
    ((congrArg (bitPackedProjHom (topEntries c_tab d b_char) b_char w hw) hl).trans hw₁)
    ((congrArg (bitPackedProjHom (botEntries d b_char) M_out w hw) hr).trans hw₂)

/-- Extract `(T₁, T₂)` from a combined `(topWords + botWords)`-word slice of `< 2 ^ w` words. -/
@[expose] def tablesOfWords (w c_tab d b_char M_out : ℕ) (hw : 0 < w)
    (words : Fin (topWords w c_tab d b_char + botWords w d b_char M_out) → Fin (2 ^ w)) :
    DoubleTabTopSeed (c_tab + 1) d b_char × DoubleTabBotSeed d b_char M_out :=
  let pair := bothPackedProjHom w c_tab d b_char M_out hw
    ((Equiv.piCongrRight fun _ => (BitString.equivFin w).symm) words)
  (DoubleTabulation.topSliceEquiv (c_tab + 1) d b_char
      ((Equiv.piCongrRight fun _ => BitString.equivFin b_char) pair.1),
    DoubleTabulation.botSliceEquiv d b_char M_out
      ((Equiv.piCongrRight fun _ => BitString.equivFin M_out) pair.2))

theorem uniformOfFintype_map_tablesOfWords (w c_tab d b_char M_out : ℕ) (hw : 0 < w) :
    (PMF.uniformOfFintype
      (Fin (topWords w c_tab d b_char + botWords w d b_char M_out) → Fin (2 ^ w))).map
        (tablesOfWords w c_tab d b_char M_out hw) =
      PMF.uniformOfFintype
        (DoubleTabTopSeed (c_tab + 1) d b_char × DoubleTabBotSeed d b_char M_out) := by
  let e_in :
      (Fin (topWords w c_tab d b_char + botWords w d b_char M_out) → Fin (2 ^ w)) ≃
        (Fin (topWords w c_tab d b_char + botWords w d b_char M_out) → BitString w) :=
    Equiv.piCongrRight fun _ => (BitString.equivFin w).symm
  let e_out :
      ((Fin (topEntries c_tab d b_char) → BitString b_char) ×
        (Fin (botEntries d b_char) → BitString M_out)) ≃
        (DoubleTabTopSeed (c_tab + 1) d b_char × DoubleTabBotSeed d b_char M_out) :=
    Equiv.prodCongr
      ((Equiv.piCongrRight fun _ => BitString.equivFin b_char).trans
        (DoubleTabulation.topSliceEquiv (c_tab + 1) d b_char))
      ((Equiv.piCongrRight fun _ => BitString.equivFin M_out).trans
        (DoubleTabulation.botSliceEquiv d b_char M_out))
  have hfn : tablesOfWords w c_tab d b_char M_out hw =
      e_out ∘ bothPackedProjHom w c_tab d b_char M_out hw ∘ e_in := rfl
  rw [hfn, ← PMF.map_comp, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv e_in,
    PMF.uniformOfFintype_map_addHom _ (surjective_bothPackedProjHom hw),
    PMF.uniformOfFintype_map_equiv e_out]

/-- Structured Word-RAM program on `Data 12` (keeping `reg 0 = base`) that samples `(α, T₁, T₂)`
into `[base, base + space w c_tab d b_char M_out)`. -/
@[expose] def resampleCode (w w₀ c_tab d b_char M_out : ℕ) : Code .exact 12 :=
  .seq (.seq (.op (.const 5 (2 ^ (w₀ - 1) - 1))) (.rand 7 5))
    (.seq
      (.seq (.op (.store 0 7))
      (.seq (.op (.const 6 1))
      (.seq (.op (.exactBin .add 3 0 6))
      (.seq (.op (.const 4 (space w c_tab d b_char M_out)))
      (.seq (.op (.exactBin .add 4 0 4))
            (.op (.const 5 (2 ^ w - 1))))))))
      (Tabulation.randFillLoop.rename DoubleTabulation.fillMap12))

/-- Instruction count `5 * (topWords + botWords) + 10` of `resampleCode`. -/
@[expose] def resampleSteps (w c_tab d b_char M_out : ℕ) : ℕ :=
  5 * (topWords w c_tab d b_char + botWords w d b_char M_out) + 10

/-- Explicit `ProbComp (Data 12 × ℕ)` induced by `resampleCode`. -/
@[expose] noncomputable def resampleComp (base w w₀ c_tab d b_char M_out : ℕ) (x : Data 12) :
    ProbComp (Data 12 × ℕ) := do
  let kα ← ProbComp.unifFin (2 ^ (w₀ - 1) - 1)
  let x1 := (((((((x.set 5 (2 ^ (w₀ - 1) - 1)).set 7 kα.val).write base kα.val).set 6 1).set 3
    (base + 1)).set 4 (base + space w c_tab d b_char M_out)).set 5 (2 ^ w - 1))
  let z ← Tabulation.randFillComp w (base + 1)
    (topWords w c_tab d b_char + botWords w d b_char M_out)
    (x1.comap DoubleTabulation.fillMap12)
  pure (z.1.extend DoubleTabulation.fillMap12 x1, 2 + (6 + z.2))

theorem resampleCode_execRand {w w₀ base c_tab d b_char M_out : ℕ} {x : Data 12}
    (hw : 0 < w) (hw₀_le : w₀ ≤ w) (hbase : x.regs 0 = base)
    (hfit_end : Fits w (base + space w c_tab d b_char M_out)) :
    ExecRand w (resampleCode w w₀ c_tab d b_char M_out) x
      (resampleComp base w w₀ c_tab d b_char M_out x) := by
  have hfit_mask_α : Fits w (2 ^ (w₀ - 1) - 1) := by
    have hle : w₀ - 1 < w := by omega
    calc 2 ^ (w₀ - 1) - 1 < 2 ^ (w₀ - 1) := Nat.sub_lt (Nat.two_pow_pos _) one_pos
      _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hle.le
  have hfit_mask_w : Fits w (2 ^ w - 1) := Nat.sub_lt (Nat.two_pow_pos w) one_pos
  have hfit_one : Fits w 1 := by
    change 1 < 2 ^ w
    exact Nat.one_lt_two_pow hw.ne'
  have hfit_sp : Fits w (space w c_tab d b_char M_out) := hfit_end.of_le (by omega)
  have hfit_b1 : Fits w (base + 1) :=
    hfit_end.of_le (by have := space_pos w c_tab d b_char M_out; omega)
  set d0 := x.set 5 (2 ^ (w₀ - 1) - 1)
  have s1 : Exec w (.op (.const 5 (2 ^ (w₀ - 1) - 1)) : Code .exact 12) x d0 1 :=
    Exec.const hfit_mask_α
  have s2_raw := ExecRand.rand (B := .exact) (w := w) (dst := (7 : Fin 12)) (src := (5 : Fin 12))
    (x := d0) (by simp +decide [d0, hfit_mask_α])
  have hr5_d0 : d0.regs 5 = 2 ^ (w₀ - 1) - 1 := by simp +decide [d0]
  rw [hr5_d0] at s2_raw
  have s12 := ExecRand.seq
    (m₂ := fun z => do
      let k ← ProbComp.unifFin (2 ^ (w₀ - 1) - 1)
      pure (z.set 7 k.val, 1))
    s1.execRand (fun z hz => by cases OracleComp.eq_of_mem_supportWith_pure hz; exact s2_raw)
  have s_rest : ∀ z ∈ (do
      let k ← ProbComp.unifFin (2 ^ (w₀ - 1) - 1)
      pure (d0.set 7 k.val, 1 + 1) : ProbComp (Data 12 × ℕ)).support,
      ExecRand w
        (.seq
          (.seq (.op (.store 0 7))
          (.seq (.op (.const 6 1))
          (.seq (.op (.exactBin .add 3 0 6))
          (.seq (.op (.const 4 (space w c_tab d b_char M_out)))
          (.seq (.op (.exactBin .add 4 0 4))
                (.op (.const 5 (2 ^ w - 1))))))))
          (Tabulation.randFillLoop.rename DoubleTabulation.fillMap12))
        z.1
        (do
          let x1 := ((((((z.1.write base (z.1.regs 7)).set 6 1).set 3 (base + 1)).set 4
            (base + space w c_tab d b_char M_out)).set 5 (2 ^ w - 1)))
          let zf ← Tabulation.randFillComp w (base + 1)
            (topWords w c_tab d b_char + botWords w d b_char M_out)
            (x1.comap DoubleTabulation.fillMap12)
          pure (zf.1.extend DoubleTabulation.fillMap12 x1, 6 + zf.2)) := by
    intro z hz
    obtain ⟨k, -, hk⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    cases OracleComp.eq_of_mem_supportWith_pure hk
    set a0 := d0.set 7 k.val
    have ha0_0 : a0.regs 0 = base := by simp +decide [a0, d0, hbase]
    have ha0_7 : a0.regs 7 = k.val := by simp +decide [a0]
    set a1 := a0.write base k.val
    have e1 : Exec w (.op (.store 0 7) : Code .exact 12) a0 a1 1 := by
      simpa [a1, ha0_0, ha0_7] using (Exec.store (B := .exact) (w := w) (a := 0) (s := 7) (x := a0))
    set a2 := a1.set 6 1
    have e2 : Exec w (.op (.const 6 1) : Code .exact 12) a1 a2 1 := Exec.const hfit_one
    set a3 := a2.set 3 (base + 1)
    have e3 : Exec w (.op (.exactBin .add 3 0 6) : Code .exact 12) a2 a3 1 := by
      apply Exec.op
      rw [Op.eval_exactBin]
      have h0 : a2.regs 0 = base := by simp +decide [a2, a1, Data.write, ha0_0]
      have h6 : a2.regs 6 = 1 := by simp +decide [a2]
      rw [h0, h6]
      exact Data.put_of_fits hfit_b1
    set a4 := a3.set 4 (space w c_tab d b_char M_out)
    have e4 : Exec w (.op (.const 4 (space w c_tab d b_char M_out)) : Code .exact 12) a3 a4 1 :=
      Exec.const hfit_sp
    set a5 := a4.set 4 (base + space w c_tab d b_char M_out)
    have e5 : Exec w (.op (.exactBin .add 4 0 4) : Code .exact 12) a4 a5 1 := by
      apply Exec.op
      rw [Op.eval_exactBin]
      have h0 : a4.regs 0 = base := by simp +decide [a4, a3, a2, a1, Data.write, ha0_0]
      have h4 : a4.regs 4 = space w c_tab d b_char M_out := by simp +decide [a4]
      rw [h0, h4]
      exact Data.put_of_fits hfit_end
    set a6 := a5.set 5 (2 ^ w - 1)
    have e6 : Exec w (.op (.const 5 (2 ^ w - 1)) : Code .exact 12) a5 a6 1 :=
      Exec.const hfit_mask_w
    have edet : Exec w
        (.seq (.op (.store 0 7))
        (.seq (.op (.const 6 1))
        (.seq (.op (.exactBin .add 3 0 6))
        (.seq (.op (.const 4 (space w c_tab d b_char M_out)))
        (.seq (.op (.exactBin .add 4 0 4))
              (.op (.const 5 (2 ^ w - 1)))))))) a0 a6 6 :=
      e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))
    have hsp_eq : (base + 1) + (topWords w c_tab d b_char + botWords w d b_char M_out) =
        base + space w c_tab d b_char M_out := by
      unfold space; omega
    have hloop_in := Tabulation.randFillLoop_execRand (w := w) (bits := w) (arrBase := base + 1)
      (topWords w c_tab d b_char + botWords w d b_char M_out)
      (x := a6.comap DoubleTabulation.fillMap12)
      (by simp +decide [a6, a5, a4, a3, DoubleTabulation.fillMap12, Data.comap])
      (by simp +decide [a6, a5, DoubleTabulation.fillMap12, Data.comap, hsp_eq])
      (by simp +decide [a6, DoubleTabulation.fillMap12, Data.comap])
      (by simp +decide [a6, a5, a4, a3, a2, DoubleTabulation.fillMap12, Data.comap])
      (by rwa [hsp_eq]) hfit_mask_w
    have hloop := hloop_in.rename DoubleTabulation.injective_fillMap12
    have ha6 : a6 = (((((a0.write base k.val).set 6 1).set 3 (base + 1)).set 4
        (base + space w c_tab d b_char M_out)).set 5 (2 ^ w - 1)) := by
      dsimp only [a6, a5, a4, a3, a2, a1]
      congr 1
      ext i <;> simp [Data.set]
    have hseq := ExecRand.seq
      (m₂ := fun zf_in : Data 12 =>
        (fun zf : Data 6 × ℕ => (zf.1.extend DoubleTabulation.fillMap12 zf_in, zf.2)) <$>
          Tabulation.randFillComp w (base + 1)
            (topWords w c_tab d b_char + botWords w d b_char M_out)
            (zf_in.comap DoubleTabulation.fillMap12))
      edet.execRand (fun zf_in hz_in => by
        cases OracleComp.eq_of_mem_supportWith_pure hz_in
        exact hloop)
    rw [ha6] at hseq
    simpa only [ha0_7, bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def] using hseq
  have hall := ExecRand.seq
    (c₁ := .seq (.op (.const 5 (2 ^ (w₀ - 1) - 1))) (.rand 7 5))
    (c₂ := .seq
        (.seq (.op (.store 0 7))
        (.seq (.op (.const 6 1))
        (.seq (.op (.exactBin .add 3 0 6))
        (.seq (.op (.const 4 (space w c_tab d b_char M_out)))
        (.seq (.op (.exactBin .add 4 0 4))
              (.op (.const 5 (2 ^ w - 1))))))))
        (Tabulation.randFillLoop.rename DoubleTabulation.fillMap12))
    (m₂ := fun z => do
      let x1 := ((((((z.write base (z.regs 7)).set 6 1).set 3 (base + 1)).set 4
        (base + space w c_tab d b_char M_out)).set 5 (2 ^ w - 1)))
      let zf ← Tabulation.randFillComp w (base + 1)
        (topWords w c_tab d b_char + botWords w d b_char M_out)
        (x1.comap DoubleTabulation.fillMap12)
      pure (zf.1.extend DoubleTabulation.fillMap12 x1, 6 + zf.2))
    (by simpa only [bind_assoc, pure_bind] using s12)
    (fun z hz => by
      have hz' : z ∈ (do
          let k ← ProbComp.unifFin (2 ^ (w₀ - 1) - 1)
          pure (d0.set 7 k.val, 1 + 1) : ProbComp (Data 12 × ℕ)).support := by
        simpa only [bind_assoc, pure_bind] using hz
      exact s_rest z hz')
  simpa only [resampleCode, resampleComp, d0, Data.set_regs, Function.update_self,
    bind_assoc, pure_bind] using hall

theorem isQueryBounded_resampleComp (base w w₀ c_tab d b_char M_out : ℕ) (x : Data 12) :
    (resampleComp base w w₀ c_tab d b_char M_out x).IsQueryBounded
      (1 + (topWords w c_tab d b_char + botWords w d b_char M_out)) := by
  dsimp only [resampleComp]
  refine (ProbComp.isQueryBounded_unifFin _).bind fun kα => ?_
  simpa only [Nat.add_zero] using
    (Tabulation.isQueryBounded_randFillComp w (base + 1)
      (topWords w c_tab d b_char + botWords w d b_char M_out) _).bind fun _ => .pure _ 0

/-- Pathwise postcondition of `resampleComp`: executes in `resampleSteps` instructions, preserves
`reg 0 = base`, establishes `SeedRep`, preserves `Bounded w`, and modifies only
`[base, base + space)`. -/
theorem mem_support_resampleComp {base w w₀ c_tab d b_char M_out : ℕ} {x : Data 12}
    (hw : 0 < w) (hw₀_le : w₀ ≤ w) (hbase : x.regs 0 = base)
    (hfit_end : Fits w (base + space w c_tab d b_char M_out))
    (hx_bdd : x.Bounded w) {z : Data 12 × ℕ}
    (hz : z ∈ (resampleComp base w w₀ c_tab d b_char M_out x).support) :
    z.1.regs 0 = base ∧
    SeedRep base w w₀ c_tab d b_char M_out
      (extractSeed base w w₀ c_tab d b_char M_out z.1.mem) z.1.mem ∧
    (∀ q < topWords w c_tab d b_char + botWords w d b_char M_out, z.1.mem (base + 1 + q) < 2 ^ w) ∧
    (∀ a, (a < base ∨ base + space w c_tab d b_char M_out ≤ a) → z.1.mem a = x.mem a) ∧
    z.1.Bounded w ∧
    z.2 = resampleSteps w c_tab d b_char M_out := by
  have hex := resampleCode_execRand hw hw₀_le hbase hfit_end
  have hbdd := hex.bounded hx_bdd hz
  dsimp only [resampleComp] at hz
  obtain ⟨kα, -, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
  obtain ⟨zf, hzf, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
  cases OracleComp.eq_of_mem_supportWith_pure hpure
  obtain ⟨hsteps, _, _, _, _, hextra, hlt, hframe⟩ := Tabulation.mem_support_randFillComp hzf
  set x1 := (((((((x.set 5 (2 ^ (w₀ - 1) - 1)).set 7 kα.val).write base kα.val).set 6 1).set 3
    (base + 1)).set 4 (base + space w c_tab d b_char M_out)).set 5 (2 ^ w - 1))
  set y := zf.1.extend DoubleTabulation.fillMap12 x1
  have hy0 : y.regs 0 = base := by
    change (y.comap DoubleTabulation.fillMap12).regs Tabulation.regExtra = base
    rw [Data.comap_extend DoubleTabulation.injective_fillMap12, hextra]
    simp +decide [x1, Data.write, DoubleTabulation.fillMap12, Data.comap, hbase]
  have hkα_lt : kα.val < 2 ^ (w₀ - 1) := by
    have hpos : 1 ≤ 2 ^ (w₀ - 1) := Nat.one_le_two_pow
    have hk := kα.isLt
    omega
  have hmem_base : zf.1.mem base = kα.val := by
    rw [hframe base (Or.inl (by omega))]
    simp [x1, Data.write]
  have hsp_def : space w c_tab d b_char M_out =
      1 + topWords w c_tab d b_char + botWords w d b_char M_out := rfl
  refine ⟨hy0, seedRep_extractSeed
    (by change zf.1.mem base < 2 ^ (w₀ - 1); rw [hmem_base]; exact hkα_lt), hlt, ?_, hbdd, ?_⟩
  · intro a ha
    have ha_ne : a ≠ base := by omega
    have ha_out : a < base + 1 ∨
        base + 1 + (topWords w c_tab d b_char + botWords w d b_char M_out) ≤ a := by
      omega
    change zf.1.mem a = x.mem a
    rw [hframe a ha_out]
    simp [x1, Data.write, Function.update_of_ne ha_ne]
  · unfold resampleSteps
    rw [hsteps]
    omega

/-- **Exact product uniformity of `resampleComp`**: when `0 < w`, `b_char ≤ w`, and `M_out ≤ w`,
the extracted seed `extractSeed base w w₀ c_tab d b_char M_out z.1.mem` under `resampleComp` has
exact uniform distribution `PMF.uniformOfFintype (Seed w₀ c_tab d b_char M_out)`. -/
theorem map_extractSeed_eval_resampleComp {base w w₀ c_tab d b_char M_out : ℕ}
    (hw : 0 < w) (hb_le : b_char ≤ w) (hM_le : M_out ≤ w) (x : Data 12) :
    ((resampleComp base w w₀ c_tab d b_char M_out x).eval).map
      (fun z => extractSeed base w w₀ c_tab d b_char M_out z.1.mem) =
      PMF.uniformOfFintype (Seed w₀ c_tab d b_char M_out) := by
  let eα : Fin (2 ^ (w₀ - 1) - 1 + 1) ≃ Fin (2 ^ (w₀ - 1)) :=
    finCongr (Nat.sub_add_cancel Nat.one_le_two_pow)
  let W_tot := topWords w c_tab d b_char + botWords w d b_char M_out
  have hinner : ∀ kα : Fin (2 ^ (w₀ - 1) - 1 + 1),
      (let x1 := (((((((x.set 5 (2 ^ (w₀ - 1) - 1)).set 7 kα.val).write base kα.val).set 6 1).set 3
        (base + 1)).set 4 (base + space w c_tab d b_char M_out)).set 5 (2 ^ w - 1))
       (do
         let zf ← Tabulation.randFillComp w (base + 1) W_tot (x1.comap DoubleTabulation.fillMap12)
         pure (zf.1.extend DoubleTabulation.fillMap12 x1, 2 + (6 + zf.2))).eval).map
        (fun z : Data 12 × ℕ => extractSeed base w w₀ c_tab d b_char M_out z.1.mem) =
      (PMF.uniformOfFintype
        (DoubleTabTopSeed (c_tab + 1) d b_char × DoubleTabBotSeed d b_char M_out)).map
          (fun T => (eα kα, T)) := by
    intro kα
    dsimp only
    set x1 := (((((((x.set 5 (2 ^ (w₀ - 1) - 1)).set 7 kα.val).write base kα.val).set 6 1).set 3
      (base + 1)).set 4 (base + space w c_tab d b_char M_out)).set 5 (2 ^ w - 1))
    set mf := Tabulation.randFillComp w (base + 1) W_tot (x1.comap DoubleTabulation.fillMap12)
    have hd : (do
        let zf ← mf
        pure (zf.1.extend DoubleTabulation.fillMap12 x1, 2 + (6 + zf.2))) =
        (fun zf : Data 6 × ℕ => (zf.1.extend DoubleTabulation.fillMap12 x1, 2 + (6 + zf.2))) <$>
          mf := bind_pure_comp _ _
    rw [hd, ProbComp.eval_map, PMF.map_comp]
    have hcongr :
        mf.eval.map
          ((fun z : Data 12 × ℕ => extractSeed base w w₀ c_tab d b_char M_out z.1.mem) ∘
            fun zf : Data 6 × ℕ => (zf.1.extend DoubleTabulation.fillMap12 x1, 2 + (6 + zf.2))) =
        mf.eval.map
          ((fun T => (eα kα, T)) ∘
            tablesOfWords w c_tab d b_char M_out hw ∘
            fun zf : Data 6 × ℕ => Tabulation.extractSlice (base + 1) w W_tot zf.1.mem) := by
      refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun zf hzf => ?_
      rw [ProbComp.support_eval] at hzf
      obtain ⟨_, _, _, _, _, _, hlt, hframe⟩ := Tabulation.mem_support_randFillComp hzf
      have hmem_base : zf.1.mem base = kα.val := by
        rw [hframe base (Or.inl (by omega))]
        simp [x1, Data.write]
      have hα_eq : wordOfNat (w₀ - 1) (zf.1.mem base) = eα kα := by
        rw [hmem_base, wordOfNat_unifFin]
      have htop_eq : extractPackedSlice (base + 1) (topEntries c_tab d b_char) b_char w zf.1.mem =
          (Equiv.piCongrRight fun _ => BitString.equivFin b_char)
            (bitPackedProjHom (topEntries c_tab d b_char) b_char w hw
              (fun q => (BitString.equivFin w).symm
                (Tabulation.extractSlice (base + 1) w W_tot zf.1.mem
                  (Fin.castAdd (botWords w d b_char M_out) q)))) := by
        rw [extractPackedSlice_eq_packedSliceOfWords hw hb_le
          (fun q hq => hlt q (by dsimp only [W_tot, topWords]; omega))]
        rfl
      have hbot_eq : extractPackedSlice (base + offBot w c_tab d b_char) (botEntries d b_char)
          M_out w zf.1.mem =
          (Equiv.piCongrRight fun _ => BitString.equivFin M_out)
            (bitPackedProjHom (botEntries d b_char) M_out w hw
              (fun q => (BitString.equivFin w).symm
                (Tabulation.extractSlice (base + 1) w W_tot zf.1.mem
                  (Fin.natAdd (topWords w c_tab d b_char) q)))) := by
        rw [extractPackedSlice_eq_packedSliceOfWords hw hM_le (fun q hq => by
          have hq' : topWords w c_tab d b_char + q < W_tot := by
            dsimp only [W_tot, botWords]; omega
          simpa only [offBot, Nat.add_assoc] using hlt _ hq')]
        dsimp only [packedSliceOfWords]
        congr 2
        funext q
        change (BitString.equivFin w).symm
            (wordOfNat w (zf.1.mem ((base + offBot w c_tab d b_char) + q.val))) =
          (BitString.equivFin w).symm
            (wordOfNat w (zf.1.mem ((base + 1) + (topWords w c_tab d b_char + q.val))))
        rw [show (base + offBot w c_tab d b_char) + q.val =
          (base + 1) + (topWords w c_tab d b_char + q.val) by unfold offBot; omega]
      dsimp only [Function.comp_apply, extractSeed, tablesOfWords, Data.extend]
      rw [hα_eq, htop_eq, hbot_eq]
      rfl
    rw [hcongr, ← PMF.map_comp, ← PMF.map_comp, Tabulation.map_extractSlice_eval_randFillComp,
      uniformOfFintype_map_tablesOfWords]
  dsimp only [resampleComp]
  rw [ProbComp.eval_bind, ProbComp.eval_unifFin, PMF.map_bind]
  have hbind :
      (PMF.uniformOfFintype (Fin (2 ^ (w₀ - 1) - 1 + 1))).bind
        (fun kα =>
          (let x1 := (((((((x.set 5 (2 ^ (w₀ - 1) - 1)).set 7 kα.val).write base kα.val).set 6
            1).set 3 (base + 1)).set 4 (base + space w c_tab d b_char M_out)).set 5 (2 ^ w - 1))
           (do
             let zf ← Tabulation.randFillComp w (base + 1) W_tot
               (x1.comap DoubleTabulation.fillMap12)
             pure (zf.1.extend DoubleTabulation.fillMap12 x1, 2 + (6 + zf.2))).eval).map
            (fun z : Data 12 × ℕ => extractSeed base w w₀ c_tab d b_char M_out z.1.mem)) =
      (PMF.uniformOfFintype (Fin (2 ^ (w₀ - 1) - 1 + 1))).bind
        (fun kα =>
          (PMF.uniformOfFintype
            (DoubleTabTopSeed (c_tab + 1) d b_char × DoubleTabBotSeed d b_char M_out)).map
              (fun T => (eα kα, T))) := by
    congr 1
    funext kα
    exact hinner kα
  rw [hbind]
  have heq_α := PMF.uniformOfFintype_map_equiv eα
  have hprod :
      ((PMF.uniformOfFintype (Fin (2 ^ (w₀ - 1) - 1 + 1))).map eα).bind
        (fun α =>
          (PMF.uniformOfFintype
            (DoubleTabTopSeed (c_tab + 1) d b_char × DoubleTabBotSeed d b_char M_out)).map
              (fun T => (α, T))) =
      PMF.uniformOfFintype (Seed w₀ c_tab d b_char M_out) := by
    rw [heq_α]
    dsimp only [Seed]
    exact uniformOfFintype_prod _ _
  rwa [PMF.bind_map] at hprod


/-! ## Section 3: `Memory.Prog` + `realize` deterministic `O(c_tab * d)` evaluation -/

/-- `Memory.Prog` read of the `k`-bit entry at `idx` in a bit-packed array at `base + offset`. -/
@[expose] def readPackedProg (base offset k w idx : ℕ) : Memory.Prog ℕ := do
  let wOff := wordOffset k w idx
  let bOff := bitOffset k w idx
  let k₀ := lowWidth k w idx
  let k₁ := highWidth k w idx
  let word₀ ← Memory.read (base + offset + wOff)
  let word₁ ← Memory.read (base + offset + wOff + 1)
  let low := (word₀ >>> bOff) &&& (2 ^ k₀ - 1)
  let high := (word₁ >>> 0) &&& (2 ^ k₁ - 1)
  pure (low ^^^ (high <<< k₀))

/-- Parameter-free `Memory.Prog` wrapper for `readPackedProg`
(`d = (((base, offset), (k, w)), idx)`). -/
@[expose] def readPackedGenProg (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) : Memory.Prog ℕ :=
  readPackedProg d.1.1.1 d.1.1.2 d.1.2.1 d.1.2.2 d.2

theorem validHistory_readPackedProg {w base offset N k idx : ℕ} {s : Memory.State}
    (hw : 0 < w) (hidx : idx < N)
    (ha : base + offset + packedWords N k w ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (readPackedProg base offset k w idx)) := by
  have hlt := wordOffset_add_one_lt_packedWords (k := k) hw hidx
  change base + offset + wordOffset k w idx < s.frontier ∧
    base + offset + wordOffset k w idx + 1 < s.frontier ∧ True
  exact ⟨by omega, by omega, trivial⟩

@[simp]
theorem clientResult_readPackedProg (base offset k w idx : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (readPackedProg base offset k w idx) =
      readPacked (base + offset) k w s.mem idx := rfl

theorem clientState_readPackedProg (base offset k w idx : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readPackedProg base offset k w idx) = s := rfl

@[simp]
theorem memoryCost_readPackedProg (base offset k w idx : ℕ) (s : Memory.State) :
    memoryCost (readPackedProg base offset k w idx) s = 2 := rfl

@[simp]
private theorem clientResult_pure' {α : Type} (w : ℕ) (s : Memory.State) (a : α) :
    (Memory.spec w).clientResult s (pure a) = a := rfl

private theorem clientState_pure' {α : Type} (w : ℕ) (s : Memory.State) (a : α) :
    (Memory.spec w).clientState s (pure a) = s := rfl

private theorem readPackedCode_not_readsWidth : ¬readPackedCode.ReadsWidth := by
  simp [readPackedCode, addrSetupCode, offsetSetupCode, maskSetupCode, readPackedFinishCode,
    Code.ReadsWidth, Op.ReadsWidth, Op.exactBin]

/-- Uniform parameter-free `Realizes .exact` certificate for `readPackedGenProg`. -/
theorem realizes_readPackedGen :
    Realizes .exact readPackedGenProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w d _ => ∃ N, w = d.1.2.2 ∧ 0 < w ∧ d.1.2.1 ≤ w ∧ d.2 < N ∧
        Fits w (d.1.1.1 + d.1.1.2 + packedWords N d.1.2.1 w))
      (fun _ _ => 0) := by
  let perm : Fin 10 ≃ Fin 10 := Equiv.swap 0 2
  refine ⟨8, 38, fun _ src tmp =>
    .seq (.op (.exactBin .add (tmp 2) (src 0) (src 1)))
      (.seq (.op (.copy (tmp 1) (src 4)))
        (.seq (.op (.copy (tmp 8) (src 3)))
          (.seq (.op (.copy (tmp 9) (src 2)))
            (readPackedCode.rename (tmp ∘ perm))))), ?_⟩
  intro r frontier src tmp hi hd hf _
  have hperm_inj : Function.Injective (tmp ∘ perm) := hi.comp perm.injective
  refine ⟨?_, ?_⟩
  · simp [Code.ReadsWidth, Op.ReadsWidth, Op.exactBin, Code.readsWidth_rename,
      readPackedCode_not_readsWidth]
  · intro w d x hx hin ⟨N, heq, hw, hkw, hidx, hfit⟩ _
    have hsrc0 : x.regs (src 0) = d.1.1.1 := congrFun hin 0
    have hsrc1 : x.regs (src 1) = d.1.1.2 := congrFun hin 1
    have hsrc2 : x.regs (src 2) = d.1.2.1 := congrFun hin 2
    have hsrc3 : x.regs (src 3) = d.1.2.2 := congrFun hin 3
    have hsrc4 : x.regs (src 4) = d.2 := congrFun hin 4
    let x₁ := x.set (tmp 2) (d.1.1.1 + d.1.1.2)
    let x₂ := x₁.set (tmp 1) (x₁.regs (src 4))
    let x₃ := x₂.set (tmp 8) (x₂.regs (src 3))
    let x₄ := x₃.set (tmp 9) (x₃.regs (src 2))
    have hc1 :
        ExecWithin (B := .exact) w (.op (.exactBin .add (tmp 2) (src 0) (src 1))) x x₁ 1 := by
      apply ExecWithin.op
      rw [Op.eval_exactBin, hsrc0, hsrc1]
      exact Data.put_of_fits (hfit.of_le (by omega))
    have hc2 : ExecWithin (B := .exact) w (.op (.copy (tmp 1) (src 4))) x₁ x₂ 1 := ExecWithin.copy
    have hc3 : ExecWithin (B := .exact) w (.op (.copy (tmp 8) (src 3))) x₂ x₃ 1 := ExecWithin.copy
    have hc4 : ExecWithin (B := .exact) w (.op (.copy (tmp 9) (src 2))) x₃ x₄ 1 := ExecWithin.copy
    have hx₄_bdd : x₄.Bounded w := hc4.bounded (hc3.bounded (hc2.bounded (hc1.bounded hx)))
    have hne : ∀ (a b : Fin 10), a ≠ b → tmp a ≠ tmp b := fun a b hab h => hab (hi h)
    have hbase0 : (x₄.comap (tmp ∘ perm)).regs 0 = d.1.1.1 + d.1.1.2 := by
      change x₄.regs (tmp (perm 0)) = d.1.1.1 + d.1.1.2
      have hp0 : perm 0 = 2 := by decide
      rw [hp0]; dsimp only [x₄, x₃, x₂, x₁, Data.set]
      rw [Function.update_of_ne (hne 2 9 (by decide)),
        Function.update_of_ne (hne 2 8 (by decide)),
        Function.update_of_ne (hne 2 1 (by decide)), Function.update_self]
    have hidx1 : (x₄.comap (tmp ∘ perm)).regs 1 = d.2 := by
      change x₄.regs (tmp (perm 1)) = d.2
      have hp1 : perm 1 = 1 := by decide
      rw [hp1]; dsimp only [x₄, x₃, x₂, x₁, Data.set]
      rw [Function.update_of_ne (hne 1 9 (by decide)),
        Function.update_of_ne (hne 1 8 (by decide)),
        Function.update_self, Function.update_of_ne (hd 4 2), hsrc4]
    have hw8 : (x₄.comap (tmp ∘ perm)).regs 8 = w := by
      change x₄.regs (tmp (perm 8)) = w
      have hp8 : perm 8 = 8 := by decide
      rw [hp8]; dsimp only [x₄, x₃, x₂, x₁, Data.set]
      rw [Function.update_of_ne (hne 8 9 (by decide)), Function.update_self,
        Function.update_of_ne (hd 3 1), Function.update_of_ne (hd 3 2), hsrc3, heq]
    have hk9 : (x₄.comap (tmp ∘ perm)).regs 9 = d.1.2.1 := by
      change x₄.regs (tmp (perm 9)) = d.1.2.1
      have hp9 : perm 9 = 9 := by decide
      rw [hp9]; dsimp only [x₄, x₃, x₂, x₁, Data.set]
      rw [Function.update_self, Function.update_of_ne (hd 2 8),
        Function.update_of_ne (hd 2 1), Function.update_of_ne (hd 2 2), hsrc2]
    obtain ⟨y_core, hex_core, hymem, _, _, hy2⟩ :=
      readPackedCode_execWithin hw hkw hidx (hx₄_bdd.comap (tmp ∘ perm)) hbase0 hidx1 hw8 hk9 hfit
    have hex_ren := hex_core.rename hperm_inj
    let y := y_core.extend (tmp ∘ perm) x₄
    refine ⟨y, (hc1.seq (hc2.seq (hc3.seq (hc4.seq hex_ren)))).mono
      (by change 1 + (1 + (1 + (1 + 34))) ≤ 38 * (2 + 0 + 1); omega), ?_, ?_, ?_⟩
    · apply Memory.State.ext
      · exact hymem
      · change y.regs frontier = x.regs frontier
        have hnot : ¬∃ j : Fin 10, (tmp ∘ perm) j = frontier := by
          rintro ⟨j, hj⟩; exact hf (perm j) hj
        change Function.extend (tmp ∘ perm) y_core.regs x₄.regs frontier = x.regs frontier
        rw [Function.extend_apply' _ _ _ hnot]
        dsimp only [x₄, x₃, x₂, x₁, Data.set]
        rw [Function.update_of_ne (hf 9).symm, Function.update_of_ne (hf 8).symm,
          Function.update_of_ne (hf 1).symm, Function.update_of_ne (hf 2).symm]
    · intro i
      have hi0 : i = 0 := Fin.eq_zero i
      subst hi0
      rw [clientResult_width]
      change y.regs (tmp 0) = readPacked (d.1.1.1 + d.1.1.2) d.1.2.1 d.1.2.2 x.mem d.2
      have hp2 : tmp 0 = (tmp ∘ perm) 2 := by congr 1
      rw [hp2]
      change (y.comap (tmp ∘ perm)).regs 2 = _
      rw [Data.comap_extend hperm_inj, hy2, ← heq]
      rfl
    · intro i _ htmp
      have hnot : ¬∃ j : Fin 10, (tmp ∘ perm) j = i := by
        rintro ⟨j, hj⟩; exact htmp (perm j) hj
      change Function.extend (tmp ∘ perm) y_core.regs x₄.regs i = x.regs i
      rw [Function.extend_apply' _ _ _ hnot]
      dsimp only [x₄, x₃, x₂, x₁, Data.set]
      rw [Function.update_of_ne (htmp 9).symm, Function.update_of_ne (htmp 8).symm,
        Function.update_of_ne (htmp 1).symm, Function.update_of_ne (htmp 2).symm]

/-- Runtime register block of 16 precomputed hash parameters for parameter-free `Realizes`. -/
@[expose] def HashParams : Type := Fin 16 → ℕ

instance : WordEncoding HashParams := ⟨16, Function.Embedding.refl (Fin 16 → ℕ)⟩

/-- Construct the 16-word parameter vector for `(w, w₀, R, c_tab, d, b_char, M_out)`. -/
@[expose] def mkHashParams (w w₀ R c_tab d b_char M_out : ℕ) : HashParams := fun i =>
  match i.val with
  | 0 => w
  | 1 => w₀ - R
  | 2 => (w₀ - 1) / 2
  | 3 => 2 * ((w₀ - 1) / 2)
  | 4 => 2 ^ (w₀ - 1) - 1
  | 5 => 2 ^ ((w₀ - 1) / 2) - 1
  | 6 => 2 ^ ((w₀ - 1) - (w₀ - 1) / 2) - 1
  | 7 => 2 ^ ((w₀ - 1) - 2 * ((w₀ - 1) / 2)) - 1
  | 8 => b_char
  | 9 => 2 ^ b_char - 1
  | 10 => 2 ^ b_char
  | 11 => M_out
  | 12 => offBot w c_tab d b_char
  | 13 => c_tab + 1
  | 14 => c_tab
  | _ => d

/-- Word width $w$ in the hash parameter vector. -/
@[expose] def hpW (hp : HashParams) : ℕ := hp 0
/-- Shift count $w₀ - R$ in the hash parameter vector. -/
@[expose] def hpShiftR (hp : HashParams) : ℕ := hp 1
/-- Half-chunk bitwidth $\lfloor(w₀ - 1) / 2\rfloor$ in the hash parameter vector. -/
@[expose] def hpHalfM (hp : HashParams) : ℕ := hp 2
/-- Double half-chunk bitwidth $2 \lfloor(w₀ - 1) / 2\rfloor$ in the hash parameter vector. -/
@[expose] def hpTwoHalfM (hp : HashParams) : ℕ := hp 3
/-- Low chunk mask $2^{w₀ - 1} - 1$ in the hash parameter vector. -/
@[expose] def hpMaskM (hp : HashParams) : ℕ := hp 4
/-- First half-chunk mask in the hash parameter vector. -/
@[expose] def hpMaskHalf (hp : HashParams) : ℕ := hp 5
/-- Second half-chunk mask in the hash parameter vector. -/
@[expose] def hpMaskRem (hp : HashParams) : ℕ := hp 6
/-- Top remainder bit mask in the hash parameter vector. -/
@[expose] def hpMaskTop (hp : HashParams) : ℕ := hp 7
/-- Character bitwidth $b$ in the hash parameter vector. -/
@[expose] def hpBChar (hp : HashParams) : ℕ := hp 8
/-- Character mask $2^b - 1$ in the hash parameter vector. -/
@[expose] def hpMaskB (hp : HashParams) : ℕ := hp 9
/-- Character radix $2^b$ in the hash parameter vector. -/
@[expose] def hpPowB (hp : HashParams) : ℕ := hp 10
/-- Output word count $M_{\mathrm{out}}$ in the hash parameter vector. -/
@[expose] def hpMOut (hp : HashParams) : ℕ := hp 11
/-- Memory word offset of bottom table in the hash parameter vector. -/
@[expose] def hpOffBot (hp : HashParams) : ℕ := hp 12
/-- Chunk count plus one ($c_{\mathrm{tab}} + 1$) in the hash parameter vector. -/
@[expose] def hpCPlusOne (hp : HashParams) : ℕ := hp 13
/-- Chunk count $c_{\mathrm{tab}}$ in the hash parameter vector. -/
@[expose] def hpCTab (hp : HashParams) : ℕ := hp 14
/-- Dimension $d$ in the hash parameter vector. -/
@[expose] def hpD (hp : HashParams) : ℕ := hp 15

theorem mkHashParams_0 (w w₀ R c_tab d b_char M_out : ℕ) :
    mkHashParams w w₀ R c_tab d b_char M_out 0 = w := rfl
theorem mkHashParams_1 (w w₀ R c_tab d b_char M_out : ℕ) :
    mkHashParams w w₀ R c_tab d b_char M_out 1 = w₀ - R := rfl
theorem mkHashParams_2 (w w₀ R c_tab d b_char M_out : ℕ) :
    mkHashParams w w₀ R c_tab d b_char M_out 2 = (w₀ - 1) / 2 := rfl
theorem mkHashParams_3 (w w₀ R c_tab d b_char M_out : ℕ) :
    mkHashParams w w₀ R c_tab d b_char M_out 3 = 2 * ((w₀ - 1) / 2) := rfl
theorem mkHashParams_4 (w w₀ R c_tab d b_char M_out : ℕ) :
    mkHashParams w w₀ R c_tab d b_char M_out 4 = 2 ^ (w₀ - 1) - 1 := rfl
theorem mkHashParams_5 (w w₀ R c_tab d b_char M_out : ℕ) :
    mkHashParams w w₀ R c_tab d b_char M_out 5 = 2 ^ ((w₀ - 1) / 2) - 1 := rfl
theorem mkHashParams_6 (w w₀ R c_tab d b_char M_out : ℕ) :
    mkHashParams w w₀ R c_tab d b_char M_out 6 = 2 ^ ((w₀ - 1) - (w₀ - 1) / 2) - 1 := rfl
theorem mkHashParams_7 (w w₀ R c_tab d b_char M_out : ℕ) :
    mkHashParams w w₀ R c_tab d b_char M_out 7 = 2 ^ ((w₀ - 1) - 2 * ((w₀ - 1) / 2)) - 1 := rfl
theorem mkHashParams_8 (w w₀ R c_tab d b_char M_out : ℕ) :
    mkHashParams w w₀ R c_tab d b_char M_out 8 = b_char := rfl
theorem mkHashParams_9 (w w₀ R c_tab d b_char M_out : ℕ) :
    mkHashParams w w₀ R c_tab d b_char M_out 9 = 2 ^ b_char - 1 := rfl
theorem mkHashParams_10 (w w₀ R c_tab d b_char M_out : ℕ) :
    mkHashParams w w₀ R c_tab d b_char M_out 10 = 2 ^ b_char := rfl
theorem mkHashParams_11 (w w₀ R c_tab d b_char M_out : ℕ) :
    mkHashParams w w₀ R c_tab d b_char M_out 11 = M_out := rfl
theorem mkHashParams_12 (w w₀ R c_tab d b_char M_out : ℕ) :
    mkHashParams w w₀ R c_tab d b_char M_out 12 = offBot w c_tab d b_char := rfl
theorem mkHashParams_13 (w w₀ R c_tab d b_char M_out : ℕ) :
    mkHashParams w w₀ R c_tab d b_char M_out 13 = c_tab + 1 := rfl
theorem mkHashParams_14 (w w₀ R c_tab d b_char M_out : ℕ) :
    mkHashParams w w₀ R c_tab d b_char M_out 14 = c_tab := rfl
theorem mkHashParams_15 (w w₀ R c_tab d b_char M_out : ℕ) :
    mkHashParams w w₀ R c_tab d b_char M_out 15 = d := rfl

@[simp] theorem hpW_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpW (mkHashParams w w₀ R c_tab d b_char M_out) = w := rfl
@[simp] theorem hpShiftR_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpShiftR (mkHashParams w w₀ R c_tab d b_char M_out) = w₀ - R := rfl
@[simp] theorem hpHalfM_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpHalfM (mkHashParams w w₀ R c_tab d b_char M_out) = (w₀ - 1) / 2 := rfl
@[simp] theorem hpTwoHalfM_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpTwoHalfM (mkHashParams w w₀ R c_tab d b_char M_out) = 2 * ((w₀ - 1) / 2) := rfl
@[simp] theorem hpMaskM_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpMaskM (mkHashParams w w₀ R c_tab d b_char M_out) = 2 ^ (w₀ - 1) - 1 := rfl
@[simp] theorem hpMaskHalf_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpMaskHalf (mkHashParams w w₀ R c_tab d b_char M_out) = 2 ^ ((w₀ - 1) / 2) - 1 := rfl
@[simp] theorem hpMaskRem_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpMaskRem (mkHashParams w w₀ R c_tab d b_char M_out) = 2 ^ ((w₀ - 1) - (w₀ - 1) / 2) - 1 := rfl
@[simp] theorem hpMaskTop_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpMaskTop (mkHashParams w w₀ R c_tab d b_char M_out) =
      2 ^ ((w₀ - 1) - 2 * ((w₀ - 1) / 2)) - 1 := rfl
@[simp] theorem hpBChar_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpBChar (mkHashParams w w₀ R c_tab d b_char M_out) = b_char := rfl
@[simp] theorem hpMaskB_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpMaskB (mkHashParams w w₀ R c_tab d b_char M_out) = 2 ^ b_char - 1 := rfl
@[simp] theorem hpPowB_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpPowB (mkHashParams w w₀ R c_tab d b_char M_out) = 2 ^ b_char := rfl
@[simp] theorem hpMOut_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpMOut (mkHashParams w w₀ R c_tab d b_char M_out) = M_out := rfl
@[simp] theorem hpOffBot_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpOffBot (mkHashParams w w₀ R c_tab d b_char M_out) = offBot w c_tab d b_char := rfl
@[simp] theorem hpCPlusOne_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpCPlusOne (mkHashParams w w₀ R c_tab d b_char M_out) = c_tab + 1 := rfl
@[simp] theorem hpCTab_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpCTab (mkHashParams w w₀ R c_tab d b_char M_out) = c_tab := rfl
@[simp] theorem hpD_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpD (mkHashParams w w₀ R c_tab d b_char M_out) = d := rfl

/-- Well-formedness envelope for `HashParams` at `base` on a `w`-bit machine. -/
@[expose] def HashEnv (w : ℕ) (hp : HashParams) (base : ℕ) : Prop :=
  ∃ w₀ R c_tab d b_char M_out,
    0 < w ∧ 0 < w₀ ∧ w₀ ≤ w ∧ b_char < w ∧ M_out ≤ w ∧
    topEntries c_tab d b_char < 2 ^ w ∧
    botEntries d b_char < 2 ^ w ∧
    c_tab + 1 < 2 ^ w ∧ d < 2 ^ w ∧
    Fits w (base + space w c_tab d b_char M_out) ∧
    hp = mkHashParams w w₀ R c_tab d b_char M_out

/-- Fit of all 16 words in `mkHashParams` under `HashEnv`. -/
theorem fits_mkHashParams {w base : ℕ} {hp : HashParams} (henv : HashEnv w hp base) (i : Fin 16) :
    Fits w (hp i) := by
  obtain ⟨w₀, R, c_tab, d, b_char, M_out, hw, hw₀, hw₀_le, hb, hM, _, _, hc1, hd_lt, hfit_sp,
    rfl⟩ := henv
  have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
  fin_cases i <;> dsimp only [mkHashParams, Fits]
  · exact hw_lt
  · exact (Nat.sub_le w₀ R).trans_lt (hw₀_le.trans_lt hw_lt)
  · exact (Nat.div_le_self _ 2).trans_lt ((Nat.sub_le w₀ 1).trans_lt (hw₀_le.trans_lt hw_lt))
  · exact (Nat.mul_div_le (w₀ - 1) 2).trans_lt ((Nat.sub_le w₀ 1).trans_lt (hw₀_le.trans_lt hw_lt))
  · exact (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans_le
      (Nat.pow_le_pow_right two_pos (by omega))
  · exact (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans_le
      (Nat.pow_le_pow_right two_pos (by omega))
  · exact (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans_le
      (Nat.pow_le_pow_right two_pos (by omega))
  · exact (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans_le
      (Nat.pow_le_pow_right two_pos (by omega))
  · exact hb.trans hw_lt
  · exact (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans (Nat.pow_lt_pow_right (by decide) hb)
  · exact Nat.pow_lt_pow_right (by decide) hb
  · exact hM.trans_lt hw_lt
  · change offBot w c_tab d b_char < 2 ^ w
    have hsp_eq : space w c_tab d b_char M_out =
        offBot w c_tab d b_char + botWords w d b_char M_out := rfl
    exact hfit_sp.of_le (by omega)
  · exact hc1
  · exact (Nat.lt_succ_self c_tab).trans hc1
  · exact hd_lt

/-- Inner-loop body (`p = ((hp, (base, j)), ((i, y_acc), r_cur))`): extracts character `i` from
`r_cur`, reads `T₁[i, j, ch]`, XORs into `y_acc`, and shifts `r_cur` right by `b_char`. -/
@[expose] def innerStepGenProg
    (p : (HashParams × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)) : Memory.Prog ((ℕ × ℕ) × ℕ) := do
  let ch ← pure (p.2.2 &&& hpMaskB p.1.1)
  let row ← pure (p.1.2.2 * hpCPlusOne p.1.1 + p.2.1.1)
  let idx₁ ← pure (row * hpPowB p.1.1 + ch)
  let one_off ← pure 1
  let t_val ← readPackedGenProg (((p.1.2.1, one_off), (hpBChar p.1.1, hpW p.1.1)), idx₁)
  let i_next ← pure (p.2.1.1 + 1)
  let y_next ← pure (p.2.1.2 ^^^ t_val)
  let r_next ← pure (p.2.2 >>> hpBChar p.1.1)
  pure ((i_next, y_next), r_next)

@[simp]
theorem memoryCost_innerStepGenProg (p : (HashParams × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ))
    (s : Memory.State) :
    memoryCost (innerStepGenProg p) s = 2 := rfl

theorem memoryCost_innerStepGenProg_pos (p : (HashParams × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ))
    (s : Memory.State) :
    1 ≤ memoryCost (innerStepGenProg p) s := by simp

/-- Precondition for `innerStepGenProg`. -/
@[expose] def InnerStepGenPre (w : ℕ) (p : (HashParams × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ))
    (_s : Memory.State) : Prop :=
  HashEnv w p.1.1 p.1.2.1 ∧
  p.1.2.2 < hpD p.1.1 ∧
  p.2.1.1 < hpCTab p.1.1 ∧
  p.2.1.2 < hpPowB p.1.1

theorem realizes_innerStepGen :
    Realizes .exact innerStepGenProg
      (WordEncoding.encode (α := (HashParams × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      InnerStepGenPre
      (fun _ _ => 0) := by
  have hrp := realizes_readPackedGen
  realize
  all_goals (
    rcases d with ⟨⟨hp, base, j⟩, ⟨i, y⟩, r⟩
    obtain ⟨⟨w₀, R, c_tab, d_par, b_char, M_out, hw, hw₀, hw₀_le, hb, hM, htop_lt, hbot_lt,
      hc1, hd_lt, hfit_sp, heq_hp⟩, hj_lt, hi_lt, hy_lt⟩ := h
    subst heq_hp
    dsimp only [hpW, hpBChar, hpMaskB, hpPowB, hpCPlusOne, hpCTab, hpD,
      mkHashParams_0, mkHashParams_8, mkHashParams_9, mkHashParams_10, mkHashParams_13,
      mkHashParams_14, mkHashParams_15] at *
  )
  · have hrow_lt : j * (c_tab + 1) + i < d_par * (c_tab + 1) := by
      calc j * (c_tab + 1) + i
          < j * (c_tab + 1) + (c_tab + 1) := Nat.add_lt_add_left (by omega) _
        _ = (j + 1) * (c_tab + 1) := by ring
        _ ≤ d_par * (c_tab + 1) := Nat.mul_le_mul_right _ hj_lt
    have hle_top : d_par * (c_tab + 1) ≤ topEntries c_tab d_par b_char := by
      dsimp only [topEntries]
      calc d_par * (c_tab + 1) = (c_tab + 1) * d_par * 1 := by ring
        _ ≤ (c_tab + 1) * d_par * 2 ^ b_char :=
            Nat.mul_le_mul_left _ (Nat.one_le_two_pow)
    exact (hrow_lt.trans_le hle_top).trans htop_lt
  · have hch_lt : r &&& (2 ^ b_char - 1) < 2 ^ b_char := by
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hidx_lt :
        (j * (c_tab + 1) + i) * 2 ^ b_char + (r &&& (2 ^ b_char - 1)) <
          topEntries c_tab d_par b_char := by
      have h := DoubleTabulation.topAddr_lt_base_add_topWords 0 (c_tab + 1) d_par b_char
        ⟨i, by omega⟩ ⟨j, hj_lt⟩ ⟨_, hch_lt⟩
      dsimp only [DoubleTabulation.topAddr, DoubleTabulation.topWords, topEntries] at h ⊢
      omega
    exact hidx_lt.trans htop_lt
  · exact Nat.one_lt_two_pow hw.ne'
  · have hch_lt : r &&& (2 ^ b_char - 1) < 2 ^ b_char := by
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hidx_lt :
        (j * (c_tab + 1) + i) * 2 ^ b_char + (r &&& (2 ^ b_char - 1)) <
          topEntries c_tab d_par b_char := by
      have h := DoubleTabulation.topAddr_lt_base_add_topWords 0 (c_tab + 1) d_par b_char
        ⟨i, by omega⟩ ⟨j, hj_lt⟩ ⟨_, hch_lt⟩
      dsimp only [DoubleTabulation.topAddr, DoubleTabulation.topWords, topEntries] at h ⊢
      omega
    refine ⟨topEntries c_tab d_par b_char, rfl, hw, hb.le, hidx_lt, ?_⟩
    exact hfit_sp.of_le (by unfold space topWords; omega)
  · exact (by omega : i + 1 < c_tab + 1).trans hc1
  · have ht_lt : readPacked (base + 1) b_char w s.mem
        ((j * (c_tab + 1) + i) * 2 ^ b_char + (r &&& (2 ^ b_char - 1))) <
        2 ^ b_char :=
      readPacked_lt _ _ _ _ _
    exact (Nat.xor_lt_two_pow hy_lt ht_lt).trans (Nat.pow_lt_pow_right (by decide) hb)

/-- Parameter-free wrapper for `iterate innerStepGenProg`. -/
@[expose] def innerLoopGenProg
    (p : ((HashParams × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)) × ℕ) : Memory.Prog ((ℕ × ℕ) × ℕ) :=
  iterate innerStepGenProg p.1.1 p.2 p.1.2

theorem realizes_innerLoopGen :
    Realizes .exact innerLoopGenProg
      (WordEncoding.encode (α := ((HashParams × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (fun w p s => iterationSafe innerStepGenProg InnerStepGenPre w p.1.1 p.2 p.1.2 s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := HashParams × (ℕ × ℕ)))
    (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
    realizes_innerStepGen
    memoryCost_innerStepGenProg_pos

/-- Outer-loop body (`p = ((hp, (base, (s_val, rKey))), (j, out_acc))`): computes `y_j` across all
`c_tab + 1` characters, reads `T₂[j, y_j]`, and XORs into `out_acc`. -/
@[expose] def outerStepGenProg
    (p : (HashParams × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let zero_v ← pure 0
  let inner_res ← innerLoopGenProg
    (((p.1.1, (p.1.2.1, p.2.1)), ((zero_v, zero_v), p.1.2.2.2)), hpCTab p.1.1)
  let row_s ← pure (p.2.1 * hpCPlusOne p.1.1 + hpCTab p.1.1)
  let idx_s ← pure (row_s * hpPowB p.1.1 + p.1.2.2.1)
  let one_off ← pure 1
  let t_salt ← readPackedGenProg
    (((p.1.2.1, one_off), (hpBChar p.1.1, hpW p.1.1)), idx_s)
  let y_j ← pure (inner_res.1.2 ^^^ t_salt)
  let idx₂ ← pure (p.2.1 * hpPowB p.1.1 + y_j)
  let z_j ← readPackedGenProg
    (((p.1.2.1, hpOffBot p.1.1), (hpMOut p.1.1, hpW p.1.1)), idx₂)
  let j_next ← pure (p.2.1 + 1)
  let out_next ← pure (p.2.2 ^^^ z_j)
  pure (j_next, out_next)

theorem memoryCost_outerStepGenProg_pos
    (p : (HashParams × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (outerStepGenProg p) s := by
  unfold outerStepGenProg readPackedGenProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  rw [memoryCost_bind, memoryCost_bind, memoryCost_readPackedProg]
  omega

theorem innerLoop_invariant {w : ℕ} {hp : HashParams} {base j : ℕ} {s : Memory.State}
    (henv : HashEnv w hp base) (hj : j < hpD hp) :
    ∀ m i y r, i + m ≤ hpCTab hp → y < hpPowB hp →
      iterationSafe innerStepGenProg InnerStepGenPre w (hp, (base, j)) m ((i, y), r) s ∧
      (Memory.spec 0).clientState s
        (iterate innerStepGenProg (hp, (base, j)) m ((i, y), r)) = s ∧
      ((Memory.spec 0).clientResult s
        (iterate innerStepGenProg (hp, (base, j)) m ((i, y), r))).1.2 < hpPowB hp := by
  obtain ⟨w₀, R, c_tab, d_par, b_char, M_out, hw, hw₀, hw₀_le, hb, hM, htop_lt, hbot_lt,
    hc1, hd_lt, hfit_sp, rfl⟩ := henv
  intro m
  induction m with
  | zero =>
    intro i y r _ hy
    exact ⟨trivial, rfl, hy⟩
  | succ m ih =>
    intro i y r him hy
    dsimp only [hpCTab_mk, hpPowB_mk] at him hy ⊢
    have hpre : InnerStepGenPre w ((mkHashParams w w₀ R c_tab d_par b_char M_out, (base, j)),
        ((i, y), r)) s :=
      ⟨⟨w₀, R, c_tab, d_par, b_char, M_out, hw, hw₀, hw₀_le, hb, hM, htop_lt, hbot_lt, hc1,
        hd_lt, hfit_sp, rfl⟩, hj, by dsimp only [hpCTab_mk]; omega, hy⟩
    have ht_lt : readPacked (base + 1) b_char w s.mem
        ((j * (c_tab + 1) + i) * 2 ^ b_char + (r &&& (2 ^ b_char - 1))) < 2 ^ b_char :=
      readPacked_lt _ _ _ _ _
    have hy' : y ^^^ readPacked (base + 1) b_char w s.mem
        ((j * (c_tab + 1) + i) * 2 ^ b_char + (r &&& (2 ^ b_char - 1))) < 2 ^ b_char :=
      Nat.xor_lt_two_pow hy ht_lt
    have hstep_st : (Memory.spec 0).clientState s
        (innerStepGenProg ((mkHashParams w w₀ R c_tab d_par b_char M_out, (base, j)),
          ((i, y), r))) = s := rfl
    obtain ⟨hsafe_m, hst_m, hy_m⟩ := ih (i + 1)
      (y ^^^ readPacked (base + 1) b_char w s.mem
        ((j * (c_tab + 1) + i) * 2 ^ b_char + (r &&& (2 ^ b_char - 1))))
      (r >>> b_char) (by dsimp only [hpCTab_mk]; omega) hy'
    refine ⟨⟨hpre, ?_⟩, ?_, ?_⟩
    · rw [hstep_st]; exact hsafe_m
    · unfold iterate
      rw [StateTransitionSpec.clientState_bind, clientState_width, hstep_st]
      exact hst_m
    · unfold iterate
      rw [StateTransitionSpec.clientResult_bind, clientState_width, hstep_st]
      exact hy_m

/-- Precondition for `outerStepGenProg`. -/
@[expose] def OuterStepGenPre (w : ℕ) (p : (HashParams × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ))
    (_s : Memory.State) : Prop :=
  HashEnv w p.1.1 p.1.2.1 ∧
  p.1.2.2.1 < hpPowB p.1.1 ∧
  p.2.1 < hpD p.1.1 ∧
  p.2.2 < 2 ^ hpMOut p.1.1

private theorem mul_add_xor_lt_botEntries {j d_par y t b_char : ℕ}
    (hj : j < d_par) (hy : y < 2 ^ b_char) (ht : t < 2 ^ b_char) :
    j * 2 ^ b_char + (y ^^^ t) < botEntries d_par b_char := by
  calc j * 2 ^ b_char + (y ^^^ t)
      < j * 2 ^ b_char + 2 ^ b_char := Nat.add_lt_add_left (Nat.xor_lt_two_pow hy ht) _
    _ = (j + 1) * 2 ^ b_char := by ring
    _ ≤ d_par * 2 ^ b_char := Nat.mul_le_mul_right _ hj

theorem realizes_outerStepGen :
    Realizes .exact outerStepGenProg
      (WordEncoding.encode (α := (HashParams × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      OuterStepGenPre
      (fun _ _ => 0) := by
  have hil := realizes_innerLoopGen
  have hrp := realizes_readPackedGen
  realize
  all_goals (
    rcases d with ⟨⟨hp, base, s_val, rKey⟩, j, out⟩
    obtain ⟨henv, hs_lt, hj_lt, hout_lt⟩ := h
    obtain ⟨w₀, R, c_tab, d_par, b_char, M_out, hw, hw₀, hw₀_le, hb, hM, htop_lt, hbot_lt,
      hc1, hd_lt, hfit_sp, heq_hp⟩ := henv
    subst heq_hp
    dsimp only [hpW, hpBChar, hpMaskB, hpPowB, hpMOut, hpOffBot, hpCPlusOne, hpCTab, hpD,
      mkHashParams_0, mkHashParams_8, mkHashParams_9, mkHashParams_10, mkHashParams_11,
      mkHashParams_12, mkHashParams_13, mkHashParams_14, mkHashParams_15] at *
    have henv' : HashEnv w (mkHashParams w w₀ R c_tab d_par b_char M_out) base :=
      ⟨w₀, R, c_tab, d_par, b_char, M_out, hw, hw₀, hw₀_le, hb, hM, htop_lt, hbot_lt, hc1,
        hd_lt, hfit_sp, rfl⟩
    have hinv := innerLoop_invariant (s := s) henv' (by dsimp only [hpD_mk]; exact hj_lt)
      c_tab 0 0 rKey (by dsimp only [hpCTab_mk]; omega)
      (by dsimp only [hpPowB_mk]; exact Nat.two_pow_pos b_char)
    dsimp only [hpPowB_mk] at hinv
  )
  · exact hinv.1
  · have hrow_s : j * (c_tab + 1) + c_tab < d_par * (c_tab + 1) := by
      calc j * (c_tab + 1) + c_tab
          < j * (c_tab + 1) + (c_tab + 1) := Nat.add_lt_add_left (by omega) _
        _ = (j + 1) * (c_tab + 1) := by ring
        _ ≤ d_par * (c_tab + 1) := Nat.mul_le_mul_right _ hj_lt
    have hle_top : d_par * (c_tab + 1) ≤ topEntries c_tab d_par b_char := by
      dsimp only [topEntries]
      calc d_par * (c_tab + 1) = (c_tab + 1) * d_par * 1 := by ring
        _ ≤ (c_tab + 1) * d_par * 2 ^ b_char := Nat.mul_le_mul_left _ Nat.one_le_two_pow
    exact (hrow_s.trans_le hle_top).trans htop_lt
  · have hidx_s : (j * (c_tab + 1) + c_tab) * 2 ^ b_char + s_val <
        topEntries c_tab d_par b_char := by
      have h := DoubleTabulation.topAddr_lt_base_add_topWords 0 (c_tab + 1) d_par b_char
        ⟨c_tab, by omega⟩ ⟨j, hj_lt⟩ ⟨s_val, hs_lt⟩
      dsimp only [DoubleTabulation.topAddr, DoubleTabulation.topWords, topEntries] at h ⊢
      omega
    exact hidx_s.trans htop_lt
  · exact Nat.one_lt_two_pow hw.ne'
  · have hidx_s : (j * (c_tab + 1) + c_tab) * 2 ^ b_char + s_val <
        topEntries c_tab d_par b_char := by
      have h := DoubleTabulation.topAddr_lt_base_add_topWords 0 (c_tab + 1) d_par b_char
        ⟨c_tab, by omega⟩ ⟨j, hj_lt⟩ ⟨s_val, hs_lt⟩
      dsimp only [DoubleTabulation.topAddr, DoubleTabulation.topWords, topEntries] at h ⊢
      omega
    refine ⟨topEntries c_tab d_par b_char, rfl, hw, hb.le, hidx_s, ?_⟩
    exact hfit_sp.of_le (by unfold space topWords; omega)
  · dsimp only [innerLoopGenProg, readPackedGenProg, clientResult_readPackedProg]
    exact (Nat.xor_lt_two_pow hinv.2.2 (readPacked_lt _ _ _ _ _)).trans
      (Nat.pow_lt_pow_right (by decide) hb)
  · dsimp only [innerLoopGenProg, readPackedGenProg, clientResult_readPackedProg]
    exact (mul_add_xor_lt_botEntries hj_lt hinv.2.2 (readPacked_lt _ _ _ _ _)).trans hbot_lt
  · dsimp only [innerLoopGenProg, readPackedGenProg, clientResult_readPackedProg]
    refine ⟨botEntries d_par b_char, rfl, hw, hM,
      mul_add_xor_lt_botEntries hj_lt hinv.2.2 (readPacked_lt _ _ _ _ _), ?_⟩
    exact hfit_sp.of_le (by unfold space offBot botWords; omega)
  · exact (by omega : j + 1 ≤ d_par).trans_lt hd_lt
  · dsimp only [readPackedGenProg, clientResult_readPackedProg]
    exact (Nat.xor_lt_two_pow hout_lt (readPacked_lt _ _ _ _ _)).trans_le
      (Nat.pow_le_pow_right two_pos hM)

/-- Parameter-free wrapper for `iterate outerStepGenProg`. -/
@[expose] def outerLoopGenProg
    (p : ((HashParams × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ)) × ℕ) : Memory.Prog (ℕ × ℕ) :=
  iterate outerStepGenProg p.1.1 p.2 p.1.2

theorem realizes_outerLoopGen :
    Realizes .exact outerLoopGenProg
      (WordEncoding.encode (α := ((HashParams × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w p s => iterationSafe outerStepGenProg OuterStepGenPre w p.1.1 p.2 p.1.2 s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := HashParams × (ℕ × (ℕ × ℕ))))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizes_outerStepGen
    memoryCost_outerStepGenProg_pos

theorem outerLoop_invariant {w : ℕ} {hp : HashParams} {base s_val rKey : ℕ} {s : Memory.State}
    (henv : HashEnv w hp base) (hs_lt : s_val < hpPowB hp) :
    ∀ m j out, j + m ≤ hpD hp → out < 2 ^ hpMOut hp →
      iterationSafe outerStepGenProg OuterStepGenPre w (hp, (base, (s_val, rKey))) m (j, out) s ∧
      (Memory.spec 0).clientState s
        (iterate outerStepGenProg (hp, (base, (s_val, rKey))) m (j, out)) = s := by
  obtain ⟨w₀, R, c_tab, d_par, b_char, M_out, hw, hw₀, hw₀_le, hb, hM, htop_lt, hbot_lt,
    hc1, hd_lt, hfit_sp, rfl⟩ := henv
  intro m
  induction m with
  | zero =>
    intro j out _ _
    exact ⟨trivial, rfl⟩
  | succ m ih =>
    intro j out hjm hout
    dsimp only [hpD_mk, hpMOut_mk] at hjm hout ⊢
    have henv' : HashEnv w (mkHashParams w w₀ R c_tab d_par b_char M_out) base :=
      ⟨w₀, R, c_tab, d_par, b_char, M_out, hw, hw₀, hw₀_le, hb, hM, htop_lt, hbot_lt, hc1,
        hd_lt, hfit_sp, rfl⟩
    have hj_lt : j < hpD (mkHashParams w w₀ R c_tab d_par b_char M_out) := by
      dsimp only [hpD_mk]; omega
    have hpre : OuterStepGenPre w
        ((mkHashParams w w₀ R c_tab d_par b_char M_out, (base, (s_val, rKey))), (j, out)) s :=
      ⟨henv', hs_lt, hj_lt, hout⟩
    have hinv_in := innerLoop_invariant (s := s) henv' hj_lt c_tab 0 0 rKey
      (by dsimp only [hpCTab_mk]; omega) (Nat.two_pow_pos b_char)
    have hstep_st : (Memory.spec 0).clientState s
        (outerStepGenProg
          ((mkHashParams w w₀ R c_tab d_par b_char M_out, (base, (s_val, rKey))), (j, out))) =
          s := by
      unfold outerStepGenProg innerLoopGenProg readPackedGenProg
      simp only [pure_bind, hpCTab_mk]
      rw [StateTransitionSpec.clientState_bind, clientState_width, hinv_in.2.1,
        StateTransitionSpec.clientState_bind, clientState_width, clientState_readPackedProg,
        StateTransitionSpec.clientState_bind, clientState_width, clientState_readPackedProg]
      rfl
    have hstep_fst : ((Memory.spec 0).clientResult s
        (outerStepGenProg
          ((mkHashParams w w₀ R c_tab d_par b_char M_out, (base, (s_val, rKey))), (j, out)))).1 =
          j + 1 := by
      unfold outerStepGenProg innerLoopGenProg readPackedGenProg
      simp only [pure_bind, hpCTab_mk]
      rw [StateTransitionSpec.clientResult_bind, clientState_width, hinv_in.2.1,
        StateTransitionSpec.clientResult_bind, clientState_width, clientState_readPackedProg,
        StateTransitionSpec.clientResult_bind, clientState_width, clientState_readPackedProg]
      rfl
    have hout' : ((Memory.spec 0).clientResult s
        (outerStepGenProg
          ((mkHashParams w w₀ R c_tab d_par b_char M_out, (base, (s_val, rKey))), (j, out)))).2 <
          2 ^ M_out := by
      unfold outerStepGenProg innerLoopGenProg readPackedGenProg
      simp only [pure_bind, hpCTab_mk, hpMOut_mk, hpOffBot_mk, hpW_mk]
      rw [StateTransitionSpec.clientResult_bind, clientState_width, hinv_in.2.1,
        StateTransitionSpec.clientResult_bind, clientState_width, clientState_readPackedProg,
        StateTransitionSpec.clientResult_bind, clientState_width, clientResult_width,
        clientState_readPackedProg, clientResult_readPackedProg]
      exact Nat.xor_lt_two_pow hout (readPacked_lt _ _ _ _ _)
    obtain ⟨hsafe_m, hst_m⟩ := ih (j + 1) _ (by dsimp only [hpD_mk]; omega) hout'
    have hpair_eq : (j + 1, ((Memory.spec 0).clientResult s
        (outerStepGenProg
          ((mkHashParams w w₀ R c_tab d_par b_char M_out, (base, (s_val, rKey))), (j, out)))).2) =
        (Memory.spec 0).clientResult s
          (outerStepGenProg
            ((mkHashParams w w₀ R c_tab d_par b_char M_out, (base, (s_val, rKey))), (j, out))) :=
      Prod.ext hstep_fst.symm rfl
    rw [hpair_eq] at hsafe_m hst_m
    refine ⟨⟨hpre, ?_⟩, ?_⟩
    · rw [clientResult_width, clientState_width, hstep_st]; exact hsafe_m
    · unfold iterate
      rw [StateTransitionSpec.clientState_bind, clientResult_width, clientState_width, hstep_st]
      exact hst_m

/-- Parameter-free `Memory.Prog` hash evaluation (`p = (hp, ((base, s_val), u_val))`):
computes `rKey = oddMulModWord w₀ (s.mem base) u_val >>> (w₀ - R)` and evaluates `(c_tab + 1, d)`
bit-packed double tabulation in `O(c_tab * d)` deterministic steps. -/
@[expose] def evalGenProg (p : HashParams × ((ℕ × ℕ) × ℕ)) : Memory.Prog ℕ := do
  let α_val ← Memory.read p.2.1.1
  let x' ← pure (p.2.2 &&& hpMaskM p.1)
  let α₀ ← pure (α_val &&& hpMaskHalf p.1)
  let α₁ ← pure (α_val >>> hpHalfM p.1)
  let x₀ ← pure (x' &&& hpMaskHalf p.1)
  let x₁ ← pure (x' >>> hpHalfM p.1)
  let p₀ ← pure ((α₀ * x₀) &&& hpMaskM p.1)
  let p₁ ← pure (((α₀ * x₁) &&& hpMaskRem p.1) <<< hpHalfM p.1)
  let p₂ ← pure (((α₁ * x₀) &&& hpMaskRem p.1) <<< hpHalfM p.1)
  let p₃ ← pure (((α₁ &&& hpMaskTop p.1) * (x₁ &&& hpMaskTop p.1)) <<< hpTwoHalfM p.1)
  let s₁ ← pure ((p₀ + p₁) &&& hpMaskM p.1)
  let s₂ ← pure ((s₁ + p₂) &&& hpMaskM p.1)
  let hm ← pure ((s₂ + p₃) &&& hpMaskM p.1)
  let one_v ← pure 1
  let rKey ← pure (((p.2.2 &&& one_v) +
    ((((p.2.2 >>> one_v) + hm) &&& hpMaskM p.1) <<< one_v)) >>> hpShiftR p.1)
  let zero_v ← pure 0
  let out ← outerLoopGenProg
    (((p.1, (p.2.1.1, (p.2.1.2, rKey))), (zero_v, zero_v)), hpD p.1)
  pure out.2

/-- Specialized `Memory.Prog` hash evaluation at concrete `(w, w₀, R, c_tab, d, b_char, M_out)`. -/
@[expose] def evalProg (w w₀ R c_tab d b_char M_out : ℕ) (d_in : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ :=
  evalGenProg (mkHashParams w w₀ R c_tab d b_char M_out, d_in)

/-- Precondition for `evalGenProg`. -/
@[expose] def EvalGenPre (w : ℕ) (p : HashParams × ((ℕ × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  HashEnv w p.1 p.2.1.1 ∧
  p.2.1.1 < s.frontier ∧
  s.mem p.2.1.1 ≤ hpMaskM p.1 ∧
  p.2.1.2 < hpPowB p.1 ∧
  p.2.2 ≤ (hpMaskM p.1 <<< 1) + 1

private theorem mul_parts_fits {w₀ w α_val u_val : ℕ} (hw₀ : 0 < w₀) (hw₀_le : w₀ ≤ w)
    (hα : α_val < 2 ^ (w₀ - 1)) (hu : u_val < 2 ^ w₀) :
    let m := w₀ - 1
    let h := m / 2
    let x' := u_val &&& (2 ^ m - 1)
    let α₀ := α_val &&& (2 ^ h - 1)
    let α₁ := α_val >>> h
    let x₀ := x' &&& (2 ^ h - 1)
    let x₁ := x' >>> h
    let p₀ := (α₀ * x₀) &&& (2 ^ m - 1)
    let p₁ := ((α₀ * x₁) &&& (2 ^ (m - h) - 1)) <<< h
    let p₂ := ((α₁ * x₀) &&& (2 ^ (m - h) - 1)) <<< h
    let p₃ := ((α₁ &&& (2 ^ (m - 2 * h) - 1)) * (x₁ &&& (2 ^ (m - 2 * h) - 1))) <<< (2 * h)
    let s₁ := (p₀ + p₁) &&& (2 ^ m - 1)
    let s₂ := (s₁ + p₂) &&& (2 ^ m - 1)
    let hm := (s₂ + p₃) &&& (2 ^ m - 1)
    Fits w (α₀ * x₀) ∧
    Fits w (α₀ * x₁) ∧
    Fits w (((α₀ * x₁) &&& (2 ^ (m - h) - 1)) <<< h) ∧
    Fits w (α₁ * x₀) ∧
    Fits w (((α₁ * x₀) &&& (2 ^ (m - h) - 1)) <<< h) ∧
    Fits w ((α₁ &&& (2 ^ (m - 2 * h) - 1)) * (x₁ &&& (2 ^ (m - 2 * h) - 1))) ∧
    Fits w (((α₁ &&& (2 ^ (m - 2 * h) - 1)) * (x₁ &&& (2 ^ (m - 2 * h) - 1))) <<< (2 * h)) ∧
    Fits w (p₀ + p₁) ∧
    Fits w (s₁ + p₂) ∧
    Fits w (s₂ + p₃) ∧
    Fits w ((u_val >>> 1) + hm) ∧
    Fits w ((((u_val >>> 1) + hm) &&& (2 ^ m - 1)) <<< 1) ∧
    Fits w ((u_val &&& 1) + ((((u_val >>> 1) + hm) &&& (2 ^ m - 1)) <<< 1)) := by
  intro m h x' α₀ α₁ x₀ x₁ p₀ p₁ p₂ p₃ s₁ s₂ hm
  have h2m_lt_w : 2 * 2 ^ m ≤ 2 ^ w := by
    have hm1 : m + 1 = w₀ := Nat.sub_add_cancel hw₀
    calc 2 * 2 ^ m = 2 ^ (m + 1) := (pow_succ' 2 m).symm
      _ = 2 ^ w₀ := by rw [hm1]
      _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hw₀_le
  have hm_lt_w : 2 ^ m < 2 ^ w := by
    have := Nat.two_pow_pos m
    omega
  have h_le : h ≤ m := Nat.div_le_self m 2
  have h2_le : 2 * h ≤ m := Nat.mul_div_le m 2
  have hα₀ : α₀ < 2 ^ h := by
    dsimp only [α₀]; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hx₀ : x₀ < 2 ^ h := by
    dsimp only [x₀]; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hα₁ : α₁ < 2 ^ (m - h) := by
    dsimp only [α₁]; rw [Nat.shiftRight_eq_div_pow]
    refine Nat.div_lt_of_lt_mul ?_
    rw [← pow_add, Nat.add_sub_of_le h_le]
    exact hα
  have hx' : x' < 2 ^ m := by
    dsimp only [x']; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hx₁ : x₁ < 2 ^ (m - h) := by
    dsimp only [x₁]; rw [Nat.shiftRight_eq_div_pow]
    refine Nat.div_lt_of_lt_mul ?_
    rw [← pow_add, Nat.add_sub_of_le h_le]
    exact hx'
  have hp₀_raw : α₀ * x₀ < 2 ^ m := by
    calc α₀ * x₀ < 2 ^ h * 2 ^ h := Nat.mul_lt_mul'' hα₀ hx₀
      _ = 2 ^ (2 * h) := by rw [← pow_add, two_mul]
      _ ≤ 2 ^ m := Nat.pow_le_pow_right two_pos h2_le
  have hp₁_raw : α₀ * x₁ < 2 ^ m := by
    calc α₀ * x₁ < 2 ^ h * 2 ^ (m - h) := Nat.mul_lt_mul'' hα₀ hx₁
      _ = 2 ^ m := by rw [← pow_add, Nat.add_sub_of_le h_le]
  have hp₂_raw : α₁ * x₀ < 2 ^ m := by
    calc α₁ * x₀ < 2 ^ (m - h) * 2 ^ h := Nat.mul_lt_mul'' hα₁ hx₀
      _ = 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel h_le]
  have hp₁_lt : p₁ < 2 ^ m := by
    dsimp only [p₁]; rw [Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod]
    calc ((α₀ * x₁) % 2 ^ (m - h)) * 2 ^ h
        < 2 ^ (m - h) * 2 ^ h := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.two_pow_pos _)
      _ = 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel h_le]
  have hp₂_lt : p₂ < 2 ^ m := by
    dsimp only [p₂]; rw [Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod]
    calc ((α₁ * x₀) % 2 ^ (m - h)) * 2 ^ h
        < 2 ^ (m - h) * 2 ^ h := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.two_pow_pos _)
      _ = 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel h_le]
  have hp₃_mul_lt :
      (α₁ &&& (2 ^ (m - 2 * h) - 1)) * (x₁ &&& (2 ^ (m - 2 * h) - 1)) < 2 ^ (m - 2 * h) := by
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
    have hd_le : m - 2 * h ≤ 1 := by omega
    rcases (by omega : m - 2 * h = 0 ∨ m - 2 * h = 1) with hd0 | hd1
    · rw [hd0, pow_zero, Nat.mod_one, zero_mul]; exact one_pos
    · rw [hd1, pow_one]
      have h1 : α₁ % 2 < 2 := Nat.mod_lt _ two_pos
      have h2 : x₁ % 2 < 2 := Nat.mod_lt _ two_pos
      rcases (by omega : α₁ % 2 = 0 ∨ α₁ % 2 = 1) with h0 | h1_eq
      · simp [h0]
      · simp [h1_eq, h2]
  have hp₃_lt : p₃ < 2 ^ m := by
    dsimp only [p₃]; rw [Nat.shiftLeft_eq]
    calc _ < 2 ^ (m - 2 * h) * 2 ^ (2 * h) :=
          Nat.mul_lt_mul_of_pos_right hp₃_mul_lt (Nat.two_pow_pos _)
      _ = 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel h2_le]
  have hp₀_lt : p₀ < 2 ^ m := by
    dsimp only [p₀]; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hs₁_lt : s₁ < 2 ^ m := by
    dsimp only [s₁]; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hs₂_lt : s₂ < 2 ^ m := by
    dsimp only [s₂]; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hhm_lt : hm < 2 ^ m := by
    dsimp only [hm]; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hu_shr : u_val >>> 1 < 2 ^ m := by
    rw [Nat.shiftRight_eq_div_pow, pow_one]
    refine Nat.div_lt_of_lt_mul ?_
    calc u_val < 2 ^ w₀ := hu
      _ = 2 * 2 ^ m := by rw [← pow_succ', Nat.sub_add_cancel hw₀]
  have hsh_fin : ((((u_val >>> 1) + hm) &&& (2 ^ m - 1)) <<< 1) ≤ 2 * 2 ^ m - 2 := by
    rw [Nat.shiftLeft_eq, pow_one, Nat.and_two_pow_sub_one_eq_mod]
    have hmod : ((u_val >>> 1) + hm) % 2 ^ m < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos _)
    omega
  have hubit : u_val &&& 1 < 2 := by
    change u_val &&& (2 ^ 1 - 1) < 2
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ two_pos
  dsimp only [Fits]
  exact ⟨hp₀_raw.trans hm_lt_w, hp₁_raw.trans hm_lt_w, hp₁_lt.trans hm_lt_w,
    hp₂_raw.trans hm_lt_w, hp₂_lt.trans hm_lt_w,
    hp₃_mul_lt.trans_le ((Nat.pow_le_pow_right two_pos (by omega)).trans hm_lt_w.le),
    hp₃_lt.trans hm_lt_w,
    by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **Parameter-free `Realizes .exact` certificate for `evalGenProg` (`¬ReadsWidth`, single compiled
`Code .exact`)**. -/
theorem realizes_evalGen :
    Realizes .exact evalGenProg
      (WordEncoding.encode (α := HashParams × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := ℕ))
      EvalGenPre
      (fun _ _ => 0) := by
  have hol := realizes_outerLoopGen
  realize
  all_goals (
    rcases d with ⟨hp, ⟨base, s_val⟩, u_val⟩
    obtain ⟨henv, hbase_fr, hα_le, hs_lt, hu_le⟩ := h
    obtain ⟨w₀, R, c_tab, d_par, b_char, M_out, hw, hw₀, hw₀_le, hb, hM, htop_lt, hbot_lt,
      hc1, hd_lt, hfit_sp, heq_hp⟩ := henv
    subst heq_hp
    dsimp only [hpW, hpShiftR, hpHalfM, hpTwoHalfM, hpMaskM, hpMaskHalf, hpMaskRem, hpMaskTop,
      hpBChar, hpMaskB, hpPowB, hpMOut, hpOffBot, hpCPlusOne, hpCTab, hpD,
      mkHashParams_0, mkHashParams_1, mkHashParams_2, mkHashParams_3, mkHashParams_4,
      mkHashParams_5, mkHashParams_6, mkHashParams_7, mkHashParams_8, mkHashParams_9,
      mkHashParams_10, mkHashParams_11, mkHashParams_12, mkHashParams_13, mkHashParams_14,
      mkHashParams_15] at *
    have hα_lt : s.mem base < 2 ^ (w₀ - 1) := by
      have hpos : 1 ≤ 2 ^ (w₀ - 1) := Nat.one_le_two_pow
      omega
    have hu_lt : u_val < 2 ^ w₀ := by
      rw [Nat.shiftLeft_eq, pow_one] at hu_le
      have hpow : 2 * 2 ^ (w₀ - 1) = 2 ^ w₀ := by
        rw [← pow_succ', Nat.sub_add_cancel hw₀]
      have hpos : 1 ≤ 2 ^ (w₀ - 1) := Nat.one_le_two_pow
      omega
    have hmp := mul_parts_fits hw₀ hw₀_le hα_lt hu_lt
  )
  · exact hmp.1
  · exact hmp.2.2.1
  · exact hmp.2.1
  · exact hmp.2.2.2.2.1
  · exact hmp.2.2.2.1
  · exact hmp.2.2.2.2.2.2.1
  · exact hmp.2.2.2.2.2.2.2.1
  · exact hmp.2.2.2.2.2.2.2.2.1
  · exact hmp.2.2.2.2.2.2.2.2.2.1
  · exact Nat.one_lt_two_pow hw.ne'
  · exact hmp.2.2.2.2.2.2.2.2.2.2.2.2
  · exact hmp.2.2.2.2.2.2.2.2.2.2.1
  · refine (outerLoop_invariant
      ⟨w₀, R, c_tab, d_par, b_char, M_out, hw, hw₀, hw₀_le, hb, hM, htop_lt, hbot_lt, hc1,
        hd_lt, hfit_sp, rfl⟩ (by dsimp only [hpPowB_mk]; exact hs_lt) d_par 0 0 ?_
      (by dsimp only [hpMOut_mk]; exact Nat.two_pow_pos M_out)).1
    dsimp only [hpD_mk]; omega

/-! ### Functional correctness, `ValidHistory`, and `memoryCost` of `evalProg` -/

private def innerPrefixXor {c_tab d b_char : ℕ}
    (T₁ : DoubleTabTopSeed (c_tab + 1) d b_char) (chars : Fin (c_tab + 1) → Fin (2 ^ b_char))
    (j : Fin d) (i : ℕ) (hi : i ≤ c_tab + 1) : Fin (2 ^ b_char) :=
  BitString.equivFin b_char
    (∑ k : Fin i,
      (BitString.equivFin b_char).symm
        (T₁ (Fin.castLE hi k) j (chars (Fin.castLE hi k))))

private theorem val_innerPrefixXor_zero {c_tab d b_char : ℕ}
    (T₁ : DoubleTabTopSeed (c_tab + 1) d b_char) (chars : Fin (c_tab + 1) → Fin (2 ^ b_char))
    (j : Fin d) :
    (innerPrefixXor T₁ chars j 0 (Nat.zero_le _)).val = 0 := by
  dsimp only [innerPrefixXor]
  rw [Finset.univ_eq_empty, Finset.sum_empty]
  exact BitString.val_equivFin_false b_char

private theorem val_innerPrefixXor_succ {c_tab d b_char : ℕ}
    (T₁ : DoubleTabTopSeed (c_tab + 1) d b_char) (chars : Fin (c_tab + 1) → Fin (2 ^ b_char))
    (j : Fin d) {i : ℕ} (hi : i + 1 ≤ c_tab + 1) :
    (innerPrefixXor T₁ chars j (i + 1) hi).val =
      (innerPrefixXor T₁ chars j i (Nat.le_of_succ_le hi)).val ^^^
        (T₁ ⟨i, hi⟩ j (chars ⟨i, hi⟩)).val := by
  dsimp only [innerPrefixXor]
  rw [Fin.sum_univ_castSucc, BitString.val_equivFin_add, Equiv.apply_symm_apply]
  rfl

private def outerPrefixXor {c_tab d b_char M_out : ℕ}
    (T₁ : DoubleTabTopSeed (c_tab + 1) d b_char) (T₂ : DoubleTabBotSeed d b_char M_out)
    (chars : Fin (c_tab + 1) → Fin (2 ^ b_char)) (j : ℕ) (hj : j ≤ d) : Fin (2 ^ M_out) :=
  BitString.equivFin M_out
    (∑ k : Fin j,
      (BitString.equivFin M_out).symm
        (T₂ (Fin.castLE hj k) (simpleTabTuple T₁ chars (Fin.castLE hj k))))

private theorem val_outerPrefixXor_zero {c_tab d b_char M_out : ℕ}
    (T₁ : DoubleTabTopSeed (c_tab + 1) d b_char) (T₂ : DoubleTabBotSeed d b_char M_out)
    (chars : Fin (c_tab + 1) → Fin (2 ^ b_char)) :
    (outerPrefixXor T₁ T₂ chars 0 (Nat.zero_le d)).val = 0 := by
  dsimp only [outerPrefixXor]
  rw [Finset.univ_eq_empty, Finset.sum_empty]
  exact BitString.val_equivFin_false M_out

private theorem val_outerPrefixXor_succ {c_tab d b_char M_out : ℕ}
    (T₁ : DoubleTabTopSeed (c_tab + 1) d b_char) (T₂ : DoubleTabBotSeed d b_char M_out)
    (chars : Fin (c_tab + 1) → Fin (2 ^ b_char)) {j : ℕ} (hj : j + 1 ≤ d) :
    (outerPrefixXor T₁ T₂ chars (j + 1) hj).val =
      (outerPrefixXor T₁ T₂ chars j (Nat.le_of_succ_le hj)).val ^^^
        (T₂ ⟨j, hj⟩ (simpleTabTuple T₁ chars ⟨j, hj⟩)).val := by
  dsimp only [outerPrefixXor]
  rw [Fin.sum_univ_castSucc, BitString.val_equivFin_add, Equiv.apply_symm_apply]
  rfl

private theorem iterate_innerStep_eq {base w w₀ R c_tab d b_char M_out s_max : ℕ}
    {θ : Seed w₀ c_tab d b_char M_out} {s : Memory.State}
    (hrep : SeedRep base w w₀ c_tab d b_char M_out θ s.mem)
    (salt : Fin s_max) (rKey : Fin (2 ^ min w₀ R)) (j : Fin d) :
    ∀ m i (him : i + m ≤ c_tab),
      (Memory.spec 0).clientResult s
        (iterate innerStepGenProg
          (mkHashParams w w₀ R c_tab d b_char M_out, (base, j.val)) m
          ((i, (innerPrefixXor θ.2.1 (saltedChars c_tab b_char salt rKey) j i (by omega)).val),
            rKey.val >>> (i * b_char))) =
        ((i + m, (innerPrefixXor θ.2.1 (saltedChars c_tab b_char salt rKey) j (i + m)
          (by omega)).val), rKey.val >>> ((i + m) * b_char)) ∧
      (Memory.spec 0).clientState s
        (iterate innerStepGenProg
          (mkHashParams w w₀ R c_tab d b_char M_out, (base, j.val)) m
          ((i, (innerPrefixXor θ.2.1 (saltedChars c_tab b_char salt rKey) j i (by omega)).val),
            rKey.val >>> (i * b_char))) = s := by
  intro m
  induction m with
  | zero =>
    intro i _
    have h0 : i + 0 = i := Nat.add_zero i
    simp only [h0]
    exact ⟨rfl, rfl⟩
  | succ m ih =>
    intro i him
    have hi_lt : i < c_tab := by omega
    have hch_eq : ((rKey.val >>> (i * b_char)) &&& (2 ^ b_char - 1)) =
        (saltedChars c_tab b_char salt rKey ⟨i, by omega⟩).val := by
      have hcast : (⟨i, by omega⟩ : Fin (c_tab + 1)) = (⟨i, hi_lt⟩ : Fin c_tab).castSucc := rfl
      rw [hcast, saltedChars, Fin.snoc_castSucc]
      rfl
    have ht_eq : readPacked (base + 1) b_char w s.mem
        ((j.val * (c_tab + 1) + i) * 2 ^ b_char +
          ((rKey.val >>> (i * b_char)) &&& (2 ^ b_char - 1))) =
        (θ.2.1 ⟨i, by omega⟩ j (saltedChars c_tab b_char salt rKey ⟨i, by omega⟩)).val := by
      rw [hch_eq]
      exact hrep.2.1 ⟨i, by omega⟩ j _
    have hshr : (rKey.val >>> (i * b_char)) >>> b_char = rKey.val >>> ((i + 1) * b_char) := by
      rw [← Nat.shiftRight_add, Nat.add_mul, Nat.one_mul]
    have hy_succ := val_innerPrefixXor_succ θ.2.1 (saltedChars c_tab b_char salt rKey) j
      (i := i) (by omega)
    have hstep_res : (Memory.spec 0).clientResult s
        (innerStepGenProg ((mkHashParams w w₀ R c_tab d b_char M_out, (base, j.val)),
          ((i, (innerPrefixXor θ.2.1 (saltedChars c_tab b_char salt rKey) j i (by omega)).val),
            rKey.val >>> (i * b_char)))) =
        ((i + 1, (innerPrefixXor θ.2.1 (saltedChars c_tab b_char salt rKey) j (i + 1)
          (by omega)).val), rKey.val >>> ((i + 1) * b_char)) := by
      unfold innerStepGenProg readPackedGenProg
      simp only [pure_bind, hpMaskB_mk, hpCPlusOne_mk, hpPowB_mk, hpBChar_mk, hpW_mk]
      rw [StateTransitionSpec.clientResult_bind, clientState_width, clientResult_width,
        clientResult_readPackedProg, clientState_readPackedProg, clientResult_pure',
        ht_eq, ← hy_succ, hshr]
    have hstep_st : (Memory.spec 0).clientState s
        (innerStepGenProg ((mkHashParams w w₀ R c_tab d b_char M_out, (base, j.val)),
          ((i, (innerPrefixXor θ.2.1 (saltedChars c_tab b_char salt rKey) j i (by omega)).val),
            rKey.val >>> (i * b_char)))) = s := rfl
    obtain ⟨hres_m, hst_m⟩ := ih (i + 1) (by omega)
    have him_eq : i + 1 + m = i + (m + 1) := by omega
    refine ⟨?_, ?_⟩
    · unfold iterate
      rw [StateTransitionSpec.clientResult_bind, clientState_width, clientResult_width,
        hstep_st, hstep_res, hres_m]
      simp only [him_eq]
    · unfold iterate
      rw [StateTransitionSpec.clientState_bind, clientState_width, clientResult_width,
        hstep_st, hstep_res, hst_m]

private theorem iterate_outerStep_eq {base w w₀ R c_tab d b_char M_out s_max : ℕ}
    {θ : Seed w₀ c_tab d b_char M_out} {s : Memory.State}
    (hs_max : s_max ≤ 2 ^ b_char)
    (hrep : SeedRep base w w₀ c_tab d b_char M_out θ s.mem)
    (salt : Fin s_max) (rKey : Fin (2 ^ min w₀ R)) :
    ∀ m j (hjm : j + m ≤ d),
      (Memory.spec 0).clientResult s
        (iterate outerStepGenProg
          (mkHashParams w w₀ R c_tab d b_char M_out, (base, (salt.val, rKey.val))) m
          (j, (outerPrefixXor θ.2.1 θ.2.2 (saltedChars c_tab b_char salt rKey) j (by omega)).val)) =
        (j + m, (outerPrefixXor θ.2.1 θ.2.2 (saltedChars c_tab b_char salt rKey) (j + m)
          (by omega)).val) ∧
      (Memory.spec 0).clientState s
        (iterate outerStepGenProg
          (mkHashParams w w₀ R c_tab d b_char M_out, (base, (salt.val, rKey.val))) m
          (j, (outerPrefixXor θ.2.1 θ.2.2 (saltedChars c_tab b_char salt rKey) j
            (by omega)).val)) = s := by
  intro m
  induction m with
  | zero =>
    intro j _
    have h0 : j + 0 = j := Nat.add_zero j
    simp only [h0]
    exact ⟨rfl, rfl⟩
  | succ m ih =>
    intro j hjm
    have hj_lt : j < d := by omega
    let chars := saltedChars c_tab b_char salt rKey
    have hin := iterate_innerStep_eq hrep salt rKey ⟨j, hj_lt⟩ c_tab 0 (by omega)
    simp only [zero_add, zero_mul, Nat.shiftRight_zero, val_innerPrefixXor_zero] at hin
    have hsalt_ch : salt.val = (chars (Fin.last c_tab)).val := by
      dsimp only [chars, saltedChars]
      rw [Fin.snoc_last]
      exact (Nat.mod_eq_of_lt (salt.isLt.trans_le hs_max)).symm
    have htsalt : readPacked (base + 1) b_char w s.mem
        ((j * (c_tab + 1) + c_tab) * 2 ^ b_char + salt.val) =
        (θ.2.1 (Fin.last c_tab) ⟨j, hj_lt⟩ (chars (Fin.last c_tab))).val := by
      rw [hsalt_ch]
      exact hrep.2.1 (Fin.last c_tab) ⟨j, hj_lt⟩ _
    have hy_full : (innerPrefixXor θ.2.1 chars ⟨j, hj_lt⟩ c_tab (by omega)).val ^^^
        (θ.2.1 (Fin.last c_tab) ⟨j, hj_lt⟩ (chars (Fin.last c_tab))).val =
        (simpleTabTuple θ.2.1 chars ⟨j, hj_lt⟩).val := by
      have hs := val_innerPrefixXor_succ θ.2.1 chars ⟨j, hj_lt⟩ (i := c_tab) le_rfl
      exact hs.symm
    have hz_eq : readPacked (base + offBot w c_tab d b_char) M_out w s.mem
        (j * 2 ^ b_char + (simpleTabTuple θ.2.1 chars ⟨j, hj_lt⟩).val) =
        (θ.2.2 ⟨j, hj_lt⟩ (simpleTabTuple θ.2.1 chars ⟨j, hj_lt⟩)).val :=
      hrep.2.2 ⟨j, hj_lt⟩ _
    have hout_succ := val_outerPrefixXor_succ θ.2.1 θ.2.2 chars (j := j) (by omega)
    have hstep_st : (Memory.spec 0).clientState s
        (outerStepGenProg
          ((mkHashParams w w₀ R c_tab d b_char M_out, (base, (salt.val, rKey.val))),
            (j, (outerPrefixXor θ.2.1 θ.2.2 chars j (by omega)).val))) = s := by
      unfold outerStepGenProg innerLoopGenProg readPackedGenProg
      simp only [pure_bind, hpCTab_mk]
      rw [StateTransitionSpec.clientState_bind, clientState_width, hin.2,
        StateTransitionSpec.clientState_bind, clientState_width, clientState_readPackedProg,
        StateTransitionSpec.clientState_bind, clientState_width, clientState_readPackedProg]
      rfl
    have hstep_res : (Memory.spec 0).clientResult s
        (outerStepGenProg
          ((mkHashParams w w₀ R c_tab d b_char M_out, (base, (salt.val, rKey.val))),
            (j, (outerPrefixXor θ.2.1 θ.2.2 chars j (by omega)).val))) =
        (j + 1, (outerPrefixXor θ.2.1 θ.2.2 chars (j + 1) (by omega)).val) := by
      unfold outerStepGenProg innerLoopGenProg readPackedGenProg
      simp only [pure_bind, hpCTab_mk, hpCPlusOne_mk, hpPowB_mk, hpBChar_mk, hpW_mk,
        hpOffBot_mk, hpMOut_mk]
      rw [StateTransitionSpec.clientResult_bind, clientState_width, clientResult_width,
        hin.2, hin.1,
        StateTransitionSpec.clientResult_bind, clientState_width, clientResult_width,
        clientState_readPackedProg, clientResult_readPackedProg,
        StateTransitionSpec.clientResult_bind, clientState_width, clientResult_width,
        clientState_readPackedProg, clientResult_readPackedProg, clientResult_pure',
        htsalt, hy_full, hz_eq, ← hout_succ]
    obtain ⟨hres_m, hst_m⟩ := ih (j + 1) (by omega)
    have hjm_eq : j + 1 + m = j + (m + 1) := by omega
    refine ⟨?_, ?_⟩
    · unfold iterate
      rw [StateTransitionSpec.clientResult_bind, clientState_width, clientResult_width,
        hstep_st, hstep_res, hres_m]
      simp only [hjm_eq]
    · unfold iterate
      rw [StateTransitionSpec.clientState_bind, clientState_width, clientResult_width,
        hstep_st, hstep_res, hst_m]

/-- **Exact functional correctness and state preservation of `evalProg`**:
under `SeedRep`, `evalProg` leaves `s` unchanged and returns `(evalSalted ... θ (salt, u)).val`. -/
theorem evalProg_spec {U w w₀ R c_tab d b_char M_out s_max base : ℕ}
    {θ : Seed w₀ c_tab d b_char M_out} {s : Memory.State}
    (hw₀ : 0 < w₀) (hs_max : s_max ≤ 2 ^ b_char)
    (hrep : SeedRep base w w₀ c_tab d b_char M_out θ s.mem)
    (salt : Fin s_max) (u : Fin U) :
    (Memory.spec 0).clientResult s
      (evalProg w w₀ R c_tab d b_char M_out ((base, salt.val), u.val)) =
      (evalSalted U w₀ R c_tab d b_char M_out s_max θ (salt, u)).val ∧
    (Memory.spec 0).clientState s
      (evalProg w w₀ R c_tab d b_char M_out ((base, salt.val), u.val)) = s := by
  have hrkey_eq :
      oddMulModWord w₀ (s.mem base) u.val >>> (w₀ - R) =
        (multiplyShiftReduced U w₀ R θ.1 u).val := by
    rw [hrep.1]
    exact oddMulModWord_shiftRight_eq_multiplyShiftReduced hw₀ θ.1 u
  have hout := iterate_outerStep_eq hs_max hrep salt (multiplyShiftReduced U w₀ R θ.1 u) d 0
    (by omega)
  simp only [zero_add, val_outerPrefixXor_zero] at hout
  have hread_res : (Memory.spec 0).clientResult s (Memory.read base) = s.mem base := rfl
  have hread_st : (Memory.spec 0).clientState s (Memory.read base) = s := rfl
  unfold evalProg evalGenProg outerLoopGenProg
  simp only [pure_bind, hpMaskM_mk, hpMaskHalf_mk, hpHalfM_mk, hpMaskRem_mk, hpMaskTop_mk,
    hpTwoHalfM_mk, hpShiftR_mk, hpD_mk]
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    clientState_width, clientResult_width, hread_res, hread_st,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    clientState_width, clientResult_width, clientResult_pure', clientState_pure']
  change (((Memory.spec 0).clientResult s
      (iterate outerStepGenProg
        (mkHashParams w w₀ R c_tab d b_char M_out,
          (base, (salt.val, oddMulModWord w₀ (s.mem base) u.val >>> (w₀ - R)))) d (0, 0))).2 = _ ∧
    (Memory.spec 0).clientState s
      (iterate outerStepGenProg
        (mkHashParams w w₀ R c_tab d b_char M_out,
          (base, (salt.val, oddMulModWord w₀ (s.mem base) u.val >>> (w₀ - R)))) d (0, 0)) = s)
  rw [hrkey_eq, hout.1, hout.2]
  exact ⟨rfl, rfl⟩

/-- Exact `memoryCost` of `evalProg`: `1 + 2 * d * (c_tab + 2)` (`O(c_tab * d)`). -/
theorem memoryCost_evalProg (w w₀ R c_tab d b_char M_out : ℕ) (d_in : (ℕ × ℕ) × ℕ)
    (s : Memory.State) :
    memoryCost (evalProg w w₀ R c_tab d b_char M_out d_in) s = 1 + 2 * d * (c_tab + 2) := by
  have hin_cost : ∀ j m i y r,
      memoryCost (iterate innerStepGenProg
        (mkHashParams w w₀ R c_tab d b_char M_out, (d_in.1.1, j)) m ((i, y), r)) s = 2 * m ∧
      (Memory.spec 0).clientState s
        (iterate innerStepGenProg
          (mkHashParams w w₀ R c_tab d b_char M_out, (d_in.1.1, j)) m ((i, y), r)) = s := by
    intro j m
    induction m with
    | zero =>
      intro i y r
      exact ⟨rfl, rfl⟩
    | succ m ih =>
      intro i y r
      have hst1 : (Memory.spec 0).clientState s
          (innerStepGenProg
            ((mkHashParams w w₀ R c_tab d b_char M_out, (d_in.1.1, j)), ((i, y), r))) = s := rfl
      have hres1 : (Memory.spec 0).clientResult s
          (innerStepGenProg
            ((mkHashParams w w₀ R c_tab d b_char M_out, (d_in.1.1, j)), ((i, y), r))) =
          ((i + 1, y ^^^ readPacked (d_in.1.1 + 1) b_char w s.mem
            ((j * (c_tab + 1) + i) * 2 ^ b_char + (r &&& (2 ^ b_char - 1)))),
            r >>> b_char) := by
        unfold innerStepGenProg readPackedGenProg
        simp only [pure_bind, hpMaskB_mk, hpCPlusOne_mk, hpPowB_mk, hpBChar_mk, hpW_mk]
        rw [StateTransitionSpec.clientResult_bind, clientState_width, clientResult_width,
          clientResult_readPackedProg, clientState_readPackedProg, clientResult_pure']
      obtain ⟨hc_m, hst_m⟩ := ih (i + 1)
        (y ^^^ readPacked (d_in.1.1 + 1) b_char w s.mem
          ((j * (c_tab + 1) + i) * 2 ^ b_char + (r &&& (2 ^ b_char - 1))))
        (r >>> b_char)
      refine ⟨?_, ?_⟩
      · unfold iterate
        rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_innerStepGenProg,
          clientState_width, clientResult_width, hst1, hres1, hc_m]
        ring
      · unfold iterate
        rw [StateTransitionSpec.clientState_bind, clientState_width, clientResult_width,
          hst1, hres1, hst_m]
  have hout_cost : ∀ rKey m j out,
      memoryCost (iterate outerStepGenProg
        (mkHashParams w w₀ R c_tab d b_char M_out, (d_in.1.1, (d_in.1.2, rKey))) m (j, out)) s =
        2 * m * (c_tab + 2) := by
    intro rKey m
    induction m with
    | zero =>
      intro j out
      change 0 = 2 * 0 * (c_tab + 2)
      simp
    | succ m ih =>
      intro j out
      obtain ⟨hinc, hinst⟩ := hin_cost j c_tab 0 0 rKey
      have hstep_cost : memoryCost (outerStepGenProg
          ((mkHashParams w w₀ R c_tab d b_char M_out, (d_in.1.1, (d_in.1.2, rKey))), (j, out))) s =
          2 * (c_tab + 2) := by
        unfold outerStepGenProg innerLoopGenProg readPackedGenProg
        simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, hpCTab_mk]
        rw [memoryCost_bind, clientState_width, hinc, hinst,
          memoryCost_bind, clientState_width, clientState_readPackedProg, memoryCost_readPackedProg,
          memoryCost_bind, clientState_width, clientState_readPackedProg, memoryCost_readPackedProg,
          memoryCost_pure]
        ring
      have hstep_st : (Memory.spec 0).clientState s
          (outerStepGenProg
            ((mkHashParams w w₀ R c_tab d b_char M_out, (d_in.1.1, (d_in.1.2, rKey))),
              (j, out))) = s := by
        unfold outerStepGenProg innerLoopGenProg readPackedGenProg
        simp only [pure_bind, hpCTab_mk]
        rw [StateTransitionSpec.clientState_bind, clientState_width, hinst,
          StateTransitionSpec.clientState_bind, clientState_width, clientState_readPackedProg,
          StateTransitionSpec.clientState_bind, clientState_width, clientState_readPackedProg,
          clientState_pure']
      unfold iterate
      rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hstep_cost, clientState_width, hstep_st,
        ih]
      ring
  have hread_cost : memoryCost (Memory.read d_in.1.1) s = 1 := rfl
  have hread_st : (Memory.spec 0).clientState s (Memory.read d_in.1.1) = s := rfl
  unfold evalProg evalGenProg outerLoopGenProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, hpD_mk]
  rw [memoryCost_bind, hread_cost, hread_st, memoryCost_bind, hout_cost, memoryCost_pure]
  omega

private theorem validHistory_bind_of_eq {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : (Memory.spec w).ValidHistory ((Memory.spec 0).clientState s p)
      ((Memory.spec w).clientHistory ((Memory.spec 0).clientState s p)
        (q ((Memory.spec 0).clientResult s p)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) := by
  change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p.bind q))
  rw [validHistory_bind, clientResult_width, clientState_width]
  exact ⟨hp, hq⟩

private theorem validHistory_iterate_of_safe {δ σ : Type} {w : ℕ}
    {body : δ × σ → Memory.Prog σ} {safe : ℕ → δ × σ → Memory.State → Prop}
    {d : δ} (n : ℕ) (a : σ) (s : Memory.State)
    (hst : ∀ a' s', safe w (d, a') s' → (Memory.spec 0).clientState s' (body (d, a')) = s')
    (hbody : ∀ a', safe w (d, a') s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (body (d, a'))))
    (hsafe : iterationSafe body safe w d n a s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (iterate body d n a)) := by
  induction n generalizing a with
  | zero => trivial
  | succ n ih =>
    unfold iterate
    unfold iterationSafe at hsafe
    apply validHistory_bind_of_eq (hbody a hsafe.1)
    have hst' := hst a s hsafe.1
    rw [clientResult_width, clientState_width] at hsafe
    rw [hst'] at hsafe ⊢
    exact ih _ hsafe.2

/-- Memory history admissibility (`ValidHistory`) for `evalGenProg` under `EvalGenPre` and
`base + space ≤ s.frontier`. -/
theorem validHistory_evalGenProg {w : ℕ} {p : HashParams × ((ℕ × ℕ) × ℕ)} {s : Memory.State}
    (hpre : EvalGenPre w p s)
    (hfr : p.2.1.1 + space w (hpCTab p.1) (hpD p.1) (hpBChar p.1) (hpMOut p.1) ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (evalGenProg p)) := by
  rcases p with ⟨hp, ⟨base, s_val⟩, u_val⟩
  obtain ⟨henv, hbase_fr, _, hs_lt, _⟩ := hpre
  obtain ⟨w₀, R, c_tab, d_par, b_char, M_out, hw, hw₀, hw₀_le, hb, hM, htop_lt, hbot_lt,
    hc1, hd_lt, hfit_sp, heq_hp⟩ := henv
  subst heq_hp
  have henv' : HashEnv w (mkHashParams w w₀ R c_tab d_par b_char M_out) base :=
    ⟨w₀, R, c_tab, d_par, b_char, M_out, hw, hw₀, hw₀_le, hb, hM, htop_lt, hbot_lt, hc1,
      hd_lt, hfit_sp, rfl⟩
  dsimp only [hpCTab_mk, hpD_mk, hpBChar_mk, hpMOut_mk, hpPowB_mk] at hfr hs_lt
  have hinner_valid : ∀ j (hj : j < d_par) rKey,
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate innerStepGenProg
            (mkHashParams w w₀ R c_tab d_par b_char M_out, (base, j)) c_tab
            ((0, 0), rKey))) := by
    intro j hj rKey
    have hinv := innerLoop_invariant (s := s) henv' (by dsimp only [hpD_mk]; exact hj)
      c_tab 0 0 rKey (by dsimp only [hpCTab_mk]; omega)
      (by dsimp only [hpPowB_mk]; exact Nat.two_pow_pos b_char)
    refine validHistory_iterate_of_safe c_tab ((0, 0), rKey) s (fun _ _ _ => rfl) ?_ hinv.1
    intro ⟨⟨i, y⟩, r⟩ hsafe_in
    have hi_lt : i < c_tab := by simpa only [hpCTab_mk] using hsafe_in.2.2.1
    have hch_lt : r &&& (2 ^ b_char - 1) < 2 ^ b_char := by
      rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hidx_lt : (j * (c_tab + 1) + i) * 2 ^ b_char + (r &&& (2 ^ b_char - 1)) <
        topEntries c_tab d_par b_char := by
      have h := DoubleTabulation.topAddr_lt_base_add_topWords 0 (c_tab + 1) d_par b_char
        ⟨i, by omega⟩ ⟨j, hj⟩ ⟨_, hch_lt⟩
      dsimp only [DoubleTabulation.topAddr, DoubleTabulation.topWords, topEntries] at h ⊢
      omega
    unfold innerStepGenProg readPackedGenProg
    simp only [pure_bind, hpMaskB_mk, hpCPlusOne_mk, hpPowB_mk, hpBChar_mk, hpW_mk]
    refine validHistory_bind_of_eq ?_ trivial
    exact validHistory_readPackedProg hw hidx_lt (by unfold space topWords at hfr; omega)
  have houter_valid : ∀ rKey,
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate outerStepGenProg
            (mkHashParams w w₀ R c_tab d_par b_char M_out, (base, (s_val, rKey))) d_par
            (0, 0))) := by
    intro rKey
    have hinv_out := outerLoop_invariant (rKey := rKey) (s := s) henv'
      (by dsimp only [hpPowB_mk]; exact hs_lt)
      d_par 0 0 (by dsimp only [hpD_mk]; omega)
      (by dsimp only [hpMOut_mk]; exact Nat.two_pow_pos _)
    refine validHistory_iterate_of_safe d_par (0, 0) s ?_ ?_ hinv_out.1
    · intro ⟨j, out⟩ s' hsafe_out
      have hj : j < d_par := by simpa only [hpD_mk] using hsafe_out.2.2.1
      have hin := innerLoop_invariant (s := s') henv' (by dsimp only [hpD_mk]; exact hj)
        c_tab 0 0 rKey (by dsimp only [hpCTab_mk]; omega)
        (by dsimp only [hpPowB_mk]; exact Nat.two_pow_pos b_char)
      unfold outerStepGenProg innerLoopGenProg readPackedGenProg
      simp only [pure_bind, hpCTab_mk]
      rw [StateTransitionSpec.clientState_bind, clientState_width, hin.2.1,
        StateTransitionSpec.clientState_bind, clientState_width, clientState_readPackedProg,
        StateTransitionSpec.clientState_bind, clientState_width, clientState_readPackedProg,
        clientState_pure']
    · intro ⟨j, out⟩ hsafe_out
      have hj : j < d_par := by simpa only [hpD_mk] using hsafe_out.2.2.1
      have hin := innerLoop_invariant (s := s) henv' (by dsimp only [hpD_mk]; exact hj)
        c_tab 0 0 rKey (by dsimp only [hpCTab_mk]; omega)
        (by dsimp only [hpPowB_mk]; exact Nat.two_pow_pos b_char)
      have hidx_s : (j * (c_tab + 1) + c_tab) * 2 ^ b_char + s_val <
          topEntries c_tab d_par b_char := by
        have h := DoubleTabulation.topAddr_lt_base_add_topWords 0 (c_tab + 1) d_par b_char
          ⟨c_tab, by omega⟩ ⟨j, hj⟩ ⟨s_val, hs_lt⟩
        dsimp only [DoubleTabulation.topAddr, DoubleTabulation.topWords, topEntries] at h ⊢
        omega
      unfold outerStepGenProg innerLoopGenProg readPackedGenProg
      simp only [pure_bind, hpCTab_mk, hpCPlusOne_mk, hpPowB_mk, hpBChar_mk, hpW_mk,
        hpOffBot_mk, hpMOut_mk]
      refine validHistory_bind_of_eq (hinner_valid j hj rKey) ?_
      rw [hin.2.1]
      refine validHistory_bind_of_eq
        (validHistory_readPackedProg hw hidx_s (by unfold space topWords at hfr; omega)) ?_
      rw [clientState_readPackedProg, clientResult_readPackedProg]
      refine validHistory_bind_of_eq
        (validHistory_readPackedProg hw
          (mul_add_xor_lt_botEntries hj (by simpa only [hpPowB_mk] using hin.2.2)
            (readPacked_lt _ _ _ _ _))
          (by unfold space botWords at hfr; unfold offBot; omega))
        trivial
  unfold evalGenProg outerLoopGenProg
  have hread_valid : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.read base)) := ⟨hbase_fr, trivial⟩
  have hread_st : (Memory.spec 0).clientState s (Memory.read base) = s := rfl
  refine validHistory_bind_of_eq hread_valid ?_
  rw [hread_st]
  simp only [pure_bind, hpD_mk]
  exact validHistory_bind_of_eq (houter_valid _) trivial

/-- Specialized `ValidHistory` lemma for `evalProg`. -/
theorem validHistory_evalProg {w w₀ R c_tab d b_char M_out : ℕ} {d_in : (ℕ × ℕ) × ℕ}
    {s : Memory.State}
    (hpre : EvalGenPre w (mkHashParams w w₀ R c_tab d b_char M_out, d_in) s)
    (hfr : d_in.1.1 + space w c_tab d b_char M_out ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (evalProg w w₀ R c_tab d b_char M_out d_in)) :=
  validHistory_evalGenProg hpre hfr

end Cslib.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation

end

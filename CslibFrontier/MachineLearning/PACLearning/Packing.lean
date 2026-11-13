/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.GrowthFunction
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Packing numbers of a binary class on a sample

Fix points `x : Fin m → α` and a binary concept class `C`. A set `P` of labelings of `x` realized
by `C` is *`ε`-separated* if any two distinct labelings in `P` differ on at least `ε m` of the
points, i.e. their normalized Hamming distance is at least `ε`. This file bounds the size of such
a set by the growth function, and hence, by Sauer's lemma, by a power of `1 / ε` whose exponent is
proportional to the VC dimension and independent of `m`.

The argument is *subsampling* [Vershynin2018, Lemma 8.3.19 and Theorem 8.3.18]. A uniformly random
tuple `t` of `k` indices separates a fixed pair of `ε`-separated labelings unless all `k` indices
land where they agree, which happens with probability at most `(1 - ε) ^ k ≤ exp (-ε k)`. When
`|P|² exp (-ε k) < 1`, some `t` separates every pair, so the labelings in `P` stay distinct on the
`k` points `x ∘ t` and `|P| ≤ Π_C(k)`. The proof counts the tuples directly. Taking
`k = ⌊2 log |P| / ε⌋ + 1` and the form `Π_C(k) ≤ exp (k / T) T ^ d` of Sauer's lemma with
`T = 4 / ε` gives `|P| ≤ (8 / ε) ^ (2 d)` when every set shattered by `C` has at most `d` points.
This is Dudley's bound, with a constant in the exponent; Haussler's sharper
`e (d + 1) (2 e / ε) ^ d` needs a different argument and is not formalized here.

A maximal separated subset is also a net at the same scale
(`Cslib.Code.exists_subset_pairwise_lt_hammingDist_forall_exists_le`), so the bound also limits the
size of nets. Chaining arguments need nets at every scale whose sizes grow polynomially in `1 / ε`.
They give the agnostic sample complexity `O((d + log (1 / δ)) / ε²)` stated in
[ShalevShwartzBenDavid2014, Theorem 6.8]. That book proves only the weaker
`O((d log (d / ε) + log (1 / δ)) / ε²)` (Section 28.1), leaving out the chaining argument
(Lemma 27.4) that the sharp form needs.

## Main results

- `exists_injOn_comp_of_two_mul_log_card_lt`: a tuple of `k` indices on which the words of an
  `ε`-separated set stay distinct, when `2 log |P| < ε k`.
- `card_le_growthFunction_of_two_mul_log_card_lt`: an `ε`-separated set of labelings realized by
  `C` has at most `Π_C(k)` elements.
- `card_le_div_pow_of_le_hammingDist`: with Sauer's lemma, it has at most `(8 / ε) ^ (2 d)`.

## References

* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018], Section 8.3
* [R. M. Dudley, *Central limit theorems for empirical measures*][Dudley1978]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open Finset

namespace Cslib.MachineLearning.PACLearning

variable {α : Type*}

/-- **Subsampling.** If any two distinct words in `P` differ in at least `ε m` of their `m` letters
and `2 log |P| < ε k`, then some `k` of the positions, possibly repeated, already distinguish all
words in `P`. -/
theorem exists_injOn_comp_of_two_mul_log_card_lt {β : Type*} [DecidableEq β] {m k : ℕ}
    (hm : 0 < m) (P : Finset (Fin m → β)) {ε : ℝ}
    (hP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ε * m ≤ hammingDist u v)
    (hk : 2 * Real.log P.card < ε * k) :
    ∃ t : Fin k → Fin m, Set.InjOn (fun (u : Fin m → β) j => u (t j)) P := by
  classical
  -- The tuples on which a given ordered pair of distinct words agree.
  set agree : (Fin m → β) × (Fin m → β) → Finset (Fin m) := fun p => univ.filter
    fun i => p.1 i = p.2 i
  set bad : Finset (Fin k → Fin m) :=
    P.offDiag.biUnion fun p => Fintype.piFinset fun _ : Fin k => agree p
  -- A pair at Hamming distance at least `ε m` agrees on at most `exp (-ε) m` points.
  have hagree : ∀ p ∈ P.offDiag, ((agree p).card : ℝ) ≤ Real.exp (-ε) * m := by
    intro p hp
    obtain ⟨hp1, hp2, hne⟩ := mem_offDiag.1 hp
    have hsum : (agree p).card + hammingDist p.1 p.2 = m := by
      have := card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
        (fun i => p.1 i = p.2 i)
      simpa [agree, hammingDist] using this
    have hd := hP _ hp1 _ hp2 hne
    have hcast : ((agree p).card : ℝ) + hammingDist p.1 p.2 = m := by exact_mod_cast hsum
    have hexp : 1 - ε ≤ Real.exp (-ε) := by linarith [Real.add_one_le_exp (-ε)]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  -- Fewer than `m ^ k` tuples are bad.
  have hbad : bad.card < Fintype.card (Fin k → Fin m) := by
    rcases P.eq_empty_or_nonempty with hP0 | hPne
    · simp only [bad, hP0, offDiag_empty, biUnion_empty, card_empty, Fintype.card_fun,
        Fintype.card_fin]
      exact pow_pos hm k
    have hN : (0 : ℝ) < P.card := by exact_mod_cast hPne.card_pos
    have hcard : (bad.card : ℝ) ≤ P.card ^ 2 * (Real.exp (-ε) * m) ^ k := by
      calc (bad.card : ℝ) ≤ ∑ p ∈ P.offDiag, ((agree p).card : ℝ) ^ k := by
            have := card_biUnion_le (s := P.offDiag)
              (t := fun p => Fintype.piFinset fun _ : Fin k => agree p)
            simp only [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin] at this
            exact_mod_cast this
        _ ≤ ∑ _p ∈ P.offDiag, (Real.exp (-ε) * m) ^ k :=
            sum_le_sum fun p hp => pow_le_pow_left₀ (Nat.cast_nonneg _) (hagree p hp) k
        _ = P.offDiag.card * (Real.exp (-ε) * m) ^ k := by rw [sum_const, nsmul_eq_mul]
        _ ≤ P.card ^ 2 * (Real.exp (-ε) * m) ^ k := by
            gcongr
            rw [offDiag_card]
            exact_mod_cast (Nat.sub_le _ _).trans (by rw [sq])
    have hlt : (P.card : ℝ) ^ 2 * Real.exp (-ε) ^ k < 1 := by
      rw [← Real.exp_log hN, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add,
        Real.exp_lt_one_iff]
      push_cast
      linarith
    have hmk : (0 : ℝ) < (m : ℝ) ^ k := by positivity
    have : (bad.card : ℝ) < (m : ℝ) ^ k := by
      calc (bad.card : ℝ) ≤ P.card ^ 2 * (Real.exp (-ε) * m) ^ k := hcard
        _ = (P.card ^ 2 * Real.exp (-ε) ^ k) * (m : ℝ) ^ k := by ring
        _ < 1 * (m : ℝ) ^ k := by gcongr
        _ = (m : ℝ) ^ k := one_mul _
    simpa [Fintype.card_fun] using (by exact_mod_cast this : bad.card < m ^ k)
  obtain ⟨t, -, ht⟩ := exists_mem_notMem_of_card_lt_card (s := bad) (t := univ)
    (by simpa using hbad)
  refine ⟨t, fun u hu v hv huv => ?_⟩
  by_contra hne
  refine ht (mem_biUnion.2 ⟨(u, v), mem_offDiag.2 ⟨hu, hv, hne⟩, ?_⟩)
  simp only [Fintype.mem_piFinset, agree, mem_filter, mem_univ, true_and]
  exact fun j => congrFun huv j

/-- **Packing by the growth function.** If the labelings in `P ⊆ restriction C x` pairwise differ
on at least `ε m` of the `m > 0` points `x` and `2 log |P| < ε k`, then `|P| ≤ Π_C(k)`. -/
theorem card_le_growthFunction_of_two_mul_log_card_lt (C : ConceptClass α Bool) {m k : ℕ}
    (hm : 0 < m) {x : Fin m → α} {P : Finset (Fin m → Bool)}
    (hPC : ∀ u ∈ P, u ∈ restriction C x) {ε : ℝ}
    (hP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ε * m ≤ hammingDist u v)
    (hk : 2 * Real.log P.card < ε * k) :
    P.card ≤ growthFunction C k := by
  classical
  obtain ⟨t, ht⟩ := exists_injOn_comp_of_two_mul_log_card_lt hm P hP hk
  calc P.card = (P.image fun (u : Fin m → Bool) j => u (t j)).card := (card_image_of_injOn ht).symm
    _ = ((P.image fun (u : Fin m → Bool) j => u (t j) : Finset _) : Set (Fin k → Bool)).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ (restriction C (x ∘ t)).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.toFinite _)
        intro w hw
        obtain ⟨u, hu, rfl⟩ := mem_image.1 (mem_coe.1 hw)
        obtain ⟨c, hc, hcu⟩ := mem_restriction.1 (hPC u hu)
        exact mem_restriction.2 ⟨c, hc, fun j => hcu (t j)⟩
    _ ≤ growthFunction C k := ncard_restriction_le_growthFunction C (x ∘ t)

/-- **Packing bound for VC classes** [Vershynin2018, Theorem 8.3.18; Dudley1978]: if every set
shattered by `C` has at most `d` points, a set of labelings realized by `C` on `m` points whose
members pairwise differ on at least `ε m` points, `0 < ε ≤ 1`, has at most `(8 / ε) ^ (2 d)`
elements. -/
theorem card_le_div_pow_of_le_hammingDist {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ} {x : Fin m → α}
    {P : Finset (Fin m → Bool)} (hPC : ∀ u ∈ P, u ∈ restriction C x) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ε * m ≤ hammingDist u v) :
    (P.card : ℝ) ≤ (8 / ε) ^ (2 * d) := by
  have hone : (1 : ℝ) ≤ (8 / ε) ^ (2 * d) :=
    one_le_pow₀ (by rw [le_div_iff₀ hε]; linarith)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- On no points there is a single labeling.
    have : P.card ≤ 1 := (card_le_univ P).trans (by simp)
    exact (by exact_mod_cast this : (P.card : ℝ) ≤ 1).trans hone
  rcases P.eq_empty_or_nonempty with hP0 | hPne
  · simpa [hP0] using hone.trans' zero_le_one
  have hN : (0 : ℝ) < P.card := by exact_mod_cast hPne.card_pos
  set L := Real.log P.card with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hPne.card_pos)
  -- The subsample size `k = ⌊2 L / ε⌋ + 1`.
  set k := ⌊2 * L / ε⌋₊ + 1 with hk
  have hkcast : (k : ℝ) = ⌊2 * L / ε⌋₊ + 1 := by rw [hk]; push_cast; rfl
  have hk1 : 2 * L / ε < k := by rw [hkcast]; exact Nat.lt_floor_add_one _
  have hk2 : (k : ℝ) ≤ 2 * L / ε + 1 := by
    rw [hkcast]; linarith [Nat.floor_le (div_nonneg (mul_nonneg zero_le_two hL0) hε.le)]
  have hlog : 2 * L < ε * k := by
    have := (div_lt_iff₀ hε).1 hk1
    linarith
  -- Sauer's lemma with `T = 4 / ε`.
  set T := 4 / ε with hT
  have hT1 : 1 ≤ T := by rw [hT, le_div_iff₀ hε]; linarith
  have hgrowth : (P.card : ℝ) ≤ growthFunction C k := by
    exact_mod_cast card_le_growthFunction_of_two_mul_log_card_lt C hm hPC hP hlog
  have hsauer : (P.card : ℝ) ≤ Real.exp (k / T) * T ^ d :=
    hgrowth.trans (growthFunction_le_exp_mul_pow hC k hT1)
  have hkT : (k : ℝ) / T ≤ L / 2 + ε / 4 := by
    rw [hT, div_div_eq_mul_div, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have := mul_le_mul_of_nonneg_left hk2 hε.le
    rw [mul_add, mul_div_cancel₀ _ hε.ne', mul_one] at this
    nlinarith
  -- Squaring removes the square root of `|P| = exp L`.
  have hsq : (P.card : ℝ) ^ 2 ≤ P.card * (Real.exp (ε / 2) * T ^ (2 * d)) := by
    have h1 : (P.card : ℝ) ≤ Real.exp (L / 2 + ε / 4) * T ^ d :=
      hsauer.trans (by gcongr)
    calc (P.card : ℝ) ^ 2 ≤ (Real.exp (L / 2 + ε / 4) * T ^ d) ^ 2 := by gcongr
      _ = Real.exp (L / 2 + ε / 4) ^ 2 * T ^ (2 * d) := by rw [mul_pow, ← pow_mul, mul_comm d]
      _ = Real.exp L * (Real.exp (ε / 2) * T ^ (2 * d)) := by
          rw [← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
          push_cast
          ring_nf
      _ = P.card * (Real.exp (ε / 2) * T ^ (2 * d)) := by rw [hL, Real.exp_log hN]
  have hle : (P.card : ℝ) ≤ Real.exp (ε / 2) * T ^ (2 * d) := by
    have := hsq
    rw [sq] at this
    exact le_of_mul_le_mul_left this hN
  -- `exp (ε / 2) < 2`, since `exp ε ≤ e < 4`.
  have hexp2 : Real.exp (ε / 2) < 2 := by
    have hsq2 : Real.exp (ε / 2) ^ 2 < 2 ^ 2 := by
      rw [← Real.exp_nat_mul]
      calc Real.exp ((2 : ℕ) * (ε / 2)) = Real.exp ε := by push_cast; ring_nf
        _ ≤ Real.exp 1 := Real.exp_le_exp.2 hε1
        _ < 2 ^ 2 := by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    exact lt_of_pow_lt_pow_left₀ 2 zero_le_two hsq2
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- With `d = 0`, `|P| < 2`.
    have h2 : (P.card : ℝ) < 2 := by
      have : (P.card : ℝ) ≤ Real.exp (ε / 2) := by simpa using hle
      linarith
    have : P.card ≤ 1 := by
      have : P.card < 2 := by exact_mod_cast h2
      omega
    simpa using (by exact_mod_cast this : (P.card : ℝ) ≤ 1)
  · calc (P.card : ℝ) ≤ Real.exp (ε / 2) * T ^ (2 * d) := hle
      _ ≤ 2 ^ (2 * d) * T ^ (2 * d) := by
          gcongr
          calc Real.exp (ε / 2) ≤ 2 := hexp2.le
            _ = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ (2 * d) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = (8 / ε) ^ (2 * d) := by
          rw [← mul_pow, hT]
          congr 1
          ring

end Cslib.MachineLearning.PACLearning

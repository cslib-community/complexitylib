/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.FeistelPerm
public import CslibFrontier.Probability.KWiseIndependent.Concentration
import CslibFrontier.Foundations.Data.Nat.Power
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for assumption-free Feistel permutation families (`Lemmas 5.1–5.2`, `Corollaries B.5–B.6`)

Non-vacuity and concrete behavioral tests for `CslibFrontier.DataStructure.Dictionary.FeistelPerm`
and `CslibFrontier.Probability.KWiseIndependent.Concentration`:
1. Concrete checks of `mixedDomainEquiv`, `feistelMixedEquiv`, `bitDomainEquiv`, `feistelBitEquiv`,
   and agreement with `FeistelQuotient.feistelBucket` / `feistelReconstruct` on a non-power-of-two
   right domain (`s = 3`, `T = 5`, `Fin 40 ≃ Fin 8 × Fin 5`).
2. Bucket-load conservation, right-coordinate (`Prod.snd`) uniqueness within each bucket, an
   explicit contrast between same-right-coordinate non-collision and distinct-right-coordinate
   collision, and a direct check of `dens_abs_sum_sub_expect_le`.
3. Proper-subset (`S ⊂ univ`) non-vacuity of `dens_childRouter_bucketLoad_outside_le` (closed
   parameters `c = 1, q = 4, b = 46, s = 1` on `{0} ×ˢ univ`, where a constant round function sends
   all `2 ^ 46` keys to bucket `0` and `0` to bucket `1`),
   `dens_childRouter_bucketLoad_outside_le_of_threshold` (sparse `{0} ×ˢ univ` on a
   non-power-of-two `T`), `childRouterSeedBits_pow_le`, and
   `dens_childRouterBit_bucketLoad_outside_le` (`s = 1`).
4. Concrete Section 5.4 instantiation of `idCompressorSeedBits_le`, `idCompressorPerm` lossless
   recovery, `dens_not_injOn_idCompressorHead_le_two_div_sq` (`n_next = 64`, `n_bar = 80`,
   `I_next = 24`, `T = 1000`), and `dens_not_injOn_idCompressorBit_le`.
-/

public section

namespace ComplexityTests.FeistelPerm

open Cslib.DataStructure.Dictionary Cslib.DataStructure.Dictionary.FeistelPerm
open Cslib.Probability Finset
open scoped BigOperators

/-! ## 1. Mixed-domain involution and `FeistelQuotient` bridge on `Fin (2 ^ 3 * 5)` -/

def sampleRound35 (z : Fin 5) : Fin (2 ^ 3) :=
  ⟨(3 * z.val + 2) % 8, Nat.mod_lt _ (by decide)⟩

theorem mixedDomain_roundtrip_and_bridge :
    mixedDomainEquiv 3 5 ⟨29, by decide⟩ = (⟨5, by decide⟩, ⟨3, by decide⟩) ∧
    feistelMixedEquiv sampleRound35 ⟨29, by decide⟩ = ⟨30, by decide⟩ ∧
    feistelMixedEquiv sampleRound35 ⟨30, by decide⟩ = ⟨29, by decide⟩ ∧
    (∀ u : Fin (2 ^ 3 * 5),
      (feistelHead sampleRound35 (mixedDomainEquiv 3 5 u)).val =
        FeistelQuotient.feistelBucket 3 (fun q => 3 * q + 2) u.val) ∧
    (∀ (b : Fin (2 ^ 3)) (q : Fin 5),
      ((mixedDomainEquiv 3 5).symm (recoverLeft sampleRound35 b q, q)).val =
        FeistelQuotient.feistelReconstruct 3 (fun r => 3 * r + 2) b.val q.val) :=
  ⟨by decide,
   by decide,
   by decide,
   fun u => val_feistelHead_mixedDomainEquiv_eq_feistelBucket (fun q => 3 * q + 2) u,
   fun b q => val_mixedDomainEquiv_symm_recoverLeft_eq_feistelReconstruct (fun r => 3 * r + 2) b q⟩

theorem bitDomain_concrete_eval :
    let f (z : Fin (2 ^ (6 - 3))) : Fin (2 ^ 3) := ⟨(5 * z.val + 1) % 8, Nat.mod_lt _ (by decide)⟩
    feistelBitEquiv (s := 3) (L := 6) (by decide) f ⟨45, by decide⟩ = ⟨47, by decide⟩ ∧
    feistelBitEquiv (s := 3) (L := 6) (by decide) f ⟨47, by decide⟩ = ⟨45, by decide⟩ :=
  ⟨by decide, by decide⟩

/-! ## 2. Right-part uniqueness per bucket, collision contrast, and `k`-wise concentration -/

def sampleList35 : List (Fin (2 ^ 3) × Fin 5) :=
  [(⟨1, by decide⟩, ⟨0, by decide⟩),
   (⟨3, by decide⟩, ⟨0, by decide⟩),
   (⟨3, by decide⟩, ⟨1, by decide⟩),
   (⟨6, by decide⟩, ⟨2, by decide⟩),
   (⟨0, by decide⟩, ⟨4, by decide⟩),
   (⟨7, by decide⟩, ⟨4, by decide⟩)]

def sampleSet35 : Finset (Fin (2 ^ 3) × Fin 5) :=
  sampleList35.toFinset

theorem bucketLoad_partition_and_collision_contrast :
    (∑ b : Fin (2 ^ 3), bucketLoad sampleRound35 sampleSet35 b) = 6 ∧
    (∀ b : Fin (2 ^ 3),
      #(({x ∈ sampleSet35 | feistelHead sampleRound35 x = b}).image Prod.snd) =
        bucketLoad sampleRound35 sampleSet35 b) ∧
    (∀ f : Fin 5 → Fin (2 ^ 3),
      feistelHead (s := 3) f (⟨1, by decide⟩, ⟨0, by decide⟩) ≠
        feistelHead (s := 3) f (⟨3, by decide⟩, ⟨0, by decide⟩)) ∧
    feistelHead (s := 3)
        (fun z : Fin 5 => if z.val = 0 then ⟨2, by decide⟩ else ⟨0, by decide⟩)
        (⟨1, by decide⟩, ⟨0, by decide⟩) =
      feistelHead (s := 3)
        (fun z : Fin 5 => if z.val = 0 then ⟨2, by decide⟩ else ⟨0, by decide⟩)
        (⟨3, by decide⟩, ⟨1, by decide⟩) :=
  ⟨(sum_bucketLoad_eq_card sampleRound35 sampleSet35).trans
     (List.toFinset_card_of_nodup (by decide)),
   fun b => card_image_snd_filter_feistelHead_eq sampleRound35 sampleSet35 b,
   fun f => feistelHead_ne_of_snd_eq_of_ne rfl (by decide),
   by decide⟩

/-- Direct instantiation of `Cslib.Probability.dens_abs_sum_sub_expect_le_two_pow` for `4`-wise
(`m = 2`) independent indicator variables over `Fin 32 → Fin 2` (`μ = 16`, `a = 16`,
`6 * 2 * 16 = 192 ≤ 16 ^ 2`). -/
theorem kWise_concentration_two_pow_instance :
    let R : Finset (Fin 32) := univ
    let g (_ : Fin 32) (y : Fin 2) : ℝ := if y.val = 0 then 1 else 0
    (dens {f : Fin 32 → Fin 2 |
      (16 : ℝ) ≤ |∑ z ∈ R, (g z (f z) - 𝔼 y, g z y)|} : ℝ) ≤ 1 / 2 := by
  intro R g
  have hg : ∀ z ∈ R, ∀ y : Fin 2, g z y ∈ Set.Icc 0 1 := by
    intro _ _ y
    dsimp only [g]
    split_ifs <;> constructor <;> norm_num
  have hmean : ∑ z ∈ R, (𝔼 y, g z y) ≤ (16 : ℝ) := by
    have hexp (z : Fin 32) : (𝔼 y, g z y) = (1 : ℝ) / 2 := by
      rw [Fintype.expect_eq_sum_div_card]
      simp only [g, Fin.sum_univ_two, Fin.val_zero, ↓reduceIte, Fin.val_one, one_ne_zero,
        Fintype.card_fin]
      norm_num
    simp only [hexp, sum_const, R, card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  exact (dens_abs_sum_sub_expect_le_two_pow (m := 2) (a := 16) (by decide)
    (isKWiseIndependentHash_id 4) R g hg hmean (by norm_num) le_rfl (by norm_num)).trans
    (by norm_num)

/-! ## 3. Proper-subset non-vacuity of `Corollary B.5` and `Lemma 5.1` (`S ⊂ univ`) -/

/-- Closed-parameter proper-subset instantiation of `dens_childRouter_bucketLoad_outside_le` at
`c = 1`, `q = 4`, `b = 46`, `s = 1`, `T = 2 ^ 46` on `S = {0} ×ˢ univ ⊂ Fin 2 × Fin (2 ^ 46)`
(`#S = 2 ^ 46 < 2 ^ 47`). A constant-zero round function routes all `2 ^ 46` keys to bucket `0` and
`0` keys to bucket `1`, whereas random `ChildRouterSeed 1 4 46 1` balances both buckets within
`± (1/5)(2 ^ 45) ^ (2/3)` except with seed density at most `1 / (4 * (#S) ^ 2)`. -/
theorem childRouter_properSubset_closed_params_nonvacuous :
    let S : Finset (Fin (2 ^ 1) × Fin (2 ^ 46)) :=
      ({⟨0, by decide⟩} : Finset (Fin (2 ^ 1))) ×ˢ univ
    S.Nonempty ∧ S ⊂ univ ∧
    bucketLoad (fun _ : Fin (2 ^ 46) => (⟨0, by decide⟩ : Fin (2 ^ 1))) S ⟨0, by decide⟩ =
      2 ^ 46 ∧
    bucketLoad (fun _ : Fin (2 ^ 46) => (⟨0, by decide⟩ : Fin (2 ^ 1))) S ⟨1, by decide⟩ = 0 ∧
    (dens {θ : ChildRouterSeed 1 4 46 1 |
      ¬ ∀ bucket : Fin (2 ^ 1),
        (#S : ℝ) / (2 ^ 1 : ℝ) - ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ 1 : ℝ)) ^ ((2 : ℝ) / 3) ≤
            (bucketLoad (childRouterRound 1 4 46 1 (2 ^ 46) θ) S bucket : ℝ) ∧
          (bucketLoad (childRouterRound 1 4 46 1 (2 ^ 46) θ) S bucket : ℝ) ≤
            (#S : ℝ) / (2 ^ 1 : ℝ) + ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ 1 : ℝ)) ^ ((2 : ℝ) / 3)} :
      ℝ) ≤ 1 / (4 * (#S : ℝ) ^ 2) := by
  intro S
  have hne : S.Nonempty := ⟨(⟨0, by decide⟩, ⟨0, by decide⟩), by simp [S]⟩
  have hssub : S ⊂ univ := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨subset_univ S, fun heq => ?_⟩
    have hmem : ((⟨1, by decide⟩ : Fin (2 ^ 1)), (⟨0, by decide⟩ : Fin (2 ^ 46))) ∈ S :=
      heq.symm ▸ mem_univ _
    simp [S] at hmem
  have hb0 :
      bucketLoad (fun _ : Fin (2 ^ 46) => (⟨0, by decide⟩ : Fin (2 ^ 1))) S ⟨0, by decide⟩ =
        2 ^ 46 := by
    rw [bucketLoad, filter_true_of_mem]
    · simp [S]
    · intro x hx
      rcases mem_product.mp hx with ⟨hx1, _⟩
      simp only [feistelHead, mem_singleton.mp hx1]
      decide
  have hb1 :
      bucketLoad (fun _ : Fin (2 ^ 46) => (⟨0, by decide⟩ : Fin (2 ^ 1))) S ⟨1, by decide⟩ =
        0 := by
    rw [bucketLoad, card_eq_zero, filter_eq_empty_iff]
    intro x hx
    rcases mem_product.mp hx with ⟨hx1, _⟩
    simp only [feistelHead, mem_singleton.mp hx1]
    decide
  set n := #S
  set m := childRouterHalfInd n
  have hcard : n = 2 ^ 46 := by
    simp [n, S]
  have hclog : Nat.clog 2 (max n 2) ≤ 46 := by
    rw [hcard]
    exact Nat.clog_le_of_le_pow (by decide)
  have hm_le : m ≤ 142 := by
    have hm_eq := childRouterHalfInd_eq n
    omega
  have hcode : 4 * n * doubleTabCodeBound 1 (2 * 4 * 1) 4 (2 * m) ≤ 2 ^ ((4 - 1) * 46) := by
    calc 4 * n * doubleTabCodeBound 1 (2 * 4 * 1) 4 (2 * m)
        ≤ 4 * 2 ^ 46 * doubleTabCodeBound 1 8 4 (2 * 142) := by
          rw [hcard]
          refine Nat.mul_le_mul_left _ ?_
          dsimp only [doubleTabCodeBound]
          exact Nat.mul_le_mul_left 1
            (Nat.pow_le_pow_left
              (Nat.mul_le_mul_right 8 (Nat.pow_le_pow_left (by omega) 2)) 4)
      _ ≤ 2 ^ ((4 - 1) * 46) := by decide
  have hconc : 2 ^ 1 * (150 * m) ^ 3 ≤ n := by
    calc 2 ^ 1 * (150 * m) ^ 3
        ≤ 2 * (150 * 142) ^ 3 :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega) 3)
      _ ≤ 2 ^ 46 := by decide
      _ = n := hcard.symm
  exact ⟨hne, hssub, hb0, hb1,
    dens_childRouter_bucketLoad_outside_le (by decide) (by decide) (by decide) S hcode hconc⟩

/-- Proper-subset non-vacuous joint instantiation of
`dens_childRouter_bucketLoad_outside_le_of_threshold` and `childRouterSeedBits_pow_le` for every
`ε_inv : ℕ` and `s ≥ childRouterMinS` on `S = {0} ×ˢ univ ⊂ Fin (2 ^ s) × Fin T` for a
non-power-of-two `T`. -/
theorem childRouter_threshold_properSubset_nonvacuous (ε_inv s : ℕ) (hs : childRouterMinS ≤ s) :
    let T := max (childRouterThreshold ε_inv 2) (2 ^ s * s ^ 4) + 1
    let S : Finset (Fin (2 ^ s) × Fin T) :=
      ({⟨0, Nat.two_pow_pos s⟩} : Finset (Fin (2 ^ s))) ×ˢ univ
    let c := childRouterChars ε_inv
    let q := childRouterRep ε_inv 2
    let b := childRouterCharBits c T
    S.Nonempty ∧ S ⊂ univ ∧
    (childRouterSeedBits c q b s) ^ max ε_inv 1 ≤ childRouterSpaceConst ε_inv 2 * (2 ^ s * T) ∧
    (dens {θ : ChildRouterSeed c q b s |
      ¬ ∀ bucket : Fin (2 ^ s),
        (#S : ℝ) / (2 ^ s : ℝ) - ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ s : ℝ)) ^ ((2 : ℝ) / 3) ≤
            (bucketLoad (childRouterRound c q b s T θ) S bucket : ℝ) ∧
          (bucketLoad (childRouterRound c q b s T θ) S bucket : ℝ) ≤
            (#S : ℝ) / (2 ^ s : ℝ) + ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ s : ℝ)) ^ ((2 : ℝ) / 3)} :
      ℝ) ≤ 1 / (4 * (#S : ℝ) ^ 2) := by
  intro T S c q b
  have hs1 : 1 ≤ s := le_trans (by rw [childRouterMinS_eq]; decide : 1 ≤ childRouterMinS) hs
  have h2s : 2 ≤ 2 ^ s :=
    calc 2 = 2 ^ 1 := by decide
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hs1
  have hT1 : 1 ≤ T := Nat.succ_pos _
  have hne : S.Nonempty := ⟨(⟨0, Nat.two_pow_pos s⟩, ⟨0, hT1⟩), by simp [S]⟩
  have hssub : S ⊂ univ := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨subset_univ S, fun heq => ?_⟩
    have hmem : ((⟨1, h2s⟩ : Fin (2 ^ s)), (⟨0, hT1⟩ : Fin T)) ∈ S :=
      heq.symm ▸ mem_univ _
    have h1 := mem_singleton.mp (mem_product.mp hmem).1
    exact Nat.one_ne_zero (congrArg Fin.val h1)
  have hprod_le_T : 2 ^ s * s ^ 4 ≤ T := (le_max_right _ _).trans (Nat.le_succ _)
  have h2s_le_T : 2 ^ s ≤ T := by
    have hs4_pos : 1 ≤ s ^ 4 := Nat.one_le_pow 4 s hs1
    exact (Nat.le_mul_of_pos_right (2 ^ s) hs4_pos).trans hprod_le_T
  have hth_le_T : childRouterThreshold ε_inv 2 ≤ T := (le_max_left _ _).trans (Nat.le_succ _)
  have hcard : #S = T := by
    simp [S]
  have hgap : 2 ^ s * T ≤ T ^ max 2 1 := by
    change 2 ^ s * T ≤ T ^ 2
    rw [sq]
    exact Nat.mul_le_mul_right T h2s_le_T
  have hthresh : childRouterThreshold ε_inv 2 ≤ #S := hcard.symm ▸ hth_le_T
  have hconc : 2 ^ s * (150 * childRouterHalfInd #S) ^ 3 ≤ #S :=
    childRouter_conc_of_two_pow_mul_pow_four_le hs (hcard.symm ▸ hprod_le_T)
  exact ⟨hne, hssub, childRouterSeedBits_pow_le ε_inv 2 s hT1,
    dens_childRouter_bucketLoad_outside_le_of_threshold hgap S hthresh hconc⟩

/-- Proper-subset instantiation of `dens_childRouterBit_bucketLoad_outside_le` at
`s = 1` (binary child split, where `s < childRouterMinS`) on the lower half `{u | u.val < 2 ^ M}`
of `Fin (2 ^ (M + 1))`. -/
theorem childRouterBit_binary_split_nonvacuous (ε_inv : ℕ) :
    ∃ (L : ℕ) (hsL : 1 ≤ L) (S : Finset (Fin (2 ^ L))),
      let c := childRouterChars ε_inv
      let q := childRouterRep ε_inv 2
      let b := childRouterCharBits c (2 ^ (L - 1))
      S.Nonempty ∧ S ⊂ univ ∧
      (dens {θ : ChildRouterSeed c q b 1 |
        ¬ ∀ bucket : Fin (2 ^ 1),
          (#S : ℝ) / (2 ^ 1 : ℝ) - ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ 1 : ℝ)) ^ ((2 : ℝ) / 3) ≤
              (bucketLoad (childRouterRound c q b 1 (2 ^ (L - 1)) θ)
                (S.map (bitDomainEquiv hsL).toEmbedding) bucket : ℝ) ∧
            (bucketLoad (childRouterRound c q b 1 (2 ^ (L - 1)) θ)
                (S.map (bitDomainEquiv hsL).toEmbedding) bucket : ℝ) ≤
              (#S : ℝ) / (2 ^ 1 : ℝ) + ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ 1 : ℝ)) ^ ((2 : ℝ) / 3)} :
        ℝ) ≤ 1 / (4 * (#S : ℝ) ^ 2) := by
  set E := Nat.clog 2 (max (childRouterThreshold ε_inv 2) 2)
  let M := max E 300
  let L := M + 1
  have hsL : 1 ≤ L := Nat.le_add_left 1 M
  let emb : Fin (2 ^ M) ↪ Fin (2 ^ L) :=
    ⟨fun u => ⟨u.val, lt_of_lt_of_le u.isLt (Nat.pow_le_pow_right (by decide) (Nat.le_succ M))⟩,
     fun _ _ h => by simpa only [Fin.ext_iff] using h⟩
  let S : Finset (Fin (2 ^ L)) := (univ : Finset (Fin (2 ^ M))).map emb
  refine ⟨L, hsL, S, ?_⟩
  have hM300 : 300 ≤ M := le_max_right E 300
  have hcard : #S = 2 ^ M := by simp [S]
  have hne : S.Nonempty := by
    rw [← card_pos, hcard]
    exact Nat.two_pow_pos M
  have hssub : S ⊂ univ := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨subset_univ S, fun heq => ?_⟩
    have hlt : #S < #(univ : Finset (Fin (2 ^ L))) := by
      rw [hcard, card_univ, Fintype.card_fin]
      exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self M)
    exact (heq ▸ hlt).false
  have hgap : L ≤ max 2 1 * (L - 1) := by
    change M + 1 ≤ 2 * (M + 1 - 1)
    omega
  have hthresh : childRouterThreshold ε_inv 2 ≤ #S := by
    rw [hcard]
    calc childRouterThreshold ε_inv 2
        ≤ max (childRouterThreshold ε_inv 2) 2 := le_max_left _ _
      _ ≤ 2 ^ E := Nat.le_pow_clog (by decide) _
      _ ≤ 2 ^ M := Nat.pow_le_pow_right (by decide) (le_max_left E 300)
  have hconc : 2 ^ 1 * (150 * childRouterHalfInd #S) ^ 3 ≤ #S := by
    rw [hcard]
    have hmax : max (2 ^ M) 2 = 2 ^ M :=
      max_eq_left (calc 2 = 2 ^ 1 := by decide
        _ ≤ 2 ^ M := Nat.pow_le_pow_right (by decide) (by omega))
    have hclog : Nat.clog 2 (max (2 ^ M) 2) ≤ M := by
      rw [hmax]
      exact Nat.clog_le_of_le_pow le_rfl
    have h150 : 150 * childRouterHalfInd (2 ^ M) ≤ 2 ^ 9 * (M - 28) := by
      rw [childRouterHalfInd_eq]
      omega
    have hpow3 : (M - 28) ^ 3 ≤ 2 ^ (M - 28) :=
      Nat.pow_le_two_pow (by decide) (by omega)
    calc 2 ^ 1 * (150 * childRouterHalfInd (2 ^ M)) ^ 3
        ≤ 2 * (2 ^ 9 * (M - 28)) ^ 3 :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left h150 3)
      _ = 2 ^ 28 * (M - 28) ^ 3 := by ring
      _ ≤ 2 ^ 28 * 2 ^ (M - 28) := Nat.mul_le_mul_left _ hpow3
      _ = 2 ^ M := by
          rw [← Nat.pow_add]
          congr 1
          omega
  exact ⟨hne, hssub,
    dens_childRouterBit_bucketLoad_outside_le hsL hgap S hthresh hconc⟩

/-! ## 4. Non-vacuity of `Corollary B.6` and `Lemma 5.2` (`ℋ_ℓ^id` at `n_next = 64`) -/

theorem idCompressor_section5_4_instance
    (S : Finset (Fin (2 ^ 24) × Fin 1000)) (hS : #S ≤ 80) :
    idCompressorSeedBits 24 1000 ≤ 144 ∧
    (∀ (θ : IdCompressorSeed 24 1000) (x : Fin (2 ^ 24) × Fin 1000),
      idCompressorPerm 24 1000 θ (idCompressorPerm 24 1000 θ x) = x) ∧
    (dens {θ : IdCompressorSeed 24 1000 |
      ¬ Set.InjOn (idCompressorHead 24 1000 θ) (S : Set (Fin (2 ^ 24) × Fin 1000))} : ℝ) ≤
      1 / 2048 := by
  have hbits : idCompressorSeedBits 24 1000 ≤ 144 := by
    have hclog : Nat.clog 2 (max 1000 2) ≤ 10 := Nat.clog_le_of_le_pow (by decide)
    have hle := idCompressorSeedBits_le 24 1000
    omega
  have hd := dens_not_injOn_idCompressorHead_le_two_div_sq
    (n_bar := 80) (n_next := 64) S hS (by decide) (by decide)
  exact ⟨hbits, idCompressorPerm_involutive 24 1000, by norm_num at hd; exact hd⟩

theorem idCompressorBit_fin2_pow_40 (S : Finset (Fin (2 ^ 40))) :
    (dens {θ : IdCompressorSeed 24 (2 ^ (40 - 24)) |
      ¬ Set.InjOn (fun u => idCompressorHead 24 (2 ^ (40 - 24)) θ (bitDomainEquiv (by decide) u))
        (S : Set (Fin (2 ^ 40)))} : ℝ) ≤
      (#S : ℝ) ^ 2 / (2 * (2 ^ 24 : ℝ)) :=
  dens_not_injOn_idCompressorBit_le (by decide) S

/-- Public bridge connecting `childRouterPerm` and `idCompressorHead` / `idCompressorPerm` to the
underlying `doubleTabHash` and `trinomialPolyHash` round functions from outside `FeistelPerm`. -/
theorem round_hash_bridge (c q b s T : ℕ) (θ_ch : ChildRouterSeed c q b s)
    (θ_id : IdCompressorSeed s T) (x : Fin (2 ^ s) × Fin T) :
    childRouterPerm c q b s T θ_ch x =
      (x.1 ^^^ doubleTabHash c (2 * q * c) b T s θ_ch.1 θ_ch.2 x.2, x.2) ∧
    idCompressorHead s T θ_id x =
      x.1 ^^^ trinomialPolyHash (trinomialStep T s) 2 T s θ_id x.2 ∧
    idCompressorPerm s T θ_id x =
      (x.1 ^^^ trinomialPolyHash (trinomialStep T s) 2 T s θ_id x.2, x.2) := by
  simp only [childRouterPerm_apply, feistelPair, feistelHead, childRouterRound_apply,
    idCompressorHead_apply, idCompressorPerm_apply, idCompressorRound_apply, and_self]

end ComplexityTests.FeistelPerm

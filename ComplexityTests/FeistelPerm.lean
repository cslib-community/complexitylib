/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.Dictionary.FeistelPerm
import Complexity.Foundations.Data.Nat.Power
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for assumption-free Feistel permutation families (`Lemmas 5.1–5.2`, `Corollaries B.5–B.6`)

Non-vacuity and concrete behavioral tests for `Complexity.DataStructure.Dictionary.FeistelPerm`:
1. Concrete checks of `mixedDomainEquiv`, `feistelMixedEquiv`, `bitDomainEquiv`, `feistelBitEquiv`,
   and agreement with `FeistelQuotient.feistelBucket` / `feistelReconstruct` on a non-power-of-two
   right domain (`s = 3`, `T = 5`, `Fin 40 ≃ Fin 8 × Fin 5`).
2. Bucket-load conservation, right-coordinate (`Prod.snd`) uniqueness within each bucket, and an
   explicit contrast between same-right-coordinate non-collision and distinct-right-coordinate
   collision.
3. Non-vacuous instantiations of `dens_childRouter_bucketLoad_outside_le` (closed parameters
   `c = 1, q = 4, b = 45, s = 1`), `corollaryB5_concentration`, `childRouterSeedBits_pow_le`, and
   `lemma5_1_concentration` (including binary child split `s = 1`).
4. Concrete Section 5.4 instantiation of `idCompressorSeedBits_le`, `idCompressorPerm` lossless
   recovery, `dens_not_injOn_idCompressorHead_le_two_div_sq` (`n_next = 64`, `n_bar = 80`,
   `I_next = 24`, `T = 1000`), and `lemma5_2_collision_le`.
-/

public section

namespace ComplexityTests.FeistelPerm

open Cslib.DataStructure.Dictionary Cslib.DataStructure.Dictionary.FeistelPerm
open Cslib.Probability Finset

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

/-! ## 2. Right-part uniqueness per bucket vs distinct-right-part collision -/

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

/-! ## 3. Non-vacuity of `Corollary B.5` and `Lemma 5.1` (`s ≥ childRouterMinS` and `s = 1`) -/

/-- Closed-parameter non-vacuous instantiation of `dens_childRouter_bucketLoad_outside_le` at
`c = 1`, `q = 4`, `b = 45`, `s = 1`, `T = 2 ^ 45` on the full domain `Fin 2 × Fin (2 ^ 45)`
(`#S = 2 ^ 46`). -/
theorem childRouter_closed_params_nonvacuous :
    let S : Finset (Fin (2 ^ 1) × Fin (2 ^ 45)) := univ
    (dens {θ : ChildRouterSeed 1 4 45 1 |
      ¬ ∀ bucket : Fin (2 ^ 1),
        (#S : ℝ) / (2 ^ 1 : ℝ) - ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ 1 : ℝ)) ^ ((2 : ℝ) / 3) ≤
            (bucketLoad (childRouterRound 1 4 45 1 (2 ^ 45) θ) S bucket : ℝ) ∧
          (bucketLoad (childRouterRound 1 4 45 1 (2 ^ 45) θ) S bucket : ℝ) ≤
            (#S : ℝ) / (2 ^ 1 : ℝ) + ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ 1 : ℝ)) ^ ((2 : ℝ) / 3)} :
      ℝ) ≤ 1 / (4 * (#S : ℝ) ^ 2) := by
  intro S
  set n := #S
  set m := childRouterHalfInd n
  have hcard : n = 2 ^ 46 := by
    simp only [n, S, card_univ, Fintype.card_prod, Fintype.card_fin]
    decide
  have hclog : Nat.clog 2 (max n 2) ≤ 46 := by
    rw [hcard]
    exact Nat.clog_le_of_le_pow (by decide)
  have hm_le : m ≤ 142 := by
    dsimp only [m, childRouterHalfInd]
    omega
  have hcode : 4 * n * doubleTabCodeBound 1 (2 * 4 * 1) 4 (2 * m) ≤ 2 ^ ((4 - 1) * 45) := by
    calc 4 * n * doubleTabCodeBound 1 (2 * 4 * 1) 4 (2 * m)
        ≤ 4 * 2 ^ 46 * doubleTabCodeBound 1 8 4 (2 * 142) := by
          rw [hcard]
          refine Nat.mul_le_mul_left _ ?_
          dsimp only [doubleTabCodeBound]
          exact Nat.mul_le_mul_left 1
            (Nat.pow_le_pow_left
              (Nat.mul_le_mul_right 8 (Nat.pow_le_pow_left (by omega) 2)) 4)
      _ ≤ 2 ^ ((4 - 1) * 45) := by decide
  have hconc : 2 ^ 1 * (150 * m) ^ 3 ≤ n := by
    calc 2 ^ 1 * (150 * m) ^ 3
        ≤ 2 * (150 * 142) ^ 3 :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega) 3)
      _ ≤ 2 ^ 46 := by decide
      _ = n := hcard.symm
  exact dens_childRouter_bucketLoad_outside_le (by decide) (by decide) (by decide) S hcode hconc

/-- Non-vacuous joint instantiation of `corollaryB5_concentration` and `childRouterSeedBits_pow_le`
for every `ε_inv : ℕ` and `s ≥ childRouterMinS` on a non-power-of-two `T`. -/
theorem corollaryB5_nonvacuous (ε_inv s : ℕ) (hs : childRouterMinS ≤ s) :
    let T := max (childRouterThreshold ε_inv 2) (max (2 ^ s) (s ^ 4)) + 1
    let S : Finset (Fin (2 ^ s) × Fin T) := univ
    let c := childRouterChars ε_inv
    let q := childRouterRep ε_inv 2
    let b := childRouterCharBits c T
    (childRouterSeedBits c q b s) ^ max ε_inv 1 ≤ childRouterSpaceConst ε_inv 2 * (2 ^ s * T) ∧
    (dens {θ : ChildRouterSeed c q b s |
      ¬ ∀ bucket : Fin (2 ^ s),
        (#S : ℝ) / (2 ^ s : ℝ) - ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ s : ℝ)) ^ ((2 : ℝ) / 3) ≤
            (bucketLoad (childRouterRound c q b s T θ) S bucket : ℝ) ∧
          (bucketLoad (childRouterRound c q b s T θ) S bucket : ℝ) ≤
            (#S : ℝ) / (2 ^ s : ℝ) + ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ s : ℝ)) ^ ((2 : ℝ) / 3)} :
      ℝ) ≤ 1 / (4 * (#S : ℝ) ^ 2) := by
  intro T S c q b
  have hT1 : 1 ≤ T := Nat.succ_pos _
  have h2s_le_T : 2 ^ s ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans (Nat.le_succ _))
  have hs4_le_T : s ^ 4 ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans (Nat.le_succ _))
  have hth_le_T : childRouterThreshold ε_inv 2 ≤ T := (le_max_left _ _).trans (Nat.le_succ _)
  have hcard : #S = 2 ^ s * T := by
    simp only [S, card_univ, Fintype.card_prod, Fintype.card_fin]
  have hgap : 2 ^ s * T ≤ T ^ max 2 1 := by
    change 2 ^ s * T ≤ T ^ 2
    rw [sq]
    exact Nat.mul_le_mul_right T h2s_le_T
  have hthresh : childRouterThreshold ε_inv 2 ≤ #S := by
    rw [hcard]
    exact hth_le_T.trans (Nat.le_mul_of_pos_left T (Nat.two_pow_pos s))
  have hconc : 2 ^ s * (150 * childRouterHalfInd #S) ^ 3 ≤ #S := by
    refine childRouter_conc_of_two_pow_mul_pow_four_le hs ?_
    rw [hcard]
    exact Nat.mul_le_mul_left (2 ^ s) hs4_le_T
  exact ⟨childRouterSeedBits_pow_le ε_inv 2 s hT1,
    corollaryB5_concentration hgap S hthresh hconc⟩

/-- Non-vacuous instantiation of `lemma5_1_concentration` at `s = 1` (binary child split, where
`s < childRouterMinS`), confirming our quantitative concentration premise holds down to `s = 1`. -/
theorem lemma5_1_binary_split_nonvacuous (ε_inv : ℕ) :
    ∃ (L : ℕ) (hsL : 1 ≤ L),
      let S : Finset (Fin (2 ^ L)) := univ
      let c := childRouterChars ε_inv
      let q := childRouterRep ε_inv 2
      let b := childRouterCharBits c (2 ^ (L - 1))
      #S = 2 ^ L ∧
      (dens {θ : ChildRouterSeed c q b 1 |
        ¬ ∀ bucket : Fin (2 ^ 1),
          (#S : ℝ) / (2 ^ 1 : ℝ) - ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ 1 : ℝ)) ^ ((2 : ℝ) / 3) ≤
              (bucketLoad (childRouterRound c q b 1 (2 ^ (L - 1)) θ)
                (S.map (bitDomainEquiv hsL).toEmbedding) bucket : ℝ) ∧
            (bucketLoad (childRouterRound c q b 1 (2 ^ (L - 1)) θ)
                (S.map (bitDomainEquiv hsL).toEmbedding) bucket : ℝ) ≤
              (#S : ℝ) / (2 ^ 1 : ℝ) + ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ 1 : ℝ)) ^ ((2 : ℝ) / 3)} :
        ℝ) ≤ 1 / (4 * (#S : ℝ) ^ 2) := by
  set E := childRouterChars ε_inv * max 2 1 * childRouterMinB ε_inv 2
  let M := max E 300
  let L := M + 1
  have hsL : 1 ≤ L := Nat.le_add_left 1 M
  refine ⟨L, hsL, ?_⟩
  let S : Finset (Fin (2 ^ L)) := univ
  have hM300 : 300 ≤ M := le_max_right E 300
  have hLM : L = M + 1 := rfl
  have hcard : #S = 2 ^ L := by simp only [S, card_univ, Fintype.card_fin]
  have hgap : L ≤ max 2 1 * (L - 1) := by
    change L ≤ 2 * (L - 1)
    omega
  have hthresh : childRouterThreshold ε_inv 2 ≤ #S := by
    rw [hcard]
    change 2 ^ E ≤ 2 ^ L
    exact Nat.pow_le_pow_right (by decide) ((le_max_left E 300).trans (Nat.le_succ M))
  have hconc : 2 ^ 1 * (150 * childRouterHalfInd #S) ^ 3 ≤ #S := by
    rw [hcard]
    have hmax : max (2 ^ L) 2 = 2 ^ L :=
      max_eq_left (calc 2 = 2 ^ 1 := by decide
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) (by omega))
    have hclog : Nat.clog 2 (max (2 ^ L) 2) ≤ L := by
      rw [hmax]
      exact Nat.clog_le_of_le_pow le_rfl
    have h150 : 150 * childRouterHalfInd (2 ^ L) ≤ 2 ^ 9 * (M - 27) := by
      unfold childRouterHalfInd
      omega
    have hpow3 : (M - 27) ^ 3 ≤ 2 ^ (M - 27) :=
      Nat.pow_le_two_pow (by decide) (by omega)
    calc 2 ^ 1 * (150 * childRouterHalfInd (2 ^ L)) ^ 3
        ≤ 2 * (2 ^ 9 * (M - 27)) ^ 3 :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left h150 3)
      _ = 2 ^ 28 * (M - 27) ^ 3 := by ring
      _ ≤ 2 ^ 28 * 2 ^ (M - 27) := Nat.mul_le_mul_left _ hpow3
      _ = 2 ^ (M + 1) := by
          rw [← Nat.pow_add]
          congr 1
          omega
  exact ⟨hcard, lemma5_1_concentration hsL hgap S hthresh hconc⟩

/-! ## 4. Non-vacuity of `Corollary B.6` and `Lemma 5.2` (`ℋ_ℓ^id` at `n_next = 64`) -/

theorem idCompressor_section5_4_instance
    (S : Finset (Fin (2 ^ 24) × Fin 1000)) (hS : #S ≤ 80) :
    idCompressorSeedBits 1000 24 ≤ 144 ∧
    (∀ (θ : IdCompressorSeed 1000 24) (x : Fin (2 ^ 24) × Fin 1000),
      idCompressorPerm 24 1000 θ (idCompressorPerm 24 1000 θ x) = x) ∧
    (dens {θ : IdCompressorSeed 1000 24 |
      ¬ Set.InjOn (idCompressorHead 24 1000 θ) (S : Set (Fin (2 ^ 24) × Fin 1000))} : ℝ) ≤
      1 / 2048 := by
  have hbits : idCompressorSeedBits 1000 24 ≤ 144 := by
    have hclog : Nat.clog 2 (max 1000 2) ≤ 10 := Nat.clog_le_of_le_pow (by decide)
    have hle := idCompressorSeedBits_le 1000 24
    omega
  have hd := dens_not_injOn_idCompressorHead_le_two_div_sq
    (n_bar := 80) (n_next := 64) S hS (by decide) (by decide)
  exact ⟨hbits, idCompressorPerm_involutive 24 1000, by norm_num at hd; exact hd⟩

theorem lemma5_2_fin2_pow_40 (S : Finset (Fin (2 ^ 40))) :
    (dens {θ : IdCompressorSeed (2 ^ (40 - 24)) 24 |
      ¬ Set.InjOn (fun u => idCompressorHead 24 (2 ^ (40 - 24)) θ (bitDomainEquiv (by decide) u))
        (S : Set (Fin (2 ^ 40)))} : ℝ) ≤
      (#S : ℝ) ^ 2 / (2 * (2 ^ 24 : ℝ)) :=
  lemma5_2_collision_le (by decide) S

end ComplexityTests.FeistelPerm

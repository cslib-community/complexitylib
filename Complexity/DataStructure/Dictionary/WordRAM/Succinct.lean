/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.WordRAM.SuccinctDispatch
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Map
import Complexity.Tactic.Fits

/-!
# Fixed-Capacity Succinct Dynamic Dictionary with Deletions on the Word-RAM

This module packages the fixed-capacity succinct dynamic dictionary with deletions (`insert`,
`delete`, `query`) over `Cslib.WordRAM.Basis.exact` and `Cslib.WordRAM.Basis.standard` as a
reusable `Cslib.DataStructure.WordRAM.Randomized.StateTransitionImpl` certificate
(`Cslib.DataStructure.Dictionary.WordRAM.Succinct.impl` and `implStandard`) for
`Cslib.DataStructure.Dictionary.Dynamic.spec U V n_max`.

## Mathematical and algorithmic design

This implementation combines the bucket partition and fingerprint-indexed buckets of
[Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 3–4][BenderFarachColtonKuszmaulKuszmaul2024] with one-round Feistel quotienting
([Arbitman, Naor, and Segev, FOCS 2010, Claim 5.7][ArbitmanNaorSegev2010];
[Bender, Conway, Farach-Colton, Kuszmaul, and Tagliavini, *J. ACM* 2023, Section 7, arXiv
pp. 31–33][BenderConwayFarachColtonKuszmaulTagliavini2023]). It uses fixed-width full slabs with a
shared tail pool ([Bender, Farach-Colton, J. Kuszmaul, W. Kuszmaul, and M. Liu, STOC 2022,
Sections 5.2 and 6.1, Lemma 24][BenderFarachColtonKuszmaulKuszmaulLiu2022]) together with this
formalization's own micro-bucket chains and slab-hysteresis potential.
Unlike [Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA
2024][BenderFarachColtonKuszmaulKuszmaul2024], the capacity `n_max` is fixed without table resizing.
Hashing uses explicit two-stage 3-wise independent quotient hashing rather than fully random hash
functions (SOSA 2024 Section 2.1). Operations here run in `O(1)` expected amortized time on
oblivious operation sequences fixed before initialization. By contrast, SOSA 2024 Lemma 4.3 gives
worst-case `O(1)` queries and deletions and expected `O(1)` insertions at fixed capacity. SOSA 2024
Sections 5–6 prove with-high-probability bounds and add resizing.

1. **One-round Feistel quotienting (`FeistelQuotient`)**: splits each key `u : Fin U` into a
   `bucketBits n_max`-bit low part and a `quotientBits U n_max`-bit quotient `q`, storing only `q`
   and reconstructing `u` injectively within each bucket
   `b = (h₁(q) mod 2 ^ b_bits) ⊕ (u mod 2 ^ b_bits)`. Storing `n_max` quotients of
   `quotientBits U n_max` bits and `n_max` values of `valBits V` bits uses at most
   `Dynamic.optBits U V n_max + 5 * n_max * Dynamic.logLogFactor n_max` bits
   (`quotient_val_bits_le_optBits`).
   We assume `n_max ≤ U` because keys are distinct elements of `Fin U` (so at most `U` distinct keys
   can coexist, and `U.choose n_max = 0` when `n_max > U`).
2. **Slab + tail slot store (`SuccinctSlotInv`, `SuccinctSlabOps`, `SuccinctTailOps`)**:
   stores up to `n_max` active items in a single `n_max`-slot array (`slotOf`), packing full slabs
   of `slabSize n_max = 2 ^ slabBits n_max` (`(slabScale n_max) ^ 2` when `0 < bucketBits n_max`,
   else `1`) items from the low end and individual tail items from the high end under
   `gm 0 * slabSize n_max + gm 1 ≤ n_max` (`SlotStoreInv.multi_total_le`). Per-bucket item counts
   depend only on the current live set, while the split between full slabs and tail items depends
   on history. `bucketPotential` pays for the lazy promotions and demotions.
3. **Two-stage universe-reduced 3-wise quotient hashing (`ReducedKWise`)**: maps quotients into
   `(bucket, local micro-bucket)` pairs using `O(1) + o(n_max) / w` words of seed and bit-packed
   Four-Russians carryless multiplication tables (`hashSpace U w n_max`), without any
   `U ≤ poly(n_max)` restriction.
4. **`Memory.Prog` + `realize` refinement (`SuccinctProg` .. `SuccinctDispatch`)**: all
   deterministic bucket, slab, tail, and micro-chain operations are written as parameter-free
   `Memory.Prog` subroutines compiled to `WordRAM.Code` via `realize`. They receive the 36 static
   parameters in registers loaded by the 36-instruction `loadParamsCode` prefix.

## Cost model and parameter dependence

* **Program specialization**: the five generic `Memory.Prog` subroutines do not depend on
  `(U, V, w, n_max)`. The full program `subroutineCode U V w n_max` depends on `(U, V, w, n_max)`
  only through the `space` constant in `allocSpan`, the 36-instruction `loadParamsCode` prefix, and
  the hash code. It does not depend on `base` (passed in `frontierReg` at initialization).
  No theorem bounds static code size. All time bounds (`initSteps`, `chargeVal`, `charge`) count
  **executed Word-RAM instructions**.
* **Initialization (`initSteps`)**: `initSteps U n_max ≤ 31 * n_max + 1091 ≤ 1091 * (n_max + 1)`
  (`initSteps_le`, `initSteps_le_mul`). Initialization builds the Four-Russians table and draws one
  uniform quotient-hash seed (`seedSlack = 1`, `initPotential = 0`) that operations keep unchanged.
* **Space (`space`)**: `space U V w n_max ≤ Dynamic.succinctWords 81 213 U V w n_max` words
  (`space_le_succinctWords`) for every `0 < w` and `n_max ≤ U` with `Fits w U` (`U < 2 ^ w`).
* **Constant operation charge (`seq_expected_amortized`)**: at the `Memory.Prog` level
  (`SuccinctHash`), `queryWithHashProg_dict_spec`, `insertWithHashProg_dict_spec`, and
  `deleteWithHashProg_dict_spec` prove per-seed **amortized** `memoryCost` bounds of
  `26 + 8 * probeExcess`, `184 + 8 * probeExcess`, and `270 + 8 * probeExcess` with potential
  `66 * slotPotential` (unchanged on `query`). In turn,
  `tsum_uniform_probeExcess_reducedPolyHash_le_five` bounds expected `probeExcess` by `5`. Because
  the five generic `Memory.Prog` subroutines (`extractQuotGenProg`, `queryWithHashGenProg`,
  `insertWithHashGenProg`, `deletePrepWithHashGenProg`, `deleteFinishWithHashGenProg`) do not depend
  on `(U, V, w, n_max)`, both the register budget `rSuccinct` and the operation charge
  `chargeVal = 313 * opFactor + 284725` are parameter-free `O(1)` constants across all
  `(U, V, w, n_max)`, `base`, and `ops.length`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.impl`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.implStandard`: `Randomized.StateTransitionImpl`
  certificates over `Basis.exact` and `Basis.standard`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.initTime_impl_le`:
  `(impl hw hnU hU hV hfit).initTime ≤ initSteps U n_max + 1` and
  `initSteps U n_max + 1 ≤ 31 * n_max + 1092`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.seq_expected_amortized`: end-to-end
  multi-operation distributional correctness and constant expected amortized execution certificate.

## References

* [Y. Arbitman, M. Naor, G. Segev, *Backyard Cuckoo Hashing: Constant Worst-Case Operations with a
  Succinct Representation*][ArbitmanNaorSegev2010]
* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul, M. Liu,
  *On the Optimal Time/Space Tradeoff for Hash Tables*][BenderFarachColtonKuszmaulKuszmaulLiu2022]
* [M. A. Bender, A. Conway, M. Farach-Colton, W. Kuszmaul, G. Tagliavini,
  *Iceberg Hashing: Optimizing Many Hash-Table Criteria at
  Once*][BenderConwayFarachColtonKuszmaulTagliavini2023]
* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.Succinct

open Cslib.WordRAM Cslib.WordRAM.ExactLog Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.Probability
open Finset
open scoped BigOperators ENNReal

/-! ## Section 1: `allocSpan`, `initSetup`, and `StateTransitionImpl` packaging (`impl`) -/

theorem span_exec_succinct {U V w n_max base : ℕ}
    (hfit : Fits w (base + space U V w n_max))
    {x : Data rSuccinct}
    (hfr : x.regs frontierReg = base) :
    ∃ x₁ : Data rSuccinct,
      ExecWithin w (subroutineCode U V w n_max).allocSpan x x₁ 3 ∧
      x₁.mem = x.mem ∧
      x₁.regs baseReg = base ∧
      x₁.regs frontierReg = base + space U V w n_max ∧
      (∀ j : Fin 0, x₁.regs ((subroutineCode U V w n_max).initParams j) = Fin.elim0 j) := by
  let s₁ := x.set baseReg (x.regs frontierReg)
  let s₂ := s₁.set curReg (space U V w n_max)
  let s₃ := s₂.set frontierReg (base + space U V w n_max)
  have e₁ : ExecWithin (B := .exact) w
      (.op (.copy baseReg frontierReg)) x s₁ 1 :=
    ExecWithin.copy
  have e₂ : ExecWithin (B := .exact) w
      (.op (.const curReg (space U V w n_max))) s₁ s₂ 1 :=
    ExecWithin.const (by fits)
  have e₃ : ExecWithin (B := .exact) w
      (.op (.exactBin .add frontierReg frontierReg curReg)) s₂ s₃ 1 := by
    apply ExecWithin.op
    rw [Op.eval_exactBin]
    have hfr₂ : s₂.regs frontierReg = base := by
      simp only [s₂, s₁, Data.set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, hfr]
    have hcur₂ : s₂.regs curReg = space U V w n_max := by
      simp only [s₂, Data.set_regs, update_sReg, ↓reduceIte]
    rw [hfr₂, hcur₂]
    exact Data.put_of_fits hfit
  refine ⟨s₃, e₁.seq (e₂.seq e₃), rfl, ?_, ?_, fun j => Fin.elim0 j⟩
  · simp only [s₃, s₂, s₁, Data.set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, hfr]
  · simp only [s₃, Data.set_regs, update_sReg, ↓reduceIte]

theorem setup_exec_succinct {U V w n_max base : ℕ}
    (hwf : DictParamsWf U V w n_max)
    (hfit : Fits w (base + space U V w n_max))
    {x₁ : Data rSuccinct}
    (hx₁ : x₁.Bounded w)
    (hbase : x₁.regs baseReg = base)
    (hfr : x₁.regs frontierReg = base + space U V w n_max)
    (hz : ∀ a ∈ (Block.mk base (space U V w n_max)).footprint, x₁.mem a = 0) :
    ∃ ν₀ : PMF (QuotHashSeed U n_max × Data rSuccinct),
      ExecCodeDist w (subroutineCode U V w n_max).initSetup x₁ (ν₀.map Prod.snd)
        ((ReducedKWise.initTableSteps (qBits U n_max) (hashB n_max) (totalMicroBits n_max) +
          ReducedKWise.resampleSteps (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3 : ℕ) :
          ℝ≥0∞) ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ 1 * (PMF.uniformOfFintype (QuotHashSeed U n_max)) θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs frontierReg = base + space U V w n_max ∧
        Rep U V w n_max base p.1 (Dictionary.empty U) p.2 ∧
        potential U V w n_max base p.1 p.2 ≤ 0 ∧
        Modifies (Block.mk base (space U V w n_max)).footprint x₁.mem p.2.mem := by
  have hfit_hash : Fits w (base + hashSpace U w n_max) := by
    refine hfit.of_le ?_
    unfold space totalSpace offGM offLM offVal offQuot
    omega
  have hc_le : 2 * reducedChunkBits
      (reducedTrinomialStep (qBits U n_max) (hashB n_max) (totalMicroBits n_max)) ≤ w :=
    le_of_lt (two_mul_reducedChunkBits_hash_lt hwf.2.1 (le_of_lt hwf.2.2.1) hfit)
  obtain ⟨y_tab, he_tab, hy_base, hy_tab, hy_mod⟩ :=
    ReducedKWise.initTableCode_execWithin (x := x₁.comap coreReg)
      hbase hc_le hfit_hash
  have hy_bdd : y_tab.Bounded w := he_tab.bounded (hx₁.comap coreReg)
  let x₂ : Data rSuccinct := y_tab.extend coreReg x₁
  have hx₂_bdd : x₂.Bounded w := hy_bdd.extend coreReg_injective hx₁
  have he_tab_ren : ExecCodeDist w
      ((ReducedKWise.initTableCode w (qBits U n_max) (hashB n_max)
        (totalMicroBits n_max) 3).rename coreReg)
      x₁ (PMF.pure x₂)
      (ReducedKWise.initTableSteps (qBits U n_max) (hashB n_max)
        (totalMicroBits n_max) : ℝ≥0∞) := by
    simpa [x₂] using (ExecCodeDist.of_execWithin he_tab).rename coreReg_injective
  have hx₂_comap : x₂.comap coreReg = y_tab :=
    Data.comap_extend coreReg_injective y_tab x₁
  have hbase₂ : (x₂.comap coreReg).regs 0 = base := by
    rw [hx₂_comap]; exact hy_base
  have htab₂ : ReducedKWise.TableRep base w (qBits U n_max) (hashB n_max)
      (totalMicroBits n_max) 3 (x₂.comap coreReg).mem := by
    rw [hx₂_comap]; exact hy_tab
  have hres_rand := ReducedKWise.resampleCode_execRand (x := x₂.comap coreReg)
    hbase₂ (qBits_le_of_le_pow hwf.1 (le_of_lt hwf.2.2.1)) hc_le hfit_hash
  obtain ⟨ν_core, he_res, hunif, hsupp_res⟩ :=
    Impl.resample_exec_of_execRand (space := hashSpace U w n_max)
      (ReducedKWise.extractSeed base (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3)
      hres_rand
      (ReducedKWise.map_extractSeed_eval_resampleComp base (qBits U n_max) (hashB n_max)
        (totalMicroBits n_max) 3 (x₂.comap coreReg))
      (fun z hz => by
        obtain ⟨hz0, htab', hseed', hframe, hsteps⟩ :=
          ReducedKWise.mem_support_resampleComp hbase₂ htab₂ hz
        refine ⟨hz0, htab', hseed', ?_, le_of_eq hsteps⟩
        intro a ha
        simp only [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
        apply hframe a
        rcases ha with hlt | hge
        · exact Or.inl hlt
        · exact Or.inr (le_trans (Nat.add_le_add_left (Nat.le_add_right _ _) base) hge))
  have he_res_ren := he_res.rename coreReg_injective
  let lift0 : LatentState (QuotHashSeed U n_max) 240 →
      QuotHashSeed U n_max × Data rSuccinct :=
    fun p => (p.latent, p.data.extend coreReg x₂)
  let ν₀ := ν_core.map lift0
  have he_res_ν₀ : ExecCodeDist w
      ((ReducedKWise.resampleCode (qBits U n_max) (hashB n_max)
        (totalMicroBits n_max) 3).rename coreReg)
      x₂ (ν₀.map Prod.snd)
      (ReducedKWise.resampleSteps (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3 :
        ℝ≥0∞) := by
    refine he_res_ren.congr_dist ?_ le_rfl
    dsimp only [ν₀, lift0]
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  refine ⟨ν₀, ?_, ?_, ?_⟩
  · simpa only [subroutineCode, Nat.cast_add] using he_tab_ren.seq_pure he_res_ν₀
  · intro θ
    dsimp only [ν₀, lift0]
    rw [PMF.map_comp]
    change (ν_core.map LatentState.latent) θ ≤ _
    rw [hunif, one_mul]
  · intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨hq_base, hq_tab, hq_seed, hq_mod⟩ := hsupp_res q hq
    have hq_bdd : q.data.Bounded w :=
      he_res.bounded (hx₂_bdd.comap coreReg) q.data
        ((PMF.mem_support_map_iff _ _ _).mpr ⟨q, hq, rfl⟩)
    let z := q.data.extend coreReg x₂
    have hz_bdd : z.Bounded w := hq_bdd.extend coreReg_injective hx₂_bdd
    have hz_base : z.regs baseReg = base := by
      change (z.comap coreReg).regs 0 = base
      rw [Data.comap_extend coreReg_injective]
      exact hq_base
    have hz_fr : z.regs frontierReg = base + space U V w n_max := by
      dsimp only [z, x₂]
      have h240 : 240 ≤ frontierReg.val := le_rfl
      rw [Data.extend_regs_of_notMem _ _ (notMem_range_coreReg h240),
        Data.extend_regs_of_notMem _ _ (notMem_range_coreReg h240)]
      exact hfr
    have htable_zero : ∀ a, base + hashSpace U w n_max ≤ a →
        a < base + space U V w n_max → z.mem a = 0 := by
      intro a ha1 ha2
      have ha_not_hash : a ∉ (Block.mk base (hashSpace U w n_max)).footprint := by
        simp only [Block.mem_footprint, Block.Owns]
        omega
      have h1 : z.mem a = x₂.mem a := hq_mod a ha_not_hash
      have h2 : x₂.mem a = x₁.mem a := hy_mod a (Or.inr ha1)
      have ha_in : a ∈ (Block.mk base (space U V w n_max)).footprint := by
        simp only [Block.mem_footprint, Block.Owns]
        exact ⟨by omega, ha2⟩
      rw [h1, h2, hz a ha_in]
    have hgm0 : ∀ i, gmAt base U V w n_max (hashSpace U w n_max) z.mem i = 0 :=
      fun i => congrFun (gmAt_zero_of_init hwf.1 htable_zero) i
    have hlm0 : ∀ idx, lmAt base U V w n_max (hashSpace U w n_max) z.mem idx = 0 :=
      fun idx => congrFun (lmAt_zero_of_init hwf.1 htable_zero) idx
    obtain ⟨hdict0, hpot0⟩ :=
      dictStateInv_of_zero (s := memoryState frontierReg z) q.latent hgm0 hlm0
    have hmod_all : Modifies (Block.mk base (space U V w n_max)).footprint x₁.mem z.mem := by
      intro a ha
      simp only [Block.mem_footprint, Block.Owns] at ha
      have ha_not_hash : a ∉ (Block.mk base (hashSpace U w n_max)).footprint := by
        simp only [Block.mem_footprint, Block.Owns]
        intro ⟨h1, h2⟩
        apply ha ⟨h1, lt_of_lt_of_le h2 ?_⟩
        unfold space totalSpace offGM offLM offVal offQuot
        omega
      have h1 : z.mem a = x₂.mem a := hq_mod a ha_not_hash
      have h2 : x₂.mem a = x₁.mem a := by
        apply hy_mod a
        by_cases hlt : a < base
        · exact Or.inl (lt_of_lt_of_le hlt (by dsimp [ReducedKWise.tabBase]; omega))
        · refine Or.inr ?_
          simp only [Block.mem_footprint, Block.Owns, hashSpace, not_and_or, not_le, not_lt]
            at ha_not_hash
          omega
      exact h1.trans h2
    refine ⟨hz_fr, ⟨hz_bdd, hz_base, hz_fr, hq_tab, hq_seed, hdict0⟩, ?_, hmod_all⟩
    unfold potential
    change slotPotential n_max (gmAt base U V w n_max (hashSpace U w n_max) (lift0 q).2.mem) = 0
      at hpot0
    rw [hpot0, Nat.mul_zero]

theorem tsum_mul_probeExcess_le {U V w n_max base : ℕ} (hnU : n_max ≤ U)
    {s_abs : Dictionary.State U} (u : Fin U)
    (ν : PMF (QuotHashSeed U n_max × Data rSuccinct))
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ 1 * (PMF.uniformOfFintype (QuotHashSeed U n_max)) θ)
    (hsupp : ∀ p ∈ ν.support, Rep U V w n_max base p.1 s_abs p.2) :
    (∑' p, ν p *
      ((8 * opFactor) *
        probeExcess n_max (qStage1 U n_max p.1.1) (polyStage2 U n_max) p.1.2
          (Dictionary.dom s_abs) u : ℕ)) ≤
      (40 * opFactor : ℝ≥0∞) := by
  obtain ⟨p₀, hp₀⟩ := ν.support_nonempty
  have hdict₀ := (hsupp p₀ hp₀).2.2.2.2.2
  obtain ⟨L₀, hb₀⟩ := hdict₀.hbucket
  have hcard_le : (Dictionary.dom s_abs).card ≤ n_max := by
    rw [← hdict₀.htot]
    unfold totalSlots
    split_ifs with hb_z
    · exact hb₀.hslot.single_valid hb_z
    · exact hb₀.hslot.multi_total_le (Nat.pos_of_ne_zero hb_z)
  have herase_le : #((Dictionary.dom s_abs).erase u) ≤ n_max :=
    Finset.card_erase_le.trans hcard_le
  let E (θ : QuotHashSeed U n_max) : ℝ≥0∞ :=
    (probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
      (Dictionary.dom s_abs) u : ℝ≥0∞)
  have hmap :
      (∑' p, ν p * ((8 * opFactor : ℝ≥0∞) * E p.1)) =
        (8 * opFactor : ℝ≥0∞) * ∑' θ, (ν.map Prod.fst) θ * E θ := by
    rw [← ENNReal.tsum_mul_left,
      ← Cslib.Probability.PMF.tsum_map_mul ν Prod.fst
        (fun θ => (8 * opFactor : ℝ≥0∞) * E θ)]
    refine tsum_congr fun p => ?_
    ring
  have hle_unif :
      (∑' θ, (ν.map Prod.fst) θ * E θ) ≤
        ∑' θ, (PMF.uniformOfFintype (QuotHashSeed U n_max)) θ * E θ := by
    refine tsum_le_tsum fun θ => ?_
    have hs := hseed θ
    rw [one_mul] at hs
    exact mul_le_mul' hs le_rfl
  have h5 := tsum_uniform_probeExcess_reducedPolyHash_le_five hnU (Dictionary.dom s_abs) u herase_le
  calc (∑' p, ν p *
        ((8 * opFactor) *
          probeExcess n_max (qStage1 U n_max p.1.1) (polyStage2 U n_max) p.1.2
            (Dictionary.dom s_abs) u : ℕ))
      = ∑' p, ν p * ((8 * opFactor : ℝ≥0∞) * E p.1) := by
        refine tsum_congr fun p => ?_
        push_cast
        rfl
    _ = (8 * opFactor : ℝ≥0∞) * ∑' θ, (ν.map Prod.fst) θ * E θ := hmap
    _ ≤ (8 * opFactor : ℝ≥0∞) *
          ∑' θ, (PMF.uniformOfFintype (QuotHashSeed U n_max)) θ * E θ :=
        mul_le_mul' le_rfl hle_unif
    _ ≤ (8 * opFactor : ℝ≥0∞) * 5 :=
        mul_le_mul' le_rfl h5
    _ = (40 * opFactor : ℝ≥0∞) := by
        norm_cast; ring

@[simp]
theorem input_tagReg (U V w n_max : ℕ) :
    (subroutineCode U V w n_max).input tagReg = true :=
  decide_eq_true (Or.inl rfl)

@[simp]
theorem input_argUReg (U V w n_max : ℕ) :
    (subroutineCode U V w n_max).input argUReg = true :=
  decide_eq_true (Or.inr (Or.inl rfl))

@[simp]
theorem input_argVReg (U V w n_max : ℕ) :
    (subroutineCode U V w n_max).input argVReg = true :=
  decide_eq_true (Or.inr (Or.inr rfl))

theorem input_sReg_eq_false {U V w n_max : ℕ} {i : Fin 292}
    (h1 : i ≠ 244) (h2 : i ≠ 245) (h3 : i ≠ 246) :
    (subroutineCode U V w n_max).input (sReg i) = false := by
  dsimp only [subroutineCode]
  rw [decide_eq_false_iff_not]
  rintro (h | h | h)
  · exact h1 (sReg_injective h)
  · exact h2 (sReg_injective h)
  · exact h3 (sReg_injective h)

/-- Reusable `Randomized.StateTransitionImpl` certificate over `Basis.exact` for the fixed-capacity
succinct dynamic dictionary (`Dynamic.spec U V n_max`). -/
@[expose]
noncomputable def impl {U V w n_max base : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + space U V w n_max)) :
    Randomized.StateTransitionImpl (subroutineCode U V w n_max)
      (Dynamic.spec U V n_max) w base Fin.elim0 (Dictionary.empty U) :=
  have hwf : DictParamsWf U V w n_max := ⟨hw, hnU, hU, le_of_lt hV⟩
  have hw2 : 2 ≤ w := two_le_w_of_fits_space hfit
  Randomized.StateTransitionImpl.ofFn
    (Seed := QuotHashSeed U n_max)
    (seedLaw := PMF.uniformOfFintype (QuotHashSeed U n_max))
    (seedSlack := 1)
    (seedSlack_ne_top := by simp)
    (space := space U V w n_max)
    (spanTime := 3)
    (setupTime :=
      ((ReducedKWise.initTableSteps (qBits U n_max) (hashB n_max) (totalMicroBits n_max) +
        ReducedKWise.resampleSteps (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3 : ℕ) :
        ℝ≥0∞))
    (initPotential := 0)
    (charge := charge)
    (rep := Rep U V w n_max base)
    (potential := potential U V w n_max base)
    (encode := encode)
    (argMatch := argMatch)
    (decode := decode)
    (bounded := fun h => h.1)
    (arguments_fit := by
      intro s o hval i hi
      have hfit0 : Fits w 0 := Nat.two_pow_pos w
      have hfit2 : Fits w 2 :=
        lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right two_pos hw2)
      have hfit1 : Fits w 1 := by fits
      rcases of_decide_eq_true hi with rfl | rfl | rfl <;> cases o with
      | query u =>
        all_goals dsimp only [encode]
        all_goals split_ifs <;> first | exact hfit0 | exact u.isLt.trans hU
      | insert u v =>
        all_goals dsimp only [encode]
        all_goals split_ifs <;>
          first | exact hfit1 | exact u.isLt.trans hU | exact hval.2.trans hV | exact hfit0
      | delete u =>
        all_goals dsimp only [encode]
        all_goals split_ifs <;> first | exact hfit2 | exact u.isLt.trans hU | exact hfit0)
    (encode_matches := by
      intro o regs
      cases o with
      | query u =>
        dsimp only [argMatch, encode]
        simp only [input_tagReg, input_argUReg, sReg_inj, Fin.reduceEq, ↓reduceIte, and_self]
      | insert u v =>
        dsimp only [argMatch, encode]
        simp only [input_tagReg, input_argUReg, input_argVReg, sReg_inj, Fin.reduceEq, ↓reduceIte,
          and_self]
      | delete u =>
        dsimp only [argMatch, encode]
        simp only [input_tagReg, input_argUReg, sReg_inj, Fin.reduceEq, ↓reduceIte, and_self])
    (rep_supported := by
      intro θ s x x' hregs hmem hx'_bdd ⟨_, hbase, hfr, htab, hseed, hdict⟩
      have hbase' : x'.regs baseReg = base :=
        (hregs baseReg
          (input_sReg_eq_false (by decide) (by decide) (by decide))).trans hbase
      have hfr' : x'.regs frontierReg = base + space U V w n_max :=
        (hregs frontierReg
          (input_sReg_eq_false (by decide) (by decide) (by decide))).trans hfr
      have hhash_eq : ∀ a, base ≤ a → a < base + hashSpace U w n_max → x.mem a = x'.mem a := by
        intro a ha1 ha2
        refine (hmem a ?_).symm
        simp only [Block.mem_footprint, Block.Owns]
        refine ⟨ha1, lt_of_lt_of_le ha2 ?_⟩
        unfold space totalSpace offGM offLM offVal offQuot
        omega
      have htab_eq : ∀ a, base + hashSpace U w n_max ≤ a → a < base + space U V w n_max →
          (memoryState frontierReg x).mem a =
            (memoryState frontierReg x').mem a := by
        intro a ha1 ha2
        refine (hmem a ?_).symm
        simp only [Block.mem_footprint, Block.Owns]
        exact ⟨by omega, ha2⟩
      exact ⟨hx'_bdd, hbase', hfr',
        tableRep_congr hhash_eq htab,
        seedRep_congr hhash_eq hseed,
        dictStateInv_congr hw htab_eq hdict⟩)
    (potential_supported := by
      intro θ s x x' _ hmem _
      unfold potential
      have htab_eq : ∀ a, base + hashSpace U w n_max ≤ a → a < base + space U V w n_max →
          x'.mem a = x.mem a := by
        intro a ha1 ha2
        refine hmem a ?_
        simp only [Block.mem_footprint, Block.Owns]
        exact ⟨by omega, ha2⟩
      rw [(arrays_congr_of_eq_on hw htab_eq).2.2.2])
    (clear_nodup := by
      change (List.map sReg [241, 242, 243, 0, 240]).Nodup
      exact (List.nodup_map_iff sReg_injective).mpr (by decide))
    (params_not_clear := fun j => Fin.elim0 j)
    (incCur_eval := by
      intro x h1 hfit_inc
      change x.regs oneReg = 1 at h1
      change (Op.exactBin .add curReg curReg oneReg).eval w x = _
      rw [Op.eval_exactBin, h1]
      exact Data.put_of_fits hfit_inc)
    (span_exec := fun _ hfr _ => span_exec_succinct hfit hfr)
    (setup_exec := fun hx₁ hbase hfr _ hz => setup_exec_succinct hwf hfit hx₁ hbase hfr hz)
    (step_exec := by
      classical
      intro s o ν hv hseed hsupp
      let nextData (p : QuotHashSeed U n_max × Data rSuccinct) :
          Data rSuccinct :=
        if hp : p ∈ ν.support then
          Classical.choose (exec_opCode hwf hV hfit p.1 s o hv (hsupp p hp).1 (hsupp p hp).2)
        else p.2
      let nextSteps (p : QuotHashSeed U n_max × Data rSuccinct) : ℕ :=
        if hp : p ∈ ν.support then
          Classical.choose (Classical.choose_spec
            (exec_opCode hwf hV hfit p.1 s o hv (hsupp p hp).1 (hsupp p hp).2))
        else 0
      let μ_step (p : QuotHashSeed U n_max × Data rSuccinct) :
          PMF (QuotHashSeed U n_max × Data rSuccinct) :=
        PMF.pure (p.1, nextData p)
      let T_step (p : QuotHashSeed U n_max × Data rSuccinct) : ℝ≥0∞ :=
        (nextSteps p : ℝ≥0∞)
      refine ⟨μ_step, T_step, ?_, ?_, ?_⟩
      · intro p hp
        have hspec := Classical.choose_spec (Classical.choose_spec
          (exec_opCode hwf hV hfit p.1 s o hv (hsupp p hp).1 (hsupp p hp).2))
        have hd_eq : nextData p =
            Classical.choose (exec_opCode hwf hV hfit p.1 s o hv (hsupp p hp).1 (hsupp p hp).2) :=
          dite_eq_left hp
        have hs_eq : nextSteps p =
            Classical.choose (Classical.choose_spec
              (exec_opCode hwf hV hfit p.1 s o hv (hsupp p hp).1 (hsupp p hp).2)) :=
          dite_eq_left hp
        refine ⟨?_, ?_⟩
        · dsimp only [μ_step, T_step]
          rw [PMF.pure_map, hd_eq, hs_eq]
          exact ExecCodeDist.of_execWithin hspec.1
        · intro q hq
          dsimp only [μ_step] at hq
          rw [PMF.support_pure, Set.mem_singleton_iff] at hq
          subst hq
          dsimp only
          rw [hd_eq]
          exact ⟨hspec.2.1, hspec.2.2.1, hspec.2.2.2.1⟩
      · intro θ'
        have hmap_eq : (ν.bind μ_step).map Prod.fst = ν.map Prod.fst := by
          rw [PMF.map_bind]
          dsimp only [μ_step]
          simp only [PMF.pure_map]
          rfl
        rw [hmap_eq]
        exact hseed θ'
      · have hinner : ∀ p,
            T_step p + (∑' q, μ_step p q * (potential U V w n_max base q.1 q.2 : ℝ≥0∞)) =
              (nextSteps p + potential U V w n_max base p.1 (nextData p) : ℕ) := by
          intro p
          dsimp only [μ_step, T_step]
          rw [tsum_eq_single (p.1, nextData p)
            (fun q hq => by rw [PMF.pure_apply_of_ne _ _ hq, zero_mul])]
          simp
        simp_rw [hinner]
        have hptwise :
            (∑' p, ν p * (nextSteps p + potential U V w n_max base p.1 (nextData p) : ℕ)) ≤
              ∑' p, ν p *
                ((potential U V w n_max base p.1 p.2 : ℝ≥0∞) +
                  (273 * opFactor + 284725 : ℝ≥0∞) +
                  ((8 * opFactor) *
                    probeExcess n_max (qStage1 U n_max p.1.1) (polyStage2 U n_max) p.1.2
                      (Dictionary.dom s) (opKey o) : ℕ)) := by
          refine tsum_le_tsum fun p => ?_
          by_cases hp : p ∈ ν.support
          · refine mul_le_mul' le_rfl ?_
            have hspec := Classical.choose_spec (Classical.choose_spec
              (exec_opCode hwf hV hfit p.1 s o hv (hsupp p hp).1 (hsupp p hp).2))
            have hd_eq : nextData p =
                Classical.choose
                  (exec_opCode hwf hV hfit p.1 s o hv (hsupp p hp).1 (hsupp p hp).2) :=
              dite_eq_left hp
            have hs_eq : nextSteps p =
                Classical.choose (Classical.choose_spec
                  (exec_opCode hwf hV hfit p.1 s o hv (hsupp p hp).1 (hsupp p hp).2)) :=
              dite_eq_left hp
            rw [hd_eq, hs_eq]
            exact_mod_cast hspec.2.2.2.2
          · rw [(PMF.apply_eq_zero_iff _ _).mpr hp, zero_mul, zero_mul]
        have hprobe_sum :=
          tsum_mul_probeExcess_le hnU (opKey o) ν hseed (fun p hp => (hsupp p hp).1)
        have hsplit :
            (∑' p, ν p *
              ((potential U V w n_max base p.1 p.2 : ℝ≥0∞) +
                (273 * opFactor + 284725 : ℝ≥0∞) +
                ((8 * opFactor) *
                  probeExcess n_max (qStage1 U n_max p.1.1) (polyStage2 U n_max) p.1.2
                    (Dictionary.dom s) (opKey o) : ℕ))) =
              (∑' p, ν p * (potential U V w n_max base p.1 p.2 : ℝ≥0∞)) +
                (273 * opFactor + 284725 : ℝ≥0∞) +
                ∑' p, ν p *
                  ((8 * opFactor) *
                    probeExcess n_max (qStage1 U n_max p.1.1) (polyStage2 U n_max) p.1.2
                      (Dictionary.dom s) (opKey o) : ℕ) := by
          simp_rw [mul_add, tsum_add, ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]
        have hch_eq :
            (273 * opFactor + 284725 : ℝ≥0∞) +
              (40 * opFactor : ℝ≥0∞) =
            (charge s o : ℝ≥0∞) := by
          unfold charge chargeVal
          rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat]
          ring
        calc (∑' p, ν p * (nextSteps p + potential U V w n_max base p.1 (nextData p) : ℕ))
            ≤ (∑' p, ν p * (potential U V w n_max base p.1 p.2 : ℝ≥0∞)) +
                (273 * opFactor + 284725 : ℝ≥0∞) +
                ∑' p, ν p *
                  ((8 * opFactor) *
                    probeExcess n_max (qStage1 U n_max p.1.1) (polyStage2 U n_max) p.1.2
                      (Dictionary.dom s) (opKey o) : ℕ) := hsplit ▸ hptwise
          _ ≤ (∑' p, ν p * (potential U V w n_max base p.1 p.2 : ℝ≥0∞)) +
                (273 * opFactor + 284725 : ℝ≥0∞) +
                (40 * opFactor : ℝ≥0∞) :=
              add_le_add le_rfl hprobe_sum
          _ = (charge s o : ℝ≥0∞) +
                ∑' p, ν p * (potential U V w n_max base p.1 p.2 : ℝ≥0∞) := by
              rw [add_assoc, hch_eq, add_comm])

/-- Reusable `Randomized.StateTransitionImpl` certificate over `Basis.standard` for the
fixed-capacity succinct dynamic dictionary (`Dynamic.spec U V n_max`). -/
@[expose]
noncomputable def implStandard {U V w n_max base : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + space U V w n_max)) :
    Randomized.StateTransitionImpl (subroutineCode U V w n_max).toStandard
      (Dynamic.spec U V n_max) w base Fin.elim0 (Dictionary.empty U) :=
  (impl hw hnU hU hV hfit).toStandard

/-- The total initialization time `(impl hw hnU hU hV hfit).initTime` is bounded by
`initSteps U n_max + 1 ≤ 31 * n_max + 1092`. -/
theorem initTime_impl_le {U V w n_max base : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + space U V w n_max)) :
    (impl hw hnU hU hV hfit).initTime ≤ (initSteps U n_max + 1 : ℕ) ∧
    initSteps U n_max + 1 ≤ 31 * n_max + 1092 := by
  refine ⟨?_, by have := initSteps_le U n_max; omega⟩
  dsimp only [impl, Randomized.StateTransitionImpl.ofFn, Randomized.StateTransitionImpl.initTime]
  norm_cast
  unfold initSteps
  omega

theorem totalCost_charge_eq (U V n_max : ℕ) (s₀ : Dictionary.State U)
    (ops : List (Dynamic.Op U)) :
    (Dynamic.spec U V n_max).totalCost charge s₀ ops =
      ops.length * chargeVal := by
  induction ops generalizing s₀ with
  | nil => simp
  | cons o os ih =>
    rw [StateTransitionSpec.totalCost_cons, ih]
    unfold charge
    simp only [List.length_cons]
    ring

/-- **Headline multi-operation theorem (`seq_expected_amortized`):**
Starting from zeroed memory on `[base, base + space U V w n_max)`, fresh initialization followed by
any valid operation sequence `ops : List (Dynamic.Op U)` (`ValidHistory (Dictionary.empty U) ops`)
preserves `Rep` across `ops` with expected total instruction count at most
`initTime + ops.length * chargeVal` for the parameter-free `O(1)` operation charge `chargeVal`
(amortized across `ops`). Companion theorems `space_le_succinctWords` and
`initTime_impl_le` / `initSteps_le` establish the succinct space and linear initialization
bounds. -/
theorem seq_expected_amortized {U V w n_max base : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + space U V w n_max))
    {x : Data rSuccinct} (ops : List (Dynamic.Op U))
    (hx : x.Bounded w) (hfr : x.regs frontierReg = base)
    (hz : ∀ a ∈ (Block.mk base (space U V w n_max)).footprint, x.mem a = 0)
    (hv : (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    ∃ (ν₀ ν_final : PMF ((impl hw hnU hU hV hfit).Seed × Data rSuccinct))
      (T_ops : ℝ≥0∞),
      ExecCodeDist w (subroutineCode U V w n_max).initFresh x (ν₀.map Prod.snd)
        (impl hw hnU hU hV hfit).initTime ∧
      (impl hw hnU hU hV hfit).ExecStepsOfFn (Dictionary.empty U) ops ν₀ ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ (PMF.uniformOfFintype (QuotHashSeed U n_max)) θ) ∧
      (∀ p ∈ ν_final.support,
        Rep U V w n_max base p.1 ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).1 p.2) ∧
      (impl hw hnU hU hV hfit).initTime + T_ops +
        (∑' q, ν_final q * (potential U V w n_max base q.1 q.2 : ℝ≥0∞)) ≤
        (impl hw hnU hU hV hfit).initTime + (ops.length * chargeVal : ℕ) := by
  let C := impl hw hnU hU hV hfit
  obtain ⟨ν₀, ν_final, T_ops, he_init, hex_steps, hseed_final, hrep_final, hamort⟩ :=
    C.seq_expected_amortized_ofFn ops hx hfr (fun j => Fin.elim0 j) hz hv
  refine ⟨ν₀, ν_final, T_ops, he_init, hex_steps, fun θ => ?_, hrep_final, ?_⟩
  · have hs := hseed_final θ
    change (ν_final.map Prod.fst) θ ≤ 1 * (PMF.uniformOfFintype (QuotHashSeed U n_max)) θ at hs
    rwa [one_mul] at hs
  · change C.initTime + T_ops +
        (∑' q, ν_final q * (potential U V w n_max base q.1 q.2 : ℝ≥0∞)) ≤
      C.initTime + (0 : ℕ) +
        ((Dynamic.spec U V n_max).totalCost charge (Dictionary.empty U) ops : ℝ≥0∞)
      at hamort
    rw [totalCost_charge_eq] at hamort
    simpa only [Nat.cast_zero, add_zero] using hamort

end Cslib.DataStructure.Dictionary.WordRAM.Succinct

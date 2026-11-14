/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.MetaSync
public import CslibFrontier.Computability.WordRAM.Resizable.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# In-Epoch Resizable Succinct Compacted Representation and In-Epoch Primitives (Milestone M3a)

This module formalizes Milestone `M3a` (part of `#3167`) of the resizable succinct dynamic
dictionary on the word-granular **Resizable Word RAM** (`Cslib.WordRAM.Resizable`).

It establishes:
1. **Static `1 · OPT` compacted epoch footprint bounds** (`compactedEpochWords_le_succinctWords`,
   `w_mul_compactedEpochWords_le_bits`): under `EpochValid U n N`, the live compacted epoch
   footprint formula is at most `Dynamic.succinctWords 1355 441 U V w n` words (`1 · OPT`,
   never `2 · OPT`). The constant `1355` decomposes algebraically as `11 + 1344`, where
   `11 = 5 + 6` bounds the quotient-bit slack (5 from Feistel quotient/val vs `optBits` and
   6 from `quotientBits U N ≤ quotientBits U n + 6` via `N ≤ 4 * n`), and `1344 = 16 * 84`
   bounds the `84 * N * logLogFactor N` metadata arrays via `N ≤ 4 * n` and
   `logLogFactor N ≤ 4 * logLogFactor n` (the static footprint formula constant is 1355;
   ≤ 680 is the T59 §5.3 window-shift constant for operational dynamic windows in M3b).
2. **Dense key reconstruction and live representation invariants** (`reconstructKeyAt_spec`,
   `CompactedSplitRep`, `CompactedRep`, `compactedRep_empty`): every dense slot $d < n$
   reconstructs a live $(u, v)$ in $s_{\mathrm{abs}}$ injectively and surjectively.

Operational execution (`inEpochOpCode`, `PeakFrontierLe ≤ base + compactedEpochWords`, and $O(1)$
expected amortized dynamic step bounds) is deferred to Milestone `M3b` (see GitHub issue
comment https://github.com/cslib-community/cslib-frontier/issues/3167#issuecomment-6871600467
and `ROADMAP.md`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompactedSplitRep`:
  active epoch representation at arbitrary `(metaBase, itemBase)`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompactedRep`:
  live resting invariant on `RData r` at `frontier = base + compactedEpochWords`.

## Main results

* `compactedEpochWords_le_succinctWords`: live epoch words bounded by succinct words.
* `w_mul_compactedEpochWords_le_bits`: word-multiplied `1 · OPT` bit-space bound.
* `reconstructKeyAt_spec`: exact bijective key/value reconstruction on live dense slots.
* `compactedRep_empty`: initial empty dictionary representation certificate.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4 and 6][BenderFarachColtonKuszmaulKuszmaul2024]
* [W. Kuszmaul, J. Liang, and R. Zhou, *Succinct Dynamic Rank/Select*, SODA 2026,
  Section 5.1][KuszmaulLiangZhou2026]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM
open scoped BigOperators ENNReal

/-! ## Section 1: Compacted Epoch `1 · OPT` Word-Space and Bit-Space Bounds -/

private theorem compactedEpochWords_pos_le_div_add {U V w N n : ℕ}
    (hw : 0 < w) (hNU : N ≤ U) (hU : U ≤ 2 ^ w) :
    offCompItems U w N + compactedItemWords U V w N n ≤
      (n * (quotientBits U N + valBits V) + localMetaLen N * effBucketPosBits N +
        globalMetaLen N * globalPtrBits N + (2 * maxTailItems N) * globalPtrBits N +
        (2 * N) * 1 + w - 1) / w + 441 := by
  have hlm_eq : 9 * totalMicroBuckets N = localMetaLen N := by
    unfold localMetaLen effBucketCap totalMicroBuckets totalMicroBits numBuckets numMicroPerBucket
    rw [Nat.pow_add]; ring
  have hh := hashSpace_le hw hNU hU
  have h1 := div_add_mul_packedWords_le 9
    (n * (quotientBits U N + valBits V)) 2 (totalMicroBuckets N) (effBucketPosBits N) w
  rw [hlm_eq] at h1
  have h2 := div_add_packedWords_le
    (n * (quotientBits U N + valBits V) + localMetaLen N * effBucketPosBits N) 29
    (globalMetaLen N) (globalPtrBits N) w
  have h3 := div_add_mul_packedWords_le 2
    (n * (quotientBits U N + valBits V) + localMetaLen N * effBucketPosBits N +
      globalMetaLen N * globalPtrBits N) 32 (maxTailItems N) (globalPtrBits N) w
  have h4 := div_add_packedWords_le
    (n * (quotientBits U N + valBits V) + localMetaLen N * effBucketPosBits N +
      globalMetaLen N * globalPtrBits N + (2 * maxTailItems N) * globalPtrBits N) 38
    (2 * N) 1 w
  unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords
    epochHashSpace epochQBits epochHashB lmSubWords compactedItemWords
  unfold hashSpace qBits hashB at hh
  omega

/-- **Static `1 · OPT` word-space bound (`compactedEpochWords_le_succinctWords`):**
whenever `EpochValid U n N` (`n = 0 ∧ N = 0` or `1 ≤ n ≤ N ≤ 4 * n ∧ N ≤ U`), the live compacted
footprint `compactedEpochWords U V w N n` is at most `Dynamic.succinctWords 1355 441 U V w n`. -/
theorem compactedEpochWords_le_succinctWords {U V w N n : ℕ}
    (hw : 0 < w) (hU : Fits w U) (_hU_pos : 0 < U) (_hV_pos : 0 < V) (hev : EpochValid U n N) :
    compactedEpochWords U V w N n ≤ Dynamic.succinctWords 1355 441 U V w n := by
  rcases hev with ⟨rfl, rfl⟩ | ⟨_, hnN, hN4, hNU⟩
  · unfold compactedEpochWords rootHdrWords Dynamic.succinctWords
    simp only [↓reduceIte]
    exact (by decide : 8 ≤ 441).trans (Nat.le_add_left 441 _)
  · unfold compactedEpochWords
    split_ifs with hn0
    · unfold rootHdrWords Dynamic.succinctWords
      exact (by decide : 8 ≤ 441).trans (Nat.le_add_left 441 _)
    · have hnU : n ≤ U := hnN.trans hNU
      have hbase := compactedEpochWords_pos_le_div_add (V := V) (n := n) hw hNU hU.le
      have hq6 := quotientBits_le_add_six_of_le_four_mul U hnN hN4
      have hqv_opt := quotient_val_bits_le_optBits (U := U) (V := V) (n := n)
      have hll_n := Dynamic.one_le_logLogFactor n
      have hll_N : Dynamic.logLogFactor N ≤ 4 * Dynamic.logLogFactor n :=
        (Dynamic.logLogFactor_mono hN4).trans (Dynamic.logLogFactor_four_mul_le n)
      have hlm := localMetaLen_mul_effBucketPosBits_le N
      have hgm := globalMetaLen_mul_globalPtrBits_le N
      have htail := maxTailItems_mul_globalPtrBits_le N
      have hitem_bits :
          n * (quotientBits U N + valBits V) ≤
            Dynamic.optBits U V n + 11 * n * Dynamic.logLogFactor n := by
        have hmul : n * (quotientBits U N + valBits V) ≤
            n * (quotientBits U n + valBits V) + 6 * n := by
          calc n * (quotientBits U N + valBits V)
              ≤ n * (quotientBits U n + 6 + valBits V) := Nat.mul_le_mul_left n (by omega)
            _ = n * (quotientBits U n + valBits V) + 6 * n := by ring
        have h6n : 6 * n ≤ 6 * n * Dynamic.logLogFactor n := by
          calc 6 * n = 6 * n * 1 := by ring
            _ ≤ 6 * n * Dynamic.logLogFactor n := by gcongr
        have h11 : 5 * n * Dynamic.logLogFactor n + 6 * n * Dynamic.logLogFactor n =
            11 * n * Dynamic.logLogFactor n := by ring
        omega
      have hmeta_bits :
          localMetaLen N * effBucketPosBits N + globalMetaLen N * globalPtrBits N +
            (2 * maxTailItems N) * globalPtrBits N + (2 * N) * 1 ≤
            1344 * n * Dynamic.logLogFactor n := by
        have hll_N1 := Dynamic.one_le_logLogFactor N
        have h2tail : (2 * maxTailItems N) * globalPtrBits N ≤ 8 * N := by
          calc (2 * maxTailItems N) * globalPtrBits N
              = 2 * (maxTailItems N * globalPtrBits N) := by ring
            _ ≤ 2 * (4 * N) := Nat.mul_le_mul_left 2 htail
            _ = 8 * N := by ring
        have h10N : (2 * maxTailItems N) * globalPtrBits N + (2 * N) * 1 ≤
            10 * N * Dynamic.logLogFactor N := by
          have h10 : 10 * N ≤ 10 * N * Dynamic.logLogFactor N := by
            calc 10 * N = 10 * N * 1 := by ring
              _ ≤ 10 * N * Dynamic.logLogFactor N := by gcongr
          omega
        have h84N :
            localMetaLen N * effBucketPosBits N + globalMetaLen N * globalPtrBits N +
              (2 * maxTailItems N) * globalPtrBits N + (2 * N) * 1 ≤
              84 * N * Dynamic.logLogFactor N := by
          have : 84 * N * Dynamic.logLogFactor N =
              54 * N * Dynamic.logLogFactor N + 20 * N * Dynamic.logLogFactor N +
                10 * N * Dynamic.logLogFactor N := by ring
          omega
        have hN_ll : N * Dynamic.logLogFactor N ≤ 16 * (n * Dynamic.logLogFactor n) := by
          calc N * Dynamic.logLogFactor N
              ≤ (4 * n) * (4 * Dynamic.logLogFactor n) := Nat.mul_le_mul hN4 hll_N
            _ = 16 * (n * Dynamic.logLogFactor n) := by ring
        nlinarith
      have hnum :
          n * (quotientBits U N + valBits V) + localMetaLen N * effBucketPosBits N +
            globalMetaLen N * globalPtrBits N + (2 * maxTailItems N) * globalPtrBits N +
            (2 * N) * 1 + w - 1 ≤
          Dynamic.optBits U V n + 1355 * n * Dynamic.logLogFactor n + w - 1 := by
        have : 1355 * n * Dynamic.logLogFactor n =
            11 * n * Dynamic.logLogFactor n + 1344 * n * Dynamic.logLogFactor n := by ring
        omega
      have hdiv := Nat.div_le_div_right (c := w) hnum
      unfold Dynamic.succinctWords
      omega

/-- **Static `1 · OPT` bit-space bound (`w_mul_compactedEpochWords_le_bits`):**
multiplying `compactedEpochWords U V w N n` by `w` yields at most
`Dynamic.optBits U V n + 1355 * n * Dynamic.logLogFactor n + 442 * w` bits across every valid
epoch (`EpochValid U n N`). -/
theorem w_mul_compactedEpochWords_le_bits {U V w N n : ℕ}
    (hw : 0 < w) (hU : Fits w U) (hU_pos : 0 < U) (hV_pos : 0 < V) (hev : EpochValid U n N) :
    w * compactedEpochWords U V w N n ≤
      Dynamic.optBits U V n + 1355 * n * Dynamic.logLogFactor n + 442 * w := by
  calc w * compactedEpochWords U V w N n
      ≤ w * Dynamic.succinctWords 1355 441 U V w n :=
        Nat.mul_le_mul_left w (compactedEpochWords_le_succinctWords hw hU hU_pos hV_pos hev)
    _ ≤ Dynamic.optBits U V n + 1355 * n * Dynamic.logLogFactor n + (441 + 1) * w :=
        succinctWords_mul_w_le_bits 1355 441 U V w n

/-! ## Section 2: Key Reconstruction and Compacted Representation Invariants -/

/-- Every dense slot `d < n` reconstructs a live `(u, v)` in `s_abs`
injectively and surjectively. -/
theorem reconstructKeyAt_spec {metaBase itemBase U V w N n : ℕ} {θ : QuotHashSeed U N}
    {s_abs : Dictionary.State U} {s_fix s : Memory.State}
    (hvals : Dictionary.ValuesBounded V s_abs) (hNU : N ≤ U)
    (hinv : DictStateInv U V (ghostW w) N 0 θ s_abs s_fix)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hn : totalSlots N (compGmAt metaBase U w N s.mem) = n) :
    (∀ d < n, ∃ hu : reconstructKeyAt metaBase itemBase U V w N n θ s.mem d < U,
      s_abs ⟨reconstructKeyAt metaBase itemBase U V w N n θ s.mem d, hu⟩ =
        some (compValAt itemBase U V w N n s.mem d) ∧
      compValAt itemBase U V w N n s.mem d < V) ∧
    (∀ d₁ < n, ∀ d₂ < n,
      reconstructKeyAt metaBase itemBase U V w N n θ s.mem d₁ =
      reconstructKeyAt metaBase itemBase U V w N n θ s.mem d₂ → d₁ = d₂) ∧
    (∀ u : Fin U, (s_abs u).isSome →
      ∃ d < n, reconstructKeyAt metaBase itemBase U V w N n θ s.mem d = u.val) := by
  obtain ⟨L, hbucket⟩ := hinv.hbucket
  set gm := compGmAt metaBase U w N s.mem
  set td := compTDAt metaBase U w N s.mem
  set dt := compDTAt metaBase U w N s.mem
  set wg := ghostW w
  have hgm_eq : gmAt 0 U V wg N (hashSpace U wg N) s_fix.mem = gm := by
    change gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem = _
    exact hcpl.gm_eq.symm
  have hslot : SlotStoreInv N gm := by rw [← hgm_eq]; exact hbucket.hslot
  have htd : 0 < bucketBits N → TailDenseInv N (gm 0) (gm 1) td dt := fun hb => by
    have hwin := hcpl.win_inv; simp only [Nat.ne_of_gt hb, ↓reduceIte] at hwin; exact hwin
  have htot_eq : epochTotalSlots N gm = n := hn
  have h1 : ∀ d < n, ∃ hu : reconstructKeyAt metaBase itemBase U V w N n θ s.mem d < U,
      s_abs ⟨reconstructKeyAt metaBase itemBase U V w N n θ s.mem d, hu⟩ =
        some (compValAt itemBase U V w N n s.mem d) ∧
      compValAt itemBase U V w N n s.mem d < V := fun d hd => by
    have hd_tot : d < totalSlots N gm := hn ▸ hd
    obtain ⟨hb_lt, hj_lt, _⟩ := ownerBucketOfDense_lt_and_slotOf hslot htd hd_tot
    have hvirt_eq := physOfDense_eq_slotOf_owner hslot htd hd_tot
    set b := ownerBucketOfDense N gm dt d
    set j := logicalIdxOfDense N gm dt d
    have hj_lt' : j < bCount N (gmAt 0 U V wg N (hashSpace U wg N) s_fix.mem) b := by
      rw [hgm_eq]; exact hj_lt
    have hg_eq : slotOf N (gmAt 0 U V wg N (hashSpace U wg N) s_fix.mem) b j = slotOf N gm b j := by
      rw [hgm_eq]
    have hsp : (physByBase N (compGmAt metaBase U w N s.mem 0 * slabSize N)
        (compDTAt metaBase U w N s.mem) d) = physOfDense N gm dt d := rfl
    have haddr_eq : (physByBase N (compGmAt metaBase U w N s.mem 0 * slabSize N)
        (compDTAt metaBase U w N s.mem) d) =
        slotOf N (gmAt 0 U V wg N (hashSpace U wg N) s_fix.mem) b j := by
      rw [hsp, hvirt_eq, hg_eq]
    have hq_d : quotAt 0 U wg N (hashSpace U wg N) s_fix.mem
        (slotOf N (gmAt 0 U V wg N (hashSpace U wg N) s_fix.mem) b j) =
        compQuotAt itemBase U V w N n s.mem d := by
      have hq0 := hcpl.quot_eq d hd_tot
      change compQuotAt itemBase U V w N (epochTotalSlots N gm) s.mem d = _ at hq0
      rw [htot_eq] at hq0
      rw [← haddr_eq]
      exact hq0.symm
    have hv_d : valAt 0 U V wg N (hashSpace U wg N) s_fix.mem
        (slotOf N (gmAt 0 U V wg N (hashSpace U wg N) s_fix.mem) b j) =
        compValAt itemBase U V w N n s.mem d := by
      have hv0 := hcpl.val_eq d hd_tot
      change compValAt itemBase U V w N (epochTotalSlots N gm) s.mem d = _ at hv0
      rw [htot_eq] at hv0
      rw [← haddr_eq]
      exact hv0.symm
    have hmap := hbucket.hmap_some b hb_lt j hj_lt'
    rw [hq_d, hv_d] at hmap; unfold bucketMapOfState at hmap
    split_ifs at hmap with hcond
    exact ⟨hcond.1, hmap, hvals _ _ hmap⟩
  refine ⟨h1, fun d₁ hd₁ d₂ hd₂ heq => ?_, fun u hu => ?_⟩
  · have hd₁_tot : d₁ < totalSlots N gm := hn ▸ hd₁
    have hd₂_tot : d₂ < totalSlots N gm := hn ▸ hd₂
    obtain ⟨hb₁_lt, hj₁_lt, hd₁_eq⟩ := ownerBucketOfDense_lt_and_slotOf hslot htd hd₁_tot
    obtain ⟨hb₂_lt, hj₂_lt, hd₂_eq⟩ := ownerBucketOfDense_lt_and_slotOf hslot htd hd₂_tot
    have hvirt₁ := physOfDense_eq_slotOf_owner hslot htd hd₁_tot
    have hvirt₂ := physOfDense_eq_slotOf_owner hslot htd hd₂_tot
    set b₁ := ownerBucketOfDense N gm dt d₁
    set j₁ := logicalIdxOfDense N gm dt d₁
    set b₂ := ownerBucketOfDense N gm dt d₂
    set j₂ := logicalIdxOfDense N gm dt d₂
    have hfb₁ := feistelBucket_feistelReconstruct (hValOfSeed U N θ) hb₁_lt
      (compQuotAt itemBase U V w N n s.mem d₁)
    have hfb₂ := feistelBucket_feistelReconstruct (hValOfSeed U N θ) hb₂_lt
      (compQuotAt itemBase U V w N n s.mem d₂)
    change feistelReconstruct (bucketBits N) (hValOfSeed U N θ) b₁ _ =
      feistelReconstruct (bucketBits N) (hValOfSeed U N θ) b₂ _ at heq
    have hb_eq : b₁ = b₂ := by rw [← hfb₁.1, heq, hfb₂.1]
    have hq_eq : compQuotAt itemBase U V w N n s.mem d₁ =
        compQuotAt itemBase U V w N n s.mem d₂ := by rw [← hfb₁.2, heq, hfb₂.2]
    have hj₁_lt' : j₁ < bCount N (gmAt 0 U V wg N (hashSpace U wg N) s_fix.mem) b₁ := by
      rw [hgm_eq]; exact hj₁_lt
    have hj₂_lt' : j₂ < bCount N (gmAt 0 U V wg N (hashSpace U wg N) s_fix.mem) b₁ := by
      rw [hgm_eq, hb_eq]; exact hj₂_lt
    have hsp₁ : (physByBase N (compGmAt metaBase U w N s.mem 0 * slabSize N)
        (compDTAt metaBase U w N s.mem) d₁) = physOfDense N gm dt d₁ := rfl
    have hsp₂ : (physByBase N (compGmAt metaBase U w N s.mem 0 * slabSize N)
        (compDTAt metaBase U w N s.mem) d₂) = physOfDense N gm dt d₂ := rfl
    have haddr₁ : (physByBase N (compGmAt metaBase U w N s.mem 0 * slabSize N)
        (compDTAt metaBase U w N s.mem) d₁) =
        slotOf N (gmAt 0 U V wg N (hashSpace U wg N) s_fix.mem) b₁ j₁ := by
      rw [hsp₁, hvirt₁, hgm_eq]
    have haddr₂ : (physByBase N (compGmAt metaBase U w N s.mem 0 * slabSize N)
        (compDTAt metaBase U w N s.mem) d₂) =
        slotOf N (gmAt 0 U V wg N (hashSpace U wg N) s_fix.mem) b₁ j₂ := by
      rw [hsp₂, hvirt₂, hb_eq, hgm_eq]
    have hq₁ : quotAt 0 U wg N (hashSpace U wg N) s_fix.mem
        (slotOf N (gmAt 0 U V wg N (hashSpace U wg N) s_fix.mem) b₁ j₁) =
        compQuotAt itemBase U V w N n s.mem d₁ := by
      have hq0 := hcpl.quot_eq d₁ hd₁_tot
      change compQuotAt itemBase U V w N (epochTotalSlots N gm) s.mem d₁ = _ at hq0
      rw [htot_eq] at hq0
      rw [← haddr₁]
      exact hq0.symm
    have hq₂ : quotAt 0 U wg N (hashSpace U wg N) s_fix.mem
        (slotOf N (gmAt 0 U V wg N (hashSpace U wg N) s_fix.mem) b₁ j₂) =
        compQuotAt itemBase U V w N n s.mem d₂ := by
      have hq0 := hcpl.quot_eq d₂ hd₂_tot
      change compQuotAt itemBase U V w N (epochTotalSlots N gm) s.mem d₂ = _ at hq0
      rw [htot_eq] at hq0
      rw [← haddr₂]
      exact hq0.symm
    have hj_eq := hbucket.hnodup_q b₁ hb₁_lt j₁ hj₁_lt' j₂ hj₂_lt' (by rw [hq₁, hq₂, hq_eq])
    rw [← hd₁_eq, ← hd₂_eq, hb_eq, hj_eq]
  · set b := feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val
    set q := keyQuotient (bucketBits N) u.val
    have hb_lt : b < numBuckets N := feistelBucket_lt (bucketBits N) (hValOfSeed U N θ) u.val
    have hbm_eq := bucketMapOfState_feistelBucket hNU (hValOfSeed U N θ) s_abs u
    obtain ⟨j, hj_lt', hq_j⟩ := (hbucket.hmap_dom b hb_lt q).mp (by rwa [hbm_eq])
    have hj_lt : j < bCount N gm b := by rw [← hgm_eq]; exact hj_lt'
    obtain ⟨hd_lt, hb_inv, _⟩ := denseOfPhys_slotOf_lt_and_inv hslot htd hb_lt hj_lt
    have hvirt_inv := physOfDense_denseOfPhys_slotOf hslot htd hb_lt hj_lt
    set d := denseOfPhys N gm td (slotOf N gm b j)
    have hd_n : d < n := hn ▸ hd_lt
    refine ⟨d, hd_n, ?_⟩
    have hsp : (physByBase N (compGmAt metaBase U w N s.mem 0 * slabSize N)
        (compDTAt metaBase U w N s.mem) d) = physOfDense N gm dt d := rfl
    have hq_d : compQuotAt itemBase U V w N n s.mem d = q := by
      have hq0 := hcpl.quot_eq d hd_lt
      change compQuotAt itemBase U V w N (epochTotalSlots N gm) s.mem d = _ at hq0
      rw [htot_eq] at hq0
      rw [hq0, hsp, hvirt_inv, ← hgm_eq]
      exact hq_j
    unfold reconstructKeyAt; dsimp only
    rw [show ownerBucketOfDense N gm dt d = b from hb_inv, hq_d]
    exact feistelReconstruct_feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val

/-- Active compacted epoch invariant at arbitrary `(metaBase, itemBase)` (`s : Memory.State`). -/
structure CompactedSplitRep (metaBase itemBase U V w N n n_init : ℕ)
    (θ : QuotHashSeed U N) (s_abs : Dictionary.State U) (s : Memory.State) : Prop where
  root_hdr : RootHeaderValid U V w N n n_init metaBase s.mem
  params_stored : EpochParamsStored U V w N metaBase s.mem
  hash_rep : ReducedKWise.Rep (metaBase + epochHdrWords) w (qBits U N) (hashB N)
    (totalMicroBits N) 3 θ s.mem
  card_eq : (Dictionary.dom s_abs).card = n
  vals_lt : Dictionary.ValuesBounded V s_abs
  coupled : ∃ s_fix : Memory.State,
    DictStateInv U V (ghostW w) N 0 θ s_abs s_fix ∧
    totalSlots N (compGmAt metaBase U w N s.mem) = n ∧
    FixedCoupled metaBase itemBase U V w N s_fix s

/-- Live resting representation invariant on `RData r` (`metaBase = base`, exact `x.frontier`). -/
structure CompactedRep {r : ℕ} (U V w N n n_init base : ℕ)
    (s_abs : Dictionary.State U) (x : RData r) : Prop where
  bounded : x.Bounded w
  frontier_eq : x.frontier = base + compactedEpochWords U V w N n
  root_hdr : RootHeaderValid U V w N n n_init base x.mem
  fits_U : Fits w U
  pos_U : 0 < U
  pos_V : 0 < V
  card_eq : (Dictionary.dom s_abs).card = n
  vals_lt : Dictionary.ValuesBounded V s_abs
  epoch_inv : EpochValid U n N
  active_inv : 0 < n → ∃ θ : QuotHashSeed U N,
    CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
      ⟨x.mem, x.frontier⟩

/-- An empty dictionary state (`n = 0`, `N = 0`) satisfies `CompactedRep`. -/
theorem compactedRep_empty {r : ℕ} {U V w base : ℕ} {x : RData r}
    (hx : x.Bounded w) (hfr : x.frontier = base + 8)
    (hhdr : RootHeaderValid U V w 0 0 0 base x.mem) :
    CompactedRep U V w 0 0 0 base (Dictionary.empty U) x := by
  refine ⟨hx, ?_, hhdr, hhdr.fits_U, hhdr.pos_U, hhdr.pos_V, ?_, ?_, Or.inl ⟨rfl, rfl⟩,
    fun hn0 => (Nat.not_lt_zero 0 hn0).elim⟩
  · unfold compactedEpochWords rootHdrWords; rw [hfr]; simp
  · simp only [Dictionary.dom_empty, Finset.card_empty]
  · intro u v hsome; cases hsome

/-- An active compacted epoch split representation yields a resting `CompactedRep`. -/
theorem compactedRep_of_split {r : ℕ} {U V w N n n_init base : ℕ} {θ : QuotHashSeed U N}
    {s_abs : Dictionary.State U} {x : RData r}
    (hx : x.Bounded w)
    (hfr : x.frontier = base + compactedEpochWords U V w N n)
    (hepoch : EpochValid U n N)
    (hsplit : CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
      ⟨x.mem, x.frontier⟩) :
    CompactedRep U V w N n n_init base s_abs x :=
  ⟨hx, hfr, hsplit.root_hdr, hsplit.root_hdr.fits_U, hsplit.root_hdr.pos_U, hsplit.root_hdr.pos_V,
    hsplit.card_eq, hsplit.vals_lt, hepoch, fun _ => ⟨θ, hsplit⟩⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

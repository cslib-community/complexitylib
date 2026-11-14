/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.WindowOps
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctHash

/-!
# Metadata Frame Laws, Circular-Window Effects, and Compacted Slot Resolution

This module connects the low-level `Memory.Prog` primitives in `WindowOps.lean` to the pure
metadata and circular-window invariants in `Compaction.lean` and `SuccinctHash.lean`:
* cross-region non-interference and `Function.update` laws for `compLmAt`, `compGmAt`, `compTDAt`,
  `compDTAt`, `compQuotAt`, and `compValAt`;
* state-transition specifications for `winGrowRightGenProg`, `winGrowLeftGenProg`,
  `winShrinkRightGenProg`, and `winShrinkLeftGenProg`;
* register-width bounds `fits_mkCompParams` and `fits_const_of_compMetaEnv`;
* compacted slot-resolution and owner-bucket recovery operations (`readCompBucketCountGenProg`,
  `recoverOwnerBucketGenProg`) and bijection `reconstructKeyAt_spec`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.readCompBucketCountGenProg`,
  `recoverOwnerBucketGenProg`: compacted metadata accessors.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.reconstructKeyAt`:
  mathematical key reconstruction at dense index `d < n`.

## Main results

* `winGrowRightGenProg_effect`, `winGrowLeftGenProg_effect`, `winShrinkRightGenProg_effect`,
  `winShrinkLeftGenProg_effect`: circular-window effect laws on `Memory.State`.
* `fits_mkCompParams`: all 36 words of `mkCompParams U V w N` fit in `w` bits.
* `reconstructKeyAt_spec`: dense slots `[0, n)` reconstruct `s_abs` bijectively.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4][BenderFarachColtonKuszmaulKuszmaul2024]
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

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: Cross-Region Congruence and Pure `Function.update` Frame Laws -/

theorem compLmAt_congr {metaBase U w N : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ}
    (h : ∀ addr, metaBase + offCompLM U w N ≤ addr ∧ addr < metaBase + offCompGM U w N →
      mem₁ addr = mem₂ addr) :
    compLmAt metaBase U w N mem₁ = compLmAt metaBase U w N mem₂ := by
  funext ⟨c, idx⟩
  unfold compLmAt; dsimp only
  split_ifs with hc
  · refine readPacked_congr hw (fun addr haddr => h addr ?_) hc.2
    have hmul : (c + 1) * lmSubWords N w ≤ 9 * lmSubWords N w :=
      Nat.mul_le_mul_right _ hc.1
    rw [Nat.add_one_mul] at hmul
    unfold offCompGM offCompLMSub lmSubWords at *
    omega
  · rfl

theorem compGmAt_congr {metaBase U w N : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ}
    (h : ∀ addr, metaBase + offCompGM U w N ≤ addr ∧ addr < metaBase + offTailToDense U w N →
      mem₁ addr = mem₂ addr) :
    compGmAt metaBase U w N mem₁ = compGmAt metaBase U w N mem₂ := by
  funext idx
  unfold compGmAt
  split_ifs with hidx
  · refine readPacked_congr hw (fun addr haddr => h addr ?_) hidx
    unfold offTailToDense at *; omega
  · rfl

theorem compTDAt_congr {metaBase U w N : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ}
    (h : ∀ addr, metaBase + offTailToDense U w N ≤ addr ∧ addr < metaBase + offDenseToTail U w N →
      mem₁ addr = mem₂ addr) :
    compTDAt metaBase U w N mem₁ = compTDAt metaBase U w N mem₂ := by
  funext t
  unfold compTDAt
  split_ifs with ht
  · refine readPacked_congr hw (fun addr haddr => h addr ?_) ht
    unfold offDenseToTail at *; omega
  · rfl

theorem compDTAt_congr {metaBase U w N : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ}
    (h : ∀ addr, metaBase + offDenseToTail U w N ≤ addr ∧ addr < metaBase + offCompItems U w N →
      mem₁ addr = mem₂ addr) :
    compDTAt metaBase U w N mem₁ = compDTAt metaBase U w N mem₂ := by
  funext r
  unfold compDTAt
  split_ifs with hr
  · refine readPacked_congr hw (fun addr haddr => h addr ?_) hr
    unfold offCompItems at *; omega
  · rfl

/-- Updating `LocalMeta[c, idx] := val` updates `compLmAt` via `Function.update` and preserves
all other metadata views, dense item views (`metaBase + offCompItems ≤ itemBase`), and outside
memory. -/
theorem writeCompLM_effect {metaBase itemBase U V w N m_items idx val : ℕ} (c : Fin 9)
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hidx : idx < totalMicroBuckets N) (hval : val < 2 ^ effBucketPosBits N) (mem : ℕ → ℕ) :
    let mem' := writePacked (metaBase + offCompLMSub U w N c.val)
      (effBucketPosBits N) w mem idx val
    compLmAt metaBase U w N mem' = Function.update (compLmAt metaBase U w N mem) (c.val, idx) val ∧
    compGmAt metaBase U w N mem' = compGmAt metaBase U w N mem ∧
    compTDAt metaBase U w N mem' = compTDAt metaBase U w N mem ∧
    compDTAt metaBase U w N mem' = compDTAt metaBase U w N mem ∧
    compQuotAt itemBase U V w N m_items mem' = compQuotAt itemBase U V w N m_items mem ∧
    compValAt itemBase U V w N m_items mem' = compValAt itemBase U V w N m_items mem ∧
    (∀ a, ¬(metaBase + offCompLM U w N ≤ a ∧ a < metaBase + offCompGM U w N) →
      mem' a = mem a) := by
  intro mem'
  have hout : ∀ a, ¬(metaBase + offCompLM U w N ≤ a ∧ a < metaBase + offCompGM U w N) →
      mem' a = mem a := fun a ha => by
    refine writePacked_outside hw mem hidx val (fun hin => ha ?_)
    have hmul : (c.val + 1) * lmSubWords N w ≤ 9 * lmSubWords N w :=
      Nat.mul_le_mul_right _ c.isLt
    rw [Nat.add_one_mul] at hmul
    unfold offCompGM offCompLMSub lmSubWords at *; omega
  have hlm : compLmAt metaBase U w N mem' =
      Function.update (compLmAt metaBase U w N mem) (c.val, idx) val := by
    funext ⟨c', idx'⟩
    by_cases hci : (c', idx') = (c.val, idx)
    · injection hci with hc_eq hidx_eq; subst hc_eq hidx_eq
      rw [Function.update_self]
      unfold compLmAt; simp only [c.isLt, hidx, and_self, ↓reduceIte]
      exact readPacked_writePacked_self _ _ _ _ _ hval
    · rw [Function.update_of_ne hci]
      unfold compLmAt; dsimp only
      split_ifs with hc'
      · by_cases hce : c' = c.val
        · subst hce
          exact readPacked_writePacked_of_ne hw mem (fun h => hci (Prod.ext rfl h)) val
        · refine readPacked_congr hw (fun addr haddr => ?_) hc'.2
          refine writePacked_outside hw mem hidx val (fun hin => ?_)
          rcases lt_or_gt_of_ne hce with hlt | hgt
          · have hmul := Nat.mul_le_mul_right (lmSubWords N w) hlt
            rw [Nat.add_one_mul] at hmul
            unfold offCompLMSub lmSubWords at *; omega
          · have hmul := Nat.mul_le_mul_right (lmSubWords N w) hgt
            rw [Nat.add_one_mul] at hmul
            unfold offCompLMSub lmSubWords at *; omega
      · rfl
  have h1 : offCompGM U w N ≤ offTailToDense U w N := Nat.le_add_right _ _
  have h2 : offTailToDense U w N ≤ offDenseToTail U w N := Nat.le_add_right _ _
  have h3 : offDenseToTail U w N ≤ offCompItems U w N := Nat.le_add_right _ _
  exact ⟨hlm,
    compGmAt_congr hw (fun a ha => hout a (by omega)),
    compTDAt_congr hw (fun a ha => hout a (by omega)),
    compDTAt_congr hw (fun a ha => hout a (by omega)),
    compQuotAt_congr hw (fun a ha => hout a (by omega)),
    compValAt_congr hw (fun a ha => hout a (by omega)),
    hout⟩

/-- Updating `GlobalMeta[idx] := val` updates `compGmAt` via `Function.update` and preserves all
other views and outside memory. -/
theorem writeCompGM_effect {metaBase itemBase U V w N m_items idx val : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hidx : idx < globalMetaLen N) (hval : val < 2 ^ globalPtrBits N) (mem : ℕ → ℕ) :
    let mem' := writePacked (metaBase + offCompGM U w N) (globalPtrBits N) w mem idx val
    compGmAt metaBase U w N mem' = Function.update (compGmAt metaBase U w N mem) idx val ∧
    compLmAt metaBase U w N mem' = compLmAt metaBase U w N mem ∧
    compTDAt metaBase U w N mem' = compTDAt metaBase U w N mem ∧
    compDTAt metaBase U w N mem' = compDTAt metaBase U w N mem ∧
    compQuotAt itemBase U V w N m_items mem' = compQuotAt itemBase U V w N m_items mem ∧
    compValAt itemBase U V w N m_items mem' = compValAt itemBase U V w N m_items mem ∧
    (∀ a, ¬(metaBase + offCompGM U w N ≤ a ∧ a < metaBase + offTailToDense U w N) →
      mem' a = mem a) := by
  intro mem'
  have hout : ∀ a, ¬(metaBase + offCompGM U w N ≤ a ∧ a < metaBase + offTailToDense U w N) →
      mem' a = mem a := fun a ha =>
    writePacked_outside hw mem hidx val (fun hin => ha (by unfold offTailToDense; omega))
  have hgm : compGmAt metaBase U w N mem' =
      Function.update (compGmAt metaBase U w N mem) idx val := by
    funext idx'
    by_cases heq : idx' = idx
    · subst heq; rw [Function.update_self]; unfold compGmAt; simp only [hidx, ↓reduceIte]
      exact readPacked_writePacked_self _ _ _ _ _ hval
    · rw [Function.update_of_ne heq]; unfold compGmAt; split_ifs with hlt
      · exact readPacked_writePacked_of_ne hw mem heq val
      · rfl
  have h0 : offCompLM U w N ≤ offCompGM U w N := Nat.le_add_right _ _
  have h2 : offTailToDense U w N ≤ offDenseToTail U w N := Nat.le_add_right _ _
  have h3 : offDenseToTail U w N ≤ offCompItems U w N := Nat.le_add_right _ _
  exact ⟨hgm,
    compLmAt_congr hw (fun a ha => hout a (by omega)),
    compTDAt_congr hw (fun a ha => hout a (by omega)),
    compDTAt_congr hw (fun a ha => hout a (by omega)),
    compQuotAt_congr hw (fun a ha => hout a (by omega)),
    compValAt_congr hw (fun a ha => hout a (by omega)),
    hout⟩
/-- Updating `TailToDense[t] := val` updates `compTDAt` via `Function.update` and preserves all
other views and outside memory. -/
theorem writeCompTD_effect {metaBase itemBase U V w N m_items t val : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (ht : t < maxTailItems N) (hval : val < 2 ^ globalPtrBits N) (mem : ℕ → ℕ) :
    let mem' := writePacked (metaBase + offTailToDense U w N) (globalPtrBits N) w mem t val
    compTDAt metaBase U w N mem' = Function.update (compTDAt metaBase U w N mem) t val ∧
    compLmAt metaBase U w N mem' = compLmAt metaBase U w N mem ∧
    compGmAt metaBase U w N mem' = compGmAt metaBase U w N mem ∧
    compDTAt metaBase U w N mem' = compDTAt metaBase U w N mem ∧
    compQuotAt itemBase U V w N m_items mem' = compQuotAt itemBase U V w N m_items mem ∧
    compValAt itemBase U V w N m_items mem' = compValAt itemBase U V w N m_items mem ∧
    (∀ a, ¬(metaBase + offTailToDense U w N ≤ a ∧ a < metaBase + offDenseToTail U w N) →
      mem' a = mem a) := by
  intro mem'
  have hout : ∀ a, ¬(metaBase + offTailToDense U w N ≤ a ∧ a < metaBase + offDenseToTail U w N) →
      mem' a = mem a := fun a ha =>
    writePacked_outside hw mem ht val (fun hin => ha (by unfold offDenseToTail; omega))
  have htd : compTDAt metaBase U w N mem' =
      Function.update (compTDAt metaBase U w N mem) t val := by
    funext t'
    by_cases heq : t' = t
    · subst heq; rw [Function.update_self]; unfold compTDAt; simp only [ht, ↓reduceIte]
      exact readPacked_writePacked_self _ _ _ _ _ hval
    · rw [Function.update_of_ne heq]; unfold compTDAt; split_ifs with hlt
      · exact readPacked_writePacked_of_ne hw mem heq val
      · rfl
  have h0 : offCompLM U w N ≤ offCompGM U w N := Nat.le_add_right _ _
  have h1 : offCompGM U w N ≤ offTailToDense U w N := Nat.le_add_right _ _
  have h3 : offDenseToTail U w N ≤ offCompItems U w N := Nat.le_add_right _ _
  exact ⟨htd,
    compLmAt_congr hw (fun a ha => hout a (by omega)),
    compGmAt_congr hw (fun a ha => hout a (by omega)),
    compDTAt_congr hw (fun a ha => hout a (by omega)),
    compQuotAt_congr hw (fun a ha => hout a (by omega)),
    compValAt_congr hw (fun a ha => hout a (by omega)),
    hout⟩

/-- Updating `DenseToTail[r] := val` updates `compDTAt` via `Function.update` and preserves all
other views and outside memory. -/
theorem writeCompDT_effect {metaBase itemBase U V w N m_items r val : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hr : r < maxTailItems N) (hval : val < 2 ^ globalPtrBits N) (mem : ℕ → ℕ) :
    let mem' := writePacked (metaBase + offDenseToTail U w N) (globalPtrBits N) w mem r val
    compDTAt metaBase U w N mem' = Function.update (compDTAt metaBase U w N mem) r val ∧
    compLmAt metaBase U w N mem' = compLmAt metaBase U w N mem ∧
    compGmAt metaBase U w N mem' = compGmAt metaBase U w N mem ∧
    compTDAt metaBase U w N mem' = compTDAt metaBase U w N mem ∧
    compQuotAt itemBase U V w N m_items mem' = compQuotAt itemBase U V w N m_items mem ∧
    compValAt itemBase U V w N m_items mem' = compValAt itemBase U V w N m_items mem ∧
    (∀ a, ¬(metaBase + offDenseToTail U w N ≤ a ∧ a < metaBase + offCompItems U w N) →
      mem' a = mem a) := by
  intro mem'
  have hout : ∀ a, ¬(metaBase + offDenseToTail U w N ≤ a ∧ a < metaBase + offCompItems U w N) →
      mem' a = mem a := fun a ha =>
    writePacked_outside hw mem hr val (fun hin => ha (by unfold offCompItems; omega))
  have hdt : compDTAt metaBase U w N mem' =
      Function.update (compDTAt metaBase U w N mem) r val := by
    funext r'
    by_cases heq : r' = r
    · subst heq; rw [Function.update_self]; unfold compDTAt; simp only [hr, ↓reduceIte]
      exact readPacked_writePacked_self _ _ _ _ _ hval
    · rw [Function.update_of_ne heq]; unfold compDTAt; split_ifs with hlt
      · exact readPacked_writePacked_of_ne hw mem heq val
      · rfl
  have h0 : offCompLM U w N ≤ offCompGM U w N := Nat.le_add_right _ _
  have h1 : offCompGM U w N ≤ offTailToDense U w N := Nat.le_add_right _ _
  have h2 : offTailToDense U w N ≤ offDenseToTail U w N := Nat.le_add_right _ _
  exact ⟨hdt,
    compLmAt_congr hw (fun a ha => hout a (by omega)),
    compGmAt_congr hw (fun a ha => hout a (by omega)),
    compTDAt_congr hw (fun a ha => hout a (by omega)),
    compQuotAt_congr hw (fun a ha => hout a (by omega)),
    compValAt_congr hw (fun a ha => hout a (by omega)),
    hout⟩

/-- Writing a dense quotient at `itemBase` (`metaBase + offCompItems ≤ itemBase`) preserves all
metadata views at `metaBase`. -/
theorem writeCompQuot_meta_frame {metaBase itemBase U V w N m_items d q : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase) (hd : d < m_items)
    (mem : ℕ → ℕ) :
    let mem' := writeCompQuot itemBase U V w N mem d q
    compLmAt metaBase U w N mem' = compLmAt metaBase U w N mem ∧
    compGmAt metaBase U w N mem' = compGmAt metaBase U w N mem ∧
    compTDAt metaBase U w N mem' = compTDAt metaBase U w N mem ∧
    compDTAt metaBase U w N mem' = compDTAt metaBase U w N mem := by
  intro mem'
  have h0 : offCompLM U w N ≤ offCompGM U w N := Nat.le_add_right _ _
  have h1 : offCompGM U w N ≤ offTailToDense U w N := Nat.le_add_right _ _
  have h2 : offTailToDense U w N ≤ offDenseToTail U w N := Nat.le_add_right _ _
  have h3 : offDenseToTail U w N ≤ offCompItems U w N := Nat.le_add_right _ _
  exact ⟨compLmAt_congr hw (fun a ha => writeCompQuot_outside hw hd mem (by omega)),
    compGmAt_congr hw (fun a ha => writeCompQuot_outside hw hd mem (by omega)),
    compTDAt_congr hw (fun a ha => writeCompQuot_outside hw hd mem (by omega)),
    compDTAt_congr hw (fun a ha => writeCompQuot_outside hw hd mem (by omega))⟩

/-- Writing a dense value at `itemBase` (`metaBase + offCompItems ≤ itemBase`) preserves all
metadata views at `metaBase`. -/
theorem writeCompVal_meta_frame {metaBase itemBase U V w N m_items d v : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase) (hd : d < m_items)
    (mem : ℕ → ℕ) :
    let mem' := writeCompVal itemBase U V w N mem d v
    compLmAt metaBase U w N mem' = compLmAt metaBase U w N mem ∧
    compGmAt metaBase U w N mem' = compGmAt metaBase U w N mem ∧
    compTDAt metaBase U w N mem' = compTDAt metaBase U w N mem ∧
    compDTAt metaBase U w N mem' = compDTAt metaBase U w N mem := by
  intro mem'
  have h0 : offCompLM U w N ≤ offCompGM U w N := Nat.le_add_right _ _
  have h1 : offCompGM U w N ≤ offTailToDense U w N := Nat.le_add_right _ _
  have h2 : offTailToDense U w N ≤ offDenseToTail U w N := Nat.le_add_right _ _
  have h3 : offDenseToTail U w N ≤ offCompItems U w N := Nat.le_add_right _ _
  exact ⟨compLmAt_congr hw (fun a ha => writeCompVal_outside hw hd mem (by omega)),
    compGmAt_congr hw (fun a ha => writeCompVal_outside hw hd mem (by omega)),
    compTDAt_congr hw (fun a ha => writeCompVal_outside hw hd mem (by omega)),
    compDTAt_congr hw (fun a ha => writeCompVal_outside hw hd mem (by omega))⟩

/-! ## Section 2: Circular-Window State-Transition Specifications -/

private theorem lt_two_pow_globalPtrBits_of_lt_maxTail {N x : ℕ} (hx : x < maxTailItems N) :
    x < 2 ^ globalPtrBits N := by
  have hM : maxTailItems N ≤ N := maxTailItems_le_of_pos (by omega)
  exact lt_two_pow_globalPtrBits_of_le_n_max (by omega)

private theorem winUpdatePair_effect_core {metaBase itemBase U V w N m_items t c : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (ht : t < maxTailItems N) (hc : c < maxTailItems N) (s : Memory.State) :
    let mem₁ := writePacked (metaBase + offTailToDense U w N) (globalPtrBits N) w s.mem t c
    let mem₂ := writePacked (metaBase + offDenseToTail U w N) (globalPtrBits N) w mem₁ c t
    compTDAt metaBase U w N mem₂ = Function.update (compTDAt metaBase U w N s.mem) t c ∧
    compDTAt metaBase U w N mem₂ =
      Function.update (compDTAt metaBase U w N s.mem) c t ∧
    compLmAt metaBase U w N mem₂ = compLmAt metaBase U w N s.mem ∧
    compGmAt metaBase U w N mem₂ = compGmAt metaBase U w N s.mem ∧
    compQuotAt itemBase U V w N m_items mem₂ = compQuotAt itemBase U V w N m_items s.mem ∧
    compValAt itemBase U V w N m_items mem₂ = compValAt itemBase U V w N m_items s.mem ∧
    (∀ a, ¬(metaBase + offTailToDense U w N ≤ a ∧ a < metaBase + offCompItems U w N) →
      mem₂ a = s.mem a) := by
  intro mem₁ mem₂
  have hc_pow := lt_two_pow_globalPtrBits_of_lt_maxTail hc
  have ht_pow := lt_two_pow_globalPtrBits_of_lt_maxTail ht
  obtain ⟨htd1, hlm1, hgm1, hdt1, hq1, hv1, hout1⟩ :=
    writeCompTD_effect (itemBase := itemBase) (U := U) (V := V) (m_items := m_items)
      hw hitem ht hc_pow s.mem
  obtain ⟨hdt2, hlm2, hgm2, htd2, hq2, hv2, hout2⟩ :=
    writeCompDT_effect (itemBase := itemBase) (U := U) (V := V) (m_items := m_items)
      hw hitem hc ht_pow mem₁
  have htd_le : offTailToDense U w N ≤ offDenseToTail U w N := Nat.le_add_right _ _
  have hdt_le : offDenseToTail U w N ≤ offCompItems U w N := Nat.le_add_right _ _
  exact ⟨htd2.trans htd1, hdt2.trans (congrArg (fun f => Function.update f c t) hdt1),
    hlm2.trans hlm1, hgm2.trans hgm1, hq2.trans hq1, hv2.trans hv1,
    fun a ha => (hout2 a (by omega)).trans (hout1 a (by omega))⟩

theorem winGrowRightGenProg_effect {metaBase itemBase U V w N m_items b_win n_win : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hn : n_win < maxTailItems N) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s
      (winGrowRightGenProg ((mkCompParams U V w N, metaBase), (b_win, n_win)))
    s'.frontier = s.frontier ∧
    compTDAt metaBase U w N s'.mem =
      (winGrowRight (maxTailItems N) b_win n_win
        (compTDAt metaBase U w N s.mem, compDTAt metaBase U w N s.mem)).1 ∧
    compDTAt metaBase U w N s'.mem =
      (winGrowRight (maxTailItems N) b_win n_win
        (compTDAt metaBase U w N s.mem, compDTAt metaBase U w N s.mem)).2 ∧
    compLmAt metaBase U w N s'.mem = compLmAt metaBase U w N s.mem ∧
    compGmAt metaBase U w N s'.mem = compGmAt metaBase U w N s.mem ∧
    compQuotAt itemBase U V w N m_items s'.mem = compQuotAt itemBase U V w N m_items s.mem ∧
    compValAt itemBase U V w N m_items s'.mem = compValAt itemBase U V w N m_items s.mem ∧
    (∀ a, ¬(metaBase + offTailToDense U w N ≤ a ∧ a < metaBase + offCompItems U w N) →
      s'.mem a = s.mem a) := by
  intro s'
  have hM_pos : 0 < maxTailItems N := by omega
  set c := (b_win + n_win) % maxTailItems N
  have hc_lt : c < maxTailItems N := Nat.mod_lt _ hM_pos
  have hs' := clientState_winGrowRightGenProg U V w N metaBase b_win n_win s
  have hcore := winUpdatePair_effect_core
    (itemBase := itemBase) (U := U) (V := V) (m_items := m_items)
    hw hitem hn hc_lt s
  dsimp only [s']; rw [hs']; dsimp only [winGrowRight]
  exact ⟨rfl, hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2.1,
    hcore.2.2.2.2.2.1, hcore.2.2.2.2.2.2⟩

theorem winGrowLeftGenProg_effect {metaBase itemBase U V w N m_items b_win n_win : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hn : n_win < maxTailItems N) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s
      (winGrowLeftGenProg ((mkCompParams U V w N, metaBase), (b_win, n_win)))
    s'.frontier = s.frontier ∧
    compTDAt metaBase U w N s'.mem =
      (winGrowLeft (maxTailItems N) b_win n_win
        (compTDAt metaBase U w N s.mem, compDTAt metaBase U w N s.mem)).1 ∧
    compDTAt metaBase U w N s'.mem =
      (winGrowLeft (maxTailItems N) b_win n_win
        (compTDAt metaBase U w N s.mem, compDTAt metaBase U w N s.mem)).2 ∧
    compLmAt metaBase U w N s'.mem = compLmAt metaBase U w N s.mem ∧
    compGmAt metaBase U w N s'.mem = compGmAt metaBase U w N s.mem ∧
    compQuotAt itemBase U V w N m_items s'.mem = compQuotAt itemBase U V w N m_items s.mem ∧
    compValAt itemBase U V w N m_items s'.mem = compValAt itemBase U V w N m_items s.mem ∧
    (∀ a, ¬(metaBase + offTailToDense U w N ≤ a ∧ a < metaBase + offCompItems U w N) →
      s'.mem a = s.mem a) := by
  intro s'
  have hM_pos : 0 < maxTailItems N := by omega
  set c := b_win % maxTailItems N
  have hc_lt : c < maxTailItems N := Nat.mod_lt _ hM_pos
  have hs' := clientState_winGrowLeftGenProg U V w N metaBase b_win n_win s
  have hcore := winUpdatePair_effect_core
    (itemBase := itemBase) (U := U) (V := V) (m_items := m_items)
    hw hitem hn hc_lt s
  dsimp only [s']; rw [hs']; dsimp only [winGrowLeft]
  exact ⟨rfl, hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2.1,
    hcore.2.2.2.2.2.1, hcore.2.2.2.2.2.2⟩

theorem winShrinkRightGenProg_effect {metaBase itemBase U V w N m_items b_win n_win : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hn : n_win < maxTailItems N)
    (s : Memory.State)
    (hdt_lt : compDTAt metaBase U w N s.mem ((b_win + n_win) % maxTailItems N) < maxTailItems N)
    (htd_lt : compTDAt metaBase U w N s.mem n_win < maxTailItems N) :
    let s' := (Memory.spec 0).clientState s
      (winShrinkRightGenProg ((mkCompParams U V w N, metaBase), (b_win, n_win)))
    s'.frontier = s.frontier ∧
    compTDAt metaBase U w N s'.mem =
      (winShrinkRight (maxTailItems N) b_win n_win
        (compTDAt metaBase U w N s.mem, compDTAt metaBase U w N s.mem)).1 ∧
    compDTAt metaBase U w N s'.mem =
      (winShrinkRight (maxTailItems N) b_win n_win
        (compTDAt metaBase U w N s.mem, compDTAt metaBase U w N s.mem)).2 ∧
    compLmAt metaBase U w N s'.mem = compLmAt metaBase U w N s.mem ∧
    compGmAt metaBase U w N s'.mem = compGmAt metaBase U w N s.mem ∧
    compQuotAt itemBase U V w N m_items s'.mem = compQuotAt itemBase U V w N m_items s.mem ∧
    compValAt itemBase U V w N m_items s'.mem = compValAt itemBase U V w N m_items s.mem ∧
    (∀ a, ¬(metaBase + offTailToDense U w N ≤ a ∧ a < metaBase + offCompItems U w N) →
      s'.mem a = s.mem a) := by
  intro s'
  have hM_pos : 0 < maxTailItems N := by omega
  have hc_lt : (b_win + n_win) % maxTailItems N < maxTailItems N := Nat.mod_lt _ hM_pos
  set t_rem := compDTAt metaBase U w N s.mem ((b_win + n_win) % maxTailItems N)
  set c_last := compTDAt metaBase U w N s.mem n_win
  have hs' := clientState_winShrinkRightGenProg (U := U) (V := V) (w := w) (metaBase := metaBase)
    (s := s) hc_lt hn
  have hcore := winUpdatePair_effect_core
    (itemBase := itemBase) (U := U) (V := V) (m_items := m_items)
    hw hitem hdt_lt htd_lt s
  dsimp only [s']; rw [hs']; dsimp only [winShrinkRight]
  exact ⟨rfl, hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2.1,
    hcore.2.2.2.2.2.1, hcore.2.2.2.2.2.2⟩

theorem winShrinkLeftGenProg_effect {metaBase itemBase U V w N m_items b_win n_win : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hn : n_win < maxTailItems N)
    (s : Memory.State)
    (hdt_lt : compDTAt metaBase U w N s.mem (b_win % maxTailItems N) < maxTailItems N)
    (htd_lt : compTDAt metaBase U w N s.mem n_win < maxTailItems N) :
    let s' := (Memory.spec 0).clientState s
      (winShrinkLeftGenProg ((mkCompParams U V w N, metaBase), (b_win, n_win)))
    s'.frontier = s.frontier ∧
    compTDAt metaBase U w N s'.mem =
      (winShrinkLeft (maxTailItems N) b_win n_win
        (compTDAt metaBase U w N s.mem, compDTAt metaBase U w N s.mem)).1 ∧
    compDTAt metaBase U w N s'.mem =
      (winShrinkLeft (maxTailItems N) b_win n_win
        (compTDAt metaBase U w N s.mem, compDTAt metaBase U w N s.mem)).2 ∧
    compLmAt metaBase U w N s'.mem = compLmAt metaBase U w N s.mem ∧
    compGmAt metaBase U w N s'.mem = compGmAt metaBase U w N s.mem ∧
    compQuotAt itemBase U V w N m_items s'.mem = compQuotAt itemBase U V w N m_items s.mem ∧
    compValAt itemBase U V w N m_items s'.mem = compValAt itemBase U V w N m_items s.mem ∧
    (∀ a, ¬(metaBase + offTailToDense U w N ≤ a ∧ a < metaBase + offCompItems U w N) →
      s'.mem a = s.mem a) := by
  intro s'
  have hM_pos : 0 < maxTailItems N := by omega
  have hc_lt : b_win % maxTailItems N < maxTailItems N := Nat.mod_lt _ hM_pos
  set t_rem := compDTAt metaBase U w N s.mem (b_win % maxTailItems N)
  set c_last := compTDAt metaBase U w N s.mem n_win
  have hs' := clientState_winShrinkLeftGenProg (U := U) (V := V) (w := w) (metaBase := metaBase)
    (s := s) hc_lt hn
  have hcore := winUpdatePair_effect_core
    (itemBase := itemBase) (U := U) (V := V) (m_items := m_items)
    hw hitem hdt_lt htd_lt s
  dsimp only [s']; rw [hs']; dsimp only [winShrinkLeft]
  exact ⟨rfl, hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2.1,
    hcore.2.2.2.2.2.1, hcore.2.2.2.2.2.2⟩
/-! ## Section 3: Register-Width Bounds (`fits_mkCompParams`) -/

theorem fits_const_of_offCompItems {U w N metaBase c : ℕ}
    (hfit : Fits w (metaBase + offCompItems U w N)) (hc : c ≤ 225) : Fits w c := by
  refine lt_of_le_of_lt ?_ hfit
  unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega
theorem fits_of_le_max_N_one {U w N x : ℕ} (hw : 0 < w) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hx : x ≤ max N 1) : Fits w x :=
  (max_n_one_lt_two_pow_w hw hnU hU).of_le hx
theorem fits_of_le_globalMetaLen_comp {U w N x : ℕ} (hb_pos : 0 < bucketBits N)
    (hw : 0 < w) (hnU : N ≤ U) (hU : U < 2 ^ w) (hx : x ≤ globalMetaLen N) : Fits w x := by
  have hmax := max_n_one_lt_two_pow_w hw hnU hU
  have hlen := globalMetaLen_le_of_bucketBits_pos hb_pos
  exact hmax.of_le (by omega)

/-- Every entry of `mkCompParams U V w N` fits in a `w`-bit word whenever `0 < w`, `0 < N`,
`N ≤ U < 2 ^ w`, `V ≤ 2 ^ w`, and `Fits w (metaBase + offCompItems U w N)`. -/
theorem fits_mkCompParams {U V w N metaBase : ℕ}
    (hw : 0 < w) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hfit : Fits w (metaBase + offCompItems U w N)) (i : Fin 36) :
    Fits w (mkCompParams U V w N i) := by
  have hoff : Fits w (offCompItems U w N) := lt_of_le_of_lt (Nat.le_add_left _ _) hfit
  have hw_fit : Fits w w := Nat.lt_two_pow_self
  have hmax_fit : Fits w (max N 1) := max_n_one_lt_two_pow_w hw hnU hU
  have h2b_le : 2 ^ bucketBits N ≤ max N 1 :=
    (Nat.pow_le_pow_right two_pos (bucketBits_le_totalMicroBits N)).trans (totalMicroBuckets_le N)
  have h2b_fit : Fits w (2 ^ bucketBits N) := hmax_fit.of_le h2b_le
  have hslab_fit : Fits w (slabSize N) := hmax_fit.of_le (slabSize_le_max_n_one N)
  have h2slab_fit : Fits w (2 * slabSize N) := by
    rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
    · have h1 : slabSize N = 1 := by simp [slabSize, slabBits, hb0]
      rw [h1]; exact fits_const_of_offCompItems hfit (by decide)
    · have hcube := numBuckets_mul_slabScale_cubed_le hb_pos
      have hK := (slabSize_eq_sq_of_pos hb_pos).1
      have hB := numBuckets_pos N
      have hS := two_le_slabScale N
      have hle : 2 * slabSize N ≤ numBuckets N * (slabScale N) ^ 3 := by
        rw [hK]
        calc 2 * (slabScale N) ^ 2 = 1 * ((slabScale N) ^ 2 * 2) := by ring
          _ ≤ numBuckets N * ((slabScale N) ^ 2 * slabScale N) :=
            Nat.mul_le_mul hB (Nat.mul_le_mul_left _ hS)
          _ = numBuckets N * (slabScale N) ^ 3 := by ring
      exact hmax_fit.of_le (by omega)
  have hdir_fit : Fits w (dirSlabsPerBucket N) := by
    rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
    · simp only [dirSlabsPerBucket, hb0, ↓reduceIte]
      exact fits_const_of_offCompItems hfit (by decide)
    · exact fits_of_le_globalMetaLen_comp hb_pos hw hnU hU
        (dirSlabsPerBucket_le_globalMetaLen hb_pos)
  have htail_fit : Fits w (tailCapPerBucket N) := by
    rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
    · simp only [tailCapPerBucket, hb0, ↓reduceIte]
      exact fits_const_of_offCompItems hfit (by decide)
    · exact fits_of_le_globalMetaLen_comp hb_pos hw hnU hU
        (tailCapPerBucket_le_globalMetaLen hb_pos)
  have hgm_fit : Fits w (gmSlabDirBase N) ∧ Fits w (gmTailPtrBase N) ∧
      Fits w (gmTailOwnerBase N) ∧ Fits w (gmSlabMetaBase N) := by
    rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
    · have h7 : Fits w 7 := fits_const_of_offCompItems hfit (by decide)
      simp only [gmSlabMetaBase, gmTailOwnerBase, gmTailPtrBase, gmSlabDirBase, maxTailItems,
        tailCapPerBucket, dirSlabsPerBucket, numBuckets, hb0, ↓reduceIte, Nat.pow_zero,
        Nat.mul_one, Nat.mul_zero, Nat.add_zero]
      exact ⟨h7, h7, h7, h7⟩
    · have hlen := gmSlabMetaBase_add_eq_globalMetaLen hb_pos
      have hd_le : gmSlabDirBase N ≤ globalMetaLen N := by
        unfold gmSlabMetaBase gmTailOwnerBase gmTailPtrBase at hlen; omega
      have hp_le : gmTailPtrBase N ≤ globalMetaLen N := by
        unfold gmSlabMetaBase gmTailOwnerBase at hlen; omega
      have ho_le : gmTailOwnerBase N ≤ globalMetaLen N := by
        unfold gmSlabMetaBase at hlen; omega
      have hm_le : gmSlabMetaBase N ≤ globalMetaLen N := by omega
      exact ⟨fits_of_le_globalMetaLen_comp hb_pos hw hnU hU hd_le,
        fits_of_le_globalMetaLen_comp hb_pos hw hnU hU hp_le,
        fits_of_le_globalMetaLen_comp hb_pos hw hnU hU ho_le,
        fits_of_le_globalMetaLen_comp hb_pos hw hnU hU hm_le⟩
  have hmicro_fit : Fits w (numMicroPerBucket N) := by
    have h1 : numMicroPerBucket N ≤ totalMicroBuckets N := by
      rw [totalMicroBuckets_eq_mul]; exact Nat.le_mul_of_pos_left _ (numBuckets_pos N)
    exact hmax_fit.of_le (h1.trans (totalMicroBuckets_le N))
  have hM_fit : Fits w (maxTailItems N) := by
    rcases Nat.eq_zero_or_pos (maxTailItems N) with h0 | hpos
    · rw [h0]; exact fits_const_of_offCompItems hfit (by decide)
    · exact lt_of_le_of_lt (maxTailItems_le_of_pos hpos |>.trans hnU) hU
  have hoffLM_fit : ∀ c ≤ 8, Fits w (offCompLMSub U w N c) := fun c hc => by
    refine lt_of_le_of_lt ?_ hoff
    have hmul : c * lmSubWords N w ≤ 9 * lmSubWords N w := Nat.mul_le_mul_right _ (by omega)
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLMSub; omega
  fin_cases i <;> simp only [mkCompParams]
  · exact hw_fit
  · exact lt_of_le_of_lt hnU hU
  · exact lt_of_le_of_lt (by omega) hU
  · exact lt_of_le_of_lt (quotientBits_le_of_le_pow hU.le) hw_fit
  · exact lt_of_le_of_lt (Nat.clog_le_of_le_pow hV) hw_fit
  · exact hoffLM_fit 0 (by decide)
  · exact hoffLM_fit 1 (by decide)
  · exact hoffLM_fit 2 (by decide)
  · exact hoffLM_fit 3 (by decide)
  · exact hoffLM_fit 4 (by decide)
  · exact hoffLM_fit 5 (by decide)
  · exact hoffLM_fit 6 (by decide)
  · exact hoffLM_fit 7 (by decide)
  · exact hoffLM_fit 8 (by decide)
  · exact lt_of_le_of_lt (effBucketPosBits_le_of_lt_pow hnU hU) hw_fit
  · exact lt_of_le_of_lt (by unfold offCompItems offDenseToTail offTailToDense; omega) hoff
  · exact lt_of_le_of_lt (globalPtrBits_le_of_lt_pow hnU hU) hw_fit
  · exact lt_of_le_of_lt (by unfold offCompItems offDenseToTail; omega) hoff
  · exact lt_of_le_of_lt (by unfold offCompItems; omega) hoff
  · exact hM_fit
  · exact h2b_fit.of_le (le_of_lt Nat.lt_two_pow_self)
  · exact h2b_fit.of_le (Nat.sub_le _ _)
  · exact hslab_fit
  · exact hslab_fit.of_le (Nat.sub_le _ _)
  · exact h2slab_fit
  · exact hdir_fit
  · exact hdir_fit.of_le (Nat.sub_le _ _)
  · exact htail_fit
  · exact hgm_fit.1
  · exact hgm_fit.2.1
  · exact hgm_fit.2.2.1
  · exact hgm_fit.2.2.2
  · exact hmicro_fit
  · exact lt_of_le_of_lt ((Nat.min_le_left _ _).trans hnU) hU
  · exact hoff
  · exact lt_of_le_of_lt (by
      unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM; omega) hoff
/-! ## Section 4: Compacted Slot Resolution, Owner-Bucket Recovery, and Key Reconstruction -/

/-- Read `bCount N gm b` at `metaBase` in `Memory.Prog` (`¬ReadsWidth`). -/
def readCompBucketCountGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), b) => do
    let z ← pure 0
    if cpBucketBits cp = z then
      readCompGMGenProg ((cp, metaBase), z)
    else do
      let b3 := b + b + b
      let q_idx ← pure (4 + b3)
      let r_idx ← pure (4 + b3 + 1)
      let q_b ← readCompGMGenProg ((cp, metaBase), q_idx)
      let r_b ← readCompGMGenProg ((cp, metaBase), r_idx)
      pure (q_b * cpSlabSize cp + r_b)

theorem clientResult_readCompBucketCountGenProg {U V w N metaBase b : ℕ} {s : Memory.State}
    (hb : b < numBuckets N) :
    (Memory.spec 0).clientResult s
        (readCompBucketCountGenProg ((mkCompParams U V w N, metaBase), b)) =
      bCount N (compGmAt metaBase U w N s.mem) b := by
  dsimp only [readCompBucketCountGenProg, bCount, cpBucketBits_mk, cpSlabSize_mk]
  simp only [pure_bind]
  by_cases hb0 : bucketBits N = 0
  · have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have hb_eq : b = 0 := by simp only [numBuckets, hb0, pow_zero] at hb; omega
    subst hb_eq; simp [hb0, h0_lt]
  · have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    have hq_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hr_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have hr_eq : gmQIdx b + 1 = gmRIdx b := rfl
    rw [ite_eq_right hb0, ite_eq_right hb0, ite_eq_left hb, hq_eq, hr_eq,
      prog_clientResult_bind, clientResult_readCompGMGenProg hq_lt, clientState_readCompGMGenProg,
      prog_clientResult_bind, clientResult_readCompGMGenProg hr_lt, clientState_readCompGMGenProg,
      prog_clientResult_pure]

theorem clientState_readCompBucketCountGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readCompBucketCountGenProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  unfold StateTransitionSpec.clientState; dsimp only [readCompBucketCountGenProg]
  simp only [pure_bind]; split_ifs <;> simp

@[simp] theorem runClient_state_readCompBucketCountGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (readCompBucketCountGenProg d))) = s :=
  clientState_readCompBucketCountGenProg d s

theorem memoryCost_readCompBucketCountGenProg_le (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readCompBucketCountGenProg d) s ≤ 4 := by
  rcases d with ⟨⟨cp, metaBase⟩, b⟩
  dsimp only [readCompBucketCountGenProg]; simp only [pure_bind]
  split_ifs <;> simp

/-- Precondition for reading the count of items in bucket `b` from compacted metadata. -/
@[expose] def ReadCompBucketCountPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), b), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N

theorem realizesBounded_readCompBucketCountGen :
    RealizesBounded .exact readCompBucketCountGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      ReadCompBucketCountPre (fun _ _ => 0) := by
  have hgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, b⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hslot, hb⟩ := h
    simp only [cpBucketBits_mk, cpSlabSize_mk] at *
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have hfit_meta : Fits w (metaBase + offCompItems U w N) :=
      lt_of_le_of_lt hfr hmem.1)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, h0_lt⟩
  all_goals (
    have hb_pos : 0 < bucketBits N := by omega
    have hb_ne : bucketBits N ≠ 0 := hb_pos.ne'
    have hq_lt : gmQIdx b < globalMetaLen N := gmQIdx_lt hb_pos hb
    have hr_lt : gmRIdx b < globalMetaLen N := gmRIdx_lt hb_pos hb
    have hq_eq : 4 + (b + b + b) = gmQIdx b := by unfold gmQIdx; omega
    have hr_eq : gmQIdx b + 1 = gmRIdx b := rfl
    have hbc_le : bCount N (compGmAt metaBase U w N s.mem) b ≤ N := bCount_le_n_max hslot b
    unfold bCount at hbc_le; simp only [hb_ne, ↓reduceIte, hb] at hbc_le
    try simp only [hq_eq, hr_eq, StateTransitionSpec.clientState,
      clientResult_readCompGMGenProg hq_lt, clientResult_readCompGMGenProg hr_lt,
      runClient_state_readCompGMGenProg] at *)
  all_goals try exact fits_of_le_globalMetaLen_comp hb_pos hw hnU hU (by
    unfold gmQIdx gmRIdx at *; omega)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by assumption⟩
  all_goals exact lt_of_le_of_lt (by omega) hU

private def recoverOwnerTailProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), d) => do
    let r ← pure (d % cpMaxTail cp)
    let t ← readCompDTGenProg ((cp, metaBase), r)
    let idx ← pure (cpGmTailOwnerBase cp + t)
    let desc ← readCompGMGenProg ((cp, metaBase), idx)
    pure (desc / cpTailCap cp)

private def RecoverOwnerTailPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), d), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      0 < bucketBits N ∧ 0 < maxTailItems N ∧
      compDTAt metaBase U w N s.mem (d % maxTailItems N) < maxTailItems N

private theorem realizesBounded_recoverOwnerTail :
    RealizesBounded .exact recoverOwnerTailProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      RecoverOwnerTailPre (fun _ _ => 0) := by
  have hdt := realizesBounded_readCompDTGen
  have hgm := realizesBounded_readCompGMGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, idx_d⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, hM_pos, ht_M⟩ := h
    have hb_ne : bucketBits N ≠ 0 := hb_pos.ne'
    have hr_lt : idx_d % maxTailItems N < maxTailItems N := Nat.mod_lt _ hM_pos
    have hidx_lt := gmTailOwnerIdx_lt hb_pos ht_M
    have hlen_le := globalMetaLen_le_of_bucketBits_pos hb_pos
    try simp only [cpMaxTail_mk, cpGmTailOwnerBase_mk, cpTailCap_mk,
      StateTransitionSpec.clientState, clientResult_readCompDTGenProg hr_lt,
      runClient_state_readCompDTGenProg] at *)
  all_goals try omega
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hr_lt⟩
  all_goals try (unfold gmTailOwnerIdx at hidx_lt
                 exact (lt_of_lt_of_le hidx_lt (hlen_le.trans (by omega))).trans hU)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hidx_lt⟩
  · have hK := slabSize_pos N
    unfold tailCapPerBucket; rw [ite_eq_right hb_ne]; omega

/-- Recover `ownerBucketOfDense N gm dt d` in $O(1)$ steps (`Memory.Prog`, `¬ReadsWidth`). -/
def recoverOwnerBucketGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), d) => do
    let z ← pure 0
    if cpBucketBits cp = z then pure z
    else do
      let n_slabs ← readCompGMGenProg ((cp, metaBase), z)
      let b_tail ← pure (n_slabs * cpSlabSize cp)
      if d < b_tail then do
        let p := d / cpSlabSize cp
        let p2 := p + p
        let idx ← pure (cpGmSlabMetaBase cp + (p2 + p2))
        readCompGMGenProg ((cp, metaBase), idx)
      else
        recoverOwnerTailProg ((cp, metaBase), d)

theorem clientResult_recoverOwnerBucketGenProg {U V w N metaBase d : ℕ} {s : Memory.State}
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (htd : 0 < bucketBits N →
      TailDenseInv N (compGmAt metaBase U w N s.mem 0) (compGmAt metaBase U w N s.mem 1)
        (compTDAt metaBase U w N s.mem) (compDTAt metaBase U w N s.mem))
    (hd : d < epochTotalSlots N (compGmAt metaBase U w N s.mem)) :
    (Memory.spec 0).clientResult s
        (recoverOwnerBucketGenProg ((mkCompParams U V w N, metaBase), d)) =
      ownerBucketOfDense N (compGmAt metaBase U w N s.mem) (compDTAt metaBase U w N s.mem) d := by
  dsimp only [recoverOwnerBucketGenProg, recoverOwnerTailProg, ownerBucketOfDense,
    cpBucketBits_mk, cpSlabSize_mk, cpGmSlabMetaBase_mk, cpMaxTail_mk,
    cpGmTailOwnerBase_mk, cpTailCap_mk]
  simp only [pure_bind]
  by_cases hb0 : bucketBits N = 0
  · rw [ite_eq_left hb0, ite_eq_left hb0]; rfl
  · rw [ite_eq_right hb0, ite_eq_right hb0]
    have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    rw [prog_clientResult_bind, clientResult_readCompGMGenProg h0_lt, clientState_readCompGMGenProg]
    by_cases hd_slab : d < compGmAt metaBase U w N s.mem 0 * slabSize N
    · rw [ite_eq_left hd_slab, ite_eq_left hd_slab]
      have hslab := hslot.multi_slab hb_pos
      have hp_lt : d / slabSize N < maxFullSlabs N := by
        have h1 : d / slabSize N < compGmAt metaBase U w N s.mem 0 :=
          Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
        have := hslab.nslabs_eq.trans_le hslab.nslabs_le; omega
      have hidx_lt : gmSlabOwnerBIdx N (d / slabSize N) < globalMetaLen N :=
        gmSlabOwnerBIdx_lt hb_pos hp_lt
      have hidx_eq : gmSlabMetaBase N + (d / slabSize N + d / slabSize N +
          (d / slabSize N + d / slabSize N)) = gmSlabOwnerBIdx N (d / slabSize N) := by
        unfold gmSlabOwnerBIdx; omega
      rw [hidx_eq]
      exact clientResult_readCompGMGenProg hidx_lt s
    · rw [ite_eq_right hd_slab, ite_eq_right hd_slab]
      unfold epochTotalSlots at hd; rw [ite_eq_right hb0] at hd
      have htd' := htd hb_pos
      have htail := hslot.multi_tail hb_pos
      obtain ⟨ht_lt, _⟩ := htd'.owner_valid d (by omega) hd
      have hM_le : compGmAt metaBase U w N s.mem 1 ≤ maxTailItems N :=
        htail.ntails_eq.trans_le htail.ntails_le
      have hM_pos : 0 < maxTailItems N := by omega
      have hr_lt : d % maxTailItems N < maxTailItems N := Nat.mod_lt _ hM_pos
      have ht_M : compDTAt metaBase U w N s.mem (d % maxTailItems N) < maxTailItems N := by omega
      have hidx_lt : gmTailOwnerIdx N (compDTAt metaBase U w N s.mem (d % maxTailItems N)) <
          globalMetaLen N := gmTailOwnerIdx_lt hb_pos ht_M
      have hidx_eq : gmTailOwnerBase N + compDTAt metaBase U w N s.mem (d % maxTailItems N) =
          gmTailOwnerIdx N (compDTAt metaBase U w N s.mem (d % maxTailItems N)) := rfl
      rw [prog_clientResult_bind, clientResult_readCompDTGenProg hr_lt,
        clientState_readCompDTGenProg, hidx_eq, prog_clientResult_bind,
        clientResult_readCompGMGenProg hidx_lt, clientState_readCompGMGenProg,
        prog_clientResult_pure]

/-- Precondition for recovering the owner bucket of dense item `d`. -/
@[expose] def RecoverOwnerBucketPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), d), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      (0 < bucketBits N →
        TailDenseInv N (compGmAt metaBase U w N s.mem 0) (compGmAt metaBase U w N s.mem 1)
          (compTDAt metaBase U w N s.mem) (compDTAt metaBase U w N s.mem)) ∧
      d < epochTotalSlots N (compGmAt metaBase U w N s.mem)

theorem realizesBounded_recoverOwnerBucketGen :
    RealizesBounded .exact recoverOwnerBucketGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      RecoverOwnerBucketPre (fun _ _ => 0) := by
  have hgm := realizesBounded_readCompGMGen
  have htail_op := realizesBounded_recoverOwnerTail
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, idx_d⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hslot, htd, hd_lt⟩ := h
    simp only [cpBucketBits_mk, cpSlabSize_mk, cpGmSlabMetaBase_mk] at *
    have hb_pos : 0 < bucketBits N := by omega
    have hb_ne : bucketBits N ≠ 0 := hb_pos.ne'
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    have hSN := hslot.multi_total_le hb_pos
    have hlen_le := globalMetaLen_le_of_bucketBits_pos hb_pos
    try simp only [StateTransitionSpec.clientState, clientResult_readCompGMGenProg h0_lt,
      runClient_state_readCompGMGenProg] at *)
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, h0_lt⟩
  all_goals try exact (slabSize_pos N).ne'
  all_goals try exact lt_of_le_of_lt (by omega) hU
  · have hslab := hslot.multi_slab hb_pos
    have hp_lt : idx_d / slabSize N < maxFullSlabs N := by
      have h1 : idx_d / slabSize N < compGmAt metaBase U w N s.mem 0 :=
        Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have := hslab.nslabs_eq.trans_le hslab.nslabs_le; omega
    have hidx := gmSlabOwnerBIdx_lt hb_pos hp_lt
    unfold gmSlabOwnerBIdx at hidx
    exact lt_of_le_of_lt (by omega) hU
  · have hslab := hslot.multi_slab hb_pos
    have hp_lt : idx_d / slabSize N < maxFullSlabs N := by
      have h1 : idx_d / slabSize N < compGmAt metaBase U w N s.mem 0 :=
        Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have := hslab.nslabs_eq.trans_le hslab.nslabs_le; omega
    have hidx := gmSlabOwnerBIdx_lt hb_pos hp_lt
    have heq : gmSlabMetaBase N + (idx_d / slabSize N + idx_d / slabSize N +
        (idx_d / slabSize N + idx_d / slabSize N)) = gmSlabOwnerBIdx N (idx_d / slabSize N) := by
      unfold gmSlabOwnerBIdx; omega
    rw [heq]
    exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hidx⟩
  · unfold epochTotalSlots at hd_lt; rw [ite_eq_right hb_ne] at hd_lt
    have htd' := htd hb_pos
    have htail := hslot.multi_tail hb_pos
    obtain ⟨ht_lt, _⟩ := htd'.owner_valid idx_d (by omega) hd_lt
    have hM_le : compGmAt metaBase U w N s.mem 1 ≤ maxTailItems N :=
      htail.ntails_eq.trans_le htail.ntails_le
    exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hb_pos, by omega, by omega⟩

/-- Reconstruct the key `u` stored at dense index `d < n` in `(metaBase, itemBase)`. -/
@[expose] noncomputable def reconstructKeyAt (metaBase itemBase U V w N n : ℕ)
    (θ : QuotHashSeed U N) (mem : ℕ → ℕ) (d : ℕ) : ℕ :=
  let b := ownerBucketOfDense N (compGmAt metaBase U w N mem) (compDTAt metaBase U w N mem) d
  let q := compQuotAt itemBase U V w N n mem d
  feistelReconstruct (bucketBits N) (hValOfSeed U N θ) b q

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

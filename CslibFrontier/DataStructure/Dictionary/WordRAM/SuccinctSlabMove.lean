/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabPool
import CslibFrontier.Tactic.Realize

/-!
# Slab Promotion Loop in `Memory.Prog`

This module implements the `K`-step (`K = slabSize n_max`) slab promotion (`promoteStepProg`,
`promoteLoopProg`, and `promoteSlabProg`) in `Memory.Prog`, proves that it preserves
`SlotStoreInv`, `bCount`, and all logical `(quotAt, valAt)` entries via `slotOf`, and certifies
its Word-RAM realization via `realize` and `Realizes.iterate₀`. Slab demotion (`demoteSlabProg`)
is implemented in `CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabDemote`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.promoteStepProg`: single step
  `k < slabSize n_max` of slab promotion.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.promoteLoopProg`: `K`-step iteration of
  `promoteStepProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.promoteSlabProg`: complete slab promotion
  (`promoteLoopProg` followed by `gmPushSlabProg`).
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.PromoteSlabInv`: entry invariant for
  `promoteSlabProg` (`gm (gmRIdx b) = 2 * slabSize n_max`).

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.promoteStepProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_promoteStepGen`: single-step invariant
  preservation and `Realizes` certificate for `promoteStepProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.promoteSlabProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_promoteSlabGen`: full-slab promotion
  invariant preservation, `O(K)` `memoryCost`, and `Realizes` certificate for `promoteSlabProg`.
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
open Finset

/-! ## Section 1: Single step of slab promotion (`promoteStepProg`) -/

/-- Parameter-free single step `k < slabSize n_max` of slab promotion for
`x = ((dp, (base, b)), k)`. -/
def promoteStepGenProg (x : (DictParams × (ℕ × ℕ)) × ℕ) : Memory.Prog ℕ := do
  let dp := x.1.1
  let base := x.1.2.1
  let b := x.1.2.2
  let k := x.2
  let u := dpSlabSizeSubOne dp - k
  let r_top := dpSlabSize dp + u
  let t_u ← readGMGenProg (dp, (base, dpGmTailPtrBase dp + (b * dpTailCap dp + u)))
  let t_top ← readGMGenProg (dp, (base, dpGmTailPtrBase dp + (b * dpTailCap dp + r_top)))
  let p_new ← readGMGenProg (dp, (base, 0))
  let g_u := dpNMaxSubOne dp - t_u
  let g_top := dpNMaxSubOne dp - t_top
  let g_slab := p_new * dpSlabSize dp + k
  let q_u ← readQuotGenProg (dp, (base, g_u))
  let v_u ← readValGenProg (dp, (base, g_u))
  let q_top ← readQuotGenProg (dp, (base, g_top))
  let v_top ← readValGenProg (dp, (base, g_top))
  writeQuotGenProg (dp, ((base, g_u), q_top))
  writeValGenProg (dp, ((base, g_u), v_top))
  removeLastTailItemGenProg (dp, (base, b))
  writeQuotGenProg (dp, ((base, g_slab), q_u))
  let _ ← writeValGenProg (dp, ((base, g_slab), v_u))
  pure (k + 1)

/-- One step `k < slabSize n_max` of slab promotion for `x = ((base, b), k)`:
1. Reads the payload `(q_u, v_u)` at low tail item `u = (slabSize n_max - 1) - k` and the payload
   `(q_top, v_top)` at the last tail item `r_top = slabSize n_max + u = gm (gmRIdx b) - 1`.
2. Copies `(q_top, v_top)` into tail item `u`.
3. Calls `removeLastTailItemProg (base, b)` to compact and remove tail item `r_top`.
4. Writes `(q_u, v_u)` into physical slab slot `gm 0 * slabSize n_max + k` and returns `k + 1`. -/
def promoteStepProg (U V w n_max h_space : ℕ) (x : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let base := x.1.1
  let b := x.1.2
  let k := x.2
  let u := (slabSize n_max - 1) - k
  let r_top := slabSize n_max + u
  let t_u ← readGMProg U V w n_max h_space
    (base, gmTailPtrBase n_max + (b * tailCapPerBucket n_max + u))
  let t_top ← readGMProg U V w n_max h_space
    (base, gmTailPtrBase n_max + (b * tailCapPerBucket n_max + r_top))
  let p_new ← readGMProg U V w n_max h_space (base, 0)
  let g_u := (n_max - 1) - t_u
  let g_top := (n_max - 1) - t_top
  let g_slab := p_new * slabSize n_max + k
  let q_u ← readQuotProg U w n_max h_space (base, g_u)
  let v_u ← readValProg U V w n_max h_space (base, g_u)
  let q_top ← readQuotProg U w n_max h_space (base, g_top)
  let v_top ← readValProg U V w n_max h_space (base, g_top)
  writeQuotProg U w n_max h_space ((base, g_u), q_top)
  writeValProg U V w n_max h_space ((base, g_u), v_top)
  removeLastTailItemProg U V w n_max h_space (base, b)
  writeQuotProg U w n_max h_space ((base, g_slab), q_u)
  let _ ← writeValProg U V w n_max h_space ((base, g_slab), v_u)
  pure (k + 1)

@[simp] theorem promoteStepGenProg_mk (U V w n_max h_space : ℕ) (d1 : ℕ × ℕ) (d2 : ℕ) :
    promoteStepGenProg ((mkDictParams U V w n_max h_space, d1), d2) =
      promoteStepProg U V w n_max h_space (d1, d2) := by
  simp only [promoteStepGenProg, promoteStepProg, p_slabSizeSubOne_mk, p_slabSize_mk,
    p_gmTailPtrBase_mk, p_tailCap_mk, p_nMaxSubOne_mk, readGMGenProg_mk, readQuotGenProg_mk,
    readValGenProg_mk, writeQuotGenProg_mk, writeValGenProg_mk, removeLastTailItemGenProg_mk]

@[simp]
theorem memoryCost_promoteStepProg (U V w n_max h_space : ℕ) (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (promoteStepProg U V w n_max h_space x) s = 66 := by
  simp [promoteStepProg, -bind_pure_comp, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]

theorem one_le_memoryCost_promoteStepGenProg (x : (DictParams × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (promoteStepGenProg x) s := by
  unfold promoteStepGenProg readGMGenProg readPackedGenProg
  dsimp only
  rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_readPackedProg]
  omega

/-- Pure state invariant for step `k` (`k < slabSize n_max`) of `promoteStepProg`. -/
@[expose]
def PromoteStepInv (U V w₀ n_max h_space base b k : ℕ) (s : Memory.State) : Prop :=
  let gm := gmAt base U V w₀ n_max h_space s.mem
  b < numBuckets n_max ∧
  k < slabSize n_max ∧
  TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1) ∧
  SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0) ∧
  gm (gmRIdx b) = 2 * slabSize n_max - k ∧
  gm 0 * slabSize n_max + k + gm 1 ≤ n_max

/-- Precondition for `promoteStepProg` in `Realizes`. -/
@[expose]
def PromoteStepPre (U V w₀ n_max h_space w base b k : ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  PromoteStepInv U V w₀ n_max h_space base b k s ∧
  0 < bucketBits n_max

/-- Parameter-free precondition for `promoteStepGenProg`. -/
@[expose]
def PromoteStepGenPre (w : ℕ) (x : (DictParams × (ℕ × ℕ)) × ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w x.1.1 x.1.2.1 ∧
  PromoteStepInv (dpU x.1.1) (dpV x.1.1) (dpW x.1.1) (dpNMax x.1.1) (dpHSpace x.1.1)
    x.1.2.1 x.1.2.2 x.2 s ∧
  0 < bucketBits (dpNMax x.1.1)

@[simp] theorem promoteStepGenPre_mk (U V w₀ n_max h_space w : ℕ) (d1 : ℕ × ℕ) (d2 : ℕ)
    (s : Memory.State) :
    PromoteStepGenPre w ((mkDictParams U V w₀ n_max h_space, d1), d2) s ↔
      PromoteStepPre U V w₀ n_max h_space w d1.1 d1.2 d2 s := Iff.rfl

/-- Under `PromoteStepInv U V w n_max h_space base b k s` (`k < slabSize n_max`,
`gm (gmRIdx b) = 2 * slabSize n_max - k`), `promoteStepProg` returns `k + 1` in `memoryCost = 66`
(`memoryCost_promoteStepProg`). It preserves `frontier`, `lmAt`, and memory outside
`[base + offQuot h_space, base + totalSpace U V w n_max h_space)`. It moves tail item
`u = (slabSize n_max - 1) - k` of bucket `b` to physical slab slot `gm 0 * slabSize n_max + k`,
compacts the last tail item `r_top = slabSize n_max + u` into `u`, and updates `gmAt` to
`gmRemoveTail n_max gm b`. -/
theorem promoteStepProg_effect {U V w n_max h_space base b k : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    (s : Memory.State)
    (hpre : PromoteStepInv U V w n_max h_space base b k s) :
    let gm := gmAt base U V w n_max h_space s.mem
    let qA := quotAt base U w n_max h_space s.mem
    let vA := valAt base U V w n_max h_space s.mem
    let u := (slabSize n_max - 1) - k
    let r_top := slabSize n_max + u
    let g_u := (n_max - 1) - gm (gmTailPtrIdx n_max b u)
    let g_top := (n_max - 1) - gm (gmTailPtrIdx n_max b r_top)
    let g_del := (n_max - 1) - gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1))
    let g_last := (n_max - 1) - (gm 1 - 1)
    let g_slab := gm 0 * slabSize n_max + k
    let s' := (Memory.spec 0).clientState s
      (promoteStepProg U V w n_max h_space ((base, b), k))
    (Memory.spec 0).clientResult s
      (promoteStepProg U V w n_max h_space ((base, b), k)) = k + 1 ∧
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem =
      Function.update
        (Function.update (Function.update qA g_u (qA g_top))
          g_del (Function.update qA g_u (qA g_top) g_last))
        g_slab (qA g_u) ∧
    valAt base U V w n_max h_space s'.mem =
      Function.update
        (Function.update (Function.update vA g_u (vA g_top))
          g_del (Function.update vA g_u (vA g_top) g_last))
        g_slab (vA g_u) ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem = gmRemoveTail n_max gm b := by
  intro gm qA vA u r_top g_u g_top g_del g_last g_slab s'
  rcases hpre with ⟨hb, hk_lt, htail, _, hrb_eq, htot⟩
  change gm (gmRIdx b) = 2 * slabSize n_max - k at hrb_eq
  change gm 0 * slabSize n_max + k + gm 1 ≤ n_max at htot
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  have hTcap : tailCapPerBucket n_max = 2 * slabSize n_max := by
    unfold tailCapPerBucket; rw [ite_eq_right hb0]
  have hr_le_nt : gm (gmRIdx b) ≤ gm 1 := r_le_ntails_of_tailBijection htail hb
  have hu_lt_r : u < gm (gmRIdx b) := by dsimp only [u]; omega
  have hr_top_eq : r_top = gm (gmRIdx b) - 1 := by dsimp only [r_top, u]; omega
  have hr_top_lt_r : r_top < gm (gmRIdx b) := by dsimp only [r_top, u]; omega
  have hu_cap : u < tailCapPerBucket n_max := by dsimp only [u]; omega
  have hr_top_cap : r_top < tailCapPerBucket n_max := by dsimp only [r_top, u]; omega
  have hptr_u_lt : gmTailPtrBase n_max + (b * tailCapPerBucket n_max + u) <
      globalMetaLen n_max := gmTailPtrIdx_lt hb_pos hb hu_cap
  have hptr_top_lt : gmTailPtrBase n_max + (b * tailCapPerBucket n_max + r_top) <
      globalMetaLen n_max := gmTailPtrIdx_lt hb_pos hb hr_top_cap
  have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
  have htu_lt_gm1 : gm (gmTailPtrIdx n_max b u) < gm 1 := htail.ptr_lt b hb u hu_lt_r
  have httop_lt_gm1 : gm (gmTailPtrIdx n_max b r_top) < gm 1 := htail.ptr_lt b hb r_top hr_top_lt_r
  have hgu_lt : g_u < n_max := by dsimp only [g_u]; omega
  have hgtop_lt : g_top < n_max := by dsimp only [g_top]; omega
  have hgslab_lt : g_slab < n_max := by dsimp only [g_slab]; omega
  have hqu_lt : qA g_u < 2 ^ quotientBits U n_max := quotAt_lt _ _ _ _ _ _ _
  have hvu_lt : vA g_u < 2 ^ valBits V := valAt_lt _ _ _ _ _ _ _ _
  have hqtop_lt : qA g_top < 2 ^ quotientBits U n_max := quotAt_lt _ _ _ _ _ _ _
  have hvtop_lt : vA g_top < 2 ^ valBits V := valAt_lt _ _ _ _ _ _ _ _
  set t_u := gm (gmTailPtrIdx n_max b u)
  set t_top := gm (gmTailPtrIdx n_max b r_top)
  set p_new := gm 0
  set q_u := qA g_u
  set v_u := vA g_u
  set q_top := qA g_top
  set v_top := vA g_top
  have hres_tu : (Memory.spec 0).clientResult s
      (readGMProg U V w n_max h_space
        (base, gmTailPtrBase n_max + (b * tailCapPerBucket n_max + u))) = t_u :=
    clientResult_readGMProg s hptr_u_lt
  have hres_ttop : (Memory.spec 0).clientResult s
      (readGMProg U V w n_max h_space
        (base, gmTailPtrBase n_max + (b * tailCapPerBucket n_max + r_top))) = t_top :=
    clientResult_readGMProg s hptr_top_lt
  have hres_p : (Memory.spec 0).clientResult s
      (readGMProg U V w n_max h_space (base, 0)) = p_new :=
    clientResult_readGMProg s h0_lt
  have hres_qu : (Memory.spec 0).clientResult s
      (readQuotProg U w n_max h_space (base, g_u)) = q_u :=
    clientResult_readQuotProg s hgu_lt
  have hres_vu : (Memory.spec 0).clientResult s
      (readValProg U V w n_max h_space (base, g_u)) = v_u :=
    clientResult_readValProg s hgu_lt
  have hres_qtop : (Memory.spec 0).clientResult s
      (readQuotProg U w n_max h_space (base, g_top)) = q_top :=
    clientResult_readQuotProg s hgtop_lt
  have hres_vtop : (Memory.spec 0).clientResult s
      (readValProg U V w n_max h_space (base, g_top)) = v_top :=
    clientResult_readValProg s hgtop_lt
  obtain ⟨hf1, hout1, hq1, hv1, hl1, hg1⟩ :=
    writeQuotProg_effect (base := base) (V := V) (h_space := h_space) hw hgu_lt hqtop_lt s
  set s₁ := (Memory.spec 0).clientState s (writeQuotProg U w n_max h_space ((base, g_u), q_top))
  obtain ⟨hf2, hout2, hq2, hv2, hl2, hg2⟩ :=
    writeValProg_effect (base := base) (h_space := h_space) hw hgu_lt hvtop_lt s₁
  set s₂ := (Memory.spec 0).clientState s₁ (writeValProg U V w n_max h_space ((base, g_u), v_top))
  have hgm2 : gmAt base U V w n_max h_space s₂.mem = gm := by rw [hg2, hg1]
  have htail2 : TailBijection n_max (gmAt base U V w n_max h_space s₂.mem)
      (fun b' => gmAt base U V w n_max h_space s₂.mem (gmRIdx b'))
      (gmAt base U V w n_max h_space s₂.mem 1) := by
    rw [hgm2]; exact htail
  have hr2_pos : 1 ≤ gmAt base U V w n_max h_space s₂.mem (gmRIdx b) := by
    rw [hgm2]; omega
  obtain ⟨hf3, hout3, hq3, hv3, hl3, hg3⟩ :=
    removeLastTailItemProg_effect (U := U) (V := V) (h_space := h_space)
      hw hb_pos hb s₂ htail2 hr2_pos
  set s₃ := (Memory.spec 0).clientState s₂ (removeLastTailItemProg U V w n_max h_space (base, b))
  obtain ⟨hf4, hout4, hq4, hv4, hl4, hg4⟩ :=
    writeQuotProg_effect (base := base) (V := V) (h_space := h_space) hw hgslab_lt hqu_lt s₃
  set s₄ := (Memory.spec 0).clientState s₃ (writeQuotProg U w n_max h_space ((base, g_slab), q_u))
  obtain ⟨hf5, hout5, hq5, hv5, hl5, hg5⟩ :=
    writeValProg_effect (base := base) (h_space := h_space) hw hgslab_lt hvu_lt s₄
  set s₅ := (Memory.spec 0).clientState s₄ (writeValProg U V w n_max h_space ((base, g_slab), v_u))
  have hres : (Memory.spec 0).clientResult s
      (promoteStepProg U V w n_max h_space ((base, b), k)) = k + 1 := by
    unfold promoteStepProg
    dsimp only
    repeat rw [StateTransitionSpec.clientResult_bind]
    rfl
  have hst : s' = s₅ := by
    change (Memory.spec 0).clientState s
      (promoteStepProg U V w n_max h_space ((base, b), k)) = s₅
    unfold promoteStepProg
    dsimp only
    rw [StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_tu,
      StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_ttop,
      StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_p,
      StateTransitionSpec.clientState_bind, clientState_readQuotProg, hres_qu,
      StateTransitionSpec.clientState_bind, clientState_readValProg, hres_vu,
      StateTransitionSpec.clientState_bind, clientState_readQuotProg, hres_qtop,
      StateTransitionSpec.clientState_bind, clientState_readValProg, hres_vtop]
    repeat rw [StateTransitionSpec.clientState_bind]
    rfl
  rw [hst]
  refine ⟨hres, by rw [hf5, hf4, hf3, hf2, hf1], ?_,
    by rw [hq5, hq4, hq3, hgm2, hq2, hq1],
    by rw [hv5, hv4, hv3, hgm2, hv2, hv1],
    by rw [hl5, hl4, hl3, hl2, hl1],
    by rw [hg5, hg4, hg3, hgm2]⟩
  intro a ha
  rw [hout5 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega),
    hout4 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega),
    hout3 a ha,
    hout2 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega),
    hout1 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega)]

private theorem promoteStep_bounds {U V w₀ n_max h_space w base b k : ℕ}
    {s : Memory.State} (hw : 0 < w₀)
    (h : PromoteStepPre U V w₀ n_max h_space w base b k s) :
    let u := (slabSize n_max - 1) - k
    let r_top := slabSize n_max + u
    let ptr_u_idx := gmTailPtrBase n_max + (b * tailCapPerBucket n_max + u)
    let ptr_top_idx := gmTailPtrBase n_max + (b * tailCapPerBucket n_max + r_top)
    let t_u := (Memory.spec 0).clientResult s (readGMProg U V w₀ n_max h_space (base, ptr_u_idx))
    let s1 := (Memory.spec 0).clientState s (readGMProg U V w₀ n_max h_space (base, ptr_u_idx))
    let t_top := (Memory.spec 0).clientResult s1
      (readGMProg U V w₀ n_max h_space (base, ptr_top_idx))
    let s2 := (Memory.spec 0).clientState s1
      (readGMProg U V w₀ n_max h_space (base, ptr_top_idx))
    let p_new := (Memory.spec 0).clientResult s2 (readGMProg U V w₀ n_max h_space (base, 0))
    let g_u := (n_max - 1) - t_u
    let g_top := (n_max - 1) - t_top
    let g_slab := p_new * slabSize n_max + k
    let q_top := (Memory.spec 0).clientResult s (readQuotProg U w₀ n_max h_space (base, g_top))
    let v_top := (Memory.spec 0).clientResult s (readValProg U V w₀ n_max h_space (base, g_top))
    let s_wq := (Memory.spec 0).clientState s
      (writeQuotProg U w₀ n_max h_space ((base, g_u), q_top))
    let s_wv := (Memory.spec 0).clientState s_wq
      (writeValProg U V w₀ n_max h_space ((base, g_u), v_top))
    k ≤ slabSize n_max - 1 ∧
    r_top ≤ tailCapPerBucket n_max ∧
    ptr_u_idx < globalMetaLen n_max ∧
    ptr_top_idx < globalMetaLen n_max ∧
    0 < globalMetaLen n_max ∧
    t_u ≤ n_max - 1 ∧
    t_top ≤ n_max - 1 ∧
    g_u < n_max ∧
    g_top < n_max ∧
    g_slab < n_max ∧
    TailBijection n_max (gmAt base U V w₀ n_max h_space s_wv.mem)
      (fun b' => gmAt base U V w₀ n_max h_space s_wv.mem (gmRIdx b'))
      (gmAt base U V w₀ n_max h_space s_wv.mem 1) ∧
    1 ≤ gmAt base U V w₀ n_max h_space s_wv.mem (gmRIdx b) ∧
    k + 1 ≤ max n_max 1 := by
  rcases h with ⟨_, ⟨hb, hk_lt, htail, _, hrb_eq, htot⟩, hb_pos⟩
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  have hTcap : tailCapPerBucket n_max = 2 * slabSize n_max := by
    unfold tailCapPerBucket; rw [ite_eq_right hb0]
  intro u r_top ptr_u_idx ptr_top_idx t_u s1 t_top s2 p_new
    g_u g_top g_slab q_top v_top s_wq s_wv
  let gm := gmAt base U V w₀ n_max h_space s.mem
  change b < numBuckets n_max at hb
  change k < slabSize n_max at hk_lt
  change gm (gmRIdx b) = 2 * slabSize n_max - k at hrb_eq
  change gm 0 * slabSize n_max + k + gm 1 ≤ n_max at htot
  have hr_le_nt : gm (gmRIdx b) ≤ gm 1 := r_le_ntails_of_tailBijection htail hb
  have hu_lt_r : u < gm (gmRIdx b) := by dsimp only [u]; omega
  have hr_top_lt_r : r_top < gm (gmRIdx b) := by dsimp only [r_top, u]; omega
  have hu_cap : u < tailCapPerBucket n_max := by dsimp only [u]; omega
  have hr_top_cap : r_top < tailCapPerBucket n_max := by dsimp only [r_top, u]; omega
  have hptr_u_lt : ptr_u_idx < globalMetaLen n_max := gmTailPtrIdx_lt hb_pos hb hu_cap
  have hptr_top_lt : ptr_top_idx < globalMetaLen n_max := gmTailPtrIdx_lt hb_pos hb hr_top_cap
  have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
  have htu_eq : t_u = gm (gmTailPtrIdx n_max b u) := clientResult_readGMProg s hptr_u_lt
  have httop_eq : t_top = gm (gmTailPtrIdx n_max b r_top) :=
    clientResult_readGMProg s hptr_top_lt
  have hpnew_eq : p_new = gm 0 := clientResult_readGMProg s h0_lt
  have htu_lt_gm1 : gm (gmTailPtrIdx n_max b u) < gm 1 := htail.ptr_lt b hb u hu_lt_r
  have httop_lt_gm1 : gm (gmTailPtrIdx n_max b r_top) < gm 1 := htail.ptr_lt b hb r_top hr_top_lt_r
  have htu_le : t_u ≤ n_max - 1 := by rw [htu_eq]; omega
  have httop_le : t_top ≤ n_max - 1 := by rw [httop_eq]; omega
  have hgu_lt : g_u < n_max := by dsimp only [g_u]; omega
  have hgtop_lt : g_top < n_max := by dsimp only [g_top]; omega
  have hgslab_lt : g_slab < n_max := by dsimp only [g_slab]; rw [hpnew_eq]; omega
  have hqtop_eq : q_top = quotAt base U w₀ n_max h_space s.mem g_top :=
    clientResult_readQuotProg s hgtop_lt
  have hvtop_eq : v_top = valAt base U V w₀ n_max h_space s.mem g_top :=
    clientResult_readValProg s hgtop_lt
  have hqtop_lt : q_top < 2 ^ quotientBits U n_max := by
    rw [hqtop_eq]; exact quotAt_lt _ _ _ _ _ _ _
  have hvtop_lt : v_top < 2 ^ valBits V := by
    rw [hvtop_eq]; exact valAt_lt _ _ _ _ _ _ _ _
  obtain ⟨_, _, _, _, _, hg1⟩ :=
    writeQuotProg_effect (base := base) (V := V) (h_space := h_space) hw hgu_lt hqtop_lt s
  obtain ⟨_, _, _, _, _, hg2⟩ :=
    writeValProg_effect (base := base) (h_space := h_space) hw hgu_lt hvtop_lt s_wq
  have hgm_wv : gmAt base U V w₀ n_max h_space s_wv.mem = gm := by
    dsimp only [s_wv]; rw [hg2, hg1]
  refine ⟨by omega, le_of_lt hr_top_cap, hptr_u_lt, hptr_top_lt, h0_lt, htu_le, httop_le,
    hgu_lt, hgtop_lt, hgslab_lt, ?_, ?_, by omega⟩
  · rw [hgm_wv]; exact htail
  · rw [hgm_wv]; omega

theorem realizes_promoteStepGen :
    Realizes .exact promoteStepGenProg
      (WordEncoding.encode (α := (DictParams × (ℕ × ℕ)) × ℕ)) (WordEncoding.encode (α := ℕ))
      PromoteStepGenPre
      (fun _ _ => 0) := by
  have hrg := realizes_readGMGen
  have hrq := realizes_readQuotGen
  have hwq := realizes_writeQuotGen
  have hrv := realizes_readValGen
  have hwv := realizes_writeValGen
  have hrem := realizes_removeLastTailItemGen
  refine Realizes.congr (p := fun d : (DictParams × (ℕ × ℕ)) × ℕ => do
      let u ← pure (dpSlabSizeSubOne d.1.1 - d.2)
      let r_top ← pure (dpSlabSize d.1.1 + u)
      let ptr_u_idx ← pure (dpGmTailPtrBase d.1.1 + (d.1.2.2 * dpTailCap d.1.1 + u))
      let t_u ← readGMGenProg (d.1.1, (d.1.2.1, ptr_u_idx))
      let ptr_top_idx ← pure (dpGmTailPtrBase d.1.1 + (d.1.2.2 * dpTailCap d.1.1 + r_top))
      let t_top ← readGMGenProg (d.1.1, (d.1.2.1, ptr_top_idx))
      let i0 ← pure 0
      let p_new ← readGMGenProg (d.1.1, (d.1.2.1, i0))
      let g_u ← pure (dpNMaxSubOne d.1.1 - t_u)
      let g_top ← pure (dpNMaxSubOne d.1.1 - t_top)
      let g_slab ← pure (p_new * dpSlabSize d.1.1 + d.2)
      let q_u ← readQuotGenProg (d.1.1, (d.1.2.1, g_u))
      let v_u ← readValGenProg (d.1.1, (d.1.2.1, g_u))
      let q_top ← readQuotGenProg (d.1.1, (d.1.2.1, g_top))
      let v_top ← readValGenProg (d.1.1, (d.1.2.1, g_top))
      writeQuotGenProg (d.1.1, ((d.1.2.1, g_u), q_top))
      writeValGenProg (d.1.1, ((d.1.2.1, g_u), v_top))
      removeLastTailItemGenProg (d.1.1, d.1.2)
      writeQuotGenProg (d.1.1, ((d.1.2.1, g_slab), q_u))
      let _ ← writeValGenProg (d.1.1, ((d.1.2.1, g_slab), v_u))
      pure (d.2 + 1)) ?_
    (fun d => by simp only [promoteStepGenProg, pure_bind])
  realize
  all_goals (
    rcases d with ⟨⟨dp, d1⟩, d2⟩
    let d := (d1, d2)
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1
    simpDictParamsWith [promoteStepGenPre_mk, removeLastTailItemGenPre_mk,
      removeLastTailItemGenProg_mk]
  )
  · exact (promoteStep_bounds hw h).1
  · exact fits_of_le_globalMetaLen h.1 h.2.2 hw hnU hU
      ((promoteStep_bounds hw h).2.1.trans (tailCapPerBucket_le_globalMetaLen h.2.2))
  · exact fits_of_le_globalMetaLen h.1 h.2.2 hw hnU hU
      (le_of_lt (promoteStep_bounds hw h).2.2.1)
  · exact h.1
  · exact (promoteStep_bounds hw h).2.2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2 hw hnU hU
      (le_of_lt (promoteStep_bounds hw h).2.2.2.1)
  · exact (promoteStep_bounds hw h).2.2.2.1
  · exact (promoteStep_bounds hw h).2.2.2.2.1
  · exact (promoteStep_bounds hw h).2.2.2.2.2.1
  · exact (promoteStep_bounds hw h).2.2.2.2.2.2.1
  · exact fits_of_le_max_n_one h.1 hw hnU hU
      (le_trans (le_of_lt (promoteStep_bounds hw h).2.2.2.2.2.2.2.2.2.1)
        (le_max_left n_max 1))
  · exact (promoteStep_bounds hw h).2.2.2.2.2.2.2.1
  · exact (promoteStep_bounds hw h).2.2.2.2.2.2.2.2.1
  · exact ⟨h.1, (promoteStep_bounds hw h).2.2.2.2.2.2.2.2.2.2.1, h.2.1.1,
      (promoteStep_bounds hw h).2.2.2.2.2.2.2.2.2.2.2.1, h.2.2⟩
  · exact (promoteStep_bounds hw h).2.2.2.2.2.2.2.2.2.1
  · exact fits_of_le_max_n_one h.1 hw hnU hU
      (promoteStep_bounds hw h).2.2.2.2.2.2.2.2.2.2.2.2

/-! ## Section 2: `PromoteArrInv`, `PromoteLoopInv`, and `promoteSlabProg` -/

/-- Array payload invariant at iteration `k ≤ slabSize n_max` of the slab-promotion loop. -/
structure PromoteArrInv {α : Type*} (n_max b : ℕ) (gm₀ : ℕ → ℕ) (arr₀ : ℕ → α)
    (k : ℕ) (gm : ℕ → ℕ) (arr : ℕ → α) : Prop where
  other_bucket : ∀ b' < numBuckets n_max, b' ≠ b → ∀ j < bCount n_max gm₀ b',
    arr (slotOf n_max gm b' j) = arr₀ (slotOf n_max gm₀ b' j)
  same_slabs : ∀ j < gm₀ (gmQIdx b) * slabSize n_max,
    arr (slotOf n_max gm b j) = arr₀ (slotOf n_max gm₀ b j)
  low_tail : ∀ u < slabSize n_max - k,
    arr (slotOf n_max gm b (gm₀ (gmQIdx b) * slabSize n_max + u)) =
      arr₀ (slotOf n_max gm₀ b (gm₀ (gmQIdx b) * slabSize n_max + u))
  high_tail : ∀ u < slabSize n_max - k,
    arr (slotOf n_max gm b (gm₀ (gmQIdx b) * slabSize n_max + (slabSize n_max + u))) =
      arr₀ (slotOf n_max gm₀ b (gm₀ (gmQIdx b) * slabSize n_max + (slabSize n_max + u)))
  shifted_tail : ∀ u, slabSize n_max - k ≤ u → u < slabSize n_max →
    arr (slotOf n_max gm b (gm₀ (gmQIdx b) * slabSize n_max + u)) =
      arr₀ (slotOf n_max gm₀ b (gm₀ (gmQIdx b) * slabSize n_max + (slabSize n_max + u)))
  new_slab : ∀ k' < k,
    arr (gm₀ 0 * slabSize n_max + k') =
      arr₀ (slotOf n_max gm₀ b (gm₀ (gmQIdx b) * slabSize n_max + (slabSize n_max - 1 - k')))

theorem promoteArrInv_zero {α : Type*} (n_max b : ℕ) (gm₀ : ℕ → ℕ) (arr₀ : ℕ → α) :
    PromoteArrInv n_max b gm₀ arr₀ 0 gm₀ arr₀ := by
  refine ⟨fun _ _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun u h1 h2 => by omega, fun k' hk' => by omega⟩

theorem promoteArrInv_step {α : Type*} {n_max b k : ℕ} {gm₀ gm : ℕ → ℕ} {arr₀ arr : ℕ → α}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max) (hk : k < slabSize n_max)
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0))
    (h0 : gm 0 = gm₀ 0)
    (hq : ∀ b' < numBuckets n_max, gm (gmQIdx b') = gm₀ (gmQIdx b'))
    (hr_other : ∀ b' < numBuckets n_max, b' ≠ b → gm (gmRIdx b') = gm₀ (gmRIdx b'))
    (hr_b : gm (gmRIdx b) = 2 * slabSize n_max - k)
    (htot : gm 0 * slabSize n_max + k + gm 1 ≤ n_max)
    (harr : PromoteArrInv n_max b gm₀ arr₀ k gm arr) :
    let u := (slabSize n_max - 1) - k
    let r_top := slabSize n_max + u
    let g_u := (n_max - 1) - gm (gmTailPtrIdx n_max b u)
    let g_top := (n_max - 1) - gm (gmTailPtrIdx n_max b r_top)
    let g_del := (n_max - 1) - gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1))
    let g_last := (n_max - 1) - (gm 1 - 1)
    let g_slab := gm 0 * slabSize n_max + k
    let arr₁ := Function.update arr g_u (arr g_top)
    let arr₂ := Function.update arr₁ g_del (arr₁ g_last)
    let arr₃ := Function.update arr₂ g_slab (arr g_u)
    PromoteArrInv n_max b gm₀ arr₀ (k + 1) (gmRemoveTail n_max gm b) arr₃ := by
  intro u r_top g_u g_top g_del g_last g_slab arr₁ arr₂ arr₃
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  have hTcap : tailCapPerBucket n_max = 2 * slabSize n_max := by
    unfold tailCapPerBucket; rw [ite_eq_right hb0]
  have hr_pos : 1 ≤ gm (gmRIdx b) := by omega
  have htot0 : gm 0 * slabSize n_max + gm 1 ≤ n_max := by omega
  have hpres := gmRemoveTail_preserves_nonTail hb hr_pos htail
  have ⟨hupd_slot, hupd_low⟩ := update_slotOf_gmRemoveTail arr₁ hb_pos hb hr_pos htail hslab htot0
  have hu_lt_r : u < gm (gmRIdx b) := by omega
  have hr_top_lt_r : r_top < gm (gmRIdx b) := by omega
  have hu_cap : u < tailCapPerBucket n_max := by omega
  have htu_lt_gm1 : gm (gmTailPtrIdx n_max b u) < gm 1 := htail.ptr_lt b hb u hu_lt_r
  have hgu_eq_slot : g_u = slotOf n_max gm b (gm₀ (gmQIdx b) * slabSize n_max + u) := by
    unfold slotOf
    rw [ite_eq_right hb0, hq b hb]
    have hnot : ¬(gm₀ (gmQIdx b) * slabSize n_max + u < gm₀ (gmQIdx b) * slabSize n_max) := by omega
    rw [ite_eq_right hnot, Nat.add_sub_cancel_left]
  have hgtop_eq_slot : g_top = slotOf n_max gm b (gm₀ (gmQIdx b) * slabSize n_max + r_top) := by
    unfold slotOf
    rw [ite_eq_right hb0, hq b hb]
    have hnot : ¬(gm₀ (gmQIdx b) * slabSize n_max + r_top < gm₀ (gmQIdx b) * slabSize n_max) := by
      omega
    rw [ite_eq_right hnot, Nat.add_sub_cancel_left]
  -- Helper: for any active slot `(b', j)` in `gmRemoveTail n_max gm b`, `slotOf ≠ g_slab`,
  -- so `arr₃ (slotOf gm' b' j) = arr₁ (slotOf gm b' j)`.
  have harr3_slot : ∀ b' < numBuckets n_max, ∀ j < bCount n_max (gmRemoveTail n_max gm b) b',
      arr₃ (slotOf n_max (gmRemoveTail n_max gm b) b' j) = arr₁ (slotOf n_max gm b' j) := by
    intro b' hb' j hj
    have hne_slab : slotOf n_max (gmRemoveTail n_max gm b) b' j ≠ g_slab := by
      unfold bCount at hj
      simp only [hb0, ↓reduceIte, hb'] at hj
      unfold slotOf
      rw [ite_eq_right hb0]
      split_ifs with hj_slab
      · have hs_lt : j / slabSize n_max < gmRemoveTail n_max gm b (gmQIdx b') :=
          Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
        have ⟨_, hslab'⟩ := slabBijection_gmRemoveTail hb hr_pos htail hslab
        have hp_lt : slabPtrOf n_max (gmRemoveTail n_max gm b) b' (j / slabSize n_max) < gm 0 := by
          rw [← hpres.1]
          exact hslab'.ptr_lt b' hb' _ hs_lt
        have hmod_lt : j % slabSize n_max < slabSize n_max := Nat.mod_lt j hK_pos
        have h1 : (slabPtrOf n_max (gmRemoveTail n_max gm b) b' (j / slabSize n_max) + 1) *
            slabSize n_max ≤ gm 0 * slabSize n_max := Nat.mul_le_mul_right _ hp_lt
        rw [Nat.add_one_mul] at h1
        dsimp only [g_slab]
        omega
      · have hr'_lt : j - gmRemoveTail n_max gm b (gmQIdx b') * slabSize n_max <
            gmRemoveTail n_max gm b (gmRIdx b') := by omega
        have htail' := tailBijection_gmRemoveTail hb hr_pos htail
        have ht'_lt : gmRemoveTail n_max gm b
            (gmTailPtrIdx n_max b' (j - gmRemoveTail n_max gm b (gmQIdx b') * slabSize n_max)) <
            gm 1 - 1 := by
          rw [← hpres.2.1]
          exact htail'.ptr_lt b' hb' _ hr'_lt
        dsimp only [g_slab]
        omega
    dsimp only [arr₃]
    rw [Function.update_of_ne hne_slab]
    exact hupd_slot b' hb' j hj
  -- Helper: any slab slot `< gm 0 * K` is `≠ g_u`.
  have hslab_ne_gu : ∀ b' < numBuckets n_max, ∀ j < gm₀ (gmQIdx b') * slabSize n_max,
      slotOf n_max gm b' j ≠ g_u := by
    intro b' hb' j hj
    unfold slotOf
    rw [ite_eq_right hb0, hq b' hb', ite_eq_left hj]
    have hs_lt : j / slabSize n_max < gm (gmQIdx b') := by
      rw [hq b' hb']
      exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hp_lt : slabPtrOf n_max gm b' (j / slabSize n_max) < gm 0 := hslab.ptr_lt b' hb' _ hs_lt
    have hmod_lt : j % slabSize n_max < slabSize n_max := Nat.mod_lt j hK_pos
    have h1 : (slabPtrOf n_max gm b' (j / slabSize n_max) + 1) * slabSize n_max ≤
        gm 0 * slabSize n_max := Nat.mul_le_mul_right _ hp_lt
    rw [Nat.add_one_mul] at h1
    dsimp only [g_u]
    omega
  -- Helper: any tail slot `(b', r')` with `(b', r') ≠ (b, u)` is `≠ g_u`.
  have htail_ne_gu : ∀ b' < numBuckets n_max, ∀ r' < gm (gmRIdx b'),
      (b' ≠ b ∨ r' ≠ u) →
      slotOf n_max gm b' (gm₀ (gmQIdx b') * slabSize n_max + r') ≠ g_u := by
    intro b' hb' r' hr' hne
    unfold slotOf
    rw [ite_eq_right hb0, hq b' hb']
    have hnot : ¬(gm₀ (gmQIdx b') * slabSize n_max + r' < gm₀ (gmQIdx b') * slabSize n_max) := by
      omega
    rw [ite_eq_right hnot, Nat.add_sub_cancel_left]
    have ht'_lt : gm (gmTailPtrIdx n_max b' r') < gm 1 := htail.ptr_lt b' hb' r' hr'
    have hr'_cap : r' < tailCapPerBucket n_max := lt_of_lt_of_le hr' (htail.r_le b' hb')
    dsimp only [g_u]
    intro heq
    have ht_eq : gm (gmTailPtrIdx n_max b' r') = gm (gmTailPtrIdx n_max b u) := by omega
    have hown := congrArg (gm ∘ gmTailOwnerIdx n_max) ht_eq
    dsimp only [Function.comp_apply] at hown
    rw [htail.owner_ptr b' hb' r' hr', htail.owner_ptr b hb u hu_lt_r] at hown
    obtain ⟨hb_eq, hr_eq⟩ := flat_descriptor_inj hr'_cap hu_cap hown
    rcases hne with hne_b | hne_r
    · exact hne_b hb_eq
    · exact hne_r hr_eq
  have hbc_other : ∀ b' < numBuckets n_max, b' ≠ b →
      bCount n_max (gmRemoveTail n_max gm b) b' = bCount n_max gm₀ b' := by
    intro b' hb' hne
    unfold bCount
    simp only [hb0, ↓reduceIte, hb']
    rw [hpres.2.2.2.2.1 b' hb', hq b' hb', hpres.2.2.2.1 b' hb' hne, hr_other b' hb' hne]
  have hbc_b : bCount n_max (gmRemoveTail n_max gm b) b =
      gm₀ (gmQIdx b) * slabSize n_max + (2 * slabSize n_max - (k + 1)) := by
    unfold bCount
    simp only [hb0, ↓reduceIte, hb]
    rw [hpres.2.2.2.2.1 b hb, hq b hb, hpres.2.2.1, hr_b]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b' hb' hne j hj
    have hj' : j < bCount n_max (gmRemoveTail n_max gm b) b' := by
      rwa [hbc_other b' hb' hne]
    rw [harr3_slot b' hb' j hj']
    dsimp only [arr₁]
    by_cases hj_slab : j < gm₀ (gmQIdx b') * slabSize n_max
    · rw [Function.update_of_ne (hslab_ne_gu b' hb' j hj_slab)]
      exact harr.other_bucket b' hb' hne j hj
    · set r' := j - gm₀ (gmQIdx b') * slabSize n_max
      have hj_eq : j = gm₀ (gmQIdx b') * slabSize n_max + r' := by omega
      have hr'_lt : r' < gm (gmRIdx b') := by
        unfold bCount at hj
        simp only [hb0, ↓reduceIte, hb'] at hj
        rw [hr_other b' hb' hne]
        dsimp only [r']
        omega
      rw [hj_eq, Function.update_of_ne (htail_ne_gu b' hb' r' hr'_lt (Or.inl hne)), ← hj_eq]
      exact harr.other_bucket b' hb' hne j hj
  · intro j hj
    have hj' : j < bCount n_max (gmRemoveTail n_max gm b) b := by rw [hbc_b]; omega
    rw [harr3_slot b hb j hj']
    dsimp only [arr₁]
    rw [Function.update_of_ne (hslab_ne_gu b hb j hj)]
    exact harr.same_slabs j hj
  · intro u' hu'
    have hj' : gm₀ (gmQIdx b) * slabSize n_max + u' <
        bCount n_max (gmRemoveTail n_max gm b) b := by rw [hbc_b]; omega
    rw [harr3_slot b hb _ hj']
    dsimp only [arr₁]
    have hu'_lt_r : u' < gm (gmRIdx b) := by omega
    have hu'_ne : u' ≠ u := by dsimp only [u]; omega
    rw [Function.update_of_ne (htail_ne_gu b hb u' hu'_lt_r (Or.inr hu'_ne))]
    exact harr.low_tail u' (by omega)
  · intro u' hu'
    have hj' : gm₀ (gmQIdx b) * slabSize n_max + (slabSize n_max + u') <
        bCount n_max (gmRemoveTail n_max gm b) b := by rw [hbc_b]; omega
    rw [harr3_slot b hb _ hj']
    dsimp only [arr₁]
    have hr'_lt_r : slabSize n_max + u' < gm (gmRIdx b) := by omega
    have hr'_ne : slabSize n_max + u' ≠ u := by dsimp only [u]; omega
    rw [Function.update_of_ne (htail_ne_gu b hb (slabSize n_max + u') hr'_lt_r (Or.inr hr'_ne))]
    exact harr.high_tail u' (by omega)
  · intro u' hu'_ge hu'_lt
    have hj' : gm₀ (gmQIdx b) * slabSize n_max + u' <
        bCount n_max (gmRemoveTail n_max gm b) b := by rw [hbc_b]; omega
    rw [harr3_slot b hb _ hj']
    dsimp only [arr₁]
    by_cases heq : u' = u
    · subst heq
      rw [← hgu_eq_slot, Function.update_self, hgtop_eq_slot]
      exact harr.high_tail u (by dsimp only [u]; omega)
    · have hu'_lt_r : u' < gm (gmRIdx b) := by omega
      rw [Function.update_of_ne (htail_ne_gu b hb u' hu'_lt_r (Or.inr heq))]
      exact harr.shifted_tail u' (by dsimp only [u] at heq; omega) hu'_lt
  · intro k' hk'
    dsimp only [arr₃]
    by_cases heq : k' = k
    · subst heq
      rw [← h0, Function.update_self, hgu_eq_slot]
      exact harr.low_tail u (by dsimp only [u]; omega)
    · have hne_slab : gm₀ 0 * slabSize n_max + k' ≠ g_slab := by
        dsimp only [g_slab]; rw [h0]; omega
      have hlt_low : gm₀ 0 * slabSize n_max + k' < n_max - gm 1 := by
        rw [← h0]; omega
      have hne_gu : gm₀ 0 * slabSize n_max + k' ≠ g_u := by
        dsimp only [g_u]; rw [← h0]; omega
      rw [Function.update_of_ne hne_slab]
      dsimp only [arr₂, g_del, g_last]
      rw [hupd_low _ hlt_low]
      dsimp only [arr₁]
      rw [Function.update_of_ne hne_gu]
      exact harr.new_slab k' (by omega)

/-- Loop invariant at step `k ≤ slabSize n_max` of `promoteLoopProg`. -/
structure PromoteLoopInv (U V w₀ n_max h_space base b : ℕ) (s₀ : Memory.State)
    (k : ℕ) (s : Memory.State) : Prop where
  b_lt : b < numBuckets n_max
  k_le : k ≤ slabSize n_max
  frontier_eq : s.frontier = s₀.frontier
  mem_out : ∀ a, ¬(base + offQuot h_space ≤ a ∧
    a < base + totalSpace U V w₀ n_max h_space) → s.mem a = s₀.mem a
  lm_eq : lmAt base U V w₀ n_max h_space s.mem = lmAt base U V w₀ n_max h_space s₀.mem
  tail_bij : TailBijection n_max (gmAt base U V w₀ n_max h_space s.mem)
    (fun b' => gmAt base U V w₀ n_max h_space s.mem (gmRIdx b'))
    (gmAt base U V w₀ n_max h_space s.mem 1)
  slab_bij : SlabBijection n_max (gmAt base U V w₀ n_max h_space s.mem)
    (fun b' => gmAt base U V w₀ n_max h_space s.mem (gmQIdx b'))
    (gmAt base U V w₀ n_max h_space s.mem 0)
  gm0_eq : gmAt base U V w₀ n_max h_space s.mem 0 = gmAt base U V w₀ n_max h_space s₀.mem 0
  gm1_eq : gmAt base U V w₀ n_max h_space s.mem 1 + k = gmAt base U V w₀ n_max h_space s₀.mem 1
  rb_eq : gmAt base U V w₀ n_max h_space s.mem (gmRIdx b) = 2 * slabSize n_max - k
  r_other : ∀ b' < numBuckets n_max, b' ≠ b →
    gmAt base U V w₀ n_max h_space s.mem (gmRIdx b') =
      gmAt base U V w₀ n_max h_space s₀.mem (gmRIdx b')
  q_eq : ∀ b' < numBuckets n_max,
    gmAt base U V w₀ n_max h_space s.mem (gmQIdx b') =
      gmAt base U V w₀ n_max h_space s₀.mem (gmQIdx b')
  tot_le : gmAt base U V w₀ n_max h_space s.mem 0 * slabSize n_max + k +
    gmAt base U V w₀ n_max h_space s.mem 1 ≤ n_max
  quot_inv : PromoteArrInv n_max b (gmAt base U V w₀ n_max h_space s₀.mem)
    (quotAt base U w₀ n_max h_space s₀.mem) k
    (gmAt base U V w₀ n_max h_space s.mem) (quotAt base U w₀ n_max h_space s.mem)
  val_inv : PromoteArrInv n_max b (gmAt base U V w₀ n_max h_space s₀.mem)
    (valAt base U V w₀ n_max h_space s₀.mem) k
    (gmAt base U V w₀ n_max h_space s.mem) (valAt base U V w₀ n_max h_space s.mem)

theorem promoteStepInv_of_loopInv {U V w₀ n_max h_space base b k : ℕ} {s₀ s : Memory.State}
    (hinv : PromoteLoopInv U V w₀ n_max h_space base b s₀ k s) (hk : k < slabSize n_max) :
    PromoteStepInv U V w₀ n_max h_space base b k s :=
  ⟨hinv.b_lt, hk, hinv.tail_bij, hinv.slab_bij, hinv.rb_eq, hinv.tot_le⟩

theorem promoteLoopInv_step {U V w₀ n_max h_space base b k : ℕ} {s₀ s : Memory.State}
    (hw : 0 < w₀) (hb_pos : 0 < bucketBits n_max)
    (hinv : PromoteLoopInv U V w₀ n_max h_space base b s₀ k s) (hk : k < slabSize n_max) :
    let s' := (Memory.spec 0).clientState s
      (promoteStepProg U V w₀ n_max h_space ((base, b), k))
    (Memory.spec 0).clientResult s
      (promoteStepProg U V w₀ n_max h_space ((base, b), k)) = k + 1 ∧
    PromoteLoopInv U V w₀ n_max h_space base b s₀ (k + 1) s' := by
  have hstep := promoteStepInv_of_loopInv hinv hk
  obtain ⟨hres, hf, hout, hq, hv, hl, hgm⟩ :=
    promoteStepProg_effect hw hb_pos s hstep
  have hrb_eq : gmAt base U V w₀ n_max h_space s.mem (gmRIdx b) = 2 * slabSize n_max - k :=
    hinv.rb_eq
  have hr_pos : 1 ≤ gmAt base U V w₀ n_max h_space s.mem (gmRIdx b) := by omega
  have hpres := gmRemoveTail_preserves_nonTail hinv.b_lt hr_pos hinv.tail_bij
  have htail' := tailBijection_gmRemoveTail hinv.b_lt hr_pos hinv.tail_bij
  have ⟨_, hslab'⟩ := slabBijection_gmRemoveTail hinv.b_lt hr_pos hinv.tail_bij hinv.slab_bij
  have hgm1_pos : 1 ≤ gmAt base U V w₀ n_max h_space s.mem 1 := by
    have := r_le_ntails_of_tailBijection hinv.tail_bij hinv.b_lt
    omega
  refine ⟨hres, ⟨hinv.b_lt, by omega, hf.trans hinv.frontier_eq,
    fun a ha => (hout a ha).trans (hinv.mem_out a ha), hl.trans hinv.lm_eq,
    by rw [hgm]; exact htail', by rw [hgm]; exact hslab',
    by rw [hgm, hpres.1, hinv.gm0_eq],
    by rw [hgm, hpres.2.1]; have := hinv.gm1_eq; omega,
    by rw [hgm, hpres.2.2.1, hrb_eq]; omega,
    fun b' hb' hne => by rw [hgm, hpres.2.2.2.1 b' hb' hne, hinv.r_other b' hb' hne],
    fun b' hb' => by rw [hgm, hpres.2.2.2.2.1 b' hb', hinv.q_eq b' hb'],
    by rw [hgm, hpres.1, hpres.2.1]; have := hinv.tot_le; omega,
    ?_, ?_⟩⟩
  · rw [hgm, hq]
    exact promoteArrInv_step hb_pos hinv.b_lt hk hinv.tail_bij hinv.slab_bij
      hinv.gm0_eq hinv.q_eq hinv.r_other hinv.rb_eq hinv.tot_le hinv.quot_inv
  · rw [hgm, hv]
    exact promoteArrInv_step hb_pos hinv.b_lt hk hinv.tail_bij hinv.slab_bij
      hinv.gm0_eq hinv.q_eq hinv.r_other hinv.rb_eq hinv.tot_le hinv.val_inv

theorem iterate_promoteStepProg_spec {U V w₀ n_max h_space w base b : ℕ} {s₀ : Memory.State}
    (hw : 0 < w₀) (hb_pos : 0 < bucketBits n_max) :
    ∀ m k (s : Memory.State),
      k + m ≤ slabSize n_max →
      PromoteLoopInv U V w₀ n_max h_space base b s₀ k s →
      PromoteLoopInv U V w₀ n_max h_space base b s₀ (k + m)
        ((Memory.spec 0).clientState s
          (iterate (promoteStepProg U V w₀ n_max h_space) (base, b) m k)) ∧
      memoryCost (iterate (promoteStepProg U V w₀ n_max h_space) (base, b) m k) s = 66 * m ∧
      (DictEnvGen w (mkDictParams U V w₀ n_max h_space) base →
        iterationSafe (promoteStepProg U V w₀ n_max h_space)
          (fun w x s => PromoteStepPre U V w₀ n_max h_space w x.1.1 x.1.2 x.2 s)
          w (base, b) m k s) := by
  intro m
  induction m with
  | zero =>
    intro k s _ hinv
    simp only [iterate, Nat.add_zero, Nat.mul_zero, memoryCost_pure, iterationSafe]
    exact ⟨hinv, trivial, fun _ => trivial⟩
  | succ m ih =>
    intro k s hkm hinv
    have hk_lt : k < slabSize n_max := by omega
    obtain ⟨hres, hinv'⟩ := promoteLoopInv_step hw hb_pos hinv hk_lt
    obtain ⟨hfinal, hcost, hsafe⟩ := ih (k + 1)
      ((Memory.spec 0).clientState s (promoteStepProg U V w₀ n_max h_space ((base, b), k)))
      (by omega) hinv'
    refine ⟨?_, ?_, ?_⟩
    · unfold iterate
      rw [StateTransitionSpec.clientState_bind, hres]
      rw [show k + (m + 1) = (k + 1) + m by omega]
      exact hfinal
    · simp only [iterate, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
        memoryCost_promoteStepProg, hres, hcost]
      omega
    · intro hdenv
      simp only [iterationSafe, hres]
      exact ⟨⟨hdenv, promoteStepInv_of_loopInv hinv hk_lt, hb_pos⟩, hsafe hdenv⟩

/-- Parameter-free wrapper for `iterate promoteStepGenProg` with signature
`(((dp, (base, b)), k), m) → Memory.Prog ℕ` matching `Realizes.iterate₀`. -/
def promoteLoopGenProg (d : ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ) : Memory.Prog ℕ :=
  iterate promoteStepGenProg d.1.1 d.2 d.1.2

/-- Wrapper for `iterate (promoteStepProg U V w n_max h_space)` with signature
`(((base, b), k), m) → Memory.Prog ℕ` matching `Realizes.iterate₀`. -/
def promoteLoopProg (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ :=
  iterate (promoteStepProg U V w n_max h_space) d.1.1 d.2 d.1.2

@[simp] theorem iterate_promoteStepGenProg_mk (U V w n_max h_space : ℕ)
    (d : ℕ × ℕ) (m k : ℕ) :
    iterate promoteStepGenProg (mkDictParams U V w n_max h_space, d) m k =
      iterate (promoteStepProg U V w n_max h_space) d m k := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih =>
    unfold iterate
    rw [promoteStepGenProg_mk]
    congr 1
    funext s'
    exact ih s'

@[simp] theorem promoteLoopGenProg_mk (U V w n_max h_space : ℕ)
    (d1 : ℕ × ℕ) (d2 d3 : ℕ) :
    promoteLoopGenProg (((mkDictParams U V w n_max h_space, d1), d2), d3) =
      promoteLoopProg U V w n_max h_space ((d1, d2), d3) :=
  iterate_promoteStepGenProg_mk U V w n_max h_space d1 d3 d2

@[simp] theorem iterationSafe_promoteStepGenProg_mk (U V w₀ n_max h_space w : ℕ)
    (d : ℕ × ℕ) (m k : ℕ) (s : Memory.State) :
    iterationSafe promoteStepGenProg PromoteStepGenPre w
        (mkDictParams U V w₀ n_max h_space, d) m k s ↔
      iterationSafe (promoteStepProg U V w₀ n_max h_space)
        (fun w x s => PromoteStepPre U V w₀ n_max h_space w x.1.1 x.1.2 x.2 s)
        w d m k s := by
  induction m generalizing k s with
  | zero => exact Iff.rfl
  | succ m ih =>
    unfold iterationSafe
    rw [promoteStepGenPre_mk, promoteStepGenProg_mk]
    exact and_congr_right fun _ => ih _ _

theorem realizes_promoteLoopGen :
    Realizes .exact promoteLoopGenProg
      (WordEncoding.encode (α := ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d s =>
        iterationSafe promoteStepGenProg PromoteStepGenPre w d.1.1 d.2 d.1.2 s)
      (fun _ _ => 0) :=
  Realizes.iterate₀ (WordEncoding.encode (α := DictParams × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ))
    realizes_promoteStepGen
    one_le_memoryCost_promoteStepGenProg

/-- Parameter-free `Memory.Prog` operation promoting `K = slabSize n_max` tail items of bucket
`b = d.2.2` at `base = d.2.1` into a new full slab. -/
def promoteSlabGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog Unit := do
  let _ ← promoteLoopGenProg ((d, 0), dpSlabSize d.1)
  gmPushSlabGenProg d

/-- `Memory.Prog` operation promoting `K = slabSize n_max` tail items of bucket `b = d.2` at
`base = d.1` (`gm (gmRIdx b) = 2 * K`) into a new full slab via `promoteLoopProg` followed by
`gmPushSlabProg`. -/
def promoteSlabProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog Unit := do
  let _ ← promoteLoopProg U V w n_max h_space ((d, 0), slabSize n_max)
  gmPushSlabProg U V w n_max h_space d

@[simp] theorem promoteSlabGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    promoteSlabGenProg (mkDictParams U V w n_max h_space, d) =
      promoteSlabProg U V w n_max h_space d := by
  simp only [promoteSlabGenProg, promoteSlabProg, p_slabSize_mk,
    promoteLoopGenProg_mk, gmPushSlabGenProg_mk]

/-- Pure entry invariant for `promoteSlabProg`. -/
@[expose]
def PromoteSlabInv (U V w₀ n_max h_space base b : ℕ) (s : Memory.State) : Prop :=
  let gm := gmAt base U V w₀ n_max h_space s.mem
  b < numBuckets n_max ∧
  TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1) ∧
  SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0) ∧
  gm (gmRIdx b) = 2 * slabSize n_max ∧
  (∀ b' < numBuckets n_max, b' ≠ b →
    gm (gmRIdx b') < tailCapPerBucket n_max ∧
    (0 < gm (gmQIdx b') → 1 ≤ gm (gmRIdx b'))) ∧
  gm 0 * slabSize n_max + gm 1 ≤ n_max

/-- Precondition for `promoteSlabProg` in `Realizes`. -/
@[expose]
def PromoteSlabPre (U V w₀ n_max h_space w base b : ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  PromoteSlabInv U V w₀ n_max h_space base b s ∧
  0 < bucketBits n_max

/-- Parameter-free precondition for `promoteSlabGenProg`. -/
@[expose]
def PromoteSlabGenPre (w : ℕ) (d : DictParams × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w d.1 d.2.1 ∧
  PromoteSlabInv (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) d.2.1 d.2.2 s ∧
  0 < bucketBits (dpNMax d.1)

@[simp] theorem promoteSlabGenPre_mk (U V w₀ n_max h_space w : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    PromoteSlabGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      PromoteSlabPre U V w₀ n_max h_space w d.1 d.2 s := Iff.rfl

theorem promoteLoopInv_zero {U V w₀ n_max h_space base b : ℕ} {s₀ : Memory.State}
    (hpre : PromoteSlabInv U V w₀ n_max h_space base b s₀) :
    PromoteLoopInv U V w₀ n_max h_space base b s₀ 0 s₀ := by
  rcases hpre with ⟨hb, htail, hslab, hrb, _, htot⟩
  refine ⟨hb, Nat.zero_le _, rfl, fun _ _ => rfl, rfl, htail, hslab, rfl,
    Nat.add_zero _, by omega, fun _ _ _ => rfl, fun _ _ => rfl, by omega,
    promoteArrInv_zero _ _ _ _, promoteArrInv_zero _ _ _ _⟩

theorem slotOf_gmPushSlab_preserve {α : Type*} {n_max b : ℕ} {gm₀ gm : ℕ → ℕ} {arr₀ arr : ℕ → α}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0))
    (h0 : gm 0 = gm₀ 0)
    (hq : ∀ b' < numBuckets n_max, gm (gmQIdx b') = gm₀ (gmQIdx b'))
    (hr_other : ∀ b' < numBuckets n_max, b' ≠ b → gm (gmRIdx b') = gm₀ (gmRIdx b'))
    (hr_b : gm (gmRIdx b) = slabSize n_max)
    (_hr0_b : gm₀ (gmRIdx b) = 2 * slabSize n_max)
    (htot : (gm 0 + 1) * slabSize n_max + gm 1 ≤ n_max)
    (harr : PromoteArrInv n_max b gm₀ arr₀ (slabSize n_max) gm arr) :
    ∀ b' < numBuckets n_max, ∀ j < bCount n_max (gmPushSlab n_max gm b) b',
      arr (slotOf n_max (gmPushSlab n_max gm b) b' j) = arr₀ (slotOf n_max gm₀ b' j) := by
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  have htot' : (gm 0 + 1) * slabSize n_max ≤ n_max := by omega
  have hp_lt : gm 0 < maxFullSlabs n_max := nslabs_lt_maxFullSlabs_of_mul_le hb_pos htot'
  have hf := gmPushSlab_fields gm hb
  have ⟨hptr, _⟩ := slabBijection_gmPushSlab hb hp_lt hslab
  intro b' hb' j hj
  unfold bCount at hj
  simp only [hb0, ↓reduceIte, hb'] at hj
  by_cases hbeq : b' = b
  · subst b'
    have hq_b_push : gmPushSlab n_max gm b (gmQIdx b) = gm (gmQIdx b) + 1 := by
      rw [hf.2.2.2.2.1 b hb, ite_eq_left rfl]
    rw [hq_b_push, hf.2.2.1 b hb, hq b hb, hr_b] at hj
    conv_lhs => unfold slotOf
    rw [ite_eq_right hb0, hq_b_push, hq b hb]
    split_ifs with hj_slab
    · by_cases hj_old : j < gm₀ (gmQIdx b) * slabSize n_max
      · have hs_lt : j / slabSize n_max < gmPushSlab n_max gm b (gmQIdx b) := by
          rw [hq_b_push, hq b hb]
          exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj_slab)
        have hs_ne : j / slabSize n_max ≠ gm (gmQIdx b) := by
          rw [hq b hb]
          have : j / slabSize n_max < gm₀ (gmQIdx b) :=
            Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
          omega
        rw [hptr b hb (j / slabSize n_max) hs_lt, ite_eq_right (fun h => hs_ne h.2)]
        have hslot_eq :
            slabPtrOf n_max gm b (j / slabSize n_max) * slabSize n_max +
              (slabSize n_max - 1 - j % slabSize n_max) = slotOf n_max gm b j := by
          unfold slotOf
          rw [ite_eq_right hb0, hq b hb, ite_eq_left hj_old]
        rw [hslot_eq]
        exact harr.same_slabs j hj_old
      · set u := j - gm₀ (gmQIdx b) * slabSize n_max
        have hu_lt : u < slabSize n_max := by
          rw [Nat.add_one_mul] at hj_slab; dsimp only [u]; omega
        have hj_eq : j = gm₀ (gmQIdx b) * slabSize n_max + u := by dsimp only [u]; omega
        have hs_lt : j / slabSize n_max < gmPushSlab n_max gm b (gmQIdx b) := by
          rw [hq_b_push, hq b hb]
          exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj_slab)
        have hs_eq : j / slabSize n_max = gm (gmQIdx b) := by
          rw [hq b hb, hj_eq, Nat.mul_comm, Nat.mul_add_div hK_pos,
            Nat.div_eq_of_lt hu_lt, Nat.add_zero]
        have hmod_eq : j % slabSize n_max = u := by
          rw [hj_eq, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hu_lt]
        rw [hptr b hb (j / slabSize n_max) hs_lt, ite_eq_left ⟨rfl, hs_eq⟩, hmod_eq, h0]
        have hnew := harr.new_slab (slabSize n_max - 1 - u) (by omega)
        rw [show slabSize n_max - 1 - (slabSize n_max - 1 - u) = u by omega, ← hj_eq] at hnew
        exact hnew
    · set u := j - (gm₀ (gmQIdx b) + 1) * slabSize n_max
      have hu_lt : u < slabSize n_max := by dsimp only [u]; omega
      have hu_cap : u < tailCapPerBucket n_max := by
        unfold tailCapPerBucket; rw [ite_eq_right hb0]; omega
      have hd_lt : b * tailCapPerBucket n_max + u < maxTailItems n_max :=
        mul_tailCapPerBucket_add_lt_maxTailItems hb hu_cap
      have hptr_tail : gmPushSlab n_max gm b (gmTailPtrIdx n_max b u) =
          gm (gmTailPtrIdx n_max b u) :=
        hf.2.2.2.1 _ (by unfold gmTailPtrIdx gmTailPtrFlatIdx; omega)
          (by unfold gmTailPtrIdx gmTailPtrFlatIdx gmSlabMetaBase gmTailOwnerBase; omega)
      rw [hptr_tail]
      have hslot_gm : n_max - 1 - gm (gmTailPtrIdx n_max b u) =
          slotOf n_max gm b (gm₀ (gmQIdx b) * slabSize n_max + u) := by
        unfold slotOf
        rw [ite_eq_right hb0, hq b hb]
        have hnot : ¬(gm₀ (gmQIdx b) * slabSize n_max + u < gm₀ (gmQIdx b) * slabSize n_max) := by
          omega
        rw [ite_eq_right hnot, Nat.add_sub_cancel_left]
      rw [hslot_gm, harr.shifted_tail u (by omega) hu_lt]
      congr 2
      dsimp only [u]
      rw [Nat.add_one_mul] at hj_slab ⊢
      omega
  · have hq_b'_push : gmPushSlab n_max gm b (gmQIdx b') = gm (gmQIdx b') := by
      rw [hf.2.2.2.2.1 b' hb', ite_eq_right hbeq]
    rw [hq_b'_push, hf.2.2.1 b' hb', hq b' hb', hr_other b' hb' hbeq] at hj
    have hslot_eq : slotOf n_max (gmPushSlab n_max gm b) b' j = slotOf n_max gm b' j := by
      unfold slotOf
      rw [ite_eq_right hb0, ite_eq_right hb0, hq_b'_push, hq b' hb']
      split_ifs with hj_slab
      · have hs_lt : j / slabSize n_max < gmPushSlab n_max gm b (gmQIdx b') := by
          rw [hq_b'_push, hq b' hb']
          exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj_slab)
        rw [hptr b' hb' (j / slabSize n_max) hs_lt, ite_eq_right (fun h => hbeq h.1)]
      · have hr'_lt : j - gm₀ (gmQIdx b') * slabSize n_max < gm (gmRIdx b') := by
          rw [hr_other b' hb' hbeq]; omega
        have hr'_cap : j - gm₀ (gmQIdx b') * slabSize n_max < tailCapPerBucket n_max :=
          lt_of_lt_of_le hr'_lt (htail.r_le b' hb')
        have hd'_lt : b' * tailCapPerBucket n_max + (j - gm₀ (gmQIdx b') * slabSize n_max) <
            maxTailItems n_max :=
          mul_tailCapPerBucket_add_lt_maxTailItems hb' hr'_cap
        rw [hf.2.2.2.1 _ (by unfold gmTailPtrIdx gmTailPtrFlatIdx; omega)
          (by unfold gmTailPtrIdx gmTailPtrFlatIdx gmSlabMetaBase gmTailOwnerBase; omega)]
    rw [hslot_eq]
    exact harr.other_bucket b' hb' hbeq j (by unfold bCount; simp [hb0, hb', hj])

/-- Under `PromoteSlabInv U V w n_max h_space base b s` (`gm (gmRIdx b) = 2 * slabSize n_max`),
`promoteSlabProg` runs in `memoryCost ≤ 66 * slabSize n_max + 38` and preserves `frontier`, `lmAt`,
and memory outside `[base + offQuot h_space, base + totalSpace U V w n_max h_space)`. It restores
`SlotStoreInv n_max gm'` with `gm' (gmQIdx b) = gm₀ (gmQIdx b) + 1`,
`gm' (gmRIdx b) = slabSize n_max`, and unchanged `(gmQIdx b', gmRIdx b')` for `b' ≠ b`. It also
preserves `bCount` and every logical `(quotAt, valAt)` entry at `slotOf` across all buckets. -/
theorem promoteSlabProg_effect {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    (s : Memory.State)
    (hpre : PromoteSlabInv U V w n_max h_space base b s) :
    let gm₀ := gmAt base U V w n_max h_space s.mem
    let s' := (Memory.spec 0).clientState s (promoteSlabProg U V w n_max h_space (base, b))
    let gm' := gmAt base U V w n_max h_space s'.mem
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    SlotStoreInv n_max gm' ∧
    gm' (gmQIdx b) = gm₀ (gmQIdx b) + 1 ∧
    gm' (gmRIdx b) = slabSize n_max ∧
    (∀ b' < numBuckets n_max, b' ≠ b →
      gm' (gmQIdx b') = gm₀ (gmQIdx b') ∧ gm' (gmRIdx b') = gm₀ (gmRIdx b')) ∧
    (∀ b' < numBuckets n_max, bCount n_max gm' b' = bCount n_max gm₀ b') ∧
    (∀ b' < numBuckets n_max, ∀ j < bCount n_max gm' b',
      quotAt base U w n_max h_space s'.mem (slotOf n_max gm' b' j) =
        quotAt base U w n_max h_space s.mem (slotOf n_max gm₀ b' j) ∧
      valAt base U V w n_max h_space s'.mem (slotOf n_max gm' b' j) =
        valAt base U V w n_max h_space s.mem (slotOf n_max gm₀ b' j)) ∧
    memoryCost (promoteSlabProg U V w n_max h_space (base, b)) s ≤
      66 * slabSize n_max + 38 := by
  intro gm₀ s' gm'
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  have hloop0 := promoteLoopInv_zero hpre
  obtain ⟨hloopK, hcost_loop, _⟩ :=
    iterate_promoteStepProg_spec (w := w) hw hb_pos (slabSize n_max) 0 s
      (by omega) hloop0
  rw [Nat.zero_add] at hloopK
  set s₁ := (Memory.spec 0).clientState s
    (promoteLoopProg U V w n_max h_space (((base, b), 0), slabSize n_max))
  change PromoteLoopInv U V w n_max h_space base b s (slabSize n_max) s₁ at hloopK
  have htot1 : (gmAt base U V w n_max h_space s₁.mem 0 + 1) * slabSize n_max ≤ n_max := by
    have := hloopK.tot_le
    rw [Nat.add_one_mul]
    omega
  have hp_lt1 : gmAt base U V w n_max h_space s₁.mem 0 < maxFullSlabs n_max :=
    nslabs_lt_maxFullSlabs_of_mul_le hb_pos htot1
  obtain ⟨hf_push, hout_push, hq_push, hv_push, hl_push, hgm_push⟩ :=
    gmPushSlabProg_effect (U := U) (V := V) (h_space := h_space)
      hw hb_pos hloopK.b_lt s₁ hloopK.slab_bij hp_lt1
  have hst : s' =
      (Memory.spec 0).clientState s₁ (gmPushSlabProg U V w n_max h_space (base, b)) := by
    change (Memory.spec 0).clientState s (promoteSlabProg U V w n_max h_space (base, b)) = _
    unfold promoteSlabProg
    rw [StateTransitionSpec.clientState_bind]
  let gm₁ := gmAt base U V w n_max h_space s₁.mem
  have hgm'_eq : gm' = gmPushSlab n_max gm₁ b := by
    dsimp only [gm']; rw [hst, hgm_push]
  have hf_fields := gmPushSlab_fields gm₁ hloopK.b_lt
  have ⟨_, hslab2⟩ := slabBijection_gmPushSlab hloopK.b_lt hp_lt1 hloopK.slab_bij
  have htail2 := tailBijection_gmPushSlab hloopK.b_lt hloopK.tail_bij
  have hqb : gm' (gmQIdx b) = gm₀ (gmQIdx b) + 1 := by
    rw [hgm'_eq, hf_fields.2.2.2.2.1 b hloopK.b_lt, ite_eq_left rfl]
    dsimp only [gm₁, gm₀]
    rw [hloopK.q_eq b hloopK.b_lt]
  have hrb : gm' (gmRIdx b) = slabSize n_max := by
    rw [hgm'_eq, hf_fields.2.2.1 b hloopK.b_lt]
    dsimp only [gm₁]
    rw [hloopK.rb_eq]
    omega
  have hother : ∀ b' < numBuckets n_max, b' ≠ b →
      gm' (gmQIdx b') = gm₀ (gmQIdx b') ∧ gm' (gmRIdx b') = gm₀ (gmRIdx b') := by
    intro b' hb' hne
    rw [hgm'_eq, hf_fields.2.2.2.2.1 b' hb', ite_eq_right hne, hf_fields.2.2.1 b' hb']
    dsimp only [gm₁, gm₀]
    rw [hloopK.q_eq b' hb', hloopK.r_other b' hb' hne]
    exact ⟨rfl, rfl⟩
  have hinv2 : SlotStoreInv n_max gm' := by
    refine ⟨fun h0 => by omega, fun _ => by rw [hgm'_eq]; exact htail2,
      fun _ => by rw [hgm'_eq]; exact hslab2, fun _ b' hb' => ?_, fun _ => ?_⟩
    · by_cases hbeq : b' = b
      · subst b'
        rw [hrb]
        unfold tailCapPerBucket
        rw [ite_eq_right hb0]
        omega
      · rw [(hother b' hb' hbeq).1, (hother b' hb' hbeq).2]
        exact hpre.2.2.2.2.1 b' hb' hbeq
    · rw [hgm'_eq, hf_fields.1, hf_fields.2.1, Nat.add_one_mul]
      have := hloopK.tot_le
      omega
  have hbc : ∀ b' < numBuckets n_max, bCount n_max gm' b' = bCount n_max gm₀ b' := by
    intro b' hb'
    unfold bCount
    simp only [hb0, ↓reduceIte, hb']
    by_cases hbeq : b' = b
    · subst b'
      rw [hqb, hrb]
      dsimp only [gm₀]
      rw [hpre.2.2.2.1, Nat.add_one_mul]
      omega
    · rw [(hother b' hb' hbeq).1, (hother b' hb' hbeq).2]
  have htot_push : (gm₁ 0 + 1) * slabSize n_max + gm₁ 1 ≤ n_max := by
    rw [Nat.add_one_mul]; have := hloopK.tot_le; omega
  have hrb1 : gm₁ (gmRIdx b) = slabSize n_max := by
    dsimp only [gm₁]; rw [hloopK.rb_eq]; omega
  have hq_slot := slotOf_gmPushSlab_preserve hb_pos hloopK.b_lt hloopK.tail_bij hloopK.slab_bij
    hloopK.gm0_eq hloopK.q_eq hloopK.r_other hrb1 hpre.2.2.2.1 htot_push hloopK.quot_inv
  have hv_slot := slotOf_gmPushSlab_preserve hb_pos hloopK.b_lt hloopK.tail_bij hloopK.slab_bij
    hloopK.gm0_eq hloopK.q_eq hloopK.r_other hrb1 hpre.2.2.2.1 htot_push hloopK.val_inv
  refine ⟨by rw [hst, hf_push, hloopK.frontier_eq],
    fun a ha => by
      have ha' : ¬(base + offGM U V w n_max h_space ≤ a ∧
          a < base + totalSpace U V w n_max h_space) := by
        dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega
      rw [hst, hout_push a ha', hloopK.mem_out a ha],
    by rw [hst, hl_push, hloopK.lm_eq],
    hinv2, hqb, hrb, hother, hbc,
    fun b' hb' j hj => ?_, ?_⟩
  · rw [hst, hq_push, hv_push, hgm'_eq]
    rw [hgm'_eq] at hj
    exact ⟨hq_slot b' hb' j hj, hv_slot b' hb' j hj⟩
  · unfold promoteSlabProg
    rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    change memoryCost
        (iterate (promoteStepProg U V w n_max h_space) (base, b) (slabSize n_max) 0) s +
      memoryCost (gmPushSlabProg U V w n_max h_space (base, b)) s₁ ≤ _
    rw [hcost_loop]
    have hpush_cost := memoryCost_gmPushSlabProg_le U V w n_max h_space (base, b) s₁
    omega

theorem realizes_promoteSlabGen :
    Realizes .exact promoteSlabGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      PromoteSlabGenPre
      (fun _ _ => 0) := by
  have hloop := realizes_promoteLoopGen
  have hpush := realizes_gmPushSlabGen
  refine Realizes.congr (p := fun d : DictParams × (ℕ × ℕ) => do
      let k0 ← pure 0
      let _ ← promoteLoopGenProg ((d, k0), dpSlabSize d.1)
      gmPushSlabGenProg d) ?_
    (fun d => by simp only [promoteSlabGenProg, pure_bind])
  realizeDictWith [promoteSlabGenPre_mk, iterationSafe_promoteStepGenProg_mk,
    promoteLoopGenProg_mk, gmPushSlabGenPre_mk, gmPushSlabGenProg_mk]
  · exact (iterate_promoteStepProg_spec hw h.2.2 (slabSize n_max) 0 s
      (by omega) (promoteLoopInv_zero h.2.1)).2.2 h.1
  · rcases d with ⟨base, b⟩
    dsimp only at h
    have hloopK := (iterate_promoteStepProg_spec (w := w) hw h.2.2 (slabSize n_max) 0 s
      (by omega) (promoteLoopInv_zero h.2.1)).1
    rw [Nat.zero_add] at hloopK
    have htot1 : (gmAt base U V w₀ n_max h_space
        ((Memory.spec 0).clientState s
          (promoteLoopProg U V w₀ n_max h_space (((base, b), 0), slabSize n_max))).mem 0 + 1) *
        slabSize n_max ≤ n_max := by
      unfold promoteLoopProg
      dsimp only
      have := hloopK.tot_le
      rw [Nat.add_one_mul]
      omega
    unfold GmPushSlabPre
    exact ⟨h.1, hloopK.slab_bij, h.2.1.1, nslabs_lt_maxFullSlabs_of_mul_le h.2.2 htot1, h.2.2⟩

end Cslib.DataStructure.Dictionary.WordRAM.Succinct

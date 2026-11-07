/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabMove
import Complexity.Tactic.Realize

/-!
# `Memory.Prog` Slab Demotion Loop (`demoteStepProg`, `demoteLoopProg`, `demoteSlabProg`)

This module implements the `K = slabSize n_max`-step slab-demotion loop for the fixed-capacity
succinct dictionary using `Memory.Prog`, `iterate`, and the `realize` tactic (`Realizes.iterate₀`).
When a bucket `b` has `gm (gmRIdx b) = 0` tail items and `1 ≤ gm (gmQIdx b)` full slabs after
removing its last tail item, `demoteSlabProg` moves the `K` items from the top slab
`p_del = gm (gmSlabTopIdx b)` into the tail of bucket `b`, compacts the physical slab pool by
copying the `K` items of `p_last = gm 0 - 1` into `p_del`, and pops the top slab descriptor via
`gmPopSlabProg`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.demoteStepProg`: single step `k < slabSize n_max`
  of slab demotion.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.demoteLoopProg`: `K`-step iteration of
  `demoteStepProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.demoteSlabProg`: complete slab demotion
  (`demoteLoopProg` followed by `gmPopSlabProg`).
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.DemoteSlabInv`: entry invariant for
  `demoteSlabProg` (`gm (gmRIdx b) = 0 ∧ 0 < gm (gmQIdx b)`).

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.demoteStepProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_demoteStepGen`: single-step invariant
  preservation and `Realizes` certificate for `demoteStepProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.demoteSlabProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_demoteSlabGen`: full-slab demotion
  invariant preservation, `O(K)` `memoryCost`, and `Realizes` certificate for `demoteSlabProg`.
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

/-! ## Section 1: Single step `demoteStepProg` -/

/-- Parameter-free single step `k < slabSize n_max` of slab demotion for
`x = ((dp, (base, b)), k)`. -/
def demoteStepGenProg (x : (DictParams × (ℕ × ℕ)) × ℕ) : Memory.Prog ℕ := do
  let dp := x.1.1
  let base := x.1.2.1
  let b := x.1.2.2
  let k := x.2
  let u := dpSlabSizeSubOne dp - k
  let p_del ← readGMGenProg (dp, (base, 4 + 3 * b + 2))
  let n_slabs ← readGMGenProg (dp, (base, 0))
  let p_last := n_slabs - 1
  let g_del := p_del * dpSlabSize dp + u
  let g_last := p_last * dpSlabSize dp + u
  let q_del ← readQuotGenProg (dp, (base, g_del))
  let v_del ← readValGenProg (dp, (base, g_del))
  let q_last ← readQuotGenProg (dp, (base, g_last))
  let v_last ← readValGenProg (dp, (base, g_last))
  let t_new ← appendTailItemGenProg (dp, (base, b))
  let g_tail := dpNMaxSubOne dp - t_new
  writeQuotGenProg (dp, ((base, g_del), q_last))
  writeValGenProg (dp, ((base, g_del), v_last))
  writeQuotGenProg (dp, ((base, g_tail), q_del))
  let _ ← writeValGenProg (dp, ((base, g_tail), v_del))
  pure (k + 1)

/-- One iteration (`0 ≤ k < slabSize n_max`) of the slab-demotion loop for bucket `b = x.1.2`
at `base = x.1.1` with loop index `k = x.2`.
For `u = (slabSize n_max - 1) - k`, `p_del = gm (gmSlabTopIdx b)`, and `p_last = gm 0 - 1`:
1. Reads `(q_del, v_del)` at `g_del = p_del * slabSize n_max + u` and `(q_last, v_last)` at
   `g_last = p_last * slabSize n_max + u`.
2. Appends a new tail item `t_new = gm 1` to bucket `b` (`g_tail = (n_max - 1) - t_new`).
3. Writes `(q_last, v_last)` to `g_del` first, and `(q_del, v_del)` to `g_tail` second,
   then returns `k + 1`. -/
def demoteStepProg (U V w n_max h_space : ℕ) (x : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let base := x.1.1
  let b := x.1.2
  let k := x.2
  let u := (slabSize n_max - 1) - k
  let p_del ← readGMProg U V w n_max h_space (base, 4 + 3 * b + 2)
  let n_slabs ← readGMProg U V w n_max h_space (base, 0)
  let p_last := n_slabs - 1
  let g_del := p_del * slabSize n_max + u
  let g_last := p_last * slabSize n_max + u
  let q_del ← readQuotProg U w n_max h_space (base, g_del)
  let v_del ← readValProg U V w n_max h_space (base, g_del)
  let q_last ← readQuotProg U w n_max h_space (base, g_last)
  let v_last ← readValProg U V w n_max h_space (base, g_last)
  let t_new ← appendTailItemProg U V w n_max h_space (base, b)
  let g_tail := (n_max - 1) - t_new
  writeQuotProg U w n_max h_space ((base, g_del), q_last)
  writeValProg U V w n_max h_space ((base, g_del), v_last)
  writeQuotProg U w n_max h_space ((base, g_tail), q_del)
  let _ ← writeValProg U V w n_max h_space ((base, g_tail), v_del)
  pure (k + 1)

@[simp] theorem demoteStepGenProg_mk (U V w n_max h_space : ℕ) (d1 : ℕ × ℕ) (d2 : ℕ) :
    demoteStepGenProg ((mkDictParams U V w n_max h_space, d1), d2) =
      demoteStepProg U V w n_max h_space (d1, d2) := by
  simp only [demoteStepGenProg, demoteStepProg, p_slabSizeSubOne_mk, p_slabSize_mk,
    p_nMaxSubOne_mk, readGMGenProg_mk, readQuotGenProg_mk, readValGenProg_mk,
    writeQuotGenProg_mk, writeValGenProg_mk, appendTailItemGenProg_mk]

@[simp]
theorem memoryCost_demoteStepProg (U V w n_max h_space : ℕ) (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (demoteStepProg U V w n_max h_space x) s = 48 := by
  simp [demoteStepProg, -bind_pure_comp, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]

theorem one_le_memoryCost_demoteStepGenProg (x : (DictParams × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (demoteStepGenProg x) s := by
  unfold demoteStepGenProg readGMGenProg readPackedGenProg
  dsimp only
  rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_readPackedProg]
  omega

/-- Pure state invariant for step `k` (`k < slabSize n_max`) of `demoteStepProg`. -/
@[expose]
def DemoteStepInv (U V w₀ n_max h_space base b k : ℕ) (s : Memory.State) : Prop :=
  let gm := gmAt base U V w₀ n_max h_space s.mem
  b < numBuckets n_max ∧
  k < slabSize n_max ∧
  TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1) ∧
  SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0) ∧
  gm (gmRIdx b) = k ∧
  1 ≤ gm (gmQIdx b) ∧
  (gm 0 - 1) * slabSize n_max + (slabSize n_max - k) + gm 1 ≤ n_max

/-- Precondition for `demoteStepProg` in `Realizes`. -/
@[expose]
def DemoteStepPre (U V w₀ n_max h_space w base b k : ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  DemoteStepInv U V w₀ n_max h_space base b k s ∧
  0 < bucketBits n_max

/-- Parameter-free precondition for `demoteStepGenProg`. -/
@[expose]
def DemoteStepGenPre (w : ℕ) (x : (DictParams × (ℕ × ℕ)) × ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w x.1.1 x.1.2.1 ∧
  DemoteStepInv (dpU x.1.1) (dpV x.1.1) (dpW x.1.1) (dpNMax x.1.1) (dpHSpace x.1.1)
    x.1.2.1 x.1.2.2 x.2 s ∧
  0 < bucketBits (dpNMax x.1.1)

@[simp] theorem demoteStepGenPre_mk (U V w₀ n_max h_space w : ℕ) (d1 : ℕ × ℕ) (d2 : ℕ)
    (s : Memory.State) :
    DemoteStepGenPre w ((mkDictParams U V w₀ n_max h_space, d1), d2) s ↔
      DemoteStepPre U V w₀ n_max h_space w d1.1 d1.2 d2 s := Iff.rfl

theorem demoteStepProg_effect {U V w n_max h_space base b k : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    (s : Memory.State)
    (hpre : DemoteStepInv U V w n_max h_space base b k s) :
    let gm := gmAt base U V w n_max h_space s.mem
    let qA := quotAt base U w n_max h_space s.mem
    let vA := valAt base U V w n_max h_space s.mem
    let u := (slabSize n_max - 1) - k
    let p_del := gm (gmSlabTopIdx b)
    let p_last := gm 0 - 1
    let g_del := p_del * slabSize n_max + u
    let g_last := p_last * slabSize n_max + u
    let g_tail := (n_max - 1) - gm 1
    let s' := (Memory.spec 0).clientState s
      (demoteStepProg U V w n_max h_space ((base, b), k))
    (Memory.spec 0).clientResult s
      (demoteStepProg U V w n_max h_space ((base, b), k)) = k + 1 ∧
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem =
      Function.update (Function.update qA g_del (qA g_last)) g_tail (qA g_del) ∧
    valAt base U V w n_max h_space s'.mem =
      Function.update (Function.update vA g_del (vA g_last)) g_tail (vA g_del) ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem = gmAppendTail n_max gm b := by
  intro gm qA vA u p_del p_last g_del g_last g_tail s'
  rcases hpre with ⟨hb, hk, htail, hslab, hrb, hqb_pos, htot⟩
  change TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1) at htail
  change SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0) at hslab
  change gm (gmRIdx b) = k at hrb
  change 1 ≤ gm (gmQIdx b) at hqb_pos
  change (gm 0 - 1) * slabSize n_max + (slabSize n_max - k) + gm 1 ≤ n_max at htot
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  have hu_lt : u < slabSize n_max := by dsimp only [u]; omega
  have htop_eq := hslab.top_eq b hb (gm (gmQIdx b) - 1) (by omega) (by omega)
  have hp_del_lt : p_del < gm 0 := by
    dsimp only [p_del]; rw [htop_eq]; exact hslab.ptr_lt b hb (gm (gmQIdx b) - 1) (by omega)
  have hgm0_pos : 1 ≤ gm 0 := by omega
  have hp_last_lt : p_last < gm 0 := by dsimp only [p_last]; omega
  have htop_idx_lt : 4 + 3 * b + 2 < globalMetaLen n_max := gmSlabTopIdx_lt hb_pos hb
  have h0_idx_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
  have hg_last_lt : g_last < n_max := by
    dsimp only [g_last, p_last, u]; omega
  have hg_del_lt : g_del < n_max := by
    have hle : p_del ≤ p_last := by dsimp only [p_last]; omega
    have hmul : p_del * slabSize n_max ≤ p_last * slabSize n_max := Nat.mul_le_mul_right _ hle
    dsimp only [g_del, g_last] at hg_last_lt ⊢
    omega
  have hr_cap : gm (gmRIdx b) < tailCapPerBucket n_max := by
    unfold tailCapPerBucket; rw [ite_eq_right hb0, hrb]; omega
  have ht_cap : gm 1 < maxTailItems n_max := ntails_lt_maxTailItems_of_r_lt hb hr_cap htail
  have hg_tail_lt : g_tail < n_max := by
    have : (gm 0 - 1) * slabSize n_max ≥ 0 := Nat.zero_le _
    dsimp only [g_tail]; omega
  have hq_del_lt : qA g_del < 2 ^ quotientBits U n_max := quotAt_lt _ _ _ _ _ _ _
  have hv_del_lt : vA g_del < 2 ^ valBits V := valAt_lt _ _ _ _ _ _ _ _
  have hq_last_lt : qA g_last < 2 ^ quotientBits U n_max := quotAt_lt _ _ _ _ _ _ _
  have hv_last_lt : vA g_last < 2 ^ valBits V := valAt_lt _ _ _ _ _ _ _ _
  let s₁ := (Memory.spec 0).clientState s
    (appendTailItemProg U V w n_max h_space (base, b))
  obtain ⟨hres_app, hf1, hout1, hq1, hv1, hl1, hg1⟩ :=
    appendTailItemProg_effect (U := U) (V := V) (h_space := h_space)
      hw hb_pos hb s htail hr_cap
  let s₂ := (Memory.spec 0).clientState s₁
    (writeQuotProg U w n_max h_space ((base, g_del), qA g_last))
  obtain ⟨hf2, hout2, hq2, hv2, hl2, hg2⟩ :=
    writeQuotProg_effect (base := base) (V := V) (h_space := h_space)
      hw hg_del_lt hq_last_lt s₁
  let s₃ := (Memory.spec 0).clientState s₂
    (writeValProg U V w n_max h_space ((base, g_del), vA g_last))
  obtain ⟨hf3, hout3, hq3, hv3, hl3, hg3⟩ :=
    writeValProg_effect (base := base) (h_space := h_space)
      hw hg_del_lt hv_last_lt s₂
  let s₄ := (Memory.spec 0).clientState s₃
    (writeQuotProg U w n_max h_space ((base, g_tail), qA g_del))
  obtain ⟨hf4, hout4, hq4, hv4, hl4, hg4⟩ :=
    writeQuotProg_effect (base := base) (V := V) (h_space := h_space)
      hw hg_tail_lt hq_del_lt s₃
  let s₅ := (Memory.spec 0).clientState s₄
    (writeValProg U V w n_max h_space ((base, g_tail), vA g_del))
  obtain ⟨hf5, hout5, hq5, hv5, hl5, hg5⟩ :=
    writeValProg_effect (base := base) (h_space := h_space)
      hw hg_tail_lt hv_del_lt s₄
  have hres_eq : (Memory.spec 0).clientResult s
      (demoteStepProg U V w n_max h_space ((base, b), k)) = k + 1 := by
    unfold demoteStepProg
    dsimp only
    rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      clientResult_readGMProg s (by exact htop_idx_lt),
      StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      clientResult_readGMProg s (by exact h0_idx_lt),
      StateTransitionSpec.clientResult_bind, clientState_readQuotProg,
      clientResult_readQuotProg s (by exact hg_del_lt),
      StateTransitionSpec.clientResult_bind, clientState_readValProg,
      clientResult_readValProg s (by exact hg_del_lt),
      StateTransitionSpec.clientResult_bind, clientState_readQuotProg,
      clientResult_readQuotProg s (by exact hg_last_lt),
      StateTransitionSpec.clientResult_bind, clientState_readValProg,
      clientResult_readValProg s (by exact hg_last_lt)]
    simp only [StateTransitionSpec.clientResult_bind]
    rfl
  have hst : s' = s₅ := by
    change (Memory.spec 0).clientState s
      (demoteStepProg U V w n_max h_space ((base, b), k)) = s₅
    unfold demoteStepProg
    dsimp only
    rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
      clientResult_readGMProg s (by exact htop_idx_lt),
      StateTransitionSpec.clientState_bind, clientState_readGMProg,
      clientResult_readGMProg s (by exact h0_idx_lt),
      StateTransitionSpec.clientState_bind, clientState_readQuotProg,
      clientResult_readQuotProg s (by exact hg_del_lt),
      StateTransitionSpec.clientState_bind, clientState_readValProg,
      clientResult_readValProg s (by exact hg_del_lt),
      StateTransitionSpec.clientState_bind, clientState_readQuotProg,
      clientResult_readQuotProg s (by exact hg_last_lt),
      StateTransitionSpec.clientState_bind, clientState_readValProg,
      clientResult_readValProg s (by exact hg_last_lt),
      StateTransitionSpec.clientState_bind, hres_app]
    repeat rw [StateTransitionSpec.clientState_bind]
    rfl
  rw [hst]
  refine ⟨hres_eq, by rw [hf5, hf4, hf3, hf2, hf1], ?_,
    by rw [hq5, hq4, hq3, hq2, hq1],
    by rw [hv5, hv4, hv3, hv2, hv1],
    by rw [hl5, hl4, hl3, hl2, hl1],
    by rw [hg5, hg4, hg3, hg2, hg1]⟩
  intro a ha
  rw [hout5 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega),
    hout4 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega),
    hout3 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega),
    hout2 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega),
    hout1 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega)]

private theorem demoteStep_bounds {U V w₀ n_max h_space w base b k : ℕ}
    {s : Memory.State}
    (hw : 0 < w₀)
    (h : DemoteStepPre U V w₀ n_max h_space w base b k s) :
    let u := (slabSize n_max - 1) - k
    let e_pdel := (Memory.spec 0).clientResult s
      (readGMProg U V w₀ n_max h_space (base, 4 + 3 * b + 2))
    let s1 := (Memory.spec 0).clientState s
      (readGMProg U V w₀ n_max h_space (base, 4 + 3 * b + 2))
    let e_nslabs := (Memory.spec 0).clientResult s1
      (readGMProg U V w₀ n_max h_space (base, 0))
    let s2 := (Memory.spec 0).clientState s1
      (readGMProg U V w₀ n_max h_space (base, 0))
    let e_plast := e_nslabs - 1
    let g_del := e_pdel * slabSize n_max + u
    let g_last := e_plast * slabSize n_max + u
    let s3 := (Memory.spec 0).clientState s2
      (readQuotProg U w₀ n_max h_space (base, g_del))
    let q_del := (Memory.spec 0).clientResult s2
      (readQuotProg U w₀ n_max h_space (base, g_del))
    let s4 := (Memory.spec 0).clientState s3
      (readValProg U V w₀ n_max h_space (base, g_del))
    let v_del := (Memory.spec 0).clientResult s3
      (readValProg U V w₀ n_max h_space (base, g_del))
    let s5 := (Memory.spec 0).clientState s4
      (readQuotProg U w₀ n_max h_space (base, g_last))
    let q_last := (Memory.spec 0).clientResult s4
      (readQuotProg U w₀ n_max h_space (base, g_last))
    let s6 := (Memory.spec 0).clientState s5
      (readValProg U V w₀ n_max h_space (base, g_last))
    let v_last := (Memory.spec 0).clientResult s5
      (readValProg U V w₀ n_max h_space (base, g_last))
    let e_tnew := (Memory.spec 0).clientResult s6
      (appendTailItemProg U V w₀ n_max h_space (base, b))
    let g_tail := (n_max - 1) - e_tnew
    k ≤ slabSize n_max - 1 ∧
    4 + 3 * b + 2 < globalMetaLen n_max ∧
    0 < globalMetaLen n_max ∧
    1 ≤ e_nslabs ∧
    g_del < n_max ∧
    g_last < n_max ∧
    AppendTailItemPre U V w₀ n_max h_space w base b s6 ∧
    e_tnew ≤ n_max - 1 ∧
    g_tail < n_max ∧
    q_last < 2 ^ quotientBits U n_max ∧
    v_last < 2 ^ valBits V ∧
    q_del < 2 ^ quotientBits U n_max ∧
    v_del < 2 ^ valBits V ∧
    k + 1 ≤ max n_max 1 := by
  rcases h with ⟨hdict, ⟨hb, hk, htail, hslab, hrb, hqb_pos, htot⟩, hb_pos⟩
  intro u e_pdel s1 e_nslabs s2 e_plast g_del g_last
    s3 q_del s4 v_del s5 q_last s6 v_last e_tnew g_tail
  let gm := gmAt base U V w₀ n_max h_space s.mem
  change b < numBuckets n_max at hb
  change k < slabSize n_max at hk
  change TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1) at htail
  change SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0) at hslab
  change gm (gmRIdx b) = k at hrb
  change 1 ≤ gm (gmQIdx b) at hqb_pos
  change (gm 0 - 1) * slabSize n_max + (slabSize n_max - k) + gm 1 ≤ n_max at htot
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  have hK_le : slabSize n_max ≤ max n_max 1 := slabSize_le_max_n_one n_max
  have htop_eq := hslab.top_eq b hb (gm (gmQIdx b) - 1) (by omega) (by omega)
  have hp_del_lt : gm (gmSlabTopIdx b) < gm 0 := by
    rw [htop_eq]; exact hslab.ptr_lt b hb (gm (gmQIdx b) - 1) (by omega)
  have hgm0_pos : 1 ≤ gm 0 := by omega
  have htop_idx_lt : 4 + 3 * b + 2 < globalMetaLen n_max := gmSlabTopIdx_lt hb_pos hb
  have h0_idx_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
  have hr_cap : gm (gmRIdx b) < tailCapPerBucket n_max := by
    unfold tailCapPerBucket; rw [ite_eq_right hb0, hrb]; omega
  have hepdel : e_pdel = gm (gmSlabTopIdx b) := clientResult_readGMProg s htop_idx_lt
  have hs1 : s1 = s := rfl
  have henslabs : e_nslabs = gm 0 := by
    dsimp only [e_nslabs]; rw [hs1]; exact clientResult_readGMProg s h0_idx_lt
  have hs2 : s2 = s := rfl
  have hg_last_lt : g_last < n_max := by
    dsimp only [g_last, e_plast, u]; rw [henslabs]; omega
  have hg_del_lt : g_del < n_max := by
    have hle : e_pdel ≤ e_plast := by dsimp only [e_plast]; rw [hepdel, henslabs]; omega
    have hmul : e_pdel * slabSize n_max ≤ e_plast * slabSize n_max :=
      Nat.mul_le_mul_right _ hle
    dsimp only [g_del, g_last] at hg_last_lt ⊢
    omega
  have hs6 : s6 = s := rfl
  obtain ⟨hres_app, _⟩ :=
    appendTailItemProg_effect (U := U) (V := V) (h_space := h_space)
      hw hb_pos hb s htail hr_cap
  have hetnew : e_tnew = gm 1 := by
    dsimp only [e_tnew]; rw [hs6]; exact hres_app
  have ht_lt_n : gm 1 < n_max := by
    have : (gm 0 - 1) * slabSize n_max ≥ 0 := Nat.zero_le _
    omega
  have hq_del : q_del = quotAt base U w₀ n_max h_space s.mem g_del :=
    clientResult_readQuotProg s hg_del_lt
  have hv_del : v_del = valAt base U V w₀ n_max h_space s.mem g_del :=
    clientResult_readValProg s hg_del_lt
  have hq_last : q_last = quotAt base U w₀ n_max h_space s.mem g_last :=
    clientResult_readQuotProg s hg_last_lt
  have hv_last : v_last = valAt base U V w₀ n_max h_space s.mem g_last :=
    clientResult_readValProg s hg_last_lt
  refine ⟨by omega, htop_idx_lt, h0_idx_lt, by rw [henslabs]; exact hgm0_pos,
    hg_del_lt, hg_last_lt,
    by rw [hs6]; exact ⟨hdict, htail, hb, hr_cap, hb_pos⟩,
    by rw [hetnew]; omega,
    by dsimp only [g_tail]; rw [hetnew]; omega,
    by rw [hq_last]; exact quotAt_lt _ _ _ _ _ _ _,
    by rw [hv_last]; exact valAt_lt _ _ _ _ _ _ _ _,
    by rw [hq_del]; exact quotAt_lt _ _ _ _ _ _ _,
    by rw [hv_del]; exact valAt_lt _ _ _ _ _ _ _ _,
    by omega⟩

theorem realizes_demoteStepGen :
    Realizes .exact demoteStepGenProg
      (WordEncoding.encode (α := (DictParams × (ℕ × ℕ)) × ℕ)) (WordEncoding.encode (α := ℕ))
      DemoteStepGenPre
      (fun _ _ => 0) := by
  have hrg := realizes_readGMGen
  have hrq := realizes_readQuotGen
  have hwq := realizes_writeQuotGen
  have hrv := realizes_readValGen
  have hwv := realizes_writeValGen
  have happ := realizes_appendTailItemGen
  refine Realizes.congr (p := fun d : (DictParams × (ℕ × ℕ)) × ℕ => do
      let u ← pure (dpSlabSizeSubOne d.1.1 - d.2)
      let top_idx ← pure (4 + 3 * d.1.2.2 + 2)
      let p_del ← readGMGenProg (d.1.1, (d.1.2.1, top_idx))
      let i0 ← pure 0
      let n_slabs ← readGMGenProg (d.1.1, (d.1.2.1, i0))
      let p_last ← pure (n_slabs - 1)
      let g_del ← pure (p_del * dpSlabSize d.1.1 + u)
      let g_last ← pure (p_last * dpSlabSize d.1.1 + u)
      let q_del ← readQuotGenProg (d.1.1, (d.1.2.1, g_del))
      let v_del ← readValGenProg (d.1.1, (d.1.2.1, g_del))
      let q_last ← readQuotGenProg (d.1.1, (d.1.2.1, g_last))
      let v_last ← readValGenProg (d.1.1, (d.1.2.1, g_last))
      let t_new ← appendTailItemGenProg (d.1.1, d.1.2)
      let g_tail ← pure (dpNMaxSubOne d.1.1 - t_new)
      writeQuotGenProg (d.1.1, ((d.1.2.1, g_del), q_last))
      writeValGenProg (d.1.1, ((d.1.2.1, g_del), v_last))
      writeQuotGenProg (d.1.1, ((d.1.2.1, g_tail), q_del))
      let _ ← writeValGenProg (d.1.1, ((d.1.2.1, g_tail), v_del))
      pure (d.2 + 1)) ?_
    (fun d => by simp only [demoteStepGenProg, pure_bind])
  realize
  all_goals (
    rcases d with ⟨⟨dp, d1⟩, d2⟩
    let d := (d1, d2)
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1
    simpDictParamsWith [demoteStepGenPre_mk, appendTailItemGenPre_mk, appendTailItemGenProg_mk]
  )
  · exact (demoteStep_bounds hw h).1
  · exact fits_of_le_globalMetaLen h.1 h.2.2 hw hnU hU
      (le_of_lt (demoteStep_bounds hw h).2.1)
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact h.1
  · exact (demoteStep_bounds hw h).2.1
  · exact (demoteStep_bounds hw h).2.2.1
  · exact (demoteStep_bounds hw h).2.2.2.1
  · exact fits_of_le_max_n_one h.1 hw hnU hU
      (le_trans (le_of_lt (demoteStep_bounds hw h).2.2.2.2.1) (le_max_left n_max 1))
  · exact fits_of_le_max_n_one h.1 hw hnU hU
      (le_trans (le_of_lt (demoteStep_bounds hw h).2.2.2.2.2.1) (le_max_left n_max 1))
  · exact (demoteStep_bounds hw h).2.2.2.2.1
  · exact (demoteStep_bounds hw h).2.2.2.2.2.1
  · exact (demoteStep_bounds hw h).2.2.2.2.2.2.1
  · exact (demoteStep_bounds hw h).2.2.2.2.2.2.2.1
  · exact (demoteStep_bounds hw h).2.2.2.2.2.2.2.2.1
  · exact fits_of_le_max_n_one h.1 hw hnU hU
      (demoteStep_bounds hw h).2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## Section 2: `DemoteArrInv`, `DemoteLoopInv`, and `demoteSlabProg` -/

/-- Array payload invariant at iteration `k ≤ slabSize n_max` of the slab-demotion loop. -/
structure DemoteArrInv {α : Type*} (n_max b : ℕ) (gm₀ : ℕ → ℕ) (arr₀ : ℕ → α)
    (k : ℕ) (gm : ℕ → ℕ) (arr : ℕ → α) : Prop where
  other_slabs : ∀ p < gm₀ 0 - 1, p ≠ gm₀ (gmSlabTopIdx b) → ∀ u < slabSize n_max,
    arr (p * slabSize n_max + u) = arr₀ (p * slabSize n_max + u)
  other_tails : ∀ t < gm₀ 1,
    arr ((n_max - 1) - t) = arr₀ ((n_max - 1) - t)
  rem_del : ∀ u < slabSize n_max - k,
    arr (gm₀ (gmSlabTopIdx b) * slabSize n_max + u) =
      arr₀ (gm₀ (gmSlabTopIdx b) * slabSize n_max + u)
  rem_last : ∀ u < slabSize n_max - k,
    arr ((gm₀ 0 - 1) * slabSize n_max + u) = arr₀ ((gm₀ 0 - 1) * slabSize n_max + u)
  moved_last : gm₀ (gmSlabTopIdx b) < gm₀ 0 - 1 →
    ∀ u, slabSize n_max - k ≤ u → u < slabSize n_max →
      arr (gm₀ (gmSlabTopIdx b) * slabSize n_max + u) =
        arr₀ ((gm₀ 0 - 1) * slabSize n_max + u)
  demoted_tail : ∀ r < k,
    arr ((n_max - 1) - gm (gmTailPtrIdx n_max b r)) =
      arr₀ (gm₀ (gmSlabTopIdx b) * slabSize n_max + (slabSize n_max - 1 - r))

theorem demoteArrInv_zero {α : Type*} (n_max b : ℕ) (gm₀ : ℕ → ℕ) (arr₀ : ℕ → α) :
    DemoteArrInv n_max b gm₀ arr₀ 0 gm₀ arr₀ := by
  refine ⟨fun _ _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ u h1 h2 => by omega, fun r hr => by omega⟩

theorem demoteArrInv_step {α : Type*} {n_max b k : ℕ} {gm₀ gm : ℕ → ℕ} {arr₀ arr : ℕ → α}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (hk : k < slabSize n_max)
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0))
    (h0 : gm 0 = gm₀ 0)
    (h1_ge : gm₀ 1 ≤ gm 1)
    (htop_b : gm (gmSlabTopIdx b) = gm₀ (gmSlabTopIdx b))
    (hr_b : gm (gmRIdx b) = k)
    (hqb_pos : 1 ≤ gm (gmQIdx b))
    (htot : (gm 0 - 1) * slabSize n_max + (slabSize n_max - k) + gm 1 ≤ n_max)
    (harr : DemoteArrInv n_max b gm₀ arr₀ k gm arr) :
    let u_k := (slabSize n_max - 1) - k
    let g_del := gm (gmSlabTopIdx b) * slabSize n_max + u_k
    let g_last := (gm 0 - 1) * slabSize n_max + u_k
    let g_tail := (n_max - 1) - gm 1
    let arr' := Function.update (Function.update arr g_del (arr g_last)) g_tail (arr g_del)
    DemoteArrInv n_max b gm₀ arr₀ (k + 1) (gmAppendTail n_max gm b) arr' := by
  intro u_k g_del g_last g_tail arr'
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  have hu_k_lt : u_k < slabSize n_max - k := by dsimp only [u_k]; omega
  have hu_k_slab : u_k < slabSize n_max := by dsimp only [u_k]; omega
  have htop_eq := hslab.top_eq b hb (gm (gmQIdx b) - 1) (by omega) (by omega)
  have hp_del_lt : gm (gmSlabTopIdx b) < gm 0 := by
    rw [htop_eq]; exact hslab.ptr_lt b hb (gm (gmQIdx b) - 1) (by omega)
  have hgm0_pos : 1 ≤ gm 0 := by omega
  have hr_cap : gm (gmRIdx b) < tailCapPerBucket n_max := by
    unfold tailCapPerBucket; rw [ite_eq_right hb0, hr_b]; omega
  have ht_cap : gm 1 < maxTailItems n_max := ntails_lt_maxTailItems_of_r_lt hb hr_cap htail
  have hpres := gmAppendTail_preserves_nonTail gm hb hr_cap ht_cap
  obtain ⟨hptr_val, _⟩ := gmAppendTail_tail gm hb hr_cap ht_cap
  have hg_del_le_last : g_del ≤ g_last := by
    have hle : gm (gmSlabTopIdx b) ≤ gm 0 - 1 := by omega
    have hmul : gm (gmSlabTopIdx b) * slabSize n_max ≤ (gm 0 - 1) * slabSize n_max :=
      Nat.mul_le_mul_right _ hle
    dsimp only [g_del, g_last]; omega
  have hg_last_le_tail : g_last ≤ g_tail := by
    dsimp only [g_last, g_tail, u_k]; omega
  have harr_del : arr g_del = arr₀ (gm₀ (gmSlabTopIdx b) * slabSize n_max + u_k) := by
    dsimp only [g_del]; rw [htop_b]; exact harr.rem_del u_k hu_k_lt
  have harr_last : arr g_last = arr₀ ((gm₀ 0 - 1) * slabSize n_max + u_k) := by
    dsimp only [g_last]; rw [h0]; exact harr.rem_last u_k hu_k_lt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp hp_ne u hu
    have hp_mul : (p + 1) * slabSize n_max ≤ (gm 0 - 1) * slabSize n_max :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_one_mul] at hp_mul
    have hlt_last : p * slabSize n_max + u < g_last := by
      dsimp only [g_last]; omega
    have hne_tail : p * slabSize n_max + u ≠ g_tail := by omega
    have hne_del : p * slabSize n_max + u ≠ g_del := by
      intro heq
      apply hp_ne
      have hdiv1 : (p * slabSize n_max + u) / slabSize n_max = p := by
        rw [Nat.mul_comm, Nat.mul_add_div hK_pos, Nat.div_eq_of_lt hu, Nat.add_zero]
      have hdiv2 : g_del / slabSize n_max = gm₀ (gmSlabTopIdx b) := by
        dsimp only [g_del]
        rw [htop_b, Nat.mul_comm, Nat.mul_add_div hK_pos,
          Nat.div_eq_of_lt hu_k_slab, Nat.add_zero]
      rw [← hdiv1, heq, hdiv2]
    dsimp only [arr']
    rw [Function.update_of_ne hne_tail, Function.update_of_ne hne_del]
    exact harr.other_slabs p hp hp_ne u hu
  · intro t ht
    have hgt : g_tail < (n_max - 1) - t := by
      dsimp only [g_tail]; omega
    dsimp only [arr']
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact harr.other_tails t ht
  · intro u hu
    have hu_lt_uk : u < u_k := by dsimp only [u_k]; omega
    have hlt_del : gm₀ (gmSlabTopIdx b) * slabSize n_max + u < g_del := by
      dsimp only [g_del]; rw [htop_b]; omega
    dsimp only [arr']
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact harr.rem_del u (by omega)
  · intro u hu
    have hu_lt_uk : u < u_k := by dsimp only [u_k]; omega
    have hlt_last : (gm₀ 0 - 1) * slabSize n_max + u < g_last := by
      dsimp only [g_last]; rw [h0]; omega
    have hne_del : (gm₀ 0 - 1) * slabSize n_max + u ≠ g_del := by
      intro heq
      have hmod1 : ((gm₀ 0 - 1) * slabSize n_max + u) % slabSize n_max = u := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      have hmod2 : g_del % slabSize n_max = u_k := by
        dsimp only [g_del]
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hu_k_slab]
      rw [heq, hmod2] at hmod1
      omega
    dsimp only [arr']
    rw [Function.update_of_ne (by omega), Function.update_of_ne hne_del]
    exact harr.rem_last u (by omega)
  · intro hp_lt_last u hu_ge hu_lt
    have hp_mul : (gm₀ (gmSlabTopIdx b) + 1) * slabSize n_max ≤ (gm 0 - 1) * slabSize n_max :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_one_mul] at hp_mul
    have hlt_last : gm₀ (gmSlabTopIdx b) * slabSize n_max + u < g_last := by
      dsimp only [g_last]; omega
    dsimp only [arr']
    rw [Function.update_of_ne (by omega)]
    by_cases hueq : u = u_k
    · subst hueq
      have heq_del : gm₀ (gmSlabTopIdx b) * slabSize n_max + u_k = g_del := by
        dsimp only [g_del]; rw [htop_b]
      rw [heq_del, Function.update_self, harr_last]
    · have hne_del : gm₀ (gmSlabTopIdx b) * slabSize n_max + u ≠ g_del := by
        dsimp only [g_del]; rw [htop_b]; omega
      rw [Function.update_of_ne hne_del]
      exact harr.moved_last hp_lt_last u (by dsimp only [u_k] at hueq; omega) hu_lt
  · intro r hr
    have hr_cap' : r < tailCapPerBucket n_max := by
      unfold tailCapPerBucket; rw [ite_eq_right hb0]; omega
    have hd_lt : b * tailCapPerBucket n_max + r < maxTailItems n_max := by
      unfold maxTailItems
      have h1 : (b + 1) * tailCapPerBucket n_max ≤ numBuckets n_max * tailCapPerBucket n_max :=
        Nat.mul_le_mul_right _ hb
      nlinarith
    rw [gmTailPtrIdx, hptr_val _ hd_lt]
    by_cases hreq : r = k
    · subst hreq
      have hd_eq : b * tailCapPerBucket n_max + r =
          b * tailCapPerBucket n_max + gm (gmRIdx b) := by rw [hr_b]
      rw [ite_eq_left hd_eq]
      dsimp only [arr', g_tail]
      rw [Function.update_self, harr_del]
    · have hr_lt_k : r < k := by omega
      have hd_ne : b * tailCapPerBucket n_max + r ≠
          b * tailCapPerBucket n_max + gm (gmRIdx b) := by rw [hr_b]; omega
      rw [ite_eq_right hd_ne, ← gmTailPtrIdx]
      have ht_r_lt : gm (gmTailPtrIdx n_max b r) < gm 1 :=
        htail.ptr_lt b hb r (by rw [hr_b]; exact hr_lt_k)
      have hgt : g_tail < (n_max - 1) - gm (gmTailPtrIdx n_max b r) := by
        dsimp only [g_tail]; omega
      dsimp only [arr']
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact harr.demoted_tail r hr_lt_k

/-- Full loop invariant for `k ≤ slabSize n_max` iterations of `demoteStepProg` starting from
`s₀`. -/
structure DemoteLoopInv (U V w₀ n_max h_space base b : ℕ) (s₀ : Memory.State)
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
  gm1_eq : gmAt base U V w₀ n_max h_space s.mem 1 = gmAt base U V w₀ n_max h_space s₀.mem 1 + k
  rb_eq : gmAt base U V w₀ n_max h_space s.mem (gmRIdx b) = k
  qb_pos : 1 ≤ gmAt base U V w₀ n_max h_space s.mem (gmQIdx b)
  top_b_eq : gmAt base U V w₀ n_max h_space s.mem (gmSlabTopIdx b) =
    gmAt base U V w₀ n_max h_space s₀.mem (gmSlabTopIdx b)
  r_other : ∀ b' < numBuckets n_max, b' ≠ b →
    gmAt base U V w₀ n_max h_space s.mem (gmRIdx b') =
      gmAt base U V w₀ n_max h_space s₀.mem (gmRIdx b')
  q_eq : ∀ b' < numBuckets n_max,
    gmAt base U V w₀ n_max h_space s.mem (gmQIdx b') =
      gmAt base U V w₀ n_max h_space s₀.mem (gmQIdx b')
  slabPtr_eq : ∀ b' s_idx,
    slabPtrOf n_max (gmAt base U V w₀ n_max h_space s.mem) b' s_idx =
      slabPtrOf n_max (gmAt base U V w₀ n_max h_space s₀.mem) b' s_idx
  tail_other : ∀ b' < numBuckets n_max, b' ≠ b →
    ∀ r < gmAt base U V w₀ n_max h_space s₀.mem (gmRIdx b'),
      gmAt base U V w₀ n_max h_space s.mem (gmTailPtrIdx n_max b' r) =
        gmAt base U V w₀ n_max h_space s₀.mem (gmTailPtrIdx n_max b' r)
  tot_le : (gmAt base U V w₀ n_max h_space s.mem 0 - 1) * slabSize n_max +
    (slabSize n_max - k) + gmAt base U V w₀ n_max h_space s.mem 1 ≤ n_max
  quot_inv : DemoteArrInv n_max b
    (gmAt base U V w₀ n_max h_space s₀.mem) (quotAt base U w₀ n_max h_space s₀.mem)
    k (gmAt base U V w₀ n_max h_space s.mem) (quotAt base U w₀ n_max h_space s.mem)
  val_inv : DemoteArrInv n_max b
    (gmAt base U V w₀ n_max h_space s₀.mem) (valAt base U V w₀ n_max h_space s₀.mem)
    k (gmAt base U V w₀ n_max h_space s.mem) (valAt base U V w₀ n_max h_space s.mem)

theorem demoteLoopInv_to_stepInv {U V w₀ n_max h_space base b k : ℕ}
    {s₀ s : Memory.State}
    (hloop : DemoteLoopInv U V w₀ n_max h_space base b s₀ k s)
    (hk : k < slabSize n_max) :
    DemoteStepInv U V w₀ n_max h_space base b k s :=
  ⟨hloop.b_lt, hk, hloop.tail_bij, hloop.slab_bij, hloop.rb_eq, hloop.qb_pos, hloop.tot_le⟩

theorem demoteLoopInv_step {U V w₀ n_max h_space base b k : ℕ}
    {s₀ s : Memory.State}
    (hw : 0 < w₀) (hb_pos : 0 < bucketBits n_max)
    (hloop : DemoteLoopInv U V w₀ n_max h_space base b s₀ k s)
    (hk : k < slabSize n_max) :
    let s' := (Memory.spec 0).clientState s
      (demoteStepProg U V w₀ n_max h_space ((base, b), k))
    (Memory.spec 0).clientResult s
      (demoteStepProg U V w₀ n_max h_space ((base, b), k)) = k + 1 ∧
    DemoteLoopInv U V w₀ n_max h_space base b s₀ (k + 1) s' := by
  intro s'
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hstep := demoteLoopInv_to_stepInv hloop hk
  obtain ⟨hres, hf, hout, hq, hv, hl, hgm⟩ :=
    demoteStepProg_effect hw hb_pos s hstep
  let gm := gmAt base U V w₀ n_max h_space s.mem
  let gm₀ := gmAt base U V w₀ n_max h_space s₀.mem
  have hr_cap : gm (gmRIdx b) < tailCapPerBucket n_max := by
    unfold tailCapPerBucket; dsimp only [gm]; rw [ite_eq_right hb0, hloop.rb_eq]; omega
  have ht_cap : gm 1 < maxTailItems n_max :=
    ntails_lt_maxTailItems_of_r_lt hloop.b_lt hr_cap hloop.tail_bij
  have hpres := gmAppendTail_preserves_nonTail gm hloop.b_lt hr_cap ht_cap
  obtain ⟨hptr_val, _⟩ := gmAppendTail_tail gm hloop.b_lt hr_cap ht_cap
  have htail' := tailBijection_gmAppendTail hloop.b_lt hr_cap ht_cap hloop.tail_bij
  have ⟨hptr_slab, hslab'⟩ := slabBijection_gmAppendTail hloop.b_lt hr_cap ht_cap hloop.slab_bij
  have h1_ge : gm₀ 1 ≤ gm 1 := by
    have := hloop.gm1_eq; dsimp only [gm, gm₀]; omega
  have hq_inv' := demoteArrInv_step hb_pos hloop.b_lt hk hloop.tail_bij hloop.slab_bij
    hloop.gm0_eq h1_ge hloop.top_b_eq hloop.rb_eq hloop.qb_pos hloop.tot_le hloop.quot_inv
  have hv_inv' := demoteArrInv_step hb_pos hloop.b_lt hk hloop.tail_bij hloop.slab_bij
    hloop.gm0_eq h1_ge hloop.top_b_eq hloop.rb_eq hloop.qb_pos hloop.tot_le hloop.val_inv
  refine ⟨hres, hloop.b_lt, by omega,
    by rw [hf, hloop.frontier_eq],
    fun a ha => by rw [hout a ha, hloop.mem_out a ha],
    by rw [hl, hloop.lm_eq],
    by rw [hgm]; exact htail',
    by rw [hgm]; exact hslab',
    by rw [hgm, hpres.1]; exact hloop.gm0_eq,
    by rw [hgm, hpres.2.1]; dsimp only [gm, gm₀] at *; rw [hloop.gm1_eq]; omega,
    by rw [hgm, hpres.2.2.1]; dsimp only [gm]; rw [hloop.rb_eq],
    by rw [hgm, hpres.2.2.2.2.1 b hloop.b_lt]; exact hloop.qb_pos,
    by rw [hgm, hpres.2.2.2.2.2.1 b hloop.b_lt]; exact hloop.top_b_eq,
    fun b' hb' hne => by rw [hgm, hpres.2.2.2.1 b' hb' hne]; exact hloop.r_other b' hb' hne,
    fun b' hb' => by rw [hgm, hpres.2.2.2.2.1 b' hb']; exact hloop.q_eq b' hb',
    fun b' s_idx => by rw [hgm, hptr_slab]; exact hloop.slabPtr_eq b' s_idx,
    fun b' hb' hne r hr => ?_,
    by rw [hgm, hpres.1, hpres.2.1]; have := hloop.tot_le; dsimp only [gm] at *; omega,
    by rw [hgm, hq]; exact hq_inv',
    by rw [hgm, hv]; exact hv_inv'⟩
  have hr_cap' : r < tailCapPerBucket n_max := by
    have hr_eq := hloop.r_other b' hb' hne
    have hr_le := hloop.tail_bij.r_le b' hb'
    omega
  have hd_lt : b' * tailCapPerBucket n_max + r < maxTailItems n_max := by
    unfold maxTailItems
    have h1 : (b' + 1) * tailCapPerBucket n_max ≤ numBuckets n_max * tailCapPerBucket n_max :=
      Nat.mul_le_mul_right _ hb'
    nlinarith
  have hd_ne : b' * tailCapPerBucket n_max + r ≠
      b * tailCapPerBucket n_max + gm (gmRIdx b) := by
    intro heq
    obtain ⟨hbeq, _⟩ := flat_descriptor_inj hr_cap' hr_cap heq
    exact hne hbeq
  rw [hgm, gmTailPtrIdx, hptr_val _ hd_lt, ite_eq_right hd_ne, ← gmTailPtrIdx]
  exact hloop.tail_other b' hb' hne r hr

/-- Parameter-free `Memory.Prog` loop executing `n` iterations of `demoteStepGenProg` starting
from index `k`: `d = (((dp, (base, b)), k), n)`. -/
def demoteLoopGenProg (d : ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ) : Memory.Prog ℕ :=
  iterate demoteStepGenProg d.1.1 d.2 d.1.2

/-- `Memory.Prog` loop executing `n` iterations of `demoteStepProg` starting from index `k`:
`d = (((base, b), k), n)`. -/
def demoteLoopProg (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ :=
  iterate (demoteStepProg U V w n_max h_space) d.1.1 d.2 d.1.2

@[simp] theorem iterate_demoteStepGenProg_mk (U V w n_max h_space : ℕ)
    (d : ℕ × ℕ) (m k : ℕ) :
    iterate demoteStepGenProg (mkDictParams U V w n_max h_space, d) m k =
      iterate (demoteStepProg U V w n_max h_space) d m k := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih =>
    unfold iterate
    rw [demoteStepGenProg_mk]
    congr 1
    funext s'
    exact ih s'

@[simp] theorem demoteLoopGenProg_mk (U V w n_max h_space : ℕ)
    (d1 : ℕ × ℕ) (d2 d3 : ℕ) :
    demoteLoopGenProg (((mkDictParams U V w n_max h_space, d1), d2), d3) =
      demoteLoopProg U V w n_max h_space ((d1, d2), d3) :=
  iterate_demoteStepGenProg_mk U V w n_max h_space d1 d3 d2

@[simp] theorem iterationSafe_demoteStepGenProg_mk (U V w₀ n_max h_space w : ℕ)
    (d : ℕ × ℕ) (m k : ℕ) (s : Memory.State) :
    iterationSafe demoteStepGenProg DemoteStepGenPre w
        (mkDictParams U V w₀ n_max h_space, d) m k s ↔
      iterationSafe (demoteStepProg U V w₀ n_max h_space)
        (fun w x s => DemoteStepPre U V w₀ n_max h_space w x.1.1 x.1.2 x.2 s)
        w d m k s := by
  induction m generalizing k s with
  | zero => exact Iff.rfl
  | succ m ih =>
    unfold iterationSafe
    rw [demoteStepGenPre_mk, demoteStepGenProg_mk]
    exact and_congr_right fun _ => ih _ _

theorem iterate_demoteStepProg_spec {U V w₀ n_max h_space base b w : ℕ} {s₀ : Memory.State}
    (hw : 0 < w₀) (hb_pos : 0 < bucketBits n_max)
    (n k : ℕ) (s : Memory.State)
    (hnk : k + n ≤ slabSize n_max)
    (hloop : DemoteLoopInv U V w₀ n_max h_space base b s₀ k s) :
    let prog := iterate (demoteStepProg U V w₀ n_max h_space) (base, b) n k
    DemoteLoopInv U V w₀ n_max h_space base b s₀ (k + n)
      ((Memory.spec 0).clientState s prog) ∧
    memoryCost prog s = 48 * n ∧
    (DictEnvGen w (mkDictParams U V w₀ n_max h_space) base →
      iterationSafe (demoteStepProg U V w₀ n_max h_space)
        (fun w x s => DemoteStepPre U V w₀ n_max h_space w x.1.1 x.1.2 x.2 s)
        w (base, b) n k s) := by
  induction n generalizing k s with
  | zero =>
    simp only [iterate, Nat.add_zero, memoryCost_pure, Nat.mul_zero, iterationSafe]
    exact ⟨hloop, trivial, fun _ => trivial⟩
  | succ n ih =>
    have hk : k < slabSize n_max := by omega
    have hstep := demoteLoopInv_to_stepInv hloop hk
    obtain ⟨hres, hloop'⟩ := demoteLoopInv_step hw hb_pos hloop hk
    let s' := (Memory.spec 0).clientState s
      (demoteStepProg U V w₀ n_max h_space ((base, b), k))
    obtain ⟨hfinal, hcost', hsafe'⟩ := ih (k + 1) s' (by omega) hloop'
    rw [show k + 1 + n = k + (n + 1) by omega] at hfinal
    refine ⟨?_, ?_, ?_⟩
    · simp only [iterate]
      rw [StateTransitionSpec.clientState_bind, hres]
      exact hfinal
    · simp only [iterate]
      rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_demoteStepProg, hres]
      change 48 + memoryCost
        (iterate (demoteStepProg U V w₀ n_max h_space) (base, b) n (k + 1)) s' = 48 * (n + 1)
      rw [hcost']
      omega
    · intro hdict
      simp only [iterationSafe]
      rw [hres]
      exact ⟨⟨hdict, hstep, hb_pos⟩, hsafe' hdict⟩

theorem realizes_demoteLoopGen :
    Realizes .exact demoteLoopGenProg
      (WordEncoding.encode (α := ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d s =>
        iterationSafe demoteStepGenProg DemoteStepGenPre w d.1.1 d.2 d.1.2 s)
      (fun _ _ => 0) :=
  Realizes.iterate₀ (WordEncoding.encode (α := DictParams × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ))
    realizes_demoteStepGen
    one_le_memoryCost_demoteStepGenProg

/-- Parameter-free `Memory.Prog` operation demoting the top full slab of bucket `b = d.2.2` at
`base = d.2.1` into `K = slabSize n_max` tail items. -/
def demoteSlabGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog Unit := do
  let _ ← demoteLoopGenProg ((d, 0), dpSlabSize d.1)
  gmPopSlabGenProg d

/-- `Memory.Prog` operation demoting the top full slab of bucket `b = d.2` at `base = d.1`
(`gm (gmRIdx b) = 0`, `1 ≤ gm (gmQIdx b)`) into `K = slabSize n_max` tail items via
`demoteLoopProg` followed by `gmPopSlabProg`. -/
def demoteSlabProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog Unit := do
  let _ ← demoteLoopProg U V w n_max h_space ((d, 0), slabSize n_max)
  gmPopSlabProg U V w n_max h_space d

@[simp] theorem demoteSlabGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    demoteSlabGenProg (mkDictParams U V w n_max h_space, d) =
      demoteSlabProg U V w n_max h_space d := by
  simp only [demoteSlabGenProg, demoteSlabProg, p_slabSize_mk,
    demoteLoopGenProg_mk, gmPopSlabGenProg_mk]

/-- Pure entry invariant for `demoteSlabProg`. -/
@[expose]
def DemoteSlabInv (U V w₀ n_max h_space base b : ℕ) (s : Memory.State) : Prop :=
  let gm := gmAt base U V w₀ n_max h_space s.mem
  b < numBuckets n_max ∧
  TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1) ∧
  SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0) ∧
  gm (gmRIdx b) = 0 ∧
  1 ≤ gm (gmQIdx b) ∧
  (∀ b' < numBuckets n_max, b' ≠ b →
    gm (gmRIdx b') < tailCapPerBucket n_max ∧
    (0 < gm (gmQIdx b') → 1 ≤ gm (gmRIdx b'))) ∧
  gm 0 * slabSize n_max + gm 1 ≤ n_max

/-- Precondition for `demoteSlabProg` in `Realizes`. -/
@[expose]
def DemoteSlabPre (U V w₀ n_max h_space w base b : ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  DemoteSlabInv U V w₀ n_max h_space base b s ∧
  0 < bucketBits n_max

/-- Parameter-free precondition for `demoteSlabGenProg`. -/
@[expose]
def DemoteSlabGenPre (w : ℕ) (d : DictParams × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w d.1 d.2.1 ∧
  DemoteSlabInv (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) d.2.1 d.2.2 s ∧
  0 < bucketBits (dpNMax d.1)

@[simp] theorem demoteSlabGenPre_mk (U V w₀ n_max h_space w : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    DemoteSlabGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      DemoteSlabPre U V w₀ n_max h_space w d.1 d.2 s := Iff.rfl

theorem demoteLoopInv_zero {U V w₀ n_max h_space base b : ℕ} {s₀ : Memory.State}
    (hpre : DemoteSlabInv U V w₀ n_max h_space base b s₀) :
    DemoteLoopInv U V w₀ n_max h_space base b s₀ 0 s₀ := by
  rcases hpre with ⟨hb, htail, hslab, hrb, hqb_pos, _, htot⟩
  set gm₀ := gmAt base U V w₀ n_max h_space s₀.mem
  have htop_eq := hslab.top_eq b hb (gm₀ (gmQIdx b) - 1) (by omega) (by omega)
  have hp_del_lt : gm₀ (gmSlabTopIdx b) < gm₀ 0 := by
    rw [htop_eq]; exact hslab.ptr_lt b hb (gm₀ (gmQIdx b) - 1) (by omega)
  have hgm0_eq : gm₀ 0 - 1 + 1 = gm₀ 0 := by omega
  have htot' : (gm₀ 0 - 1) * slabSize n_max + (slabSize n_max - 0) + gm₀ 1 ≤ n_max := by
    rw [Nat.sub_zero, ← Nat.add_one_mul, hgm0_eq]
    exact htot
  refine ⟨hb, Nat.zero_le _, rfl, fun _ _ => rfl, rfl, htail, hslab, rfl,
    (Nat.add_zero _).symm, hrb, hqb_pos, rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ _ _ _ => rfl, htot',
    demoteArrInv_zero _ _ _ _, demoteArrInv_zero _ _ _ _⟩

theorem slotOf_gmPopSlab_preserve {α : Type*} {n_max b : ℕ} {gm₀ gm : ℕ → ℕ} {arr₀ arr : ℕ → α}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (htail₀ : TailBijection n_max gm₀ (fun b' => gm₀ (gmRIdx b')) (gm₀ 1))
    (_htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1))
    (hslab₀ : SlabBijection n_max gm₀ (fun b' => gm₀ (gmQIdx b')) (gm₀ 0))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0))
    (h0 : gm 0 = gm₀ 0)
    (hq : ∀ b' < numBuckets n_max, gm (gmQIdx b') = gm₀ (gmQIdx b'))
    (htop_b : gm (gmSlabTopIdx b) = gm₀ (gmSlabTopIdx b))
    (hr_other : ∀ b' < numBuckets n_max, b' ≠ b → gm (gmRIdx b') = gm₀ (gmRIdx b'))
    (hr_b : gm (gmRIdx b) = slabSize n_max)
    (_hr0_b : gm₀ (gmRIdx b) = 0)
    (hqb_pos : 1 ≤ gm₀ (gmQIdx b))
    (hslabPtr : ∀ b' s_idx, slabPtrOf n_max gm b' s_idx = slabPtrOf n_max gm₀ b' s_idx)
    (htail_other : ∀ b' < numBuckets n_max, b' ≠ b → ∀ r < gm₀ (gmRIdx b'),
      gm (gmTailPtrIdx n_max b' r) = gm₀ (gmTailPtrIdx n_max b' r))
    (harr : DemoteArrInv n_max b gm₀ arr₀ (slabSize n_max) gm arr) :
    ∀ b' < numBuckets n_max, ∀ j < bCount n_max (gmPopSlab n_max gm b) b',
      arr (slotOf n_max (gmPopSlab n_max gm b) b' j) = arr₀ (slotOf n_max gm₀ b' j) := by
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  have hqb_pos' : 1 ≤ gm (gmQIdx b) := by rw [hq b hb]; exact hqb_pos
  have hf := gmPopSlab_preserves_tail hb hslab
  have ⟨hptr, _⟩ := slabBijection_gmPopSlab hb hqb_pos' hslab
  have htop_eq0 := hslab₀.top_eq b hb (gm₀ (gmQIdx b) - 1) (by omega) (by omega)
  have hp_del_lt0 : gm₀ (gmSlabTopIdx b) < gm₀ 0 := by
    rw [htop_eq0]; exact hslab₀.ptr_lt b hb (gm₀ (gmQIdx b) - 1) (by omega)
  intro b' hb' j hj
  unfold bCount at hj
  simp only [hb0, ↓reduceIte, hb'] at hj
  unfold slotOf
  rw [ite_eq_right hb0, ite_eq_right hb0]
  by_cases hj_slab : j < gmPopSlab n_max gm b (gmQIdx b') * slabSize n_max <;>
    by_cases hj_slab0 : j < gm₀ (gmQIdx b') * slabSize n_max <;>
    simp only [hj_slab, hj_slab0, ↓reduceIte]
  · have hs_lt : j / slabSize n_max < gmPopSlab n_max gm b (gmQIdx b') :=
      Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hs_lt0 : j / slabSize n_max < gm₀ (gmQIdx b') :=
      Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hu_lt : slabSize n_max - 1 - j % slabSize n_max < slabSize n_max := by
      have := Nat.mod_lt j hK_pos; omega
    have hne_top : ¬(b' = b ∧ j / slabSize n_max = gm₀ (gmQIdx b) - 1) := by
      rintro ⟨hbeq, hseq⟩
      subst hbeq
      rw [hf.2.2.2.1 b' hb', ite_eq_left rfl, hq b' hb'] at hs_lt
      omega
    have hp_ne_del : slabPtrOf n_max gm₀ b' (j / slabSize n_max) ≠ gm₀ (gmSlabTopIdx b) := by
      intro heq
      rw [htop_eq0] at heq
      have hB1 := hslab₀.ownerB_ptr b' hb' (j / slabSize n_max) hs_lt0
      have hB2 := hslab₀.ownerB_ptr b hb (gm₀ (gmQIdx b) - 1) (by omega)
      have hS1 := hslab₀.ownerS_ptr b' hb' (j / slabSize n_max) hs_lt0
      have hS2 := hslab₀.ownerS_ptr b hb (gm₀ (gmQIdx b) - 1) (by omega)
      rw [heq] at hB1 hS1
      exact hne_top ⟨hB1.symm.trans hB2, hS1.symm.trans hS2⟩
    rw [hptr b' hb' (j / slabSize n_max) hs_lt, hslabPtr, h0, htop_b]
    split_ifs with hp_last
    · rw [hp_last]
      have hp_del_lt_last : gm₀ (gmSlabTopIdx b) < gm₀ 0 - 1 := by
        rw [hp_last] at hp_ne_del; omega
      exact harr.moved_last hp_del_lt_last _ (by omega) hu_lt
    · have hp_lt0 : slabPtrOf n_max gm₀ b' (j / slabSize n_max) < gm₀ 0 :=
        hslab₀.ptr_lt b' hb' (j / slabSize n_max) hs_lt0
      exact harr.other_slabs _ (by omega) hp_ne_del _ hu_lt
  · exfalso
    rw [hf.2.2.2.1 b' hb'] at hj_slab
    split_ifs at hj_slab with hbeq
    · subst hbeq
      rw [hq b' hb'] at hj_slab
      have hle_mul : (gm₀ (gmQIdx b') - 1) * slabSize n_max ≤ gm₀ (gmQIdx b') * slabSize n_max :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    · rw [hq b' hb'] at hj_slab
      omega
  · by_cases hbeq : b' = b
    · subst hbeq
      rw [hf.2.2.2.1 b' hb', ite_eq_left rfl, hq b' hb'] at hj_slab hj ⊢
      rw [hf.2.2.1 b' hb', hr_b] at hj
      set r := j - (gm₀ (gmQIdx b') - 1) * slabSize n_max
      have hr_lt : r < slabSize n_max := by
        have hmul : gm₀ (gmQIdx b') * slabSize n_max =
            (gm₀ (gmQIdx b') - 1) * slabSize n_max + slabSize n_max := by
          rw [← Nat.add_one_mul, Nat.sub_add_cancel hqb_pos]
        dsimp only [r]; omega
      have hj_eq : j = (gm₀ (gmQIdx b') - 1) * slabSize n_max + r := by
        dsimp only [r]; omega
      have hr_cap : r < tailCapPerBucket n_max := by
        unfold tailCapPerBucket; rw [ite_eq_right hb0]; omega
      have hd_lt : b' * tailCapPerBucket n_max + r < maxTailItems n_max := by
        unfold maxTailItems
        have h1 : (b' + 1) * tailCapPerBucket n_max ≤ numBuckets n_max * tailCapPerBucket n_max :=
          Nat.mul_le_mul_right _ hb'
        nlinarith
      rw [hf.2.2.2.2 _ (by unfold gmTailPtrIdx gmTailPtrFlatIdx; omega)
        (by unfold gmTailPtrIdx gmTailPtrFlatIdx gmSlabMetaBase gmTailOwnerBase; omega)]
      rw [harr.demoted_tail r hr_lt, htop_eq0]
      have hs_eq : j / slabSize n_max = gm₀ (gmQIdx b') - 1 := by
        rw [hj_eq, Nat.mul_comm, Nat.mul_add_div hK_pos,
          Nat.div_eq_of_lt hr_lt, Nat.add_zero]
      have hmod_eq : j % slabSize n_max = r := by
        rw [hj_eq, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr_lt]
      rw [hs_eq, hmod_eq]
    · exfalso
      rw [hf.2.2.2.1 b' hb', ite_eq_right hbeq, hq b' hb'] at hj_slab
      exact hj_slab hj_slab0
  · by_cases hbeq : b' = b
    · exfalso
      subst hbeq
      rw [hf.2.2.2.1 b' hb', ite_eq_left rfl, hf.2.2.1 b' hb', hq b' hb', hr_b] at hj
      have hmul : gm₀ (gmQIdx b') * slabSize n_max =
          (gm₀ (gmQIdx b') - 1) * slabSize n_max + slabSize n_max := by
        rw [← Nat.add_one_mul, Nat.sub_add_cancel hqb_pos]
      omega
    · rw [hf.2.2.2.1 b' hb', ite_eq_right hbeq, hq b' hb'] at hj_slab hj ⊢
      rw [hf.2.2.1 b' hb', hr_other b' hb' hbeq] at hj
      set r := j - gm₀ (gmQIdx b') * slabSize n_max
      have hr_lt : r < gm₀ (gmRIdx b') := by dsimp only [r]; omega
      have hr_cap : r < tailCapPerBucket n_max := lt_of_lt_of_le hr_lt (htail₀.r_le b' hb')
      have hd_lt : b' * tailCapPerBucket n_max + r < maxTailItems n_max := by
        unfold maxTailItems
        have h1 : (b' + 1) * tailCapPerBucket n_max ≤ numBuckets n_max * tailCapPerBucket n_max :=
          Nat.mul_le_mul_right _ hb'
        nlinarith
      rw [hf.2.2.2.2 _ (by unfold gmTailPtrIdx gmTailPtrFlatIdx; omega)
        (by unfold gmTailPtrIdx gmTailPtrFlatIdx gmSlabMetaBase gmTailOwnerBase; omega),
        htail_other b' hb' hbeq r hr_lt]
      exact harr.other_tails _ (htail₀.ptr_lt b' hb' r hr_lt)

theorem demoteSlabProg_effect {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    (s : Memory.State)
    (hpre : DemoteSlabInv U V w n_max h_space base b s) :
    let gm₀ := gmAt base U V w n_max h_space s.mem
    let s' := (Memory.spec 0).clientState s (demoteSlabProg U V w n_max h_space (base, b))
    let gm' := gmAt base U V w n_max h_space s'.mem
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    SlotStoreInv n_max gm' ∧
    gm' (gmQIdx b) = gm₀ (gmQIdx b) - 1 ∧
    gm' (gmRIdx b) = slabSize n_max ∧
    (∀ b' < numBuckets n_max, b' ≠ b →
      gm' (gmQIdx b') = gm₀ (gmQIdx b') ∧ gm' (gmRIdx b') = gm₀ (gmRIdx b')) ∧
    (∀ b' < numBuckets n_max, bCount n_max gm' b' = bCount n_max gm₀ b') ∧
    (∀ b' < numBuckets n_max, ∀ j < bCount n_max gm' b',
      quotAt base U w n_max h_space s'.mem (slotOf n_max gm' b' j) =
        quotAt base U w n_max h_space s.mem (slotOf n_max gm₀ b' j) ∧
      valAt base U V w n_max h_space s'.mem (slotOf n_max gm' b' j) =
        valAt base U V w n_max h_space s.mem (slotOf n_max gm₀ b' j)) ∧
    memoryCost (demoteSlabProg U V w n_max h_space (base, b)) s ≤
      48 * slabSize n_max + 68 := by
  intro gm₀ s' gm'
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  have hloop0 := demoteLoopInv_zero hpre
  obtain ⟨hloopK, hcost_loop, _⟩ :=
    iterate_demoteStepProg_spec (w := w) hw hb_pos (slabSize n_max) 0 s
      (by omega) hloop0
  rw [Nat.zero_add] at hloopK
  set s₁ := (Memory.spec 0).clientState s
    (demoteLoopProg U V w n_max h_space (((base, b), 0), slabSize n_max))
  change DemoteLoopInv U V w n_max h_space base b s (slabSize n_max) s₁ at hloopK
  obtain ⟨hf_pop, hout_pop, hq_pop, hv_pop, hl_pop, hgm_pop⟩ :=
    gmPopSlabProg_effect (U := U) (V := V) (h_space := h_space)
      hw hb_pos hloopK.b_lt s₁ hloopK.slab_bij hloopK.qb_pos
  have hst : s' =
      (Memory.spec 0).clientState s₁ (gmPopSlabProg U V w n_max h_space (base, b)) := by
    change (Memory.spec 0).clientState s (demoteSlabProg U V w n_max h_space (base, b)) = _
    unfold demoteSlabProg
    rw [StateTransitionSpec.clientState_bind]
  let gm₁ := gmAt base U V w n_max h_space s₁.mem
  have hgm'_eq : gm' = gmPopSlab n_max gm₁ b := by
    dsimp only [gm']; rw [hst, hgm_pop]
  have hf_fields := gmPopSlab_preserves_tail hloopK.b_lt hloopK.slab_bij
  have ⟨_, hslab2⟩ := slabBijection_gmPopSlab hloopK.b_lt hloopK.qb_pos hloopK.slab_bij
  have htail2 := tailBijection_gmPopSlab hloopK.b_lt hloopK.slab_bij hloopK.tail_bij
  have hqb : gm' (gmQIdx b) = gm₀ (gmQIdx b) - 1 := by
    rw [hgm'_eq, hf_fields.2.2.2.1 b hloopK.b_lt, ite_eq_left rfl]
    dsimp only [gm₁, gm₀]
    rw [hloopK.q_eq b hloopK.b_lt]
  have hrb : gm' (gmRIdx b) = slabSize n_max := by
    rw [hgm'_eq, hf_fields.2.2.1 b hloopK.b_lt]
    exact hloopK.rb_eq
  have hother : ∀ b' < numBuckets n_max, b' ≠ b →
      gm' (gmQIdx b') = gm₀ (gmQIdx b') ∧ gm' (gmRIdx b') = gm₀ (gmRIdx b') := by
    intro b' hb' hne
    rw [hgm'_eq, hf_fields.2.2.2.1 b' hb', ite_eq_right hne, hf_fields.2.2.1 b' hb']
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
        exact hpre.2.2.2.2.2.1 b' hb' hbeq
    · rw [hgm'_eq, hf_fields.1, hf_fields.2.1]
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
      have hqb0 : 1 ≤ gm₀ (gmQIdx b) := hpre.2.2.2.2.1
      rw [hpre.2.2.2.1, Nat.add_zero, ← Nat.add_one_mul, Nat.sub_add_cancel hqb0]
    · rw [(hother b' hb' hbeq).1, (hother b' hb' hbeq).2]
  have hq_slot := slotOf_gmPopSlab_preserve hb_pos hloopK.b_lt hpre.2.1 hloopK.tail_bij
    hpre.2.2.1 hloopK.slab_bij hloopK.gm0_eq hloopK.q_eq hloopK.top_b_eq hloopK.r_other
    hloopK.rb_eq hpre.2.2.2.1 hpre.2.2.2.2.1 hloopK.slabPtr_eq hloopK.tail_other hloopK.quot_inv
  have hv_slot := slotOf_gmPopSlab_preserve hb_pos hloopK.b_lt hpre.2.1 hloopK.tail_bij
    hpre.2.2.1 hloopK.slab_bij hloopK.gm0_eq hloopK.q_eq hloopK.top_b_eq hloopK.r_other
    hloopK.rb_eq hpre.2.2.2.1 hpre.2.2.2.2.1 hloopK.slabPtr_eq hloopK.tail_other hloopK.val_inv
  refine ⟨by rw [hst, hf_pop, hloopK.frontier_eq],
    fun a ha => by
      have ha' : ¬(base + offGM U V w n_max h_space ≤ a ∧
          a < base + totalSpace U V w n_max h_space) := by
        dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega
      rw [hst, hout_pop a ha', hloopK.mem_out a ha],
    by rw [hst, hl_pop, hloopK.lm_eq],
    hinv2, hqb, hrb, hother, hbc,
    fun b' hb' j hj => ?_, ?_⟩
  · rw [hst, hq_pop, hv_pop, hgm'_eq]
    rw [hgm'_eq] at hj
    exact ⟨hq_slot b' hb' j hj, hv_slot b' hb' j hj⟩
  · unfold demoteSlabProg
    rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    change memoryCost
        (iterate (demoteStepProg U V w n_max h_space) (base, b) (slabSize n_max) 0) s +
      memoryCost (gmPopSlabProg U V w n_max h_space (base, b)) s₁ ≤ _
    rw [hcost_loop]
    have hpop_cost := memoryCost_gmPopSlabProg_le U V w n_max h_space (base, b) s₁
    omega

theorem realizes_demoteSlabGen :
    Realizes .exact demoteSlabGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      DemoteSlabGenPre
      (fun _ _ => 0) := by
  have hloop := realizes_demoteLoopGen
  have hpop := realizes_gmPopSlabGen
  refine Realizes.congr (p := fun d : DictParams × (ℕ × ℕ) => do
      let k0 ← pure 0
      let _ ← demoteLoopGenProg ((d, k0), dpSlabSize d.1)
      gmPopSlabGenProg d) ?_
    (fun d => by simp only [demoteSlabGenProg, pure_bind])
  realizeDictWith [demoteSlabGenPre_mk, iterationSafe_demoteStepGenProg_mk,
    demoteLoopGenProg_mk, gmPopSlabGenPre_mk, gmPopSlabGenProg_mk]
  · exact (iterate_demoteStepProg_spec hw h.2.2 (slabSize n_max) 0 s
      (by omega) (demoteLoopInv_zero h.2.1)).2.2 h.1
  · rcases d with ⟨base, b⟩
    dsimp only at h
    have hloopK := (iterate_demoteStepProg_spec (w := w) hw h.2.2 (slabSize n_max) 0 s
      (by omega) (demoteLoopInv_zero h.2.1)).1
    rw [Nat.zero_add] at hloopK
    unfold GmPopSlabPre demoteLoopProg
    dsimp only
    exact ⟨h.1, hloopK.slab_bij, h.2.1.1, hloopK.qb_pos, h.2.2⟩

end Cslib.DataStructure.Dictionary.WordRAM.Succinct

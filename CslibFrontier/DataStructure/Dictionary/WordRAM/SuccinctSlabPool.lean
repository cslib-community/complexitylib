/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabBijection
import CslibFrontier.Tactic.Realize

/-!
# `Memory.Prog` Slab-Stack Metadata Operations (`gmPushSlabProg`, `gmPopSlabProg`)

This module defines the `Memory.Prog` operations that push and pop full-slab descriptors in
`GlobalMeta` (`gmPushSlabProg`, `gmUnlinkTopSlabProg`, `gmCompactSlabProg`, `gmPopSlabProg`),
proves their exact pure effects (`gmPushSlab`, `gmUnlinkTopSlab`, `gmCompactSlab`, `gmPopSlab`),
and certifies them via the `realize` tactic.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmPushSlabProg`: `Memory.Prog` operation
  allocating `p_new = gm 0` as the new top slab of bucket `b`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmUnlinkTopSlabProg`: `Memory.Prog` operation
  unlinking the top slab of bucket `b`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmCompactSlabProg`: `Memory.Prog` operation
  compacting `p_last = gm 0 - 1` into `p_del`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmPopSlabProg`: `Memory.Prog` operation popping
  the top slab of bucket `b` and compacting the slab pool.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmPushSlabProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_gmPushSlabGen`: effect and `Realizes`
  certificate for `gmPushSlabProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmUnlinkTopSlabProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmCompactSlabProg_effect`: effects of the two
  stages of `gmPopSlabProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmPopSlabProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_gmPopSlabGen`: effect and `Realizes`
  certificate for `gmPopSlabProg`.
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

/-! ## Section 1: Conditional `writeGMProg` helper -/

theorem writeGMProg_ite_effect {U V w n_max h_space base idx val : ℕ}
    (P : Prop) [Decidable P] (hw : 0 < w)
    (hidx : P → idx < globalMetaLen n_max) (hval : P → val < 2 ^ globalPtrBits n_max)
    (s : Memory.State) :
    let prog : Memory.Prog Unit :=
      if P then writeGMProg U V w n_max h_space ((base, idx), val) else pure ()
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offGM U V w n_max h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem =
      if P then Function.update (gmAt base U V w n_max h_space s.mem) idx val
      else gmAt base U V w n_max h_space s.mem := by
  intro prog s'
  dsimp only [prog, s']
  split_ifs with hP
  · exact writeGMProg_effect (base := base) (U := U) (V := V) (h_space := h_space)
      hw (hidx hP) (hval hP) s
  · exact ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 2: `gmPushSlabProg` and `realizes_gmPushSlabGen` -/

/-- Parameter-free `Memory.Prog` operation allocating a new full slab `p_new = gm 0` as the new top
slab `s_new = gm (gmQIdx b)` of bucket `b = d.2.2` at `base = d.2.1`. -/
def gmPushSlabGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog Unit := do
  let q_b ← readGMGenProg (d.1, (d.2.1, 4 + 3 * d.2.2))
  let p_new ← readGMGenProg (d.1, (d.2.1, 0))
  let top_old ← readGMGenProg (d.1, (d.2.1, 4 + 3 * d.2.2 + 2))
  writeGMGenProg (d.1, ((d.2.1, dpGmSlabMetaBase d.1 + 4 * p_new), d.2.2))
  writeGMGenProg (d.1, ((d.2.1, dpGmSlabMetaBase d.1 + 4 * p_new + 1), q_b))
  writeGMGenProg (d.1, ((d.2.1, dpGmSlabMetaBase d.1 + 4 * p_new + 2), top_old))
  (if 0 < q_b then
    writeGMGenProg (d.1, ((d.2.1, dpGmSlabMetaBase d.1 + 4 * top_old + 3), p_new))
  else pure ()) >>= fun _ => do
  (if q_b < dpDirSlabs d.1 then
    writeGMGenProg (d.1,
      ((d.2.1, dpGmSlabDirBase d.1 + d.2.2 * dpDirSlabs d.1 + q_b), p_new))
  else pure ()) >>= fun _ => do
  writeGMGenProg (d.1, ((d.2.1, 4 + 3 * d.2.2 + 2), p_new))
  writeGMGenProg (d.1, ((d.2.1, 4 + 3 * d.2.2), q_b + 1))
  writeGMGenProg (d.1, ((d.2.1, 0), p_new + 1))

/-- `Memory.Prog` operation allocating a new full slab `p_new = gm 0` as the new top slab
`s_new = gm (gmQIdx b)` of bucket `b = d.2` at `base = d.1`. -/
def gmPushSlabProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog Unit := do
  let q_b ← readGMProg U V w n_max h_space (d.1, 4 + 3 * d.2)
  let p_new ← readGMProg U V w n_max h_space (d.1, 0)
  let top_old ← readGMProg U V w n_max h_space (d.1, 4 + 3 * d.2 + 2)
  writeGMProg U V w n_max h_space ((d.1, gmSlabMetaBase n_max + 4 * p_new), d.2)
  writeGMProg U V w n_max h_space ((d.1, gmSlabMetaBase n_max + 4 * p_new + 1), q_b)
  writeGMProg U V w n_max h_space ((d.1, gmSlabMetaBase n_max + 4 * p_new + 2), top_old)
  (if 0 < q_b then
    writeGMProg U V w n_max h_space ((d.1, gmSlabMetaBase n_max + 4 * top_old + 3), p_new)
  else pure ()) >>= fun _ => do
  (if q_b < dirSlabsPerBucket n_max then
    writeGMProg U V w n_max h_space
      ((d.1, gmSlabDirBase n_max + d.2 * dirSlabsPerBucket n_max + q_b), p_new)
  else pure ()) >>= fun _ => do
  writeGMProg U V w n_max h_space ((d.1, 4 + 3 * d.2 + 2), p_new)
  writeGMProg U V w n_max h_space ((d.1, 4 + 3 * d.2), q_b + 1)
  writeGMProg U V w n_max h_space ((d.1, 0), p_new + 1)

@[simp] theorem gmPushSlabGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    gmPushSlabGenProg (mkDictParams U V w n_max h_space, d) =
      gmPushSlabProg U V w n_max h_space d := by rfl

theorem memoryCost_gmPushSlabProg_le (U V w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (gmPushSlabProg U V w n_max h_space d) s ≤ 38 := by
  unfold gmPushSlabProg
  simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
    memoryCost_readGMProg, memoryCost_writeGMProg]
  split_ifs <;> simp only [memoryCost_writeGMProg, memoryCost_pure] <;> omega

/-- Precondition for `gmPushSlabProg`. -/
@[expose]
def GmPushSlabPre (U V w₀ n_max h_space w base b : ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  SlabBijection n_max (gmAt base U V w₀ n_max h_space s.mem)
    (fun b' => gmAt base U V w₀ n_max h_space s.mem (gmQIdx b'))
    (gmAt base U V w₀ n_max h_space s.mem 0) ∧
  b < numBuckets n_max ∧
  gmAt base U V w₀ n_max h_space s.mem 0 < maxFullSlabs n_max ∧
  0 < bucketBits n_max

/-- Parameter-free precondition for `gmPushSlabGenProg`. -/
@[expose]
def GmPushSlabGenPre (w : ℕ) (d : DictParams × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w d.1 d.2.1 ∧
  SlabBijection (dpNMax d.1)
    (gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem)
    (fun b' => gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1)
      s.mem (gmQIdx b'))
    (gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem 0) ∧
  d.2.2 < numBuckets (dpNMax d.1) ∧
  gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem 0 <
    maxFullSlabs (dpNMax d.1) ∧
  0 < bucketBits (dpNMax d.1)

@[simp] theorem gmPushSlabGenPre_mk (U V w₀ n_max h_space w : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    GmPushSlabGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      GmPushSlabPre U V w₀ n_max h_space w d.1 d.2 s := Iff.rfl

/-- Under `SlabBijection` and `gm 0 < maxFullSlabs n_max` (`b < numBuckets n_max`),
`gmPushSlabProg` runs in `memoryCost ≤ 38` (`memoryCost_gmPushSlabProg_le`) and preserves
`frontier`, `quotAt`, `valAt`, `lmAt`, and memory outside
`[base + offGM U V w n_max h_space, base + totalSpace U V w n_max h_space)`. It updates `gmAt` to
`gmPushSlab n_max gm b`, allocating `p_new = gm 0` as the new top slab of bucket `b`. -/
theorem gmPushSlabProg_effect {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (s : Memory.State)
    (hslab : SlabBijection n_max (gmAt base U V w n_max h_space s.mem)
      (fun b' => gmAt base U V w n_max h_space s.mem (gmQIdx b'))
      (gmAt base U V w n_max h_space s.mem 0))
    (hp_lt : gmAt base U V w n_max h_space s.mem 0 < maxFullSlabs n_max) :
    let s' := (Memory.spec 0).clientState s (gmPushSlabProg U V w n_max h_space (base, b))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offGM U V w n_max h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem =
      gmPushSlab n_max (gmAt base U V w n_max h_space s.mem) b := by
  intro s'
  set gm := gmAt base U V w n_max h_space s.mem
  set q_b := gm (gmQIdx b)
  set p_new := gm 0
  set top_old := gm (gmSlabTopIdx b)
  have hq_idx_lt : 4 + 3 * b < globalMetaLen n_max := gmQIdx_lt hb_pos hb
  have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
  have htop_idx_lt : 4 + 3 * b + 2 < globalMetaLen n_max := gmSlabTopIdx_lt hb_pos hb
  have hownB_lt : gmSlabMetaBase n_max + 4 * p_new < globalMetaLen n_max :=
    gmSlabOwnerBIdx_lt hb_pos hp_lt
  have hownS_lt : gmSlabMetaBase n_max + 4 * p_new + 1 < globalMetaLen n_max :=
    gmSlabOwnerSIdx_lt hb_pos hp_lt
  have hbel_lt : gmSlabMetaBase n_max + 4 * p_new + 2 < globalMetaLen n_max :=
    gmSlabBelowIdx_lt hb_pos hp_lt
  have habv_lt : 0 < q_b → gmSlabMetaBase n_max + 4 * top_old + 3 < globalMetaLen n_max := by
    intro hq_pos
    exact gmSlabAboveIdx_lt hb_pos ((hslab.top_lt hb hq_pos).trans hp_lt)
  have hdir_lt : q_b < dirSlabsPerBucket n_max →
      gmSlabDirBase n_max + b * dirSlabsPerBucket n_max + q_b < globalMetaLen n_max :=
    fun hdir => gmSlabDirIdx_lt hb_pos hb hdir
  have hmax_le : maxFullSlabs n_max ≤ n_max := maxFullSlabs_le n_max
  have hq_le_p : q_b ≤ p_new := q_le_nslabs_of_slabBijection hslab hb
  have hb_val_lt : b < 2 ^ globalPtrBits n_max :=
    lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos (by omega)
  have hq_val_lt : q_b < 2 ^ globalPtrBits n_max := gmAt_lt ..
  have hp_val_lt : p_new < 2 ^ globalPtrBits n_max := gmAt_lt ..
  have htop_val_lt : top_old < 2 ^ globalPtrBits n_max := gmAt_lt ..
  have hq1_val_lt : q_b + 1 < 2 ^ globalPtrBits n_max :=
    lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hp1_val_lt : p_new + 1 < 2 ^ globalPtrBits n_max :=
    lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hres_q : (Memory.spec 0).clientResult s
      (readGMProg U V w n_max h_space (base, 4 + 3 * b)) = q_b :=
    clientResult_readGMProg s hq_idx_lt
  have hres_p : (Memory.spec 0).clientResult s
      (readGMProg U V w n_max h_space (base, 0)) = p_new :=
    clientResult_readGMProg s h0_lt
  have hres_top : (Memory.spec 0).clientResult s
      (readGMProg U V w n_max h_space (base, 4 + 3 * b + 2)) = top_old :=
    clientResult_readGMProg s htop_idx_lt
  obtain ⟨hf1, hout1, hq1, hv1, hl1, hg1⟩ :=
    writeGMProg_effect (base := base) (U := U) (V := V) (h_space := h_space) hw hownB_lt hb_val_lt s
  set s₁ := (Memory.spec 0).clientState s
    (writeGMProg U V w n_max h_space ((base, gmSlabMetaBase n_max + 4 * p_new), b))
  obtain ⟨hf2, hout2, hq2, hv2, hl2, hg2⟩ :=
    writeGMProg_effect (base := base) (U := U) (V := V) (h_space := h_space)
      hw hownS_lt hq_val_lt s₁
  set s₂ := (Memory.spec 0).clientState s₁
    (writeGMProg U V w n_max h_space ((base, gmSlabMetaBase n_max + 4 * p_new + 1), q_b))
  obtain ⟨hf3, hout3, hq3, hv3, hl3, hg3⟩ :=
    writeGMProg_effect (base := base) (U := U) (V := V) (h_space := h_space)
      hw hbel_lt htop_val_lt s₂
  set s₃ := (Memory.spec 0).clientState s₂
    (writeGMProg U V w n_max h_space ((base, gmSlabMetaBase n_max + 4 * p_new + 2), top_old))
  obtain ⟨hf4, hout4, hq4, hv4, hl4, hg4⟩ :=
    writeGMProg_ite_effect (base := base) (U := U) (V := V) (h_space := h_space)
      (0 < q_b) hw habv_lt (fun _ => hp_val_lt) s₃
  set s₄ := (Memory.spec 0).clientState s₃
    (if 0 < q_b then
      writeGMProg U V w n_max h_space ((base, gmSlabMetaBase n_max + 4 * top_old + 3), p_new)
    else pure ())
  obtain ⟨hf5, hout5, hq5, hv5, hl5, hg5⟩ :=
    writeGMProg_ite_effect (base := base) (U := U) (V := V) (h_space := h_space)
      (q_b < dirSlabsPerBucket n_max) hw hdir_lt (fun _ => hp_val_lt) s₄
  set s₅ := (Memory.spec 0).clientState s₄
    (if q_b < dirSlabsPerBucket n_max then
      writeGMProg U V w n_max h_space
        ((base, gmSlabDirBase n_max + b * dirSlabsPerBucket n_max + q_b), p_new)
    else pure ())
  obtain ⟨hf6, hout6, hq6, hv6, hl6, hg6⟩ :=
    writeGMProg_effect (base := base) (U := U) (V := V) (h_space := h_space)
      hw htop_idx_lt hp_val_lt s₅
  set s₆ := (Memory.spec 0).clientState s₅
    (writeGMProg U V w n_max h_space ((base, 4 + 3 * b + 2), p_new))
  obtain ⟨hf7, hout7, hq7, hv7, hl7, hg7⟩ :=
    writeGMProg_effect (base := base) (U := U) (V := V) (h_space := h_space)
      hw hq_idx_lt hq1_val_lt s₆
  set s₇ := (Memory.spec 0).clientState s₆
    (writeGMProg U V w n_max h_space ((base, 4 + 3 * b), q_b + 1))
  obtain ⟨hf8, hout8, hq8, hv8, hl8, hg8⟩ :=
    writeGMProg_effect (base := base) (U := U) (V := V) (h_space := h_space) hw h0_lt hp1_val_lt s₇
  set s₈ := (Memory.spec 0).clientState s₇
    (writeGMProg U V w n_max h_space ((base, 0), p_new + 1))
  have hst : s' = s₈ := by
    change (Memory.spec 0).clientState s (gmPushSlabProg U V w n_max h_space (base, b)) = s₈
    unfold gmPushSlabProg
    dsimp only
    rw [StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_q,
      StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_p,
      StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_top]
    repeat rw [StateTransitionSpec.clientState_bind]
  rw [hst]
  refine ⟨by rw [hf8, hf7, hf6, hf5, hf4, hf3, hf2, hf1],
    fun a ha => by rw [hout8 a ha, hout7 a ha, hout6 a ha, hout5 a ha,
      hout4 a ha, hout3 a ha, hout2 a ha, hout1 a ha],
    by rw [hq8, hq7, hq6, hq5, hq4, hq3, hq2, hq1],
    by rw [hv8, hv7, hv6, hv5, hv4, hv3, hv2, hv1],
    by rw [hl8, hl7, hl6, hl5, hl4, hl3, hl2, hl1], ?_⟩
  rw [hg8, hg7, hg6, hg5, hg4, hg3, hg2, hg1]
  rfl

private theorem gmPushSlab_bounds {U V w₀ n_max h_space w : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (h : GmPushSlabPre U V w₀ n_max h_space w d.1 d.2 s) :
    let e_qb := (Memory.spec 0).clientResult s (readGMProg U V w₀ n_max h_space (d.1, 4 + 3 * d.2))
    let s1 := (Memory.spec 0).clientState s (readGMProg U V w₀ n_max h_space (d.1, 4 + 3 * d.2))
    let e_pnew := (Memory.spec 0).clientResult s1 (readGMProg U V w₀ n_max h_space (d.1, 0))
    let s2 := (Memory.spec 0).clientState s1 (readGMProg U V w₀ n_max h_space (d.1, 0))
    let e_top := (Memory.spec 0).clientResult s2
      (readGMProg U V w₀ n_max h_space (d.1, 4 + 3 * d.2 + 2))
    4 + 3 * d.2 < globalMetaLen n_max ∧
    0 < globalMetaLen n_max ∧
    4 + 3 * d.2 + 2 < globalMetaLen n_max ∧
    gmSlabMetaBase n_max + 4 * e_pnew < globalMetaLen n_max ∧
    gmSlabMetaBase n_max + 4 * e_pnew + 1 < globalMetaLen n_max ∧
    gmSlabMetaBase n_max + 4 * e_pnew + 2 < globalMetaLen n_max ∧
    (0 < e_qb → gmSlabMetaBase n_max + 4 * e_top + 3 < globalMetaLen n_max) ∧
    (e_qb < dirSlabsPerBucket n_max →
      gmSlabDirBase n_max + d.2 * dirSlabsPerBucket n_max + e_qb < globalMetaLen n_max) ∧
    e_qb + 1 ≤ n_max ∧
    e_pnew + 1 ≤ n_max := by
  rcases h with ⟨_, hslab, hb, hp_lt, hb_pos⟩
  set gm := gmAt d.1 U V w₀ n_max h_space s.mem
  have hq_idx_lt : 4 + 3 * d.2 < globalMetaLen n_max := gmQIdx_lt hb_pos hb
  have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
  have htop_idx_lt : 4 + 3 * d.2 + 2 < globalMetaLen n_max := gmSlabTopIdx_lt hb_pos hb
  intro e_qb s1 e_pnew s2 e_top
  have heqb : e_qb = gm (gmQIdx d.2) := clientResult_readGMProg s hq_idx_lt
  have hs1 : s1 = s := rfl
  have hepnew : e_pnew = gm 0 := by
    dsimp only [e_pnew]; rw [hs1]; exact clientResult_readGMProg s h0_lt
  have hs2 : s2 = s := rfl
  have hetop : e_top = gm (gmSlabTopIdx d.2) := by
    dsimp only [e_top]; rw [hs2]; exact clientResult_readGMProg s htop_idx_lt
  have hq_le_p : gm (gmQIdx d.2) ≤ gm 0 := q_le_nslabs_of_slabBijection hslab hb
  have hmax_le : maxFullSlabs n_max ≤ n_max := maxFullSlabs_le n_max
  refine ⟨hq_idx_lt, h0_lt, htop_idx_lt,
    by rw [hepnew]; exact gmSlabOwnerBIdx_lt hb_pos hp_lt,
    by rw [hepnew]; exact gmSlabOwnerSIdx_lt hb_pos hp_lt,
    by rw [hepnew]; exact gmSlabBelowIdx_lt hb_pos hp_lt, ?_, ?_,
    by rw [heqb]; omega, by rw [hepnew]; omega⟩
  · intro hq_pos
    rw [heqb] at hq_pos
    rw [hetop]
    exact gmSlabAboveIdx_lt hb_pos ((hslab.top_lt hb hq_pos).trans hp_lt)
  · intro hdir
    rw [heqb] at hdir ⊢
    exact gmSlabDirIdx_lt hb_pos hb hdir

theorem realizes_gmPushSlabGen :
    Realizes .exact gmPushSlabGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      GmPushSlabGenPre
      (fun _ _ => 0) := by
  have hrg := realizes_readGMGen
  have hwg := realizes_writeGMGen
  refine Realizes.congr (p := fun d : DictParams × (ℕ × ℕ) => do
      let q_idx ← pure (4 + 3 * d.2.2)
      let q_b ← readGMGenProg (d.1, (d.2.1, q_idx))
      let i0 ← pure 0
      let p_new ← readGMGenProg (d.1, (d.2.1, i0))
      let top_idx ← pure (4 + 3 * d.2.2 + 2)
      let top_old ← readGMGenProg (d.1, (d.2.1, top_idx))
      let ownB_idx ← pure (dpGmSlabMetaBase d.1 + 4 * p_new)
      writeGMGenProg (d.1, ((d.2.1, ownB_idx), d.2.2))
      let ownS_idx ← pure (dpGmSlabMetaBase d.1 + 4 * p_new + 1)
      writeGMGenProg (d.1, ((d.2.1, ownS_idx), q_b))
      let bel_idx ← pure (dpGmSlabMetaBase d.1 + 4 * p_new + 2)
      writeGMGenProg (d.1, ((d.2.1, bel_idx), top_old))
      (if i0 < q_b then do
        let abv_idx ← pure (dpGmSlabMetaBase d.1 + 4 * top_old + 3)
        writeGMGenProg (d.1, ((d.2.1, abv_idx), p_new))
      else pure ()) >>= fun _ => do
      (if q_b < dpDirSlabs d.1 then do
        let dir_idx ← pure (dpGmSlabDirBase d.1 + d.2.2 * dpDirSlabs d.1 + q_b)
        writeGMGenProg (d.1, ((d.2.1, dir_idx), p_new))
      else pure ()) >>= fun _ => do
      writeGMGenProg (d.1, ((d.2.1, top_idx), p_new))
      let q_next ← pure (q_b + 1)
      writeGMGenProg (d.1, ((d.2.1, q_idx), q_next))
      let p_next ← pure (p_new + 1)
      writeGMGenProg (d.1, ((d.2.1, i0), p_next))) ?_
    (fun d => by simp only [gmPushSlabGenProg, pure_bind])
  realizeDictWith [gmPushSlabGenPre_mk]
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (le_of_lt (gmPushSlab_bounds h).1)
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact h.1
  · exact (gmPushSlab_bounds h).1
  · exact (gmPushSlab_bounds h).2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (le_of_lt (gmPushSlab_bounds h).2.2.1)
  · exact (gmPushSlab_bounds h).2.2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (le_of_lt (gmPushSlab_bounds h).2.2.2.1)
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact (gmPushSlab_bounds h).2.2.2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (le_of_lt (gmPushSlab_bounds h).2.2.2.2.1)
  · exact (gmPushSlab_bounds h).2.2.2.2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (le_of_lt (gmPushSlab_bounds h).2.2.2.2.2.1)
  · exact (gmPushSlab_bounds h).2.2.2.2.2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (le_of_lt ((gmPushSlab_bounds h).2.2.2.2.2.2.1 hc))
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact h.1
  · exact (gmPushSlab_bounds h).2.2.2.2.2.2.1 hc
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (le_of_lt ((gmPushSlab_bounds h).2.2.2.2.2.2.2.1 hc))
  · exact h.1
  · exact ((gmPushSlab_bounds h).2.2.2.2.2.2.2.1 hc)
  · exact fits_of_le_max_n_one h.1 hw hnU hU
      ((gmPushSlab_bounds h).2.2.2.2.2.2.2.2.1.trans (Nat.le_max_left n_max 1))
  · exact fits_of_le_max_n_one h.1 hw hnU hU
      ((gmPushSlab_bounds h).2.2.2.2.2.2.2.2.2.trans (Nat.le_max_left n_max 1))

/-! ## Section 3: `gmUnlinkTopSlabProg`, `gmCompactSlabProg`, `gmPopSlabProg` -/

/-- Parameter-free `Memory.Prog` operation unlinking the top slab of bucket `b = d.2.2` at
`base = d.2.1`. -/
def gmUnlinkTopSlabGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog ℕ := do
  let q_b ← readGMGenProg (d.1, (d.2.1, 4 + 3 * d.2.2))
  let p_del ← readGMGenProg (d.1, (d.2.1, 4 + 3 * d.2.2 + 2))
  let bel_del ← readGMGenProg (d.1, (d.2.1, dpGmSlabMetaBase d.1 + 4 * p_del + 2))
  writeGMGenProg (d.1, ((d.2.1, 4 + 3 * d.2.2 + 2), bel_del))
  let _ ← writeGMGenProg (d.1, ((d.2.1, 4 + 3 * d.2.2), q_b - 1))
  pure p_del

/-- `Memory.Prog` operation unlinking the top slab of bucket `b = d.2` at `base = d.1` and
returning its physical slab index `p_del = gm (gmSlabTopIdx b)`. -/
def gmUnlinkTopSlabProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let q_b ← readGMProg U V w n_max h_space (d.1, 4 + 3 * d.2)
  let p_del ← readGMProg U V w n_max h_space (d.1, 4 + 3 * d.2 + 2)
  let bel_del ← readGMProg U V w n_max h_space (d.1, gmSlabMetaBase n_max + 4 * p_del + 2)
  writeGMProg U V w n_max h_space ((d.1, 4 + 3 * d.2 + 2), bel_del)
  let _ ← writeGMProg U V w n_max h_space ((d.1, 4 + 3 * d.2), q_b - 1)
  pure p_del

@[simp] theorem gmUnlinkTopSlabGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    gmUnlinkTopSlabGenProg (mkDictParams U V w n_max h_space, d) =
      gmUnlinkTopSlabProg U V w n_max h_space d := by rfl

@[simp]
theorem memoryCost_gmUnlinkTopSlabProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (gmUnlinkTopSlabProg U V w n_max h_space d) s = 14 := by
  simp [gmUnlinkTopSlabProg, -bind_pure_comp, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]

/-- Precondition for `gmUnlinkTopSlabProg` and `gmPopSlabProg`. -/
@[expose]
def GmPopSlabPre (U V w₀ n_max h_space w base b : ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  SlabBijection n_max (gmAt base U V w₀ n_max h_space s.mem)
    (fun b' => gmAt base U V w₀ n_max h_space s.mem (gmQIdx b'))
    (gmAt base U V w₀ n_max h_space s.mem 0) ∧
  b < numBuckets n_max ∧
  1 ≤ gmAt base U V w₀ n_max h_space s.mem (gmQIdx b) ∧
  0 < bucketBits n_max

/-- Parameter-free precondition for `gmUnlinkTopSlabGenProg` and `gmPopSlabGenProg`. -/
@[expose]
def GmPopSlabGenPre (w : ℕ) (d : DictParams × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w d.1 d.2.1 ∧
  SlabBijection (dpNMax d.1)
    (gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem)
    (fun b' => gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1)
      s.mem (gmQIdx b'))
    (gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem 0) ∧
  d.2.2 < numBuckets (dpNMax d.1) ∧
  1 ≤ gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem (gmQIdx d.2.2) ∧
  0 < bucketBits (dpNMax d.1)

@[simp] theorem gmPopSlabGenPre_mk (U V w₀ n_max h_space w : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    GmPopSlabGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      GmPopSlabPre U V w₀ n_max h_space w d.1 d.2 s := Iff.rfl

theorem gmUnlinkTopSlabProg_effect {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (s : Memory.State)
    (hslab : SlabBijection n_max (gmAt base U V w n_max h_space s.mem)
      (fun b' => gmAt base U V w n_max h_space s.mem (gmQIdx b'))
      (gmAt base U V w n_max h_space s.mem 0))
    (hq_pos : 1 ≤ gmAt base U V w n_max h_space s.mem (gmQIdx b)) :
    let s' := (Memory.spec 0).clientState s (gmUnlinkTopSlabProg U V w n_max h_space (base, b))
    (Memory.spec 0).clientResult s (gmUnlinkTopSlabProg U V w n_max h_space (base, b)) =
      gmAt base U V w n_max h_space s.mem (gmSlabTopIdx b) ∧
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offGM U V w n_max h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem =
      gmUnlinkTopSlab n_max (gmAt base U V w n_max h_space s.mem) b := by
  intro s'
  set gm := gmAt base U V w n_max h_space s.mem
  set q_b := gm (gmQIdx b)
  set p_del := gm (gmSlabTopIdx b)
  set bel_del := gm (gmSlabBelowIdx n_max p_del)
  have hq_idx_lt : 4 + 3 * b < globalMetaLen n_max := gmQIdx_lt hb_pos hb
  have htop_idx_lt : 4 + 3 * b + 2 < globalMetaLen n_max := gmSlabTopIdx_lt hb_pos hb
  have hp_del_lt : p_del < gm 0 := hslab.top_lt hb hq_pos
  have hp_del_cap : p_del < maxFullSlabs n_max := lt_of_lt_of_le hp_del_lt hslab.nslabs_le
  have hbel_idx_lt : gmSlabMetaBase n_max + 4 * p_del + 2 < globalMetaLen n_max :=
    gmSlabBelowIdx_lt hb_pos hp_del_cap
  have hbel_val_lt : bel_del < 2 ^ globalPtrBits n_max := gmAt_lt ..
  have hq1_val_lt : q_b - 1 < 2 ^ globalPtrBits n_max :=
    lt_of_le_of_lt (Nat.sub_le _ _) (gmAt_lt ..)
  unfold gmUnlinkTopSlabProg
  dsimp only at s' ⊢
  rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
    clientResult_readGMProg s (by exact hq_idx_lt),
    StateTransitionSpec.clientResult_bind, clientState_readGMProg,
    clientResult_readGMProg s (by exact htop_idx_lt),
    StateTransitionSpec.clientResult_bind, clientState_readGMProg,
    clientResult_readGMProg s (by exact hbel_idx_lt)]
  simp only [StateTransitionSpec.clientResult_bind]
  let s₁ := (Memory.spec 0).clientState s
    (writeGMProg U V w n_max h_space ((base, 4 + 3 * b + 2), bel_del))
  obtain ⟨hf1, hout1, hq1, hv1, hl1, hg1⟩ :=
    writeGMProg_effect (base := base) (U := U) (V := V) (h_space := h_space)
      hw htop_idx_lt hbel_val_lt s
  let s₂ := (Memory.spec 0).clientState s₁
    (writeGMProg U V w n_max h_space ((base, 4 + 3 * b), q_b - 1))
  obtain ⟨hf2, hout2, hq2, hv2, hl2, hg2⟩ :=
    writeGMProg_effect (base := base) (U := U) (V := V) (h_space := h_space)
      hw hq_idx_lt hq1_val_lt s₁
  have hst : s' = s₂ := by
    change (Memory.spec 0).clientState s (gmUnlinkTopSlabProg U V w n_max h_space (base, b)) = s₂
    unfold gmUnlinkTopSlabProg
    dsimp only
    rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
      clientResult_readGMProg s (by exact hq_idx_lt),
      StateTransitionSpec.clientState_bind, clientState_readGMProg,
      clientResult_readGMProg s (by exact htop_idx_lt),
      StateTransitionSpec.clientState_bind, clientState_readGMProg,
      clientResult_readGMProg s (by exact hbel_idx_lt)]
    repeat rw [StateTransitionSpec.clientState_bind]
    rfl
  rw [hst]
  refine ⟨rfl, by rw [hf2, hf1], fun a ha => by rw [hout2 a ha, hout1 a ha],
    by rw [hq2, hq1], by rw [hv2, hv1], by rw [hl2, hl1], ?_⟩
  rw [hg2, hg1]
  rfl

private theorem gmUnlinkTopSlab_bounds {U V w₀ n_max h_space w : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (h : GmPopSlabPre U V w₀ n_max h_space w d.1 d.2 s) :
    let e_qb := (Memory.spec 0).clientResult s (readGMProg U V w₀ n_max h_space (d.1, 4 + 3 * d.2))
    let s1 := (Memory.spec 0).clientState s (readGMProg U V w₀ n_max h_space (d.1, 4 + 3 * d.2))
    let e_pdel := (Memory.spec 0).clientResult s1
      (readGMProg U V w₀ n_max h_space (d.1, 4 + 3 * d.2 + 2))
    4 + 3 * d.2 < globalMetaLen n_max ∧
    4 + 3 * d.2 + 2 < globalMetaLen n_max ∧
    gmSlabMetaBase n_max + 4 * e_pdel + 2 < globalMetaLen n_max ∧
    1 ≤ e_qb := by
  rcases h with ⟨_, hslab, hb, hq_pos, hb_pos⟩
  set gm := gmAt d.1 U V w₀ n_max h_space s.mem
  have hq_idx_lt : 4 + 3 * d.2 < globalMetaLen n_max := gmQIdx_lt hb_pos hb
  have htop_idx_lt : 4 + 3 * d.2 + 2 < globalMetaLen n_max := gmSlabTopIdx_lt hb_pos hb
  intro e_qb s1 e_pdel
  have heqb : e_qb = gm (gmQIdx d.2) := clientResult_readGMProg s hq_idx_lt
  have hs1 : s1 = s := rfl
  have hepdel : e_pdel = gm (gmSlabTopIdx d.2) := by
    dsimp only [e_pdel]; rw [hs1]; exact clientResult_readGMProg s htop_idx_lt
  have hp_del_cap : gm (gmSlabTopIdx d.2) < maxFullSlabs n_max :=
    lt_of_lt_of_le (hslab.top_lt hb hq_pos) hslab.nslabs_le
  refine ⟨hq_idx_lt, htop_idx_lt,
    by rw [hepdel]; exact gmSlabBelowIdx_lt hb_pos hp_del_cap,
    by rw [heqb]; exact hq_pos⟩

theorem realizes_gmUnlinkTopSlabGen :
    Realizes .exact gmUnlinkTopSlabGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      GmPopSlabGenPre
      (fun _ _ => 0) := by
  have hrg := realizes_readGMGen
  have hwg := realizes_writeGMGen
  refine Realizes.congr (p := fun d : DictParams × (ℕ × ℕ) => do
      let q_idx ← pure (4 + 3 * d.2.2)
      let q_b ← readGMGenProg (d.1, (d.2.1, q_idx))
      let top_idx ← pure (4 + 3 * d.2.2 + 2)
      let p_del ← readGMGenProg (d.1, (d.2.1, top_idx))
      let bel_idx ← pure (dpGmSlabMetaBase d.1 + 4 * p_del + 2)
      let bel_del ← readGMGenProg (d.1, (d.2.1, bel_idx))
      writeGMGenProg (d.1, ((d.2.1, top_idx), bel_del))
      let q_prev ← pure (q_b - 1)
      let _ ← writeGMGenProg (d.1, ((d.2.1, q_idx), q_prev))
      pure p_del) ?_
    (fun d => by simp only [gmUnlinkTopSlabGenProg, pure_bind])
  realizeDictWith [gmPopSlabGenPre_mk]
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (le_of_lt (gmUnlinkTopSlab_bounds h).1)
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact h.1
  · exact (gmUnlinkTopSlab_bounds h).1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (le_of_lt (gmUnlinkTopSlab_bounds h).2.1)
  · exact (gmUnlinkTopSlab_bounds h).2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (le_of_lt (gmUnlinkTopSlab_bounds h).2.2.1)
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact (gmUnlinkTopSlab_bounds h).2.2.1
  · exact (gmUnlinkTopSlab_bounds h).2.2.2

/-- Pure first half of `gmCompactSlab` when `p_del < p_last`: updates the directory and top pointer
of `b_last`. -/
@[expose]
def gmRelinkMovedSlab (n_max : ℕ) (gmA : ℕ → ℕ) (p_del p_last : ℕ) : ℕ → ℕ :=
  let b_last := gmA (gmSlabOwnerBIdx n_max p_last)
  let s_last := gmA (gmSlabOwnerSIdx n_max p_last)
  let q_last := gmA (gmQIdx b_last)
  let gm₁ := if s_last < dirSlabsPerBucket n_max then
    Function.update gmA (gmSlabDirIdx n_max b_last s_last) p_del else gmA
  if s_last + 1 = q_last then
    Function.update gm₁ (gmSlabTopIdx b_last) p_del else gm₁

/-- Pure second half of `gmCompactSlab` when `p_del < p_last`: updates the neighbor links of
`bel_last` and `abv_last` and copies the 4 metadata fields of `p_last` into `p_del`. -/
@[expose]
def gmLinkMovedNeighbors (n_max : ℕ) (gm₂ : ℕ → ℕ) (p_del p_last : ℕ) : ℕ → ℕ :=
  let b_last := gm₂ (gmSlabOwnerBIdx n_max p_last)
  let s_last := gm₂ (gmSlabOwnerSIdx n_max p_last)
  let bel_last := gm₂ (gmSlabBelowIdx n_max p_last)
  let abv_last := gm₂ (gmSlabAboveIdx n_max p_last)
  let q_last := gm₂ (gmQIdx b_last)
  let gm₃ := if 0 < s_last then
    Function.update gm₂ (gmSlabAboveIdx n_max bel_last) p_del else gm₂
  let gm₄ := if s_last + 1 < q_last then
    Function.update gm₃ (gmSlabBelowIdx n_max abv_last) p_del else gm₃
  Function.update
    (Function.update
      (Function.update
        (Function.update gm₄ (gmSlabOwnerBIdx n_max p_del) b_last)
        (gmSlabOwnerSIdx n_max p_del) s_last)
      (gmSlabBelowIdx n_max p_del) bel_last)
    (gmSlabAboveIdx n_max p_del) abv_last

theorem gmRelinkMovedSlab_preserves_meta {n_max : ℕ} (gmA : ℕ → ℕ) {p_del p_last : ℕ}
    (hb_last : gmA (gmSlabOwnerBIdx n_max p_last) < numBuckets n_max) :
    let gm₂ := gmRelinkMovedSlab n_max gmA p_del p_last
    gm₂ 0 = gmA 0 ∧
    gm₂ (gmQIdx (gmA (gmSlabOwnerBIdx n_max p_last))) =
      gmA (gmQIdx (gmA (gmSlabOwnerBIdx n_max p_last))) ∧
    (∀ idx, gmSlabMetaBase n_max ≤ idx → gm₂ idx = gmA idx) := by
  dsimp only
  unfold gmRelinkMovedSlab
  generalize gmA (gmSlabOwnerBIdx n_max p_last) = b₀ at hb_last ⊢
  generalize gmA (gmSlabOwnerSIdx n_max p_last) = s₀
  have hdir : s₀ < dirSlabsPerBucket n_max →
      b₀ * dirSlabsPerBucket n_max + s₀ < numBuckets n_max * dirSlabsPerBucket n_max := by
    intro hs
    have h1 : (b₀ + 1) * dirSlabsPerBucket n_max ≤
        numBuckets n_max * dirSlabsPerBucket n_max := Nat.mul_le_mul_right _ hb_last
    nlinarith
  unfold gmQIdx gmSlabTopIdx gmSlabDirIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase
  refine ⟨?_, ?_, ?_⟩
  · split_ifs
    all_goals repeat rw [Function.update_of_ne (by omega)]
    all_goals rfl
  · split_ifs
    all_goals repeat rw [Function.update_of_ne (by omega)]
    all_goals rfl
  · intro idx hidx
    split_ifs with h1 h2 h2
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by have := hdir h2; omega)]
    · rw [Function.update_of_ne (by omega)]
    · rw [Function.update_of_ne (by have := hdir h2; omega)]
    · rfl

theorem gmCompactSlab_eq_parts {n_max : ℕ} (gmA : ℕ → ℕ) {p_del : ℕ}
    (hlt : p_del < gmA 0 - 1)
    (hb_last : gmA (gmSlabOwnerBIdx n_max (gmA 0 - 1)) < numBuckets n_max) :
    Function.update
      (gmLinkMovedNeighbors n_max
        (gmRelinkMovedSlab n_max gmA p_del (gmA 0 - 1)) p_del (gmA 0 - 1))
      0 (gmA 0 - 1) = gmCompactSlab n_max gmA p_del := by
  rcases gmRelinkMovedSlab_preserves_meta gmA (p_del := p_del) hb_last with ⟨_, hpQ, hpGe⟩
  have hB : gmSlabMetaBase n_max ≤ gmSlabOwnerBIdx n_max (gmA 0 - 1) := by
    unfold gmSlabOwnerBIdx; omega
  have hS : gmSlabMetaBase n_max ≤ gmSlabOwnerSIdx n_max (gmA 0 - 1) := by
    unfold gmSlabOwnerSIdx; omega
  have hBel : gmSlabMetaBase n_max ≤ gmSlabBelowIdx n_max (gmA 0 - 1) := by
    unfold gmSlabBelowIdx; omega
  have hAbv : gmSlabMetaBase n_max ≤ gmSlabAboveIdx n_max (gmA 0 - 1) := by
    unfold gmSlabAboveIdx; omega
  unfold gmLinkMovedNeighbors gmCompactSlab
  dsimp only
  rw [ite_eq_left hlt, hpGe _ hB, hpGe _ hS, hpGe _ hBel, hpGe _ hAbv, hpQ]
  rfl

/-- Parameter-free `Memory.Prog` helper performing `gmRelinkMovedSlab` for
`d = (dp, ((base, p_del), p_last))`. -/
def gmRelinkMovedSlabGenProg (d : DictParams × ((ℕ × ℕ) × ℕ)) : Memory.Prog Unit := do
  let base := d.2.1.1
  let p_del := d.2.1.2
  let p_last := d.2.2
  let b_last ← readGMGenProg (d.1, (base, dpGmSlabMetaBase d.1 + 4 * p_last))
  let s_last ← readGMGenProg (d.1, (base, dpGmSlabMetaBase d.1 + 4 * p_last + 1))
  let q_last ← readGMGenProg (d.1, (base, 4 + 3 * b_last))
  (if s_last < dpDirSlabs d.1 then
    writeGMGenProg (d.1,
      ((base, dpGmSlabDirBase d.1 + b_last * dpDirSlabs d.1 + s_last), p_del))
  else pure ()) >>= fun _ => do
    if s_last + 1 = q_last then
      writeGMGenProg (d.1, ((base, 4 + 3 * b_last + 2), p_del))
    else pure ()

/-- `Memory.Prog` helper performing `gmRelinkMovedSlab` for `d = ((base, p_del), p_last)`. -/
def gmRelinkMovedSlabProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit := do
  let base := d.1.1
  let p_del := d.1.2
  let p_last := d.2
  let b_last ← readGMProg U V w n_max h_space (base, gmSlabMetaBase n_max + 4 * p_last)
  let s_last ← readGMProg U V w n_max h_space (base, gmSlabMetaBase n_max + 4 * p_last + 1)
  let q_last ← readGMProg U V w n_max h_space (base, 4 + 3 * b_last)
  (if s_last < dirSlabsPerBucket n_max then
    writeGMProg U V w n_max h_space
      ((base, gmSlabDirBase n_max + b_last * dirSlabsPerBucket n_max + s_last), p_del)
  else pure ()) >>= fun _ => do
    if s_last + 1 = q_last then
      writeGMProg U V w n_max h_space ((base, 4 + 3 * b_last + 2), p_del)
    else pure ()

@[simp] theorem gmRelinkMovedSlabGenProg_mk (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) :
    gmRelinkMovedSlabGenProg (mkDictParams U V w n_max h_space, d) =
      gmRelinkMovedSlabProg U V w n_max h_space d := by rfl

theorem memoryCost_gmRelinkMovedSlabProg_le (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ)
    (s : Memory.State) :
    memoryCost (gmRelinkMovedSlabProg U V w n_max h_space d) s ≤ 14 := by
  unfold gmRelinkMovedSlabProg
  dsimp only
  simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_readGMProg]
  split_ifs <;> simp only [memoryCost_writeGMProg, memoryCost_pure] <;> omega

/-- Pure bounds invariant for `gmRelinkMovedSlabProg` and `gmLinkMovedNeighborsProg`. -/
@[expose]
def GmMovedSlabInv (U V w₀ n_max h_space base p_del p_last : ℕ) (s : Memory.State) : Prop :=
  let gm := gmAt base U V w₀ n_max h_space s.mem
  let b_last := gm (gmSlabOwnerBIdx n_max p_last)
  let s_last := gm (gmSlabOwnerSIdx n_max p_last)
  let bel_last := gm (gmSlabBelowIdx n_max p_last)
  let abv_last := gm (gmSlabAboveIdx n_max p_last)
  let q_last := gm (gmQIdx b_last)
  p_del < maxFullSlabs n_max ∧
  p_last < maxFullSlabs n_max ∧
  b_last < numBuckets n_max ∧
  s_last + 1 ≤ n_max ∧
  (0 < s_last → bel_last < maxFullSlabs n_max) ∧
  (s_last + 1 < q_last → abv_last < maxFullSlabs n_max) ∧
  0 < bucketBits n_max

/-- Precondition for `gmRelinkMovedSlabProg` and `gmLinkMovedNeighborsProg`. -/
@[expose]
def GmMovedSlabPre (U V w₀ n_max h_space w base p_del p_last : ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  GmMovedSlabInv U V w₀ n_max h_space base p_del p_last s

/-- Parameter-free precondition for `gmRelinkMovedSlabGenProg` and `gmLinkMovedNeighborsGenProg`. -/
@[expose]
def GmMovedSlabGenPre (w : ℕ) (d : DictParams × ((ℕ × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w d.1 d.2.1.1 ∧
  GmMovedSlabInv (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1)
    d.2.1.1 d.2.1.2 d.2.2 s

@[simp] theorem gmMovedSlabGenPre_mk (U V w₀ n_max h_space w : ℕ) (d : (ℕ × ℕ) × ℕ)
    (s : Memory.State) :
    GmMovedSlabGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      GmMovedSlabPre U V w₀ n_max h_space w d.1.1 d.1.2 d.2 s := Iff.rfl

theorem gmRelinkMovedSlabProg_effect {U V w n_max h_space base p_del p_last : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    (s : Memory.State)
    (hpre : GmMovedSlabInv U V w n_max h_space base p_del p_last s) :
    let s' := (Memory.spec 0).clientState s
      (gmRelinkMovedSlabProg U V w n_max h_space ((base, p_del), p_last))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offGM U V w n_max h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem =
      gmRelinkMovedSlab n_max (gmAt base U V w n_max h_space s.mem) p_del p_last := by
  intro s'
  rcases hpre with ⟨hp_del_cap, hp_last_cap, hb_last, _, _, _⟩
  set gm := gmAt base U V w n_max h_space s.mem
  set b_last := gm (gmSlabOwnerBIdx n_max p_last)
  set s_last := gm (gmSlabOwnerSIdx n_max p_last)
  set q_last := gm (gmQIdx b_last)
  have hownB_last_lt : gmSlabMetaBase n_max + 4 * p_last < globalMetaLen n_max :=
    gmSlabOwnerBIdx_lt hb_pos hp_last_cap
  have hownS_last_lt : gmSlabMetaBase n_max + 4 * p_last + 1 < globalMetaLen n_max :=
    gmSlabOwnerSIdx_lt hb_pos hp_last_cap
  have hq_last_lt : 4 + 3 * b_last < globalMetaLen n_max := gmQIdx_lt hb_pos hb_last
  have hdir_lt : s_last < dirSlabsPerBucket n_max →
      gmSlabDirBase n_max + b_last * dirSlabsPerBucket n_max + s_last < globalMetaLen n_max :=
    fun hdir => gmSlabDirIdx_lt hb_pos hb_last hdir
  have htop_lt : s_last + 1 = q_last → 4 + 3 * b_last + 2 < globalMetaLen n_max :=
    fun _ => gmSlabTopIdx_lt hb_pos hb_last
  have hmax_le : maxFullSlabs n_max ≤ n_max := maxFullSlabs_le n_max
  have hp_del_val_lt : p_del < 2 ^ globalPtrBits n_max :=
    lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hres_b : (Memory.spec 0).clientResult s
      (readGMProg U V w n_max h_space (base, gmSlabMetaBase n_max + 4 * p_last)) = b_last :=
    clientResult_readGMProg s hownB_last_lt
  have hres_s : (Memory.spec 0).clientResult s
      (readGMProg U V w n_max h_space (base, gmSlabMetaBase n_max + 4 * p_last + 1)) = s_last :=
    clientResult_readGMProg s hownS_last_lt
  have hres_q : (Memory.spec 0).clientResult s
      (readGMProg U V w n_max h_space (base, 4 + 3 * b_last)) = q_last :=
    clientResult_readGMProg s hq_last_lt
  obtain ⟨hf1, hout1, hq1, hv1, hl1, hg1⟩ :=
    writeGMProg_ite_effect (base := base) (U := U) (V := V) (h_space := h_space)
      (s_last < dirSlabsPerBucket n_max) hw hdir_lt (fun _ => hp_del_val_lt) s
  set s₁ := (Memory.spec 0).clientState s
    (if s_last < dirSlabsPerBucket n_max then
      writeGMProg U V w n_max h_space
        ((base, gmSlabDirBase n_max + b_last * dirSlabsPerBucket n_max + s_last), p_del)
    else pure ())
  obtain ⟨hf2, hout2, hq2, hv2, hl2, hg2⟩ :=
    writeGMProg_ite_effect (base := base) (U := U) (V := V) (h_space := h_space)
      (s_last + 1 = q_last) hw htop_lt (fun _ => hp_del_val_lt) s₁
  set s₂ := (Memory.spec 0).clientState s₁
    (if s_last + 1 = q_last then
      writeGMProg U V w n_max h_space ((base, 4 + 3 * b_last + 2), p_del)
    else pure ())
  have hst : s' = s₂ := by
    change (Memory.spec 0).clientState s
      (gmRelinkMovedSlabProg U V w n_max h_space ((base, p_del), p_last)) = s₂
    unfold gmRelinkMovedSlabProg
    dsimp only
    rw [StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_b,
      StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_s,
      StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_q,
      StateTransitionSpec.clientState_bind]
  rw [hst]
  refine ⟨by rw [hf2, hf1], fun a ha => by rw [hout2 a ha, hout1 a ha],
    by rw [hq2, hq1], by rw [hv2, hv1], by rw [hl2, hl1], ?_⟩
  rw [hg2, hg1]
  rfl

private theorem gmRelinkMovedSlab_bounds {U V w₀ n_max h_space w : ℕ}
    {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (h : GmMovedSlabPre U V w₀ n_max h_space w d.1.1 d.1.2 d.2 s) :
    let e_blast := (Memory.spec 0).clientResult s
      (readGMProg U V w₀ n_max h_space (d.1.1, gmSlabMetaBase n_max + 4 * d.2))
    let s1 := (Memory.spec 0).clientState s
      (readGMProg U V w₀ n_max h_space (d.1.1, gmSlabMetaBase n_max + 4 * d.2))
    let e_slast := (Memory.spec 0).clientResult s1
      (readGMProg U V w₀ n_max h_space (d.1.1, gmSlabMetaBase n_max + 4 * d.2 + 1))
    let s2 := (Memory.spec 0).clientState s1
      (readGMProg U V w₀ n_max h_space (d.1.1, gmSlabMetaBase n_max + 4 * d.2 + 1))
    let e_qlast := (Memory.spec 0).clientResult s2
      (readGMProg U V w₀ n_max h_space (d.1.1, 4 + 3 * e_blast))
    gmSlabMetaBase n_max + 4 * d.2 < globalMetaLen n_max ∧
    gmSlabMetaBase n_max + 4 * d.2 + 1 < globalMetaLen n_max ∧
    4 + 3 * e_blast < globalMetaLen n_max ∧
    (e_slast < dirSlabsPerBucket n_max →
      gmSlabDirBase n_max + e_blast * dirSlabsPerBucket n_max + e_slast < globalMetaLen n_max) ∧
    e_slast + 1 ≤ n_max ∧
    (e_slast + 1 = e_qlast → 4 + 3 * e_blast + 2 < globalMetaLen n_max) := by
  rcases h with ⟨_, _, hp_last_cap, hb_last, hs_le, _, _, hb_pos⟩
  set gm := gmAt d.1.1 U V w₀ n_max h_space s.mem
  have hownB_lt := gmSlabOwnerBIdx_lt hb_pos hp_last_cap
  have hownS_lt := gmSlabOwnerSIdx_lt hb_pos hp_last_cap
  intro e_blast s1 e_slast s2 e_qlast
  have heblast : e_blast = gm (gmSlabOwnerBIdx n_max d.2) :=
    clientResult_readGMProg s (by exact hownB_lt)
  have hs1 : s1 = s := rfl
  have heslast : e_slast = gm (gmSlabOwnerSIdx n_max d.2) := by
    dsimp only [e_slast]; rw [hs1]; exact clientResult_readGMProg s (by exact hownS_lt)
  have hq_lt : 4 + 3 * gm (gmSlabOwnerBIdx n_max d.2) < globalMetaLen n_max :=
    gmQIdx_lt hb_pos hb_last
  refine ⟨hownB_lt, hownS_lt, by rw [heblast]; exact hq_lt, ?_, by rw [heslast]; exact hs_le, ?_⟩
  · intro hdir
    rw [heblast, heslast]; rw [heslast] at hdir
    exact gmSlabDirIdx_lt hb_pos hb_last hdir
  · intro _
    rw [heblast]
    exact gmSlabTopIdx_lt hb_pos hb_last

theorem realizes_gmRelinkMovedSlabGen :
    Realizes .exact gmRelinkMovedSlabGenProg
      (WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ))) (WordEncoding.encode (α := Unit))
      GmMovedSlabGenPre
      (fun _ _ => 0) := by
  have hrg := realizes_readGMGen
  have hwg := realizes_writeGMGen
  refine Realizes.congr (p := fun d : DictParams × ((ℕ × ℕ) × ℕ) => do
      let ownB_idx ← pure (dpGmSlabMetaBase d.1 + 4 * d.2.2)
      let b_last ← readGMGenProg (d.1, (d.2.1.1, ownB_idx))
      let ownS_idx ← pure (dpGmSlabMetaBase d.1 + 4 * d.2.2 + 1)
      let s_last ← readGMGenProg (d.1, (d.2.1.1, ownS_idx))
      let q_idx ← pure (4 + 3 * b_last)
      let q_last ← readGMGenProg (d.1, (d.2.1.1, q_idx))
      (if s_last < dpDirSlabs d.1 then do
        let dir_idx ← pure (dpGmSlabDirBase d.1 + b_last * dpDirSlabs d.1 + s_last)
        writeGMGenProg (d.1, ((d.2.1.1, dir_idx), d.2.1.2))
      else pure ()) >>= fun _ => do
        let s_next ← pure (s_last + 1)
        if s_next = q_last then do
          let top_idx ← pure (4 + 3 * b_last + 2)
          writeGMGenProg (d.1, ((d.2.1.1, top_idx), d.2.1.2))
        else pure ()) ?_
    (fun d => by simp only [gmRelinkMovedSlabGenProg, pure_bind])
  realizeDictWith [gmMovedSlabGenPre_mk]
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2.2.2.2 hw hnU hU
      (le_of_lt (gmRelinkMovedSlab_bounds h).1)
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact h.1
  · exact (gmRelinkMovedSlab_bounds h).1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2.2.2.2 hw hnU hU
      (le_of_lt (gmRelinkMovedSlab_bounds h).2.1)
  · exact (gmRelinkMovedSlab_bounds h).2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2.2.2.2 hw hnU hU
      (le_of_lt (gmRelinkMovedSlab_bounds h).2.2.1)
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact (gmRelinkMovedSlab_bounds h).2.2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2.2.2.2 hw hnU hU
      (le_of_lt ((gmRelinkMovedSlab_bounds h).2.2.2.1 hc))
  · exact h.1
  · exact ((gmRelinkMovedSlab_bounds h).2.2.2.1 hc)
  · exact fits_of_le_max_n_one h.1 hw hnU hU
      ((gmRelinkMovedSlab_bounds h).2.2.2.2.1.trans (Nat.le_max_left n_max 1))
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2.2.2.2 hw hnU hU
      (le_of_lt ((gmRelinkMovedSlab_bounds h).2.2.2.2.2 hc))
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact h.1
  · exact ((gmRelinkMovedSlab_bounds h).2.2.2.2.2 hc)

/-- Parameter-free `Memory.Prog` helper performing `gmLinkMovedNeighbors` for
`d = (dp, ((base, p_del), p_last))`. -/
def gmLinkMovedNeighborsGenProg (d : DictParams × ((ℕ × ℕ) × ℕ)) : Memory.Prog Unit := do
  let base := d.2.1.1
  let p_del := d.2.1.2
  let p_last := d.2.2
  let b_last ← readGMGenProg (d.1, (base, dpGmSlabMetaBase d.1 + 4 * p_last))
  let s_last ← readGMGenProg (d.1, (base, dpGmSlabMetaBase d.1 + 4 * p_last + 1))
  let bel_last ← readGMGenProg (d.1, (base, dpGmSlabMetaBase d.1 + 4 * p_last + 2))
  let abv_last ← readGMGenProg (d.1, (base, dpGmSlabMetaBase d.1 + 4 * p_last + 3))
  let q_last ← readGMGenProg (d.1, (base, 4 + 3 * b_last))
  (if 0 < s_last then
    writeGMGenProg (d.1, ((base, dpGmSlabMetaBase d.1 + 4 * bel_last + 3), p_del))
  else pure ()) >>= fun _ => do
    (if s_last + 1 < q_last then
      writeGMGenProg (d.1, ((base, dpGmSlabMetaBase d.1 + 4 * abv_last + 2), p_del))
    else pure ()) >>= fun _ => do
      writeGMGenProg (d.1, ((base, dpGmSlabMetaBase d.1 + 4 * p_del), b_last))
      writeGMGenProg (d.1, ((base, dpGmSlabMetaBase d.1 + 4 * p_del + 1), s_last))
      writeGMGenProg (d.1, ((base, dpGmSlabMetaBase d.1 + 4 * p_del + 2), bel_last))
      writeGMGenProg (d.1, ((base, dpGmSlabMetaBase d.1 + 4 * p_del + 3), abv_last))

/-- `Memory.Prog` helper performing `gmLinkMovedNeighbors` for `d = ((base, p_del), p_last)`. -/
def gmLinkMovedNeighborsProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit := do
  let base := d.1.1
  let p_del := d.1.2
  let p_last := d.2
  let b_last ← readGMProg U V w n_max h_space (base, gmSlabMetaBase n_max + 4 * p_last)
  let s_last ← readGMProg U V w n_max h_space (base, gmSlabMetaBase n_max + 4 * p_last + 1)
  let bel_last ← readGMProg U V w n_max h_space (base, gmSlabMetaBase n_max + 4 * p_last + 2)
  let abv_last ← readGMProg U V w n_max h_space (base, gmSlabMetaBase n_max + 4 * p_last + 3)
  let q_last ← readGMProg U V w n_max h_space (base, 4 + 3 * b_last)
  (if 0 < s_last then
    writeGMProg U V w n_max h_space ((base, gmSlabMetaBase n_max + 4 * bel_last + 3), p_del)
  else pure ()) >>= fun _ => do
    (if s_last + 1 < q_last then
      writeGMProg U V w n_max h_space ((base, gmSlabMetaBase n_max + 4 * abv_last + 2), p_del)
    else pure ()) >>= fun _ => do
      writeGMProg U V w n_max h_space ((base, gmSlabMetaBase n_max + 4 * p_del), b_last)
      writeGMProg U V w n_max h_space ((base, gmSlabMetaBase n_max + 4 * p_del + 1), s_last)
      writeGMProg U V w n_max h_space ((base, gmSlabMetaBase n_max + 4 * p_del + 2), bel_last)
      writeGMProg U V w n_max h_space ((base, gmSlabMetaBase n_max + 4 * p_del + 3), abv_last)

@[simp] theorem gmLinkMovedNeighborsGenProg_mk (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) :
    gmLinkMovedNeighborsGenProg (mkDictParams U V w n_max h_space, d) =
      gmLinkMovedNeighborsProg U V w n_max h_space d := by rfl

theorem memoryCost_gmLinkMovedNeighborsProg_le (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ)
    (s : Memory.State) :
    memoryCost (gmLinkMovedNeighborsProg U V w n_max h_space d) s ≤ 34 := by
  unfold gmLinkMovedNeighborsProg
  dsimp only
  simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
    memoryCost_readGMProg, memoryCost_writeGMProg]
  split_ifs <;> simp only [memoryCost_writeGMProg, memoryCost_pure] <;> omega

theorem gmLinkMovedNeighborsProg_effect {U V w n_max h_space base p_del p_last : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    (s : Memory.State)
    (hpre : GmMovedSlabInv U V w n_max h_space base p_del p_last s) :
    let s' := (Memory.spec 0).clientState s
      (gmLinkMovedNeighborsProg U V w n_max h_space ((base, p_del), p_last))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offGM U V w n_max h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem =
      gmLinkMovedNeighbors n_max (gmAt base U V w n_max h_space s.mem) p_del p_last := by
  intro s'
  rcases hpre with ⟨hp_del_cap, hp_last_cap, hb_last, _, hbel_cap, habv_cap, _⟩
  set gm := gmAt base U V w n_max h_space s.mem
  set b_last := gm (gmSlabOwnerBIdx n_max p_last)
  set s_last := gm (gmSlabOwnerSIdx n_max p_last)
  set bel_last := gm (gmSlabBelowIdx n_max p_last)
  set abv_last := gm (gmSlabAboveIdx n_max p_last)
  set q_last := gm (gmQIdx b_last)
  have hownB_last_lt : gmSlabMetaBase n_max + 4 * p_last < globalMetaLen n_max :=
    gmSlabOwnerBIdx_lt hb_pos hp_last_cap
  have hownS_last_lt : gmSlabMetaBase n_max + 4 * p_last + 1 < globalMetaLen n_max :=
    gmSlabOwnerSIdx_lt hb_pos hp_last_cap
  have hbel_last_lt : gmSlabMetaBase n_max + 4 * p_last + 2 < globalMetaLen n_max :=
    gmSlabBelowIdx_lt hb_pos hp_last_cap
  have habv_last_lt : gmSlabMetaBase n_max + 4 * p_last + 3 < globalMetaLen n_max :=
    gmSlabAboveIdx_lt hb_pos hp_last_cap
  have hq_last_lt : 4 + 3 * b_last < globalMetaLen n_max := gmQIdx_lt hb_pos hb_last
  have hownB_del_lt : gmSlabMetaBase n_max + 4 * p_del < globalMetaLen n_max :=
    gmSlabOwnerBIdx_lt hb_pos hp_del_cap
  have hownS_del_lt : gmSlabMetaBase n_max + 4 * p_del + 1 < globalMetaLen n_max :=
    gmSlabOwnerSIdx_lt hb_pos hp_del_cap
  have hbel_del_lt : gmSlabMetaBase n_max + 4 * p_del + 2 < globalMetaLen n_max :=
    gmSlabBelowIdx_lt hb_pos hp_del_cap
  have habv_del_lt : gmSlabMetaBase n_max + 4 * p_del + 3 < globalMetaLen n_max :=
    gmSlabAboveIdx_lt hb_pos hp_del_cap
  have habv_bel_lt : 0 < s_last →
      gmSlabMetaBase n_max + 4 * bel_last + 3 < globalMetaLen n_max :=
    fun hs => gmSlabAboveIdx_lt hb_pos (hbel_cap hs)
  have hbel_abv_lt : s_last + 1 < q_last →
      gmSlabMetaBase n_max + 4 * abv_last + 2 < globalMetaLen n_max :=
    fun hs => gmSlabBelowIdx_lt hb_pos (habv_cap hs)
  have hmax_le : maxFullSlabs n_max ≤ n_max := maxFullSlabs_le n_max
  have hp_del_val_lt : p_del < 2 ^ globalPtrBits n_max :=
    lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hb_val_lt : b_last < 2 ^ globalPtrBits n_max := gmAt_lt ..
  have hs_val_lt : s_last < 2 ^ globalPtrBits n_max := gmAt_lt ..
  have hbel_val_lt : bel_last < 2 ^ globalPtrBits n_max := gmAt_lt ..
  have habv_val_lt : abv_last < 2 ^ globalPtrBits n_max := gmAt_lt ..
  have hres_b : (Memory.spec 0).clientResult s
      (readGMProg U V w n_max h_space (base, gmSlabMetaBase n_max + 4 * p_last)) = b_last :=
    clientResult_readGMProg s hownB_last_lt
  have hres_s : (Memory.spec 0).clientResult s
      (readGMProg U V w n_max h_space (base, gmSlabMetaBase n_max + 4 * p_last + 1)) = s_last :=
    clientResult_readGMProg s hownS_last_lt
  have hres_bel : (Memory.spec 0).clientResult s
      (readGMProg U V w n_max h_space (base, gmSlabMetaBase n_max + 4 * p_last + 2)) = bel_last :=
    clientResult_readGMProg s hbel_last_lt
  have hres_abv : (Memory.spec 0).clientResult s
      (readGMProg U V w n_max h_space (base, gmSlabMetaBase n_max + 4 * p_last + 3)) = abv_last :=
    clientResult_readGMProg s habv_last_lt
  have hres_q : (Memory.spec 0).clientResult s
      (readGMProg U V w n_max h_space (base, 4 + 3 * b_last)) = q_last :=
    clientResult_readGMProg s hq_last_lt
  obtain ⟨hf1, hout1, hq1, hv1, hl1, hg1⟩ :=
    writeGMProg_ite_effect (base := base) (U := U) (V := V) (h_space := h_space)
      (0 < s_last) hw habv_bel_lt (fun _ => hp_del_val_lt) s
  set s₁ := (Memory.spec 0).clientState s
    (if 0 < s_last then
      writeGMProg U V w n_max h_space ((base, gmSlabMetaBase n_max + 4 * bel_last + 3), p_del)
    else pure ())
  obtain ⟨hf2, hout2, hq2, hv2, hl2, hg2⟩ :=
    writeGMProg_ite_effect (base := base) (U := U) (V := V) (h_space := h_space)
      (s_last + 1 < q_last) hw hbel_abv_lt (fun _ => hp_del_val_lt) s₁
  set s₂ := (Memory.spec 0).clientState s₁
    (if s_last + 1 < q_last then
      writeGMProg U V w n_max h_space ((base, gmSlabMetaBase n_max + 4 * abv_last + 2), p_del)
    else pure ())
  obtain ⟨hf3, hout3, hq3, hv3, hl3, hg3⟩ :=
    writeGMProg_effect (base := base) (U := U) (V := V) (h_space := h_space)
      hw hownB_del_lt hb_val_lt s₂
  set s₃ := (Memory.spec 0).clientState s₂
    (writeGMProg U V w n_max h_space ((base, gmSlabMetaBase n_max + 4 * p_del), b_last))
  obtain ⟨hf4, hout4, hq4, hv4, hl4, hg4⟩ :=
    writeGMProg_effect (base := base) (U := U) (V := V) (h_space := h_space)
      hw hownS_del_lt hs_val_lt s₃
  set s₄ := (Memory.spec 0).clientState s₃
    (writeGMProg U V w n_max h_space ((base, gmSlabMetaBase n_max + 4 * p_del + 1), s_last))
  obtain ⟨hf5, hout5, hq5, hv5, hl5, hg5⟩ :=
    writeGMProg_effect (base := base) (U := U) (V := V) (h_space := h_space)
      hw hbel_del_lt hbel_val_lt s₄
  set s₅ := (Memory.spec 0).clientState s₄
    (writeGMProg U V w n_max h_space ((base, gmSlabMetaBase n_max + 4 * p_del + 2), bel_last))
  obtain ⟨hf6, hout6, hq6, hv6, hl6, hg6⟩ :=
    writeGMProg_effect (base := base) (U := U) (V := V) (h_space := h_space)
      hw habv_del_lt habv_val_lt s₅
  set s₆ := (Memory.spec 0).clientState s₅
    (writeGMProg U V w n_max h_space ((base, gmSlabMetaBase n_max + 4 * p_del + 3), abv_last))
  have hst : s' = s₆ := by
    change (Memory.spec 0).clientState s
      (gmLinkMovedNeighborsProg U V w n_max h_space ((base, p_del), p_last)) = s₆
    unfold gmLinkMovedNeighborsProg
    dsimp only
    rw [StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_b,
      StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_s,
      StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_bel,
      StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_abv,
      StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_q]
    repeat rw [StateTransitionSpec.clientState_bind]
  rw [hst]
  refine ⟨by rw [hf6, hf5, hf4, hf3, hf2, hf1],
    fun a ha => by rw [hout6 a ha, hout5 a ha, hout4 a ha, hout3 a ha, hout2 a ha, hout1 a ha],
    by rw [hq6, hq5, hq4, hq3, hq2, hq1],
    by rw [hv6, hv5, hv4, hv3, hv2, hv1],
    by rw [hl6, hl5, hl4, hl3, hl2, hl1], ?_⟩
  rw [hg6, hg5, hg4, hg3, hg2, hg1]
  rfl

private theorem gmLinkMovedNeighbors_bounds {U V w₀ n_max h_space w : ℕ}
    {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (h : GmMovedSlabPre U V w₀ n_max h_space w d.1.1 d.1.2 d.2 s) :
    let e_blast := (Memory.spec 0).clientResult s
      (readGMProg U V w₀ n_max h_space (d.1.1, gmSlabMetaBase n_max + 4 * d.2))
    let s1 := (Memory.spec 0).clientState s
      (readGMProg U V w₀ n_max h_space (d.1.1, gmSlabMetaBase n_max + 4 * d.2))
    let e_slast := (Memory.spec 0).clientResult s1
      (readGMProg U V w₀ n_max h_space (d.1.1, gmSlabMetaBase n_max + 4 * d.2 + 1))
    let s2 := (Memory.spec 0).clientState s1
      (readGMProg U V w₀ n_max h_space (d.1.1, gmSlabMetaBase n_max + 4 * d.2 + 1))
    let e_bellast := (Memory.spec 0).clientResult s2
      (readGMProg U V w₀ n_max h_space (d.1.1, gmSlabMetaBase n_max + 4 * d.2 + 2))
    let s3 := (Memory.spec 0).clientState s2
      (readGMProg U V w₀ n_max h_space (d.1.1, gmSlabMetaBase n_max + 4 * d.2 + 2))
    let e_abvlast := (Memory.spec 0).clientResult s3
      (readGMProg U V w₀ n_max h_space (d.1.1, gmSlabMetaBase n_max + 4 * d.2 + 3))
    let s4 := (Memory.spec 0).clientState s3
      (readGMProg U V w₀ n_max h_space (d.1.1, gmSlabMetaBase n_max + 4 * d.2 + 3))
    let e_qlast := (Memory.spec 0).clientResult s4
      (readGMProg U V w₀ n_max h_space (d.1.1, 4 + 3 * e_blast))
    gmSlabMetaBase n_max + 4 * d.2 < globalMetaLen n_max ∧
    gmSlabMetaBase n_max + 4 * d.2 + 1 < globalMetaLen n_max ∧
    gmSlabMetaBase n_max + 4 * d.2 + 2 < globalMetaLen n_max ∧
    gmSlabMetaBase n_max + 4 * d.2 + 3 < globalMetaLen n_max ∧
    4 + 3 * e_blast < globalMetaLen n_max ∧
    (0 < e_slast → gmSlabMetaBase n_max + 4 * e_bellast + 3 < globalMetaLen n_max) ∧
    e_slast + 1 ≤ n_max ∧
    (e_slast + 1 < e_qlast → gmSlabMetaBase n_max + 4 * e_abvlast + 2 < globalMetaLen n_max) ∧
    gmSlabMetaBase n_max + 4 * d.1.2 < globalMetaLen n_max ∧
    gmSlabMetaBase n_max + 4 * d.1.2 + 1 < globalMetaLen n_max ∧
    gmSlabMetaBase n_max + 4 * d.1.2 + 2 < globalMetaLen n_max ∧
    gmSlabMetaBase n_max + 4 * d.1.2 + 3 < globalMetaLen n_max := by
  rcases h with ⟨_, hp_del_cap, hp_last_cap, hb_last, hs_le, hbel_cap, habv_cap, hb_pos⟩
  set gm := gmAt d.1.1 U V w₀ n_max h_space s.mem
  have hownB_lt := gmSlabOwnerBIdx_lt hb_pos hp_last_cap
  have hownS_lt := gmSlabOwnerSIdx_lt hb_pos hp_last_cap
  have hbel_lt := gmSlabBelowIdx_lt hb_pos hp_last_cap
  have habv_lt := gmSlabAboveIdx_lt hb_pos hp_last_cap
  intro e_blast s1 e_slast s2 e_bellast s3 e_abvlast s4 e_qlast
  have heblast : e_blast = gm (gmSlabOwnerBIdx n_max d.2) :=
    clientResult_readGMProg s (by exact hownB_lt)
  have hs1 : s1 = s := rfl
  have heslast : e_slast = gm (gmSlabOwnerSIdx n_max d.2) := by
    dsimp only [e_slast]; rw [hs1]; exact clientResult_readGMProg s (by exact hownS_lt)
  have hs2 : s2 = s := rfl
  have hebellast : e_bellast = gm (gmSlabBelowIdx n_max d.2) := by
    dsimp only [e_bellast]; rw [hs2]; exact clientResult_readGMProg s (by exact hbel_lt)
  have hs3 : s3 = s := rfl
  have heabvlast : e_abvlast = gm (gmSlabAboveIdx n_max d.2) := by
    dsimp only [e_abvlast]; rw [hs3]; exact clientResult_readGMProg s (by exact habv_lt)
  have hs4 : s4 = s := rfl
  have hq_lt : 4 + 3 * gm (gmSlabOwnerBIdx n_max d.2) < globalMetaLen n_max :=
    gmQIdx_lt hb_pos hb_last
  have heqlast : e_qlast = gm (gmQIdx (gm (gmSlabOwnerBIdx n_max d.2))) := by
    dsimp only [e_qlast]; rw [hs4, heblast]; exact clientResult_readGMProg s (by exact hq_lt)
  refine ⟨hownB_lt, hownS_lt, hbel_lt, habv_lt, by rw [heblast]; exact hq_lt,
    fun hs => by rw [hebellast]; rw [heslast] at hs; exact gmSlabAboveIdx_lt hb_pos (hbel_cap hs),
    by rw [heslast]; exact hs_le,
    fun hs => by
      rw [heabvlast]; rw [heslast, heqlast] at hs
      exact gmSlabBelowIdx_lt hb_pos (habv_cap hs),
    gmSlabOwnerBIdx_lt hb_pos hp_del_cap,
    gmSlabOwnerSIdx_lt hb_pos hp_del_cap,
    gmSlabBelowIdx_lt hb_pos hp_del_cap,
    gmSlabAboveIdx_lt hb_pos hp_del_cap⟩

theorem realizes_gmLinkMovedNeighborsGen :
    Realizes .exact gmLinkMovedNeighborsGenProg
      (WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ))) (WordEncoding.encode (α := Unit))
      GmMovedSlabGenPre
      (fun _ _ => 0) := by
  have hrg := realizes_readGMGen
  have hwg := realizes_writeGMGen
  refine Realizes.congr (p := fun d : DictParams × ((ℕ × ℕ) × ℕ) => do
      let ownB_last_idx ← pure (dpGmSlabMetaBase d.1 + 4 * d.2.2)
      let b_last ← readGMGenProg (d.1, (d.2.1.1, ownB_last_idx))
      let ownS_last_idx ← pure (dpGmSlabMetaBase d.1 + 4 * d.2.2 + 1)
      let s_last ← readGMGenProg (d.1, (d.2.1.1, ownS_last_idx))
      let bel_last_idx ← pure (dpGmSlabMetaBase d.1 + 4 * d.2.2 + 2)
      let bel_last ← readGMGenProg (d.1, (d.2.1.1, bel_last_idx))
      let abv_last_idx ← pure (dpGmSlabMetaBase d.1 + 4 * d.2.2 + 3)
      let abv_last ← readGMGenProg (d.1, (d.2.1.1, abv_last_idx))
      let q_last_idx ← pure (4 + 3 * b_last)
      let q_last ← readGMGenProg (d.1, (d.2.1.1, q_last_idx))
      let i0 ← pure 0
      (if i0 < s_last then do
        let abv_bel_idx ← pure (dpGmSlabMetaBase d.1 + 4 * bel_last + 3)
        writeGMGenProg (d.1, ((d.2.1.1, abv_bel_idx), d.2.1.2))
      else pure ()) >>= fun _ => do
        let s_last_next ← pure (s_last + 1)
        (if s_last_next < q_last then do
          let bel_abv_idx ← pure (dpGmSlabMetaBase d.1 + 4 * abv_last + 2)
          writeGMGenProg (d.1, ((d.2.1.1, bel_abv_idx), d.2.1.2))
        else pure ()) >>= fun _ => do
          let ownB_del_idx ← pure (dpGmSlabMetaBase d.1 + 4 * d.2.1.2)
          writeGMGenProg (d.1, ((d.2.1.1, ownB_del_idx), b_last))
          let ownS_del_idx ← pure (dpGmSlabMetaBase d.1 + 4 * d.2.1.2 + 1)
          writeGMGenProg (d.1, ((d.2.1.1, ownS_del_idx), s_last))
          let bel_del_idx ← pure (dpGmSlabMetaBase d.1 + 4 * d.2.1.2 + 2)
          writeGMGenProg (d.1, ((d.2.1.1, bel_del_idx), bel_last))
          let abv_del_idx ← pure (dpGmSlabMetaBase d.1 + 4 * d.2.1.2 + 3)
          writeGMGenProg (d.1, ((d.2.1.1, abv_del_idx), abv_last))) ?_
    (fun d => by simp only [gmLinkMovedNeighborsGenProg, pure_bind])
  realizeDictWith [gmMovedSlabGenPre_mk]
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2.2.2.2 hw hnU hU
      (le_of_lt (gmLinkMovedNeighbors_bounds h).1)
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact h.1
  · exact (gmLinkMovedNeighbors_bounds h).1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2.2.2.2 hw hnU hU
      (le_of_lt (gmLinkMovedNeighbors_bounds h).2.1)
  · exact (gmLinkMovedNeighbors_bounds h).2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2.2.2.2 hw hnU hU
      (le_of_lt (gmLinkMovedNeighbors_bounds h).2.2.1)
  · exact (gmLinkMovedNeighbors_bounds h).2.2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2.2.2.2 hw hnU hU
      (le_of_lt (gmLinkMovedNeighbors_bounds h).2.2.2.1)
  · exact (gmLinkMovedNeighbors_bounds h).2.2.2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2.2.2.2 hw hnU hU
      (le_of_lt (gmLinkMovedNeighbors_bounds h).2.2.2.2.1)
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact (gmLinkMovedNeighbors_bounds h).2.2.2.2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2.2.2.2 hw hnU hU
      (le_of_lt ((gmLinkMovedNeighbors_bounds h).2.2.2.2.2.1 hc))
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact h.1
  · exact ((gmLinkMovedNeighbors_bounds h).2.2.2.2.2.1 hc)
  · exact fits_of_le_max_n_one h.1 hw hnU hU
      ((gmLinkMovedNeighbors_bounds h).2.2.2.2.2.2.1.trans (Nat.le_max_left n_max 1))
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2.2.2.2 hw hnU hU
      (le_of_lt ((gmLinkMovedNeighbors_bounds h).2.2.2.2.2.2.2.1 hc))
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact h.1
  · exact ((gmLinkMovedNeighbors_bounds h).2.2.2.2.2.2.2.1 hc)
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2.2.2.2 hw hnU hU
      (le_of_lt (gmLinkMovedNeighbors_bounds h).2.2.2.2.2.2.2.2.1)
  · exact (gmLinkMovedNeighbors_bounds h).2.2.2.2.2.2.2.2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2.2.2.2 hw hnU hU
      (le_of_lt (gmLinkMovedNeighbors_bounds h).2.2.2.2.2.2.2.2.2.1)
  · exact (gmLinkMovedNeighbors_bounds h).2.2.2.2.2.2.2.2.2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2.2.2.2 hw hnU hU
      (le_of_lt (gmLinkMovedNeighbors_bounds h).2.2.2.2.2.2.2.2.2.2.1)
  · exact (gmLinkMovedNeighbors_bounds h).2.2.2.2.2.2.2.2.2.2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2.2.2.2 hw hnU hU
      (le_of_lt (gmLinkMovedNeighbors_bounds h).2.2.2.2.2.2.2.2.2.2.2)
  · exact (gmLinkMovedNeighbors_bounds h).2.2.2.2.2.2.2.2.2.2.2

/-- Parameter-free `Memory.Prog` operation compacting the slab pool by relocating the metadata of
`p_last = gm 0 - 1` into `p_del = d.2.2` (when `p_del < p_last`) and decrementing `gm 0`. -/
def gmCompactSlabGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog Unit := do
  let n_slabs ← readGMGenProg (d.1, (d.2.1, 0))
  let p_last := n_slabs - 1
  if d.2.2 < p_last then
    gmRelinkMovedSlabGenProg (d.1, (d.2, p_last))
    gmLinkMovedNeighborsGenProg (d.1, (d.2, p_last))
    writeGMGenProg (d.1, ((d.2.1, 0), p_last))
  else
    writeGMGenProg (d.1, ((d.2.1, 0), p_last))

/-- `Memory.Prog` operation compacting the slab pool by relocating the metadata of
`p_last = gm 0 - 1` into `p_del = d.2` (when `p_del < p_last`) and decrementing `gm 0`. -/
def gmCompactSlabProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog Unit := do
  let n_slabs ← readGMProg U V w n_max h_space (d.1, 0)
  let p_last := n_slabs - 1
  if d.2 < p_last then
    gmRelinkMovedSlabProg U V w n_max h_space (d, p_last)
    gmLinkMovedNeighborsProg U V w n_max h_space (d, p_last)
    writeGMProg U V w n_max h_space ((d.1, 0), p_last)
  else
    writeGMProg U V w n_max h_space ((d.1, 0), p_last)

@[simp] theorem gmCompactSlabGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    gmCompactSlabGenProg (mkDictParams U V w n_max h_space, d) =
      gmCompactSlabProg U V w n_max h_space d := by rfl

theorem memoryCost_gmCompactSlabProg_le (U V w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (gmCompactSlabProg U V w n_max h_space d) s ≤ 54 := by
  unfold gmCompactSlabProg
  dsimp only
  rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_readGMProg]
  split_ifs with hlt
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_writeGMProg]
    have h1 := memoryCost_gmRelinkMovedSlabProg_le U V w n_max h_space
      (d, (Memory.spec 0).clientResult s (readGMProg U V w n_max h_space (d.1, 0)) - 1)
      ((Memory.spec 0).clientState s (readGMProg U V w n_max h_space (d.1, 0)))
    have h2 := memoryCost_gmLinkMovedNeighborsProg_le U V w n_max h_space
      (d, (Memory.spec 0).clientResult s (readGMProg U V w n_max h_space (d.1, 0)) - 1)
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState s (readGMProg U V w n_max h_space (d.1, 0)))
        (gmRelinkMovedSlabProg U V w n_max h_space
          (d, (Memory.spec 0).clientResult s (readGMProg U V w n_max h_space (d.1, 0)) - 1)))
    omega
  · rw [memoryCost_writeGMProg]
    omega

/-- Pure bounds invariant for `gmCompactSlabProg`. -/
@[expose]
def GmCompactSlabInv (U V w₀ n_max h_space base p_del : ℕ) (s : Memory.State) : Prop :=
  let gm := gmAt base U V w₀ n_max h_space s.mem
  let p_last := gm 0 - 1
  1 ≤ gm 0 ∧
  gm 0 ≤ maxFullSlabs n_max ∧
  p_del < gm 0 ∧
  (p_del < p_last → GmMovedSlabInv U V w₀ n_max h_space base p_del p_last s)

/-- Precondition for `gmCompactSlabProg`. -/
@[expose]
def GmCompactSlabPre (U V w₀ n_max h_space w base p_del : ℕ) (s : Memory.State) : Prop :=
  let gm := gmAt base U V w₀ n_max h_space s.mem
  let p_last := gm 0 - 1
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  1 ≤ gm 0 ∧
  gm 0 ≤ maxFullSlabs n_max ∧
  p_del < gm 0 ∧
  (p_del < p_last → GmMovedSlabPre U V w₀ n_max h_space w base p_del p_last s)

/-- Parameter-free precondition for `gmCompactSlabGenProg`. -/
@[expose]
def GmCompactSlabGenPre (w : ℕ) (d : DictParams × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  let gm := gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem
  let p_last := gm 0 - 1
  DictEnvGen w d.1 d.2.1 ∧
  1 ≤ gm 0 ∧
  gm 0 ≤ maxFullSlabs (dpNMax d.1) ∧
  d.2.2 < gm 0 ∧
  (d.2.2 < p_last → GmMovedSlabGenPre w (d.1, (d.2, p_last)) s)

@[simp] theorem gmCompactSlabGenPre_mk (U V w₀ n_max h_space w : ℕ) (d : ℕ × ℕ)
    (s : Memory.State) :
    GmCompactSlabGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      GmCompactSlabPre U V w₀ n_max h_space w d.1 d.2 s := Iff.rfl

theorem gmMovedSlabInv_after_relink {U V w₀ n_max h_space base p_del p_last : ℕ}
    {s : Memory.State} (hw : 0 < w₀) (hb_pos : 0 < bucketBits n_max)
    (hinv : GmMovedSlabInv U V w₀ n_max h_space base p_del p_last s) :
    GmMovedSlabInv U V w₀ n_max h_space base p_del p_last
      ((Memory.spec 0).clientState s
        (gmRelinkMovedSlabProg U V w₀ n_max h_space ((base, p_del), p_last))) := by
  obtain ⟨_, _, _, _, _, hgm⟩ := gmRelinkMovedSlabProg_effect hw hb_pos s hinv
  rcases hinv with ⟨hp_del_cap, hp_last_cap, hb_last, hs_le, hbel_cap, habv_cap, _⟩
  rcases gmRelinkMovedSlab_preserves_meta
    (gmAt base U V w₀ n_max h_space s.mem) (p_del := p_del) hb_last with ⟨_, hpQ, hpGe⟩
  have hB : gmSlabMetaBase n_max ≤ gmSlabOwnerBIdx n_max p_last := by
    unfold gmSlabOwnerBIdx; omega
  have hS : gmSlabMetaBase n_max ≤ gmSlabOwnerSIdx n_max p_last := by
    unfold gmSlabOwnerSIdx; omega
  have hBel : gmSlabMetaBase n_max ≤ gmSlabBelowIdx n_max p_last := by
    unfold gmSlabBelowIdx; omega
  have hAbv : gmSlabMetaBase n_max ≤ gmSlabAboveIdx n_max p_last := by
    unfold gmSlabAboveIdx; omega
  unfold GmMovedSlabInv
  dsimp only
  rw [hgm, hpGe _ hB, hpGe _ hS, hpGe _ hBel, hpGe _ hAbv, hpQ]
  exact ⟨hp_del_cap, hp_last_cap, hb_last, hs_le, hbel_cap, habv_cap, hb_pos⟩

theorem gmMovedSlabPre_after_relink {U V w₀ n_max h_space w base p_del p_last : ℕ}
    {s : Memory.State} (hw : 0 < w₀)
    (hpre : GmMovedSlabPre U V w₀ n_max h_space w base p_del p_last s) :
    GmMovedSlabPre U V w₀ n_max h_space w base p_del p_last
      ((Memory.spec 0).clientState s
        (gmRelinkMovedSlabProg U V w₀ n_max h_space ((base, p_del), p_last))) :=
  ⟨hpre.1, gmMovedSlabInv_after_relink hw hpre.2.2.2.2.2.2.2 hpre.2⟩

theorem gmCompactSlabProg_effect {U V w n_max h_space base p_del : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    (s : Memory.State)
    (hpre : GmCompactSlabInv U V w n_max h_space base p_del s) :
    let s' := (Memory.spec 0).clientState s (gmCompactSlabProg U V w n_max h_space (base, p_del))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offGM U V w n_max h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem =
      gmCompactSlab n_max (gmAt base U V w n_max h_space s.mem) p_del := by
  intro s'
  rcases hpre with ⟨h0_pos, h0_le, _, hcond⟩
  set gm := gmAt base U V w n_max h_space s.mem
  set p_last := gm 0 - 1
  have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
  have hmax_le : maxFullSlabs n_max ≤ n_max := maxFullSlabs_le n_max
  have hp_last_val_lt : p_last < 2 ^ globalPtrBits n_max :=
    lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  by_cases hlt : p_del < p_last
  · have hm1 := hcond hlt
    have hm2 := gmMovedSlabInv_after_relink hw hb_pos hm1
    obtain ⟨hf1, hout1, hq1, hv1, hl1, hg1⟩ := gmRelinkMovedSlabProg_effect hw hb_pos s hm1
    let s₁ := (Memory.spec 0).clientState s
      (gmRelinkMovedSlabProg U V w n_max h_space ((base, p_del), p_last))
    obtain ⟨hf2, hout2, hq2, hv2, hl2, hg2⟩ := gmLinkMovedNeighborsProg_effect hw hb_pos s₁ hm2
    let s₂ := (Memory.spec 0).clientState s₁
      (gmLinkMovedNeighborsProg U V w n_max h_space ((base, p_del), p_last))
    obtain ⟨hf3, hout3, hq3, hv3, hl3, hg3⟩ :=
      writeGMProg_effect (base := base) (U := U) (V := V) (h_space := h_space)
        hw h0_lt hp_last_val_lt s₂
    let s₃ := (Memory.spec 0).clientState s₂ (writeGMProg U V w n_max h_space ((base, 0), p_last))
    have hst : s' = s₃ := by
      change (Memory.spec 0).clientState s
        (gmCompactSlabProg U V w n_max h_space (base, p_del)) = s₃
      unfold gmCompactSlabProg
      dsimp only
      rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
        clientResult_readGMProg s h0_lt, ite_eq_left hlt,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
    rw [hst]
    refine ⟨by rw [hf3, hf2, hf1],
      fun a ha => by rw [hout3 a ha, hout2 a ha, hout1 a ha],
      by rw [hq3, hq2, hq1], by rw [hv3, hv2, hv1], by rw [hl3, hl2, hl1], ?_⟩
    rw [hg3, hg2, hg1]
    exact gmCompactSlab_eq_parts gm hlt hm1.2.2.1
  · obtain ⟨hf1, hout1, hq1, hv1, hl1, hg1⟩ :=
      writeGMProg_effect (base := base) (U := U) (V := V) (h_space := h_space)
        hw h0_lt hp_last_val_lt s
    let s₁ := (Memory.spec 0).clientState s (writeGMProg U V w n_max h_space ((base, 0), p_last))
    have hst : s' = s₁ := by
      change (Memory.spec 0).clientState s
        (gmCompactSlabProg U V w n_max h_space (base, p_del)) = s₁
      unfold gmCompactSlabProg
      dsimp only
      rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
        clientResult_readGMProg s h0_lt, ite_eq_right hlt]
    rw [hst]
    refine ⟨hf1, hout1, hq1, hv1, hl1, ?_⟩
    unfold gmCompactSlab
    rw [ite_eq_right hlt, hg1]

theorem realizes_gmCompactSlabGen :
    Realizes .exact gmCompactSlabGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      GmCompactSlabGenPre
      (fun _ _ => 0) := by
  have hrg := realizes_readGMGen
  have hwg := realizes_writeGMGen
  have hrel := realizes_gmRelinkMovedSlabGen
  have hlnk := realizes_gmLinkMovedNeighborsGen
  refine Realizes.congr (p := fun d : DictParams × (ℕ × ℕ) => do
      let i0 ← pure 0
      let n_slabs ← readGMGenProg (d.1, (d.2.1, i0))
      let p_last ← pure (n_slabs - 1)
      if d.2.2 < p_last then do
        gmRelinkMovedSlabGenProg (d.1, (d.2, p_last))
        gmLinkMovedNeighborsGenProg (d.1, (d.2, p_last))
        writeGMGenProg (d.1, ((d.2.1, i0), p_last))
      else
        writeGMGenProg (d.1, ((d.2.1, i0), p_last))) ?_
    (fun d => by simp only [gmCompactSlabGenProg, pure_bind])
  realizeDictWith [gmCompactSlabGenPre_mk, gmMovedSlabGenPre_mk,
    gmRelinkMovedSlabGenProg_mk, gmLinkMovedNeighborsGenProg_mk]
  · exact h.1
  · unfold globalMetaLen; omega
  · have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
    rw [clientResult_readGMProg s h0_lt]; exact h.2.1
  · have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
    rw [clientResult_readGMProg s h0_lt] at hc ⊢
    exact h.2.2.2.2 hc
  · have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
    rw [clientResult_readGMProg s h0_lt] at hc ⊢
    exact gmMovedSlabPre_after_relink hw (h.2.2.2.2 hc)
  · exact h.1
  · unfold globalMetaLen; omega
  · exact h.1
  · unfold globalMetaLen; omega

/-- Parameter-free `Memory.Prog` operation popping the top slab of bucket `b = d.2.2` at
`base = d.2.1` and compacting the physical slab pool. -/
def gmPopSlabGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog Unit := do
  let p_del ← gmUnlinkTopSlabGenProg d
  gmCompactSlabGenProg (d.1, (d.2.1, p_del))

/-- `Memory.Prog` operation popping the top slab of bucket `b = d.2` at `base = d.1` and compacting
the physical slab pool. -/
def gmPopSlabProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog Unit := do
  let p_del ← gmUnlinkTopSlabProg U V w n_max h_space d
  gmCompactSlabProg U V w n_max h_space (d.1, p_del)

@[simp] theorem gmPopSlabGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    gmPopSlabGenProg (mkDictParams U V w n_max h_space, d) =
      gmPopSlabProg U V w n_max h_space d := by rfl

theorem memoryCost_gmPopSlabProg_le (U V w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (gmPopSlabProg U V w n_max h_space d) s ≤ 68 := by
  unfold gmPopSlabProg
  rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_gmUnlinkTopSlabProg]
  have h := memoryCost_gmCompactSlabProg_le U V w n_max h_space
    (d.1, (Memory.spec 0).clientResult s (gmUnlinkTopSlabProg U V w n_max h_space d))
    ((Memory.spec 0).clientState s (gmUnlinkTopSlabProg U V w n_max h_space d))
  omega

theorem gmCompactSlabInv_of_slabBijection {U V w₀ n_max h_space base b : ℕ}
    (hw : 0 < w₀) (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (s : Memory.State)
    (hslab : SlabBijection n_max (gmAt base U V w₀ n_max h_space s.mem)
      (fun b' => gmAt base U V w₀ n_max h_space s.mem (gmQIdx b'))
      (gmAt base U V w₀ n_max h_space s.mem 0))
    (hq_pos : 1 ≤ gmAt base U V w₀ n_max h_space s.mem (gmQIdx b)) :
    GmCompactSlabInv U V w₀ n_max h_space base
      ((Memory.spec 0).clientResult s (gmUnlinkTopSlabProg U V w₀ n_max h_space (base, b)))
      ((Memory.spec 0).clientState s (gmUnlinkTopSlabProg U V w₀ n_max h_space (base, b))) := by
  obtain ⟨hres, _, _, _, _, _, hgm⟩ :=
    gmUnlinkTopSlabProg_effect (U := U) (V := V) (h_space := h_space) hw hb_pos hb s hslab hq_pos
  set gm := gmAt base U V w₀ n_max h_space s.mem
  have hu := gmUnlinkTopSlab_fields gm hb
  rcases hu with ⟨hu0, _, _, huQ, _, huGe, _⟩
  have hB_ge : ∀ p, gmSlabDirBase n_max ≤ gmSlabOwnerBIdx n_max p :=
    fun _ => by unfold gmSlabOwnerBIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hS_ge : ∀ p, gmSlabDirBase n_max ≤ gmSlabOwnerSIdx n_max p :=
    fun _ => by unfold gmSlabOwnerSIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hBel_ge : ∀ p, gmSlabDirBase n_max ≤ gmSlabBelowIdx n_max p :=
    fun _ => by unfold gmSlabBelowIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hAbv_ge : ∀ p, gmSlabDirBase n_max ≤ gmSlabAboveIdx n_max p :=
    fun _ => by unfold gmSlabAboveIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hp_del_lt : gm (gmSlabTopIdx b) < gm 0 := hslab.top_lt hb hq_pos
  unfold GmCompactSlabInv GmMovedSlabInv
  dsimp only
  rw [hres, hgm, hu0]
  refine ⟨by omega, hslab.nslabs_le, hp_del_lt, ?_⟩
  intro hlt
  rw [huGe _ (hB_ge _), huGe _ (hS_ge _), huGe _ (hBel_ge _), huGe _ (hAbv_ge _)]
  obtain ⟨hb_last, hs_last, hptr_last⟩ := hslab.owner_valid (gm 0 - 1) (by omega)
  have hq_last_le : gm (gmQIdx (gm (gmSlabOwnerBIdx n_max (gm 0 - 1)))) ≤ gm 0 :=
    q_le_nslabs_of_slabBijection hslab hb_last
  have hmax_le : maxFullSlabs n_max ≤ n_max := maxFullSlabs_le n_max
  refine ⟨lt_of_lt_of_le hp_del_lt hslab.nslabs_le,
    lt_of_lt_of_le (by omega : gm 0 - 1 < gm 0) hslab.nslabs_le,
    hb_last, by have := hslab.nslabs_le; omega, ?_, ?_, hb_pos⟩
  · intro hs_pos
    have hbel_eq := hslab.below_eq _ hb_last _ hs_last hs_pos
    rw [hptr_last] at hbel_eq
    rw [hbel_eq]
    exact hslab.ptr_lt_maxFullSlabs hb_last (by omega)
  · intro hs_lt_q
    rw [huQ _ hb_last] at hs_lt_q
    have hs1_lt : gm (gmSlabOwnerSIdx n_max (gm 0 - 1)) + 1 <
        gm (gmQIdx (gm (gmSlabOwnerBIdx n_max (gm 0 - 1)))) := by
      split_ifs at hs_lt_q with hbeq
      · subst hbeq; omega
      · exact hs_lt_q
    have habv_eq := hslab.above_eq _ hb_last _ hs_last hs1_lt
    rw [hptr_last] at habv_eq
    rw [habv_eq]
    exact hslab.ptr_lt_maxFullSlabs hb_last hs1_lt

theorem gmCompactSlabPre_of_gmPopSlabPre {U V w₀ n_max h_space w base b : ℕ} {s : Memory.State}
    (hw : 0 < w₀)
    (h : GmPopSlabPre U V w₀ n_max h_space w base b s) :
    GmCompactSlabPre U V w₀ n_max h_space w base
      ((Memory.spec 0).clientResult s (gmUnlinkTopSlabProg U V w₀ n_max h_space (base, b)))
      ((Memory.spec 0).clientState s (gmUnlinkTopSlabProg U V w₀ n_max h_space (base, b))) := by
  rcases h with ⟨hdict, hslab, hb, hq_pos, hb_pos⟩
  have hinv := gmCompactSlabInv_of_slabBijection hw hb_pos hb s hslab hq_pos
  rcases hinv with ⟨h1, h2, h3, h4⟩
  exact ⟨hdict, h1, h2, h3, fun hlt => ⟨hdict, h4 hlt⟩⟩

/-- Under `SlabBijection` and `1 ≤ gm (gmQIdx b)` (`b < numBuckets n_max`), `gmPopSlabProg` runs in
`memoryCost ≤ 68` (`memoryCost_gmPopSlabProg_le`) and preserves `frontier`, `quotAt`, `valAt`,
`lmAt`, and memory outside
`[base + offGM U V w n_max h_space, base + totalSpace U V w n_max h_space)`. It updates `gmAt` to
`gmPopSlab n_max gm b`, unlinking the top slab `p_del` of bucket `b` and compacting
`p_last = gm 0 - 1` into `p_del`. -/
theorem gmPopSlabProg_effect {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (s : Memory.State)
    (hslab : SlabBijection n_max (gmAt base U V w n_max h_space s.mem)
      (fun b' => gmAt base U V w n_max h_space s.mem (gmQIdx b'))
      (gmAt base U V w n_max h_space s.mem 0))
    (hq_pos : 1 ≤ gmAt base U V w n_max h_space s.mem (gmQIdx b)) :
    let s' := (Memory.spec 0).clientState s (gmPopSlabProg U V w n_max h_space (base, b))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offGM U V w n_max h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem =
      gmPopSlab n_max (gmAt base U V w n_max h_space s.mem) b := by
  intro s'
  let s₁ := (Memory.spec 0).clientState s (gmUnlinkTopSlabProg U V w n_max h_space (base, b))
  let p_del := (Memory.spec 0).clientResult s (gmUnlinkTopSlabProg U V w n_max h_space (base, b))
  obtain ⟨hres, hf1, hout1, hq1, hv1, hl1, hg1⟩ :=
    gmUnlinkTopSlabProg_effect (U := U) (V := V) (h_space := h_space) hw hb_pos hb s hslab hq_pos
  have hcomp : GmCompactSlabInv U V w n_max h_space base p_del s₁ :=
    gmCompactSlabInv_of_slabBijection hw hb_pos hb s hslab hq_pos
  obtain ⟨hf2, hout2, hq2, hv2, hl2, hg2⟩ :=
    gmCompactSlabProg_effect hw hb_pos s₁ hcomp
  have hst : s' = (Memory.spec 0).clientState s₁
      (gmCompactSlabProg U V w n_max h_space (base, p_del)) := by
    change (Memory.spec 0).clientState s (gmPopSlabProg U V w n_max h_space (base, b)) = _
    unfold gmPopSlabProg
    rw [StateTransitionSpec.clientState_bind]
  rw [hst]
  refine ⟨by rw [hf2, hf1], fun a ha => by rw [hout2 a ha, hout1 a ha],
    by rw [hq2, hq1], by rw [hv2, hv1], by rw [hl2, hl1], ?_⟩
  rw [hg2, hg1]
  dsimp only [p_del]
  rw [hres]
  rfl

theorem realizes_gmPopSlabGen :
    Realizes .exact gmPopSlabGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      GmPopSlabGenPre
      (fun _ _ => 0) := by
  have hunl := realizes_gmUnlinkTopSlabGen
  have hcmp := realizes_gmCompactSlabGen
  unfold gmPopSlabGenProg
  realizeDictWith [gmPopSlabGenPre_mk, gmCompactSlabGenPre_mk, gmUnlinkTopSlabGenProg_mk]
  · exact h
  · exact gmCompactSlabPre_of_gmPopSlabPre hw h

end Cslib.DataStructure.Dictionary.WordRAM.Succinct

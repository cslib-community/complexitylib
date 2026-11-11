/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctDeleteOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctTailOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabPool
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabMove
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabDemote
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabOps
import all CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctDeleteOps

/-!
# Memory History Admissibility (`ValidHistory`) for Succinct Dictionary Programs

This module proves `(Memory.spec w).ValidHistory` for all `Memory.Prog` operations of the
fixed-capacity succinct dictionary (`queryBodyProg`, `insertBodyProg`, `deletePrepProg`, and
`deleteFinishProg`), discharging the admissibility obligation required when extracting native
Word-RAM `Code` via `Realizes.code_spec`. The proofs unfold the unexposed programs of the tail and
slab operation modules and reuse private bound lemmas of `SuccinctTailOps`, `SuccinctSlabPool`,
`SuccinctSlabMove`, `SuccinctSlabDemote` and `SuccinctDeleteOps`; from `SuccinctSlabOps` they need
only the bodies of `lastSlotOfProg`, `pushBackTailWriteProg`, `pushBackSlotProg` and
`popBackSlotProg`. This module reads all of these through `import all`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.ValidMem`: memory state well-formedness at word
  width `w` and frontier `≥ F`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.ValidProg`: predicate asserting that a
  `Memory.Prog` client produces a valid memory history from `s` whenever `ValidMem w F s` holds.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.dictFrontier`: standard dictionary frontier
  `base + totalSpace U V w n_max h_space`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.validProg_queryBody`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.validProg_insertBody`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.validProg_deletePrep`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.validProg_deleteFinish`: memory history
  admissibility for the four top-level `Memory.Prog` dictionary subroutines.
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

/-! ## Section 1: `ValidMem`, `ValidProg` combinators, and bit-packed array primitives -/

/-- A memory state is well-formed at word size `w` and has frontier at least `F`. -/
@[expose] def ValidMem (w F : ℕ) (s : Memory.State) : Prop :=
  Memory.WellFormed w s ∧ F ≤ s.frontier

/-- A `Memory.Prog` client produces a valid memory history from `s` whenever `ValidMem w F s`
holds. -/
@[expose] def ValidProg {α : Type} (w F : ℕ) (s : Memory.State) (p : Memory.Prog α) : Prop :=
  ValidMem w F s → (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)

theorem validMem_clientState {α : Type} {w F : ℕ} {s : Memory.State} {p : Memory.Prog α}
    (hm : ValidMem w F s) (hp : ValidProg w F s p) :
    ValidMem w F ((Memory.spec 0).clientState s p) := by
  have hv := hp hm
  rw [← clientState_width w, ← (Memory.spec w).run_runClient p s]
  exact ⟨hm.1.run hv, hm.2.trans (Memory.frontier_le_run s _)⟩

theorem validProg_pure {α : Type} {w F : ℕ} {s : Memory.State} (a : α) :
    ValidProg w F s (pure a) :=
  fun _ => trivial

theorem validProg_bind {α β : Type} {w F : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : ValidProg w F s p)
    (hq : ValidProg w F ((Memory.spec 0).clientState s p)
      (q ((Memory.spec 0).clientResult s p))) :
    ValidProg w F s (p >>= q) := by
  intro hm
  change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p.bind q))
  rw [validHistory_bind, clientResult_width, clientState_width]
  exact ⟨hp hm, hq (validMem_clientState hm hp)⟩

theorem validProg_seq {α β : Type} {w F : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {r : Memory.Prog β}
    (hp : ValidProg w F s p)
    (hr : ∀ s', ValidProg w F s' r) :
    ValidProg w F s (p >>= fun _ => r) :=
  validProg_bind hp (hr _)

theorem validProg_ite {α : Type} {w F : ℕ} {s : Memory.State} {c : Prop} [Decidable c]
    {p₁ p₂ : Memory.Prog α}
    (h₁ : c → ValidProg w F s p₁) (h₂ : ¬c → ValidProg w F s p₂) :
    ValidProg w F s (if c then p₁ else p₂) := by
  split_ifs with h
  · exact h₁ h
  · exact h₂ h

theorem validProg_iterate {δ σ : Type} {w F : ℕ}
    {body : δ × σ → Memory.Prog σ} {safe : ℕ → δ × σ → Memory.State → Prop}
    {d : δ} (n : ℕ) (a : σ) (s : Memory.State)
    (hbody : ∀ a' s', safe w (d, a') s' → ValidProg w F s' (body (d, a')))
    (hsafe : iterationSafe body safe w d n a s) :
    ValidProg w F s (iterate body d n a) := by
  induction n generalizing a s with
  | zero => exact validProg_pure a
  | succ n ih =>
    exact validProg_bind (hbody a s hsafe.1) (ih _ _ hsafe.2)

theorem validProg_boundedWhile {δ σ : Type} {w F : ℕ}
    {guard : δ → σ → Prop} [∀ d a, Decidable (guard d a)]
    {body : δ × σ → Memory.Prog σ} {safe : ℕ → δ × σ → Memory.State → Prop}
    {d : δ} (n : ℕ) (a : σ) (s : Memory.State)
    (hbody : ∀ a' s', safe w (d, a') s' → ValidProg w F s' (body (d, a')))
    (hsafe : whileSafe guard body safe w d n a s) :
    ValidProg w F s (boundedWhile guard body d n a) := by
  induction n generalizing a s with
  | zero => exact validProg_pure a
  | succ n ih =>
    unfold boundedWhile
    unfold whileSafe at hsafe
    split_ifs at hsafe ⊢ with hg
    · exact validProg_bind (hbody a s hsafe.1) (ih _ _ hsafe.2)
    · exact validProg_pure a

/-- Standard dictionary frontier `base + totalSpace U V w n_max h_space`. -/
abbrev dictFrontier (U V w n_max h_space base : ℕ) : ℕ :=
  base + totalSpace U V w n_max h_space

theorem validProg_readQuot {U V w n_max h_space base idx : ℕ} {s : Memory.State}
    (hw : 0 < w) (hidx : idx < n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readQuotProg U w n_max h_space (base, idx)) := by
  intro ⟨_, hf⟩
  exact validHistory_readPackedProg hw hidx
    (by dsimp only [dictFrontier, totalSpace, offGM, offLM, offVal, offQuot] at hf ⊢; omega)

theorem validProg_writeQuot {U V w n_max h_space base idx val : ℕ} {s : Memory.State}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hidx : idx < n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (writeQuotProg U w n_max h_space ((base, idx), val)) := by
  intro ⟨hwf, hf⟩
  exact validHistory_writePackedProg hw (quotientBits_le_of_le_pow hU) hidx hwf
    (by dsimp only [dictFrontier, totalSpace, offGM, offLM, offVal, offQuot] at hf ⊢; omega)

theorem validProg_readVal {U V w n_max h_space base idx : ℕ} {s : Memory.State}
    (hw : 0 < w) (hidx : idx < n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readValProg U V w n_max h_space (base, idx)) := by
  intro ⟨_, hf⟩
  exact validHistory_readPackedProg hw hidx
    (by dsimp only [dictFrontier, totalSpace, offGM, offLM, offVal] at hf ⊢; omega)

theorem validProg_writeVal {U V w n_max h_space base idx val : ℕ} {s : Memory.State}
    (hw : 0 < w) (hV : V ≤ 2 ^ w) (hidx : idx < n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (writeValProg U V w n_max h_space ((base, idx), val)) := by
  intro ⟨hwf, hf⟩
  exact validHistory_writePackedProg hw (Nat.clog_le_of_le_pow hV) hidx hwf
    (by dsimp only [dictFrontier, totalSpace, offGM, offLM, offVal] at hf ⊢; omega)

theorem validProg_readLM {U V w n_max h_space c base idx : ℕ} {s : Memory.State}
    (hw : 0 < w) (hc : c < 9) (hidx : idx < totalMicroBuckets n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readLMProg U V w n_max h_space c (base, idx)) := by
  intro ⟨_, hf⟩
  have hsub : (c + 1) * lmSubWords n_max w ≤ 9 * lmSubWords n_max w :=
    Nat.mul_le_mul_right _ hc
  rw [Nat.add_one_mul] at hsub
  exact validHistory_readPackedProg hw hidx
    (by
      unfold lmSubWords at hsub
      dsimp only [dictFrontier, totalSpace, offGM, offLMSub, offLM, lmSubWords] at hf ⊢
      omega)

theorem validProg_writeLM {U V w n_max h_space c base idx val : ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hc : c < 9)
    (hidx : idx < totalMicroBuckets n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (writeLMProg U V w n_max h_space c ((base, idx), val)) := by
  intro ⟨hwf, hf⟩
  have hsub : (c + 1) * lmSubWords n_max w ≤ 9 * lmSubWords n_max w :=
    Nat.mul_le_mul_right _ hc
  rw [Nat.add_one_mul] at hsub
  exact validHistory_writePackedProg hw (effBucketPosBits_le_of_lt_pow hnU hU) hidx hwf
    (by
      unfold lmSubWords at hsub
      dsimp only [dictFrontier, totalSpace, offGM, offLMSub, offLM, lmSubWords] at hf ⊢
      omega)

theorem validProg_readGM {U V w n_max h_space base idx : ℕ} {s : Memory.State}
    (hw : 0 < w) (hidx : idx < globalMetaLen n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readGMProg U V w n_max h_space (base, idx)) := by
  intro ⟨_, hf⟩
  exact validHistory_readPackedProg hw hidx
    (by dsimp only [dictFrontier, totalSpace] at hf ⊢; omega)

theorem validProg_bind_readGM_eq {α : Type} {U V w n_max h_space base idx v : ℕ} {s : Memory.State}
    {k : ℕ → Memory.Prog α}
    (hw : 0 < w) (hidx : idx < globalMetaLen n_max)
    (hval : gmAt base U V w n_max h_space s.mem idx = v)
    (hk : ValidProg w (dictFrontier U V w n_max h_space base) s (k v)) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readGMProg U V w n_max h_space (base, idx) >>= k) := by
  refine validProg_bind (validProg_readGM hw hidx) ?_
  rwa [clientState_readGMProg, clientResult_readGMProg s hidx, hval]

theorem validProg_writeGM {U V w n_max h_space base idx val : ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hidx : idx < globalMetaLen n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (writeGMProg U V w n_max h_space ((base, idx), val)) := by
  intro ⟨hwf, hf⟩
  exact validHistory_writePackedProg hw (globalPtrBits_le_of_lt_pow hnU hU) hidx hwf
    (by dsimp only [dictFrontier, totalSpace] at hf ⊢; omega)

/-! ## Section 2: Slot resolution, tail pool, and slab pool operations -/

theorem validProg_readBucketCount {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w) (hb : d.2 < numBuckets n_max) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (readBucketCountProg U V w n_max h_space d) := by
  unfold readBucketCountProg
  split_ifs with hb0
  · exact validProg_readGM hw (by unfold globalMetaLen; omega)
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    exact validProg_bind (validProg_readGM hw (gmQIdx_lt hb_pos hb))
      (validProg_bind (validProg_readGM hw (gmRIdx_lt hb_pos hb)) (validProg_pure _))

theorem validProg_resolveIndexedSlot {U V w n_max h_space : ℕ} {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hw : 0 < w)
    (hinv : SlotStoreInv n_max (gmAt d.1.1 U V w n_max h_space s.mem))
    (hb : d.1.2 < numBuckets n_max)
    (hj_bc : d.2 < bCount n_max (gmAt d.1.1 U V w n_max h_space s.mem) d.1.2)
    (hj_cap : d.2 < effBucketCap n_max) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1) s
      (resolveIndexedSlotProg U V w n_max h_space d) := by
  unfold resolveIndexedSlotProg
  split_ifs with hb0
  · exact validProg_pure _
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    have hq_lt : 4 + 3 * d.1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos hb
    refine validProg_bind (validProg_readGM hw hq_lt) ?_
    rw [clientState_readGMProg, clientResult_readGMProg s hq_lt]
    refine validProg_ite (fun _ => ?_) (fun hns => ?_)
    · have hcap := effBucketCap_eq_dirSlabs_mul_slabSize hb_pos
      have hs_dir : d.2 / slabSize n_max < dirSlabsPerBucket n_max :=
        Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hcap]; exact hj_cap)
      exact validProg_bind (validProg_readGM hw (gmSlabDirIdx_lt hb_pos hb hs_dir))
        (validProg_pure _)
    · obtain ⟨-, hr_cap⟩ := hinv.tailOffset_lt hb_pos hb hj_bc hns
      exact validProg_bind (validProg_readGM hw (gmTailPtrIdx_lt hb_pos hb hr_cap))
        (validProg_pure _)

theorem validProg_appendTailItem {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hb_pos : 0 < bucketBits n_max)
    (htail : TailBijection n_max (gmAt d.1 U V w n_max h_space s.mem)
      (fun b => gmAt d.1 U V w n_max h_space s.mem (gmRIdx b))
      (gmAt d.1 U V w n_max h_space s.mem 1))
    (hb : d.2 < numBuckets n_max)
    (hr_lt : gmAt d.1 U V w n_max h_space s.mem (gmRIdx d.2) < tailCapPerBucket n_max) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (appendTailItemProg U V w n_max h_space d) := by
  obtain ⟨hr_idx, h1_idx, hptr_lt, hown_lt, -, -⟩ :=
    appendTailItem_bounds (V := V) (h_space := h_space) ⟨htail, hb, hr_lt, hb_pos⟩
  unfold appendTailItemProg
  refine validProg_bind (validProg_readGM hw hr_idx) ?_
  refine validProg_bind (validProg_readGM hw h1_idx) ?_
  exact validProg_bind (validProg_writeGM hw hnU hU hptr_lt)
    (validProg_bind (validProg_writeGM hw hnU hU hown_lt)
      (validProg_bind (validProg_writeGM hw hnU hU hr_idx)
        (validProg_bind (validProg_writeGM hw hnU hU h1_idx) (validProg_pure _))))

theorem validProg_removeLastTailItem {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits n_max)
    (htail : TailBijection n_max (gmAt d.1 U V w n_max h_space s.mem)
      (fun b => gmAt d.1 U V w n_max h_space s.mem (gmRIdx b))
      (gmAt d.1 U V w n_max h_space s.mem 1))
    (hb : d.2 < numBuckets n_max)
    (hr_pos : 1 ≤ gmAt d.1 U V w n_max h_space s.mem (gmRIdx d.2)) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (removeLastTailItemProg U V w n_max h_space d) := by
  obtain ⟨hr_idx_lt, -, hptr_del_lt, h1_lt, -, hown_last_lt, -, -, hg_last_lt, hg_del_lt,
      hptr_last_lt, hown_del_lt⟩ :=
    removeLastTailItem_bounds (V := V) (h_space := h_space) ⟨htail, hb, hr_pos, hb_pos⟩
  unfold removeLastTailItemProg
  refine validProg_bind (validProg_readGM hw hr_idx_lt) ?_
  refine validProg_bind (validProg_readGM hw hptr_del_lt) ?_
  refine validProg_bind (validProg_readGM hw h1_lt) ?_
  refine validProg_bind (validProg_readGM hw hown_last_lt) ?_
  refine validProg_bind (validProg_readQuot hw hg_last_lt) ?_
  refine validProg_bind (validProg_writeQuot hw hU.le hg_del_lt) ?_
  refine validProg_bind (validProg_readVal hw hg_last_lt) ?_
  refine validProg_bind (validProg_writeVal hw hV hg_del_lt) ?_
  refine validProg_bind (validProg_writeGM hw hnU hU hptr_last_lt) ?_
  refine validProg_bind (validProg_writeGM hw hnU hU hown_del_lt) ?_
  refine validProg_bind (validProg_writeGM hw hnU hU hr_idx_lt) ?_
  exact validProg_writeGM hw hnU hU h1_lt

theorem validProg_gmPushSlab {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hb_pos : 0 < bucketBits n_max)
    (hslab : SlabBijection n_max (gmAt d.1 U V w n_max h_space s.mem)
      (fun b' => gmAt d.1 U V w n_max h_space s.mem (gmQIdx b'))
      (gmAt d.1 U V w n_max h_space s.mem 0))
    (hb : d.2 < numBuckets n_max)
    (hp_lt : gmAt d.1 U V w n_max h_space s.mem 0 < maxFullSlabs n_max) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (gmPushSlabProg U V w n_max h_space d) := by
  obtain ⟨hq_idx_lt, h0_lt, htop_idx_lt, hownB_lt, hownS_lt, hbel_lt, habv_lt, hdir_lt, -, -⟩ :=
    gmPushSlab_bounds (V := V) (h_space := h_space) ⟨hslab, hb, hp_lt, hb_pos⟩
  unfold gmPushSlabProg
  refine validProg_bind (validProg_readGM hw hq_idx_lt) ?_
  refine validProg_bind (validProg_readGM hw h0_lt) ?_
  refine validProg_bind (validProg_readGM hw htop_idx_lt) ?_
  refine validProg_seq (validProg_writeGM hw hnU hU hownB_lt) (fun _ => ?_)
  refine validProg_seq (validProg_writeGM hw hnU hU hownS_lt) (fun _ => ?_)
  refine validProg_seq (validProg_writeGM hw hnU hU hbel_lt) (fun _ => ?_)
  refine validProg_seq ?_ (fun _ => ?_)
  · exact validProg_ite (fun hc => validProg_writeGM hw hnU hU (habv_lt hc))
      (fun _ => validProg_pure ())
  refine validProg_seq ?_ (fun _ => ?_)
  · exact validProg_ite (fun hc => validProg_writeGM hw hnU hU (hdir_lt hc))
      (fun _ => validProg_pure ())
  refine validProg_seq (validProg_writeGM hw hnU hU htop_idx_lt) (fun _ => ?_)
  refine validProg_seq (validProg_writeGM hw hnU hU hq_idx_lt) (fun _ => ?_)
  exact validProg_writeGM hw hnU hU h0_lt

theorem validProg_gmUnlinkTopSlab {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hb_pos : 0 < bucketBits n_max)
    (hslab : SlabBijection n_max (gmAt d.1 U V w n_max h_space s.mem)
      (fun b' => gmAt d.1 U V w n_max h_space s.mem (gmQIdx b'))
      (gmAt d.1 U V w n_max h_space s.mem 0))
    (hb : d.2 < numBuckets n_max)
    (hq_pos : 1 ≤ gmAt d.1 U V w n_max h_space s.mem (gmQIdx d.2)) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (gmUnlinkTopSlabProg U V w n_max h_space d) := by
  obtain ⟨hq_idx_lt, htop_idx_lt, hbel_idx_lt, -⟩ :=
    gmUnlinkTopSlab_bounds (V := V) (h_space := h_space) ⟨hslab, hb, hq_pos, hb_pos⟩
  unfold gmUnlinkTopSlabProg
  refine validProg_bind (validProg_readGM hw hq_idx_lt) ?_
  refine validProg_bind (validProg_readGM hw htop_idx_lt) ?_
  refine validProg_bind (validProg_readGM hw hbel_idx_lt) ?_
  refine validProg_bind (validProg_writeGM hw hnU hU htop_idx_lt) ?_
  refine validProg_bind (validProg_writeGM hw hnU hU hq_idx_lt) ?_
  exact validProg_pure _

theorem validProg_gmRelinkMovedSlab {U V w n_max h_space : ℕ} {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hb_pos : 0 < bucketBits n_max)
    (hpre : GmMovedSlabInv U V w n_max h_space d.1.1 d.1.2 d.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1) s
      (gmRelinkMovedSlabProg U V w n_max h_space d) := by
  obtain ⟨hownB_last_lt, hownS_last_lt, hq_last_lt, hdir_lt, -, htop_lt⟩ :=
    gmRelinkMovedSlab_bounds hb_pos hpre
  unfold gmRelinkMovedSlabProg
  dsimp only
  refine validProg_bind (validProg_readGM hw hownB_last_lt) ?_
  refine validProg_bind (validProg_readGM hw hownS_last_lt) ?_
  refine validProg_bind (validProg_readGM hw hq_last_lt) ?_
  refine validProg_bind
    (validProg_ite (fun hc => validProg_writeGM hw hnU hU (hdir_lt hc))
      (fun _ => validProg_pure ())) ?_
  exact validProg_ite (fun hc => validProg_writeGM hw hnU hU (htop_lt hc))
    (fun _ => validProg_pure ())

theorem validProg_gmLinkMovedNeighbors {U V w n_max h_space : ℕ} {d : (ℕ × ℕ) × ℕ}
    {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hb_pos : 0 < bucketBits n_max)
    (hpre : GmMovedSlabInv U V w n_max h_space d.1.1 d.1.2 d.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1) s
      (gmLinkMovedNeighborsProg U V w n_max h_space d) := by
  obtain ⟨hownB_last_lt, hownS_last_lt, hbel_last_lt, habv_last_lt, hq_last_lt, habv_bel_lt, -,
      hbel_abv_lt, hownB_del_lt, hownS_del_lt, hbel_del_lt, habv_del_lt⟩ :=
    gmLinkMovedNeighbors_bounds hb_pos hpre
  unfold gmLinkMovedNeighborsProg
  refine validProg_bind (validProg_readGM hw hownB_last_lt) ?_
  refine validProg_bind (validProg_readGM hw hownS_last_lt) ?_
  refine validProg_bind (validProg_readGM hw hbel_last_lt) ?_
  refine validProg_bind (validProg_readGM hw habv_last_lt) ?_
  refine validProg_bind (validProg_readGM hw hq_last_lt) ?_
  refine validProg_bind ?_ ?_
  · exact validProg_ite (fun hc => validProg_writeGM hw hnU hU (habv_bel_lt hc))
      (fun _ => validProg_pure ())
  refine validProg_bind ?_ ?_
  · exact validProg_ite (fun hc => validProg_writeGM hw hnU hU (hbel_abv_lt hc))
      (fun _ => validProg_pure ())
  refine validProg_bind (validProg_writeGM hw hnU hU hownB_del_lt) ?_
  refine validProg_bind (validProg_writeGM hw hnU hU hownS_del_lt) ?_
  refine validProg_bind (validProg_writeGM hw hnU hU hbel_del_lt) ?_
  exact validProg_writeGM hw hnU hU habv_del_lt

theorem validProg_gmCompactSlab {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hb_pos : 0 < bucketBits n_max)
    (hpre : GmCompactSlabInv U V w n_max h_space d.1 d.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (gmCompactSlabProg U V w n_max h_space d) := by
  have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
  unfold gmCompactSlabProg
  refine validProg_bind (validProg_readGM hw h0_lt) ?_
  rw [clientState_readGMProg, clientResult_readGMProg s h0_lt]
  refine validProg_ite (fun hc => ?_) (fun _ => validProg_writeGM hw hnU hU h0_lt)
  have hm1 := hpre.2.2.2 hc
  have hm2 := gmMovedSlabInv_after_relink hw hb_pos hm1
  refine validProg_bind
    (validProg_gmRelinkMovedSlab (d := (d, gmAt d.1 U V w n_max h_space s.mem 0 - 1))
      hw hnU hU hb_pos hm1) ?_
  refine validProg_bind
    (validProg_gmLinkMovedNeighbors (d := (d, gmAt d.1 U V w n_max h_space s.mem 0 - 1))
      hw hnU hU hb_pos hm2) ?_
  exact validProg_writeGM hw hnU hU h0_lt

theorem validProg_gmPopSlab {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hb_pos : 0 < bucketBits n_max)
    (hslab : SlabBijection n_max (gmAt d.1 U V w n_max h_space s.mem)
      (fun b' => gmAt d.1 U V w n_max h_space s.mem (gmQIdx b'))
      (gmAt d.1 U V w n_max h_space s.mem 0))
    (hb : d.2 < numBuckets n_max)
    (hq_pos : 1 ≤ gmAt d.1 U V w n_max h_space s.mem (gmQIdx d.2)) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (gmPopSlabProg U V w n_max h_space d) := by
  unfold gmPopSlabProg
  refine validProg_bind (validProg_gmUnlinkTopSlab hw hnU hU hb_pos hslab hb hq_pos) ?_
  exact validProg_gmCompactSlab
    (d := (d.1,
      (Memory.spec 0).clientResult s (gmUnlinkTopSlabProg U V w n_max h_space (d.1, d.2))))
    hw hnU hU hb_pos (gmCompactSlabInv_of_slabBijection hw hb_pos hb s hslab hq_pos)

/-! ## Section 3: Slab promotion, demotion, and amortized slot operations -/

theorem validProg_promoteStep {U V w n_max h_space : ℕ} {x : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits n_max)
    (hpre : PromoteStepInv U V w n_max h_space x.1.1 x.1.2 x.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space x.1.1) s
      (promoteStepProg U V w n_max h_space x) := by
  obtain ⟨-, -, hptr_u_lt, hptr_top_lt, h0_lt, -, -, hgu_lt, hgtop_lt, hgslab_lt, htail2,
      hr2_pos, -⟩ := promoteStep_bounds hw ⟨hpre, hb_pos⟩
  unfold promoteStepProg
  dsimp only
  refine validProg_bind (validProg_readGM hw hptr_u_lt) ?_
  refine validProg_bind (validProg_readGM hw hptr_top_lt) ?_
  refine validProg_bind (validProg_readGM hw h0_lt) ?_
  refine validProg_bind (validProg_readQuot hw hgu_lt) ?_
  refine validProg_bind (validProg_readVal hw hgu_lt) ?_
  refine validProg_bind (validProg_readQuot hw hgtop_lt) ?_
  refine validProg_bind (validProg_readVal hw hgtop_lt) ?_
  refine validProg_bind (validProg_writeQuot hw hU.le hgu_lt) ?_
  refine validProg_bind (validProg_writeVal hw hV hgu_lt) ?_
  refine validProg_bind (validProg_removeLastTailItem (d := (x.1.1, x.1.2))
    hw hnU hU hV hb_pos htail2 hpre.1 hr2_pos) ?_
  refine validProg_bind (validProg_writeQuot hw hU.le hgslab_lt) ?_
  refine validProg_bind (validProg_writeVal hw hV hgslab_lt) ?_
  exact validProg_pure _

theorem validProg_promoteLoop {U V w n_max h_space : ℕ} {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits n_max)
    (hsafe : iterationSafe (promoteStepProg U V w n_max h_space)
      (fun w' x s' => PromoteStepPre U V w n_max h_space w' x.1.1 x.1.2 x.2 s')
      w d.1.1 d.2 d.1.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1.1) s
      (promoteLoopProg U V w n_max h_space d) := by
  unfold promoteLoopProg
  exact validProg_iterate d.2 d.1.2 s
    (fun a' s' h => validProg_promoteStep (x := (d.1.1, a')) hw hnU hU hV hb_pos h.2.1) hsafe

/-- The parameter bounds recorded by `DictEnvGen` for concrete parameters `mkDictParams`. -/
private theorem dictEnvGen_mk_bounds {w' U V w n_max h_space base : ℕ}
    (h : DictEnvGen w' (mkDictParams U V w n_max h_space) base) :
    0 < w ∧ n_max ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w := by
  obtain ⟨U', V', w₀, n', _, hw, hnU, hU, hV, heq⟩ := h.params
  have hU' : U = U' := by simpa using congrArg dpU heq
  have hV' : V = V' := by simpa using congrArg dpV heq
  have hw' : w = w₀ := by simpa using congrArg dpW heq
  have hn' : n_max = n' := by simpa using congrArg dpNMax heq
  subst hU' hV' hw' hn'
  exact ⟨hw, hnU, hU, hV⟩

theorem validProg_promoteSlab {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hb_pos : 0 < bucketBits n_max)
    (hdenv : DictEnvGen w (mkDictParams U V w n_max h_space) d.1)
    (hpre : PromoteSlabInv U V w n_max h_space d.1 d.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (promoteSlabProg U V w n_max h_space d) := by
  obtain ⟨hw, hnU, hU, hV⟩ := dictEnvGen_mk_bounds hdenv
  obtain ⟨hloopK, _, hsafe⟩ :=
    iterate_promoteStepProg_spec (w := w) hw hb_pos (slabSize n_max) 0 s
      (by omega) (promoteLoopInv_zero hpre)
  rw [Nat.zero_add] at hloopK
  let s₁ := (Memory.spec 0).clientState s
    (promoteLoopProg U V w n_max h_space ((d, 0), slabSize n_max))
  have htot1 : (gmAt d.1 U V w n_max h_space s₁.mem 0 + 1) * slabSize n_max ≤ n_max := by
    have := hloopK.tot_le
    dsimp only [s₁, promoteLoopProg] at this ⊢
    rw [Prod.mk.eta] at this
    rw [Nat.add_one_mul]; omega
  have hp_lt1 : gmAt d.1 U V w n_max h_space s₁.mem 0 < maxFullSlabs n_max :=
    nslabs_lt_maxFullSlabs_of_mul_le hb_pos htot1
  unfold promoteSlabProg
  refine validProg_bind
    (validProg_promoteLoop (d := ((d, 0), slabSize n_max)) hw hnU hU hV hb_pos (hsafe hdenv)) ?_
  exact validProg_gmPushSlab (d := d) hw hnU hU hb_pos hloopK.slab_bij hloopK.b_lt hp_lt1

theorem validProg_demoteStep {U V w n_max h_space : ℕ} {x : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits n_max)
    (hpre : DemoteStepInv U V w n_max h_space x.1.1 x.1.2 x.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space x.1.1) s
      (demoteStepProg U V w n_max h_space x) := by
  obtain ⟨-, htop_idx_lt, h0_idx_lt, -, hg_del_lt, hg_last_lt, ⟨htail, hb, hr_cap, -⟩, -,
      hg_tail_lt, -⟩ := demoteStep_bounds hw ⟨hpre, hb_pos⟩
  unfold demoteStepProg
  dsimp only
  refine validProg_bind (validProg_readGM hw htop_idx_lt) ?_
  refine validProg_bind (validProg_readGM hw h0_idx_lt) ?_
  refine validProg_bind (validProg_readQuot hw hg_del_lt) ?_
  refine validProg_bind (validProg_readVal hw hg_del_lt) ?_
  refine validProg_bind (validProg_readQuot hw hg_last_lt) ?_
  refine validProg_bind (validProg_readVal hw hg_last_lt) ?_
  refine validProg_bind
    (validProg_appendTailItem (d := (x.1.1, x.1.2)) hw hnU hU hb_pos htail hb hr_cap) ?_
  refine validProg_bind (validProg_writeQuot hw hU.le hg_del_lt) ?_
  refine validProg_bind (validProg_writeVal hw hV hg_del_lt) ?_
  refine validProg_bind (validProg_writeQuot hw hU.le hg_tail_lt) ?_
  refine validProg_bind (validProg_writeVal hw hV hg_tail_lt) ?_
  exact validProg_pure _

theorem validProg_demoteLoop {U V w n_max h_space : ℕ} {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits n_max)
    (hsafe : iterationSafe (demoteStepProg U V w n_max h_space)
      (fun w' x s' => DemoteStepPre U V w n_max h_space w' x.1.1 x.1.2 x.2 s')
      w d.1.1 d.2 d.1.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1.1) s
      (demoteLoopProg U V w n_max h_space d) := by
  unfold demoteLoopProg
  exact validProg_iterate d.2 d.1.2 s
    (fun a' s' h => validProg_demoteStep (x := (d.1.1, a')) hw hnU hU hV hb_pos h.2.1) hsafe

theorem validProg_demoteSlab {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits n_max)
    (hdenv : DictEnvGen w (mkDictParams U V w n_max h_space) d.1)
    (hpre : DemoteSlabInv U V w n_max h_space d.1 d.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (demoteSlabProg U V w n_max h_space d) := by
  obtain ⟨hloopK, _, hsafe⟩ :=
    iterate_demoteStepProg_spec (w := w) hw hb_pos (slabSize n_max) 0 s
      (by omega) (demoteLoopInv_zero hpre)
  rw [Nat.zero_add] at hloopK
  unfold demoteSlabProg
  refine validProg_bind
    (validProg_demoteLoop (d := ((d, 0), slabSize n_max)) hw hnU hU hV hb_pos (hsafe hdenv)) ?_
  exact validProg_gmPopSlab (d := d) hw hnU hU hb_pos hloopK.slab_bij hloopK.b_lt hloopK.qb_pos

theorem validProg_lastSlotOf {U V w n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w)
    (hinv : SlotStoreInv n_max (gmAt d.1 U V w n_max h_space s.mem))
    (hb : d.2 < numBuckets n_max)
    (hbc : 1 ≤ bCount n_max (gmAt d.1 U V w n_max h_space s.mem) d.2) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (lastSlotOfProg U V w n_max h_space d) := by
  unfold lastSlotOfProg
  split_ifs with hb0
  · exact validProg_bind (validProg_readGM hw (by unfold globalMetaLen; omega)) (validProg_pure _)
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    have hr_idx_lt : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
    have hr_pos : 1 ≤ gmAt d.1 U V w n_max h_space s.mem (gmRIdx d.2) :=
      pos_gmRIdx_of_pos_bCount hb_pos hinv hb hbc
    have hr_cap : gmAt d.1 U V w n_max h_space s.mem (4 + 3 * d.2 + 1) - 1 <
        tailCapPerBucket n_max := by
      have := (hinv.multi_r_bounds hb_pos d.2 hb).1
      unfold gmRIdx at this hr_pos
      omega
    have hptr_lt := gmTailPtrIdx_lt hb_pos hb hr_cap
    refine validProg_bind (validProg_readGM hw hr_idx_lt) ?_
    rw [clientState_readGMProg, clientResult_readGMProg s hr_idx_lt]
    exact validProg_bind (validProg_readGM hw hptr_lt) (validProg_pure _)

theorem validProg_pushBackTailWrite {U V w n_max h_space : ℕ}
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits n_max)
    (hinv : SlotStoreInv n_max (gmAt d.1.1.1 U V w n_max h_space s.mem))
    (hb : d.1.1.2 < numBuckets n_max)
    (htot : totalSlots n_max (gmAt d.1.1.1 U V w n_max h_space s.mem) < n_max) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1.1) s
      (pushBackTailWriteProg U V w n_max h_space d) := by
  let base := d.1.1.1
  let b := d.1.1.2
  let gm₀ := gmAt base U V w n_max h_space s.mem
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have htot' : gm₀ 0 * slabSize n_max + gm₀ 1 < n_max := by
    change totalSlots n_max gm₀ < n_max at htot
    unfold totalSlots at htot; rw [ite_eq_right hb0] at htot; exact htot
  have htail₀ := hinv.multi_tail hb_pos
  have hr_lt := (hinv.multi_r_bounds hb_pos b hb).1
  obtain ⟨hres_app, _⟩ :=
    appendTailItemProg_effect (U := U) (V := V) (h_space := h_space)
      hw hb_pos hb s htail₀ hr_lt
  have hg_new_lt : (n_max - 1) - gm₀ 1 < n_max := by omega
  have hr_idx_lt : 4 + 3 * b + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
  dsimp only [base, b, gm₀] at hb htail₀ hr_lt hres_app hg_new_lt hr_idx_lt
  unfold pushBackTailWriteProg
  dsimp only
  refine validProg_bind
    (validProg_appendTailItem (d := d.1.1) hw hnU hU hb_pos htail₀ hb hr_lt) ?_
  rw [hres_app]
  refine validProg_bind (validProg_writeQuot hw hU.le hg_new_lt) ?_
  refine validProg_bind (validProg_writeVal hw hV hg_new_lt) ?_
  exact validProg_readGM hw hr_idx_lt

theorem validProg_pushBackSlot {U V w n_max h_space : ℕ}
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hpre : PushBackSlotPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1.1) s
      (pushBackSlotProg U V w n_max h_space d) := by
  rcases hpre with ⟨hdenv, hinv, hb, htot, hq_lt, hv_lt⟩
  let base := d.1.1.1
  let b := d.1.1.2
  let gm₀ := gmAt base U V w n_max h_space s.mem
  unfold pushBackSlotProg
  split_ifs with hb0
  · have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
    have hc_lt : gm₀ 0 < n_max := by
      change totalSlots n_max gm₀ < n_max at htot
      unfold totalSlots at htot; rw [ite_eq_left hb0] at htot; exact htot
    dsimp only [base, gm₀] at hc_lt
    refine validProg_bind (validProg_readGM hw h0_lt) ?_
    rw [clientState_readGMProg, clientResult_readGMProg s h0_lt]
    refine validProg_bind (validProg_writeQuot hw hU.le hc_lt) ?_
    refine validProg_bind (validProg_writeVal hw hV hc_lt) ?_
    exact validProg_writeGM hw hnU hU h0_lt
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    have htot0_lt : gm₀ 0 * slabSize n_max + gm₀ 1 < n_max := by
      change totalSlots n_max gm₀ < n_max at htot
      unfold totalSlots at htot; rw [ite_eq_right hb0] at htot; exact htot
    rcases d with ⟨⟨⟨base', b'⟩, q_val⟩, v_val⟩
    dsimp only [base, b, gm₀] at hdenv hinv hb htot htot0_lt hq_lt hv_lt ⊢
    obtain ⟨hres1, _, _, _, _, htail1, hslab1, htot1, _, hrb1, hother1, _⟩ :=
      pushBackTailWriteProg_effect (U := U) (V := V) (h_space := h_space)
        hw hb_pos s hinv hb htot hq_lt hv_lt
    refine validProg_bind
      (validProg_pushBackTailWrite (d := (((base', b'), q_val), v_val))
        hw hnU hU hV hb_pos hinv hb htot) ?_
    refine validProg_ite (fun hc => ?_) (fun _ => validProg_pure ())
    rw [hres1] at hc
    have hpre_prom : PromoteSlabInv U V w n_max h_space base' b'
        ((Memory.spec 0).clientState s
          (pushBackTailWriteProg U V w n_max h_space (((base', b'), q_val), v_val))) := by
      refine ⟨hb, htail1, hslab1, by rw [hrb1, hc], fun b'' hb'' hne => ?_, by omega⟩
      rw [(hother1 b'' hb'' hne).1, (hother1 b'' hb'' hne).2]
      exact hinv.multi_r_bounds hb_pos b'' hb''
    exact validProg_promoteSlab (d := (base', b')) hb_pos hdenv hpre_prom

theorem validProg_popBackSlot {U V w n_max h_space : ℕ}
    {d : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hpre : PopBackSlotPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (popBackSlotProg U V w n_max h_space d) := by
  rcases hpre with ⟨hdenv, hinv, hb, hbc⟩
  let base := d.1
  let b := d.2
  let gm₀ := gmAt base U V w n_max h_space s.mem
  unfold popBackSlotProg
  split_ifs with hb0
  · have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
    exact validProg_bind (validProg_readGM hw h0_lt)
      (validProg_writeGM hw hnU hU h0_lt)
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    have hr0_pos : 1 ≤ gm₀ (gmRIdx b) := pos_gmRIdx_of_pos_bCount hb_pos hinv hb hbc
    have htail₀ := hinv.multi_tail hb_pos
    have hslab₀ := hinv.multi_slab hb_pos
    have htot₀ := hinv.multi_total_le hb_pos
    rcases d with ⟨base', b'⟩
    dsimp only [base, b, gm₀] at hdenv hinv hb hbc hr0_pos htail₀ hslab₀ htot₀ ⊢
    obtain ⟨_, _, _, _, _, hgm1_eq⟩ :=
      removeLastTailItemProg_effect (U := U) (V := V) (h_space := h_space)
        hw hb_pos hb s htail₀ hr0_pos
    let s₁ := (Memory.spec 0).clientState s (removeLastTailItemProg U V w n_max h_space (base', b'))
    let gm₁ := gmAt base' U V w n_max h_space s₁.mem
    change gm₁ = gmRemoveTail n_max (gmAt base' U V w n_max h_space s.mem) b' at hgm1_eq
    have hpres1 := gmRemoveTail_preserves_nonTail hb hr0_pos htail₀
    have htail1 : TailBijection n_max gm₁ (fun b'' => gm₁ (gmRIdx b'')) (gm₁ 1) := by
      rw [hgm1_eq]; exact tailBijection_gmRemoveTail hb hr0_pos htail₀
    have hslab1 : SlabBijection n_max gm₁ (fun b'' => gm₁ (gmQIdx b'')) (gm₁ 0) := by
      rw [hgm1_eq]; exact (slabBijection_gmRemoveTail hb hr0_pos htail₀ hslab₀).2
    have hgm1_pos : 1 ≤ gmAt base' U V w n_max h_space s.mem 1 := by
      have := r_le_ntails_of_tailBijection htail₀ hb; omega
    have htot1 : gm₁ 0 * slabSize n_max + gm₁ 1 ≤ n_max := by
      rw [hgm1_eq, hpres1.1, hpres1.2.1]; omega
    have hqb1 : gm₁ (gmQIdx b') = gmAt base' U V w n_max h_space s.mem (gmQIdx b') := by
      rw [hgm1_eq, hpres1.2.2.2.2.1 b' hb]
    have hrb1 : gm₁ (gmRIdx b') = gmAt base' U V w n_max h_space s.mem (gmRIdx b') - 1 := by
      rw [hgm1_eq, hpres1.2.2.1]
    have hother1 : ∀ b'' < numBuckets n_max, b'' ≠ b' →
        gm₁ (gmQIdx b'') = gmAt base' U V w n_max h_space s.mem (gmQIdx b'') ∧
        gm₁ (gmRIdx b'') = gmAt base' U V w n_max h_space s.mem (gmRIdx b'') := by
      intro b'' hb'' hne
      exact ⟨by rw [hgm1_eq, hpres1.2.2.2.2.1 b'' hb''],
        by rw [hgm1_eq, hpres1.2.2.2.1 b'' hb'' hne]⟩
    have hr_idx_lt : 4 + 3 * b' + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
    have hq_idx_lt : 4 + 3 * b' < globalMetaLen n_max := gmQIdx_lt hb_pos hb
    refine validProg_bind
      (validProg_removeLastTailItem (d := (base', b')) hw hnU hU hV hb_pos htail₀ hb hr0_pos) ?_
    refine validProg_bind (validProg_readGM hw hr_idx_lt) ?_
    rw [clientState_readGMProg, clientResult_readGMProg s₁ hr_idx_lt]
    refine validProg_bind (validProg_readGM hw hq_idx_lt) ?_
    rw [clientState_readGMProg, clientResult_readGMProg s₁ hq_idx_lt]
    refine validProg_ite (fun hr_zero => ?_) (fun _ => validProg_pure ())
    refine validProg_ite (fun hq_pos => ?_) (fun _ => validProg_pure ())
    have hpre_dem : DemoteSlabInv U V w n_max h_space base' b' s₁ := by
      refine ⟨hb, htail1, hslab1, hr_zero, hq_pos, fun b'' hb'' hne => ?_, htot1⟩
      change gm₁ (gmRIdx b'') < tailCapPerBucket n_max ∧
        (0 < gm₁ (gmQIdx b'') → 1 ≤ gm₁ (gmRIdx b''))
      rw [(hother1 b'' hb'' hne).1, (hother1 b'' hb'' hne).2]
      exact hinv.multi_r_bounds hb_pos b'' hb''
    exact validProg_demoteSlab (d := (base', b')) hw hnU hU hV hb_pos hdenv hpre_dem

/-! ## Section 4: Micro-Chain Accessors, Prepend/Unlink, and Search Loops -/

theorem validProg_readLMHead {U V w n_max h_space base b m : ℕ}
    (hw : 0 < w) {s : Memory.State}
    (hb : b < numBuckets n_max) (hm : m < numMicroPerBucket n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readLMHeadProg U V w n_max h_space ((base, b), m)) :=
  validProg_readLM hw (by decide) (lmHeadIdx_lt hb hm)

theorem validProg_writeLMHead {U V w n_max h_space base b m v : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) {s : Memory.State}
    (hb : b < numBuckets n_max) (hm : m < numMicroPerBucket n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (writeLMHeadProg U V w n_max h_space (((base, b), m), v)) :=
  validProg_writeLM hw hnU hU (by decide) (lmHeadIdx_lt hb hm)

theorem validProg_readLMMod4 {U V w n_max h_space c_base base b j : ℕ}
    (hw : 0 < w) (hc : c_base + 3 < 9) {s : Memory.State}
    (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readLMMod4Prog U V w n_max h_space c_base ((base, b), j)) := by
  unfold readLMMod4Prog
  simp only [pure_bind]
  split_ifs <;> exact validProg_readLM hw (by omega) (lmSlotIdx_lt hb hj)

theorem validProg_writeLMMod4 {U V w n_max h_space c_base base b j v : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hc : c_base + 3 < 9)
    {s : Memory.State}
    (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (writeLMMod4Prog U V w n_max h_space c_base (((base, b), j), v)) := by
  unfold writeLMMod4Prog
  simp only [pure_bind]
  split_ifs <;> exact validProg_writeLM hw hnU hU (by omega) (lmSlotIdx_lt hb hj)

theorem validProg_readLMPrev {U V w n_max h_space base b j : ℕ}
    (hw : 0 < w) {s : Memory.State}
    (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readLMPrevProg U V w n_max h_space ((base, b), j)) :=
  validProg_readLMMod4 hw (by decide) hb hj

theorem validProg_writeLMPrev {U V w n_max h_space base b j v : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) {s : Memory.State}
    (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (writeLMPrevProg U V w n_max h_space (((base, b), j), v)) :=
  validProg_writeLMMod4 hw hnU hU (by decide) hb hj

theorem validProg_readLMNext {U V w n_max h_space base b j : ℕ}
    (hw : 0 < w) {s : Memory.State}
    (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readLMNextProg U V w n_max h_space ((base, b), j)) :=
  validProg_readLMMod4 hw (by decide) hb hj

theorem validProg_writeLMNext {U V w n_max h_space base b j v : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) {s : Memory.State}
    (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max) :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (writeLMNextProg U V w n_max h_space (((base, b), j), v)) :=
  validProg_writeLMMod4 hw hnU hU (by decide) hb hj

theorem validProg_lmPrepend {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : LMPrependPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1.1) s
      (lmPrependProg U V w n_max h_space d) := by
  rcases hpre with ⟨_, hb, hm, hj, _, hold⟩
  unfold lmPrependProg
  simp only [pure_bind]
  refine validProg_bind (validProg_readLMHead hw hb hm) ?_
  rw [clientState_readLMHeadProg, clientResult_readLMHeadProg s hb hm]
  refine validProg_bind (validProg_writeLMPrev hw hnU hU hb hj) ?_
  refine validProg_bind (validProg_writeLMNext hw hnU hU hb hj) ?_
  refine validProg_ite (fun hpos => ?_) (fun _ => validProg_writeLMHead hw hnU hU hb hm)
  have hold_idx : lmHead n_max (lmAt d.1.1.1 U V w n_max h_space s.mem) d.1.1.2 d.1.2 - 1 <
      effBucketCap n_max := by omega
  exact validProg_bind (validProg_writeLMPrev hw hnU hU hb hold_idx)
    (validProg_writeLMHead hw hnU hU hb hm)

theorem validProg_lmUnlink {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : LMUnlinkPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1.1) s
      (lmUnlinkProg U V w n_max h_space d) := by
  rcases hpre with ⟨_, hb, hm, hj, hp, hn⟩
  unfold lmUnlinkProg
  simp only [pure_bind]
  refine validProg_bind (validProg_readLMPrev hw hb hj) ?_
  rw [clientState_readLMPrevProg, clientResult_readLMPrevProg s hb hj]
  refine validProg_bind (validProg_readLMNext hw hb hj) ?_
  rw [clientState_readLMNextProg, clientResult_readLMNextProg s hb hj]
  refine validProg_ite (fun hp_pos => ?_) (fun _ => ?_)
  · have hp_idx : lmPrev n_max (lmAt d.1.1.1 U V w n_max h_space s.mem) d.1.1.2 d.2 - 1 <
        effBucketCap n_max := by omega
    refine validProg_bind (validProg_writeLMNext hw hnU hU hb hp_idx) ?_
    refine validProg_ite (fun hn_pos => ?_) (fun _ => validProg_pure ())
    have hn_idx : lmNext n_max (lmAt d.1.1.1 U V w n_max h_space s.mem) d.1.1.2 d.2 - 1 <
        effBucketCap n_max := by omega
    exact validProg_writeLMPrev hw hnU hU hb hn_idx
  · refine validProg_bind (validProg_writeLMHead hw hnU hU hb hm) ?_
    refine validProg_ite (fun hn_pos => ?_) (fun _ => validProg_pure ())
    have hn_idx : lmNext n_max (lmAt d.1.1.1 U V w n_max h_space s.mem) d.1.1.2 d.2 - 1 <
        effBucketCap n_max := by omega
    exact validProg_writeLMPrev hw hnU hU hb hn_idx

theorem validProg_microStep {U V w n_max h_space : ℕ}
    (hw : 0 < w) {x : (((ℕ × ℕ) × ℕ) × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)} {s : Memory.State}
    (hpre : MicroStepPre U V w n_max h_space w x s) :
    ValidProg w (dictFrontier U V w n_max h_space x.1.1.1.1) s
      (microStepProg U V w n_max h_space x) := by
  rcases hpre with ⟨_, hb, _, hj_cap, hj_bc, hinv⟩
  have hphys_lt : slotOf n_max (gmAt x.1.1.1.1 U V w n_max h_space s.mem)
      x.1.1.1.2 (x.2.1.1.1 - 1) < n_max :=
    (slotOf_lt_and_injective hinv).1 x.1.1.1.2 hb (x.2.1.1.1 - 1) hj_bc
  unfold microStepProg
  simp only [pure_bind]
  refine validProg_bind (validProg_readLMNext hw hb hj_cap) ?_
  rw [clientState_readLMNextProg]
  refine validProg_bind
    (validProg_resolveIndexedSlot (d := (x.1.1.1, x.2.1.1.1 - 1)) hw hinv hb hj_bc hj_cap) ?_
  rw [clientState_resolveIndexedSlotProg,
    clientResult_resolveIndexedSlotProg (x.1.1.1, x.2.1.1.1 - 1) s hinv hb hj_bc hj_cap]
  refine validProg_bind (validProg_readQuot hw hphys_lt) ?_
  exact validProg_ite (fun _ => validProg_pure _) (fun _ => validProg_pure _)

theorem validProg_microLoop {U V w n_max h_space : ℕ}
    (hw : 0 < w) {x : (((ℕ × ℕ) × ℕ) × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)} {s : Memory.State}
    (hsafe : whileSafe microLoopGuard (microStepProg U V w n_max h_space)
      (MicroStepPre U V w n_max h_space) w x.1 (effBucketCap n_max) x.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space x.1.1.1.1) s
      (microLoopProg U V w n_max h_space x) := by
  unfold microLoopProg
  exact validProg_boundedWhile (effBucketCap n_max) x.2 s
    (fun a' s' h => validProg_microStep (x := (x.1, a')) hw h) hsafe

theorem validProg_searchMicroChain {U V w n_max h_space : ℕ}
    (hw : 0 < w) {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : SearchMicroChainPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1.1) s
      (searchMicroChainProg U V w n_max h_space d) := by
  rcases hpre with ⟨henv, hb, hm, hinv, L, hchain, hc_lt⟩
  unfold searchMicroChainProg
  simp only [pure_bind]
  refine validProg_bind (validProg_readLMHead hw hb hm) ?_
  rw [clientState_readLMHeadProg, clientResult_readLMHeadProg s hb hm]
  exact validProg_microLoop
    (x := ((d.1, 0),
      (((lmHead n_max (lmAt d.1.1.1 U V w n_max h_space s.mem) d.1.1.2 d.2, 0), 0), 0)))
    hw (searchMicroChainProg_spec henv hb hm hinv hchain hc_lt).2.2.1

theorem validProg_resolveOvfStep {U V w n_max h_space : ℕ}
    {d : (ℕ × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (hpre : ResolveOvfStepPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1) s
      (resolveOvfStepProg U V w n_max h_space d) := by
  rcases hpre with ⟨henv, hb, hj_bc, hinv, hp, hb_pos⟩
  have hw : 0 < w := (dictEnvGen_mk_bounds henv).1
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK : 0 < slabSize n_max := slabSize_pos n_max
  have hq_lt : 4 + 3 * d.1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos hb
  have hslab := hinv.multi_slab hb_pos
  unfold resolveOvfStepProg
  simp only [pure_bind]
  refine validProg_bind (validProg_readGM hw hq_lt) ?_
  rw [clientState_readGMProg, clientResult_readGMProg s hq_lt,
    show 4 + 3 * d.1.2 = gmQIdx d.1.2 from rfl]
  refine validProg_ite (fun hj_slab => ?_) (fun hj_tail => ?_)
  · refine validProg_ite (fun _ => ?_) (fun _ => validProg_pure _)
    refine validProg_ite (fun _ => ?_) (fun _ => validProg_pure _)
    have hp_eq := hp hj_slab
    have hs_lt : d.2.1 / slabSize n_max <
        gmAt d.1.1 U V w n_max h_space s.mem (gmQIdx d.1.2) :=
      (Nat.div_lt_iff_lt_mul hK).2 hj_slab
    have hp_lt_max : d.2.2 < maxFullSlabs n_max := hp_eq ▸ hslab.ptr_lt_maxFullSlabs hb hs_lt
    exact validProg_bind (validProg_readGM hw (gmSlabAboveIdx_lt hb_pos hp_lt_max))
      (validProg_pure _)
  · obtain ⟨-, hr_cap⟩ := hinv.tailOffset_lt hb_pos hb hj_bc hj_tail
    exact validProg_bind (validProg_readGM hw (gmTailPtrIdx_lt hb_pos hb hr_cap))
      (validProg_pure _)

theorem validProg_ovfStep {U V w n_max h_space : ℕ}
    (hw : 0 < w) (_hb_pos : 0 < bucketBits n_max)
    {x : ((ℕ × ℕ) × ℕ) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)} {s : Memory.State}
    (hpre : OvfStepPre U V w n_max h_space w x s) :
    ValidProg w (dictFrontier U V w n_max h_space x.1.1.1) s
      (ovfStepProg U V w n_max h_space x) := by
  rcases hpre with ⟨henv, hb, hj_bc, hinv, hp, hb_pos⟩
  unfold ovfStepProg
  simp only [pure_bind]
  refine validProg_bind
    (validProg_resolveOvfStep (d := (x.1.1, x.2.1.1.1))
      ⟨henv, hb, hj_bc, hinv, hp, hb_pos⟩) ?_
  rw [clientState_resolveOvfStepProg,
    (clientResult_resolveOvfStepProg (d := (x.1.1, x.2.1.1.1)) s hb_pos hb hj_bc hinv hp).1]
  have hphys_lt : slotOf n_max (gmAt x.1.1.1 U V w n_max h_space s.mem) x.1.1.2 x.2.1.1.1.1 <
      n_max :=
    (slotOf_lt_and_injective hinv).1 x.1.1.2 hb x.2.1.1.1.1 hj_bc
  refine validProg_bind (validProg_readQuot hw hphys_lt) ?_
  exact validProg_ite
    (fun _ => validProg_ite (fun _ => validProg_pure _) (fun _ => validProg_pure _))
    (fun _ => validProg_pure _)

theorem validProg_ovfLoop {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    {d : (((ℕ × ℕ) × ℕ) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) × ℕ} {s : Memory.State}
    (hsafe : iterationSafe (ovfStepProg U V w n_max h_space)
      (OvfStepPre U V w n_max h_space) w d.1.1 d.2 d.1.2 s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1.1.1) s
      (ovfLoopProg U V w n_max h_space d) := by
  unfold ovfLoopProg
  exact validProg_iterate d.2 d.1.2 s
    (fun a' s' h => validProg_ovfStep (x := (d.1.1, a')) hw hb_pos h) hsafe

theorem validProg_initOvfSearch {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    {d : ℕ × ℕ} {s : Memory.State}
    (hb : d.2 < numBuckets n_max)
    (hinv : SlotStoreInv n_max (gmAt d.1 U V w n_max h_space s.mem)) :
    ValidProg w (dictFrontier U V w n_max h_space d.1) s
      (initOvfSearchProg U V w n_max h_space d) := by
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hq_lt : 4 + 3 * d.2 < globalMetaLen n_max := gmQIdx_lt hb_pos hb
  have hr_lt : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
  have hbc_eq : gmAt d.1 U V w n_max h_space s.mem (4 + 3 * d.2) * slabSize n_max +
      gmAt d.1 U V w n_max h_space s.mem (4 + 3 * d.2 + 1) =
      bCount n_max (gmAt d.1 U V w n_max h_space s.mem) d.2 := by
    unfold bCount gmQIdx gmRIdx; simp [hb0, hb]
  have hbc_le : bCount n_max (gmAt d.1 U V w n_max h_space s.mem) d.2 ≤ n_max :=
    bCount_le_n_max hinv d.2
  unfold initOvfSearchProg
  simp only [pure_bind]
  refine validProg_bind (validProg_readGM hw hq_lt) ?_
  rw [clientState_readGMProg, clientResult_readGMProg s hq_lt]
  refine validProg_bind (validProg_readGM hw hr_lt) ?_
  rw [clientState_readGMProg, clientResult_readGMProg s hr_lt, hbc_eq]
  refine validProg_ite (fun hcap_c => ?_) (fun _ => validProg_pure _)
  refine validProg_ite (fun hcap_q => ?_) (fun _ => validProg_pure _)
  have hcap_eq : min n_max (effBucketCap n_max) = effBucketCap n_max := by omega
  rw [hcap_eq] at hcap_c hcap_q
  obtain ⟨hdir_idx_lt, hp_prev_eq, hp_prev_lt_max⟩ :=
    hinv.lastDirSlab_ptr hb_pos hb hcap_q.le
  refine validProg_bind (validProg_readGM hw hdir_idx_lt) ?_
  rw [clientState_readGMProg, clientResult_readGMProg s hdir_idx_lt, hp_prev_eq]
  exact validProg_bind (validProg_readGM hw (gmSlabAboveIdx_lt hb_pos hp_prev_lt_max))
    (validProg_pure _)

theorem validProg_searchOverflow {U V w n_max h_space : ℕ}
    (hw : 0 < w) {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hpre : SearchOverflowPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1) s
      (searchOverflowProg U V w n_max h_space d) := by
  rcases hpre with ⟨henv, hb, hinv⟩
  unfold searchOverflowProg
  by_cases hb0 : bucketBits n_max = 0
  · simp only [hb0, ↓reduceIte, pure_bind]
    exact validProg_pure _
  · simp only [hb0, ↓reduceIte, pure_bind]
    have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    refine validProg_bind (validProg_initOvfSearch (d := d.1) hw hb_pos hb hinv) ?_
    rw [clientState_initOvfSearchProg]
    have hsafe := (searchOverflowProg_spec henv hb hinv).2.2.1 hb_pos
    exact validProg_bind
      (validProg_ovfLoop
        (d := ((d, ((((min n_max (effBucketCap n_max),
          ((Memory.spec 0).clientResult s (initOvfSearchProg U V w n_max h_space d.1)).1), 0), 0),
          0)), ((Memory.spec 0).clientResult s (initOvfSearchProg U V w n_max h_space d.1)).2))
        hw hb_pos hsafe)
      (validProg_pure _)

theorem validProg_searchBucket {U V w n_max h_space : ℕ}
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : SearchMicroChainPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1.1) s
      (searchBucketProg U V w n_max h_space d) := by
  have hw : 0 < w := (dictEnvGen_mk_bounds hpre.1).1
  obtain ⟨L, hchain, hc_lt⟩ := hpre.2.2.2.2
  unfold searchBucketProg
  simp only [pure_bind]
  refine validProg_bind (validProg_searchMicroChain hw hpre) ?_
  rw [(searchMicroChainProg_spec hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hchain hc_lt).1]
  exact validProg_ite (fun _ => validProg_pure _)
    (fun _ => validProg_searchOverflow (d := d.1) hw ⟨hpre.1, hpre.2.1, hpre.2.2.2.1⟩)

theorem validProg_queryBody {U V w n_max h_space : ℕ}
    (hw : 0 < w) {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : SearchMicroChainPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1.1) s
      (queryBodyProg U V w n_max h_space d) := by
  obtain ⟨L, hchain, hc_lt⟩ := hpre.2.2.2.2
  unfold queryBodyProg
  simp only [pure_bind]
  refine validProg_bind (validProg_searchBucket hpre) ?_
  have hsb := searchBucketProg_spec hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hchain hc_lt
  rw [hsb.1]
  refine validProg_ite (fun hf1 => ?_) (fun _ => validProg_pure _)
  have hspec := hsb.2.2
  dsimp only at hspec
  split_ifs at hspec with hex
  · have hphys_lt : ((Memory.spec 0).clientResult s
        (searchBucketProg U V w n_max h_space d)).2 < n_max := by
      rw [hspec.2.2.2.2]
      exact (slotOf_lt_and_injective hpre.2.2.2.1).1 d.1.1.2 hpre.2.1 _ hspec.2.1
    exact validProg_bind (validProg_readVal hw hphys_lt) (validProg_pure _)
  · omega

/-! ## Section 5: Chain Prepend/Unlink, Insert, and Delete Operations -/

theorem validProg_prependIfIndexed {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : PrependIfIndexedPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1.1) s
      (prependIfIndexedProg U V w n_max h_space d) := by
  rcases hpre with ⟨hdenv, hb, hm, hold⟩
  unfold prependIfIndexedProg
  simp only [pure_bind]
  refine validProg_ite (fun hj_min => ?_) (fun _ => validProg_pure ())
  exact validProg_lmPrepend (d := d) hw hnU hU ⟨hdenv, hb, hm, by omega, by omega, hold⟩

theorem validProg_unlinkIfIndexed {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : UnlinkIfIndexedPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1.1) s
      (unlinkIfIndexedProg U V w n_max h_space d) := by
  rcases hpre with ⟨hdenv, hb, hm, hbound⟩
  unfold unlinkIfIndexedProg
  simp only [pure_bind]
  refine validProg_ite (fun hj_min => ?_) (fun _ => validProg_pure ())
  have hj_cap : d.2 < effBucketCap n_max := by omega
  rcases hbound hj_cap with ⟨hp, hn⟩
  exact validProg_lmUnlink (d := d) hw hnU hU ⟨hdenv, hb, hm, hj_cap, hp, hn⟩

theorem validProg_readTotalSlots {U V w n_max h_space : ℕ}
    (hw : 0 < w) {base : ℕ} {s : Memory.State} :
    ValidProg w (dictFrontier U V w n_max h_space base) s
      (readTotalSlotsProg U V w n_max h_space base) := by
  unfold readTotalSlotsProg
  have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
  split_ifs with hb0
  · simp only [pure_bind]
    exact validProg_readGM hw h0_lt
  · simp only [pure_bind]
    have h1_lt : 1 < globalMetaLen n_max := by unfold globalMetaLen; omega
    exact validProg_bind (validProg_readGM hw h0_lt)
      (validProg_bind (validProg_readGM hw h1_lt) (validProg_pure _))

theorem validProg_copyLastPayload {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hpre : CopyLastPayloadPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1) s
      (copyLastPayloadProg U V w n_max h_space d) := by
  rcases hpre with ⟨_, hinv, hb, hbc, hdst⟩
  unfold copyLastPayloadProg
  refine validProg_bind (validProg_lastSlotOf (d := d.1) hw hinv hb hbc) ?_
  rw [clientState_lastSlotOfProg, clientResult_lastSlotOfProg d.1 s hinv hb hbc]
  have hsrc : slotOf n_max (gmAt d.1.1 U V w n_max h_space s.mem) d.1.2
      (bCount n_max (gmAt d.1.1 U V w n_max h_space s.mem) d.1.2 - 1) < n_max :=
    (slotOf_lt_and_injective hinv).1 d.1.2 hb _ (by omega)
  refine validProg_bind (validProg_readQuot hw hsrc) ?_
  rw [clientState_readQuotProg]
  refine validProg_bind (validProg_readVal hw hsrc) ?_
  rw [clientState_readValProg]
  exact validProg_bind (validProg_writeQuot hw hU.le hdst) (validProg_writeVal hw hV hdst)

theorem validProg_insertNew {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    {d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : InsertNewPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1.1.1) s
      (insertNewProg U V w n_max h_space d) := by
  rcases hpre with ⟨hdenv, hb, hm, hq_lt, hv_lt, hinv, hold⟩
  unfold insertNewProg
  simp only [pure_bind]
  refine validProg_bind (validProg_readTotalSlots hw) ?_
  rw [clientState_readTotalSlotsProg, clientResult_readTotalSlotsProg]
  refine validProg_ite (fun htot => ?_) (fun _ => validProg_pure ())
  refine validProg_bind (validProg_readBucketCount (d := d.1.1.1) hw hb) ?_
  rw [clientState_readBucketCountProg]
  refine validProg_bind
    (validProg_pushBackSlot (d := d.1) hw hnU hU hV ⟨hdenv, hinv, hb, htot, hq_lt, hv_lt⟩) ?_
  have eff := pushBackSlotProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
    (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (q_val := d.1.1.2)
    (v_val := d.1.2) hw s hinv hb htot hq_lt hv_lt
  refine validProg_prependIfIndexed
    (d := ((d.1.1.1, d.2), (Memory.spec 0).clientResult s
      (readBucketCountProg U V w n_max h_space d.1.1.1)))
    hw hnU hU ⟨hdenv, hb, hm, ?_⟩
  rw [eff.2.2.1]
  exact hold

theorem validProg_insertBody {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    {d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : InsertBodyPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1.1.1) s
      (insertBodyProg U V w n_max h_space d) := by
  rcases hpre with ⟨hsb_pre, hq_lt, hv_lt⟩
  obtain ⟨L, hchain, hc_lt⟩ := hsb_pre.2.2.2.2
  unfold insertBodyProg
  simp only [pure_bind]
  refine validProg_bind (validProg_searchBucket (d := (d.1.1, d.2)) hsb_pre) ?_
  have hsb := searchBucketProg_spec hsb_pre.1 hsb_pre.2.1 hsb_pre.2.2.1 hsb_pre.2.2.2.1 hchain hc_lt
  rw [hsb.1]
  refine validProg_ite (fun hf1 => ?_) (fun _ => ?_)
  · have hspec := hsb.2.2
    dsimp only at hspec
    split_ifs at hspec with hex
    · have hphys_lt : ((Memory.spec 0).clientResult s
          (searchBucketProg U V w n_max h_space (d.1.1, d.2))).2 < n_max := by
        rw [hspec.2.2.2.2]
        exact (slotOf_lt_and_injective hsb_pre.2.2.2.1).1 d.1.1.1.2 hsb_pre.2.1 _ hspec.2.1
      exact validProg_writeVal hw hV hphys_lt
    · omega
  · exact validProg_insertNew (d := d) hw hnU hU hV
      ⟨hsb_pre.1, hsb_pre.2.1, hsb_pre.2.2.1, hq_lt, hv_lt, hsb_pre.2.2.2.1, hchain.head_le_cap⟩

theorem validProg_deletePrep {U V w n_max h_space : ℕ}
    (hw : 0 < w) {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : SearchMicroChainPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1.1) s
      (deletePrepProg U V w n_max h_space d) := by
  obtain ⟨L, hchain, hc_lt⟩ := hpre.2.2.2.2
  unfold deletePrepProg
  simp only [pure_bind]
  refine validProg_bind (validProg_searchBucket (d := d) hpre) ?_
  have hsb := searchBucketProg_spec hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hchain hc_lt
  rw [hsb.1]
  refine validProg_ite (fun hf1 => ?_) (fun _ => validProg_pure _)
  have hbc : 1 ≤ bCount n_max (gmAt d.1.1.1 U V w n_max h_space s.mem) d.1.1.2 :=
    searchBucketProg_found_imp_pos_bCount hpre hf1
  refine validProg_bind (validProg_lastSlotOf (d := d.1.1) hw hpre.2.2.2.1 hpre.2.1 hbc) ?_
  rw [clientState_lastSlotOfProg,
    clientResult_lastSlotOfProg d.1.1 s hpre.2.2.2.1 hpre.2.1 hbc]
  have hlast_lt : slotOf n_max (gmAt d.1.1.1 U V w n_max h_space s.mem) d.1.1.2
      (bCount n_max (gmAt d.1.1.1 U V w n_max h_space s.mem) d.1.1.2 - 1) < n_max :=
    (slotOf_lt_and_injective hpre.2.2.2.1).1 d.1.1.2 hpre.2.1 _ (by omega)
  exact validProg_bind (validProg_readQuot hw hlast_lt) (validProg_pure _)

theorem validProg_deleteSwap {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    {d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (hpre : DeleteSwapPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1.1.1) s
      (deleteSwapProg U V w n_max h_space d) := by
  obtain ⟨L, hval, hmem_if⟩ := hpre.2.2.2.2.2.2.2
  have hu_pre : UnlinkIfIndexedPre U V w n_max h_space w ((d.1.1.1, d.2.1), d.2.2) s := by
    refine ⟨hpre.1, hpre.2.2.1, hpre.2.2.2.1, fun hj_cap => ?_⟩
    have hmem := hmem_if hj_cap
    exact ⟨(hval.1 d.1.1.1.2 hpre.2.2.1 d.2.1 hpre.2.2.2.1).prev_le_cap hmem,
      (hval.1 d.1.1.1.2 hpre.2.2.1 d.2.1 hpre.2.2.2.1).next_le_cap hmem⟩
  have eff_u := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w) (n_max := n_max)
    (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (m := d.2.1) (j_del := d.2.2)
    hw hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.2.2.1 hval hmem_if
  let s₁ := (Memory.spec 0).clientState s
    (unlinkIfIndexedProg U V w n_max h_space ((d.1.1.1, d.2.1), d.2.2))
  have hslot₁ : SlotStoreInv n_max (gmAt d.1.1.1.1 U V w n_max h_space s₁.mem) := by
    rw [eff_u.2.2.2.2.1]; exact hpre.2.1
  have hbc₁ : 1 ≤ bCount n_max (gmAt d.1.1.1.1 U V w n_max h_space s₁.mem) d.1.1.1.2 := by
    rw [eff_u.2.2.2.2.1]; exact hpre.2.2.2.2.1
  have hc_pre : CopyLastPayloadPre U V w n_max h_space w (d.1.1.1, d.1.2) s₁ :=
    ⟨hpre.1, hslot₁, hpre.2.2.1, hbc₁, hpre.2.2.2.2.2.1⟩
  have eff_c := copyLastPayloadProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
    (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (phys_del := d.1.2)
    hw hslot₁ hpre.2.2.1 hbc₁ hpre.2.2.2.2.2.1
  obtain ⟨L₁, hval₁, _⟩ := eff_u.2.2.2.2.2
  let s₂ := (Memory.spec 0).clientState s₁
    (copyLastPayloadProg U V w n_max h_space (d.1.1.1, d.1.2))
  have hp_pre : PrependIfIndexedPre U V w n_max h_space w ((d.1.1.1, d.2.1), d.1.1.2) s₂ := by
    refine ⟨hpre.1, hpre.2.2.1, hpre.2.2.2.1, ?_⟩
    rw [eff_c.2.2.2.2.1]
    exact (hval₁.1 d.1.1.1.2 hpre.2.2.1 d.2.1 hpre.2.2.2.1).head_le_cap
  unfold deleteSwapProg
  refine validProg_bind
    (validProg_unlinkIfIndexed (d := ((d.1.1.1, d.2.1), d.2.2)) hw hnU hU hu_pre) ?_
  refine validProg_bind (validProg_copyLastPayload (d := (d.1.1.1, d.1.2)) hw hU hV hc_pre) ?_
  exact validProg_prependIfIndexed (d := ((d.1.1.1, d.2.1), d.1.1.2)) hw hnU hU hp_pre

theorem validProg_deleteFound {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    {d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (hpre : DeleteFoundPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1.1.1) s
      (deleteFoundProg U V w n_max h_space d) := by
  obtain ⟨L, hval, hmem_del, hmem_last⟩ := hpre.2.2.2.2.2.2.2
  have hj_n : d.1.1.2 < n_max :=
    lt_of_lt_of_le hpre.2.2.2.2.2.1 (bCount_le_n_max hpre.2.1 d.1.1.1.2)
  have hu_pre : UnlinkIfIndexedPre U V w n_max h_space w ((d.1.1.1, d.2.1), d.1.1.2) s := by
    refine ⟨hpre.1, hpre.2.2.1, hpre.2.2.2.1, fun hj_cap => ?_⟩
    have hmem := hmem_del hj_cap
    exact ⟨(hval.1 d.1.1.1.2 hpre.2.2.1 d.2.1 hpre.2.2.2.1).prev_le_cap hmem,
      (hval.1 d.1.1.1.2 hpre.2.2.1 d.2.1 hpre.2.2.2.1).next_le_cap hmem⟩
  have eff_u := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w) (n_max := n_max)
    (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (m := d.2.1) (j_del := d.1.1.2)
    hw hpre.2.2.1 hpre.2.2.2.1 hj_n hval hmem_del
  let s₁ := (Memory.spec 0).clientState s
    (unlinkIfIndexedProg U V w n_max h_space ((d.1.1.1, d.2.1), d.1.1.2))
  have hbc_pos : 1 ≤ bCount n_max (gmAt d.1.1.1.1 U V w n_max h_space s.mem) d.1.1.1.2 := by
    have := hpre.2.2.2.2.2.1; omega
  unfold deleteFoundProg
  simp only [pure_bind]
  refine validProg_bind
    (validProg_unlinkIfIndexed (d := ((d.1.1.1, d.2.1), d.1.1.2)) hw hnU hU hu_pre) ?_
  refine validProg_bind (validProg_readBucketCount (d := d.1.1.1) hw hpre.2.2.1) ?_
  rw [clientState_readBucketCountProg,
    clientResult_readBucketCountProg d.1.1.1 s₁ hpre.2.2.1, eff_u.2.2.2.2.1]
  refine validProg_ite (fun hc => ?_) (fun _ => ?_)
  · obtain ⟨L₁, hval₁, hmem₁⟩ := eff_u.2.2.2.2.2
    let j_last := bCount n_max (gmAt d.1.1.1.1 U V w n_max h_space s.mem) d.1.1.1.2 - 1
    have hj_last_n : j_last < n_max := by
      have := bCount_le_n_max hpre.2.1 d.1.1.1.2; omega
    have hsw_pre : DeleteSwapPre U V w n_max h_space w (d.1, (d.2.2, j_last)) s₁ := by
      refine ⟨hpre.1, by rw [eff_u.2.2.2.2.1]; exact hpre.2.1, hpre.2.2.1, hpre.2.2.2.2.1,
        by rw [eff_u.2.2.2.2.1]; exact hbc_pos, hpre.2.2.2.2.2.2.1, hj_last_n, L₁, hval₁,
        fun hj_cap => ?_⟩
      dsimp only at hj_cap ⊢
      rw [hmem₁ d.1.1.1.2 hpre.2.2.1 d.2.2 hpre.2.2.2.2.1]
      exact ⟨hmem_last hj_cap, fun ⟨_, heq⟩ => by omega⟩
    refine validProg_bind
      (validProg_deleteSwap (d := (d.1, (d.2.2, j_last))) hw hnU hU hV hsw_pre) ?_
    have eff_u2 := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (m := d.2.2) (j_del := j_last)
      (s := s₁) hw hpre.2.2.1 hpre.2.2.2.2.1 hj_last_n hval₁
      (fun hj_cap => (hmem₁ d.1.1.1.2 hpre.2.2.1 d.2.2 hpre.2.2.2.2.1 j_last).mpr
        ⟨hmem_last hj_cap, fun ⟨_, heq⟩ => by omega⟩)
    let s₂ := (Memory.spec 0).clientState s₁
      (unlinkIfIndexedProg U V w n_max h_space ((d.1.1.1, d.2.2), j_last))
    have hslot₂ : SlotStoreInv n_max (gmAt d.1.1.1.1 U V w n_max h_space s₂.mem) := by
      rw [eff_u2.2.2.2.2.1, eff_u.2.2.2.2.1]; exact hpre.2.1
    have hbc₂ : 1 ≤ bCount n_max (gmAt d.1.1.1.1 U V w n_max h_space s₂.mem) d.1.1.1.2 := by
      rw [eff_u2.2.2.2.2.1, eff_u.2.2.2.2.1]; exact hbc_pos
    have eff_c := copyLastPayloadProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (phys_del := d.1.2)
      hw hslot₂ hpre.2.2.1 hbc₂ hpre.2.2.2.2.2.2.1
    let s₃ := (Memory.spec 0).clientState s₂
      (copyLastPayloadProg U V w n_max h_space (d.1.1.1, d.1.2))
    obtain ⟨L₂, hval₂, hmem₂⟩ := eff_u2.2.2.2.2.2
    have hval₃ : AllChainsValid n_max (lmAt d.1.1.1.1 U V w n_max h_space s₃.mem) L₂ :=
      hval₂.of_lm_eq eff_c.2.2.2.2.1
    have hj_not₂ : ∀ m' < numMicroPerBucket n_max, d.1.1.2 ∉ L₂ d.1.1.1.2 m' := by
      intro m' hm' hj_in
      have hj_in₁ := ((hmem₂ d.1.1.1.2 hpre.2.2.1 m' hm' d.1.1.2).mp hj_in).1
      exact ((hmem₁ d.1.1.1.2 hpre.2.2.1 m' hm' d.1.1.2).mp hj_in₁).2 ⟨rfl, rfl⟩
    have eff_pr := prependIfIndexedProg_allChainsValid (U := U) (V := V) (w := w) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (m := d.2.2) (j_new := d.1.1.2)
      (s := s₃) hw hpre.2.2.1 hpre.2.2.2.2.1 hj_n hval₃ hj_not₂
    have hst_sw : (Memory.spec 0).clientState s₁
        (deleteSwapProg U V w n_max h_space (d.1, (d.2.2, j_last))) =
        (Memory.spec 0).clientState s₃
          (prependIfIndexedProg U V w n_max h_space ((d.1.1.1, d.2.2), d.1.1.2)) := by
      unfold deleteSwapProg
      repeat rw [StateTransitionSpec.clientState_bind]
    have hgm_sw : gmAt d.1.1.1.1 U V w n_max h_space
        ((Memory.spec 0).clientState s₁
          (deleteSwapProg U V w n_max h_space (d.1, (d.2.2, j_last)))).mem =
        gmAt d.1.1.1.1 U V w n_max h_space s.mem := by
      rw [hst_sw, eff_pr.2.2.2.2.1, eff_c.2.2.2.2.2, eff_u2.2.2.2.2.1, eff_u.2.2.2.2.1]
    refine validProg_popBackSlot (d := d.1.1.1) hw hnU hU hV ⟨hpre.1, ?_, hpre.2.2.1, ?_⟩
    · rw [hgm_sw]; exact hpre.2.1
    · rw [hgm_sw]; exact hbc_pos
  · refine validProg_popBackSlot (d := d.1.1.1) hw hnU hU hV ⟨hpre.1, ?_, hpre.2.2.1, ?_⟩
    · rw [eff_u.2.2.2.2.1]; exact hpre.2.1
    · rw [eff_u.2.2.2.2.1]; exact hbc_pos

theorem validProg_deleteFinish {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    {d : ((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : DeleteFinishPre U V w n_max h_space w d s) :
    ValidProg w (dictFrontier U V w n_max h_space d.1.1.1.1.1) s
      (deleteFinishProg U V w n_max h_space d) := by
  unfold deleteFinishProg
  simp only [pure_bind]
  refine validProg_ite (fun hfound => ?_) (fun _ => validProg_pure ())
  exact validProg_deleteFound
    (d := (((d.1.1.1.1, d.1.1.1.2.2), d.1.1.2), (d.1.2, d.2)))
    hw hnU hU hV (hpre.2 hfound)

end Cslib.DataStructure.Dictionary.WordRAM.Succinct

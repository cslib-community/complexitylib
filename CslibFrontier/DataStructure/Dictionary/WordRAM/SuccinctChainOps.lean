/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSearch
import CslibFrontier.Tactic.Realize

/-!
# Micro-Chain Update Helpers and Bucket Metadata Readers in `Memory.Prog`

This module defines and verifies the `Memory.Prog` building blocks used by the bucket-level
dictionary operations (`insertBodyProg`, `deletePrepProg`, `deleteFinishProg`):
* `AllChainsValid`: global doubly-linked chain invariant across all `(b, m)` pairs;
* `prependIfIndexedProg` and `unlinkIfIndexedProg`: conditional micro-chain updates when a logical
  slot index `j` is in the indexed prefix `j < effBucketCap n_max`;
* `readTotalSlotsProg`: `O(1)` reader for `totalSlots` (`readBucketCountProg` for `bCount` lives in
  `SuccinctProg.lean`);
* `copyLastPayloadProg`: `O(1)` payload copy from the last logical slot of bucket `b` to `phys_del`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.AllChainsValid`: global doubly-linked chain
  invariant across all `(b, m)` pairs.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.prependIfIndexedProg`: conditional `Memory.Prog`
  prepending `j_new` to micro-chain `(b, m)` when `j_new < effBucketCap n_max`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.unlinkIfIndexedProg`: conditional `Memory.Prog`
  unlinking `j_del` from micro-chain `(b, m)` when `j_del < effBucketCap n_max`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.readTotalSlotsProg`: `Memory.Prog` operation
  reading `totalSlots`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.copyLastPayloadProg`: `Memory.Prog` operation
  copying `(Quotients, Values)` from the last slot of bucket `b` to `phys_del`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.lmPrependProg_allChainsValid`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.lmUnlinkProg_allChainsValid`: preservation of
  `AllChainsValid` under prepend and unlink.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.prependIfIndexedProg_allChainsValid`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_prependIfIndexedGen`: effect and
  `Realizes` certificate for `prependIfIndexedProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.unlinkIfIndexedProg_allChainsValid`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_unlinkIfIndexedGen`: effect and
  `Realizes` certificate for `unlinkIfIndexedProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.clientResult_readTotalSlotsProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_readTotalSlotsGen`: specification and
  `Realizes` certificate for `readTotalSlotsProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.copyLastPayloadProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_copyLastPayloadGen`: effect and
  `Realizes` certificate for `copyLastPayloadProg`.
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

/-! ## Section 1: `AllChainsValid` and micro-chain update preservation -/

/-- Global doubly-linked micro-bucket chain invariant across all buckets `b < numBuckets n_max`
and local micro-buckets `m < numMicroPerBucket n_max`, together with pairwise disjointness of
chains within each bucket `b`. -/
@[expose]
def AllChainsValid (n_max : ℕ) (lm : ℕ × ℕ → ℕ) (L : ℕ → ℕ → List ℕ) : Prop :=
  (∀ b < numBuckets n_max, ∀ m < numMicroPerBucket n_max,
    IsDLChain n_max (lmHead n_max lm b m) (lmPrev n_max lm b) (lmNext n_max lm b) (L b m)) ∧
  (∀ b < numBuckets n_max, ∀ m₁ < numMicroPerBucket n_max, ∀ m₂ < numMicroPerBucket n_max,
    ∀ j, j ∈ L b m₁ → j ∈ L b m₂ → m₁ = m₂)

/-- An all-zero `LocalMeta` array satisfies `AllChainsValid` with empty chains `L b m = []`. -/
theorem allChainsValid_of_zero (n_max : ℕ) {lm : ℕ × ℕ → ℕ} (hzero : ∀ p, lm p = 0) :
    AllChainsValid n_max lm (fun _ _ => []) := by
  refine ⟨fun b _ m _ => ?_, fun _ _ _ _ _ _ _ h => by nomatch h⟩
  have hh : lmHead n_max lm b m = 0 := by unfold lmHead; exact hzero _
  rw [hh]
  exact isDLChain_nil n_max _ _

/-- `AllChainsValid` depends only on `lm`. -/
theorem AllChainsValid.of_lm_eq {n_max : ℕ} {lm lm' : ℕ × ℕ → ℕ} {L : ℕ → ℕ → List ℕ}
    (h : AllChainsValid n_max lm L) (heq : lm' = lm) :
    AllChainsValid n_max lm' L := by
  subst heq; exact h

/-- Prepending `j_new < effBucketCap n_max` (with `j_new ∉ L b m'` for all `m'`) preserves
`AllChainsValid`. -/
theorem lmPrependProg_allChainsValid {U V w n_max h_space base b m j_new : ℕ}
    {L : ℕ → ℕ → List ℕ} {s : Memory.State}
    (hw : 0 < w) (hb : b < numBuckets n_max) (hm : m < numMicroPerBucket n_max)
    (hj_cap : j_new < effBucketCap n_max) (hj_n : j_new < n_max)
    (hvalid : AllChainsValid n_max (lmAt base U V w n_max h_space s.mem) L)
    (hj_not : ∀ m' < numMicroPerBucket n_max, j_new ∉ L b m') :
    let s' := (Memory.spec 0).clientState s
      (lmPrependProg U V w n_max h_space (((base, b), m), j_new))
    let L' := fun b' m' => if b' = b ∧ m' = m then j_new :: L b m else L b' m'
    AllChainsValid n_max (lmAt base U V w n_max h_space s'.mem) L' := by
  intro s' L'
  have hold_le : lmHead n_max (lmAt base U V w n_max h_space s.mem) b m ≤ effBucketCap n_max :=
    (hvalid.1 b hb m hm).head_le_cap
  have eff := lmPrependProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
    (h_space := h_space) (base := base) hw hb hm hj_cap hj_n hold_le
  rcases eff with ⟨_, _, _, _, _, hhead, hnext, hprev⟩
  refine ⟨fun b' hb' m' hm' => ?_, fun b' hb' m₁ hm₁ m₂ hm₂ j hj₁ hj₂ => ?_⟩
  · dsimp only [L']
    by_cases hbm : b' = b ∧ m' = m
    · rcases hbm with ⟨rfl, rfl⟩
      rw [ite_eq_left ⟨rfl, rfl⟩]
      have hprep := isDLChain_prepend (hvalid.1 b' hb' m' hm') hj_cap (hj_not m' hm')
      refine hprep.congr (by rw [hhead b' hb' m' hm', ite_eq_left ⟨rfl, rfl⟩])
        (fun x hx => ?_) (fun x hx => ?_)
      · have hx_cap : x < effBucketCap n_max := by
          rcases List.mem_cons.mp hx with rfl | hx_old
          · exact hj_cap
          · exact (hvalid.1 b' hb' m' hm').lt_cap_of_mem hx_old
        rw [hprev b' hb' x hx_cap, ite_eq_left rfl]
      · have hx_cap : x < effBucketCap n_max := by
          rcases List.mem_cons.mp hx with rfl | hx_old
          · exact hj_cap
          · exact (hvalid.1 b' hb' m' hm').lt_cap_of_mem hx_old
        rw [hnext b' hb' x hx_cap, ite_eq_left rfl]
    · rw [ite_eq_right hbm]
      refine (hvalid.1 b' hb' m' hm').congr
        (by rw [hhead b' hb' m' hm', ite_eq_right hbm])
        (fun x hx => ?_) (fun x hx => ?_)
      · have hx_cap := (hvalid.1 b' hb' m' hm').lt_cap_of_mem hx
        rw [hprev b' hb' x hx_cap]
        split_ifs with hb_eq hpos
        · subst hb_eq
          have hm_ne : m' ≠ m := fun heq => hbm ⟨rfl, heq⟩
          have hold_mem := ((hvalid.1 b' hb' m hm).head_sub_one_mem hpos).1
          have hx_ne_old : x ≠ lmHead n_max (lmAt base U V w n_max h_space s.mem) b' m - 1 :=
            fun heq => hm_ne (hvalid.2 b' hb' m' hm' m hm x hx (heq ▸ hold_mem))
          have hx_ne_new : x ≠ j_new := fun heq => hj_not m' hm' (heq ▸ hx)
          rw [Function.update_of_ne hx_ne_old, Function.update_of_ne hx_ne_new]
        · subst hb_eq
          have hx_ne_new : x ≠ j_new := fun heq => hj_not m' hm' (heq ▸ hx)
          rw [Function.update_of_ne hx_ne_new]
        · rfl
      · have hx_cap := (hvalid.1 b' hb' m' hm').lt_cap_of_mem hx
        rw [hnext b' hb' x hx_cap]
        split_ifs with hb_eq
        · subst hb_eq
          have hx_ne_new : x ≠ j_new := fun heq => hj_not m' hm' (heq ▸ hx)
          rw [Function.update_of_ne hx_ne_new]
        · rfl
  · dsimp only [L'] at hj₁ hj₂
    by_cases h1 : b' = b ∧ m₁ = m <;> by_cases h2 : b' = b ∧ m₂ = m
    · rw [h1.2, h2.2]
    · rw [ite_eq_left h1] at hj₁
      rw [ite_eq_right h2] at hj₂
      rcases List.mem_cons.mp hj₁ with rfl | hj₁_old
      · exact False.elim (hj_not m₂ hm₂ (h1.1 ▸ hj₂))
      · exact hvalid.2 b' hb' m₁ hm₁ m₂ hm₂ j (h1.1 ▸ h1.2 ▸ hj₁_old) hj₂
    · rw [ite_eq_right h1] at hj₁
      rw [ite_eq_left h2] at hj₂
      rcases List.mem_cons.mp hj₂ with rfl | hj₂_old
      · exact False.elim (hj_not m₁ hm₁ (h2.1 ▸ hj₁))
      · exact hvalid.2 b' hb' m₁ hm₁ m₂ hm₂ j hj₁ (h2.1 ▸ h2.2 ▸ hj₂_old)
    · rw [ite_eq_right h1] at hj₁
      rw [ite_eq_right h2] at hj₂
      exact hvalid.2 b' hb' m₁ hm₁ m₂ hm₂ j hj₁ hj₂

/-- Unlinking `j_del ∈ L b m` preserves `AllChainsValid` and removes `(b, j_del)` from the
chain family. -/
theorem lmUnlinkProg_allChainsValid {U V w n_max h_space base b m j_del : ℕ}
    {L : ℕ → ℕ → List ℕ} {s : Memory.State}
    (hw : 0 < w) (hb : b < numBuckets n_max) (hm : m < numMicroPerBucket n_max)
    (hvalid : AllChainsValid n_max (lmAt base U V w n_max h_space s.mem) L)
    (hmem : j_del ∈ L b m) :
    let s' := (Memory.spec 0).clientState s
      (lmUnlinkProg U V w n_max h_space (((base, b), m), j_del))
    let L' := fun b' m' => if b' = b ∧ m' = m then (L b m).erase j_del else L b' m'
    AllChainsValid n_max (lmAt base U V w n_max h_space s'.mem) L' ∧
    (∀ b' < numBuckets n_max, ∀ m' < numMicroPerBucket n_max, ∀ j,
      j ∈ L' b' m' ↔ j ∈ L b' m' ∧ ¬(b' = b ∧ j = j_del)) := by
  intro s' L'
  have hj_cap : j_del < effBucketCap n_max := (hvalid.1 b hb m hm).lt_cap_of_mem hmem
  have hp_le : lmPrev n_max (lmAt base U V w n_max h_space s.mem) b j_del ≤ effBucketCap n_max :=
    (hvalid.1 b hb m hm).prev_le_cap hmem
  have hn_le : lmNext n_max (lmAt base U V w n_max h_space s.mem) b j_del ≤ effBucketCap n_max :=
    (hvalid.1 b hb m hm).next_le_cap hmem
  have eff := lmUnlinkProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
    (h_space := h_space) (base := base) hw hb hm hj_cap hp_le hn_le
  rcases eff with ⟨_, _, _, _, _, hhead, hnext, hprev⟩
  refine ⟨⟨fun b' hb' m' hm' => ?_, fun b' hb' m₁ hm₁ m₂ hm₂ j hj₁ hj₂ => ?_⟩,
    fun b' hb' m' hm' j => ?_⟩
  · dsimp only [L']
    by_cases hbm : b' = b ∧ m' = m
    · rcases hbm with ⟨rfl, rfl⟩
      rw [ite_eq_left ⟨rfl, rfl⟩]
      have hunl := isDLChain_unlink (hvalid.1 b' hb' m' hm') hmem
      refine hunl.congr (by rw [hhead b' hb' m' hm', ite_eq_left ⟨rfl, rfl⟩])
        (fun x hx => ?_) (fun x hx => ?_)
      · have hx_cap := (hvalid.1 b' hb' m' hm').lt_cap_of_mem (List.mem_of_mem_erase hx)
        rw [hprev b' hb' x hx_cap, ite_eq_left rfl]
      · have hx_cap := (hvalid.1 b' hb' m' hm').lt_cap_of_mem (List.mem_of_mem_erase hx)
        rw [hnext b' hb' x hx_cap, ite_eq_left rfl]
    · rw [ite_eq_right hbm]
      refine (hvalid.1 b' hb' m' hm').congr
        (by rw [hhead b' hb' m' hm', ite_eq_right hbm])
        (fun x hx => ?_) (fun x hx => ?_)
      · have hx_cap := (hvalid.1 b' hb' m' hm').lt_cap_of_mem hx
        rw [hprev b' hb' x hx_cap]
        split_ifs with hb_eq hn_pos
        · subst hb_eq
          have hm_ne : m' ≠ m := fun heq => hbm ⟨rfl, heq⟩
          have hn_mem := ((hvalid.1 b' hb' m hm).2.next_sub_one_mem hmem hn_pos).1
          have hx_ne : x ≠ lmNext n_max (lmAt base U V w n_max h_space s.mem) b' j_del - 1 :=
            fun heq => hm_ne (hvalid.2 b' hb' m' hm' m hm x hx (heq ▸ hn_mem))
          rw [Function.update_of_ne hx_ne]
        · subst hb_eq; rfl
        · rfl
      · have hx_cap := (hvalid.1 b' hb' m' hm').lt_cap_of_mem hx
        rw [hnext b' hb' x hx_cap]
        split_ifs with hb_eq hp_pos
        · subst hb_eq
          have hm_ne : m' ≠ m := fun heq => hbm ⟨rfl, heq⟩
          rcases (hvalid.1 b' hb' m hm).2.prev_sub_one_mem hmem hp_pos with hp0 | hp_mem
          · omega
          · have hx_ne : x ≠ lmPrev n_max (lmAt base U V w n_max h_space s.mem) b' j_del - 1 :=
              fun heq => hm_ne (hvalid.2 b' hb' m' hm' m hm x hx (heq ▸ hp_mem))
            rw [Function.update_of_ne hx_ne]
        · subst hb_eq; rfl
        · rfl
  · have hj₁_old : j ∈ L b' m₁ := by
      dsimp only [L'] at hj₁
      split_ifs at hj₁ with h1
      · exact h1.1 ▸ h1.2 ▸ List.mem_of_mem_erase hj₁
      · exact hj₁
    have hj₂_old : j ∈ L b' m₂ := by
      dsimp only [L'] at hj₂
      split_ifs at hj₂ with h2
      · exact h2.1 ▸ h2.2 ▸ List.mem_of_mem_erase hj₂
      · exact hj₂
    exact hvalid.2 b' hb' m₁ hm₁ m₂ hm₂ j hj₁_old hj₂_old
  · dsimp only [L']
    by_cases hbm : b' = b ∧ m' = m
    · rcases hbm with ⟨rfl, rfl⟩
      rw [ite_eq_left ⟨rfl, rfl⟩]
      have hnodup := (hvalid.1 b' hb' m' hm').nodup
      constructor
      · intro hj_er
        refine ⟨List.mem_of_mem_erase hj_er, ?_⟩
        rintro ⟨_, rfl⟩
        exact (List.Nodup.not_mem_erase hnodup) hj_er
      · rintro ⟨hj_in, hne⟩
        exact (List.mem_erase_of_ne (fun heq => hne ⟨rfl, heq⟩)).mpr hj_in
    · rw [ite_eq_right hbm]
      constructor
      · intro hj_in
        refine ⟨hj_in, ?_⟩
        rintro ⟨rfl, rfl⟩
        exact hbm ⟨rfl, hvalid.2 b' hb' m' hm' m hm j hj_in hmem⟩
      · exact And.left

/-! ## Section 2: `prependIfIndexedProg`, `unlinkIfIndexedProg`, and bucket readers -/

/-- Parameter-free `Memory.Prog` operation prepending `j_new = d.2` to micro-bucket chain
`(b, m) = (d.1.2.1.2, d.1.2.2)` at `base = d.1.2.1.1` when
`j_new < min n_max (effBucketCap n_max)`. -/
@[expose]
def prependIfIndexedGenProg (d : (DictParams × ((ℕ × ℕ) × ℕ)) × ℕ) : Memory.Prog Unit := do
  let cap ← pure (dpMinCap d.1.1)
  if d.2 < cap then
    lmPrependGenProg (d.1.1, (d.1.2, d.2))
  else
    pure ()

/-- `Memory.Prog` operation prepending `j_new = d.2` to micro-bucket chain
`(b, m) = (d.1.1.2, d.1.2)` at `base = d.1.1.1` when `j_new < min n_max (effBucketCap n_max)`. -/
@[expose]
def prependIfIndexedProg (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog Unit := do
  let cap ← pure (min n_max (effBucketCap n_max))
  if d.2 < cap then
    lmPrependProg U V w n_max h_space d
  else
    pure ()

@[simp]
theorem prependIfIndexedGenProg_mk (U V w n_max h_space : ℕ)
    (d1 : (ℕ × ℕ) × ℕ) (d2 : ℕ) :
    prependIfIndexedGenProg ((mkDictParams U V w n_max h_space, d1), d2) =
      prependIfIndexedProg U V w n_max h_space (d1, d2) := by
  simp only [prependIfIndexedGenProg, prependIfIndexedProg, p_minCap_mk, lmPrependGenProg_mk]

theorem memoryCost_prependIfIndexedProg_le (U V w n_max h_space : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (prependIfIndexedProg U V w n_max h_space d) s ≤ 18 := by
  unfold prependIfIndexedProg
  simp only [pure_bind]
  split_ifs
  · exact memoryCost_lmPrependProg_le U V w n_max h_space d s
  · simp [memoryCost_pure]

/-- Precondition for `prependIfIndexedProg` in `Realizes`. -/
@[expose]
def PrependIfIndexedPre (U V w₀ n_max h_space w : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) d.1.1.1 ∧
  d.1.1.2 < numBuckets n_max ∧
  d.1.2 < numMicroPerBucket n_max ∧
  lmHead n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 d.1.2 ≤ effBucketCap n_max

/-- Parameter-free precondition for `prependIfIndexedGenProg`. -/
@[expose]
def PrependIfIndexedGenPre (w : ℕ)
    (d : (DictParams × ((ℕ × ℕ) × ℕ)) × ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w d.1.1 d.1.2.1.1 ∧
  d.1.2.1.2 < numBuckets (dpNMax d.1.1) ∧
  d.1.2.2 < numMicroPerBucket (dpNMax d.1.1) ∧
  lmHead (dpNMax d.1.1)
    (lmAt d.1.2.1.1 (dpU d.1.1) (dpV d.1.1) (dpW d.1.1) (dpNMax d.1.1) (dpHSpace d.1.1) s.mem)
    d.1.2.1.2 d.1.2.2 ≤ effBucketCap (dpNMax d.1.1)

@[simp]
theorem prependIfIndexedGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d1 : (ℕ × ℕ) × ℕ) (d2 : ℕ) (s : Memory.State) :
    PrependIfIndexedGenPre w ((mkDictParams U V w₀ n_max h_space, d1), d2) s ↔
      PrependIfIndexedPre U V w₀ n_max h_space w (d1, d2) s := Iff.rfl

theorem realizes_prependIfIndexedGen :
    Realizes .exact prependIfIndexedGenProg
      (WordEncoding.encode (α := (DictParams × ((ℕ × ℕ) × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      PrependIfIndexedGenPre
      (fun _ _ => 0) := by
  have hp := realizes_lmPrependGen
  realize
  all_goals (
    rcases d with ⟨⟨dp, d1⟩, d2⟩
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1
    simpDictParamsWith [prependIfIndexedGenPre_mk, PrependIfIndexedPre, prependIfIndexedGenProg_mk,
      lmPrependGenPre_mk, LMPrependPre, lmPrependGenProg_mk]
  )
  · exact ⟨h.1, h.2.1, h.2.2.1, by omega, by omega, h.2.2.2⟩

/-- Pure state effect and `AllChainsValid` preservation of `prependIfIndexedProg`. -/
theorem prependIfIndexedProg_allChainsValid {U V w n_max h_space base b m j_new : ℕ}
    {L : ℕ → ℕ → List ℕ} {s : Memory.State}
    (hw : 0 < w) (hb : b < numBuckets n_max) (hm : m < numMicroPerBucket n_max)
    (hj_n : j_new < n_max)
    (hvalid : AllChainsValid n_max (lmAt base U V w n_max h_space s.mem) L)
    (hj_not : ∀ m' < numMicroPerBucket n_max, j_new ∉ L b m') :
    let d := (((base, b), m), j_new)
    let s' := (Memory.spec 0).clientState s (prependIfIndexedProg U V w n_max h_space d)
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offLM U V w n_max h_space ≤ a ∧ a < base + offGM U V w n_max h_space) →
      s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem = gmAt base U V w n_max h_space s.mem ∧
    ∃ L' : ℕ → ℕ → List ℕ,
      AllChainsValid n_max (lmAt base U V w n_max h_space s'.mem) L' ∧
      (∀ b' < numBuckets n_max, ∀ m' < numMicroPerBucket n_max, ∀ j,
        j ∈ L' b' m' ↔
          j ∈ L b' m' ∨ (b' = b ∧ m' = m ∧ j = j_new ∧ j_new < effBucketCap n_max)) := by
  intro d s'
  by_cases hj_min : j_new < min n_max (effBucketCap n_max)
  · have hj_cap : j_new < effBucketCap n_max := (lt_min_iff.mp hj_min).2
    have hs' : s' = (Memory.spec 0).clientState s
        (lmPrependProg U V w n_max h_space (((base, b), m), j_new)) := by
      change (Memory.spec 0).clientState s (prependIfIndexedProg U V w n_max h_space d) = _
      unfold prependIfIndexedProg
      simp only [pure_bind, d]
      rw [ite_eq_left hj_min]
    have hold_le : lmHead n_max (lmAt base U V w n_max h_space s.mem) b m ≤ effBucketCap n_max :=
      (hvalid.1 b hb m hm).head_le_cap
    have eff := lmPrependProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
      (h_space := h_space) (base := base) hw hb hm hj_cap hj_n hold_le
    have hval' := lmPrependProg_allChainsValid (U := U) (V := V) (w := w) (n_max := n_max)
      (h_space := h_space) (base := base) hw hb hm hj_cap hj_n hvalid hj_not
    rw [hs']
    refine ⟨eff.1, eff.2.1, eff.2.2.1, eff.2.2.2.1, eff.2.2.2.2.1,
      fun b' m' => if b' = b ∧ m' = m then j_new :: L b m else L b' m', hval',
      fun b' hb' m' hm' j => ?_⟩
    dsimp only
    by_cases hbm : b' = b ∧ m' = m
    · rcases hbm with ⟨rfl, rfl⟩
      rw [ite_eq_left ⟨rfl, rfl⟩, List.mem_cons]
      constructor
      · rintro (rfl | hj_in)
        · exact Or.inr ⟨rfl, rfl, rfl, hj_cap⟩
        · exact Or.inl hj_in
      · rintro (hj_in | ⟨_, _, rfl, _⟩)
        · exact Or.inr hj_in
        · exact Or.inl rfl
    · rw [ite_eq_right hbm]
      constructor
      · exact Or.inl
      · rintro (hj_in | ⟨rfl, rfl, _⟩)
        · exact hj_in
        · exact False.elim (hbm ⟨rfl, rfl⟩)
  · have hj_not_cap : ¬(j_new < effBucketCap n_max) := fun hc => hj_min (lt_min hj_n hc)
    have hs' : s' = s := by
      change (Memory.spec 0).clientState s (prependIfIndexedProg U V w n_max h_space d) = s
      unfold prependIfIndexedProg
      simp only [pure_bind, d]
      rw [ite_eq_right hj_min]
      rfl
    rw [hs']
    refine ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, L, hvalid, fun b' _ m' _ j => ?_⟩
    constructor
    · exact Or.inl
    · rintro (hj_in | ⟨_, _, _, hcap⟩)
      · exact hj_in
      · exact False.elim (hj_not_cap hcap)

/-- Parameter-free `Memory.Prog` operation unlinking `j_del = d.2` from micro-bucket chain
`(b, m) = (d.1.2.1.2, d.1.2.2)` at `base = d.1.2.1.1` when
`j_del < min n_max (effBucketCap n_max)`. -/
@[expose]
def unlinkIfIndexedGenProg (d : (DictParams × ((ℕ × ℕ) × ℕ)) × ℕ) : Memory.Prog Unit := do
  let cap ← pure (dpMinCap d.1.1)
  if d.2 < cap then
    lmUnlinkGenProg (d.1.1, (d.1.2, d.2))
  else
    pure ()

/-- `Memory.Prog` operation unlinking `j_del = d.2` from micro-bucket chain
`(b, m) = (d.1.1.2, d.1.2)` at `base = d.1.1.1` when `j_del < min n_max (effBucketCap n_max)`. -/
@[expose]
def unlinkIfIndexedProg (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog Unit := do
  let cap ← pure (min n_max (effBucketCap n_max))
  if d.2 < cap then
    lmUnlinkProg U V w n_max h_space d
  else
    pure ()

@[simp]
theorem unlinkIfIndexedGenProg_mk (U V w n_max h_space : ℕ)
    (d1 : (ℕ × ℕ) × ℕ) (d2 : ℕ) :
    unlinkIfIndexedGenProg ((mkDictParams U V w n_max h_space, d1), d2) =
      unlinkIfIndexedProg U V w n_max h_space (d1, d2) := by
  simp only [unlinkIfIndexedGenProg, unlinkIfIndexedProg, p_minCap_mk, lmUnlinkGenProg_mk]

theorem memoryCost_unlinkIfIndexedProg_le (U V w n_max h_space : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (unlinkIfIndexedProg U V w n_max h_space d) s ≤ 12 := by
  unfold unlinkIfIndexedProg
  simp only [pure_bind]
  split_ifs
  · exact memoryCost_lmUnlinkProg_le U V w n_max h_space d s
  · simp [memoryCost_pure]

/-- Precondition for `unlinkIfIndexedProg` in `Realizes`. -/
@[expose]
def UnlinkIfIndexedPre (U V w₀ n_max h_space w : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) d.1.1.1 ∧
  d.1.1.2 < numBuckets n_max ∧
  d.1.2 < numMicroPerBucket n_max ∧
  (d.2 < effBucketCap n_max →
    lmPrev n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 d.2 ≤ effBucketCap n_max ∧
    lmNext n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 d.2 ≤ effBucketCap n_max)

/-- Parameter-free precondition for `unlinkIfIndexedGenProg`. -/
@[expose]
def UnlinkIfIndexedGenPre (w : ℕ)
    (d : (DictParams × ((ℕ × ℕ) × ℕ)) × ℕ) (s : Memory.State) : Prop :=
  let lm := lmAt d.1.2.1.1 (dpU d.1.1) (dpV d.1.1) (dpW d.1.1) (dpNMax d.1.1) (dpHSpace d.1.1) s.mem
  DictEnvGen w d.1.1 d.1.2.1.1 ∧
  d.1.2.1.2 < numBuckets (dpNMax d.1.1) ∧
  d.1.2.2 < numMicroPerBucket (dpNMax d.1.1) ∧
  (d.2 < effBucketCap (dpNMax d.1.1) →
    lmPrev (dpNMax d.1.1) lm d.1.2.1.2 d.2 ≤ effBucketCap (dpNMax d.1.1) ∧
    lmNext (dpNMax d.1.1) lm d.1.2.1.2 d.2 ≤ effBucketCap (dpNMax d.1.1))

@[simp]
theorem unlinkIfIndexedGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d1 : (ℕ × ℕ) × ℕ) (d2 : ℕ) (s : Memory.State) :
    UnlinkIfIndexedGenPre w ((mkDictParams U V w₀ n_max h_space, d1), d2) s ↔
      UnlinkIfIndexedPre U V w₀ n_max h_space w (d1, d2) s := Iff.rfl

theorem realizes_unlinkIfIndexedGen :
    Realizes .exact unlinkIfIndexedGenProg
      (WordEncoding.encode (α := (DictParams × ((ℕ × ℕ) × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      UnlinkIfIndexedGenPre
      (fun _ _ => 0) := by
  have hu := realizes_lmUnlinkGen
  realize
  all_goals (
    rcases d with ⟨⟨dp, d1⟩, d2⟩
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1
    simpDictParamsWith [unlinkIfIndexedGenPre_mk, UnlinkIfIndexedPre, unlinkIfIndexedGenProg_mk,
      lmUnlinkGenPre_mk, LMUnlinkPre, lmUnlinkGenProg_mk]
  )
  · have hj_cap : d2 < effBucketCap n_max := by omega
    exact ⟨h.1, h.2.1, h.2.2.1, hj_cap, (h.2.2.2 hj_cap).1, (h.2.2.2 hj_cap).2⟩

/-- Pure state effect and `AllChainsValid` preservation of `unlinkIfIndexedProg`. -/
theorem unlinkIfIndexedProg_allChainsValid {U V w n_max h_space base b m j_del : ℕ}
    {L : ℕ → ℕ → List ℕ} {s : Memory.State}
    (hw : 0 < w) (hb : b < numBuckets n_max) (hm : m < numMicroPerBucket n_max)
    (hj_n : j_del < n_max)
    (hvalid : AllChainsValid n_max (lmAt base U V w n_max h_space s.mem) L)
    (hmem_if : j_del < effBucketCap n_max → j_del ∈ L b m) :
    let d := (((base, b), m), j_del)
    let s' := (Memory.spec 0).clientState s (unlinkIfIndexedProg U V w n_max h_space d)
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offLM U V w n_max h_space ≤ a ∧ a < base + offGM U V w n_max h_space) →
      s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem = gmAt base U V w n_max h_space s.mem ∧
    ∃ L' : ℕ → ℕ → List ℕ,
      AllChainsValid n_max (lmAt base U V w n_max h_space s'.mem) L' ∧
      (∀ b' < numBuckets n_max, ∀ m' < numMicroPerBucket n_max, ∀ j,
        j ∈ L' b' m' ↔ j ∈ L b' m' ∧ ¬(b' = b ∧ j = j_del)) := by
  intro d s'
  by_cases hj_min : j_del < min n_max (effBucketCap n_max)
  · have hj_cap : j_del < effBucketCap n_max := (lt_min_iff.mp hj_min).2
    have hmem := hmem_if hj_cap
    have hs' : s' = (Memory.spec 0).clientState s
        (lmUnlinkProg U V w n_max h_space (((base, b), m), j_del)) := by
      change (Memory.spec 0).clientState s (unlinkIfIndexedProg U V w n_max h_space d) = _
      unfold unlinkIfIndexedProg
      simp only [pure_bind, d]
      rw [ite_eq_left hj_min]
    have hp_le : lmPrev n_max (lmAt base U V w n_max h_space s.mem) b j_del ≤ effBucketCap n_max :=
      (hvalid.1 b hb m hm).prev_le_cap hmem
    have hn_le : lmNext n_max (lmAt base U V w n_max h_space s.mem) b j_del ≤ effBucketCap n_max :=
      (hvalid.1 b hb m hm).next_le_cap hmem
    have eff := lmUnlinkProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
      (h_space := h_space) (base := base) hw hb hm hj_cap hp_le hn_le
    have ⟨hval', hmem'⟩ := lmUnlinkProg_allChainsValid (U := U) (V := V) (w := w)
      (n_max := n_max) (h_space := h_space) (base := base) hw hb hm hvalid hmem
    rw [hs']
    exact ⟨eff.1, eff.2.1, eff.2.2.1, eff.2.2.2.1, eff.2.2.2.2.1, _, hval', hmem'⟩
  · have hj_not_cap : ¬(j_del < effBucketCap n_max) := fun hc => hj_min (lt_min hj_n hc)
    have hs' : s' = s := by
      change (Memory.spec 0).clientState s (unlinkIfIndexedProg U V w n_max h_space d) = s
      unfold unlinkIfIndexedProg
      simp only [pure_bind, d]
      rw [ite_eq_right hj_min]
      rfl
    rw [hs']
    refine ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, L, hvalid, fun b' hb' m' hm' j => ?_⟩
    constructor
    · intro hj_in
      refine ⟨hj_in, ?_⟩
      rintro ⟨_, rfl⟩
      exact hj_not_cap ((hvalid.1 b' hb' m' hm').lt_cap_of_mem hj_in)
    · exact And.left

/-- Parameter-free `Memory.Prog` reader returning `totalSlots n_max gm` at `base = d.2`. -/
@[expose]
def readTotalSlotsGenProg (d : DictParams × ℕ) : Memory.Prog ℕ :=
  if dpBucketBits d.1 = 0 then do
    let i0 ← pure 0
    readGMGenProg (d.1, (d.2, i0))
  else do
    let i0 ← pure 0
    let i1 ← pure 1
    let n_slabs ← readGMGenProg (d.1, (d.2, i0))
    let n_tails ← readGMGenProg (d.1, (d.2, i1))
    pure (n_slabs * dpSlabSize d.1 + n_tails)

/-- `Memory.Prog` reader returning `totalSlots n_max gm` at `base`. -/
@[expose]
def readTotalSlotsProg (U V w n_max h_space : ℕ) (base : ℕ) : Memory.Prog ℕ :=
  if bucketBits n_max = 0 then do
    let i0 ← pure 0
    readGMProg U V w n_max h_space (base, i0)
  else do
    let i0 ← pure 0
    let i1 ← pure 1
    let n_slabs ← readGMProg U V w n_max h_space (base, i0)
    let n_tails ← readGMProg U V w n_max h_space (base, i1)
    pure (n_slabs * slabSize n_max + n_tails)

@[simp]
theorem readTotalSlotsGenProg_mk (U V w n_max h_space base : ℕ) :
    readTotalSlotsGenProg (mkDictParams U V w n_max h_space, base) =
      readTotalSlotsProg U V w n_max h_space base := by
  by_cases hb0 : bucketBits n_max = 0 <;>
    simp [readTotalSlotsGenProg, readTotalSlotsProg, hb0, ← PFunctor.FreeM.bind_eq_bind]

theorem clientState_readTotalSlotsProg (U V w n_max h_space : ℕ) (base : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readTotalSlotsProg U V w n_max h_space base) = s := by
  unfold readTotalSlotsProg
  split_ifs <;> rfl

theorem memoryCost_readTotalSlotsProg_le (U V w n_max h_space : ℕ) (base : ℕ) (s : Memory.State) :
    memoryCost (readTotalSlotsProg U V w n_max h_space base) s ≤ 4 := by
  unfold readTotalSlotsProg
  split_ifs
  · change 2 ≤ 4; omega
  · change 4 ≤ 4; omega

theorem clientResult_readTotalSlotsProg (U V w n_max h_space : ℕ) (base : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (readTotalSlotsProg U V w n_max h_space base) =
      totalSlots n_max (gmAt base U V w n_max h_space s.mem) := by
  unfold readTotalSlotsProg totalSlots
  have h0_lt : 0 < globalMetaLen n_max := by
    unfold globalMetaLen
    exact Nat.lt_of_lt_of_le (by decide : 0 < 4) (Nat.le_add_right 4 _)
  by_cases hb0 : bucketBits n_max = 0
  · simp only [hb0, ↓reduceIte, pure_bind, clientResult_readGMProg s h0_lt]
  · have h1_lt : 1 < globalMetaLen n_max := by
      unfold globalMetaLen
      exact Nat.lt_of_lt_of_le (by decide : 1 < 4) (Nat.le_add_right 4 _)
    simp only [hb0, ↓reduceIte, pure_bind]
    rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      clientResult_readGMProg s h0_lt,
      StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      clientResult_readGMProg s h1_lt]
    rfl

theorem realizes_readTotalSlotsGen :
    Realizes .exact readTotalSlotsGenProg
      (WordEncoding.encode (α := DictParams × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w d s => DictEnvGen w d.1 d.2 ∧
        SlotStoreInv (dpNMax d.1)
          (gmAt d.2 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem))
      (fun _ _ => 0) := by
  realizeDict using [realizes_readGMGen]
  · exact h.1
  · unfold globalMetaLen; omega
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact h.1
  · unfold globalMetaLen; omega
  · unfold globalMetaLen; omega
  · have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
    have h1_lt : 1 < globalMetaLen n_max := by unfold globalMetaLen; omega
    rw [clientState_readGMProg, clientResult_readGMProg s h0_lt,
      clientResult_readGMProg s h1_lt]
    exact fits_of_le_max_n_one h.1 hw hnU hU
      (le_trans (h.2.multi_total_le (Nat.pos_of_ne_zero hc)) (le_max_left _ _))

/-- Parameter-free `Memory.Prog` helper copying `(quotAt, valAt)` from the last logical slot
`lastSlotOfGenProg (dp, (base, b))` of bucket `b = d.2.1.2` (`base = d.2.1.1`) into
`phys_del = d.2.2`. -/
@[expose]
def copyLastPayloadGenProg (d : DictParams × ((ℕ × ℕ) × ℕ)) : Memory.Prog Unit := do
  let phys_last ← lastSlotOfGenProg (d.1, d.2.1)
  let q_last ← readQuotGenProg (d.1, (d.2.1.1, phys_last))
  let v_last ← readValGenProg (d.1, (d.2.1.1, phys_last))
  writeQuotGenProg (d.1, ((d.2.1.1, d.2.2), q_last))
  writeValGenProg (d.1, ((d.2.1.1, d.2.2), v_last))

/-- `Memory.Prog` helper copying `(quotAt, valAt)` from the last logical slot
`lastSlotOfProg (base, b)` of bucket `b = d.1.2` (`base = d.1.1`) into `phys_del = d.2`. -/
@[expose]
def copyLastPayloadProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit := do
  let phys_last ← lastSlotOfProg U V w n_max h_space d.1
  let q_last ← readQuotProg U w n_max h_space (d.1.1, phys_last)
  let v_last ← readValProg U V w n_max h_space (d.1.1, phys_last)
  writeQuotProg U w n_max h_space ((d.1.1, d.2), q_last)
  writeValProg U V w n_max h_space ((d.1.1, d.2), v_last)

@[simp]
theorem copyLastPayloadGenProg_mk (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) :
    copyLastPayloadGenProg (mkDictParams U V w n_max h_space, d) =
      copyLastPayloadProg U V w n_max h_space d := by
  simp only [copyLastPayloadGenProg, copyLastPayloadProg, lastSlotOfGenProg_mk,
    readQuotGenProg_mk, readValGenProg_mk, writeQuotGenProg_mk, writeValGenProg_mk]

theorem memoryCost_copyLastPayloadProg_le (U V w n_max h_space : ℕ)
    (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (copyLastPayloadProg U V w n_max h_space d) s ≤ 20 := by
  unfold copyLastPayloadProg
  simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
    memoryCost_readQuotProg, memoryCost_readValProg,
    memoryCost_writeQuotProg, memoryCost_writeValProg]
  have := memoryCost_lastSlotOfProg_le U V w n_max h_space d.1 s
  omega

/-- Precondition for `copyLastPayloadProg` in `Realizes`. -/
@[expose]
def CopyLastPayloadPre (U V w₀ n_max h_space w : ℕ)
    (d : (ℕ × ℕ) × ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) d.1.1 ∧
  SlotStoreInv n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) ∧
  d.1.2 < numBuckets n_max ∧
  1 ≤ bCount n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2 ∧
  d.2 < n_max

/-- Parameter-free precondition for `copyLastPayloadGenProg`. -/
@[expose]
def CopyLastPayloadGenPre (w : ℕ)
    (d : DictParams × ((ℕ × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  let gm := gmAt d.2.1.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem
  DictEnvGen w d.1 d.2.1.1 ∧
  SlotStoreInv (dpNMax d.1) gm ∧
  d.2.1.2 < numBuckets (dpNMax d.1) ∧
  1 ≤ bCount (dpNMax d.1) gm d.2.1.2 ∧
  d.2.2 < dpNMax d.1

@[simp]
theorem copyLastPayloadGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    CopyLastPayloadGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      CopyLastPayloadPre U V w₀ n_max h_space w d s := Iff.rfl

theorem realizes_copyLastPayloadGen :
    Realizes .exact copyLastPayloadGenProg
      (WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      CopyLastPayloadGenPre
      (fun _ _ => 0) := by
  realizeDictWith [copyLastPayloadGenPre_mk, CopyLastPayloadPre,
    lastSlotOfGenPre_mk, lastSlotOfGenProg_mk] using
    [realizes_lastSlotOfGen, realizes_readQuotGen, realizes_readValGen, realizes_writeQuotGen,
      realizes_writeValGen]
  · exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · exact h.1
  · rw [clientResult_lastSlotOfProg d.1 s h.2.1 h.2.2.1 h.2.2.2.1]
    exact (slotOf_lt_and_injective h.2.1).1 d.1.2 h.2.2.1 _ (by have := h.2.2.2.1; omega)
  · exact h.2.2.2.2

/-- Pure state effect of `copyLastPayloadProg`. -/
theorem copyLastPayloadProg_effect {U V w n_max h_space base b phys_del : ℕ}
    (hw : 0 < w) {s : Memory.State}
    (hinv : SlotStoreInv n_max (gmAt base U V w n_max h_space s.mem))
    (hb : b < numBuckets n_max)
    (hbc : 1 ≤ bCount n_max (gmAt base U V w n_max h_space s.mem) b)
    (hphys_del : phys_del < n_max) :
    let gm := gmAt base U V w n_max h_space s.mem
    let phys_last := slotOf n_max gm b (bCount n_max gm b - 1)
    let q_last := quotAt base U w n_max h_space s.mem phys_last
    let v_last := valAt base U V w n_max h_space s.mem phys_last
    let s' := (Memory.spec 0).clientState s
      (copyLastPayloadProg U V w n_max h_space ((base, b), phys_del))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧ a < base + totalSpace U V w n_max h_space) →
      s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem =
      Function.update (quotAt base U w n_max h_space s.mem) phys_del q_last ∧
    valAt base U V w n_max h_space s'.mem =
      Function.update (valAt base U V w n_max h_space s.mem) phys_del v_last ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem = gmAt base U V w n_max h_space s.mem := by
  intro gm phys_last q_last v_last s'
  dsimp only [gm, phys_last, q_last, v_last] at *
  have hphys_last : slotOf n_max (gmAt base U V w n_max h_space s.mem) b
      (bCount n_max (gmAt base U V w n_max h_space s.mem) b - 1) < n_max :=
    (slotOf_lt_and_injective hinv).1 b hb _ (by omega)
  have hq_lt : q_last < 2 ^ quotientBits U n_max := quotAt_lt base U w n_max h_space s.mem phys_last
  have hv_lt : v_last < 2 ^ valBits V := valAt_lt base U V w n_max h_space s.mem phys_last
  let s₁ := (Memory.spec 0).clientState s
    (writeQuotProg U w n_max h_space ((base, phys_del), q_last))
  have eff₁ := writeQuotProg_effect (base := base) (V := V) (h_space := h_space)
    hw hphys_del hq_lt s
  have eff₂ := writeValProg_effect (U := U) (base := base) (h_space := h_space)
    hw hphys_del hv_lt s₁
  have hs' : s' = (Memory.spec 0).clientState s₁
      (writeValProg U V w n_max h_space ((base, phys_del), v_last)) := by
    dsimp only [s', s₁, q_last, v_last, phys_last, gm]
    unfold copyLastPayloadProg
    rw [StateTransitionSpec.clientState_bind, clientState_lastSlotOfProg,
      clientResult_lastSlotOfProg (base, b) s hinv hb hbc,
      StateTransitionSpec.clientState_bind, clientState_readQuotProg,
      clientResult_readQuotProg s hphys_last,
      StateTransitionSpec.clientState_bind, clientState_readValProg,
      clientResult_readValProg s hphys_last,
      StateTransitionSpec.clientState_bind]
  rw [hs']
  refine ⟨eff₂.1.trans eff₁.1,
    fun a ha => ?_,
    eff₂.2.2.1.trans eff₁.2.2.1,
    eff₂.2.2.2.1.trans (congrArg (fun f => Function.update f phys_del v_last) eff₁.2.2.2.1),
    eff₂.2.2.2.2.1.trans eff₁.2.2.2.2.1,
    eff₂.2.2.2.2.2.trans eff₁.2.2.2.2.2⟩
  rw [eff₂.2.1 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega),
    eff₁.2.1 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega)]

end Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.WordRAM.SuccinctBucketOps
import Complexity.Tactic.Realize

/-!
# Bucket-Level Dictionary Deletion (`deletePrepProg`, `deleteFinishProg`) in `Memory.Prog`

This module realizes the two-phase bucket-level deletion of the fixed-capacity succinct dictionary
in `Memory.Prog` via `realize`:
* `deletePrepProg` and `realizes_deletePrepGen`: Phase 1 of `delete` (search bucket `b` for
  `q_target` and, if found, read the quotient `q_last` of the last slot in the bucket so that the
  Word-RAM wrapper can compute `m_last`);
* `deleteSwapProg`, `deleteFoundProg`, `deleteFinishProg`, and `realizes_deleteFinishGen`: Phase 2
  of `delete` (unlink the deleted slot, swap the last slot into the deleted slot and relink into
  `m_last` when `j_del < j_last`, and pop the last slot from the bucket).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.deletePrepProg`: Phase 1 of `delete` in
  `Memory.Prog` (searches bucket `b` and reads `q_last` when found).
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.deleteSwapProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.deleteFoundProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.deleteFinishProg`: Phase 2 of `delete` in
  `Memory.Prog` (unlinks `j_del`, relocates `j_last` into `j_del` when `j_del < j_last`, and calls
  `popBackSlotProg`).

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_deletePrepGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.deletePrepProg_bucket_spec`: `Realizes`
  certificate and bucket-level specification for `deletePrepProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_deleteFinishGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.deleteFinishProg_bucket_spec`: `Realizes`
  certificate, `BucketStateInv` preservation, and amortized `memoryCost` bound for
  `deleteFinishProg`.
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

/-! ## Section 1: `deletePrepProg` via `realize` -/

/-- Parameter-free Phase 1 of `delete` (`d = (dp, (((base, b), q_target), m))`):
searches bucket `b` for `q_target`; if found (`res.1.1 = 1`), resolves the last slot `phys_last` of
bucket `b`, reads its quotient `q_last`, and returns `(res, q_last)`; otherwise returns
`(((0, 0), 0), 0)`. -/
@[expose]
def deletePrepGenProg
    (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) : Memory.Prog (((ℕ × ℕ) × ℕ) × ℕ) := do
  let res ← searchBucketGenProg d
  let z1 ← pure 1
  if res.1.1 = z1 then do
    let phys_last ← lastSlotOfGenProg (d.1, d.2.1.1)
    let q_last ← readQuotGenProg (d.1, (d.2.1.1.1, phys_last))
    pure (res, q_last)
  else do
    let z0 ← pure 0
    pure (((z0, z0), z0), z0)

/-- Phase 1 of `delete` (`d = (((base, b), q_target), m)`):
searches bucket `b` for `q_target`; if found (`res.1.1 = 1`), resolves the last slot `phys_last` of
bucket `b`, reads its quotient `q_last`, and returns `(res, q_last)`; otherwise returns
`(((0, 0), 0), 0)`. -/
@[expose]
def deletePrepProg (U V w n_max h_space : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog (((ℕ × ℕ) × ℕ) × ℕ) := do
  let res ← searchBucketProg U V w n_max h_space d
  let z1 ← pure 1
  if res.1.1 = z1 then do
    let phys_last ← lastSlotOfProg U V w n_max h_space d.1.1
    let q_last ← readQuotProg U w n_max h_space (d.1.1.1, phys_last)
    pure (res, q_last)
  else do
    let z0 ← pure 0
    pure (((z0, z0), z0), z0)

@[simp]
theorem deletePrepGenProg_mk (U V w n_max h_space : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    deletePrepGenProg (mkDictParams U V w n_max h_space, d) =
      deletePrepProg U V w n_max h_space d := by
  simp only [deletePrepGenProg, deletePrepProg, searchBucketGenProg_mk, lastSlotOfGenProg_mk,
    readQuotGenProg_mk]

/-- When `searchBucketProg` reports `found = 1`, the returned logical index is `< bCount`, so
`1 ≤ bCount`. -/
private theorem searchBucketProg_found_imp_pos_bCount {U V w₀ n_max h_space w : ℕ}
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (h : SearchMicroChainPre U V w₀ n_max h_space w d s)
    (hfound :
      ((Memory.spec 0).clientResult s (searchBucketProg U V w₀ n_max h_space d)).1.1 = 1) :
    1 ≤ bCount n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 := by
  obtain ⟨L, hchain, hc_lt⟩ := h.2.2.2.2
  have hres := (searchBucketProg_spec h.1 h.2.1 h.2.2.1 h.2.2.2.1 hchain hc_lt).2.2
  dsimp only at hres
  by_cases hex :
      (∃ j ∈ L, quotAt d.1.1.1 U w₀ n_max h_space s.mem
        (slotOf n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 j) = d.1.2) ∨
      (∃ j, effBucketCap n_max ≤ j ∧
        j < bCount n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 ∧
        quotAt d.1.1.1 U w₀ n_max h_space s.mem
          (slotOf n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 j) = d.1.2)
  · rw [ite_eq_left hex] at hres
    have := hres.2.1
    omega
  · rw [ite_eq_right hex] at hres
    omega

theorem realizes_deletePrepGen :
    Realizes .exact deletePrepGenProg
      (WordEncoding.encode (α := DictParams × (((ℕ × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      SearchMicroChainGenPre
      (fun _ _ => 0) := by
  have hsb := realizes_searchBucketGen
  have hl := realizes_lastSlotOfGen
  have hrq := realizes_readQuotGen
  realizeDictWith [searchMicroChainGenPre_mk, SearchMicroChainPre, searchBucketGenProg_mk,
    lastSlotOfGenPre_mk, lastSlotOfGenProg_mk]
  · exact h
  · exact fits_const_of_dictEnv h.1 (by decide)
  · obtain ⟨L, hchain, hc_lt⟩ := h.2.2.2.2
    rw [(searchBucketProg_spec h.1 h.2.1 h.2.2.1 h.2.2.2.1 hchain hc_lt).1]
    exact ⟨h.1, h.2.2.2.1, h.2.1, searchBucketProg_found_imp_pos_bCount h hc⟩
  · exact h.1
  · obtain ⟨L, hchain, hc_lt⟩ := h.2.2.2.2
    rw [(searchBucketProg_spec h.1 h.2.1 h.2.2.1 h.2.2.2.1 hchain hc_lt).1]
    have hbc := searchBucketProg_found_imp_pos_bCount h hc
    rw [clientResult_lastSlotOfProg d.1.1 s h.2.2.2.1 h.2.1 hbc]
    exact (slotOf_lt_and_injective h.2.2.2.1).1 d.1.1.2 h.2.1 _ (by omega)

/-- Specification of `deletePrepProg` under `BucketStateInv` when `m = mOf q_target`. -/
theorem deletePrepProg_bucket_spec {U V w₀ n_max h_space w base b q_target m : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s : Memory.State}
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hb : b < numBuckets n_max) (hm_eq : m = mOf q_target)
    (hm_lt : m < numMicroPerBucket n_max) :
    let gm := gmAt base U V w₀ n_max h_space s.mem
    let d := (((base, b), q_target), m)
    let prog := deletePrepProg U V w₀ n_max h_space d
    let prep := (Memory.spec 0).clientResult s prog
    (Memory.spec 0).clientState s prog = s ∧
    memoryCost prog s ≤
      16 + 8 * (L b m).length + 6 * (bCount n_max gm b - effBucketCap n_max) ∧
    prep.2 < 2 ^ quotientBits U n_max ∧
    (if ∃ j < bCount n_max gm b,
         quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm b j) = q_target then
       prep.1.1.1 = 1 ∧
       prep.1.1.2 < bCount n_max gm b ∧
       quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm b prep.1.1.2) = q_target ∧
       prep.1.2 = slotOf n_max gm b prep.1.1.2 ∧
       prep.2 = quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm b (bCount n_max gm b - 1))
     else
       prep.1.1.1 = 0 ∧ prep.2 = 0) := by
  intro gm d prog prep
  dsimp only [gm, d, prog, prep]
  have hsb := searchBucketProg_bucket_spec hinv henv hb hm_eq hm_lt (q_target := q_target)
  dsimp only at hsb
  set res := (Memory.spec 0).clientResult s
    (searchBucketProg U V w₀ n_max h_space (((base, b), q_target), m))
  have hres := hsb.2.2
  by_cases hex : ∃ j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b,
      quotAt base U w₀ n_max h_space s.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j) = q_target
  · rw [ite_eq_left hex] at hres
    rcases hres with ⟨hf1, hj_lt, hq_match, hphys_eq⟩
    have hbc : 1 ≤ bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b := by omega
    have hphys_last_lt :
        slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b
          (bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b - 1) < n_max :=
      (slotOf_lt_and_injective hinv.hslot).1 b hb _ (by omega)
    have hprep_eq :
        (Memory.spec 0).clientResult s
          (deletePrepProg U V w₀ n_max h_space (((base, b), q_target), m)) =
        (res,
          quotAt base U w₀ n_max h_space s.mem
            (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b
              (bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b - 1))) := by
      unfold deletePrepProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientResult_bind, hsb.1]
      change (Memory.spec 0).clientResult s
        (if res.1.1 = 1 then do
           let phys_last ← lastSlotOfProg U V w₀ n_max h_space (base, b)
           let q_last ← readQuotProg U w₀ n_max h_space (base, phys_last)
           pure (res, q_last)
         else pure (((0, 0), 0), 0)) = _
      rw [ite_eq_left hf1, StateTransitionSpec.clientResult_bind, clientState_lastSlotOfProg,
        clientResult_lastSlotOfProg (base, b) s hinv.hslot hb hbc,
        StateTransitionSpec.clientResult_bind, clientState_readQuotProg,
        clientResult_readQuotProg s hphys_last_lt]
      rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold deletePrepProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, hsb.1]
      change (Memory.spec 0).clientState s
        (if res.1.1 = 1 then do
           let phys_last ← lastSlotOfProg U V w₀ n_max h_space (base, b)
           let q_last ← readQuotProg U w₀ n_max h_space (base, phys_last)
           pure (res, q_last)
         else pure (((0, 0), 0), 0)) = s
      rw [ite_eq_left hf1, StateTransitionSpec.clientState_bind, clientState_lastSlotOfProg,
        StateTransitionSpec.clientState_bind, clientState_readQuotProg]
      rfl
    · unfold deletePrepProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
      rw [memoryCost_bind, hsb.1]
      change memoryCost (searchBucketProg U V w₀ n_max h_space (((base, b), q_target), m)) s +
        memoryCost (if res.1.1 = 1 then _ else _) s ≤ _
      rw [ite_eq_left hf1, memoryCost_bind, clientState_lastSlotOfProg,
        memoryCost_bind, memoryCost_readQuotProg, clientState_readQuotProg, memoryCost_pure]
      have hc1 := hsb.2.1
      have hc2 := memoryCost_lastSlotOfProg_le U V w₀ n_max h_space (base, b) s
      omega
    · rw [hprep_eq]
      exact quotAt_lt base U w₀ n_max h_space s.mem _
    · rw [ite_eq_left hex, hprep_eq]
      exact ⟨hf1, hj_lt, hq_match, hphys_eq, rfl⟩
  · rw [ite_eq_right hex] at hres
    have hne1 : res.1.1 ≠ 1 := by omega
    have hprep_eq :
        (Memory.spec 0).clientResult s
          (deletePrepProg U V w₀ n_max h_space (((base, b), q_target), m)) =
        (((0, 0), 0), 0) := by
      unfold deletePrepProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientResult_bind, hsb.1]
      change (Memory.spec 0).clientResult s
        (if res.1.1 = 1 then _ else pure (((0, 0), 0), 0)) = _
      rw [ite_eq_right hne1]
      rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold deletePrepProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, hsb.1]
      change (Memory.spec 0).clientState s
        (if res.1.1 = 1 then _ else pure (((0, 0), 0), 0)) = s
      rw [ite_eq_right hne1]
      rfl
    · unfold deletePrepProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
      rw [memoryCost_bind, hsb.1]
      change memoryCost (searchBucketProg U V w₀ n_max h_space (((base, b), q_target), m)) s +
        memoryCost (if res.1.1 = 1 then _ else pure (((0, 0), 0), 0)) s ≤ _
      rw [ite_eq_right hne1, memoryCost_pure]
      have := hsb.2.1
      omega
    · rw [hprep_eq]
      exact Nat.two_pow_pos _
    · rw [ite_eq_right hex, hprep_eq]
      exact ⟨rfl, rfl⟩

/-! ## Section 2: `deleteSwapProg`, `deleteFoundProg`, and `deleteFinishProg` via `realize` -/

/-- Parameter-free swap helper for `delete` when `j_del < j_last`
(`d = (dp, ((((base, b), j_del), phys_del), (m_last, j_last)))`). -/
@[expose]
def deleteSwapGenProg
    (d : DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ))) : Memory.Prog Unit := do
  unlinkIfIndexedGenProg ((d.1, (d.2.1.1.1, d.2.2.1)), d.2.2.2)
  copyLastPayloadGenProg (d.1, (d.2.1.1.1, d.2.1.2))
  prependIfIndexedGenProg ((d.1, (d.2.1.1.1, d.2.2.1)), d.2.1.1.2)

/-- Swap helper for `delete` when `j_del < j_last`
(`d = ((((base, b), j_del), phys_del), (m_last, j_last))`):
unlinks `j_last` from `(b, m_last)` (if indexed), copies `(q_last, v_last)` into `phys_del`, and
prepends `j_del` to `(b, m_last)` (if indexed). -/
@[expose]
def deleteSwapProg (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : Memory.Prog Unit := do
  unlinkIfIndexedProg U V w n_max h_space ((d.1.1.1, d.2.1), d.2.2)
  copyLastPayloadProg U V w n_max h_space (d.1.1.1, d.1.2)
  prependIfIndexedProg U V w n_max h_space ((d.1.1.1, d.2.1), d.1.1.2)

@[simp]
theorem deleteSwapGenProg_mk (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) :
    deleteSwapGenProg (mkDictParams U V w n_max h_space, d) =
      deleteSwapProg U V w n_max h_space d := by
  simp only [deleteSwapGenProg, deleteSwapProg, unlinkIfIndexedGenProg_mk,
    copyLastPayloadGenProg_mk, prependIfIndexedGenProg_mk]

theorem memoryCost_deleteSwapProg_le (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (deleteSwapProg U V w n_max h_space d) s ≤ 50 := by
  unfold deleteSwapProg
  simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  have h1 := memoryCost_unlinkIfIndexedProg_le U V w n_max h_space ((d.1.1.1, d.2.1), d.2.2) s
  let s₁ := (Memory.spec 0).clientState s
    (unlinkIfIndexedProg U V w n_max h_space ((d.1.1.1, d.2.1), d.2.2))
  have h2 := memoryCost_copyLastPayloadProg_le U V w n_max h_space (d.1.1.1, d.1.2) s₁
  let s₂ := (Memory.spec 0).clientState s₁
    (copyLastPayloadProg U V w n_max h_space (d.1.1.1, d.1.2))
  have h3 := memoryCost_prependIfIndexedProg_le U V w n_max h_space ((d.1.1.1, d.2.1), d.1.1.2) s₂
  dsimp only [s₁, s₂] at h2 h3
  omega

/-- Precondition for `deleteSwapProg` in `Realizes`. -/
@[expose]
def DeleteSwapPre (U V w₀ n_max h_space w : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) d.1.1.1.1 ∧
  SlotStoreInv n_max (gmAt d.1.1.1.1 U V w₀ n_max h_space s.mem) ∧
  d.1.1.1.2 < numBuckets n_max ∧
  d.2.1 < numMicroPerBucket n_max ∧
  1 ≤ bCount n_max (gmAt d.1.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.1.2 ∧
  d.1.2 < n_max ∧
  d.2.2 < n_max ∧
  ∃ L : ℕ → ℕ → List ℕ,
    AllChainsValid n_max (lmAt d.1.1.1.1 U V w₀ n_max h_space s.mem) L ∧
    (d.2.2 < effBucketCap n_max → d.2.2 ∈ L d.1.1.1.2 d.2.1)

/-- Parameter-free precondition for `deleteSwapGenProg` in `Realizes`. -/
@[expose]
def DeleteSwapGenPre (w : ℕ)
    (d : DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ))) (s : Memory.State) : Prop :=
  let gm := gmAt d.2.1.1.1.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem
  let lm := lmAt d.2.1.1.1.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem
  DictEnvGen w d.1 d.2.1.1.1.1 ∧
  SlotStoreInv (dpNMax d.1) gm ∧
  d.2.1.1.1.2 < numBuckets (dpNMax d.1) ∧
  d.2.2.1 < numMicroPerBucket (dpNMax d.1) ∧
  1 ≤ bCount (dpNMax d.1) gm d.2.1.1.1.2 ∧
  d.2.1.2 < dpNMax d.1 ∧
  d.2.2.2 < dpNMax d.1 ∧
  ∃ L : ℕ → ℕ → List ℕ,
    AllChainsValid (dpNMax d.1) lm L ∧
    (d.2.2.2 < effBucketCap (dpNMax d.1) → d.2.2.2 ∈ L d.2.1.1.1.2 d.2.2.1)

@[simp]
theorem deleteSwapGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    DeleteSwapGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      DeleteSwapPre U V w₀ n_max h_space w d s := Iff.rfl

theorem realizes_deleteSwapGen :
    Realizes .exact deleteSwapGenProg
      (WordEncoding.encode (α := DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      DeleteSwapGenPre
      (fun _ _ => 0) := by
  have hu := realizes_unlinkIfIndexedGen
  have hc := realizes_copyLastPayloadGen
  have hp := realizes_prependIfIndexedGen
  realizeDictWith [deleteSwapGenPre_mk, DeleteSwapPre,
    unlinkIfIndexedGenPre_mk, UnlinkIfIndexedPre, unlinkIfIndexedGenProg_mk,
    copyLastPayloadGenPre_mk, CopyLastPayloadPre, copyLastPayloadGenProg_mk,
    prependIfIndexedGenPre_mk, PrependIfIndexedPre, prependIfIndexedGenProg_mk]
  · obtain ⟨L, hval, hmem_if⟩ := h.2.2.2.2.2.2.2
    refine ⟨h.1, h.2.2.1, h.2.2.2.1, fun hj_cap => ?_⟩
    have hmem := hmem_if hj_cap
    exact ⟨(hval.1 d.1.1.1.2 h.2.2.1 d.2.1 h.2.2.2.1).prev_le_cap hmem,
      (hval.1 d.1.1.1.2 h.2.2.1 d.2.1 h.2.2.2.1).next_le_cap hmem⟩
  · obtain ⟨L, hval, hmem_if⟩ := h.2.2.2.2.2.2.2
    have eff_u := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (m := d.2.1) (j_del := d.2.2)
      hw h.2.2.1 h.2.2.2.1 h.2.2.2.2.2.2.1 hval hmem_if
    refine ⟨h.1, ?_, h.2.2.1, ?_, h.2.2.2.2.2.1⟩
    · rw [eff_u.2.2.2.2.1]; exact h.2.1
    · rw [eff_u.2.2.2.2.1]; exact h.2.2.2.2.1
  · obtain ⟨L, hval, hmem_if⟩ := h.2.2.2.2.2.2.2
    have eff_u := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (m := d.2.1) (j_del := d.2.2)
      hw h.2.2.1 h.2.2.2.1 h.2.2.2.2.2.2.1 hval hmem_if
    let s₁ := (Memory.spec 0).clientState s
      (unlinkIfIndexedProg U V w₀ n_max h_space ((d.1.1.1, d.2.1), d.2.2))
    have hslot₁ : SlotStoreInv n_max (gmAt d.1.1.1.1 U V w₀ n_max h_space s₁.mem) := by
      rw [eff_u.2.2.2.2.1]; exact h.2.1
    have hbc₁ : 1 ≤ bCount n_max (gmAt d.1.1.1.1 U V w₀ n_max h_space s₁.mem) d.1.1.1.2 := by
      rw [eff_u.2.2.2.2.1]; exact h.2.2.2.2.1
    have eff_c := copyLastPayloadProg_effect (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (phys_del := d.1.2)
      hw hslot₁ h.2.2.1 hbc₁ h.2.2.2.2.2.1
    obtain ⟨L₁, hval₁, _⟩ := eff_u.2.2.2.2.2
    refine ⟨h.1, h.2.2.1, h.2.2.2.1, ?_⟩
    rw [eff_c.2.2.2.2.1]
    exact (hval₁.1 d.1.1.1.2 h.2.2.1 d.2.1 h.2.2.2.1).head_le_cap

/-- Parameter-free found-branch helper for `delete`
(`d = (dp, ((((base, b), j_del), phys_del), (m, m_last)))`). -/
@[expose]
def deleteFoundGenProg
    (d : DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ))) : Memory.Prog Unit := do
  unlinkIfIndexedGenProg ((d.1, (d.2.1.1.1, d.2.2.1)), d.2.1.1.2)
  let c_b ← readBucketCountGenProg (d.1, d.2.1.1.1)
  let j_last ← pure (c_b - 1)
  if d.2.1.1.2 < j_last then do
    deleteSwapGenProg (d.1, (d.2.1, (d.2.2.2, j_last)))
    popBackSlotGenProg (d.1, d.2.1.1.1)
  else
    popBackSlotGenProg (d.1, d.2.1.1.1)

/-- Found-branch helper for `delete` (`d = ((((base, b), j_del), phys_del), (m, m_last))`):
unlinks `j_del` from `(b, m)`, reads `c_b`, runs `deleteSwapProg` if `j_del < c_b - 1`, and
calls `popBackSlotProg`. -/
@[expose]
def deleteFoundProg (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : Memory.Prog Unit := do
  unlinkIfIndexedProg U V w n_max h_space ((d.1.1.1, d.2.1), d.1.1.2)
  let c_b ← readBucketCountProg U V w n_max h_space d.1.1.1
  let j_last ← pure (c_b - 1)
  if d.1.1.2 < j_last then do
    deleteSwapProg U V w n_max h_space (d.1, (d.2.2, j_last))
    popBackSlotProg U V w n_max h_space d.1.1.1
  else
    popBackSlotProg U V w n_max h_space d.1.1.1

@[simp]
theorem deleteFoundGenProg_mk (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) :
    deleteFoundGenProg (mkDictParams U V w n_max h_space, d) =
      deleteFoundProg U V w n_max h_space d := by
  simp only [deleteFoundGenProg, deleteFoundProg, unlinkIfIndexedGenProg_mk,
    readBucketCountGenProg_mk, deleteSwapGenProg_mk, popBackSlotGenProg_mk]

/-- Precondition for `deleteFoundProg` in `Realizes`. -/
@[expose]
def DeleteFoundPre (U V w₀ n_max h_space w : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  let base := d.1.1.1.1
  let b := d.1.1.1.2
  let j_del := d.1.1.2
  let phys_del := d.1.2
  let m := d.2.1
  let m_last := d.2.2
  let gm := gmAt base U V w₀ n_max h_space s.mem
  let lm := lmAt base U V w₀ n_max h_space s.mem
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  SlotStoreInv n_max gm ∧
  b < numBuckets n_max ∧
  m < numMicroPerBucket n_max ∧
  m_last < numMicroPerBucket n_max ∧
  j_del < bCount n_max gm b ∧
  phys_del < n_max ∧
  ∃ L : ℕ → ℕ → List ℕ,
    AllChainsValid n_max lm L ∧
    (j_del < effBucketCap n_max → j_del ∈ L b m) ∧
    (bCount n_max gm b - 1 < effBucketCap n_max → bCount n_max gm b - 1 ∈ L b m_last)

/-- Parameter-free precondition for `deleteFoundGenProg` in `Realizes`. -/
@[expose]
def DeleteFoundGenPre (w : ℕ)
    (d : DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ))) (s : Memory.State) : Prop :=
  let base := d.2.1.1.1.1
  let b := d.2.1.1.1.2
  let j_del := d.2.1.1.2
  let phys_del := d.2.1.2
  let m := d.2.2.1
  let m_last := d.2.2.2
  let gm := gmAt base (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem
  let lm := lmAt base (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem
  DictEnvGen w d.1 base ∧
  SlotStoreInv (dpNMax d.1) gm ∧
  b < numBuckets (dpNMax d.1) ∧
  m < numMicroPerBucket (dpNMax d.1) ∧
  m_last < numMicroPerBucket (dpNMax d.1) ∧
  j_del < bCount (dpNMax d.1) gm b ∧
  phys_del < dpNMax d.1 ∧
  ∃ L : ℕ → ℕ → List ℕ,
    AllChainsValid (dpNMax d.1) lm L ∧
    (j_del < effBucketCap (dpNMax d.1) → j_del ∈ L b m) ∧
    (bCount (dpNMax d.1) gm b - 1 < effBucketCap (dpNMax d.1) →
      bCount (dpNMax d.1) gm b - 1 ∈ L b m_last)

@[simp]
theorem deleteFoundGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    DeleteFoundGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      DeleteFoundPre U V w₀ n_max h_space w d s := Iff.rfl

theorem realizes_deleteFoundGen :
    Realizes .exact deleteFoundGenProg
      (WordEncoding.encode (α := DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      DeleteFoundGenPre
      (fun _ _ => 0) := by
  have hu := realizes_unlinkIfIndexedGen
  have hbc := realizes_readBucketCountGen
  have hsw := realizes_deleteSwapGen
  have hpop := realizes_popBackSlotGen
  realizeDictWith [deleteFoundGenPre_mk, DeleteFoundPre,
    unlinkIfIndexedGenPre_mk, UnlinkIfIndexedPre, unlinkIfIndexedGenProg_mk,
    deleteSwapGenPre_mk, DeleteSwapPre, deleteSwapGenProg_mk,
    popBackSlotGenPre_mk, PopBackSlotPre, popBackSlotGenProg_mk]
  · obtain ⟨L, hval, hmem_del, _⟩ := h.2.2.2.2.2.2.2
    refine ⟨h.1, h.2.2.1, h.2.2.2.1, fun hj_cap => ?_⟩
    have hmem := hmem_del hj_cap
    exact ⟨(hval.1 d.1.1.1.2 h.2.2.1 d.2.1 h.2.2.2.1).prev_le_cap hmem,
      (hval.1 d.1.1.1.2 h.2.2.1 d.2.1 h.2.2.2.1).next_le_cap hmem⟩
  · exact h.1
  · obtain ⟨L, hval, hmem_del, _⟩ := h.2.2.2.2.2.2.2
    have hj_n : d.1.1.2 < n_max :=
      lt_of_lt_of_le h.2.2.2.2.2.1 (bCount_le_n_max h.2.1 d.1.1.1.2)
    have eff_u := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (m := d.2.1) (j_del := d.1.1.2)
      hw h.2.2.1 h.2.2.2.1 hj_n hval hmem_del
    rw [eff_u.2.2.2.2.1]
    exact h.2.1
  · exact h.2.2.1
  · obtain ⟨L, hval, hmem_del, _⟩ := h.2.2.2.2.2.2.2
    have hj_n : d.1.1.2 < n_max :=
      lt_of_lt_of_le h.2.2.2.2.2.1 (bCount_le_n_max h.2.1 d.1.1.1.2)
    have eff_u := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (m := d.2.1) (j_del := d.1.1.2)
      hw h.2.2.1 h.2.2.2.1 hj_n hval hmem_del
    rw [clientResult_readBucketCountProg d.1.1.1 _ h.2.2.1, eff_u.2.2.2.2.1]
    have := h.2.2.2.2.2.1
    omega
  · obtain ⟨L, hval, hmem_del, hmem_last⟩ := h.2.2.2.2.2.2.2
    have hj_n : d.1.1.2 < n_max :=
      lt_of_lt_of_le h.2.2.2.2.2.1 (bCount_le_n_max h.2.1 d.1.1.1.2)
    have eff_u := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (m := d.2.1) (j_del := d.1.1.2)
      hw h.2.2.1 h.2.2.2.1 hj_n hval hmem_del
    rw [clientState_readBucketCountProg]
    rw [clientResult_readBucketCountProg d.1.1.1 _ h.2.2.1, eff_u.2.2.2.2.1] at hc ⊢
    obtain ⟨L₁, hval₁, hmem₁⟩ := eff_u.2.2.2.2.2
    have hbc_pos : 1 ≤ bCount n_max (gmAt d.1.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.1.2 := by
      have := h.2.2.2.2.2.1; omega
    have hj_last_n : bCount n_max (gmAt d.1.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.1.2 - 1 <
        n_max := by
      have := bCount_le_n_max h.2.1 d.1.1.1.2; omega
    refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1,
      hbc_pos, h.2.2.2.2.2.2.1, hj_last_n, L₁, hval₁,
      fun hj_cap => ?_⟩
    rw [hmem₁ d.1.1.1.2 h.2.2.1 d.2.2 h.2.2.2.2.1]
    exact ⟨hmem_last hj_cap, fun ⟨_, heq⟩ => by omega⟩
  · obtain ⟨L, hval, hmem_del, hmem_last⟩ := h.2.2.2.2.2.2.2
    have hj_n : d.1.1.2 < n_max :=
      lt_of_lt_of_le h.2.2.2.2.2.1 (bCount_le_n_max h.2.1 d.1.1.1.2)
    have eff_u := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (m := d.2.1) (j_del := d.1.1.2)
      hw h.2.2.1 h.2.2.2.1 hj_n hval hmem_del
    rw [clientState_readBucketCountProg]
    rw [clientResult_readBucketCountProg d.1.1.1 _ h.2.2.1, eff_u.2.2.2.2.1] at hc ⊢
    let j_last := bCount n_max (gmAt d.1.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.1.2 - 1
    let s₁ := (Memory.spec 0).clientState s
      (unlinkIfIndexedProg U V w₀ n_max h_space ((d.1.1.1, d.2.1), d.1.1.2))
    obtain ⟨L₁, hval₁, hmem₁⟩ := eff_u.2.2.2.2.2
    have hbc_pos : 1 ≤ bCount n_max (gmAt d.1.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.1.2 := by
      have := h.2.2.2.2.2.1; omega
    have hj_last_n : j_last < n_max := by
      have := bCount_le_n_max h.2.1 d.1.1.1.2; omega
    have eff_u2 := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (m := d.2.2) (j_del := j_last)
      (s := s₁) hw h.2.2.1 h.2.2.2.2.1 hj_last_n hval₁
      (fun hj_cap => (hmem₁ d.1.1.1.2 h.2.2.1 d.2.2 h.2.2.2.2.1 j_last).mpr
        ⟨hmem_last hj_cap, fun ⟨_, heq⟩ => by omega⟩)
    let s₂ := (Memory.spec 0).clientState s₁
      (unlinkIfIndexedProg U V w₀ n_max h_space ((d.1.1.1, d.2.2), j_last))
    have hslot₂ : SlotStoreInv n_max (gmAt d.1.1.1.1 U V w₀ n_max h_space s₂.mem) := by
      rw [eff_u2.2.2.2.2.1, eff_u.2.2.2.2.1]; exact h.2.1
    have hbc₂ : 1 ≤ bCount n_max (gmAt d.1.1.1.1 U V w₀ n_max h_space s₂.mem) d.1.1.1.2 := by
      rw [eff_u2.2.2.2.2.1, eff_u.2.2.2.2.1]; exact hbc_pos
    have eff_c := copyLastPayloadProg_effect (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (phys_del := d.1.2)
      hw hslot₂ h.2.2.1 hbc₂ h.2.2.2.2.2.2.1
    let s₃ := (Memory.spec 0).clientState s₂
      (copyLastPayloadProg U V w₀ n_max h_space (d.1.1.1, d.1.2))
    obtain ⟨L₂, hval₂, hmem₂⟩ := eff_u2.2.2.2.2.2
    have hval₃ : AllChainsValid n_max (lmAt d.1.1.1.1 U V w₀ n_max h_space s₃.mem) L₂ :=
      hval₂.of_lm_eq eff_c.2.2.2.2.1
    have hj_not₂ : ∀ m' < numMicroPerBucket n_max, d.1.1.2 ∉ L₂ d.1.1.1.2 m' := by
      intro m' hm' hj_in
      have hj_in₁ := ((hmem₂ d.1.1.1.2 h.2.2.1 m' hm' d.1.1.2).mp hj_in).1
      exact ((hmem₁ d.1.1.1.2 h.2.2.1 m' hm' d.1.1.2).mp hj_in₁).2 ⟨rfl, rfl⟩
    have eff_pr := prependIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (m := d.2.2) (j_new := d.1.1.2)
      (s := s₃) hw h.2.2.1 h.2.2.2.2.1 hj_n hval₃ hj_not₂
    have hst_sw : (Memory.spec 0).clientState s₁
        (deleteSwapProg U V w₀ n_max h_space (d.1, (d.2.2, j_last))) =
        (Memory.spec 0).clientState s₃
          (prependIfIndexedProg U V w₀ n_max h_space ((d.1.1.1, d.2.2), d.1.1.2)) := by
      unfold deleteSwapProg
      repeat rw [StateTransitionSpec.clientState_bind]
    have hgm_sw : gmAt d.1.1.1.1 U V w₀ n_max h_space
        ((Memory.spec 0).clientState s₁
          (deleteSwapProg U V w₀ n_max h_space (d.1, (d.2.2, j_last)))).mem =
        gmAt d.1.1.1.1 U V w₀ n_max h_space s.mem := by
      rw [hst_sw, eff_pr.2.2.2.2.1, eff_c.2.2.2.2.2, eff_u2.2.2.2.2.1, eff_u.2.2.2.2.1]
    refine ⟨h.1, ?_, h.2.2.1, ?_⟩
    · rw [hgm_sw]; exact h.2.1
    · rw [hgm_sw]; exact hbc_pos
  · obtain ⟨L, hval, hmem_del, _⟩ := h.2.2.2.2.2.2.2
    have hj_n : d.1.1.2 < n_max :=
      lt_of_lt_of_le h.2.2.2.2.2.1 (bCount_le_n_max h.2.1 d.1.1.1.2)
    have eff_u := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (m := d.2.1) (j_del := d.1.1.2)
      hw h.2.2.1 h.2.2.2.1 hj_n hval hmem_del
    rw [clientState_readBucketCountProg]
    have hbc_pos : 1 ≤ bCount n_max (gmAt d.1.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.1.2 := by
      have := h.2.2.2.2.2.1; omega
    refine ⟨h.1, ?_, h.2.2.1, ?_⟩
    · rw [eff_u.2.2.2.2.1]; exact h.2.1
    · rw [eff_u.2.2.2.2.1]; exact hbc_pos

/-- Parameter-free Phase 2 of `delete`
(`d = (dp, (((((base, b), (found, j_del)), phys_del), m), m_last))`). -/
@[expose]
def deleteFinishGenProg
    (d : DictParams × (((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ)) : Memory.Prog Unit := do
  let z1 ← pure 1
  if d.2.1.1.1.2.1 = z1 then
    deleteFoundGenProg
      (d.1, (((d.2.1.1.1.1, d.2.1.1.1.2.2), d.2.1.1.2), (d.2.1.2, d.2.2)))
  else
    pure ()

/-- Phase 2 of `delete` (`d = ((((base, b), (found, j_del)), phys_del), m), m_last`):
if `found = 1`, calls `deleteFoundProg`; otherwise returns `()`. -/
@[expose]
def deleteFinishProg (U V w n_max h_space : ℕ)
    (d : ((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) : Memory.Prog Unit := do
  let z1 ← pure 1
  if d.1.1.1.2.1 = z1 then
    deleteFoundProg U V w n_max h_space
      (((d.1.1.1.1, d.1.1.1.2.2), d.1.1.2), (d.1.2, d.2))
  else
    pure ()

@[simp]
theorem deleteFinishGenProg_mk (U V w n_max h_space : ℕ)
    (d : ((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) :
    deleteFinishGenProg (mkDictParams U V w n_max h_space, d) =
      deleteFinishProg U V w n_max h_space d := by
  simp only [deleteFinishGenProg, deleteFinishProg, deleteFoundGenProg_mk]

/-- Precondition for `deleteFinishProg` in `Realizes`. -/
@[expose]
def DeleteFinishPre (U V w₀ n_max h_space w : ℕ)
    (d : ((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) d.1.1.1.1.1 ∧
  (d.1.1.1.2.1 = 1 →
    DeleteFoundPre U V w₀ n_max h_space w
      (((d.1.1.1.1, d.1.1.1.2.2), d.1.1.2), (d.1.2, d.2)) s)

/-- Parameter-free precondition for `deleteFinishGenProg` in `Realizes`. -/
@[expose]
def DeleteFinishGenPre (w : ℕ)
    (d : DictParams × (((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w d.1 d.2.1.1.1.1.1 ∧
  (d.2.1.1.1.2.1 = 1 →
    DeleteFoundGenPre w
      (d.1, (((d.2.1.1.1.1, d.2.1.1.1.2.2), d.2.1.1.2), (d.2.1.2, d.2.2))) s)

@[simp]
theorem deleteFinishGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d : ((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    DeleteFinishGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      DeleteFinishPre U V w₀ n_max h_space w d s := Iff.rfl

theorem realizes_deleteFinishGen :
    Realizes .exact deleteFinishGenProg
      (WordEncoding.encode (α := DictParams × (((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      DeleteFinishGenPre
      (fun _ _ => 0) := by
  have hdf := realizes_deleteFoundGen
  realizeDictWith [deleteFinishGenPre_mk, DeleteFinishPre,
    deleteFoundGenPre_mk, DeleteFoundPre, deleteFoundGenProg_mk]
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact h.2 hc

/-- Pure state effect, `BucketStateInv` preservation, and amortized `memoryCost` bound of
`deleteFinishProg` following `deletePrepProg` under `BucketStateInv`. -/
theorem deleteFinishProg_bucket_spec {U V w₀ n_max h_space w base b q_target m : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s : Memory.State}
    (hw : 0 < w₀)
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hb : b < numBuckets n_max) (hm_eq : m = mOf q_target)
    (hm_lt : m < numMicroPerBucket n_max)
    (hmOf_lt : ∀ q < 2 ^ quotientBits U n_max, mOf q < numMicroPerBucket n_max) :
    let gm₀ := gmAt base U V w₀ n_max h_space s.mem
    let prep := (Memory.spec 0).clientResult s
      (deletePrepProg U V w₀ n_max h_space (((base, b), q_target), m))
    let m_last := mOf prep.2
    let d_fin := (((((base, b), prep.1.1), prep.1.2), m), m_last)
    let s' := (Memory.spec 0).clientState s (deleteFinishProg U V w₀ n_max h_space d_fin)
    let gm' := gmAt base U V w₀ n_max h_space s'.mem
    let B' := Function.update B b (Function.update (B b) q_target none)
    DeleteFinishPre U V w₀ n_max h_space w d_fin s ∧
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w₀ n_max h_space) → s'.mem a = s.mem a) ∧
    (∃ L', BucketStateInv U V w₀ n_max h_space base mOf L' B' s') ∧
    totalSlots n_max gm' =
      (if (B b q_target).isSome then totalSlots n_max gm₀ - 1 else totalSlots n_max gm₀) ∧
    memoryCost (deleteFinishProg U V w₀ n_max h_space d_fin) s + 66 * slotPotential n_max gm' ≤
      66 * slotPotential n_max gm₀ + 240 := by
  intro gm₀ prep m_last d_fin s' gm' B'
  have hprep := deletePrepProg_bucket_spec hinv henv hb hm_eq hm_lt (q_target := q_target)
  change
    (Memory.spec 0).clientState s
      (deletePrepProg U V w₀ n_max h_space (((base, b), q_target), m)) = s ∧
    memoryCost (deletePrepProg U V w₀ n_max h_space (((base, b), q_target), m)) s ≤
      16 + 8 * (L b m).length + 6 * (bCount n_max gm₀ b - effBucketCap n_max) ∧
    prep.2 < 2 ^ quotientBits U n_max ∧
    (if ∃ j < bCount n_max gm₀ b,
         quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm₀ b j) = q_target then
       prep.1.1.1 = 1 ∧
       prep.1.1.2 < bCount n_max gm₀ b ∧
       quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm₀ b prep.1.1.2) = q_target ∧
       prep.1.2 = slotOf n_max gm₀ b prep.1.1.2 ∧
       prep.2 = quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm₀ b (bCount n_max gm₀ b - 1))
     else
       prep.1.1.1 = 0 ∧ prep.2 = 0) at hprep
  have hm_last_lt : m_last < numMicroPerBucket n_max := hmOf_lt prep.2 hprep.2.2.1
  have hprep_branch := hprep.2.2.2
  by_cases hex : ∃ j < bCount n_max gm₀ b,
      quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm₀ b j) = q_target
  · rw [ite_eq_left hex] at hprep_branch
    rcases hprep_branch with ⟨hf1, hj_del_lt, hq_del, hphys_del_eq, hq_last_eq⟩
    have hsome : (B b q_target).isSome := (hinv.hmap_dom b hb q_target).mpr hex
    let j_del := prep.1.1.2
    let phys_del := prep.1.2
    let j_last := bCount n_max gm₀ b - 1
    change phys_del = slotOf n_max gm₀ b j_del at hphys_del_eq
    have hj_last_lt : j_last < bCount n_max gm₀ b := by omega
    have hbc_pos : 1 ≤ bCount n_max gm₀ b := by omega
    have hphys_del_lt : phys_del < n_max := by
      rw [hphys_del_eq]
      exact (slotOf_lt_and_injective hinv.hslot).1 b hb j_del hj_del_lt
    have hj_del_n : j_del < n_max :=
      lt_of_lt_of_le hj_del_lt (bCount_le_n_max hinv.hslot b)
    have hj_last_n : j_last < n_max :=
      lt_of_lt_of_le hj_last_lt (bCount_le_n_max hinv.hslot b)
    have hmem_del : j_del < effBucketCap n_max → j_del ∈ L b m := fun hj_cap =>
      (hinv.hchain_mem b hb m hm_lt j_del).mpr ⟨hj_del_lt, hj_cap, by rw [hq_del, hm_eq]⟩
    have hmem_last : j_last < effBucketCap n_max → j_last ∈ L b m_last := fun hj_cap =>
      (hinv.hchain_mem b hb m_last hm_last_lt j_last).mpr
        ⟨hj_last_lt, hj_cap, by dsimp only [m_last]; rw [hq_last_eq]⟩
    have hpre_found : DeleteFoundPre U V w₀ n_max h_space w
        ((((base, b), j_del), phys_del), (m, m_last)) s :=
      ⟨henv, hinv.hslot, hb, hm_lt, hm_last_lt, hj_del_lt, hphys_del_lt,
        L, hinv.hchains, hmem_del, hmem_last⟩
    have hpre_fin : DeleteFinishPre U V w₀ n_max h_space w d_fin s :=
      ⟨henv, fun _ => hpre_found⟩
    -- Step 1: unlinkIfIndexedProg j_del from (b, m)
    let s₁ := (Memory.spec 0).clientState s
      (unlinkIfIndexedProg U V w₀ n_max h_space (((base, b), m), j_del))
    have eff_u1 := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := base) (b := b) (m := m) (j_del := j_del)
      hw hb hm_lt hj_del_n hinv.hchains hmem_del
    rcases eff_u1 with ⟨hf_u1, hout_u1, hq_u1, hv_u1, hgm_u1, L₁, hval₁, hmem₁⟩
    -- Unify the two subcases (j_del < j_last vs j_del = j_last) via idxMap
    let idxMap (j : ℕ) : ℕ := if j = j_del then j_last else j
    have h_unified :
        s'.frontier = s.frontier ∧
        (∀ a, ¬(base + offQuot h_space ≤ a ∧
            a < base + totalSpace U V w₀ n_max h_space) → s'.mem a = s.mem a) ∧
        SlotStoreInv n_max gm' ∧
        totalSlots n_max gm' + 1 = totalSlots n_max gm₀ ∧
        bCount n_max gm' b = j_last ∧
        (∀ b' < numBuckets n_max, b' ≠ b → bCount n_max gm' b' = bCount n_max gm₀ b') ∧
        (∀ b' < numBuckets n_max, b' ≠ b → ∀ j < bCount n_max gm₀ b',
          quotAt base U w₀ n_max h_space s'.mem (slotOf n_max gm' b' j) =
            quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm₀ b' j) ∧
          valAt base U V w₀ n_max h_space s'.mem (slotOf n_max gm' b' j) =
            valAt base U V w₀ n_max h_space s.mem (slotOf n_max gm₀ b' j)) ∧
        (∀ j < j_last,
          quotAt base U w₀ n_max h_space s'.mem (slotOf n_max gm' b j) =
            quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm₀ b (idxMap j)) ∧
          valAt base U V w₀ n_max h_space s'.mem (slotOf n_max gm' b j) =
            valAt base U V w₀ n_max h_space s.mem (slotOf n_max gm₀ b (idxMap j))) ∧
        (∃ L', AllChainsValid n_max (lmAt base U V w₀ n_max h_space s'.mem) L' ∧
          (∀ b' < numBuckets n_max, b' ≠ b → ∀ m' < numMicroPerBucket n_max, ∀ j,
            j ∈ L' b' m' ↔ j ∈ L b' m') ∧
          (∀ m' < numMicroPerBucket n_max, ∀ j,
            j ∈ L' b m' ↔
              j < j_last ∧ j < effBucketCap n_max ∧
              mOf (quotAt base U w₀ n_max h_space s.mem
                (slotOf n_max gm₀ b (idxMap j))) = m')) ∧
        memoryCost (deleteFinishProg U V w₀ n_max h_space d_fin) s + 66 * slotPotential n_max gm' ≤
          66 * slotPotential n_max gm₀ + 240 := by
      by_cases hlt : j_del < j_last
      · -- Subcase: j_del < j_last (swap occurs)
        have hmem_last₁ : j_last < effBucketCap n_max → j_last ∈ L₁ b m_last := by
          intro hj_cap
          rw [hmem₁ b hb m_last hm_last_lt j_last]
          exact ⟨hmem_last hj_cap, fun ⟨_, heq⟩ => by omega⟩
        let s₂ := (Memory.spec 0).clientState s₁
          (unlinkIfIndexedProg U V w₀ n_max h_space (((base, b), m_last), j_last))
        have eff_u2 := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀)
          (n_max := n_max) (h_space := h_space) (base := base) (b := b) (m := m_last)
          (j_del := j_last) (s := s₁) hw hb hm_last_lt hj_last_n hval₁ hmem_last₁
        rcases eff_u2 with ⟨hf_u2, hout_u2, hq_u2, hv_u2, hgm_u2, L₂, hval₂, hmem₂⟩
        have hslot₂ : SlotStoreInv n_max (gmAt base U V w₀ n_max h_space s₂.mem) := by
          rw [hgm_u2, hgm_u1]; exact hinv.hslot
        have hbc₂ : 1 ≤ bCount n_max (gmAt base U V w₀ n_max h_space s₂.mem) b := by
          rw [hgm_u2, hgm_u1]; exact hbc_pos
        let s₃ := (Memory.spec 0).clientState s₂
          (copyLastPayloadProg U V w₀ n_max h_space ((base, b), phys_del))
        have eff_c := copyLastPayloadProg_effect (U := U) (V := V) (w := w₀) (n_max := n_max)
          (h_space := h_space) (base := base) (b := b) (phys_del := phys_del) (s := s₂)
          hw hslot₂ hb hbc₂ hphys_del_lt
        rcases eff_c with ⟨hf_c, hout_c, hq_c, hv_c, hlm_c, hgm_c⟩
        have hval₃ : AllChainsValid n_max (lmAt base U V w₀ n_max h_space s₃.mem) L₂ :=
          hval₂.of_lm_eq hlm_c
        have hj_not₂ : ∀ m' < numMicroPerBucket n_max, j_del ∉ L₂ b m' := by
          intro m' hm' hj_in
          have hj_in₁ := ((hmem₂ b hb m' hm' j_del).mp hj_in).1
          exact ((hmem₁ b hb m' hm' j_del).mp hj_in₁).2 ⟨rfl, rfl⟩
        let s₄ := (Memory.spec 0).clientState s₃
          (prependIfIndexedProg U V w₀ n_max h_space (((base, b), m_last), j_del))
        have eff_pr := prependIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀)
          (n_max := n_max) (h_space := h_space) (base := base) (b := b) (m := m_last)
          (j_new := j_del) (s := s₃) hw hb hm_last_lt hj_del_n hval₃ hj_not₂
        rcases eff_pr with ⟨hf_pr, hout_pr, hq_pr, hv_pr, hgm_pr, L₃, hval₄, hmem₃⟩
        have hgm₄_eq : gmAt base U V w₀ n_max h_space s₄.mem = gm₀ := by
          rw [hgm_pr, hgm_c, hgm_u2, hgm_u1]
        have hslot₄ : SlotStoreInv n_max (gmAt base U V w₀ n_max h_space s₄.mem) := by
          rw [hgm₄_eq]; exact hinv.hslot
        have hbc₄ : 1 ≤ bCount n_max (gmAt base U V w₀ n_max h_space s₄.mem) b := by
          rw [hgm₄_eq]; exact hbc_pos
        have eff_pop := popBackSlotProg_effect (U := U) (V := V) (w := w₀) (n_max := n_max)
          (h_space := h_space) (base := base) (b := b) hw s₄ hslot₄ hb hbc₄
        rcases eff_pop with ⟨hf_pop, hout_pop, hlm_pop, hslot_pop, htot_pop, hbc_b_pop,
          hbc_other_pop, hold_pop, hcost_pop⟩
        have hs'_eq : s' = (Memory.spec 0).clientState s₄
            (popBackSlotProg U V w₀ n_max h_space (base, b)) := by
          change (Memory.spec 0).clientState s (deleteFinishProg U V w₀ n_max h_space d_fin) = _
          unfold deleteFinishProg deleteFoundProg deleteSwapProg
          simp only [pure_bind, d_fin]
          rw [ite_eq_left hf1, StateTransitionSpec.clientState_bind,
            StateTransitionSpec.clientState_bind, clientState_readBucketCountProg,
            clientResult_readBucketCountProg (base, b) s₁ hb, hgm_u1,
            ite_eq_left hlt]
          repeat rw [StateTransitionSpec.clientState_bind]
        have hcost_fin : memoryCost (deleteFinishProg U V w₀ n_max h_space d_fin) s ≤
            66 + memoryCost (popBackSlotProg U V w₀ n_max h_space (base, b)) s₄ := by
          unfold deleteFinishProg deleteFoundProg
          simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, d_fin]
          rw [ite_eq_left hf1, memoryCost_bind, memoryCost_bind,
            clientState_readBucketCountProg, clientResult_readBucketCountProg (base, b) s₁ hb,
            hgm_u1, ite_eq_left hlt, memoryCost_bind]
          have hc_u1 := memoryCost_unlinkIfIndexedProg_le U V w₀ n_max h_space
            (((base, b), m), j_del) s
          have hc_bc := memoryCost_readBucketCountProg_le (U := U) (V := V) (w := w₀)
            (n_max := n_max) (h_space := h_space) (base, b) s₁
          have hc_sw := memoryCost_deleteSwapProg_le U V w₀ n_max h_space
            ((((base, b), j_del), phys_del), (m_last, j_last)) s₁
          have hst_sw : (Memory.spec 0).clientState s₁
              (deleteSwapProg U V w₀ n_max h_space
                ((((base, b), j_del), phys_del), (m_last, j_last))) = s₄ := by
            unfold deleteSwapProg
            repeat rw [StateTransitionSpec.clientState_bind]
          rw [hst_sw]
          dsimp only [s₁, j_del, phys_del, j_last, gm₀] at hc_u1 hc_bc hc_sw ⊢
          omega
        rw [← hs'_eq] at hf_pop hout_pop hlm_pop hslot_pop htot_pop
        rw [← hs'_eq] at hbc_b_pop hbc_other_pop hold_pop hcost_pop
        rw [hgm₄_eq] at htot_pop hbc_b_pop hbc_other_pop hold_pop hcost_pop
        change SlotStoreInv n_max gm' at hslot_pop
        change totalSlots n_max gm' + 1 = totalSlots n_max gm₀ at htot_pop
        change bCount n_max gm' b = j_last at hbc_b_pop
        change ∀ b' < numBuckets n_max, b' ≠ b → bCount n_max gm' b' = bCount n_max gm₀ b'
          at hbc_other_pop
        have hq₄ : quotAt base U w₀ n_max h_space s₄.mem =
            Function.update (quotAt base U w₀ n_max h_space s.mem) phys_del
              (quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm₀ b j_last)) := by
          rw [hq_pr, hq_c, hgm_u2, hgm_u1, hq_u2, hq_u1]
        have hv₄ : valAt base U V w₀ n_max h_space s₄.mem =
            Function.update (valAt base U V w₀ n_max h_space s.mem) phys_del
              (valAt base U V w₀ n_max h_space s.mem (slotOf n_max gm₀ b j_last)) := by
          rw [hv_pr, hv_c, hgm_u2, hgm_u1, hv_u2, hv_u1]
        refine ⟨by rw [hf_pop, hf_pr, hf_c, hf_u2, hf_u1],
          fun a ha => by
            have ha_lm : ¬(base + offLM U V w₀ n_max h_space ≤ a ∧
                a < base + offGM U V w₀ n_max h_space) := by
              dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega
            rw [hout_pop a ha, hout_pr a ha_lm, hout_c a ha, hout_u2 a ha_lm, hout_u1 a ha_lm],
          hslot_pop, htot_pop, hbc_b_pop, hbc_other_pop,
          fun b' hb' hne j hj => ?_,
          fun j hj => ?_,
          ⟨L₃, hval₄.of_lm_eq hlm_pop, fun b' hb' hne m' hm' j => ?_, fun m' hm' j => ?_⟩,
          by dsimp only [gm₀, gm'] at hcost_pop ⊢; omega⟩
        · have hj' : j < bCount n_max gm' b' := by rw [hbc_other_pop b' hb' hne]; exact hj
          have hslot_ne : slotOf n_max gm₀ b' j ≠ phys_del := by
            rw [hphys_del_eq]
            intro heq
            exact hne
              ((slotOf_lt_and_injective hinv.hslot).2 b' hb' j hj b hb j_del hj_del_lt heq).1
          rw [(hold_pop b' hb' j hj').1, (hold_pop b' hb' j hj').2, hq₄, hv₄,
            Function.update_of_ne hslot_ne, Function.update_of_ne hslot_ne]
          exact ⟨rfl, rfl⟩
        · have hj' : j < bCount n_max gm' b := by rw [hbc_b_pop]; exact hj
          rw [(hold_pop b hb j hj').1, (hold_pop b hb j hj').2, hq₄, hv₄]
          dsimp only [idxMap]
          by_cases hjeq : j = j_del
          · subst hjeq
            rw [ite_eq_left rfl, ← hphys_del_eq, Function.update_self, Function.update_self]
            exact ⟨rfl, rfl⟩
          · rw [ite_eq_right hjeq]
            have hj_lt0 : j < bCount n_max gm₀ b := by omega
            have hslot_ne : slotOf n_max gm₀ b j ≠ phys_del := by
              rw [hphys_del_eq]
              intro heq
              exact hjeq
                ((slotOf_lt_and_injective hinv.hslot).2 b hb j hj_lt0 b hb j_del hj_del_lt heq).2
            rw [Function.update_of_ne hslot_ne, Function.update_of_ne hslot_ne]
            exact ⟨rfl, rfl⟩
        · rw [hmem₃ b' hb' m' hm' j, hmem₂ b' hb' m' hm' j, hmem₁ b' hb' m' hm' j]
          constructor
          · rintro (⟨⟨hj_in, _⟩, _⟩ | ⟨h_eq, _⟩)
            · exact hj_in
            · exact False.elim (hne h_eq)
          · intro hj_in
            exact Or.inl ⟨⟨hj_in, fun ⟨h_eq, _⟩ => hne h_eq⟩, fun ⟨h_eq, _⟩ => hne h_eq⟩
        · rw [hmem₃ b hb m' hm' j, hmem₂ b hb m' hm' j, hmem₁ b hb m' hm' j,
            hinv.hchain_mem b hb m' hm' j]
          dsimp only [idxMap]
          by_cases hjeq : j = j_del
          · subst hjeq
            rw [ite_eq_left rfl]
            have hm_last_eq : mOf (quotAt base U w₀ n_max h_space s.mem
                (slotOf n_max gm₀ b j_last)) = m_last := by
              dsimp only [m_last]; rw [hq_last_eq]
            constructor
            · rintro (⟨⟨_, hne⟩, _⟩ | ⟨_, rfl, _, hcap'⟩)
              · exact False.elim (hne ⟨rfl, rfl⟩)
              · exact ⟨hlt, hcap', hm_last_eq⟩
            · rintro ⟨_, hcap', hm_eq'⟩
              exact Or.inr ⟨rfl, hm_eq'.symm.trans hm_last_eq, rfl, hcap'⟩
          · rw [ite_eq_right hjeq]
            constructor
            · rintro (⟨⟨⟨hj_bc, hj_cap, hm_j⟩, _⟩, hne_last⟩ | ⟨_, _, h_eq, _⟩)
              · have hj_ne_last : j ≠ j_last := fun heq => hne_last ⟨rfl, heq⟩
                exact ⟨by dsimp only [j_last, gm₀] at hj_bc hj_ne_last ⊢; omega, hj_cap, hm_j⟩
              · exact False.elim (hjeq h_eq)
            · rintro ⟨hj_lt_last, hj_cap, hm_j⟩
              refine Or.inl ⟨⟨⟨by dsimp only [j_last, gm₀] at hj_lt_last ⊢; omega, hj_cap, hm_j⟩,
                fun ⟨_, h_eq⟩ => hjeq h_eq⟩,
                fun ⟨_, h_eq⟩ => by omega⟩
      · -- Subcase: j_del = j_last (no swap)
        have hjeq_last : j_del = j_last := by omega
        have hidx_id : ∀ j < j_last, idxMap j = j := by
          intro j hj
          dsimp only [idxMap]
          rw [ite_eq_right (by omega)]
        have hslot₁ : SlotStoreInv n_max (gmAt base U V w₀ n_max h_space s₁.mem) := by
          rw [hgm_u1]; exact hinv.hslot
        have hbc₁ : 1 ≤ bCount n_max (gmAt base U V w₀ n_max h_space s₁.mem) b := by
          rw [hgm_u1]; exact hbc_pos
        have eff_pop := popBackSlotProg_effect (U := U) (V := V) (w := w₀) (n_max := n_max)
          (h_space := h_space) (base := base) (b := b) hw s₁ hslot₁ hb hbc₁
        rcases eff_pop with ⟨hf_pop, hout_pop, hlm_pop, hslot_pop, htot_pop, hbc_b_pop,
          hbc_other_pop, hold_pop, hcost_pop⟩
        have hs'_eq : s' = (Memory.spec 0).clientState s₁
            (popBackSlotProg U V w₀ n_max h_space (base, b)) := by
          change (Memory.spec 0).clientState s (deleteFinishProg U V w₀ n_max h_space d_fin) = _
          unfold deleteFinishProg deleteFoundProg
          simp only [pure_bind, d_fin]
          rw [ite_eq_left hf1, StateTransitionSpec.clientState_bind,
            StateTransitionSpec.clientState_bind, clientState_readBucketCountProg,
            clientResult_readBucketCountProg (base, b) s₁ hb, hgm_u1,
            ite_eq_right hlt]
        have hcost_fin : memoryCost (deleteFinishProg U V w₀ n_max h_space d_fin) s ≤
            16 + memoryCost (popBackSlotProg U V w₀ n_max h_space (base, b)) s₁ := by
          unfold deleteFinishProg deleteFoundProg
          simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, d_fin]
          rw [ite_eq_left hf1, memoryCost_bind, memoryCost_bind,
            clientState_readBucketCountProg, clientResult_readBucketCountProg (base, b) s₁ hb,
            hgm_u1, ite_eq_right hlt]
          have hc_u1 := memoryCost_unlinkIfIndexedProg_le U V w₀ n_max h_space
            (((base, b), m), j_del) s
          have hc_bc := memoryCost_readBucketCountProg_le (U := U) (V := V) (w := w₀)
            (n_max := n_max) (h_space := h_space) (base, b) s₁
          dsimp only [s₁, j_del] at hc_u1 hc_bc ⊢
          omega
        rw [← hs'_eq] at hf_pop hout_pop hlm_pop hslot_pop htot_pop
        rw [← hs'_eq] at hbc_b_pop hbc_other_pop hold_pop hcost_pop
        rw [hgm_u1] at htot_pop hbc_b_pop hbc_other_pop hold_pop hcost_pop
        change SlotStoreInv n_max gm' at hslot_pop
        change totalSlots n_max gm' + 1 = totalSlots n_max gm₀ at htot_pop
        change bCount n_max gm' b = j_last at hbc_b_pop
        change ∀ b' < numBuckets n_max, b' ≠ b → bCount n_max gm' b' = bCount n_max gm₀ b'
          at hbc_other_pop
        refine ⟨by rw [hf_pop, hf_u1],
          fun a ha => by
            have ha_lm : ¬(base + offLM U V w₀ n_max h_space ≤ a ∧
                a < base + offGM U V w₀ n_max h_space) := by
              dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega
            rw [hout_pop a ha, hout_u1 a ha_lm],
          hslot_pop, htot_pop, hbc_b_pop, hbc_other_pop,
          fun b' hb' hne j hj => ?_,
          fun j hj => ?_,
          ⟨L₁, hval₁.of_lm_eq hlm_pop, fun b' hb' hne m' hm' j => ?_, fun m' hm' j => ?_⟩,
          by dsimp only [gm₀, gm'] at hcost_pop ⊢; omega⟩
        · have hj' : j < bCount n_max gm' b' := by rw [hbc_other_pop b' hb' hne]; exact hj
          rw [(hold_pop b' hb' j hj').1, (hold_pop b' hb' j hj').2, hq_u1, hv_u1]
          exact ⟨rfl, rfl⟩
        · have hj' : j < bCount n_max gm' b := by rw [hbc_b_pop]; exact hj
          rw [hidx_id j hj, (hold_pop b hb j hj').1, (hold_pop b hb j hj').2, hq_u1, hv_u1]
          exact ⟨rfl, rfl⟩
        · rw [hmem₁ b' hb' m' hm' j]
          exact ⟨And.left, fun hj_in => ⟨hj_in, fun ⟨h_eq, _⟩ => hne h_eq⟩⟩
        · rw [hmem₁ b hb m' hm' j, hinv.hchain_mem b hb m' hm' j]
          constructor
          · rintro ⟨⟨hj_bc, hj_cap, hm_j⟩, hne_del⟩
            have hj_ne : j ≠ j_last := by rw [← hjeq_last]; exact fun heq => hne_del ⟨rfl, heq⟩
            have hj_lt_last : j < j_last := by dsimp only [j_last, gm₀] at hj_bc hj_ne ⊢; omega
            rw [hidx_id j hj_lt_last]
            exact ⟨hj_lt_last, hj_cap, hm_j⟩
          · rintro ⟨hj_lt_last, hj_cap, hm_j⟩
            rw [hidx_id j hj_lt_last] at hm_j
            exact ⟨⟨by dsimp only [j_last, gm₀] at hj_lt_last ⊢; omega, hj_cap, hm_j⟩,
              fun ⟨_, h_eq⟩ => by
                dsimp only [j_del, j_last, gm₀] at hj_lt_last hjeq_last h_eq ⊢; omega⟩
    -- Now assemble the theorem from `h_unified`
    rcases h_unified with ⟨hf', hout', hslot', htot', hbc_b', hbc_other', hold_other', hold_b',
      ⟨L', hchains', hmem_other', hmem_b'⟩, hcost'⟩
    have hidx_lt : ∀ j < j_last, idxMap j < bCount n_max gm₀ b ∧ idxMap j ≠ j_del := by
      intro j hj
      dsimp only [idxMap]
      split_ifs with hjeq
      · subst hjeq; exact ⟨hj_last_lt, by omega⟩
      · exact ⟨by omega, hjeq⟩
    have hidx_inj : ∀ j₁ < j_last, ∀ j₂ < j_last, idxMap j₁ = idxMap j₂ → j₁ = j₂ := by
      intro j₁ hj₁ j₂ hj₂ heq
      dsimp only [idxMap] at heq
      split_ifs at heq with h1 h2 h2 <;> omega
    refine ⟨hpre_fin, hf', hout', ⟨L', ?_⟩,
      by rw [ite_eq_left hsome]; omega,
      hcost'⟩
    refine ⟨hslot', hchains',
      fun b' hb' m' hm' j => ?_,
      fun b' hb' j₁ hj₁ j₂ hj₂ hq_eq => ?_,
      fun b' hb' j hj => ?_,
      fun b' hb' q => ?_⟩
    · by_cases hbeq : b' = b
      · subst hbeq
        rw [hmem_b' m' hm' j]
        change _ ↔ j < bCount n_max gm' b' ∧ _
        rw [hbc_b']
        constructor
        · rintro ⟨hj_lt, hj_cap, hm_j⟩
          rw [(hold_b' j hj_lt).1]
          exact ⟨hj_lt, hj_cap, hm_j⟩
        · rintro ⟨hj_lt, hj_cap, hm_j⟩
          rw [(hold_b' j hj_lt).1] at hm_j
          exact ⟨hj_lt, hj_cap, hm_j⟩
      · rw [hmem_other' b' hb' hbeq m' hm' j, hinv.hchain_mem b' hb' m' hm' j]
        change _ ↔ j < bCount n_max gm' b' ∧ _
        rw [hbc_other' b' hb' hbeq]
        constructor
        · rintro ⟨hj_lt, hj_cap, hm_j⟩
          rw [(hold_other' b' hb' hbeq j hj_lt).1]
          exact ⟨hj_lt, hj_cap, hm_j⟩
        · rintro ⟨hj_lt, hj_cap, hm_j⟩
          rw [(hold_other' b' hb' hbeq j hj_lt).1] at hm_j
          exact ⟨hj_lt, hj_cap, hm_j⟩
    · change j₁ < bCount n_max gm' b' at hj₁
      change j₂ < bCount n_max gm' b' at hj₂
      change quotAt base U w₀ n_max h_space s'.mem (slotOf n_max gm' b' j₁) =
        quotAt base U w₀ n_max h_space s'.mem (slotOf n_max gm' b' j₂) at hq_eq
      by_cases hbeq : b' = b
      · subst hbeq
        rw [hbc_b'] at hj₁ hj₂
        rw [(hold_b' j₁ hj₁).1, (hold_b' j₂ hj₂).1] at hq_eq
        exact hidx_inj j₁ hj₁ j₂ hj₂
          (hinv.hnodup_q b' hb' (idxMap j₁) (hidx_lt j₁ hj₁).1
            (idxMap j₂) (hidx_lt j₂ hj₂).1 hq_eq)
      · rw [hbc_other' b' hb' hbeq] at hj₁ hj₂
        rw [(hold_other' b' hb' hbeq j₁ hj₁).1, (hold_other' b' hb' hbeq j₂ hj₂).1] at hq_eq
        exact hinv.hnodup_q b' hb' j₁ hj₁ j₂ hj₂ hq_eq
    · change j < bCount n_max gm' b' at hj
      change B' b' (quotAt base U w₀ n_max h_space s'.mem (slotOf n_max gm' b' j)) =
        some (valAt base U V w₀ n_max h_space s'.mem (slotOf n_max gm' b' j))
      dsimp only [B']
      by_cases hbeq : b' = b
      · subst hbeq
        rw [Function.update_self]
        rw [hbc_b'] at hj
        rw [(hold_b' j hj).1, (hold_b' j hj).2]
        obtain ⟨hidx_b, hidx_ne⟩ := hidx_lt j hj
        have hq_ne : quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm₀ b' (idxMap j)) ≠
            q_target :=
          fun heq => hidx_ne (hinv.hnodup_q b' hb' (idxMap j) hidx_b j_del hj_del_lt
            (heq.trans hq_del.symm))
        rw [Function.update_of_ne hq_ne]
        exact hinv.hmap_some b' hb' (idxMap j) hidx_b
      · rw [Function.update_of_ne hbeq]
        rw [hbc_other' b' hb' hbeq] at hj
        rw [(hold_other' b' hb' hbeq j hj).1, (hold_other' b' hb' hbeq j hj).2]
        exact hinv.hmap_some b' hb' j hj
    · change (B' b' q).isSome ↔
        ∃ j < bCount n_max gm' b',
          quotAt base U w₀ n_max h_space s'.mem (slotOf n_max gm' b' j) = q
      dsimp only [B']
      by_cases hbeq : b' = b
      · subst hbeq
        rw [Function.update_self, hbc_b']
        by_cases hqeq : q = q_target
        · subst hqeq
          rw [Function.update_self]
          constructor
          · intro h; simp at h
          · rintro ⟨j, hj_lt, hq_j⟩
            rw [(hold_b' j hj_lt).1] at hq_j
            obtain ⟨hidx_b, hidx_ne⟩ := hidx_lt j hj_lt
            exact False.elim (hidx_ne
              (hinv.hnodup_q b' hb' (idxMap j) hidx_b j_del hj_del_lt (hq_j.trans hq_del.symm)))
        · rw [Function.update_of_ne hqeq, hinv.hmap_dom b' hb' q]
          constructor
          · rintro ⟨k, hk_lt, hq_k⟩
            have hk_ne_del : k ≠ j_del := fun heq => hqeq (hq_k.symm.trans (heq ▸ hq_del))
            by_cases hk_last : k = j_last
            · subst hk_last
              have hdel_lt : j_del < j_last := by omega
              refine ⟨j_del, hdel_lt, ?_⟩
              rw [(hold_b' j_del hdel_lt).1]
              dsimp only [idxMap]
              rw [ite_eq_left rfl]
              exact hq_k
            · have hk_lt_last : k < j_last := by dsimp only [j_last, gm₀] at hk_lt hk_last ⊢; omega
              refine ⟨k, hk_lt_last, ?_⟩
              rw [(hold_b' k hk_lt_last).1]
              dsimp only [idxMap]
              rw [ite_eq_right hk_ne_del]
              exact hq_k
          · rintro ⟨j, hj_lt, hq_j⟩
            rw [(hold_b' j hj_lt).1] at hq_j
            exact ⟨idxMap j, (hidx_lt j hj_lt).1, hq_j⟩
      · rw [Function.update_of_ne hbeq, hbc_other' b' hb' hbeq, hinv.hmap_dom b' hb' q]
        constructor <;> rintro ⟨j, hj_lt, hq_j⟩ <;> refine ⟨j, hj_lt, ?_⟩
        · rw [(hold_other' b' hb' hbeq j hj_lt).1]; exact hq_j
        · rw [← (hold_other' b' hb' hbeq j hj_lt).1]; exact hq_j
  · -- Case: key not found (res_prep.1.1.1 = 0)
    rw [ite_eq_right hex] at hprep_branch
    rcases hprep_branch with ⟨hf0, _⟩
    have hnot_some : ¬(B b q_target).isSome := mt (hinv.hmap_dom b hb q_target).mp hex
    have hB_none : B b q_target = none := by
      cases hB : B b q_target with
      | none => rfl
      | some v => simp [hB] at hnot_some
    have hB'_eq : B' = B := by
      dsimp only [B']
      ext b' q'
      by_cases hbeq : b' = b
      · subst hbeq
        rw [Function.update_self]
        by_cases hqeq : q' = q_target
        · subst hqeq; rw [Function.update_self, hB_none]
        · rw [Function.update_of_ne hqeq]
      · rw [Function.update_of_ne hbeq]
    have hne1 : prep.1.1.1 ≠ 1 := by omega
    have hs'_eq : s' = s := by
      change (Memory.spec 0).clientState s (deleteFinishProg U V w₀ n_max h_space d_fin) = s
      unfold deleteFinishProg
      simp only [pure_bind, d_fin]
      rw [ite_eq_right hne1]
      rfl
    have hcost0 : memoryCost (deleteFinishProg U V w₀ n_max h_space d_fin) s = 0 := by
      unfold deleteFinishProg
      simp only [pure_bind, d_fin]
      rw [ite_eq_right hne1]
      rfl
    have hgm'_eq : gm' = gm₀ := by dsimp only [gm', gm₀]; rw [hs'_eq]
    refine ⟨⟨henv, fun h => by dsimp only [d_fin] at h; omega⟩,
      by rw [hs'_eq],
      fun _ _ => by rw [hs'_eq],
      ⟨L, by rw [hs'_eq, hB'_eq]; exact hinv⟩,
      by rw [hgm'_eq, ite_eq_right hnot_some],
      by rw [hcost0, hgm'_eq]; omega⟩

end Cslib.DataStructure.Dictionary.WordRAM.Succinct

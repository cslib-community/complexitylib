/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.WordRAM.SuccinctMicroChain
import Complexity.Tactic.Realize

/-!
# Succinct Dictionary Bucket Search and Query in `Memory.Prog` via `realize`

This module implements Phase 2 overflow search (`resolveOvfStepProg`, `ovfStepProg`,
`ovfLoopProg`, `searchOverflowProg`), the combined two-phase bucket search (`searchBucketProg`),
and the dictionary lookup body (`queryBodyProg`) in the `Memory.Prog` monad, certifying each via
`Realizes .exact` and the `realize` tactic.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.resolveOvfStepProg`: single-step overflow slot
  resolver advancing along `slabAbove` across slab boundaries.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.ovfStepProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.ovfLoopProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.searchOverflowProg`: Phase 2 overflow scan over
  `j ∈ [effBucketCap n_max, bCount n_max gm b)`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.searchBucketProg`: combined two-phase bucket
  search (`searchMicroChainProg` followed by `searchOverflowProg`).
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.queryBodyProg`: `Memory.Prog` lookup body
  returning `Option ℕ`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.searchOverflowProg_spec`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_searchOverflowGen`: specification and
  `Realizes` certificate for `searchOverflowProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.searchBucketProg_spec`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_searchBucketGen`: specification and
  `Realizes` certificate for `searchBucketProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.queryBodyProg_spec`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_queryBodyGen`: specification and
  `Realizes` certificate for `queryBodyProg`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.Succinct

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray

/-! ## Section 1: Overflow Slot Resolution (`resolveOvfStepProg`) -/

/-- Arithmetic helper: when `(K - 1) - j % K = 0` (`0 < K`), `(j + 1) / K = j / K + 1` and
`(j / K + 1) * K = j + 1`. -/
private theorem div_succ_of_sub_mod_eq_zero {j K : ℕ} (hK : 0 < K) (hoff : (K - 1) - j % K = 0) :
    (j + 1) / K = j / K + 1 ∧ (j / K + 1) * K = j + 1 := by
  have hmod_lt : j % K < K := Nat.mod_lt j hK
  have hmod_eq : j % K = K - 1 := by omega
  have hj_eq : j + 1 = (j / K + 1) * K := by
    have hdiv := Nat.div_add_mod j K
    calc j + 1 = K * (j / K) + j % K + 1 := by omega
      _ = K * (j / K) + K := by omega
      _ = (j / K + 1) * K := by ring
  refine ⟨?_, hj_eq.symm⟩
  rw [hj_eq, Nat.mul_div_cancel _ hK]

/-- Arithmetic helper: when `(K - 1) - j % K ≠ 0` (`0 < K`), `(j + 1) / K = j / K`. -/
private theorem div_succ_of_sub_mod_ne_zero {j K : ℕ} (hK : 0 < K) (hoff : (K - 1) - j % K ≠ 0) :
    (j + 1) / K = j / K := by
  have hmod_lt : j % K < K := Nat.mod_lt j hK
  have hrem_lt : j % K + 1 < K := by omega
  have hj_eq : j + 1 = (j % K + 1) + K * (j / K) := by
    have hdiv := Nat.div_add_mod j K
    omega
  rw [hj_eq, Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hrem_lt, Nat.zero_add]

/-- Parameter-free single-step overflow slot resolver (`d = ((dp, (base, b)), (j, p_cur))`),
returning `(slotOf n_max gm b j, p_next)` where `p_next` advances along `slabAbove` at the end of
each full slab (`off = 0` and `j + 1 < q_b * slabSize n_max`). -/
@[expose] def resolveOvfStepGenProg
    (d : (DictParams × (ℕ × ℕ)) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let q_idx ← pure (4 + 3 * d.1.2.2)
  let q_b ← readGMGenProg (d.1.1, (d.1.2.1, q_idx))
  let qK ← pure (q_b * dpSlabSize d.1.1)
  if d.2.1 < qK then do
    let off ← pure (dpSlabSizeSubOne d.1.1 - d.2.1 % dpSlabSize d.1.1)
    let phys ← pure (d.2.2 * dpSlabSize d.1.1 + off)
    let z0 ← pure 0
    if off = z0 then do
      let j1 ← pure (d.2.1 + 1)
      if j1 < qK then do
        let abv_idx ← pure (dpGmSlabMetaBase d.1.1 + 4 * d.2.2 + 3)
        let p_next ← readGMGenProg (d.1.1, (d.1.2.1, abv_idx))
        pure (phys, p_next)
      else
        pure (phys, d.2.2)
    else
      pure (phys, d.2.2)
  else do
    let r ← pure (d.2.1 - qK)
    let t_idx ← pure (dpGmTailPtrBase d.1.1 + (d.1.2.2 * dpTailCap d.1.1 + r))
    let t ← readGMGenProg (d.1.1, (d.1.2.1, t_idx))
    let phys ← pure (dpNMaxSubOne d.1.1 - t)
    pure (phys, d.2.2)

/-- Single-step overflow slot resolver (`d = ((base, b), (j, p_cur))`), returning
`(slotOf n_max gm b j, p_next)` where `p_next` advances along `slabAbove` at the end of each
full slab (`off = 0` and `j + 1 < q_b * slabSize n_max`). -/
@[expose] def resolveOvfStepProg (U V w n_max h_space : ℕ)
    (d : (ℕ × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let q_idx ← pure (4 + 3 * d.1.2)
  let q_b ← readGMProg U V w n_max h_space (d.1.1, q_idx)
  let qK ← pure (q_b * slabSize n_max)
  if d.2.1 < qK then do
    let off ← pure ((slabSize n_max - 1) - d.2.1 % slabSize n_max)
    let phys ← pure (d.2.2 * slabSize n_max + off)
    let z0 ← pure 0
    if off = z0 then do
      let j1 ← pure (d.2.1 + 1)
      if j1 < qK then do
        let abv_idx ← pure (gmSlabMetaBase n_max + 4 * d.2.2 + 3)
        let p_next ← readGMProg U V w n_max h_space (d.1.1, abv_idx)
        pure (phys, p_next)
      else
        pure (phys, d.2.2)
    else
      pure (phys, d.2.2)
  else do
    let r ← pure (d.2.1 - qK)
    let t_idx ← pure (gmTailPtrBase n_max + (d.1.2 * tailCapPerBucket n_max + r))
    let t ← readGMProg U V w n_max h_space (d.1.1, t_idx)
    let phys ← pure ((n_max - 1) - t)
    pure (phys, d.2.2)

@[simp]
theorem resolveOvfStepGenProg_mk (U V w n_max h_space : ℕ)
    (d1 d2 : ℕ × ℕ) :
    resolveOvfStepGenProg ((mkDictParams U V w n_max h_space, d1), d2) =
      resolveOvfStepProg U V w n_max h_space (d1, d2) := by
  simp only [resolveOvfStepGenProg, resolveOvfStepProg, p_slabSize_mk, p_slabSizeSubOne_mk,
    p_gmSlabMetaBase_mk, p_gmTailPtrBase_mk, p_tailCap_mk, p_nMaxSubOne_mk, readGMGenProg_mk]

theorem memoryCost_resolveOvfStepGenProg_pos
    (d : (DictParams × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (resolveOvfStepGenProg d) s := by
  unfold resolveOvfStepGenProg readGMGenProg readPackedGenProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  rw [memoryCost_bind, memoryCost_readPackedProg]
  omega

theorem clientState_resolveOvfStepProg (U V w n_max h_space : ℕ)
    (d : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (resolveOvfStepProg U V w n_max h_space d) = s := by
  unfold resolveOvfStepProg
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_readGMProg]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_readGMProg]; rfl
  · rfl
  · rfl
  · rw [StateTransitionSpec.clientState_bind, clientState_readGMProg]; rfl

theorem memoryCost_resolveOvfStepProg_le (U V w n_max h_space : ℕ)
    (d : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (resolveOvfStepProg U V w n_max h_space d) s ≤ 4 := by
  unfold resolveOvfStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  rw [memoryCost_bind, clientState_readGMProg, memoryCost_readGMProg]
  split_ifs
  · rw [memoryCost_bind, clientState_readGMProg, memoryCost_readGMProg]
    change 2 + (2 + 0) ≤ 4; omega
  · change 2 + 0 ≤ 4; omega
  · change 2 + 0 ≤ 4; omega
  · rw [memoryCost_bind, clientState_readGMProg, memoryCost_readGMProg]
    change 2 + (2 + 0) ≤ 4; omega

/-- Precondition for `resolveOvfStepProg` (`d = ((base, b), (j, p_cur))`). -/
@[expose] def ResolveOvfStepPre (U V w₀ n_max h_space w : ℕ)
    (d : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  let gm := gmAt d.1.1 U V w₀ n_max h_space s.mem
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) d.1.1 ∧
  d.1.2 < numBuckets n_max ∧
  d.2.1 < bCount n_max gm d.1.2 ∧
  SlotStoreInv n_max gm ∧
  (d.2.1 < gm (gmQIdx d.1.2) * slabSize n_max →
    d.2.2 = slabPtrOf n_max gm d.1.2 (d.2.1 / slabSize n_max)) ∧
  0 < bucketBits n_max

/-- Parameter-free precondition for `resolveOvfStepGenProg`. -/
@[expose] def ResolveOvfStepGenPre (w : ℕ)
    (d : (DictParams × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  let gm := gmAt d.1.2.1 (dpU d.1.1) (dpV d.1.1) (dpW d.1.1) (dpNMax d.1.1) (dpHSpace d.1.1) s.mem
  DictEnvGen w d.1.1 d.1.2.1 ∧
  d.1.2.2 < numBuckets (dpNMax d.1.1) ∧
  d.2.1 < bCount (dpNMax d.1.1) gm d.1.2.2 ∧
  SlotStoreInv (dpNMax d.1.1) gm ∧
  (d.2.1 < gm (gmQIdx d.1.2.2) * slabSize (dpNMax d.1.1) →
    d.2.2 = slabPtrOf (dpNMax d.1.1) gm d.1.2.2 (d.2.1 / slabSize (dpNMax d.1.1))) ∧
  0 < bucketBits (dpNMax d.1.1)

@[simp]
theorem resolveOvfStepGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d1 d2 : ℕ × ℕ) (s : Memory.State) :
    ResolveOvfStepGenPre w ((mkDictParams U V w₀ n_max h_space, d1), d2) s ↔
      ResolveOvfStepPre U V w₀ n_max h_space w (d1, d2) s := Iff.rfl

theorem clientResult_resolveOvfStepProg {U V w n_max h_space : ℕ}
    {d : (ℕ × ℕ) × (ℕ × ℕ)} (s : Memory.State)
    (hb_pos : 0 < bucketBits n_max)
    (hb : d.1.2 < numBuckets n_max)
    (hj_bc : d.2.1 < bCount n_max (gmAt d.1.1 U V w n_max h_space s.mem) d.1.2)
    (hinv : SlotStoreInv n_max (gmAt d.1.1 U V w n_max h_space s.mem))
    (hp : d.2.1 < gmAt d.1.1 U V w n_max h_space s.mem (gmQIdx d.1.2) * slabSize n_max →
      d.2.2 = slabPtrOf n_max (gmAt d.1.1 U V w n_max h_space s.mem) d.1.2
        (d.2.1 / slabSize n_max)) :
    let gm := gmAt d.1.1 U V w n_max h_space s.mem
    let res := (Memory.spec 0).clientResult s (resolveOvfStepProg U V w n_max h_space d)
    res.1 = slotOf n_max gm d.1.2 d.2.1 ∧
    (d.2.1 + 1 < gm (gmQIdx d.1.2) * slabSize n_max →
      res.2 = slabPtrOf n_max gm d.1.2 ((d.2.1 + 1) / slabSize n_max)) := by
  intro gm res
  dsimp only [gm, res] at *
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK : 0 < slabSize n_max := slabSize_pos n_max
  have hq_lt : 4 + 3 * d.1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos hb
  have hslab := hinv.multi_slab hb_pos
  unfold resolveOvfStepProg
  simp only [pure_bind]
  rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
    clientResult_readGMProg s hq_lt, show 4 + 3 * d.1.2 = gmQIdx d.1.2 from rfl]
  split_ifs with hj_slab hoff hj1_slab
  · have hp_eq := hp hj_slab
    have ⟨hdiv_eq, hmul_eq⟩ := div_succ_of_sub_mod_eq_zero hK hoff
    have hs_lt : d.2.1 / slabSize n_max <
        gmAt d.1.1 U V w n_max h_space s.mem (gmQIdx d.1.2) :=
      Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hs1_lt : d.2.1 / slabSize n_max + 1 <
        gmAt d.1.1 U V w n_max h_space s.mem (gmQIdx d.1.2) := by
      have : (d.2.1 / slabSize n_max + 1) * slabSize n_max <
          gmAt d.1.1 U V w n_max h_space s.mem (gmQIdx d.1.2) * slabSize n_max := by rwa [hmul_eq]
      exact (Nat.mul_lt_mul_right hK).mp this
    have hp_lt_max : d.2.2 < maxFullSlabs n_max := by
      rw [hp_eq]
      exact lt_of_lt_of_le (hslab.ptr_lt d.1.2 hb _ hs_lt) hslab.nslabs_le
    have habove_lt : gmSlabMetaBase n_max + 4 * d.2.2 + 3 < globalMetaLen n_max :=
      gmSlabAboveIdx_lt hb_pos hp_lt_max
    rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      clientResult_readGMProg s habove_lt]
    refine ⟨?_, fun _ => ?_⟩
    · unfold slotOf
      rw [ite_eq_right hb0, ite_eq_left hj_slab, hp_eq]
      rfl
    · change gmAt d.1.1 U V w n_max h_space s.mem (gmSlabAboveIdx n_max d.2.2) = _
      rw [hp_eq, hslab.above_eq d.1.2 hb _ hs_lt hs1_lt, hdiv_eq]
  · have hp_eq := hp hj_slab
    refine ⟨?_, fun h => (hj1_slab h).elim⟩
    unfold slotOf
    rw [ite_eq_right hb0, ite_eq_left hj_slab, hp_eq]
    rfl
  · have hp_eq := hp hj_slab
    have hdiv_eq := div_succ_of_sub_mod_ne_zero hK hoff
    refine ⟨?_, fun _ => by rw [hp_eq, hdiv_eq]; rfl⟩
    unfold slotOf
    rw [ite_eq_right hb0, ite_eq_left hj_slab, hp_eq]
    rfl
  · unfold bCount at hj_bc
    simp only [hb0, ↓reduceIte, hb] at hj_bc
    have hr_lt : d.2.1 - gmAt d.1.1 U V w n_max h_space s.mem (gmQIdx d.1.2) * slabSize n_max <
        gmAt d.1.1 U V w n_max h_space s.mem (gmRIdx d.1.2) := by omega
    have hr_cap : d.2.1 - gmAt d.1.1 U V w n_max h_space s.mem (gmQIdx d.1.2) * slabSize n_max <
        tailCapPerBucket n_max :=
      lt_of_lt_of_le hr_lt (hinv.multi_r_bounds hb_pos d.1.2 hb).1.le
    have hptr_lt : gmTailPtrBase n_max +
        (d.1.2 * tailCapPerBucket n_max +
          (d.2.1 - gmAt d.1.1 U V w n_max h_space s.mem (gmQIdx d.1.2) * slabSize n_max)) <
        globalMetaLen n_max :=
      gmTailPtrIdx_lt hb_pos hb hr_cap
    rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      clientResult_readGMProg s hptr_lt]
    refine ⟨?_, fun h => by omega⟩
    unfold slotOf
    rw [ite_eq_right hb0, ite_eq_right hj_slab]
    rfl

theorem realizes_resolveOvfStepGen :
    Realizes .exact resolveOvfStepGenProg
      (WordEncoding.encode (α := (DictParams × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      ResolveOvfStepGenPre
      (fun _ _ => 0) := by
  have hrg := realizes_readGMGen
  realize
  all_goals (
    rcases d with ⟨⟨dp, d1⟩, d2⟩
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1
    have hb_pos : 0 < bucketBits n_max := h.2.2.2.2.2
    have hK : 0 < slabSize n_max := slabSize_pos n_max
    simpDictParamsWith [resolveOvfStepGenPre_mk, ResolveOvfStepPre, resolveOvfStepGenProg_mk]
  )
  · exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU (le_of_lt (gmQIdx_lt hb_pos h.2.1))
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact h.1
  · exact gmQIdx_lt hb_pos h.2.1
  · have hq_lt : 4 + 3 * d1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos h.2.1
    rw [clientResult_readGMProg _ hq_lt]
    have hbc := bCount_le_n_max h.2.2.2.1 d1.2
    have hb0 : bucketBits n_max ≠ 0 := by omega
    unfold bCount at hbc
    simp only [hb0, ↓reduceIte, h.2.1, gmQIdx] at hbc
    exact fits_of_le_max_n_one h.1 hw hnU hU (by omega)
  · exact Nat.ne_of_gt hK
  · have := Nat.mod_lt d2.1 hK; omega
  · have hq_lt : 4 + 3 * d1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos h.2.1
    have hqb := clientResult_readGMProg s (base := d1.1) (U := U) (V := V)
      (w := w₀) (h_space := h_space) hq_lt
    rw [hqb] at hc
    have hp_eq := h.2.2.2.2.1 hc
    have hslab := h.2.2.2.1.multi_slab hb_pos
    have hs_lt : d2.1 / slabSize n_max <
        gmAt d1.1 U V w₀ n_max h_space s.mem (gmQIdx d1.2) :=
      Nat.div_lt_of_lt_mul (by unfold gmQIdx; rw [Nat.mul_comm]; exact hc)
    have hp_lt : d2.2 < gmAt d1.1 U V w₀ n_max h_space s.mem 0 := by
      rw [hp_eq, hslab.nslabs_eq]
      exact hslab.ptr_lt d1.2 h.2.1 _ hs_lt
    have hmod_lt : d2.1 % slabSize n_max < slabSize n_max := Nat.mod_lt _ hK
    have h1 : (d2.2 + 1) * slabSize n_max ≤
        gmAt d1.1 U V w₀ n_max h_space s.mem 0 * slabSize n_max :=
      Nat.mul_le_mul_right _ hp_lt
    rw [Nat.add_one_mul] at h1
    have htot := h.2.2.2.1.multi_total_le hb_pos
    exact fits_of_le_max_n_one h.1 hw hnU hU (by omega)
  · have hbc := bCount_le_n_max h.2.2.2.1 d1.2
    have := h.2.2.1
    exact fits_of_le_max_n_one h.1 hw hnU hU (by omega)
  · have hq_lt : 4 + 3 * d1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos h.2.1
    have hqb := clientResult_readGMProg s (base := d1.1) (U := U) (V := V)
      (w := w₀) (h_space := h_space) hq_lt
    rw [hqb] at hc
    have hj_lt : d2.1 < gmAt d1.1 U V w₀ n_max h_space s.mem (gmQIdx d1.2) * slabSize n_max :=
      Nat.lt_of_succ_lt hc
    have hp_eq := h.2.2.2.2.1 hj_lt
    have hslab := h.2.2.2.1.multi_slab hb_pos
    have hs_lt : d2.1 / slabSize n_max <
        gmAt d1.1 U V w₀ n_max h_space s.mem (gmQIdx d1.2) :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj_lt)
    have hp_lt_max : d2.2 < maxFullSlabs n_max := by
      rw [hp_eq]
      exact lt_of_lt_of_le (hslab.ptr_lt d1.2 h.2.1 _ hs_lt) hslab.nslabs_le
    exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU
      (le_of_lt (gmSlabAboveIdx_lt hb_pos hp_lt_max))
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact h.1
  · have hq_lt : 4 + 3 * d1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos h.2.1
    have hqb := clientResult_readGMProg s (base := d1.1) (U := U) (V := V)
      (w := w₀) (h_space := h_space) hq_lt
    rw [hqb] at hc
    have hj_lt : d2.1 < gmAt d1.1 U V w₀ n_max h_space s.mem (gmQIdx d1.2) * slabSize n_max :=
      Nat.lt_of_succ_lt hc
    have hp_eq := h.2.2.2.2.1 hj_lt
    have hslab := h.2.2.2.1.multi_slab hb_pos
    have hs_lt : d2.1 / slabSize n_max <
        gmAt d1.1 U V w₀ n_max h_space s.mem (gmQIdx d1.2) :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj_lt)
    have hp_lt_max : d2.2 < maxFullSlabs n_max := by
      rw [hp_eq]
      exact lt_of_lt_of_le (hslab.ptr_lt d1.2 h.2.1 _ hs_lt) hslab.nslabs_le
    exact gmSlabAboveIdx_lt hb_pos hp_lt_max
  · omega
  · have hq_lt : 4 + 3 * d1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos h.2.1
    have hqb := clientResult_readGMProg s (base := d1.1) (U := U) (V := V)
      (w := w₀) (h_space := h_space) hq_lt
    rw [hqb] at hc ⊢
    have hb0 : bucketBits n_max ≠ 0 := by omega
    have hj_bc := h.2.2.1
    unfold bCount at hj_bc
    simp only [hb0, ↓reduceIte, h.2.1, gmQIdx] at hj_bc
    have hr_lt : d2.1 - gmAt d1.1 U V w₀ n_max h_space s.mem (4 + 3 * d1.2) * slabSize n_max <
        gmAt d1.1 U V w₀ n_max h_space s.mem (gmRIdx d1.2) := by omega
    have hr_cap : d2.1 - gmAt d1.1 U V w₀ n_max h_space s.mem (4 + 3 * d1.2) * slabSize n_max <
        tailCapPerBucket n_max :=
      lt_of_lt_of_le hr_lt (h.2.2.2.1.multi_r_bounds hb_pos d1.2 h.2.1).1.le
    exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU
      (le_of_lt (gmTailPtrIdx_lt hb_pos h.2.1 hr_cap))
  · exact h.1
  · have hq_lt : 4 + 3 * d1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos h.2.1
    have hqb := clientResult_readGMProg s (base := d1.1) (U := U) (V := V)
      (w := w₀) (h_space := h_space) hq_lt
    rw [hqb] at hc ⊢
    have hb0 : bucketBits n_max ≠ 0 := by omega
    have hj_bc := h.2.2.1
    unfold bCount at hj_bc
    simp only [hb0, ↓reduceIte, h.2.1, gmQIdx] at hj_bc
    have hr_lt : d2.1 - gmAt d1.1 U V w₀ n_max h_space s.mem (4 + 3 * d1.2) * slabSize n_max <
        gmAt d1.1 U V w₀ n_max h_space s.mem (gmRIdx d1.2) := by omega
    have hr_cap : d2.1 - gmAt d1.1 U V w₀ n_max h_space s.mem (4 + 3 * d1.2) * slabSize n_max <
        tailCapPerBucket n_max :=
      lt_of_lt_of_le hr_lt (h.2.2.2.1.multi_r_bounds hb_pos d1.2 h.2.1).1.le
    exact gmTailPtrIdx_lt hb_pos h.2.1 hr_cap
  · have hq_lt : 4 + 3 * d1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos h.2.1
    have hqb := clientResult_readGMProg s (base := d1.1) (U := U) (V := V)
      (w := w₀) (h_space := h_space) hq_lt
    rw [clientState_readGMProg]
    rw [hqb] at hc ⊢
    have hb0 : bucketBits n_max ≠ 0 := by omega
    have hj_bc := h.2.2.1
    unfold bCount at hj_bc
    simp only [hb0, ↓reduceIte, h.2.1, gmQIdx] at hj_bc
    have hr_lt : d2.1 - gmAt d1.1 U V w₀ n_max h_space s.mem (4 + 3 * d1.2) * slabSize n_max <
        gmAt d1.1 U V w₀ n_max h_space s.mem (gmRIdx d1.2) := by omega
    have hr_cap : d2.1 - gmAt d1.1 U V w₀ n_max h_space s.mem (4 + 3 * d1.2) * slabSize n_max <
        tailCapPerBucket n_max :=
      lt_of_lt_of_le hr_lt (h.2.2.2.1.multi_r_bounds hb_pos d1.2 h.2.1).1.le
    have hptr_lt : gmTailPtrBase n_max + (d1.2 * tailCapPerBucket n_max +
        (d2.1 - gmAt d1.1 U V w₀ n_max h_space s.mem (4 + 3 * d1.2) * slabSize n_max)) <
        globalMetaLen n_max := gmTailPtrIdx_lt hb_pos h.2.1 hr_cap
    rw [clientResult_readGMProg _ hptr_lt]
    have htail := h.2.2.2.1.multi_tail hb_pos
    have ht_lt : gmAt d1.1 U V w₀ n_max h_space s.mem
        (gmTailPtrIdx n_max d1.2
          (d2.1 - gmAt d1.1 U V w₀ n_max h_space s.mem (4 + 3 * d1.2) * slabSize n_max)) <
        gmAt d1.1 U V w₀ n_max h_space s.mem 1 := by
      rw [htail.ntails_eq]
      exact htail.ptr_lt d1.2 h.2.1 _ hr_lt
    have htot := h.2.2.2.1.multi_total_le hb_pos
    have hn_pos := one_le_n_max_of_bucketBits_pos hb_pos
    unfold gmTailPtrIdx gmTailPtrFlatIdx at ht_lt
    omega

/-! ## Section 2: Phase 2 Overflow Search (`ovfStepProg`, `ovfLoopProg`, `searchOverflowProg`) -/

/-- Parameter-free step of Phase 2 overflow search (`x = ((dp, ((base, b), q_target)),
((((j, p_cur), found), j_found), phys_found))`). -/
@[expose] def ovfStepGenProg
    (x : (DictParams × ((ℕ × ℕ) × ℕ)) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) :
    Memory.Prog ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) := do
  let pair ← resolveOvfStepGenProg ((x.1.1, x.1.2.1), x.2.1.1.1)
  let q_val ← readQuotGenProg (x.1.1, (x.1.2.1.1, pair.1))
  let j1 ← pure (x.2.1.1.1.1 + 1)
  let z0 ← pure 0
  if x.2.1.1.2 = z0 then
    if q_val = x.1.2.2 then do
      let z1 ← pure 1
      pure ((((j1, pair.2), z1), x.2.1.1.1.1), pair.1)
    else
      pure ((((j1, pair.2), z0), x.2.1.2), x.2.2)
  else
    pure ((((j1, pair.2), x.2.1.1.2), x.2.1.2), x.2.2)

/-- One step of Phase 2 overflow search (`x = (((base, b), q_target), ((((j, p_cur), found),
j_found), phys_found))`). Resolves `(phys, p_next) ← resolveOvfStepProg` and reads `q_val` at
`phys`, recording the first matching slot `(1, j, phys)` when `found = 0 ∧ q_val = q_target`. -/
@[expose] def ovfStepProg (U V w n_max h_space : ℕ)
    (x : ((ℕ × ℕ) × ℕ) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) :
    Memory.Prog ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) := do
  let pair ← resolveOvfStepProg U V w n_max h_space (x.1.1, x.2.1.1.1)
  let q_val ← readQuotProg U w n_max h_space (x.1.1.1, pair.1)
  let j1 ← pure (x.2.1.1.1.1 + 1)
  let z0 ← pure 0
  if x.2.1.1.2 = z0 then
    if q_val = x.1.2 then do
      let z1 ← pure 1
      pure ((((j1, pair.2), z1), x.2.1.1.1.1), pair.1)
    else
      pure ((((j1, pair.2), z0), x.2.1.2), x.2.2)
  else
    pure ((((j1, pair.2), x.2.1.1.2), x.2.1.2), x.2.2)

@[simp]
theorem ovfStepGenProg_mk (U V w n_max h_space : ℕ)
    (x1 : (ℕ × ℕ) × ℕ) (x2 : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) :
    ovfStepGenProg ((mkDictParams U V w n_max h_space, x1), x2) =
      ovfStepProg U V w n_max h_space (x1, x2) := by
  simp only [ovfStepGenProg, ovfStepProg, resolveOvfStepGenProg_mk, readQuotGenProg_mk]

theorem memoryCost_ovfStepGenProg_pos
    (x : (DictParams × ((ℕ × ℕ) × ℕ)) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (ovfStepGenProg x) s := by
  unfold ovfStepGenProg
  simp only [← PFunctor.FreeM.bind_eq_bind]
  rw [memoryCost_bind]
  have := memoryCost_resolveOvfStepGenProg_pos ((x.1.1, x.1.2.1), x.2.1.1.1) s
  omega

theorem clientState_ovfStepProg (U V w n_max h_space : ℕ)
    (x : ((ℕ × ℕ) × ℕ) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (ovfStepProg U V w n_max h_space x) = s := by
  unfold ovfStepProg
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_resolveOvfStepProg,
    StateTransitionSpec.clientState_bind, clientState_readQuotProg]
  split_ifs <;> rfl

theorem memoryCost_ovfStepProg_le (U V w n_max h_space : ℕ)
    (x : ((ℕ × ℕ) × ℕ) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) (s : Memory.State) :
    memoryCost (ovfStepProg U V w n_max h_space x) s ≤ 6 := by
  unfold ovfStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  rw [memoryCost_bind, clientState_resolveOvfStepProg, memoryCost_bind]
  have := memoryCost_resolveOvfStepProg_le U V w n_max h_space (x.1.1, x.2.1.1.1) s
  split_ifs <;> · change memoryCost (resolveOvfStepProg _ _ _ _ _ _) s + (2 + 0) ≤ 6; omega

/-- Precondition for `ovfStepProg`. -/
@[expose] def OvfStepPre (U V w₀ n_max h_space w : ℕ)
    (x : ((ℕ × ℕ) × ℕ) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  ResolveOvfStepPre U V w₀ n_max h_space w (x.1.1, x.2.1.1.1) s

/-- Parameter-free precondition for `ovfStepGenProg`. -/
@[expose] def OvfStepGenPre (w : ℕ)
    (x : (DictParams × ((ℕ × ℕ) × ℕ)) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  ResolveOvfStepGenPre w ((x.1.1, x.1.2.1), x.2.1.1.1) s

@[simp]
theorem ovfStepGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (x1 : (ℕ × ℕ) × ℕ) (x2 : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    OvfStepGenPre w ((mkDictParams U V w₀ n_max h_space, x1), x2) s ↔
      OvfStepPre U V w₀ n_max h_space w (x1, x2) s := Iff.rfl

theorem clientResult_ovfStepProg {U V w n_max h_space : ℕ}
    {x : ((ℕ × ℕ) × ℕ) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)} (s : Memory.State)
    (hb_pos : 0 < bucketBits n_max)
    (hb : x.1.1.2 < numBuckets n_max)
    (hj_bc : x.2.1.1.1.1 < bCount n_max (gmAt x.1.1.1 U V w n_max h_space s.mem) x.1.1.2)
    (hinv : SlotStoreInv n_max (gmAt x.1.1.1 U V w n_max h_space s.mem))
    (hp : x.2.1.1.1.1 <
        gmAt x.1.1.1 U V w n_max h_space s.mem (gmQIdx x.1.1.2) * slabSize n_max →
      x.2.1.1.1.2 = slabPtrOf n_max (gmAt x.1.1.1 U V w n_max h_space s.mem) x.1.1.2
        (x.2.1.1.1.1 / slabSize n_max)) :
    let gm := gmAt x.1.1.1 U V w n_max h_space s.mem
    let pair := (Memory.spec 0).clientResult s
      (resolveOvfStepProg U V w n_max h_space (x.1.1, x.2.1.1.1))
    let phys := slotOf n_max gm x.1.1.2 x.2.1.1.1.1
    let q_val := quotAt x.1.1.1 U w n_max h_space s.mem phys
    (Memory.spec 0).clientResult s (ovfStepProg U V w n_max h_space x) =
      (if x.2.1.1.2 = 0 then
        if q_val = x.1.2 then
          ((((x.2.1.1.1.1 + 1, pair.2), 1), x.2.1.1.1.1), phys)
        else
          ((((x.2.1.1.1.1 + 1, pair.2), 0), x.2.1.2), x.2.2)
       else
         ((((x.2.1.1.1.1 + 1, pair.2), x.2.1.1.2), x.2.1.2), x.2.2)) ∧
    (x.2.1.1.1.1 + 1 < gm (gmQIdx x.1.1.2) * slabSize n_max →
      pair.2 = slabPtrOf n_max gm x.1.1.2 ((x.2.1.1.1.1 + 1) / slabSize n_max)) := by
  intro gm pair phys q_val
  dsimp only [gm, pair, phys, q_val] at *
  have hres := clientResult_resolveOvfStepProg (d := (x.1.1, x.2.1.1.1))
    s hb_pos hb hj_bc hinv hp
  have hphys_lt : slotOf n_max (gmAt x.1.1.1 U V w n_max h_space s.mem) x.1.1.2 x.2.1.1.1.1 <
      n_max := (slotOf_lt_and_injective hinv).1 x.1.1.2 hb x.2.1.1.1.1 hj_bc
  unfold ovfStepProg
  simp only [pure_bind]
  rw [StateTransitionSpec.clientResult_bind, clientState_resolveOvfStepProg,
    StateTransitionSpec.clientResult_bind, clientState_readQuotProg]
  rw [show ((Memory.spec 0).clientResult s
      (resolveOvfStepProg U V w n_max h_space (x.1.1, x.2.1.1.1))).1 =
      slotOf n_max (gmAt x.1.1.1 U V w n_max h_space s.mem) x.1.1.2 x.2.1.1.1.1 from hres.1,
    clientResult_readQuotProg s hphys_lt]
  split_ifs <;> exact ⟨rfl, hres.2⟩

theorem realizes_ovfStepGen :
    Realizes .exact ovfStepGenProg
      (WordEncoding.encode (α := (DictParams × ((ℕ × ℕ) × ℕ)) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ))
      OvfStepGenPre
      (fun _ _ => 0) := by
  have hres := realizes_resolveOvfStepGen
  have hrq := realizes_readQuotGen
  realize
  all_goals (
    rcases d with ⟨⟨dp, d1⟩, d2⟩
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1
    have hb_pos : 0 < bucketBits n_max := h.2.2.2.2.2
    simpDictParamsWith [ovfStepGenPre_mk, OvfStepPre, ovfStepGenProg_mk,
      resolveOvfStepGenPre_mk, ResolveOvfStepPre, resolveOvfStepGenProg_mk]
  )
  · exact h
  · exact h.1
  · rw [(clientResult_resolveOvfStepProg (d := (d1.1, d2.1.1.1)) s
      hb_pos h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1).1]
    exact (slotOf_lt_and_injective h.2.2.2.1).1 d1.1.2 h.2.1 d2.1.1.1.1 h.2.2.1
  · have hbc := bCount_le_n_max h.2.2.2.1 d1.1.2
    have := h.2.2.1
    exact fits_of_le_max_n_one h.1 hw hnU hU (by omega)
  · exact fits_const_of_dictEnv h.1 (by decide)

/-- Parameter-free wrapper for `iterate ovfStepGenProg` matching `Realizes.iterate₀`. -/
@[expose] def ovfLoopGenProg
    (d : ((DictParams × ((ℕ × ℕ) × ℕ)) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) × ℕ) :
    Memory.Prog ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) :=
  iterate ovfStepGenProg d.1.1 d.2 d.1.2

/-- Wrapper for `iterate (ovfStepProg ...)` matching `Realizes.iterate₀`. -/
@[expose] def ovfLoopProg (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) × ℕ) :
    Memory.Prog ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) :=
  iterate (ovfStepProg U V w n_max h_space) d.1.1 d.2 d.1.2

@[simp]
theorem iterate_ovfStepGenProg_mk (U V w n_max h_space : ℕ)
    (ctx : (ℕ × ℕ) × ℕ) (m : ℕ) (acc : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) :
    iterate ovfStepGenProg (mkDictParams U V w n_max h_space, ctx) m acc =
      iterate (ovfStepProg U V w n_max h_space) ctx m acc := by
  induction m generalizing acc with
  | zero => rfl
  | succ m ih =>
    simp only [iterate, ovfStepGenProg_mk, ih]

@[simp]
theorem ovfLoopGenProg_mk (U V w n_max h_space : ℕ)
    (ctx : (ℕ × ℕ) × ℕ) (acc : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) (m : ℕ) :
    ovfLoopGenProg (((mkDictParams U V w n_max h_space, ctx), acc), m) =
      ovfLoopProg U V w n_max h_space ((ctx, acc), m) :=
  iterate_ovfStepGenProg_mk U V w n_max h_space ctx m acc

@[simp]
theorem iterationSafe_ovfStepGenProg_mk (U V w₀ n_max h_space w : ℕ)
    (ctx : (ℕ × ℕ) × ℕ) (m : ℕ) (acc : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    iterationSafe ovfStepGenProg OvfStepGenPre w
      (mkDictParams U V w₀ n_max h_space, ctx) m acc s ↔
    iterationSafe (ovfStepProg U V w₀ n_max h_space) (OvfStepPre U V w₀ n_max h_space)
      w ctx m acc s := by
  induction m generalizing acc s with
  | zero => rfl
  | succ m ih =>
    simp only [iterationSafe, ovfStepGenPre_mk, ovfStepGenProg_mk, ih]

theorem realizes_ovfLoopGen :
    Realizes .exact ovfLoopGenProg
      (WordEncoding.encode (α := ((DictParams × ((ℕ × ℕ) × ℕ)) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) × ℕ))
      (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ))
      (fun w d s =>
        iterationSafe ovfStepGenProg OvfStepGenPre w d.1.1 d.2 d.1.2 s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ)))
    (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ))
    realizes_ovfStepGen
    memoryCost_ovfStepGenProg_pos

open Classical in
/-- Structural induction lemma for `iterate (ovfStepProg ...)` over `m` overflow slots
`j .. j + m - 1`. -/
theorem iterate_ovfStepProg_spec {U V w₀ n_max h_space w base b q_target : ℕ} {s : Memory.State}
    (hb_pos : 0 < bucketBits n_max)
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hb : b < numBuckets n_max)
    (hinv : SlotStoreInv n_max (gmAt base U V w₀ n_max h_space s.mem)) :
    ∀ m j p_cur found j_found phys_found,
      j + m ≤ bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b →
      (j < gmAt base U V w₀ n_max h_space s.mem (gmQIdx b) * slabSize n_max →
        p_cur = slabPtrOf n_max (gmAt base U V w₀ n_max h_space s.mem) b (j / slabSize n_max)) →
      let prog := iterate (ovfStepProg U V w₀ n_max h_space) ((base, b), q_target) m
        ((((j, p_cur), found), j_found), phys_found)
      (Memory.spec 0).clientState s prog = s ∧
      memoryCost prog s ≤ 6 * m ∧
      iterationSafe (ovfStepProg U V w₀ n_max h_space)
        (OvfStepPre U V w₀ n_max h_space) w ((base, b), q_target) m
        ((((j, p_cur), found), j_found), phys_found) s ∧
      (let res := (Memory.spec 0).clientResult s prog
       if found = 0 then
         if ∃ k, j ≤ k ∧ k < j + m ∧
             quotAt base U w₀ n_max h_space s.mem
               (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b k) = q_target then
           res.1.1.2 = 1 ∧ j ≤ res.1.2 ∧ res.1.2 < j + m ∧
           quotAt base U w₀ n_max h_space s.mem
             (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b res.1.2) = q_target ∧
           res.2 = slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b res.1.2
         else
           res.1.1.2 = 0
       else
         res.1.1.2 = found ∧ res.1.2 = j_found ∧ res.2 = phys_found) := by
  intro m
  induction m with
  | zero =>
    intro j p_cur found j_found phys_found _ _ prog
    refine ⟨rfl, by simp [prog, iterate], trivial, ?_⟩
    dsimp only [prog, iterate, StateTransitionSpec.clientResult, StateTransitionSpec.runClient]
    split_ifs with hf hex
    · obtain ⟨k, hk1, hk2, _⟩ := hex; omega
    · exact hf
    · exact ⟨rfl, rfl, rfl⟩
  | succ m ih =>
    intro j p_cur found j_found phys_found hjm hp prog
    dsimp only [prog] at *
    have hj_bc : j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b := by omega
    have hpre : OvfStepPre U V w₀ n_max h_space w
        (((base, b), q_target), ((((j, p_cur), found), j_found), phys_found)) s :=
      ⟨henv, hb, hj_bc, hinv, hp, hb_pos⟩
    obtain ⟨hstep_res, hp_next⟩ :=
      clientResult_ovfStepProg
        (x := (((base, b), q_target), ((((j, p_cur), found), j_found), phys_found)))
        s hb_pos hb hj_bc hinv hp
    dsimp only at hstep_res hp_next
    have hstep_st := clientState_ovfStepProg U V w₀ n_max h_space
      (((base, b), q_target), ((((j, p_cur), found), j_found), phys_found)) s
    have hstep_cost := memoryCost_ovfStepProg_le U V w₀ n_max h_space
      (((base, b), q_target), ((((j, p_cur), found), j_found), phys_found)) s
    set pair := (Memory.spec 0).clientResult s
      (resolveOvfStepProg U V w₀ n_max h_space ((base, b), (j, p_cur)))
    set phys := slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j
    set q_val := quotAt base U w₀ n_max h_space s.mem phys
    have hjm' : (j + 1) + m ≤ bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b := by omega
    by_cases hf0 : found = 0
    · subst hf0
      by_cases hmatch : q_val = q_target
      · have hstep_eq : (Memory.spec 0).clientResult s
            (ovfStepProg U V w₀ n_max h_space
              (((base, b), q_target), ((((j, p_cur), 0), j_found), phys_found))) =
            ((((j + 1, pair.2), 1), j), phys) := by
          rw [hstep_res, ite_eq_left rfl, ite_eq_left hmatch]
        have hih := ih (j + 1) pair.2 1 j phys hjm' hp_next
        refine ⟨?_, ?_, ?_, ?_⟩
        · unfold iterate
          rw [StateTransitionSpec.clientState_bind, hstep_st, hstep_eq]
          exact hih.1
        · unfold iterate
          rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hstep_st, hstep_eq]
          have := hih.2.1; omega
        · rw [iterationSafe, hstep_st, hstep_eq]
          exact ⟨hpre, hih.2.2.1⟩
        · unfold iterate
          rw [StateTransitionSpec.clientResult_bind, hstep_st, hstep_eq]
          have hih_res := hih.2.2.2
          rw [ite_eq_right (by decide : (1 : ℕ) ≠ 0)] at hih_res
          rw [ite_eq_left rfl]
          have hex : ∃ k, j ≤ k ∧ k < j + (m + 1) ∧
              quotAt base U w₀ n_max h_space s.mem
                (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b k) = q_target :=
            ⟨j, le_rfl, by omega, hmatch⟩
          rw [ite_eq_left hex]
          exact ⟨hih_res.1, by rw [hih_res.2.1], by rw [hih_res.2.1]; omega,
            by rw [hih_res.2.1]; exact hmatch, by rw [hih_res.2.1, hih_res.2.2]⟩
      · have hstep_eq : (Memory.spec 0).clientResult s
            (ovfStepProg U V w₀ n_max h_space
              (((base, b), q_target), ((((j, p_cur), 0), j_found), phys_found))) =
            ((((j + 1, pair.2), 0), j_found), phys_found) := by
          rw [hstep_res, ite_eq_left rfl, ite_eq_right hmatch]
        have hih := ih (j + 1) pair.2 0 j_found phys_found hjm' hp_next
        refine ⟨?_, ?_, ?_, ?_⟩
        · unfold iterate
          rw [StateTransitionSpec.clientState_bind, hstep_st, hstep_eq]
          exact hih.1
        · unfold iterate
          rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hstep_st, hstep_eq]
          have := hih.2.1; omega
        · rw [iterationSafe, hstep_st, hstep_eq]
          exact ⟨hpre, hih.2.2.1⟩
        · unfold iterate
          rw [StateTransitionSpec.clientResult_bind, hstep_st, hstep_eq]
          have hih_res := hih.2.2.2
          rw [ite_eq_left rfl] at hih_res ⊢
          by_cases hex' : ∃ k, j + 1 ≤ k ∧ k < j + 1 + m ∧
              quotAt base U w₀ n_max h_space s.mem
                (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b k) = q_target
          · have hex : ∃ k, j ≤ k ∧ k < j + (m + 1) ∧
                quotAt base U w₀ n_max h_space s.mem
                  (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b k) = q_target := by
              obtain ⟨k, hk1, hk2, hqk⟩ := hex'
              exact ⟨k, by omega, by omega, hqk⟩
            rw [ite_eq_left hex'] at hih_res
            rw [ite_eq_left hex]
            exact ⟨hih_res.1, by omega, by omega, hih_res.2.2.2.1, hih_res.2.2.2.2⟩
          · have hno : ¬∃ k, j ≤ k ∧ k < j + (m + 1) ∧
                quotAt base U w₀ n_max h_space s.mem
                  (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b k) = q_target := by
              rintro ⟨k, hk1, hk2, hqk⟩
              rcases eq_or_lt_of_le hk1 with rfl | hlt
              · exact hmatch hqk
              · exact hex' ⟨k, by omega, by omega, hqk⟩
            rw [ite_eq_right hex'] at hih_res
            rw [ite_eq_right hno]
            exact hih_res
    · have hstep_eq : (Memory.spec 0).clientResult s
          (ovfStepProg U V w₀ n_max h_space
            (((base, b), q_target), ((((j, p_cur), found), j_found), phys_found))) =
          ((((j + 1, pair.2), found), j_found), phys_found) := by
        rw [hstep_res, ite_eq_right hf0]
      have hih := ih (j + 1) pair.2 found j_found phys_found hjm' hp_next
      refine ⟨?_, ?_, ?_, ?_⟩
      · unfold iterate
        rw [StateTransitionSpec.clientState_bind, hstep_st, hstep_eq]
        exact hih.1
      · unfold iterate
        rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hstep_st, hstep_eq]
        have := hih.2.1; omega
      · rw [iterationSafe, hstep_st, hstep_eq]
        exact ⟨hpre, hih.2.2.1⟩
      · unfold iterate
        rw [StateTransitionSpec.clientResult_bind, hstep_st, hstep_eq]
        have hih_res := hih.2.2.2
        rw [ite_eq_right hf0] at hih_res ⊢
        exact hih_res

/-- Parameter-free helper initializing `(p_init, fuel)` for Phase 2 overflow search
(`d = (dp, (base, b))`). -/
@[expose] def initOvfSearchGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let q_idx ← pure (4 + 3 * d.2.2)
  let q_b ← readGMGenProg (d.1, (d.2.1, q_idx))
  let r_idx ← pure (q_idx + 1)
  let r_b ← readGMGenProg (d.1, (d.2.1, r_idx))
  let qK ← pure (q_b * dpSlabSize d.1)
  let c ← pure (qK + r_b)
  let cap ← pure (dpMinCap d.1)
  let z0 ← pure 0
  if cap < c then do
    let fuel ← pure (c - cap)
    if cap < qK then do
      let dir_idx ← pure (dpGmSlabDirBase d.1 + d.2.2 * dpDirSlabs d.1 +
        dpDirSlabsSubOne d.1)
      let p_prev ← readGMGenProg (d.1, (d.2.1, dir_idx))
      let abv_idx ← pure (dpGmSlabMetaBase d.1 + 4 * p_prev + 3)
      let p_init ← readGMGenProg (d.1, (d.2.1, abv_idx))
      pure (p_init, fuel)
    else
      pure (z0, fuel)
  else
    pure (z0, z0)

/-- Helper initializing `(p_init, fuel)` for Phase 2 overflow search (`d = (base, b)`). -/
@[expose] def initOvfSearchProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog (ℕ × ℕ) := do
  let q_idx ← pure (4 + 3 * d.2)
  let q_b ← readGMProg U V w n_max h_space (d.1, q_idx)
  let r_idx ← pure (q_idx + 1)
  let r_b ← readGMProg U V w n_max h_space (d.1, r_idx)
  let qK ← pure (q_b * slabSize n_max)
  let c ← pure (qK + r_b)
  let cap ← pure (min n_max (effBucketCap n_max))
  let z0 ← pure 0
  if cap < c then do
    let fuel ← pure (c - cap)
    if cap < qK then do
      let dir_idx ← pure (gmSlabDirBase n_max + d.2 * dirSlabsPerBucket n_max +
        (dirSlabsPerBucket n_max - 1))
      let p_prev ← readGMProg U V w n_max h_space (d.1, dir_idx)
      let abv_idx ← pure (gmSlabMetaBase n_max + 4 * p_prev + 3)
      let p_init ← readGMProg U V w n_max h_space (d.1, abv_idx)
      pure (p_init, fuel)
    else
      pure (z0, fuel)
  else
    pure (z0, z0)

@[simp]
theorem initOvfSearchGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    initOvfSearchGenProg (mkDictParams U V w n_max h_space, d) =
      initOvfSearchProg U V w n_max h_space d := by
  simp only [initOvfSearchGenProg, initOvfSearchProg, p_slabSize_mk, p_minCap_mk,
    p_gmSlabDirBase_mk, p_dirSlabs_mk, p_dirSlabsSubOne_mk, p_gmSlabMetaBase_mk,
    readGMGenProg_mk]

theorem clientState_initOvfSearchProg (U V w n_max h_space : ℕ)
    (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (initOvfSearchProg U V w n_max h_space d) = s := by
  unfold initOvfSearchProg
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
    StateTransitionSpec.clientState_bind, clientState_readGMProg]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
      StateTransitionSpec.clientState_bind, clientState_readGMProg]
    rfl
  · rfl
  · rfl

theorem memoryCost_initOvfSearchProg_le (U V w n_max h_space : ℕ)
    (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (initOvfSearchProg U V w n_max h_space d) s ≤ 8 := by
  unfold initOvfSearchProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  rw [memoryCost_bind, clientState_readGMProg, memoryCost_bind, clientState_readGMProg]
  split_ifs
  · rw [memoryCost_bind, clientState_readGMProg, memoryCost_bind, clientState_readGMProg]
    change 2 + (2 + (2 + (2 + 0))) ≤ 8; omega
  · change 2 + (2 + 0) ≤ 8; omega
  · change 2 + (2 + 0) ≤ 8; omega

theorem dirSlabsPerBucket_pos_of_pos {n_max : ℕ} (hb : 0 < bucketBits n_max) :
    0 < dirSlabsPerBucket n_max := by
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hS := two_le_slabScale n_max
  unfold dirSlabsPerBucket
  rw [ite_eq_right hb0]
  omega

theorem clientResult_initOvfSearchProg {U V w n_max h_space : ℕ}
    {d : ℕ × ℕ} (s : Memory.State)
    (hb_pos : 0 < bucketBits n_max)
    (hb : d.2 < numBuckets n_max)
    (hinv : SlotStoreInv n_max (gmAt d.1 U V w n_max h_space s.mem)) :
    let gm := gmAt d.1 U V w n_max h_space s.mem
    let res := (Memory.spec 0).clientResult s (initOvfSearchProg U V w n_max h_space d)
    res.2 = bCount n_max gm d.2 - effBucketCap n_max ∧
    (effBucketCap n_max < bCount n_max gm d.2 →
      effBucketCap n_max < gm (gmQIdx d.2) * slabSize n_max →
      res.1 = slabPtrOf n_max gm d.2 (effBucketCap n_max / slabSize n_max)) := by
  intro gm res
  dsimp only [gm, res] at *
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK : 0 < slabSize n_max := slabSize_pos n_max
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
  rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
    clientResult_readGMProg s hq_lt, StateTransitionSpec.clientResult_bind,
    clientState_readGMProg, clientResult_readGMProg s hr_lt, hbc_eq]
  split_ifs with hcap_c hcap_q
  · have hcap_eq : min n_max (effBucketCap n_max) = effBucketCap n_max := by omega
    rw [hcap_eq] at hcap_c hcap_q ⊢
    have hdir_pos := dirSlabsPerBucket_pos_of_pos hb_pos
    have hcap_dir := effBucketCap_eq_dirSlabs_mul_slabSize hb_pos
    have hdir_lt_q : dirSlabsPerBucket n_max <
        gmAt d.1 U V w n_max h_space s.mem (4 + 3 * d.2) :=
      (Nat.mul_lt_mul_right hK).mp (by rwa [← hcap_dir])
    have hslab := hinv.multi_slab hb_pos
    have hs_last_dir : dirSlabsPerBucket n_max - 1 < dirSlabsPerBucket n_max := by omega
    have hs_last_q : dirSlabsPerBucket n_max - 1 <
        gmAt d.1 U V w n_max h_space s.mem (gmQIdx d.2) := by
      unfold gmQIdx; omega
    have hdir_idx_lt : gmSlabDirBase n_max + d.2 * dirSlabsPerBucket n_max +
        (dirSlabsPerBucket n_max - 1) < globalMetaLen n_max :=
      gmSlabDirIdx_lt hb_pos hb hs_last_dir
    have hp_prev_eq := hslab.dir_eq d.2 hb (dirSlabsPerBucket n_max - 1) hs_last_q hs_last_dir
    unfold gmSlabDirIdx at hp_prev_eq
    have hp_prev_lt_max : slabPtrOf n_max (gmAt d.1 U V w n_max h_space s.mem) d.2
        (dirSlabsPerBucket n_max - 1) < maxFullSlabs n_max :=
      lt_of_lt_of_le (hslab.ptr_lt d.2 hb _ hs_last_q) hslab.nslabs_le
    rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      clientResult_readGMProg s hdir_idx_lt, hp_prev_eq]
    have habv_lt : gmSlabMetaBase n_max +
        4 * slabPtrOf n_max (gmAt d.1 U V w n_max h_space s.mem) d.2
          (dirSlabsPerBucket n_max - 1) + 3 < globalMetaLen n_max :=
      gmSlabAboveIdx_lt hb_pos hp_prev_lt_max
    rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      clientResult_readGMProg s habv_lt]
    refine ⟨rfl, fun _ _ => ?_⟩
    change gmAt d.1 U V w n_max h_space s.mem
      (gmSlabAboveIdx n_max
        (slabPtrOf n_max (gmAt d.1 U V w n_max h_space s.mem) d.2
          (dirSlabsPerBucket n_max - 1))) = _
    have hs_succ : (dirSlabsPerBucket n_max - 1) + 1 = dirSlabsPerBucket n_max := by omega
    rw [hslab.above_eq d.2 hb _ hs_last_q (by unfold gmQIdx; omega), hs_succ, hcap_dir,
      Nat.mul_div_cancel _ hK]
  · refine ⟨by change _ - _ = _ - _; omega, fun _ hq => by unfold gmQIdx at hq; omega⟩
  · refine ⟨by change 0 = _ - _; omega, fun hc _ => by omega⟩

theorem realizes_initOvfSearchGen :
    Realizes .exact initOvfSearchGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d s => DictEnvGen w d.1 d.2.1 ∧
        d.2.2 < numBuckets (dpNMax d.1) ∧
        SlotStoreInv (dpNMax d.1)
          (gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem) ∧
        0 < bucketBits (dpNMax d.1))
      (fun _ _ => 0) := by
  have hrg := realizes_readGMGen
  realizeDictWith [initOvfSearchGenProg_mk]
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2 hw hnU hU (le_of_lt (gmQIdx_lt h.2.2.2 h.2.1))
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact h.1
  · exact gmQIdx_lt h.2.2.2 h.2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2 hw hnU hU (le_of_lt (gmRIdx_lt h.2.2.2 h.2.1))
  · exact gmRIdx_lt h.2.2.2 h.2.1
  · have hb_pos := h.2.2.2
    have hb0 : bucketBits n_max ≠ 0 := by omega
    have hq_lt : 4 + 3 * d.2 < globalMetaLen n_max := gmQIdx_lt hb_pos h.2.1
    rw [clientResult_readGMProg _ hq_lt]
    have hbc := bCount_le_n_max h.2.2.1 d.2
    unfold bCount at hbc
    simp only [hb0, ↓reduceIte, h.2.1, gmQIdx] at hbc
    exact fits_of_le_max_n_one h.1 hw hnU hU (by omega)
  · have hb_pos := h.2.2.2
    have hb0 : bucketBits n_max ≠ 0 := by omega
    have hq_lt : 4 + 3 * d.2 < globalMetaLen n_max := gmQIdx_lt hb_pos h.2.1
    have hr_lt : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos h.2.1
    rw [clientState_readGMProg, clientResult_readGMProg _ hq_lt, clientResult_readGMProg _ hr_lt]
    have hbc := bCount_le_n_max h.2.2.1 d.2
    unfold bCount at hbc
    simp only [hb0, ↓reduceIte, h.2.1, gmQIdx, gmRIdx] at hbc
    exact fits_of_le_max_n_one h.1 hw hnU hU (by omega)
  · exact le_of_lt hc
  · have hb_pos := h.2.2.2
    have hdir_pos := dirSlabsPerBucket_pos_of_pos hb_pos
    have hs_last_dir : dirSlabsPerBucket n_max - 1 < dirSlabsPerBucket n_max := by omega
    exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU
      (le_of_lt (gmSlabDirIdx_lt hb_pos h.2.1 hs_last_dir))
  · exact h.1
  · have hb_pos := h.2.2.2
    have hdir_pos := dirSlabsPerBucket_pos_of_pos hb_pos
    have hs_last_dir : dirSlabsPerBucket n_max - 1 < dirSlabsPerBucket n_max := by omega
    exact gmSlabDirIdx_lt hb_pos h.2.1 hs_last_dir
  · have hb_pos := h.2.2.2
    have hb0 : bucketBits n_max ≠ 0 := by omega
    have hK : 0 < slabSize n_max := slabSize_pos n_max
    have hq_lt : 4 + 3 * d.2 < globalMetaLen n_max := gmQIdx_lt hb_pos h.2.1
    have hqb := clientResult_readGMProg s (base := d.1) (U := U) (V := V)
      (w := w₀) (h_space := h_space) hq_lt
    rw [hqb] at hc
    have hdir_pos := dirSlabsPerBucket_pos_of_pos hb_pos
    have hs_last_dir : dirSlabsPerBucket n_max - 1 < dirSlabsPerBucket n_max := by omega
    have hdir_idx_lt : gmSlabDirBase n_max + d.2 * dirSlabsPerBucket n_max +
        (dirSlabsPerBucket n_max - 1) < globalMetaLen n_max :=
      gmSlabDirIdx_lt hb_pos h.2.1 hs_last_dir
    repeat rw [clientState_readGMProg]
    rw [clientResult_readGMProg _ hdir_idx_lt]
    have hcap_le : effBucketCap n_max ≤
        gmAt d.1 U V w₀ n_max h_space s.mem (4 + 3 * d.2) * slabSize n_max := by
      have hbc := bCount_le_n_max h.2.2.1 d.2
      unfold bCount at hbc
      simp only [hb0, ↓reduceIte, h.2.1, gmQIdx] at hbc
      omega
    have hcap_dir := effBucketCap_eq_dirSlabs_mul_slabSize hb_pos
    have hdir_le_q : dirSlabsPerBucket n_max ≤
        gmAt d.1 U V w₀ n_max h_space s.mem (gmQIdx d.2) :=
      Nat.le_of_mul_le_mul_right (by unfold gmQIdx; omega) hK
    have hs_last_q : dirSlabsPerBucket n_max - 1 <
        gmAt d.1 U V w₀ n_max h_space s.mem (gmQIdx d.2) := by omega
    have hslab := h.2.2.1.multi_slab hb_pos
    have hp_prev_eq := hslab.dir_eq d.2 h.2.1 (dirSlabsPerBucket n_max - 1) hs_last_q hs_last_dir
    unfold gmSlabDirIdx at hp_prev_eq
    rw [hp_prev_eq]
    have hp_lt_max : slabPtrOf n_max (gmAt d.1 U V w₀ n_max h_space s.mem) d.2
        (dirSlabsPerBucket n_max - 1) < maxFullSlabs n_max :=
      lt_of_lt_of_le (hslab.ptr_lt d.2 h.2.1 _ hs_last_q) hslab.nslabs_le
    exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU
      (le_of_lt (gmSlabAboveIdx_lt hb_pos hp_lt_max))
  · exact fits_const_of_dictEnv h.1 (by decide)
  · have hb_pos := h.2.2.2
    have hb0 : bucketBits n_max ≠ 0 := by omega
    have hK : 0 < slabSize n_max := slabSize_pos n_max
    have hq_lt : 4 + 3 * d.2 < globalMetaLen n_max := gmQIdx_lt hb_pos h.2.1
    have hqb := clientResult_readGMProg s (base := d.1) (U := U) (V := V)
      (w := w₀) (h_space := h_space) hq_lt
    rw [hqb] at hc
    have hdir_pos := dirSlabsPerBucket_pos_of_pos hb_pos
    have hs_last_dir : dirSlabsPerBucket n_max - 1 < dirSlabsPerBucket n_max := by omega
    have hdir_idx_lt : gmSlabDirBase n_max + d.2 * dirSlabsPerBucket n_max +
        (dirSlabsPerBucket n_max - 1) < globalMetaLen n_max :=
      gmSlabDirIdx_lt hb_pos h.2.1 hs_last_dir
    repeat rw [clientState_readGMProg]
    rw [clientResult_readGMProg _ hdir_idx_lt]
    have hcap_le : effBucketCap n_max ≤
        gmAt d.1 U V w₀ n_max h_space s.mem (4 + 3 * d.2) * slabSize n_max := by
      have hbc := bCount_le_n_max h.2.2.1 d.2
      unfold bCount at hbc
      simp only [hb0, ↓reduceIte, h.2.1, gmQIdx] at hbc
      omega
    have hcap_dir := effBucketCap_eq_dirSlabs_mul_slabSize hb_pos
    have hdir_le_q : dirSlabsPerBucket n_max ≤
        gmAt d.1 U V w₀ n_max h_space s.mem (gmQIdx d.2) :=
      Nat.le_of_mul_le_mul_right (by unfold gmQIdx; omega) hK
    have hs_last_q : dirSlabsPerBucket n_max - 1 <
        gmAt d.1 U V w₀ n_max h_space s.mem (gmQIdx d.2) := by omega
    have hslab := h.2.2.1.multi_slab hb_pos
    have hp_prev_eq := hslab.dir_eq d.2 h.2.1 (dirSlabsPerBucket n_max - 1) hs_last_q hs_last_dir
    unfold gmSlabDirIdx at hp_prev_eq
    rw [hp_prev_eq]
    have hp_lt_max : slabPtrOf n_max (gmAt d.1 U V w₀ n_max h_space s.mem) d.2
        (dirSlabsPerBucket n_max - 1) < maxFullSlabs n_max :=
      lt_of_lt_of_le (hslab.ptr_lt d.2 h.2.1 _ hs_last_q) hslab.nslabs_le
    exact gmSlabAboveIdx_lt hb_pos hp_lt_max

/-- Parameter-free Phase 2 overflow search `searchOverflowGenProg`: scans overflow slots
`j ∈ [effBucketCap n_max, bCount n_max gm b)` in bucket `b = d.2.1.2` for quotient
`q_target = d.2.2`, returning `((found, j_found), phys_found)`. -/
@[expose] def searchOverflowGenProg (d : DictParams × ((ℕ × ℕ) × ℕ)) :
    Memory.Prog ((ℕ × ℕ) × ℕ) :=
  if dpBucketBits d.1 = 0 then do
    let z0 ← pure 0
    pure ((z0, z0), z0)
  else do
    let init ← initOvfSearchGenProg (d.1, d.2.1)
    let j0 ← pure (dpMinCap d.1)
    let z0 ← pure 0
    let res ← ovfLoopGenProg
      (((d.1, d.2), ((((j0, init.1), z0), z0), z0)), init.2)
    pure ((res.1.1.2, res.1.2), res.2)

/-- Phase 2 overflow search `searchOverflowProg`: scans overflow slots
`j ∈ [effBucketCap n_max, bCount n_max gm b)` in bucket `b = d.1.2` for quotient `q_target = d.2`,
returning `((found, j_found), phys_found)`. -/
@[expose] def searchOverflowProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) :
    Memory.Prog ((ℕ × ℕ) × ℕ) :=
  if bucketBits n_max = 0 then do
    let z0 ← pure 0
    pure ((z0, z0), z0)
  else do
    let init ← initOvfSearchProg U V w n_max h_space d.1
    let j0 ← pure (min n_max (effBucketCap n_max))
    let z0 ← pure 0
    let res ← ovfLoopProg U V w n_max h_space
      ((d, ((((j0, init.1), z0), z0), z0)), init.2)
    pure ((res.1.1.2, res.1.2), res.2)

@[simp]
theorem searchOverflowGenProg_mk (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) :
    searchOverflowGenProg (mkDictParams U V w n_max h_space, d) =
      searchOverflowProg U V w n_max h_space d := by
  simp only [searchOverflowGenProg, searchOverflowProg, p_bucketBits_mk, p_minCap_mk,
    initOvfSearchGenProg_mk, ovfLoopGenProg_mk]

/-- Precondition for `searchOverflowProg` (`d = ((base, b), q_target)`). -/
@[expose] def SearchOverflowPre (U V w₀ n_max h_space w : ℕ)
    (d : (ℕ × ℕ) × ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) d.1.1 ∧
  d.1.2 < numBuckets n_max ∧
  SlotStoreInv n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem)

/-- Parameter-free precondition for `searchOverflowGenProg`. -/
@[expose] def SearchOverflowGenPre (w : ℕ)
    (d : DictParams × ((ℕ × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w d.1 d.2.1.1 ∧
  d.2.1.2 < numBuckets (dpNMax d.1) ∧
  SlotStoreInv (dpNMax d.1)
    (gmAt d.2.1.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem)

@[simp]
theorem searchOverflowGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    SearchOverflowGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      SearchOverflowPre U V w₀ n_max h_space w d s := Iff.rfl

open Classical in
theorem searchOverflowProg_spec {U V w₀ n_max h_space w : ℕ}
    {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) d.1.1)
    (hb : d.1.2 < numBuckets n_max)
    (hinv : SlotStoreInv n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem)) :
    let gm := gmAt d.1.1 U V w₀ n_max h_space s.mem
    let prog := searchOverflowProg U V w₀ n_max h_space d
    (Memory.spec 0).clientState s prog = s ∧
    memoryCost prog s ≤ 8 + 6 * (bCount n_max gm d.1.2 - effBucketCap n_max) ∧
    (0 < bucketBits n_max →
      let init := (Memory.spec 0).clientResult s (initOvfSearchProg U V w₀ n_max h_space d.1)
      iterationSafe (ovfStepProg U V w₀ n_max h_space)
        (OvfStepPre U V w₀ n_max h_space) w d init.2
        ((((min n_max (effBucketCap n_max), init.1), 0), 0), 0) s) ∧
    (let res := (Memory.spec 0).clientResult s prog
     if ∃ j, effBucketCap n_max ≤ j ∧ j < bCount n_max gm d.1.2 ∧
         quotAt d.1.1 U w₀ n_max h_space s.mem (slotOf n_max gm d.1.2 j) = d.2 then
       res.1.1 = 1 ∧ effBucketCap n_max ≤ res.1.2 ∧ res.1.2 < bCount n_max gm d.1.2 ∧
       quotAt d.1.1 U w₀ n_max h_space s.mem (slotOf n_max gm d.1.2 res.1.2) = d.2 ∧
       res.2 = slotOf n_max gm d.1.2 res.1.2
     else
       res.1.1 = 0) := by
  intro gm prog
  dsimp only [gm, prog] at *
  rcases Nat.eq_zero_or_pos (bucketBits n_max) with hb0 | hb_pos
  · have hbc_le : bCount n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2 ≤ n_max :=
      bCount_le_n_max hinv d.1.2
    have hlt_cap : n_max < effBucketCap n_max := lt_effBucketCap_of_bucketBits_eq_zero hb0
    have hno : ¬∃ j, effBucketCap n_max ≤ j ∧
        j < bCount n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2 ∧
        quotAt d.1.1 U w₀ n_max h_space s.mem
          (slotOf n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2 j) = d.2 := by
      rintro ⟨j, hj1, hj2, _⟩; omega
    refine ⟨by simp [searchOverflowProg, hb0]; rfl,
      by simp [searchOverflowProg, hb0],
      fun h => by omega, ?_⟩
    dsimp only [searchOverflowProg]
    rw [ite_eq_left hb0, ite_eq_right hno]
    rfl
  · have hb0 : bucketBits n_max ≠ 0 := by omega
    have hinit := clientResult_initOvfSearchProg (d := d.1) s hb_pos hb hinv
    set init := (Memory.spec 0).clientResult s (initOvfSearchProg U V w₀ n_max h_space d.1)
    dsimp only at hinit
    have hbc_le : bCount n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2 ≤ n_max :=
      bCount_le_n_max hinv d.1.2
    by_cases hovf : effBucketCap n_max < bCount n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2
    · have hmin_eq : min n_max (effBucketCap n_max) = effBucketCap n_max := by omega
      have hjm : effBucketCap n_max + init.2 ≤
          bCount n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2 := by
        rw [hinit.1]; omega
      have hjm_eq : effBucketCap n_max + init.2 =
          bCount n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2 := by
        rw [hinit.1]; omega
      have hp0 : effBucketCap n_max <
          gmAt d.1.1 U V w₀ n_max h_space s.mem (gmQIdx d.1.2) * slabSize n_max →
          init.1 = slabPtrOf n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2
            (effBucketCap n_max / slabSize n_max) :=
        hinit.2 hovf
      have hloop := iterate_ovfStepProg_spec (q_target := d.2) hb_pos henv hb hinv
        init.2 (effBucketCap n_max) init.1 0 0 0 hjm hp0
      dsimp only at hloop
      refine ⟨?_, ?_, ?_, ?_⟩
      · unfold searchOverflowProg ovfLoopProg
        rw [ite_eq_right hb0]
        simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, clientState_initOvfSearchProg,
          StateTransitionSpec.clientState_bind, hmin_eq]
        change (Memory.spec 0).clientState
          ((Memory.spec 0).clientState s
            (iterate (ovfStepProg U V w₀ n_max h_space) ((d.1.1, d.1.2), d.2) init.2
              ((((effBucketCap n_max, init.1), 0), 0), 0))) _ = s
        rw [hloop.1]
        rfl
      · unfold searchOverflowProg ovfLoopProg
        rw [ite_eq_right hb0]
        simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
        rw [memoryCost_bind, clientState_initOvfSearchProg, memoryCost_bind, hmin_eq]
        have h1 := memoryCost_initOvfSearchProg_le U V w₀ n_max h_space d.1 s
        have h2 := hloop.2.1
        change memoryCost (initOvfSearchProg U V w₀ n_max h_space d.1) s +
          (memoryCost (iterate (ovfStepProg U V w₀ n_max h_space) ((d.1.1, d.1.2), d.2) init.2
            ((((effBucketCap n_max, init.1), 0), 0), 0)) s + 0) ≤ _
        rw [hinit.1] at h2
        omega
      · intro _
        rw [hmin_eq]
        exact hloop.2.2.1
      · unfold searchOverflowProg ovfLoopProg
        rw [ite_eq_right hb0]
        simp only [pure_bind]
        rw [StateTransitionSpec.clientResult_bind, clientState_initOvfSearchProg,
          StateTransitionSpec.clientResult_bind, hmin_eq]
        have hres := hloop.2.2.2
        rw [ite_eq_left rfl, hjm_eq] at hres
        exact hres
    · have hfuel0 : init.2 = 0 := by rw [hinit.1]; omega
      have hno : ¬∃ j, effBucketCap n_max ≤ j ∧
          j < bCount n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2 ∧
          quotAt d.1.1 U w₀ n_max h_space s.mem
            (slotOf n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2 j) = d.2 := by
        rintro ⟨j, hj1, hj2, _⟩; omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · unfold searchOverflowProg ovfLoopProg
        rw [ite_eq_right hb0]
        simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, clientState_initOvfSearchProg]
        change (Memory.spec 0).clientState s
          (do
            let res ← iterate (ovfStepProg U V w₀ n_max h_space) d init.2
              ((((min n_max (effBucketCap n_max), init.1), 0), 0), 0)
            pure ((res.1.1.2, res.1.2), res.2)) = s
        rw [hfuel0, iterate]
        rfl
      · unfold searchOverflowProg ovfLoopProg
        rw [ite_eq_right hb0]
        simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
        rw [memoryCost_bind, clientState_initOvfSearchProg]
        change memoryCost (initOvfSearchProg U V w₀ n_max h_space d.1) s +
          memoryCost (PFunctor.FreeM.bind
            (iterate (ovfStepProg U V w₀ n_max h_space) d init.2
              ((((min n_max (effBucketCap n_max), init.1), 0), 0), 0))
            (fun res => pure ((res.1.1.2, res.1.2), res.2))) s ≤ _
        rw [hfuel0, iterate]
        have := memoryCost_initOvfSearchProg_le U V w₀ n_max h_space d.1 s
        change memoryCost (initOvfSearchProg U V w₀ n_max h_space d.1) s + 0 ≤ _
        omega
      · intro _
        rw [hfuel0]
        trivial
      · unfold searchOverflowProg ovfLoopProg
        rw [ite_eq_right hb0, ite_eq_right hno]
        simp only [pure_bind]
        rw [StateTransitionSpec.clientResult_bind, clientState_initOvfSearchProg]
        change ((Memory.spec 0).clientResult s
          (do
            let res ← iterate (ovfStepProg U V w₀ n_max h_space) d init.2
              ((((min n_max (effBucketCap n_max), init.1), 0), 0), 0)
            pure ((res.1.1.2, res.1.2), res.2))).1.1 = 0
        rw [hfuel0, iterate]
        rfl

theorem realizes_searchOverflowGen :
    Realizes .exact searchOverflowGenProg
      (WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      SearchOverflowGenPre
      (fun _ _ => 0) := by
  have hinit := realizes_initOvfSearchGen
  have hloop := realizes_ovfLoopGen
  refine Realizes.congr (p := fun d : DictParams × ((ℕ × ℕ) × ℕ) => do
      let z0 ← pure 0
      if dpBucketBits d.1 = z0 then
        pure ((z0, z0), z0)
      else
        let init ← initOvfSearchGenProg (d.1, d.2.1)
        let j0 ← pure (dpMinCap d.1)
        let res ← ovfLoopGenProg
          (((d.1, d.2), ((((j0, init.1), z0), z0), z0)), init.2)
        pure ((res.1.1.2, res.1.2), res.2)) ?_
    (fun d => by simp only [searchOverflowGenProg, ← PFunctor.FreeM.bind_eq_bind, pure_bind])
  realizeDictWith [searchOverflowGenPre_mk, SearchOverflowPre,
    initOvfSearchGenProg_mk, ovfLoopGenProg_mk, iterationSafe_ovfStepGenProg_mk]
  · exact h.1
  · exact h.2.1
  · exact h.2.2
  · exact Nat.pos_of_ne_zero hc
  · rw [clientState_initOvfSearchProg]
    exact (searchOverflowProg_spec h.1 h.2.1 h.2.2).2.2.1 (Nat.pos_of_ne_zero hc)

/-! ## Section 3: Combined Two-Phase Bucket Search (`searchBucketProg`) and `queryBodyProg` -/

/-- Parameter-free two-phase bucket search `searchBucketGenProg`
(`d = (dp, (((base, b), q_target), m))`):
first searches the micro-bucket chain `(b, m)` via `searchMicroChainGenProg`; if not found,
searches any overflow slots `j ∈ [effBucketCap n_max, bCount n_max gm b)` via
`searchOverflowGenProg`. Returns `((found, j_found), phys_found)`. -/
@[expose] def searchBucketGenProg
    (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) : Memory.Prog ((ℕ × ℕ) × ℕ) := do
  let res1 ← searchMicroChainGenProg d
  let z1 ← pure 1
  if res1.1.1.2 = z1 then
    pure ((z1, res1.1.2), res1.2)
  else
    searchOverflowGenProg (d.1, d.2.1)

/-- Two-phase bucket search `searchBucketProg` (`d = (((base, b), q_target), m)`):
first searches the micro-bucket chain `(b, m)` via `searchMicroChainProg`; if not found,
searches any overflow slots `j ∈ [effBucketCap n_max, bCount n_max gm b)` via
`searchOverflowProg`. Returns `((found, j_found), phys_found)`. -/
@[expose] def searchBucketProg (U V w n_max h_space : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ((ℕ × ℕ) × ℕ) := do
  let res1 ← searchMicroChainProg U V w n_max h_space d
  let z1 ← pure 1
  if res1.1.1.2 = z1 then
    pure ((z1, res1.1.2), res1.2)
  else
    searchOverflowProg U V w n_max h_space d.1

@[simp]
theorem searchBucketGenProg_mk (U V w n_max h_space : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    searchBucketGenProg (mkDictParams U V w n_max h_space, d) =
      searchBucketProg U V w n_max h_space d := by
  simp only [searchBucketGenProg, searchBucketProg, searchMicroChainGenProg_mk,
    searchOverflowGenProg_mk]

open Classical in
theorem searchBucketProg_spec {U V w₀ n_max h_space w : ℕ}
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State} {L : List ℕ}
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) d.1.1.1)
    (hb : d.1.1.2 < numBuckets n_max)
    (hm : d.2 < numMicroPerBucket n_max)
    (hinv : SlotStoreInv n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem))
    (hchain : IsDLChain n_max (lmHead n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 d.2)
      (lmPrev n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2)
      (lmNext n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2) L)
    (hc_lt : ∀ j ∈ L, j < bCount n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2) :
    let gm := gmAt d.1.1.1 U V w₀ n_max h_space s.mem
    let prog := searchBucketProg U V w₀ n_max h_space d
    (Memory.spec 0).clientState s prog = s ∧
    memoryCost prog s ≤
      10 + 8 * L.length + 6 * (bCount n_max gm d.1.1.2 - effBucketCap n_max) ∧
    (let res := (Memory.spec 0).clientResult s prog
     if (∃ j ∈ L, quotAt d.1.1.1 U w₀ n_max h_space s.mem (slotOf n_max gm d.1.1.2 j) = d.1.2) ∨
        (∃ j, effBucketCap n_max ≤ j ∧ j < bCount n_max gm d.1.1.2 ∧
          quotAt d.1.1.1 U w₀ n_max h_space s.mem (slotOf n_max gm d.1.1.2 j) = d.1.2) then
       res.1.1 = 1 ∧ res.1.2 < bCount n_max gm d.1.1.2 ∧
       (res.1.2 ∈ L ∨ effBucketCap n_max ≤ res.1.2) ∧
       quotAt d.1.1.1 U w₀ n_max h_space s.mem (slotOf n_max gm d.1.1.2 res.1.2) = d.1.2 ∧
       res.2 = slotOf n_max gm d.1.1.2 res.1.2
     else
       res.1.1 = 0) := by
  intro gm prog
  dsimp only [gm, prog] at *
  have h1 := searchMicroChainProg_spec henv hb hm hinv hchain hc_lt
  have h2 := searchOverflowProg_spec (d := d.1) henv hb hinv
  dsimp only at h1 h2
  set res1 := (Memory.spec 0).clientResult s (searchMicroChainProg U V w₀ n_max h_space d)
  have hres1_spec := h1.2.2.2
  by_cases hex1 : ∃ j ∈ L,
      quotAt d.1.1.1 U w₀ n_max h_space s.mem
        (slotOf n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 j) = d.1.2
  · rw [ite_eq_left hex1] at hres1_spec
    have hf1 : res1.1.1.2 = 1 := by rw [hres1_spec.1]
    have hres_eq : (Memory.spec 0).clientResult s (searchBucketProg U V w₀ n_max h_space d) =
        ((1, res1.1.2), res1.2) := by
      unfold searchBucketProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientResult_bind, h1.1]
      change (Memory.spec 0).clientResult s
        (if res1.1.1.2 = 1 then pure ((1, res1.1.2), res1.2)
         else searchOverflowProg U V w₀ n_max h_space d.1) = _
      rw [ite_eq_left hf1]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · unfold searchBucketProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, h1.1]
      change (Memory.spec 0).clientState s
        (if res1.1.1.2 = 1 then pure ((1, res1.1.2), res1.2)
         else searchOverflowProg U V w₀ n_max h_space d.1) = s
      rw [ite_eq_left hf1]
      rfl
    · unfold searchBucketProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
      rw [memoryCost_bind, h1.1]
      change memoryCost (searchMicroChainProg U V w₀ n_max h_space d) s +
        memoryCost (if res1.1.1.2 = 1 then pure ((1, res1.1.2), res1.2)
          else searchOverflowProg U V w₀ n_max h_space d.1) s ≤ _
      rw [ite_eq_left hf1]
      have := h1.2.1
      change memoryCost (searchMicroChainProg U V w₀ n_max h_space d) s + 0 ≤ _
      omega
    · rw [hres_eq, ite_eq_left (Or.inl hex1)]
      exact ⟨rfl, hc_lt _ hres1_spec.2.1, Or.inl hres1_spec.2.1,
        hres1_spec.2.2.1, hres1_spec.2.2.2⟩
  · rw [ite_eq_right hex1] at hres1_spec
    have hf0 : res1.1.1.2 = 0 := by rw [hres1_spec]
    have hne1 : res1.1.1.2 ≠ 1 := by omega
    have hres_eq : (Memory.spec 0).clientResult s (searchBucketProg U V w₀ n_max h_space d) =
        (Memory.spec 0).clientResult s (searchOverflowProg U V w₀ n_max h_space d.1) := by
      unfold searchBucketProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientResult_bind, h1.1]
      change (Memory.spec 0).clientResult s
        (if res1.1.1.2 = 1 then pure ((1, res1.1.2), res1.2)
         else searchOverflowProg U V w₀ n_max h_space d.1) = _
      rw [ite_eq_right hne1]
    refine ⟨?_, ?_, ?_⟩
    · unfold searchBucketProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, h1.1]
      change (Memory.spec 0).clientState s
        (if res1.1.1.2 = 1 then pure ((1, res1.1.2), res1.2)
         else searchOverflowProg U V w₀ n_max h_space d.1) = s
      rw [ite_eq_right hne1]
      exact h2.1
    · unfold searchBucketProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
      rw [memoryCost_bind, h1.1]
      change memoryCost (searchMicroChainProg U V w₀ n_max h_space d) s +
        memoryCost (if res1.1.1.2 = 1 then pure ((1, res1.1.2), res1.2)
          else searchOverflowProg U V w₀ n_max h_space d.1) s ≤ _
      rw [ite_eq_right hne1]
      have hc1 := h1.2.1
      have hc2 := h2.2.1
      omega
    · rw [hres_eq]
      have hres2_spec := h2.2.2.2
      by_cases hex2 : ∃ j, effBucketCap n_max ≤ j ∧
          j < bCount n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 ∧
          quotAt d.1.1.1 U w₀ n_max h_space s.mem
            (slotOf n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 j) = d.1.2
      · rw [ite_eq_left hex2] at hres2_spec
        rw [ite_eq_left (Or.inr hex2)]
        exact ⟨hres2_spec.1, hres2_spec.2.2.1, Or.inr hres2_spec.2.1,
          hres2_spec.2.2.2.1, hres2_spec.2.2.2.2⟩
      · rw [ite_eq_right hex2] at hres2_spec
        have hno : ¬((∃ j ∈ L,
            quotAt d.1.1.1 U w₀ n_max h_space s.mem
              (slotOf n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 j) = d.1.2) ∨
          (∃ j, effBucketCap n_max ≤ j ∧
            j < bCount n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 ∧
            quotAt d.1.1.1 U w₀ n_max h_space s.mem
              (slotOf n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 j) = d.1.2)) := by
          rintro (h | h)
          · exact hex1 h
          · exact hex2 h
        rw [ite_eq_right hno]
        exact hres2_spec

theorem realizes_searchBucketGen :
    Realizes .exact searchBucketGenProg
      (WordEncoding.encode (α := DictParams × (((ℕ × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      SearchMicroChainGenPre
      (fun _ _ => 0) := by
  have hm := realizes_searchMicroChainGen
  have ho := realizes_searchOverflowGen
  realizeDictWith [searchMicroChainGenPre_mk, SearchMicroChainPre, searchMicroChainGenProg_mk,
    searchOverflowGenPre_mk, SearchOverflowPre, searchOverflowGenProg_mk]
  · exact h
  · exact fits_const_of_dictEnv h.1 (by decide)
  · obtain ⟨L, hchain, hc_lt⟩ := h.2.2.2.2
    rw [(searchMicroChainProg_spec h.1 h.2.1 h.2.2.1 h.2.2.2.1 hchain hc_lt).1]
    exact ⟨h.1, h.2.1, h.2.2.2.1⟩

/-- Parameter-free dictionary lookup body `queryBodyGenProg`
(`d = (dp, (((base, b), q_target), m))`):
calls `searchBucketGenProg` and, if found (`res.1.1 = 1`), reads and returns `some v` from `Values`
at physical slot `res.2`, otherwise returns `none`. -/
@[expose] def queryBodyGenProg
    (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) : Memory.Prog (Option ℕ) := do
  let res ← searchBucketGenProg d
  let z1 ← pure 1
  if res.1.1 = z1 then do
    let v ← readValGenProg (d.1, (d.2.1.1.1, res.2))
    pure (some v)
  else
    pure none

/-- Dictionary lookup body `queryBodyProg` (`d = (((base, b), q_target), m)`):
calls `searchBucketProg` and, if found (`res.1.1 = 1`), reads and returns `some v` from `Values`
at physical slot `res.2`, otherwise returns `none`. -/
@[expose] def queryBodyProg (U V w n_max h_space : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog (Option ℕ) := do
  let res ← searchBucketProg U V w n_max h_space d
  let z1 ← pure 1
  if res.1.1 = z1 then do
    let v ← readValProg U V w n_max h_space (d.1.1.1, res.2)
    pure (some v)
  else
    pure none

@[simp]
theorem queryBodyGenProg_mk (U V w n_max h_space : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    queryBodyGenProg (mkDictParams U V w n_max h_space, d) =
      queryBodyProg U V w n_max h_space d := by
  simp only [queryBodyGenProg, queryBodyProg, searchBucketGenProg_mk, readValGenProg_mk]

open Classical in
theorem queryBodyProg_spec {U V w₀ n_max h_space w : ℕ}
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State} {L : List ℕ}
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) d.1.1.1)
    (hb : d.1.1.2 < numBuckets n_max)
    (hm : d.2 < numMicroPerBucket n_max)
    (hinv : SlotStoreInv n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem))
    (hchain : IsDLChain n_max (lmHead n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 d.2)
      (lmPrev n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2)
      (lmNext n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2) L)
    (hc_lt : ∀ j ∈ L, j < bCount n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2) :
    let gm := gmAt d.1.1.1 U V w₀ n_max h_space s.mem
    let prog := queryBodyProg U V w₀ n_max h_space d
    (Memory.spec 0).clientState s prog = s ∧
    memoryCost prog s ≤
      12 + 8 * L.length + 6 * (bCount n_max gm d.1.1.2 - effBucketCap n_max) ∧
    (let res := (Memory.spec 0).clientResult s prog
     if (∃ j ∈ L, quotAt d.1.1.1 U w₀ n_max h_space s.mem (slotOf n_max gm d.1.1.2 j) = d.1.2) ∨
        (∃ j, effBucketCap n_max ≤ j ∧ j < bCount n_max gm d.1.1.2 ∧
          quotAt d.1.1.1 U w₀ n_max h_space s.mem (slotOf n_max gm d.1.1.2 j) = d.1.2) then
       ∃ j < bCount n_max gm d.1.1.2,
         quotAt d.1.1.1 U w₀ n_max h_space s.mem (slotOf n_max gm d.1.1.2 j) = d.1.2 ∧
         res = some (valAt d.1.1.1 U V w₀ n_max h_space s.mem (slotOf n_max gm d.1.1.2 j))
     else
       res = none) := by
  intro gm prog
  dsimp only [gm, prog] at *
  have hsb := searchBucketProg_spec henv hb hm hinv hchain hc_lt
  dsimp only at hsb
  set res := (Memory.spec 0).clientResult s (searchBucketProg U V w₀ n_max h_space d)
  have hsb_res := hsb.2.2
  by_cases hex :
      (∃ j ∈ L, quotAt d.1.1.1 U w₀ n_max h_space s.mem
        (slotOf n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 j) = d.1.2) ∨
      (∃ j, effBucketCap n_max ≤ j ∧
        j < bCount n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 ∧
        quotAt d.1.1.1 U w₀ n_max h_space s.mem
          (slotOf n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 j) = d.1.2)
  · rw [ite_eq_left hex] at hsb_res
    have hf1 : res.1.1 = 1 := hsb_res.1
    have hphys_lt : res.2 < n_max := by
      rw [hsb_res.2.2.2.2]
      exact (slotOf_lt_and_injective hinv).1 d.1.1.2 hb res.1.2 hsb_res.2.1
    have hres_eq : (Memory.spec 0).clientResult s (queryBodyProg U V w₀ n_max h_space d) =
        some (valAt d.1.1.1 U V w₀ n_max h_space s.mem res.2) := by
      unfold queryBodyProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientResult_bind, hsb.1]
      change (Memory.spec 0).clientResult s
        (if res.1.1 = 1 then do
          let v ← readValProg U V w₀ n_max h_space (d.1.1.1, res.2)
          pure (some v)
         else pure none) = _
      rw [ite_eq_left hf1, StateTransitionSpec.clientResult_bind,
        clientState_readValProg, clientResult_readValProg s hphys_lt]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · unfold queryBodyProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, hsb.1]
      change (Memory.spec 0).clientState s
        (if res.1.1 = 1 then do
          let v ← readValProg U V w₀ n_max h_space (d.1.1.1, res.2)
          pure (some v)
         else pure none) = s
      rw [ite_eq_left hf1, StateTransitionSpec.clientState_bind, clientState_readValProg]
      rfl
    · unfold queryBodyProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
      rw [memoryCost_bind, hsb.1]
      change memoryCost (searchBucketProg U V w₀ n_max h_space d) s +
        memoryCost (if res.1.1 = 1 then
          PFunctor.FreeM.bind (readValProg U V w₀ n_max h_space (d.1.1.1, res.2))
            (fun v => pure (some v))
          else pure none) s ≤ _
      rw [ite_eq_left hf1, memoryCost_bind, memoryCost_readValProg]
      have := hsb.2.1
      change memoryCost (searchBucketProg U V w₀ n_max h_space d) s + (2 + 0) ≤ _
      omega
    · rw [hres_eq, ite_eq_left hex]
      exact ⟨res.1.2, hsb_res.2.1, hsb_res.2.2.2.1, by rw [hsb_res.2.2.2.2]⟩
  · rw [ite_eq_right hex] at hsb_res
    have hne1 : res.1.1 ≠ 1 := by omega
    have hres_eq : (Memory.spec 0).clientResult s (queryBodyProg U V w₀ n_max h_space d) =
        none := by
      unfold queryBodyProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientResult_bind, hsb.1]
      change (Memory.spec 0).clientResult s
        (if res.1.1 = 1 then do
          let v ← readValProg U V w₀ n_max h_space (d.1.1.1, res.2)
          pure (some v)
         else pure none) = _
      rw [ite_eq_right hne1]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · unfold queryBodyProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, hsb.1]
      change (Memory.spec 0).clientState s
        (if res.1.1 = 1 then do
          let v ← readValProg U V w₀ n_max h_space (d.1.1.1, res.2)
          pure (some v)
         else pure none) = s
      rw [ite_eq_right hne1]
      rfl
    · unfold queryBodyProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
      rw [memoryCost_bind, hsb.1]
      change memoryCost (searchBucketProg U V w₀ n_max h_space d) s +
        memoryCost (if res.1.1 = 1 then
          PFunctor.FreeM.bind (readValProg U V w₀ n_max h_space (d.1.1.1, res.2))
            (fun v => pure (some v))
          else pure none) s ≤ _
      rw [ite_eq_right hne1]
      have := hsb.2.1
      change memoryCost (searchBucketProg U V w₀ n_max h_space d) s + 0 ≤ _
      omega
    · rw [hres_eq, ite_eq_right hex]

theorem realizes_queryBodyGen :
    Realizes .exact queryBodyGenProg
      (WordEncoding.encode (α := DictParams × (((ℕ × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := Option ℕ))
      SearchMicroChainGenPre
      (fun _ _ => 0) := by
  have hsb := realizes_searchBucketGen
  have hrv := realizes_readValGen
  realizeDictWith [searchMicroChainGenPre_mk, SearchMicroChainPre, searchBucketGenProg_mk]
  · exact h
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact h.1
  · obtain ⟨L, hchain, hc_lt⟩ := h.2.2.2.2
    have hspec := (searchBucketProg_spec h.1 h.2.1 h.2.2.1 h.2.2.2.1 hchain hc_lt).2.2
    dsimp only at hspec
    by_cases hex :
        (∃ j ∈ L, quotAt d.1.1.1 U w₀ n_max h_space s.mem
          (slotOf n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 j) = d.1.2) ∨
        (∃ j, effBucketCap n_max ≤ j ∧
          j < bCount n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 ∧
          quotAt d.1.1.1 U w₀ n_max h_space s.mem
            (slotOf n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 j) = d.1.2)
    · rw [ite_eq_left hex] at hspec
      rw [hspec.2.2.2.2]
      exact (slotOf_lt_and_injective h.2.2.2.1).1 d.1.1.2 h.2.1 _ hspec.2.1
    · rw [ite_eq_right hex] at hspec
      omega
  · exact fits_const_of_dictEnv h.1 (by decide)

end Cslib.DataStructure.Dictionary.WordRAM.Succinct

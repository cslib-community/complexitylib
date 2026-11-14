/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise.ParamsInit
public import CslibFrontier.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise.Horner

/-!
# Runtime-Parameterized `ReducedKWise` Hashing on the Resizable Word RAM

Completes the parameter-free (`¬ReadsWidth`) Word-RAM / Resizable Word RAM compilation of the
two-stage universe-reduced $k$-wise independent polynomial hash family of
[BenderFarachColtonKuszmaulKuszmaul2024] (`Cslib.Probability.reducedPolyHash`):
* `evalHashGenProg`: runtime polynomial evaluation and `b'`-bit output extraction in `Memory.Prog`
  certified via `by realize` (`RealizesBounded .exact`), using `O(k)` deterministic operations and
  the 162-word scratch slice `[scratchBase, scratchBase + 162)` rather than 240 static registers;
* `resampleHashCode`: parameter-free `RCode .exact r` subroutine resampling a uniform seed
  `ReducedPolySeed w₀ b b' k` (`ExecRCodeDist`).

Re-exports `RuntimeReducedKWise.ParamsInit` (`HashParams`, `mkHashParams`, `initTableGenProg`) and
`RuntimeReducedKWise.Horner`.

## Main definitions

* `Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise.evalHashGenProg`, `evalMemBound`,
  `EvalHashGenPre`: runtime `k`-wise polynomial hash evaluator in `Memory.Prog`.
* `Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise.resampleHashCode`: parameter-free
  `RCode .exact r` subroutine resampling a uniform `ReducedPolySeed w₀ b b' k`.

## Main results

* `evalHashGenProg_spec`, `realizesBounded_evalHashGen`: exact agreement with
  `Cslib.Probability.reducedPolyHash`, `O(k)` memory cost,
    and `RealizesBounded .exact` certificate.
* `not_readsWidth_resampleHashCode`, `resampleHashCode_execRCodeDist`: width-independence and
  `ExecRCodeDist` uniform seed-sampling specification on the Resizable Word RAM.

## References

* [BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.HashFamily.WordRAM Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise
open Cslib.Probability
open scoped ENNReal

local notation "rStep" => reducedTrinomialStep
local notation "rChunk" w₀:arg b:arg b':arg => reducedChunkBits (reducedTrinomialStep w₀ b b')
local notation "rHalf" w₀:arg b:arg b':arg => reducedHalfLimbs (reducedTrinomialStep w₀ b b')
local notation "rLimbs" w₀:arg b:arg b':arg => reducedLimbCount (reducedTrinomialStep w₀ b b')
local notation "rPack" w:arg w₀:arg b:arg b':arg =>
  reducedPackShift (reducedTrinomialStep w₀ b b') w

/-! ## Section 1: Output limb packing and full `evalHashGenProg` -/

private def packOutStepGenProg :
    (HashParams × ℕ) × (ℕ × ℕ × ℕ × ℕ) → Memory.Prog (ℕ × ℕ × ℕ × ℕ)
  | ((hp, scratchBase), (m, out, remB, sh)) => do
    let limb ← Memory.read (scratchBase + m)
    let c := hpC hp
    if 0 < remB then
      if c < remB then
        let part := (limb &&& hpMaskC hp) <<< sh
        pure (m + 1, out ^^^ part, remB - c, sh + c)
      else
        let mask := (1 <<< remB) - 1
        let part := (limb &&& mask) <<< sh
        pure (m + 1, out ^^^ part, 0, sh + remB)
    else
      pure (m + 1, out, 0, sh)

private def PackOutStepPre (w : ℕ) :
    (HashParams × ℕ) × (ℕ × ℕ × ℕ × ℕ) → Memory.State → Prop
  | ((hp, scratchBase), (m, out, remB, sh)), s => ∃ w₀ b b' k,
    b' ≤ w ∧ 2 * rChunk w₀ b b' < w ∧ hp = mkHashParams w w₀ b b' k ∧
    scratchBase + scratchWords ≤ s.frontier ∧
    m < rLimbs w₀ b b' ∧ out < 2 ^ w ∧ remB ≤ b' ∧ sh + remB = b'

private theorem realizesBounded_packOutStepGen :
    RealizesBounded .exact packOutStepGenProg
      (WordEncoding.encode (α := (HashParams × ℕ) × (ℕ × ℕ × ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ × ℕ × ℕ)) PackOutStepPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨hp, scratchBase⟩, ⟨m, out, remB, sh⟩⟩
    obtain ⟨w₀, b, b', k, hb'_le, hc_lt, rfl, hfr_s, hm_lt, hout_lt, hrem_le, hsum⟩ := h
    try (dsimp only [hpC_mk, hpMaskC_mk] at *)
    try dsimp only [accWords, prodWords, scratchWords] at *
    have hL_le : rLimbs w₀ b b' ≤ 54 := reducedLimbCount_le _
    have hw_lt : Fits w w := Nat.lt_two_pow_self
    have hpow2c : Fits w (2 ^ (2 * rChunk w₀ b b')) := Nat.pow_lt_pow_right one_lt_two hc_lt
    have hpowc : Fits w (2 ^ rChunk w₀ b b') :=
      hpow2c.of_le (Nat.pow_le_pow_right two_pos (by omega)))
  all_goals try omega
  all_goals try exact hmem.1.of_le (by omega)
  all_goals try exact hw_lt.of_le (by omega)
  all_goals (try (rw [Nat.shiftLeft_eq, one_mul]; exact Nat.one_le_two_pow))
  all_goals (try
    have hrem_lt_w : remB < w := by omega
    rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right one_lt_two hrem_lt_w)
  all_goals (try
    have hpart : (s.mem (scratchBase + m) &&& (2 ^ rChunk w₀ b b' - 1)) <<< sh < 2 ^ w := by
      rw [Nat.shiftLeft_eq]
      calc (s.mem (scratchBase + m) &&& (2 ^ rChunk w₀ b b' - 1)) * 2 ^ sh
          < 2 ^ rChunk w₀ b b' * 2 ^ sh :=
            Nat.mul_lt_mul_of_pos_right (and_two_pow_sub_one_lt _ _) (Nat.two_pow_pos sh)
        _ = 2 ^ (rChunk w₀ b b' + sh) := (pow_add 2 _ sh).symm
        _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos (by omega)
    first | exact hpart | exact Nat.xor_lt_two_pow hout_lt hpart)
  all_goals (try
    have hpart : (s.mem (scratchBase + m) &&& ((1 <<< remB) - 1)) <<< sh < 2 ^ w := by
      rw [Nat.shiftLeft_eq 1 remB, one_mul, Nat.shiftLeft_eq]
      calc (s.mem (scratchBase + m) &&& (2 ^ remB - 1)) * 2 ^ sh
          < 2 ^ remB * 2 ^ sh :=
            Nat.mul_lt_mul_of_pos_right (and_two_pow_sub_one_lt _ remB) (Nat.two_pow_pos sh)
        _ = 2 ^ (remB + sh) := (pow_add 2 remB sh).symm
        _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos (by omega)
    first | exact hpart | exact Nat.xor_lt_two_pow hout_lt hpart)

private theorem packOutLoop_spec {w w₀ b b' k scratchBase evalVal : ℕ} {s₀ : Memory.State}
    (hb'_le : b' ≤ w) (hc_lt : 2 * rChunk w₀ b b' < w)
    (hfr_s : scratchBase + scratchWords ≤ s₀.frontier)
    (heval_lt : evalVal < 2 ^ (rLimbs w₀ b b' * rChunk w₀ b b'))
    (hacc₀ : ∀ m < rLimbs w₀ b b',
      s₀.mem (scratchBase + m) = getLimb (rChunk w₀ b b') evalVal m) :
    let hp := mkHashParams w w₀ b b' k
    let prog := iterate packOutStepGenProg (hp, scratchBase) (rLimbs w₀ b b') (0, 0, b', 0)
    iterationSafe packOutStepGenProg PackOutStepPre w (hp, scratchBase) (rLimbs w₀ b b')
      (0, 0, b', 0) s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ rLimbs w₀ b b' ∧ (Memory.spec 0).clientState s₀ prog = s₀ ∧
    ((Memory.spec 0).clientResult s₀ prog).2.1 = evalVal &&& (2 ^ b' - 1) := by
  intro hp prog
  have hL_le : rLimbs w₀ b b' ≤ 54 := reducedLimbCount_le _
  try dsimp only [accWords, prodWords, scratchWords] at *
  let inv (m : ℕ) (st : ℕ × ℕ × ℕ × ℕ) (s : Memory.State) : Prop :=
    s₀ = s ∧ (m, packLimbs (rChunk w₀ b b') m (getLimb (rChunk w₀ b b') evalVal) &&& (2 ^ b' - 1),
      b' - m * rChunk w₀ b b', min b' (m * rChunk w₀ b b')) = st
  obtain ⟨hsafe, hv, hcost, _, _, hs'_eq, hres_eq⟩ :=
    iterate_spec packOutStepGenProg PackOutStepPre w (hp, scratchBase) 1 (rLimbs w₀ b b') inv
      (fun _ => False)
      (fun m hm st s ⟨hs_eq, hst⟩ => by
        subst hs_eq; subst hst
        have hout_lt :
            (packLimbs (rChunk w₀ b b') m (getLimb (rChunk w₀ b b') evalVal) &&& (2 ^ b' - 1)) <
              2 ^ w :=
          (and_two_pow_sub_one_lt _ b').trans_le (Nat.pow_le_pow_right two_pos hb'_le)
        refine ⟨⟨w₀, b, b', k, hb'_le, hc_lt, rfl, hfr_s, hm, hout_lt, Nat.sub_le _ _, by omega⟩,
          ?_, ?_, ?_, fun _ _ => ?_, ?_, ?_⟩
        · dsimp only [packOutStepGenProg, hp, hpC_mk, hpMaskC_mk]
          have hlt_m : scratchBase + m < s₀.frontier := by omega
          split_ifs <;> exact ⟨hlt_m, trivial⟩
        · dsimp only [packOutStepGenProg, hp, hpC_mk, hpMaskC_mk]; split_ifs <;> exact le_rfl
        · dsimp only [packOutStepGenProg, hp, hpC_mk, hpMaskC_mk]; split_ifs <;> rfl
        · dsimp only [packOutStepGenProg, hp, hpC_mk, hpMaskC_mk]; split_ifs <;> rfl
        · dsimp only [packOutStepGenProg, hp, hpC_mk, hpMaskC_mk]; split_ifs <;> rfl
        · dsimp only [packOutStepGenProg, hp, hpC_mk, hpMaskC_mk]
          rw [StateTransitionSpec.clientResult_bind]
          have hread_res : (Memory.spec 0).clientResult s₀ (Memory.read (scratchBase + m)) =
              s₀.mem (scratchBase + m) := rfl
          rw [hread_res]
          by_cases hrem : 0 < b' - m * rChunk w₀ b b'
          · simp only [hrem, ↓reduceIte]
            have hm_lt_b : m * rChunk w₀ b b' < b' := by omega
            have hmin_sh : min b' (m * rChunk w₀ b b') = reducedOutShift (
              rChunk w₀ b b') b' m := by
              dsimp only [reducedOutShift]; rw [ite_eq_left hm_lt_b]; omega
            by_cases hlt : rChunk w₀ b b' < b' - m * rChunk w₀ b b'
            · simp only [hlt, ↓reduceIte]
              change _ = (m + 1, (packLimbs (rChunk w₀ b b') m (getLimb (
                rChunk w₀ b b') evalVal) &&&
                (2 ^ b' - 1)) ^^^ ((s₀.mem (scratchBase + m) &&&
                  (2 ^ rChunk w₀ b b' - 1)) <<< min b' (m * rChunk w₀ b b')),
                b' - m * rChunk w₀ b b' - rChunk w₀ b b',
                min b' (m * rChunk w₀ b b') + rChunk w₀ b b')
              have hmask_eq : 2 ^ rChunk w₀ b b' - 1 = reducedOutMask (rChunk w₀ b b') b' m := by
                dsimp only [reducedOutMask]; rw [Nat.min_eq_left (le_of_lt hlt)]
              rw [hacc₀ m hm, hmask_eq, hmin_sh, ← packLimbs_and_mask_succ, Nat.succ_mul]
              refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
              · dsimp only; omega
              · dsimp only [reducedOutShift]; rw [ite_eq_left hm_lt_b, Nat.min_eq_right (by omega)]
            · simp only [hlt, ↓reduceIte]
              change _ = (m + 1, (packLimbs (rChunk w₀ b b') m (getLimb (
                rChunk w₀ b b') evalVal) &&&
                (2 ^ b' - 1)) ^^^ ((s₀.mem (scratchBase + m) &&&
                  ((1 <<< (b' - m * rChunk w₀ b b')) - 1)) <<< min b' (m * rChunk w₀ b b')),
                0, min b' (m * rChunk w₀ b b') + (b' - m * rChunk w₀ b b'))
              have hmask_eq :
                  (1 <<< (b' - m * rChunk w₀ b b')) - 1 = reducedOutMask (
                    rChunk w₀ b b') b' m := by
                dsimp only [reducedOutMask]
                rw [Nat.shiftLeft_eq, one_mul, Nat.min_eq_right (by omega)]
              rw [hacc₀ m hm, hmask_eq, hmin_sh, ← packLimbs_and_mask_succ, Nat.succ_mul]
              refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
              · dsimp only; omega
              · dsimp only [reducedOutShift]; rw [ite_eq_left hm_lt_b, Nat.min_eq_left (by omega)]
                omega
          · simp only [hrem, ↓reduceIte]
            change _ = (m + 1, packLimbs (rChunk w₀ b b') m (getLimb (rChunk w₀ b b') evalVal) &&&
              (2 ^ b' - 1), 0, min b' (m * rChunk w₀ b b'))
            have hmask0 : reducedOutMask (rChunk w₀ b b') b' m = 0 := by
              dsimp only [reducedOutMask]
              rw [show min (rChunk w₀ b b') (b' - m * rChunk w₀ b b') = 0 by omega]; rfl
            have hsucc :
                packLimbs (rChunk w₀ b b') (m + 1) (getLimb (rChunk w₀ b b') evalVal) &&&
                  (2 ^ b' - 1) =
                packLimbs (rChunk w₀ b b') m (getLimb (rChunk w₀ b b') evalVal) &&&
                  (2 ^ b' - 1) := by
              rw [packLimbs_and_mask_succ, hmask0, Nat.and_zero, Nat.zero_shiftLeft, Nat.xor_zero]
            rw [hsucc, Nat.succ_mul]
            refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
            · dsimp only; omega
            · dsimp only; rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)])
      (0, 0, b', 0) s₀ ⟨rfl, by simp only [packLimbs, Nat.zero_and, Nat.zero_mul, Nat.sub_zero,
        Nat.min_eq_right (Nat.zero_le b')]⟩
  refine ⟨hsafe, hv, by simpa only [one_mul] using hcost, hs'_eq.symm, ?_⟩
  rw [← hres_eq, packLimbs_getLimb (reducedChunkBits_pos _) (rLimbs w₀ b b') heval_lt]

/-- Complete runtime polynomial hash evaluation `Memory.Prog`. -/
def evalHashGenProg : HashParams × ℕ × ℕ × ℕ → Memory.Prog ℕ
  | (hp, hashBase, scratchBase, uVal) => do
    let rVal ← reduceKeyGenProg (hp, hashBase, uVal)
    let _ ← iterate zeroWordsStepProg scratchBase (2 * hpL0 hp) 0
    let _ ← iterate hornerStepGenProg (hp, hashBase, scratchBase, rVal) (hpK hp) 0
    let (_, out, _, _) ← iterate packOutStepGenProg (hp, scratchBase) (2 * hpL0 hp)
      (0, 0, hpB' hp, 0)
    pure out

/-- Parameter-independent `O(k)` upper bound on `memoryCost (evalHashGenProg d) s`. -/
@[expose] def evalMemBound (k : ℕ) : ℕ := 15014 * k + 109

/-- Entry precondition for `evalHashGenProg`. -/
def EvalHashGenPre (w : ℕ) : HashParams × ℕ × ℕ × ℕ → Memory.State → Prop
  | (hp, hashBase, scratchBase, uVal), s =>
    ∃ U w₀ b b' k, ∃ θ : ReducedPolySeed w₀ b b' k, ∃ u : Fin U,
      0 < w₀ ∧ w₀ ≤ w ∧ U ≤ 2 ^ w₀ ∧ b' ≤ w ∧ 0 < k ∧
      2 * rChunk w₀ b b' < w ∧ hp = mkHashParams w w₀ b b' k ∧ uVal = u.val ∧
      hashBase + ReducedKWise.space w w₀ b b' k ≤ s.frontier ∧
      Fits w (hashBase + ReducedKWise.space w w₀ b b' k) ∧
      scratchBase + scratchWords ≤ s.frontier ∧ Fits w (scratchBase + scratchWords) ∧
      (hashBase + ReducedKWise.space w w₀ b b' k ≤ scratchBase ∨
        scratchBase + scratchWords ≤ hashBase) ∧
      ReducedKWise.Rep hashBase w w₀ b b' k θ s.mem

private theorem evalHashGenProg_aux {w U w₀ b b' k hashBase scratchBase : ℕ}
    {θ : ReducedPolySeed w₀ b b' k} {u : Fin U} {s₀ : Memory.State}
    (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (hU : U ≤ 2 ^ w₀) (hb' : b' ≤ w) (hk_pos : 0 < k)
    (hc_lt : 2 * rChunk w₀ b b' < w)
    (hfr_h : hashBase + ReducedKWise.space w w₀ b b' k ≤ s₀.frontier)
    (hfit_h : Fits w (hashBase + ReducedKWise.space w w₀ b b' k))
    (hfr_s : scratchBase + scratchWords ≤ s₀.frontier)
    (hfit_s : Fits w (scratchBase + scratchWords))
    (hdisj : hashBase + ReducedKWise.space w w₀ b b' k ≤ scratchBase ∨
      scratchBase + scratchWords ≤ hashBase)
    (hrep : ReducedKWise.Rep hashBase w w₀ b b' k θ s₀.mem) :
    let hp := mkHashParams w w₀ b b' k
    let r := multiplyShiftReduced U w₀ (3 * b) θ.1 u
    let prog := evalHashGenProg (hp, hashBase, scratchBase, u.val)
    let s₁ := (Memory.spec 0).clientState s₀ (iterate zeroWordsStepProg scratchBase
      (rLimbs w₀ b b') 0)
    let s₂ := (Memory.spec 0).clientState s₁
      (iterate hornerStepGenProg (hp, hashBase, scratchBase, r.val) k 0)
    let s' := (Memory.spec 0).clientState s₀ prog
    EvalHashGenPre w (hp, hashBase, scratchBase, u.val) s₀ ∧
    ReduceKeyGenPre w (hp, hashBase, u.val) s₀ ∧
    iterationSafe zeroWordsStepProg ZeroWordsStepPre w scratchBase (rLimbs w₀ b b') 0 s₀ ∧
    iterationSafe hornerStepGenProg HornerStepPre w (hp, hashBase, scratchBase, r.val) k 0 s₁ ∧
    iterationSafe packOutStepGenProg PackOutStepPre w (hp, scratchBase) (rLimbs w₀ b b')
      (0, 0, b', 0) s₂ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ evalMemBound k ∧
    (Memory.spec 0).clientResult s₀ prog = (reducedPolyHash U w₀ b b' k θ u).val ∧
    s'.frontier = s₀.frontier ∧
    (∀ a, (a < scratchBase ∨ scratchBase + scratchWords ≤ a) → s'.mem a = s₀.mem a) := by
  have haccW : accWords = 54 := rfl
  have hscrW : scratchWords = 162 := rfl
  intro hp r prog s₁ s₂ s'
  have hL_le : rLimbs w₀ b b' ≤ 54 := reducedLimbCount_le _
  have hu_lt_w0 : u.val < 2 ^ w₀ := lt_of_lt_of_le u.isLt hU
  have hα_eq : s₀.mem hashBase = θ.1.val := hrep.2.1
  have hr_eq : (Memory.spec 0).clientResult s₀ (reduceKeyGenProg (hp, hashBase, u.val)) =
    r.val := by
    change oddMulModWord w₀ (s₀.mem hashBase) u.val >>> (w₀ - min w₀ (3 * b)) = r.val
    rw [hα_eq, show w₀ - min w₀ (3 * b) = w₀ - 3 * b by omega]
    exact oddMulModWord_shiftRight_eq_multiplyShiftReduced hw₀_pos θ.1 u
  obtain ⟨hsafe_z, hv_z, hcost_z, hfr_z, hz_mem, hout_z⟩ :=
    zeroWordsLoop_spec (w := w) (baseAddr := scratchBase) (n := rLimbs w₀ b b') (s₀ := s₀)
      (by omega)
  have htab₁ : ReducedKWise.TableRep hashBase w w₀ b b' k s₁.mem :=
    tableRep_congr hrep.1 fun a h1 h2 => (hout_z a (by omega)).symm
  have hseed₁ : ReducedKWise.SeedRep hashBase w₀ b b' k θ s₁.mem :=
    seedRep_congr (w := w) hrep.2 fun a h1 h2 => (hout_z a (by omega)).symm
  obtain ⟨hsafe_h, hv_h, hcost_h, hfr_h2, hacc_h, hout_h⟩ :=
    hornerLoop_spec hw₀ hc_lt (hfr_z.symm ▸ hfr_h) (hfr_z.symm ▸ hfr_s) hdisj htab₁ hseed₁ hz_mem
  let evalVal := (trinomialPolyEval (rStep w₀ b b') k (2 ^ min w₀ (3 * b)) θ.2 r).val
  have heval_lt : evalVal < 2 ^ (rLimbs w₀ b b' * rChunk w₀ b b') := by
    rw [reducedLimbCount_mul_chunkBits]
    exact (trinomialPolyEval (rStep w₀ b b') k (2 ^ min w₀ (3 * b)) θ.2 r).isLt
  obtain ⟨hsafe_p, hv_p, hcost_p, hs_p, hres_p⟩ :=
    packOutLoop_spec (w₀ := w₀) (b := b) (k := k) hb' hc_lt
      (by rw [hfr_h2, hfr_z]; exact hfr_s) heval_lt hacc_h
  have hprog_eq : prog = (do
      let rVal ← reduceKeyGenProg (hp, hashBase, u.val)
      let _ ← iterate zeroWordsStepProg scratchBase (rLimbs w₀ b b') 0
      let _ ← iterate hornerStepGenProg (hp, hashBase, scratchBase, rVal) k 0
      let (_, out, _, _) ← iterate packOutStepGenProg (hp, scratchBase) (rLimbs w₀ b b')
        (0, 0, b', 0)
      pure out) := rfl
  have hrk_state : (Memory.spec 0).clientState s₀ (reduceKeyGenProg (hp, hashBase, u.val)) =
    s₀ := rfl
  have hs'_eq : s' = s₂ := by
    dsimp only [s']; rw [hprog_eq, StateTransitionSpec.clientState_bind, hr_eq, hrk_state,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind, hs_p]; rfl
  refine ⟨⟨U, w₀, b, b', k, θ, u, hw₀_pos, hw₀, hU, hb', hk_pos, hc_lt, rfl, rfl,
      hfr_h, hfit_h, hfr_s, hfit_s, hdisj, hrep⟩,
    ⟨w₀, b, b', k, hw₀_pos, hw₀, hc_lt, rfl,
      by unfold ReducedKWise.space ReducedKWise.seedWords at hfr_h; omega,
      hα_eq ▸ θ.1.isLt, hu_lt_w0⟩,
    hsafe_z, hsafe_h, hsafe_p, ?_, ?_, ?_, by rw [hs'_eq, hfr_h2, hfr_z], fun a ha => ?_⟩
  · rw [hprog_eq, validHistory_bind', hr_eq, hrk_state, validHistory_bind',
      validHistory_bind', validHistory_bind']
    have hv_rk : (Memory.spec w).ValidHistory s₀
        ((Memory.spec w).clientHistory s₀ (reduceKeyGenProg (hp, hashBase, u.val))) := by
      change hashBase < s₀.frontier ∧ True
      exact ⟨by unfold ReducedKWise.space ReducedKWise.seedWords at hfr_h; omega, trivial⟩
    exact ⟨hv_rk, hv_z, hv_h, hv_p, trivial⟩
  · rw [hprog_eq, memoryCost_bind', hr_eq, hrk_state, memoryCost_bind', memoryCost_bind',
      memoryCost_bind']
    have hstep_bound :
        1 + 2 * rLimbs w₀ b b' + (1 + 5 * rLimbs w₀ b b') * rLimbs w₀ b b' +
          5 * rLimbs w₀ b b' ≤ 15014 := by nlinarith
    have hmul_bound := Nat.mul_le_mul_right k hstep_bound
    have hrk_cost : memoryCost (reduceKeyGenProg (hp, hashBase, u.val)) s₀ = 1 := rfl
    have htail_cost : memoryCost (match (Memory.spec 0).clientResult s₂
        (iterate packOutStepGenProg (hp, scratchBase) (rLimbs w₀ b b') (0, 0, b', 0)) with
        | (_, out, _, _) => (pure out : Memory.Prog ℕ)) s₂ = 0 := rfl
    change memoryCost (reduceKeyGenProg (hp, hashBase, u.val)) s₀ +
      (memoryCost (iterate zeroWordsStepProg scratchBase (rLimbs w₀ b b') 0) s₀ +
        (memoryCost (iterate hornerStepGenProg (hp, hashBase, scratchBase, r.val) k 0) s₁ +
          (memoryCost (iterate packOutStepGenProg (hp, scratchBase) (rLimbs w₀ b b')
            (0, 0, b', 0)) s₂ + _))) ≤ _
    rw [hrk_cost, hs_p, htail_cost]
    dsimp only [hp, r, s₁, s₂, evalMemBound] at hcost_h hcost_p ⊢
    omega
  · rw [hprog_eq, StateTransitionSpec.clientResult_bind, hr_eq, hrk_state,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientResult_bind, hs_p]
    change ((Memory.spec 0).clientResult s₂
      (iterate packOutStepGenProg (hp, scratchBase) (rLimbs w₀ b b') (0, 0, b', 0))).2.1 = _
    rw [hres_p]; exact (val_trinomialPolyHash (rStep w₀ b b') k (2 ^ min w₀ (3 * b)) b' θ.2 r).symm
  · rw [hs'_eq]; exact (hout_h a ha).trans (hout_z a (by omega))

/-- **Full specification of `evalHashGenProg`**. -/
theorem evalHashGenProg_spec {w U w₀ b b' k hashBase scratchBase : ℕ}
    {θ : ReducedPolySeed w₀ b b' k} {u : Fin U} {s₀ : Memory.State}
    (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (hU : U ≤ 2 ^ w₀) (hb' : b' ≤ w) (hk_pos : 0 < k)
    (hc_lt : 2 * rChunk w₀ b b' < w)
    (hfr_h : hashBase + ReducedKWise.space w w₀ b b' k ≤ s₀.frontier)
    (hfit_h : Fits w (hashBase + ReducedKWise.space w w₀ b b' k))
    (hfr_s : scratchBase + scratchWords ≤ s₀.frontier)
    (hfit_s : Fits w (scratchBase + scratchWords))
    (hdisj : hashBase + ReducedKWise.space w w₀ b b' k ≤ scratchBase ∨
      scratchBase + scratchWords ≤ hashBase)
    (hrep : ReducedKWise.Rep hashBase w w₀ b b' k θ s₀.mem) :
    let hp := mkHashParams w w₀ b b' k
    let prog := evalHashGenProg (hp, hashBase, scratchBase, u.val)
    let s' := (Memory.spec 0).clientState s₀ prog
    EvalHashGenPre w (hp, hashBase, scratchBase, u.val) s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ evalMemBound k ∧
    (Memory.spec 0).clientResult s₀ prog = (reducedPolyHash U w₀ b b' k θ u).val ∧
    s'.frontier = s₀.frontier ∧
    (∀ a, (a < scratchBase ∨ scratchBase + scratchWords ≤ a) → s'.mem a = s₀.mem a) := by
  obtain ⟨hpre, _, _, _, _, hv, hcost, hres, hfr', hout⟩ :=
    evalHashGenProg_aux hw₀_pos hw₀ hU hb' hk_pos hc_lt hfr_h hfit_h hfr_s hfit_s hdisj hrep
  exact ⟨hpre, hv, hcost, hres, hfr', hout⟩

/-- **Parameter-free `RealizesBounded .exact` certificate for `evalHashGenProg`** (
  `¬ReadsWidth`). -/
theorem realizesBounded_evalHashGen :
    RealizesBounded .exact evalHashGenProg
      (WordEncoding.encode (α := HashParams × ℕ × ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      EvalHashGenPre (fun _ _ => 0) := by
  have hrk := realizesBounded_reduceKeyGen
  have hz := realizesBounded_zeroWordsStep
  have hh := realizesBounded_hornerStepGen
  have hp_cert := realizesBounded_packOutStepGen
  realize
  all_goals (
    rcases d with ⟨hp, hashBase, scratchBase, uVal⟩
    obtain ⟨U, w₀, b, b', k, θ, u, hw₀_pos, hw₀, hU, hb', hk_pos, hc_lt, rfl, rfl,
      hfr_h, hfit_h, hfr_s, hfit_s, hdisj, hrep⟩ := h
    try (dsimp only [hpL0_mk, hpK_mk, hpB'_mk] at *)
    try dsimp only [accWords, prodWords, scratchWords] at *
    have hL_le : rLimbs w₀ b b' ≤ 54 := reducedLimbCount_le _
    have h2L0 : 2 * rHalf w₀ b b' = rLimbs w₀ b b' := rfl
    obtain ⟨_, hrk_pre, hsafe_z, hsafe_h, hsafe_p, _⟩ :=
      evalHashGenProg_aux (u := u) hw₀_pos hw₀ hU hb' hk_pos hc_lt hfr_h hfit_h hfr_s hfit_s
        hdisj hrep
    have hr_eq : (Memory.spec 0).clientResult s
        (reduceKeyGenProg (mkHashParams w w₀ b b' k, hashBase, u.val)) =
        (multiplyShiftReduced U w₀ (3 * b) θ.1 u).val := by
      change oddMulModWord w₀ (s.mem hashBase) u.val >>> (w₀ - min w₀ (3 * b)) = _
      rw [hrep.2.1, show w₀ - min w₀ (3 * b) = w₀ - 3 * b by omega]
      exact oddMulModWord_shiftRight_eq_multiplyShiftReduced hw₀_pos θ.1 u)
  all_goals try exact hrk_pre
  all_goals try exact hfit_s.of_le (by omega)
  all_goals first
    | (rw [h2L0]; exact iterationSafe_imp hsafe_z (fun _ => rfl) (fun _ _ hs => hs))
    | (rw [hr_eq]; exact iterationSafe_imp hsafe_h (fun _ => rfl) (fun _ _ hs => hs))
    | (rw [hr_eq, h2L0]; exact iterationSafe_imp hsafe_p (fun _ => rfl) (fun _ _ hs => hs))

/-! ## Section 4: Parameter-free seed resampling (`resampleHashCode`) on `RCode .exact r` -/

private def randFillRBody {r : ℕ} (rPtr rMask rOne rVal : Fin r) : RCode .exact r :=
  .seq (.rand rVal rMask)
    (.seq (.op (.store rPtr rVal)) (.op (.exactBin .add rPtr rPtr rOne)))

private def randFillRLoop {r : ℕ} (rPtr rEnd rMask rOne rVal : Fin r) : RCode .exact r :=
  .loop (.lt rPtr rEnd) (randFillRBody rPtr rMask rOne rVal)

private noncomputable def randFillRPMF {r : ℕ} (rPtr rVal : Fin r) (bits arrBase : ℕ) :
    ℕ → RData r → PMF (RData r)
  | 0, x => PMF.pure x
  | len + 1, x =>
    (ProbComp.unifFin (2 ^ bits - 1)).eval.bind fun k =>
      randFillRPMF rPtr rVal bits (arrBase + 1) len
        (((x.set rVal k.val).write arrBase k.val).set rPtr (arrBase + 1))

private theorem randFillRLoop_exec {r w L_peak bits arrBase : ℕ}
    {rPtr rEnd rMask rOne rVal : Fin r}
    (hd : [rPtr, rEnd, rMask, rOne, rVal].Nodup) (len : ℕ) {x : RData r}
    (hL : x.frontier ≤ L_peak) (hfr : arrBase + len ≤ x.frontier)
    (hfit_end : Fits w (arrBase + len)) (hfit_mask : Fits w (2 ^ bits - 1))
    (hptr : x.regs rPtr = arrBase) (hend : x.regs rEnd = arrBase + len)
    (hmask : x.regs rMask = 2 ^ bits - 1) (hone : x.regs rOne = 1) :
    ExecRCodeDist w (randFillRLoop rPtr rEnd rMask rOne rVal) x
      (randFillRPMF rPtr rVal bits arrBase len x) (5 * len + 2 : ℕ) L_peak := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, ← ne_eq,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨hpe, hpm, hpo, hpv⟩, ⟨hem, heo, hev⟩, ⟨hmo, hmv⟩, hov, -⟩ := hd
  induction len generalizing arrBase x with
  | zero =>
    exact ExecRCodeDist.of_demonicExec
      (RDemonicExec.loop_exit hL (by simp [Cond.Holds, hptr, hend]) rfl)
  | succ len ih =>
    have hc : (Cond.lt rPtr rEnd).Holds x.toData := by simp [Cond.Holds, hptr, hend]
    have hrand := ExecRCodeDist.rand (B := .exact) (w := w) (dst := rVal) (src := rMask) (x := x)
      hL (hmask ▸ hfit_mask)
    rw [hmask] at hrand
    have hrest : ∀ y ∈ ((ProbComp.unifFin (2 ^ bits - 1)).eval.map
        fun k => x.set rVal k.val).support,
        ExecRCodeDist w (.seq (.op (.store rPtr rVal)) (.op (.exactBin .add rPtr rPtr rOne))) y
          (PMF.pure ((y.write arrBase (y.regs rVal)).set rPtr (arrBase + 1))) 2 L_peak := by
      intro y hy
      simp only [PMF.mem_support_map_iff] at hy
      obtain ⟨k, _, rfl⟩ := hy
      have hyp : (x.set rVal k.val).regs rPtr = arrBase := by
        simp [Function.update_of_ne hpv, hptr]
      have hs1 := RDemonicExec.store (B := .exact) (a := rPtr) (s := rVal) (w := w)
        (L_peak := L_peak) (x := x.set rVal k.val) hL
        (by rw [hyp]; simp only [RData.set_frontier]; omega)
      rw [hyp] at hs1
      have hs2 := RDemonicExec.exactBin (f := .add) (d := rPtr) (i := rPtr) (j := rOne)
        (w := w) (L_peak := L_peak)
        (x := (x.set rVal k.val).write arrBase ((x.set rVal k.val).regs rVal)) hL
        (v := arrBase + 1)
        (by simp [BinOp.evalExact, hyp, Function.update_of_ne hov, hone])
        (hfit_end.of_le (by omega))
      exact ExecRCodeDist.of_demonicExec (hs1.seq_eq hs2)
    have hbody := ExecRCodeDist.seq_const (B₂ := 2) hrand hrest (fun _ _ => le_rfl)
    have hiter := ExecRCodeDist.loop_iter
      (μ₂ := fun z => randFillRPMF rPtr rVal bits (arrBase + 1) len z)
      (T₂ := fun _ => (5 * len + 2 : ℕ)) hc hbody fun z hz => by
      simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff, PMF.support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨_, ⟨k, _, rfl⟩, rfl⟩ := hz
      have hreg_v : (x.set rVal k.val).regs rVal = k.val := by simp
      rw [hreg_v]
      exact ih (arrBase := arrBase + 1)
        (x := ((x.set rVal k.val).write arrBase k.val).set rPtr (arrBase + 1))
        (by simp only [RData.set_frontier, RData.write_frontier]; exact hL)
        (by simp only [RData.set_frontier, RData.write_frontier]; omega)
        (by rwa [show arrBase + 1 + len = arrBase + (len + 1) by omega])
        (by simp)
        (by simp only [RData.set_regs, RData.write_regs, Function.update_of_ne hpe.symm,
              Function.update_of_ne hev, hend]; omega)
        (by simp [Function.update_of_ne hpm.symm, Function.update_of_ne hmv, hmask])
        (by simp [Function.update_of_ne hpo.symm, Function.update_of_ne hov, hone])
    refine hiter.congr_dist ?_ ?_
    · simp [randFillRPMF, PMF.bind_bind, PMF.bind_map, Function.comp_def]
    · rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      have hle : 1 + 2 + 2 + (5 * len + 2) ≤ 5 * (len + 1) + 2 := by omega
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
        (Nat.cast_le (α := ℝ≥0∞)).mpr hle

private theorem mem_support_randFillRPMF {r bits arrBase len : ℕ} {rPtr rVal : Fin r}
    (_hpv : rPtr ≠ rVal) {x y : RData r}
    (hy : y ∈ (randFillRPMF rPtr rVal bits arrBase len x).support) :
    y.frontier = x.frontier ∧
    (∀ j, j ≠ rPtr → j ≠ rVal → y.regs j = x.regs j) ∧
    (∀ i < len, y.mem (arrBase + i) < 2 ^ bits) ∧
    (∀ a, (a < arrBase ∨ arrBase + len ≤ a) → y.mem a = x.mem a) := by
  induction len generalizing arrBase x with
  | zero =>
    rw [randFillRPMF, PMF.support_pure, Set.mem_singleton_iff] at hy; subst hy
    exact ⟨rfl, fun _ _ _ => rfl, fun _ hi => (Nat.not_lt_zero _ hi).elim, fun _ _ => rfl⟩
  | succ len ih =>
    rw [randFillRPMF, PMF.mem_support_bind_iff] at hy
    obtain ⟨k, _, hy'⟩ := hy
    obtain ⟨hfr, hreg, hlt, hframe⟩ := ih hy'
    have hk_lt : k.val < 2 ^ bits := by
      have := Nat.one_le_two_pow (n := bits); have := k.isLt; omega
    refine ⟨hfr, fun j hj1 hj2 => (hreg j hj1 hj2).trans
      (by simp [Function.update_of_ne hj1, Function.update_of_ne hj2]), fun i hi => ?_,
      fun a ha => (hframe a (by omega)).trans
        (by simp [Function.update_of_ne (by omega : a ≠ arrBase)])⟩
    rcases eq_or_ne i 0 with rfl | hi0
    · rw [Nat.add_zero, hframe arrBase (Or.inl (by omega))]; simpa using hk_lt
    · simpa only [show arrBase + 1 + (i - 1) = arrBase + i by omega] using hlt (i - 1) (by omega)

private theorem map_extractSlice_randFillRPMF {r : ℕ} (rPtr rVal : Fin r) (hpv : rPtr ≠ rVal)
    (bits arrBase len : ℕ) (x : RData r) :
    (randFillRPMF rPtr rVal bits arrBase len x).map
      (fun y => Tabulation.extractSlice arrBase bits len y.mem) =
      PMF.uniformOfFintype (Fin len → Fin (2 ^ bits)) := by
  induction len generalizing arrBase x with
  | zero =>
    ext f
    have heq : f = Tabulation.extractSlice arrBase bits 0 x.mem := Subsingleton.elim _ _
    simp [randFillRPMF, PMF.map, PMF.pure_apply, heq, PMF.uniformOfFintype_apply]
  | succ len ih =>
    let e := finCongr (Nat.sub_add_cancel (Nat.one_le_two_pow (n := bits)))
    have hstep : (randFillRPMF rPtr rVal bits arrBase (len + 1) x).map
        (fun y => Tabulation.extractSlice arrBase bits (len + 1) y.mem) =
        (PMF.uniformOfFintype (Fin (2 ^ bits))).bind (fun first =>
          (PMF.uniformOfFintype (Fin len → Fin (2 ^ bits))).map (Fin.cons first)) := by
      rw [randFillRPMF, ProbComp.eval_unifFin, PMF.map_bind]
      have hbody : ∀ k : Fin (2 ^ bits - 1 + 1),
          (randFillRPMF rPtr rVal bits (arrBase + 1) len
            (((x.set rVal k.val).write arrBase k.val).set rPtr (arrBase + 1))).map
            (fun y => Tabulation.extractSlice arrBase bits (len + 1) y.mem) =
          (PMF.uniformOfFintype (Fin len → Fin (2 ^ bits))).map (Fin.cons (e k)) := fun k => by
        set xk := (((x.set rVal k.val).write arrBase k.val).set rPtr (arrBase + 1))
        have hcongr : (randFillRPMF rPtr rVal bits (arrBase + 1) len xk).map
            (fun y => Tabulation.extractSlice arrBase bits (len + 1) y.mem) =
            (randFillRPMF rPtr rVal bits (arrBase + 1) len xk).map
            (Fin.cons (e k) ∘ fun y => Tabulation.extractSlice (arrBase + 1) bits len y.mem) := by
          refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun y hy => ?_
          obtain ⟨_, _, _, hframe⟩ := mem_support_randFillRPMF hpv hy
          funext j; refine Fin.cases ?_ ?_ j
          · have h0 := hframe arrBase (Or.inl (by omega))
            simp [Tabulation.extractSlice, h0, xk, e]
          · intro i; simp only [Tabulation.extractSlice, Fin.cons_succ, Fin.val_succ,
              Function.comp_apply]; congr 2; omega
        rw [hcongr, ← PMF.map_comp, ih]
      rw [show (PMF.uniformOfFintype (Fin (2 ^ bits - 1 + 1))).bind _ =
          (PMF.uniformOfFintype (Fin (2 ^ bits - 1 + 1))).bind
            (fun k => (PMF.uniformOfFintype (Fin len → Fin (2 ^ bits))).map (Fin.cons (e k))) from
          congrArg _ (funext hbody),
        ← PMF.uniformOfFintype_map_equiv e, PMF.bind_map]; rfl
    rw [hstep, ← PMF.pi_uniformOfFintype, ← PMF.pi_fin_succ, PMF.pi_uniformOfFintype]

/-- Parameter-free `RCode .exact r` subroutine resampling a uniform `ReducedPolySeed w₀ b b' k`. -/
def resampleHashCode {r : ℕ}
    (rBase rMaskM rBotWords rMaskC rPtr rEnd rMask rOne rVal : Fin r) : RCode .exact r :=
  .seq (.op (.copy rPtr rBase)) <| .seq (.op (.const rOne 1)) <|
  .seq (.op (.exactBin .add rEnd rBase rOne)) <| .seq (.op (.copy rMask rMaskM)) <|
  .seq (randFillRLoop rPtr rEnd rMask rOne rVal) <| .seq (.op (.copy rPtr rEnd)) <|
  .seq (.op (.exactBin .add rEnd rEnd rBotWords)) <| .seq (.op (.copy rMask rMaskC)) <|
  randFillRLoop rPtr rEnd rMask rOne rVal

theorem not_readsWidth_resampleHashCode {r : ℕ}
    (rBase rMaskM rBotWords rMaskC rPtr rEnd rMask rOne rVal : Fin r) :
    ¬(resampleHashCode rBase rMaskM rBotWords rMaskC rPtr rEnd rMask rOne rVal).ReadsWidth := by
  simp [resampleHashCode, randFillRLoop, randFillRBody, RCode.ReadsWidth, Op.ReadsWidth,
    Op.exactBin]

/-- **Compositional `ExecRCodeDist` specification of `resampleHashCode`**. -/
theorem resampleHashCode_execRCodeDist {r w L_peak w₀ b b' k hashBase : ℕ}
    {rBase rMaskM rBotWords rMaskC rPtr rEnd rMask rOne rVal : Fin r} {x : RData r}
    (hd : [rBase, rMaskM, rBotWords, rMaskC, rPtr, rEnd, rMask, rOne, rVal].Nodup)
    (hw₀ : w₀ ≤ w) (hc_lt : 2 * rChunk w₀ b b' < w) (hL : x.frontier ≤ L_peak)
    (hfr : hashBase + ReducedKWise.seedWords w₀ b b' k ≤ x.frontier)
    (hfit : Fits w (hashBase + ReducedKWise.seedWords w₀ b b' k))
    (hbase : x.regs rBase = hashBase)
    (hmaskM : x.regs rMaskM = 2 ^ (w₀ - 1) - 1)
    (hbot : x.regs rBotWords = k * rLimbs w₀ b b')
    (hmaskC : x.regs rMaskC = 2 ^ rChunk w₀ b b' - 1) :
    ∃ μ : PMF (RData r),
      ExecRCodeDist w (resampleHashCode rBase rMaskM rBotWords rMaskC rPtr rEnd rMask rOne rVal)
        x μ (5 * ReducedKWise.seedWords w₀ b b' k + 11 : ℕ) L_peak ∧
      μ.map (fun y => ReducedKWise.extractSeed hashBase w₀ b b' k y.mem) =
        PMF.uniformOfFintype (ReducedPolySeed w₀ b b' k) ∧
      ∀ y ∈ μ.support,
        y.frontier = x.frontier ∧
        ReducedKWise.SeedRep hashBase w₀ b b' k
          (ReducedKWise.extractSeed hashBase w₀ b b' k y.mem) y.mem ∧
        (∀ a, (a < hashBase ∨ hashBase + ReducedKWise.seedWords w₀ b b' k ≤ a) →
          y.mem a = x.mem a) ∧
        (∀ j, j ∉ [rPtr, rEnd, rMask, rOne, rVal] → y.regs j = x.regs j) := by
  have hfit1 : Fits w 1 := hfit.of_le (by dsimp only [ReducedKWise.seedWords]; omega)
  have hfit_top : Fits w (hashBase + 1) := hfit.of_le (
    by dsimp only [ReducedKWise.seedWords]; omega)
  have hfit_end : Fits w (hashBase + 1 + k * rLimbs w₀ b b') :=
    hfit.of_le (by unfold ReducedKWise.seedWords; omega)
  have hfit_mM : Fits w (2 ^ (w₀ - 1) - 1) :=
    (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans_le (Nat.pow_le_pow_right two_pos (by omega))
  have hfit_mC : Fits w (2 ^ rChunk w₀ b b' - 1) :=
    (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans_le (Nat.pow_le_pow_right two_pos (by omega))
  have hd5 : [rPtr, rEnd, rMask, rOne, rVal].Nodup :=
    ((((List.nodup_cons.mp hd).2 |> List.nodup_cons.mp).2 |> List.nodup_cons.mp).2 |>
      List.nodup_cons.mp).2
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, ← ne_eq,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨_, _, _, hbp, hbe, hbm, hbo, hbv⟩, ⟨_, _, hmp, hme, hmm, hmo, hmv⟩,
    ⟨_, hwp, hwe, hwm, hwo, hwv⟩, ⟨hcp, hce, hcm, hco, hcv⟩,
    ⟨hpe, hpm, hpo, hpv⟩, ⟨hem, heo, hev⟩, ⟨hmo', hmv'⟩, hov, -⟩ := hd
  set x1 := (((x.set rPtr hashBase).set rOne 1).set rEnd (hashBase + 1)).set rMask (2 ^ (
    w₀ - 1) - 1)
  have hl1 := randFillRLoop_exec hd5 1 (x := x1) hL
    (by simp only [x1, RData.set_frontier]; unfold ReducedKWise.seedWords at hfr; omega)
    hfit_top hfit_mM
    (by simp [x1, Function.update_of_ne hpm, Function.update_of_ne hpe, Function.update_of_ne hpo])
    (by simp [x1, Function.update_of_ne hem]) (by simp [x1])
    (by simp [x1, Function.update_of_ne hmo'.symm, Function.update_of_ne heo.symm])
  let step2 (y1 : RData r) : RData r :=
    ((y1.set rPtr (hashBase + 1)).set rEnd (hashBase + 1 + k * rLimbs w₀ b b')).set
      rMask (2 ^ rChunk w₀ b b' - 1)
  let μ2 (y1 : RData r) : PMF (RData r) :=
    randFillRPMF rPtr rVal (rChunk w₀ b b') (hashBase + 1) (k * rLimbs w₀ b b') (step2 y1)
  set μ1 := randFillRPMF rPtr rVal (w₀ - 1) hashBase 1 x1
  refine ⟨μ1.bind μ2, ?_, ?_, ?_⟩
  · have he1 := RDemonicExec.copy (B := .exact) (d := rPtr) (s := rBase) (w := w) hL (x := x)
    rw [hbase] at he1
    have he2 := RDemonicExec.const (B := .exact) (d := rOne) (w := w) (L_peak := L_peak)
      (x := x.set rPtr hashBase) hL hfit1
    have he3 := RDemonicExec.exactBin (f := .add) (d := rEnd) (i := rBase) (j := rOne) (w := w)
      (L_peak := L_peak) (x := (x.set rPtr hashBase).set rOne 1) hL (v := hashBase + 1)
      (by simp [BinOp.evalExact, Function.update_of_ne hbo, Function.update_of_ne hbp, hbase])
      hfit_top
    have he4 := RDemonicExec.copy (B := .exact) (d := rMask) (s := rMaskM) (w := w)
      (L_peak := L_peak) (x := ((x.set rPtr hashBase).set rOne 1).set rEnd (hashBase + 1)) hL
    have hm_eq : (((x.set rPtr hashBase).set rOne 1).set rEnd (hashBase + 1)).regs rMaskM =
        2 ^ (w₀ - 1) - 1 := by
      simp [Function.update_of_ne hme, Function.update_of_ne hmo, Function.update_of_ne hmp,
        hmaskM]
    rw [hm_eq] at he4
    have hrest := ExecRCodeDist.seq_const (B₂ := ((3 + (5 * (k * rLimbs w₀ b b') + 2) : ℕ) : ℝ≥0∞))
      hl1 (fun y1 hy1 => by
        obtain ⟨hy1_fr, hy1_reg, _, _⟩ := mem_support_randFillRPMF hpv hy1
        have hy1_end : y1.regs rEnd = hashBase + 1 :=
          (hy1_reg rEnd hpe.symm hev).trans (by simp [x1, Function.update_of_ne hem])
        have hy1_bot : y1.regs rBotWords = k * rLimbs w₀ b b' :=
          (hy1_reg rBotWords hwp hwv).trans
            (by simp [x1, Function.update_of_ne hwm, Function.update_of_ne hwe,
                  Function.update_of_ne hwo, Function.update_of_ne hwp, hbot])
        have hy1_mc : y1.regs rMaskC = 2 ^ rChunk w₀ b b' - 1 :=
          (hy1_reg rMaskC hcp hcv).trans
            (by simp [x1, Function.update_of_ne hcm, Function.update_of_ne hce,
                  Function.update_of_ne hco, Function.update_of_ne hcp, hmaskC])
        have hy1_one : y1.regs rOne = 1 :=
          (hy1_reg rOne hpo.symm hov).trans
            (by simp [x1, Function.update_of_ne hmo'.symm, Function.update_of_ne heo.symm])
        have f1 := RDemonicExec.copy (B := .exact) (d := rPtr) (s := rEnd) (w := w) (x := y1)
          (hy1_fr ▸ hL)
        rw [hy1_end] at f1
        have f2 := RDemonicExec.exactBin (f := .add) (d := rEnd) (i := rEnd) (j := rBotWords)
          (w := w) (L_peak := L_peak) (x := y1.set rPtr (hashBase + 1)) (hy1_fr ▸ hL)
          (v := hashBase + 1 + k * rLimbs w₀ b b')
          (by simp [BinOp.evalExact, Function.update_of_ne hpe.symm, Function.update_of_ne hwp,
                hy1_end, hy1_bot]) hfit_end
        have f3 := RDemonicExec.copy (B := .exact) (d := rMask) (s := rMaskC) (w := w)
          (L_peak := L_peak)
          (x := (y1.set rPtr (hashBase + 1)).set rEnd (hashBase + 1 + k * rLimbs w₀ b b'))
          (hy1_fr ▸ hL)
        have hmc' :
            ((y1.set rPtr (hashBase + 1)).set rEnd
              (hashBase + 1 + k * rLimbs w₀ b b')).regs rMaskC = 2 ^ rChunk w₀ b b' - 1 := by
          simp [Function.update_of_ne hce, Function.update_of_ne hcp, hy1_mc]
        rw [hmc'] at f3
        have fl2 := randFillRLoop_exec hd5 (k * rLimbs w₀ b b') (arrBase := hashBase + 1)
          (x := step2 y1)
          (by dsimp only [step2]; simp only [RData.set_frontier, hy1_fr, x1]; exact hL)
          (by dsimp only [step2]; simp only [RData.set_frontier, hy1_fr, x1]
              unfold ReducedKWise.seedWords at hfr; omega) hfit_end hfit_mC
          (by simp [step2, Function.update_of_ne hpm, Function.update_of_ne hpe])
          (by simp [step2, Function.update_of_ne hem]) (by simp [step2])
          (by simp [step2, Function.update_of_ne hmo'.symm, Function.update_of_ne heo.symm,
                Function.update_of_ne hpo.symm, hy1_one])
        exact ((ExecRCodeDist.of_demonicExec f1).seq_pure
          ((ExecRCodeDist.of_demonicExec f2).seq_pure
            ((ExecRCodeDist.of_demonicExec f3).seq_pure fl2))).congr_dist rfl
          (by have hle : 1 + (1 + (1 + (5 * (k * rLimbs w₀ b b') + 2))) ≤
                3 + (5 * (k * rLimbs w₀ b b') + 2) := by omega
              simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
                (Nat.cast_le (α := ℝ≥0∞)).mpr hle))
      (fun _ _ => le_rfl)
    refine ((ExecRCodeDist.of_demonicExec he1).seq_pure
      ((ExecRCodeDist.of_demonicExec he2).seq_pure
        ((ExecRCodeDist.of_demonicExec he3).seq_pure
          ((ExecRCodeDist.of_demonicExec he4).seq_pure hrest)))).congr_dist rfl ?_
    have hle : 1 + (1 + (1 + (1 + ((5 * 1 + 2) + (3 + (5 * (k * rLimbs w₀ b b') + 2)))))) ≤
        5 * ReducedKWise.seedWords w₀ b b' k + 11 := by
      unfold ReducedKWise.seedWords; omega
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
      (Nat.cast_le (α := ℝ≥0∞)).mpr hle
  · have hm1_unif : μ1.map (fun y1 => ReducedKWise.extractTop hashBase w₀ y1.mem) =
        PMF.uniformOfFintype (ReducedTopSeed w₀) := by
      have hc1 : (fun y1 : RData r => ReducedKWise.extractTop hashBase w₀ y1.mem) =
          ReducedKWise.topSliceEquiv w₀ ∘
            fun y1 => Tabulation.extractSlice hashBase (w₀ - 1) 1 y1.mem := rfl
      rw [hc1, ← PMF.map_comp, map_extractSlice_randFillRPMF rPtr rVal hpv,
        PMF.uniformOfFintype_map_equiv]
    have hinner : ∀ y1 : RData r,
        (μ2 y1).map (fun y => ReducedKWise.extractSeed hashBase w₀ b b' k y.mem) =
        (PMF.uniformOfFintype (ReducedBotSeed w₀ b b' k)).map
          (fun β => (ReducedKWise.extractTop hashBase w₀ y1.mem, β)) := fun y1 => by
      have hcongr : (μ2 y1).map (fun y => ReducedKWise.extractSeed hashBase w₀ b b' k y.mem) =
          (μ2 y1).map ((fun β => (ReducedKWise.extractTop hashBase w₀ y1.mem, β)) ∘
            ReducedKWise.botSliceEquiv w₀ b b' k ∘
            fun y => Tabulation.extractSlice (hashBase + 1) (rChunk w₀ b b')
              (k * rLimbs w₀ b b') y.mem) := by
        refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun y hy => ?_
        obtain ⟨_, _, _, hframe2⟩ := mem_support_randFillRPMF hpv hy
        have htop_eq : ReducedKWise.extractTop hashBase w₀ y.mem =
            ReducedKWise.extractTop hashBase w₀ y1.mem := by
          dsimp only [ReducedKWise.extractTop]; congr 1 with idx : 1
          dsimp only [Tabulation.extractSlice]
          rw [hframe2 (hashBase + idx.val) (Or.inl (by have := idx.isLt; omega))]; rfl
        dsimp only [Function.comp_apply, ReducedKWise.extractSeed, ReducedKWise.extractBot]
        rw [htop_eq]
      rw [hcongr, ← PMF.map_comp, ← PMF.map_comp, map_extractSlice_randFillRPMF rPtr rVal hpv,
        PMF.uniformOfFintype_map_equiv]
    have hbind_eq : μ1.bind (fun y1 => (μ2 y1).map
          (fun y => ReducedKWise.extractSeed hashBase w₀ b b' k y.mem)) =
        (μ1.map (fun y1 => ReducedKWise.extractTop hashBase w₀ y1.mem)).bind
          (fun α => (PMF.uniformOfFintype (ReducedBotSeed w₀ b b' k)).map (fun β => (α, β))) := by
      rw [PMF.bind_map]; exact congrArg _ (funext hinner)
    rw [PMF.map_bind, hbind_eq, hm1_unif, PMF.uniformOfFintype_prod]
  · intro y hy
    rw [PMF.mem_support_bind_iff] at hy
    obtain ⟨y1, hy1, hy2⟩ := hy
    obtain ⟨hfr1, hreg1, hlt1, hframe1⟩ := mem_support_randFillRPMF hpv hy1
    obtain ⟨hfr2, hreg2, hlt2, hframe2⟩ := mem_support_randFillRPMF hpv hy2
    have hframe_all : ∀ a, (a < hashBase ∨ hashBase + ReducedKWise.seedWords w₀ b b' k ≤ a) →
        y.mem a = x.mem a := fun a ha => by
      unfold ReducedKWise.seedWords at ha
      rw [hframe2 a (by omega)]; exact hframe1 a (by omega)
    refine ⟨hfr2.trans hfr1, ⟨?_, fun j m => ?_⟩, hframe_all, fun j hj => ?_⟩
    · have hm_eq : y.mem hashBase = y1.mem hashBase := hframe2 hashBase (Or.inl (by omega))
      have hlt_v : y1.mem hashBase < 2 ^ (w₀ - 1) := by simpa using hlt1 0 Nat.one_pos
      change y.mem hashBase = (ReducedKWise.extractTop hashBase w₀ y.mem).val
      rw [ReducedKWise.extractTop_val, hm_eq, wordOfNat_val_of_lt hlt_v]
    · have hidx_lt : m.val + rLimbs w₀ b b' * j.val < k * rLimbs w₀ b b' := by
        calc m.val + rLimbs w₀ b b' * j.val
            < rLimbs w₀ b b' + rLimbs w₀ b b' * j.val := Nat.add_lt_add_right m.isLt _
          _ = (j.val + 1) * rLimbs w₀ b b' := by ring
          _ ≤ k * rLimbs w₀ b b' := Nat.mul_le_mul_right _ j.isLt
      change y.mem (hashBase + 1 + (m.val + rLimbs w₀ b b' * j.val)) =
        getLimb (rChunk w₀ b b') (ReducedKWise.extractBot hashBase w₀ b b' k y.mem j).val m.val
      rw [ReducedKWise.getLimb_extractBot_val,
        wordOfNat_val_of_lt (hlt2 _ hidx_lt)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨hjp, hje, hjm, hjo, hjv⟩ := hj
      exact (hreg2 j hjp hjv).trans (by
        simp only [step2, RData.set_regs, Function.update_of_ne hjm, Function.update_of_ne hje,
          Function.update_of_ne hjp]
        exact (hreg1 j hjp hjv).trans (by
          simp [x1, Function.update_of_ne hjm, Function.update_of_ne hje,
            Function.update_of_ne hjo, Function.update_of_ne hjp]))

end Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise

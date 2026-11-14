/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise.ParamsInit

/-!
# Runtime Key Reduction and Trinomial-Field Horner Loop for `ReducedKWise`

Compiles Stage-1 overflow-free odd multiply-shift reduction (`reduceKeyGenProg`) and the Stage-2
runtime limb-by-limb Horner polynomial evaluation loop (`hornerStepGenProg`, `hornerLoop_spec`)
over $\mathrm{GF}(2)[X]/(X^{2 \cdot 3^t} + X^{3^t} + 1)$ of
[BenderFarachColtonKuszmaulKuszmaul2024] in `Memory.Prog` via `by realize`, storing the `≤ 54`
accumulator limbs and `≤ 108` product limbs in a 162-word scratch slice `[scratchBase, +162)`.

## Main definitions

* `Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise.hornerStepGenProg`,
  `HornerStepPre`: single Horner degree step (carryless multiplication + trinomial reduction +
  seed addition) in `Memory.Prog`.

## Main results

* `realizesBounded_hornerStepGen`, `hornerLoop_spec`: `RealizesBounded .exact` certificate and
  field-evaluation specification (`trinomialPolyEval`) for the `k`-step Horner loop.

## References

* [BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.HashFamily.WordRAM Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise
open Cslib.Probability

local notation "rStep" => reducedTrinomialStep
local notation "rChunk" w₀:arg b:arg b':arg => reducedChunkBits (reducedTrinomialStep w₀ b b')
local notation "rHalf" w₀:arg b:arg b':arg => reducedHalfLimbs (reducedTrinomialStep w₀ b b')
local notation "rLimbs" w₀:arg b:arg b':arg => reducedLimbCount (reducedTrinomialStep w₀ b b')
local notation "rPack" w:arg w₀:arg b:arg b':arg =>
  reducedPackShift (reducedTrinomialStep w₀ b b') w

/-! ## Section 3: Runtime `Memory.Prog` polynomial hash evaluation (`evalHashGenProg`) -/

private def innerClmulStepGenProg :
    (HashParams × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((hp, tBase, prodBase, i, uLimb), (m, curR)) => do
    let c := hpC hp; let maskC := hpMaskC hp
    let vLimb := curR &&& maskC; let idx := (uLimb <<< c) + vLimb
    let word ← Memory.read (tBase + (idx >>> hpP hp))
    let sh := (idx &&& hpMaskP hp) * hpTwoC hp
    let cl := (word >>> sh) &&& hpMask2C hp
    let lo := cl &&& maskC; let hi := cl >>> c; let im := i + m
    let old0 ← Memory.read (prodBase + im); Memory.write (prodBase + im) (old0 ^^^ lo)
    let old1 ← Memory.read (prodBase + im + 1); Memory.write (prodBase + im + 1) (old1 ^^^ hi)
    pure (m + 1, curR >>> c)

private def InnerClmulStepPre (w : ℕ) :
    (HashParams × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((hp, tBase, prodBase, i, uLimb), (m, curR)), s => ∃ w₀ b b' k hashBase,
    2 * rChunk w₀ b b' < w ∧ hp = mkHashParams w w₀ b b' k ∧
    tBase = ReducedKWise.tabBase hashBase w₀ b b' k ∧
    hashBase + ReducedKWise.space w w₀ b b' k ≤ s.frontier ∧
    prodBase + 2 * rLimbs w₀ b b' ≤ s.frontier ∧
    i < rLimbs w₀ b b' ∧ m < rLimbs w₀ b b' ∧ uLimb < 2 ^ rChunk w₀ b b' ∧ Fits w curR

private theorem realizesBounded_innerClmulStepGen :
    RealizesBounded .exact innerClmulStepGenProg
      (WordEncoding.encode (α := (HashParams × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ)) InnerClmulStepPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨hp, tBase, prodBase, i, uLimb⟩, ⟨m, curR⟩⟩
    obtain ⟨w₀, b, b', k, hashBase, hc_lt, rfl, rfl, hfr_h, hfr_p, hi_lt, hm_lt, hu_lt,
      hcur_fit⟩ := h
    try (dsimp only [hpC_mk, hpMaskC_mk, hpP_mk, hpMaskP_mk, hpTwoC_mk, hpMask2C_mk] at *)
    have hpack_le : 2 ^ rPack w w₀ b b' * (2 * rChunk w₀ b b') ≤ w :=
      two_pow_reducedPackShift_mul_le (le_of_lt hc_lt)
    have hpow2c : Fits w (2 ^ (2 * rChunk w₀ b b')) := Nat.pow_lt_pow_right one_lt_two hc_lt
    have hpowc : Fits w (2 ^ rChunk w₀ b b') :=
      hpow2c.of_le (Nat.pow_le_pow_right two_pos (by omega))
    have hv_lt := and_two_pow_sub_one_lt curR (rChunk w₀ b b')
    have hu_sh_lt : uLimb <<< rChunk w₀ b b' < 2 ^ (2 * rChunk w₀ b b') := by
      rw [Nat.shiftLeft_eq, two_mul, pow_add]
      exact Nat.mul_lt_mul_of_pos_right hu_lt (Nat.two_pow_pos _)
    have hidx_lt :
        (uLimb <<< rChunk w₀ b b') + (curR &&& (2 ^ rChunk w₀ b b' - 1)) <
          2 ^ (2 * rChunk w₀ b b') := by
      rw [Nat.shiftLeft_eq]
      calc uLimb * 2 ^ rChunk w₀ b b' + (curR &&& (2 ^ rChunk w₀ b b' - 1))
          < uLimb * 2 ^ rChunk w₀ b b' + 2 ^ rChunk w₀ b b' := Nat.add_lt_add_left hv_lt _
        _ = (uLimb + 1) * 2 ^ rChunk w₀ b b' := by ring
        _ ≤ 2 ^ rChunk w₀ b b' * 2 ^ rChunk w₀ b b' := Nat.mul_le_mul_right _ hu_lt
        _ = 2 ^ (2 * rChunk w₀ b b') := by rw [← pow_add, two_mul]
    have hwIdx_lt := shiftRight_lt_reducedTableWords (w := w) hidx_lt
    have hge_wIdx := Nat.zero_le (((uLimb <<< rChunk w₀ b b') +
      (curR &&& (2 ^ rChunk w₀ b b' - 1))) >>> rPack w w₀ b b')
    have ht_fr :
        ReducedKWise.tabBase hashBase w₀ b b' k + reducedTableWords (rStep w₀ b b') w ≤
          s.frontier := by
      simpa only [ReducedKWise.tabBase, ReducedKWise.space, ReducedKWise.tableWords,
        Nat.add_assoc] using hfr_h
    have hsh_lt :
        (((uLimb <<< rChunk w₀ b b') + (curR &&& (2 ^ rChunk w₀ b b' - 1))) &&&
          (2 ^ rPack w w₀ b b' - 1)) * (2 * rChunk w₀ b b') < w :=
      (Nat.mul_lt_mul_of_pos_right (and_two_pow_sub_one_lt _ _)
        (have := reducedChunkBits_pos (rStep w₀ b b'); by omega)).trans_le hpack_le)
  all_goals try exact hpow2c.of_le (le_of_lt hidx_lt)
  all_goals try exact hmem.1.of_le (by omega)
  all_goals try exact hsh_lt.trans Nat.lt_two_pow_self
  all_goals (try
    exact Nat.xor_lt_two_pow (hmem.2 _)
      (hpowc.of_le (le_of_lt (and_two_pow_sub_one_lt _ (rChunk w₀ b b')))))
  all_goals (try
    refine Nat.xor_lt_two_pow ?_ (hpow2c.of_le
      ((Nat.shiftRight_le _ _).trans (le_of_lt (and_two_pow_sub_one_lt _ (2 * rChunk w₀ b b')))))
    rw [Function.update_of_ne (by omega)]; exact hmem.2 _)

private theorem innerClmulLoop_spec {w w₀ b b' k hashBase prodBase i uLimb rVal : ℕ}
    {s₀ : Memory.State}
    (hc_lt : 2 * rChunk w₀ b b' < w)
    (hfr_h : hashBase + ReducedKWise.space w w₀ b b' k ≤ s₀.frontier)
    (hfr_p : prodBase + 2 * rLimbs w₀ b b' ≤ s₀.frontier)
    (hdisj : hashBase + ReducedKWise.space w w₀ b b' k ≤ prodBase ∨
      prodBase + 2 * rLimbs w₀ b b' ≤ hashBase)
    (htab : ReducedKWise.TableRep hashBase w w₀ b b' k s₀.mem)
    (hi_lt : i < rLimbs w₀ b b') (hu_lt : uLimb < 2 ^ rChunk w₀ b b') (hr_fit : Fits w rVal)
    (hprod₀ : ∀ d < 2 * rLimbs w₀ b b', s₀.mem (prodBase + d) < 2 ^ rChunk w₀ b b') :
    let hp := mkHashParams w w₀ b b' k
    let env := (hp, ReducedKWise.tabBase hashBase w₀ b b' k, prodBase, i, uLimb)
    let prog := iterate innerClmulStepGenProg env (rLimbs w₀ b b') (0, rVal)
    let s' := (Memory.spec 0).clientState s₀ prog
    iterationSafe innerClmulStepGenProg InnerClmulStepPre w env (rLimbs w₀ b b') (0, rVal) s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ 5 * rLimbs w₀ b b' ∧ s'.frontier = s₀.frontier ∧
    (∀ d < 2 * rLimbs w₀ b b', s'.mem (prodBase + d) < 2 ^ rChunk w₀ b b') ∧
    packLimbs (rChunk w₀ b b') (2 * rLimbs w₀ b b') (fun d => s'.mem (prodBase + d)) =
      packLimbs (rChunk w₀ b b') (2 * rLimbs w₀ b b') (fun d => s₀.mem (prodBase + d)) ^^^
        (clmul uLimb (truncLimbs (rChunk w₀ b b') (rLimbs w₀ b b') rVal) <<<
          (i * rChunk w₀ b b')) ∧
    (∀ a, (a < prodBase ∨ prodBase + 2 * rLimbs w₀ b b' ≤ a) → s'.mem a = s₀.mem a) := by
  intro hp env prog s'
  have hc_pos : 0 < rChunk w₀ b b' := reducedChunkBits_pos _
  have hpow2c : Fits w (2 ^ (2 * rChunk w₀ b b')) := Nat.pow_lt_pow_right one_lt_two hc_lt
  have hpowc : Fits w (2 ^ rChunk w₀ b b') :=
    hpow2c.of_le (Nat.pow_le_pow_right two_pos (by omega))
  let P₀ := packLimbs (rChunk w₀ b b') (2 * rLimbs w₀ b b') (fun d => s₀.mem (prodBase + d))
  let inv (m : ℕ) (st : ℕ × ℕ) (s : Memory.State) : Prop :=
    (m, rVal >>> (m * rChunk w₀ b b')) = st ∧ s.frontier = s₀.frontier ∧
    ReducedKWise.TableRep hashBase w w₀ b b' k s.mem ∧
    (∀ d < 2 * rLimbs w₀ b b', s.mem (prodBase + d) < 2 ^ rChunk w₀ b b') ∧
    packLimbs (rChunk w₀ b b') (2 * rLimbs w₀ b b') (fun d => s.mem (prodBase + d)) =
      P₀ ^^^ (clmul uLimb (truncLimbs (rChunk w₀ b b') m rVal) <<< (i * rChunk w₀ b b'))
  obtain ⟨hsafe, hv, hcost, hfr', hmod, _, _, _, hprod', hpack'⟩ :=
    iterate_spec innerClmulStepGenProg InnerClmulStepPre w env 5 (rLimbs w₀ b b') inv
      (fun x => prodBase ≤ x ∧ x < prodBase + 2 * rLimbs w₀ b b')
      (fun m hm st s ⟨hst, hfr_eq, htab_s, hprod_s, hpack_s⟩ => by
        subst hst
        let curR := rVal >>> (m * rChunk w₀ b b')
        let vLimb := curR &&& (2 ^ rChunk w₀ b b' - 1)
        have hv_lt : vLimb < 2 ^ rChunk w₀ b b' := and_two_pow_sub_one_lt curR _
        let idx := (uLimb <<< rChunk w₀ b b') + vLimb
        have hidx_lt : idx < 2 ^ (2 * rChunk w₀ b b') := by
          dsimp only [idx]; rw [Nat.shiftLeft_eq]
          calc uLimb * 2 ^ rChunk w₀ b b' + vLimb
              < uLimb * 2 ^ rChunk w₀ b b' + 2 ^ rChunk w₀ b b' := Nat.add_lt_add_left hv_lt _
            _ = (uLimb + 1) * 2 ^ rChunk w₀ b b' := by ring
            _ ≤ 2 ^ rChunk w₀ b b' * 2 ^ rChunk w₀ b b' := Nat.mul_le_mul_right _ hu_lt
            _ = 2 ^ (2 * rChunk w₀ b b') := by rw [← pow_add, two_mul]
        have hidx_u : idx >>> rChunk w₀ b b' = uLimb := by
          dsimp only [idx]; rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, mul_comm uLimb,
            Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hv_lt, Nat.add_zero]
        have hidx_v : idx &&& (2 ^ rChunk w₀ b b' - 1) = vLimb := by
          dsimp only [idx]; rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, Nat.add_comm,
            Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv_lt]
        have hwIdx_lt := shiftRight_lt_reducedTableWords (w := w) hidx_lt
        have hcl_eq :
            ((s.mem (ReducedKWise.tabBase hashBase w₀ b b' k + (idx >>> rPack w w₀ b b')) >>>
              ((idx &&& (2 ^ rPack w w₀ b b' - 1)) * (2 * rChunk w₀ b b'))) &&&
              (2 ^ (2 * rChunk w₀ b b') - 1)) = clmul uLimb vLimb := by
          change getLimb (2 * rChunk w₀ b b')
            (s.mem (ReducedKWise.tabBase hashBase w₀ b b' k + (idx >>> rPack w w₀ b b')))
            (idx &&& (2 ^ rPack w w₀ b b' - 1)) = _
          rw [htab_s.2 idx hidx_lt, hidx_u, hidx_v]
        have hcl_lt := clmul_lt_two_pow_two_mul hu_lt hv_lt
        let lo := clmul uLimb vLimb &&& (2 ^ rChunk w₀ b b' - 1)
        let hi := clmul uLimb vLimb >>> rChunk w₀ b b'
        have hlo_lt : lo < 2 ^ rChunk w₀ b b' := and_two_pow_sub_one_lt _ _
        have hhi_lt : hi < 2 ^ rChunk w₀ b b' := by
          dsimp only [hi]; rw [Nat.shiftRight_eq_div_pow]
          exact Nat.div_lt_of_lt_mul (by rwa [← pow_add, ← two_mul])
        set s₁ := (Memory.spec 0).clientState s (innerClmulStepGenProg (env, (m, curR)))
        have hs₁_mem : s₁.mem = Function.update
            (Function.update s.mem (prodBase + (i + m)) (s.mem (prodBase + (i + m)) ^^^ lo))
            (prodBase + (i + m) + 1) (s.mem (prodBase + (i + m) + 1) ^^^ hi) := by
          dsimp only [s₁, innerClmulStepGenProg, env, hp, hpC_mk, hpMaskC_mk, hpP_mk,
            hpMaskP_mk, hpTwoC_mk, hpMask2C_mk, lo, hi, idx, vLimb]
          change Function.update (Function.update s.mem (prodBase + (i + m)) _)
            (prodBase + (i + m) + 1) (Function.update s.mem (prodBase + (i + m)) _
              (prodBase + (i + m) + 1) ^^^ _) = _
          rw [hcl_eq, Function.update_of_ne (by omega)]
        have hmod₁ :
            ∀ x, ¬(prodBase ≤ x ∧ x < prodBase + 2 * rLimbs w₀ b b') → s₁.mem x = s.mem x :=
          fun x hx => by rw [hs₁_mem, Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
        let f := fun d => s.mem (prodBase + d)
        have hs₁_fn : ∀ d < 2 * rLimbs w₀ b b', s₁.mem (prodBase + d) =
            Function.update (Function.update f (i + m) (f (i + m) ^^^ lo))
              (i + m + 1) (f (i + m + 1) ^^^ hi) d := fun d _ => by
          rw [hs₁_mem]
          rcases eq_or_ne d (i + m + 1) with rfl | hne1
          · have had : prodBase + (i + m + 1) = prodBase + (i + m) + 1 := by omega
            dsimp only [f]; rw [had, Function.update_self, Function.update_self]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne hne1]
            rcases eq_or_ne d (i + m) with rfl | hne0
            · dsimp only [f]; rw [Function.update_self, Function.update_self]
            · rw [Function.update_of_ne (by omega), Function.update_of_ne hne0]
        refine ⟨⟨w₀, b, b', k, hashBase, hc_lt, rfl, rfl, hfr_eq.symm ▸ hfr_h, hfr_eq.symm ▸ hfr_p,
          hi_lt, hm, hu_lt, hr_fit.of_le (Nat.shiftRight_le _ _)⟩, ?_, le_rfl, rfl, hmod₁, ?_,
          hfr_eq, tableRep_congr htab_s (fun a h1 h2 => (hmod₁ a (by omega)).symm),
          fun d hd => ?_, ?_⟩
        · have ht_fr :
              ReducedKWise.tabBase hashBase w₀ b b' k + reducedTableWords (rStep w₀ b b') w ≤
                s.frontier := by
            rw [hfr_eq]
            unfold ReducedKWise.space ReducedKWise.tableWords at hfr_h; unfold
              ReducedKWise.tabBase; omega
          have hlt_t := lt_of_lt_of_le (Nat.add_lt_add_left hwIdx_lt _) ht_fr
          have hlt_p0 : prodBase + (i + m) < s.frontier := by rw [hfr_eq]; omega
          have hlt_p1 : prodBase + (i + m) + 1 < s.frontier := by rw [hfr_eq]; omega
          dsimp only [innerClmulStepGenProg, env, hp, hpC_mk, hpMaskC_mk, hpP_mk, hpMaskP_mk,
            hpTwoC_mk, hpMask2C_mk]
          refine ⟨hlt_t, hlt_p0, ⟨hlt_p0, hpowc.of_le (le_of_lt (Nat.xor_lt_two_pow
            (hprod_s (i + m) (by omega)) (and_two_pow_sub_one_lt _ _)))⟩, hlt_p1,
            ⟨hlt_p1, ?_⟩, trivial⟩
          change Fits w (Function.update s.mem (prodBase + (i + m)) _ (prodBase + (
            i + m) + 1) ^^^ _)
          rw [Function.update_of_ne (by omega), hcl_eq]
          have h1 : s.mem (prodBase + (i + m) + 1) < 2 ^ rChunk w₀ b b' := by
            simpa only [show prodBase + (i + m) + 1 = prodBase + (i + m + 1) by omega] using
              hprod_s (i + m + 1) (by omega)
          exact hpowc.of_le (le_of_lt (Nat.xor_lt_two_pow h1 hhi_lt))
        · change (m + 1, rVal >>> ((m + 1) * rChunk w₀ b b')) =
            (m + 1, (rVal >>> (m * rChunk w₀ b b')) >>> rChunk w₀ b b')
          rw [← Nat.shiftRight_add, ← Nat.succ_mul]
        · rw [hs₁_fn d hd]
          rcases eq_or_ne d (i + m + 1) with rfl | hne1
          · rw [Function.update_self]; exact Nat.xor_lt_two_pow (hprod_s _ hd) hhi_lt
          · rw [Function.update_of_ne hne1]
            rcases eq_or_ne d (i + m) with rfl | hne0
            · rw [Function.update_self]; exact Nat.xor_lt_two_pow (hprod_s _ hd) hlo_lt
            · rw [Function.update_of_ne hne0]; exact hprod_s d hd
        · rw [packLimbs_congr hs₁_fn, packLimbs_update_pair hc_pos f (by omega) hcl_lt,
            hpack_s, Nat.xor_assoc]
          change P₀ ^^^ (clmul uLimb (truncLimbs (rChunk w₀ b b') m rVal) <<<
              (i * rChunk w₀ b b') ^^^
            clmul uLimb (getLimb (rChunk w₀ b b') rVal m) <<< ((i + m) * rChunk w₀ b b')) = _
          rw [← clmul_truncLimbs_right_succ])
      (0, rVal) s₀ ⟨by simp only [Nat.zero_mul, Nat.shiftRight_zero], rfl, htab, hprod₀,
        by rw [truncLimbs_zero, clmul_zero_right, Nat.zero_shiftLeft, Nat.xor_zero]⟩
  exact ⟨hsafe, hv, hcost, hfr', hprod', hpack', fun a ha => hmod a (by omega)⟩

/-- Outer carryless multiplication step subroutine. -/
def outerClmulStepGenProg : (HashParams × ℕ × ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((hp, tBase, scratchBase, rVal), i) => do
    let uLimb ← Memory.read (scratchBase + i)
    let prodBase ← pure (scratchBase + accWords)
    let _ ← iterate innerClmulStepGenProg (hp, tBase, prodBase, i, uLimb) (2 * hpL0 hp) (0, rVal)
    pure (i + 1)

private def OuterClmulStepPre (w : ℕ) :
    (HashParams × ℕ × ℕ × ℕ) × ℕ → Memory.State → Prop
  | ((hp, tBase, scratchBase, rVal), i), s => ∃ w₀ b b' k hashBase,
    2 * rChunk w₀ b b' < w ∧ hp = mkHashParams w w₀ b b' k ∧
    tBase = ReducedKWise.tabBase hashBase w₀ b b' k ∧
    hashBase + ReducedKWise.space w w₀ b b' k ≤ s.frontier ∧
    scratchBase + scratchWords ≤ s.frontier ∧
    (hashBase + ReducedKWise.space w w₀ b b' k ≤ scratchBase ∨
      scratchBase + scratchWords ≤ hashBase) ∧
    ReducedKWise.TableRep hashBase w w₀ b b' k s.mem ∧
    i < rLimbs w₀ b b' ∧ Fits w rVal ∧
    (∀ m < rLimbs w₀ b b', s.mem (scratchBase + m) < 2 ^ rChunk w₀ b b') ∧
    (∀ d < 2 * rLimbs w₀ b b', s.mem (scratchBase + accWords + d) < 2 ^ rChunk w₀ b b')

private theorem realizesBounded_outerClmulStepGen :
    RealizesBounded .exact outerClmulStepGenProg
      (WordEncoding.encode (α := (HashParams × ℕ × ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ)) OuterClmulStepPre (fun _ _ => 0) := by
  have hinner := realizesBounded_innerClmulStepGen
  realize
  all_goals (
    rcases d with ⟨⟨hp, tBase, scratchBase, rVal⟩, i⟩
    obtain ⟨w₀, b, b', k, hashBase, hc_lt, rfl, rfl, hfr_h, hfr_s, hdisj, htab,
      hi_lt, hr_fit, hacc_lt, hprod_lt⟩ := h
    try (dsimp only [hpL0_mk] at *)
    try dsimp only [accWords, prodWords, scratchWords] at *
    have hL_le : rLimbs w₀ b b' ≤ 54 := reducedLimbCount_le _
    have hL_eq : 2 * rHalf w₀ b b' = rLimbs w₀ b b' := rfl)
  all_goals try exact hmem.1.of_le (by omega)
  all_goals (
    rw [hL_eq]
    have haccW : accWords = 54 := rfl
    have hscrW : scratchWords = 162 := rfl
    exact iterationSafe_imp
      (innerClmulLoop_spec hc_lt hfr_h (by omega) (by omega) htab hi_lt (hacc_lt i hi_lt)
        hr_fit hprod_lt).1
      (fun _ => rfl) (fun _ _ hs => hs))

private theorem outerClmulLoop_spec {w w₀ b b' k hashBase scratchBase rVal accVal : ℕ}
    {s₀ : Memory.State}
    (hc_lt : 2 * rChunk w₀ b b' < w)
    (hfr_h : hashBase + ReducedKWise.space w w₀ b b' k ≤ s₀.frontier)
    (hfr_s : scratchBase + scratchWords ≤ s₀.frontier)
    (hdisj : hashBase + ReducedKWise.space w w₀ b b' k ≤ scratchBase ∨
      scratchBase + scratchWords ≤ hashBase)
    (htab : ReducedKWise.TableRep hashBase w w₀ b b' k s₀.mem)
    (hr_fit : Fits w rVal) (hr_lt : rVal < 2 ^ (rLimbs w₀ b b' * rChunk w₀ b b'))
    (hacc_lt : accVal < 2 ^ (rLimbs w₀ b b' * rChunk w₀ b b'))
    (hacc₀ : ∀ m < rLimbs w₀ b b', s₀.mem (scratchBase + m) = getLimb (rChunk w₀ b b') accVal m)
    (hprod₀_zero : ∀ d < 2 * rLimbs w₀ b b', s₀.mem (scratchBase + accWords + d) = 0) :
    let hp := mkHashParams w w₀ b b' k
    let env := (hp, ReducedKWise.tabBase hashBase w₀ b b' k, scratchBase, rVal)
    let prog := iterate outerClmulStepGenProg env (rLimbs w₀ b b') 0
    let s' := (Memory.spec 0).clientState s₀ prog
    iterationSafe outerClmulStepGenProg OuterClmulStepPre w env (rLimbs w₀ b b') 0 s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ (1 + 5 * rLimbs w₀ b b') * rLimbs w₀ b b' ∧ s'.frontier = s₀.frontier ∧
    (∀ d < 2 * rLimbs w₀ b b',
      s'.mem (scratchBase + accWords + d) = getLimb (rChunk w₀ b b') (clmul accVal rVal) d) ∧
    (∀ a, (a < scratchBase + accWords ∨ scratchBase + accWords + 2 * rLimbs w₀ b b' ≤ a) →
      s'.mem a = s₀.mem a) := by
  have haccW : accWords = 54 := rfl
  have hscrW : scratchWords = 162 := rfl
  intro hp env prog s'
  have hL_le : rLimbs w₀ b b' ≤ 54 := reducedLimbCount_le _
  have hprod₀_pack :
      packLimbs (rChunk w₀ b b') (2 * rLimbs w₀ b b')
        (fun d => s₀.mem (scratchBase + accWords + d)) = 0 := by
    have hz : ∀ n, packLimbs (rChunk w₀ b b') n (fun _ => 0) = 0 := fun n => by
      induction n with
      | zero => rfl
      | succ n ih => simp only [packLimbs, ih, Nat.zero_and, Nat.zero_shiftLeft, Nat.xor_zero]
    rw [packLimbs_congr (g := fun _ => 0) hprod₀_zero, hz]
  let inv (i st : ℕ) (s : Memory.State) : Prop :=
    i = st ∧ s.frontier = s₀.frontier ∧
    ReducedKWise.TableRep hashBase w w₀ b b' k s.mem ∧
    (∀ m < rLimbs w₀ b b', s.mem (scratchBase + m) = getLimb (rChunk w₀ b b') accVal m) ∧
    (∀ d < 2 * rLimbs w₀ b b', s.mem (scratchBase + accWords + d) < 2 ^ rChunk w₀ b b') ∧
    packLimbs (rChunk w₀ b b') (2 * rLimbs w₀ b b') (fun d => s.mem (scratchBase + accWords + d)) =
      clmul (truncLimbs (rChunk w₀ b b') i accVal) rVal
  obtain ⟨hsafe, hv, hcost, hfr', hmod, _, _, _, _, hprod_lt', hpack'⟩ :=
    iterate_spec outerClmulStepGenProg OuterClmulStepPre w env (1 + 5 * rLimbs w₀ b b')
      (rLimbs w₀ b b') inv
      (fun x => scratchBase + accWords ≤ x ∧ x < scratchBase + accWords + 2 * rLimbs w₀ b b')
      (fun i hi st s ⟨hst, hfr_eq, htab_s, hacc_s, hprod_s, hpack_s⟩ => by
        subst hst
        have hu_eq := hacc_s i hi
        have hu_lt : s.mem (scratchBase + i) < 2 ^ rChunk w₀ b b' :=
          hu_eq ▸ getLimb_lt (rChunk w₀ b b') accVal i
        obtain ⟨_, hv_in, hcost_in, hfr_in, hprod_in, hpack_in, hout_in⟩ :=
          innerClmulLoop_spec hc_lt (hfr_eq.symm ▸ hfr_h) (by rw [hfr_eq]; omega) (by omega)
            htab_s hi hu_lt hr_fit hprod_s
        set stepP := outerClmulStepGenProg (env, i)
        have hstep_eq : stepP = (do
            let uLimb ← Memory.read (scratchBase + i)
            let _ ← iterate innerClmulStepGenProg (hp, ReducedKWise.tabBase hashBase w₀ b b' k,
              scratchBase + accWords, i, uLimb) (rLimbs w₀ b b') (0, rVal)
            pure (i + 1)) := rfl
        set s_in := (Memory.spec 0).clientState s
          (iterate innerClmulStepGenProg (hp, ReducedKWise.tabBase hashBase w₀ b b' k,
            scratchBase + accWords, i, s.mem (scratchBase + i)) (rLimbs w₀ b b') (0, rVal))
        have hs₁_eq : (Memory.spec 0).clientState s stepP = s_in := by
          rw [hstep_eq, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
          rfl
        refine ⟨⟨w₀, b, b', k, hashBase, hc_lt, rfl, rfl, hfr_eq.symm ▸ hfr_h, hfr_eq.symm ▸ hfr_s,
          hdisj, htab_s, hi, hr_fit, fun m hm => hacc_s m hm ▸ getLimb_lt _ accVal m, hprod_s⟩,
          ?_, ?_, by rw [hs₁_eq]; exact hfr_in,
          fun x hx => by rw [hs₁_eq]; exact hout_in x (by omega),
          by rw [hstep_eq, StateTransitionSpec.clientResult_bind,
                 StateTransitionSpec.clientResult_bind]; rfl,
          by rw [hs₁_eq, hfr_in, hfr_eq],
          tableRep_congr htab_s
            (fun a h1 h2 => by rw [hs₁_eq]; exact (hout_in a (by omega)).symm),
          fun m hm => by rw [hs₁_eq, hout_in _ (Or.inl (by omega))]; exact hacc_s m hm,
          by rw [hs₁_eq]; exact hprod_in, ?_⟩
        · rw [hstep_eq, validHistory_bind', validHistory_bind']
          exact ⟨by change scratchBase + i < s.frontier ∧ True; rw [hfr_eq]; exact ⟨by omega,
            trivial⟩,
            hv_in, trivial⟩
        · rw [hstep_eq, memoryCost_bind', memoryCost_bind', memoryCost_pure, Nat.add_zero]
          exact Nat.add_le_add_left hcost_in 1
        · rw [hs₁_eq, hpack_in, hpack_s, hu_eq, truncLimbs_of_lt hr_lt,
            ← clmul_truncLimbs_left_succ])
      0 s₀ ⟨rfl, rfl, htab, hacc₀, fun d hd => by rw [hprod₀_zero d hd]; exact Nat.two_pow_pos _,
        by rw [hprod₀_pack, truncLimbs_zero, clmul_zero_left]⟩
  rw [truncLimbs_of_lt hacc_lt] at hpack'
  refine ⟨hsafe, hv, hcost, hfr', fun d hd => ?_, fun a ha => hmod a (by omega)⟩
  rw [← hpack', getLimb_packLimbs_of_lt _ hd (hprod_lt' d hd)]

/-- Remainder addition step subroutine. -/
def reduceAddStepGenProg : (HashParams × ℕ × ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((hp, hashBase, scratchBase, coeffOff), m) => do
    let seedLimb ← Memory.read (hashBase + coeffOff + m)
    let prodBase := scratchBase + accWords; let L₀ := hpL0 hp
    let p0 ← Memory.read (prodBase + m)
    let redLimb ←
      if m < L₀ then do
        let p3 ← Memory.read (prodBase + (3 * L₀ + m))
        let p2 ← Memory.read (prodBase + (2 * L₀ + m))
        pure ((p0 ^^^ p3) ^^^ p2)
      else do
        let p1 ← Memory.read (prodBase + (L₀ + m))
        pure (p0 ^^^ p1)
    Memory.write (scratchBase + m) (redLimb ^^^ seedLimb)
    pure (m + 1)

private def ReduceAddStepPre (w : ℕ) :
    (HashParams × ℕ × ℕ × ℕ) × ℕ → Memory.State → Prop
  | ((hp, hashBase, scratchBase, coeffOff), m), s => ∃ w₀ b b' k,
    2 * rChunk w₀ b b' < w ∧ hp = mkHashParams w w₀ b b' k ∧
    coeffOff + rLimbs w₀ b b' ≤ ReducedKWise.seedWords w₀ b b' k ∧
    hashBase + ReducedKWise.space w w₀ b b' k ≤ s.frontier ∧
    scratchBase + scratchWords ≤ s.frontier ∧ m < rLimbs w₀ b b'

private theorem realizesBounded_reduceAddStepGen :
    RealizesBounded .exact reduceAddStepGenProg
      (WordEncoding.encode (α := (HashParams × ℕ × ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ)) ReduceAddStepPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨hp, hashBase, scratchBase, coeffOff⟩, m⟩
    obtain ⟨w₀, b, b', k, hc_lt, rfl, hcoeff, hfr_h, hfr_s, hm_lt⟩ := h
    try (dsimp only [hpL0_mk] at *)
    try dsimp only [accWords, prodWords, scratchWords] at *
    have hL_eq : rLimbs w₀ b b' = 2 * rHalf w₀ b b' := rfl
    have hL0_le : rHalf w₀ b b' ≤ 27 := reducedHalfLimbs_le _
    have hxor3 := Nat.xor_lt_two_pow
      (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (hmem.2 (scratchBase + accWords + m))
        (hmem.2 (scratchBase + accWords + (3 * rHalf w₀ b b' + m))))
        (hmem.2 (scratchBase + accWords + (2 * rHalf w₀ b b' + m))))
      (hmem.2 (hashBase + coeffOff + m)))
  all_goals try exact hmem.1.of_le (by unfold ReducedKWise.space at hfr_h; omega)
  all_goals try exact Nat.xor_lt_two_pow (hmem.2 _) (hmem.2 _)
  all_goals try exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (hmem.2 _) (hmem.2 _)) (hmem.2 _)
  all_goals exact hxor3

private theorem reduceAddLoop_spec {w w₀ b b' k hashBase scratchBase PVal : ℕ}
    {θ : ReducedPolySeed w₀ b b' k} {coeffIdx : Fin k} {s₀ : Memory.State}
    (hc_lt : 2 * rChunk w₀ b b' < w)
    (hfr_h : hashBase + ReducedKWise.space w w₀ b b' k ≤ s₀.frontier)
    (hfr_s : scratchBase + scratchWords ≤ s₀.frontier)
    (hdisj : hashBase + ReducedKWise.space w w₀ b b' k ≤ scratchBase ∨
      scratchBase + scratchWords ≤ hashBase)
    (hP_lt : PVal < 2 ^ (2 * rLimbs w₀ b b' * rChunk w₀ b b'))
    (hseed : ReducedKWise.SeedRep hashBase w₀ b b' k θ s₀.mem)
    (hprod₀ : ∀ d < 2 * rLimbs w₀ b b',
      s₀.mem (scratchBase + accWords + d) = getLimb (rChunk w₀ b b') PVal d) :
    let hp := mkHashParams w w₀ b b' k
    let coeffOff := 1 + rLimbs w₀ b b' * coeffIdx.val
    let newAcc := reduceTrinomialCode (rStep w₀ b b') PVal ^^^ (θ.2 coeffIdx).val
    let env := (hp, hashBase, scratchBase, coeffOff)
    let prog := iterate reduceAddStepGenProg env (rLimbs w₀ b b') 0
    let s' := (Memory.spec 0).clientState s₀ prog
    iterationSafe reduceAddStepGenProg ReduceAddStepPre w env (rLimbs w₀ b b') 0 s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ 5 * rLimbs w₀ b b' ∧ s'.frontier = s₀.frontier ∧
    (∀ i < rLimbs w₀ b b', s'.mem (scratchBase + i) = getLimb (rChunk w₀ b b') newAcc i) ∧
    (∀ a, (a < scratchBase ∨ scratchBase + rLimbs w₀ b b' ≤ a) → s'.mem a = s₀.mem a) := by
  have haccW : accWords = 54 := rfl
  have hscrW : scratchWords = 162 := rfl
  intro hp coeffOff newAcc env prog s'
  have hL_eq : rLimbs w₀ b b' = 2 * rHalf w₀ b b' := rfl
  have hL0_le : rHalf w₀ b b' ≤ 27 := reducedHalfLimbs_le _
  have hpow2c : Fits w (2 ^ (2 * rChunk w₀ b b')) := Nat.pow_lt_pow_right one_lt_two hc_lt
  have hpowc : Fits w (2 ^ rChunk w₀ b b') :=
    hpow2c.of_le (Nat.pow_le_pow_right two_pos (by omega))
  have hcoeff_le : coeffOff + rLimbs w₀ b b' ≤ ReducedKWise.seedWords w₀ b b' k := by
    have hmul : rLimbs w₀ b b' * coeffIdx.val + rLimbs w₀ b b' ≤ k * rLimbs w₀ b b' := by
      calc rLimbs w₀ b b' * coeffIdx.val + rLimbs w₀ b b'
          = (coeffIdx.val + 1) * rLimbs w₀ b b' := by ring
        _ ≤ k * rLimbs w₀ b b' := Nat.mul_le_mul_right _ coeffIdx.isLt
    dsimp only [coeffOff]; unfold ReducedKWise.seedWords; omega
  let inv (m st : ℕ) (s : Memory.State) : Prop :=
    m = st ∧ s.frontier = s₀.frontier ∧
    ReducedKWise.SeedRep hashBase w₀ b b' k θ s.mem ∧
    (∀ d < 2 * rLimbs w₀ b b',
      s.mem (scratchBase + accWords + d) = getLimb (rChunk w₀ b b') PVal d) ∧
    (∀ i < m, s.mem (scratchBase + i) = getLimb (rChunk w₀ b b') newAcc i)
  obtain ⟨hsafe, hv, hcost, hfr', hmod, _, _, _, _, hacc'⟩ :=
    iterate_spec reduceAddStepGenProg ReduceAddStepPre w env 5 (rLimbs w₀ b b') inv
      (fun x => scratchBase ≤ x ∧ x < scratchBase + rLimbs w₀ b b')
      (fun m hm st s ⟨hst, hfr_eq, hseed_s, hprod_s, hacc_s⟩ => by
        subst hst
        have hseed_eq :
            s.mem (hashBase + coeffOff + m) = getLimb (rChunk w₀ b b') (θ.2 coeffIdx).val m := by
          rw [show hashBase + coeffOff + m = hashBase + 1 + (m + rLimbs w₀ b b' * coeffIdx.val) by
            dsimp only [coeffOff]; ring]
          exact hseed_s.2 coeffIdx ⟨m, hm⟩
        set stepP := reduceAddStepGenProg (env, m)
        set s₁ := (Memory.spec 0).clientState s stepP
        have hlt_seed : hashBase + coeffOff + m < s.frontier := by
          rw [hfr_eq]; unfold ReducedKWise.space at hfr_h; omega
        have hlt_p0 : scratchBase + accWords + m < s.frontier := by rw [hfr_eq]; omega
        have hlt_scr : scratchBase + m < s.frontier := by rw [hfr_eq]; omega
        have hstep_props : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s stepP) ∧
            memoryCost stepP s ≤ 5 ∧ (Memory.spec 0).clientResult s stepP = m + 1 ∧
            s₁.frontier = s.frontier ∧
            s₁.mem = Function.update s.mem (scratchBase + m) (getLimb (
              rChunk w₀ b b') newAcc m) := by
          dsimp only [s₁, stepP, reduceAddStepGenProg, env, hp, hpL0_mk]
          by_cases hm_low' : m < rHalf w₀ b b'
          · simp only [hm_low', ↓reduceIte]
            have hval_eq : (((s.mem (scratchBase + accWords + m) ^^^
                s.mem (scratchBase + accWords + (3 * rHalf w₀ b b' + m))) ^^^
                s.mem (scratchBase + accWords + (2 * rHalf w₀ b b' + m))) ^^^
                s.mem (hashBase + coeffOff + m)) = getLimb (rChunk w₀ b b') newAcc m := by
              rw [hprod_s m (by omega), hprod_s (3 * rHalf w₀ b b' + m) (by omega),
                hprod_s (2 * rHalf w₀ b b' + m) (by omega),
                (getLimb_reduceTrinomialCode_low (rStep w₀ b b') PVal hm_low').symm,
                hseed_eq, ← getLimb_xor]
            refine ⟨⟨hlt_seed, hlt_p0, ?_, ?_, ⟨hlt_scr,
              hval_eq ▸ hpowc.of_le (le_of_lt (getLimb_lt _ _ _))⟩, trivial⟩,
              le_rfl, rfl, rfl, congrArg (Function.update s.mem (scratchBase + m)) hval_eq⟩
            · change scratchBase + accWords + (3 * rHalf w₀ b b' + m) < s.frontier
              rw [hfr_eq]; omega
            · change scratchBase + accWords + (2 * rHalf w₀ b b' + m) < s.frontier
              rw [hfr_eq]; omega
          · simp only [hm_low', ↓reduceIte]
            have hm_ge : rHalf w₀ b b' ≤ m := le_of_not_gt hm_low'
            have hhigh := getLimb_reduceTrinomialCode_high (rStep w₀ b b') PVal
              (m := m - rHalf w₀ b b') (by omega)
            dsimp only at hhigh
            rw [Nat.add_sub_of_le hm_ge,
              show 2 * rHalf w₀ b b' + (m - rHalf w₀ b b') = rHalf w₀ b b' + m by omega,
              getLimb_eq_zero_of_lt (d := 4 * rHalf w₀ b b' + (m - rHalf w₀ b b')) hP_lt (
                by omega),
              Nat.xor_zero] at hhigh
            have hval_eq : (s.mem (scratchBase + accWords + m) ^^^
                s.mem (scratchBase + accWords + (rHalf w₀ b b' + m))) ^^^
                s.mem (hashBase + coeffOff + m) = getLimb (rChunk w₀ b b') newAcc m := by
              rw [hprod_s m (by omega), hprod_s (rHalf w₀ b b' + m) (by omega), hhigh.symm,
                hseed_eq, ← getLimb_xor]
            refine ⟨⟨hlt_seed, hlt_p0, ?_, ⟨hlt_scr,
              hval_eq ▸ hpowc.of_le (le_of_lt (getLimb_lt _ _ _))⟩, trivial⟩,
              show (4 : ℕ) ≤ 5 by decide, rfl, rfl,
              congrArg (Function.update s.mem (scratchBase + m)) hval_eq⟩
            change scratchBase + accWords + (rHalf w₀ b b' + m) < s.frontier
            rw [hfr_eq]; omega
        obtain ⟨hv_step, hc_step, hres_step, hfr_step, hs₁_mem⟩ := hstep_props
        have hmod₁ :
            ∀ x, ¬(scratchBase ≤ x ∧ x < scratchBase + rLimbs w₀ b b') → s₁.mem x = s.mem x :=
          fun x hx => by rw [hs₁_mem, Function.update_of_ne (by omega)]
        refine ⟨⟨w₀, b, b', k, hc_lt, rfl, hcoeff_le, hfr_eq.symm ▸ hfr_h, hfr_eq.symm ▸ hfr_s,
          hm⟩,
          hv_step, hc_step, hfr_step, hmod₁, hres_step.symm, hfr_step.trans hfr_eq,
          seedRep_congr (w := w) hseed_s (fun a h1 h2 => (hmod₁ a (by omega)).symm),
          fun d hd => (hmod₁ _ (by omega)).trans (hprod_s d hd),
          fun i hi => ?_⟩
        rw [hs₁_mem]
        rcases eq_or_ne i m with rfl | hne
        · exact Function.update_self _ _ _
        · rw [Function.update_of_ne (by omega)]; exact hacc_s i (by omega))
      0 s₀ ⟨rfl, rfl, hseed, hprod₀, fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
  exact ⟨hsafe, hv, hcost, hfr', hacc', fun a ha => hmod a (by omega)⟩

/-- Single Horner polynomial step subroutine. -/
@[expose] def hornerStepGenProg : (HashParams × ℕ × ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((hp, hashBase, scratchBase, rVal), j) => do
    Memory.write (scratchBase + accWords) 0
    let prodBase ← pure (scratchBase + accWords)
    let _ ← iterate zeroWordsStepProg prodBase (4 * hpL0 hp) 0
    let tBase ← pure (hashBase + hpSeedWords hp)
    let _ ← iterate outerClmulStepGenProg (hp, tBase, scratchBase, rVal) (2 * hpL0 hp) 0
    let coeffOff ← pure (1 + (2 * hpL0 hp) * (hpK hp - 1 - j))
    let _ ← iterate reduceAddStepGenProg (hp, hashBase, scratchBase, coeffOff) (2 * hpL0 hp) 0
    pure (j + 1)

/-- Precondition for `hornerStepGenProg`. -/
def HornerStepPre (w : ℕ) :
    (HashParams × ℕ × ℕ × ℕ) × ℕ → Memory.State → Prop
  | ((hp, hashBase, scratchBase, rVal), j), s =>
    ∃ w₀ b b' k, ∃ θ : ReducedPolySeed w₀ b b' k, ∃ accVal : ℕ,
      2 * rChunk w₀ b b' < w ∧ hp = mkHashParams w w₀ b b' k ∧
      hashBase + ReducedKWise.space w w₀ b b' k ≤ s.frontier ∧
      scratchBase + scratchWords ≤ s.frontier ∧
      (hashBase + ReducedKWise.space w w₀ b b' k ≤ scratchBase ∨
        scratchBase + scratchWords ≤ hashBase) ∧
      ReducedKWise.TableRep hashBase w w₀ b b' k s.mem ∧
      ReducedKWise.SeedRep hashBase w₀ b b' k θ s.mem ∧
      j < k ∧ Fits w rVal ∧ rVal < 2 ^ (rLimbs w₀ b b' * rChunk w₀ b b') ∧
      accVal < 2 ^ (rLimbs w₀ b b' * rChunk w₀ b b') ∧
      (∀ m < rLimbs w₀ b b', s.mem (scratchBase + m) = getLimb (rChunk w₀ b b') accVal m)

private theorem hornerStep_spec {w w₀ b b' k hashBase scratchBase rVal accVal j : ℕ}
    {θ : ReducedPolySeed w₀ b b' k} {s : Memory.State}
    (hc_lt : 2 * rChunk w₀ b b' < w)
    (hfr_h : hashBase + ReducedKWise.space w w₀ b b' k ≤ s.frontier)
    (hfr_s : scratchBase + scratchWords ≤ s.frontier)
    (hdisj : hashBase + ReducedKWise.space w w₀ b b' k ≤ scratchBase ∨
      scratchBase + scratchWords ≤ hashBase)
    (htab : ReducedKWise.TableRep hashBase w w₀ b b' k s.mem)
    (hseed : ReducedKWise.SeedRep hashBase w₀ b b' k θ s.mem)
    (hj_lt : j < k) (hr_fit : Fits w rVal)
    (hr_lt : rVal < 2 ^ (rLimbs w₀ b b' * rChunk w₀ b b'))
    (hacc_lt : accVal < 2 ^ (rLimbs w₀ b b' * rChunk w₀ b b'))
    (hacc : ∀ m < rLimbs w₀ b b', s.mem (scratchBase + m) = getLimb (rChunk w₀ b b') accVal m) :
    let hp := mkHashParams w w₀ b b' k
    let prodBase := scratchBase + accWords
    let tBase := ReducedKWise.tabBase hashBase w₀ b b' k
    let coeffOff := 1 + rLimbs w₀ b b' * (k - 1 - j)
    let newAcc :=
      reduceTrinomialCode (rStep w₀ b b') (clmul accVal rVal) ^^^ (θ.2 ⟨k - 1 - j, by omega⟩).val
    let s₀ := (Memory.spec 0).clientState s (Memory.write prodBase 0)
    let s₁ := (Memory.spec 0).clientState s₀ (iterate zeroWordsStepProg prodBase
      (2 * rLimbs w₀ b b') 0)
    let s₂ := (Memory.spec 0).clientState s₁
      (iterate outerClmulStepGenProg (hp, tBase, scratchBase, rVal) (rLimbs w₀ b b') 0)
    let stepP := hornerStepGenProg ((hp, hashBase, scratchBase, rVal), j)
    let s' := (Memory.spec 0).clientState s stepP
    iterationSafe zeroWordsStepProg ZeroWordsStepPre w prodBase (2 * rLimbs w₀ b b') 0 s₀ ∧
    iterationSafe outerClmulStepGenProg OuterClmulStepPre w (hp, tBase, scratchBase, rVal)
      (rLimbs w₀ b b') 0 s₁ ∧
    iterationSafe reduceAddStepGenProg ReduceAddStepPre w (hp, hashBase, scratchBase, coeffOff)
      (rLimbs w₀ b b') 0 s₂ ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s stepP) ∧
    memoryCost stepP s ≤
      1 + 2 * rLimbs w₀ b b' + (1 + 5 * rLimbs w₀ b b') * rLimbs w₀ b b' + 5 * rLimbs w₀ b b' ∧
    (Memory.spec 0).clientResult s stepP = j + 1 ∧ s'.frontier = s.frontier ∧
    (∀ m < rLimbs w₀ b b', s'.mem (scratchBase + m) = getLimb (rChunk w₀ b b') newAcc m) ∧
    (∀ a, (a < scratchBase ∨ scratchBase + scratchWords ≤ a) → s'.mem a = s.mem a) := by
  have haccW : accWords = 54 := rfl
  have hscrW : scratchWords = 162 := rfl
  intro hp prodBase tBase coeffOff newAcc s₀ s₁ s₂ stepP s'
  have hL_le : rLimbs w₀ b b' ≤ 54 := reducedLimbCount_le _
  obtain ⟨hsafe_z, hv_z, hcost_z, hfr_z, hz_mem, hout_z⟩ :=
    zeroWordsLoop_spec (w := w) (baseAddr := prodBase) (n := 2 * rLimbs w₀ b b') (s₀ := s₀)
      (by change prodBase + 2 * rLimbs w₀ b b' ≤ s.frontier; dsimp only [prodBase]; omega)
  have hs₁_out : ∀ a, (a < scratchBase ∨ scratchBase + scratchWords ≤ a) → s₁.mem a = s.mem a :=
    fun a ha => (hout_z a (by dsimp only [prodBase]; omega)).trans
      (Function.update_of_ne (by dsimp only [prodBase]; omega) _ _)
  have htab₁ : ReducedKWise.TableRep hashBase w w₀ b b' k s₁.mem :=
    tableRep_congr htab fun a h1 h2 => (hs₁_out a (by omega)).symm
  have hacc₁ :
      ∀ m < rLimbs w₀ b b', s₁.mem (scratchBase + m) = getLimb (rChunk w₀ b b') accVal m :=
    fun m hm => (hout_z _ (Or.inl (by dsimp only [prodBase]; omega))).trans
      ((Function.update_of_ne (by dsimp only [prodBase]; omega) _ _).trans (hacc m hm))
  obtain ⟨hsafe_o, hv_o, hcost_o, hfr_o, hprod₂, hout_o⟩ :=
    outerClmulLoop_spec hc_lt (by rw [hfr_z]; exact hfr_h) (by rw [hfr_z]; exact hfr_s)
      hdisj htab₁ hr_fit hr_lt hacc_lt hacc₁ hz_mem
  have hs₂_out : ∀ a, (a < scratchBase ∨ scratchBase + scratchWords ≤ a) → s₂.mem a = s.mem a :=
    fun a ha => (hout_o a (by omega)).trans (hs₁_out a ha)
  have hseed₂ : ReducedKWise.SeedRep hashBase w₀ b b' k θ s₂.mem :=
    seedRep_congr (w := w) hseed fun a h1 h2 => (hs₂_out a (by omega)).symm
  have hP_lt : clmul accVal rVal < 2 ^ (2 * rLimbs w₀ b b' * rChunk w₀ b b') := by
    rw [Nat.mul_assoc]; exact clmul_lt_two_pow_two_mul hacc_lt hr_lt
  obtain ⟨hsafe_r, hv_r, hcost_r, hfr_r, hacc_r, hout_r⟩ :=
    reduceAddLoop_spec hc_lt (by rw [hfr_o, hfr_z]; exact hfr_h)
      (by rw [hfr_o, hfr_z]; exact hfr_s)
      hdisj hP_lt hseed₂ (coeffIdx := ⟨k - 1 - j, by omega⟩) hprod₂
  have h4L0 : 4 * hpL0 hp = 2 * rLimbs w₀ b b' := by
    dsimp only [hp, hpL0_mk, reducedLimbCount]; ring
  have hstep_eq : stepP = (do
      Memory.write prodBase 0
      let _ ← iterate zeroWordsStepProg prodBase (2 * rLimbs w₀ b b') 0
      let _ ← iterate outerClmulStepGenProg (hp, tBase, scratchBase, rVal) (rLimbs w₀ b b') 0
      let _ ← iterate reduceAddStepGenProg (hp, hashBase, scratchBase, coeffOff) (rLimbs w₀ b b') 0
      pure (j + 1)) := by
    dsimp only [stepP, hornerStepGenProg, prodBase, tBase, ReducedKWise.tabBase, coeffOff]
    rw [h4L0]; rfl
  have hs'_eq : s' = (Memory.spec 0).clientState s₂
      (iterate reduceAddStepGenProg (hp, hashBase, scratchBase, coeffOff) (rLimbs w₀ b b') 0) := by
    dsimp only [s']; rw [hstep_eq, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind]; rfl
  refine ⟨hsafe_z, hsafe_o, hsafe_r, ?_, ?_, ?_, hs'_eq ▸ (hfr_r.trans (hfr_o.trans hfr_z)),
    hs'_eq ▸ hacc_r, fun a ha => hs'_eq ▸ (hout_r a (by omega)).trans (hs₂_out a ha)⟩
  · rw [hstep_eq, validHistory_bind', validHistory_bind', validHistory_bind', validHistory_bind']
    exact ⟨⟨⟨by dsimp only [prodBase]; omega, Nat.two_pow_pos w⟩, trivial⟩, hv_z, hv_o, hv_r,
      trivial⟩
  · rw [hstep_eq, memoryCost_bind', memoryCost_bind', memoryCost_bind', memoryCost_bind',
      memoryCost_pure, Nat.add_zero]
    change 1 + (memoryCost (iterate zeroWordsStepProg prodBase (2 * rLimbs w₀ b b') 0) s₀ +
      (memoryCost (iterate outerClmulStepGenProg (hp, tBase, scratchBase, rVal)
        (rLimbs w₀ b b') 0) s₁ +
        memoryCost (iterate reduceAddStepGenProg (hp, hashBase, scratchBase, coeffOff)
          (rLimbs w₀ b b') 0) s₂)) ≤ _
    exact Nat.add_le_add_left (Nat.add_le_add hcost_z (
      Nat.add_le_add hcost_o hcost_r)) 1 |>.trans_eq
      (by ring)
  · rw [hstep_eq, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind]; rfl

theorem realizesBounded_hornerStepGen :
    RealizesBounded .exact hornerStepGenProg
      (WordEncoding.encode (α := (HashParams × ℕ × ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ)) HornerStepPre (fun _ _ => 0) := by
  have hz := realizesBounded_zeroWordsStep
  have ho := realizesBounded_outerClmulStepGen
  have hr := realizesBounded_reduceAddStepGen
  realize
  all_goals (
    rcases d with ⟨⟨hp, hashBase, scratchBase, rVal⟩, j⟩
    obtain ⟨w₀, b, b', k, θ, accVal, hc_lt, rfl, hfr_h, hfr_s, hdisj, htab, hseed,
      hj_lt, hr_fit, hr_lt, hacc_lt, hacc⟩ := h
    try (dsimp only [hpL0_mk, hpSeedWords_mk, hpK_mk] at *)
    try dsimp only [accWords, prodWords, scratchWords] at *
    have hL0_le : rHalf w₀ b b' ≤ 27 := reducedHalfLimbs_le _
    have hL_le : rLimbs w₀ b b' ≤ 54 := reducedLimbCount_le _
    have h4L0 : 4 * rHalf w₀ b b' = 2 * rLimbs w₀ b b' := by
      dsimp only [reducedLimbCount]; ring
    have h2L0 : 2 * rHalf w₀ b b' = rLimbs w₀ b b' := rfl
    have hmul_lt : rLimbs w₀ b b' * (k - 1 - j) < k * rLimbs w₀ b b' := by
      rw [mul_comm]; exact Nat.mul_lt_mul_of_pos_right (by omega) (reducedLimbCount_pos _)
    have hk_le_s : k ≤ k * rLimbs w₀ b b' := Nat.le_mul_of_pos_right k (reducedLimbCount_pos _)
    obtain ⟨hsafe_z, hsafe_o, hsafe_r, _⟩ :=
      hornerStep_spec hc_lt hfr_h hfr_s hdisj htab hseed hj_lt hr_fit hr_lt hacc_lt hacc)
  all_goals (try
    try rw [h2L0]
    unfold ReducedKWise.space ReducedKWise.seedWords at hfr_h; omega)
  all_goals try exact hmem.1.of_le (by
    try rw [h2L0]
    unfold ReducedKWise.space at hfr_h; try unfold ReducedKWise.seedWords at *; omega)
  all_goals first
    | (rw [h4L0]; exact iterationSafe_imp hsafe_z (fun _ => rfl) (fun _ _ hs => hs))
    | (rw [h4L0, h2L0]; exact iterationSafe_imp hsafe_o (fun _ => rfl) (fun _ _ hs => hs))
    | (rw [h4L0, h2L0]; exact iterationSafe_imp hsafe_r (fun _ => rfl) (fun _ _ hs => hs))

theorem hornerLoop_spec {w w₀ b b' k hashBase scratchBase : ℕ}
    {θ : ReducedPolySeed w₀ b b' k} {r : Fin (2 ^ min w₀ (3 * b))} {s₁ : Memory.State}
    (hw₀ : w₀ ≤ w) (hc_lt : 2 * rChunk w₀ b b' < w)
    (hfr_h : hashBase + ReducedKWise.space w w₀ b b' k ≤ s₁.frontier)
    (hfr_s : scratchBase + scratchWords ≤ s₁.frontier)
    (hdisj : hashBase + ReducedKWise.space w w₀ b b' k ≤ scratchBase ∨
      scratchBase + scratchWords ≤ hashBase)
    (htab₁ : ReducedKWise.TableRep hashBase w w₀ b b' k s₁.mem)
    (hseed₁ : ReducedKWise.SeedRep hashBase w₀ b b' k θ s₁.mem)
    (hz_mem : ∀ m < rLimbs w₀ b b', s₁.mem (scratchBase + m) = 0) :
    let hp := mkHashParams w w₀ b b' k
    let prog := iterate hornerStepGenProg (hp, hashBase, scratchBase, r.val) k 0
    let s₂ := (Memory.spec 0).clientState s₁ prog
    iterationSafe hornerStepGenProg HornerStepPre w (hp, hashBase, scratchBase, r.val) k 0 s₁ ∧
    (Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁ prog) ∧
    memoryCost prog s₁ ≤
      (1 + 2 * rLimbs w₀ b b' + (1 + 5 * rLimbs w₀ b b') * rLimbs w₀ b b' +
        5 * rLimbs w₀ b b') * k ∧
    s₂.frontier = s₁.frontier ∧
    (∀ m < rLimbs w₀ b b', s₂.mem (scratchBase + m) =
      getLimb (rChunk w₀ b b')
        (trinomialPolyEval (rStep w₀ b b') k (2 ^ min w₀ (3 * b)) θ.2 r).val m) ∧
    (∀ a, (a < scratchBase ∨ scratchBase + scratchWords ≤ a) → s₂.mem a = s₁.mem a) := by
  have haccW : accWords = 54 := rfl
  have hscrW : scratchWords = 162 := rfl
  intro hp prog s₂
  let c_field : Fin k → TrinomialField (rStep w₀ b b') :=
    fun j => (TrinomialField.equivFin (rStep w₀ b b')).symm (θ.2 j)
  let x_field : TrinomialField (rStep w₀ b b') :=
    AdjoinRoot.mk (trinomial (rStep w₀ b b')) (polyOfCode r.val)
  have hzero_val :
      (TrinomialField.equivFin (rStep w₀ b b') (0 : TrinomialField (rStep w₀ b b'))).val = 0 := by
    rw [show (0 : TrinomialField (rStep w₀ b b')) =
      AdjoinRoot.mk (trinomial (rStep w₀ b b')) (polyOfCode 0) by simp]
    exact TrinomialField.val_equivFin_mk_polyOfCode _ (by positivity)
  have hLc : rLimbs w₀ b b' * rChunk w₀ b b' = 2 * 3 ^ rStep w₀ b b' :=
    reducedLimbCount_mul_chunkBits _
  have hr_fit : Fits w r.val :=
    r.isLt.trans_le (Nat.pow_le_pow_right two_pos ((Nat.min_le_left _ _).trans hw₀))
  have hr_deg : r.val < 2 ^ (2 * 3 ^ rStep w₀ b b') :=
    r.isLt.trans_le (two_pow_min_le_two_pow_reducedTrinomialDeg w₀ b b')
  have hr_lt : r.val < 2 ^ (rLimbs w₀ b b' * rChunk w₀ b b') := by rw [hLc]; exact hr_deg
  have hx_val : (TrinomialField.equivFin (rStep w₀ b b') x_field).val = r.val :=
    TrinomialField.val_equivFin_mk_polyOfCode _ hr_deg
  obtain ⟨hsafe, hv, hcost, hfr_h2, hmod, _, _, _, _, hacc_h⟩ :=
    iterate_spec hornerStepGenProg HornerStepPre w (hp, hashBase, scratchBase, r.val)
      (1 + 2 * rLimbs w₀ b b' + (1 + 5 * rLimbs w₀ b b') * rLimbs w₀ b b' + 5 * rLimbs w₀ b b') k
      (fun j st s => j = st ∧ s.frontier = s₁.frontier ∧
        ReducedKWise.TableRep hashBase w w₀ b b' k s.mem ∧
        ReducedKWise.SeedRep hashBase w₀ b b' k θ s.mem ∧
        ∀ m < rLimbs w₀ b b', s.mem (scratchBase + m) =
          getLimb (rChunk w₀ b b')
            (TrinomialField.equivFin (rStep w₀ b b')
              (hornerPrefix (rStep w₀ b b') k c_field x_field j)).val m)
      (fun x => scratchBase ≤ x ∧ x < scratchBase + scratchWords)
      (fun j hj st s ⟨hst, hfr_cur, htab_cur, hseed_cur, hacc_cur⟩ => by
        subst hst
        let acc := hornerPrefix (rStep w₀ b b') k c_field x_field j
        let accVal := (TrinomialField.equivFin (rStep w₀ b b') acc).val
        have hacc_lt : accVal < 2 ^ (rLimbs w₀ b b' * rChunk w₀ b b') := by
          rw [hLc]; exact (TrinomialField.equivFin (rStep w₀ b b') acc).isLt
        obtain ⟨_, _, _, hv_st, hc_st, hres_st, hfr_st, hacc_st, hout_st⟩ :=
          hornerStep_spec hc_lt (hfr_cur.symm ▸ hfr_h) (hfr_cur.symm ▸ hfr_s) hdisj
            htab_cur hseed_cur hj hr_fit hr_lt hacc_lt hacc_cur
        have hmod_st : ∀ x, ¬(scratchBase ≤ x ∧ x < scratchBase + scratchWords) →
            ((Memory.spec 0).clientState s
              (hornerStepGenProg ((hp, hashBase, scratchBase, r.val), j))).mem x = s.mem x :=
          fun x hx => hout_st x (by omega)
        refine ⟨⟨w₀, b, b', k, θ, accVal, hc_lt, rfl, hfr_cur.symm ▸ hfr_h, hfr_cur.symm ▸ hfr_s,
          hdisj, htab_cur, hseed_cur, hj, hr_fit, hr_lt, hacc_lt, hacc_cur⟩,
          hv_st, hc_st, hfr_st, hmod_st, hres_st.symm, hfr_st.trans hfr_cur,
          tableRep_congr htab_cur (fun a h1 h2 => (hmod_st a (by omega)).symm),
          seedRep_congr (w := w) hseed_cur (fun a h1 h2 => (hmod_st a (by omega)).symm),
          fun m hm => ?_⟩
        rw [hacc_st m hm]; congr 1
        have hmul_val : reduceTrinomialCode (rStep w₀ b b') (clmul accVal r.val) =
            (TrinomialField.equivFin (rStep w₀ b b') (acc * x_field)).val := by
          rw [TrinomialField.val_equivFin_mul, hx_val]
        have hseed_val : (θ.2 ⟨k - 1 - j, by omega⟩).val =
            (TrinomialField.equivFin (rStep w₀ b b') (c_field ⟨k - 1 - j, by omega⟩)).val :=
          (congrArg Fin.val ((TrinomialField.equivFin (rStep w₀ b b')).apply_symm_apply _)).symm
        rw [hmul_val, hseed_val, ← TrinomialField.val_equivFin_add]
        dsimp only [hornerPrefix]; rw [dite_eq_left hj])
      0 s₁ ⟨rfl, rfl, htab₁, hseed₁, fun m hm => by
        rw [hz_mem m hm]; dsimp only [hornerPrefix]; rw [hzero_val]; simp [getLimb]⟩
  refine ⟨hsafe, hv, hcost, hfr_h2, fun m hm => ?_, fun a ha => hmod a (by omega)⟩
  rw [hacc_h m hm, hornerPrefix_self_eq_polynomialHash]; rfl

end Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise

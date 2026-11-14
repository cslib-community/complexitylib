/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Resizable.Randomized
public import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
public import CslibFrontier.Computability.WordRAM.Realization.GlueVector
public import CslibFrontier.Computability.WordRAM.Realization.LoopCongr
public import CslibFrontier.DataStructure.HashFamily.WordRAM.ReducedKWise

/-!
# Runtime `ReducedKWise` Parameters and Four-Russians Table Initialization

Defines the 162-word limb scratch layout (`accWords`, `prodWords`, `scratchWords`), the 19-word
runtime parameter vector (`HashParams`, `mkHashParams`), loop-verification helpers on
`Memory.Prog`, and the parameter-free (`¬ReadsWidth`) runtime Four-Russians carryless
multiplication table builder (`initTableGenProg`) for the two-stage universe-reduced $k$-wise
independent polynomial hash family of [BenderFarachColtonKuszmaulKuszmaul2024].

## Main definitions

* `Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise.accWords`, `prodWords`,
  `scratchWords`: 162-word limb scratch layout (`54` accumulator words + `108` product words).
* `Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise.HashParams`, `mkHashParams`:
  19-word runtime parameter vector encoding shifts, masks, and loop bounds.
* `Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise.initTableGenProg`,
  `InitTableGenPre`: runtime Four-Russians carryless multiplication table builder in `Memory.Prog`.
* `Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise.reduceKeyGenProg`,
  `ReduceKeyGenPre`, `zeroWordsStepProg`, `ZeroWordsStepPre`: Stage-1 key reduction and bounded
  word-zeroing loop body in `Memory.Prog`.

## Main results

* `fits_mkHashParams`: every entry of `mkHashParams` fits in a `w`-bit word.
* `initTableGenProg_spec`, `realizesBounded_initTableGen`: functional correctness (`O(2 ^ (2 * c))`
  memory operations establishing `ReducedKWise.TableRep`) and `RealizesBounded .exact` certificate.
* `realizesBounded_reduceKeyGen`, `realizesBounded_zeroWordsStep`, `zeroWordsLoop_spec`:
  certificates and specification for Stage-1 key reduction and bounded word-zeroing.

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

/-! ## Section 1: 162-word scratch layout, runtime `HashParams`, and loop helpers -/

/-- Number of accumulator limb words (`54 ≥ reducedLimbCount t`) at `[scratchBase, +54)`. -/
@[expose] def accWords : ℕ := 54
/-- Number of product limb words (`108 ≥ 2 * reducedLimbCount t`) at `[scratchBase + 54, +108)`. -/
@[expose] def prodWords : ℕ := 108
/-- Total scratch footprint (`54 + 108 = 162` words) for runtime polynomial hash evaluation. -/
@[expose] def scratchWords : ℕ := 162

@[simp] theorem accWords_eq : accWords = 54 := rfl
@[simp] theorem prodWords_eq : prodWords = 108 := rfl
@[simp] theorem scratchWords_eq : scratchWords = 162 := rfl

local notation "rStep" => reducedTrinomialStep
local notation "rChunk" w₀:arg b:arg b':arg => reducedChunkBits (reducedTrinomialStep w₀ b b')
local notation "rHalf" w₀:arg b:arg b':arg => reducedHalfLimbs (reducedTrinomialStep w₀ b b')
local notation "rLimbs" w₀:arg b:arg b':arg => reducedLimbCount (reducedTrinomialStep w₀ b b')
local notation "rPack" w:arg w₀:arg b:arg b':arg =>
  reducedPackShift (reducedTrinomialStep w₀ b b') w

/-- 19-word runtime parameter vector passed to `initTableGenProg` and `evalHashGenProg`. -/
@[expose] def HashParams : Type := Fin 19 → ℕ

instance : WordEncoding HashParams := ⟨19, Function.Embedding.refl (Fin 19 → ℕ)⟩

/-- Populate the 19-word `HashParams` vector for `(w, w₀, b, b', k)`. -/
@[expose] def mkHashParams (w w₀ b b' k : ℕ) : HashParams :=
  let c := rChunk w₀ b b'; let L₀ := rHalf w₀ b b'
  let L := rLimbs w₀ b b'; let p := rPack w w₀ b b'
  let m := w₀ - 1; let h := m / 2
  ![ReducedKWise.space w w₀ b b' k, ReducedKWise.seedWords w₀ b b' k, k * L,
    2 ^ m - 1, h, 2 ^ h - 1, 2 ^ (m - h) - 1, 2 ^ (m - 2 * h) - 1,
    w₀ - min w₀ (3 * b), c, 2 ^ c - 1, 2 * c, 2 ^ (2 * c),
    2 ^ (2 * c) - 1, p, 2 ^ p - 1, L₀, k, b']

/-- Total word space allocated for hash parameters and polynomial state. -/
abbrev hpSpace (hp : HashParams) : ℕ := hp 0
/-- Number of seed words for the hash family. -/
abbrev hpSeedWords (hp : HashParams) : ℕ := hp 1
/-- Number of bottom-limb words. -/
abbrev hpBotWords (hp : HashParams) : ℕ := hp 2
/-- Bitmask for limb size $m$. -/
abbrev hpMaskM (hp : HashParams) : ℕ := hp 3
/-- Half-limb width $h$. -/
abbrev hpHalfM (hp : HashParams) : ℕ := hp 4
/-- Bitmask for half-limb width $h$. -/
abbrev hpMaskH (hp : HashParams) : ℕ := hp 5
/-- Bitmask for $m - h$ bits. -/
abbrev hpMaskMH (hp : HashParams) : ℕ := hp 6
/-- Bitmask for $m - 2h$ bits. -/
abbrev hpMaskM2H (hp : HashParams) : ℕ := hp 7
/-- Shift amount for remainder reduction. -/
abbrev hpRemShift (hp : HashParams) : ℕ := hp 8
/-- Chunk width $c$. -/
abbrev hpC (hp : HashParams) : ℕ := hp 9
/-- Bitmask for chunk width $c$. -/
abbrev hpMaskC (hp : HashParams) : ℕ := hp 10
/-- Twice the chunk width, $2c$. -/
abbrev hpTwoC (hp : HashParams) : ℕ := hp 11
/-- Power of two $2^{2c}$. -/
abbrev hpPow2C (hp : HashParams) : ℕ := hp 12
/-- Bitmask for $2c$ bits. -/
abbrev hpMask2C (hp : HashParams) : ℕ := hp 13
/-- Packing shift parameter $p$. -/
abbrev hpP (hp : HashParams) : ℕ := hp 14
/-- Bitmask for $p$ bits. -/
abbrev hpMaskP (hp : HashParams) : ℕ := hp 15
/-- Number of initial limb words $L_0$. -/
abbrev hpL0 (hp : HashParams) : ℕ := hp 16
/-- Polynomial degree parameter $k$. -/
abbrev hpK (hp : HashParams) : ℕ := hp 17
/-- Target hash output bit-length $b'$. -/
abbrev hpB' (hp : HashParams) : ℕ := hp 18

@[simp] theorem hpSpace_mk (w w₀ b b' k : ℕ) :
    hpSpace (mkHashParams w w₀ b b' k) = ReducedKWise.space w w₀ b b' k := rfl
@[simp] theorem hpSeedWords_mk (w w₀ b b' k : ℕ) :
    hpSeedWords (mkHashParams w w₀ b b' k) = ReducedKWise.seedWords w₀ b b' k := rfl
@[simp] theorem hpBotWords_mk (w w₀ b b' k : ℕ) :
    hpBotWords (mkHashParams w w₀ b b' k) = k * rLimbs w₀ b b' := rfl
@[simp] theorem hpMaskM_mk (w w₀ b b' k : ℕ) :
    hpMaskM (mkHashParams w w₀ b b' k) = 2 ^ (w₀ - 1) - 1 := rfl
@[simp] theorem hpHalfM_mk (w w₀ b b' k : ℕ) :
    hpHalfM (mkHashParams w w₀ b b' k) = (w₀ - 1) / 2 := rfl
@[simp] theorem hpMaskH_mk (w w₀ b b' k : ℕ) :
    hpMaskH (mkHashParams w w₀ b b' k) = 2 ^ ((w₀ - 1) / 2) - 1 := rfl
@[simp] theorem hpMaskMH_mk (w w₀ b b' k : ℕ) :
    hpMaskMH (mkHashParams w w₀ b b' k) = 2 ^ ((w₀ - 1) - (w₀ - 1) / 2) - 1 := rfl
@[simp] theorem hpMaskM2H_mk (w w₀ b b' k : ℕ) :
    hpMaskM2H (mkHashParams w w₀ b b' k) = 2 ^ ((w₀ - 1) - 2 * ((w₀ - 1) / 2)) - 1 := rfl
@[simp] theorem hpRemShift_mk (w w₀ b b' k : ℕ) :
    hpRemShift (mkHashParams w w₀ b b' k) = w₀ - min w₀ (3 * b) := rfl
@[simp] theorem hpC_mk (w w₀ b b' k : ℕ) : hpC (mkHashParams w w₀ b b' k) = rChunk w₀ b b' := rfl
@[simp] theorem hpMaskC_mk (w w₀ b b' k : ℕ) :
    hpMaskC (mkHashParams w w₀ b b' k) = 2 ^ rChunk w₀ b b' - 1 := rfl
@[simp] theorem hpTwoC_mk (w w₀ b b' k : ℕ) :
    hpTwoC (mkHashParams w w₀ b b' k) = 2 * rChunk w₀ b b' := rfl
@[simp] theorem hpPow2C_mk (w w₀ b b' k : ℕ) :
    hpPow2C (mkHashParams w w₀ b b' k) = 2 ^ (2 * rChunk w₀ b b') := rfl
@[simp] theorem hpMask2C_mk (w w₀ b b' k : ℕ) :
    hpMask2C (mkHashParams w w₀ b b' k) = 2 ^ (2 * rChunk w₀ b b') - 1 := rfl
@[simp] theorem hpP_mk (w w₀ b b' k : ℕ) : hpP (mkHashParams w w₀ b b' k) = rPack w w₀ b b' := rfl
@[simp] theorem hpMaskP_mk (w w₀ b b' k : ℕ) :
    hpMaskP (mkHashParams w w₀ b b' k) = 2 ^ rPack w w₀ b b' - 1 := rfl
@[simp] theorem hpL0_mk (w w₀ b b' k : ℕ) : hpL0 (mkHashParams w w₀ b b' k) = rHalf w₀ b b' := rfl
@[simp] theorem hpK_mk (w w₀ b b' k : ℕ) : hpK (mkHashParams w w₀ b b' k) = k := rfl
@[simp] theorem hpB'_mk (w w₀ b b' k : ℕ) : hpB' (mkHashParams w w₀ b b' k) = b' := rfl

/-- Every word of `mkHashParams w w₀ b b' k` fits in a `w`-bit register. -/
theorem fits_mkHashParams {w w₀ b b' k hashBase scratchBase : ℕ}
    (_hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (hb' : b' ≤ w) (hc_lt : 2 * rChunk w₀ b b' < w)
    (hfit_hash : Fits w (hashBase + ReducedKWise.space w w₀ b b' k))
    (hfit_scr : Fits w (scratchBase + scratchWords)) (i : Fin 19) :
    Fits w (mkHashParams w w₀ b b' k i) := by
  have hw_lt : Fits w w := Nat.lt_two_pow_self
  have h162 : Fits w 162 := hfit_scr.of_le (by dsimp only [scratchWords]; omega)
  have hspace : Fits w (ReducedKWise.space w w₀ b b' k) := hfit_hash.of_le (by omega)
  have hpow2c : Fits w (2 ^ (2 * rChunk w₀ b b')) := Nat.pow_lt_pow_right one_lt_two hc_lt
  have hpowc_le : 2 ^ rChunk w₀ b b' ≤ 2 ^ (2 * rChunk w₀ b b') :=
    Nat.pow_le_pow_right two_pos (by omega)
  have hp_le : rPack w w₀ b b' ≤ 2 * rChunk w₀ b b' := reducedPackShift_le _ w
  have hpowm : Fits w (2 ^ (w₀ - 1)) := Nat.pow_lt_pow_right one_lt_two (by omega)
  have hL0_le : rHalf w₀ b b' ≤ 27 := reducedHalfLimbs_le _
  have hseed_ge : 1 + k * rLimbs w₀ b b' ≤ ReducedKWise.space w w₀ b b' k :=
    Nat.le_add_right _ (ReducedKWise.tableWords w w₀ b b')
  have hk_le : k ≤ k * rLimbs w₀ b b' := Nat.le_mul_of_pos_right k (reducedLimbCount_pos _)
  fin_cases i
  · exact hspace
  · exact hspace.of_le (u := ReducedKWise.seedWords w₀ b b' k) hseed_ge
  · exact hspace.of_le (u := k * rLimbs w₀ b b') (by omega)
  · exact hpowm.of_le (u := 2 ^ (w₀ - 1) - 1) (Nat.sub_le _ _)
  · exact hw_lt.of_le (u := (w₀ - 1) / 2) (by omega)
  · exact hpowm.of_le (u := 2 ^ ((w₀ - 1) / 2) - 1)
      ((Nat.sub_le _ _).trans (Nat.pow_le_pow_right two_pos (Nat.div_le_self _ 2)))
  · exact hpowm.of_le (u := 2 ^ ((w₀ - 1) - (w₀ - 1) / 2) - 1)
      ((Nat.sub_le _ _).trans (Nat.pow_le_pow_right two_pos (Nat.sub_le _ _)))
  · exact hpowm.of_le (u := 2 ^ ((w₀ - 1) - 2 * ((w₀ - 1) / 2)) - 1)
      ((Nat.sub_le _ _).trans (Nat.pow_le_pow_right two_pos (Nat.sub_le _ _)))
  · exact hw_lt.of_le (u := w₀ - min w₀ (3 * b)) (by omega)
  · exact hw_lt.of_le (u := rChunk w₀ b b') (by omega)
  · exact hpow2c.of_le (u := 2 ^ rChunk w₀ b b' - 1) ((Nat.sub_le _ _).trans hpowc_le)
  · exact hw_lt.of_le (u := 2 * rChunk w₀ b b') (by omega)
  · exact hpow2c
  · exact hpow2c.of_le (u := 2 ^ (2 * rChunk w₀ b b') - 1) (Nat.sub_le _ _)
  · exact hw_lt.of_le (u := rPack w w₀ b b') (by omega)
  · exact hpow2c.of_le (u := 2 ^ rPack w w₀ b b' - 1)
      ((Nat.sub_le _ _).trans (Nat.pow_le_pow_right two_pos hp_le))
  · exact h162.of_le (u := rHalf w₀ b b') (by omega)
  · exact hspace.of_le (u := k) (by omega)
  · exact hw_lt.of_le (u := b') hb'

/-! ## Section 2: Runtime `Memory.Prog` table construction (`initTableGenProg`) -/

private theorem clmulTab_index_props {c idx : ℕ} (hidx : idx < 2 ^ (2 * c)) :
    let u := idx >>> c; let v := idx &&& (2 ^ c - 1); let prevIdx := (u <<< c) + (v >>> 1)
    u < 2 ^ c ∧ v < 2 ^ c ∧ prevIdx < 2 ^ (2 * c) ∧ prevIdx ≤ idx ∧
    (v ≠ 0 → prevIdx < idx) ∧ (v = 0 → prevIdx = idx) ∧
    prevIdx >>> c = u ∧ (prevIdx &&& (2 ^ c - 1)) = v >>> 1 := by
  intro u v prevIdx
  have hu_lt : u < 2 ^ c := by
    dsimp only [u]; rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rwa [← pow_add, ← two_mul])
  have hv_lt : v < 2 ^ c := and_two_pow_sub_one_lt idx c
  have hv_shr_lt : v >>> 1 < 2 ^ c := lt_of_le_of_lt (Nat.shiftRight_le v 1) hv_lt
  have hdecomp : (u <<< c) + v = idx := by
    dsimp only [u, v]
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod, mul_comm]
    exact Nat.div_add_mod idx (2 ^ c)
  have hprev_le : prevIdx ≤ idx := by have := Nat.shiftRight_le v 1; dsimp only [prevIdx]; omega
  refine ⟨hu_lt, hv_lt, lt_of_le_of_lt hprev_le hidx, hprev_le, fun hv0 => ?_, fun hv0 => ?_,
    ?_, ?_⟩
  · have : v >>> 1 < v := by rw [Nat.shiftRight_eq_div_pow, pow_one]; omega
    dsimp only [prevIdx]; omega
  · have : v >>> 1 = 0 := by rw [hv0]; rfl
    dsimp only [prevIdx]; omega
  · dsimp only [prevIdx]
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, mul_comm u (2 ^ c),
      Nat.mul_add_div (Nat.two_pow_pos c), Nat.div_eq_of_lt hv_shr_lt, Nat.add_zero]
  · dsimp only [prevIdx]
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hv_shr_lt]

private def initTableClearProg : (HashParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((hp, hashBase), idx) => do
    let tBase := hashBase + hpSeedWords hp
    let wIdx := idx >>> hpP hp
    let sh := (idx &&& hpMaskP hp) * hpTwoC hp
    let curWord ← Memory.read (tBase + wIdx)
    let cleared := curWord &&& ((1 <<< sh) - 1)
    Memory.write (tBase + wIdx) cleared
    pure cleared

private def initTableWriteProg : ((HashParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((hp, hashBase), idx), cleared) => do
    let tBase := hashBase + hpSeedWords hp
    let wIdx := idx >>> hpP hp
    let sh := (idx &&& hpMaskP hp) * hpTwoC hp
    let u := idx >>> hpC hp; let v := idx &&& hpMaskC hp
    let prevIdx := (u <<< hpC hp) + (v >>> 1)
    let prevWord ← Memory.read (tBase + (prevIdx >>> hpP hp))
    let prevEntry := (prevWord >>> ((prevIdx &&& hpMaskP hp) * hpTwoC hp)) &&& hpMask2C hp
    let newEntry := ((v &&& 1) * u) ^^^ (prevEntry <<< 1)
    Memory.write (tBase + wIdx) (cleared ^^^ (newEntry <<< sh))
    pure (idx + 1)

private def initTableStepGenProg : (HashParams × ℕ) × ℕ → Memory.Prog ℕ
  | (env, idx) => do
    let cleared ← initTableClearProg (env, idx)
    initTableWriteProg ((env, idx), cleared)

/-- Full runtime Four-Russians table initialization `Memory.Prog`. -/
def initTableGenProg : HashParams × ℕ → Memory.Prog ℕ
  | (hp, hashBase) => iterate initTableStepGenProg (hp, hashBase) (hpPow2C hp) 0

private def InitTableStepGenPre (w : ℕ) : (HashParams × ℕ) × ℕ → Memory.State → Prop
  | ((hp, hashBase), idx), s => ∃ w₀ b b' k,
    2 * rChunk w₀ b b' < w ∧ hp = mkHashParams w w₀ b b' k ∧ idx < 2 ^ (2 * rChunk w₀ b b') ∧
    hashBase + ReducedKWise.space w w₀ b b' k ≤ s.frontier ∧
    (∀ i < idx, getLimb (2 * rChunk w₀ b b')
      (s.mem (ReducedKWise.tabBase hashBase w₀ b b' k + (i >>> rPack w w₀ b b')))
      (i &&& (2 ^ rPack w w₀ b b' - 1)) =
      clmul (i >>> rChunk w₀ b b') (i &&& (2 ^ rChunk w₀ b b' - 1)))

/-- Precondition for `initTableGenProg`. -/
def InitTableGenPre (w : ℕ) : HashParams × ℕ → Memory.State → Prop
  | (hp, hashBase), s => ∃ w₀ b b' k,
    2 * rChunk w₀ b b' < w ∧ hp = mkHashParams w w₀ b b' k ∧
    hashBase + ReducedKWise.space w w₀ b b' k ≤ s.frontier ∧
    Fits w (hashBase + ReducedKWise.space w w₀ b b' k)

private theorem prevWord_limb_eq {w w₀ b b' k hashBase idx : ℕ} {mem : ℕ → ℕ}
    (hidx : idx < 2 ^ (2 * rChunk w₀ b b'))
    (hentry : ∀ i < idx, getLimb (2 * rChunk w₀ b b')
      (mem (ReducedKWise.tabBase hashBase w₀ b b' k + (i >>> rPack w w₀ b b')))
      (i &&& (2 ^ rPack w w₀ b b' - 1)) =
      clmul (i >>> rChunk w₀ b b') (i &&& (2 ^ rChunk w₀ b b' - 1))) :
    let c := rChunk w₀ b b'; let p := rPack w w₀ b b'
    let tBase := ReducedKWise.tabBase hashBase w₀ b b' k
    let sh := (idx &&& (2 ^ p - 1)) * (2 * c)
    let prevIdx := ((idx >>> c) <<< c) + ((idx &&& (2 ^ c - 1)) >>> 1)
    let masked := mem (tBase + (idx >>> p)) &&& ((1 <<< sh) - 1)
    let prevWord := Function.update mem (tBase + (idx >>> p)) masked (tBase + (prevIdx >>> p))
    (prevWord >>> ((prevIdx &&& (2 ^ p - 1)) * (2 * c))) &&& (2 ^ (2 * c) - 1) =
      clmul (idx >>> c) ((idx &&& (2 ^ c - 1)) >>> 1) := by
  intro c p tBase sh prevIdx masked prevWord
  obtain ⟨_, _, _, _, hprev_lt, hprev_zero, hprev_u, hprev_v⟩ := clmulTab_index_props hidx
  change getLimb (2 * c) prevWord (prevIdx &&& (2 ^ p - 1)) = _
  have hmask_eq : (1 <<< sh) - 1 = 2 ^ ((idx &&& (2 ^ p - 1)) * (2 * c)) - 1 := by
    rw [Nat.shiftLeft_eq, one_mul]
  by_cases hv0 : idx &&& (2 ^ c - 1) = 0
  · dsimp only [prevWord, masked]
    rw [show prevIdx = idx from hprev_zero hv0, Function.update_self,
      show (idx &&& (2 ^ c - 1)) >>> 1 = 0 by rw [hv0]; rfl, clmul_zero_right, hmask_eq]
    exact getLimb_and_self (2 * c) _ _
  · have hplt : prevIdx < idx := hprev_lt hv0
    dsimp only [prevWord, masked]
    rcases eq_or_ne (prevIdx >>> p) (idx >>> p) with hw_eq | hw_ne
    · rw [hw_eq, Function.update_self, hmask_eq,
        getLimb_and_low (and_lt_of_lt_of_shiftRight_eq hplt hw_eq), ← hw_eq,
        hentry prevIdx hplt, hprev_u, hprev_v]
    · rw [Function.update_of_ne (by omega), hentry prevIdx hplt, hprev_u, hprev_v]

private def InitTableWritePre (w : ℕ) : ((HashParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((hp, hashBase), idx), cleared), s => ∃ w₀ b b' k,
    2 * rChunk w₀ b b' < w ∧ hp = mkHashParams w w₀ b b' k ∧ idx < 2 ^ (2 * rChunk w₀ b b') ∧
    hashBase + ReducedKWise.space w w₀ b b' k ≤ s.frontier ∧
    cleared < 2 ^ ((idx &&& (2 ^ rPack w w₀ b b' - 1)) * (2 * rChunk w₀ b b')) ∧
    (s.mem (ReducedKWise.tabBase hashBase w₀ b b' k +
        ((((idx >>> rChunk w₀ b b' <<< rChunk w₀ b b') +
          ((idx &&& (2 ^ rChunk w₀ b b' - 1)) >>> 1)) >>> rPack w w₀ b b'))) >>>
      ((((idx >>> rChunk w₀ b b' <<< rChunk w₀ b b') +
        ((idx &&& (2 ^ rChunk w₀ b b' - 1)) >>> 1)) &&& (2 ^ rPack w w₀ b b' - 1)) *
        (2 * rChunk w₀ b b'))) &&& (2 ^ (2 * rChunk w₀ b b') - 1) =
      clmul (idx >>> rChunk w₀ b b') ((idx &&& (2 ^ rChunk w₀ b b' - 1)) >>> 1)

private theorem realizesBounded_initTableClear :
    RealizesBounded .exact initTableClearProg
      (WordEncoding.encode (α := (HashParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      InitTableStepGenPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨hp, hashBase⟩, idx⟩
    obtain ⟨w₀, b, b', k, hc_lt, rfl, hidx, hfr, _⟩ := h
    try (dsimp only [hpSeedWords_mk, hpP_mk, hpMaskP_mk, hpTwoC_mk] at *)
    have hc_pos : 0 < rChunk w₀ b b' := reducedChunkBits_pos _
    have hpack_le : 2 ^ rPack w w₀ b b' * (2 * rChunk w₀ b b') ≤ w :=
      two_pow_reducedPackShift_mul_le (le_of_lt hc_lt)
    have hwIdx_lt := shiftRight_lt_reducedTableWords (w := w) hidx
    have hsub_lt := and_two_pow_sub_one_lt idx (rPack w w₀ b b')
    have hsh_lt : (idx &&& (2 ^ rPack w w₀ b b' - 1)) * (2 * rChunk w₀ b b') < w :=
      (Nat.mul_lt_mul_of_pos_right hsub_lt (by omega)).trans_le hpack_le
    have hfr_end :
        hashBase + ReducedKWise.seedWords w₀ b b' k + reducedTableWords (rStep w₀ b b') w ≤
          s.frontier := by
      simpa only [ReducedKWise.space, ReducedKWise.tableWords, Nat.add_assoc] using hfr
    have hge1 := Nat.zero_le (idx >>> rPack w w₀ b b'))
  all_goals try (rw [Nat.shiftLeft_eq, one_mul]; exact Nat.one_le_two_pow)
  all_goals try (rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right one_lt_two hsh_lt)
  all_goals try exact hmem.1.of_le (by omega)
  all_goals exact hsh_lt.trans Nat.lt_two_pow_self

private theorem realizesBounded_initTableWrite :
    RealizesBounded .exact initTableWriteProg
      (WordEncoding.encode (α := ((HashParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      InitTableWritePre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨⟨hp, hashBase⟩, idx⟩, cleared⟩
    obtain ⟨w₀, b, b', k, hc_lt, rfl, hidx, hfr, hclr_lt, hlimb⟩ := h
    try (dsimp only [hpSeedWords_mk, hpP_mk, hpMaskP_mk, hpTwoC_mk, hpC_mk, hpMaskC_mk,
      hpMask2C_mk] at *)
    dsimp only [ReducedKWise.tabBase] at hlimb
    have hc_pos : 0 < rChunk w₀ b b' := reducedChunkBits_pos _
    have hpack_le : 2 ^ rPack w w₀ b b' * (2 * rChunk w₀ b b') ≤ w :=
      two_pow_reducedPackShift_mul_le (le_of_lt hc_lt)
    have hpow_pack_le : 2 ^ (2 ^ rPack w w₀ b b' * (2 * rChunk w₀ b b')) ≤ 2 ^ w :=
      Nat.pow_le_pow_right two_pos hpack_le
    have hpow2c : Fits w (2 ^ (2 * rChunk w₀ b b')) := Nat.pow_lt_pow_right one_lt_two hc_lt
    obtain ⟨hu_lt, hv_lt, _, hprev_le, _, _, _, _⟩ := clmulTab_index_props hidx
    have hwIdx_lt := shiftRight_lt_reducedTableWords (w := w) hidx
    have hprevWIdx_le :
        (((idx >>> rChunk w₀ b b' <<< rChunk w₀ b b') +
          ((idx &&& (2 ^ rChunk w₀ b b' - 1)) >>> 1)) >>> rPack w w₀ b b') ≤
          idx >>> rPack w w₀ b b' := by
      rw [Nat.shiftRight_eq_div_pow _ (rPack w w₀ b b'),
        Nat.shiftRight_eq_div_pow _ (rPack w w₀ b b')]
      exact Nat.div_le_div_right hprev_le
    have hsub_lt := and_two_pow_sub_one_lt idx (rPack w w₀ b b')
    have hsh_lt : (idx &&& (2 ^ rPack w w₀ b b' - 1)) * (2 * rChunk w₀ b b') < w :=
      (Nat.mul_lt_mul_of_pos_right hsub_lt (by omega)).trans_le hpack_le
    have hpSh_lt :
        ((((idx >>> rChunk w₀ b b' <<< rChunk w₀ b b') +
          ((idx &&& (2 ^ rChunk w₀ b b' - 1)) >>> 1)) &&& (2 ^ rPack w w₀ b b' - 1)) *
          (2 * rChunk w₀ b b')) < w :=
      (Nat.mul_lt_mul_of_pos_right (and_two_pow_sub_one_lt _ _) (by omega)).trans_le hpack_le
    have hval_lt := clmul_lt_two_pow_two_mul hu_lt hv_lt
    have hpow_sub1_le :
        2 ^ (((idx &&& (2 ^ rPack w w₀ b b' - 1)) + 1) * (2 * rChunk w₀ b b')) ≤
          2 ^ (2 ^ rPack w w₀ b b' * (2 * rChunk w₀ b b')) :=
      Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_right _ hsub_lt)
    have hval_sh_lt :
        clmul (idx >>> rChunk w₀ b b') (idx &&& (2 ^ rChunk w₀ b b' - 1)) <<<
          ((idx &&& (2 ^ rPack w w₀ b b' - 1)) * (2 * rChunk w₀ b b')) <
          2 ^ (((idx &&& (2 ^ rPack w w₀ b b' - 1)) + 1) * (2 * rChunk w₀ b b')) := by
      rw [Nat.shiftLeft_eq]
      calc _ < 2 ^ (2 * rChunk w₀ b b') *
              2 ^ ((idx &&& (2 ^ rPack w w₀ b b' - 1)) * (2 * rChunk w₀ b b')) :=
            Nat.mul_lt_mul_of_pos_right hval_lt (Nat.two_pow_pos _)
        _ = _ := by rw [← pow_add]; congr 1; ring
    have hnew_lt := ((xor_shiftLeft_lt_two_pow hclr_lt hval_lt).trans_le hpow_sub1_le).trans_le
      hpow_pack_le
    have hv_shr_lt : (idx &&& (2 ^ rChunk w₀ b b' - 1)) >>> 1 < 2 ^ (rChunk w₀ b b' - 1) := by
      rw [Nat.shiftRight_eq_div_pow, pow_one]
      exact Nat.div_lt_of_lt_mul (by rwa [← pow_succ', Nat.sub_add_cancel hc_pos])
    have hcl_sh1_lt :
        clmul (idx >>> rChunk w₀ b b') ((idx &&& (2 ^ rChunk w₀ b b' - 1)) >>> 1) <<< 1 <
          2 ^ (2 * rChunk w₀ b b') := by
      have hcl_lt := clmul_lt_two_pow hu_lt hv_shr_lt
      rw [show rChunk w₀ b b' + (rChunk w₀ b b' - 1) = 2 * rChunk w₀ b b' - 1 by omega] at hcl_lt
      have : 2 ^ (2 * rChunk w₀ b b') = 2 ^ (2 * rChunk w₀ b b' - 1) * 2 := by
        conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ 2 * rChunk w₀ b b' by omega), pow_succ]
      rw [Nat.shiftLeft_eq, pow_one]; omega
    have hbit_lt :
        ((idx &&& (2 ^ rChunk w₀ b b' - 1)) &&& 1) * (idx >>> rChunk w₀ b b') <
          2 ^ (2 * rChunk w₀ b b') := by
      have hle : ((idx &&& (2 ^ rChunk w₀ b b' - 1)) &&& 1) * (idx >>> rChunk w₀ b b') ≤
          1 * (idx >>> rChunk w₀ b b') := Nat.mul_le_mul_right _ Nat.and_le_right
      rw [Nat.one_mul] at hle
      exact (lt_of_le_of_lt hle hu_lt).trans_le (Nat.pow_le_pow_right two_pos (by omega))
    have hfr_end :
        hashBase + ReducedKWise.seedWords w₀ b b' k + reducedTableWords (rStep w₀ b b') w ≤
          s.frontier := by
      simpa only [ReducedKWise.space, ReducedKWise.tableWords, Nat.add_assoc] using hfr
    have hge1 := Nat.zero_le (idx >>> rPack w w₀ b b')
    have hge2 := Nat.zero_le (((idx >>> rChunk w₀ b b' <<< rChunk w₀ b b') +
      ((idx &&& (2 ^ rChunk w₀ b b' - 1)) >>> 1)) >>> rPack w w₀ b b'))
  all_goals try exact hmem.1.of_le (by omega)
  all_goals try exact hpow2c.of_le (by omega)
  all_goals try exact hsh_lt.trans Nat.lt_two_pow_self
  all_goals try exact hpSh_lt.trans Nat.lt_two_pow_self
  all_goals try (rw [hlimb, clmul_eq_bit_mul_xor]; exact hnew_lt)
  all_goals try (rw [hlimb, clmul_eq_bit_mul_xor]
                 exact (hval_sh_lt.trans_le hpow_sub1_le).trans_le hpow_pack_le)

private theorem realizesBounded_initTableStepGen :
    RealizesBounded .exact initTableStepGenProg
      (WordEncoding.encode (α := (HashParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      InitTableStepGenPre (fun _ _ => 0) := by
  have hc := realizesBounded_initTableClear
  have hw := realizesBounded_initTableWrite
  realize
  all_goals (
    rcases d with ⟨⟨hp, hashBase⟩, idx⟩
    rcases h with ⟨w₀, b, b', k, hc_lt, rfl, hidx, hfr, hentry⟩)
  · exact ⟨w₀, b, b', k, hc_lt, rfl, hidx, hfr, hentry⟩
  · refine ⟨w₀, b, b', k, hc_lt, rfl, hidx, hfr, ?_, prevWord_limb_eq hidx hentry⟩
    change (s.mem _ &&& ((1 <<< _) - 1)) < _
    rw [Nat.shiftLeft_eq, one_mul]; exact and_two_pow_sub_one_lt _ _

private theorem initTableGenProg_aux {w w₀ b b' k hashBase : ℕ} {s₀ : Memory.State}
    (hc_lt : 2 * rChunk w₀ b b' < w)
    (hfr : hashBase + ReducedKWise.space w w₀ b b' k ≤ s₀.frontier)
    (hfit : Fits w (hashBase + ReducedKWise.space w w₀ b b' k)) :
    let hp := mkHashParams w w₀ b b' k
    let prog := initTableGenProg (hp, hashBase)
    let s' := (Memory.spec 0).clientState s₀ prog
    InitTableGenPre w (hp, hashBase) s₀ ∧
    iterationSafe initTableStepGenProg InitTableStepGenPre w (hp, hashBase)
      (2 ^ (2 * rChunk w₀ b b')) 0 s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ 4 * 2 ^ (2 * rChunk w₀ b b') ∧ s'.frontier = s₀.frontier ∧
    ReducedKWise.TableRep hashBase w w₀ b b' k s'.mem ∧
    (∀ a, (a < ReducedKWise.tabBase hashBase w₀ b b' k ∨
        hashBase + ReducedKWise.space w w₀ b b' k ≤ a) → s'.mem a = s₀.mem a) := by
  intro hp prog s'
  have hc_pos : 0 < rChunk w₀ b b' := reducedChunkBits_pos _
  have hpack_le : 2 ^ rPack w w₀ b b' * (2 * rChunk w₀ b b') ≤ w :=
    two_pow_reducedPackShift_mul_le (le_of_lt hc_lt)
  have hpow_pack_le : 2 ^ (2 ^ rPack w w₀ b b' * (2 * rChunk w₀ b b')) ≤ 2 ^ w :=
    Nat.pow_le_pow_right two_pos hpack_le
  let inv (idx a : ℕ) (s : Memory.State) : Prop :=
    idx = a ∧ hashBase + ReducedKWise.space w w₀ b b' k ≤ s.frontier ∧
    (∀ wIdx < idx >>> rPack w w₀ b b',
      s.mem (ReducedKWise.tabBase hashBase w₀ b b' k + wIdx) <
        2 ^ (2 ^ rPack w w₀ b b' * (2 * rChunk w₀ b b'))) ∧
    (∀ i < idx, getLimb (2 * rChunk w₀ b b')
      (s.mem (ReducedKWise.tabBase hashBase w₀ b b' k + (i >>> rPack w w₀ b b')))
      (i &&& (2 ^ rPack w w₀ b b' - 1)) =
      clmul (i >>> rChunk w₀ b b') (i &&& (2 ^ rChunk w₀ b b' - 1)))
  let mod (x : ℕ) : Prop :=
    ReducedKWise.tabBase hashBase w₀ b b' k ≤ x ∧ x < hashBase + ReducedKWise.space w w₀ b b' k
  have hprog_eq : prog =
      iterate initTableStepGenProg (hp, hashBase) (2 ^ (2 * rChunk w₀ b b')) 0 := rfl
  obtain ⟨hsafe, hv, hcost, hfr', hmod, _, _, hword', hentry'⟩ :=
    iterate_spec initTableStepGenProg InitTableStepGenPre w (hp, hashBase) 4
      (2 ^ (2 * rChunk w₀ b b')) inv mod
      (fun idx hidx a s ⟨ha_eq, hfr_s, hword, hentry⟩ => by
        subst ha_eq
        obtain ⟨hu_lt, hv_lt, _, hprev_le, _, _, _, _⟩ := clmulTab_index_props hidx
        have hwIdx_lt := shiftRight_lt_reducedTableWords (w := w) hidx
        have hprevWIdx_le :
            (((idx >>> rChunk w₀ b b' <<< rChunk w₀ b b') +
              ((idx &&& (2 ^ rChunk w₀ b b' - 1)) >>> 1)) >>> rPack w w₀ b b') ≤
              idx >>> rPack w w₀ b b' := by
          rw [Nat.shiftRight_eq_div_pow _ (rPack w w₀ b b'),
            Nat.shiftRight_eq_div_pow _ (rPack w w₀ b b')]
          exact Nat.div_le_div_right hprev_le
        have htBase_end :
            ReducedKWise.tabBase hashBase w₀ b b' k + reducedTableWords (rStep w₀ b b') w ≤
              s.frontier := by
          unfold ReducedKWise.tabBase; unfold ReducedKWise.space ReducedKWise.tableWords at hfr_s
          omega
        have hsub_lt := and_two_pow_sub_one_lt idx (rPack w w₀ b b')
        have hsh_lt : (idx &&& (2 ^ rPack w w₀ b b' - 1)) * (2 * rChunk w₀ b b') < w :=
          (Nat.mul_lt_mul_of_pos_right hsub_lt (by omega)).trans_le hpack_le
        let sh := (idx &&& (2 ^ rPack w w₀ b b' - 1)) * (2 * rChunk w₀ b b')
        let masked := s.mem (ReducedKWise.tabBase hashBase w₀ b b' k + (
          idx >>> rPack w w₀ b b')) &&&
          ((1 <<< sh) - 1)
        have hmasked_lt : masked < 2 ^ sh := by
          dsimp only [masked]; rw [Nat.shiftLeft_eq, one_mul]; exact and_two_pow_sub_one_lt _ sh
        have hlimb := prevWord_limb_eq hidx hentry
        dsimp only [ReducedKWise.tabBase] at hlimb
        have hval_lt := clmul_lt_two_pow_two_mul hu_lt hv_lt
        let newWord := masked ^^^
          (clmul (idx >>> rChunk w₀ b b') (idx &&& (2 ^ rChunk w₀ b b' - 1)) <<< sh)
        have hnew_pack_lt : newWord < 2 ^ (2 ^ rPack w w₀ b b' * (2 * rChunk w₀ b b')) :=
          (xor_shiftLeft_lt_two_pow hmasked_lt hval_lt).trans_le
            (Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_right _ hsub_lt))
        set s₁ := (Memory.spec 0).clientState s (initTableStepGenProg ((hp, hashBase), idx))
        have hs₁_mem : s₁.mem = Function.update s.mem
            (ReducedKWise.tabBase hashBase w₀ b b' k + (idx >>> rPack w w₀ b b')) newWord := by
          dsimp only [s₁, initTableStepGenProg, initTableClearProg, initTableWriteProg, hp,
            hpSeedWords_mk, hpP_mk, hpMaskP_mk, hpTwoC_mk, hpC_mk, hpMaskC_mk, hpMask2C_mk,
            newWord, masked, sh]
          unfold ReducedKWise.tabBase
          change Function.update (Function.update s.mem _ _) _ _ = _
          rw [hlimb, clmul_eq_bit_mul_xor, Function.update_idem]
        refine ⟨⟨w₀, b, b', k, hc_lt, rfl, hidx, hfr_s, hentry⟩, ?_, le_rfl, rfl,
          fun x hx => ?_, rfl, hfr_s, fun w' hw' => ?_, fun i hi => ?_⟩
        · dsimp only [initTableStepGenProg]
          rw [validHistory_bind']
          have hlt1 :
              hashBase + ReducedKWise.seedWords w₀ b b' k + (idx >>> rPack w w₀ b b') <
                s.frontier := by
            have h1 := Nat.add_lt_add_left hwIdx_lt (ReducedKWise.tabBase hashBase w₀ b b' k)
            unfold ReducedKWise.tabBase at h1 htBase_end
            exact lt_of_lt_of_le h1 htBase_end
          have hlt2 : hashBase + ReducedKWise.seedWords w₀ b b' k +
              ((((idx >>> rChunk w₀ b b' <<< rChunk w₀ b b') +
                ((idx &&& (2 ^ rChunk w₀ b b' - 1)) >>> 1)) >>> rPack w w₀ b b')) < s.frontier :=
            lt_of_le_of_lt (Nat.add_le_add_left hprevWIdx_le _) hlt1
          have hr_clr : (Memory.spec 0).clientResult s
              (initTableClearProg ((hp, hashBase), idx)) = masked := rfl
          have hs_clr : ((Memory.spec 0).clientState s
              (initTableClearProg ((hp, hashBase), idx))).mem =
              Function.update s.mem
                (hashBase + ReducedKWise.seedWords w₀ b b' k + (idx >>> rPack w w₀ b b'))
                masked := rfl
          refine ⟨?_, ?_⟩
          · dsimp only [initTableClearProg, hp, hpSeedWords_mk, hpP_mk, hpMaskP_mk, hpTwoC_mk]
            exact ⟨hlt1, ⟨hlt1, hmasked_lt.trans (Nat.pow_lt_pow_right one_lt_two hsh_lt)⟩,
              trivial⟩
          · rw [hr_clr]
            dsimp only [initTableWriteProg, hp, hpSeedWords_mk, hpP_mk, hpMaskP_mk, hpTwoC_mk,
              hpC_mk, hpMaskC_mk, hpMask2C_mk]
            refine ⟨hlt2, ⟨hlt1, ?_⟩, trivial⟩
            change Fits w (masked ^^^ (((((idx &&& (2 ^ rChunk w₀ b b' - 1)) &&& 1) *
              (idx >>> rChunk w₀ b b')) ^^^
              ((((((Memory.spec 0).clientState s (initTableClearProg ((hp, hashBase), idx))).mem
                (hashBase + ReducedKWise.seedWords w₀ b b' k +
                  ((((idx >>> rChunk w₀ b b' <<< rChunk w₀ b b') +
                    ((idx &&& (2 ^ rChunk w₀ b b' - 1)) >>> 1)) >>> rPack w w₀ b b')))) >>>
                ((((idx >>> rChunk w₀ b b' <<< rChunk w₀ b b') +
                  ((idx &&& (2 ^ rChunk w₀ b b' - 1)) >>> 1)) &&& (2 ^ rPack w w₀ b b' - 1)) *
                  (2 * rChunk w₀ b b'))) &&& (2 ^ (2 * rChunk w₀ b b') - 1)) <<< 1)) <<< sh))
            have hupd : Function.update s.mem
                (hashBase + ReducedKWise.seedWords w₀ b b' k + idx >>> rPack w w₀ b b') masked =
                Function.update s.mem
                  (hashBase + ReducedKWise.seedWords w₀ b b' k + idx >>> rPack w w₀ b b')
                  (s.mem (hashBase + ReducedKWise.seedWords w₀ b b' k +
                    idx >>> rPack w w₀ b b') &&&
                    ((1 <<< ((idx &&& (2 ^ rPack w w₀ b b' - 1)) *
                      (2 * rChunk w₀ b b'))) - 1)) := rfl
            rw [hs_clr, hupd, hlimb, clmul_eq_bit_mul_xor]
            exact hnew_pack_lt.trans_le hpow_pack_le
        · rw [hs₁_mem, Function.update_of_ne]
          intro heq; apply hx; rw [heq]
          refine ⟨Nat.le_add_right _ _, ?_⟩
          unfold ReducedKWise.tabBase ReducedKWise.space ReducedKWise.tableWords
          rw [← Nat.add_assoc]; exact Nat.add_lt_add_left hwIdx_lt _
        · rw [hs₁_mem]
          have := shiftRight_add_one_le idx (rPack w w₀ b b')
          rcases eq_or_lt_of_le (show w' ≤ idx >>> rPack w w₀ b b' by omega) with rfl | hlt
          · rw [Function.update_self]; exact hnew_pack_lt
          · rw [Function.update_of_ne (by omega)]; exact hword w' hlt
        · rw [hs₁_mem]
          have hmask_eq : (1 <<< sh) - 1 =
              2 ^ ((idx &&& (2 ^ rPack w w₀ b b' - 1)) * (2 * rChunk w₀ b b')) - 1 := by
            rw [Nat.shiftLeft_eq, one_mul]
          rcases eq_or_ne i idx with rfl | hne
          · rw [Function.update_self]; exact getLimb_xor_shiftLeft_self hmasked_lt hval_lt
          · have hilt : i < idx := by omega
            rcases eq_or_ne (i >>> rPack w w₀ b b') (idx >>> rPack w w₀ b b') with hw_eq | hw_ne
            · rw [hw_eq, Function.update_self]
              have hsub_i := and_lt_of_lt_of_shiftRight_eq hilt hw_eq
              dsimp only [newWord, masked, sh]
              rw [hmask_eq, getLimb_xor_shiftLeft_of_ne hval_lt (ne_of_lt hsub_i),
                getLimb_and_low hsub_i, ← hw_eq, hentry i hilt]
            · rw [Function.update_of_ne (by omega)]; exact hentry i hilt)
      0 s₀ ⟨rfl, hfr, fun _ hw' => by simp only [Nat.zero_shiftRight, not_lt_zero] at hw',
        fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
  dsimp only [s']; rw [hprog_eq]
  refine ⟨⟨w₀, b, b', k, hc_lt, rfl, hfr, hfit⟩, hsafe, hv, hcost, hfr',
    ⟨fun wIdx hwIdx => ?_, hentry'⟩, fun a ha => hmod a (by dsimp only [mod]; omega)⟩
  have hsh := two_pow_two_mul_chunkBits_shiftRight (rStep w₀ b b') w
  exact hword' wIdx (hsh.symm ▸ hwIdx)

/-- **Full specification of `initTableGenProg`**. -/
theorem initTableGenProg_spec {w w₀ b b' k hashBase : ℕ} {s₀ : Memory.State}
    (hc_lt : 2 * rChunk w₀ b b' < w)
    (hfr : hashBase + ReducedKWise.space w w₀ b b' k ≤ s₀.frontier)
    (hfit : Fits w (hashBase + ReducedKWise.space w w₀ b b' k)) :
    let hp := mkHashParams w w₀ b b' k
    let prog := initTableGenProg (hp, hashBase)
    let s' := (Memory.spec 0).clientState s₀ prog
    InitTableGenPre w (hp, hashBase) s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ 4 * 2 ^ (2 * rChunk w₀ b b') ∧ s'.frontier = s₀.frontier ∧
    ReducedKWise.TableRep hashBase w w₀ b b' k s'.mem ∧
    (∀ a, (a < ReducedKWise.tabBase hashBase w₀ b b' k ∨
        hashBase + ReducedKWise.space w w₀ b b' k ≤ a) → s'.mem a = s₀.mem a) := by
  obtain ⟨hpre, _, hv, hcost, hfr', htab, hframe⟩ := initTableGenProg_aux hc_lt hfr hfit
  exact ⟨hpre, hv, hcost, hfr', htab, hframe⟩

/-- **Parameter-free `RealizesBounded .exact` certificate for `initTableGenProg`** (
  `¬ReadsWidth`). -/
theorem realizesBounded_initTableGen :
    RealizesBounded .exact initTableGenProg
      (WordEncoding.encode (α := HashParams × ℕ)) (WordEncoding.encode (α := ℕ))
      InitTableGenPre (fun _ _ => 0) := by
  have hstep := realizesBounded_initTableStepGen
  realize
  all_goals (
    rcases d with ⟨hp, hashBase⟩
    obtain ⟨w₀, b, b', k, hc_lt, rfl, hfr, hfit⟩ := h
    try (dsimp only [hpPow2C_mk] at *)
    )
  all_goals exact (initTableGenProg_aux hc_lt hfr hfit).2.1


/-! ## Section 3: Key reduction and word-zeroing helpers -/

/-- Karatsuba half-limb multiplication subroutine. -/
@[expose] def karatsubaHalfProg : HashParams × ℕ × ℕ → Memory.Prog ℕ
  | (hp, α, x') => do
    let maskM := hpMaskM hp; let h := hpHalfM hp; let maskH := hpMaskH hp
    let maskMH := hpMaskMH hp; let maskM2H := hpMaskM2H hp
    let α₀ ← pure (α &&& maskH); let α₁ ← pure (α >>> h)
    let x₀ ← pure (x' &&& maskH); let x₁ ← pure (x' >>> h)
    let p₀ ← pure ((α₀ * x₀) &&& maskM)
    let p₁ ← pure (((α₀ * x₁) &&& maskMH) <<< h)
    let s₁ ← pure ((p₀ + p₁) &&& maskM)
    let p₂ ← pure (((α₁ * x₀) &&& maskMH) <<< h)
    let s₂ ← pure ((s₁ + p₂) &&& maskM)
    let p₃ ← pure (((α₁ &&& maskM2H) * (x₁ &&& maskM2H)) <<< (2 * h))
    pure ((s₂ + p₃) &&& maskM)

private def KaratsubaHalfPre (w : ℕ) : HashParams × ℕ × ℕ → Memory.State → Prop
  | (hp, α, x'), _ => ∃ w₀ b b' k,
    0 < w₀ ∧ w₀ ≤ w ∧ 2 * rChunk w₀ b b' < w ∧ hp = mkHashParams w w₀ b b' k ∧
    α < 2 ^ (w₀ - 1) ∧ x' < 2 ^ (w₀ - 1)

private theorem realizesBounded_karatsubaHalf :
    RealizesBounded .exact karatsubaHalfProg
      (WordEncoding.encode (α := HashParams × ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      KaratsubaHalfPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨hp, α, x'⟩
    obtain ⟨w₀, b, b', k, hw₀_pos, hw₀_le, hc_lt, rfl, hα_lt, hx'_lt⟩ := h
    try (dsimp only [hpMaskM_mk, hpHalfM_mk, hpMaskH_mk, hpMaskMH_mk, hpMaskM2H_mk] at *)
    have hm_lt : w₀ - 1 < w := by omega
    have h_le : (w₀ - 1) / 2 ≤ w₀ - 1 := Nat.div_le_self _ 2
    have h2_le : 2 * ((w₀ - 1) / 2) ≤ w₀ - 1 := Nat.mul_div_le _ 2
    have hpow2m : 2 ^ (w₀ - 1) + 2 ^ (w₀ - 1) ≤ 2 ^ w := by
      have : 2 ^ ((w₀ - 1) + 1) ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hm_lt
      rw [pow_succ'] at this; linarith
    have hfit_2m : Fits w (2 ^ (w₀ - 1)) := by change 2 ^ (w₀ - 1) < 2 ^ w; linarith
    have hα0 : α &&& (2 ^ ((w₀ - 1) / 2) - 1) < 2 ^ ((w₀ - 1) / 2) := and_two_pow_sub_one_lt _ _
    have hα1 : α >>> ((w₀ - 1) / 2) < 2 ^ ((w₀ - 1) - (w₀ - 1) / 2) :=
      shiftRight_lt_pow_sub h_le hα_lt
    have hx0 : x' &&& (2 ^ ((w₀ - 1) / 2) - 1) < 2 ^ ((w₀ - 1) / 2) := and_two_pow_sub_one_lt _ _
    have hx1 : x' >>> ((w₀ - 1) / 2) < 2 ^ ((w₀ - 1) - (w₀ - 1) / 2) :=
      shiftRight_lt_pow_sub h_le hx'_lt
    have hmul00 : (α &&& (2 ^ ((w₀ - 1) / 2) - 1)) * (x' &&& (2 ^ ((w₀ - 1) / 2) - 1)) <
        2 ^ (w₀ - 1) :=
      (Nat.mul_lt_mul'' hα0 hx0).trans_le
        (by rw [← pow_add, ← two_mul]; exact Nat.pow_le_pow_right two_pos h2_le)
    have hmul01 : (α &&& (2 ^ ((w₀ - 1) / 2) - 1)) * (x' >>> ((w₀ - 1) / 2)) < 2 ^ (w₀ - 1) :=
      (Nat.mul_lt_mul'' hα0 hx1).trans_eq (by rw [← pow_add, Nat.add_sub_of_le h_le])
    have hmul10 : (α >>> ((w₀ - 1) / 2)) * (x' &&& (2 ^ ((w₀ - 1) / 2) - 1)) < 2 ^ (w₀ - 1) :=
      (Nat.mul_lt_mul'' hα1 hx0).trans_eq (by rw [← pow_add, Nat.sub_add_cancel h_le])
    have hp1 : (((α &&& (2 ^ ((w₀ - 1) / 2) - 1)) * (x' >>> ((w₀ - 1) / 2))) &&&
        (2 ^ ((w₀ - 1) - (w₀ - 1) / 2) - 1)) <<< ((w₀ - 1) / 2) < 2 ^ (w₀ - 1) := by
      rw [Nat.shiftLeft_eq]
      exact (Nat.mul_lt_mul_of_pos_right (and_two_pow_sub_one_lt _ _)
        (Nat.two_pow_pos _)).trans_eq (by rw [← pow_add, Nat.sub_add_cancel h_le])
    have hp2 : (((α >>> ((w₀ - 1) / 2)) * (x' &&& (2 ^ ((w₀ - 1) / 2) - 1))) &&&
        (2 ^ ((w₀ - 1) - (w₀ - 1) / 2) - 1)) <<< ((w₀ - 1) / 2) < 2 ^ (w₀ - 1) := by
      rw [Nat.shiftLeft_eq]
      exact (Nat.mul_lt_mul_of_pos_right (and_two_pow_sub_one_lt _ _)
        (Nat.two_pow_pos _)).trans_eq (by rw [← pow_add, Nat.sub_add_cancel h_le])
    have hq3 : ((α >>> ((w₀ - 1) / 2)) &&& (2 ^ ((w₀ - 1) - 2 * ((w₀ - 1) / 2)) - 1)) *
        ((x' >>> ((w₀ - 1) / 2)) &&& (2 ^ ((w₀ - 1) - 2 * ((w₀ - 1) / 2)) - 1)) <
          2 ^ ((w₀ - 1) - 2 * ((w₀ - 1) / 2)) := by
      have h1 := (and_two_pow_sub_one_lt (α >>> ((w₀ - 1) / 2)) _).trans_le
        (Nat.pow_le_pow_right two_pos (show (w₀ - 1) - 2 * ((w₀ - 1) / 2) ≤ 1 by omega))
      have h2 := and_two_pow_sub_one_lt (x' >>> ((w₀ - 1) / 2)) ((w₀ - 1) - 2 * ((w₀ - 1) / 2))
      have hle1 : (α >>> ((w₀ - 1) / 2)) &&& (2 ^ ((w₀ - 1) - 2 * ((w₀ - 1) / 2)) - 1) ≤ 1 := by
        omega
      exact lt_of_le_of_lt (by calc _ ≤ 1 * _ := Nat.mul_le_mul_right _ hle1
        _ = _ := Nat.one_mul _) h2
    have hp3 : (((α >>> ((w₀ - 1) / 2)) &&& (2 ^ ((w₀ - 1) - 2 * ((w₀ - 1) / 2)) - 1)) *
        ((x' >>> ((w₀ - 1) / 2)) &&& (2 ^ ((w₀ - 1) - 2 * ((w₀ - 1) / 2)) - 1))) <<<
          (2 * ((w₀ - 1) / 2)) < 2 ^ (w₀ - 1) := by
      rw [Nat.shiftLeft_eq]
      exact (Nat.mul_lt_mul_of_pos_right hq3 (Nat.two_pow_pos _)).trans_eq
        (by rw [← pow_add, Nat.sub_add_cancel h2_le])
    have h2_fit : Fits w 2 :=
      (show 2 < w by have := reducedChunkBits_pos (rStep w₀ b b'); omega).trans Nat.lt_two_pow_self
    have hp0_lt := and_two_pow_sub_one_lt
      ((α &&& (2 ^ ((w₀ - 1) / 2) - 1)) * (x' &&& (2 ^ ((w₀ - 1) / 2) - 1))) (w₀ - 1)
    have hs1_lt := and_two_pow_sub_one_lt
      ((((α &&& (2 ^ ((w₀ - 1) / 2) - 1)) * (x' &&& (2 ^ ((w₀ - 1) / 2) - 1))) &&&
        (2 ^ (w₀ - 1) - 1)) +
       ((((α &&& (2 ^ ((w₀ - 1) / 2) - 1)) * (x' >>> ((w₀ - 1) / 2))) &&&
        (2 ^ ((w₀ - 1) - (w₀ - 1) / 2) - 1)) <<< ((w₀ - 1) / 2))) (w₀ - 1)
    have hs2_lt := and_two_pow_sub_one_lt
      ((((((α &&& (2 ^ ((w₀ - 1) / 2) - 1)) * (x' &&& (2 ^ ((w₀ - 1) / 2) - 1))) &&&
        (2 ^ (w₀ - 1) - 1)) +
       ((((α &&& (2 ^ ((w₀ - 1) / 2) - 1)) * (x' >>> ((w₀ - 1) / 2))) &&&
        (2 ^ ((w₀ - 1) - (w₀ - 1) / 2) - 1)) <<< ((w₀ - 1) / 2))) &&& (2 ^ (w₀ - 1) - 1)) +
       ((((α >>> ((w₀ - 1) / 2)) * (x' &&& (2 ^ ((w₀ - 1) / 2) - 1))) &&&
        (2 ^ ((w₀ - 1) - (w₀ - 1) / 2) - 1)) <<< ((w₀ - 1) / 2))) (w₀ - 1))
  all_goals try exact h2_fit
  all_goals try exact (show 2 * ((w₀ - 1) / 2) < w by omega).trans Nat.lt_two_pow_self
  all_goals try exact hfit_2m.of_le (le_of_lt hmul00)
  all_goals try exact hfit_2m.of_le (le_of_lt hmul01)
  all_goals try exact hfit_2m.of_le (le_of_lt hmul10)
  all_goals try exact hfit_2m.of_le (le_of_lt hp1)
  all_goals try exact hfit_2m.of_le (le_of_lt hp2)
  all_goals try exact hfit_2m.of_le (le_of_lt hp3)
  all_goals exact lt_of_lt_of_le (by omega) hpow2m

/-- Universe-reduction key evaluator subroutine. -/
@[expose] def reduceKeyGenProg : HashParams × ℕ × ℕ → Memory.Prog ℕ
  | (hp, hashBase, uVal) => do
    let α ← Memory.read hashBase
    let x' ← pure (uVal &&& hpMaskM hp)
    let half ← karatsubaHalfProg (hp, α, x')
    let odd ← pure ((uVal &&& 1) + ((((uVal >>> 1) + half) &&& hpMaskM hp) <<< 1))
    pure (odd >>> hpRemShift hp)

/-- Precondition for `reduceKeyGenProg`. -/
@[expose] def ReduceKeyGenPre (w : ℕ) : HashParams × ℕ × ℕ → Memory.State → Prop
  | (hp, hashBase, uVal), s => ∃ w₀ b b' k,
    0 < w₀ ∧ w₀ ≤ w ∧ 2 * rChunk w₀ b b' < w ∧ hp = mkHashParams w w₀ b b' k ∧
    hashBase < s.frontier ∧ s.mem hashBase < 2 ^ (w₀ - 1) ∧ uVal < 2 ^ w₀

theorem realizesBounded_reduceKeyGen :
    RealizesBounded .exact reduceKeyGenProg
      (WordEncoding.encode (α := HashParams × ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      ReduceKeyGenPre (fun _ _ => 0) := by
  have hk := realizesBounded_karatsubaHalf
  realize
  all_goals (
    rcases d with ⟨hp, hashBase, uVal⟩
    obtain ⟨w₀, b, b', k, hw₀_pos, hw₀_le, hc_lt, rfl, hfr, hα_lt, hu_lt⟩ := h
    try (dsimp only [hpMaskM_mk, hpRemShift_mk] at *)
    have hm_lt : w₀ - 1 < w := by omega
    have hpow2m : 2 ^ (w₀ - 1) + 2 ^ (w₀ - 1) ≤ 2 ^ w := by
      have : 2 ^ ((w₀ - 1) + 1) ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hm_lt
      rw [pow_succ'] at this; linarith
    have hu_shr : uVal >>> 1 < 2 ^ (w₀ - 1) := by
      rw [Nat.shiftRight_eq_div_pow, pow_one]
      exact Nat.div_lt_of_lt_mul (by
        have hm_eq : w₀ = (w₀ - 1) + 1 := by omega
        rw [hm_eq, pow_succ'] at hu_lt; exact hu_lt)
    have hhalf_lt : (Memory.spec 0).clientResult s
        (karatsubaHalfProg (mkHashParams w w₀ b b' k, s.mem hashBase,
          uVal &&& (2 ^ (w₀ - 1) - 1))) < 2 ^ (w₀ - 1) := by
      dsimp only [karatsubaHalfProg]; exact and_two_pow_sub_one_lt _ (w₀ - 1)
    have hbit : uVal &&& 1 < 2 := by
      rw [Nat.and_two_pow_sub_one_eq_mod uVal 1]; exact Nat.mod_lt uVal two_pos
    have h2_fit : Fits w 2 :=
      (show 2 < w by have := reducedChunkBits_pos (
        rStep w₀ b b'); omega).trans Nat.lt_two_pow_self)
  all_goals try exact ⟨w₀, b, b', k, hw₀_pos, hw₀_le, hc_lt, rfl, hα_lt,
    and_two_pow_sub_one_lt _ (w₀ - 1)⟩
  all_goals try exact h2_fit.of_le (by omega)
  all_goals try exact lt_of_lt_of_le (by omega) hpow2m
  all_goals (
    have hm1 := and_two_pow_sub_one_lt ((uVal >>> 1) +
      (Memory.spec 0).clientResult s
        (karatsubaHalfProg (mkHashParams w w₀ b b' k, s.mem hashBase,
          uVal &&& (2 ^ (w₀ - 1) - 1)))) (w₀ - 1)
    rw [Nat.shiftLeft_eq, pow_one]
    exact lt_of_lt_of_le (by omega) hpow2m)

/-- Single word zeroing step subroutine. -/
@[expose] def zeroWordsStepProg : ℕ × ℕ → Memory.Prog ℕ
  | (baseAddr, i) => do Memory.write (baseAddr + i) 0; pure (i + 1)

/-- Precondition for `zeroWordsStepProg`. -/
@[expose] def ZeroWordsStepPre (_w : ℕ) : ℕ × ℕ → Memory.State → Prop
  | (baseAddr, i), s => baseAddr + i < s.frontier

theorem realizesBounded_zeroWordsStep :
    RealizesBounded .exact zeroWordsStepProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      ZeroWordsStepPre (fun _ _ => 0) := by
  realize
  all_goals (rcases d with ⟨baseAddr, i⟩; dsimp only [ZeroWordsStepPre] at h)
  all_goals exact hmem.1.of_le (by omega)

theorem zeroWordsLoop_spec {w baseAddr n : ℕ} {s₀ : Memory.State}
    (hfr : baseAddr + n ≤ s₀.frontier) :
    let prog := iterate zeroWordsStepProg baseAddr n 0
    let s' := (Memory.spec 0).clientState s₀ prog
    iterationSafe zeroWordsStepProg ZeroWordsStepPre w baseAddr n 0 s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ n ∧ s'.frontier = s₀.frontier ∧
    (∀ d < n, s'.mem (baseAddr + d) = 0) ∧
    (∀ a, (a < baseAddr ∨ baseAddr + n ≤ a) → s'.mem a = s₀.mem a) := by
  obtain ⟨hsafe, hv, hcost, hfr', hmod, _, _, hz⟩ :=
    iterate_spec zeroWordsStepProg ZeroWordsStepPre w baseAddr 1 n
      (fun k i s => k = i ∧ baseAddr + n ≤ s.frontier ∧ ∀ d < k, s.mem (baseAddr + d) = 0)
      (fun x => baseAddr ≤ x ∧ x < baseAddr + n)
      (fun k hk i s ⟨hi_eq, hfr_s, hz_s⟩ => by
        subst hi_eq
        refine ⟨by dsimp only [ZeroWordsStepPre]; omega, ⟨⟨by omega, Nat.two_pow_pos w⟩, trivial⟩,
          le_rfl, rfl, fun x hx => Function.update_of_ne (by omega) _ _, rfl, hfr_s,
            fun d hd => ?_⟩
        change Function.update s.mem (baseAddr + k) 0 (baseAddr + d) = 0
        rcases eq_or_ne d k with rfl | hne
        · exact Function.update_self _ _ _
        · rw [Function.update_of_ne (by omega)]; exact hz_s d (by omega))
      0 s₀ ⟨rfl, hfr, fun _ hd => (Nat.not_lt_zero _ hd).elim⟩
  exact ⟨hsafe, hv, by simpa only [one_mul] using hcost, hfr', hz, fun a ha => hmod a (by omega)⟩

end Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise

/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.HashFamily.WordRAM.Basic
public import CslibFrontier.DataStructure.HashFamily.WordRAM.Tabulation
public import CslibFrontier.Probability.KWiseIndependent.ReducedLimbs
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Tactic.Fits

/-!
# Universe-Reduced `k`-Wise Independent Hashing with Bit-Packed Tables

This module provides a reusable Word-RAM implementation of the two-stage universe-reduced `k`-wise
independent hash family (`Cslib.Probability.reducedPolyHash U w₀ b b' k`) over
`Cslib.WordRAM.Basis.exact` and lifts it to `Cslib.WordRAM.Basis.standard`:

1. **Two-stage construction without any universe restriction (`U ≤ 2 ^ w₀`, `0 < w₀ ≤ w`)**:
   - **Stage 1 (overflow-free multiply-shift reduction)**: reduces any `w₀`-bit key `u : Fin U`
     (`0 < w₀ ≤ w`) to `R = min w₀ (3 * b)` bits via `multiplyShiftReduced U w₀ (3 * b) α u` using
     `oddMulModWord` (`39` deterministic instructions, no `2 * w₀ ≤ w` restriction).
   - **Stage 2 (limb-aligned trinomial polynomial hash with bit-packed Four-Russians table)**:
     evaluates a degree-`< k` polynomial over `GF(2)[X] / (X^{2·3^t} + X^{3^t} + 1)` on the reduced
     key using `L = reducedLimbCount t ≤ 54` limbs of `c = reducedChunkBits t = 3 ^ (t - 3)` bits
     and a bit-packed Four-Russians carryless multiplication table of
     `reducedTableBits t ≤ max 8 (2 ^ (b / 2)) = o(2 ^ b)` bits (`b' ≤ 3 * b`).
2. **Compact `O(k) + o(2 ^ b) / w`-word memory layout (`space w w₀ b b' k`)**:
   - `[base, base + 1 + k * L)` stores the top seed `α : Fin (2 ^ (w₀ - 1))` (`1` word) and the
     `k * L` `c`-bit limbs of the polynomial coefficients `β : Fin k → Fin (2 ^ (2 * 3 ^ t))`
     (`1 + k * L ≤ 1 + 54 * k = O(k)` words).
   - `[base + 1 + k * L, base + space w w₀ b b' k)` stores the bit-packed carryless multiplication
     table in `tableWords w w₀ b b' = reducedTableWords t w` words.
3. **`O(1)` worst-case evaluation time for fixed `k` (`evalCode w w₀ b b' k`)**:
   - Executes in `evalSteps w₀ b b' k ≤ evalBound k = 47250 * k + 591 = O(k)` deterministic
     instructions completely independent of `w`, `w₀`, `b`, `b'`, and `U`.
4. **Conditional `k`-wise independence and `HashFamily.WordRAM.Impl` packaging**:
   - Conditioned on any top seed `α ∈ reducedGoodTop U w₀ (3 * b) S` that is injective on
     `S : Finset (Fin U)` (failure probability `≤ (#S * (#S - 1)) / 2 ^ min w₀ (3 * b)`), the
     restricted family on `S` is exact `k`-wise independent (`IsKWiseIndependentHash k`).

## Main definitions

* `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.seedWords`,
  `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.tableWords`,
  `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.space`: memory footprint sizes.
* `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.TableRep`,
  `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.SeedRep`,
  `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.Rep`: memory representation predicates.
* `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.initTableCode`,
  `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.resampleCode`,
  `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.evalCode`: Word-RAM programs on `Data 240`.
* `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.impl`,
  `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.implStandard`: `HashFamily.WordRAM.Impl`
  certificates.

## Main results

* `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.space_le`:
  `space w w₀ b b' k ≤ 2 + 54 * k + 2 * max 8 (2 ^ (b / 2)) / w` when `b' ≤ 3 * b`.
* `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.initTableCode_execWithin`: deterministic
  table initialization.
* `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.resampleCode_execRand`,
  `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.map_extractSeed_eval_resampleComp`: exact
  product uniformity of seed resampling.
* `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.evalCode_execWithin`,
  `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.evalSteps_le`: deterministic evaluation in
  `≤ 47250 * k + 591` instructions.

## References

* [M. Dietzfelbinger, T. Hagerup, J. Katajainen, M. Penttonen, *A Reliable Randomized Algorithm
  for the Closest-Pair Problem*][DietzfelbingerHagerupKatajainenPenttonen1997]
* [S. P. Vadhan, *Pseudorandomness*, Section 3.5.5][Vadhan2012]
* [M. N. Wegman, J. L. Carter, *New hash functions and their use in authentication and set
  equality*][WegmanCarter1981]
-/

public section

open Cslib.WordRAM Cslib.WordRAM.ExactLog Cslib.DataStructure.WordRAM.Randomized Cslib.Probability
open scoped ENNReal BigOperators

namespace Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise

/-! ## Section 1: Memory layout, representation predicates, and seed extraction -/

/-- Number of seed words `1 + k * reducedLimbCount (reducedTrinomialStep w₀ b b')` (`1` word for the
multiply-shift seed `α` and `k * L` words for the `c`-bit limbs of the `k` polynomial
coefficients). -/
@[expose] def seedWords (w₀ b b' k : ℕ) : ℕ :=
  1 + k * reducedLimbCount (reducedTrinomialStep w₀ b b')

/-- Number of words `reducedTableWords (reducedTrinomialStep w₀ b b') w` occupied by the bit-packed
Four-Russians carryless multiplication table. -/
@[expose] def tableWords (w w₀ b b' : ℕ) : ℕ :=
  reducedTableWords (reducedTrinomialStep w₀ b b') w

/-- Total memory footprint `seedWords w₀ b b' k + tableWords w w₀ b b'` in words. -/
@[expose] def space (w w₀ b b' k : ℕ) : ℕ :=
  seedWords w₀ b b' k + tableWords w w₀ b b'

/-- Base address `base + seedWords w₀ b b' k` of the bit-packed carryless multiplication table. -/
@[expose] def tabBase (base w₀ b b' k : ℕ) : ℕ :=
  base + seedWords w₀ b b' k

/-- Address `base + 1 + (m.val + L * j.val)` of the `m`-th limb of polynomial coefficient `j`. -/
@[expose] def coeffLimbAddr (base w₀ b b' : ℕ) {k : ℕ}
    (j : Fin k) (m : Fin (reducedLimbCount (reducedTrinomialStep w₀ b b'))) : ℕ :=
  base + 1 + (m.val + reducedLimbCount (reducedTrinomialStep w₀ b b') * j.val)

theorem seedWords_pos (w₀ b b' k : ℕ) : 0 < seedWords w₀ b b' k := by
  dsimp only [seedWords]; omega

theorem seedWords_le (w₀ b b' k : ℕ) : seedWords w₀ b b' k ≤ 1 + 54 * k := by
  dsimp only [seedWords]
  have hL := reducedLimbCount_le (reducedTrinomialStep w₀ b b')
  nlinarith

theorem tableWords_le {w w₀ b b' : ℕ} (hw₀ : w₀ ≤ w) (hb' : b' ≤ 3 * b) (hb'_w : b' ≤ w)
    (hw : 2 ≤ w) :
    tableWords w w₀ b b' ≤ 2 * max 8 (2 ^ (b / 2)) / w + 1 := by
  dsimp only [tableWords]
  have hc := two_mul_reducedChunkBits_le (b := b) hw₀ hb'_w hw
  have h1 := reducedTableWords_le hc
  have h2 := reducedTableBits_le (w₀ := w₀) hb'
  exact h1.trans (Nat.add_le_add_right (Nat.div_le_div_right (by omega)) 1)

/-- **Compact space bound**: whenever `w₀ ≤ w`, `b' ≤ 3 * b`, `b' ≤ w`, and `2 ≤ w`,
`space w w₀ b b' k` uses at most `2 + 54 * k + 2 * max 8 (2 ^ (b / 2)) / w` words
(`O(k) + o(2 ^ b) / w`). -/
theorem space_le {w w₀ b b' k : ℕ} (hw₀ : w₀ ≤ w) (hb' : b' ≤ 3 * b) (hb'_w : b' ≤ w)
    (hw : 2 ≤ w) :
    space w w₀ b b' k ≤ 2 + 54 * k + 2 * max 8 (2 ^ (b / 2)) / w := by
  dsimp only [space]
  have hs := seedWords_le w₀ b b' k
  have ht := tableWords_le hw₀ hb' hb'_w hw
  omega

/-- Whenever `2 * reducedChunkBits t ≤ w` and `Fits w (base + space w w₀ b b' k)`, we have strict
inequality `2 * reducedChunkBits t < w` (and hence `2 ^ (2 * reducedChunkBits t) < 2 ^ w`). -/
theorem two_mul_reducedChunkBits_lt_of_fits_space {w base w₀ b b' k : ℕ}
    (hc : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') ≤ w)
    (hfit : Fits w (base + space w w₀ b b' k)) :
    2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w := by
  set t := reducedTrinomialStep w₀ b b'
  set c := reducedChunkBits t
  by_contra hnot
  have heq : 2 * c = w := by omega
  have hc_pos : 0 < 2 * c := by have := reducedChunkBits_pos t; omega
  have hdiv : w / (2 * c) = 1 := by rw [← heq, Nat.div_self hc_pos]
  have hp0 : reducedPackShift t w = 0 := by
    dsimp only [reducedPackShift]
    rw [hdiv]
    simp
  have htw : tableWords w w₀ b b' = 2 ^ w := by
    dsimp only [tableWords, reducedTableWords]
    rw [hp0, Nat.sub_zero, heq]
  have hlt : base + space w w₀ b b' k < 2 ^ w := hfit
  dsimp only [space] at hlt
  omega

/-- Deterministic precomputed table invariant at `tabBase base w₀ b b' k`: every table word is
`< 2 ^ (2 ^ p * (2 * c))` and every `2 * c`-bit slice `idx < 2 ^ (2 * c)` stores
`clmul (idx >>> c) (idx &&& (2 ^ c - 1))`. -/
@[expose] def TableRep (base w w₀ b b' k : ℕ) (mem : ℕ → ℕ) : Prop :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let p := reducedPackShift t w
  let tBase := tabBase base w₀ b b' k
  (∀ wIdx < tableWords w w₀ b b', mem (tBase + wIdx) < 2 ^ (2 ^ p * (2 * c))) ∧
  (∀ idx < 2 ^ (2 * c),
    getLimb (2 * c) (mem (tBase + (idx >>> p))) (idx &&& (2 ^ p - 1)) =
      clmul (idx >>> c) (idx &&& (2 ^ c - 1)))

/-- Seed representation invariant linking `θ : ReducedPolySeed w₀ b b' k` to memory at
`[base, base + seedWords w₀ b b' k)`. -/
@[expose] def SeedRep (base w₀ b b' k : ℕ) (θ : ReducedPolySeed w₀ b b' k) (mem : ℕ → ℕ) : Prop :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let L := reducedLimbCount t
  mem base = θ.1.val ∧
  ∀ (j : Fin k) (m : Fin L),
    mem (base + 1 + (m.val + L * j.val)) = getLimb c (θ.2 j).val m.val

/-- Combined table + seed invariant `TableRep ∧ SeedRep`. -/
@[expose] def Rep (base w w₀ b b' k : ℕ) (θ : ReducedPolySeed w₀ b b' k) (mem : ℕ → ℕ) : Prop :=
  TableRep base w w₀ b b' k mem ∧ SeedRep base w₀ b b' k θ mem

/-- Equivalence `(Fin 1 → Fin (2 ^ (w₀ - 1))) ≃ ReducedTopSeed w₀`. -/
@[expose] def topSliceEquiv (w₀ : ℕ) :
    (Fin 1 → Fin (2 ^ (w₀ - 1))) ≃ ReducedTopSeed w₀ :=
  Equiv.funUnique (Fin 1) (Fin (2 ^ (w₀ - 1)))

/-- Equivalence between flat `k * L`-word slices of `c`-bit limbs and
`ReducedBotSeed w₀ b b' k`. -/
@[expose] def botSliceEquiv (w₀ b b' k : ℕ) :
    let t := reducedTrinomialStep w₀ b b'
    (Fin (k * reducedLimbCount t) → Fin (2 ^ reducedChunkBits t)) ≃
      ReducedBotSeed w₀ b b' k :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let L := reducedLimbCount t
  (Equiv.arrowCongr finProdFinEquiv (Equiv.refl (Fin (2 ^ c)))).symm.trans <|
    (Equiv.curry (Fin k) (Fin L) (Fin (2 ^ c))).trans <|
      Equiv.arrowCongr (Equiv.refl (Fin k))
        ((limbsEquivFin c L (reducedChunkBits_pos t)).trans
          (finCongr (by rw [reducedLimbCount_mul_chunkBits])))

/-- Extract the top-level multiply-shift seed `α : ReducedTopSeed w₀` from `mem base`. -/
@[expose] def extractTop (base w₀ : ℕ) (mem : ℕ → ℕ) : ReducedTopSeed w₀ :=
  topSliceEquiv w₀ (Tabulation.extractSlice base (w₀ - 1) 1 mem)

/-- Extract the bottom-level polynomial seed `β : ReducedBotSeed w₀ b b' k` from
`[base + 1, base + 1 + k * L)`. -/
@[expose] def extractBot (base w₀ b b' k : ℕ) (mem : ℕ → ℕ) : ReducedBotSeed w₀ b b' k :=
  let t := reducedTrinomialStep w₀ b b'
  botSliceEquiv w₀ b b' k
    (Tabulation.extractSlice (base + 1) (reducedChunkBits t) (k * reducedLimbCount t) mem)

/-- Extract the full seed `(α, β) : ReducedPolySeed w₀ b b' k` from memory. -/
@[expose] def extractSeed (base w₀ b b' k : ℕ) (mem : ℕ → ℕ) : ReducedPolySeed w₀ b b' k :=
  (extractTop base w₀ mem, extractBot base w₀ b b' k mem)

@[simp]
theorem extractTop_val (base w₀ : ℕ) (mem : ℕ → ℕ) :
    (extractTop base w₀ mem).val = (Tabulation.extractWord (w₀ - 1) (mem base)).val := by
  change (Tabulation.extractWord (w₀ - 1) (mem (base + (0 : Fin 1).val))).val =
    (Tabulation.extractWord (w₀ - 1) (mem base)).val
  rw [Fin.val_zero, Nat.add_zero]

theorem getLimb_extractBot_val (base w₀ b b' k : ℕ) (mem : ℕ → ℕ)
    (j : Fin k) (m : Fin (reducedLimbCount (reducedTrinomialStep w₀ b b'))) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    getLimb c (extractBot base w₀ b b' k mem j).val m.val =
      (Tabulation.extractWord c (mem (base + 1 + (m.val + L * j.val)))).val := by
  intro t c L
  have hc := reducedChunkBits_pos t
  let f : Fin L → Fin (2 ^ c) := fun m' =>
    Tabulation.extractSlice (base + 1) c (k * L) mem (finProdFinEquiv (j, m'))
  have hval : (extractBot base w₀ b b' k mem j).val = (limbsEquivFin c L hc f).val := rfl
  have hinv : (limbsEquivFin c L hc).symm (limbsEquivFin c L hc f) m = f m := by
    rw [Equiv.symm_apply_apply]
  have hinv_val : getLimb c (limbsEquivFin c L hc f).val m.val = (f m).val :=
    congrArg Fin.val hinv
  rw [hval, hinv_val]
  rfl

/-! ## Register layout on `Data 240` -/

/-- Reduced-key limb register `20 + m % 54` (`0 ≤ m < L ≤ 54`). -/
@[expose] def xReg (m : ℕ) : Fin 240 :=
  ⟨20 + m % 54, by omega⟩

/-- Horner accumulator limb register `74 + m % 54` (`0 ≤ m < L ≤ 54`). -/
@[expose] def accReg (m : ℕ) : Fin 240 :=
  ⟨74 + m % 54, by omega⟩

/-- Carryless product limb register `128 + d % 108` (`0 ≤ d < 2 * L ≤ 108`). -/
@[expose] def prodReg (d : ℕ) : Fin 240 :=
  ⟨128 + d % 108, by omega⟩

/-- Register embedding `Fin 6 → Fin 240` for `Tabulation.randFillLoop`:
maps `[0, 1, 2, 3, 4, 5] ↦ [3, 4, 5, 6, 7, 0]`. -/
@[expose] def fillMap240 : Fin 6 → Fin 240
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => 5
  | ⟨3, _⟩ => 6
  | ⟨4, _⟩ => 7
  | ⟨5, _⟩ => 0

theorem injective_fillMap240 : Function.Injective fillMap240 := by
  decide

/-! ## Section 2: Bit-packed Four-Russians table construction (`initTableCode`) -/

/-- 11-instruction setup before `clmulTabLoop` on `Data 240`. -/
@[expose] def initTableSetupCode (w w₀ b b' k : ℕ) : Code .exact 240 :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let p := reducedPackShift t w
  let s := seedWords w₀ b b' k
  .seq (.op (.const 1 s))
  (.seq (.op (.exactBin .add 1 0 1))
  (.seq (.op (.const 2 0))
  (.seq (.op (.const 3 (2 ^ (2 * c))))
  (.seq (.op (.const 4 c))
  (.seq (.op (.const 5 (2 ^ c - 1)))
  (.seq (.op (.const 6 1))
  (.seq (.op (.const 7 p))
  (.seq (.op (.const 8 (2 ^ p - 1)))
  (.seq (.op (.const 9 (2 * c)))
        (.op (.const 18 (2 ^ (2 * c) - 1))))))))))))

/-- Closed-form state after `initTableSetupCode w w₀ b b' k`. -/
@[expose] def initTableSetupData (base w w₀ b b' k : ℕ) (x : Data 240) : Data 240 :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let p := reducedPackShift t w
  let s := seedWords w₀ b b' k
  (((((((((((x.set 1 s).set 1 (base + s)).set 2 0).set 3 (2 ^ (2 * c))).set 4 c).set 5
    (2 ^ c - 1)).set 6 1).set 7 p).set 8 (2 ^ p - 1)).set 9 (2 * c)).set 18 (2 ^ (2 * c) - 1))

/-- 29-instruction body of `clmulTabLoop` on `Data 240`, populating slice `idx &&& (2 ^ p - 1)` of
`mem[tabBase + (idx >>> p)]` with `clmul (idx >>> c) (idx &&& (2 ^ c - 1))`. -/
@[expose] def clmulTabBody : Code .exact 240 :=
  .seq (.op (.exactBin .shiftRight 10 2 7))
  (.seq (.op (.exactBin .add 10 1 10))
  (.seq (.op (.exactBin .and 11 2 8))
  (.seq (.op (.exactBin .mul 11 11 9))
  (.seq (.op (.exactBin .shiftLeft 12 6 11))
  (.seq (.op (.exactBin .sub 12 12 6))
  (.seq (.op (.load 13 10))
  (.seq (.op (.exactBin .and 13 13 12))
  (.seq (.op (.store 10 13))
  (.seq (.op (.exactBin .shiftRight 14 2 4))
  (.seq (.op (.exactBin .and 15 2 5))
  (.seq (.op (.exactBin .shiftRight 16 15 6))
  (.seq (.op (.exactBin .shiftLeft 17 14 4))
  (.seq (.op (.exactBin .add 16 17 16))
  (.seq (.op (.exactBin .shiftRight 17 16 7))
  (.seq (.op (.exactBin .add 17 1 17))
  (.seq (.op (.load 17 17))
  (.seq (.op (.exactBin .and 16 16 8))
  (.seq (.op (.exactBin .mul 16 16 9))
  (.seq (.op (.exactBin .shiftRight 17 17 16))
  (.seq (.op (.exactBin .and 17 17 18))
  (.seq (.op (.exactBin .shiftLeft 17 17 6))
  (.seq (.op (.exactBin .and 15 15 6))
  (.seq (.op (.exactBin .mul 15 15 14))
  (.seq (.op (.exactBin .xor 17 15 17))
  (.seq (.op (.exactBin .shiftLeft 17 17 11))
  (.seq (.op (.exactBin .xor 13 13 17))
  (.seq (.op (.store 10 13))
        (.op (.exactBin .add 2 2 6)))))))))))))))))))))))))))))

/-- Loop `while idx < 2 ^ (2 * c) do clmulTabBody` populating the bit-packed carryless
multiplication table. -/
@[expose] def clmulTabLoop : Code .exact 240 :=
  .loop (.lt 2 3) clmulTabBody

/-- Full table initialization program on `Data 240`. -/
@[expose] def initTableCode (w w₀ b b' k : ℕ) : Code .exact 240 :=
  .seq (initTableSetupCode w w₀ b b' k) clmulTabLoop

/-- Exact instruction count `31 * 2 ^ (2 * c) + 13` of `initTableCode w w₀ b b' k`. -/
@[expose] def initTableSteps (w₀ b b' : ℕ) : ℕ :=
  31 * 2 ^ (2 * reducedChunkBits (reducedTrinomialStep w₀ b b')) + 13

theorem clmulTabLoop_exec {w tBase t : ℕ}
    (hc_lt : 2 * reducedChunkBits t < w)
    (hfit_end : Fits w (tBase + reducedTableWords t w)) :
    let c := reducedChunkBits t
    let p := reducedPackShift t w
    ∀ rem idx : ℕ, ∀ x : Data 240,
      idx + rem = 2 ^ (2 * c) →
      x.regs 0 = x.regs 0 →
      x.regs 1 = tBase →
      x.regs 2 = idx →
      x.regs 3 = 2 ^ (2 * c) →
      x.regs 4 = c →
      x.regs 5 = 2 ^ c - 1 →
      x.regs 6 = 1 →
      x.regs 7 = p →
      x.regs 8 = 2 ^ p - 1 →
      x.regs 9 = 2 * c →
      x.regs 18 = 2 ^ (2 * c) - 1 →
      (∀ wIdx < idx >>> p, x.mem (tBase + wIdx) < 2 ^ (2 ^ p * (2 * c))) →
      (∀ i < idx,
        getLimb (2 * c) (x.mem (tBase + (i >>> p))) (i &&& (2 ^ p - 1)) =
          clmul (i >>> c) (i &&& (2 ^ c - 1))) →
      ∃ y : Data 240,
        Exec w clmulTabLoop x y (31 * rem + 2) ∧
        y.regs 0 = x.regs 0 ∧
        (∀ wIdx < reducedTableWords t w, y.mem (tBase + wIdx) < 2 ^ (2 ^ p * (2 * c))) ∧
        (∀ i < 2 ^ (2 * c),
          getLimb (2 * c) (y.mem (tBase + (i >>> p))) (i &&& (2 ^ p - 1)) =
            clmul (i >>> c) (i &&& (2 ^ c - 1))) ∧
        (∀ a, (a < tBase + (idx >>> p) ∨ tBase + reducedTableWords t w ≤ a) →
          y.mem a = x.mem a) := by
  intro c p rem
  have hc_pos : 0 < c := reducedChunkBits_pos t
  have h2c_le : 2 * c ≤ w := le_of_lt hc_lt
  have hpack_le : 2 ^ p * (2 * c) ≤ w := two_pow_reducedPackShift_mul_le h2c_le
  have hpow_pack_le : 2 ^ (2 ^ p * (2 * c)) ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hpack_le
  have hpow_2c_lt : 2 ^ (2 * c) < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hc_lt
  induction rem with
  | zero =>
    intro idx x hsum _ h1 h2 h3 _ _ _ _ _ _ _ hword hentry
    have hidx_eq : idx = 2 ^ (2 * c) := by omega
    have hc_exit : ¬(Cond.lt (2 : Fin 240) 3).Holds x := by
      simp [Cond.Holds, h2, h3, hidx_eq]
    refine ⟨x, Exec.loop_exit hc_exit, rfl, ?_, ?_, fun _ _ => rfl⟩
    · intro wIdx hwIdx
      have hsh : idx >>> p = reducedTableWords t w := by
        rw [hidx_eq]
        exact two_pow_two_mul_chunkBits_shiftRight t w
      exact hword wIdx (hsh.symm ▸ hwIdx)
    · intro i hi
      exact hentry i (hidx_eq ▸ hi)
  | succ rem ih =>
    intro idx x hsum _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 hword hentry
    have hidx_lt : idx < 2 ^ (2 * c) := by omega
    have hc_hold : (Cond.lt (2 : Fin 240) 3).Holds x := by
      simp [Cond.Holds, h2, h3, hidx_lt]
    obtain ⟨hu_lt, hv_lt, huv_eq, hprev_le, hprev_lt, hprev_zero, hprev_u, hprev_v⟩ :=
      clmulTab_index_props hidx_lt
    set u := idx >>> c with hu
    set v := idx &&& (2 ^ c - 1) with hv
    set prevIdx := (u <<< c) + (v >>> 1) with hprevIdx
    set wIdx := idx >>> p with hwIdx
    set subIdx := idx &&& (2 ^ p - 1) with hsubIdx
    set sh := subIdx * (2 * c) with hsh
    set prevWIdx := prevIdx >>> p with hprevWIdx
    set prevSub := prevIdx &&& (2 ^ p - 1) with hprevSub
    set prevSh := prevSub * (2 * c) with hprevSh
    have hwIdx_lt : wIdx < reducedTableWords t w := shiftRight_lt_reducedTableWords hidx_lt
    have hprevWIdx_le : prevWIdx ≤ wIdx := by
      dsimp only [prevWIdx, wIdx]
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
      exact Nat.div_le_div_right hprev_le
    have hprevWIdx_lt : prevWIdx < reducedTableWords t w := lt_of_le_of_lt hprevWIdx_le hwIdx_lt
    have hsub_lt : subIdx < 2 ^ p := by
      dsimp only [subIdx]
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos p)
    have hprevSub_lt : prevSub < 2 ^ p := by
      dsimp only [prevSub]
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos p)
    have hsh_lt : sh < w := by
      dsimp only [sh]
      calc subIdx * (2 * c) < 2 ^ p * (2 * c) :=
            Nat.mul_lt_mul_of_pos_right hsub_lt (by omega)
        _ ≤ w := hpack_le
    have hprevSh_lt : prevSh < w := by
      dsimp only [prevSh]
      calc prevSub * (2 * c) < 2 ^ p * (2 * c) :=
            Nat.mul_lt_mul_of_pos_right hprevSub_lt (by omega)
        _ ≤ w := hpack_le
    have hpow_sh_lt : 2 ^ sh < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hsh_lt
    have hfit_2c : Fits w (2 ^ (2 * c)) := hpow_2c_lt
    have hpow_p_le : 2 ^ p ≤ 2 ^ (2 * c) := Nat.pow_le_pow_right two_pos (reducedPackShift_le t w)
    have hfit_subIdx : Fits w subIdx := (hsub_lt.trans_le hpow_p_le).trans hpow_2c_lt
    have hfit_sh : Fits w sh := hsh_lt.trans Nat.lt_two_pow_self
    have hfit_pow_sh : Fits w (1 <<< sh) := by
      rw [Nat.shiftLeft_eq, one_mul]
      exact hpow_sh_lt
    set oldWord := x.mem (tBase + wIdx) with holdWord
    set maskedWord := oldWord &&& ((1 <<< sh) - 1) with hmaskedWord
    have hmasked_lt : maskedWord < 2 ^ sh := by
      dsimp only [maskedWord]
      rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos sh)
    have hfit_masked : Fits w maskedWord := hmasked_lt.trans hpow_sh_lt
    have hpow_c_le : 2 ^ c ≤ 2 ^ (2 * c) := Nat.pow_le_pow_right two_pos (by omega)
    have hfit_v : Fits w v := by fits
    have hfit_prevSub : Fits w prevSub := (hprevSub_lt.trans_le hpow_p_le).trans hpow_2c_lt
    have hfit_prevSh : Fits w prevSh := hprevSh_lt.trans Nat.lt_two_pow_self
    have hprev_val_lt : clmul u (v >>> 1) < 2 ^ (2 * c - 1) := by
      have hv_shr_lt : v >>> 1 < 2 ^ (c - 1) := by
        rw [Nat.shiftRight_eq_div_pow, pow_one]
        apply Nat.div_lt_of_lt_mul
        rwa [← pow_succ', Nat.sub_add_cancel hc_pos]
      have hlt := clmul_lt_two_pow hu_lt hv_shr_lt
      rwa [show c + (c - 1) = 2 * c - 1 by omega] at hlt
    have hcl_sh1_lt : clmul u (v >>> 1) <<< 1 < 2 ^ (2 * c) := by
      rw [Nat.shiftLeft_eq, pow_one]
      have hpow_split : 2 ^ (2 * c) = 2 ^ (2 * c - 1) * 2 := by
        conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ 2 * c by omega), pow_succ]
      omega
    have hfit_vbit : Fits w (v &&& 1) := hfit_v.of_le Nat.and_le_left
    have hbit_le : (v &&& 1) * u ≤ u := by
      calc (v &&& 1) * u ≤ 1 * u := Nat.mul_le_mul_right u Nat.and_le_right
        _ = u := Nat.one_mul u
    have hval_lt : clmul u v < 2 ^ (2 * c) := clmul_lt_two_pow_two_mul hu_lt hv_lt
    have hval_sh_lt : clmul u v <<< sh < 2 ^ ((subIdx + 1) * (2 * c)) := by
      rw [Nat.shiftLeft_eq, Nat.succ_mul, pow_add, mul_comm]
      exact Nat.mul_lt_mul_of_pos_left hval_lt (Nat.two_pow_pos sh)
    have hsub1_le : (subIdx + 1) * (2 * c) ≤ 2 ^ p * (2 * c) :=
      Nat.mul_le_mul_right _ hsub_lt
    have hpow_sub1_le : 2 ^ ((subIdx + 1) * (2 * c)) ≤ 2 ^ (2 ^ p * (2 * c)) :=
      Nat.pow_le_pow_right two_pos hsub1_le
    have hfit_val_sh : Fits w (clmul u v <<< sh) :=
      (hval_sh_lt.trans_le hpow_sub1_le).trans_le hpow_pack_le
    set newWord := maskedWord ^^^ (clmul u v <<< sh) with hnewWord
    have hnewWord_lt : newWord < 2 ^ ((subIdx + 1) * (2 * c)) :=
      xor_shiftLeft_lt_two_pow hmasked_lt hval_lt
    have hnewWord_pack_lt : newWord < 2 ^ (2 ^ p * (2 * c)) :=
      hnewWord_lt.trans_le hpow_sub1_le
    have hfit_newWord : Fits w newWord := hnewWord_pack_lt.trans_le hpow_pack_le
    set prevWord := (((((((((x.set 10 wIdx).set 10 (tBase + wIdx)).set 11 subIdx).set 11 sh).set
      12 (1 <<< sh)).set 12 ((1 <<< sh) - 1)).set 13 oldWord).set 13 maskedWord).write
      (tBase + wIdx) maskedWord).mem (tBase + prevWIdx) with hprevWord
    have hprevWord_lt : prevWord < 2 ^ (2 ^ p * (2 * c)) := by
      dsimp only [prevWord, Data.write, Data.set]
      rcases eq_or_lt_of_le hprevWIdx_le with heq | hlt
      · rw [heq, Function.update_self]
        exact hmasked_lt.trans_le
          (Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_right _ (le_of_lt hsub_lt)))
      · rw [Function.update_of_ne (by omega)]
        exact hword prevWIdx hlt
    have hprevWord_shr_lt : prevWord >>> prevSh < 2 ^ w :=
      ((Nat.shiftRight_le prevWord prevSh).trans_lt hprevWord_lt).trans_le hpow_pack_le
    have hfit_prevWord_shr : Fits w (prevWord >>> prevSh) := hprevWord_shr_lt
    have hprevWord_limb : (prevWord >>> prevSh) &&& (2 ^ (2 * c) - 1) = clmul u (v >>> 1) := by
      change getLimb (2 * c) prevWord prevSub = clmul u (v >>> 1)
      dsimp only [prevWord, Data.write, Data.set]
      have hmask_eq : (1 <<< sh) - 1 = 2 ^ (subIdx * (2 * c)) - 1 := by
        rw [Nat.shiftLeft_eq, one_mul]
      by_cases hv0 : v = 0
      · have hpeq : prevIdx = idx := hprev_zero hv0
        have hv_shr0 : v >>> 1 = 0 := by rw [hv0]; rfl
        have hw_eq : prevWIdx = wIdx := by dsimp only [prevWIdx, wIdx]; rw [hpeq]
        have hs_eq : prevSub = subIdx := by dsimp only [prevSub, subIdx]; rw [hpeq]
        rw [hw_eq, hs_eq, Function.update_self, hv_shr0, clmul_zero_right]
        dsimp only [maskedWord]
        rw [hmask_eq]
        exact getLimb_and_self (2 * c) oldWord subIdx
      · have hplt : prevIdx < idx := hprev_lt hv0
        rcases eq_or_ne prevWIdx wIdx with hw_eq | hw_ne
        · rw [hw_eq, Function.update_self]
          dsimp only [maskedWord, oldWord]
          rw [hmask_eq]
          have hsub_lt_prev : prevSub < subIdx :=
            and_lt_of_lt_of_shiftRight_eq hplt hw_eq
          rw [getLimb_and_low hsub_lt_prev, ← hw_eq, hentry prevIdx hplt, hprev_u, hprev_v]
        · rw [Function.update_of_ne (by omega), hentry prevIdx hplt, hprev_u, hprev_v]
    have hword' : ∀ w' < (idx + 1) >>> p,
        Function.update x.mem (tBase + wIdx) newWord (tBase + w') < 2 ^ (2 ^ p * (2 * c)) := by
      intro w' hw'
      have hw'_le : w' ≤ wIdx := by
        have := shiftRight_add_one_le idx p
        dsimp only [wIdx]
        omega
      rcases eq_or_lt_of_le hw'_le with rfl | hlt
      · rw [Function.update_self]
        exact hnewWord_pack_lt
      · rw [Function.update_of_ne (by omega)]
        exact hword w' hlt
    have hentry' : ∀ i < idx + 1,
        getLimb (2 * c) (Function.update x.mem (tBase + wIdx) newWord (tBase + (i >>> p)))
          (i &&& (2 ^ p - 1)) =
          clmul (i >>> c) (i &&& (2 ^ c - 1)) := by
      intro i hi
      have hmask_eq : (1 <<< sh) - 1 = 2 ^ (subIdx * (2 * c)) - 1 := by
        rw [Nat.shiftLeft_eq, one_mul]
      rcases eq_or_ne i idx with rfl | hne
      · change getLimb (2 * c)
            (Function.update x.mem (tBase + wIdx) newWord (tBase + wIdx)) subIdx = clmul u v
        rw [Function.update_self]
        dsimp only [newWord, sh]
        exact getLimb_xor_shiftLeft_self hmasked_lt hval_lt
      · have hilt : i < idx := by omega
        rcases eq_or_ne (i >>> p) wIdx with hw_eq | hw_ne
        · rw [hw_eq, Function.update_self]
          have hsub_lt_i : i &&& (2 ^ p - 1) < subIdx :=
            and_lt_of_lt_of_shiftRight_eq hilt hw_eq
          dsimp only [newWord, maskedWord, oldWord, sh]
          rw [hmask_eq, getLimb_xor_shiftLeft_of_ne hval_lt (ne_of_lt hsub_lt_i),
            getLimb_and_low hsub_lt_i, ← hw_eq, hentry i hilt]
        · rw [Function.update_of_ne (by omega)]
          exact hentry i hilt
    have hsh_le : wIdx ≤ (idx + 1) >>> p := by
      change idx >>> p ≤ (idx + 1) >>> p
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
      exact Nat.div_le_div_right (Nat.le_succ idx)
    have hbody : WP.Exact w clmulTabBody x fun z n => n = 29 ∧
        ∃ y, Exec w clmulTabLoop z y (31 * rem + 2) ∧ y.regs 0 = x.regs 0 ∧
          (∀ wIdx < reducedTableWords t w, y.mem (tBase + wIdx) < 2 ^ (2 ^ p * (2 * c))) ∧
          (∀ i < 2 ^ (2 * c),
            getLimb (2 * c) (y.mem (tBase + (i >>> p))) (i &&& (2 ^ p - 1)) =
              clmul (i >>> c) (i &&& (2 ^ c - 1))) ∧
          ∀ a, (a < tBase + wIdx ∨ tBase + reducedTableWords t w ≤ a) →
            y.mem a = x.mem a := by
      unfold clmulTabBody
      wram_exec [h1, h2, h4, h5, h6, h7, h8, h9, h18, ← hu, ← hv, ← hprevIdx, ← hwIdx,
        ← hsubIdx, ← hsh, ← hprevWIdx, ← hprevSub, ← hprevSh, ← holdWord, ← hmaskedWord,
        ← hnewWord, ← hprevWord, hprevWord_limb, clmul_eq_bit_mul_xor]
      exact (ih (idx + 1) _ (by omega) rfl (by wram_simp [h1]) (by wram_simp) (by wram_simp [h3])
        (by wram_simp [h4]) (by wram_simp [h5]) (by wram_simp [h6]) (by wram_simp [h7])
        (by wram_simp [h8]) (by wram_simp [h9]) (by wram_simp [h18])
        (by simp only [Data.set_mem, Data.write_mem, Function.update_idem]; exact hword')
        (by simp only [Data.set_mem, Data.write_mem, Function.update_idem]; exact hentry')).elim
        fun y ⟨hrec, hy0, hyword, hyentry, hyout⟩ =>
        ⟨y, hrec, hy0.trans (by wram_simp), hyword, hyentry, fun a ha => by
          rw [hyout a (by omega)]
          wram_simp⟩
    obtain ⟨z, n, hb, rfl, y, hrec, hy⟩ := hbody
    refine ⟨y, ?_, hy⟩
    simpa only [clmulTabLoop, show 29 + (31 * rem + 2) + 2 = 31 * (rem + 1) + 2 by omega] using
      Exec.loop_iter hc_hold hb hrec

/-- **Deterministic execution of `initTableCode w w₀ b b' k`**: establishes `TableRep`, preserves
`reg 0 = base`, and modifies only `[tabBase base w₀ b b' k, base + space w w₀ b b' k)`. -/
theorem initTableCode_exec {w base w₀ b b' k : ℕ} {x : Data 240}
    (hbase : x.regs 0 = base)
    (hc : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') ≤ w)
    (hfit_space : Fits w (base + space w w₀ b b' k)) :
    ∃ y : Data 240,
      Exec w (initTableCode w w₀ b b' k) x y (initTableSteps w₀ b b') ∧
      y.regs 0 = base ∧
      TableRep base w w₀ b b' k y.mem ∧
      (∀ a, (a < tabBase base w₀ b b' k ∨ base + space w w₀ b b' k ≤ a) → y.mem a = x.mem a) := by
  set t := reducedTrinomialStep w₀ b b' with ht
  set c := reducedChunkBits t with hc_def
  set p := reducedPackShift t w with hp_def
  set s := seedWords w₀ b b' k with hs
  have hc_lt : 2 * c < w := two_mul_reducedChunkBits_lt_of_fits_space hc hfit_space
  have hpow_2c_lt : 2 ^ (2 * c) < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hc_lt
  have hfit_2c : Fits w (2 ^ (2 * c)) := hpow_2c_lt
  have hfit_s : Fits w s := hfit_space.of_le (by dsimp only [space]; omega)
  have hfit_tBase : Fits w (base + s) := hfit_space.of_le (by dsimp only [space]; omega)
  have hfit_c : Fits w c :=
    hfit_2c.of_le (le_of_lt (Nat.lt_of_le_of_lt (by omega) Nat.lt_two_pow_self))
  have hfit_mask_c : Fits w (2 ^ c - 1) :=
    hfit_2c.of_le ((Nat.sub_le _ _).trans (Nat.pow_le_pow_right two_pos (by omega)))
  have hp_le : p ≤ 2 * c := reducedPackShift_le t w
  have hfit_p : Fits w p := hfit_2c.of_le (hp_le.trans (le_of_lt Nat.lt_two_pow_self))
  have hfit_mask_p : Fits w (2 ^ p - 1) :=
    hfit_2c.of_le ((Nat.sub_le _ _).trans (Nat.pow_le_pow_right two_pos hp_le))
  have hfit_2c_val : Fits w (2 * c) := hfit_2c.of_le (le_of_lt Nat.lt_two_pow_self)
  have hfit_end : Fits w (tabBase base w₀ b b' k + reducedTableWords t w) := by
    simpa only [tabBase, space, tableWords, Nat.add_assoc] using hfit_space
  unfold initTableCode initTableSetupCode
  wram_exec [hbase, ← ht, ← hc_def, ← hp_def, ← hs]
  wram_call (clmulTabLoop_exec (tBase := tabBase base w₀ b b' k) (t := t) hc_lt hfit_end
    (2 ^ (2 * c)) 0 _ (Nat.zero_add _) rfl (by wram_simp [tabBase, s]) (by wram_simp)
    (by wram_simp [c, t]) (by wram_simp [c, t]) (by wram_simp [c, t]) (by wram_simp)
    (by wram_simp [p, t]) (by wram_simp [p, t]) (by wram_simp [c, t]) (by wram_simp [c, t])
    (by intro _ h; simp at h) (by intro _ h; omega))
    with y ⟨hy0, hyword, hyentry, hyout⟩
  refine ⟨by simp only [initTableSteps, c, t], hy0.trans (by wram_simp [hbase]),
    ⟨hyword, hyentry⟩, fun a ha => hyout a ?_⟩
  simp only [Nat.zero_shiftRight, Nat.add_zero]
  dsimp only [space, tableWords, tabBase, t] at ha ⊢
  omega

/-- `ExecWithin` corollary of `initTableCode_exec`. -/
theorem initTableCode_execWithin {w base w₀ b b' k : ℕ} {x : Data 240}
    (hbase : x.regs 0 = base)
    (hc : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') ≤ w)
    (hfit_space : Fits w (base + space w w₀ b b' k)) :
    ∃ y : Data 240,
      ExecWithin w (initTableCode w w₀ b b' k) x y (initTableSteps w₀ b b') ∧
      y.regs 0 = base ∧
      TableRep base w w₀ b b' k y.mem ∧
      (∀ a, (a < tabBase base w₀ b b' k ∨ base + space w w₀ b b' k ≤ a) → y.mem a = x.mem a) := by
  obtain ⟨y, hex, hy0, htab, hmod⟩ := initTableCode_exec hbase hc hfit_space
  exact ⟨y, hex.within, hy0, htab, hmod⟩

/-! ## Section 3: Exact uniform seed resampling (`resampleCode`) -/

/-- 5-instruction setup for the top-seed `Tabulation.randFillLoop` call on `Data 240`. -/
@[expose] def resampleSetup1Code (w₀ : ℕ) : Code .exact 240 :=
  .seq (.op (.copy 3 0))
  (.seq (.op (.const 4 1))
  (.seq (.op (.exactBin .add 4 0 4))
  (.seq (.op (.const 5 (2 ^ (w₀ - 1) - 1)))
        (.op (.const 6 1)))))

/-- State after `resampleSetup1Code w₀`. -/
@[expose] def resampleSetup1Data (base w₀ : ℕ) (x : Data 240) : Data 240 :=
  ((((x.set 3 base).set 4 1).set 4 (base + 1)).set 5 (2 ^ (w₀ - 1) - 1)).set 6 1

/-- 4-instruction setup for the bottom-seed `Tabulation.randFillLoop` call on `Data 240`. -/
@[expose] def resampleSetup2Code (w₀ b b' k : ℕ) : Code .exact 240 :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let L := reducedLimbCount t
  .seq (.op (.copy 3 4))
  (.seq (.op (.const 5 (k * L)))
  (.seq (.op (.exactBin .add 4 4 5))
        (.op (.const 5 (2 ^ c - 1)))))

/-- State after `resampleSetup2Code w₀ b b' k`. -/
@[expose] def resampleSetup2Data (base w₀ b b' k : ℕ) (x : Data 240) : Data 240 :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let L := reducedLimbCount t
  (((x.set 3 (base + 1)).set 5 (k * L)).set 4 (base + 1 + k * L)).set 5 (2 ^ c - 1)

/-- Structured Word-RAM program on `Data 240` that resamples both `α` and `β` via two sequential
`Tabulation.randFillLoop` calls. -/
@[expose] def resampleCode (w₀ b b' k : ℕ) : Code .exact 240 :=
  .seq (resampleSetup1Code w₀)
  (.seq (Tabulation.randFillLoop.rename fillMap240)
  (.seq (resampleSetup2Code w₀ b b' k)
        (Tabulation.randFillLoop.rename fillMap240)))

/-- Exact instruction count `5 * seedWords w₀ b b' k + 13` of `resampleCode w₀ b b' k`. -/
@[expose] def resampleSteps (w₀ b b' k : ℕ) : ℕ :=
  5 * seedWords w₀ b b' k + 13

/-- Explicit `ProbComp (Data 240 × ℕ)` induced by `resampleCode w₀ b b' k`. -/
@[expose] noncomputable def resampleComp (base w₀ b b' k : ℕ) (x : Data 240) :
    ProbComp (Data 240 × ℕ) := do
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let L := reducedLimbCount t
  let x1 := resampleSetup1Data base w₀ x
  let z1 ← Tabulation.randFillComp (w₀ - 1) base 1 (x1.comap fillMap240)
  let x2 := resampleSetup2Data base w₀ b b' k (z1.1.extend fillMap240 x1)
  let z2 ← Tabulation.randFillComp c (base + 1) (k * L) (x2.comap fillMap240)
  pure (z2.1.extend fillMap240 x2, 5 + (z1.2 + (4 + z2.2)))

private theorem resampleSetup1Code_exec {w base w₀ : ℕ} {x : Data 240}
    (hbase : x.regs 0 = base)
    (hfit_top : Fits w (base + 1))
    (hfit_mask_top : Fits w (2 ^ (w₀ - 1) - 1)) :
    Exec w (resampleSetup1Code w₀) x (resampleSetup1Data base w₀ x) 5 := by
  unfold resampleSetup1Code resampleSetup1Data
  wram_exec [hbase]

private theorem resampleSetup2Code_exec {w base w₀ b b' k : ℕ} {x : Data 240}
    (h4 : x.regs 4 = base + 1)
    (hfit_end : Fits w (base + 1 + k * reducedLimbCount (reducedTrinomialStep w₀ b b')))
    (hfit_mask_c : Fits w (2 ^ reducedChunkBits (reducedTrinomialStep w₀ b b') - 1)) :
    Exec w (resampleSetup2Code w₀ b b' k) x (resampleSetup2Data base w₀ b b' k x) 4 := by
  unfold resampleSetup2Code resampleSetup2Data
  wram_exec [h4]

/-- **Exact `ExecRand` execution of `resampleCode w₀ b b' k`**. -/
theorem resampleCode_execRand {w base w₀ b b' k : ℕ} {x : Data 240}
    (hbase : x.regs 0 = base)
    (hw₀ : w₀ ≤ w)
    (hc : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') ≤ w)
    (hfit_space : Fits w (base + space w w₀ b b' k)) :
    ExecRand w (resampleCode w₀ b b' k) x (resampleComp base w₀ b b' k x) := by
  set t := reducedTrinomialStep w₀ b b'
  set c := reducedChunkBits t
  set L := reducedLimbCount t
  have hfit_end : Fits w (base + 1 + k * L) :=
    hfit_space.of_le (by dsimp only [space, seedWords, L, t]; omega)
  have hfit_top : Fits w (base + 1) := by fits
  have hfit_mask_top : Fits w (2 ^ (w₀ - 1) - 1) :=
    (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans_le (Nat.pow_le_pow_right two_pos (by omega))
  have hfit_mask_c : Fits w (2 ^ c - 1) :=
    (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans_le (Nat.pow_le_pow_right two_pos (by omega))
  set x1 := resampleSetup1Data base w₀ x
  have h1 := (resampleSetup1Code_exec hbase hfit_top hfit_mask_top).execRand
  have hloop1_inner := Tabulation.randFillLoop_execRand (w := w) (bits := w₀ - 1) (arrBase := base)
    1 (x := x1.comap fillMap240)
    (by simp +decide [x1, resampleSetup1Data, fillMap240, Data.comap])
    (by simp +decide [x1, resampleSetup1Data, fillMap240, Data.comap])
    (by simp +decide [x1, resampleSetup1Data, fillMap240, Data.comap])
    (by simp +decide [x1, resampleSetup1Data, fillMap240, Data.comap])
    hfit_top hfit_mask_top
  have hloop1 := hloop1_inner.rename injective_fillMap240
  have hrest : ∀ z1 ∈ (Tabulation.randFillComp (w₀ - 1) base 1
      (x1.comap fillMap240)).support,
      ExecRand w (.seq (resampleSetup2Code w₀ b b' k) (Tabulation.randFillLoop.rename fillMap240))
        (z1.1.extend fillMap240 x1) (do
          let x2 := resampleSetup2Data base w₀ b b' k (z1.1.extend fillMap240 x1)
          let z2 ← Tabulation.randFillComp c (base + 1) (k * L) (x2.comap fillMap240)
          pure (z2.1.extend fillMap240 x2, 4 + z2.2)) := by
    intro z1 hz1
    obtain ⟨_, _, hend1, _, hone1, _, _, _⟩ := Tabulation.mem_support_randFillComp hz1
    set y1 := z1.1.extend fillMap240 x1
    have hy1_4 : y1.regs 4 = base + 1 := by
      change (y1.comap fillMap240).regs Tabulation.regEnd = base + 1
      rw [Data.comap_extend injective_fillMap240, hend1]
      simp +decide [x1, resampleSetup1Data, fillMap240, Data.comap]
    have hy1_6 : y1.regs 6 = 1 := by
      change (y1.comap fillMap240).regs Tabulation.regOne = 1
      rw [Data.comap_extend injective_fillMap240, hone1]
      simp +decide [x1, resampleSetup1Data, fillMap240, Data.comap]
    set x2 := resampleSetup2Data base w₀ b b' k y1
    have h2 := (resampleSetup2Code_exec hy1_4 hfit_end hfit_mask_c).execRand
    have hloop2_inner := Tabulation.randFillLoop_execRand (w := w) (bits := c)
      (arrBase := base + 1) (k * L) (x := x2.comap fillMap240)
      (by simp +decide [x2, resampleSetup2Data, fillMap240, Data.comap])
      (by simp +decide [x2, resampleSetup2Data, fillMap240, Data.comap, L, t])
      (by simp +decide [x2, resampleSetup2Data, fillMap240, Data.comap, c, t])
      (by simp +decide [x2, resampleSetup2Data, fillMap240, Data.comap, hy1_6])
      hfit_end hfit_mask_c
    have hloop2 := hloop2_inner.rename injective_fillMap240
    have hseq2 := ExecRand.seq
      (m₂ := fun z : Data 240 =>
        (fun z2 : Data 6 × ℕ => (z2.1.extend fillMap240 z, z2.2)) <$>
          Tabulation.randFillComp c (base + 1) (k * L) (z.comap fillMap240))
      h2 (fun z hz => by
        cases OracleComp.eq_of_mem_supportWith_pure hz
        exact hloop2)
    simpa only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def] using hseq2
  have hseq12 := ExecRand.seq
    (m₂ := fun z : Data 240 => do
      let x2 := resampleSetup2Data base w₀ b b' k z
      let z2 ← Tabulation.randFillComp c (base + 1) (k * L) (x2.comap fillMap240)
      pure (z2.1.extend fillMap240 x2, 4 + z2.2))
    hloop1 (fun z hz => by
      obtain ⟨z1, hz1, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
      exact hrest z1 hz1)
  have hall := ExecRand.seq
    (m₂ := fun z : Data 240 => do
      let z1 ← Tabulation.randFillComp (w₀ - 1) base 1 (z.comap fillMap240)
      let x2 := resampleSetup2Data base w₀ b b' k (z1.1.extend fillMap240 z)
      let z2 ← Tabulation.randFillComp c (base + 1) (k * L) (x2.comap fillMap240)
      pure (z2.1.extend fillMap240 x2, z1.2 + (4 + z2.2)))
    h1 (fun z hz => by
      cases OracleComp.eq_of_mem_supportWith_pure hz
      simpa only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def] using hseq12)
  simpa only [resampleCode, resampleComp, bind_assoc, pure_bind, map_eq_bind_pure_comp,
    Function.comp_def] using hall

/-- Pathwise postcondition of `resampleComp`: executes in `resampleSteps w₀ b b' k` instructions,
preserves `reg 0 = base` and `TableRep`, establishes `SeedRep`, and modifies only
`[base, base + seedWords w₀ b b' k)`. -/
theorem mem_support_resampleComp {base w w₀ b b' k : ℕ} {x : Data 240}
    (hbase : x.regs 0 = base)
    (htab : TableRep base w w₀ b b' k x.mem)
    {z : Data 240 × ℕ}
    (hz : z ∈ (resampleComp base w₀ b b' k x).support) :
    z.1.regs 0 = base ∧
    TableRep base w w₀ b b' k z.1.mem ∧
    SeedRep base w₀ b b' k (extractSeed base w₀ b b' k z.1.mem) z.1.mem ∧
    (∀ a, (a < base ∨ base + seedWords w₀ b b' k ≤ a) → z.1.mem a = x.mem a) ∧
    z.2 = resampleSteps w₀ b b' k := by
  set t := reducedTrinomialStep w₀ b b'
  set c := reducedChunkBits t
  set L := reducedLimbCount t
  dsimp only [resampleComp] at hz
  obtain ⟨z1, hz1, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
  obtain ⟨z2, hz2, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
  cases OracleComp.eq_of_mem_supportWith_pure hpure
  obtain ⟨hsteps1, _, _, _, _, hextra1, hlt1, hframe1⟩ := Tabulation.mem_support_randFillComp hz1
  obtain ⟨hsteps2, _, _, _, _, hextra2, hlt2, hframe2⟩ := Tabulation.mem_support_randFillComp hz2
  set x1 := resampleSetup1Data base w₀ x
  set y1 := z1.1.extend fillMap240 x1
  set x2 := resampleSetup2Data base w₀ b b' k y1
  set y2 := z2.1.extend fillMap240 x2
  have hy1_0 : y1.regs 0 = base := by
    change (y1.comap fillMap240).regs Tabulation.regExtra = base
    rw [Data.comap_extend injective_fillMap240, hextra1]
    exact hbase
  have hy2_0 : y2.regs 0 = base := by
    change (y2.comap fillMap240).regs Tabulation.regExtra = base
    rw [Data.comap_extend injective_fillMap240, hextra2]
    exact hy1_0
  have hframe_all : ∀ a, (a < base ∨ base + seedWords w₀ b b' k ≤ a) →
      z2.1.mem a = x.mem a := by
    intro a ha
    have ha2 : a < base + 1 ∨ base + 1 + k * L ≤ a := by
      dsimp only [seedWords, L, t] at ha ⊢; omega
    have ha1 : a < base ∨ base + 1 ≤ a := by
      dsimp only [seedWords, L, t] at ha ⊢; omega
    rw [hframe2 a ha2]
    exact hframe1 a ha1
  have htab' : TableRep base w w₀ b b' k z2.1.mem := by
    obtain ⟨hw_old, he_old⟩ := htab
    refine ⟨fun wIdx hwIdx => ?_, fun idx hidx => ?_⟩
    · have ha : base + seedWords w₀ b b' k ≤ tabBase base w₀ b b' k + wIdx := by
        dsimp only [tabBase]; exact Nat.le_add_right _ _
      rw [hframe_all _ (Or.inr ha)]
      exact hw_old wIdx hwIdx
    · have ha : base + seedWords w₀ b b' k ≤
          tabBase base w₀ b b' k + (idx >>> reducedPackShift t w) := by
        dsimp only [tabBase]; exact Nat.le_add_right _ _
      rw [hframe_all _ (Or.inr ha)]
      exact he_old idx hidx
  refine ⟨hy2_0, htab', ⟨?_, ?_⟩, hframe_all, ?_⟩
  · have hm_eq : z2.1.mem base = z1.1.mem base :=
      hframe2 base (Or.inl (by omega))
    have hlt_val : z1.1.mem base < 2 ^ (w₀ - 1) := by
      simpa only [Nat.add_zero] using hlt1 0 Nat.one_pos
    change z2.1.mem base = (extractTop base w₀ z2.1.mem).val
    rw [extractTop_val, hm_eq, Tabulation.extractWord_val_of_lt hlt_val]
  · intro j m
    have hidx_lt : m.val + L * j.val < k * L := by
      calc m.val + L * j.val < L + L * j.val := Nat.add_lt_add_right m.isLt _
        _ = (j.val + 1) * L := by ring
        _ ≤ k * L := Nat.mul_le_mul_right L j.isLt
    have hlt_val : z2.1.mem (base + 1 + (m.val + L * j.val)) < 2 ^ c :=
      hlt2 (m.val + L * j.val) hidx_lt
    change z2.1.mem (base + 1 + (m.val + L * j.val)) =
      getLimb c (extractBot base w₀ b b' k z2.1.mem j).val m.val
    rw [getLimb_extractBot_val, Tabulation.extractWord_val_of_lt hlt_val]
  · dsimp only [resampleSteps, seedWords, L, t]
    rw [hsteps1, hsteps2]
    ring

/-- **Exact product uniformity of `resampleComp`**: `extractSeed base w₀ b b' k z.1.mem` under
`resampleComp base w₀ b b' k x` has distribution
`PMF.uniformOfFintype (ReducedPolySeed w₀ b b' k)`. -/
theorem map_extractSeed_eval_resampleComp (base w₀ b b' k : ℕ) (x : Data 240) :
    ((resampleComp base w₀ b b' k x).eval).map (fun z => extractSeed base w₀ b b' k z.1.mem) =
      PMF.uniformOfFintype (ReducedPolySeed w₀ b b' k) := by
  set t := reducedTrinomialStep w₀ b b'
  set c := reducedChunkBits t
  set L := reducedLimbCount t
  set x1 := resampleSetup1Data base w₀ x
  set m1 := Tabulation.randFillComp (w₀ - 1) base 1 (x1.comap fillMap240)
  have hm1_unif : m1.eval.map (fun z1 : Data 6 × ℕ => extractTop base w₀ z1.1.mem) =
      PMF.uniformOfFintype (ReducedTopSeed w₀) := by
    have hcomp : (fun z1 : Data 6 × ℕ => extractTop base w₀ z1.1.mem) =
        topSliceEquiv w₀ ∘
          fun z1 : Data 6 × ℕ => Tabulation.extractSlice base (w₀ - 1) 1 z1.1.mem := rfl
    rw [hcomp, ← PMF.map_comp, Tabulation.map_extractSlice_eval_randFillComp,
      PMF.uniformOfFintype_map_equiv]
  have hinner : ∀ z1 : Data 6 × ℕ,
      (let x2 := resampleSetup2Data base w₀ b b' k (z1.1.extend fillMap240 x1)
       (do
         let z2 ← Tabulation.randFillComp c (base + 1) (k * L) (x2.comap fillMap240)
         pure (z2.1.extend fillMap240 x2, 5 + (z1.2 + (4 + z2.2)))).eval).map
        (fun z : Data 240 × ℕ => extractSeed base w₀ b b' k z.1.mem) =
      (PMF.uniformOfFintype (ReducedBotSeed w₀ b b' k)).map
        (fun β => (extractTop base w₀ z1.1.mem, β)) := by
    intro z1
    dsimp only
    set x2 := resampleSetup2Data base w₀ b b' k (z1.1.extend fillMap240 x1)
    set m2 := Tabulation.randFillComp c (base + 1) (k * L) (x2.comap fillMap240)
    have hd : (do
        let z2 ← m2
        pure (z2.1.extend fillMap240 x2, 5 + (z1.2 + (4 + z2.2)))) =
        (fun z2 : Data 6 × ℕ => (z2.1.extend fillMap240 x2, 5 + (z1.2 + (4 + z2.2)))) <$> m2 :=
      bind_pure_comp _ _
    rw [hd, ProbComp.eval_map, PMF.map_comp]
    have hcongr :
        m2.eval.map
          ((fun z : Data 240 × ℕ => extractSeed base w₀ b b' k z.1.mem) ∘
            fun z2 : Data 6 × ℕ => (z2.1.extend fillMap240 x2, 5 + (z1.2 + (4 + z2.2)))) =
        m2.eval.map
          ((fun β => (extractTop base w₀ z1.1.mem, β)) ∘
            botSliceEquiv w₀ b b' k ∘
            fun z2 : Data 6 × ℕ =>
              Tabulation.extractSlice (base + 1) c (k * L) z2.1.mem) := by
      refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun z2 hz2 => ?_
      rw [ProbComp.support_eval] at hz2
      obtain ⟨_, _, _, _, _, _, _, hframe2⟩ := Tabulation.mem_support_randFillComp hz2
      have htop_eq : extractTop base w₀ z2.1.mem = extractTop base w₀ z1.1.mem := by
        dsimp only [extractTop]
        congr 1 with idx : 1
        dsimp only [Tabulation.extractSlice]
        rw [hframe2 (base + idx.val) (Or.inl (by have := idx.isLt; omega))]
        rfl
      dsimp only [Function.comp_apply, extractSeed, extractBot, Data.extend]
      rw [htop_eq]
    rw [hcongr, ← PMF.map_comp, ← PMF.map_comp, Tabulation.map_extractSlice_eval_randFillComp,
      PMF.uniformOfFintype_map_equiv]
  dsimp only [resampleComp]
  rw [ProbComp.eval_bind, PMF.map_bind]
  have hbind : m1.eval.bind
      (fun z1 =>
        (let x2 := resampleSetup2Data base w₀ b b' k (z1.1.extend fillMap240 x1)
         (do
           let z2 ← Tabulation.randFillComp c (base + 1) (k * L) (x2.comap fillMap240)
           pure (z2.1.extend fillMap240 x2, 5 + (z1.2 + (4 + z2.2)))).eval).map
          (fun z : Data 240 × ℕ => extractSeed base w₀ b b' k z.1.mem)) =
      m1.eval.bind
        (fun z1 =>
          (PMF.uniformOfFintype (ReducedBotSeed w₀ b b' k)).map
            (fun β => (extractTop base w₀ z1.1.mem, β))) := by
    congr 1 with z1 : 1
    exact hinner z1
  rw [hbind]
  have hmap_bind :
      m1.eval.bind
        (fun z1 =>
          (PMF.uniformOfFintype (ReducedBotSeed w₀ b b' k)).map
            (fun β => (extractTop base w₀ z1.1.mem, β))) =
      (m1.eval.map (fun z1 => extractTop base w₀ z1.1.mem)).bind
        (fun α => (PMF.uniformOfFintype (ReducedBotSeed w₀ b b' k)).map (α, ·)) := by
    rw [PMF.bind_map]
    rfl
  rw [hmap_bind, hm1_unif, PMF.uniformOfFintype_prod]

/-! ## Section 4: Word-RAM `evalCode` and deterministic execution -/

@[simp] private theorem data_set_self {regs : ℕ} (x : Data regs) (r : Fin regs) :
    x.set r (x.regs r) = x := by
  cases x
  simp [Data.set]

private theorem exec_copy_self (w : ℕ) (r : Fin 240) (x : Data 240) :
    Exec w (.op (.copy r r) : Code .exact 240) x x 1 := by
  simpa only [data_set_self] using (Exec.copy (B := .exact) (w := w) (d := r) (s := r) (x := x))

/-- Ascending sequential composition of `n` blocks `f 0, f 1, ..., f (n - 1)`. -/
@[expose] def seqAsc (f : ℕ → Code .exact 240) : ℕ → Code .exact 240
  | 0 => .op (.copy 0 0)
  | n + 1 => .seq (seqAsc f n) (f n)

private theorem seqAsc_exec {w : ℕ} (f : ℕ → Code .exact 240) (step : ℕ)
    (P : ℕ → Data 240 → Prop) (n : ℕ)
    (hstep : ∀ i < n, ∀ x : Data 240, P i x → ∃ y, Exec w (f i) x y step ∧ P (i + 1) y)
    {x : Data 240} (hx : P 0 x) :
    ∃ y, Exec w (seqAsc f n) x y (n * step + 1) ∧ P n y := by
  induction n with
  | zero =>
    rw [Nat.zero_mul, Nat.zero_add]
    exact ⟨x, exec_copy_self w 0 x, hx⟩
  | succ n ih =>
    obtain ⟨y, hy_exec, hy_P⟩ := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    obtain ⟨z, hz_exec, hz_P⟩ := hstep n (Nat.lt_succ_self n) y hy_P
    refine ⟨z, ?_, hz_P⟩
    rw [show (n + 1) * step + 1 = (n * step + 1) + step by ring]
    exact hy_exec.seq hz_exec

private theorem and_two_pow_sub_one_lt (a n : ℕ) : a &&& (2 ^ n - 1) < 2 ^ n := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt a (Nat.two_pow_pos n)

private theorem xReg_ne_low (m : ℕ) {r : Fin 240} (hr : r.val < 20) : xReg m ≠ r := by
  intro h; have := congrArg Fin.val h; dsimp only [xReg] at this; omega

private theorem accReg_ne_low (m : ℕ) {r : Fin 240} (hr : r.val < 20) : accReg m ≠ r := by
  intro h; have := congrArg Fin.val h; dsimp only [accReg] at this; omega

private theorem prodReg_ne_low (d : ℕ) {r : Fin 240} (hr : r.val < 20) : prodReg d ≠ r := by
  intro h; have := congrArg Fin.val h; dsimp only [prodReg] at this; omega

private theorem xReg_ne_accReg (m₁ m₂ : ℕ) : xReg m₁ ≠ accReg m₂ := by
  intro h; have := congrArg Fin.val h; dsimp only [xReg, accReg] at this; omega

private theorem xReg_ne_prodReg (m d : ℕ) : xReg m ≠ prodReg d := by
  intro h; have := congrArg Fin.val h; dsimp only [xReg, prodReg] at this; omega

private theorem accReg_ne_prodReg (m d : ℕ) : accReg m ≠ prodReg d := by
  intro h; have := congrArg Fin.val h; dsimp only [accReg, prodReg] at this; omega

private theorem xReg_ne_of_ne {m₁ m₂ : ℕ} (h1 : m₁ < 54) (h2 : m₂ < 54) (hne : m₁ ≠ m₂) :
    xReg m₁ ≠ xReg m₂ := by
  intro h; have := congrArg Fin.val h; dsimp only [xReg] at this; omega

private theorem accReg_ne_of_ne {m₁ m₂ : ℕ} (h1 : m₁ < 54) (h2 : m₂ < 54) (hne : m₁ ≠ m₂) :
    accReg m₁ ≠ accReg m₂ := by
  intro h; have := congrArg Fin.val h; dsimp only [accReg] at this; omega

private theorem prodReg_ne_of_ne {d₁ d₂ : ℕ} (h1 : d₁ < 108) (h2 : d₂ < 108) (hne : d₁ ≠ d₂) :
    prodReg d₁ ≠ prodReg d₂ := by
  intro h; have := congrArg Fin.val h; dsimp only [prodReg] at this; omega

/-- Part 1a of Stage 1 (`12` instructions): loads `α = x.mem (x.regs 0)`, sets half-width masks and
shifts in `regs 5..10`, and splits `α` and `x' = x.regs 1 &&& (2 ^ m - 1)` into `regs 12..15`. -/
@[expose] def halfMulSetupCode (m : ℕ) : Code .exact 240 :=
  let h := m / 2
  .seq (.op (.load 4 0))
  (.seq (.op (.const 5 (2 ^ m - 1)))
  (.seq (.op (.const 6 h))
  (.seq (.op (.const 7 (2 ^ h - 1)))
  (.seq (.op (.const 8 (2 ^ (m - h) - 1)))
  (.seq (.op (.const 9 (2 ^ (m - 2 * h) - 1)))
  (.seq (.op (.const 10 (2 * h)))
  (.seq (.op (.exactBin .and 11 1 5))
  (.seq (.op (.exactBin .and 12 4 7))
  (.seq (.op (.exactBin .shiftRight 13 4 6))
  (.seq (.op (.exactBin .and 14 11 7))
        (.op (.exactBin .shiftRight 15 11 6))))))))))))

/-- Part 1b of Stage 1 (`18` instructions): combines the half-words in `regs 12..15` into
`halfMulMod m α x'` in `reg 3`. -/
@[expose] def halfMulCombineCode : Code .exact 240 :=
  .seq (.op (.exactBin .mul 3 12 14))
  (.seq (.op (.exactBin .and 3 3 5))
  (.seq (.op (.exactBin .mul 16 12 15))
  (.seq (.op (.exactBin .and 16 16 8))
  (.seq (.op (.exactBin .shiftLeft 16 16 6))
  (.seq (.op (.exactBin .add 3 3 16))
  (.seq (.op (.exactBin .and 3 3 5))
  (.seq (.op (.exactBin .mul 16 13 14))
  (.seq (.op (.exactBin .and 16 16 8))
  (.seq (.op (.exactBin .shiftLeft 16 16 6))
  (.seq (.op (.exactBin .add 3 3 16))
  (.seq (.op (.exactBin .and 3 3 5))
  (.seq (.op (.exactBin .and 13 13 9))
  (.seq (.op (.exactBin .and 15 15 9))
  (.seq (.op (.exactBin .mul 16 13 15))
  (.seq (.op (.exactBin .shiftLeft 16 16 10))
  (.seq (.op (.exactBin .add 3 3 16))
        (.op (.exactBin .and 3 3 5))))))))))))))))))

/-- Part 1c of Stage 1 (`9` instructions): finishes `oddMulModWord w₀ α u` and shifts right by
`w₀ - min w₀ (3 * b)` into `reg 3`. -/
@[expose] def finishReduceCode (w₀ b : ℕ) : Code .exact 240 :=
  .seq (.op (.const 6 1))
  (.seq (.op (.exactBin .shiftRight 11 1 6))
  (.seq (.op (.exactBin .add 3 11 3))
  (.seq (.op (.exactBin .and 3 3 5))
  (.seq (.op (.exactBin .shiftLeft 3 3 6))
  (.seq (.op (.exactBin .and 11 1 6))
  (.seq (.op (.exactBin .add 3 11 3))
  (.seq (.op (.const 6 (w₀ - min w₀ (3 * b))))
        (.op (.exactBin .shiftRight 3 3 6)))))))))

/-- Stage 1 of `evalCode` (`39` instructions): computes the multiply-shift reduced key
`oddMulModWord w₀ α u >>> (w₀ - min w₀ (3 * b))` into `reg 3`. -/
@[expose] def reduceKeyCode (w₀ b : ℕ) : Code .exact 240 :=
  .seq (halfMulSetupCode (w₀ - 1))
  (.seq halfMulCombineCode (finishReduceCode w₀ b))

private theorem shiftRight_lt_pow_sub {m h a : ℕ} (hle : h ≤ m) (ha : a < 2 ^ m) :
    a >>> h < 2 ^ (m - h) := by
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.div_lt_of_lt_mul
  rw [← pow_add, Nat.add_sub_of_le hle]
  exact ha

private theorem halfMulSetupCode_exec {w m : ℕ} (hm : m < w) (x : Data 240)
    (hα : x.mem (x.regs 0) < 2 ^ m) :
    let h := m / 2
    let α := x.mem (x.regs 0)
    let x' := x.regs 1 &&& (2 ^ m - 1)
    ∃ y, Exec w (halfMulSetupCode m) x y 12 ∧
      y.regs 0 = x.regs 0 ∧
      y.regs 1 = x.regs 1 ∧
      y.regs 5 = 2 ^ m - 1 ∧
      y.regs 6 = h ∧
      y.regs 7 = 2 ^ h - 1 ∧
      y.regs 8 = 2 ^ (m - h) - 1 ∧
      y.regs 9 = 2 ^ (m - 2 * h) - 1 ∧
      y.regs 10 = 2 * h ∧
      y.regs 12 = α &&& (2 ^ h - 1) ∧
      y.regs 13 = α >>> h ∧
      y.regs 14 = x' &&& (2 ^ h - 1) ∧
      y.regs 15 = x' >>> h ∧
      y.mem = x.mem := by
  intro h α x'
  have hpow_m_lt : 2 ^ m < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hm
  have hfit_m : Fits w (2 ^ m) := hpow_m_lt
  have h_le : h ≤ m := Nat.div_le_self m 2
  have h2_le : 2 * h ≤ m := Nat.mul_div_le m 2
  have hm_lt_pow : m < 2 ^ m := Nat.lt_two_pow_self
  have hfit_mask_h : Fits w (2 ^ h - 1) :=
    hfit_m.of_le ((Nat.sub_le _ _).trans (Nat.pow_le_pow_right two_pos h_le))
  have hfit_mask_mh : Fits w (2 ^ (m - h) - 1) :=
    hfit_m.of_le ((Nat.sub_le _ _).trans (Nat.pow_le_pow_right two_pos (Nat.sub_le m h)))
  have hfit_mask_m2h : Fits w (2 ^ (m - 2 * h) - 1) :=
    hfit_m.of_le ((Nat.sub_le _ _).trans (Nat.pow_le_pow_right two_pos (Nat.sub_le m (2 * h))))
  have hx'_lt : x' < 2 ^ m := and_two_pow_sub_one_lt (x.regs 1) m
  have hfit_α0 : Fits w (α &&& (2 ^ h - 1)) :=
    hfit_m.of_le ((le_of_lt (and_two_pow_sub_one_lt α h)).trans (Nat.pow_le_pow_right two_pos h_le))
  have hfit_α1 : Fits w (α >>> h) :=
    hfit_m.of_le (( Nat.shiftRight_le α h).trans (le_of_lt hα))
  have hfit_x0 : Fits w (x' &&& (2 ^ h - 1)) :=
    hfit_m.of_le
      ((le_of_lt (and_two_pow_sub_one_lt x' h)).trans (Nat.pow_le_pow_right two_pos h_le))
  have hfit_x1 : Fits w (x' >>> h) :=
    hfit_m.of_le ((Nat.shiftRight_le x' h).trans (le_of_lt hx'_lt))
  simp only [h, α, x'] at *
  unfold halfMulSetupCode
  wram_exec
  wram_simp

private theorem halfMulCombineCode_exec {w m α x' : ℕ} (hm : m < w)
    (hα : α < 2 ^ m) (hx' : x' < 2 ^ m) (x : Data 240)
    (h5 : x.regs 5 = 2 ^ m - 1)
    (h6 : x.regs 6 = m / 2)
    (h8 : x.regs 8 = 2 ^ (m - m / 2) - 1)
    (h9 : x.regs 9 = 2 ^ (m - 2 * (m / 2)) - 1)
    (h10 : x.regs 10 = 2 * (m / 2))
    (h12 : x.regs 12 = α &&& (2 ^ (m / 2) - 1))
    (h13 : x.regs 13 = α >>> (m / 2))
    (h14 : x.regs 14 = x' &&& (2 ^ (m / 2) - 1))
    (h15 : x.regs 15 = x' >>> (m / 2)) :
    ∃ y, Exec w halfMulCombineCode x y 18 ∧
      y.regs 0 = x.regs 0 ∧
      y.regs 1 = x.regs 1 ∧
      y.regs 3 = halfMulMod m α x' ∧
      y.regs 5 = 2 ^ m - 1 ∧
      y.mem = x.mem := by
  set h := m / 2
  have h_le : h ≤ m := Nat.div_le_self m 2
  have h2_le : 2 * h ≤ m := Nat.mul_div_le m 2
  have hpow_m_le : 2 ^ m + 2 ^ m ≤ 2 ^ w := by
    have : 2 ^ (m + 1) ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hm
    rw [pow_succ'] at this
    linarith
  have hpow_m_lt : 2 ^ m < 2 ^ w := by linarith
  have hfit_m : Fits w (2 ^ m) := hpow_m_lt
  set α₀ := α &&& (2 ^ h - 1)
  set α₁ := α >>> h
  set x₀ := x' &&& (2 ^ h - 1)
  set x₁ := x' >>> h
  have hα0 : α₀ < 2 ^ h := and_two_pow_sub_one_lt α h
  have hα1 : α₁ < 2 ^ (m - h) := shiftRight_lt_pow_sub h_le hα
  have hx0 : x₀ < 2 ^ h := and_two_pow_sub_one_lt x' h
  have hx1 : x₁ < 2 ^ (m - h) := shiftRight_lt_pow_sub h_le hx'
  have hmul00 : α₀ * x₀ < 2 ^ m := by
    calc α₀ * x₀ < 2 ^ h * 2 ^ h := Nat.mul_lt_mul'' hα0 hx0
      _ = 2 ^ (2 * h) := by rw [← pow_add, two_mul]
      _ ≤ 2 ^ m := Nat.pow_le_pow_right two_pos h2_le
  have hmul01 : α₀ * x₁ < 2 ^ m := by
    calc α₀ * x₁ < 2 ^ h * 2 ^ (m - h) := Nat.mul_lt_mul'' hα0 hx1
      _ = 2 ^ m := by rw [← pow_add, Nat.add_sub_of_le h_le]
  have hmul10 : α₁ * x₀ < 2 ^ m := by
    calc α₁ * x₀ < 2 ^ (m - h) * 2 ^ h := Nat.mul_lt_mul'' hα1 hx0
      _ = 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel h_le]
  set p₀ := (α₀ * x₀) &&& (2 ^ m - 1) with hp₀
  set q₁ := (α₀ * x₁) &&& (2 ^ (m - h) - 1) with hq₁
  set p₁ := q₁ <<< h with hp₁
  set u₁ := (p₀ + p₁) &&& (2 ^ m - 1) with hu₁
  set q₂ := (α₁ * x₀) &&& (2 ^ (m - h) - 1) with hq₂
  set p₂ := q₂ <<< h with hp₂
  set u₂ := (u₁ + p₂) &&& (2 ^ m - 1) with hu₂
  set α₁' := α₁ &&& (2 ^ (m - 2 * h) - 1) with hα₁'
  set x₁' := x₁ &&& (2 ^ (m - 2 * h) - 1) with hx₁'
  set q₃ := α₁' * x₁' with hq₃
  set p₃ := q₃ <<< (2 * h) with hp₃
  set u₃ := (u₂ + p₃) &&& (2 ^ m - 1) with hu₃
  have hp0 : p₀ < 2 ^ m := and_two_pow_sub_one_lt _ m
  have hq1 : q₁ < 2 ^ (m - h) := and_two_pow_sub_one_lt _ (m - h)
  have hp1 : p₁ < 2 ^ m := by
    dsimp only [p₁]
    rw [Nat.shiftLeft_eq]
    calc q₁ * 2 ^ h < 2 ^ (m - h) * 2 ^ h := Nat.mul_lt_mul_of_pos_right hq1 (Nat.two_pow_pos h)
      _ = 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel h_le]
  have hu1 : u₁ < 2 ^ m := and_two_pow_sub_one_lt _ m
  have hq2 : q₂ < 2 ^ (m - h) := and_two_pow_sub_one_lt _ (m - h)
  have hp2 : p₂ < 2 ^ m := by
    dsimp only [p₂]
    rw [Nat.shiftLeft_eq]
    calc q₂ * 2 ^ h < 2 ^ (m - h) * 2 ^ h := Nat.mul_lt_mul_of_pos_right hq2 (Nat.two_pow_pos h)
      _ = 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel h_le]
  have hu2 : u₂ < 2 ^ m := and_two_pow_sub_one_lt _ m
  have hα1' : α₁' < 2 ^ (m - 2 * h) := and_two_pow_sub_one_lt _ (m - 2 * h)
  have hx1' : x₁' < 2 ^ (m - 2 * h) := and_two_pow_sub_one_lt _ (m - 2 * h)
  have hq3 : q₃ < 2 ^ (m - 2 * h) := by
    have hd : m - 2 * h ≤ 1 := by omega
    have hle1 : α₁' ≤ 1 := by
      have : α₁' < 2 ^ 1 := lt_of_lt_of_le hα1' (Nat.pow_le_pow_right two_pos hd)
      omega
    have : q₃ ≤ x₁' := by
      dsimp only [q₃]
      calc α₁' * x₁' ≤ 1 * x₁' := Nat.mul_le_mul_right x₁' hle1
        _ = x₁' := one_mul x₁'
    exact lt_of_le_of_lt this hx1'
  have hp3 : p₃ < 2 ^ m := by
    dsimp only [p₃]
    rw [Nat.shiftLeft_eq]
    calc q₃ * 2 ^ (2 * h)
        < 2 ^ (m - 2 * h) * 2 ^ (2 * h) :=
          Nat.mul_lt_mul_of_pos_right hq3 (Nat.two_pow_pos (2 * h))
      _ = 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel h2_le]
  have hu3 : u₃ < 2 ^ m := and_two_pow_sub_one_lt _ m
  have hpow_mh : 2 ^ (m - h) ≤ 2 ^ m := Nat.pow_le_pow_right two_pos (Nat.sub_le m h)
  have hpow_m2h : 2 ^ (m - 2 * h) ≤ 2 ^ m := Nat.pow_le_pow_right two_pos (Nat.sub_le m (2 * h))
  unfold halfMulCombineCode
  wram_exec [h5, h6, h8, h9, h10, h12, h13, h14, h15, ← hp₀, ← hq₁, ← hp₁, ← hu₁, ← hq₂, ← hp₂,
    ← hu₂, ← hα₁', ← hx₁', ← hq₃, ← hp₃, ← hu₃]
  wram_simp [h5, u₃, u₂, u₁, p₃, q₃, α₁', x₁', p₂, q₂, p₁, q₁, p₀, α₀, α₁, x₀, x₁, h, halfMulMod]

private theorem finishReduceCode_exec {w w₀ b α u : ℕ} (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w)
    (hu : u < 2 ^ w₀) (x : Data 240)
    (h1 : x.regs 1 = u)
    (h3 : x.regs 3 = halfMulMod (w₀ - 1) α (u &&& (2 ^ (w₀ - 1) - 1)))
    (h5 : x.regs 5 = 2 ^ (w₀ - 1) - 1) :
    ∃ y, Exec w (finishReduceCode w₀ b) x y 9 ∧
      y.regs 0 = x.regs 0 ∧
      y.regs 3 = oddMulModWord w₀ α u >>> (w₀ - min w₀ (3 * b)) ∧
      y.mem = x.mem := by
  set m := w₀ - 1
  have hm_eq : m + 1 = w₀ := Nat.sub_add_cancel hw₀_pos
  have hpow_w0_le : 2 ^ w₀ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hw₀
  have hpow_m_mul : 2 * 2 ^ m = 2 ^ w₀ := by rw [← pow_succ', hm_eq]
  have hfit_1 : Fits w 1 := by
    have : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right two_pos (by omega)
    change 1 < 2 ^ w; omega
  set p := halfMulMod m α (u &&& (2 ^ m - 1)) with hp
  have hp_lt : p < 2 ^ m := halfMulMod_lt m α _
  have hu_shr_lt : u >>> 1 < 2 ^ m := by
    have : m = w₀ - 1 := rfl
    rw [this]
    exact shiftRight_lt_pow_sub hw₀_pos hu
  have hadd_lt : (u >>> 1) + p < 2 ^ w₀ := by linarith
  set q := ((u >>> 1) + p) &&& (2 ^ m - 1) with hq
  have hq_lt : q < 2 ^ m := and_two_pow_sub_one_lt _ m
  have hq_shl_lt : q <<< 1 < 2 ^ w₀ := by
    rw [Nat.shiftLeft_eq, pow_one]
    linarith
  have hubit_lt : u &&& 1 < 2 ^ w₀ := by
    have : u &&& 1 < 2 ^ 1 := and_two_pow_sub_one_lt u 1
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right two_pos hw₀_pos)
  have hodd_lt : oddMulModWord w₀ α u < 2 ^ w₀ := oddMulModWord_lt hw₀_pos α u
  have hrem_shift_lt : w₀ - min w₀ (3 * b) < 2 ^ w := by
    calc w₀ - min w₀ (3 * b) ≤ w₀ := Nat.sub_le _ _
      _ ≤ w := hw₀
      _ < 2 ^ w := Nat.lt_two_pow_self
  have hres_lt : oddMulModWord w₀ α u >>> (w₀ - min w₀ (3 * b)) < 2 ^ w :=
    lt_of_le_of_lt (Nat.shiftRight_le _ _) (lt_of_lt_of_le hodd_lt hpow_w0_le)
  have hodd_eq : (u &&& 1) + (q <<< 1) = oddMulModWord w₀ α u := by
    simp [oddMulModWord, q, p, m]
  unfold finishReduceCode
  wram_exec [h1, h3, h5, ← hq, hodd_eq]
  wram_simp

/-- Stage 1 execution: computes
`oddMulModWord w₀ (x.mem (x.regs 0)) (x.regs 1) >>> (w₀ - min w₀ (3 * b))`
into `reg 3` in `39` steps, preserving `reg 0` and memory. -/
theorem reduceKeyCode_exec {w w₀ b : ℕ} (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (x : Data 240)
    (hα : x.mem (x.regs 0) < 2 ^ (w₀ - 1)) (hu : x.regs 1 < 2 ^ w₀) :
    ∃ y, Exec w (reduceKeyCode w₀ b) x y 39 ∧
      y.regs 0 = x.regs 0 ∧
      y.regs 3 = oddMulModWord w₀ (x.mem (x.regs 0)) (x.regs 1) >>> (w₀ - min w₀ (3 * b)) ∧
      y.mem = x.mem := by
  have hm : w₀ - 1 < w := by omega
  obtain ⟨y1, e1, hy1_0, hy1_1, hy1_5, hy1_6, _, hy1_8, hy1_9, hy1_10, hy1_12, hy1_13, hy1_14,
      hy1_15, hy1_mem⟩ := halfMulSetupCode_exec hm x hα
  have hx'_lt : x.regs 1 &&& (2 ^ (w₀ - 1) - 1) < 2 ^ (w₀ - 1) :=
    and_two_pow_sub_one_lt (x.regs 1) (w₀ - 1)
  obtain ⟨y2, e2, hy2_0, hy2_1, hy2_3, hy2_5, hy2_mem⟩ :=
    halfMulCombineCode_exec hm hα hx'_lt y1 hy1_5 hy1_6 hy1_8 hy1_9 hy1_10 hy1_12 hy1_13 hy1_14
      hy1_15
  obtain ⟨y3, e3, hy3_0, hy3_3, hy3_mem⟩ :=
    finishReduceCode_exec hw₀_pos hw₀ hu y2 (hy2_1.trans hy1_1) hy2_3 hy2_5
  refine ⟨y3, ?_, hy3_0.trans (hy2_0.trans hy1_0), hy3_3, hy3_mem.trans (hy2_mem.trans hy1_mem)⟩
  simpa only [reduceKeyCode] using e1.seq (e2.seq e3)

/-- Step `m` of Stage 2 (`5` instructions): extracts limb `m` of `r_val` from `reg 3` into `xReg m`,
shifts `reg 3` right by `c`, and zeroes `accReg m`. -/
@[expose] def initLimbStep (c m : ℕ) : Code .exact 240 :=
  .seq (.op (.const 10 c))
  (.seq (.op (.const 11 (2 ^ c - 1)))
  (.seq (.op (.exactBin .and (xReg m) 3 11))
  (.seq (.op (.exactBin .shiftRight 3 3 10))
        (.op (.const (accReg m) 0)))))

/-- Stage 2a of `evalCode`: extracts all `L` limbs of the reduced key into `xReg 0 .. xReg (L - 1)`
and zeroes `accReg 0 .. accReg (L - 1)`. -/
@[expose] def initLimbsCode (t : ℕ) : Code .exact 240 :=
  seqAsc (initLimbStep (reducedChunkBits t)) (reducedLimbCount t)

private theorem initLimbsCode_exec {w t r_val : ℕ} (hc_lt : 2 * reducedChunkBits t < w)
    (hr : r_val < 2 ^ w) (x : Data 240) (h3 : x.regs 3 = r_val) :
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    ∃ y, Exec w (initLimbsCode t) x y (L * 5 + 1) ∧
      y.regs 0 = x.regs 0 ∧
      (∀ m < L, y.regs (xReg m) = getLimb c r_val m) ∧
      (∀ m < L, y.regs (accReg m) = 0) ∧
      y.mem = x.mem := by
  intro c L
  have hL_le : L ≤ 54 := reducedLimbCount_le t
  have hpow_2c_lt : 2 ^ (2 * c) < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hc_lt
  have hfit_2c : Fits w (2 ^ (2 * c)) := hpow_2c_lt
  have hfit_c : Fits w c :=
    hfit_2c.of_le (le_of_lt (Nat.lt_of_le_of_lt (by omega) Nat.lt_two_pow_self))
  have hfit_mask_c : Fits w (2 ^ c - 1) :=
    hfit_2c.of_le ((Nat.sub_le _ _).trans (Nat.pow_le_pow_right two_pos (by omega)))
  let P (n : ℕ) (z : Data 240) : Prop :=
    z.regs 0 = x.regs 0 ∧
    z.regs 3 = r_val >>> (n * c) ∧
    (∀ m < n, z.regs (xReg m) = getLimb c r_val m) ∧
    (∀ m < n, z.regs (accReg m) = 0) ∧
    z.mem = x.mem
  have hP0 : P 0 x := by
    refine ⟨rfl, ?_, fun _ hm => (Nat.not_lt_zero _ hm).elim,
      fun _ hm => (Nat.not_lt_zero _ hm).elim, rfl⟩
    rw [Nat.zero_mul, Nat.shiftRight_zero, h3]
  obtain ⟨y, hy_exec, hy0, _, hyx, hya, hymem⟩ :=
    seqAsc_exec (initLimbStep c) 5 P L (fun i hi z ⟨hz0, hz3, hzx, hza, hzmem⟩ => by
      have hi54 : i < 54 := lt_of_lt_of_le hi hL_le
      have hfit_limb : Fits w (getLimb c r_val i) :=
        hfit_2c.of_le ((le_of_lt (getLimb_lt c r_val i)).trans
          (Nat.pow_le_pow_right two_pos (by omega)))
      have hfit_shr : Fits w (r_val >>> ((i + 1) * c)) :=
        lt_of_le_of_lt (Nat.shiftRight_le _ _) hr
      set s1 := z.set 10 c
      have e1 : Exec w (.op (.const 10 c) : Code .exact 240) z s1 1 := Exec.const hfit_c
      set s2 := s1.set 11 (2 ^ c - 1)
      have e2 : Exec w (.op (.const 11 (2 ^ c - 1)) : Code .exact 240) s1 s2 1 :=
        Exec.const hfit_mask_c
      set s3 := s2.set (xReg i) (getLimb c r_val i)
      have e3 : Exec w (.op (.exactBin .and (xReg i) 3 11) : Code .exact 240) s2 s3 1 :=
        exec_exactBin (by simp +decide [s2, s1, hz3, getLimb]) hfit_limb
      set s4 := s3.set 3 (r_val >>> ((i + 1) * c))
      have hshr_eq : (s3.regs 3) >>> (s3.regs 10) = r_val >>> ((i + 1) * c) := by
        have h3_s3 : s3.regs 3 = r_val >>> (i * c) := by
          dsimp only [s3, s2, s1, Data.set]
          rw [Function.update_of_ne (xReg_ne_low i (r := 3) (by decide)).symm]
          simp +decide [hz3]
        have h10_s3 : s3.regs 10 = c := by
          dsimp only [s3, s2, s1, Data.set]
          rw [Function.update_of_ne (xReg_ne_low i (r := 10) (by decide)).symm]
          simp +decide
        rw [h3_s3, h10_s3, ← Nat.shiftRight_add, ← Nat.succ_mul]
      have e4 : Exec w (.op (.exactBin .shiftRight 3 3 10) : Code .exact 240) s3 s4 1 :=
        exec_exactBin (by simp [hshr_eq]) hfit_shr
      set s5 := s4.set (accReg i) 0
      have e5 : Exec w (.op (.const (accReg i) 0) : Code .exact 240) s4 s5 1 := Exec.const (by fits)
      refine ⟨s5, e1.seq (e2.seq (e3.seq (e4.seq e5))), ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only [s5, s4, s3, s2, s1, Data.set]
        rw [Function.update_of_ne (accReg_ne_low i (r := 0) (by decide)).symm,
          Function.update_of_ne (by decide : (0 : Fin 240) ≠ 3),
          Function.update_of_ne (xReg_ne_low i (r := 0) (by decide)).symm,
          Function.update_of_ne (by decide : (0 : Fin 240) ≠ 11),
          Function.update_of_ne (by decide : (0 : Fin 240) ≠ 10), hz0]
      · dsimp only [s5, s4, Data.set]
        rw [Function.update_of_ne (accReg_ne_low i (r := 3) (by decide)).symm, Function.update_self]
      · intro m hm
        dsimp only [s5, s4, s3, s2, s1, Data.set]
        rw [Function.update_of_ne (xReg_ne_accReg m i),
          Function.update_of_ne (xReg_ne_low m (r := 3) (by decide))]
        rcases eq_or_ne m i with rfl | hne
        · exact Function.update_self _ _ _
        · have hm54 : m < 54 := by omega
          rw [Function.update_of_ne (xReg_ne_of_ne hm54 hi54 hne),
            Function.update_of_ne (xReg_ne_low m (r := 11) (by decide)),
            Function.update_of_ne (xReg_ne_low m (r := 10) (by decide))]
          exact hzx m (by omega)
      · intro m hm
        dsimp only [s5, s4, s3, s2, s1, Data.set]
        rcases eq_or_ne m i with rfl | hne
        · exact Function.update_self _ _ _
        · have hm54 : m < 54 := by omega
          rw [Function.update_of_ne (accReg_ne_of_ne hm54 hi54 hne),
            Function.update_of_ne (accReg_ne_low m (r := 3) (by decide)),
            Function.update_of_ne (xReg_ne_accReg i m).symm,
            Function.update_of_ne (accReg_ne_low m (r := 11) (by decide)),
            Function.update_of_ne (accReg_ne_low m (r := 10) (by decide))]
          exact hza m (by omega)
      · exact hzmem) hP0
  exact ⟨y, hy_exec, hy0, hyx, hya, hymem⟩

/-- Stage 2b of `evalCode` (`8` instructions): loads table/chunk constants into `regs 4..9` and
`reg 18`. -/
@[expose] def hornerSetupCode (w w₀ b b' k : ℕ) : Code .exact 240 :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let p := reducedPackShift t w
  .seq (.op (.const 4 (seedWords w₀ b b' k)))
  (.seq (.op (.exactBin .add 4 0 4))
  (.seq (.op (.const 5 c))
  (.seq (.op (.const 6 (2 ^ c - 1)))
  (.seq (.op (.const 7 p))
  (.seq (.op (.const 8 (2 ^ p - 1)))
  (.seq (.op (.const 9 (2 * c)))
        (.op (.const 18 (2 ^ (2 * c) - 1)))))))))

private theorem hornerSetupCode_exec {w base w₀ b b' k : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k))
    (x : Data 240) (h0 : x.regs 0 = base) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let p := reducedPackShift t w
    ∃ y, Exec w (hornerSetupCode w w₀ b b' k) x y 8 ∧
      y.regs 0 = base ∧
      y.regs 4 = tabBase base w₀ b b' k ∧
      y.regs 5 = c ∧
      y.regs 6 = 2 ^ c - 1 ∧
      y.regs 7 = p ∧
      y.regs 8 = 2 ^ p - 1 ∧
      y.regs 9 = 2 * c ∧
      y.regs 18 = 2 ^ (2 * c) - 1 ∧
      (∀ r : Fin 240, 20 ≤ r.val → y.regs r = x.regs r) ∧
      y.mem = x.mem := by
  intro t c p
  have hpow_2c_lt : 2 ^ (2 * c) < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hc_lt
  have hfit_2c : Fits w (2 ^ (2 * c)) := hpow_2c_lt
  have hfit_s : Fits w (seedWords w₀ b b' k) := hfit_space.of_le (by dsimp only [space]; omega)
  have hfit_tBase : Fits w (tabBase base w₀ b b' k) :=
    hfit_space.of_le (by dsimp only [tabBase, space]; omega)
  have hfit_c : Fits w c :=
    hfit_2c.of_le (le_of_lt (Nat.lt_of_le_of_lt (by omega) Nat.lt_two_pow_self))
  have hfit_mask_c : Fits w (2 ^ c - 1) :=
    hfit_2c.of_le ((Nat.sub_le _ _).trans (Nat.pow_le_pow_right two_pos (by omega)))
  have hp_le : p ≤ 2 * c := reducedPackShift_le t w
  have hfit_p : Fits w p := hfit_2c.of_le (hp_le.trans (le_of_lt Nat.lt_two_pow_self))
  have hfit_mask_p : Fits w (2 ^ p - 1) :=
    hfit_2c.of_le ((Nat.sub_le _ _).trans (Nat.pow_le_pow_right two_pos hp_le))
  have hfit_2c_val : Fits w (2 * c) := hfit_2c.of_le (le_of_lt Nat.lt_two_pow_self)
  simp only [t, c, p] at *
  unfold hornerSetupCode
  wram_exec [h0, show base + seedWords w₀ b b' k = tabBase base w₀ b b' k from rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl⟩ <;> wram_simp [h0, t, c, p]

/-- Register invariant preserved across all Stage 3 Horner operations. -/
@[expose] def HornerConsts (base w w₀ b b' k r_val : ℕ) (x : Data 240) : Prop :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let p := reducedPackShift t w
  let L := reducedLimbCount t
  x.regs 0 = base ∧
  x.regs 4 = tabBase base w₀ b b' k ∧
  x.regs 5 = c ∧
  x.regs 6 = 2 ^ c - 1 ∧
  x.regs 7 = p ∧
  x.regs 8 = 2 ^ p - 1 ∧
  x.regs 9 = 2 * c ∧
  x.regs 18 = 2 ^ (2 * c) - 1 ∧
  ∀ m < L, x.regs (xReg m) = getLimb c r_val m

private theorem HornerConsts.set_scratch {base w w₀ b b' k r_val : ℕ} {x : Data 240}
    (hc : HornerConsts base w w₀ b b' k r_val x) {r : Fin 240}
    (hr1 : 10 ≤ r.val) (hr2 : r.val < 18) (v : ℕ) :
    HornerConsts base w w₀ b b' k r_val (x.set r v) := by
  obtain ⟨h0, h4, h5, h6, h7, h8, h9, h18, hx⟩ := hc
  have hne : ∀ s : Fin 240, (s.val < 10 ∨ s.val = 18) → s ≠ r := by
    intro s hs h; subst h; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun m hm => ?_⟩
  · dsimp only [Data.set]; rw [Function.update_of_ne (hne 0 (by decide))]; exact h0
  · dsimp only [Data.set]; rw [Function.update_of_ne (hne 4 (by decide))]; exact h4
  · dsimp only [Data.set]; rw [Function.update_of_ne (hne 5 (by decide))]; exact h5
  · dsimp only [Data.set]; rw [Function.update_of_ne (hne 6 (by decide))]; exact h6
  · dsimp only [Data.set]; rw [Function.update_of_ne (hne 7 (by decide))]; exact h7
  · dsimp only [Data.set]; rw [Function.update_of_ne (hne 8 (by decide))]; exact h8
  · dsimp only [Data.set]; rw [Function.update_of_ne (hne 9 (by decide))]; exact h9
  · dsimp only [Data.set]; rw [Function.update_of_ne (hne 18 (by decide))]; exact h18
  · dsimp only [Data.set]
    rw [Function.update_of_ne (xReg_ne_low m (by omega))]
    exact hx m hm

private theorem HornerConsts.set_prodReg {base w w₀ b b' k r_val : ℕ} {x : Data 240}
    (hc : HornerConsts base w w₀ b b' k r_val x) (d v : ℕ) :
    HornerConsts base w w₀ b b' k r_val (x.set (prodReg d) v) := by
  obtain ⟨h0, h4, h5, h6, h7, h8, h9, h18, hx⟩ := hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun m hm => ?_⟩
  · dsimp only [Data.set]; rw [Function.update_of_ne (prodReg_ne_low d (r := 0) (by decide)).symm]
    exact h0
  · dsimp only [Data.set]; rw [Function.update_of_ne (prodReg_ne_low d (r := 4) (by decide)).symm]
    exact h4
  · dsimp only [Data.set]; rw [Function.update_of_ne (prodReg_ne_low d (r := 5) (by decide)).symm]
    exact h5
  · dsimp only [Data.set]; rw [Function.update_of_ne (prodReg_ne_low d (r := 6) (by decide)).symm]
    exact h6
  · dsimp only [Data.set]; rw [Function.update_of_ne (prodReg_ne_low d (r := 7) (by decide)).symm]
    exact h7
  · dsimp only [Data.set]; rw [Function.update_of_ne (prodReg_ne_low d (r := 8) (by decide)).symm]
    exact h8
  · dsimp only [Data.set]; rw [Function.update_of_ne (prodReg_ne_low d (r := 9) (by decide)).symm]
    exact h9
  · dsimp only [Data.set]; rw [Function.update_of_ne (prodReg_ne_low d (r := 18) (by decide)).symm]
    exact h18
  · dsimp only [Data.set]; rw [Function.update_of_ne (xReg_ne_prodReg m d)]; exact hx m hm

private theorem HornerConsts.set_accReg {base w w₀ b b' k r_val : ℕ} {x : Data 240}
    (hc : HornerConsts base w w₀ b b' k r_val x) (m' v : ℕ) :
    HornerConsts base w w₀ b b' k r_val (x.set (accReg m') v) := by
  obtain ⟨h0, h4, h5, h6, h7, h8, h9, h18, hx⟩ := hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun m hm => ?_⟩
  · dsimp only [Data.set]; rw [Function.update_of_ne (accReg_ne_low m' (r := 0) (by decide)).symm]
    exact h0
  · dsimp only [Data.set]; rw [Function.update_of_ne (accReg_ne_low m' (r := 4) (by decide)).symm]
    exact h4
  · dsimp only [Data.set]; rw [Function.update_of_ne (accReg_ne_low m' (r := 5) (by decide)).symm]
    exact h5
  · dsimp only [Data.set]; rw [Function.update_of_ne (accReg_ne_low m' (r := 6) (by decide)).symm]
    exact h6
  · dsimp only [Data.set]; rw [Function.update_of_ne (accReg_ne_low m' (r := 7) (by decide)).symm]
    exact h7
  · dsimp only [Data.set]; rw [Function.update_of_ne (accReg_ne_low m' (r := 8) (by decide)).symm]
    exact h8
  · dsimp only [Data.set]; rw [Function.update_of_ne (accReg_ne_low m' (r := 9) (by decide)).symm]
    exact h9
  · dsimp only [Data.set]; rw [Function.update_of_ne (accReg_ne_low m' (r := 18) (by decide)).symm]
    exact h18
  · dsimp only [Data.set]; rw [Function.update_of_ne (xReg_ne_accReg m m')]; exact hx m hm

/-- Invariant combining `HornerConsts` and the current accumulator limbs in `accReg`. -/
@[expose] def ClmulInv (base w w₀ b b' k r_val acc_val : ℕ) (x : Data 240) : Prop :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let L := reducedLimbCount t
  HornerConsts base w w₀ b b' k r_val x ∧
  ∀ m < L, x.regs (accReg m) = getLimb c acc_val m

private theorem ClmulInv.set_scratch {base w w₀ b b' k r_val acc_val : ℕ} {x : Data 240}
    (h : ClmulInv base w w₀ b b' k r_val acc_val x) {r : Fin 240}
    (hr1 : 10 ≤ r.val) (hr2 : r.val < 18) (v : ℕ) :
    ClmulInv base w w₀ b b' k r_val acc_val (x.set r v) := by
  refine ⟨h.1.set_scratch hr1 hr2 v, fun m hm => ?_⟩
  dsimp only [Data.set]
  rw [Function.update_of_ne (accReg_ne_low m (by omega))]
  exact h.2 m hm

private theorem ClmulInv.set_prodReg {base w w₀ b b' k r_val acc_val : ℕ} {x : Data 240}
    (h : ClmulInv base w w₀ b b' k r_val acc_val x) (d v : ℕ) :
    ClmulInv base w w₀ b b' k r_val acc_val (x.set (prodReg d) v) := by
  refine ⟨h.1.set_prodReg d v, fun m hm => ?_⟩
  dsimp only [Data.set]
  rw [Function.update_of_ne (accReg_ne_prodReg m d)]
  exact h.2 m hm

/-- Zeroes `prodReg 0 .. prodReg (2 * L - 1)`. -/
@[expose] def zeroProdCode (L : ℕ) : Code .exact 240 :=
  seqAsc (fun d => .op (.const (prodReg d) 0)) (2 * L)

private theorem packLimbs_zero_fn (c n : ℕ) : packLimbs c n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [packLimbs, ih]

private theorem zeroProdCode_exec {base w w₀ b b' k r_val acc_val : ℕ}
    (x : Data 240) (hinv : ClmulInv base w w₀ b b' k r_val acc_val x) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    ∃ y, Exec w (zeroProdCode L) x y (2 * L * 1 + 1) ∧
      ClmulInv base w w₀ b b' k r_val acc_val y ∧
      (∀ d < 2 * L, y.regs (prodReg d) < 2 ^ c) ∧
      packLimbs c (2 * L) (fun d => y.regs (prodReg d)) = 0 ∧
      y.mem = x.mem := by
  intro t c L
  have hL_le : L ≤ 54 := reducedLimbCount_le t
  have hfit_0 : Fits w 0 := Nat.two_pow_pos w
  let P (n : ℕ) (z : Data 240) : Prop :=
    ClmulInv base w w₀ b b' k r_val acc_val z ∧
    (∀ d < n, z.regs (prodReg d) = 0) ∧
    z.mem = x.mem
  have hP0 : P 0 x := ⟨hinv, fun _ hd => (Nat.not_lt_zero _ hd).elim, rfl⟩
  obtain ⟨y, hy_exec, hy_inv, hy_zero, hy_mem⟩ :=
    seqAsc_exec (fun d => .op (.const (prodReg d) 0)) 1 P (2 * L)
      (fun i hi z ⟨hz_inv, hz_zero, hz_mem⟩ => by
        have hi108 : i < 108 := by omega
        set s1 := z.set (prodReg i) 0
        have e1 : Exec w (.op (.const (prodReg i) 0) : Code .exact 240) z s1 1 :=
          Exec.const hfit_0
        refine ⟨s1, e1, hz_inv.set_prodReg i 0, fun d hd => ?_, hz_mem⟩
        dsimp only [s1, Data.set]
        rcases eq_or_ne d i with rfl | hne
        · exact Function.update_self _ _ _
        · rw [Function.update_of_ne (prodReg_ne_of_ne (by omega) hi108 hne)]
          exact hz_zero d (by omega)) hP0
  refine ⟨y, hy_exec, hy_inv, fun d hd => ?_, ?_, hy_mem⟩
  · rw [hy_zero d hd]
    exact Nat.two_pow_pos c
  · rw [packLimbs_congr (g := fun _ => 0) hy_zero, packLimbs_zero_fn]

/-- Inner step `(i, m)` (`13` instructions): looks up `clmul (accLimb i) (xLimb m)` in the
bit-packed Four-Russians table and XORs its low and high `c`-bit halves into `prodReg (i + m)` and
`prodReg (i + m + 1)`. -/
@[expose] def innerClmulStep (i m : ℕ) : Code .exact 240 :=
  .seq (.op (.exactBin .shiftLeft 10 (accReg i) 5))
  (.seq (.op (.exactBin .add 10 10 (xReg m)))
  (.seq (.op (.exactBin .shiftRight 11 10 7))
  (.seq (.op (.exactBin .add 11 4 11))
  (.seq (.op (.load 12 11))
  (.seq (.op (.exactBin .and 11 10 8))
  (.seq (.op (.exactBin .mul 11 11 9))
  (.seq (.op (.exactBin .shiftRight 12 12 11))
  (.seq (.op (.exactBin .and 12 12 18))
  (.seq (.op (.exactBin .and 13 12 6))
  (.seq (.op (.exactBin .shiftRight 14 12 5))
  (.seq (.op (.exactBin .xor (prodReg (i + m)) (prodReg (i + m)) 13))
        (.op (.exactBin .xor (prodReg (i + m + 1)) (prodReg (i + m + 1)) 14)))))))))))))

/-- Row `i` of limb-by-limb carryless multiplication. -/
@[expose] def outerClmulStep (L i : ℕ) : Code .exact 240 :=
  seqAsc (innerClmulStep i) L

/-- Full `L × L` limb-by-limb carryless multiplication into `prodReg 0 .. prodReg (2 * L - 1)`. -/
@[expose] def clmulLimbsCode (L : ℕ) : Code .exact 240 :=
  seqAsc (outerClmulStep L) L

private theorem pair_index_props {c u v : ℕ} (hu : u < 2 ^ c) (hv : v < 2 ^ c) :
    (u <<< c) + v < 2 ^ (2 * c) ∧
    ((u <<< c) + v) >>> c = u ∧
    ((u <<< c) + v) &&& (2 ^ c - 1) = v := by
  have hpow : 0 < 2 ^ c := Nat.two_pow_pos c
  have hlt : (u <<< c) + v < 2 ^ (2 * c) := by
    rw [Nat.shiftLeft_eq, two_mul, pow_add]
    calc u * 2 ^ c + v < u * 2 ^ c + 2 ^ c := Nat.add_lt_add_left hv _
      _ = (u + 1) * 2 ^ c := by ring
      _ ≤ 2 ^ c * 2 ^ c := Nat.mul_le_mul_right _ hu
  have hdiv : ((u <<< c) + v) >>> c = u := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, mul_comm u (2 ^ c),
      Nat.mul_add_div hpow, Nat.div_eq_of_lt hv, add_zero]
  have hmod : ((u <<< c) + v) &&& (2 ^ c - 1) = v := by
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, mul_comm u (2 ^ c),
      Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
  exact ⟨hlt, hdiv, hmod⟩

private theorem innerClmulStep_exec {base w w₀ b b' k r_val acc_val i m : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k))
    (hi : i < reducedLimbCount (reducedTrinomialStep w₀ b b'))
    (hm : m < reducedLimbCount (reducedTrinomialStep w₀ b b'))
    (x : Data 240)
    (hinv : ClmulInv base w w₀ b b' k r_val acc_val x)
    (htab : TableRep base w w₀ b b' k x.mem)
    (hprod_lt : ∀ d < 2 * reducedLimbCount (reducedTrinomialStep w₀ b b'),
      x.regs (prodReg d) < 2 ^ reducedChunkBits (reducedTrinomialStep w₀ b b')) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    let u := getLimb c acc_val i
    let v := getLimb c r_val m
    ∃ y, Exec w (innerClmulStep i m) x y 13 ∧
      ClmulInv base w w₀ b b' k r_val acc_val y ∧
      (∀ d < 2 * L, y.regs (prodReg d) < 2 ^ c) ∧
      packLimbs c (2 * L) (fun d => y.regs (prodReg d)) =
        packLimbs c (2 * L) (fun d => x.regs (prodReg d)) ^^^ (clmul u v <<< ((i + m) * c)) ∧
      y.mem = x.mem := by
  intro t c L u v
  set p := reducedPackShift t w
  set tBase := tabBase base w₀ b b' k
  have hc_pos : 0 < c := reducedChunkBits_pos t
  have hL_le : L ≤ 54 := reducedLimbCount_le t
  have hpow_2c_lt : 2 ^ (2 * c) < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hc_lt
  have hfit_2c : Fits w (2 ^ (2 * c)) := hpow_2c_lt
  have hpack_le : 2 ^ p * (2 * c) ≤ w := two_pow_reducedPackShift_mul_le (le_of_lt hc_lt)
  have hpow_pack_le : 2 ^ (2 ^ p * (2 * c)) ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hpack_le
  have hfit_end : Fits w (tBase + reducedTableWords t w) := by
    simpa only [tBase, tabBase, space, tableWords, Nat.add_assoc] using hfit_space
  have ⟨⟨h0, h4, h5, h6, h7, h8, h9, h18, hxReg⟩, haccReg⟩ := hinv
  change x.regs 5 = c at h5
  change x.regs 6 = 2 ^ c - 1 at h6
  change x.regs 7 = p at h7
  change x.regs 8 = 2 ^ p - 1 at h8
  change x.regs 9 = 2 * c at h9
  change x.regs 18 = 2 ^ (2 * c) - 1 at h18
  change i < L at hi
  change m < L at hm
  have hu_reg : x.regs (accReg i) = u := haccReg i hi
  have hv_reg : x.regs (xReg m) = v := hxReg m hm
  have hu_lt : u < 2 ^ c := getLimb_lt c acc_val i
  have hv_lt : v < 2 ^ c := getLimb_lt c r_val m
  obtain ⟨hidx_lt, hidx_u, hidx_v⟩ := pair_index_props hu_lt hv_lt
  set idx := (u <<< c) + v with hidx_def
  have hshl_lt : u <<< c < 2 ^ (2 * c) := lt_of_le_of_lt (Nat.le_add_right _ _) hidx_lt
  set wIdx := idx >>> p with hwIdx_def
  set subIdx := idx &&& (2 ^ p - 1) with hsubIdx_def
  set sh := subIdx * (2 * c) with hsh_def
  have hwIdx_lt : wIdx < reducedTableWords t w := shiftRight_lt_reducedTableWords hidx_lt
  have hsub_lt : subIdx < 2 ^ p := and_two_pow_sub_one_lt idx p
  have hsh_lt : sh < w := by
    calc subIdx * (2 * c) < 2 ^ p * (2 * c) :=
          Nat.mul_lt_mul_of_pos_right hsub_lt (by omega)
      _ ≤ w := hpack_le
  have hfit_sh : Fits w sh := lt_trans hsh_lt Nat.lt_two_pow_self
  have hfit_sub : Fits w subIdx :=
    hfit_sh.of_le (Nat.le_mul_of_pos_right _ (by omega : 0 < 2 * c))
  set word := x.mem (tBase + wIdx) with hword_def
  have hword_lt : word < 2 ^ (2 ^ p * (2 * c)) := htab.1 wIdx hwIdx_lt
  have hfit_word_shr : Fits w (word >>> sh) :=
    lt_of_le_of_lt (Nat.shiftRight_le _ _) (lt_of_lt_of_le hword_lt hpow_pack_le)
  have hlimb_eq : (word >>> sh) &&& (2 ^ (2 * c) - 1) = clmul u v := by
    have := htab.2 idx hidx_lt
    dsimp only [getLimb, wIdx, subIdx, sh, word, tBase] at this ⊢
    rw [this, hidx_u, hidx_v]
  have hcl_lt : clmul u v < 2 ^ (2 * c) := clmul_lt_two_pow_two_mul hu_lt hv_lt
  set lo := clmul u v &&& (2 ^ c - 1) with hlo_def
  set hi_part := clmul u v >>> c with hhi_def
  have hlo_lt : lo < 2 ^ c := and_two_pow_sub_one_lt _ c
  have hhi_lt : hi_part < 2 ^ c := by
    have := shiftRight_lt_pow_sub (by omega : c ≤ 2 * c) hcl_lt
    simpa only [Nat.two_mul, Nat.add_sub_cancel] using this
  have hpow_c_lt : 2 ^ c < 2 ^ w :=
    lt_of_le_of_lt (Nat.pow_le_pow_right two_pos (by omega : c ≤ 2 * c)) hpow_2c_lt
  have him1_lt : i + m + 1 < 2 * L := by omega
  have him_lt : i + m < 2 * L := by omega
  set old0 := x.regs (prodReg (i + m)) with hold0_def
  set old1 := x.regs (prodReg (i + m + 1)) with hold1_def
  have hold0_lt : old0 < 2 ^ c := hprod_lt (i + m) him_lt
  have hold1_lt : old1 < 2 ^ c := hprod_lt (i + m + 1) him1_lt
  have hnew0_lt : old0 ^^^ lo < 2 ^ c := Nat.xor_lt_two_pow hold0_lt hlo_lt
  have hnew1_lt : old1 ^^^ hi_part < 2 ^ c := Nat.xor_lt_two_pow hold1_lt hhi_lt
  set s11 := ((((((((((x.set 10 (u <<< c)).set 10 idx).set 11 wIdx).set 11 (tBase + wIdx)).set 12
    word).set 11 subIdx).set 11 sh).set 12 (word >>> sh)).set 12 (clmul u v)).set 13 lo).set 14
    hi_part
  have hs11_prod : ∀ d, s11.regs (prodReg d) = x.regs (prodReg d) := by
    intro d
    dsimp only [s11, Data.set]
    repeat rw [Function.update_of_ne (prodReg_ne_low d (by decide))]
  set s13 := (s11.set (prodReg (i + m)) (old0 ^^^ lo)).set (prodReg (i + m + 1)) (old1 ^^^ hi_part)
  have hexec : Exec w (innerClmulStep i m) x s13 13 := by
    unfold innerClmulStep
    wram_exec [hu_reg, hv_reg, h4, show tabBase base w₀ b b' k = tBase from rfl, h5, h6, h7, h8, h9,
      h18, ← hidx_def, ← hwIdx_def, ← hsubIdx_def,
      ← hsh_def, ← hword_def, hlimb_eq, ← hlo_def, ← hhi_def, ← hold0_def, ← hold1_def]
  have hs11_inv : ClmulInv base w w₀ b b' k r_val acc_val s11 := by
    have i1 := hinv.set_scratch (r := 10) (by decide) (by decide) (u <<< c)
    have i2 := i1.set_scratch (r := 10) (by decide) (by decide) idx
    have i3 := i2.set_scratch (r := 11) (by decide) (by decide) wIdx
    have i4 := i3.set_scratch (r := 11) (by decide) (by decide) (tBase + wIdx)
    have i5 := i4.set_scratch (r := 12) (by decide) (by decide) word
    have i6 := i5.set_scratch (r := 11) (by decide) (by decide) subIdx
    have i7 := i6.set_scratch (r := 11) (by decide) (by decide) sh
    have i8 := i7.set_scratch (r := 12) (by decide) (by decide) (word >>> sh)
    have i9 := i8.set_scratch (r := 12) (by decide) (by decide) (clmul u v)
    have i10 := i9.set_scratch (r := 13) (by decide) (by decide) lo
    exact i10.set_scratch (r := 14) (by decide) (by decide) hi_part
  have hs13_inv : ClmulInv base w w₀ b b' k r_val acc_val s13 :=
    (hs11_inv.set_prodReg (i + m) (old0 ^^^ lo)).set_prodReg (i + m + 1) (old1 ^^^ hi_part)
  let f := fun d => x.regs (prodReg d)
  have hs13_fn : ∀ d < 2 * L, s13.regs (prodReg d) =
      Function.update (Function.update f (i + m) (f (i + m) ^^^ lo))
        (i + m + 1) (f (i + m + 1) ^^^ hi_part) d := by
    intro d hd
    dsimp only [s13, Data.set, f]
    rcases eq_or_ne d (i + m + 1) with rfl | hne1
    · rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (prodReg_ne_of_ne (by omega) (by omega) hne1),
        Function.update_of_ne hne1]
      rcases eq_or_ne d (i + m) with rfl | hne0
      · rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne (prodReg_ne_of_ne (by omega) (by omega) hne0),
          Function.update_of_ne hne0, hs11_prod d]
  refine ⟨s13, hexec, hs13_inv, fun d hd => ?_, ?_, rfl⟩
  · rw [hs13_fn d hd]
    rcases eq_or_ne d (i + m + 1) with rfl | hne1
    · rw [Function.update_self]; exact hnew1_lt
    · rw [Function.update_of_ne hne1]
      rcases eq_or_ne d (i + m) with rfl | hne0
      · rw [Function.update_self]; exact hnew0_lt
      · rw [Function.update_of_ne hne0]; exact hprod_lt d hd
  · rw [packLimbs_congr hs13_fn]
    exact packLimbs_update_pair hc_pos f him1_lt hcl_lt

private theorem outerClmulStep_exec {base w w₀ b b' k r_val acc_val i : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k))
    (hi : i < reducedLimbCount (reducedTrinomialStep w₀ b b'))
    (x : Data 240)
    (hinv : ClmulInv base w w₀ b b' k r_val acc_val x)
    (htab : TableRep base w w₀ b b' k x.mem)
    (hprod_lt : ∀ d < 2 * reducedLimbCount (reducedTrinomialStep w₀ b b'),
      x.regs (prodReg d) < 2 ^ reducedChunkBits (reducedTrinomialStep w₀ b b')) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    ∃ y, Exec w (outerClmulStep L i) x y (L * 13 + 1) ∧
      ClmulInv base w w₀ b b' k r_val acc_val y ∧
      (∀ d < 2 * L, y.regs (prodReg d) < 2 ^ c) ∧
      packLimbs c (2 * L) (fun d => y.regs (prodReg d)) =
        packLimbs c (2 * L) (fun d => x.regs (prodReg d)) ^^^
          (clmul (getLimb c acc_val i) (truncLimbs c L r_val) <<< (i * c)) ∧
      y.mem = x.mem := by
  intro t c L
  set P₀ := packLimbs c (2 * L) (fun d => x.regs (prodReg d))
  let P (m : ℕ) (z : Data 240) : Prop :=
    ClmulInv base w w₀ b b' k r_val acc_val z ∧
    (∀ d < 2 * L, z.regs (prodReg d) < 2 ^ c) ∧
    packLimbs c (2 * L) (fun d => z.regs (prodReg d)) =
      P₀ ^^^ (clmul (getLimb c acc_val i) (truncLimbs c m r_val) <<< (i * c)) ∧
    z.mem = x.mem
  have hP0 : P 0 x := by
    refine ⟨hinv, hprod_lt, ?_, rfl⟩
    rw [truncLimbs_zero, clmul_zero_right, Nat.zero_shiftLeft, Nat.xor_zero]
  obtain ⟨y, hy_exec, hy_inv, hy_lt, hy_pack, hy_mem⟩ :=
    seqAsc_exec (innerClmulStep i) 13 P L (fun m hm z ⟨hz_inv, hz_lt, hz_pack, hz_mem⟩ => by
      have htab_z : TableRep base w w₀ b b' k z.mem := hz_mem ▸ htab
      obtain ⟨z', hz'_exec, hz'_inv, hz'_lt, hz'_pack, hz'_mem⟩ :=
        innerClmulStep_exec hc_lt hfit_space hi hm z hz_inv htab_z hz_lt
      refine ⟨z', hz'_exec, hz'_inv, hz'_lt, ?_, hz'_mem.trans hz_mem⟩
      rw [hz'_pack, hz_pack, Nat.xor_assoc, ← clmul_truncLimbs_right_succ]) hP0
  exact ⟨y, hy_exec, hy_inv, hy_lt, hy_pack, hy_mem⟩

private theorem clmulLimbsCode_exec {base w w₀ b b' k r_val acc_val : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k))
    (hr_lt : r_val < 2 ^ (reducedLimbCount (reducedTrinomialStep w₀ b b') *
      reducedChunkBits (reducedTrinomialStep w₀ b b')))
    (hacc_lt : acc_val < 2 ^ (reducedLimbCount (reducedTrinomialStep w₀ b b') *
      reducedChunkBits (reducedTrinomialStep w₀ b b')))
    (x : Data 240)
    (hinv : ClmulInv base w w₀ b b' k r_val acc_val x)
    (htab : TableRep base w w₀ b b' k x.mem)
    (hprod_lt : ∀ d < 2 * reducedLimbCount (reducedTrinomialStep w₀ b b'),
      x.regs (prodReg d) < 2 ^ reducedChunkBits (reducedTrinomialStep w₀ b b'))
    (hprod_zero : packLimbs (reducedChunkBits (reducedTrinomialStep w₀ b b'))
      (2 * reducedLimbCount (reducedTrinomialStep w₀ b b')) (fun d => x.regs (prodReg d)) = 0) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    ∃ y, Exec w (clmulLimbsCode L) x y (L * (L * 13 + 1) + 1) ∧
      HornerConsts base w w₀ b b' k r_val y ∧
      (∀ d < 2 * L, y.regs (prodReg d) = getLimb c (clmul acc_val r_val) d) ∧
      y.mem = x.mem := by
  intro t c L
  let P (i : ℕ) (z : Data 240) : Prop :=
    ClmulInv base w w₀ b b' k r_val acc_val z ∧
    (∀ d < 2 * L, z.regs (prodReg d) < 2 ^ c) ∧
    packLimbs c (2 * L) (fun d => z.regs (prodReg d)) = clmul (truncLimbs c i acc_val) r_val ∧
    z.mem = x.mem
  have hP0 : P 0 x := by
    refine ⟨hinv, hprod_lt, ?_, rfl⟩
    rw [hprod_zero, truncLimbs_zero, clmul_zero_left]
  obtain ⟨y, hy_exec, hy_inv, hy_lt, hy_pack, hy_mem⟩ :=
    seqAsc_exec (outerClmulStep L) (L * 13 + 1) P L
      (fun i hi z ⟨hz_inv, hz_lt, hz_pack, hz_mem⟩ => by
        have htab_z : TableRep base w w₀ b b' k z.mem := hz_mem ▸ htab
        obtain ⟨z', hz'_exec, hz'_inv, hz'_lt, hz'_pack, hz'_mem⟩ :=
          outerClmulStep_exec hc_lt hfit_space hi z hz_inv htab_z hz_lt
        refine ⟨z', hz'_exec, hz'_inv, hz'_lt, ?_, hz'_mem.trans hz_mem⟩
        rw [hz'_pack, hz_pack, truncLimbs_of_lt hr_lt, ← clmul_truncLimbs_left_succ]) hP0
  rw [truncLimbs_of_lt hacc_lt] at hy_pack
  refine ⟨y, hy_exec, hy_inv.1, fun d hd => ?_, hy_mem⟩
  rw [← hy_pack, getLimb_packLimbs_of_lt c hd (hy_lt d hd)]

private theorem getLimb_eq_zero_of_lt {c n d P : ℕ} (hP : P < 2 ^ (n * c)) (hd : n ≤ d) :
    getLimb c P d = 0 := by
  dsimp only [getLimb]
  have hle : n * c ≤ d * c := Nat.mul_le_mul_right c hd
  have hlt : P < 2 ^ (d * c) := lt_of_lt_of_le hP (Nat.pow_le_pow_right two_pos hle)
  have hdiv : P >>> (d * c) = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hlt
  rw [hdiv, Nat.zero_and]

/-- Step `m < 2 * L₀` of trinomial reduction and seed addition (`6` instructions):
loads limb `m` of coefficient `coeffIdx` from memory, reduces the product limbs in `prodReg`
modulo `X ^ (2 * 3 ^ t) + X ^ (3 ^ t) + 1`, and writes the XOR into `accReg m`. -/
@[expose] def reduceAddStep (L₀ coeffIdx m : ℕ) : Code .exact 240 :=
  .seq (.op (.const 10 (1 + (m + 2 * L₀ * coeffIdx))))
  (.seq (.op (.exactBin .add 10 0 10))
  (.seq (.op (.load 11 10))
  (.seq (if m < L₀ then
          .seq (.op (.exactBin .xor 12 (prodReg m) (prodReg (3 * L₀ + m))))
               (.op (.exactBin .xor 12 12 (prodReg (2 * L₀ + m))))
        else
          .seq (.op (.exactBin .xor 12 (prodReg m) (prodReg (L₀ + m))))
               (.op (.copy 12 12)))
        (.op (.exactBin .xor (accReg m) 12 11)))))

/-- Trinomial reduction and seed addition across all `2 * L₀ = L` limbs. -/
@[expose] def reduceAddCode (L₀ coeffIdx : ℕ) : Code .exact 240 :=
  seqAsc (reduceAddStep L₀ coeffIdx) (2 * L₀)

private theorem reduceAddStep_exec {base w w₀ b b' k r_val P_val : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k))
    (hP_lt : P_val < 2 ^ (2 * reducedLimbCount (reducedTrinomialStep w₀ b b') *
      reducedChunkBits (reducedTrinomialStep w₀ b b')))
    (θ : ReducedPolySeed w₀ b b' k) (coeffIdx : Fin k) (m : ℕ)
    (hm : m < reducedLimbCount (reducedTrinomialStep w₀ b b'))
    (x : Data 240)
    (hc : HornerConsts base w w₀ b b' k r_val x)
    (hseed : SeedRep base w₀ b b' k θ x.mem)
    (hprod : ∀ d < 2 * reducedLimbCount (reducedTrinomialStep w₀ b b'),
      x.regs (prodReg d) = getLimb (reducedChunkBits (reducedTrinomialStep w₀ b b')) P_val d) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    let L₀ := reducedHalfLimbs t
    let newAcc := reduceTrinomialCode t P_val ^^^ (θ.2 coeffIdx).val
    ∃ y, Exec w (reduceAddStep L₀ coeffIdx.val m) x y 6 ∧
      HornerConsts base w w₀ b b' k r_val y ∧
      (∀ d < 2 * L, y.regs (prodReg d) = getLimb c P_val d) ∧
      y.regs (accReg m) = getLimb c newAcc m ∧
      (∀ i < m, y.regs (accReg i) = x.regs (accReg i)) ∧
      y.mem = x.mem := by
  intro t c L L₀ newAcc
  have hL_eq : L = 2 * L₀ := rfl
  have hL_le : L ≤ 54 := reducedLimbCount_le t
  change m < L at hm
  have hpow_2c_lt : 2 ^ (2 * c) < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hc_lt
  have hpow_c_lt : 2 ^ c < 2 ^ w :=
    lt_of_le_of_lt (Nat.pow_le_pow_right two_pos (by omega : c ≤ 2 * c)) hpow_2c_lt
  set off := 1 + (m + 2 * L₀ * coeffIdx.val)
  have hoff_lt_seed : off < seedWords w₀ b b' k := by
    dsimp only [off, seedWords]
    change 1 + (m + L * coeffIdx.val) < 1 + k * L
    have : m + L * coeffIdx.val < L + L * coeffIdx.val := Nat.add_lt_add_right hm _
    have hmul : L + L * coeffIdx.val ≤ k * L := by
      calc L + L * coeffIdx.val = (coeffIdx.val + 1) * L := by ring
        _ ≤ k * L := Nat.mul_le_mul_right L coeffIdx.isLt
    omega
  have hfit_off : Fits w off := hfit_space.of_le (by dsimp only [space]; omega)
  have hfit_addr : Fits w (base + off) := hfit_space.of_le (by dsimp only [space]; omega)
  have h0 : x.regs 0 = base := hc.1
  set sBot := (θ.2 coeffIdx).val
  set seedLimb := getLimb c sBot m
  have hmem_eq : x.mem (base + off) = seedLimb := by
    have hrep := hseed.2 coeffIdx ⟨m, hm⟩
    dsimp only [off, seedLimb, sBot]
    rw [show base + (1 + (m + 2 * L₀ * coeffIdx.val)) = base + 1 + (m + L * coeffIdx.val) by
      rw [hL_eq]; ring]
    exact hrep
  set s1 := x.set 10 off
  have e1 : Exec w (.op (.const 10 off) : Code .exact 240) x s1 1 := Exec.const hfit_off
  set s2 := s1.set 10 (base + off)
  have e2 : Exec w (.op (.exactBin .add 10 0 10) : Code .exact 240) s1 s2 1 :=
    exec_exactBin (by simp +decide [s1, h0]) hfit_addr
  set s3 := s2.set 11 seedLimb
  have e3 : Exec w (.op (.load 11 10) : Code .exact 240) s2 s3 1 := by
    simpa +decide [s3, s2, s1, hmem_eq] using
      (Exec.load (B := .exact) (w := w) (d := 11) (a := 10) (x := s2))
  have hs3_hc : HornerConsts base w w₀ b b' k r_val s3 :=
    ((hc.set_scratch (r := 10) (by decide) (by decide) off).set_scratch
      (r := 10) (by decide) (by decide) (base + off)).set_scratch
      (r := 11) (by decide) (by decide) seedLimb
  have hs3_prod : ∀ d < 2 * L, s3.regs (prodReg d) = getLimb c P_val d := by
    intro d hd
    dsimp only [s3, s2, s1, Data.set]
    repeat rw [Function.update_of_ne (prodReg_ne_low d (by decide))]
    exact hprod d hd
  have hs3_acc : ∀ i, s3.regs (accReg i) = x.regs (accReg i) := by
    intro i
    dsimp only [s3, s2, s1, Data.set]
    repeat rw [Function.update_of_ne (accReg_ne_low i (by decide))]
  set redLimb := getLimb c (reduceTrinomialCode t P_val) m
  have hmid : ∃ s4 : Data 240,
      Exec w (if m < L₀ then
          .seq (.op (.exactBin .xor 12 (prodReg m) (prodReg (3 * L₀ + m))))
               (.op (.exactBin .xor 12 12 (prodReg (2 * L₀ + m))))
        else
          .seq (.op (.exactBin .xor 12 (prodReg m) (prodReg (L₀ + m))))
               (.op (.copy 12 12))) s3 s4 2 ∧
      HornerConsts base w w₀ b b' k r_val s4 ∧
      s4.regs 11 = seedLimb ∧
      s4.regs 12 = redLimb ∧
      (∀ d < 2 * L, s4.regs (prodReg d) = getLimb c P_val d) ∧
      (∀ i < m, s4.regs (accReg i) = x.regs (accReg i)) ∧
      s4.mem = x.mem := by
    by_cases hm_low : m < L₀
    · rw [ite_eq_left hm_low]
      set v1 := getLimb c P_val m ^^^ getLimb c P_val (3 * L₀ + m)
      have hv1_lt : v1 < 2 ^ c := Nat.xor_lt_two_pow (getLimb_lt _ _ _) (getLimb_lt _ _ _)
      have hred_eq : v1 ^^^ getLimb c P_val (2 * L₀ + m) = redLimb :=
        (getLimb_reduceTrinomialCode_low t P_val hm_low).symm
      have hred_lt : redLimb < 2 ^ c := getLimb_lt _ _ _
      set s4a := s3.set 12 v1
      have e4a : Exec w
          (.op (.exactBin .xor 12 (prodReg m) (prodReg (3 * L₀ + m))) : Code .exact 240)
          s3 s4a 1 :=
        exec_exactBin
          (by
            dsimp only [BinOp.evalExact]
            rw [hs3_prod m (by omega), hs3_prod (3 * L₀ + m) (by omega)])
          (lt_trans hv1_lt hpow_c_lt)
      set s4b := s4a.set 12 redLimb
      have e4b : Exec w
          (.op (.exactBin .xor 12 12 (prodReg (2 * L₀ + m))) : Code .exact 240)
          s4a s4b 1 :=
        exec_exactBin
          (by
            dsimp only [s4a, Data.set, BinOp.evalExact]
            rw [Function.update_self,
              Function.update_of_ne (prodReg_ne_low (2 * L₀ + m) (r := 12) (by decide)),
              hs3_prod (2 * L₀ + m) (by omega), hred_eq])
          (lt_trans hred_lt hpow_c_lt)
      refine ⟨s4b, e4a.seq e4b,
        (hs3_hc.set_scratch (r := 12) (by decide) (by decide) v1).set_scratch
          (r := 12) (by decide) (by decide) redLimb,
        by simp +decide [s4b, s4a, s3],
        by simp +decide [s4b],
        fun d hd => ?_, fun i _ => ?_, rfl⟩
      · dsimp only [s4b, s4a, Data.set]
        repeat rw [Function.update_of_ne (prodReg_ne_low d (by decide))]
        exact hs3_prod d hd
      · dsimp only [s4b, s4a, Data.set]
        repeat rw [Function.update_of_ne (accReg_ne_low i (by decide))]
        exact hs3_acc i
    · rw [ite_eq_right hm_low]
      have hm_ge : L₀ ≤ m := le_of_not_gt hm_low
      have hm'_lt : m - L₀ < L₀ := by omega
      change P_val < 2 ^ ((2 * L) * c) at hP_lt
      have hzero4 : getLimb c P_val (4 * L₀ + (m - L₀)) = 0 :=
        getLimb_eq_zero_of_lt hP_lt (by omega)
      have hred_eq : getLimb c P_val m ^^^ getLimb c P_val (L₀ + m) = redLimb := by
        have hhigh : getLimb c (reduceTrinomialCode t P_val) (L₀ + (m - L₀)) =
            (getLimb c P_val (L₀ + (m - L₀)) ^^^ getLimb c P_val (4 * L₀ + (m - L₀))) ^^^
              getLimb c P_val (2 * L₀ + (m - L₀)) :=
          getLimb_reduceTrinomialCode_high t P_val hm'_lt
        rw [Nat.add_sub_of_le hm_ge,
          show 2 * L₀ + (m - L₀) = L₀ + m by omega,
          hzero4, Nat.xor_zero] at hhigh
        exact hhigh.symm
      have hred_lt : redLimb < 2 ^ c := getLimb_lt _ _ _
      set s4a := s3.set 12 redLimb
      have e4a : Exec w
          (.op (.exactBin .xor 12 (prodReg m) (prodReg (L₀ + m))) : Code .exact 240)
          s3 s4a 1 :=
        exec_exactBin
          (by
            dsimp only [BinOp.evalExact]
            rw [hs3_prod m (by omega), hs3_prod (L₀ + m) (by omega), hred_eq])
          (lt_trans hred_lt hpow_c_lt)
      have e4b : Exec w (.op (.copy 12 12) : Code .exact 240) s4a s4a 1 :=
        exec_copy_self w 12 s4a
      refine ⟨s4a, e4a.seq e4b,
        hs3_hc.set_scratch (r := 12) (by decide) (by decide) redLimb,
        by simp +decide [s4a, s3],
        by simp +decide [s4a],
        fun d hd => ?_, fun i _ => ?_, rfl⟩
      · dsimp only [s4a, Data.set]
        rw [Function.update_of_ne (prodReg_ne_low d (by decide))]
        exact hs3_prod d hd
      · dsimp only [s4a, Data.set]
        rw [Function.update_of_ne (accReg_ne_low i (by decide))]
        exact hs3_acc i
  obtain ⟨s4, e4, hs4_hc, hs4_11, hs4_12, hs4_prod, hs4_acc, hs4_mem⟩ := hmid
  have hnew_eq : redLimb ^^^ seedLimb = getLimb c newAcc m :=
    (getLimb_xor c (reduceTrinomialCode t P_val) sBot m).symm
  have hnew_lt : getLimb c newAcc m < 2 ^ c := getLimb_lt _ _ _
  set s5 := s4.set (accReg m) (getLimb c newAcc m)
  have e5 : Exec w (.op (.exactBin .xor (accReg m) 12 11) : Code .exact 240) s4 s5 1 :=
    exec_exactBin (by simp +decide [hs4_12, hs4_11, hnew_eq]) (lt_trans hnew_lt hpow_c_lt)
  refine ⟨s5, e1.seq (e2.seq (e3.seq (e4.seq e5))),
    hs4_hc.set_accReg m (getLimb c newAcc m), fun d hd => ?_,
    Function.update_self _ _ _, fun i hi => ?_, hs4_mem⟩
  · dsimp only [s5, Data.set]
    rw [Function.update_of_ne (accReg_ne_prodReg m d).symm]
    exact hs4_prod d hd
  · dsimp only [s5, Data.set]
    rw [Function.update_of_ne (accReg_ne_of_ne (by omega) (by omega) (ne_of_lt hi))]
    exact hs4_acc i hi

private theorem reduceAddCode_exec {base w w₀ b b' k r_val P_val : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k))
    (hP_lt : P_val < 2 ^ (2 * reducedLimbCount (reducedTrinomialStep w₀ b b') *
      reducedChunkBits (reducedTrinomialStep w₀ b b')))
    (θ : ReducedPolySeed w₀ b b' k) (coeffIdx : Fin k) (x : Data 240)
    (hc : HornerConsts base w w₀ b b' k r_val x)
    (hseed : SeedRep base w₀ b b' k θ x.mem)
    (hprod : ∀ d < 2 * reducedLimbCount (reducedTrinomialStep w₀ b b'),
      x.regs (prodReg d) = getLimb (reducedChunkBits (reducedTrinomialStep w₀ b b')) P_val d) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    let L₀ := reducedHalfLimbs t
    let newAcc := reduceTrinomialCode t P_val ^^^ (θ.2 coeffIdx).val
    ∃ y, Exec w (reduceAddCode L₀ coeffIdx.val) x y (L * 6 + 1) ∧
      HornerConsts base w w₀ b b' k r_val y ∧
      (∀ m < L, y.regs (accReg m) = getLimb c newAcc m) ∧
      y.mem = x.mem := by
  intro t c L L₀ newAcc
  let P (n : ℕ) (z : Data 240) : Prop :=
    HornerConsts base w w₀ b b' k r_val z ∧
    (∀ d < 2 * L, z.regs (prodReg d) = getLimb c P_val d) ∧
    (∀ m < n, z.regs (accReg m) = getLimb c newAcc m) ∧
    z.mem = x.mem
  have hP0 : P 0 x := ⟨hc, hprod, fun _ hm => (Nat.not_lt_zero _ hm).elim, rfl⟩
  obtain ⟨y, hy_exec, hy_hc, _, hy_acc, hy_mem⟩ :=
    seqAsc_exec (reduceAddStep L₀ coeffIdx.val) 6 P L
      (fun m hm z ⟨hz_hc, hz_prod, hz_acc, hz_mem⟩ => by
        have hseed_z : SeedRep base w₀ b b' k θ z.mem := hz_mem ▸ hseed
        obtain ⟨z', hz'_exec, hz'_hc, hz'_prod, hz'_m, hz'_prev, hz'_mem⟩ :=
          reduceAddStep_exec hc_lt hfit_space hP_lt θ coeffIdx m hm z hz_hc hseed_z hz_prod
        refine ⟨z', hz'_exec, hz'_hc, hz'_prod, fun i hi => ?_, hz'_mem.trans hz_mem⟩
        rcases eq_or_ne i m with rfl | hne
        · exact hz'_m
        · have hilt : i < m := by omega
          rw [hz'_prev i hilt]
          exact hz_acc i hilt) hP0
  exact ⟨y, hy_exec, hy_hc, hy_acc, hy_mem⟩

/-- Step `j < k` of Horner polynomial evaluation: multiplies `accReg` by `xReg` into `prodReg`,
reduces modulo the trinomial, and adds coefficient `k - 1 - j`. -/
@[expose] def hornerStep (t k j : ℕ) : Code .exact 240 :=
  let L₀ := reducedHalfLimbs t
  let L := reducedLimbCount t
  .seq (zeroProdCode L)
  (.seq (clmulLimbsCode L) (reduceAddCode L₀ (k - 1 - j)))

/-- Stage 3 of `evalCode`: `k` Horner steps evaluating `polynomialHash`. -/
@[expose] def hornerCode (t k : ℕ) : Code .exact 240 :=
  seqAsc (hornerStep t k) k

/-- Step count of a single `hornerStep t k j`. -/
@[expose] def hornerStepSteps (t : ℕ) : ℕ :=
  let L := reducedLimbCount t
  (2 * L * 1 + 1) + ((L * (L * 13 + 1) + 1) + (L * 6 + 1))

private theorem hornerCode_exec {base w w₀ b b' k : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k))
    (θ : ReducedPolySeed w₀ b b' k)
    (r : Fin (2 ^ min w₀ (3 * b)))
    (x : Data 240)
    (hc : HornerConsts base w w₀ b b' k r.val x)
    (htab : TableRep base w w₀ b b' k x.mem)
    (hseed : SeedRep base w₀ b b' k θ x.mem)
    (hacc0 : ∀ m < reducedLimbCount (reducedTrinomialStep w₀ b b'), x.regs (accReg m) = 0) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    let evalVal := (trinomialPolyEval t k (2 ^ min w₀ (3 * b)) θ.2 r).val
    ∃ y, Exec w (hornerCode t k) x y (k * hornerStepSteps t + 1) ∧
      HornerConsts base w w₀ b b' k r.val y ∧
      (∀ m < L, y.regs (accReg m) = getLimb c evalVal m) ∧
      y.mem = x.mem := by
  intro t c L evalVal
  have hLc : L * c = 2 * 3 ^ t := reducedLimbCount_mul_chunkBits t
  have hr_deg : r.val < 2 ^ (2 * 3 ^ t) :=
    r.isLt.trans_le (two_pow_min_le_two_pow_reducedTrinomialDeg w₀ b b')
  have hx_lt : r.val < 2 ^ (L * c) := by rw [hLc]; exact hr_deg
  set c_field : Fin k → TrinomialField t := fun j => (TrinomialField.equivFin t).symm (θ.2 j)
  set x_field : TrinomialField t := AdjoinRoot.mk (trinomial t) (polyOfCode r.val)
  have hx_val : (TrinomialField.equivFin t x_field).val = r.val :=
    TrinomialField.val_equivFin_mk_polyOfCode t hr_deg
  have hzero_val : (TrinomialField.equivFin t (0 : TrinomialField t)).val = 0 := by
    have h0_eq : (0 : TrinomialField t) = AdjoinRoot.mk (trinomial t) (polyOfCode 0) := by simp
    rw [h0_eq]
    exact TrinomialField.val_equivFin_mk_polyOfCode t (by positivity)
  let P (j : ℕ) (z : Data 240) : Prop :=
    HornerConsts base w w₀ b b' k r.val z ∧
    (∀ m < L, z.regs (accReg m) =
      getLimb c (TrinomialField.equivFin t (hornerPrefix t k c_field x_field j)).val m) ∧
    z.mem = x.mem
  have hP0 : P 0 x := by
    refine ⟨hc, fun m hm => ?_, rfl⟩
    rw [hacc0 m hm]
    dsimp only [hornerPrefix]
    rw [hzero_val]
    simp [getLimb]
  obtain ⟨y, hy_exec, hy_hc, hy_acc, hy_mem⟩ :=
    seqAsc_exec (hornerStep t k) (hornerStepSteps t) P k
      (fun j hj z ⟨hz_hc, hz_acc, hz_mem⟩ => by
        set acc := hornerPrefix t k c_field x_field j
        set acc_val := (TrinomialField.equivFin t acc).val
        have hacc_lt : acc_val < 2 ^ (L * c) := by
          rw [hLc]
          exact (TrinomialField.equivFin t acc).isLt
        have hinv : ClmulInv base w w₀ b b' k r.val acc_val z := ⟨hz_hc, hz_acc⟩
        have htab_z : TableRep base w w₀ b b' k z.mem := hz_mem ▸ htab
        obtain ⟨z1, e1, hz1_inv, hz1_lt, hz1_zero, hz1_mem⟩ := zeroProdCode_exec z hinv
        have htab_z1 : TableRep base w w₀ b b' k z1.mem := hz1_mem ▸ htab_z
        obtain ⟨z2, e2, hz2_hc, hz2_prod, hz2_mem⟩ :=
          clmulLimbsCode_exec hc_lt hfit_space hx_lt hacc_lt z1 hz1_inv htab_z1 hz1_lt hz1_zero
        have hP_lt : clmul acc_val r.val < 2 ^ (2 * L * c) := by
          rw [Nat.mul_assoc]
          exact clmul_lt_two_pow_two_mul hacc_lt hx_lt
        have hseed_z2 : SeedRep base w₀ b b' k θ z2.mem :=
          (hz2_mem.trans (hz1_mem.trans hz_mem)) ▸ hseed
        obtain ⟨z3, e3, hz3_hc, hz3_acc, hz3_mem⟩ :=
          reduceAddCode_exec hc_lt hfit_space hP_lt θ ⟨k - 1 - j, by omega⟩ z2
            hz2_hc hseed_z2 hz2_prod
        have hmem_all : z3.mem = x.mem := hz3_mem.trans (hz2_mem.trans (hz1_mem.trans hz_mem))
        refine ⟨z3, e1.seq (e2.seq e3), hz3_hc, fun m hm => ?_, hmem_all⟩
        rw [hz3_acc m hm]
        congr 1
        have hmul_val : reduceTrinomialCode t (clmul acc_val r.val) =
            (TrinomialField.equivFin t (acc * x_field)).val := by
          rw [TrinomialField.val_equivFin_mul, hx_val]
        have hseed_val : (θ.2 ⟨k - 1 - j, by omega⟩).val =
            (TrinomialField.equivFin t (c_field ⟨k - 1 - j, by omega⟩)).val := by
          have h : TrinomialField.equivFin t (c_field ⟨k - 1 - j, by omega⟩) =
              θ.2 ⟨k - 1 - j, by omega⟩ :=
            (TrinomialField.equivFin t).apply_symm_apply (θ.2 ⟨k - 1 - j, by omega⟩)
          exact (congrArg Fin.val h).symm
        rw [hmul_val, hseed_val, ← TrinomialField.val_equivFin_add]
        dsimp only [hornerPrefix]
        rw [dite_eq_left hj]) hP0
  refine ⟨y, hy_exec, hy_hc, fun m hm => ?_, hy_mem⟩
  rw [hy_acc m hm, hornerPrefix_self_eq_polynomialHash]
  rfl

/-- Step `m < L` of Stage 4 (`5` instructions): masks and shifts `accReg m` into `reg 2` to
reconstruct the low `b'` bits of the polynomial evaluation. -/
@[expose] def packOutStep (c b' m : ℕ) : Code .exact 240 :=
  .seq (.op (.const 10 (reducedOutMask c b' m)))
  (.seq (.op (.const 11 (reducedOutShift c b' m)))
  (.seq (.op (.exactBin .and 12 (accReg m) 10))
  (.seq (.op (.exactBin .shiftLeft 12 12 11))
        (.op (.exactBin .xor 2 2 12)))))

/-- Stage 4 of `evalCode`: packs the low `b'` bits of `accReg 0 .. accReg (L - 1)` into `reg 2`. -/
@[expose] def packOutCode (t b' : ℕ) : Code .exact 240 :=
  .seq (.op (.const 2 0))
       (seqAsc (packOutStep (reducedChunkBits t) b') (reducedLimbCount t))

private theorem packOutStep_exec {w t b' evalVal : ℕ}
    (hc_lt : 2 * reducedChunkBits t < w)
    (hb'_le : b' ≤ w)
    (m : ℕ) (hm : m < reducedLimbCount t)
    (x : Data 240)
    (h2 : x.regs 2 = packLimbs (reducedChunkBits t) m (getLimb (reducedChunkBits t) evalVal) &&&
      (2 ^ b' - 1))
    (hacc : ∀ i < reducedLimbCount t,
      x.regs (accReg i) = getLimb (reducedChunkBits t) evalVal i) :
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    ∃ y, Exec w (packOutStep c b' m) x y 5 ∧
      y.regs 0 = x.regs 0 ∧
      y.regs 1 = x.regs 1 ∧
      y.regs 2 = packLimbs c (m + 1) (getLimb c evalVal) &&& (2 ^ b' - 1) ∧
      (∀ i < L, y.regs (accReg i) = getLimb c evalVal i) ∧
      y.mem = x.mem := by
  intro c L
  have hpow_2c_lt : 2 ^ (2 * c) < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hc_lt
  have hpow_c_lt : 2 ^ c < 2 ^ w :=
    lt_of_le_of_lt (Nat.pow_le_pow_right two_pos (by omega : c ≤ 2 * c)) hpow_2c_lt
  have hfit_mask : Fits w (reducedOutMask c b' m) :=
    lt_trans (reducedOutMask_lt c b' m) hpow_c_lt
  have hfit_shift : Fits w (reducedOutShift c b' m) := by
    calc reducedOutShift c b' m ≤ b' := reducedOutShift_le c b' m
      _ ≤ w := hb'_le
      _ < 2 ^ w := Nat.lt_two_pow_self
  set limb := getLimb c evalVal m with hlimb_def
  set masked := limb &&& reducedOutMask c b' m with hmasked_def
  set shifted := masked <<< reducedOutShift c b' m with hshifted_def
  set next2 := packLimbs c (m + 1) (getLimb c evalVal) &&& (2 ^ b' - 1)
  have hmasked_lt : masked < 2 ^ c :=
    lt_of_le_of_lt Nat.and_le_right (reducedOutMask_lt c b' m)
  have hshifted_lt : shifted < 2 ^ w := by
    dsimp only [shifted, masked, reducedOutMask, reducedOutShift]
    split_ifs with hlt
    · have hand : limb &&& (2 ^ min c (b' - m * c) - 1) < 2 ^ (b' - m * c) := by
        rw [Nat.and_two_pow_sub_one_eq_mod]
        exact (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le
          (Nat.pow_le_pow_right two_pos (Nat.min_le_right _ _))
      rw [Nat.shiftLeft_eq]
      calc (limb &&& (2 ^ min c (b' - m * c) - 1)) * 2 ^ (m * c)
          < 2 ^ (b' - m * c) * 2 ^ (m * c) :=
            Nat.mul_lt_mul_of_pos_right hand (Nat.two_pow_pos _)
        _ = 2 ^ b' := by rw [← pow_add, Nat.sub_add_cancel (le_of_lt hlt)]
        _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hb'_le
    · have hmin : min c (b' - m * c) = 0 := by omega
      rw [hmin]
      simp only [pow_zero, Nat.sub_self, Nat.and_zero, Nat.zero_shiftLeft]
      exact Nat.two_pow_pos w
  have hnext2_eq : x.regs 2 ^^^ shifted = next2 := by
    rw [h2, ← packLimbs_and_mask_succ c b' m (getLimb c evalVal)]
  have hnext2_lt : next2 < 2 ^ w := by
    calc next2 < 2 ^ b' := and_two_pow_sub_one_lt _ b'
      _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hb'_le
  unfold packOutStep
  wram_exec [show x.regs (accReg m) = limb from hacc m hm, ← hmasked_def, ← hshifted_def,
    hnext2_eq]
  exact ⟨by wram_simp, by wram_simp, by wram_simp, fun i hi => by wram_simp [hacc i hi]; rfl, rfl⟩

private theorem packOutCode_exec {w t b' evalVal : ℕ}
    (hc_lt : 2 * reducedChunkBits t < w)
    (hb'_le : b' ≤ w)
    (heval_lt : evalVal < 2 ^ (reducedLimbCount t * reducedChunkBits t))
    (x : Data 240)
    (hacc : ∀ i < reducedLimbCount t,
      x.regs (accReg i) = getLimb (reducedChunkBits t) evalVal i) :
    let L := reducedLimbCount t
    ∃ y, Exec w (packOutCode t b') x y (1 + (L * 5 + 1)) ∧
      y.regs 0 = x.regs 0 ∧
      y.regs 1 = x.regs 1 ∧
      y.regs 2 = evalVal &&& (2 ^ b' - 1) ∧
      y.mem = x.mem := by
  intro L
  set c := reducedChunkBits t
  have hfit_0 : Fits w 0 := Nat.two_pow_pos w
  set s1 := x.set 2 0
  have e1 : Exec w (.op (.const 2 0) : Code .exact 240) x s1 1 := Exec.const hfit_0
  let P (n : ℕ) (z : Data 240) : Prop :=
    z.regs 0 = x.regs 0 ∧
    z.regs 1 = x.regs 1 ∧
    z.regs 2 = packLimbs c n (getLimb c evalVal) &&& (2 ^ b' - 1) ∧
    (∀ i < L, z.regs (accReg i) = getLimb c evalVal i) ∧
    z.mem = x.mem
  have hP0 : P 0 s1 := by
    refine ⟨by simp +decide [s1], by simp +decide [s1], by simp +decide [s1, packLimbs],
      fun i hi => ?_, rfl⟩
    dsimp only [s1, Data.set]
    rw [Function.update_of_ne (accReg_ne_low i (by decide))]
    exact hacc i hi
  obtain ⟨y, e2, hy0, hy1, hy2, _, hymem⟩ :=
    seqAsc_exec (packOutStep c b') 5 P L
      (fun m hm z ⟨hz0, hz1, hz2, hz_acc, hz_mem⟩ => by
        obtain ⟨z', hz'_exec, hz'0, hz'1, hz'2, hz'_acc, hz'_mem⟩ :=
          packOutStep_exec hc_lt hb'_le m hm z hz2 hz_acc
        exact ⟨z', hz'_exec, hz'0.trans hz0, hz'1.trans hz1, hz'2, hz'_acc, hz'_mem.trans hz_mem⟩)
      hP0
  refine ⟨y, e1.seq e2, hy0, hy1, ?_, hymem⟩
  rw [hy2, packLimbs_getLimb (reducedChunkBits_pos t) L heval_lt]

/-- Complete deterministic Word-RAM hash evaluation program `evalCode w w₀ b b' k` on `Data 240`:
reduces `reg 1` via Stage 1 (`reduceKeyCode`), unpacks limbs and sets up Horner constants via
Stage 2 (`initLimbsCode`, `hornerSetupCode`), runs `k` Horner steps via Stage 3 (`hornerCode`),
and packs the low `b'` bits into `reg 2` via Stage 4 (`packOutCode`). -/
@[expose] def evalCode (w w₀ b b' k : ℕ) : Code .exact 240 :=
  let t := reducedTrinomialStep w₀ b b'
  .seq (reduceKeyCode w₀ b)
  (.seq (initLimbsCode t)
  (.seq (hornerSetupCode w w₀ b b' k)
  (.seq (hornerCode t k)
        (packOutCode t b'))))

/-- Exact instruction count of `evalCode w w₀ b b' k`. -/
@[expose] def evalSteps (w₀ b b' k : ℕ) : ℕ :=
  let t := reducedTrinomialStep w₀ b b'
  let L := reducedLimbCount t
  39 + ((L * 5 + 1) + (8 + ((k * hornerStepSteps t + 1) + (1 + (L * 5 + 1)))))

/-- Parameter-independent `O(k)` upper bound `47250 * k + 591` on `evalSteps w₀ b b' k`. -/
@[expose] def evalBound (k : ℕ) : ℕ :=
  47250 * k + 591

/-- **`evalSteps w₀ b b' k` is `O(k)` (`evalSteps_le`)**:
for all `w₀, b, b', k : ℕ`, `evalSteps w₀ b b' k ≤ evalBound k = 47250 * k + 591`. -/
theorem evalSteps_le (w₀ b b' k : ℕ) : evalSteps w₀ b b' k ≤ evalBound k := by
  dsimp only [evalSteps, hornerStepSteps, evalBound]
  have hL : reducedLimbCount (reducedTrinomialStep w₀ b b') ≤ 54 :=
    reducedLimbCount_le (reducedTrinomialStep w₀ b b')
  have hstep : 2 * reducedLimbCount (reducedTrinomialStep w₀ b b') * 1 + 1 +
      ((reducedLimbCount (reducedTrinomialStep w₀ b b') *
        (reducedLimbCount (reducedTrinomialStep w₀ b b') * 13 + 1) + 1) +
        (reducedLimbCount (reducedTrinomialStep w₀ b b') * 6 + 1)) ≤ 47250 := by
    nlinarith
  have hmul : k * (2 * reducedLimbCount (reducedTrinomialStep w₀ b b') * 1 + 1 +
      ((reducedLimbCount (reducedTrinomialStep w₀ b b') *
        (reducedLimbCount (reducedTrinomialStep w₀ b b') * 13 + 1) + 1) +
        (reducedLimbCount (reducedTrinomialStep w₀ b b') * 6 + 1))) ≤ k * 47250 :=
    Nat.mul_le_mul_left k hstep
  omega

/-- **Deterministic execution of `evalCode w w₀ b b' k`**:
evaluates `(reducedPolyHash U w₀ b b' k θ u).val` into `reg 2` in `evalSteps w₀ b b' k`
instructions while preserving `reg 0 = base` and all memory. -/
theorem evalCode_exec {base w U w₀ b b' k : ℕ}
    (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (hU : U ≤ 2 ^ w₀) (hb' : b' ≤ w)
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k))
    (θ : ReducedPolySeed w₀ b b' k) (u : Fin U) (x : Data 240)
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = u.val)
    (htab : TableRep base w w₀ b b' k x.mem)
    (hseed : SeedRep base w₀ b b' k θ x.mem) :
    ∃ y, Exec w (evalCode w w₀ b b' k) x y (evalSteps w₀ b b' k) ∧
      y.regs 0 = base ∧
      y.regs 2 = (reducedPolyHash U w₀ b b' k θ u).val ∧
      y.mem = x.mem := by
  set t := reducedTrinomialStep w₀ b b'
  set c := reducedChunkBits t
  set L := reducedLimbCount t
  have hu_lt_w0 : u.val < 2 ^ w₀ := lt_of_lt_of_le u.isLt hU
  have hα_eq : x.mem (x.regs 0) = θ.1.val := by rw [h0, hseed.1]
  have hα_lt : x.mem (x.regs 0) < 2 ^ (w₀ - 1) := by rw [hα_eq]; exact θ.1.isLt
  have hu_reg1 : x.regs 1 < 2 ^ w₀ := by rw [h1]; exact hu_lt_w0
  obtain ⟨y1, e1, hy1_0, hy1_3, hy1_mem⟩ :=
    reduceKeyCode_exec hw₀_pos hw₀ x hα_lt hu_reg1
  rw [h0] at hy1_0
  set r := multiplyShiftReduced U w₀ (3 * b) θ.1 u
  have hr_eq : oddMulModWord w₀ (x.mem (x.regs 0)) (x.regs 1) >>> (w₀ - min w₀ (3 * b)) =
      r.val := by
    rw [hα_eq, h1, show w₀ - min w₀ (3 * b) = w₀ - 3 * b by omega]
    exact oddMulModWord_shiftRight_eq_multiplyShiftReduced hw₀_pos θ.1 u
  rw [hr_eq] at hy1_3
  have hr_lt_w : r.val < 2 ^ w :=
    lt_of_lt_of_le r.isLt
      (Nat.pow_le_pow_right two_pos ((Nat.min_le_left w₀ (3 * b)).trans hw₀))
  obtain ⟨y2, e2, hy2_0, hy2_xReg, hy2_accReg, hy2_mem⟩ :=
    initLimbsCode_exec hc_lt hr_lt_w y1 hy1_3
  rw [hy1_0] at hy2_0
  obtain ⟨y3, e3, hy3_0, hy3_4, hy3_5, hy3_6, hy3_7, hy3_8, hy3_9, hy3_18, hy3_high, hy3_mem⟩ :=
    hornerSetupCode_exec hc_lt hfit_space y2 hy2_0
  have hy3_consts : HornerConsts base w w₀ b b' k r.val y3 :=
    ⟨hy3_0, hy3_4, hy3_5, hy3_6, hy3_7, hy3_8, hy3_9, hy3_18, fun m hm =>
      (hy3_high (xReg m) (by dsimp [xReg]; omega)).trans (hy2_xReg m hm)⟩
  have hy3_acc0 : ∀ m < L, y3.regs (accReg m) = 0 := fun m hm =>
    (hy3_high (accReg m) (by dsimp [accReg]; omega)).trans (hy2_accReg m hm)
  have hmem3 : y3.mem = x.mem := hy3_mem.trans (hy2_mem.trans hy1_mem)
  obtain ⟨y4, e4, hy4_consts, hy4_acc, hy4_mem⟩ :=
    hornerCode_exec hc_lt hfit_space θ r y3 hy3_consts (hmem3 ▸ htab) (hmem3 ▸ hseed) hy3_acc0
  set evalVal := (trinomialPolyEval t k (2 ^ min w₀ (3 * b)) θ.2 r).val
  have heval_lt : evalVal < 2 ^ (L * c) := by
    rw [reducedLimbCount_mul_chunkBits]
    exact (trinomialPolyEval t k (2 ^ min w₀ (3 * b)) θ.2 r).isLt
  obtain ⟨y5, e5, hy5_0, _, hy5_2, hy5_mem⟩ :=
    packOutCode_exec hc_lt hb' heval_lt y4 hy4_acc
  refine ⟨y5, e1.seq (e2.seq (e3.seq (e4.seq e5))),
    hy5_0.trans hy4_consts.1,
    ?_,
    hy5_mem.trans (hy4_mem.trans hmem3)⟩
  rw [hy5_2]
  exact (val_trinomialPolyHash t k (2 ^ min w₀ (3 * b)) b' θ.2 r).symm

/-- `ExecWithin` wrapper for `evalCode_exec`. -/
theorem evalCode_execWithin {base w U w₀ b b' k : ℕ}
    (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (hU : U ≤ 2 ^ w₀) (hb' : b' ≤ w)
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k))
    (θ : ReducedPolySeed w₀ b b' k) (u : Fin U) (x : Data 240)
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = u.val)
    (htab : TableRep base w w₀ b b' k x.mem)
    (hseed : SeedRep base w₀ b b' k θ x.mem) :
    ∃ y, ExecWithin w (evalCode w w₀ b b' k) x y (evalSteps w₀ b b' k) ∧
      y.mem = x.mem ∧
      y.regs 0 = base ∧
      y.regs 2 = (reducedPolyHash U w₀ b b' k θ u).val := by
  obtain ⟨y, hex, hy0, hy2, hymem⟩ :=
    evalCode_exec hw₀_pos hw₀ hU hb' hc_lt hfit_space θ u x h0 h1 htab hseed
  exact ⟨y, hex.within, hymem, hy0, hy2⟩

/-! ## Section 5: Packaging as `HashFamily.WordRAM.Impl` -/

/-- Package `ReducedKWise` into a reusable `HashFamily.WordRAM.Impl` certificate over
`Basis.exact` on `Data 240`. -/
@[expose] noncomputable def impl {w base U w₀ b b' k : ℕ}
    (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (hU : U ≤ 2 ^ w₀) (hb' : b' ≤ w)
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k)) :
    Impl .exact 240 0 w base U (2 ^ b') ![] where
  Seed := ReducedPolySeed w₀ b b' k
  eval := reducedPolyHash U w₀ b b' k
  space := space w w₀ b b' k
  tableRep := TableRep base w w₀ b b' k
  seedRep := SeedRep base w₀ b b' k
  baseReg := 0
  keyReg := 1
  outReg := 2
  initParams := ![]
  key_ne_base := by decide
  params_ne_base j := Fin.elim0 j
  fits_space := hfit_space
  fits_tag := by
    have : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right two_pos (hw₀_pos.trans_le hw₀)
    change 1 < 2 ^ w
    omega
  fits_key u := by
    have hu_lt : u.val < 2 ^ w₀ := lt_of_lt_of_le u.isLt hU
    exact lt_of_lt_of_le hu_lt (Nat.pow_le_pow_right two_pos hw₀)
  addReg := Op.exactBin .add
  addReg_eval _ _ _ hfit := Data.put_of_fits hfit
  initTableCode := initTableCode w w₀ b b' k
  initTableSteps := initTableSteps w₀ b b'
  resampleCode := resampleCode w₀ b b' k
  resampleSteps := resampleSteps w₀ b b' k
  evalCode := evalCode w w₀ b b' k
  evalSteps := evalSteps w₀ b b' k
  initTable_exec {x} _ hbase _ _ := by
    obtain ⟨y, hex, hy0, htab, hmod⟩ :=
      initTableCode_execWithin hbase (le_of_lt hc_lt) hfit_space
    refine ⟨y, hex, hy0, htab, ?_⟩
    intro a ha
    rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
    apply hmod a
    rcases ha with hlt | hge
    · exact Or.inl (lt_of_lt_of_le hlt (Nat.le_add_right base _))
    · exact Or.inr hge
  resample_exec {x} _ hbase htab := by
    refine Impl.resample_exec_of_execRand
      (extractSeed base w₀ b b' k)
      (resampleCode_execRand hbase hw₀ (le_of_lt hc_lt) hfit_space)
      (map_extractSeed_eval_resampleComp base w₀ b b' k x) ?_
    intro z hz
    obtain ⟨hz0, htab', hseed', hframe, hsteps⟩ :=
      mem_support_resampleComp hbase htab hz
    refine ⟨hz0, htab', hseed', ?_, le_of_eq hsteps⟩
    intro a ha
    rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
    apply hframe a
    rcases ha with hlt | hge
    · exact Or.inl hlt
    · exact Or.inr (le_trans (Nat.add_le_add_left (Nat.le_add_right _ _) base) hge)
  eval_exec θ u {x} _ hbase hkey htab hseed :=
    evalCode_execWithin hw₀_pos hw₀ hU hb' hc_lt hfit_space θ u x hbase hkey htab hseed

/-- Standard-basis lifting of `impl`. -/
@[expose] noncomputable def implStandard {w base U w₀ b b' k : ℕ}
    (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (hU : U ≤ 2 ^ w₀) (hb' : b' ≤ w)
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k)) :
    Impl .standard 240 0 w base U (2 ^ b') ![] :=
  (impl hw₀_pos hw₀ hU hb' hc_lt hfit_space).toStandard

end Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise

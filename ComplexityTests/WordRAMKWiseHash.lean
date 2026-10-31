/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.Hashing.KWise
public import Complexity.Algorithms.WordRAM.Hashing.Tabulation

/-!
# Concrete interpreter and non-vacuity tests for `Hashing.KWise` and `Hashing.Tabulation`

Verifies both concrete `Cslib.WordRAM.Code.eval` execution and theorem-level non-vacuity of:
1. `Cslib.Algorithms.WordRAM.Hashing.KWise`:
   - `initTableCode` and `evalCode` executed via `Code.eval` at `k = 5` for both `b = 1, L = 2`
     (`n_max = 8`, `U = 4`, `M = 2`) and `b = 2, L = 1` (`n_max = 64`, `U = 4`, `M = 2`), and at
     `t = 1` (`q = 6`, `b = 2`, `L = 3`, `n_max = 64`, `U = 16`, `M = 3`, `k = 5`), agreeing on
     every tested key with direct unchunked `reduceTrinomialCode`/`clmul` Horner evaluation while
     preserving boundary sentinels;
   - non-vacuous instantiations of `initTableCode_execWithin`, `resampleCode_execRand`,
     `initCode_execRandWithin`, `evalCode_execWithin`, and `isKWiseIndependentHash_eval` at `k = 5`,
     `U = 1000`, `M = 10`, `n_max = 64`, `w = 64`.
2. `Cslib.Algorithms.WordRAM.Hashing.Tabulation.RandomTable`:
   - `lookupCode` and `xorLookupCode` executed via `Code.eval` on a concrete table of size
     `2 ^ 3 = 8`;
   - non-vacuous instantiations of `resampleCode_execRand`, `map_extractTable_eval_resampleComp`,
     `resampleCode_execRandWithin`, `lookupCode_exec`, and `xorLookupCode_exec`.
3. `Cslib.Algorithms.WordRAM.Hashing.Tabulation.TabulatedOddStride`:
   - `evalCode 3` executed via `Code.eval` on concrete character tables (`d = 3`, `b = 1`, `M = 3`),
     matching `tabulatedOddStride` and producing odd strides whose linear probe sequence `probeSeq`
     visits all `2 ^ M = 8` table slots;
   - non-vacuous instantiations of `initCode_execRand`, `map_extractTable_eval_initComp`,
     `initCode_execRandWithin`, `evalCode_execWithin`, and `bijective_probeSeq`.
-/

@[expose] public section

namespace ComplexityTests.WordRAMKWiseHash

open Cslib Cslib.Probability Cslib.WordRAM
open Cslib.Algorithms.WordRAM.Hashing
open Cslib.Algorithms.WordRAM.Hashing.Tabulation

/-! ## Helper for compacting interpreter state between `Code.eval` calls -/

/-- Rebuild a natural number from `0` and `Nat.succ` so that `Function.update` closures in its
originating expression are eliminated during kernel reduction. -/
def forceNat : ℕ → Option ℕ
  | 0 => some 0
  | n + 1 => (forceNat n).map Nat.succ

/-- Eagerly force every element of a list of natural numbers via `forceNat`. -/
def forceList : List ℕ → Option (List ℕ)
  | [] => some []
  | x :: xs =>
    match forceNat x, forceList xs with
    | some y, some ys => some (y :: ys)
    | _, _ => none

/-- Tabulate registers `0..r - 1` and memory `0..memCap - 1` into flat lists between interpreter
calls so `Function.update` closures do not accumulate across steps. -/
def compactData {r : ℕ} (memCap : ℕ) (d : Data r) : Option (Data r) := do
  let rs ← forceList ((List.finRange r).map d.regs)
  let ms ← forceList ((List.range memCap).map d.mem)
  let tail ← forceNat (d.mem memCap)
  pure
    { regs := fun i => rs.getD i.val 0
      mem := fun a => if a < memCap then ms.getD a 0 else tail }

/-! ## 1. `KWise`: concrete `Code.eval` execution matching unchunked trinomial Horner evaluation -/

/-- Structurally recursive fuel-bounded carryless multiplication for kernel `decide` reduction. -/
def clmulFuel : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, a, b =>
    if b = 0 then 0
    else (if b % 2 = 1 then a else 0) ^^^ (clmulFuel fuel a (b / 2) <<< 1)

/-- `clmulFuel fuel a b` agrees with `clmul a b` whenever `b < 2 ^ fuel`. -/
theorem clmulFuel_eq_clmul : ∀ (fuel a b : ℕ), b < 2 ^ fuel → clmulFuel fuel a b = clmul a b
  | 0, a, b, hb => by
    have hb0 : b = 0 := by omega
    subst hb0
    simp [clmulFuel]
  | fuel + 1, a, b, hb => by
    rcases eq_or_ne b 0 with rfl | hne
    · simp [clmulFuel]
    · have hb_div : b / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hb
        omega
      rw [clmulFuel, clmul, ite_eq_right hne, ite_eq_right hne,
        clmulFuel_eq_clmul fuel a (b / 2) hb_div]

/-- Sample `5`-tuple of coefficients in `Fin 4` (`t = 0`, `q = 2`, `2 ^ q = 4`). -/
def sampleCoeffs5 : Fin 5 → Fin 4
  | ⟨0, _⟩ => ⟨3, by decide⟩
  | ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨2, _⟩ => ⟨2, by decide⟩
  | ⟨3, _⟩ => ⟨3, by decide⟩
  | ⟨_, _⟩ => ⟨2, by decide⟩

/-- Computable unchunked reference Horner evaluator for `k = 5` over `TrinomialField t` using
`clmulFuel 6` and `reduceTrinomialCode` directly (without limb splitting), masked to `M` bits. -/
def trinomialHornerRef5 (t M : ℕ) (c : Fin 5 → Fin (2 ^ (2 * 3 ^ t))) (u : ℕ) : ℕ :=
  let a4 := (c ⟨4, by decide⟩).val
  let a3 := reduceTrinomialCode t (clmulFuel 6 a4 u) ^^^ (c ⟨3, by decide⟩).val
  let a2 := reduceTrinomialCode t (clmulFuel 6 a3 u) ^^^ (c ⟨2, by decide⟩).val
  let a1 := reduceTrinomialCode t (clmulFuel 6 a2 u) ^^^ (c ⟨1, by decide⟩).val
  let a0 := reduceTrinomialCode t (clmulFuel 6 a1 u) ^^^ (c ⟨0, by decide⟩).val
  a0 &&& (2 ^ M - 1)

/-- Write `5` coefficients `c : Fin 5 → Fin n` into `[base + 8, base + 13)` of `d.mem`. -/
def writeSampleCoeffs5 {n : ℕ} (base : ℕ) (c : Fin 5 → Fin n) (d : Data 18) : Data 18 :=
  ((((d.write (base + 8) (c ⟨0, by decide⟩).val).write (base + 9) (c ⟨1, by decide⟩).val).write
    (base + 10) (c ⟨2, by decide⟩).val).write (base + 11) (c ⟨3, by decide⟩).val).write
    (base + 12) (c ⟨4, by decide⟩).val

/-- Run `KWise.initTableCode 5` with `(base, n_max, U, M)` in registers `0..3`, populate `c` via
`writeSampleCoeffs5`, and evaluate `KWise.evalCode 5` via `Code.eval` on a list of keys `us`,
verifying that boundary sentinels at `base - 1` and `base + KWise.space n_max 5` are preserved both
after `initTableCode 5` and after each `evalCode 5` invocation. -/
def runKWiseEval5 {n : ℕ} (w fuel n_max U M base : ℕ) (c : Fin 5 → Fin n) (us : List ℕ) :
    Option (List ℕ × ℕ × ℕ) := do
  let sp := KWise.space n_max 5
  let d0 : Data 18 :=
    ((((((Data.init [] : Data 18).set 0 base).set 1 n_max).set 2 U).set 3 M).write
      (base - 1) 77).write (base + sp) 88
  let (d1, _) ← (KWise.initTableCode 5).eval w fuel d0
  let d2 ← compactData (base + sp + 2) (writeSampleCoeffs5 base c d1)
  let sLo ← forceNat (d2.mem (base - 1))
  let sHi ← forceNat (d2.mem (base + sp))
  let outs ← us.mapM (fun u => do
    let dIn := (d2.set 0 base).set KWise.regKey u
    let (dOut, _) ← (KWise.evalCode 5).eval w fuel dIn
    if dOut.mem (base - 1) = sLo ∧ dOut.mem (base + sp) = sHi then
      forceNat (dOut.regs KWise.regOut)
    else
      none)
  pure (outs, sLo, sHi)

/-- Concrete `Code.eval` test at `k = 5, b = 1, L = 2` (`n_max = 8`, `U = 4`, `M = 2`, `base = 10`):
`KWise.initTableCode 5` builds the `4`-entry carryless multiplication table and metadata in
`[10, 27)`, and `KWise.evalCode 5` (performing `2 × 2` multi-limb chunk multiplication at each of
the `5` Horner steps) matches `trinomialHornerRef5 0 2 sampleCoeffs5 u` on all keys
`u ∈ [0, 1, 2, 3]` while preserving sentinels at addresses `9` (`77`) and `27` (`88`). -/
theorem kwise_eval5_b1_concrete :
    runKWiseEval5 16 16 8 4 2 10 sampleCoeffs5 [0, 1, 2, 3] =
      some ([0, 1, 2, 3].map (trinomialHornerRef5 0 2 sampleCoeffs5), 77, 88) := by
  decide +kernel

/-- Concrete `Code.eval` test at `k = 5, b = 2, L = 1` (`n_max = 64`, `U = 4`, `M = 2`, `base = 4`):
`KWise.initTableCode 5` builds the `16`-entry carryless multiplication table in `[4, 33)`, and
`KWise.evalCode 5` matches `trinomialHornerRef5 0 2 sampleCoeffs5 u` on all keys `u ∈ [0, 1, 2, 3]`
while preserving sentinels at addresses `3` (`77`) and `33` (`88`). -/
theorem kwise_eval5_b2_concrete :
    runKWiseEval5 16 32 64 4 2 4 sampleCoeffs5 [0, 1, 2, 3] =
      some ([0, 1, 2, 3].map (trinomialHornerRef5 0 2 sampleCoeffs5), 77, 88) := by
  decide +kernel

/-- Sample `5`-tuple of coefficients in `Fin 64` (`t = 1`, `q = 6`, `2 ^ q = 64`) for testing
`k = 5` with `3 × 3` multi-limb multiplication over `TrinomialField 1` (`X ^ 6 + X ^ 3 + 1`). -/
def sampleCoeffs5T1 : Fin 5 → Fin 64
  | ⟨0, _⟩ => ⟨13, by decide⟩
  | ⟨1, _⟩ => ⟨42, by decide⟩
  | ⟨2, _⟩ => ⟨7, by decide⟩
  | ⟨3, _⟩ => ⟨59, by decide⟩
  | ⟨_, _⟩ => ⟨25, by decide⟩

/-- Run `KWise.initTableCode 5` and `KWise.evalCode 5` at `t = 1, q = 6, b = 2, L = 3`
(`n_max = 64, U = 16, M = 3, base = 4`). -/
def runKWiseEval5T1 (us : List ℕ) : Option (List ℕ × ℕ × ℕ) :=
  runKWiseEval5 16 32 64 16 3 4 sampleCoeffs5T1 us

/-- Concrete `Code.eval` test at `k = 5, t = 1, q = 6, b = 2, L = 3` (`3 × 3` limb multiplication
over `X ^ 6 + X ^ 3 + 1`): `KWise.evalCode 5` matches `trinomialHornerRef5 1 3 sampleCoeffs5T1` on
keys `u ∈ [0, 5, 11, 15]`. -/
theorem kwise_eval5_t1_b2_L3_concrete :
    runKWiseEval5T1 [0, 5, 11, 15] =
      some ([0, 5, 11, 15].map (trinomialHornerRef5 1 3 sampleCoeffs5T1), 77, 88) := by
  decide +kernel

/-- Non-vacuous theorem-level instantiation of `KWise.initTableCode_execWithin`,
`KWise.resampleCode_execRand`, `KWise.initCode_execRandWithin`, `KWise.evalCode_execWithin`, and
the composed Word-RAM `k`-wise independence theorem `KWise.isKWiseIndependentHash_eval` at `k = 5`,
`U = 1000`, `M = 10`, `n_max = 64`, `w = 64`, `base = 0`. -/
theorem kwise_five_wise_wordram_nonvacuous (x : Data 18)
    (h0 : x.regs 0 = 0) (h1 : x.regs 1 = 64) (h2 : x.regs 2 = 1000) (h3 : x.regs 3 = 10) :
    (∃ y : Data 18,
      ExecWithin 64 (KWise.initTableCode 5) x y (KWise.initTableSteps 64 1000 10) ∧
      KWise.TableRep 0 (KWise.chunkBits 64) 1000 10 5 y.mem) ∧
    ExecRandWithin 64 (KWise.initCode 5) x
      (fun y =>
        KWise.Rep 0 (KWise.chunkBits 64) 1000 10 5
          (KWise.extractSeeds 0 1000 10 5 y.mem) y.mem ∧
        y.regs 0 = 0 ∧
        (∀ a, (a < 0 ∨ 0 + KWise.space 64 5 ≤ a) → y.mem a = x.mem a))
      (KWise.initTableSteps 64 1000 10 + 35) 5 ∧
    (∀ y : Data 18,
      KWise.TableRep 0 (KWise.chunkBits 64) 1000 10 5 y.mem →
      y.regs 0 = 0 →
      (∀ (T : Finset (Fin 1000)), Finset.card T ≤ 5 →
        ((KWise.resampleComp 0 1000 10 5 y).eval).map
            (fun z => T.restrict (KWise.evalHashOut 64 0 5 1000 10 z.1)) =
          PMF.uniformOfFintype (T → Fin (2 ^ 10))) ∧
      ExecRand 64 (KWise.resampleCode 5) y (KWise.resampleComp 0 1000 10 5 y) ∧
      ((KWise.resampleComp 0 1000 10 5 y).eval).map
          (fun z => KWise.extractSeeds 0 1000 10 5 z.1.mem) =
        PMF.uniformOfFintype (Fin 5 → Fin (2 ^ trinomialDeg 1000 10)) ∧
      ExecRandWithin 64 (KWise.resampleCode 5) y
        (fun z =>
          KWise.Rep 0 (KWise.chunkBits 64) 1000 10 5
            (KWise.extractSeeds 0 1000 10 5 z.mem) z.mem ∧
          z.regs 0 = 0 ∧
          (∀ a, (a < 0 + 8 ∨ 0 + 8 + 5 ≤ a) → z.mem a = y.mem a))
        35 5 ∧
      (∀ (c : Fin 5 → Fin (2 ^ trinomialDeg 1000 10)) (u : Fin 1000) (x_eval : Data 18),
        KWise.Rep 0 (KWise.chunkBits 64) 1000 10 5 c x_eval.mem →
        x_eval.regs 0 = 0 →
        x_eval.regs 1 = u.val →
        ∃ y_eval : Data 18,
          ExecWithin 64 (KWise.evalCode 5) x_eval y_eval (KWise.evalSteps 64 1000 10 5) ∧
          y_eval.regs 0 = 0 ∧
          y_eval.regs 1 = u.val ∧
          y_eval.regs 2 =
            (trinomialPolyHash (trinomialStep 1000 10) 5 1000 10 c u).val ∧
          y_eval.mem = x_eval.mem)) := by
  have htr : trinomialDeg 1000 10 = 18 := by
    have hclog : Nat.clog 2 (max 1000 2) ≤ 10 :=
      (Nat.clog_le_iff_le_pow one_lt_two).mpr (by decide)
    have ht : trinomialTargetBits 1000 10 = 10 := by
      rw [trinomialTargetBits]; omega
    have hs : trinomialStep 1000 10 = 2 := by
      rw [trinomialStep, ht, trinomialStepAux, trinomialStepAux, trinomialStepAux]; decide
    rw [trinomialDeg, hs]; decide
  have hw : 2 * trinomialDeg 1000 10 ≤ 64 := by omega
  have hfit_sp : Fits 64 (0 + KWise.space 64 5) := by
    rw [fits_iff]
    dsimp [KWise.space, KWise.spaceFromB, KWise.chunkBits]
    decide
  have hfit_end : Fits 64 (0 + 8 + 5) := by rw [fits_iff]; decide
  have hfit_n : Fits 64 (max 64 2) := by rw [fits_iff]; decide
  have hfit_U : Fits 64 (max 1000 2 + 1) := by rw [fits_iff]; decide
  have hfit_q : Fits 64 (2 ^ trinomialDeg 1000 10) := by
    rw [htr, fits_iff]; decide
  obtain ⟨y, hy_exec, hy_tab, -, -⟩ :=
    KWise.initTableCode_execWithin h0 h1 h2 h3 hfit_sp hfit_n hfit_U hfit_q
  refine ⟨⟨y, hy_exec, hy_tab⟩,
    KWise.initCode_execRandWithin h0 h1 h2 h3 hfit_sp hfit_n hfit_U hfit_q,
    fun y' htab' h0' =>
      ⟨fun T hT => KWise.isKWiseIndependentHash_eval htab' h0' hw hfit_sp hT,
       KWise.resampleCode_execRand htab' h0' hfit_end hfit_q,
       KWise.map_extractSeeds_eval_resampleComp 0 1000 10 5 y',
       KWise.resampleCode_execRandWithin htab' h0' hfit_end hfit_q,
       fun c u x_eval hrep hx0 hx1 =>
         KWise.evalCode_execWithin u hrep hx0 hx1 hw hfit_sp⟩⟩

/-! ## 2. `RandomTable`: concrete `Code.eval` execution and theorem instantiations -/

/-- Populate `Z = [6, 3, 7, 1, 5, 0, 4, 2]` at `base = 4` (`M = 3`) and run
`RandomTable.lookupCode` and `RandomTable.xorLookupCode` via `Code.eval`. -/
def runRandomTableLookups : Option (List ℕ × List ℕ) := do
  let base := 4
  let d0 : Data 6 :=
    (((((((((Data.init [] : Data 6).write 4 6).write 5 3).write 6 7).write 7 1).write
      8 5).write 9 0).write 10 4).write 11 2)
  let lookups ← ([0, 2, 4, 7] : List ℕ).mapM (fun idx => do
    let dIn := (d0.set RandomTable.regBase base).set RandomTable.regIdx idx
    let (dOut, _) ← RandomTable.lookupCode.eval 16 8 dIn
    forceNat (dOut.regs RandomTable.regOut))
  let xorLookups ← ([(5, 0), (5, 2), (3, 4), (7, 7)] : List (ℕ × ℕ)).mapM (fun (f, g) => do
    let dIn := ((d0.set RandomTable.regBase base).set RandomTable.regIdx g).set
      RandomTable.regOut f
    let (dOut, _) ← RandomTable.xorLookupCode.eval 16 8 dIn
    forceNat (dOut.regs RandomTable.regOut))
  pure (lookups, xorLookups)

/-- Concrete `Code.eval` verification of `RandomTable.lookupCode` (`Z[idx]`) and
`RandomTable.xorLookupCode` (`f ^^^ Z[g]`). -/
theorem randomTable_lookup_and_xorLookup_concrete :
    runRandomTableLookups =
      some ([6, 7, 5, 2], [5 ^^^ 6, 5 ^^^ 7, 3 ^^^ 5, 7 ^^^ 2]) := by
  decide

/-- Non-vacuous theorem-level instantiation of `RandomTable.resampleCode_execRand`,
`RandomTable.map_extractTable_eval_resampleComp`, `RandomTable.resampleCode_execRandWithin`,
`RandomTable.lookupCode_exec`, and `RandomTable.xorLookupCode_exec` at `M = 4` (`2 ^ M = 16`),
`base = 10`, `w = 16`. -/
theorem randomTable_wordram_nonvacuous (x : Data 6)
    (h0 : x.regs RandomTable.regBase = 10) (h1 : x.regs RandomTable.regM = 4) :
    ExecRand 16 RandomTable.resampleCode x (RandomTable.resampleComp 10 4 x) ∧
    ((RandomTable.resampleComp 10 4 x).eval).map (fun z => RandomTable.extractTable 10 4 z.1.mem) =
      PMF.uniformOfFintype (Fin 16 → Fin 16) ∧
    ExecRandWithin 16 RandomTable.resampleCode x
      (fun y =>
        RandomTable.Rep 10 4 (RandomTable.extractTable 10 4 y.mem) y.mem ∧
        y.regs RandomTable.regBase = 10 ∧
        (∀ a, (a < 10 ∨ 10 + 16 ≤ a) → y.mem a = x.mem a))
      87 16 ∧
    (∀ (Z : Fin 16 → Fin 16) (idx : Fin 16) (y : Data 6),
      RandomTable.Rep 10 4 Z y.mem →
      y.regs RandomTable.regBase = 10 → y.regs RandomTable.regIdx = idx.val →
      Exec 16 RandomTable.lookupCode y (RandomTable.lookupData y) 2 ∧
      (RandomTable.lookupData y).regs RandomTable.regOut = (Z idx).val ∧
      (RandomTable.lookupData y).mem = y.mem) ∧
    (∀ (Z : Fin 16 → Fin 16) (idx fx : Fin 16) (y : Data 6),
      RandomTable.Rep 10 4 Z y.mem →
      y.regs RandomTable.regBase = 10 → y.regs RandomTable.regIdx = idx.val →
      y.regs RandomTable.regOut = fx.val →
      Exec 16 RandomTable.xorLookupCode y (RandomTable.xorLookupData y) 3 ∧
      (RandomTable.xorLookupData y).regs RandomTable.regOut = fx.val ^^^ (Z idx).val ∧
      (RandomTable.xorLookupData y).mem = y.mem) := by
  have hfit_end : Fits 16 (10 + 2 ^ 4) := by rw [fits_iff]; decide
  have hfit_pow : Fits 16 (2 ^ 4) := by rw [fits_iff]; decide
  refine ⟨RandomTable.resampleCode_execRand h0 h1 hfit_end hfit_pow,
    RandomTable.map_extractTable_eval_resampleComp 10 4 x,
    RandomTable.resampleCode_execRandWithin h0 h1 hfit_end hfit_pow,
    fun Z idx y hrep hy0 hy1 => ?_,
    fun Z idx fx y hrep hy0 hy1 hy2 => ?_⟩
  · obtain ⟨he, ho, -, hm⟩ := RandomTable.lookupCode_exec hrep idx hy0 hy1 hfit_end
    exact ⟨he, ho, hm⟩
  · obtain ⟨he, ho, -, -, hm⟩ :=
      RandomTable.xorLookupCode_exec hrep idx fx hy0 hy1 hy2 hfit_end hfit_pow
    exact ⟨he, ho, hm⟩

/-! ## 3. `TabulatedOddStride`: concrete `Code.eval` execution and full-cycle permutation test -/

/-- Sample flat `3 * 2 ^ 1 = 6`-entry character table `T : Fin 6 → Fin 8` (`d = 3`, `b = 1`,
`M = 3`). -/
def sampleFlatCharTable : Fin 6 → Fin 8
  | ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩ => ⟨3, by decide⟩
  | ⟨2, _⟩ => ⟨2, by decide⟩
  | ⟨3, _⟩ => ⟨0, by decide⟩
  | ⟨4, _⟩ => ⟨3, by decide⟩
  | ⟨_, _⟩ => ⟨2, by decide⟩

/-- Populate the 4 header words `(b = 1, 2 ^ b = 2, 2 ^ b - 1 = 1, 2 ^ M - 1 = 7)` and the 6
entries of `sampleFlatCharTable` starting at `base = 2` (addresses `2..11`) and run
`TabulatedOddStride.evalCode 3` via `Code.eval` on all keys `u ∈ 0..7`. -/
def runTabulatedOddStrideEval : Option (List ℕ) := do
  let base := 2
  let d0 : Data 9 :=
    (((((((((((Data.init [] : Data 9).write 2 1).write 3 2).write 4 1).write 5 7).write
      6 1).write 7 3).write 8 2).write 9 0).write 10 3).write 11 2)
  (List.range 8).mapM (fun u => do
    let dIn := (d0.set TabulatedOddStride.regBase base).set TabulatedOddStride.regKey u
    let (dOut, _) ← (TabulatedOddStride.evalCode 3).eval 16 16 dIn
    forceNat (dOut.regs TabulatedOddStride.regOut))

/-- Concrete `Code.eval` verification of `TabulatedOddStride.evalCode 3`: on all `8` keys
`u ∈ 0..7`, `evalCode 3` matches
`(TabulatedOddStride.tabulatedOddStride 1 3 3 sampleFlatCharTable u).val` and always produces an odd
stride in `{1, 3, 5, 7}`. -/
theorem tabulatedOddStride_evalCode_matches_spec :
    runTabulatedOddStrideEval =
      some ((List.range 8).map (fun u =>
        (TabulatedOddStride.tabulatedOddStride 1 3 3 sampleFlatCharTable u).val)) ∧
    ∀ u : ℕ,
      (TabulatedOddStride.tabulatedOddStride 1 3 3 sampleFlatCharTable u).val % 2 = 1 := by
  refine ⟨by decide, fun u => TabulatedOddStride.odd_oddStride (by decide) _⟩

/-- Full-cycle permutation property on `Fin 8` (`M = 3`): for every starting slot `h₁ : ℕ` and
every raw tabulation sum `tab : ℕ`, the linear probe sequence `i ↦ probeSeq 3 h₁ tab i` is a
bijection on `Fin 8` (and concretely visits all `8` slots without repetition). -/
theorem tabulatedOddStride_probeSeq_full_cycle (h₁ tab : ℕ) :
    Function.Bijective (TabulatedOddStride.probeSeq 3 h₁ tab) ∧
    ((List.finRange 8).map (fun i =>
      (TabulatedOddStride.probeSeq 3 3
        (TabulatedOddStride.simpleTab 1 3 3 sampleFlatCharTable 5).val i).val)).Nodup :=
  ⟨TabulatedOddStride.bijective_probeSeq 3 h₁ tab, by decide⟩

/-- Non-vacuous theorem-level instantiation of `TabulatedOddStride.initCode_execRand`,
`TabulatedOddStride.map_extractTable_eval_initComp`, `TabulatedOddStride.initCode_execRandWithin`,
and `TabulatedOddStride.evalCode_execWithin` at `n_max = 16`, `d = 4`, `M = 5` (`2 ^ M = 32`),
`base = 0`, `w = 16`. -/
theorem tabulatedOddStride_wordram_nonvacuous (x : Data 9)
    (h0 : x.regs TabulatedOddStride.regBase = 0)
    (h1 : x.regs TabulatedOddStride.regKey = 16)
    (h2 : x.regs TabulatedOddStride.regOut = 5) :
    ExecRand 16 (TabulatedOddStride.initCode 4) x
      (TabulatedOddStride.initComp 0 16 4 5 x) ∧
    ((TabulatedOddStride.initComp 0 16 4 5 x).eval).map
        (fun z => TabulatedOddStride.extractTable 0 (TabulatedOddStride.charBits 16) 4 5 z.1.mem) =
      PMF.uniformOfFintype (Fin (4 * 2 ^ TabulatedOddStride.charBits 16) → Fin 32) ∧
    ExecRandWithin 16 (TabulatedOddStride.initCode 4) x
      (fun y =>
        TabulatedOddStride.Rep 0 (TabulatedOddStride.charBits 16) 4 5
          (TabulatedOddStride.extractTable 0 (TabulatedOddStride.charBits 16) 4 5 y.mem) y.mem ∧
        y.regs TabulatedOddStride.regBase = 0 ∧
        (∀ a, (a < 0 ∨ 0 + TabulatedOddStride.space 16 4 ≤ a) → y.mem a = x.mem a))
      (4 * Nat.log 2 (max 16 2) + 5 * (4 * 2 ^ TabulatedOddStride.charBits 16) + 30)
      (4 * 2 ^ TabulatedOddStride.charBits 16) ∧
    (∀ (T : Fin (4 * 2 ^ TabulatedOddStride.charBits 16) → Fin 32) (u : Fin 256) (y : Data 9),
      TabulatedOddStride.Rep 0 (TabulatedOddStride.charBits 16) 4 5 T y.mem →
      y.regs TabulatedOddStride.regBase = 0 →
      y.regs TabulatedOddStride.regKey = u.val →
      ∃ z : Data 9,
        ExecWithin 16 (TabulatedOddStride.evalCode 4) y z 53 ∧
        z.regs TabulatedOddStride.regOut =
          (TabulatedOddStride.tabulatedOddStride
            (TabulatedOddStride.charBits 16) 4 5 T u.val).val ∧
        z.regs TabulatedOddStride.regBase = 0 ∧
        z.mem = y.mem) := by
  have hfit_n : Fits 16 (max 16 2) := by rw [fits_iff]; decide
  have hfit_sp : Fits 16 (0 + TabulatedOddStride.space 16 4) := by
    rw [fits_iff]
    dsimp [TabulatedOddStride.space, TabulatedOddStride.spaceFromB, TabulatedOddStride.charBits]
    decide
  have hfit_powM : Fits 16 (2 ^ 5) := by rw [fits_iff]; decide
  have hfit_2powM : Fits 16 (2 * 2 ^ 5) := by rw [fits_iff]; decide
  have hfit_d : Fits 16 4 := by rw [fits_iff]; decide
  refine ⟨TabulatedOddStride.initCode_execRand h0 h1 h2 hfit_n hfit_sp hfit_powM hfit_d,
    TabulatedOddStride.map_extractTable_eval_initComp 0 16 4 5 x,
    TabulatedOddStride.initCode_execRandWithin h0 h1 h2 hfit_n hfit_sp hfit_powM hfit_d,
    fun T u y hrep hy0 hy1 => ?_⟩
  have hfit_u : Fits 16 u.val := by
    rw [fits_iff]
    have := u.isLt
    omega
  exact TabulatedOddStride.evalCode_execWithin hrep hy0 hy1 hfit_sp hfit_2powM hfit_d hfit_u

end ComplexityTests.WordRAMKWiseHash

end

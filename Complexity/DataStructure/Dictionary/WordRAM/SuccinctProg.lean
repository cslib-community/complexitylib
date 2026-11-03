/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Absorb
public import Complexity.Computability.WordRAM.Realization.Branch
public import Complexity.Computability.WordRAM.Realization.Loop
public import Complexity.Computability.WordRAM.Realization.Primitive
public import Complexity.Computability.WordRAM.Realization.Reindex
public import Complexity.Computability.WordRAM.Realization.While
public import Complexity.Computability.WordRAM.Realization.Witness
public import Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlotStore
import Complexity.Tactic.Realize

/-!
# `Memory.Prog` Bit-Packed Array Primitives and Slot Resolution via `realize`

This module wraps the overflow-free bit-packed array operations (`readPacked`, `writePacked`) and
the four dictionary arrays (`Quotients`, `Values`, `LocalMeta`, `GlobalMeta`) as `Memory.Prog`
operations with uniform `Realizes .exact` certificates, and realizes `readBucketCountProg` and
`resolveIndexedSlotProg` via the `realize` tactic.
-/

@[expose] public section

namespace Cslib.DataStructure.Dictionary.WordRAM.Succinct

open Cslib.WordRAM Cslib.WordRAM.ExactLog Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray

/-! ## Section 1: `readPackedProg` and `writePackedProg` in `Memory.Prog` -/

/-- `Memory.Prog` operation reading the `k`-bit entry at index `idx` from a bit-packed array at
`base + offset` on a `w`-bit machine. -/
def readPackedProg (base offset k w idx : ℕ) : Memory.Prog ℕ := do
  let wOff := wordOffset k w idx
  let bOff := bitOffset k w idx
  let k₀ := lowWidth k w idx
  let k₁ := highWidth k w idx
  let word₀ ← Memory.read (base + offset + wOff)
  let word₁ ← Memory.read (base + offset + wOff + 1)
  let low := (word₀ >>> bOff) &&& (2 ^ k₀ - 1)
  let high := (word₁ >>> 0) &&& (2 ^ k₁ - 1)
  pure (low ^^^ (high <<< k₀))

/-- `Memory.Prog` operation writing `val` (`< 2 ^ k`) into the `k`-bit entry at index `idx` of a
bit-packed array at `base + offset` on a `w`-bit machine. -/
def writePackedProg (base offset k w idx val : ℕ) : Memory.Prog Unit := do
  let wOff := wordOffset k w idx
  let bOff := bitOffset k w idx
  let k₀ := lowWidth k w idx
  let k₁ := highWidth k w idx
  let word₀ ← Memory.read (base + offset + wOff)
  let old₀ := (word₀ >>> bOff) &&& (2 ^ k₀ - 1)
  let val₀ := val &&& (2 ^ k₀ - 1)
  Memory.write (base + offset + wOff) (word₀ ^^^ ((old₀ ^^^ val₀) <<< bOff))
  let word₁ ← Memory.read (base + offset + wOff + 1)
  let old₁ := (word₁ >>> 0) &&& (2 ^ k₁ - 1)
  let val₁ := (val >>> k₀) &&& (2 ^ k₁ - 1)
  Memory.write (base + offset + wOff + 1) (word₁ ^^^ ((old₁ ^^^ val₁) <<< 0))

@[simp]
theorem clientResult_readPackedProg (base offset k w idx : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (readPackedProg base offset k w idx) =
      readPacked (base + offset) k w s.mem idx :=
  rfl

@[simp]
theorem clientState_readPackedProg (base offset k w idx : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readPackedProg base offset k w idx) = s :=
  rfl

@[simp]
theorem memoryCost_readPackedProg (base offset k w idx : ℕ) (s : Memory.State) :
    memoryCost (readPackedProg base offset k w idx) s = 2 :=
  rfl

@[simp]
theorem clientResult_writePackedProg (base offset k w idx val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (writePackedProg base offset k w idx val) = () :=
  rfl

@[simp]
theorem clientState_writePackedProg (base offset k w idx val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (writePackedProg base offset k w idx val) =
      { mem := writePacked (base + offset) k w s.mem idx val, frontier := s.frontier } :=
  rfl

@[simp]
theorem memoryCost_writePackedProg (base offset k w idx val : ℕ) (s : Memory.State) :
    memoryCost (writePackedProg base offset k w idx val) s = 4 :=
  rfl

theorem validHistory_readPackedProg {w base offset N k idx : ℕ} {s : Memory.State}
    (hw : 0 < w) (hidx : idx < N)
    (ha : base + offset + packedWords N k w ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (readPackedProg base offset k w idx)) := by
  have hlt := wordOffset_add_one_lt_packedWords (k := k) hw hidx
  change base + offset + wordOffset k w idx < s.frontier ∧
    base + offset + wordOffset k w idx + 1 < s.frontier ∧ True
  exact ⟨by omega, by omega, trivial⟩

theorem validHistory_writePackedProg {w base offset N k idx val : ℕ} {s : Memory.State}
    (hw : 0 < w) (hkw : k ≤ w) (hidx : idx < N)
    (hwf : Memory.WellFormed w s)
    (ha : base + offset + packedWords N k w ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (writePackedProg base offset k w idx val)) := by
  have hlt := wordOffset_add_one_lt_packedWords (k := k) hw hidx
  set wOff := wordOffset k w idx
  set bOff := bitOffset k w idx
  set k₀ := lowWidth k w idx
  set k₁ := highWidth k w idx
  set old₀ := (s.mem (base + offset + wOff) >>> bOff) &&& (2 ^ k₀ - 1)
  set val₀ := val &&& (2 ^ k₀ - 1)
  have hδ0_lt : old₀ ^^^ val₀ < 2 ^ k₀ := by
    refine Nat.xor_lt_two_pow ?_ ?_ <;>
    · dsimp only [old₀, val₀]
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by positivity)
  have hsh0_lt : (old₀ ^^^ val₀) <<< bOff < 2 ^ w := by
    refine shiftLeft_lt_two_pow_of_lt hδ0_lt ?_
    have := bitOffset_add_lowWidth_le (k := k) (idx := idx) hw
    omega
  have hw0 : Fits w (s.mem (base + offset + wOff) ^^^ ((old₀ ^^^ val₀) <<< bOff)) :=
    Nat.xor_lt_two_pow (hwf.2 _) hsh0_lt
  let mem₁ := Function.update s.mem (base + offset + wOff)
    (s.mem (base + offset + wOff) ^^^ ((old₀ ^^^ val₀) <<< bOff))
  have hm1 : Fits w (mem₁ (base + offset + wOff + 1)) := by
    dsimp only [mem₁]
    rw [Function.update_of_ne (by omega)]
    exact hwf.2 _
  set old₁ := (mem₁ (base + offset + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)
  set val₁ := (val >>> k₀) &&& (2 ^ k₁ - 1)
  have hk1_le_w : k₁ ≤ w := by
    have := lowWidth_add_highWidth k w idx
    omega
  have hδ1_lt : old₁ ^^^ val₁ < 2 ^ k₁ := by
    refine Nat.xor_lt_two_pow ?_ ?_ <;>
    · dsimp only [old₁, val₁]
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by positivity)
  have hsh1_lt : (old₁ ^^^ val₁) <<< 0 < 2 ^ w :=
    hδ1_lt.trans_le (Nat.pow_le_pow_right (by decide) hk1_le_w)
  have hw1 : Fits w (mem₁ (base + offset + wOff + 1) ^^^ ((old₁ ^^^ val₁) <<< 0)) :=
    Nat.xor_lt_two_pow hm1 hsh1_lt
  change base + offset + wOff < s.frontier ∧
    ((base + offset + wOff < s.frontier ∧
      Fits w (s.mem (base + offset + wOff) ^^^ ((old₀ ^^^ val₀) <<< bOff))) ∧
    base + offset + wOff + 1 < s.frontier ∧
    (base + offset + wOff + 1 < s.frontier ∧
      Fits w (mem₁ (base + offset + wOff + 1) ^^^ ((old₁ ^^^ val₁) <<< 0))) ∧ True)
  exact ⟨by omega, ⟨by omega, hw0⟩, by omega, ⟨by omega, hw1⟩, trivial⟩

private theorem readsWidth_rename {B : Basis} {r₁ r₂ : ℕ} (c : Code B r₁) (f : Fin r₁ → Fin r₂) :
    (c.rename f).ReadsWidth ↔ c.ReadsWidth := by
  induction c with
  | rand _ _ => rfl
  | op o => cases o <;> rfl
  | seq c₁ c₂ ih₁ ih₂ => simp [Code.rename, Code.ReadsWidth, ih₁, ih₂]
  | branch cond c₁ c₂ ih₁ ih₂ => simp [Code.rename, Code.ReadsWidth, ih₁, ih₂]
  | loop cond body ih => simp [Code.rename, Code.ReadsWidth, ih]

private theorem readPackedCode_not_readsWidth (offset k w : ℕ) :
    ¬(readPackedCode offset k w).ReadsWidth := by
  simp [readPackedCode, addrSetupCode, offsetSetupCode, maskSetupCode, readPackedFinishCode,
    Code.ReadsWidth, Op.ReadsWidth, Op.exactBin]

private theorem writePackedCode_not_readsWidth (offset k w : ℕ) :
    ¬(writePackedCode offset k w).ReadsWidth := by
  simp [writePackedCode, addrSetupCode, offsetSetupCode, maskSetupCode, writePackedFinishCode,
    Code.ReadsWidth, Op.ReadsWidth, Op.exactBin]

/-- Uniform `Realizes .exact` certificate for `readPackedProg`. -/
theorem realizes_readPacked (offset N k w₀ : ℕ) :
    Realizes .exact (fun d : ℕ × ℕ => readPackedProg d.1 offset k w₀ d.2)
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w d _ => w = w₀ ∧ 0 < w₀ ∧ k ≤ w₀ ∧ d.2 < N ∧
        Fits w₀ (d.1 + offset + packedWords N k w₀))
      (fun _ _ => 0) := by
  let perm : Fin 10 ≃ Fin 10 := Equiv.swap 0 2
  refine ⟨8, 38, fun _ src tmp =>
    .seq (.op (.copy (tmp 2) (src 0)))
      (.seq (.op (.copy (tmp 1) (src 1)))
        ((readPackedCode offset k w₀).rename (tmp ∘ perm))), ?_⟩
  intro r frontier src tmp hi hd hf hs
  have hperm_inj : Function.Injective (tmp ∘ perm) := hi.comp perm.injective
  refine ⟨?_, ?_⟩
  · simp only [Code.ReadsWidth, Op.ReadsWidth, readsWidth_rename, false_or]
    exact readPackedCode_not_readsWidth offset k w₀
  · intro w d x hx hin ⟨heq, hw, hkw, hidx, hfit⟩ _
    subst heq
    have hsrc0 : x.regs (src 0) = d.1 := congrFun hin 0
    have hsrc1 : x.regs (src 1) = d.2 := congrFun hin 1
    let x₁ := x.set (tmp 2) (x.regs (src 0))
    let x₂ := x₁.set (tmp 1) (x₁.regs (src 1))
    have hc1 : ExecWithin (B := .exact) w (.op (.copy (tmp 2) (src 0))) x x₁ 1 := ExecWithin.copy
    have hc2 : ExecWithin (B := .exact) w (.op (.copy (tmp 1) (src 1))) x₁ x₂ 1 := ExecWithin.copy
    have hx₂_bdd : x₂.Bounded w := hc2.bounded (hc1.bounded hx)
    have hbase0 : (x₂.comap (tmp ∘ perm)).regs 0 = d.1 := by
      change x₂.regs (tmp (perm 0)) = d.1
      have hne12 : tmp 1 ≠ tmp (perm 0) := fun h => by
        have := Fin.ext_iff.mp (hi h); revert this; decide
      dsimp only [x₂, x₁, Data.set]
      rw [Function.update_of_ne hne12.symm]
      have hp0 : perm 0 = 2 := by decide
      rw [hp0, Function.update_self, hsrc0]
    have hidx1 : (x₂.comap (tmp ∘ perm)).regs 1 = d.2 := by
      change x₂.regs (tmp (perm 1)) = d.2
      have hp1 : perm 1 = 1 := by decide
      rw [hp1]
      dsimp only [x₂, x₁, Data.set]
      rw [Function.update_self, Function.update_of_ne (hd 1 2), hsrc1]
    obtain ⟨y_core, hex_core, hymem, _, _, hy2⟩ :=
      readPackedCode_execWithin hw hkw hidx (hx₂_bdd.comap (tmp ∘ perm)) hbase0 hidx1 hfit
    have hex_ren := hex_core.rename hperm_inj
    let y := y_core.extend (tmp ∘ perm) x₂
    refine ⟨y, (hc1.seq (hc2.seq hex_ren)).mono (by change 1 + (1 + 36) ≤ 38 * (2 + 0 + 1); omega),
      ?_, ?_, ?_⟩
    · apply Memory.State.ext
      · exact hymem
      · change y.regs frontier = x.regs frontier
        have hnot : ¬∃ j : Fin 10, (tmp ∘ perm) j = frontier := by
          rintro ⟨j, hj⟩; exact hf (perm j) hj
        change Function.extend (tmp ∘ perm) y_core.regs x₂.regs frontier = x.regs frontier
        rw [Function.extend_apply' _ _ _ hnot]
        dsimp only [x₂, x₁, Data.set]
        rw [Function.update_of_ne (hf 1).symm, Function.update_of_ne (hf 2).symm]
    · intro i
      have hi0 : i = 0 := Fin.eq_zero i
      subst hi0
      rw [clientResult_width]
      change y.regs (tmp 0) = readPacked (d.1 + offset) k w x.mem d.2
      have hp2 : tmp 0 = (tmp ∘ perm) 2 := by congr 1
      rw [hp2]
      change (y.comap (tmp ∘ perm)).regs 2 = _
      rw [Data.comap_extend hperm_inj, hy2]
      rfl
    · intro i _ htmp
      have hnot : ¬∃ j : Fin 10, (tmp ∘ perm) j = i := by
        rintro ⟨j, hj⟩; exact htmp (perm j) hj
      change Function.extend (tmp ∘ perm) y_core.regs x₂.regs i = x.regs i
      rw [Function.extend_apply' _ _ _ hnot]
      dsimp only [x₂, x₁, Data.set]
      rw [Function.update_of_ne (htmp 1).symm, Function.update_of_ne (htmp 2).symm]

/-- Uniform `Realizes .exact` certificate for `writePackedProg`. -/
theorem realizes_writePacked (offset N k w₀ : ℕ) :
    Realizes .exact (fun d : (ℕ × ℕ) × ℕ => writePackedProg d.1.1 offset k w₀ d.1.2 d.2)
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      (fun w d _ => w = w₀ ∧ 0 < w₀ ∧ k ≤ w₀ ∧ d.1.2 < N ∧
        Fits w₀ (d.1.1 + offset + packedWords N k w₀))
      (fun _ _ => 0) := by
  refine ⟨9, 50, fun _ src tmp =>
    .seq (.op (.copy (tmp 0) (src 0)))
      (.seq (.op (.copy (tmp 1) (src 1)))
        (.seq (.op (.copy (tmp 2) (src 2)))
          ((writePackedCode offset k w₀).rename tmp))), ?_⟩
  intro r frontier src tmp hi hd hf hs
  refine ⟨?_, ?_⟩
  · simp only [Code.ReadsWidth, Op.ReadsWidth, readsWidth_rename, false_or]
    exact writePackedCode_not_readsWidth offset k w₀
  · intro w d x hx hin ⟨heq, hw, hkw, hidx, hfit⟩ _
    subst heq
    have hsrc0 : x.regs (src 0) = d.1.1 := congrFun hin 0
    have hsrc1 : x.regs (src 1) = d.1.2 := congrFun hin 1
    have hsrc2 : x.regs (src 2) = d.2 := congrFun hin 2
    let x₁ := x.set (tmp 0) (x.regs (src 0))
    let x₂ := x₁.set (tmp 1) (x₁.regs (src 1))
    let x₃ := x₂.set (tmp 2) (x₂.regs (src 2))
    have hc1 : ExecWithin (B := .exact) w (.op (.copy (tmp 0) (src 0))) x x₁ 1 := ExecWithin.copy
    have hc2 : ExecWithin (B := .exact) w (.op (.copy (tmp 1) (src 1))) x₁ x₂ 1 := ExecWithin.copy
    have hc3 : ExecWithin (B := .exact) w (.op (.copy (tmp 2) (src 2))) x₂ x₃ 1 := ExecWithin.copy
    have hx₃_bdd : x₃.Bounded w := hc3.bounded (hc2.bounded (hc1.bounded hx))
    have hne01 : tmp 0 ≠ tmp 1 := fun h => by have := Fin.ext_iff.mp (hi h); revert this; decide
    have hne02 : tmp 0 ≠ tmp 2 := fun h => by have := Fin.ext_iff.mp (hi h); revert this; decide
    have hne12 : tmp 1 ≠ tmp 2 := fun h => by have := Fin.ext_iff.mp (hi h); revert this; decide
    have hbase0 : (x₃.comap tmp).regs 0 = d.1.1 := by
      change x₃.regs (tmp 0) = d.1.1
      dsimp only [x₃, x₂, x₁, Data.set]
      rw [Function.update_of_ne hne02, Function.update_of_ne hne01, Function.update_self, hsrc0]
    have hidx1 : (x₃.comap tmp).regs 1 = d.1.2 := by
      change x₃.regs (tmp 1) = d.1.2
      dsimp only [x₃, x₂, x₁, Data.set]
      rw [Function.update_of_ne hne12, Function.update_self, Function.update_of_ne (hd 1 0), hsrc1]
    have hval2 : (x₃.comap tmp).regs 2 = d.2 := by
      change x₃.regs (tmp 2) = d.2
      dsimp only [x₃, x₂, x₁, Data.set]
      rw [Function.update_self, Function.update_of_ne (hd 2 1), Function.update_of_ne (hd 2 0),
        hsrc2]
    obtain ⟨y_core, hex_core, hymem, _, _, _⟩ :=
      writePackedCode_execWithin hw hkw hidx (hx₃_bdd.comap tmp) hbase0 hidx1 hval2 hfit
    have hex_ren := hex_core.rename hi
    let y := y_core.extend tmp x₃
    refine ⟨y, (hc1.seq (hc2.seq (hc3.seq hex_ren))).mono
      (by change 1 + (1 + (1 + 47)) ≤ 50 * (4 + 0 + 1); omega), ?_, ?_, ?_⟩
    · apply Memory.State.ext
      · exact hymem
      · change y.regs frontier = x.regs frontier
        have hnot : ¬∃ j : Fin 10, tmp j = frontier := by rintro ⟨j, hj⟩; exact hf j hj
        change Function.extend tmp y_core.regs x₃.regs frontier = x.regs frontier
        rw [Function.extend_apply' _ _ _ hnot]
        dsimp only [x₃, x₂, x₁, Data.set]
        rw [Function.update_of_ne (hf 2).symm, Function.update_of_ne (hf 1).symm,
          Function.update_of_ne (hf 0).symm]
    · intro i
      exact Fin.elim0 i
    · intro i _ htmp
      have hnot : ¬∃ j : Fin 10, tmp j = i := by rintro ⟨j, hj⟩; exact htmp j hj
      change Function.extend tmp y_core.regs x₃.regs i = x.regs i
      rw [Function.extend_apply' _ _ _ hnot]
      dsimp only [x₃, x₂, x₁, Data.set]
      rw [Function.update_of_ne (htmp 2).symm, Function.update_of_ne (htmp 1).symm,
        Function.update_of_ne (htmp 0).symm]

/-! ## Section 2: Dictionary array `Memory.Prog` primitives (`Quot`, `Val`, `LM`, `GM`) -/

/-- Common entry envelope for dictionary `Memory.Prog` operations at `base`. -/
def DictEnv (U V w n_max h_space : ℕ) (w' base : ℕ) : Prop :=
  w' = w ∧ Fits w (base + totalSpace U V w n_max h_space)

/-- Read `Quotients[d.2]` at `base = d.1` in `Memory.Prog`. -/
def readQuotProg (U w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog ℕ :=
  readPackedProg d.1 (offQuot h_space) (quotientBits U n_max) w d.2

/-- Write `d.2` to `Quotients[d.1.2]` at `base = d.1.1` in `Memory.Prog`. -/
def writeQuotProg (U w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit :=
  writePackedProg d.1.1 (offQuot h_space) (quotientBits U n_max) w d.1.2 d.2

/-- Read `Values[d.2]` at `base = d.1` in `Memory.Prog`. -/
def readValProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog ℕ :=
  readPackedProg d.1 (offVal U w n_max h_space) (valBits V) w d.2

/-- Write `d.2` to `Values[d.1.2]` at `base = d.1.1` in `Memory.Prog`. -/
def writeValProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit :=
  writePackedProg d.1.1 (offVal U w n_max h_space) (valBits V) w d.1.2 d.2

/-- Read `LocalMeta[c, d.2]` at `base = d.1` in `Memory.Prog`. -/
def readLMProg (U V w n_max h_space c : ℕ) (d : ℕ × ℕ) : Memory.Prog ℕ :=
  readPackedProg d.1 (offLMSub U V w n_max h_space c) (effBucketPosBits n_max) w d.2

/-- Write `d.2` to `LocalMeta[c, d.1.2]` at `base = d.1.1` in `Memory.Prog`. -/
def writeLMProg (U V w n_max h_space c : ℕ) (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit :=
  writePackedProg d.1.1 (offLMSub U V w n_max h_space c) (effBucketPosBits n_max) w d.1.2 d.2

/-- Read `GlobalMeta[d.2]` at `base = d.1` in `Memory.Prog`. -/
def readGMProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog ℕ :=
  readPackedProg d.1 (offGM U V w n_max h_space) (globalPtrBits n_max) w d.2

/-- Write `d.2` to `GlobalMeta[d.1.2]` at `base = d.1.1` in `Memory.Prog`. -/
def writeGMProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit :=
  writePackedProg d.1.1 (offGM U V w n_max h_space) (globalPtrBits n_max) w d.1.2 d.2

theorem realizes_readQuot {U V w n_max h_space : ℕ} (hw : 0 < w) (hU : U ≤ 2 ^ w) :
    Realizes .exact (readQuotProg U w n_max h_space)
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w' d _ => DictEnv U V w n_max h_space w' d.1 ∧ d.2 < n_max)
      (fun _ _ => 0) := by
  refine (realizes_readPacked (offQuot h_space) n_max (quotientBits U n_max) w).consequence
    ?_ (fun _ _ => le_rfl)
  intro w' d _ _ _ ⟨⟨rfl, hspace⟩, hidx⟩
  exact ⟨rfl, hw, quotientBits_le_of_le_pow hU, hidx,
    hspace.of_le (by unfold totalSpace offGM offLM offVal offQuot; omega)⟩

theorem realizes_writeQuot {U V w n_max h_space : ℕ} (hw : 0 < w) (hU : U ≤ 2 ^ w) :
    Realizes .exact (writeQuotProg U w n_max h_space)
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      (fun w' d _ => DictEnv U V w n_max h_space w' d.1.1 ∧ d.1.2 < n_max)
      (fun _ _ => 0) := by
  refine (realizes_writePacked (offQuot h_space) n_max (quotientBits U n_max) w).consequence
    ?_ (fun _ _ => le_rfl)
  intro w' d _ _ _ ⟨⟨rfl, hspace⟩, hidx⟩
  exact ⟨rfl, hw, quotientBits_le_of_le_pow hU, hidx,
    hspace.of_le (by unfold totalSpace offGM offLM offVal offQuot; omega)⟩

theorem realizes_readVal {U V w n_max h_space : ℕ} (hw : 0 < w) (hV : V ≤ 2 ^ w) :
    Realizes .exact (readValProg U V w n_max h_space)
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w' d _ => DictEnv U V w n_max h_space w' d.1 ∧ d.2 < n_max)
      (fun _ _ => 0) := by
  refine (realizes_readPacked (offVal U w n_max h_space) n_max (valBits V) w).consequence
    ?_ (fun _ _ => le_rfl)
  intro w' d _ _ _ ⟨⟨rfl, hspace⟩, hidx⟩
  exact ⟨rfl, hw, valBits_le_of_le_pow hV, hidx,
    hspace.of_le (by unfold totalSpace offGM offLM offVal; omega)⟩

theorem realizes_writeVal {U V w n_max h_space : ℕ} (hw : 0 < w) (hV : V ≤ 2 ^ w) :
    Realizes .exact (writeValProg U V w n_max h_space)
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      (fun w' d _ => DictEnv U V w n_max h_space w' d.1.1 ∧ d.1.2 < n_max)
      (fun _ _ => 0) := by
  refine (realizes_writePacked (offVal U w n_max h_space) n_max (valBits V) w).consequence
    ?_ (fun _ _ => le_rfl)
  intro w' d _ _ _ ⟨⟨rfl, hspace⟩, hidx⟩
  exact ⟨rfl, hw, valBits_le_of_le_pow hV, hidx,
    hspace.of_le (by unfold totalSpace offGM offLM offVal; omega)⟩

theorem realizes_readLM {U V w n_max h_space c : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hc : c < 9) :
    Realizes .exact (readLMProg U V w n_max h_space c)
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w' d _ => DictEnv U V w n_max h_space w' d.1 ∧ d.2 < totalMicroBuckets n_max)
      (fun _ _ => 0) := by
  refine (realizes_readPacked (offLMSub U V w n_max h_space c) (totalMicroBuckets n_max)
    (effBucketPosBits n_max) w).consequence ?_ (fun _ _ => le_rfl)
  intro w' d _ _ _ ⟨⟨heq, hspace⟩, hidx⟩
  subst heq
  have hsub : (c + 1) * lmSubWords n_max w' ≤ 9 * lmSubWords n_max w' :=
    Nat.mul_le_mul_right _ hc
  rw [Nat.add_one_mul] at hsub
  exact ⟨rfl, hw, effBucketPosBits_le_of_lt_pow hnU hU, hidx,
    hspace.of_le (by
      unfold lmSubWords at hsub
      unfold totalSpace offGM offLMSub offLM lmSubWords
      omega)⟩

theorem realizes_writeLM {U V w n_max h_space c : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) (hc : c < 9) :
    Realizes .exact (writeLMProg U V w n_max h_space c)
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      (fun w' d _ => DictEnv U V w n_max h_space w' d.1.1 ∧ d.1.2 < totalMicroBuckets n_max)
      (fun _ _ => 0) := by
  refine (realizes_writePacked (offLMSub U V w n_max h_space c) (totalMicroBuckets n_max)
    (effBucketPosBits n_max) w).consequence ?_ (fun _ _ => le_rfl)
  intro w' d _ _ _ ⟨⟨heq, hspace⟩, hidx⟩
  subst heq
  have hsub : (c + 1) * lmSubWords n_max w' ≤ 9 * lmSubWords n_max w' :=
    Nat.mul_le_mul_right _ hc
  rw [Nat.add_one_mul] at hsub
  exact ⟨rfl, hw, effBucketPosBits_le_of_lt_pow hnU hU, hidx,
    hspace.of_le (by
      unfold lmSubWords at hsub
      unfold totalSpace offGM offLMSub offLM lmSubWords
      omega)⟩

theorem realizes_readGM {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) :
    Realizes .exact (readGMProg U V w n_max h_space)
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w' d _ => DictEnv U V w n_max h_space w' d.1 ∧ d.2 < globalMetaLen n_max)
      (fun _ _ => 0) := by
  refine (realizes_readPacked (offGM U V w n_max h_space) (globalMetaLen n_max)
    (globalPtrBits n_max) w).consequence ?_ (fun _ _ => le_rfl)
  intro w' d _ _ _ ⟨⟨heq, hspace⟩, hidx⟩
  subst heq
  exact ⟨rfl, hw, globalPtrBits_le_of_lt_pow hnU hU, hidx,
    hspace.of_le (by unfold totalSpace; omega)⟩

theorem realizes_writeGM {U V w n_max h_space : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) :
    Realizes .exact (writeGMProg U V w n_max h_space)
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      (fun w' d _ => DictEnv U V w n_max h_space w' d.1.1 ∧ d.1.2 < globalMetaLen n_max)
      (fun _ _ => 0) := by
  refine (realizes_writePacked (offGM U V w n_max h_space) (globalMetaLen n_max)
    (globalPtrBits n_max) w).consequence ?_ (fun _ _ => le_rfl)
  intro w' d _ _ _ ⟨⟨heq, hspace⟩, hidx⟩
  subst heq
  exact ⟨rfl, hw, globalPtrBits_le_of_lt_pow hnU hU, hidx,
    hspace.of_le (by unfold totalSpace; omega)⟩

@[simp]
theorem clientState_readGMProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readGMProg U V w n_max h_space d) = s :=
  rfl

theorem clientResult_readGMProg {U V w n_max h_space base idx : ℕ} (s : Memory.State)
    (hidx : idx < globalMetaLen n_max) :
    (Memory.spec 0).clientResult s (readGMProg U V w n_max h_space (base, idx)) =
      gmAt base U V w n_max h_space s.mem idx := by
  simp [readGMProg, gmAt, hidx]

theorem fits_const_of_dictEnv {U V w₀ n_max h_space w base c : ℕ}
    (h : DictEnv U V w₀ n_max h_space w base) (hc : c ≤ 24) :
    Fits w c := by
  rcases h with ⟨rfl, hspace⟩
  have hl : 2 ≤ lmSubWords n_max w := Nat.le_add_left 2 _
  have hg : 2 ≤ packedWords (globalMetaLen n_max) (globalPtrBits n_max) w := Nat.le_add_left 2 _
  have hv : 2 ≤ packedWords n_max (valBits V) w := Nat.le_add_left 2 _
  have hq : 2 ≤ packedWords n_max (quotientBits U n_max) w := Nat.le_add_left 2 _
  exact hspace.of_le (by unfold totalSpace offGM offLM offVal offQuot; omega)

theorem fits_of_le_globalMetaLen {U V w₀ n_max h_space w base x : ℕ}
    (h : DictEnv U V w₀ n_max h_space w base) (hb_pos : 0 < bucketBits n_max)
    (hw : 0 < w₀) (hnU : n_max ≤ U) (hU : U < 2 ^ w₀)
    (hx : x ≤ globalMetaLen n_max) : Fits w x := by
  rcases h with ⟨rfl, _⟩
  have hmax := max_n_one_lt_two_pow_w hw hnU hU
  have hlen := globalMetaLen_le_of_bucketBits_pos hb_pos
  exact hmax.of_le (by omega)

theorem fits_of_le_max_n_one {U V w₀ n_max h_space w base x : ℕ}
    (h : DictEnv U V w₀ n_max h_space w base)
    (hw : 0 < w₀) (hnU : n_max ≤ U) (hU : U < 2 ^ w₀)
    (hx : x ≤ max n_max 1) : Fits w x := by
  rcases h with ⟨rfl, _⟩
  exact (max_n_one_lt_two_pow_w hw hnU hU).of_le hx

theorem slabSize_le_max_n_one (n_max : ℕ) : slabSize n_max ≤ max n_max 1 := by
  rcases Nat.eq_zero_or_pos (bucketBits n_max) with hb0 | hb_pos
  · simp [slabSize, slabBits, hb0]
  · have hcube := numBuckets_mul_slabScale_cubed_le hb_pos
    have hK := (slabSize_eq_sq_of_pos hb_pos).1
    have hB := numBuckets_pos n_max
    have hS := two_le_slabScale n_max
    have : slabSize n_max ≤ numBuckets n_max * (slabScale n_max) ^ 3 := by
      rw [hK]
      calc (slabScale n_max) ^ 2 = 1 * ((slabScale n_max) ^ 2 * 1) := by ring
        _ ≤ numBuckets n_max * ((slabScale n_max) ^ 2 * slabScale n_max) :=
          Nat.mul_le_mul hB (Nat.mul_le_mul_left _ (by omega))
        _ = numBuckets n_max * (slabScale n_max) ^ 3 := by ring
    omega

theorem dirSlabsPerBucket_le_globalMetaLen {n_max : ℕ} (hb : 0 < bucketBits n_max) :
    dirSlabsPerBucket n_max ≤ globalMetaLen n_max := by
  rw [← gmSlabMetaBase_add_eq_globalMetaLen hb]
  unfold gmSlabMetaBase gmTailOwnerBase gmTailPtrBase
  have := Nat.le_mul_of_pos_left (dirSlabsPerBucket n_max) (numBuckets_pos n_max)
  omega

theorem tailCapPerBucket_le_globalMetaLen {n_max : ℕ} (hb : 0 < bucketBits n_max) :
    tailCapPerBucket n_max ≤ globalMetaLen n_max := by
  rw [← gmSlabMetaBase_add_eq_globalMetaLen hb]
  unfold gmSlabMetaBase gmTailOwnerBase maxTailItems
  have := Nat.le_mul_of_pos_left (tailCapPerBucket n_max) (numBuckets_pos n_max)
  omega

theorem effBucketCap_eq_dirSlabs_mul_slabSize {n_max : ℕ} (hb : 0 < bucketBits n_max) :
    effBucketCap n_max = dirSlabsPerBucket n_max * slabSize n_max := by
  have hb0 : bucketBits n_max ≠ 0 := by omega
  rw [effBucketCap_eq_bucketCap_of_pos hb, (slabSize_eq_sq_of_pos hb).1]
  unfold bucketCap dirSlabsPerBucket
  rw [ite_eq_right hb0]
  ring

/-! ## Section 3: `readBucketCountProg` and `resolveIndexedSlotProg` via `realize` -/

/-- `Memory.Prog` operation reading `bCount n_max gm b` (`d = (base, b)`). -/
def readBucketCountProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog ℕ :=
  if bucketBits n_max = 0 then
    readGMProg U V w n_max h_space (d.1, 0)
  else do
    let q_b ← readGMProg U V w n_max h_space (d.1, 4 + 3 * d.2)
    let r_b ← readGMProg U V w n_max h_space (d.1, 4 + 3 * d.2 + 1)
    pure (q_b * slabSize n_max + r_b)

theorem clientResult_readBucketCountProg {U V w n_max h_space : ℕ}
    (d : ℕ × ℕ) (s : Memory.State) (hb : d.2 < numBuckets n_max) :
    (Memory.spec 0).clientResult s (readBucketCountProg U V w n_max h_space d) =
      bCount n_max (gmAt d.1 U V w n_max h_space s.mem) d.2 := by
  unfold readBucketCountProg bCount
  by_cases hb0 : bucketBits n_max = 0
  · have hd2 : d.2 = 0 := by
      have : numBuckets n_max = 1 := by simp [numBuckets, hb0]
      omega
    have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
    simp only [hb0, ↓reduceIte, hd2]
    exact clientResult_readGMProg s h0_lt
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    have hq_lt : 4 + 3 * d.2 < globalMetaLen n_max := gmQIdx_lt hb_pos hb
    have hr_lt : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
    simp only [hb0, ↓reduceIte, hb]
    rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      clientResult_readGMProg s hq_lt, StateTransitionSpec.clientResult_bind,
      clientState_readGMProg, clientResult_readGMProg s hr_lt]
    rfl

@[simp]
theorem clientState_readBucketCountProg {U V w n_max h_space : ℕ}
    (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readBucketCountProg U V w n_max h_space d) = s := by
  unfold readBucketCountProg
  split_ifs <;> rfl

theorem memoryCost_readBucketCountProg_le {U V w n_max h_space : ℕ}
    (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (readBucketCountProg U V w n_max h_space d) s ≤ 4 := by
  unfold readBucketCountProg
  split_ifs
  · change 2 ≤ 4; omega
  · change 4 ≤ 4; omega

theorem realizes_readBucketCount {U V w₀ n_max h_space : ℕ}
    (hw : 0 < w₀) (hnU : n_max ≤ U) (hU : U < 2 ^ w₀) :
    Realizes .exact (readBucketCountProg U V w₀ n_max h_space)
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w d s => DictEnv U V w₀ n_max h_space w d.1 ∧
        SlotStoreInv n_max (gmAt d.1 U V w₀ n_max h_space s.mem) ∧
        d.2 < numBuckets n_max)
      (fun _ _ => 0) := by
  have hrg := realizes_readGM (U := U) (V := V) (h_space := h_space) hw hnU hU
  by_cases hb0 : bucketBits n_max = 0
  · refine Realizes.congr (p := fun d : ℕ × ℕ => do
        let i0 ← pure 0
        readGMProg U V w₀ n_max h_space (d.1, i0)) ?_
      (fun d => by simp [readBucketCountProg, hb0])
    realize
    · exact h.1
    · unfold globalMetaLen; omega
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    refine Realizes.congr (p := fun d : ℕ × ℕ => do
        let q_idx ← pure (4 + 3 * d.2)
        let q_b ← readGMProg U V w₀ n_max h_space (d.1, q_idx)
        let r_idx ← pure (q_idx + 1)
        let r_b ← readGMProg U V w₀ n_max h_space (d.1, r_idx)
        pure (q_b * slabSize n_max + r_b)) ?_
      (fun d => by simp [readBucketCountProg, hb0, ← PFunctor.FreeM.bind_eq_bind])
    realize
    · exact fits_of_le_globalMetaLen (by tauto) hb_pos hw hnU hU (le_of_lt (gmQIdx_lt hb_pos h.2.2))
    · exact fits_const_of_dictEnv (by tauto) (by decide)
    · exact h.1
    · exact gmQIdx_lt hb_pos h.2.2
    · exact fits_of_le_globalMetaLen (by tauto) hb_pos hw hnU hU (le_of_lt (gmRIdx_lt hb_pos h.2.2))
    · exact gmRIdx_lt hb_pos h.2.2
    · have hq_lt : 4 + 3 * d.2 < globalMetaLen n_max := gmQIdx_lt hb_pos h.2.2
      have hr_lt : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos h.2.2
      rw [clientState_readGMProg, clientResult_readGMProg _ hq_lt,
        clientResult_readGMProg _ hr_lt]
      have hbc := bCount_le_n_max h.2.1 d.2
      unfold bCount at hbc
      simp only [hb0, ↓reduceIte, h.2.2, gmQIdx, gmRIdx] at hbc
      exact fits_of_le_max_n_one (by tauto) hw hnU hU (by omega)
    · exact fits_of_le_max_n_one (by tauto) hw hnU hU (slabSize_le_max_n_one n_max)

/-- `Memory.Prog` operation resolving indexed local slot `j = d.2 < effBucketCap n_max` of bucket
`b = d.1.2` at `base = d.1.1` to physical slot `slotOf n_max gm b j < n_max`. -/
def resolveIndexedSlotProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ :=
  if bucketBits n_max = 0 then
    pure d.2
  else do
    let q_b ← readGMProg U V w n_max h_space (d.1.1, 4 + 3 * d.1.2)
    if d.2 < q_b * slabSize n_max then do
      let p ← readGMProg U V w n_max h_space
        (d.1.1, gmSlabDirBase n_max + d.1.2 * dirSlabsPerBucket n_max + d.2 / slabSize n_max)
      pure (p * slabSize n_max + ((slabSize n_max - 1) - d.2 % slabSize n_max))
    else do
      let t ← readGMProg U V w n_max h_space
        (d.1.1, gmTailPtrBase n_max + (d.1.2 * tailCapPerBucket n_max +
          (d.2 - q_b * slabSize n_max)))
      pure ((n_max - 1) - t)

@[simp]
theorem clientState_resolveIndexedSlotProg {U V w n_max h_space : ℕ}
    (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (resolveIndexedSlotProg U V w n_max h_space d) = s := by
  unfold resolveIndexedSlotProg
  split_ifs with hb0
  · rfl
  · rw [StateTransitionSpec.clientState_bind, clientState_readGMProg]
    split_ifs <;> rfl

theorem memoryCost_resolveIndexedSlotProg_le {U V w n_max h_space : ℕ}
    (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (resolveIndexedSlotProg U V w n_max h_space d) s ≤ 4 := by
  unfold resolveIndexedSlotProg
  split_ifs with hb0
  · change 0 ≤ 4; omega
  · simp only [← PFunctor.FreeM.bind_eq_bind]
    rw [memoryCost_bind]
    split_ifs <;> · change 2 + 2 ≤ 4; omega

theorem clientResult_resolveIndexedSlotProg {U V w n_max h_space : ℕ}
    (d : (ℕ × ℕ) × ℕ) (s : Memory.State)
    (hinv : SlotStoreInv n_max (gmAt d.1.1 U V w n_max h_space s.mem))
    (hb : d.1.2 < numBuckets n_max)
    (hj_bc : d.2 < bCount n_max (gmAt d.1.1 U V w n_max h_space s.mem) d.1.2)
    (hj_cap : d.2 < effBucketCap n_max) :
    (Memory.spec 0).clientResult s (resolveIndexedSlotProg U V w n_max h_space d) =
      slotOf n_max (gmAt d.1.1 U V w n_max h_space s.mem) d.1.2 d.2 := by
  unfold resolveIndexedSlotProg slotOf
  by_cases hb0 : bucketBits n_max = 0
  · simp [hb0]
    rfl
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    have hq_lt : 4 + 3 * d.1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos hb
    simp only [hb0, ↓reduceIte]
    rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      clientResult_readGMProg s hq_lt, show 4 + 3 * d.1.2 = gmQIdx d.1.2 from rfl]
    split_ifs with hj_slab
    · have hs_dir : d.2 / slabSize n_max < dirSlabsPerBucket n_max := by
        have hcap := effBucketCap_eq_dirSlabs_mul_slabSize hb_pos
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hcap]; exact hj_cap)
      have hs_q : d.2 / slabSize n_max < gmAt d.1.1 U V w n_max h_space s.mem (gmQIdx d.1.2) :=
        Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have hdir_lt : gmSlabDirBase n_max + d.1.2 * dirSlabsPerBucket n_max +
          d.2 / slabSize n_max < globalMetaLen n_max :=
        gmSlabDirIdx_lt hb_pos hb hs_dir
      rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
        clientResult_readGMProg s hdir_lt]
      have hdir_eq := (hinv.multi_slab hb_pos).dir_eq d.1.2 hb (d.2 / slabSize n_max) hs_q hs_dir
      unfold gmSlabDirIdx at hdir_eq
      rw [hdir_eq]
      rfl
    · unfold bCount at hj_bc
      simp only [hb0, ↓reduceIte, hb] at hj_bc
      have hr_lt : d.2 - gmAt d.1.1 U V w n_max h_space s.mem (gmQIdx d.1.2) * slabSize n_max <
          gmAt d.1.1 U V w n_max h_space s.mem (gmRIdx d.1.2) := by omega
      have hr_cap : d.2 - gmAt d.1.1 U V w n_max h_space s.mem (gmQIdx d.1.2) * slabSize n_max <
          tailCapPerBucket n_max :=
        lt_of_lt_of_le hr_lt ((hinv.multi_r_bounds hb_pos d.1.2 hb).1.le)
      have hptr_lt : gmTailPtrBase n_max + (d.1.2 * tailCapPerBucket n_max +
          (d.2 - gmAt d.1.1 U V w n_max h_space s.mem (gmQIdx d.1.2) * slabSize n_max)) <
          globalMetaLen n_max :=
        gmTailPtrIdx_lt hb_pos hb hr_cap
      rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
        clientResult_readGMProg s hptr_lt]
      rfl

private theorem resolveIndexedSlot_dir_lt {n_max b j : ℕ}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max) (hj_cap : j < effBucketCap n_max) :
    gmSlabDirBase n_max + b * dirSlabsPerBucket n_max + j / slabSize n_max <
      globalMetaLen n_max := by
  have hcap := effBucketCap_eq_dirSlabs_mul_slabSize hb_pos
  have hs_dir : j / slabSize n_max < dirSlabsPerBucket n_max :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hcap]; exact hj_cap)
  exact gmSlabDirIdx_lt hb_pos hb hs_dir

private theorem resolveIndexedSlot_slab_fit {U V w₀ n_max h_space w : ℕ}
    (hw : 0 < w₀) (hnU : n_max ≤ U) (hU : U < 2 ^ w₀)
    (hb_pos : 0 < bucketBits n_max) (d : (ℕ × ℕ) × ℕ) (s : Memory.State)
    (henv : DictEnv U V w₀ n_max h_space w d.1.1)
    (hinv : SlotStoreInv n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem))
    (hb : d.1.2 < numBuckets n_max) (hj_cap : d.2 < effBucketCap n_max)
    (hc : d.2 < (Memory.spec 0).clientResult s
      (readGMProg U V w₀ n_max h_space (d.1.1, 4 + 3 * d.1.2)) * slabSize n_max) :
    Fits w ((Memory.spec 0).clientResult
      ((Memory.spec 0).clientState s (readGMProg U V w₀ n_max h_space (d.1.1, 4 + 3 * d.1.2)))
      (readGMProg U V w₀ n_max h_space
        (d.1.1, gmSlabDirBase n_max + d.1.2 * dirSlabsPerBucket n_max + d.2 / slabSize n_max)) *
      slabSize n_max + (slabSize n_max - 1 - d.2 % slabSize n_max)) := by
  have hj_slab := hc
  have hq_lt : 4 + 3 * d.1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos hb
  rw [clientResult_readGMProg _ hq_lt] at hj_slab
  have hs_dir : d.2 / slabSize n_max < dirSlabsPerBucket n_max := by
    have hcap := effBucketCap_eq_dirSlabs_mul_slabSize hb_pos
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hcap]; exact hj_cap)
  have hs_q : d.2 / slabSize n_max < gmAt d.1.1 U V w₀ n_max h_space s.mem (gmQIdx d.1.2) :=
    Nat.div_lt_of_lt_mul (by unfold gmQIdx; rw [Nat.mul_comm]; exact hj_slab)
  have hdir_lt := resolveIndexedSlot_dir_lt hb_pos hb hj_cap
  rw [clientState_readGMProg, clientResult_readGMProg _ hdir_lt]
  have hdir_eq := (hinv.multi_slab hb_pos).dir_eq d.1.2 hb (d.2 / slabSize n_max) hs_q hs_dir
  unfold gmSlabDirIdx at hdir_eq
  rw [hdir_eq]
  have hslab := hinv.multi_slab hb_pos
  have hp_lt : slabPtrOf n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem)
      d.1.2 (d.2 / slabSize n_max) < gmAt d.1.1 U V w₀ n_max h_space s.mem 0 := by
    rw [hslab.nslabs_eq]
    exact hslab.ptr_lt d.1.2 hb _ hs_q
  have hmod_lt : d.2 % slabSize n_max < slabSize n_max := Nat.mod_lt _ (slabSize_pos n_max)
  have h1 : (slabPtrOf n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem)
      d.1.2 (d.2 / slabSize n_max) + 1) * slabSize n_max ≤
      gmAt d.1.1 U V w₀ n_max h_space s.mem 0 * slabSize n_max :=
    Nat.mul_le_mul_right _ hp_lt
  rw [Nat.add_one_mul] at h1
  have htot := hinv.multi_total_le hb_pos
  exact fits_of_le_max_n_one henv hw hnU hU (by omega)

private theorem resolveIndexedSlot_tailIdx_lt {U V w₀ n_max h_space : ℕ}
    (hb0 : ¬bucketBits n_max = 0) (hb_pos : 0 < bucketBits n_max)
    (d : (ℕ × ℕ) × ℕ) (s : Memory.State)
    (hinv : SlotStoreInv n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem))
    (hb : d.1.2 < numBuckets n_max)
    (hj_bc : d.2 < bCount n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2)
    (hc : ¬d.2 < (Memory.spec 0).clientResult s
      (readGMProg U V w₀ n_max h_space (d.1.1, 4 + 3 * d.1.2)) * slabSize n_max) :
    gmTailPtrBase n_max + (d.1.2 * tailCapPerBucket n_max +
      (d.2 - (Memory.spec 0).clientResult s
        (readGMProg U V w₀ n_max h_space (d.1.1, 4 + 3 * d.1.2)) *
        slabSize n_max)) < globalMetaLen n_max := by
  have hj_not_slab := hc
  have hq_lt : 4 + 3 * d.1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos hb
  rw [clientResult_readGMProg _ hq_lt] at hj_not_slab ⊢
  unfold bCount at hj_bc
  simp only [hb0, ↓reduceIte, hb, gmQIdx] at hj_bc
  have hr_lt : d.2 - gmAt d.1.1 U V w₀ n_max h_space s.mem (4 + 3 * d.1.2) * slabSize n_max <
      gmAt d.1.1 U V w₀ n_max h_space s.mem (gmRIdx d.1.2) := by omega
  have hr_cap : d.2 - gmAt d.1.1 U V w₀ n_max h_space s.mem (4 + 3 * d.1.2) * slabSize n_max <
      tailCapPerBucket n_max :=
    lt_of_lt_of_le hr_lt ((hinv.multi_r_bounds hb_pos d.1.2 hb).1.le)
  exact gmTailPtrIdx_lt hb_pos hb hr_cap

private theorem resolveIndexedSlot_tail_le {U V w₀ n_max h_space : ℕ}
    (hb0 : ¬bucketBits n_max = 0) (hb_pos : 0 < bucketBits n_max)
    (d : (ℕ × ℕ) × ℕ) (s : Memory.State)
    (hinv : SlotStoreInv n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem))
    (hb : d.1.2 < numBuckets n_max)
    (hj_bc : d.2 < bCount n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2)
    (hc : ¬d.2 < (Memory.spec 0).clientResult s
      (readGMProg U V w₀ n_max h_space (d.1.1, 4 + 3 * d.1.2)) * slabSize n_max) :
    (Memory.spec 0).clientResult
      ((Memory.spec 0).clientState s (readGMProg U V w₀ n_max h_space (d.1.1, 4 + 3 * d.1.2)))
      (readGMProg U V w₀ n_max h_space
        (d.1.1, gmTailPtrBase n_max + (d.1.2 * tailCapPerBucket n_max +
          (d.2 - (Memory.spec 0).clientResult s
            (readGMProg U V w₀ n_max h_space (d.1.1, 4 + 3 * d.1.2)) *
            slabSize n_max)))) ≤ n_max - 1 := by
  have hptr_lt := resolveIndexedSlot_tailIdx_lt hb0 hb_pos d s hinv hb hj_bc hc
  have hj_not_slab := hc
  have hq_lt : 4 + 3 * d.1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos hb
  rw [clientState_readGMProg, clientResult_readGMProg _ hptr_lt]
  rw [clientResult_readGMProg _ hq_lt] at hj_not_slab ⊢
  unfold bCount at hj_bc
  simp only [hb0, ↓reduceIte, hb, gmQIdx] at hj_bc
  have hr_lt : d.2 - gmAt d.1.1 U V w₀ n_max h_space s.mem (4 + 3 * d.1.2) * slabSize n_max <
      gmAt d.1.1 U V w₀ n_max h_space s.mem (gmRIdx d.1.2) := by omega
  have htail := hinv.multi_tail hb_pos
  have ht_lt : gmAt d.1.1 U V w₀ n_max h_space s.mem
      (gmTailPtrIdx n_max d.1.2
        (d.2 - gmAt d.1.1 U V w₀ n_max h_space s.mem (4 + 3 * d.1.2) * slabSize n_max)) <
      gmAt d.1.1 U V w₀ n_max h_space s.mem 1 := by
    rw [htail.ntails_eq]
    exact htail.ptr_lt d.1.2 hb _ hr_lt
  have htot := hinv.multi_total_le hb_pos
  unfold gmTailPtrIdx gmTailPtrFlatIdx at ht_lt
  omega

theorem realizes_resolveIndexedSlot {U V w₀ n_max h_space : ℕ}
    (hw : 0 < w₀) (hnU : n_max ≤ U) (hU : U < 2 ^ w₀) :
    Realizes .exact (resolveIndexedSlotProg U V w₀ n_max h_space)
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w d s => DictEnv U V w₀ n_max h_space w d.1.1 ∧
        SlotStoreInv n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) ∧
        d.1.2 < numBuckets n_max ∧
        d.2 < bCount n_max (gmAt d.1.1 U V w₀ n_max h_space s.mem) d.1.2 ∧
        d.2 < effBucketCap n_max)
      (fun _ _ => 0) := by
  have hrg := realizes_readGM (U := U) (V := V) (h_space := h_space) hw hnU hU
  by_cases hb0 : bucketBits n_max = 0
  · refine Realizes.congr (p := fun d : (ℕ × ℕ) × ℕ => pure d.2) ?_
      (fun d => by simp [resolveIndexedSlotProg, hb0])
    realize
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    refine Realizes.congr (p := fun d : (ℕ × ℕ) × ℕ => do
        let q_idx ← pure (4 + 3 * d.1.2)
        let q_b ← readGMProg U V w₀ n_max h_space (d.1.1, q_idx)
        let qK ← pure (q_b * slabSize n_max)
        if d.2 < qK then do
          let dir_idx ←
            pure (gmSlabDirBase n_max + d.1.2 * dirSlabsPerBucket n_max + d.2 / slabSize n_max)
          let p ← readGMProg U V w₀ n_max h_space (d.1.1, dir_idx)
          pure (p * slabSize n_max + ((slabSize n_max - 1) - d.2 % slabSize n_max))
        else do
          let ptr_idx ←
            pure (gmTailPtrBase n_max + (d.1.2 * tailCapPerBucket n_max + (d.2 - qK)))
          let t ← readGMProg U V w₀ n_max h_space (d.1.1, ptr_idx)
          pure ((n_max - 1) - t)) ?_
      (fun d => by simp [resolveIndexedSlotProg, hb0, ← PFunctor.FreeM.bind_eq_bind])
    realize
    · exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU (le_of_lt (gmQIdx_lt hb_pos h.2.2.1))
    · exact fits_const_of_dictEnv h.1 (by decide)
    · exact h.1
    · exact gmQIdx_lt hb_pos h.2.2.1
    · have hq_lt : 4 + 3 * d.1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos h.2.2.1
      rw [clientResult_readGMProg _ hq_lt]
      have hbc := bCount_le_n_max h.2.1 d.1.2
      unfold bCount at hbc
      simp only [hb0, ↓reduceIte, h.2.2.1, gmQIdx] at hbc
      exact fits_of_le_max_n_one h.1 hw hnU hU (by omega)
    · exact fits_of_le_max_n_one h.1 hw hnU hU (slabSize_le_max_n_one n_max)
    · exact Nat.ne_of_gt (slabSize_pos n_max)
    · exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU
        (le_of_lt (resolveIndexedSlot_dir_lt hb_pos h.2.2.1 h.2.2.2.2))
    · exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU
        (dirSlabsPerBucket_le_globalMetaLen hb_pos)
    · exact fits_of_le_max_n_one h.1 hw hnU hU (slabSize_le_max_n_one n_max)
    · exact h.1
    · exact resolveIndexedSlot_dir_lt hb_pos h.2.2.1 h.2.2.2.2
    · have := Nat.mod_lt d.2 (slabSize_pos n_max); omega
    · exact resolveIndexedSlot_slab_fit hw hnU hU hb_pos d s h.1 h.2.1 h.2.2.1 h.2.2.2.2 hc
    · exact fits_of_le_max_n_one h.1 hw hnU hU (by have := slabSize_le_max_n_one n_max; omega)
    · omega
    · exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU
        (le_of_lt (resolveIndexedSlot_tailIdx_lt hb0 hb_pos d s h.2.1 h.2.2.1 h.2.2.2.1 hc))
    · exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU
        (tailCapPerBucket_le_globalMetaLen hb_pos)
    · exact h.1
    · exact resolveIndexedSlot_tailIdx_lt hb0 hb_pos d s h.2.1 h.2.2.1 h.2.2.2.1 hc
    · exact resolveIndexedSlot_tail_le hb0 hb_pos d s h.2.1 h.2.2.1 h.2.2.2.1 hc
    · exact fits_of_le_max_n_one h.1 hw hnU hU (by omega)

/-! ## Section 4: Pure state effects and costs of `read*Prog` and `write*Prog` -/

@[simp]
theorem clientState_readQuotProg (U w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readQuotProg U w n_max h_space d) = s := rfl

@[simp]
theorem clientState_readValProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readValProg U V w n_max h_space d) = s := rfl

@[simp]
theorem clientState_readLMProg (U V w n_max h_space c : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readLMProg U V w n_max h_space c d) = s := rfl

theorem clientResult_readQuotProg {U w n_max h_space base idx : ℕ} (s : Memory.State)
    (hidx : idx < n_max) :
    (Memory.spec 0).clientResult s (readQuotProg U w n_max h_space (base, idx)) =
      quotAt base U w n_max h_space s.mem idx := by
  simp [readQuotProg, quotAt, hidx]

theorem clientResult_readValProg {U V w n_max h_space base idx : ℕ} (s : Memory.State)
    (hidx : idx < n_max) :
    (Memory.spec 0).clientResult s (readValProg U V w n_max h_space (base, idx)) =
      valAt base U V w n_max h_space s.mem idx := by
  simp [readValProg, valAt, hidx]

theorem clientResult_readLMProg {U V w n_max h_space c base idx : ℕ} (s : Memory.State)
    (hc : c < 9) (hidx : idx < totalMicroBuckets n_max) :
    (Memory.spec 0).clientResult s (readLMProg U V w n_max h_space c (base, idx)) =
      lmAt base U V w n_max h_space s.mem (c, idx) := by
  simp [readLMProg, lmAt, hc, hidx]

@[simp]
theorem memoryCost_readQuotProg (U w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (readQuotProg U w n_max h_space d) s = 2 := rfl

@[simp]
theorem memoryCost_readValProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (readValProg U V w n_max h_space d) s = 2 := rfl

@[simp]
theorem memoryCost_readLMProg (U V w n_max h_space c : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (readLMProg U V w n_max h_space c d) s = 2 := rfl

@[simp]
theorem memoryCost_readGMProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (readGMProg U V w n_max h_space d) s = 2 := rfl

@[simp]
theorem memoryCost_writeQuotProg (U w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (writeQuotProg U w n_max h_space d) s = 4 := rfl

@[simp]
theorem memoryCost_writeValProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (writeValProg U V w n_max h_space d) s = 4 := rfl

@[simp]
theorem memoryCost_writeLMProg (U V w n_max h_space c : ℕ) (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (writeLMProg U V w n_max h_space c d) s = 4 := rfl

@[simp]
theorem memoryCost_writeGMProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (writeGMProg U V w n_max h_space d) s = 4 := rfl

/-- Pure state effect of `writeQuotProg`. -/
theorem writeQuotProg_effect {U V w n_max h_space base idx val : ℕ}
    (hw : 0 < w) (hidx_lt : idx < n_max) (hval_lt : val < 2 ^ quotientBits U n_max)
    (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s (writeQuotProg U w n_max h_space ((base, idx), val))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧ a < base + offVal U w n_max h_space) →
      s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem =
      Function.update (quotAt base U w n_max h_space s.mem) idx val ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem = gmAt base U V w n_max h_space s.mem := by
  intro s'
  have hmem : s'.mem =
      writePacked (base + offQuot h_space) (quotientBits U n_max) w s.mem idx val := rfl
  have hout_mem : ∀ a, ¬(base + offQuot h_space ≤ a ∧ a < base + offVal U w n_max h_space) →
      s'.mem a = s.mem a := by
    intro a ha
    rw [hmem]
    exact writePacked_outside hw s.mem hidx_lt _ (by dsimp only [offVal] at ha; omega)
  refine ⟨rfl, hout_mem, ?_, ?_, ?_, ?_⟩
  · funext j; unfold quotAt
    by_cases hj : j = idx
    · subst hj; rw [Function.update_self]; simp only [hidx_lt, ↓reduceIte, hmem]
      exact readPacked_writePacked_self _ _ _ _ _ hval_lt
    · rw [Function.update_of_ne hj]; split_ifs with hj_lt
      · rw [hmem]; exact readPacked_writePacked_of_ne hw s.mem hj _
      · rfl
  · funext j; unfold valAt; split_ifs with hj_lt
    · exact readPacked_congr hw (fun a ⟨ha1, _⟩ => hout_mem a (by omega)) hj_lt
    · rfl
  · funext ⟨c, j⟩; unfold lmAt; split_ifs with hp
    · exact readPacked_congr hw (fun a ⟨ha1, _⟩ =>
        hout_mem a (by dsimp only [offLMSub, offLM] at ha1; omega)) hp.2
    · rfl
  · funext j; unfold gmAt; split_ifs with hj_lt
    · exact readPacked_congr hw (fun a ⟨ha1, _⟩ =>
        hout_mem a (by dsimp only [offGM, offLM] at ha1; omega)) hj_lt
    · rfl

/-- Pure state effect of `writeValProg`. -/
theorem writeValProg_effect {U V w n_max h_space base idx val : ℕ}
    (hw : 0 < w) (hidx_lt : idx < n_max) (hval_lt : val < 2 ^ valBits V)
    (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s (writeValProg U V w n_max h_space ((base, idx), val))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offVal U w n_max h_space ≤ a ∧ a < base + offLM U V w n_max h_space) →
      s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem =
      Function.update (valAt base U V w n_max h_space s.mem) idx val ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem = gmAt base U V w n_max h_space s.mem := by
  intro s'
  have hmem : s'.mem =
      writePacked (base + offVal U w n_max h_space) (valBits V) w s.mem idx val := rfl
  have hout_mem : ∀ a, ¬(base + offVal U w n_max h_space ≤ a ∧
      a < base + offLM U V w n_max h_space) → s'.mem a = s.mem a := by
    intro a ha
    rw [hmem]
    exact writePacked_outside hw s.mem hidx_lt _ (by dsimp only [offLM] at ha; omega)
  refine ⟨rfl, hout_mem, ?_, ?_, ?_, ?_⟩
  · funext j; unfold quotAt; split_ifs with hj_lt
    · exact readPacked_congr hw (fun a ⟨_, ha2⟩ =>
        hout_mem a (by dsimp only [offVal, offQuot] at ha2 ⊢; omega)) hj_lt
    · rfl
  · funext j; unfold valAt
    by_cases hj : j = idx
    · subst hj; rw [Function.update_self]; simp only [hidx_lt, ↓reduceIte, hmem]
      exact readPacked_writePacked_self _ _ _ _ _ hval_lt
    · rw [Function.update_of_ne hj]; split_ifs with hj_lt
      · rw [hmem]; exact readPacked_writePacked_of_ne hw s.mem hj _
      · rfl
  · funext ⟨c, j⟩; unfold lmAt; split_ifs with hp
    · exact readPacked_congr hw (fun a ⟨ha1, _⟩ =>
        hout_mem a (by dsimp only [offLMSub] at ha1; omega)) hp.2
    · rfl
  · funext j; unfold gmAt; split_ifs with hj_lt
    · exact readPacked_congr hw (fun a ⟨ha1, _⟩ =>
        hout_mem a (by dsimp only [offGM] at ha1; omega)) hj_lt
    · rfl

/-- Pure state effect of `writeLMProg`. -/
theorem writeLMProg_effect {U V w n_max h_space c base idx val : ℕ}
    (hw : 0 < w) (hc : c < 9) (hidx_lt : idx < totalMicroBuckets n_max)
    (hval_lt : val < 2 ^ effBucketPosBits n_max)
    (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s (writeLMProg U V w n_max h_space c ((base, idx), val))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offLM U V w n_max h_space ≤ a ∧ a < base + offGM U V w n_max h_space) →
      s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    lmAt base U V w n_max h_space s'.mem =
      Function.update (lmAt base U V w n_max h_space s.mem) (c, idx) val ∧
    gmAt base U V w n_max h_space s'.mem = gmAt base U V w n_max h_space s.mem := by
  intro s'
  have hmem : s'.mem = writePacked (base + offLMSub U V w n_max h_space c)
      (effBucketPosBits n_max) w s.mem idx val := rfl
  have hsub : (c + 1) * lmSubWords n_max w ≤ 9 * lmSubWords n_max w :=
    Nat.mul_le_mul_right _ hc
  rw [Nat.add_one_mul] at hsub
  have hout_sub : ∀ a, ¬(base + offLMSub U V w n_max h_space c ≤ a ∧
      a < base + offLMSub U V w n_max h_space c + lmSubWords n_max w) → s'.mem a = s.mem a := by
    intro a ha
    rw [hmem]
    exact writePacked_outside hw s.mem hidx_lt _ ha
  have hout_mem : ∀ a, ¬(base + offLM U V w n_max h_space ≤ a ∧
      a < base + offGM U V w n_max h_space) → s'.mem a = s.mem a := by
    intro a ha
    exact hout_sub a (by
      unfold lmSubWords at hsub
      dsimp only [offGM, offLMSub, lmSubWords] at ha ⊢
      omega)
  refine ⟨rfl, hout_mem, ?_, ?_, ?_, ?_⟩
  · funext j; unfold quotAt; split_ifs with hj_lt
    · exact readPacked_congr hw (fun a ⟨_, ha2⟩ =>
        hout_mem a (by dsimp only [offLM, offVal, offQuot] at ha2 ⊢; omega)) hj_lt
    · rfl
  · funext j; unfold valAt; split_ifs with hj_lt
    · exact readPacked_congr hw (fun a ⟨_, ha2⟩ =>
        hout_mem a (by dsimp only [offLM, offVal] at ha2 ⊢; omega)) hj_lt
    · rfl
  · funext ⟨c', j⟩; unfold lmAt
    by_cases hp_eq : (c', j) = (c, idx)
    · injection hp_eq with hc_eq hj_eq
      subst hc_eq hj_eq; rw [Function.update_self]
      simp only [hc, hidx_lt, and_self, ↓reduceIte, hmem]
      exact readPacked_writePacked_self _ _ _ _ _ hval_lt
    · rw [Function.update_of_ne hp_eq]; split_ifs with hp_lt
      · rcases hp_lt with ⟨hc', hj_lt⟩
        by_cases hc_eq : c' = c
        · subst hc_eq
          have hj_ne : j ≠ idx := fun h => hp_eq (congrArg _ h)
          rw [hmem]; exact readPacked_writePacked_of_ne hw s.mem hj_ne _
        · exact readPacked_congr hw (fun a ⟨ha1, ha2⟩ => by
            apply hout_sub
            dsimp only [offLMSub, lmSubWords] at ha1 ha2 ⊢
            rcases lt_trichotomy c' c with hlt | hlt | hlt
            · have := Nat.mul_le_mul_right
                (packedWords (totalMicroBuckets n_max) (effBucketPosBits n_max) w) hlt
              rw [Nat.add_one_mul] at this; omega
            · exact absurd hlt hc_eq
            · have := Nat.mul_le_mul_right
                (packedWords (totalMicroBuckets n_max) (effBucketPosBits n_max) w) hlt
              rw [Nat.add_one_mul] at this; omega) hj_lt
      · rfl
  · funext j; unfold gmAt; split_ifs with hj_lt
    · exact readPacked_congr hw (fun a ⟨ha1, _⟩ => hout_mem a (by omega)) hj_lt
    · rfl

/-- Pure state effect of `writeGMProg`. -/
theorem writeGMProg_effect {U V w n_max h_space base idx val : ℕ}
    (hw : 0 < w) (hidx_lt : idx < globalMetaLen n_max)
    (hval_lt : val < 2 ^ globalPtrBits n_max)
    (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s (writeGMProg U V w n_max h_space ((base, idx), val))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offGM U V w n_max h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) →
      s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem =
      Function.update (gmAt base U V w n_max h_space s.mem) idx val := by
  intro s'
  have hmem : s'.mem = writePacked (base + offGM U V w n_max h_space)
      (globalPtrBits n_max) w s.mem idx val := rfl
  have hout_mem : ∀ a, ¬(base + offGM U V w n_max h_space ≤ a ∧
      a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a := by
    intro a ha
    rw [hmem]
    exact writePacked_outside hw s.mem hidx_lt _ (by dsimp only [totalSpace] at ha; omega)
  refine ⟨rfl, hout_mem, ?_, ?_, ?_, ?_⟩
  · funext j; unfold quotAt; split_ifs with hj_lt
    · exact readPacked_congr hw (fun a ⟨_, ha2⟩ =>
        hout_mem a (by dsimp only [offGM, offLM, offVal, offQuot] at ha2 ⊢; omega)) hj_lt
    · rfl
  · funext j; unfold valAt; split_ifs with hj_lt
    · exact readPacked_congr hw (fun a ⟨_, ha2⟩ =>
        hout_mem a (by dsimp only [offGM, offLM, offVal] at ha2 ⊢; omega)) hj_lt
    · rfl
  · funext ⟨c, j⟩; unfold lmAt; split_ifs with hp
    · rcases hp with ⟨hc, hj_lt⟩
      have hsub : (c + 1) * lmSubWords n_max w ≤ 9 * lmSubWords n_max w :=
        Nat.mul_le_mul_right _ hc
      rw [Nat.add_one_mul] at hsub
      exact readPacked_congr hw (fun a ⟨_, ha2⟩ =>
        hout_mem a (by
          unfold lmSubWords at hsub
          dsimp only [offGM, offLMSub, offLM, lmSubWords] at ha2 ⊢
          omega)) hj_lt
    · rfl
  · funext j; unfold gmAt
    by_cases hj : j = idx
    · subst hj; rw [Function.update_self]; simp only [hidx_lt, ↓reduceIte, hmem]
      exact readPacked_writePacked_self _ _ _ _ _ hval_lt
    · rw [Function.update_of_ne hj]; split_ifs with hj_lt
      · rw [hmem]; exact readPacked_writePacked_of_ne hw s.mem hj _
      · rfl

end Cslib.DataStructure.Dictionary.WordRAM.Succinct

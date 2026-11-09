/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.Computability.WordRAM.Realization.Branch
public import CslibFrontier.Computability.WordRAM.Realization.Loop
public import CslibFrontier.Computability.WordRAM.Realization.Primitive
public import CslibFrontier.Computability.WordRAM.Realization.Reindex
public import CslibFrontier.Computability.WordRAM.Realization.While
public import CslibFrontier.Computability.WordRAM.Realization.Witness
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlotInv
import CslibFrontier.Computability.WordRAM.Width
import CslibFrontier.Tactic.Realize

/-!
# `Memory.Prog` Bit-Packed Array Primitives and Slot Resolution via `realize`

This module wraps the overflow-free bit-packed array operations (`readPacked`, `writePacked`) and
the four dictionary arrays (`Quotients`, `Values`, `LocalMeta`, `GlobalMeta`) as `Memory.Prog`
operations with uniform `Realizes .exact` certificates, and realizes `readBucketCountProg` and
`resolveIndexedSlotProg` via the `realize` tactic.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.readPackedProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.writePackedProg`: `Memory.Prog` wrappers for
  bit-packed array reads and writes.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.DictParams`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.mkDictParams`: 36-word runtime register block
  holding precomputed layout parameters for parameter-free `Realizes` certificates.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.DictEnv`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.DictEnvGen`: common entry envelopes for
  dictionary `Memory.Prog` subroutines.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.readQuotProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.writeQuotProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.readValProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.writeValProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.readLMProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.writeLMProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.readGMProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.writeGMProg`: typed `Memory.Prog` read/write
  accessors for the four packed dictionary arrays.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.readBucketCountProg`: `Memory.Prog` operation
  reading `bCount`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.resolveIndexedSlotProg`: `Memory.Prog`
  operation translating a bucket-local index `j` into physical slot `slotOf n_max gm b j`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_readPackedGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_writePackedGen`: uniform `Realizes`
  certificates for bit-packed reads and writes.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_readBucketCountGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_resolveIndexedSlotGen`: uniform
  `Realizes` certificates for `readBucketCountGenProg` and `resolveIndexedSlotGenProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.writeQuotProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.writeValProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.writeLMProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.writeGMProg_effect`: pure logical array update
  lemmas for the four packed dictionary arrays.
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

/-! ## Section 1: `readPackedProg` and `writePackedProg` in `Memory.Prog` -/

/-- `Memory.Prog` operation reading the `k`-bit entry at index `idx` from a bit-packed array at
`base + offset` on a `w`-bit machine. -/
@[expose] def readPackedProg (base offset k w idx : ℕ) : Memory.Prog ℕ := do
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
@[expose] def writePackedProg (base offset k w idx val : ℕ) : Memory.Prog Unit := do
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

private theorem readPackedCode_not_readsWidth :
    ¬readPackedCode.ReadsWidth := by
  simp [readPackedCode, addrSetupCode, offsetSetupCode, maskSetupCode, readPackedFinishCode,
    Code.ReadsWidth, Op.ReadsWidth, Op.exactBin]

private theorem writePackedCode_not_readsWidth :
    ¬writePackedCode.ReadsWidth := by
  simp [writePackedCode, addrSetupCode, offsetSetupCode, maskSetupCode, writePackedFinishCode,
    Code.ReadsWidth, Op.ReadsWidth, Op.exactBin]

/-- Parameter-free `Memory.Prog` wrapper for `readPackedProg` taking
`d = (((base, offset), (k, w)), idx)`. -/
@[expose] def readPackedGenProg (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) : Memory.Prog ℕ :=
  readPackedProg d.1.1.1 d.1.1.2 d.1.2.1 d.1.2.2 d.2

/-- Parameter-free `Memory.Prog` wrapper for `writePackedProg` taking
`d = ((((base, offset), (k, w)), idx), val)`. -/
@[expose] def writePackedGenProg (d : (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) : Memory.Prog Unit :=
  writePackedProg d.1.1.1.1 d.1.1.1.2 d.1.1.2.1 d.1.1.2.2 d.1.2 d.2

/-- Uniform parameter-free `Realizes .exact` certificate for `readPackedGenProg`. -/
theorem realizes_readPackedGen :
    Realizes .exact readPackedGenProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w d _ => ∃ N, w = d.1.2.2 ∧ 0 < w ∧ d.1.2.1 ≤ w ∧ d.2 < N ∧
        Fits w (d.1.1.1 + d.1.1.2 + packedWords N d.1.2.1 w))
      (fun _ _ => 0) := by
  let perm : Fin 10 ≃ Fin 10 := Equiv.swap 0 2
  refine ⟨8, 38, fun _ src tmp =>
    .seq (.op (.exactBin .add (tmp 2) (src 0) (src 1)))
      (.seq (.op (.copy (tmp 1) (src 4)))
        (.seq (.op (.copy (tmp 8) (src 3)))
          (.seq (.op (.copy (tmp 9) (src 2)))
            (readPackedCode.rename (tmp ∘ perm))))), ?_⟩
  intro r frontier src tmp hi hd hf hs
  have hperm_inj : Function.Injective (tmp ∘ perm) := hi.comp perm.injective
  refine ⟨?_, ?_⟩
  · simp [Code.ReadsWidth, Op.ReadsWidth, Op.exactBin, Code.readsWidth_rename,
      readPackedCode_not_readsWidth]
  · intro w d x hx hin ⟨N, heq, hw, hkw, hidx, hfit⟩ _
    have hsrc0 : x.regs (src 0) = d.1.1.1 := congrFun hin 0
    have hsrc1 : x.regs (src 1) = d.1.1.2 := congrFun hin 1
    have hsrc2 : x.regs (src 2) = d.1.2.1 := congrFun hin 2
    have hsrc3 : x.regs (src 3) = d.1.2.2 := congrFun hin 3
    have hsrc4 : x.regs (src 4) = d.2 := congrFun hin 4
    let x₁ := x.set (tmp 2) (d.1.1.1 + d.1.1.2)
    let x₂ := x₁.set (tmp 1) (x₁.regs (src 4))
    let x₃ := x₂.set (tmp 8) (x₂.regs (src 3))
    let x₄ := x₃.set (tmp 9) (x₃.regs (src 2))
    have hc1 :
        ExecWithin (B := .exact) w (.op (.exactBin .add (tmp 2) (src 0) (src 1))) x x₁ 1 := by
      apply ExecWithin.op
      rw [Op.eval_exactBin, hsrc0, hsrc1]
      exact Data.put_of_fits (hfit.of_le (by omega))
    have hc2 : ExecWithin (B := .exact) w (.op (.copy (tmp 1) (src 4))) x₁ x₂ 1 := ExecWithin.copy
    have hc3 : ExecWithin (B := .exact) w (.op (.copy (tmp 8) (src 3))) x₂ x₃ 1 := ExecWithin.copy
    have hc4 : ExecWithin (B := .exact) w (.op (.copy (tmp 9) (src 2))) x₃ x₄ 1 := ExecWithin.copy
    have hx₄_bdd : x₄.Bounded w := hc4.bounded (hc3.bounded (hc2.bounded (hc1.bounded hx)))
    have hne : ∀ (a b : Fin 10), a ≠ b → tmp a ≠ tmp b := fun a b hab h => hab (hi h)
    have hbase0 : (x₄.comap (tmp ∘ perm)).regs 0 = d.1.1.1 + d.1.1.2 := by
      change x₄.regs (tmp (perm 0)) = d.1.1.1 + d.1.1.2
      have hp0 : perm 0 = 2 := by decide
      rw [hp0]
      dsimp only [x₄, x₃, x₂, x₁, Data.set]
      rw [Function.update_of_ne (hne 2 9 (by decide)),
        Function.update_of_ne (hne 2 8 (by decide)),
        Function.update_of_ne (hne 2 1 (by decide)),
        Function.update_self]
    have hidx1 : (x₄.comap (tmp ∘ perm)).regs 1 = d.2 := by
      change x₄.regs (tmp (perm 1)) = d.2
      have hp1 : perm 1 = 1 := by decide
      rw [hp1]
      dsimp only [x₄, x₃, x₂, x₁, Data.set]
      rw [Function.update_of_ne (hne 1 9 (by decide)),
        Function.update_of_ne (hne 1 8 (by decide)),
        Function.update_self, Function.update_of_ne (hd 4 2), hsrc4]
    have hw8 : (x₄.comap (tmp ∘ perm)).regs 8 = w := by
      change x₄.regs (tmp (perm 8)) = w
      have hp8 : perm 8 = 8 := by decide
      rw [hp8]
      dsimp only [x₄, x₃, x₂, x₁, Data.set]
      rw [Function.update_of_ne (hne 8 9 (by decide)),
        Function.update_self, Function.update_of_ne (hd 3 1),
        Function.update_of_ne (hd 3 2), hsrc3, heq]
    have hk9 : (x₄.comap (tmp ∘ perm)).regs 9 = d.1.2.1 := by
      change x₄.regs (tmp (perm 9)) = d.1.2.1
      have hp9 : perm 9 = 9 := by decide
      rw [hp9]
      dsimp only [x₄, x₃, x₂, x₁, Data.set]
      rw [Function.update_self, Function.update_of_ne (hd 2 8),
        Function.update_of_ne (hd 2 1), Function.update_of_ne (hd 2 2), hsrc2]
    obtain ⟨y_core, hex_core, hymem, _, _, hy2⟩ :=
      readPackedCode_execWithin hw hkw hidx (hx₄_bdd.comap (tmp ∘ perm)) hbase0 hidx1 hw8 hk9 hfit
    have hex_ren := hex_core.rename hperm_inj
    let y := y_core.extend (tmp ∘ perm) x₄
    refine ⟨y, (hc1.seq (hc2.seq (hc3.seq (hc4.seq hex_ren)))).mono
      (by change 1 + (1 + (1 + (1 + 34))) ≤ 38 * (2 + 0 + 1); omega),
      ?_, ?_, ?_⟩
    · apply Memory.State.ext
      · exact hymem
      · change y.regs frontier = x.regs frontier
        have hnot : ¬∃ j : Fin 10, (tmp ∘ perm) j = frontier := by
          rintro ⟨j, hj⟩; exact hf (perm j) hj
        change Function.extend (tmp ∘ perm) y_core.regs x₄.regs frontier = x.regs frontier
        rw [Function.extend_apply' _ _ _ hnot]
        dsimp only [x₄, x₃, x₂, x₁, Data.set]
        rw [Function.update_of_ne (hf 9).symm, Function.update_of_ne (hf 8).symm,
          Function.update_of_ne (hf 1).symm, Function.update_of_ne (hf 2).symm]
    · intro i
      have hi0 : i = 0 := Fin.eq_zero i
      subst hi0
      rw [clientResult_width]
      change y.regs (tmp 0) = readPacked (d.1.1.1 + d.1.1.2) d.1.2.1 d.1.2.2 x.mem d.2
      have hp2 : tmp 0 = (tmp ∘ perm) 2 := by congr 1
      rw [hp2]
      change (y.comap (tmp ∘ perm)).regs 2 = _
      rw [Data.comap_extend hperm_inj, hy2, ← heq]
      rfl
    · intro i _ htmp
      have hnot : ¬∃ j : Fin 10, (tmp ∘ perm) j = i := by
        rintro ⟨j, hj⟩; exact htmp (perm j) hj
      change Function.extend (tmp ∘ perm) y_core.regs x₄.regs i = x.regs i
      rw [Function.extend_apply' _ _ _ hnot]
      dsimp only [x₄, x₃, x₂, x₁, Data.set]
      rw [Function.update_of_ne (htmp 9).symm, Function.update_of_ne (htmp 8).symm,
        Function.update_of_ne (htmp 1).symm, Function.update_of_ne (htmp 2).symm]

/-- Uniform parameter-free `Realizes .exact` certificate for `writePackedGenProg`. -/
theorem realizes_writePackedGen :
    Realizes .exact writePackedGenProg
      (WordEncoding.encode (α := (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      (fun w d _ => ∃ N, w = d.1.1.2.2 ∧ 0 < w ∧ d.1.1.2.1 ≤ w ∧ d.1.2 < N ∧
        Fits w (d.1.1.1.1 + d.1.1.1.2 + packedWords N d.1.1.2.1 w))
      (fun _ _ => 0) := by
  refine ⟨9, 50, fun _ src tmp =>
    .seq (.op (.exactBin .add (tmp 0) (src 0) (src 1)))
      (.seq (.op (.copy (tmp 1) (src 4)))
        (.seq (.op (.copy (tmp 2) (src 5)))
          (.seq (.op (.copy (tmp 8) (src 3)))
            (.seq (.op (.copy (tmp 9) (src 2)))
              (writePackedCode.rename tmp))))), ?_⟩
  intro r frontier src tmp hi hd hf hs
  refine ⟨?_, ?_⟩
  · simp [Code.ReadsWidth, Op.ReadsWidth, Op.exactBin, Code.readsWidth_rename,
      writePackedCode_not_readsWidth]
  · intro w d x hx hin ⟨N, heq, hw, hkw, hidx, hfit⟩ _
    have hsrc0 : x.regs (src 0) = d.1.1.1.1 := congrFun hin 0
    have hsrc1 : x.regs (src 1) = d.1.1.1.2 := congrFun hin 1
    have hsrc2 : x.regs (src 2) = d.1.1.2.1 := congrFun hin 2
    have hsrc3 : x.regs (src 3) = d.1.1.2.2 := congrFun hin 3
    have hsrc4 : x.regs (src 4) = d.1.2 := congrFun hin 4
    have hsrc5 : x.regs (src 5) = d.2 := congrFun hin 5
    let x₁ := x.set (tmp 0) (d.1.1.1.1 + d.1.1.1.2)
    let x₂ := x₁.set (tmp 1) (x₁.regs (src 4))
    let x₃ := x₂.set (tmp 2) (x₂.regs (src 5))
    let x₄ := x₃.set (tmp 8) (x₃.regs (src 3))
    let x₅ := x₄.set (tmp 9) (x₄.regs (src 2))
    have hc1 :
        ExecWithin (B := .exact) w (.op (.exactBin .add (tmp 0) (src 0) (src 1))) x x₁ 1 := by
      apply ExecWithin.op
      rw [Op.eval_exactBin, hsrc0, hsrc1]
      exact Data.put_of_fits (hfit.of_le (by omega))
    have hc2 : ExecWithin (B := .exact) w (.op (.copy (tmp 1) (src 4))) x₁ x₂ 1 := ExecWithin.copy
    have hc3 : ExecWithin (B := .exact) w (.op (.copy (tmp 2) (src 5))) x₂ x₃ 1 := ExecWithin.copy
    have hc4 : ExecWithin (B := .exact) w (.op (.copy (tmp 8) (src 3))) x₃ x₄ 1 := ExecWithin.copy
    have hc5 : ExecWithin (B := .exact) w (.op (.copy (tmp 9) (src 2))) x₄ x₅ 1 := ExecWithin.copy
    have hx₅_bdd : x₅.Bounded w :=
      hc5.bounded (hc4.bounded (hc3.bounded (hc2.bounded (hc1.bounded hx))))
    have hne : ∀ (a b : Fin 10), a ≠ b → tmp a ≠ tmp b := fun a b hab h => hab (hi h)
    have hbase0 : (x₅.comap tmp).regs 0 = d.1.1.1.1 + d.1.1.1.2 := by
      change x₅.regs (tmp 0) = d.1.1.1.1 + d.1.1.1.2
      dsimp only [x₅, x₄, x₃, x₂, x₁, Data.set]
      rw [Function.update_of_ne (hne 0 9 (by decide)),
        Function.update_of_ne (hne 0 8 (by decide)),
        Function.update_of_ne (hne 0 2 (by decide)),
        Function.update_of_ne (hne 0 1 (by decide)),
        Function.update_self]
    have hidx1 : (x₅.comap tmp).regs 1 = d.1.2 := by
      change x₅.regs (tmp 1) = d.1.2
      dsimp only [x₅, x₄, x₃, x₂, x₁, Data.set]
      rw [Function.update_of_ne (hne 1 9 (by decide)),
        Function.update_of_ne (hne 1 8 (by decide)),
        Function.update_of_ne (hne 1 2 (by decide)),
        Function.update_self, Function.update_of_ne (hd 4 0), hsrc4]
    have hval2 : (x₅.comap tmp).regs 2 = d.2 := by
      change x₅.regs (tmp 2) = d.2
      dsimp only [x₅, x₄, x₃, x₂, x₁, Data.set]
      rw [Function.update_of_ne (hne 2 9 (by decide)),
        Function.update_of_ne (hne 2 8 (by decide)),
        Function.update_self, Function.update_of_ne (hd 5 1),
        Function.update_of_ne (hd 5 0), hsrc5]
    have hw8 : (x₅.comap tmp).regs 8 = w := by
      change x₅.regs (tmp 8) = w
      dsimp only [x₅, x₄, x₃, x₂, x₁, Data.set]
      rw [Function.update_of_ne (hne 8 9 (by decide)),
        Function.update_self, Function.update_of_ne (hd 3 2),
        Function.update_of_ne (hd 3 1), Function.update_of_ne (hd 3 0), hsrc3, heq]
    have hk9 : (x₅.comap tmp).regs 9 = d.1.1.2.1 := by
      change x₅.regs (tmp 9) = d.1.1.2.1
      dsimp only [x₅, x₄, x₃, x₂, x₁, Data.set]
      rw [Function.update_self, Function.update_of_ne (hd 2 8),
        Function.update_of_ne (hd 2 2), Function.update_of_ne (hd 2 1),
        Function.update_of_ne (hd 2 0), hsrc2]
    obtain ⟨y_core, hex_core, hymem, _, _, _⟩ :=
      writePackedCode_execWithin hw hkw hidx (hx₅_bdd.comap tmp) hbase0 hidx1 hval2 hw8 hk9 hfit
    have hex_ren := hex_core.rename hi
    let y := y_core.extend tmp x₅
    refine ⟨y, (hc1.seq (hc2.seq (hc3.seq (hc4.seq (hc5.seq hex_ren))))).mono
      (by change 1 + (1 + (1 + (1 + (1 + 45)))) ≤ 50 * (4 + 0 + 1); omega), ?_, ?_, ?_⟩
    · apply Memory.State.ext
      · change y_core.mem =
          writePacked (d.1.1.1.1 + d.1.1.1.2) d.1.1.2.1 d.1.1.2.2 x.mem d.1.2 d.2
        rw [hymem, ← heq]
        rfl
      · change y.regs frontier = x.regs frontier
        have hnot : ¬∃ j : Fin 10, tmp j = frontier := by rintro ⟨j, hj⟩; exact hf j hj
        change Function.extend tmp y_core.regs x₅.regs frontier = x.regs frontier
        rw [Function.extend_apply' _ _ _ hnot]
        dsimp only [x₅, x₄, x₃, x₂, x₁, Data.set]
        rw [Function.update_of_ne (hf 9).symm, Function.update_of_ne (hf 8).symm,
          Function.update_of_ne (hf 2).symm, Function.update_of_ne (hf 1).symm,
          Function.update_of_ne (hf 0).symm]
    · intro i
      exact Fin.elim0 i
    · intro i _ htmp
      have hnot : ¬∃ j : Fin 10, tmp j = i := by rintro ⟨j, hj⟩; exact htmp j hj
      change Function.extend tmp y_core.regs x₅.regs i = x.regs i
      rw [Function.extend_apply' _ _ _ hnot]
      dsimp only [x₅, x₄, x₃, x₂, x₁, Data.set]
      rw [Function.update_of_ne (htmp 9).symm, Function.update_of_ne (htmp 8).symm,
        Function.update_of_ne (htmp 2).symm, Function.update_of_ne (htmp 1).symm,
        Function.update_of_ne (htmp 0).symm]

/-! ## Section 2: Dictionary array `Memory.Prog` primitives (`Quot`, `Val`, `LM`, `GM`) -/

/-- Runtime register block of 36 precomputed dictionary layout parameters. -/
@[expose] def DictParams : Type := Fin 36 → ℕ

instance : WordEncoding DictParams := ⟨36, Function.Embedding.refl (Fin 36 → ℕ)⟩

/-- Construct the 36-word parameter vector for `(U, V, w, n_max, h_space)`. -/
@[expose] def mkDictParams (U V w n_max h_space : ℕ) : DictParams := fun i =>
  match i.val with
  | 0 => w
  | 1 => n_max
  | 2 => n_max - 1
  | 3 => offQuot h_space
  | 4 => quotientBits U n_max
  | 5 => offVal U w n_max h_space
  | 6 => valBits V
  | 7 => offLMSub U V w n_max h_space 0
  | 8 => offLMSub U V w n_max h_space 1
  | 9 => offLMSub U V w n_max h_space 2
  | 10 => offLMSub U V w n_max h_space 3
  | 11 => offLMSub U V w n_max h_space 4
  | 12 => offLMSub U V w n_max h_space 5
  | 13 => offLMSub U V w n_max h_space 6
  | 14 => offLMSub U V w n_max h_space 7
  | 15 => offLMSub U V w n_max h_space 8
  | 16 => effBucketPosBits n_max
  | 17 => offGM U V w n_max h_space
  | 18 => globalPtrBits n_max
  | 19 => bucketBits n_max
  | 20 => 2 ^ bucketBits n_max - 1
  | 21 => slabSize n_max
  | 22 => slabSize n_max - 1
  | 23 => 2 * slabSize n_max
  | 24 => dirSlabsPerBucket n_max
  | 25 => dirSlabsPerBucket n_max - 1
  | 26 => tailCapPerBucket n_max
  | 27 => gmSlabDirBase n_max
  | 28 => gmTailPtrBase n_max
  | 29 => gmTailOwnerBase n_max
  | 30 => gmSlabMetaBase n_max
  | 31 => numMicroPerBucket n_max
  | 32 => min n_max (effBucketCap n_max)
  | 33 => U
  | 34 => V
  | 35 => h_space
  | _ => 0

/-- Word width `w` in `DictParams`. -/
@[expose] def dpW (dp : DictParams) : ℕ := dp ⟨0, by decide⟩
/-- Maximum capacity `n_max` in `DictParams`. -/
@[expose] def dpNMax (dp : DictParams) : ℕ := dp ⟨1, by decide⟩
/-- Precomputed `n_max - 1` in `DictParams`. -/
@[expose] def dpNMaxSubOne (dp : DictParams) : ℕ := dp ⟨2, by decide⟩
/-- Quotient array word offset `offQuot h_space` in `DictParams`. -/
@[expose] def dpOffQuot (dp : DictParams) : ℕ := dp ⟨3, by decide⟩
/-- Quotient bit width `quotientBits U n_max` in `DictParams`. -/
@[expose] def dpQuotBits (dp : DictParams) : ℕ := dp ⟨4, by decide⟩
/-- Value array word offset `offVal U w n_max h_space` in `DictParams`. -/
@[expose] def dpOffVal (dp : DictParams) : ℕ := dp ⟨5, by decide⟩
/-- Value bit width `valBits V` in `DictParams`. -/
@[expose] def dpValBits (dp : DictParams) : ℕ := dp ⟨6, by decide⟩
/-- Sub-array word offset `offLMSub U V w n_max h_space c` in `DictParams`. -/
@[expose] def dpOffLMSub (c : Fin 9) (dp : DictParams) : ℕ :=
  match c.val with
  | 0 => dp ⟨7, by decide⟩
  | 1 => dp ⟨8, by decide⟩
  | 2 => dp ⟨9, by decide⟩
  | 3 => dp ⟨10, by decide⟩
  | 4 => dp ⟨11, by decide⟩
  | 5 => dp ⟨12, by decide⟩
  | 6 => dp ⟨13, by decide⟩
  | 7 => dp ⟨14, by decide⟩
  | _ => dp ⟨15, by decide⟩
/-- Local metadata bit width `effBucketPosBits n_max` in `DictParams`. -/
@[expose] def dpLmBits (dp : DictParams) : ℕ := dp ⟨16, by decide⟩
/-- Global metadata word offset `offGM U V w n_max h_space` in `DictParams`. -/
@[expose] def dpOffGM (dp : DictParams) : ℕ := dp ⟨17, by decide⟩
/-- Global metadata pointer bit width `globalPtrBits n_max` in `DictParams`. -/
@[expose] def dpGmBits (dp : DictParams) : ℕ := dp ⟨18, by decide⟩
/-- Bucket index bit width `bucketBits n_max` in `DictParams`. -/
@[expose] def dpBucketBits (dp : DictParams) : ℕ := dp ⟨19, by decide⟩
/-- Bucket bitmask `2 ^ bucketBits n_max - 1` in `DictParams`. -/
@[expose] def dpBucketMask (dp : DictParams) : ℕ := dp ⟨20, by decide⟩
/-- Full-slab size `slabSize n_max` in `DictParams`. -/
@[expose] def dpSlabSize (dp : DictParams) : ℕ := dp ⟨21, by decide⟩
/-- Precomputed `slabSize n_max - 1` in `DictParams`. -/
@[expose] def dpSlabSizeSubOne (dp : DictParams) : ℕ := dp ⟨22, by decide⟩
/-- Precomputed `2 * slabSize n_max` in `DictParams`. -/
@[expose] def dpTwoSlabSize (dp : DictParams) : ℕ := dp ⟨23, by decide⟩
/-- Per-bucket slab directory size `dirSlabsPerBucket n_max` in `DictParams`. -/
@[expose] def dpDirSlabs (dp : DictParams) : ℕ := dp ⟨24, by decide⟩
/-- Precomputed `dirSlabsPerBucket n_max - 1` in `DictParams`. -/
@[expose] def dpDirSlabsSubOne (dp : DictParams) : ℕ := dp ⟨25, by decide⟩
/-- Per-bucket tail capacity `tailCapPerBucket n_max` in `DictParams`. -/
@[expose] def dpTailCap (dp : DictParams) : ℕ := dp ⟨26, by decide⟩
/-- Slab directory base index `gmSlabDirBase n_max` in `DictParams`. -/
@[expose] def dpGmSlabDirBase (dp : DictParams) : ℕ := dp ⟨27, by decide⟩
/-- Tail pointer base index `gmTailPtrBase n_max` in `DictParams`. -/
@[expose] def dpGmTailPtrBase (dp : DictParams) : ℕ := dp ⟨28, by decide⟩
/-- Tail owner base index `gmTailOwnerBase n_max` in `DictParams`. -/
@[expose] def dpGmTailOwnerBase (dp : DictParams) : ℕ := dp ⟨29, by decide⟩
/-- Slab metadata base index `gmSlabMetaBase n_max` in `DictParams`. -/
@[expose] def dpGmSlabMetaBase (dp : DictParams) : ℕ := dp ⟨30, by decide⟩
/-- Micro-buckets per bucket `numMicroPerBucket n_max` in `DictParams`. -/
@[expose] def dpNumMicro (dp : DictParams) : ℕ := dp ⟨31, by decide⟩
/-- Effective per-bucket slot cap `min n_max (effBucketCap n_max)` in `DictParams`. -/
@[expose] def dpMinCap (dp : DictParams) : ℕ := dp ⟨32, by decide⟩
/-- Key universe size `U` in `DictParams`. -/
@[expose] def dpU (dp : DictParams) : ℕ := dp ⟨33, by decide⟩
/-- Value universe size `V` in `DictParams`. -/
@[expose] def dpV (dp : DictParams) : ℕ := dp ⟨34, by decide⟩
/-- Hash block word count `h_space` in `DictParams`. -/
@[expose] def dpHSpace (dp : DictParams) : ℕ := dp ⟨35, by decide⟩

@[simp] theorem p_w_mk (U V w n_max h_space : ℕ) :
    dpW (mkDictParams U V w n_max h_space) = w := rfl
@[simp] theorem p_nMax_mk (U V w n_max h_space : ℕ) :
    dpNMax (mkDictParams U V w n_max h_space) = n_max := rfl
@[simp] theorem p_nMaxSubOne_mk (U V w n_max h_space : ℕ) :
    dpNMaxSubOne (mkDictParams U V w n_max h_space) = n_max - 1 := rfl
@[simp] theorem p_offQuot_mk (U V w n_max h_space : ℕ) :
    dpOffQuot (mkDictParams U V w n_max h_space) = offQuot h_space := rfl
@[simp] theorem p_quotBits_mk (U V w n_max h_space : ℕ) :
    dpQuotBits (mkDictParams U V w n_max h_space) = quotientBits U n_max := rfl
@[simp] theorem p_offVal_mk (U V w n_max h_space : ℕ) :
    dpOffVal (mkDictParams U V w n_max h_space) = offVal U w n_max h_space := rfl
@[simp] theorem p_valBits_mk (U V w n_max h_space : ℕ) :
    dpValBits (mkDictParams U V w n_max h_space) = valBits V := rfl
@[simp] theorem p_lmBits_mk (U V w n_max h_space : ℕ) :
    dpLmBits (mkDictParams U V w n_max h_space) = effBucketPosBits n_max := rfl
@[simp] theorem p_offGM_mk (U V w n_max h_space : ℕ) :
    dpOffGM (mkDictParams U V w n_max h_space) = offGM U V w n_max h_space := rfl
@[simp] theorem p_gmBits_mk (U V w n_max h_space : ℕ) :
    dpGmBits (mkDictParams U V w n_max h_space) = globalPtrBits n_max := rfl
@[simp] theorem p_bucketBits_mk (U V w n_max h_space : ℕ) :
    dpBucketBits (mkDictParams U V w n_max h_space) = bucketBits n_max := rfl
@[simp] theorem p_bucketMask_mk (U V w n_max h_space : ℕ) :
    dpBucketMask (mkDictParams U V w n_max h_space) = 2 ^ bucketBits n_max - 1 := rfl
@[simp] theorem p_slabSize_mk (U V w n_max h_space : ℕ) :
    dpSlabSize (mkDictParams U V w n_max h_space) = slabSize n_max := rfl
@[simp] theorem p_slabSizeSubOne_mk (U V w n_max h_space : ℕ) :
    dpSlabSizeSubOne (mkDictParams U V w n_max h_space) = slabSize n_max - 1 := rfl
@[simp] theorem p_twoSlabSize_mk (U V w n_max h_space : ℕ) :
    dpTwoSlabSize (mkDictParams U V w n_max h_space) = 2 * slabSize n_max := rfl
@[simp] theorem p_dirSlabs_mk (U V w n_max h_space : ℕ) :
    dpDirSlabs (mkDictParams U V w n_max h_space) = dirSlabsPerBucket n_max := rfl
@[simp] theorem p_dirSlabsSubOne_mk (U V w n_max h_space : ℕ) :
    dpDirSlabsSubOne (mkDictParams U V w n_max h_space) = dirSlabsPerBucket n_max - 1 := rfl
@[simp] theorem p_tailCap_mk (U V w n_max h_space : ℕ) :
    dpTailCap (mkDictParams U V w n_max h_space) = tailCapPerBucket n_max := rfl
@[simp] theorem p_gmSlabDirBase_mk (U V w n_max h_space : ℕ) :
    dpGmSlabDirBase (mkDictParams U V w n_max h_space) = gmSlabDirBase n_max := rfl
@[simp] theorem p_gmTailPtrBase_mk (U V w n_max h_space : ℕ) :
    dpGmTailPtrBase (mkDictParams U V w n_max h_space) = gmTailPtrBase n_max := rfl
@[simp] theorem p_gmTailOwnerBase_mk (U V w n_max h_space : ℕ) :
    dpGmTailOwnerBase (mkDictParams U V w n_max h_space) = gmTailOwnerBase n_max := rfl
@[simp] theorem p_gmSlabMetaBase_mk (U V w n_max h_space : ℕ) :
    dpGmSlabMetaBase (mkDictParams U V w n_max h_space) = gmSlabMetaBase n_max := rfl
@[simp] theorem p_numMicro_mk (U V w n_max h_space : ℕ) :
    dpNumMicro (mkDictParams U V w n_max h_space) = numMicroPerBucket n_max := rfl
@[simp] theorem p_minCap_mk (U V w n_max h_space : ℕ) :
    dpMinCap (mkDictParams U V w n_max h_space) = min n_max (effBucketCap n_max) := rfl
@[simp] theorem p_U_mk (U V w n_max h_space : ℕ) :
    dpU (mkDictParams U V w n_max h_space) = U := rfl
@[simp] theorem p_V_mk (U V w n_max h_space : ℕ) :
    dpV (mkDictParams U V w n_max h_space) = V := rfl
@[simp] theorem p_hSpace_mk (U V w n_max h_space : ℕ) :
    dpHSpace (mkDictParams U V w n_max h_space) = h_space := rfl
@[simp] theorem p_offLMSub_mk (U V w n_max h_space : ℕ) (c : Fin 9) :
    dpOffLMSub c (mkDictParams U V w n_max h_space) = offLMSub U V w n_max h_space c.val := by
  rcases c with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | c, hc⟩ <;> try rfl
  omega

/-- Common entry envelope for dictionary `Memory.Prog` operations at `base`. -/
@[expose] def DictEnv (U V w n_max h_space : ℕ) (w' base : ℕ) : Prop :=
  w' = w ∧ Fits w (base + totalSpace U V w n_max h_space)

/-- Combined runtime parameter and memory envelope for parameter-free `Realizes` certificates. -/
structure DictEnvGen (w : ℕ) (dp : DictParams) (base : ℕ) : Prop where
  params : ∃ U V w₀ n_max h_space,
    0 < w₀ ∧ n_max ≤ U ∧ U < 2 ^ w₀ ∧ V ≤ 2 ^ w₀ ∧
    dp = mkDictParams U V w₀ n_max h_space
  env : DictEnv (dpU dp) (dpV dp) (dpW dp) (dpNMax dp) (dpHSpace dp) w base

/-- Parameter-free `Memory.Prog` operation reading `Quotients[d.2.2]` at `base = d.2.1`. -/
@[expose] def readQuotGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog ℕ :=
  readPackedGenProg (((d.2.1, dpOffQuot d.1), (dpQuotBits d.1, dpW d.1)), d.2.2)

/-- Read `Quotients[d.2]` at `base = d.1` in `Memory.Prog`. -/
@[expose] def readQuotProg (U w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog ℕ :=
  readPackedProg d.1 (offQuot h_space) (quotientBits U n_max) w d.2

@[simp] theorem readQuotGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    readQuotGenProg (mkDictParams U V w n_max h_space, d) =
      readQuotProg U w n_max h_space d := rfl

/-- Parameter-free `Memory.Prog` operation writing `d.2.2` to `Quotients[d.2.1.2]` at
`base = d.2.1.1`. -/
@[expose] def writeQuotGenProg (d : DictParams × ((ℕ × ℕ) × ℕ)) : Memory.Prog Unit :=
  writePackedGenProg ((((d.2.1.1, dpOffQuot d.1), (dpQuotBits d.1, dpW d.1)), d.2.1.2), d.2.2)

/-- Write `d.2` to `Quotients[d.1.2]` at `base = d.1.1` in `Memory.Prog`. -/
@[expose] def writeQuotProg (U w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit :=
  writePackedProg d.1.1 (offQuot h_space) (quotientBits U n_max) w d.1.2 d.2

@[simp] theorem writeQuotGenProg_mk (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) :
    writeQuotGenProg (mkDictParams U V w n_max h_space, d) =
      writeQuotProg U w n_max h_space d := rfl

/-- Parameter-free `Memory.Prog` operation reading `Values[d.2.2]` at `base = d.2.1`. -/
@[expose] def readValGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog ℕ :=
  readPackedGenProg (((d.2.1, dpOffVal d.1), (dpValBits d.1, dpW d.1)), d.2.2)

/-- Read `Values[d.2]` at `base = d.1` in `Memory.Prog`. -/
@[expose] def readValProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog ℕ :=
  readPackedProg d.1 (offVal U w n_max h_space) (valBits V) w d.2

@[simp] theorem readValGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    readValGenProg (mkDictParams U V w n_max h_space, d) =
      readValProg U V w n_max h_space d := rfl

/-- Parameter-free `Memory.Prog` operation writing `d.2.2` to `Values[d.2.1.2]` at
`base = d.2.1.1`. -/
@[expose] def writeValGenProg (d : DictParams × ((ℕ × ℕ) × ℕ)) : Memory.Prog Unit :=
  writePackedGenProg ((((d.2.1.1, dpOffVal d.1), (dpValBits d.1, dpW d.1)), d.2.1.2), d.2.2)

/-- Write `d.2` to `Values[d.1.2]` at `base = d.1.1` in `Memory.Prog`. -/
@[expose] def writeValProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit :=
  writePackedProg d.1.1 (offVal U w n_max h_space) (valBits V) w d.1.2 d.2

@[simp] theorem writeValGenProg_mk (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) :
    writeValGenProg (mkDictParams U V w n_max h_space, d) =
      writeValProg U V w n_max h_space d := rfl

/-- Parameter-free `Memory.Prog` operation reading `LocalMeta[c, d.2.2]` at `base = d.2.1`. -/
@[expose] def readLMGenProg (c : Fin 9) (d : DictParams × (ℕ × ℕ)) : Memory.Prog ℕ :=
  readPackedGenProg (((d.2.1, dpOffLMSub c d.1), (dpLmBits d.1, dpW d.1)), d.2.2)

/-- Read `LocalMeta[c, d.2]` at `base = d.1` in `Memory.Prog`. -/
@[expose] def readLMProg (U V w n_max h_space c : ℕ) (d : ℕ × ℕ) : Memory.Prog ℕ :=
  readPackedProg d.1 (offLMSub U V w n_max h_space c) (effBucketPosBits n_max) w d.2

@[simp] theorem readLMGenProg_mk (U V w n_max h_space : ℕ) (c : Fin 9) (d : ℕ × ℕ) :
    readLMGenProg c (mkDictParams U V w n_max h_space, d) =
      readLMProg U V w n_max h_space c.val d := by
  simp [readLMGenProg, readLMProg, readPackedGenProg]

/-- Parameter-free `Memory.Prog` operation writing `d.2.2` to `LocalMeta[c, d.2.1.2]` at
`base = d.2.1.1`. -/
@[expose] def writeLMGenProg (c : Fin 9) (d : DictParams × ((ℕ × ℕ) × ℕ)) : Memory.Prog Unit :=
  writePackedGenProg ((((d.2.1.1, dpOffLMSub c d.1), (dpLmBits d.1, dpW d.1)), d.2.1.2), d.2.2)

/-- Write `d.2` to `LocalMeta[c, d.1.2]` at `base = d.1.1` in `Memory.Prog`. -/
@[expose] def writeLMProg (U V w n_max h_space c : ℕ) (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit :=
  writePackedProg d.1.1 (offLMSub U V w n_max h_space c) (effBucketPosBits n_max) w d.1.2 d.2

@[simp] theorem writeLMGenProg_mk (U V w n_max h_space : ℕ) (c : Fin 9) (d : (ℕ × ℕ) × ℕ) :
    writeLMGenProg c (mkDictParams U V w n_max h_space, d) =
      writeLMProg U V w n_max h_space c.val d := by
  simp [writeLMGenProg, writeLMProg, writePackedGenProg]

/-- Parameter-free `Memory.Prog` operation reading `GlobalMeta[d.2.2]` at `base = d.2.1`. -/
@[expose] def readGMGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog ℕ :=
  readPackedGenProg (((d.2.1, dpOffGM d.1), (dpGmBits d.1, dpW d.1)), d.2.2)

/-- Read `GlobalMeta[d.2]` at `base = d.1` in `Memory.Prog`. -/
@[expose] def readGMProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog ℕ :=
  readPackedProg d.1 (offGM U V w n_max h_space) (globalPtrBits n_max) w d.2

@[simp] theorem readGMGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    readGMGenProg (mkDictParams U V w n_max h_space, d) =
      readGMProg U V w n_max h_space d := rfl

/-- Parameter-free `Memory.Prog` operation writing `d.2.2` to `GlobalMeta[d.2.1.2]` at
`base = d.2.1.1`. -/
@[expose] def writeGMGenProg (d : DictParams × ((ℕ × ℕ) × ℕ)) : Memory.Prog Unit :=
  writePackedGenProg ((((d.2.1.1, dpOffGM d.1), (dpGmBits d.1, dpW d.1)), d.2.1.2), d.2.2)

/-- Write `d.2` to `GlobalMeta[d.1.2]` at `base = d.1.1` in `Memory.Prog`. -/
@[expose] def writeGMProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit :=
  writePackedProg d.1.1 (offGM U V w n_max h_space) (globalPtrBits n_max) w d.1.2 d.2

@[simp] theorem writeGMGenProg_mk (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) :
    writeGMGenProg (mkDictParams U V w n_max h_space, d) =
      writeGMProg U V w n_max h_space d := rfl

/-- Parameter-free `Memory.Prog` operation reading `bCount` (`d = (dp, (base, b))`). -/
@[expose] def readBucketCountGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog ℕ :=
  if dpBucketBits d.1 = 0 then
    readGMGenProg (d.1, (d.2.1, 0))
  else do
    let q_b ← readGMGenProg (d.1, (d.2.1, 4 + 3 * d.2.2))
    let r_b ← readGMGenProg (d.1, (d.2.1, 4 + 3 * d.2.2 + 1))
    pure (q_b * dpSlabSize d.1 + r_b)

/-- `Memory.Prog` operation reading `bCount n_max gm b` (`d = (base, b)`). -/
@[expose] def readBucketCountProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog ℕ :=
  if bucketBits n_max = 0 then
    readGMProg U V w n_max h_space (d.1, 0)
  else do
    let q_b ← readGMProg U V w n_max h_space (d.1, 4 + 3 * d.2)
    let r_b ← readGMProg U V w n_max h_space (d.1, 4 + 3 * d.2 + 1)
    pure (q_b * slabSize n_max + r_b)

@[simp] theorem readBucketCountGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    readBucketCountGenProg (mkDictParams U V w n_max h_space, d) =
      readBucketCountProg U V w n_max h_space d := rfl

/-- Parameter-free `Memory.Prog` operation resolving indexed local slot `j = d.2.2` of bucket
`b = d.2.1.2` at `base = d.2.1.1`. -/
@[expose] def resolveIndexedSlotGenProg (d : DictParams × ((ℕ × ℕ) × ℕ)) : Memory.Prog ℕ :=
  if dpBucketBits d.1 = 0 then
    pure d.2.2
  else do
    let q_b ← readGMGenProg (d.1, (d.2.1.1, 4 + 3 * d.2.1.2))
    if d.2.2 < q_b * dpSlabSize d.1 then do
      let p ← readGMGenProg (d.1,
        (d.2.1.1, dpGmSlabDirBase d.1 + d.2.1.2 * dpDirSlabs d.1 + d.2.2 / dpSlabSize d.1))
      pure (p * dpSlabSize d.1 + (dpSlabSizeSubOne d.1 - d.2.2 % dpSlabSize d.1))
    else do
      let t ← readGMGenProg (d.1,
        (d.2.1.1, dpGmTailPtrBase d.1 + (d.2.1.2 * dpTailCap d.1 +
          (d.2.2 - q_b * dpSlabSize d.1))))
      pure (dpNMaxSubOne d.1 - t)

/-- `Memory.Prog` operation resolving indexed local slot `j = d.2 < effBucketCap n_max` of bucket
`b = d.1.2` at `base = d.1.1` to physical slot `slotOf n_max gm b j < n_max`. -/
@[expose] def resolveIndexedSlotProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ :=
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

@[simp] theorem resolveIndexedSlotGenProg_mk (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) :
    resolveIndexedSlotGenProg (mkDictParams U V w n_max h_space, d) =
      resolveIndexedSlotProg U V w n_max h_space d := rfl

set_option hygiene false in
/-- Helper tactic that simplifies all `DictParams` field accessors and primitive `Memory.Prog`
projections after `dp = mkDictParams U V w₀ n_max h_space` has been substituted. -/
scoped macro "simpDictParamsWith" "[" extra:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    try simp only [
      $extra,*,
      p_w_mk, p_nMax_mk, p_nMaxSubOne_mk, p_offQuot_mk, p_quotBits_mk, p_offVal_mk,
      p_valBits_mk, p_lmBits_mk, p_offGM_mk, p_gmBits_mk, p_bucketBits_mk,
      p_bucketMask_mk, p_slabSize_mk, p_slabSizeSubOne_mk, p_twoSlabSize_mk,
      p_dirSlabs_mk, p_dirSlabsSubOne_mk, p_tailCap_mk, p_gmSlabDirBase_mk,
      p_gmTailPtrBase_mk, p_gmTailOwnerBase_mk, p_gmSlabMetaBase_mk, p_numMicro_mk,
      p_minCap_mk, p_U_mk, p_V_mk, p_hSpace_mk, p_offLMSub_mk,
      readQuotGenProg_mk, writeQuotGenProg_mk, readValGenProg_mk, writeValGenProg_mk,
      readLMGenProg_mk, writeLMGenProg_mk, readGMGenProg_mk, writeGMGenProg_mk,
      readBucketCountGenProg_mk, resolveIndexedSlotGenProg_mk] at *)

set_option hygiene false in
/-- Helper tactic for parameter-free `Realizes` proofs over `DictParams × D`:
runs `realize` and unpacks `d = (dp, d)` and `DictEnvGen` (`h.1`) in every resulting goal. -/
scoped macro "realizeDict" : tactic =>
  `(tactic| (
    realize
    all_goals (
      rcases d with ⟨dp, d⟩
      obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1
      simpDictParamsWith [p_w_mk]
    )))

set_option hygiene false in
/-- Helper tactic for parameter-free `Realizes` proofs over `DictParams × D` with extra
simplification lemmas for sub-programs and preconditions. -/
scoped macro "realizeDictWith" "[" extra:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    realize
    all_goals (
      rcases d with ⟨dp, d⟩
      obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1
      simpDictParamsWith [$extra,*]
    )))

theorem realizes_readQuotGen :
    Realizes .exact readQuotGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      (fun w' d _ => DictEnvGen w' d.1 d.2.1 ∧ d.2.2 < dpNMax d.1)
      (fun _ _ => 0) := by
  have hrp := realizes_readPackedGen
  unfold readQuotGenProg
  realizeDict
  rcases henv with ⟨rfl, hspace⟩
  exact ⟨n_max, rfl, hw, quotientBits_le_of_le_pow hU.le, h.2,
    hspace.of_le (by unfold totalSpace offGM offLM offVal offQuot; omega)⟩

theorem realizes_writeQuotGen :
    Realizes .exact writeQuotGenProg
      (WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ))) (WordEncoding.encode (α := Unit))
      (fun w' d _ => DictEnvGen w' d.1 d.2.1.1 ∧ d.2.1.2 < dpNMax d.1)
      (fun _ _ => 0) := by
  have hwp := realizes_writePackedGen
  unfold writeQuotGenProg
  realizeDict
  rcases henv with ⟨rfl, hspace⟩
  exact ⟨n_max, rfl, hw, quotientBits_le_of_le_pow hU.le, h.2,
    hspace.of_le (by unfold totalSpace offGM offLM offVal offQuot; omega)⟩

theorem realizes_readValGen :
    Realizes .exact readValGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      (fun w' d _ => DictEnvGen w' d.1 d.2.1 ∧ d.2.2 < dpNMax d.1)
      (fun _ _ => 0) := by
  have hrp := realizes_readPackedGen
  unfold readValGenProg
  realizeDict
  rcases henv with ⟨rfl, hspace⟩
  exact ⟨n_max, rfl, hw, Nat.clog_le_of_le_pow hV, h.2,
    hspace.of_le (by unfold totalSpace offGM offLM offVal; omega)⟩

theorem realizes_writeValGen :
    Realizes .exact writeValGenProg
      (WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ))) (WordEncoding.encode (α := Unit))
      (fun w' d _ => DictEnvGen w' d.1 d.2.1.1 ∧ d.2.1.2 < dpNMax d.1)
      (fun _ _ => 0) := by
  have hwp := realizes_writePackedGen
  unfold writeValGenProg
  realizeDict
  rcases henv with ⟨rfl, hspace⟩
  exact ⟨n_max, rfl, hw, Nat.clog_le_of_le_pow hV, h.2,
    hspace.of_le (by unfold totalSpace offGM offLM offVal; omega)⟩

theorem realizes_readLMGen (c : Fin 9) :
    Realizes .exact (readLMGenProg c)
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      (fun w' d _ => DictEnvGen w' d.1 d.2.1 ∧ d.2.2 < totalMicroBuckets (dpNMax d.1))
      (fun _ _ => 0) := by
  have hrp := realizes_readPackedGen
  unfold readLMGenProg
  fin_cases c <;>
  · realizeDict
    rcases henv with ⟨rfl, hspace⟩
    refine ⟨totalMicroBuckets n_max, rfl, hw, effBucketPosBits_le_of_lt_pow hnU hU, h.2,
      hspace.of_le ?_⟩
    unfold totalSpace offGM offLMSub offLM lmSubWords
    omega

theorem realizes_writeLMGen (c : Fin 9) :
    Realizes .exact (writeLMGenProg c)
      (WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ))) (WordEncoding.encode (α := Unit))
      (fun w' d _ => DictEnvGen w' d.1 d.2.1.1 ∧ d.2.1.2 < totalMicroBuckets (dpNMax d.1))
      (fun _ _ => 0) := by
  have hwp := realizes_writePackedGen
  unfold writeLMGenProg
  fin_cases c <;>
  · realizeDict
    rcases henv with ⟨rfl, hspace⟩
    refine ⟨totalMicroBuckets n_max, rfl, hw, effBucketPosBits_le_of_lt_pow hnU hU, h.2,
      hspace.of_le ?_⟩
    unfold totalSpace offGM offLMSub offLM lmSubWords
    omega

theorem realizes_readGMGen :
    Realizes .exact readGMGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      (fun w' d _ => DictEnvGen w' d.1 d.2.1 ∧ d.2.2 < globalMetaLen (dpNMax d.1))
      (fun _ _ => 0) := by
  have hrp := realizes_readPackedGen
  unfold readGMGenProg
  realizeDict
  rcases henv with ⟨rfl, hspace⟩
  exact ⟨globalMetaLen n_max, rfl, hw, globalPtrBits_le_of_lt_pow hnU hU, h.2,
    hspace.of_le (by unfold totalSpace; omega)⟩

theorem realizes_writeGMGen :
    Realizes .exact writeGMGenProg
      (WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ))) (WordEncoding.encode (α := Unit))
      (fun w' d _ => DictEnvGen w' d.1 d.2.1.1 ∧ d.2.1.2 < globalMetaLen (dpNMax d.1))
      (fun _ _ => 0) := by
  have hwp := realizes_writePackedGen
  unfold writeGMGenProg
  realizeDict
  rcases henv with ⟨rfl, hspace⟩
  exact ⟨globalMetaLen n_max, rfl, hw, globalPtrBits_le_of_lt_pow hnU hU, h.2,
    hspace.of_le (by unfold totalSpace; omega)⟩

theorem clientState_readGMProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readGMProg U V w n_max h_space d) = s :=
  rfl

theorem clientResult_readGMProg {U V w n_max h_space base idx : ℕ} (s : Memory.State)
    (hidx : idx < globalMetaLen n_max) :
    (Memory.spec 0).clientResult s (readGMProg U V w n_max h_space (base, idx)) =
      gmAt base U V w n_max h_space s.mem idx := by
  simp [readGMProg, gmAt, hidx]

theorem fits_const_of_dictEnv {U V w₀ n_max h_space w base c : ℕ}
    (h : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base) (hc : c ≤ 24) :
    Fits w c := by
  rcases h.env with ⟨rfl, hspace⟩
  dsimp only [p_U_mk, p_V_mk, p_w_mk, p_nMax_mk, p_hSpace_mk] at hspace
  have hl : 2 ≤ lmSubWords n_max w := Nat.le_add_left 2 _
  have hg : 2 ≤ packedWords (globalMetaLen n_max) (globalPtrBits n_max) w := Nat.le_add_left 2 _
  have hv : 2 ≤ packedWords n_max (valBits V) w := Nat.le_add_left 2 _
  have hq : 2 ≤ packedWords n_max (quotientBits U n_max) w := Nat.le_add_left 2 _
  exact hspace.of_le (by unfold totalSpace offGM offLM offVal offQuot; omega)

theorem fits_of_le_globalMetaLen {U V w₀ n_max h_space w base x : ℕ}
    (h : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base) (hb_pos : 0 < bucketBits n_max)
    (hw : 0 < w₀) (hnU : n_max ≤ U) (hU : U < 2 ^ w₀)
    (hx : x ≤ globalMetaLen n_max) : Fits w x := by
  rcases h.env with ⟨rfl, _⟩
  have hmax := max_n_one_lt_two_pow_w hw hnU hU
  have hlen := globalMetaLen_le_of_bucketBits_pos hb_pos
  exact hmax.of_le (by omega)

theorem fits_of_le_max_n_one {U V w₀ n_max h_space w base x : ℕ}
    (h : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hw : 0 < w₀) (hnU : n_max ≤ U) (hU : U < 2 ^ w₀)
    (hx : x ≤ max n_max 1) : Fits w x := by
  rcases h.env with ⟨rfl, _⟩
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
  rw [effBucketCap_eq_four_mul_slabScale_cubed_of_pos hb, (slabSize_eq_sq_of_pos hb).1]
  unfold dirSlabsPerBucket
  rw [ite_eq_right hb0]
  ring

/-! ## Section 3: `readBucketCountProg` and `resolveIndexedSlotProg` via `realize` -/

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

theorem realizes_readBucketCountGen :
    Realizes .exact readBucketCountGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      (fun w d s => DictEnvGen w d.1 d.2.1 ∧
        SlotStoreInv (dpNMax d.1)
          (gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem) ∧
        d.2.2 < numBuckets (dpNMax d.1))
      (fun _ _ => 0) := by
  have hrg := realizes_readGMGen
  refine Realizes.congr (p := fun d : DictParams × (ℕ × ℕ) =>
      if dpBucketBits d.1 = 0 then do
        let i0 ← pure 0
        readGMGenProg (d.1, (d.2.1, i0))
      else do
        let q_idx ← pure (4 + 3 * d.2.2)
        let q_b ← readGMGenProg (d.1, (d.2.1, q_idx))
        let r_idx ← pure (q_idx + 1)
        let r_b ← readGMGenProg (d.1, (d.2.1, r_idx))
        pure (q_b * dpSlabSize d.1 + r_b)) ?_
    (fun d => by simp [readBucketCountGenProg, ← PFunctor.FreeM.bind_eq_bind])
  realizeDict
  · exact h.1
  · unfold globalMetaLen; omega
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hc
    exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU (le_of_lt (gmQIdx_lt hb_pos h.2.2))
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact h.1
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hc
    exact gmQIdx_lt hb_pos h.2.2
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hc
    exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU (le_of_lt (gmRIdx_lt hb_pos h.2.2))
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hc
    exact gmRIdx_lt hb_pos h.2.2
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hc
    have hb0 : bucketBits n_max ≠ 0 := hc
    have hq_lt : 4 + 3 * d.2 < globalMetaLen n_max := gmQIdx_lt hb_pos h.2.2
    have hr_lt : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos h.2.2
    rw [clientState_readGMProg, clientResult_readGMProg _ hq_lt,
      clientResult_readGMProg _ hr_lt]
    have hbc := bCount_le_n_max h.2.1 d.2
    unfold bCount at hbc
    simp only [hb0, ↓reduceIte, h.2.2, gmQIdx, gmRIdx] at hbc
    exact fits_of_le_max_n_one h.1 hw hnU hU (by omega)

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
    change 2 + memoryCost (if d.2 < _ * slabSize n_max then _ else _) _ ≤ 4
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
  · simp only [hb0, ↓reduceIte]
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
    · have hr_cap := (hinv.tailOffset_lt hb_pos hb hj_bc hj_slab).2
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
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) d.1.1)
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
    (hb_pos : 0 < bucketBits n_max)
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
  exact gmTailPtrIdx_lt hb_pos hb (hinv.tailOffset_lt hb_pos hb hj_bc hj_not_slab).2

private theorem resolveIndexedSlot_tail_le {U V w₀ n_max h_space : ℕ}
    (hb_pos : 0 < bucketBits n_max)
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
  have hptr_lt := resolveIndexedSlot_tailIdx_lt hb_pos d s hinv hb hj_bc hc
  have hj_not_slab := hc
  have hq_lt : 4 + 3 * d.1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos hb
  rw [clientState_readGMProg, clientResult_readGMProg _ hptr_lt]
  rw [clientResult_readGMProg _ hq_lt] at hj_not_slab ⊢
  have hr_lt : d.2 - gmAt d.1.1 U V w₀ n_max h_space s.mem (4 + 3 * d.1.2) * slabSize n_max <
      gmAt d.1.1 U V w₀ n_max h_space s.mem (gmRIdx d.1.2) :=
    (hinv.tailOffset_lt hb_pos hb hj_bc hj_not_slab).1
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

theorem realizes_resolveIndexedSlotGen :
    Realizes .exact resolveIndexedSlotGenProg
      (WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ))) (WordEncoding.encode (α := ℕ))
      (fun w d s => DictEnvGen w d.1 d.2.1.1 ∧
        SlotStoreInv (dpNMax d.1)
          (gmAt d.2.1.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem) ∧
        d.2.1.2 < numBuckets (dpNMax d.1) ∧
        d.2.2 < bCount (dpNMax d.1)
          (gmAt d.2.1.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem)
          d.2.1.2 ∧
        d.2.2 < effBucketCap (dpNMax d.1))
      (fun _ _ => 0) := by
  have hrg := realizes_readGMGen
  refine Realizes.congr (p := fun d : DictParams × ((ℕ × ℕ) × ℕ) =>
      if dpBucketBits d.1 = 0 then
        pure d.2.2
      else do
        let q_idx ← pure (4 + 3 * d.2.1.2)
        let q_b ← readGMGenProg (d.1, (d.2.1.1, q_idx))
        let qK ← pure (q_b * dpSlabSize d.1)
        if d.2.2 < qK then do
          let dir_idx ←
            pure (dpGmSlabDirBase d.1 + d.2.1.2 * dpDirSlabs d.1 + d.2.2 / dpSlabSize d.1)
          let p ← readGMGenProg (d.1, (d.2.1.1, dir_idx))
          pure (p * dpSlabSize d.1 + (dpSlabSizeSubOne d.1 - d.2.2 % dpSlabSize d.1))
        else do
          let ptr_idx ←
            pure (dpGmTailPtrBase d.1 + (d.2.1.2 * dpTailCap d.1 + (d.2.2 - qK)))
          let t ← readGMGenProg (d.1, (d.2.1.1, ptr_idx))
          pure (dpNMaxSubOne d.1 - t)) ?_
    (fun d => by simp [resolveIndexedSlotGenProg, ← PFunctor.FreeM.bind_eq_bind])
  realizeDict
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero ‹¬bucketBits n_max = 0›
    exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU (le_of_lt (gmQIdx_lt hb_pos h.2.2.1))
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact h.1
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero ‹¬bucketBits n_max = 0›
    exact gmQIdx_lt hb_pos h.2.2.1
  · have hb0 : ¬bucketBits n_max = 0 := ‹¬bucketBits n_max = 0›
    have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    have hq_lt : 4 + 3 * d.1.2 < globalMetaLen n_max := gmQIdx_lt hb_pos h.2.2.1
    rw [clientResult_readGMProg _ hq_lt]
    have hbc := bCount_le_n_max h.2.1 d.1.2
    unfold bCount at hbc
    simp only [hb0, ↓reduceIte, h.2.2.1, gmQIdx] at hbc
    exact fits_of_le_max_n_one h.1 hw hnU hU (by omega)
  · exact Nat.ne_of_gt (slabSize_pos n_max)
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero ‹¬bucketBits n_max = 0›
    exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU
      (le_of_lt (resolveIndexedSlot_dir_lt hb_pos h.2.2.1 h.2.2.2.2))
  · exact h.1
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero ‹¬bucketBits n_max = 0›
    exact resolveIndexedSlot_dir_lt hb_pos h.2.2.1 h.2.2.2.2
  · have : d.2 % slabSize n_max < slabSize n_max := Nat.mod_lt d.2 (slabSize_pos n_max)
    omega
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero ‹¬bucketBits n_max = 0›
    exact resolveIndexedSlot_slab_fit hw hnU hU hb_pos d s h.1 h.2.1 h.2.2.1 h.2.2.2.2 hc
  · omega
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero ‹¬bucketBits n_max = 0›
    exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU
      (le_of_lt (resolveIndexedSlot_tailIdx_lt hb_pos d s h.2.1 h.2.2.1 h.2.2.2.1 hc))
  · exact h.1
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero ‹¬bucketBits n_max = 0›
    exact resolveIndexedSlot_tailIdx_lt hb_pos d s h.2.1 h.2.2.1 h.2.2.2.1 hc
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero ‹¬bucketBits n_max = 0›
    exact resolveIndexedSlot_tail_le hb_pos d s h.2.1 h.2.2.1 h.2.2.2.1 hc

/-! ## Section 4: Pure state effects and costs of `read*Prog` and `write*Prog` -/

theorem clientState_readQuotProg (U w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readQuotProg U w n_max h_space d) = s := rfl

theorem clientState_readValProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readValProg U V w n_max h_space d) = s := rfl

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

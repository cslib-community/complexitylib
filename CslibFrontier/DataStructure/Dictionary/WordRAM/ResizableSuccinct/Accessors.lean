/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Compaction

/-!
# `Memory.Prog` Bit-Slice and Dense Pair-Stream Primitives via `realize`

This module implements overflow-free `Memory.Prog` leaf accessors for the compacted epoch layout
and certifies every primitive with `RealizesBounded .exact` (`¬ReadsWidth`) via `by realize`:
* overflow-free bit-slice and packed-array accessors (`readBitSliceGenProg`, `writeBitSliceGenProg`,
  `readPackedCompGenProg`, `writePackedCompGenProg`);
* dense `(quotient, value)` pair-stream accessors (`readCompQuotGenProg`, `writeCompQuotGenProg`,
  `readCompValGenProg`, `writeCompValGenProg`, `copyCompItemGenProg`, `clearCompItemGenProg`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.readBitSliceGenProg`,
  `writeBitSliceGenProg`, `readPackedCompGenProg`, `writePackedCompGenProg`: bit-slice primitives.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.readCompQuotGenProg`,
  `writeCompQuotGenProg`, `readCompValGenProg`, `writeCompValGenProg`, `copyCompItemGenProg`,
  `clearCompItemGenProg`: dense item stream `Memory.Prog` primitives.

## Main results

* `realizesBounded_readBitSliceGen`, `realizesBounded_writeBitSliceGen`,
  `realizesBounded_readPackedCompGen`, `realizesBounded_writePackedCompGen`,
  `realizesBounded_readCompQuotGen`, `realizesBounded_writeCompQuotGen`,
  `realizesBounded_readCompValGen`, `realizesBounded_writeCompValGen`:
  parameter-free `RealizesBounded .exact` certificates.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM

/-! ## Section 1: `Memory.Prog` Simp Lemmas -/

theorem prog_clientResult_bind {α β : Type} (p : Memory.Prog α)
    (k : α → Memory.Prog β) (s : Memory.State) :
    (Memory.spec 0).clientResult s (p >>= k) =
      (Memory.spec 0).clientResult ((Memory.spec 0).clientState s p)
        (k ((Memory.spec 0).clientResult s p)) := (Memory.spec 0).clientResult_bind p k s
theorem prog_runClient_state_bind {α β : Type} (p : Memory.Prog α)
    (k : α → Memory.Prog β) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (p >>= k))) =
      (Memory.spec 0).clientState ((Memory.spec 0).clientState s p)
        (k ((Memory.spec 0).clientResult s p)) := (Memory.spec 0).fst_snd_runClient_bind p k s
attribute [local simp] Realization.memoryCost_bind'

theorem prog_clientResult_pure {α : Type} (x : α) (s : Memory.State) :
    (Memory.spec 0).clientResult s (pure x : Memory.Prog α) = x := rfl
theorem prog_runClient_state_pure {α : Type} (x : α) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (pure x : Memory.Prog α))) = s := rfl
theorem prog_clientResult_map {α β : Type} (f : α → β) (p : Memory.Prog α)
    (s : Memory.State) :
    (Memory.spec 0).clientResult s (f <$> p) = f ((Memory.spec 0).clientResult s p) := by
  rw [← bind_pure_comp, prog_clientResult_bind, prog_clientResult_pure]
theorem prog_runClient_state_map {α β : Type} (f : α → β) (p : Memory.Prog α)
    (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (f <$> p))) =
      (Memory.spec 0).clientState s p := by rw [← bind_pure_comp, prog_runClient_state_bind]; rfl
theorem prog_memoryCost_map {α β : Type} (f : α → β) (p : Memory.Prog α)
    (s : Memory.State) : memoryCost (f <$> p) s = memoryCost p s := by
  rw [← bind_pure_comp, memoryCost_bind', memoryCost_pure, Nat.add_zero]
theorem prog_clientResult_read (a : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (Memory.read a) = s.mem a := rfl
theorem prog_runClient_state_read (a : ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (Memory.read a))) = s := rfl
theorem prog_memoryCost_read (a : ℕ) (s : Memory.State) :
    memoryCost (Memory.read a) s = 1 := rfl
theorem prog_clientResult_write (a v : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (Memory.write a v) = () := rfl
theorem prog_runClient_state_write (a v : ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (Memory.write a v))) =
      { mem := Function.update s.mem a v, frontier := s.frontier } := rfl
theorem prog_memoryCost_write (a v : ℕ) (s : Memory.State) :
    memoryCost (Memory.write a v) s = 1 := rfl

attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 2: Overflow-Free Bit-Slice and Packed-Array Primitives -/

/-- Compute `min a b` in `Memory.Prog`. -/
private def minWidthProg : ℕ × ℕ → Memory.Prog ℕ
  | (a, b) => if a < b then pure a else pure b

@[simp] private theorem clientResult_minWidthProg (a b : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (minWidthProg (a, b)) = min a b := by
  dsimp only [minWidthProg]
  by_cases h : a < b
  · rw [ite_eq_left h, Nat.min_eq_left h.le]; rfl
  · rw [ite_eq_right h, Nat.min_eq_right (Nat.le_of_not_lt h)]; rfl

private theorem clientState_minWidthProg (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (minWidthProg p) = s := by
  rcases p with ⟨a, b⟩; dsimp only [minWidthProg]; split_ifs <;> rfl

@[simp] private theorem runClient_state_minWidthProg (p : ℕ × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (minWidthProg p))) = s :=
  clientState_minWidthProg p s

@[simp] private theorem memoryCost_minWidthProg (p : ℕ × ℕ) (s : Memory.State) :
    memoryCost (minWidthProg p) s = 0 := by
  rcases p with ⟨a, b⟩; dsimp only [minWidthProg]; split_ifs <;> rfl

/-- Precondition for `minWidthProg`. -/
private def MinWidthPre (_w : ℕ) (_p : ℕ × ℕ) (_s : Memory.State) : Prop := True

private theorem realizesBounded_minWidth :
    RealizesBounded .exact minWidthProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      MinWidthPre (fun _ _ => 0) := by
  realize

/-- Compute `2 ^ k₀ - 1` overflow-free for all `k₀ ≤ w` (`0 < w`). -/
private def maskOfWidthProg (k₀ : ℕ) : Memory.Prog ℕ :=
  if k₀ = 0 then pure 0
  else do
    let half := 1 <<< (k₀ - 1)
    pure (half + (half - 1))

private theorem two_pow_pred_add_sub_one {k₀ : ℕ} (hk : k₀ ≠ 0) :
    (1 <<< (k₀ - 1)) + ((1 <<< (k₀ - 1)) - 1) = 2 ^ k₀ - 1 := by
  rw [Nat.shiftLeft_eq, one_mul]
  have hpow : 2 ^ k₀ = 2 ^ (k₀ - 1) * 2 := by
    rw [← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk)]
  have h1 : 1 ≤ 2 ^ (k₀ - 1) := Nat.one_le_two_pow
  omega

@[simp] private theorem clientResult_maskOfWidthProg (k₀ : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (maskOfWidthProg k₀) = 2 ^ k₀ - 1 := by
  dsimp only [maskOfWidthProg]
  by_cases hk : k₀ = 0
  · subst hk; rfl
  · rw [ite_eq_right hk]; exact two_pow_pred_add_sub_one hk

private theorem clientState_maskOfWidthProg (k₀ : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (maskOfWidthProg k₀) = s := by
  dsimp only [maskOfWidthProg]; split_ifs <;> rfl

@[simp] private theorem runClient_state_maskOfWidthProg (k₀ : ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (maskOfWidthProg k₀))) = s :=
  clientState_maskOfWidthProg k₀ s

@[simp] private theorem memoryCost_maskOfWidthProg (k₀ : ℕ) (s : Memory.State) :
    memoryCost (maskOfWidthProg k₀) s = 0 := by
  dsimp only [maskOfWidthProg]; split_ifs <;> rfl

/-- Precondition for `maskOfWidthProg`. -/
private def MaskOfWidthPre (w k₀ : ℕ) (_s : Memory.State) : Prop :=
  0 < w ∧ k₀ ≤ w

private theorem realizesBounded_maskOfWidth :
    RealizesBounded .exact maskOfWidthProg
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := ℕ))
      MaskOfWidthPre (fun _ _ => 0) := by
  realize
  all_goals (
    obtain ⟨hw, hk⟩ := h
    have hlt : d - 1 < w := by omega
    have hpow_lt : 2 ^ (d - 1) < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hlt)
  all_goals try omega
  all_goals try (rw [Nat.shiftLeft_eq, one_mul]; exact Nat.one_le_two_pow)
  all_goals try (rw [Nat.shiftLeft_eq, one_mul]; exact hpow_lt)
  all_goals (
    rw [two_pow_pred_add_sub_one hc]
    exact (Nat.sub_lt (Nat.two_pow_pos d) one_pos).trans_le (Nat.pow_le_pow_right two_pos hk))

/-- Read a `k`-bit slice starting at `(base + wOff, bOff)` in `Memory.Prog`. -/
def readBitSliceGenProg : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((base, (wOff, bOff)), (k, wVal)) => do
    let rem ← pure (wVal - bOff)
    let k₀ ← minWidthProg (k, rem)
    let mask₀ ← maskOfWidthProg k₀
    let word₀ ← Memory.read (base + wOff)
    let word₁ ← Memory.read (base + wOff + 1)
    let low := (word₀ >>> bOff) &&& mask₀
    let high := word₁ &&& ((1 <<< (k - k₀)) - 1)
    pure (low ^^^ (high <<< k₀))

@[simp] theorem clientResult_readBitSliceGenProg (base wOff bOff k w : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (readBitSliceGenProg ((base, (wOff, bOff)), (k, w))) =
      readBitSlice base wOff bOff k w s.mem := by
  simp [readBitSliceGenProg, readBitSlice, Nat.shiftLeft_eq]

theorem clientState_readBitSliceGenProg (d : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (readBitSliceGenProg d) = s := by
  rcases d with ⟨⟨base, ⟨wOff, bOff⟩⟩, ⟨k, wVal⟩⟩
  unfold StateTransitionSpec.clientState
  simp [readBitSliceGenProg]

@[simp] theorem runClient_state_readBitSliceGenProg
    (d : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (readBitSliceGenProg d))) = s :=
  clientState_readBitSliceGenProg d s

@[simp] theorem memoryCost_readBitSliceGenProg (d : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (readBitSliceGenProg d) s = 2 := by
  rcases d with ⟨⟨base, ⟨wOff, bOff⟩⟩, ⟨k, wVal⟩⟩
  simp [readBitSliceGenProg]

/-- Precondition for `readBitSliceGenProg`. -/
@[expose] def ReadBitSlicePre (w : ℕ) : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.State → Prop
  | ((base, (wOff, bOff)), (k, wVal)), s =>
    0 < w ∧ w = wVal ∧ k ≤ w ∧ bOff < w ∧ base + wOff + 1 < s.frontier

theorem realizesBounded_readBitSliceGen :
    RealizesBounded .exact readBitSliceGenProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      ReadBitSlicePre (fun _ _ => 0) := by
  have hmin := realizesBounded_minWidth
  have hmask := realizesBounded_maskOfWidth
  realize
  all_goals (
    rcases d with ⟨⟨base, ⟨wOff, bOff⟩⟩, ⟨k, wVal⟩⟩
    obtain ⟨hw, hwVal, hkw, hbOff, hfr⟩ := h
    subst hwVal
    try simp only [StateTransitionSpec.clientState, clientResult_minWidthProg,
      runClient_state_minWidthProg, clientResult_maskOfWidthProg,
      runClient_state_maskOfWidthProg] at *
    have hk0_le : min k (w - bOff) ≤ k := Nat.min_le_left _ _
    have hk0_le_w : min k (w - bOff) ≤ w := hk0_le.trans hkw
    have hk1_lt : k - min k (w - bOff) < w := by
      by_cases hlt : k ≤ w - bOff
      · rw [Nat.min_eq_left hlt]; omega
      · rw [Nat.min_eq_right (by omega)]; omega)
  all_goals try exact trivial
  all_goals try exact ⟨hw, hk0_le_w⟩
  all_goals try (refine lt_of_le_of_lt ?_ hmem.1; omega)
  all_goals try omega
  all_goals try (rw [Nat.shiftLeft_eq, one_mul]; exact Nat.one_le_two_pow)
  all_goals try (rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right one_lt_two hk1_lt)
  all_goals (
    have hlow_lt : ((s.mem (base + wOff) >>> bOff) &&& (2 ^ min k (w - bOff) - 1)) < 2 ^ w := by
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le (Nat.pow_le_pow_right two_pos hk0_le_w)
    have hhigh_lt : (s.mem (base + wOff + 1) &&& ((1 <<< (k - min k (w - bOff))) - 1)) <<<
        min k (w - bOff) < 2 ^ w := by
      rw [Nat.shiftLeft_eq 1, one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq]
      calc (s.mem (base + wOff + 1) % 2 ^ (k - min k (w - bOff))) * 2 ^ min k (w - bOff)
          < 2 ^ (k - min k (w - bOff)) * 2 ^ min k (w - bOff) :=
            Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.two_pow_pos _)
        _ = 2 ^ k := by rw [← Nat.pow_add, Nat.sub_add_cancel hk0_le]
        _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hkw
    try exact hhigh_lt
    try exact Nat.xor_lt_two_pow hlow_lt hhigh_lt)

/-- Write the low `k₀`-bit portion of `val` into `base + wOff` at bit offset `bOff`. -/
private def writeBitSliceLowProg : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((base, wOff), (bOff, mask₀)), val) => do
    let word₀ ← Memory.read (base + wOff)
    let old₀ := (word₀ >>> bOff) &&& mask₀
    let val₀ := val &&& mask₀
    Memory.write (base + wOff) (word₀ ^^^ ((old₀ ^^^ val₀) <<< bOff))

private def WriteBitSliceLowPre (w : ℕ) : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((base, wOff), (bOff, mask₀)), _val), s =>
    ∃ k₀, mask₀ = 2 ^ k₀ - 1 ∧ bOff < w ∧ bOff + k₀ ≤ w ∧ base + wOff < s.frontier

private theorem realizesBounded_writeBitSliceLow :
    RealizesBounded .exact writeBitSliceLowProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ)) (WordEncoding.encode (α := Unit))
      WriteBitSliceLowPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨⟨base, wOff⟩, ⟨bOff, mask₀⟩⟩, val⟩
    obtain ⟨k₀, rfl, hbOff, hbk, hfr⟩ := h
    dsimp only at *)
  all_goals try (refine lt_of_le_of_lt ?_ hmem.1; omega)
  all_goals (
    have hδ_lt : (((s.mem (base + wOff) >>> bOff) &&& (2 ^ k₀ - 1)) ^^^
        (val &&& (2 ^ k₀ - 1))) < 2 ^ k₀ := by
      refine Nat.xor_lt_two_pow ?_ ?_ <;>
        (rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _))
    have hsh_lt : (((s.mem (base + wOff) >>> bOff) &&& (2 ^ k₀ - 1)) ^^^
        (val &&& (2 ^ k₀ - 1))) <<< bOff < 2 ^ w := by
      rw [Nat.shiftLeft_eq]
      calc _ < 2 ^ k₀ * 2 ^ bOff := Nat.mul_lt_mul_of_pos_right hδ_lt (Nat.two_pow_pos _)
        _ = 2 ^ (k₀ + bOff) := (Nat.pow_add 2 k₀ bOff).symm
        _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos (by omega)
    try exact hsh_lt
    try exact Nat.xor_lt_two_pow (hmem.2 _) hsh_lt)

/-- Write the high `k₁`-bit portion of `val >>> k₀` into `base + wOff + 1` at bit offset `0`. -/
private def writeBitSliceHighProg : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((base, wOff), (k₀, k₁)), val) => do
    let mask₁ := (1 <<< k₁) - 1
    let word₁ ← Memory.read (base + wOff + 1)
    let old₁ := word₁ &&& mask₁
    let val₁ := (val >>> k₀) &&& mask₁
    Memory.write (base + wOff + 1) (word₁ ^^^ (old₁ ^^^ val₁))

private def WriteBitSliceHighPre (w : ℕ) : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((base, wOff), (k₀, k₁)), _val), s =>
    k₀ ≤ w ∧ k₁ < w ∧ base + wOff + 1 < s.frontier

private theorem realizesBounded_writeBitSliceHigh :
    RealizesBounded .exact writeBitSliceHighProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ)) (WordEncoding.encode (α := Unit))
      WriteBitSliceHighPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨⟨base, wOff⟩, ⟨k₀, k₁⟩⟩, val⟩
    obtain ⟨hk0, hk1, hfr⟩ := h
    dsimp only at *)
  all_goals try (refine lt_of_le_of_lt ?_ hmem.1; omega)
  all_goals try (rw [Nat.shiftLeft_eq, one_mul]; exact Nat.one_le_two_pow)
  all_goals try (rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right one_lt_two hk1)
  all_goals (
    have hδ_lt : ((s.mem (base + wOff + 1) &&& ((1 <<< k₁) - 1)) ^^^
        ((val >>> k₀) &&& ((1 <<< k₁) - 1))) < 2 ^ w := by
      rw [Nat.shiftLeft_eq, one_mul]
      refine (Nat.xor_lt_two_pow ?_ ?_).trans_le (Nat.pow_le_pow_right two_pos hk1.le) <;>
        (rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _))
    try exact hδ_lt
    try exact Nat.xor_lt_two_pow (hmem.2 _) hδ_lt)

/-- Write `val` into the `k`-bit slice starting at `(base + wOff, bOff)` in `Memory.Prog`. -/
def writeBitSliceGenProg : ((ℕ × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((base, (wOff, bOff)), (k, wVal)), val) => do
    let rem ← pure (wVal - bOff)
    let k₀ ← minWidthProg (k, rem)
    let mask₀ ← maskOfWidthProg k₀
    writeBitSliceLowProg (((base, wOff), (bOff, mask₀)), val)
    let k₁ ← pure (k - k₀)
    writeBitSliceHighProg (((base, wOff), (k₀, k₁)), val)

@[simp] theorem clientResult_writeBitSliceGenProg
    (d : ((ℕ × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (writeBitSliceGenProg d) = () := by
  rcases d with ⟨⟨⟨base, ⟨wOff, bOff⟩⟩, ⟨k, wVal⟩⟩, val⟩
  simp [writeBitSliceGenProg, writeBitSliceLowProg, writeBitSliceHighProg]
theorem clientState_writeBitSliceGenProg
    (base wOff bOff k w val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (writeBitSliceGenProg (((base, (wOff, bOff)), (k, w)), val)) =
      { mem := writeBitSlice base wOff bOff k w s.mem val, frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState
  simp [writeBitSliceGenProg, writeBitSliceLowProg, writeBitSliceHighProg, writeBitSlice,
    Nat.shiftLeft_eq]
@[simp] theorem runClient_state_writeBitSliceGenProg
    (base wOff bOff k w val : ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s
        (writeBitSliceGenProg (((base, (wOff, bOff)), (k, w)), val)))) =
      { mem := writeBitSlice base wOff bOff k w s.mem val, frontier := s.frontier } :=
  clientState_writeBitSliceGenProg base wOff bOff k w val s
@[simp] theorem memoryCost_writeBitSliceGenProg
    (d : ((ℕ × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (writeBitSliceGenProg d) s = 4 := by
  rcases d with ⟨⟨⟨base, ⟨wOff, bOff⟩⟩, ⟨k, wVal⟩⟩, val⟩
  simp [writeBitSliceGenProg, writeBitSliceLowProg, writeBitSliceHighProg]
/-- Precondition for `writeBitSliceGenProg`. -/
@[expose] def WriteBitSlicePre (w : ℕ) : ((ℕ × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((base, (wOff, bOff)), (k, wVal)), _val), s =>
    0 < w ∧ w = wVal ∧ k ≤ w ∧ bOff < w ∧ base + wOff + 1 < s.frontier

theorem realizesBounded_writeBitSliceGen :
    RealizesBounded .exact writeBitSliceGenProg
      (WordEncoding.encode (α := ((ℕ × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ)) (WordEncoding.encode (α := Unit))
      WriteBitSlicePre (fun _ _ => 0) := by
  have hmin := realizesBounded_minWidth
  have hmask := realizesBounded_maskOfWidth
  have hlow := realizesBounded_writeBitSliceLow
  have hhigh := realizesBounded_writeBitSliceHigh
  realize
  all_goals (
    rcases d with ⟨⟨⟨base, ⟨wOff, bOff⟩⟩, ⟨k, wVal⟩⟩, val⟩
    obtain ⟨hw, hwVal, hkw, hbOff, hfr⟩ := h
    subst hwVal
    try simp only [StateTransitionSpec.clientState, clientResult_minWidthProg,
      runClient_state_minWidthProg, clientResult_maskOfWidthProg,
      runClient_state_maskOfWidthProg, writeBitSliceLowProg,
      prog_runClient_state_bind, prog_runClient_state_read, prog_runClient_state_write] at *
    have hk0_le : min k (w - bOff) ≤ k := Nat.min_le_left _ _
    have hk0_le_w : min k (w - bOff) ≤ w := hk0_le.trans hkw
    have hbk0 : bOff + min k (w - bOff) ≤ w := by
      have := Nat.min_le_right k (w - bOff); omega
    have hk1_lt : k - min k (w - bOff) < w := by
      by_cases hlt : k ≤ w - bOff
      · rw [Nat.min_eq_left hlt]; omega
      · rw [Nat.min_eq_right (by omega)]; omega)
  all_goals try exact trivial
  all_goals try exact ⟨hw, hk0_le_w⟩
  all_goals try exact ⟨min k (w - bOff), rfl, hbOff, hbk0, by omega⟩
  all_goals try exact ⟨hk0_le_w, hk1_lt, hfr⟩
  all_goals omega

/-- Compute `(wordOffset k wVal idx, bitOffset k wVal idx)` overflow-free in `Memory.Prog`. -/
private def packedOffsetProg : (ℕ × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((k, wVal), idx) => do
    let prodMod := (idx % wVal) * k
    let wOff := (idx / wVal) * k + prodMod / wVal
    let bOff := prodMod % wVal
    pure (wOff, bOff)

@[simp] private theorem clientResult_packedOffsetProg (k w idx : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (packedOffsetProg ((k, w), idx)) =
      (wordOffset k w idx, bitOffset k w idx) := by rfl

private theorem clientState_packedOffsetProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (packedOffsetProg d) = s := by
  rcases d with ⟨⟨k, wVal⟩, idx⟩; rfl

@[simp] private theorem runClient_state_packedOffsetProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (packedOffsetProg d))) = s :=
  clientState_packedOffsetProg d s

@[simp] private theorem memoryCost_packedOffsetProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (packedOffsetProg d) s = 0 := by
  rcases d with ⟨⟨k, wVal⟩, idx⟩; rfl

/-- Precondition for `packedOffsetProg`. -/
private def PackedOffsetPre (w : ℕ) : (ℕ × ℕ) × ℕ → Memory.State → Prop
  | ((k, wVal), idx), s =>
    0 < w ∧ w = wVal ∧ k ≤ w ∧ wordOffset k w idx < s.frontier

private theorem realizesBounded_packedOffset :
    RealizesBounded .exact packedOffsetProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ × ℕ))
      PackedOffsetPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨k, wVal⟩, idx⟩
    obtain ⟨hw, hwVal, hkw, hwo⟩ := h
    subst hwVal
    dsimp only at *
    have hwo_def : (idx / w) * k + ((idx % w) * k) / w < s.frontier := hwo)
  all_goals try exact hw.ne'
  all_goals try exact mod_mul_lt_two_pow hw hkw idx
  all_goals (refine lt_of_le_of_lt ?_ hmem.1; omega)

/-- Read `readPacked (base + offset) k w s.mem idx` in `Memory.Prog` with `RealizesBounded`. -/
def readPackedCompGenProg : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog ℕ
  | (((base, offset), (k, wVal)), idx) => do
    let wb ← packedOffsetProg ((k, wVal), idx)
    let addr ← pure (base + offset)
    readBitSliceGenProg ((addr, wb), (k, wVal))

@[simp] theorem clientResult_readPackedCompGenProg (base offset k w idx : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (readPackedCompGenProg (((base, offset), (k, w)), idx)) =
      readPacked (base + offset) k w s.mem idx := by
  simp [readPackedCompGenProg, readBitSlice, readPacked]

theorem clientState_readPackedCompGenProg
    (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readPackedCompGenProg d) = s := by
  rcases d with ⟨⟨⟨base, offset⟩, ⟨k, wVal⟩⟩, idx⟩
  unfold StateTransitionSpec.clientState
  simp [readPackedCompGenProg]

@[simp] theorem runClient_state_readPackedCompGenProg
    (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (readPackedCompGenProg d))) = s :=
  clientState_readPackedCompGenProg d s

@[simp] theorem memoryCost_readPackedCompGenProg
    (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (readPackedCompGenProg d) s = 2 := by
  rcases d with ⟨⟨⟨base, offset⟩, ⟨k, wVal⟩⟩, idx⟩
  simp [readPackedCompGenProg]

/-- Precondition for `readPackedCompGenProg`. -/
@[expose] def ReadPackedCompPre (w : ℕ) : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((base, offset), (k, wVal)), idx), s =>
    ∃ len, 0 < w ∧ w = wVal ∧ k ≤ w ∧ idx < len ∧
      base + offset + packedWords len k w ≤ s.frontier

theorem realizesBounded_readPackedCompGen :
    RealizesBounded .exact readPackedCompGenProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ)) (WordEncoding.encode (α := ℕ))
      ReadPackedCompPre (fun _ _ => 0) := by
  have hpo := realizesBounded_packedOffset
  have hrbs := realizesBounded_readBitSliceGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨base, offset⟩, ⟨k, wVal⟩⟩, idx⟩
    obtain ⟨len, hw, hwVal, hkw, hidx, hfr⟩ := h
    subst hwVal
    try simp only [StateTransitionSpec.clientState, clientResult_packedOffsetProg,
      runClient_state_packedOffsetProg] at *
    have hlt := wordOffset_add_one_lt_packedWords (k := k) hw hidx)
  all_goals try (refine lt_of_le_of_lt ?_ hmem.1; omega)
  all_goals try exact ⟨hw, rfl, hkw, by omega⟩
  all_goals exact ⟨hw, rfl, hkw, bitOffset_lt hw, by omega⟩

/-- Write `writePacked (base + offset) k w s.mem idx val` in `Memory.Prog` with
`RealizesBounded`. -/
def writePackedCompGenProg : (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog Unit
  | ((((base, offset), (k, wVal)), idx), val) => do
    let wb ← packedOffsetProg ((k, wVal), idx)
    let addr ← pure (base + offset)
    writeBitSliceGenProg (((addr, wb), (k, wVal)), val)

@[simp] theorem clientResult_writePackedCompGenProg
    (d : (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (writePackedCompGenProg d) = () := by
  rcases d with ⟨⟨⟨⟨base, offset⟩, ⟨k, wVal⟩⟩, idx⟩, val⟩
  simp [writePackedCompGenProg]

theorem clientState_writePackedCompGenProg
    (base offset k w idx val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (writePackedCompGenProg ((((base, offset), (k, w)), idx), val)) =
      { mem := writePacked (base + offset) k w s.mem idx val, frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState
  simp [writePackedCompGenProg, writeBitSlice, writePacked]

@[simp] theorem runClient_state_writePackedCompGenProg
    (base offset k w idx val : ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s
        (writePackedCompGenProg ((((base, offset), (k, w)), idx), val)))) =
      { mem := writePacked (base + offset) k w s.mem idx val, frontier := s.frontier } :=
  clientState_writePackedCompGenProg base offset k w idx val s

@[simp] theorem memoryCost_writePackedCompGenProg
    (d : (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (writePackedCompGenProg d) s = 4 := by
  rcases d with ⟨⟨⟨⟨base, offset⟩, ⟨k, wVal⟩⟩, idx⟩, val⟩
  simp [writePackedCompGenProg]

/-- Precondition for `writePackedCompGenProg`. -/
@[expose] def WritePackedCompPre (w : ℕ) : (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ → Memory.State → Prop
  | ((((base, offset), (k, wVal)), idx), _val), s =>
    ∃ len, 0 < w ∧ w = wVal ∧ k ≤ w ∧ idx < len ∧
      base + offset + packedWords len k w ≤ s.frontier

theorem realizesBounded_writePackedCompGen :
    RealizesBounded .exact writePackedCompGenProg
      (WordEncoding.encode (α := (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      WritePackedCompPre (fun _ _ => 0) := by
  have hpo := realizesBounded_packedOffset
  have hwbs := realizesBounded_writeBitSliceGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨base, offset⟩, ⟨k, wVal⟩⟩, idx⟩, val⟩
    obtain ⟨len, hw, hwVal, hkw, hidx, hfr⟩ := h
    subst hwVal
    try simp only [StateTransitionSpec.clientState, clientResult_packedOffsetProg,
      runClient_state_packedOffsetProg] at *
    have hlt := wordOffset_add_one_lt_packedWords (k := k) hw hidx)
  all_goals try (refine lt_of_le_of_lt ?_ hmem.1; omega)
  all_goals try exact ⟨hw, rfl, hkw, by omega⟩
  all_goals exact ⟨hw, rfl, hkw, bitOffset_lt hw, by omega⟩

/-! ## Section 3: Dense `(quotient, value)` Pair-Stream `Memory.Prog` Primitives -/

private theorem sub_one_add_self_lt_two_pow {w : ℕ} (hw : 0 < w) :
    (w - 1) + w < 2 ^ w := by
  induction w with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · decide
    · have hih := ih hn
      have h2 : 2 ≤ 2 ^ n := Nat.le_self_pow hn.ne' 2
      rw [Nat.pow_succ]
      omega

/-- Compute `(wOffQ q_bits v_bits wVal d, bOffQ q_bits v_bits wVal d)` overflow-free. -/
private def compQOffsetProg : ((ℕ × ℕ) × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((q_bits, v_bits), wVal), d) => do
    let wbQ ← packedOffsetProg ((q_bits, wVal), d)
    let wbV ← packedOffsetProg ((v_bits, wVal), d)
    let bsum := wbQ.2 + wbV.2
    pure (wbQ.1 + wbV.1 + bsum / wVal, bsum % wVal)

@[simp] private theorem clientResult_compQOffsetProg (q_bits v_bits w d : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (compQOffsetProg (((q_bits, v_bits), w), d)) =
      (wOffQ q_bits v_bits w d, bOffQ q_bits v_bits w d) := by
  simp [compQOffsetProg, wOffQ, bOffQ]

private theorem clientState_compQOffsetProg (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compQOffsetProg d) = s := by
  rcases d with ⟨⟨⟨q_bits, v_bits⟩, wVal⟩, idx⟩
  unfold StateTransitionSpec.clientState
  simp [compQOffsetProg]

@[simp] private theorem runClient_state_compQOffsetProg
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compQOffsetProg d))) = s :=
  clientState_compQOffsetProg d s

@[simp] private theorem memoryCost_compQOffsetProg (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compQOffsetProg d) s = 0 := by
  rcases d with ⟨⟨⟨q_bits, v_bits⟩, wVal⟩, idx⟩
  simp [compQOffsetProg]

/-- Precondition for `compQOffsetProg`. -/
private def CompQOffsetPre (w : ℕ) : ((ℕ × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((q_bits, v_bits), wVal), d), s =>
    0 < w ∧ w = wVal ∧ q_bits ≤ w ∧ v_bits ≤ w ∧ wOffQ q_bits v_bits w d < s.frontier

private theorem realizesBounded_compQOffset :
    RealizesBounded .exact compQOffsetProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ × ℕ))
      CompQOffsetPre (fun _ _ => 0) := by
  have hpo := realizesBounded_packedOffset
  realize
  all_goals (
    rcases d with ⟨⟨⟨q_bits, v_bits⟩, wVal⟩, idx⟩
    obtain ⟨hw, hwVal, hq, hv, hwo⟩ := h
    subst hwVal
    dsimp only at *
    try simp only [StateTransitionSpec.clientState, clientResult_packedOffsetProg,
      runClient_state_packedOffsetProg] at *
    have hwo_def : wordOffset q_bits w idx + wordOffset v_bits w idx +
        (bitOffset q_bits w idx + bitOffset v_bits w idx) / w < s.frontier := hwo
    have hdiv_ge := Nat.zero_le ((bitOffset q_bits w idx + bitOffset v_bits w idx) / w)
    have hbq : bitOffset q_bits w idx < w := bitOffset_lt hw
    have hbv : bitOffset v_bits w idx < w := bitOffset_lt hw
    have hbsum : bitOffset q_bits w idx + bitOffset v_bits w idx < 2 ^ w :=
      lt_of_le_of_lt (by omega) (sub_one_add_self_lt_two_pow hw))
  · unfold PackedOffsetPre; exact ⟨hw, rfl, hq, by omega⟩
  · unfold PackedOffsetPre; exact ⟨hw, rfl, hv, by omega⟩
  all_goals try exact hw.ne'
  all_goals try exact hbsum
  all_goals (refine lt_of_le_of_lt ?_ hmem.1; omega)

/-- Compute `(wOffV q_bits v_bits wVal d, bOffV q_bits v_bits wVal d)` overflow-free. -/
private def compVOffsetProg : ((ℕ × ℕ) × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((q_bits, v_bits), wVal), d) => do
    let wb ← compQOffsetProg (((q_bits, v_bits), wVal), d)
    let bsum := wb.2 + q_bits
    pure (wb.1 + bsum / wVal, bsum % wVal)

@[simp] private theorem clientResult_compVOffsetProg (q_bits v_bits w d : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (compVOffsetProg (((q_bits, v_bits), w), d)) =
      (wOffV q_bits v_bits w d, bOffV q_bits v_bits w d) := by
  simp [compVOffsetProg, wOffV, bOffV]

private theorem clientState_compVOffsetProg (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compVOffsetProg d) = s := by
  rcases d with ⟨⟨⟨q_bits, v_bits⟩, wVal⟩, idx⟩
  unfold StateTransitionSpec.clientState
  simp [compVOffsetProg]

@[simp] private theorem runClient_state_compVOffsetProg
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compVOffsetProg d))) = s :=
  clientState_compVOffsetProg d s

@[simp] private theorem memoryCost_compVOffsetProg (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compVOffsetProg d) s = 0 := by
  rcases d with ⟨⟨⟨q_bits, v_bits⟩, wVal⟩, idx⟩
  simp [compVOffsetProg]

/-- Precondition for `compVOffsetProg`. -/
private def CompVOffsetPre (w : ℕ) : ((ℕ × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((q_bits, v_bits), wVal), d), s =>
    0 < w ∧ w = wVal ∧ q_bits ≤ w ∧ v_bits ≤ w ∧ wOffV q_bits v_bits w d < s.frontier

private theorem realizesBounded_compVOffset :
    RealizesBounded .exact compVOffsetProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ × ℕ))
      CompVOffsetPre (fun _ _ => 0) := by
  have hqo := realizesBounded_compQOffset
  realize
  all_goals (
    rcases d with ⟨⟨⟨q_bits, v_bits⟩, wVal⟩, idx⟩
    obtain ⟨hw, hwVal, hq, hv, hwo⟩ := h
    subst hwVal
    dsimp only at *
    try simp only [clientResult_compQOffsetProg] at *
    have hwo_def : wOffQ q_bits v_bits w idx +
        (bOffQ q_bits v_bits w idx + q_bits) / w < s.frontier := hwo
    have hdiv_ge := Nat.zero_le ((bOffQ q_bits v_bits w idx + q_bits) / w)
    have hbQ : bOffQ q_bits v_bits w idx < w := bOffQ_lt hw
    have hbsum : bOffQ q_bits v_bits w idx + q_bits < 2 ^ w :=
      lt_of_le_of_lt (by omega) (sub_one_add_self_lt_two_pow hw))
  · unfold CompQOffsetPre; exact ⟨hw, rfl, hq, hv, by omega⟩
  all_goals try exact hw.ne'
  all_goals try exact hbsum
  all_goals (refine lt_of_le_of_lt ?_ hmem.1; omega)

/-- Entry precondition for dense `(quotient, value)` stream operations at `itemBase`. -/
@[expose] def CompItemEnv (w : ℕ) (cp : CompParams) (itemBase m_items : ℕ)
    (s : Memory.State) : Prop :=
  ∃ U V N,
    0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
    cp = mkCompParams U V w N ∧
    itemBase + compactedItemWords U V w N m_items ≤ s.frontier

/-- Entry precondition for compacted metadata and circular-window operations at `metaBase`. -/
@[expose] def CompMetaEnv (w : ℕ) (cp : CompParams) (metaBase : ℕ) (s : Memory.State) : Prop :=
  ∃ U V N,
    0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
    cp = mkCompParams U V w N ∧
    metaBase + offCompItems U w N ≤ s.frontier

/-- Read `compQuotAt itemBase U V w N m_items s.mem d` in `Memory.Prog`. -/
def readCompQuotGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, itemBase), d) => do
    let q_bits ← pure (cpQuotBits cp)
    let v_bits ← pure (cpValBits cp)
    let wVal ← pure (cpW cp)
    let wb ← compQOffsetProg (((q_bits, v_bits), wVal), d)
    readBitSliceGenProg ((itemBase, wb), (q_bits, wVal))

theorem clientResult_readCompQuotGenProg {U V w N m_items itemBase d : ℕ}
    (hd : d < m_items) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (readCompQuotGenProg ((mkCompParams U V w N, itemBase), d)) =
      compQuotAt itemBase U V w N m_items s.mem d := by
  simp [readCompQuotGenProg, compQuotAt, hd]
theorem clientState_readCompQuotGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readCompQuotGenProg d) = s := by
  rcases d with ⟨⟨cp, itemBase⟩, idx⟩; unfold StateTransitionSpec.clientState
  simp [readCompQuotGenProg]
@[simp] theorem runClient_state_readCompQuotGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (readCompQuotGenProg d))) = s :=
  clientState_readCompQuotGenProg d s
@[simp] theorem memoryCost_readCompQuotGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readCompQuotGenProg d) s = 2 := by
  rcases d with ⟨⟨cp, itemBase⟩, idx⟩; simp [readCompQuotGenProg]
/-- Precondition for `readCompQuotGenProg`. -/
@[expose] def ReadCompQuotPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, itemBase), d), s => ∃ m_items, CompItemEnv w cp itemBase m_items s ∧ d < m_items

theorem realizesBounded_readCompQuotGen :
    RealizesBounded .exact readCompQuotGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      ReadCompQuotPre (fun _ _ => 0) := by
  have hqo := realizesBounded_compQOffset
  have hrbs := realizesBounded_readBitSliceGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, itemBase⟩, idx⟩
    obtain ⟨m_items, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hidx⟩ := h
    try simp only [cpQuotBits_mk, cpValBits_mk, cpW_mk, StateTransitionSpec.clientState,
      clientResult_compQOffsetProg, runClient_state_compQOffsetProg] at *
    have hq : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU.le
    have hv : valBits V ≤ w := Nat.clog_le_of_le_pow hV
    have hlt := wOffQ_add_one_lt_compactedItemWords (U := U) (V := V) (N := N) hw hidx)
  all_goals try exact ⟨hw, rfl, hq, hv, by omega⟩
  all_goals exact ⟨hw, rfl, hq, bOffQ_lt hw, by omega⟩

/-- Write `q` into `compQuotAt` at dense index `d` in `Memory.Prog`. -/
def writeCompQuotGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, itemBase), d), q) => do
    let q_bits ← pure (cpQuotBits cp)
    let v_bits ← pure (cpValBits cp)
    let wVal ← pure (cpW cp)
    let wb ← compQOffsetProg (((q_bits, v_bits), wVal), d)
    writeBitSliceGenProg (((itemBase, wb), (q_bits, wVal)), q)

@[simp] theorem clientResult_writeCompQuotGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (writeCompQuotGenProg d) = () := by
  rcases d with ⟨⟨⟨cp, itemBase⟩, idx⟩, q⟩; simp [writeCompQuotGenProg]
theorem clientState_writeCompQuotGenProg (U V w N itemBase d q : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (writeCompQuotGenProg (((mkCompParams U V w N, itemBase), d), q)) =
      { mem := writeCompQuot itemBase U V w N s.mem d q, frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState; simp [writeCompQuotGenProg, writeCompQuot]
@[simp] theorem runClient_state_writeCompQuotGenProg
    (U V w N itemBase d q : ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s
        (writeCompQuotGenProg (((mkCompParams U V w N, itemBase), d), q)))) =
      { mem := writeCompQuot itemBase U V w N s.mem d q, frontier := s.frontier } :=
  clientState_writeCompQuotGenProg U V w N itemBase d q s
@[simp] theorem memoryCost_writeCompQuotGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (writeCompQuotGenProg d) s = 4 := by
  rcases d with ⟨⟨⟨cp, itemBase⟩, idx⟩, q⟩; simp [writeCompQuotGenProg]

/-- Precondition for `writeCompQuotGenProg`. -/
@[expose] def WriteCompQuotPre (w : ℕ) : ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, itemBase), d), _q), s => ∃ m_items, CompItemEnv w cp itemBase m_items s ∧ d < m_items

theorem realizesBounded_writeCompQuotGen :
    RealizesBounded .exact writeCompQuotGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      WriteCompQuotPre (fun _ _ => 0) := by
  have hqo := realizesBounded_compQOffset
  have hwbs := realizesBounded_writeBitSliceGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, itemBase⟩, idx⟩, q⟩
    obtain ⟨m_items, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hidx⟩ := h
    try simp only [cpQuotBits_mk, cpValBits_mk, cpW_mk, StateTransitionSpec.clientState,
      clientResult_compQOffsetProg, runClient_state_compQOffsetProg] at *
    have hq : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU.le
    have hv : valBits V ≤ w := Nat.clog_le_of_le_pow hV
    have hlt := wOffQ_add_one_lt_compactedItemWords (U := U) (V := V) (N := N) hw hidx)
  all_goals try exact ⟨hw, rfl, hq, hv, by omega⟩
  all_goals exact ⟨hw, rfl, hq, bOffQ_lt hw, by omega⟩

/-- Read `compValAt itemBase U V w N m_items s.mem d` in `Memory.Prog`. -/
def readCompValGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, itemBase), d) => do
    let q_bits ← pure (cpQuotBits cp)
    let v_bits ← pure (cpValBits cp)
    let wVal ← pure (cpW cp)
    let wb ← compVOffsetProg (((q_bits, v_bits), wVal), d)
    readBitSliceGenProg ((itemBase, wb), (v_bits, wVal))

theorem clientResult_readCompValGenProg {U V w N m_items itemBase d : ℕ}
    (hd : d < m_items) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (readCompValGenProg ((mkCompParams U V w N, itemBase), d)) =
      compValAt itemBase U V w N m_items s.mem d := by
  simp [readCompValGenProg, compValAt, hd]

theorem clientState_readCompValGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readCompValGenProg d) = s := by
  rcases d with ⟨⟨cp, itemBase⟩, idx⟩; unfold StateTransitionSpec.clientState
  simp [readCompValGenProg]
@[simp] theorem runClient_state_readCompValGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (readCompValGenProg d))) = s :=
  clientState_readCompValGenProg d s
@[simp] theorem memoryCost_readCompValGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readCompValGenProg d) s = 2 := by
  rcases d with ⟨⟨cp, itemBase⟩, idx⟩; simp [readCompValGenProg]

/-- Precondition for `readCompValGenProg`. -/
@[expose] def ReadCompValPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, itemBase), d), s => ∃ m_items, CompItemEnv w cp itemBase m_items s ∧ d < m_items

theorem realizesBounded_readCompValGen :
    RealizesBounded .exact readCompValGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      ReadCompValPre (fun _ _ => 0) := by
  have hvo := realizesBounded_compVOffset
  have hrbs := realizesBounded_readBitSliceGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, itemBase⟩, idx⟩
    obtain ⟨m_items, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hidx⟩ := h
    try simp only [cpQuotBits_mk, cpValBits_mk, cpW_mk, StateTransitionSpec.clientState,
      clientResult_compVOffsetProg, runClient_state_compVOffsetProg] at *
    have hq : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU.le
    have hv : valBits V ≤ w := Nat.clog_le_of_le_pow hV
    have hlt := wOffV_add_one_lt_compactedItemWords (U := U) (V := V) (N := N) hw hidx)
  all_goals try exact ⟨hw, rfl, hq, hv, by omega⟩
  all_goals exact ⟨hw, rfl, hv, bOffV_lt hw, by omega⟩

/-- Write `v` into `compValAt` at dense index `d` in `Memory.Prog`. -/
def writeCompValGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, itemBase), d), v) => do
    let q_bits ← pure (cpQuotBits cp)
    let v_bits ← pure (cpValBits cp)
    let wVal ← pure (cpW cp)
    let wb ← compVOffsetProg (((q_bits, v_bits), wVal), d)
    writeBitSliceGenProg (((itemBase, wb), (v_bits, wVal)), v)

@[simp] theorem clientResult_writeCompValGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (writeCompValGenProg d) = () := by
  rcases d with ⟨⟨⟨cp, itemBase⟩, idx⟩, v⟩; simp [writeCompValGenProg]
theorem clientState_writeCompValGenProg (U V w N itemBase d v : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (writeCompValGenProg (((mkCompParams U V w N, itemBase), d), v)) =
      { mem := writeCompVal itemBase U V w N s.mem d v, frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState; simp [writeCompValGenProg, writeCompVal]
@[simp] theorem runClient_state_writeCompValGenProg
    (U V w N itemBase d v : ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s
        (writeCompValGenProg (((mkCompParams U V w N, itemBase), d), v)))) =
      { mem := writeCompVal itemBase U V w N s.mem d v, frontier := s.frontier } :=
  clientState_writeCompValGenProg U V w N itemBase d v s
@[simp] theorem memoryCost_writeCompValGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (writeCompValGenProg d) s = 4 := by
  rcases d with ⟨⟨⟨cp, itemBase⟩, idx⟩, v⟩; simp [writeCompValGenProg]

/-- Precondition for `writeCompValGenProg`. -/
@[expose] def WriteCompValPre (w : ℕ) : ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, itemBase), d), _v), s => ∃ m_items, CompItemEnv w cp itemBase m_items s ∧ d < m_items

theorem realizesBounded_writeCompValGen :
    RealizesBounded .exact writeCompValGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      WriteCompValPre (fun _ _ => 0) := by
  have hvo := realizesBounded_compVOffset
  have hwbs := realizesBounded_writeBitSliceGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, itemBase⟩, idx⟩, v⟩
    obtain ⟨m_items, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hidx⟩ := h
    try simp only [cpQuotBits_mk, cpValBits_mk, cpW_mk, StateTransitionSpec.clientState,
      clientResult_compVOffsetProg, runClient_state_compVOffsetProg] at *
    have hq : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU.le
    have hv : valBits V ≤ w := Nat.clog_le_of_le_pow hV
    have hlt := wOffV_add_one_lt_compactedItemWords (U := U) (V := V) (N := N) hw hidx)
  all_goals try (dsimp only [CompVOffsetPre]; exact ⟨hw, rfl, hq, hv, by omega⟩)
  all_goals (dsimp only [WriteBitSlicePre]; exact ⟨hw, rfl, hv, bOffV_lt hw, by omega⟩)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

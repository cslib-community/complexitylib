/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Accessors

/-!
# Metadata and Circular-Window `Memory.Prog` Primitives

This module builds on `Accessors.lean` to provide `RealizesBounded .exact` (`¬ReadsWidth`)
`Memory.Prog` primitives for:
* dense item copy/clear (`copyCompItemGenProg`, `clearCompItemGenProg`);
* compacted metadata arrays (`readCompLMGenProg`, `writeCompLMGenProg`, `readCompGMGenProg`,
  `writeCompGMGenProg`, `readCompTDGenProg`, `writeCompTDGenProg`, `readCompDTGenProg`,
  `writeCompDTGenProg`);
* circular tail-to-dense window transitions (`denseOfCircGenProg`, `denseOfPhysGenProg`,
  `winGrowRightGenProg`, `winGrowLeftGenProg`, `winShrinkRightGenProg`, `winShrinkLeftGenProg`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.readCompLMGenProg`,
  `writeCompLMGenProg`, `readCompGMGenProg`, `writeCompGMGenProg`, `readCompTDGenProg`,
  `writeCompTDGenProg`, `readCompDTGenProg`, `writeCompDTGenProg`: metadata accessors.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.denseOfCircGenProg`,
  `denseOfPhysGenProg`, `winGrowRightGenProg`, `winGrowLeftGenProg`, `winShrinkRightGenProg`,
  `winShrinkLeftGenProg`: circular window `Memory.Prog` operations.

## Main results

* `realizesBounded_denseOfPhysGen`, `realizesBounded_winGrowRightGen`,
  `realizesBounded_winGrowLeftGen`, `realizesBounded_winShrinkRightGen`,
  `realizesBounded_winShrinkLeftGen`: parameter-free `RealizesBounded .exact` certificates.
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

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: Item Copy/Clear and Metadata Array Accessors -/

/-- Copy `(quot, val)` from dense slot `src` to `dst` at `itemBase`. -/
def copyCompItemGenProg : (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((cp, itemBase), (src, dst)) => do
    let q ← readCompQuotGenProg ((cp, itemBase), src)
    let v ← readCompValGenProg ((cp, itemBase), src)
    writeCompQuotGenProg (((cp, itemBase), dst), q)
    writeCompValGenProg (((cp, itemBase), dst), v)

@[simp] theorem clientResult_copyCompItemGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientResult s (copyCompItemGenProg d) = () := by
  rcases d with ⟨⟨cp, itemBase⟩, ⟨src, dst⟩⟩; simp [copyCompItemGenProg]
theorem clientState_copyCompItemGenProg {U V w N m_items itemBase src dst : ℕ}
    (hsrc : src < m_items) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (src, dst))) =
      { mem := writeCompVal itemBase U V w N
          (writeCompQuot itemBase U V w N s.mem dst (compQuotAt itemBase U V w N m_items s.mem src))
          dst (compValAt itemBase U V w N m_items s.mem src),
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState
  simp only [copyCompItemGenProg, prog_runClient_state_bind, StateTransitionSpec.clientState,
    clientResult_readCompQuotGenProg hsrc, runClient_state_readCompQuotGenProg,
    clientResult_readCompValGenProg hsrc, runClient_state_readCompValGenProg,
    runClient_state_writeCompQuotGenProg, runClient_state_writeCompValGenProg]
@[simp] theorem memoryCost_copyCompItemGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (copyCompItemGenProg d) s = 12 := by
  rcases d with ⟨⟨cp, itemBase⟩, ⟨src, dst⟩⟩; simp [copyCompItemGenProg]
/-- Precondition for copying an item between two compacted item slots. -/
@[expose] def CopyCompItemPre (w : ℕ) : (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, itemBase), (src, dst)), s =>
    ∃ m_items, CompItemEnv w cp itemBase m_items s ∧ src < m_items ∧ dst < m_items
theorem realizesBounded_copyCompItemGen :
    RealizesBounded .exact copyCompItemGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      CopyCompItemPre (fun _ _ => 0) := by
  have hrq := realizesBounded_readCompQuotGen
  have hrv := realizesBounded_readCompValGen
  have hwq := realizesBounded_writeCompQuotGen
  have hwv := realizesBounded_writeCompValGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, itemBase⟩, ⟨src, dst⟩⟩
    obtain ⟨m_items, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hsrc, hdst⟩ := h
    try simp only [StateTransitionSpec.clientState, runClient_state_readCompQuotGenProg,
      runClient_state_readCompValGenProg, runClient_state_writeCompQuotGenProg] at *)
  all_goals exact ⟨m_items, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by assumption⟩

/-- Clear `(quot, val)` to `(0, 0)` at dense index `d` before shrinking trailing words. -/
def clearCompItemGenProg : (CompParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, itemBase), d) => do
    let z ← pure 0
    writeCompQuotGenProg (((cp, itemBase), d), z)
    writeCompValGenProg (((cp, itemBase), d), z)

@[simp] theorem clientResult_clearCompItemGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (clearCompItemGenProg d) = () := by
  rcases d with ⟨⟨cp, itemBase⟩, idx⟩; simp [clearCompItemGenProg]

theorem clientState_clearCompItemGenProg (U V w N itemBase d : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (clearCompItemGenProg ((mkCompParams U V w N, itemBase), d)) =
      { mem := writeCompVal itemBase U V w N (writeCompQuot itemBase U V w N s.mem d 0) d 0,
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState
  simp [clearCompItemGenProg]

@[simp] theorem memoryCost_clearCompItemGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (clearCompItemGenProg d) s = 8 := by
  rcases d with ⟨⟨cp, itemBase⟩, idx⟩; simp [clearCompItemGenProg]

theorem realizesBounded_clearCompItemGen :
    RealizesBounded .exact clearCompItemGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      ReadCompQuotPre (fun _ _ => 0) := by
  have hwq := realizesBounded_writeCompQuotGen
  have hwv := realizesBounded_writeCompValGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, itemBase⟩, idx⟩
    obtain ⟨m_items, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hidx⟩ := h
    try simp only [StateTransitionSpec.clientState, runClient_state_writeCompQuotGenProg] at *)
  all_goals exact ⟨m_items, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hidx⟩

/-- Read `LocalMeta[c, idx]` at `metaBase` in `Memory.Prog`. -/
def readCompLMGenProg (c : Fin 9) : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), idx) => do
    let off ← pure (cpOffLMSub c cp)
    let k ← pure (cpLmBits cp)
    let wVal ← pure (cpW cp)
    readPackedCompGenProg (((metaBase, off), (k, wVal)), idx)

@[simp] theorem clientResult_readCompLMGenProg (c : Fin 9) {U V w N metaBase idx : ℕ}
    (hidx : idx < totalMicroBuckets N) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (readCompLMGenProg c ((mkCompParams U V w N, metaBase), idx)) =
      compLmAt metaBase U w N s.mem (c.val, idx) := by
  simp [readCompLMGenProg, cpOffLMSub_mk, compLmAt, c.isLt, hidx]

theorem clientState_readCompLMGenProg (c : Fin 9) (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readCompLMGenProg c d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, idx⟩; unfold StateTransitionSpec.clientState
  simp [readCompLMGenProg]
@[simp] theorem runClient_state_readCompLMGenProg
    (c : Fin 9) (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (readCompLMGenProg c d))) = s :=
  clientState_readCompLMGenProg c d s
@[simp] theorem memoryCost_readCompLMGenProg
    (c : Fin 9) (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readCompLMGenProg c d) s = 2 := by
  rcases d with ⟨⟨cp, metaBase⟩, idx⟩; simp [readCompLMGenProg]

/-- Precondition for reading from local metadata array `LM`. -/
@[expose] def CompLMPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), idx), s => CompMetaEnv w cp metaBase s ∧ idx < totalMicroBuckets (cpN cp)

theorem realizesBounded_readCompLMGen (c : Fin 9) :
    RealizesBounded .exact (readCompLMGenProg c)
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompLMPre (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  fin_cases c <;>
  · realize
    rcases d with ⟨⟨cp, metaBase⟩, idx⟩
    obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hidx⟩ := h
    simp only [cpOffLMSub_mk, cpLmBits_mk, cpW_mk, cpN_mk] at *
    refine ⟨totalMicroBuckets N, hw, rfl, effBucketPosBits_le_of_lt_pow hnU hU, hidx, ?_⟩
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLMSub offCompLM at *
    change _ + lmSubWords N w ≤ s.frontier
    omega

/-- Write `val` into `LocalMeta[c, idx]` at `metaBase` in `Memory.Prog`. -/
def writeCompLMGenProg (c : Fin 9) : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), idx), val) => do
    let off ← pure (cpOffLMSub c cp)
    let k ← pure (cpLmBits cp)
    let wVal ← pure (cpW cp)
    writePackedCompGenProg ((((metaBase, off), (k, wVal)), idx), val)

@[simp] theorem clientResult_writeCompLMGenProg
    (c : Fin 9) (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (writeCompLMGenProg c d) = () := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, idx⟩, val⟩; simp [writeCompLMGenProg]
theorem clientState_writeCompLMGenProg
    (c : Fin 9) (U V w N metaBase idx val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (writeCompLMGenProg c (((mkCompParams U V w N, metaBase), idx), val)) =
      { mem := writePacked (metaBase + offCompLMSub U w N c.val)
          (effBucketPosBits N) w s.mem idx val,
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState; simp [writeCompLMGenProg, cpOffLMSub_mk]
@[simp] theorem runClient_state_writeCompLMGenProg
    (c : Fin 9) (U V w N metaBase idx val : ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s
        (writeCompLMGenProg c (((mkCompParams U V w N, metaBase), idx), val)))) =
      { mem := writePacked (metaBase + offCompLMSub U w N c.val)
          (effBucketPosBits N) w s.mem idx val,
        frontier := s.frontier } :=
  clientState_writeCompLMGenProg c U V w N metaBase idx val s
@[simp] theorem memoryCost_writeCompLMGenProg
    (c : Fin 9) (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (writeCompLMGenProg c d) s = 4 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, idx⟩, val⟩; simp [writeCompLMGenProg]

/-- Precondition for writing to local metadata array `LM`. -/
@[expose] def WriteCompLMPre (w : ℕ) : ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), idx), _val), s =>
    CompMetaEnv w cp metaBase s ∧ idx < totalMicroBuckets (cpN cp)

theorem realizesBounded_writeCompLMGen (c : Fin 9) :
    RealizesBounded .exact (writeCompLMGenProg c)
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      WriteCompLMPre (fun _ _ => 0) := by
  have hwp := realizesBounded_writePackedCompGen
  fin_cases c <;>
  · realize
    rcases d with ⟨⟨⟨cp, metaBase⟩, idx⟩, val⟩
    obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hidx⟩ := h
    simp only [cpOffLMSub_mk, cpLmBits_mk, cpW_mk, cpN_mk] at *
    refine ⟨totalMicroBuckets N, hw, rfl, effBucketPosBits_le_of_lt_pow hnU hU, hidx, ?_⟩
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLMSub offCompLM at *
    change _ + lmSubWords N w ≤ s.frontier
    omega

/-- Read `GlobalMeta[idx]` at `metaBase` in `Memory.Prog`. -/
def readCompGMGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), idx) => do
    let off ← pure (cpOffGM cp)
    let k ← pure (cpGmBits cp)
    let wVal ← pure (cpW cp)
    readPackedCompGenProg (((metaBase, off), (k, wVal)), idx)

@[simp] theorem clientResult_readCompGMGenProg {U V w N metaBase idx : ℕ}
    (hidx : idx < globalMetaLen N) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (readCompGMGenProg ((mkCompParams U V w N, metaBase), idx)) =
      compGmAt metaBase U w N s.mem idx := by
  simp [readCompGMGenProg, compGmAt, hidx]

theorem clientState_readCompGMGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readCompGMGenProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, idx⟩; unfold StateTransitionSpec.clientState
  simp [readCompGMGenProg]
@[simp] theorem runClient_state_readCompGMGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (readCompGMGenProg d))) = s :=
  clientState_readCompGMGenProg d s
@[simp] theorem memoryCost_readCompGMGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readCompGMGenProg d) s = 2 := by
  rcases d with ⟨⟨cp, metaBase⟩, idx⟩; simp [readCompGMGenProg]

/-- Precondition for reading from global metadata array `GM`. -/
@[expose] def CompGMPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), idx), s => CompMetaEnv w cp metaBase s ∧ idx < globalMetaLen (cpN cp)

theorem realizesBounded_readCompGMGen :
    RealizesBounded .exact readCompGMGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompGMPre (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  realize
  rcases d with ⟨⟨cp, metaBase⟩, idx⟩
  obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hidx⟩ := h
  simp only [cpOffGM_mk, cpGmBits_mk, cpW_mk, cpN_mk] at *
  refine ⟨globalMetaLen N, hw, rfl, globalPtrBits_le_of_lt_pow hnU hU, hidx, ?_⟩
  unfold offCompItems offDenseToTail offTailToDense at *
  omega

/-- Write `val` into `GlobalMeta[idx]` at `metaBase` in `Memory.Prog`. -/
def writeCompGMGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), idx), val) => do
    let off ← pure (cpOffGM cp)
    let k ← pure (cpGmBits cp)
    let wVal ← pure (cpW cp)
    writePackedCompGenProg ((((metaBase, off), (k, wVal)), idx), val)

@[simp] theorem clientResult_writeCompGMGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (writeCompGMGenProg d) = () := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, idx⟩, val⟩; simp [writeCompGMGenProg]
theorem clientState_writeCompGMGenProg (U V w N metaBase idx val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (writeCompGMGenProg (((mkCompParams U V w N, metaBase), idx), val)) =
      { mem := writePacked (metaBase + offCompGM U w N) (globalPtrBits N) w s.mem idx val,
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState; simp [writeCompGMGenProg]
@[simp] theorem runClient_state_writeCompGMGenProg
    (U V w N metaBase idx val : ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s
        (writeCompGMGenProg (((mkCompParams U V w N, metaBase), idx), val)))) =
      { mem := writePacked (metaBase + offCompGM U w N) (globalPtrBits N) w s.mem idx val,
        frontier := s.frontier } :=
  clientState_writeCompGMGenProg U V w N metaBase idx val s
@[simp] theorem memoryCost_writeCompGMGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (writeCompGMGenProg d) s = 4 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, idx⟩, val⟩; simp [writeCompGMGenProg]

/-- Precondition for writing to global metadata array `GM`. -/
@[expose] def WriteCompGMPre (w : ℕ) : ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), idx), _val), s =>
    CompMetaEnv w cp metaBase s ∧ idx < globalMetaLen (cpN cp)

theorem realizesBounded_writeCompGMGen :
    RealizesBounded .exact writeCompGMGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      WriteCompGMPre (fun _ _ => 0) := by
  have hwp := realizesBounded_writePackedCompGen
  realize
  rcases d with ⟨⟨⟨cp, metaBase⟩, idx⟩, val⟩
  obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hidx⟩ := h
  simp only [cpOffGM_mk, cpGmBits_mk, cpW_mk, cpN_mk] at *
  refine ⟨globalMetaLen N, hw, rfl, globalPtrBits_le_of_lt_pow hnU hU, hidx, ?_⟩
  unfold offCompItems offDenseToTail offTailToDense at *
  omega

/-- Read `TailToDense[t]` at `metaBase` in `Memory.Prog`. -/
def readCompTDGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), t) => do
    let off ← pure (cpOffTD cp)
    let k ← pure (cpGmBits cp)
    let wVal ← pure (cpW cp)
    readPackedCompGenProg (((metaBase, off), (k, wVal)), t)

@[simp] theorem clientResult_readCompTDGenProg {U V w N metaBase t : ℕ}
    (ht : t < maxTailItems N) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (readCompTDGenProg ((mkCompParams U V w N, metaBase), t)) =
      compTDAt metaBase U w N s.mem t := by
  simp [readCompTDGenProg, compTDAt, ht]

theorem clientState_readCompTDGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readCompTDGenProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, t⟩; unfold StateTransitionSpec.clientState
  simp [readCompTDGenProg]
@[simp] theorem runClient_state_readCompTDGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (readCompTDGenProg d))) = s :=
  clientState_readCompTDGenProg d s
@[simp] theorem memoryCost_readCompTDGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readCompTDGenProg d) s = 2 := by
  rcases d with ⟨⟨cp, metaBase⟩, t⟩; simp [readCompTDGenProg]

/-- Precondition for reading from tail map `TailToDense`. -/
@[expose] def CompTailMapPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), idx), s => CompMetaEnv w cp metaBase s ∧ idx < cpMaxTail cp

theorem realizesBounded_readCompTDGen :
    RealizesBounded .exact readCompTDGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompTailMapPre (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  realize
  rcases d with ⟨⟨cp, metaBase⟩, t⟩
  obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ht⟩ := h
  simp only [cpOffTD_mk, cpGmBits_mk, cpW_mk, cpMaxTail_mk] at *
  refine ⟨maxTailItems N, hw, rfl, globalPtrBits_le_of_lt_pow hnU hU, ht, ?_⟩
  unfold offCompItems offDenseToTail at *
  omega

/-- Write `val` into `TailToDense[t]` at `metaBase` in `Memory.Prog`. -/
def writeCompTDGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), t), val) => do
    let off ← pure (cpOffTD cp)
    let k ← pure (cpGmBits cp)
    let wVal ← pure (cpW cp)
    writePackedCompGenProg ((((metaBase, off), (k, wVal)), t), val)

@[simp] theorem clientResult_writeCompTDGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (writeCompTDGenProg d) = () := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, t⟩, val⟩; simp [writeCompTDGenProg]
theorem clientState_writeCompTDGenProg (U V w N metaBase t val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (writeCompTDGenProg (((mkCompParams U V w N, metaBase), t), val)) =
      { mem := writePacked (metaBase + offTailToDense U w N) (globalPtrBits N) w s.mem t val,
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState; simp [writeCompTDGenProg]
@[simp] theorem runClient_state_writeCompTDGenProg
    (U V w N metaBase t val : ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s
        (writeCompTDGenProg (((mkCompParams U V w N, metaBase), t), val)))) =
      { mem := writePacked (metaBase + offTailToDense U w N) (globalPtrBits N) w s.mem t val,
        frontier := s.frontier } :=
  clientState_writeCompTDGenProg U V w N metaBase t val s
@[simp] theorem memoryCost_writeCompTDGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (writeCompTDGenProg d) s = 4 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, t⟩, val⟩; simp [writeCompTDGenProg]

/-- Precondition for writing to tail map `TailToDense`. -/
@[expose] def WriteCompTailMapPre (w : ℕ) : ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), idx), _val), s => CompMetaEnv w cp metaBase s ∧ idx < cpMaxTail cp

theorem realizesBounded_writeCompTDGen :
    RealizesBounded .exact writeCompTDGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      WriteCompTailMapPre (fun _ _ => 0) := by
  have hwp := realizesBounded_writePackedCompGen
  realize
  rcases d with ⟨⟨⟨cp, metaBase⟩, t⟩, val⟩
  obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ht⟩ := h
  simp only [cpOffTD_mk, cpGmBits_mk, cpW_mk, cpMaxTail_mk] at *
  refine ⟨maxTailItems N, hw, rfl, globalPtrBits_le_of_lt_pow hnU hU, ht, ?_⟩
  unfold offCompItems offDenseToTail at *
  omega

/-- Read `DenseToTail[r]` at `metaBase` in `Memory.Prog`. -/
def readCompDTGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), r) => do
    let off ← pure (cpOffDT cp)
    let k ← pure (cpGmBits cp)
    let wVal ← pure (cpW cp)
    readPackedCompGenProg (((metaBase, off), (k, wVal)), r)

@[simp] theorem clientResult_readCompDTGenProg {U V w N metaBase r : ℕ}
    (hr : r < maxTailItems N) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (readCompDTGenProg ((mkCompParams U V w N, metaBase), r)) =
      compDTAt metaBase U w N s.mem r := by
  simp [readCompDTGenProg, compDTAt, hr]

theorem clientState_readCompDTGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readCompDTGenProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, r⟩; unfold StateTransitionSpec.clientState
  simp [readCompDTGenProg]
@[simp] theorem runClient_state_readCompDTGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (readCompDTGenProg d))) = s :=
  clientState_readCompDTGenProg d s
@[simp] theorem memoryCost_readCompDTGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readCompDTGenProg d) s = 2 := by
  rcases d with ⟨⟨cp, metaBase⟩, r⟩; simp [readCompDTGenProg]

theorem realizesBounded_readCompDTGen :
    RealizesBounded .exact readCompDTGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompTailMapPre (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  realize
  rcases d with ⟨⟨cp, metaBase⟩, r⟩
  obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hr⟩ := h
  simp only [cpOffDT_mk, cpGmBits_mk, cpW_mk, cpMaxTail_mk] at *
  refine ⟨maxTailItems N, hw, rfl, globalPtrBits_le_of_lt_pow hnU hU, hr, ?_⟩
  unfold offCompItems at *
  omega

/-- Write `val` into `DenseToTail[r]` at `metaBase` in `Memory.Prog`. -/
def writeCompDTGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), r), val) => do
    let off ← pure (cpOffDT cp)
    let k ← pure (cpGmBits cp)
    let wVal ← pure (cpW cp)
    writePackedCompGenProg ((((metaBase, off), (k, wVal)), r), val)

@[simp] theorem clientResult_writeCompDTGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (writeCompDTGenProg d) = () := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, r⟩, val⟩; simp [writeCompDTGenProg]
theorem clientState_writeCompDTGenProg (U V w N metaBase r val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (writeCompDTGenProg (((mkCompParams U V w N, metaBase), r), val)) =
      { mem := writePacked (metaBase + offDenseToTail U w N) (globalPtrBits N) w s.mem r val,
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState; simp [writeCompDTGenProg]
@[simp] theorem runClient_state_writeCompDTGenProg
    (U V w N metaBase r val : ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s
        (writeCompDTGenProg (((mkCompParams U V w N, metaBase), r), val)))) =
      { mem := writePacked (metaBase + offDenseToTail U w N) (globalPtrBits N) w s.mem r val,
        frontier := s.frontier } :=
  clientState_writeCompDTGenProg U V w N metaBase r val s
@[simp] theorem memoryCost_writeCompDTGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (writeCompDTGenProg d) s = 4 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, r⟩, val⟩; simp [writeCompDTGenProg]

theorem realizesBounded_writeCompDTGen :
    RealizesBounded .exact writeCompDTGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      WriteCompTailMapPre (fun _ _ => 0) := by
  have hwp := realizesBounded_writePackedCompGen
  realize
  rcases d with ⟨⟨⟨cp, metaBase⟩, r⟩, val⟩
  obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hr⟩ := h
  simp only [cpOffDT_mk, cpGmBits_mk, cpW_mk, cpMaxTail_mk] at *
  refine ⟨maxTailItems N, hw, rfl, globalPtrBits_le_of_lt_pow hnU hU, hr, ?_⟩
  unfold offCompItems at *
  omega

/-! ## Section 2: Circular-Window Transitions, Owner-Bucket Recovery, and `fits_mkCompParams` -/

theorem maxTailItems_le_of_pos {N : ℕ} (hM : 0 < maxTailItems N) : maxTailItems N ≤ N := by
  have hb_pos : 0 < bucketBits N := by
    rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb
    · simp [maxTailItems, tailCapPerBucket, hb0] at hM
    · exact hb
  have h1 := gmSlabMetaBase_add_eq_globalMetaLen hb_pos
  have h2 := globalMetaLen_le_of_bucketBits_pos hb_pos
  unfold gmSlabMetaBase gmTailOwnerBase at h1
  omega

/-- Overflow-free evaluation of `denseOfCirc (cpMaxTail cp) b_win c` in `Memory.Prog`. -/
def denseOfCircGenProg : CompParams × (ℕ × ℕ) → Memory.Prog ℕ
  | (cp, (b_win, c)) => do
    let z ← pure 0
    if cpMaxTail cp = z then pure b_win
    else do
      let M ← pure (cpMaxTail cp)
      let rem ← pure (b_win % M)
      if c < rem then
        pure (b_win + (c + (M - rem)))
      else
        pure (b_win + (c - rem))

theorem clientResult_denseOfCircGenProg {U V w N b_win c : ℕ}
    (hc : 0 < maxTailItems N → c < maxTailItems N) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (denseOfCircGenProg (mkCompParams U V w N, (b_win, c))) =
      denseOfCirc (maxTailItems N) b_win c := by
  dsimp only [denseOfCircGenProg, denseOfCirc]
  simp only [pure_bind, cpMaxTail_mk]
  by_cases hM0 : maxTailItems N = 0
  · rw [ite_eq_left hM0, ite_eq_left hM0]; rfl
  · rw [ite_eq_right hM0, ite_eq_right hM0]
    have hM_pos : 0 < maxTailItems N := Nat.pos_of_ne_zero hM0
    have hc_lt : c < maxTailItems N := hc hM_pos
    have hrem_lt : b_win % maxTailItems N < maxTailItems N := Nat.mod_lt _ hM_pos
    by_cases hlt : c < b_win % maxTailItems N
    · rw [ite_eq_left hlt, prog_clientResult_pure]
      have heq : c + maxTailItems N - b_win % maxTailItems N =
          c + (maxTailItems N - b_win % maxTailItems N) := by omega
      rw [heq, Nat.mod_eq_of_lt (a := c + (maxTailItems N - b_win % maxTailItems N)) (by omega)]
    · rw [ite_eq_right hlt, prog_clientResult_pure]
      have heq : c + maxTailItems N - b_win % maxTailItems N =
          (c - b_win % maxTailItems N) + 1 * maxTailItems N := by omega
      rw [heq, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (a := c - b_win % maxTailItems N) (by omega)]

theorem clientState_denseOfCircGenProg (d : CompParams × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (denseOfCircGenProg d) = s := by
  rcases d with ⟨cp, ⟨b_win, c⟩⟩
  unfold StateTransitionSpec.clientState; dsimp only [denseOfCircGenProg]
  simp only [pure_bind]; split_ifs <;> rfl

@[simp] theorem runClient_state_denseOfCircGenProg
    (d : CompParams × (ℕ × ℕ)) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (denseOfCircGenProg d))) = s :=
  clientState_denseOfCircGenProg d s

@[simp] theorem memoryCost_denseOfCircGenProg (d : CompParams × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (denseOfCircGenProg d) s = 0 := by
  rcases d with ⟨cp, ⟨b_win, c⟩⟩
  dsimp only [denseOfCircGenProg]; simp only [pure_bind]; split_ifs <;> rfl

/-- Precondition for circular tail offset mapping `denseOfCirc`. -/
@[expose] def DenseOfCircPre (w : ℕ) : CompParams × (ℕ × ℕ) → Memory.State → Prop
  | (cp, (b_win, c)), _s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧ b_win ≤ N ∧
      (0 < maxTailItems N →
        c < maxTailItems N ∧ denseOfCirc (maxTailItems N) b_win c ≤ N)

theorem realizesBounded_denseOfCircGen :
    RealizesBounded .exact denseOfCircGenProg
      (WordEncoding.encode (α := CompParams × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      DenseOfCircPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨cp, ⟨b_win, c⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hbN, hM_cond⟩ := h
    simp only [cpMaxTail_mk] at *
    have hM_pos : 0 < maxTailItems N := by omega
    have hM_ne : maxTailItems N ≠ 0 := hM_pos.ne'
    obtain ⟨hc_lt, hd_le⟩ := hM_cond hM_pos
    have hMN : maxTailItems N ≤ N := maxTailItems_le_of_pos hM_pos
    have hrem_lt : b_win % maxTailItems N < maxTailItems N := Nat.mod_lt _ hM_pos
    unfold denseOfCirc at hd_le
    rw [ite_eq_right hM_ne] at hd_le)
  all_goals try omega
  · have heq : c + maxTailItems N - b_win % maxTailItems N =
        c + (maxTailItems N - b_win % maxTailItems N) := by omega
    rw [heq, Nat.mod_eq_of_lt (by omega)] at hd_le
    exact lt_of_le_of_lt (by omega) hU
  · have heq : c + maxTailItems N - b_win % maxTailItems N =
        (c - b_win % maxTailItems N) + 1 * maxTailItems N := by omega
    rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)] at hd_le
    exact lt_of_le_of_lt (by omega) hU

/-- Map physical slot `g < N` to dense index `denseOfPhys N gm td g` in `Memory.Prog`. -/
def denseOfPhysGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), g) => do
    let z ← pure 0
    if cpBucketBits cp = z then pure g
    else do
      let n_slabs ← readCompGMGenProg ((cp, metaBase), z)
      let b_tail ← pure (n_slabs * cpSlabSize cp)
      if g < b_tail then pure g
      else do
        let t ← pure (cpNSubOne cp - g)
        let c ← readCompTDGenProg ((cp, metaBase), t)
        denseOfCircGenProg (cp, (b_tail, c))

theorem clientResult_denseOfPhysGenProg {U V w N metaBase g : ℕ} {s : Memory.State}
    (ht_lt : 0 < bucketBits N → ¬(g < compGmAt metaBase U w N s.mem 0 * slabSize N) →
      N - 1 - g < maxTailItems N ∧
      compTDAt metaBase U w N s.mem (N - 1 - g) < maxTailItems N) :
    (Memory.spec 0).clientResult s
        (denseOfPhysGenProg ((mkCompParams U V w N, metaBase), g)) =
      denseOfPhys N (compGmAt metaBase U w N s.mem) (compTDAt metaBase U w N s.mem) g := by
  dsimp only [denseOfPhysGenProg, denseOfPhys, cpBucketBits_mk, cpSlabSize_mk, cpNSubOne_mk]
  simp only [pure_bind]
  by_cases hb0 : bucketBits N = 0
  · rw [ite_eq_left hb0, ite_eq_left hb0]; rfl
  · rw [ite_eq_right hb0, ite_eq_right hb0]
    have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    rw [prog_clientResult_bind, clientResult_readCompGMGenProg h0_lt,
      clientState_readCompGMGenProg]
    by_cases hg_lt : g < compGmAt metaBase U w N s.mem 0 * slabSize N
    · rw [ite_eq_left hg_lt, ite_eq_left hg_lt]; rfl
    · rw [ite_eq_right hg_lt, ite_eq_right hg_lt]
      obtain ⟨ht1, ht2⟩ := ht_lt hb_pos hg_lt
      rw [prog_clientResult_bind, clientResult_readCompTDGenProg ht1,
        clientState_readCompTDGenProg]
      exact clientResult_denseOfCircGenProg (fun _ => ht2) s

theorem clientState_denseOfPhysGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (denseOfPhysGenProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, g⟩
  unfold StateTransitionSpec.clientState; dsimp only [denseOfPhysGenProg]
  simp only [pure_bind]
  by_cases hb0 : cpBucketBits cp = 0
  · rw [ite_eq_left hb0]; rfl
  · rw [ite_eq_right hb0, prog_runClient_state_bind]
    simp only [StateTransitionSpec.clientState, runClient_state_readCompGMGenProg]
    split_ifs <;> simp

@[simp] theorem runClient_state_denseOfPhysGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (denseOfPhysGenProg d))) = s :=
  clientState_denseOfPhysGenProg d s

/-- Precondition for mapping physical slot index to dense index `denseOfPhys`. -/
@[expose] def DenseOfPhysPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), g), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧ g < N ∧
      (0 < bucketBits N →
        compGmAt metaBase U w N s.mem 0 * slabSize N ≤ N ∧
        (¬(g < compGmAt metaBase U w N s.mem 0 * slabSize N) →
          N - 1 - g < maxTailItems N ∧
          compTDAt metaBase U w N s.mem (N - 1 - g) < maxTailItems N ∧
          denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
            (compTDAt metaBase U w N s.mem (N - 1 - g)) ≤ N))

theorem realizesBounded_denseOfPhysGen :
    RealizesBounded .exact denseOfPhysGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      DenseOfPhysPre (fun _ _ => 0) := by
  have hgm := realizesBounded_readCompGMGen
  have htd := realizesBounded_readCompTDGen
  have hdoc := realizesBounded_denseOfCircGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, g⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hg_lt, hb_cond⟩ := h
    simp only [cpBucketBits_mk, cpSlabSize_mk, cpNSubOne_mk] at *
    have hb_pos : 0 < bucketBits N := by omega
    have h0_lt : 0 < globalMetaLen N := by unfold globalMetaLen; omega
    obtain ⟨hb_tail_le, htail_cond⟩ := hb_cond hb_pos
    try simp only [StateTransitionSpec.clientState, clientResult_readCompGMGenProg h0_lt,
      runClient_state_readCompGMGenProg] at *)
  all_goals try (dsimp only [CompGMPre]; exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, h0_lt⟩)
  all_goals try exact lt_of_le_of_lt (by omega) hU
  all_goals try omega
  all_goals (
    have hg_ge : ¬(g < compGmAt metaBase U w N s.mem 0 * slabSize N) := by omega
    obtain ⟨ht_lt, hc_lt, hd_le⟩ := htail_cond hg_ge
    try simp only [clientResult_readCompTDGenProg ht_lt, runClient_state_readCompTDGenProg] at *)
  · exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, ht_lt⟩
  · exact ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hb_tail_le, fun _ => ⟨hc_lt, hd_le⟩⟩

/-- Grow circular window `[b_win, b_win + n_win)` on the right by 1 (`winGrowRight`). -/
def winGrowRightGenProg : (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((cp, metaBase), (b_win, n_win)) => do
    let c ← pure ((b_win + n_win) % cpMaxTail cp)
    writeCompTDGenProg (((cp, metaBase), n_win), c)
    writeCompDTGenProg (((cp, metaBase), c), n_win)

@[simp] theorem memoryCost_winGrowRightGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (winGrowRightGenProg d) s = 8 := by
  rcases d with ⟨⟨cp, metaBase⟩, ⟨b_win, n_win⟩⟩; simp [winGrowRightGenProg]

/-- Precondition for growing the circular window on the right. -/
@[expose] def WinGrowRightPre (w : ℕ) : (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, metaBase), (b_win, n_win)), s =>
    CompMetaEnv w cp metaBase s ∧ n_win < cpMaxTail cp ∧ b_win + n_win ≤ cpN cp

theorem realizesBounded_winGrowRightGen :
    RealizesBounded .exact winGrowRightGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      WinGrowRightPre (fun _ _ => 0) := by
  have hwtd := realizesBounded_writeCompTDGen
  have hwdt := realizesBounded_writeCompDTGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, ⟨b_win, n_win⟩⟩
    obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hn_lt, hbn_le⟩ := h
    simp only [cpMaxTail_mk, cpN_mk, StateTransitionSpec.clientState,
      runClient_state_writeCompTDGenProg] at *
    have hM_pos : 0 < maxTailItems N := by omega)
  all_goals try omega
  all_goals try exact lt_of_le_of_lt (by omega) hU
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hn_lt⟩
  all_goals exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, Nat.mod_lt _ hM_pos⟩

theorem clientState_winGrowRightGenProg (U V w N metaBase b_win n_win : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (winGrowRightGenProg ((mkCompParams U V w N, metaBase), (b_win, n_win))) =
      { mem := writePacked (metaBase + offDenseToTail U w N) (globalPtrBits N) w
          (writePacked (metaBase + offTailToDense U w N) (globalPtrBits N) w s.mem n_win
            ((b_win + n_win) % maxTailItems N))
          ((b_win + n_win) % maxTailItems N) n_win,
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState; simp [winGrowRightGenProg]

/-- Grow circular window `[b_win + 1, b_win + 1 + n_win)` on the left by 1 (`winGrowLeft`). -/
def winGrowLeftGenProg : (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((cp, metaBase), (b_win, n_win)) => do
    let c ← pure (b_win % cpMaxTail cp)
    writeCompTDGenProg (((cp, metaBase), n_win), c)
    writeCompDTGenProg (((cp, metaBase), c), n_win)

@[simp] theorem memoryCost_winGrowLeftGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (winGrowLeftGenProg d) s = 8 := by
  rcases d with ⟨⟨cp, metaBase⟩, ⟨b_win, n_win⟩⟩; simp [winGrowLeftGenProg]

/-- Precondition for growing the circular window on the left. -/
@[expose] def WinGrowLeftPre (w : ℕ) : (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, metaBase), (b_win, n_win)), s =>
    CompMetaEnv w cp metaBase s ∧ n_win < cpMaxTail cp ∧ b_win ≤ cpN cp

theorem realizesBounded_winGrowLeftGen :
    RealizesBounded .exact winGrowLeftGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      WinGrowLeftPre (fun _ _ => 0) := by
  have hwtd := realizesBounded_writeCompTDGen
  have hwdt := realizesBounded_writeCompDTGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, ⟨b_win, n_win⟩⟩
    obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hn_lt, hb_le⟩ := h
    simp only [cpMaxTail_mk, cpN_mk, StateTransitionSpec.clientState,
      runClient_state_writeCompTDGenProg] at *
    have hM_pos : 0 < maxTailItems N := by omega)
  all_goals try omega
  all_goals try exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hn_lt⟩
  all_goals exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, Nat.mod_lt _ hM_pos⟩

theorem clientState_winGrowLeftGenProg (U V w N metaBase b_win n_win : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (winGrowLeftGenProg ((mkCompParams U V w N, metaBase), (b_win, n_win))) =
      { mem := writePacked (metaBase + offDenseToTail U w N) (globalPtrBits N) w
          (writePacked (metaBase + offTailToDense U w N) (globalPtrBits N) w s.mem n_win
            (b_win % maxTailItems N))
          (b_win % maxTailItems N) n_win,
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState; simp [winGrowLeftGenProg]

/-- Shrink circular window `[b_win, b_win + n_win + 1)` on the right by 1 (`winShrinkRight`). -/
def winShrinkRightGenProg : (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((cp, metaBase), (b_win, n_win)) => do
    let c_rem ← pure ((b_win + n_win) % cpMaxTail cp)
    let t_rem ← readCompDTGenProg ((cp, metaBase), c_rem)
    let c_last ← readCompTDGenProg ((cp, metaBase), n_win)
    writeCompTDGenProg (((cp, metaBase), t_rem), c_last)
    writeCompDTGenProg (((cp, metaBase), c_last), t_rem)

@[simp] theorem memoryCost_winShrinkRightGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (winShrinkRightGenProg d) s = 12 := by
  rcases d with ⟨⟨cp, metaBase⟩, ⟨b_win, n_win⟩⟩; simp [winShrinkRightGenProg]

/-- Precondition for shrinking the circular window on the right. -/
@[expose] def WinShrinkRightPre (w : ℕ) : (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, metaBase), (b_win, n_win)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      n_win < maxTailItems N ∧ b_win + n_win ≤ N ∧
      compDTAt metaBase U w N s.mem ((b_win + n_win) % maxTailItems N) < maxTailItems N ∧
      compTDAt metaBase U w N s.mem n_win < maxTailItems N

theorem realizesBounded_winShrinkRightGen :
    RealizesBounded .exact winShrinkRightGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      WinShrinkRightPre (fun _ _ => 0) := by
  have hrdt := realizesBounded_readCompDTGen
  have hrtd := realizesBounded_readCompTDGen
  have hwtd := realizesBounded_writeCompTDGen
  have hwdt := realizesBounded_writeCompDTGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, ⟨b_win, n_win⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hn_lt, hbn_le, hdt_lt, htd_lt⟩ := h
    have hM_pos : 0 < maxTailItems N := by omega
    have hcrem_lt : (b_win + n_win) % maxTailItems N < maxTailItems N := Nat.mod_lt _ hM_pos
    try simp only [cpMaxTail_mk, StateTransitionSpec.clientState,
      clientResult_readCompDTGenProg hcrem_lt, runClient_state_readCompDTGenProg,
      clientResult_readCompTDGenProg hn_lt, runClient_state_readCompTDGenProg,
      runClient_state_writeCompTDGenProg] at *)
  all_goals try omega
  all_goals try exact lt_of_le_of_lt (by omega) hU
  all_goals exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by assumption⟩

/-- Shrink circular window `[b_win, b_win + n_win + 1)` on the left by 1 (`winShrinkLeft`). -/
def winShrinkLeftGenProg : (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((cp, metaBase), (b_win, n_win)) => do
    let c_rem ← pure (b_win % cpMaxTail cp)
    let t_rem ← readCompDTGenProg ((cp, metaBase), c_rem)
    let c_last ← readCompTDGenProg ((cp, metaBase), n_win)
    writeCompTDGenProg (((cp, metaBase), t_rem), c_last)
    writeCompDTGenProg (((cp, metaBase), c_last), t_rem)

@[simp] theorem memoryCost_winShrinkLeftGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (winShrinkLeftGenProg d) s = 12 := by
  rcases d with ⟨⟨cp, metaBase⟩, ⟨b_win, n_win⟩⟩; simp [winShrinkLeftGenProg]

/-- Precondition for shrinking the circular window on the left. -/
@[expose] def WinShrinkLeftPre (w : ℕ) : (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, metaBase), (b_win, n_win)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      n_win < maxTailItems N ∧ b_win ≤ N ∧
      compDTAt metaBase U w N s.mem (b_win % maxTailItems N) < maxTailItems N ∧
      compTDAt metaBase U w N s.mem n_win < maxTailItems N

theorem realizesBounded_winShrinkLeftGen :
    RealizesBounded .exact winShrinkLeftGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      WinShrinkLeftPre (fun _ _ => 0) := by
  have hrdt := realizesBounded_readCompDTGen
  have hrtd := realizesBounded_readCompTDGen
  have hwtd := realizesBounded_writeCompTDGen
  have hwdt := realizesBounded_writeCompDTGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, metaBase⟩, ⟨b_win, n_win⟩⟩
    obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hn_lt, hb_le, hdt_lt, htd_lt⟩ := h
    have hM_pos : 0 < maxTailItems N := by omega
    have hcrem_lt : b_win % maxTailItems N < maxTailItems N := Nat.mod_lt _ hM_pos
    try simp only [cpMaxTail_mk, StateTransitionSpec.clientState,
      clientResult_readCompDTGenProg hcrem_lt, runClient_state_readCompDTGenProg,
      clientResult_readCompTDGenProg hn_lt, runClient_state_readCompTDGenProg,
      runClient_state_writeCompTDGenProg] at *)
  all_goals try omega
  all_goals exact ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, by assumption⟩

theorem clientState_winShrinkRightGenProg {U V w N metaBase b_win n_win : ℕ} {s : Memory.State}
    (hc : (b_win + n_win) % maxTailItems N < maxTailItems N) (hn : n_win < maxTailItems N) :
    (Memory.spec 0).clientState s
        (winShrinkRightGenProg ((mkCompParams U V w N, metaBase), (b_win, n_win))) =
      { mem := writePacked (metaBase + offDenseToTail U w N) (globalPtrBits N) w
          (writePacked (metaBase + offTailToDense U w N) (globalPtrBits N) w s.mem
            (compDTAt metaBase U w N s.mem ((b_win + n_win) % maxTailItems N))
            (compTDAt metaBase U w N s.mem n_win))
          (compTDAt metaBase U w N s.mem n_win)
          (compDTAt metaBase U w N s.mem ((b_win + n_win) % maxTailItems N)),
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState
  simp [winShrinkRightGenProg, hc, hn]

theorem clientState_winShrinkLeftGenProg {U V w N metaBase b_win n_win : ℕ} {s : Memory.State}
    (hc : b_win % maxTailItems N < maxTailItems N) (hn : n_win < maxTailItems N) :
    (Memory.spec 0).clientState s
        (winShrinkLeftGenProg ((mkCompParams U V w N, metaBase), (b_win, n_win))) =
      { mem := writePacked (metaBase + offDenseToTail U w N) (globalPtrBits N) w
          (writePacked (metaBase + offTailToDense U w N) (globalPtrBits N) w s.mem
            (compDTAt metaBase U w N s.mem (b_win % maxTailItems N))
            (compTDAt metaBase U w N s.mem n_win))
          (compTDAt metaBase U w N s.mem n_win)
          (compDTAt metaBase U w N s.mem (b_win % maxTailItems N)),
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState
  simp [winShrinkLeftGenProg, hc, hn]

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

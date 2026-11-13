/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveCountingRoot
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveLeafLayout
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CountingTerminalPrepare
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CountingTerminalDispatch

/-!
# Shared physical storage for a counting terminal

The left block holds the actual carry-save root configuration. The right block holds short routing
metadata, a terminal request and the preparation machine's private work tapes. Preparing a request
preserves the entire root block. Copying its component index changes only the root-index word.
-/

public section

namespace Turing.MultiTapeATM.CountingTerminalLayout

open MultiTapeTM Cslib.Circuits.Boolean.CarryLookahead.Query

/-- The combined root and terminal-preparation tape count. -/
abbrev size (k r : ℕ) : ℕ := (k + 12) + (r + 1 + 2)

/-- The carry-save evaluator occupies the left block. -/
abbrev rootTapes (k r : ℕ) : Fin (k + 12) ↪ Fin (size k r) := Fin.castAddEmb (r + 1 + 2)

/-- Terminal preparation occupies the right block. -/
abbrev prepTapes (k r : ℕ) : Fin (r + 1 + 2) ↪ Fin (size k r) := Fin.natAddEmb (k + 12)

/-- The root's binary bit-index tape. -/
abbrev rootIndex (k r : ℕ) : Fin (size k r) := rootTapes k r ⟨1, by omega⟩

/-- The separate request word, containing flags followed by a component index. -/
abbrev flags (k r : ℕ) : Fin (size k r) := prepTapes k r (CountingTerminalPrepare.flags r)

/-- The preserved routing-position metadata. -/
abbrev metadata (k r : ℕ) : Fin (size k r) :=
  prepTapes k r (CountingTerminalPrepare.metadata r)

/-- Initial root storage beside the current metadata and terminal request. The bit index starts
at zero; the native dispatch copy installs the queried index later. -/
@[expose] def storage (k r : ℕ) (input context : List Bool) (n w : ℕ)
    (p : Routing.Position) (request : List Bool) : Cfg (size k r) Bool Unit input :=
  let root := CarrySaveCountingRoot.initial k input context n w 0
  let prep := CountingTerminalPrepare.config r input p request
  ⟨none, 0, Fin.append root.workTapes prep.workTapes,
    Fin.append root.workTapePos prep.workTapePos, []⟩

/-- Viewing the right block recovers the actual terminal-preparation configuration. -/
@[simp] theorem view_prep (k r : ℕ) (input context : List Bool) (n w : ℕ)
    (p : Routing.Position) (request : List Bool) :
    viewCfg (prepTapes k r) (storage k r input context n w p request) =
      CountingTerminalPrepare.config r input p request := by
  apply Cfg.ext <;> try rfl
  · funext j
    exact Fin.append_right _ _ j
  · funext j
    exact Fin.append_right _ _ j

/-- Viewing the left block recovers the original root configuration before its index is filled. -/
@[simp] theorem view_root (k r : ℕ) (input context : List Bool) (n w : ℕ)
    (p : Routing.Position) (request : List Bool) :
    viewCfg (rootTapes k r) (storage k r input context n w p request) =
      CarrySaveCountingRoot.initial k input context n w 0 := by
  apply Cfg.ext
  · simp [viewCfg, storage, CarrySaveCountingRoot.initial, CarrySaveLeaf.initial]
  · simp [viewCfg, storage, CarrySaveCountingRoot.initial, CarrySaveLeaf.initial]
  · funext j
    exact Fin.append_left _ _ j
  · funext j
    exact Fin.append_left _ _ j
  · simp [viewCfg, storage, CarrySaveCountingRoot.initial, CarrySaveLeaf.initial]

/-- Source flags and root index occupy disjoint blocks. -/
theorem flags_ne_rootIndex (k r : ℕ) : flags k r ≠ rootIndex k r :=
  (Fin.castAdd_ne_natAdd _ _).symm

/-- The request tape is exactly the prepared request word. -/
@[simp] theorem storage_flags (k r : ℕ) (input context : List Bool) (n w : ℕ)
    (p : Routing.Position) (request : List Bool) :
    (storage k r input context n w p request).workTapes (flags k r) = tapeOfList request := by
  funext z
  simp [storage, flags, prepTapes, CountingTerminalPrepare.config,
    CountingTerminalPrepare.words, tapesCfg]

/-- The routing metadata is retained independently of the prepared request word. -/
@[simp] theorem storage_metadata (k r : ℕ) (input context : List Bool) (n w : ℕ)
    (p : Routing.Position) (request : List Bool) :
    (storage k r input context n w p request).workTapes (metadata k r) =
      tapeOfList (Routing.encPosition p) := by
  have hne : CountingTerminalPrepare.metadata r ≠ CountingTerminalPrepare.flags r :=
    (Fin.castAdd_ne_natAdd _ _).symm
  funext z
  simp [storage, metadata, prepTapes, CountingTerminalPrepare.config,
    CountingTerminalPrepare.words, tapesCfg, hne]

/-- Replacing the routing metadata changes no root tape, request word, head or output. -/
theorem storage_update_metadata (k r : ℕ) (input context : List Bool) (n w : ℕ)
    (p p' : Routing.Position) (request : List Bool) :
    { storage k r input context n w p request with
      workTapes := Function.update (storage k r input context n w p request).workTapes
        (metadata k r) (tapeOfList (Routing.encPosition p')) } =
      storage k r input context n w p' request := by
  apply Cfg.ext <;> try rfl
  funext j
  change Function.update (storage k r input context n w p request).workTapes (metadata k r)
    (tapeOfList (Routing.encPosition p')) j =
      (storage k r input context n w p' request).workTapes j
  simp only [metadata, prepTapes, Fin.natAddEmb_apply]
  cases j using Fin.addCases with
  | left j =>
    rw [Function.update_of_ne (Fin.castAdd_ne_natAdd j _)]
    simp [storage]
  | right j =>
    by_cases hm : j = CountingTerminalPrepare.metadata r
    · subst j
      rw [Function.update_self]
      exact (storage_metadata k r input context n w p' request).symm
    · have hne : Fin.natAdd (k + 12) j ≠
          Fin.natAdd (k + 12) (CountingTerminalPrepare.metadata r) :=
        (Fin.natAddEmb (k + 12)).injective.ne hm
      rw [Function.update_of_ne hne]
      funext z
      by_cases hf : j = CountingTerminalPrepare.flags r
      · subst j
        simp [storage, CountingTerminalPrepare.config, CountingTerminalPrepare.words, tapesCfg]
      · simp [storage, CountingTerminalPrepare.config, CountingTerminalPrepare.words,
          tapesCfg, Function.update_of_ne hf, Function.update_of_ne hm]

/-- The flag reader starts on the first request cell. -/
@[simp] theorem storage_flags_head (k r : ℕ) (input context : List Bool) (n w : ℕ)
    (p : Routing.Position) (request : List Bool) :
    (storage k r input context n w p request).workTapePos (flags k r) = 0 := by
  simp [storage, flags, prepTapes, CountingTerminalPrepare.config, tapesCfg]

/-- Binary zero leaves the root-index tape blank before dispatch copies a query into it. -/
@[simp] theorem storage_rootIndex (k r : ℕ) (input context : List Bool) (n w : ℕ)
    (p : Routing.Position) (request : List Bool) :
    (storage k r input context n w p request).workTapes (rootIndex k r) = tapeOfList [] := by
  change (viewCfg (rootTapes k r) (storage k r input context n w p request)).workTapes
    (CarrySaveStream.coreEmb (k + 6) 1) = _
  rw [view_root]
  simp [CarrySaveCountingRoot.initial, CarrySaveLeaf.initial]

/-- The receiving root-index head is at its origin. -/
@[simp] theorem storage_rootIndex_head (k r : ℕ) (input context : List Bool) (n w : ℕ)
    (p : Routing.Position) (request : List Bool) :
    (storage k r input context n w p request).workTapePos (rootIndex k r) = 0 := by
  change (viewCfg (rootTapes k r) (storage k r input context n w p request)).workTapePos
    (CarrySaveStream.coreEmb (k + 6) 1) = _
  rw [view_root]
  simp [CarrySaveCountingRoot.initial, CarrySaveLeaf.initial]

/-- The host input remains parked at its left blank. -/
@[simp] theorem storage_inputPos (k r : ℕ) (input context : List Bool) (n w : ℕ)
    (p : Routing.Position) (request : List Bool) :
    (storage k r input context n w p request).inputPos = 0 := rfl

/-- Preparing and dispatching a terminal starts with an empty append-only output. -/
@[simp] theorem storage_output (k r : ℕ) (input context : List Bool) (n w : ℕ)
    (p : Routing.Position) (request : List Bool) :
    (storage k r input context n w p request).output = [] := rfl

/-- Copying a requested binary index produces exactly the root evaluator's initial storage on
its own tapes. The terminal metadata and the consumed request cursor remain outside that view. -/
theorem view_root_copied (k r : ℕ) (input context : List Bool) (n w : ℕ)
    (p : Routing.Position) (request : List Bool) (i : ℕ) :
    viewCfg (rootTapes k r)
      (CountingTerminalDispatch.copied (flags k r) (rootIndex k r) (encNat i)
        (storage k r input context n w p request)) =
      CarrySaveCountingRoot.initial k input context n w i := by
  apply Cfg.ext
  · simp [viewCfg, CountingTerminalDispatch.copied, Cfg.withState,
      CarrySaveCountingRoot.initial, CarrySaveLeaf.initial]
  · simp [viewCfg, CountingTerminalDispatch.copied, Cfg.withState, storage,
      CarrySaveCountingRoot.initial, CarrySaveLeaf.initial]
  · funext j
    change Function.update
      (Fin.append (CarrySaveCountingRoot.initial k input context n w 0).workTapes
        (CountingTerminalPrepare.config r input p request).workTapes)
      (rootTapes k r 1) (tapeOfList (encNat i)) (rootTapes k r j) = _
    by_cases hj : j = 1
    · subst j
      rw [Function.update_self]
      simp [CarrySaveCountingRoot.initial, CarrySaveLeafLayout.initial_tape,
        CarrySaveLeafLayout.words]
    · rw [Function.update_of_ne ((rootTapes k r).injective.ne hj)]
      simp only [rootTapes, Fin.castAddEmb_apply, Fin.append_left,
        CarrySaveCountingRoot.initial, CarrySaveLeafLayout.initial_tape]
      have hw := congrFun (CarrySaveLeafLayout.words_update_bits k context (encNat n)
        (encNat w) (encNat (Nat.clog 2 n)) (encNat 0) [] (encUnary (Nat.clog 2 n))
        (encNat i) false) j
      rw [Function.update_of_ne hj] at hw
      exact congrArg tapeOfList hw
  · funext j
    change Function.update
      (Function.update
        (Fin.append (CarrySaveCountingRoot.initial k input context n w 0).workTapePos
          (CountingTerminalPrepare.config r input p request).workTapePos)
        (flags k r) (3 + (encNat i).length : ℕ)) (rootIndex k r) 0 (rootTapes k r j) = _
    have hjf : rootTapes k r j ≠ flags k r := Fin.castAdd_ne_natAdd _ _
    by_cases hjr : rootTapes k r j = rootIndex k r
    · rw [hjr, Function.update_self]
      simp [CarrySaveCountingRoot.initial, CarrySaveLeafLayout.initial_nil_eq_tapesCfg, tapesCfg]
    · rw [Function.update_of_ne hjr, Function.update_of_ne hjf]
      simp [CarrySaveCountingRoot.initial, CarrySaveLeafLayout.initial_nil_eq_tapesCfg, tapesCfg]
  · simp [viewCfg, CountingTerminalDispatch.copied, Cfg.withState, storage,
      CarrySaveCountingRoot.initial, CarrySaveLeaf.initial]

/-- A native preparation run extends to the combined storage without changing any root tape. -/
theorem run_prepare {r : ℕ} {S : Type} (tm : MultiTapeTM (r + 1 + 2) Bool S)
    (k : ℕ) (input context : List Bool) (n w : ℕ) (p : Routing.Position)
    (request : List Bool) (t : ℕ)
    (h : tm.runFrom ((CountingTerminalPrepare.config r input p []).withState (some tm.q₀)) t =
      (CountingTerminalPrepare.config r input p request).withState none) :
    (tm.extendTapes (prepTapes k r)).runFrom
      ((storage k r input context n w p []).withState
        (some (tm.extendTapes (prepTapes k r)).q₀)) t =
      (storage k r input context n w p request).withState none := by
  rw [runFrom_extendTapes]
  have hv : viewCfg (prepTapes k r)
      ((storage k r input context n w p []).withState (some tm.q₀)) =
      (CountingTerminalPrepare.config r input p []).withState (some tm.q₀) := by
    exact congrArg (fun c => c.withState (some tm.q₀)) (view_prep k r input context n w p [])
  rw [extendTapes_q₀, hv, h, embed_natAdd]
  apply Cfg.ext <;> try rfl
  · funext j
    induction j using Fin.addCases with
    | left j => simp [storage, Cfg.withState]
    | right j => simp [storage, Cfg.withState]
  · funext j
    induction j using Fin.addCases with
    | left j => simp [storage, Cfg.withState]
    | right j => simp [storage, Cfg.withState]

end Turing.MultiTapeATM.CountingTerminalLayout

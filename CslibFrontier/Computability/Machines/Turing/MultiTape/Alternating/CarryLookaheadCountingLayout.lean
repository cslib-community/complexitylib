/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.WordGameLeaf
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CountingTerminalLayout
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ExtendTapes
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordGameRoundTime
import Mathlib.Tactic.FinCases

/-!
# Shared tapes for finishing-adder rounds and the counting terminal

The terminal occupies the left block and native routing rounds use a separate right block. Their
metadata tape is shared: the round's metadata coordinate points into the terminal block, while its
unused right-block slot stays blank. Every other terminal tape, including the predicate context,
survives each round unchanged. The controller header occupies a separate right-block tape.
-/

public section

namespace Turing.MultiTapeATM.CarryLookaheadCountingLayout

open MultiTapeTM Cslib.Circuits.Boolean.CarryLookahead.Query

/-- Counting-terminal tapes followed by the routing round's scratch and four named tapes. -/
abbrev size (k r q : ℕ) : ℕ := CountingTerminalLayout.size k r + (q + 4)

/-- The complete counting terminal occupies the left block. -/
abbrev terminalEmbedding (k r q : ℕ) :
    Fin (CountingTerminalLayout.size k r) ↪ Fin (size k r q) := Fin.castAddEmb (q + 4)

/-- The round-local controller-header coordinate. -/
abbrev roundControl (q : ℕ) : Fin (q + 4) := Fin.natAdd q 0

/-- The round-local coordinate redirected to shared metadata. -/
abbrev roundMetadata (q : ℕ) : Fin (q + 4) := Fin.natAdd q 1

/-- The controller header is the round's control tape in the right block. -/
abbrev control (k r q : ℕ) : Fin (size k r q) :=
  Fin.natAdd (CountingTerminalLayout.size k r) (roundControl q)

/-- Both the round and terminal use the same physical routing metadata tape. -/
abbrev metadata (k r q : ℕ) : Fin (size k r q) :=
  terminalEmbedding k r q (CountingTerminalLayout.metadata k r)

/-- Routing scratch stays in the right block; its metadata coordinate shares the terminal tape. -/
@[expose] def roundEmbedding (k r q : ℕ) : Fin (q + 4) ↪ Fin (size k r q) where
  toFun i := if i = roundMetadata q then metadata k r q
    else Fin.natAdd (CountingTerminalLayout.size k r) i
  inj' := by
    intro i j h
    by_cases hi : i = roundMetadata q <;> by_cases hj : j = roundMetadata q
    · exact hi.trans hj.symm
    · simp only [hi, hj, ↓reduceIte] at h
      exact (Fin.castAdd_ne_natAdd _ _ h).elim
    · simp only [hi, hj, ↓reduceIte] at h
      exact (Fin.castAdd_ne_natAdd _ _ h.symm).elim
    · simp only [hi, hj, ↓reduceIte] at h
      exact (Fin.natAddEmb _).injective h

/-- The round's metadata coordinate points into the counting terminal. -/
@[simp] theorem roundEmbedding_metadata (k r q : ℕ) :
    roundEmbedding k r q (roundMetadata q) = metadata k r q := by
  simp [roundEmbedding]

/-- Every other routing coordinate remains in the right block. -/
theorem roundEmbedding_other (k r q : ℕ) (i : Fin (q + 4)) (hi : i ≠ roundMetadata q) :
    roundEmbedding k r q i = Fin.natAdd (CountingTerminalLayout.size k r) i := by
  simp [roundEmbedding, hi]

/-- The native round and alternating controller share precisely this control tape. -/
@[simp] theorem roundEmbedding_control (k r q : ℕ) :
    roundEmbedding k r q (roundControl q) = control k r q := by
  simp [roundEmbedding, roundControl, roundMetadata, control]

/-- Installing a controller header never overwrites a terminal tape. -/
theorem control_ne_terminal (k r q : ℕ) (i : Fin (CountingTerminalLayout.size k r)) :
    control k r q ≠ terminalEmbedding k r q i := (Fin.castAdd_ne_natAdd _ _).symm

/-- The terminal and routing blocks before installing the live controller header. -/
@[expose] def storage (k r q : ℕ) (input context : List Bool) (n w : ℕ)
    (p : Routing.Position) : Cfg (size k r q) Bool Unit input :=
  let terminal := CountingTerminalLayout.storage k r input context n w p []
  let round := WordGameRound.config q input [] [] []
  ⟨none, 0, Fin.append terminal.workTapes round.workTapes,
    Fin.append terminal.workTapePos round.workTapePos, []⟩

/-- Canonical controller storage with a header and its head at the origin. -/
@[expose] def config (k r q : ℕ) (input context : List Bool) (n w : ℕ)
    (p : Routing.Position) {S : Type} (state : Option S) (header : List Bool) :
    Cfg (size k r q) Bool S input :=
  WordGameLeaf.config (control k r q) state header 0 (storage k r q input context n w p)

/-- The terminal sees its exact stored configuration, independent of the controller header. -/
theorem view_terminal_config (k r q : ℕ) (input context : List Bool) (n w : ℕ)
    (p : Routing.Position) {S : Type} (state : Option S) (header : List Bool) :
    viewCfg (terminalEmbedding k r q) (config k r q input context n w p state header) =
      (CountingTerminalLayout.storage k r input context n w p []).withState state := by
  apply Cfg.ext <;> try rfl
  · funext i
    change Function.update (storage k r q input context n w p).workTapes (control k r q)
      (tapeOfList header) (terminalEmbedding k r q i) = _
    rw [Function.update_of_ne (control_ne_terminal k r q i).symm]
    exact Fin.append_left _ _ i
  · funext i
    change Function.update (storage k r q input context n w p).workTapePos (control k r q)
      0 (terminalEmbedding k r q i) = _
    rw [Function.update_of_ne (control_ne_terminal k r q i).symm]
    exact Fin.append_left _ _ i

private theorem tapeWords_other (q : ℕ) (header metadata : List Bool) (i : Fin (q + 4))
    (hc : i ≠ roundControl q) (hm : i ≠ roundMetadata q) :
    WordGameRound.tapeWords q header metadata [] i = [] := by
  cases i using Fin.addCases with
  | left i => simp [WordGameRound.tapeWords]
  | right i => fin_cases i <;> simp_all [WordGameRound.tapeWords, roundControl, roundMetadata]

private theorem round_config_metadata (q : ℕ) (input header data out : List Bool) :
    (WordGameRound.config q input header data out).workTapes (roundMetadata q) =
      tapeOfList data := by
  funext z
  simp [WordGameRound.config, WordGameRound.queryConfig, WordGameRound.tapeWords,
    tapesCfg, roundMetadata]

private theorem round_config_control (q : ℕ) (input header data out : List Bool) :
    (WordGameRound.config q input header data out).workTapes (roundControl q) =
      tapeOfList header := by
  funext z
  simp [WordGameRound.config, WordGameRound.queryConfig, WordGameRound.tapeWords,
    tapesCfg, roundControl]

/-- The round sees its actual header and the shared metadata, with every work head at zero. -/
theorem view_round_config (k r q : ℕ) (input context : List Bool) (n w : ℕ)
    (p : Routing.Position) {S : Type} (state : Option S) (header : List Bool) :
    viewCfg (roundEmbedding k r q) (config k r q input context n w p state header) =
      (WordGameRound.config q input header (Routing.encPosition p) []).withState state := by
  apply Cfg.ext <;> try rfl
  · funext i
    change (config k r q input context n w p state header).workTapes (roundEmbedding k r q i) =
      (WordGameRound.config q input header (Routing.encPosition p) []).workTapes i
    by_cases hm : i = roundMetadata q
    · subst i
      rw [roundEmbedding_metadata, round_config_metadata]
      exact (congrArg (fun c => c.workTapes (CountingTerminalLayout.metadata k r))
        (view_terminal_config k r q input context n w p state header)).trans
          (CountingTerminalLayout.storage_metadata k r input context n w p [])
    · rw [roundEmbedding_other k r q i hm]
      by_cases hc : i = roundControl q
      · subst i
        rw [round_config_control]
        exact Function.update_self _ _ _
      · have hne : Fin.natAdd (CountingTerminalLayout.size k r) i ≠ control k r q :=
          (Fin.natAddEmb _).injective.ne hc
        change Function.update (storage k r q input context n w p).workTapes (control k r q)
          (tapeOfList header) (Fin.natAdd (CountingTerminalLayout.size k r) i) = _
        rw [Function.update_of_ne hne]
        simp only [storage, Fin.append_right, WordGameRound.config, WordGameRound.queryConfig,
          tapesCfg, tapeWords_other q _ _ i hc hm]
  · funext i
    change (config k r q input context n w p state header).workTapePos
      (roundEmbedding k r q i) = 0
    by_cases hm : i = roundMetadata q
    · subst i
      rw [roundEmbedding_metadata]
      have hv := congrArg (fun c => c.workTapePos (CountingTerminalLayout.metadata k r))
        (view_terminal_config k r q input context n w p state header)
      refine hv.trans ?_
      simp [Cfg.withState, CountingTerminalLayout.storage, CountingTerminalLayout.metadata,
        CountingTerminalPrepare.config, tapesCfg]
    · rw [roundEmbedding_other k r q i hm]
      by_cases hc : i = roundControl q
      · subst i
        exact Function.update_self _ _ _
      · have hne : Fin.natAdd (CountingTerminalLayout.size k r) i ≠ control k r q :=
          (Fin.natAddEmb _).injective.ne hc
        change Function.update (storage k r q input context n w p).workTapePos (control k r q)
          0 (Fin.natAdd (CountingTerminalLayout.size k r) i) = 0
        rw [Function.update_of_ne hne]
        exact Fin.append_right _ _ i

private theorem storage_tape_eq (k r q : ℕ) (input context : List Bool) (n w : ℕ)
    (p p' : Routing.Position) (i : Fin (size k r q)) (hi : i ≠ metadata k r q) :
    (storage k r q input context n w p).workTapes i =
      (storage k r q input context n w p').workTapes i := by
  cases i using Fin.addCases with
  | left i =>
    have hm : i ≠ CountingTerminalLayout.metadata k r :=
      fun h => hi (congrArg (terminalEmbedding k r q) h)
    have hu := congrArg (fun c => c.workTapes i)
      (CountingTerminalLayout.storage_update_metadata k r input context n w p p' [])
    simpa only [storage, Fin.append_left, Function.update_of_ne hm] using hu
  | right i => simp only [storage, Fin.append_right]

private theorem storage_heads_eq (k r q : ℕ) (input context : List Bool) (n w : ℕ)
    (p p' : Routing.Position) :
    (storage k r q input context n w p).workTapePos =
      (storage k r q input context n w p').workTapePos := by
  funext i
  cases i using Fin.addCases with
  | left i =>
    simpa only [storage, Fin.append_left] using congrArg (fun c => c.workTapePos i)
      (CountingTerminalLayout.storage_update_metadata k r input context n w p p' [])
  | right i => simp only [storage, Fin.append_right]

private theorem config_tape_eq (k r q : ℕ) (input context : List Bool) (n w : ℕ)
    (p p' : Routing.Position) {S : Type} (state state' : Option S) (header header' : List Bool)
    (i : Fin (size k r q)) (hc : i ≠ control k r q) (hm : i ≠ metadata k r q) :
    (config k r q input context n w p state header).workTapes i =
      (config k r q input context n w p' state' header').workTapes i := by
  simpa only [config, WordGameLeaf.config, Function.update_of_ne hc] using
    storage_tape_eq k r q input context n w p p' i hm

private theorem config_heads_eq (k r q : ℕ) (input context : List Bool) (n w : ℕ)
    (p p' : Routing.Position) {S : Type} (state state' : Option S) (header header' : List Bool) :
    (config k r q input context n w p state header).workTapePos =
      (config k r q input context n w p' state' header').workTapePos :=
  congrArg (fun heads => Function.update heads (control k r q) 0)
    (storage_heads_eq k r q input context n w p p')

private theorem embed_round_config (k r q : ℕ) (input context : List Bool) (n w : ℕ)
    (p p' : Routing.Position) {S : Type} (state : Option S) (header header' : List Bool) :
    embed (roundEmbedding k r q)
      ((WordGameRound.config q input header' (Routing.encPosition p') []).withState
        (none : Option S))
      (config k r q input context n w p state header).workTapes
      (config k r q input context n w p state header).workTapePos =
      config k r q input context n w p' none header' := by
  rw [← view_round_config k r q input context n w p' (none : Option S) header']
  apply Cfg.ext <;> try rfl
  · funext i
    cases hi : partialInv (roundEmbedding k r q) i with
    | some j =>
      simp only [embed, viewCfg, hi]
      rw [partialInv_eq_some _ hi]
    | none =>
      have hn (j : Fin (q + 4)) : i ≠ roundEmbedding k r q j := by
        intro he
        rw [he, partialInv_embed] at hi
        contradiction
      have hc : i ≠ control k r q :=
        by simpa only [roundEmbedding_control] using hn (roundControl q)
      have hm : i ≠ metadata k r q :=
        by simpa only [roundEmbedding_metadata] using hn (roundMetadata q)
      simp only [embed, hi]
      exact config_tape_eq k r q input context n w p p' state none header header' i hc hm
  · funext i
    cases hi : partialInv (roundEmbedding k r q) i with
    | some j =>
      simp only [embed, viewCfg, hi]
      rw [partialInv_eq_some _ hi]
    | none =>
      simp only [embed, hi]
      exact congrFun (config_heads_eq k r q input context n w p p' state none header header') i

/-- A concrete routing round runs on the shared metadata without changing any other terminal
storage. Its local run time is unchanged by the tape embedding. -/
theorem run_round {q : ℕ} {S : Type} (tm : MultiTapeTM (q + 4) Bool S) (k r : ℕ)
    (input context : List Bool) (n w : ℕ) (p p' : Routing.Position)
    (header header' : List Bool) (t : ℕ)
    (h : tm.runFrom ((WordGameRound.config q input header (Routing.encPosition p) []).withState
          (some tm.q₀)) t =
        (WordGameRound.config q input header' (Routing.encPosition p') []).withState none) :
    (tm.extendTapes (roundEmbedding k r q)).runFrom
      (config k r q input context n w p (some (tm.extendTapes (roundEmbedding k r q)).q₀)
        header) t =
      config k r q input context n w p' none header' := by
  rw [runFrom_extendTapes, extendTapes_q₀, view_round_config, h]
  exact embed_round_config k r q input context n w p p' (some tm.q₀) header header'

/-- The embedded alternating terminal has exactly its original all-branch clock. -/
theorem haltsWithin_terminal_iff {k r : ℕ} {S : Type}
    (atm : MultiTapeATM (CountingTerminalLayout.size k r) Bool S) (q : ℕ)
    (input context : List Bool) (n w : ℕ) (p : Routing.Position) (state : Option S)
    (header : List Bool) (t : ℕ) :
    (atm.extendTapes (terminalEmbedding k r q)).HaltsWithin t
      (config k r q input context n w p state header) ↔
      atm.HaltsWithin t ((CountingTerminalLayout.storage k r input context n w p []).withState
        state) := by
  rw [haltsWithin_extendTapes_iff, view_terminal_config]

/-- The embedded alternating terminal sees the actual stored counting query. -/
theorem acceptsWithin_terminal_iff {k r : ℕ} {S : Type}
    (atm : MultiTapeATM (CountingTerminalLayout.size k r) Bool S) (q : ℕ)
    (input context : List Bool) (n w : ℕ) (p : Routing.Position) (state : Option S)
    (header : List Bool) (t : ℕ) :
    (atm.extendTapes (terminalEmbedding k r q)).AcceptsWithin t
      (config k r q input context n w p state header) ↔
      atm.AcceptsWithin t ((CountingTerminalLayout.storage k r input context n w p []).withState
        state) := by
  rw [acceptsWithin_extendTapes_iff, view_terminal_config]

end Turing.MultiTapeATM.CarryLookaheadCountingLayout

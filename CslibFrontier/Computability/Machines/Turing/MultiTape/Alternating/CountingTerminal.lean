/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CountingTerminalLayout
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ExtendTapes

/-!
# Native terminals for the finishing adder of a predicate count

One finite alternating machine prepares a terminal request from short routing metadata, reads
its flags, and either emits the constant answer or copies the requested component index and
runs the actual carry-save counting evaluator. No operand word or semantic leaf answer is given
to the machine. The clock charges preparation, flag reads, index copying and every counting step.

The physical initial storage includes the root's binary height and unary depth frontier. Their
construction is a separate charged preparation phase.
-/

public section

namespace Turing.MultiTapeATM.CountingTerminal

open MultiTapeTM Cslib.Circuits.Boolean.CarryLookahead.Query
open Cslib.Circuits.Boolean.CarrySaveQuery

/-- Preparation, three flag reads, index copying and the actual root-evaluator clock. -/
@[expose] def clock (cP dP cR dR : ℕ) (context : List Bool) (n w : ℕ)
    (p : Routing.Position) : ℕ :=
  cP * ((Routing.encPosition p).length + 1) ^ dP + 2 + 2 * w.size + 8 +
    CarrySaveCountingRoot.clock cR dR context n w

/-- One finite native terminal evaluates actual carry-save root components from routing metadata.
Both the machine and all clock constants are uniform over inputs, counts, widths and positions. -/
theorem exists_evaluator (predicate : List Bool × ℕ → Bool)
    (hp : ComputableInPolyTime predicate (encPair encBits encNat) encBool) :
    ∃ (k r : ℕ) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM (CountingTerminalLayout.size k r) Bool S) (cP dP cR dR : ℕ),
      ∀ (input context : List Bool) (n w : ℕ) (p : Routing.Position) (hw : p.width = w),
        let root := Counting.rootPair n w (fun j => predicate (context, j))
        let cfg := (CountingTerminalLayout.storage k r input context n w p []).withState
          (some atm.toPTM.initial)
        atm.HaltsWithin (clock cP dP cR dR context n w p) cfg ∧
          (atm.AcceptsWithin (clock cP dP cR dR context n w p) cfg ↔
            Terminal.response (component root false) (component root true) p hw = true) := by
  obtain ⟨k, SR, hSR, roots, cR, dR, hroots⟩ := CarrySaveCountingRoot.exists_evaluator predicate hp
  obtain ⟨r, SP, hSP, prep, cP, dP, hprep⟩ := CountingTerminalPrepare.exists_machine
  let := hSR
  let := hSP
  let family := fun carry claim => (roots carry claim).extendTapes
    (CountingTerminalLayout.rootTapes k r)
  let terminal := CountingTerminalDispatch.machine (CountingTerminalLayout.flags k r)
    (CountingTerminalLayout.rootIndex k r) (CountingTerminalLayout.flags_ne_rootIndex k r) family
  let prepare := prep.extendTapes (CountingTerminalLayout.prepTapes k r)
  let atm := prependTM prepare terminal
  refine ⟨k, r, _, inferInstance, atm, cP, dP, cR, dR, ?_⟩
  intro input context n w p hw
  let root := Counting.rootPair n w (fun j => predicate (context, j))
  let storage := CountingTerminalLayout.storage k r input context n w p (Terminal.word p)
  let rootTime := CarrySaveCountingRoot.clock cR dR context n w
  let terminalTime := 2 * w.size + 8 + rootTime
  have hflagHead : storage.workTapePos (CountingTerminalLayout.flags k r) = 0 :=
    CountingTerminalLayout.storage_flags_head k r input context n w p (Terminal.word p)
  have hterminal : ∃ t ≤ terminalTime,
      terminal.HaltsWithin t (storage.withState (some terminal.toPTM.initial)) ∧
      (terminal.AcceptsWithin t (storage.withState (some terminal.toPTM.initial)) ↔
        Terminal.response (component root false) (component root true) p hw = true) := by
    cases hq : Terminal.queries p with
    | false =>
      have hflags : storage.workTapes (CountingTerminalLayout.flags k r) =
          tapeOfList ([false, Terminal.carry p, Terminal.answer p] ++
            encNat (Terminal.index p)) := by
        simp only [storage, CountingTerminalLayout.storage_flags, Terminal.word,
          Terminal.claimOrAnswer, hq, Bool.false_eq_true, ite_false]
      have h := CountingTerminalDispatch.constant_spec (CountingTerminalLayout.flags k r)
        (CountingTerminalLayout.rootIndex k r) (CountingTerminalLayout.flags_ne_rootIndex k r)
        family storage (Terminal.carry p) (Terminal.answer p) (encNat (Terminal.index p))
        hflags hflagHead rfl
      refine ⟨3, by dsimp only [terminalTime]; omega, h.1, ?_⟩
      simpa only [Terminal.response, hq, Bool.false_eq_true, ↓reduceDIte] using h.2
    | true =>
      have hi : Terminal.index p < w := hw ▸ Terminal.index_lt hq
      let bit : Fin w := ⟨Terminal.index p, hi⟩
      have hr := hroots input context n w bit (Terminal.carry p) p.claim
      let copied := CountingTerminalDispatch.copied (CountingTerminalLayout.flags k r)
        (CountingTerminalLayout.rootIndex k r) (encNat (Terminal.index p)) storage
      have hview : viewCfg (CountingTerminalLayout.rootTapes k r) copied =
          CarrySaveCountingRoot.initial k input context n w (Terminal.index p) :=
        CountingTerminalLayout.view_root_copied k r input context n w p (Terminal.word p) _
      have hh : (family (Terminal.carry p) p.claim).HaltsWithin rootTime
          (copied.withState (some (family (Terminal.carry p) p.claim).toPTM.initial)) := by
        rw [haltsWithin_extendTapes_iff]
        change (roots (Terminal.carry p) p.claim).HaltsWithin rootTime
          ((viewCfg (CountingTerminalLayout.rootTapes k r) copied).withState
            (some (roots (Terminal.carry p) p.claim).toPTM.initial))
        rw [hview]
        exact hr.1
      have ha : (family (Terminal.carry p) p.claim).AcceptsWithin rootTime
          (copied.withState (some (family (Terminal.carry p) p.claim).toPTM.initial)) ↔
          component root (Terminal.carry p) bit = p.claim := by
        rw [acceptsWithin_extendTapes_iff]
        change (roots (Terminal.carry p) p.claim).AcceptsWithin rootTime
          ((viewCfg (CountingTerminalLayout.rootTapes k r) copied).withState
            (some (roots (Terminal.carry p) p.claim).toPTM.initial)) ↔ _
        rw [hview]
        exact hr.2
      have hflags : storage.workTapes (CountingTerminalLayout.flags k r) =
          tapeOfList ([true, Terminal.carry p, p.claim] ++ encNat (Terminal.index p)) := by
        simp only [storage, CountingTerminalLayout.storage_flags, Terminal.word,
          Terminal.claimOrAnswer, hq, ite_true]
      have h := CountingTerminalDispatch.query_spec (CountingTerminalLayout.flags k r)
        (CountingTerminalLayout.rootIndex k r) (CountingTerminalLayout.flags_ne_rootIndex k r)
        family storage (Terminal.carry p) p.claim (encNat (Terminal.index p)) rootTime
        hflags hflagHead (by simp [storage]) (by simp [storage]) rfl hh
      have hlength : (encNat (Terminal.index p)).length ≤ w.size := by
        simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_size hi.le
      refine ⟨2 * (encNat (Terminal.index p)).length + 8 + rootTime,
        by dsimp only [terminalTime]; omega, h.1, h.2.trans (ha.trans ?_)⟩
      cases hc : Terminal.carry p <;> simp [Terminal.response, hq, hc, bit]
  obtain ⟨t, ht, hh, ha⟩ := hterminal
  have hhalt := hh.mono ht
  have haccept : terminal.AcceptsWithin terminalTime
      (storage.withState (some terminal.toPTM.initial)) ↔
      Terminal.response (component root false) (component root true) p hw = true :=
    ⟨fun h => ha.mp (h.of_halted_stepCoins hh), fun h => (ha.mpr h).mono ht⟩
  have hrun := CountingTerminalLayout.run_prepare prep k input context n w p (Terminal.word p)
    (cP * ((Routing.encPosition p).length + 1) ^ dP + 2) (hprep input p)
  have h := prependTM_spec prepare terminal
    (CountingTerminalLayout.storage k r input context n w p []) storage
    (cP * ((Routing.encPosition p).length + 1) ^ dP + 2) terminalTime hrun hhalt
  have hclock : cP * ((Routing.encPosition p).length + 1) ^ dP + 2 + terminalTime =
      clock cP dP cR dR context n w p := by dsimp only [terminalTime, rootTime, clock]; omega
  rw [hclock] at h
  exact ⟨h.1, h.2.trans haccept⟩

end Turing.MultiTapeATM.CountingTerminal

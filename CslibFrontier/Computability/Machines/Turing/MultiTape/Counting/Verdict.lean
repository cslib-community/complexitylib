/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Composition
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Encoding

/-!
# Signed verdict routing

On an encoded Boolean verifier result, this fixed one-step machine emits the chosen sign once
when the result is true. A false result instead produces one accepting and one rejecting branch.
Thus unsuccessful witnesses cancel in the integer gap, including when the witness length is zero.
Every local view has a nonempty choice list and all branches halt in one instruction.

## Main definitions

* `Turing.MultiTapeCTM.verdictMachine`: the actual one-versus-two native routing machine.

## Main results

* `Turing.MultiTapeCTM.VerdictMachine.haltsWithin`: one native instruction on any input.
* `Turing.MultiTapeCTM.VerdictMachine.branchCount_eq`: exact counts on encoded Booleans.
* `Turing.MultiTapeCTM.VerdictMachine.branchCount_comp`: charged, count-preserving routing.

## References

Balanced accepting/rejecting cancellation is the standard GapP mechanism
[FennerFortnowKurtz1994]. Native occurrence semantics are credited in `MultiTape.Counting`.
-/

@[expose] public section

namespace Turing.MultiTapeCTM

open Cslib MultiTapeTM

namespace VerdictMachine

/-- Emit one Boolean verdict and halt without moving a head. -/
def halt (sign : Bool) : Turing.Action 0 Bool Unit :=
  { inputTape := 0, workTapes := Fin.elim0, output := some sign, state := none }

end VerdictMachine

/-- True yields one chosen-sign leaf; false (or a blank input) yields a balanced pair. -/
def verdictMachine (sign : Bool) : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ symbol _ _ := (if symbol = some true then [VerdictMachine.halt sign]
    else [VerdictMachine.halt true, VerdictMachine.halt false]).map
      MultiTapeMachine.Action.emptyOracleEquiv.symm

namespace VerdictMachine

/-- Both the singleton and balanced local choice lists are nonempty. -/
theorem nonblocking (sign : Bool) : (verdictMachine sign).Nonblocking := by
  intro state symbol work
  simp only [verdictMachine]
  split <;> simp

/-- Every branch halts in one native instruction, even on inputs outside the Boolean encoding. -/
theorem haltsWithin (sign : Bool) (input : List Bool) :
    (verdictMachine sign).HaltsWithin 1 (Cfg.init () input) := by
  apply haltsWithin_of_halted _ (nonblocking sign).actions_ne_nil
  intro final hfinal
  rw [runList_succ _ _ 0 () rfl] at hfinal
  obtain ⟨action, haction, hfinal⟩ := List.mem_flatMap.mp hfinal
  have hsame : final = action.apply (Cfg.init () input) := by simpa using hfinal
  rw [hsame]
  simp only [actions, Cfg.init, verdictMachine, List.map_map,
    Function.comp_def, Equiv.apply_symm_apply] at haction
  split at haction <;> simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at haction
  · rcases haction with rfl
    rfl
  · rcases haction with rfl | rfl <;> rfl

/-- The exact one-step verdict count: unsuccessful witnesses contribute one of each sign. -/
theorem branchCount_eq (sign bit : Bool) (verdict : List Bool → Bool) :
    (verdictMachine sign).branchCount verdict 1 (Cfg.init () (encBool bit)) =
      if bit then (verdict [sign]).toNat
      else (verdict [true]).toNat + (verdict [false]).toNat := by
  have hsymbol : (Cfg.init () (encBool bit) : Cfg 0 Bool Unit _).inputSymbol = some bit := by
    simp [encBool_apply]
  have ha : (verdictMachine sign).actions (Cfg.init () (encBool bit)) =
      if bit then [halt sign] else [halt true, halt false] := by
    simp only [actions, show (Cfg.init () (encBool bit) : Cfg 0 Bool Unit _).state = some ()
      from rfl, verdictMachine, hsymbol]
    cases bit <;> simp
  rw [(haltsWithin sign (encBool bit)).branchCount_eq_countP verdict,
    runList_succ _ _ 0 () rfl, ha]
  cases bit <;>
    simp [halt, Turing.Action.apply, Cfg.init, Bool.toNat, Nat.add_comm, List.countP_cons]

/-- Buffered routing preserves the chosen-sign branch for every witness and cancels false ones.
The source must really output encoded Booleans; arbitrary words beginning in `true` are not
accepted as a substitute. The buffer and its preparation are included in the displayed clock. -/
theorem branchCount_comp {k : ℕ} {State : Type} (source : MultiTapeCTM k Bool State)
    (hnon : source.Nonblocking) (input : List Bool) (fuel : ℕ)
    (hhalt : source.HaltsWithin fuel (Cfg.init source.initial input))
    (hbool : ∀ result ∈ source.runList fuel (Cfg.init source.initial input),
      ∃ bit, result.output = encBool bit) (sign verdict : Bool) :
    ((verdictMachine sign).comp source true).branchCount
        (fun out => (out == [true]) == verdict) (fuel + (fuel + 4 + 1))
        (((verdictMachine sign).comp source true).initialConfig input).tapes =
      if sign = verdict then (source.runList fuel (Cfg.init source.initial input)).length
      else source.rejectCount fuel (Cfg.init source.initial input) := by
  rw [MultiTapeCTM.branchCount_comp source (verdictMachine sign) hnon (nonblocking sign)
    true input fuel 1 hhalt (fun result _ => haltsWithin sign result.output)]
  have hsum (items : List (Cfg k Bool State input))
      (hb : ∀ result ∈ items, ∃ bit, result.output = encBool bit) :
      (items.map (fun result => (verdictMachine sign).branchCount
        (fun out => (out == [true]) == verdict) 1 (Cfg.init () result.output))).sum =
        if sign = verdict then items.length else items.countP (fun result =>
          !(result.output == [true])) := by
    induction items with
    | nil => simp
    | cons result rest ih =>
      obtain ⟨bit, hout⟩ := hb result (by simp)
      have hrest := ih (fun final hf => hb final (List.mem_cons_of_mem _ hf))
      simp only [List.map_cons, List.sum_cons, hrest, List.length_cons, List.countP_cons]
      rw [hout, branchCount_eq]
      cases sign <;> cases verdict <;> cases bit <;> simp [encBool_apply, Nat.add_comm]
  change ((source.runList fuel (Cfg.init source.initial input)).map (fun result =>
    (verdictMachine sign).branchCount (fun out => (out == [true]) == verdict) 1
      (Cfg.init () result.output))).sum = _
  rw [hsum _ hbool]
  split
  · rfl
  · exact (hhalt.branchCount_eq_countP (fun out => !(out == [true]))).symm

end VerdictMachine

end Turing.MultiTapeCTM

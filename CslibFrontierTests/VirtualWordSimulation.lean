/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.ReadMachine.VirtualWord.Simulation

/-!
# Arbitrary-state virtual-input simulation clients

A copying transducer carries an unbounded binary address and an EOF flag. It emits each symbol,
then appends its binary final address. This exercises optional reads and both output
continuations, with no fixed fold or pass count. Resumption also starts from noninitial states.
-/

public section

namespace Cslib.Complexity.VirtualWordSimulationTest

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace VirtualWord

/-- Copy symbols until the first missing symbol, retaining an unbounded binary cursor. -/
@[expose] def copier : QueryMachine (ℕ × Bool) where
  init := (0, false)
  query := Prod.fst
  next p := (p.1.1 + 1, p.2.isNone)
  emit p := p.2.toList
  halted := Prod.snd
  finish s := encNat s.1

/-- All outer components are native, including the binary final-address output. -/
theorem outer_components :
    ComputableInSpace copier.query (encPair encNat encBool) encNat
      (fun s => (encPair encNat encBool s).length) ∧
    ComputableInSpace copier.next (encPair (encPair encNat encBool) (encOption encBool))
      (encPair encNat encBool)
      (fun p => (encPair (encPair encNat encBool) (encOption encBool) p).length) ∧
    ComputableInSpace copier.emit (encPair (encPair encNat encBool) (encOption encBool))
      encBits (fun p => (encPair (encPair encNat encBool) (encOption encBool) p).length) ∧
    ComputableInSpace copier.halted (encPair encNat encBool) encBool
      (fun s => (encPair encNat encBool s).length) ∧
    ComputableInSpace copier.finish (encPair encNat encBool) encBits
      (fun s => (encPair encNat encBool s).length) := by
  have hp := fst (encPair encNat encBool) (encOption encBool)
  have hb := snd (encPair encNat encBool) (encOption encBool)
  have hf : ComputableInSpace copier.finish (encPair encNat encBool) encBits
      (fun s => (encPair encNat encBool s).length) :=
    (fst encNat encBool).of_enc_eq (fun _ => rfl)
  exact ⟨fst _ _, budget_prod (budget_natSucc hp.fst')
    (budget_finite (encC := encBool) Option.isNone hb),
    budget_finite (encC := encBits) Option.toList hb, snd _ _, hf⟩

/-- Every prefix before EOF has the expected binary cursor and EOF flag. -/
theorem copier_run (w : List Bool) {k : ℕ} (hk : k ≤ w.length + 1) :
    copier.run w k = (k, decide (w.length < k)) := by
  induction k with
  | zero => simp [QueryMachine.run_zero, copier]
  | succ k ih =>
    rw [QueryMachine.run_succ, ih (by omega)]
    have hle : k ≤ w.length := by omega
    have hnot : ¬w.length < k := by omega
    simp only [QueryMachine.step, copier, hnot, decide_false, Bool.false_eq_true, ↓reduceIte,
      QueryMachine.read]
    rcases lt_or_eq_of_le hle with hlt | rfl
    · simp [List.getElem?_eq_getElem hlt, show ¬w.length < k + 1 by omega]
    · simp

/-- One actual compiled native transducer handles every valid runtime header and unbounded word.
Its saved counter contributes logarithmically in the virtual width, beside the charged header. -/
theorem native_copier : ∃ time c, ComputableInTimeAndSpace
    (fun p : Simulation.Input => copier.output (word p.val.2 p.val.1.1 p.val.1.2.1)
      ((word p.val.2 p.val.1.1 p.val.1.2.1).length + 1))
    Simulation.encInput encBits time
    (fun p => c * (2 * (Nat.log2 (word p.val.2 p.val.1.1 p.val.1.2.1).length + 2) + 2 +
      (encData p.val.1).length + Nat.log2 (Simulation.encInput p).length + 1)) := by
  obtain ⟨hq, hn, he, hh, hf⟩ := outer_components
  refine Simulation.computableInSpace copier (encPair encNat encBool) hq hn he hh hf encBits
    _ (fun p => (word p.val.2 p.val.1.1 p.val.1.2.1).length + 1)
    (fun p => 2 * (Nat.log2 (word p.val.2 p.val.1.1 p.val.1.2.1).length + 2) + 2)
    ?_ ?_ (fun _ => rfl) ?_
  · intro p
    rw [copier_run _ le_rfl]
    simp [copier]
  · intro p k hk
    rw [copier_run _ (by omega)]
    simp [copier, show ¬(word p.val.2 p.val.1.1 p.val.1.2.1).length < k by omega]
  · intro p k hk
    rw [copier_run _ hk, length_encPair]
    have hb := length_encNat_le_log2_add_two hk
    simp only [encBool_apply, List.length_singleton]
    omega

-- A suffix differs from the physical tail at that address; copying observes the virtual symbol.
example : (Simulation.machine copier).output
    (Runtime.encInput ((2, [true, false], 9), [true, false, false, true, true]))
    (2 * (encData (2, [true, false], 9)).length + 2 + 5) =
      [true, false, true, false] ++ encNat 5 := by decide

-- The virtual end is none even if the physical tail still has a symbol there.
example : Simulation.symbol copier
    (Evaluator.loaded ((1, [], 0), [false, true]), (1, false)) (some true) = none := by decide

-- Some false remains present, rather than ending the outer computation.
example : Simulation.symbol copier
    (Evaluator.loaded ((0, [false], 0), []), (0, false)) none = some false := by decide

-- Empty virtual input: one EOF transition, then the binary final-address continuation.
example : (Simulation.machine copier).output (Runtime.encInput ((0, [], 0), [true]))
    (2 * (encData (0, [], 0)).length + 3) = encNat 1 := by decide

-- An arbitrary saved outer cursor resumes without resetting either it or the loaded header.
example : ((Simulation.machine copier).step
    (Runtime.encInput ((2, [true], 0), [false, false, false])))^[2]
    (Evaluator.loaded ((2, [true], 0), [false, false, false]), (2, false)) =
      (Evaluator.loaded ((2, [true], 0), [false, false, false]), (4, true)) := by decide

-- A halted noninitial state is fixed, including its header and original-word offset.
example : (Simulation.machine copier).step (Runtime.encInput ((0, [], 0), []))
    (Evaluator.loaded ((0, [], 0), []), (1000, true)) =
      (Evaluator.loaded ((0, [], 0), []), (1000, true)) := by decide

/-- Unbounded counter states are simulated for every valid runtime header and every clock. -/
theorem run_client (p : Simulation.Input) (k : ℕ) :
    (Simulation.machine copier).run (Simulation.encInput p)
      (2 * (encData p.val.1).length + 2 + k) =
      (Evaluator.loaded p.val, copier.run (word p.val.2 p.val.1.1 p.val.1.2.1) k) :=
  Simulation.run_loaded copier p.val p.property k

end Cslib.Complexity.VirtualWordSimulationTest

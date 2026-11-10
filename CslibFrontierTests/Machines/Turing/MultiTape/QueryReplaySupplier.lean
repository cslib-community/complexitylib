/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of native checked gate preparation)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplaySupplierTotal
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplaySupplierBounds
public import CslibFrontierTests.Machines.Turing.MultiTape.QueryReplayGate
import Mathlib.Tactic.FinCases

/-!
# Checked gate supplier regressions

The supplier reads actual packed assignment words, prepares blank entering windows at the first
interval, and queries the original input during replay. It checks unused provider labels and
keeps failed output bounded by actual stored words, even with malformed large binary widths.
-/

public section

namespace CslibFrontierTests.QueryReplaySupplier

open Turing MultiTapeTM MultiTapePTM.BlockComputation
open MultiTapePTM.BlockComputation.QueryReplay
open NativeBlockCodec

@[expose] def word := Encoding.NativeEncode.serialize code (1, true, QueryReplayGate.raw)
@[expose] def counter := ofBits ((List.replicate 4 (word ++ [false])).flatten)
@[expose] noncomputable def prepared (σ : ℕ) : CheckedGate.State 1 (Fin 1) :=
  Supplier.prepare code (1, 1, σ, 0, 2 ^ 56, counter, 14)
@[expose] noncomputable def supplier := CheckedGate.machine QueryReplayGate.reader code

private def active (expected : Option (Fin 1) → SignType) : Gate.State 1 (Fin 1) :=
  ((0, 0, expected), Load.load (1, 1, (0, 0),
    (some 0, fun _ => 0, .empty, fun _ => [0, 0, 0])))

private def done (expected : Option (Fin 1) → SignType) : Gate.State 1 (Fin 1) :=
  ((0, 0, expected), ⟨1, 1, 0, 2, none, fun _ => 0, fun _ => [0, 2, 0], .accept⟩)

private theorem prepared_eq (σ : ℕ) :
    prepared σ = .inr (active (ScheduleRead.fullrow 1 (σ, 0))) := by
  change Sum.inr _ = Sum.inr _
  congr 1
  apply Prod.ext
  · rfl
  · apply Config.ext <;> first | rfl | (funext h; fin_cases h; rfl)

private theorem run_one (expected : Option (Fin 1) → SignType) :
    (Gate.machine QueryReplayGate.reader code).runFrom [true] (active expected) 1 =
      done expected := by
  unfold active
  rw [Gate.runFrom_eq]
  simp only [QueryMachine.runFrom_succ, QueryMachine.runFrom_zero, QueryMachine.step,
    QueryReplay.machine, QueryMachine.read, tick, QueryReplayGate.reader, MultiTapeTM.tr_ofTr]
  rfl

example : (prepared 2).isRight = true := by decide
example : supplier.halted (prepared 2) = false := by decide
example : supplier.halted (supplier.runFrom [true] (prepared 2) 1) = true := by decide
example : Encoding.NativeDecode.parse (k := 1) code
    (1, supplier.finish (supplier.runFrom [true] (prepared 2) 1)) =
      some (none, fun _ => 0, .accept, fun _ => [0, 2, 0]) := by
  unfold supplier
  rw [prepared_eq, CheckedGate.runFrom_inr, run_one]
  decide
example : supplier.finish (supplier.runFrom [true] (prepared 1) 1) =
    List.replicate (Encoding.width 1 1 1) false := by
  unfold supplier
  rw [prepared_eq, CheckedGate.runFrom_inr, run_one]
  decide

@[expose] def badCounter := ofBits
  ([word ++ [false], fail ++ [false], word ++ [false], word ++ [false]].flatten)
@[expose] noncomputable def rejected : CheckedGate.State 1 (Fin 1) :=
  Supplier.prepare code (1, 1, 2, 0, 2 ^ 56, badCounter, 14)

-- All provider ports are absent at interval zero, but the failed provider is still rejected.
example : rejected.isLeft = true := by decide
example : supplier.halted rejected = true := by decide
example : supplier.finish rejected = List.replicate 13 false := by decide

-- A rejected malformed call cannot allocate a billion-cell FAIL buffer.
example : (Supplier.prepare (k := 1) code (0, 1000000000, 0, 0, 1, 0, 14)).elim
    id (fun _ => []) = [false] := by decide

-- The counter-based supplier is the explicit-word supplier on the counter's labels.
example (σ : ℕ) : prepared σ = Supplier.prepareWords code (1, 1, σ, 0,
    Assignments.labels 1 (2 ^ 56, counter, 14, Encoding.width 1 1 1)) := rfl

-- Stored encoded views need no parsing argument: a FAIL previous view gives the FAIL word.
example (input : List Bool) (providers : Fin 1 → Fin 3 → Option (View 1 (Fin 1) 1)) :
    supplier.finish (supplier.runFrom input (Supplier.prepareWords code
      (input.length, 1, 0, ((0 : Fin 1) : ℕ),
        (List.ofFn (Encoding.encode (k := 1) (b := 1) code none),
        fun h δ => List.ofFn (Encoding.encode code (providers h δ))))) 1) =
      List.replicate (Encoding.width 1 1 1) false := by
  rw [supplier, Supplier.finish_prepareWords_encode]
  simp [gate, Supplier.ofFn_encode_none]

end CslibFrontierTests.QueryReplaySupplier

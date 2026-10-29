/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.GenericRAM.Simulation.Turing
public import Complexity.Computability.GenericRAM.Simulation.Run
public import Complexity.Computability.GenericRAM.Native.Nat
public import Complexity.Computability.WordRAM.Native
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Size

/-!
# Finite RAM simulation, multi-step execution, and native transport checks

A fixed store/load/branch/halt client runs across single steps and multi-step budgets. Separate
examples exercise current and continuing labels, missing instructions, failed addresses, invalid
moved values, failed tests versus false tests, the distinction between produced and moved values,
uniform native step and run execution across runtime configurations, retention of nonpolynomial
primitive and sparse-memory resource bounds, and end-to-end polynomial-time algorithm transport.
-/

@[expose] public section

namespace ComplexityTests.GenericRAMSimulation

open Cslib.GenericRAM Turing.MultiTapeTM
open BoundedNat

/-- Initial finite configuration with two registers and empty sparse store. -/
def initial (a v default : ℕ) : FiniteState model 2 :=
  ⟨0, ![a, v], default, ∅⟩

/-- Fixed four-instruction store/load/branch/halt client program. -/
def client : Program model 2 :=
  [.op (.store 0 1), .op (.load 1 0), .branch (.test () ![0, 1]) 3, .halt 1]

-- No eager fault for invalid registers unrelated to an instruction.
example : FiniteState.step (M := model) 8 [.jump 1] (initial 99 99 99) =
    some (.inl { initial 99 99 99 with pc := 1 }) := rfl

-- The same fixed client accepts two configurations; its memory operations are real sparse writes.
example (k : ℕ) (hk : 4 ≤ k) :
    FiniteState.step (M := model) k client (initial 0 3 0) =
      some (.inl { (initial 0 3 0).write 0 3 with pc := 1 }) := by
  have h0 : 0 < k := by omega
  have h1 : 1 < k := by omega
  have h3 : 3 < k := by omega
  simp [FiniteState.step, FiniteState.dispatch, FiniteState.evalInstr, FiniteState.evalOp,
    FiniteState.resume, client, initial, model, h0, h1, h3]

/-- State reached after storing 3 at address 0. -/
def stored : FiniteState model 2 := { (initial 0 3 0).write 0 3 with pc := 1 }
/-- State reached after clearing register 1 and loading address 0 back into register 1. -/
def loaded : FiniteState model 2 := { (stored.set 1 0).set 1 3 with pc := 2 }
/-- State reached after taking the false branch to the halt instruction. -/
def halting : FiniteState model 2 := { loaded with pc := 3 }

example :
    FiniteState.step (M := model) 4 client (stored.set 1 0) = some (.inl loaded) ∧
    FiniteState.step (M := model) 8 client (stored.set 1 0) = some (.inl loaded) ∧
    FiniteState.step (M := model) 4 client loaded = some (.inl halting) ∧
    FiniteState.step (M := model) 8 client halting = some (.inr 3) :=
  ⟨rfl, rfl, rfl, rfl⟩

-- A valid jump beyond the program faults on the next fetch, not on the jump; an invalid
-- current or continuing label faults immediately; and halt does not validate a successor label.
example :
    FiniteState.step (M := model) 8 [.jump 5] (initial 0 0 0) =
      some (.inl { initial 0 0 0 with pc := 5 }) ∧
    FiniteState.step (M := model) 8 [.jump 5] { initial 0 0 0 with pc := 5 } = none ∧
    FiniteState.step (M := model) 0 [.halt 0] (initial 0 0 0) = none ∧
    FiniteState.step (M := model) 4 [.jump 4] (initial 0 0 0) = none ∧
    FiniteState.step (M := model) 1 [.op (.copy 0 0)] (initial 0 0 0) = none ∧
    FiniteState.step (M := model) 1 [.halt 0] (initial 0 0 0) = some (.inr 0) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Address extraction and loaded/source value validation are independent failure paths.
example :
    FiniteState.step (M := model) 4 [.op (.load 1 0)] (initial 4 0 0) = none ∧
    FiniteState.step (M := model) 4 [.op (.load 1 0)] (initial 0 0 4) = none ∧
    FiniteState.step (M := model) 4 [.op (.store 0 1)] (initial 4 0 0) = none ∧
    FiniteState.step (M := model) 4 [.op (.store 0 1)] (initial 0 4 0) = none ∧
    FiniteState.step (M := model) 4 [.op (.copy 0 1)] (initial 0 4 0) = none ∧
    FiniteState.step (M := model) 4 [.halt 1] (initial 0 4 0) = none ∧
    FiniteState.step (M := model) 4 [.op (.const 1 4)] (initial 0 0 0) = none ∧
    FiniteState.step (M := model) 4 [.op (.alu () 1 ![0, 1])] (initial 2 2 0) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- False advances; a failed test faults. These cannot share a Boolean-only handler.
example :
    FiniteState.step (M := model) 4 [.branch (.test () ![0, 1]) 0] (initial 0 1 0) =
      some (.inl (initial 0 1 0)) ∧
    FiniteState.step (M := model) 4 [.branch (.test () ![0, 1]) 0] (initial 2 1 0) =
      some (.inl { initial 2 1 0 with pc := 1 }) ∧
    FiniteState.step (M := model) 4 [.branch (.test () ![0, 1]) 0]
      (initial 0 4 0) = none :=
  ⟨rfl, rfl, rfl⟩

-- A model may distinguish admissible produced values from legal moves.
/-- A model where produced values can be admissible although all moves fail. -/
abbrev rejectMoves : Model := { model with validMove := fun _ _ => false }
private def noMoves : FiniteState rejectMoves 1 := ⟨0, ![0], 0, ∅⟩
example :
    FiniteState.step (M := rejectMoves) 4 [.op (.const 0 2)] noMoves =
      some (.inl { noMoves.set 0 2 with pc := 1 }) ∧
    FiniteState.step (M := rejectMoves) 4 [.op (.copy 0 0)] noMoves = none :=
  ⟨rfl, rfl⟩

-- Empty register tuples are permitted when no instruction needs a register.
example : FiniteState.step (M := model) 4 ([.jump 0] : Program model 0) ⟨0, Fin.elim0, 0, ∅⟩ =
    some (.inl ⟨0, Fin.elim0, 0, ∅⟩) := rfl

-- Functional memory has redundant sparse representations; encodings must use the finite state.
example : (initial 0 0 0).denote = ((initial 0 0 0).write 7 0).denote := by
  rw [FiniteState.denote_write]
  ext a <;> simp [FiniteState.denote, initial, Data.write]

/-- The simulation covers every bounded-natural finite state, including invalid inputs. -/
theorem all_states (k : ℕ) (p : Program model 2) (s : FiniteState model 2) :
    FiniteState.denoteResult (FiniteState.step (M := model) k p s) = step k p s.denote :=
  FiniteState.denote_step k p s

/-- Concrete native step certificate for the four-instruction store/load/branch/halt client. -/
noncomputable def clientCertificate :
    NativeCertificate (fun q : ℕ × FiniteState model 2 => FiniteState.step q.1 client q.2)
      (FiniteState.inputEncoding encoding) (FiniteState.resultEncoding encoding) :=
  FiniteState.stepCertificate encoding nativePrimitives client

/-- One finite native machine implements the fixed client across all runtime configurations. -/
theorem client_step_inO :
    ComputableInO (fun q : ℕ × FiniteState model 2 => FiniteState.step q.1 client q.2)
      (FiniteState.inputEncoding encoding) (FiniteState.resultEncoding encoding)
      (FiniteState.stepTime encoding nativePrimitives client)
      (FiniteState.stepSpace encoding nativePrimitives client) :=
  FiniteState.step_inO encoding nativePrimitives client

/-- A single finite native machine handles distinct runtime configurations (`k = 4`, `k = 8`,
and invalid `k = 0`) without fixing the configuration in its transition table. -/
theorem uniform_machine_across_configs :
    ∃ (c k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State),
      (∀ q : ℕ × FiniteState model 2,
        tm.ComputesInTimeAndSpace
          (FiniteState.inputEncoding encoding q)
          (FiniteState.resultEncoding encoding (FiniteState.step q.1 client q.2))
          (c * (FiniteState.stepTime encoding nativePrimitives client q + 1))
          (c * (FiniteState.stepSpace encoding nativePrimitives client q + 1))) ∧
      FiniteState.step (M := model) 4 client (stored.set 1 0) = some (.inl loaded) ∧
      FiniteState.step (M := model) 8 client (stored.set 1 0) = some (.inl loaded) ∧
      FiniteState.step (M := model) 0 client (stored.set 1 0) = none := by
  obtain ⟨c, ⟨k, State, hfin, tm, htm⟩, _⟩ := client_step_inO
  exact ⟨c, k, State, hfin, tm, htm, rfl, rfl, rfl⟩

/-- Encoded finite-state length on `stored` is bounded by control, register bound, default, and
store size. -/
example :
    (FiniteState.encoding encoding stored).length ≤
      2 * (encNat stored.pc).length + 2 * 2 * (2 * 2 + 1) +
        2 * (encNat stored.default).length +
        (SparseMemory.entries stored.memory).length *
          (4 * SparseMemory.maxKeyLength encNat stored.memory +
            2 * SparseMemory.maxValueLength encNat stored.memory + 3) + 3 :=
  FiniteState.length_encoding_le encoding stored (by decide)

/-- Primitive bundle whose constant certificate carries an exponential resource bound `2 ^ k`. -/
noncomputable def expPrimitives : model.NativePrimitives encoding where
  constant c :=
    ⟨fun k => (nativePrimitives.constant c).time k + 2 ^ k,
     fun k => (nativePrimitives.constant c).space k + 2 ^ k,
     (nativePrimitives.constant c).computes.mono_le
       (fun _ => Nat.le_add_right _ _) (fun _ => Nat.le_add_right _ _)⟩
  operation := nativePrimitives.operation
  test := nativePrimitives.test
  address := nativePrimitives.address
  validMove := nativePrimitives.validMove
  validPC := nativePrimitives.validPC

/-- `stepTime` and `stepSpace` retain nonpolynomial supplied primitive bounds rather than
selecting a polynomial bound. -/
theorem retained_exponential_primitive_bound (k : ℕ) (hk : 1 ≤ k) (s : FiniteState model 2)
    (hpc : s.pc = 0) :
    2 ^ k ≤ FiniteState.stepTime encoding expPrimitives [.op (.const 0 1)] (k, s) ∧
      2 ^ k ≤ FiniteState.stepSpace encoding expPrimitives [.op (.const 0 1)] (k, s) := by
  have hv : model.validPC k s.pc = true := by
    simp [model, hpc]
    omega
  have htc : 2 ^ k ≤ (expPrimitives.constant 1).time k := Nat.le_add_left _ _
  have hsc : 2 ^ k ≤ (expPrimitives.constant 1).space k := Nat.le_add_left _ _
  have hto : (expPrimitives.constant 1).time k ≤
      FiniteState.opTime encoding expPrimitives (.const 0 1) (k, s) :=
    FiniteState.le_opTime_const encoding expPrimitives 0 1 (k, s)
  have hso : (expPrimitives.constant 1).space k ≤
      FiniteState.opSpace encoding expPrimitives (.const 0 1) (k, s) :=
    FiniteState.le_opSpace_const encoding expPrimitives 0 1 (k, s)
  have hti := FiniteState.le_instrTime_op encoding expPrimitives 1 (.const 0 1) (k, s)
  have hsi := FiniteState.le_instrSpace_op encoding expPrimitives 1 (.const 0 1) (k, s)
  rw [FiniteState.stepTime_cons, FiniteState.stepSpace_cons, hv]
  simp only [hpc, ite_true]
  exact ⟨le_trans htc (le_trans hto (le_trans hti (by omega))),
    le_trans hsc (le_trans hso (le_trans hsi (by omega)))⟩

/-- Valid stores in `client` retain the parameterized sparse-memory write bound in `stepTime`. -/
theorem retained_sparse_write_bound (k : ℕ) (hk : 4 ≤ k) :
    SparseMemory.writeTime encNat encNat ((0, 3), ∅) ≤
      FiniteState.stepTime encoding nativePrimitives client (k, initial 0 3 0) := by
  have h0 : 0 < k := by omega
  have h3 : 3 < k := by omega
  have hv : model.validPC k (initial 0 3 0).pc = true := by
    simp [model, initial, h0]
  have ha : model.address k ((initial 0 3 0).regs 0) = some 0 := by
    simp [model, initial, h0]
  have hm : model.validMove k ((initial 0 3 0).regs 1) = true := by
    simp [model, initial, h3]
  have hto := FiniteState.le_opTime_store encoding nativePrimitives 0 1 (k, initial 0 3 0) 0 ha hm
  have hti := FiniteState.le_instrTime_op encoding nativePrimitives 1 (.store 0 1)
    (k, initial 0 3 0)
  rw [client, FiniteState.stepTime_cons, hv]
  have hpc : (initial 0 3 0).pc = 0 := rfl
  simp only [hpc, ite_true]
  exact le_trans hto (le_trans hti (by omega))

-- Multi-step execution across step budgets, early halting, and faulting.
/-- State reached after storing 3 at address 0 and loading address 0 back into register 1. -/
def clientLoaded : FiniteState model 2 := { stored.set 1 3 with pc := 2 }
/-- State reached after taking the false branch to the halt instruction. -/
def clientHalting : FiniteState model 2 := { clientLoaded with pc := 3 }

example :
    FiniteState.run (M := model) 4 client 0 (initial 0 3 0) = some (.inl (initial 0 3 0)) ∧
    FiniteState.run (M := model) 4 client 1 (initial 0 3 0) = some (.inl stored) ∧
    FiniteState.run (M := model) 4 client 2 (initial 0 3 0) = some (.inl clientLoaded) ∧
    FiniteState.run (M := model) 4 client 3 (initial 0 3 0) = some (.inl clientHalting) ∧
    FiniteState.run (M := model) 4 client 4 (initial 0 3 0) = some (.inr 3) ∧
    FiniteState.run (M := model) 4 client 5 (initial 0 3 0) = some (.inr 3) ∧
    FiniteState.eval (M := model) 4 client 3 (initial 0 3 0) = none ∧
    FiniteState.eval (M := model) 4 client 4 (initial 0 3 0) = some 3 ∧
    FiniteState.eval (M := model) 4 client 5 (initial 0 3 0) = some 3 ∧
    FiniteState.run (M := model) 2 client 1 (initial 0 3 0) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Finite multi-step runs refine operational `Executes` and bound sparse-memory growth.
example :
    (∃ m ≤ 4, Executes (M := model) 4 client (initial 0 3 0).denote 3 m) ∧
    (SparseMemory.entries stored.memory).length ≤
      (SparseMemory.entries (initial 0 3 0).memory).length + 1 :=
  ⟨FiniteState.executes_of_run_eq_inr (M := model) (k := 4) (p := client) (n := 4)
    (s := initial 0 3 0) rfl,
   FiniteState.length_entries_run_le
    (rfl : FiniteState.run (M := model) 4 client 1 (initial 0 3 0) = some (.inl stored))⟩

/-- `runTime` and `runSpace` dominate every active intermediate step's `stepTime` and `stepSpace`,
preserving nonpolynomial primitive bounds across multi-step runs. -/
theorem retained_exponential_run_bound (k : ℕ) (hk : 1 ≤ k) :
    2 ^ k ≤ FiniteState.runTime encoding expPrimitives [.op (.const 0 1)]
      (1, (k, initial 0 0 0)) ∧
    2 ^ k ≤ FiniteState.runSpace encoding expPrimitives [.op (.const 0 1)]
      (1, (k, initial 0 0 0)) := by
  have hrun : FiniteState.run (M := model) k [.op (.const 0 1)] 0 (initial 0 0 0) =
      some (.inl (initial 0 0 0)) := rfl
  have hstep := retained_exponential_primitive_bound k hk (initial 0 0 0) rfl
  exact ⟨le_trans hstep.1
      (FiniteState.le_runTime_of_run_eq_inl encoding expPrimitives
        [.op (.const 0 1)] (Nat.zero_le 1) hrun),
    le_trans hstep.2
      (FiniteState.le_runSpace_of_run_eq_inl encoding expPrimitives
        [.op (.const 0 1)] (Nat.zero_le 1) hrun)⟩

/-- Six-instruction program that sets register `0` to `0`, stores its input `x` (initially in
register `1`) at sparse address `0`, loads it back into register `0`, adds registers `0` and `1`
via the model ALU, branches to the halt label, and returns `x + x`. -/
def doubleProgram : Program model 2 :=
  [.op (.const 0 0), .op (.store 0 1), .op (.load 0 0),
   .op (.alu () 1 ![0, 1]), .branch (.test () ![0, 1]) 5, .halt 1]

/-- Initial finite configuration with both registers set to `x`, default `0`, and empty memory. -/
def doubleInit (x : ℕ) : FiniteState model 2 :=
  FiniteState.initConst x 0 ∅

/-- Native certificate for `doubleInit`. -/
noncomputable def doubleInitCert :
    NativeCertificate doubleInit encNat (FiniteState.encoding encoding) :=
  FiniteState.initConstCertificate (r := 2) encoding
    (NativeCertificate.linear ComputableInDegree.id'.inO_one)
    (NativeCertificate.const 0)
    (NativeCertificate.const ∅)

theorem doubleInitCert_isPolynomial : doubleInitCert.IsPolynomial :=
  FiniteState.initConstCertificate_isPolynomial (r := 2) encoding _ _ _
    (NativeCertificate.linear_isPolynomial ComputableInDegree.id'.inO_one)
    (NativeCertificate.const_isPolynomial 0)
    (NativeCertificate.const_isPolynomial ∅)

/-- Runtime configuration `(x + x) + 6` accommodates program labels `0..5` and intermediate value
`x + x`. -/
def doubleConfig (x : ℕ) : ℕ := (x + x) + 6

theorem doubleConfig_polyTime :
    ComputableInPolyTime doubleConfig encNat encNat := by
  unfold doubleConfig
  fun_prop

/-- Native certificate for `doubleConfig`. -/
noncomputable def doubleConfigCert : NativeCertificate doubleConfig encNat encNat :=
  .ofPolyTime doubleConfig_polyTime

theorem doubleConfigCert_isPolynomial : doubleConfigCert.IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial doubleConfig_polyTime

/-- Constant step budget `6` for `doubleProgram`. -/
noncomputable def doubleStepsCert : NativeCertificate (fun _ : ℕ => 6) encNat encNat :=
  NativeCertificate.const 6

theorem doubleStepsCert_isPolynomial : doubleStepsCert.IsPolynomial :=
  NativeCertificate.const_isPolynomial 6

/-- `doubleProgram` halts in `6` steps with output `x + x` at configuration `doubleConfig x` from
initial state `doubleInit x`. -/
theorem doubleProgram_run (x : ℕ) :
    FiniteState.run (doubleConfig x) doubleProgram 6 (doubleInit x) = some (.inr (x + x)) := by
  have h0 : 0 < doubleConfig x := by simp [doubleConfig]
  have h1 : 1 < doubleConfig x := by simp [doubleConfig]
  have h2 : 2 < doubleConfig x := by simp [doubleConfig]
  have h3 : 3 < doubleConfig x := by simp [doubleConfig]
  have h4 : 4 < doubleConfig x := by simp [doubleConfig]
  have h5 : 5 < doubleConfig x := by simp [doubleConfig]
  have hx : x < doubleConfig x := by simp [doubleConfig]; omega
  have hxx : x + x < doubleConfig x := by simp [doubleConfig]
  have hmem : SparseMemory.read 0 (0 : ℕ) (AList.singleton 0 x) = x := by
    simpa using congrFun (SparseMemory.read_insert 0 (0 : ℕ) x ∅) 0
  simp [FiniteState.run, FiniteState.step, FiniteState.dispatch, FiniteState.evalInstr,
    FiniteState.evalOp, FiniteState.resume, FiniteState.set, FiniteState.write, FiniteState.move,
    Model.checkedConstant, Model.checkedOp, doubleInit, FiniteState.initConst,
    FiniteState.init, doubleProgram, model, h0, h1, h2, h3, h4, h5, hx, hxx, hmem]

/-- `doubleProgram` satisfies semantic `Executes` within `6` steps for all inputs `x`. -/
theorem doubleProgram_executes (x : ℕ) :
    ∃ m ≤ 6, Executes (M := model) (doubleConfig x) doubleProgram
      (doubleInit x).denote (x + x) m :=
  FiniteState.executes_of_run_eq_inr (doubleProgram_run x)

/-- Explicit native multitape TM certificate transported from `doubleProgram`. -/
noncomputable def doubleTransportCert :
    NativeCertificate (fun x : ℕ => x + x) encNat encNat :=
  FiniteState.transportCertificate encoding nativePrimitives doubleProgram
    doubleStepsCert doubleConfigCert doubleInitCert doubleProgram_executes

/-- Whole-run explicit `ComputableInO` bound transported from `doubleProgram`. -/
theorem double_inO :
    ComputableInO (fun x : ℕ => x + x) encNat encNat
      doubleTransportCert.time doubleTransportCert.space :=
  FiniteState.transport_inO encoding nativePrimitives doubleProgram
    doubleStepsCert doubleConfigCert doubleInitCert doubleProgram_executes

/-- Automatic `ComputableInPolyTime` transport for `doubleProgram` via
`FiniteState.transport_polyTime_of_le_const`. -/
theorem double_polyTime :
    ComputableInPolyTime (fun x : ℕ => x + x) encNat encNat :=
  FiniteState.transport_polyTime_of_le_const encoding nativePrimitives doubleProgram
    doubleStepsCert doubleConfigCert doubleInitCert doubleProgram_executes
    nativePrimitives_isPolynomial
    doubleStepsCert_isPolynomial doubleConfigCert_isPolynomial doubleInitCert_isPolynomial
    6 (fun _ => le_rfl)

/-- Automatic `ComputableInPolyTime` single-step simulation for `doubleProgram` via
`FiniteState.step_polyTime`. -/
theorem double_step_polyTime :
    ComputableInPolyTime
      (fun q : ℕ × FiniteState model 2 => FiniteState.step q.1 doubleProgram q.2)
      (FiniteState.inputEncoding encoding) (FiniteState.resultEncoding encoding) :=
  FiniteState.step_polyTime encoding nativePrimitives doubleProgram nativePrimitives_isPolynomial

/-! ### End-to-end WordRAM program transport over `Basis.standard` -/

/-- Five-instruction `Basis.standard` word-RAM program that clears register `0` via bitwise XOR,
stores `x` (initially in register `1`) at memory address `0`, loads it back into register `0`,
adds registers `0` and `1`, and halts returning `x + x`. -/
def wordDoubleProgram : Cslib.WordRAM.Program Cslib.WordRAM.Basis.standard 2 :=
  [.op (.alu (.bin .xor) 0 ![0, 0]),
   .op (.store 0 1),
   .op (.load 0 0),
   .op (.alu (.bin .add) 1 ![0, 1]),
   .halt 1]

/-- Initial finite generic state for `wordDoubleProgram` with both registers set to `x`. -/
def wordDoubleInit (x : ℕ) : FiniteState Cslib.WordRAM.Basis.standard.genericModel 2 :=
  FiniteState.initConst x 0 ∅

/-- Corresponding semantic `WordRAM.State` with both registers set to `x` and zeroed memory. -/
def wordDoubleState (x : ℕ) : Cslib.WordRAM.State 2 :=
  ⟨0, ⟨fun _ => x, fun _ => 0⟩⟩

/-- Native certificate for `wordDoubleInit`. -/
noncomputable def wordDoubleInitCert :
    NativeCertificate wordDoubleInit encNat
      (FiniteState.encoding Cslib.WordRAM.Basis.standard.encoding) :=
  FiniteState.initConstCertificate (r := 2) Cslib.WordRAM.Basis.standard.encoding
    (NativeCertificate.linear ComputableInDegree.id'.inO_one)
    (NativeCertificate.const 0)
    (NativeCertificate.const ∅)

theorem wordDoubleInitCert_isPolynomial : wordDoubleInitCert.IsPolynomial :=
  FiniteState.initConstCertificate_isPolynomial (r := 2) Cslib.WordRAM.Basis.standard.encoding _ _ _
    (NativeCertificate.linear_isPolynomial ComputableInDegree.id'.inO_one)
    (NativeCertificate.const_isPolynomial 0)
    (NativeCertificate.const_isPolynomial ∅)

/-- Runtime word width `x.size + 2` (encoded in unary), accommodating `0`, `x`, and `x + x`. -/
def wordDoubleWidth (x : ℕ) : ℕ := x.size + 2

theorem wordDoubleWidth_polyTime :
    ComputableInPolyTime wordDoubleWidth encNat encUnary := by
  unfold wordDoubleWidth
  fun_prop

/-- Native certificate for `wordDoubleWidth`. -/
noncomputable def wordDoubleWidthCert : NativeCertificate wordDoubleWidth encNat encUnary :=
  .ofPolyTime wordDoubleWidth_polyTime

theorem wordDoubleWidthCert_isPolynomial : wordDoubleWidthCert.IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial wordDoubleWidth_polyTime

/-- Constant step budget `5` for `wordDoubleProgram`. -/
noncomputable def wordDoubleStepsCert : NativeCertificate (fun _ : ℕ => 5) encNat encNat :=
  NativeCertificate.const 5

theorem wordDoubleStepsCert_isPolynomial : wordDoubleStepsCert.IsPolynomial :=
  NativeCertificate.const_isPolynomial 5

/-- `wordDoubleProgram.toGeneric` halts in `5` steps with output `x + x` at width
`wordDoubleWidth x` from initial state `wordDoubleInit x`. -/
theorem wordDoubleProgram_run (x : ℕ) :
    FiniteState.run (wordDoubleWidth x) wordDoubleProgram.toGeneric 5 (wordDoubleInit x) =
      some (.inr (x + x)) := by
  have hfit0 : Cslib.WordRAM.Fits (wordDoubleWidth x) 0 := Cslib.WordRAM.fits_zero _
  have hfitxx : Cslib.WordRAM.Fits (wordDoubleWidth x) (x + x) := by
    rw [Cslib.WordRAM.fits_iff, wordDoubleWidth]
    have hx : x < 2 ^ x.size := Nat.lt_size_self x
    have hpow : 2 ^ (x.size + 2) = 4 * 2 ^ x.size := by ring
    omega
  have hmem : SparseMemory.read 0 (0 : ℕ) (AList.singleton 0 x) = x := by
    simpa using congrFun (SparseMemory.read_insert 0 (0 : ℕ) x ∅) 0
  simp only [wordDoubleProgram, Cslib.WordRAM.Program.toGeneric, List.map_cons, List.map_nil,
    Cslib.WordRAM.Instr.toGeneric, Cslib.WordRAM.Op.toGeneric]
  simp [FiniteState.run, FiniteState.step, FiniteState.dispatch, FiniteState.evalInstr,
    FiniteState.evalOp, FiniteState.resume, FiniteState.set, FiniteState.write, FiniteState.move,
    Model.checkedOp, wordDoubleInit, FiniteState.initConst, FiniteState.init,
    Cslib.WordRAM.Basis.genericModel, Cslib.WordRAM.Basis.standard,
    Cslib.WordRAM.StandardOp.eval, Cslib.WordRAM.BinOp.eval, hfit0, hfitxx, hmem]

/-- `wordDoubleProgram` satisfies semantic `WordRAM.Executes` within `5` steps for all `x`. -/
theorem wordDoubleProgram_executes (x : ℕ) :
    ∃ m ≤ 5, Cslib.WordRAM.Executes (wordDoubleWidth x) wordDoubleProgram
      (wordDoubleState x) (x + x) m := by
  obtain ⟨m, hm, hex⟩ := FiniteState.executes_of_run_eq_inr (wordDoubleProgram_run x)
  exact ⟨m, hm, Cslib.WordRAM.executes_toGeneric_iff.mp hex⟩

/-- Whole-run `ComputableInO` bound transported from `wordDoubleProgram` via
`Cslib.WordRAM.transport_inO` and `Basis.standard.nativePrimitives`. -/
theorem wordDouble_inO :
    Turing.MultiTapeTM.ComputableInO (fun x : ℕ => x + x) encNat encNat
      (fun x => wordDoubleStepsCert.time x +
        (wordDoubleWidthCert.time x + wordDoubleInitCert.time x) +
        FiniteState.runTime Cslib.WordRAM.Basis.standard.encoding
          Cslib.WordRAM.Basis.standard.nativePrimitives wordDoubleProgram.toGeneric
          (5, (wordDoubleWidth x, wordDoubleInit x)))
      (fun x => wordDoubleStepsCert.space x +
        (wordDoubleWidthCert.space x + wordDoubleInitCert.space x) +
        FiniteState.runSpace Cslib.WordRAM.Basis.standard.encoding
          Cslib.WordRAM.Basis.standard.nativePrimitives wordDoubleProgram.toGeneric
          (5, (wordDoubleWidth x, wordDoubleInit x))) :=
  Cslib.WordRAM.transport_inO Cslib.WordRAM.Basis.standard.encoding
    Cslib.WordRAM.Basis.standard.nativePrimitives wordDoubleProgram
    wordDoubleStepsCert wordDoubleWidthCert wordDoubleInitCert
    (fun _ => rfl) wordDoubleProgram_executes

/-- Automatic `ComputableInPolyTime` transport for `wordDoubleProgram` via
`Cslib.WordRAM.transport_polyTime_of_le_const` and `Basis.standard.nativePrimitives`. -/
theorem wordDouble_polyTime :
    ComputableInPolyTime (fun x : ℕ => x + x) encNat encNat :=
  Cslib.WordRAM.transport_polyTime_of_le_const Cslib.WordRAM.Basis.standard.encoding
    Cslib.WordRAM.Basis.standard.nativePrimitives wordDoubleProgram
    wordDoubleStepsCert wordDoubleWidthCert wordDoubleInitCert
    (fun _ => rfl) wordDoubleProgram_executes
    Cslib.WordRAM.Basis.standard.nativePrimitives_isPolynomial
    wordDoubleStepsCert_isPolynomial wordDoubleWidthCert_isPolynomial
    wordDoubleInitCert_isPolynomial
    5 (fun _ => le_rfl)

end ComplexityTests.GenericRAMSimulation

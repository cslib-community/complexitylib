/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Implementation

/-!
# Standalone native certificates for the realized binary heap

The fixed raw heap program projects through the existing `StateTransitionImpl` API to a
standard-basis `DynamicCertificate`. The same program and register layout serve every runtime
dimension, layout, key bound and width. Its representation is the checked compact heap
representation, and each operation pays the selected source-method bound, the native dispatcher
a charged identity suffix preserving their already canonical fixed-bank observations, and a
final halt.

This is the operation-call model: argument delivery is external, and an
adaptive client's host continuations are not timed. Whole compiled clients instead use the
original memory-method `Realizes` certificates and charge their control and input prefix.
Fresh initialization retains the compact local-zero domain; dirty initialization uses the
shared linear clear. The old instruction and register constants are not claimed.

## Main definitions

* `operationTime`: the realized body/dispatcher instruction allowance.
* `dynamicProgram`: the fixed standalone standard-basis program and canonical result bank.
* `certificate`: its correctness certificate on the original fit domain.

## Main results

* `certificate_rep_iff`: the certificate retains the checked raw heap representation.
* `instruction_bound`: each actual call pays its allowance, identity suffix and halt.
* `run_client_bound`: an adaptive client retains observations and adds these call costs.

## References

The heap semantics and invariants are reused from `BinaryHeap.Memory`; this file only applies
the shared native-certificate projections and introduces no new heap algorithm.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.BinaryHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.PriorityQueue.BinaryHeap (space)
open Cslib.DataStructure.PriorityQueue.WordRAM

/-- The source-method allowance and paid native dispatcher; the final halt is separate. -/
@[expose] noncomputable def operationTime {n : ℕ} (o : IndexedMinPQ.Op n) : ℕ :=
  Backend.factor Program.family * (memoryBound o + 1) + 8

/-- One fixed program with the existing arguments, a paid identity suffix and strict canonical
results from the operation-independent flag/payload/key bank. -/
@[expose] noncomputable def dynamicProgram (n K : ℕ) :
    DynamicProgram (indexedMinPQSpec n K) Program.registers where
  code := .seq Program.code.toStandard.code (.op (.copy Program.code.output Program.code.output))
  output := Program.code.output
  input := Program.code.input
  encode := Program.code.encode
  resultBank := Program.code.nativeResultBank
  resultType := PQCode.nativeResultType n
  resultType_eq := PQCode.nativeResultType_eq n K

variable {w n K base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K)

/-- Actual body outputs are already canonical. The paid identity suffix preserves every
register and memory cell; its readiness is established from the preceding body execution. -/
noncomputable def resultRecoding :
    NativeResultRecoding (indexedMinPQSpec n K).Result .standard Program.registers w
      (subroutineImpl hS hK).toStandard.decode (subroutineImpl hS hK).toStandard.rep
      (subroutineImpl hS hK).toStandard.potential where
  code := .op (.copy Program.code.output Program.code.output)
  resultBank := Program.code.nativeResultBank
  resultType := PQCode.nativeResultType n
  resultType_eq := PQCode.nativeResultType_eq n K
  ready o x := nativeObservation (K := K) o x.regs =
    (subroutineImpl hS hK).toStandard.decode o x.regs
  time := 1
  execute {s x} o a hr _ hready hd := by
    have hs : x.set Program.code.output (x.regs Program.code.output) = x := by
      cases x
      simp only [Data.set, Function.update_eq_self]
    refine ⟨x, ?_, (nativeObservation_eq_some_iff o x.regs a).mp (hready.trans hd), hr, rfl, rfl⟩
    simpa only [hs] using
      (ExecWithin.copy (B := Basis.standard) (w := w) (x := x)
        (d := Program.code.output) (s := Program.code.output))

private theorem result_ready {s : (indexedMinPQSpec n K).State}
    {x y : Data Program.registers} {o : IndexedMinPQ.Op n} {N : ℕ}
    (hr : (subroutineImpl hS hK).toStandard.rep s x) (hv : IndexedMinPQ.valid K s o)
    (ha : (subroutineImpl hS hK).toStandard.argMatch o x.regs)
    (he : Exec w Program.code.toStandard.code x y N) : (resultRecoding hS hK).ready o y := by
  obtain ⟨z, _, a, m, hex, _, _, _, _, _⟩ := (subroutineImpl hS hK).step_exec o hr hv ha
  have hcanonical := subroutineImpl_exec_nativeObservation hS hK o hr hv ha hex
  obtain ⟨rfl, _⟩ := he.unique (hex.mapSimulates .exactStandard)
  change nativeObservation (K := K) o y.regs = (subroutineImpl hS hK).decode o y.regs
  rw [subroutineImpl_toBase, subroutineBase_decode]
  exact hcanonical

private theorem projected_program_eq :
    (subroutineImpl hS hK).toStandard.toDynamicProgram (resultRecoding hS hK) =
      dynamicProgram n K := by
  have he : (subroutineImpl hS hK).toStandard.encode = Program.code.encode := by
    change (subroutineImpl hS hK).toSubroutineBase.encode = _
    rw [subroutineImpl_toBase]
    exact funext fun o => subroutineBase_encode hS hK o
  dsimp only [SubroutineBase.toDynamicProgram, SubroutineCode.toDynamicProgram,
    dynamicProgram, resultRecoding]
  rw [he]
  rfl

private theorem projected_potential (x : Data Program.registers) :
    (subroutineImpl hS hK).toStandard.potential x = 0 := by
  change (subroutineImpl hS hK).toSubroutineBase.potential x = 0
  rw [subroutineImpl_toBase]
  exact subroutineBase_potential hS hK x

private theorem projected_charge (s : (indexedMinPQSpec n K).State) (o : IndexedMinPQ.Op n) :
    (subroutineImpl hS hK).charge s o = operationTime o := by
  rw [subroutineImpl_toBase]
  exact subroutineBase_charge hS hK s o

private theorem projected_rep_iff {hn : Fits w n} (s : (indexedMinPQSpec n K).State)
    (x : Data Program.registers) :
    (subroutineImpl hS hK).rep s x ↔ Representation.Rep base hn hK s x := by
  rw [subroutineImpl_toBase]
  exact subroutineBase_rep_iff hS hK s x

/-- The shared standalone correctness projection, on only the original end-fit/key-fit domain. -/
noncomputable def certificate : DynamicCertificate (dynamicProgram n K) w :=
  projected_program_eq hS hK ▸ (subroutineImpl hS hK).toStandard.toCertificate
    (resultRecoding hS hK) (result_ready hS hK)

/-- The standalone certificate retains the raw Backend representation and persistent layout. -/
theorem certificate_rep_iff {hn : Fits w n} (s : (indexedMinPQSpec n K).State)
    (x : Data Program.registers) :
    (certificate hS hK).rep s x ↔ Representation.Rep base hn hK s x := by
  let C := (subroutineImpl hS hK).toStandard.toCertificate
    (resultRecoding hS hK) (result_ready hS hK)
  have hc : (certificate hS hK).rep s x ↔ C.rep s x :=
    Eq.rec (motive := fun _ h => (h ▸ C).rep s x ↔ C.rep s x)
      Iff.rfl (projected_program_eq hS hK)
  exact hc.trans (projected_rep_iff hS hK s x)

/-- Every actual admissible call pays its body allowance, one identity-copy instruction and
its final halt. Canonical observations are actual words in the fixed bank. -/
theorem instruction_bound :
    Bound (certificate hS hK).impl DynamicProgram.OperationTrace.instructions
      (fun _ o => operationTime o + 2) := by
  intro s x o a y trace hr hv he
  have hn : Fits w n := hS.of_le (by unfold space; omega)
  have hrC : (subroutineImpl hS hK).toStandard.rep s x :=
    (projected_rep_iff hS hK s x).mpr ((certificate_rep_iff (hn := hn) hS hK s x).mp hr)
  have heC : ((subroutineImpl hS hK).toStandard.toDynamicProgram
      (resultRecoding hS hK)).ExecOp w x o a y trace := by
    rw [projected_program_eq]
    exact he
  have h := (subroutineImpl hS hK).toStandard.toBound
    (resultRecoding hS hK) (result_ready hS hK) (projected_potential hS hK) hrC hv heC
  change trace.instructions ≤ (subroutineImpl hS hK).charge s o + 2 at h
  rwa [projected_charge] at h

include hS

/-- Adaptive clients preserve every observation and sum actual halt-inclusive call costs.
This does not charge host continuations or external argument delivery. -/
theorem run_client_bound {hn : Fits w n} {α : Type*} (p : (indexedMinPQSpec n K).Client α)
    {s : (indexedMinPQSpec n K).State} {x : Data Program.registers}
    (hr : Representation.Rep base hn hK s x)
    (hv : (indexedMinPQSpec n K).ValidHistory s ((indexedMinPQSpec n K).clientHistory s p)) :
    ∃ y traces,
      Executes ((dynamicProgram n K).ExecOp w) p x ((indexedMinPQSpec n K).clientResult s p)
        y traces ∧
      Representation.Rep base hn hK ((indexedMinPQSpec n K).clientState s p) y ∧
      DataStructure.total DynamicProgram.OperationTrace.instructions traces ≤
        (indexedMinPQSpec n K).totalCost (fun _ o => operationTime o + 2) s
          ((indexedMinPQSpec n K).clientHistory s p) := by
  have hrc : (subroutineImpl hS hK).toStandard.rep s x :=
    (projected_rep_iff hS hK s x).mpr hr
  obtain ⟨y, tr, he, hy, ht⟩ := (subroutineImpl hS hK).toStandard.run_client_bound
    (resultRecoding hS hK) (result_ready hS hK) (projected_potential hS hK) p hrc hv
  refine ⟨y, tr, ?_, (projected_rep_iff hS hK _ y).mp hy, ?_⟩
  · rw [projected_program_eq] at he
    exact he
  · change DataStructure.total DynamicProgram.OperationTrace.instructions tr ≤
      (indexedMinPQSpec n K).totalCost (fun s o => (subroutineImpl hS hK).charge s o + 2) s
        ((indexedMinPQSpec n K).clientHistory s p) at ht
    simpa only [projected_charge] using ht

end Cslib.DataStructure.PriorityQueue.BinaryHeap.Native

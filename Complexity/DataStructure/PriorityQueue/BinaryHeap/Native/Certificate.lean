/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.Implementation

/-!
# Standalone native certificates for the realized binary heap

The fixed raw heap program projects through the existing `StateTransitionImpl` API to a
standard-basis `DynamicCertificate`. The same program and register layout serve every runtime
dimension, layout, key bound and width. Its representation is the checked compact heap
representation, and each operation pays the selected source-method bound, the native dispatcher
and a final halt.

This is the operation-call model: argument delivery and result decoding are external, and an
adaptive client's host continuations are not timed. Whole compiled clients instead use the
original memory-method `Realizes` certificates and charge their control and input prefix.
Fresh initialization retains the compact local-zero domain; dirty initialization uses the
shared linear clear. The old instruction and register constants are not claimed.

## Main definitions

* `operationTime`: the realized body/dispatcher instruction allowance.
* `dynamicProgram`: the fixed standalone standard-basis program and existing PQ convention.
* `certificate`: its correctness certificate on the original fit domain.

## Main results

* `certificate_rep_iff`: the certificate retains the checked raw heap representation.
* `instruction_bound`: every actual admissible call pays the allowance plus its halt.
* `run_client_bound`: an adaptive client retains observations and adds these call costs.

## References

The heap semantics and invariants are reused from `BinaryHeap.Memory`; this file only applies
the shared native-certificate projections and introduces no new heap algorithm.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.BinaryHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.PriorityQueue.BinaryHeap (space)

/-- The source-method allowance and paid native dispatcher; the final halt is separate. -/
@[expose] noncomputable def operationTime {n : ℕ} (o : IndexedMinPQ.Op n) : ℕ :=
  Backend.factor Program.family * (memoryBound o + 1) + 8

/-- One fixed program, with the existing argument convention and typed result decoder. -/
@[expose] noncomputable def dynamicProgram (n K : ℕ) :
    DynamicProgram (indexedMinPQSpec n K) Program.registers where
  code := Program.code.toStandard.code
  output := Program.code.output
  input := Program.code.input
  encode := Program.code.encode
  decode := Program.code.decode (K_max := K)

variable {w n K base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K)

private theorem projected_program_eq :
    (subroutineImpl hS hK).toStandard.toDynamicProgram = dynamicProgram n K := by
  change ((subroutineImpl hS hK).toSubroutineBase.mapSimulates .exactStandard).toDynamicProgram = _
  rw [subroutineImpl_toBase]
  change Program.code.toStandard.toSubroutineCode.toDynamicProgram
    (subroutineBase hS hK).encode (subroutineBase hS hK).decode = _
  have he : (subroutineBase hS hK).encode = Program.code.encode :=
    funext fun o => subroutineBase_encode hS hK o
  have hd : (subroutineBase hS hK).decode = Program.code.decode :=
    funext fun o => subroutineBase_decode hS hK o
  rw [he, hd]
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

/-- The standalone certificate retains the raw Backend representation and persistent layout. -/
theorem certificate_rep_iff {hn : Fits w n} (s : (indexedMinPQSpec n K).State)
    (x : Data Program.registers) :
    (certificate hS hK).rep s x ↔ Representation.Rep base hn hK s x := by
  have hc : (certificate hS hK).rep s x ↔
      (subroutineImpl hS hK).toStandard.toCertificate.rep s x :=
    Eq.rec (motive := fun _ h =>
      (h ▸ (subroutineImpl hS hK).toStandard.toCertificate).rep s x ↔
        (subroutineImpl hS hK).toStandard.toCertificate.rep s x)
      Iff.rfl (projected_program_eq hS hK)
  exact hc.trans (projected_rep_iff hS hK s x)

/-- Every actual admissible standalone operation pays its native allowance and final halt.
Argument delivery and result decoding remain the existing external calling convention. -/
theorem instruction_bound :
    Bound (certificate hS hK).impl DynamicProgram.OperationTrace.instructions
      (fun _ o => operationTime o + 1) := by
  intro s x o a y trace hr hv he
  have hn : Fits w n := hS.of_le (by unfold space; omega)
  have hrC : (subroutineImpl hS hK).toStandard.rep s x :=
    (projected_rep_iff hS hK s x).mpr ((certificate_rep_iff (hn := hn) hS hK s x).mp hr)
  have heC : (subroutineImpl hS hK).toStandard.toDynamicProgram.ExecOp w x o a y trace := by
    rw [projected_program_eq]
    exact he
  have h := (subroutineImpl hS hK).toStandard.toBound
    (projected_potential hS hK) hrC hv heC
  change trace.instructions ≤ (subroutineImpl hS hK).charge s o + 1 at h
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
        (indexedMinPQSpec n K).totalCost (fun _ o => operationTime o + 1) s
          ((indexedMinPQSpec n K).clientHistory s p) := by
  have hrc : (subroutineImpl hS hK).toStandard.rep s x :=
    (projected_rep_iff hS hK s x).mpr hr
  obtain ⟨y, tr, he, hy, ht⟩ := (subroutineImpl hS hK).toStandard.run_client_bound
    (projected_potential hS hK) p hrc hv
  refine ⟨y, tr, ?_, (projected_rep_iff hS hK _ y).mp hy, ?_⟩
  · rw [projected_program_eq] at he
    exact he
  · change DataStructure.total DynamicProgram.OperationTrace.instructions tr ≤
      (indexedMinPQSpec n K).totalCost (fun s o => (subroutineImpl hS hK).charge s o + 1) s
        ((indexedMinPQSpec n K).clientHistory s p) at ht
    simpa only [projected_charge] using ht

end Cslib.DataStructure.PriorityQueue.BinaryHeap.Native

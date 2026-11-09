/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Interpreter.Output
public import CslibFrontier.Computability.GenericRAM.SparseMemory.CompactTuring
import all CslibFrontier.Computability.GenericRAM.SparseMemory.Compact
import all CslibFrontier.Computability.GenericRAM.SparseMemory.CompactTuring
import all CslibFrontier.Computability.GenericRAM.Simulation.Finite
import all CslibFrontier.Computability.GenericRAM.Simulation.Run
import all CslibFrontier.Computability.GenericRAM.Simulation.Turing
import all CslibFrontier.Computability.WordRAM.Basis
import all CslibFrontier.Computability.WordRAM.Defs
import all CslibFrontier.Computability.WordRAM.Turing

/-!
# Default deletion commutes with actual runtime-program execution

Every retained state is normalized by a real filtering computation. The exact
refinement preserves registers, labels and total memory and commutes with native
steps, including writes of zero and faults. This is stronger than applying a
space estimate to a simulation that still stores historical zero bindings.

The existing sparse scans and general interpreter polynomial workspace overhead
remain charged; compaction alone does not prove sharp source bit resources.
-/

public section
namespace Cslib.WordRAM.Interpreter
open Cslib.GenericRAM Turing.MultiTapeTM

/-- Actually delete all memory cells equal to the state's explicit default. -/
def compactState {r : ℕ} (s : FiniteState Basis.standard.genericModel r) :
    FiniteState Basis.standard.genericModel r :=
  ⟨s.pc, s.regs, s.default, SparseMemory.compact s.default s.memory⟩

/-- Normalize only continuing states; faults and returns retain their original tags. -/
def compactResult {r : ℕ} (out : FiniteState.Result Basis.standard.genericModel r) :
    FiniteState.Result Basis.standard.genericModel r := out.map (Sum.map compactState id)

/-- Compaction changes no total memory observation or register. -/
theorem denote_compactState {r : ℕ} (s : FiniteState Basis.standard.genericModel r) :
    (compactState s).denote = s.denote := by
  cases s
  simp only [compactState, FiniteState.denote, SparseMemory.read_compact]

/-- Applying the real filter twice is idempotent, including list order. -/
theorem compactState_idem {r : ℕ} (s : FiniteState Basis.standard.genericModel r) :
    compactState (compactState s) = compactState s := by
  simp only [compactState, SparseMemory.compact_idem]

private theorem compactState_set {r : ℕ} (s : FiniteState Basis.standard.genericModel r)
    (i : Fin r) (v : ℕ) : compactState ((compactState s).set i v) = compactState (s.set i v) := by
  simp only [compactState, FiniteState.set, SparseMemory.compact_idem]

private theorem compactState_write {r : ℕ} (s : FiniteState Basis.standard.genericModel r)
    (a v : ℕ) : compactState ((compactState s).write a v) = compactState (s.write a v) := by
  simp only [compactState, FiniteState.write, SparseMemory.compact_insert_compact]

private theorem evalOp_compact {r : ℕ} (w : ℕ)
    (o : GenericRAM.Op Basis.standard.genericModel r)
    (s : FiniteState Basis.standard.genericModel r) :
    (FiniteState.evalOp w o (compactState s)).map compactState =
      (FiniteState.evalOp w o s).map compactState := by
  cases o with
  | const i c =>
    simp only [FiniteState.evalOp, Option.map_map]
    congr 1
    funext v
    exact compactState_set s i v
  | alu f i args =>
    simp only [FiniteState.evalOp, compactState, Option.map_map]
    congr 1
    funext v
    exact compactState_set s i v
  | copy i j =>
    simpa only [FiniteState.evalOp, FiniteState.move, Basis.genericModel, compactState,
      Bool.true_eq, ite_true, Option.map_some,
      Option.some.injEq] using compactState_set s i (s.regs j)
  | load i a =>
    simpa only [FiniteState.evalOp, FiniteState.move, Basis.genericModel, compactState,
      SparseMemory.read_compact, Option.bind_eq_bind, Option.bind_some,
      Bool.true_eq, ite_true, Option.map_some,
      Option.some.injEq] using
      compactState_set s i (SparseMemory.read s.default (s.regs a) s.memory)
  | store a i =>
    simpa only [FiniteState.evalOp, Basis.genericModel, compactState, Option.bind_eq_bind,
      Option.bind_some, Bool.true_eq, ite_true, Option.map_some,
      Option.some.injEq] using
      compactState_write s (s.regs a) (s.regs i)

private theorem resume_compact {r : ℕ} (w pc : ℕ)
    (s : FiniteState Basis.standard.genericModel r) :
    compactResult (FiniteState.resume w pc (compactState s)) =
      compactResult (FiniteState.resume w pc s) := by
  simp only [FiniteState.resume, Basis.genericModel, compactState, compactResult,
    ite_true, Option.map_some, Sum.map_inl, SparseMemory.compact_idem]

/-- Every actual instruction commutes with default deletion, including normalized stores. -/
theorem evalInstr_compact {r : ℕ} (w pc : ℕ)
    (i : GenericRAM.Instr Basis.standard.genericModel r)
    (s : FiniteState Basis.standard.genericModel r) :
    compactResult (FiniteState.evalInstr w pc i (compactState s)) =
      compactResult (FiniteState.evalInstr w pc i s) := by
  cases i with
  | op o =>
    have hop := evalOp_compact w o s
    simp only [FiniteState.evalInstr, compactResult, bind]
    cases hleft : FiniteState.evalOp w o (compactState s) with
    | none =>
      simp only [hleft, Option.map_none] at hop
      cases hright : FiniteState.evalOp w o s with
      | none => rfl
      | some t => simp [hright] at hop
    | some t =>
      cases hright : FiniteState.evalOp w o s with
      | none => simp [hleft, hright] at hop
      | some u =>
        simp only [hleft, hright, Option.map_some, Option.some.injEq] at hop
        simpa only [bind, Option.bind_some, compactResult] using
          (resume_compact w pc t).symm.trans
            ((congrArg (fun z => compactResult (FiniteState.resume w pc z)) hop).trans
              (resume_compact w pc u))
  | jump pc => exact resume_compact w pc s
  | branch cond target =>
    cases cond with
    | test f args =>
      have bind_eq (v : Option Bool) :
          compactResult (v.bind (fun b =>
            FiniteState.resume w (if b then target else pc) (compactState s))) =
          compactResult (v.bind (fun b => FiniteState.resume w (if b then target else pc) s)) := by
        cases v with
        | none => rfl
        | some b => exact resume_compact w _ s
      exact bind_eq (Basis.standard.genericModel.evalTest w f (s.regs ∘ args))
  | halt i => rfl

/-- Uniform program dispatch commutes with deletion for every program and current label. -/
theorem step_compact {r : ℕ} (w : ℕ) (p : GenericRAM.Program Basis.standard.genericModel r)
    (s : FiniteState Basis.standard.genericModel r) :
    compactResult (FiniteState.step w p (compactState s)) =
      compactResult (FiniteState.step w p s) := by
  simp only [FiniteState.step, Basis.genericModel, ite_true]
  rw [FiniteState.dispatch_eq_getElem? w p 0 (compactState s) (Nat.zero_le _),
    FiniteState.dispatch_eq_getElem? w p 0 s (Nat.zero_le _)]
  cases hp : p[s.pc]? with
  | none =>
    simp only [compactState, Nat.sub_zero, hp, bind, Option.bind_none,
      compactResult, Option.map_none]
  | some i =>
    simpa only [compactState, Nat.sub_zero, hp, bind, Option.bind_some] using
      evalInstr_compact w (s.pc + 1) i s

/-- Actual filtering certificate, with cubic time and linear workspace in the full input wire. -/
noncomputable def compactMemoryCertificate : NativeCertificate
    (fun q : ℕ × SparseMemory ℕ ℕ => SparseMemory.compact q.1 q.2)
    (SparseMemory.compactEncoding encNat encNat) (SparseMemory.encoding encNat encNat) :=
  ⟨fun q => ((SparseMemory.compactEncoding encNat encNat q).length + 1) ^ 3,
    fun q => (SparseMemory.compactEncoding encNat encNat q).length + 1,
    SparseMemory.compact_inO_cube encNat encNat⟩

/-- One bit machine normalizes a finite state, charging all tuple projections and rebuilding. -/
noncomputable def compactStateCertificate {r : ℕ} : NativeCertificate
    (compactState (r := r)) (FiniteState.encoding Basis.standard.encoding)
    (FiniteState.encoding Basis.standard.encoding) := by
  let hid : NativeCertificate (id : FiniteState Basis.standard.genericModel r → _)
      (FiniteState.encoding Basis.standard.encoding)
      (FiniteState.encoding Basis.standard.encoding) :=
    NativeCertificate.linear (ComputableInO.of_eq fun _ => rfl)
  let fields := FiniteState.Native.fields Basis.standard.encoding hid
  let memory := compactMemoryCertificate.comp
    (NativeCertificate.prod (NativeCertificate.fst (NativeCertificate.snd
      (NativeCertificate.snd fields))) (NativeCertificate.snd (NativeCertificate.snd
        (NativeCertificate.snd fields))))
  let c := (FiniteState.Native.pack Basis.standard.encoding).comp
    (NativeCertificate.prod (NativeCertificate.fst fields)
      (NativeCertificate.prod (NativeCertificate.fst (NativeCertificate.snd fields))
        (NativeCertificate.prod (NativeCertificate.fst (NativeCertificate.snd
          (NativeCertificate.snd fields))) memory)))
  exact ⟨c.time, c.space, c.computes.of_enc_eq (fun _ => rfl)⟩

/-- State normalization cannot increase the actual finite-state encoding. -/
theorem length_compactState_le {r : ℕ} (s : FiniteState Basis.standard.genericModel r) :
    (FiniteState.encoding Basis.standard.encoding (compactState s)).length ≤
      (FiniteState.encoding Basis.standard.encoding s).length := by
  have h := SparseMemory.length_encoding_compact_le encNat encNat s.default s.memory
  simp only [FiniteState.length_encoding, compactState, Basis.encoding]
  omega

/-- One bit machine normalizes an outcome, preserving faults and returned words. -/
noncomputable def compactResultCertificate {r : ℕ} : NativeCertificate
    (compactResult (r := r)) (FiniteState.resultEncoding Basis.standard.encoding)
    (FiniteState.resultEncoding Basis.standard.encoding) := by
  let enc := FiniteState.resultEncoding (r := r) Basis.standard.encoding
  let hid : NativeCertificate (id : FiniteState.Result Basis.standard.genericModel r → _)
      enc enc := NativeCertificate.linear (ComputableInO.of_eq fun _ => rfl)
  let body := NativeCertificate.some (NativeCertificate.inl
    (compactStateCertificate (r := r) |>.comp (NativeCertificate.payload enc
      (FiniteState.encoding Basis.standard.encoding))) encNat)
  exact NativeCertificate.congr (NativeCertificate.option
    (FiniteState.continuingCertificate Basis.standard.encoding) hid body) (fun out => by
      cases out with
      | none => rfl
      | some v => cases v <;> rfl)

end Cslib.WordRAM.Interpreter

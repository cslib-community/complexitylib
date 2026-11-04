/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayCheckedGate
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding.NativeDecode

/-!
# Packed numeric answers from returned replay states

The supplier retains a binary chunk width and requested chunk index beside the checked local
replay state. Its query machine is silent: the interpolation caller extracts one numeric answer
from the returned state, rather than storing a callee output stream. Extraction reads only a
slice of the already paid Boolean gate result, including a zero-padded final partial chunk.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.SupplierChunk

open MultiTapeTM MultiTapeTM.ComputableInSpace

variable {k s : ℕ} {Q : Type}

/-- Runtime chunk width and requested chunk index. -/
abbrev Context := ℕ × ℕ

/-- Retained packed-answer metadata and the actual checked replay state. -/
abbrev State (k : ℕ) (Q : Type) := Context × CheckedGate.State k Q

/-- Binary metadata has its actual encoded storage charge. -/
@[expose] noncomputable def encContext : Context ↪ List Bool := encPair encNat encNat

/-- Replay on the same original input, retaining packed-answer metadata without an output
stream. Actual input-dependent initial states are supplied by the caller. -/
@[expose] noncomputable def machine (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    QueryMachine (State k Q) where
  init := ((0, 0), (CheckedGate.machine M e).init)
  query := fun (_, q) => (CheckedGate.machine M e).query q
  next := fun ((context, q), symbol) =>
    (context, (CheckedGate.machine M e).next (q, symbol))
  emit _ := []
  halted := fun (_, q) => (CheckedGate.machine M e).halted q
  finish _ := []

/-- Extract one numeric packed chunk from the returned checked gate state. Reading a partial
final chunk implicitly pads the missing high bits with zero. -/
@[expose] noncomputable def answer (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    State k Q → ℕ := fun ((m, chunk), q) =>
  Encoding.NativeDecode.readNat ((CheckedGate.machine M e).finish q) (chunk * m) m

variable [Finite Q]

/-- Retained numeric metadata and checked replay storage are both charged explicitly. -/
@[expose] noncomputable def encState : State k Q ↪ List Bool :=
  encPair encContext (CheckedGate.encState (k := k) (Q := Q))

/-- Queries are delegated to the checked original-input replay. -/
theorem machine_query_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).query encState encNat (fun a => (encState a).length) := by
  have hq := snd encContext (CheckedGate.encState (k := k) (Q := Q))
  exact (budget_comp_linear (CheckedGate.machine_query_inSpace M e) hq).of_enc_eq
    fun _ => rfl

/-- Transitions retain chunk metadata and charge the complete active state. -/
theorem machine_next_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).next (encPair encState (encOption encBool)) encState
      (fun a => (encPair encState (encOption encBool) a).length) := by
  have hs := fst (encState (k := k) (Q := Q)) (encOption encBool)
  have hcontext := hs.fst'
  have hq := hs.snd'
  have hsymbol := snd (encState (k := k) (Q := Q)) (encOption encBool)
  have hnext := budget_comp_linear (CheckedGate.machine_next_inSpace M e)
    (budget_prod hq hsymbol)
  exact (budget_prod hcontext hnext).of_enc_eq fun _ => rfl

/-- Intermediate output is empty; numeric answers are read from returned states. -/
theorem machine_emit_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).emit (encPair encState (encOption encBool)) encBits
      (fun a => (encPair encState (encOption encBool) a).length) :=
  budget_const [] (.refl _)

/-- Stopping is exactly that of the checked replay. -/
theorem machine_halted_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).halted encState encBool (fun a => (encState a).length) := by
  have hq := snd encContext (CheckedGate.encState (k := k) (Q := Q))
  exact (budget_comp_linear (CheckedGate.machine_halted_inSpace M e) hq).of_enc_eq
    fun _ => rfl

/-- The query-machine finish stream is empty, because the caller consumes `answer` instead. -/
theorem machine_finish_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).finish encState encBits (fun a => (encState a).length) :=
  budget_const [] (.refl _)

/-- Packed-answer extraction uses native space linear in the actual returned-state storage.
Neither the chunk width nor its offset causes allocation of its numeric magnitude. -/
theorem answer_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (answer M e) encState encNat (fun a => (encState a).length) := by
  have hcontext := fst encContext (CheckedGate.encState (k := k) (Q := Q))
  have hq := snd encContext (CheckedGate.encState (k := k) (Q := Q))
  have hm := hcontext.fst'
  have hchunk := hcontext.snd'
  have hword := budget_comp_linear (CheckedGate.machine_finish_inSpace M e) hq
  exact (budget_comp_linear Encoding.NativeDecode.readNat_inSpace
    (budget_prod hword (budget_prod (budget_natMul hchunk hm) hm))).of_enc_eq
      fun _ => rfl

omit [Finite Q] in
/-- Retained answer metadata does not change physical replay transitions. -/
theorem runFrom_eq (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (context : Context) (q : CheckedGate.State k Q) (t : ℕ) :
    (machine M e).runFrom w (context, q) t =
      (context, (CheckedGate.machine M e).runFrom w q t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [QueryMachine.runFrom_succ, ih, QueryMachine.runFrom_succ]
    simp only [QueryMachine.step, machine, QueryMachine.read]
    by_cases h : (CheckedGate.machine M e).halted
        ((CheckedGate.machine M e).runFrom w q t) = true
    · simp [h]
    · simp [h]

end Turing.MultiTapePTM.BlockComputation.QueryReplay.SupplierChunk

/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.EmitWork
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
import Mathlib.Tactic.FinCases

/-!
# Serializing native endpoint answers

`encAnswer` uses explicit validity/found tags: `[false]` for an invalid request,
`[true, false]` for valid exhaustion, and `[true, true] ++ n.bits` for an endpoint.
This differs from `encOption`, whose absent case is the empty word.

The two-tape finite serializer reads the short flag word on tape 0 and emits the index word
on tape 1 only after two true flags. It preserves both words and the previous output. No result
bit is recovered by reading the append-only output tape.
-/

public section

namespace Turing.MultiTapeTM.ScheduleEndpointAnswer

/-- Explicit validity/found tags followed by a canonical least-significant-bit-first index.
Invalid requests encode as `[false]`; valid exhaustion encodes as `[true, false]`. -/
@[expose] def encAnswer : Option (Option ℕ) ↪ List Bool :=
  ⟨fun a => match a with
    | none => [false]
    | some none => [true, false]
    | some (some n) => [true, true] ++ encNat n,
    by
      rintro (_ | (_ | n)) (_ | (_ | m)) h <;>
        simp_all only [List.cons_append, List.nil_append, List.cons.injEq, Bool.false_eq_true,
          Bool.true_eq_false, false_and, and_false, true_and, EmbeddingLike.apply_eq_iff_eq]⟩

/-- Serializer control: read validity, read found, then copy the returned binary index. -/
inductive State where
  | validity
  | found
  | copy
  deriving DecidableEq

instance : Fintype State := ⟨{.validity, .found, .copy}, fun s => by cases s <;> simp⟩

private noncomputable def copyIndex := (emitWork Bool).extendTapes (tapeEmb (1 : Fin 2))

/-- Read and emit the two flags, copying the index only for `[true,true]`. On a false flag,
halt immediately; the unused counter word is preserved without scanning it. -/
noncomputable def machine : MultiTapeTM 2 Bool State :=
  .ofTr .validity fun state input work => match state with
    | .validity =>
      ⟨0, ![(none, 1), (none, 0)], work 0,
        if work 0 == some true then some .found else none⟩
    | .found =>
      ⟨0, ![(none, 1), (none, 0)], work 0,
        if work 0 == some true then some .copy else none⟩
    | .copy =>
      let a := copyIndex.tr () input work
      { a with state := a.state.map fun _ => .copy }

private theorem copy_follows :
    machine.toMultiTapeNTM.Follows copyIndex.toMultiTapeNTM (fun _ => .copy)
    (.mapState (Option.map fun _ => .copy)) :=
  fun _ _ _ h => tr_iff.mp h ▸ rfl

private theorem runFrom_copy {input : List Bool} (c : Cfg 2 Bool Unit input) (t : ℕ) :
    machine.runFrom (c.mapState (Option.map fun _ => .copy)) t =
      (copyIndex.runFrom c t).mapState (Option.map fun _ => .copy) :=
  runFrom_map (copy_follows.stepHom (Cfg.mapState (Option.map fun _ => .copy))
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)) c t

private theorem runsBetween_copyIndex (input flags word out : List Bool) :
    RunsBetween copyIndex (tapesCfg input ![flags, word] 0 ![2, 0] out)
      (tapesCfg input ![flags, word] 0 ![2, word.length] (out ++ word))
      (word.length + 1) (word.length + 3) := by
  have h := runsBetween_emitWork (input := input) word out
  have hv : viewCfg (tapeEmb (1 : Fin 2))
      (tapesCfg input ![flags, word] 0 ![2, 0] out) =
      tapesCfg input (fun _ : Fin 1 => word) 0 0 out := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;> rfl
  rw [← hv] at h
  have he := h.extendTapes (tapeEmb (1 : Fin 2))
  have hf : embed (tapeEmb (1 : Fin 2))
      (tapesCfg input (fun _ : Fin 1 => word) 0 (fun _ => word.length) (out ++ word))
      (tapesCfg input ![flags, word] 0 ![2, 0] out).workTapes
      (tapesCfg input ![flags, word] 0 ![2, 0] out).workTapePos =
      tapesCfg input ![flags, word] 0 ![2, word.length] (out ++ word) := by
    rw [embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;>
      simp [tapesCfg]
  rw [hf] at he
  simpa [copyIndex] using he

/-- An invalid interval is serialized in one step, without reading the counter word. -/
theorem runsBetween_invalid (input word out : List Bool) :
    RunsBetween machine (tapesCfg input ![[false], word] 0 0 out)
      (tapesCfg input ![[false], word] 0 ![1, 0] (out ++ [false])) 1 4 := by
  apply RunsBetween.of_runFrom
  rw [runFrom_one, step_of_state rfl]
  refine Cfg.ext ?_ ?_ (funext fun i => ?_) (funext fun i => ?_) ?_ <;>
    (try fin_cases i) <;>
    simp [machine, tapesCfg, Cfg.withState, Cfg.workTapeSymbols, Action.apply, tapeOfList]

private theorem step_validity (input word out : List Bool) (found : Bool) :
    machine.step ((tapesCfg input ![[true, found], word] 0 0 out).withState
      (some .validity)) =
      (tapesCfg input ![[true, found], word] 0 ![1, 0] (out ++ [true])).withState
        (some .found) := by
  rw [step_of_state rfl]
  refine Cfg.ext ?_ ?_ (funext fun i => ?_) (funext fun i => ?_) ?_ <;>
    (try fin_cases i) <;>
    simp [machine, tapesCfg, Cfg.withState, Cfg.workTapeSymbols, Action.apply, tapeOfList]

/-- A valid exhausted query emits its two flags and does not inspect the unused counter word. -/
theorem runsBetween_exhausted (input word out : List Bool) :
    RunsBetween machine (tapesCfg input ![[true, false], word] 0 0 out)
      (tapesCfg input ![[true, false], word] 0 ![2, 0] (out ++ [true, false])) 2 6 := by
  apply RunsBetween.of_runFrom
  change machine.runFrom _ (1 + 1) = _
  rw [show machine.q₀ = .validity from rfl]
  simp only [runFrom_add, runFrom_one]
  rw [step_validity, step_of_state rfl]
  refine Cfg.ext ?_ ?_ (funext fun i => ?_) (funext fun i => ?_) ?_ <;>
    (try fin_cases i) <;>
    simp [machine, tapesCfg, Cfg.withState, Cfg.workTapeSymbols, Action.apply, tapeOfList,
      List.append_assoc]

/-- A successful endpoint appends both flags and the entire binary index, scanning that index
once and leaving its head at the final blank. -/
theorem runsBetween_found (input word out : List Bool) :
    RunsBetween machine (tapesCfg input ![[true, true], word] 0 0 out)
      (tapesCfg input ![[true, true], word] 0 ![2, word.length] (out ++ [true, true] ++ word))
      (word.length + 3) (2 * (word.length + 4)) := by
  have hcopy := runsBetween_copyIndex input [true, true] word (out ++ [true, true])
  have hstep : machine.step
      ((tapesCfg input ![[true, true], word] 0 ![1, 0] (out ++ [true])).withState (some .found)) =
      (tapesCfg input ![[true, true], word] 0 ![2, 0] (out ++ [true, true])).withState
        (some .copy) := by
    rw [step_of_state rfl]
    refine Cfg.ext ?_ ?_ (funext fun i => ?_) (funext fun i => ?_) ?_ <;>
      (try fin_cases i) <;>
      simp [machine, tapesCfg, Cfg.withState, Cfg.workTapeSymbols, Action.apply, tapeOfList,
        List.append_assoc]
  apply RunsBetween.of_runFrom
  rw [show machine.q₀ = .validity from rfl,
    show word.length + 3 = 1 + (1 + (word.length + 1)) by omega,
    runFrom_add, runFrom_one, step_validity, runFrom_add, runFrom_one, hstep]
  change machine.runFrom
    (((tapesCfg input ![[true, true], word] 0 ![2, 0] (out ++ [true, true])).withState
      (some copyIndex.q₀)).mapState (Option.map fun _ => .copy)) _ = _
  rw [runFrom_copy, hcopy.1]
  rfl

end Turing.MultiTapeTM.ScheduleEndpointAnswer

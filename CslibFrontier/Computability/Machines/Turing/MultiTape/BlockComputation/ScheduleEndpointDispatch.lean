/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointOutput
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointSelector
import Mathlib.Tactic.FinCases

/-!
# Runtime dispatch of native schedule endpoint queries

The first six tapes have the serialized endpoint machine's layout, and tape six holds the bounded
unary tag produced by the selector preparer. One finite machine per fixed tape count dispatches
to the selected work head and port. Invalid selectors append the invalid-answer code immediately;
valid selectors run the bounded endpoint and serialize its answer, including interval rejection.

The schedule and both query parameters remain runtime data. `runsBetween` supplies a clock linear
in the raw horizon and binary interval width. The final tag is preserved with its head restored;
all flags and endpoint scratch remain as specified by the selected six-tape machine. Validating
and preparing arbitrary raw words from the external record remain separate phases.
-/

public section

namespace Turing.MultiTapeTM.ScheduleEndpointDispatch

variable {k q : ℕ}

/-- The endpoint family has a trivial rejection state and each selected native controller's
own finite state type. -/
abbrev FamilyState (k : ℕ) : Option (Fin (3 * k)) → Type
  | none => Unit
  | some j => (fun {S : Type} (_ : MultiTapeTM 6 Bool S) => S)
      (ScheduleEndpointOutput.machine
        (ScheduleEndpointSelector.head j) (ScheduleEndpointSelector.port j))

instance (k : ℕ) (j : Option (Fin (3 * k))) : Finite (FamilyState k j) := by
  cases j <;> dsimp only [FamilyState] <;> infer_instance

/-- Emit the invalid-answer tag without changing any input or work tape. -/
def reject (K : ℕ) : MultiTapeTM K Bool Unit :=
  .ofTr () fun _ _ _ => ⟨0, fun _ => (none, 0), some false, none⟩

private noncomputable def family (k : ℕ) (j : Option (Fin (3 * k))) :
    MultiTapeTM 7 Bool (FamilyState k j) :=
  match j with
  | none => reject 7
  | some j => (ScheduleEndpointOutput.machine
      (ScheduleEndpointSelector.head j) (ScheduleEndpointSelector.port j)).extendTapes
        (Fin.castAddEmb 1)

/-- One native machine selects an endpoint controller from its runtime tag. The finite family
and every state type are fixed by `k`, before the schedule, selector or interval is supplied. -/
noncomputable def machine (k : ℕ) := UnaryDispatch.machine (6 : Fin 7) (family k)

/-- Six endpoint input tapes followed by the prepared bounded selector tag, all heads at zero. -/
@[expose] def initialConfig (input raw index tag out : List Bool) : Cfg 7 Bool Unit input :=
  tapesCfg input ![[], index, [], raw, [], [], tag] 0 0 out

/-- Invalid selectors preserve all initial words and append `false`. A valid selector retains
the endpoint's final six-tape layout and the unchanged tag with its head at zero. -/
@[expose] def finalConfig (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (selector interval : ℕ) : Cfg 7 Bool Unit input :=
  match ScheduleEndpointSelector.decode k selector with
  | none => initialConfig input (RawScheduleEndpoint.word σ) interval.bits
      (ScheduleEndpointSelector.word k selector) (out ++ [false])
  | some j => embed (Fin.castAddEmb 1)
      (ScheduleEndpointOutput.finalConfig input out σ
        (ScheduleEndpointSelector.head j) (ScheduleEndpointSelector.port j) interval)
      (fun _ => tapeOfList (ScheduleEndpointSelector.word k selector)) 0

/-- Rejection appends its single tag in one native transition, preserving arbitrary tape words,
head positions and previous output. -/
theorem runsBetween_reject {K : ℕ} {input : List Bool} (c : Cfg K Bool Unit input) :
    RunsBetween (reject K) c { c with output := c.output ++ [false] } 1 (2 * K) := by
  rw [Nat.mul_comm 2 K]
  apply RunsBetween.of_runFrom
  rw [runFrom_one, step_of_state rfl]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp [reject, Action.apply, Cfg.withState]

private theorem runsBetween_member (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (j : Fin (3 * k)) (interval : ℕ) (tag : List Bool) :
    RunsBetween (family k (some j))
      (initialConfig input (RawScheduleEndpoint.word σ) interval.bits tag out)
      (embed (Fin.castAddEmb 1)
        (ScheduleEndpointOutput.finalConfig input out σ
          (ScheduleEndpointSelector.head j) (ScheduleEndpointSelector.port j) interval)
        (fun _ => tapeOfList tag) 0)
      ((8 * k + 32) * q + 5 * interval.bits.length + 47)
      (6 * ((8 * k + 32) * q + 5 * interval.bits.length + 48) + 1) := by
  have h := ScheduleEndpointOutput.runsBetween input out σ
    (ScheduleEndpointSelector.head j) (ScheduleEndpointSelector.port j) interval
  have hv : viewCfg (Fin.castAddEmb 1 : Fin 6 ↪ Fin 7)
      (initialConfig input (RawScheduleEndpoint.word σ) interval.bits tag out) =
      ScheduleEndpointOutput.initialConfig input (RawScheduleEndpoint.word σ)
        interval.bits out := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;> rfl
  rw [← hv] at h
  have he := h.extendTapes (Fin.castAddEmb 1)
  have hf : embed (Fin.castAddEmb 1)
      (ScheduleEndpointOutput.finalConfig input out σ
        (ScheduleEndpointSelector.head j) (ScheduleEndpointSelector.port j) interval)
      (initialConfig input (RawScheduleEndpoint.word σ) interval.bits tag out).workTapes
      (initialConfig input (RawScheduleEndpoint.word σ) interval.bits tag out).workTapePos =
      embed (Fin.castAddEmb 1)
        (ScheduleEndpointOutput.finalConfig input out σ
          (ScheduleEndpointSelector.head j) (ScheduleEndpointSelector.port j) interval)
        (fun _ => tapeOfList tag) 0 := by
    rw [embed_castAdd, embed_castAdd]
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i z
    induction i using Fin.addCases with
    | left i => simp only [Fin.append_left]
    | right i =>
      simp only [Fin.append_right]
      fin_cases i
      simp [initialConfig, tapesCfg]
  simpa only [family, hf] using he

/-- The runtime-dispatched machine emits the exact tagged answer to the total semantic query,
for arbitrary selectors and interval indices on a represented raw schedule. -/
theorem finalConfig_output_query (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (selector interval : ℕ) :
    (finalConfig input out σ selector interval).output =
      out ++ ScheduleEndpointAnswer.encAnswer (ScheduleEndpointQuery.query k
        ⟨RawScheduleEndpoint.word σ, selector, interval⟩) := by
  cases hd : ScheduleEndpointSelector.decode k selector with
  | none =>
    have hs := (ScheduleEndpointSelector.decode_eq_none_iff k selector).mp hd
    have hq : ScheduleEndpointQuery.query k
        ⟨RawScheduleEndpoint.word σ, selector, interval⟩ = none := by
      apply ScheduleEndpointQuery.query_eq_none_of_not_valid
      simp [ScheduleEndpointQuery.valid, show ¬selector < 3 * k by omega]
    simp [finalConfig, hd, hq, initialConfig, tapesCfg, ScheduleEndpointAnswer.encAnswer]
  | some j =>
    have hs := (ScheduleEndpointSelector.decode_eq_some_iff k selector j).mp hd
    simp only [finalConfig, hd]
    change (ScheduleEndpointOutput.finalConfig input out σ
      (ScheduleEndpointSelector.head j) (ScheduleEndpointSelector.port j) interval).output = _
    rw [ScheduleEndpointOutput.finalConfig_output_query, ScheduleEndpointSelector.head_port, ← hs]

/-- Actual finite family dispatch plus bounded native endpoint computation and output.
Selector and interval values occur only in runtime data; the overhead is additive and linear
in the schedule horizon and interval width, even for out-of-range queries or `k = 0`. -/
theorem runsBetween (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (selector interval : ℕ) :
    RunsBetween (machine k)
      (initialConfig input (RawScheduleEndpoint.word σ) interval.bits
        (ScheduleEndpointSelector.word k selector) out)
      (finalConfig input out σ selector interval)
      ((8 * k + 32) * q + 5 * interval.bits.length + 6 * k + 49)
      (7 * ((8 * k + 32) * q + 5 * interval.bits.length + 6 * k + 50)) := by
  let tag := ScheduleEndpointSelector.word k selector
  cases hd : ScheduleEndpointSelector.decode k selector with
  | none =>
    have hr := runsBetween_reject
      (initialConfig input (RawScheduleEndpoint.word σ) interval.bits tag out)
    have hu := UnaryDispatch.runsBetween (6 : Fin 7) (family k) input out
      ![[], interval.bits, [], RawScheduleEndpoint.word σ, [], [], tag] none
      (by simp [tag, ScheduleEndpointSelector.word, hd, UnaryDispatch.code]) hr
    have hb := hu.mono
      (show 2 * (UnaryDispatch.code (none : Option (Fin (3 * k)))).length + 2 + 1 ≤
        (8 * k + 32) * q + 5 * interval.bits.length + 6 * k + 49 by
        simp [UnaryDispatch.code])
      (show 7 * (2 * (UnaryDispatch.code (none : Option (Fin (3 * k)))).length + 2 + 1 + 1) ≤
        7 * ((8 * k + 32) * q + 5 * interval.bits.length + 6 * k + 50) by
        simp only [UnaryDispatch.code, List.length_nil]
        omega)
    simpa only [machine, finalConfig, hd, initialConfig, tapesCfg, tag] using hb
  | some j =>
    have hr := runsBetween_member input out σ j interval tag
    have hu := UnaryDispatch.runsBetween (6 : Fin 7) (family k) input out
      ![[], interval.bits, [], RawScheduleEndpoint.word σ, [], [], tag] (some j)
      (by simp [tag, ScheduleEndpointSelector.word, hd]) hr
    have htag : (UnaryDispatch.code (some j)).length ≤ 3 * k := UnaryDispatch.length_code_le _
    have hb := hu.mono
      (show 2 * (UnaryDispatch.code (some j)).length + 2 +
        ((8 * k + 32) * q + 5 * interval.bits.length + 47) ≤
        (8 * k + 32) * q + 5 * interval.bits.length + 6 * k + 49 by omega)
      (show 7 * (2 * (UnaryDispatch.code (some j)).length + 2 +
        ((8 * k + 32) * q + 5 * interval.bits.length + 47) + 1) ≤
        7 * ((8 * k + 32) * q + 5 * interval.bits.length + 6 * k + 50) by omega)
    simpa only [machine, finalConfig, hd, initialConfig, tag] using hb

end Turing.MultiTapeTM.ScheduleEndpointDispatch

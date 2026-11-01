/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplaySupplierInit
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayGateCorrect
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayProvidersCorrect

/-!
# Correctness of checked local gate preparation

Successful canonical parsing of every assignment label initializes exactly the functional
block gate's entering control/window and schedule metadata. Running that prepared supplier for
one block emits precisely the existing deterministic block gate's encoded result, including
motion-check FAIL. Rejected parsing selects an explicit paid rejection buffer.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Supplier

open MultiTapeTM

variable {k s : ℕ} {Q : Type}

/-- A rejected label combination retains the actual previous-label word. -/
theorem prepare_eq_of_combined_none (e : Q ≃ Fin s) (N b σ i limit counter stride : ℕ)
    (hcombined : Providers.Labels.combine e (b, ScheduleRead.providerMap k (σ, i),
      (Assignments.labels k (limit, counter, stride, Encoding.width k s b)).1,
      (Assignments.labels k (limit, counter, stride, Encoding.width k s b)).2) = none) :
    prepare (k := k) e (N, b, σ, i, limit, counter, stride) =
      .inl (Assignments.labels k (limit, counter, stride, Encoding.width k s b)).1 := by
  simp only [prepare, hcombined]

/-- A successful combination supplies the exact native replay state with computed scheduling
metadata; no prepared semantic window is supplied by an oracle. -/
theorem prepare_eq_of_combined_some (e : Q ≃ Fin s) (N b σ i limit counter stride : ℕ)
    (raw : RawResult k Q)
    (hcombined : Providers.Labels.combine e (b, ScheduleRead.providerMap k (σ, i),
      (Assignments.labels k (limit, counter, stride, Encoding.width k s b)).1,
      (Assignments.labels k (limit, counter, stride, Encoding.width k s b)).2) = some raw) :
    prepare (k := k) e (N, b, σ, i, limit, counter, stride) =
      let (positive, negative) := ScheduleRead.origin k 0 (σ, i)
      .inr ((positive, negative, ScheduleRead.fullrow k (σ, i)),
        Load.load (N, b, (positive, negative), raw)) := by
  simp only [prepare, hcombined]

/-- When the previous and every provider label pass canonical parsing, the prepared supplier
emits exactly the encoded existing block gate. Failed head-motion validation still emits FAIL.
The premise includes providers whose windows are unused by the current schedule. -/
theorem finish_prepare_of_parses {q : ℕ} (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (b : ℕ) [NeZero b] (σ : ℕ) (i : Fin q)
    (limit counter stride : ℕ) (previous : RawResult k Q)
    (providers : Providers.ProviderValues k Q)
    (hprevious : Encoding.NativeChecked.parse e
      (b, (Assignments.labels k (limit, counter, stride, Encoding.width k s b)).1) =
        some previous)
    (hproviders : ∀ h δ, Encoding.NativeChecked.parse e
      (b, (Assignments.labels k (limit, counter, stride, Encoding.width k s b)).2 h δ) =
        some (providers h δ)) :
    (CheckedGate.machine M e).finish ((CheckedGate.machine M e).runFrom w
      (prepare e (w.length, b, σ, i, limit, counter, stride)) b) =
      List.ofFn (Encoding.encode e
        (gate (MultiTapePTM.ofDeterministic M) w b
          (scheduleOfNat k q σ) i (some (previous.toView b))
          (fun h δ => some ((providers h δ).toView b)))) := by
  classical
  let schedule := scheduleOfNat k q σ
  let raw := Providers.combine (b, Providers.portMap schedule i, previous, providers)
  have hcombined : Providers.Labels.combine e (b, ScheduleRead.providerMap k (σ, i),
      (Assignments.labels k (limit, counter, stride, Encoding.width k s b)).1,
      (Assignments.labels k (limit, counter, stride, Encoding.width k s b)).2) = some raw := by
    rw [ScheduleRead.providerMap_eq_portMap]
    exact Providers.Labels.combine_of_parse e b (Providers.portMap schedule i) _ _
      previous providers hprevious hproviders
  have hp := Load.canonical_of_checked_some e b _ previous hprevious
  have hps (h : Fin k) (δ : Fin 3) :=
    Load.canonical_of_checked_some e b _ (providers h δ) (hproviders h δ)
  have hcanonical : Load.CanonicalWindows b raw :=
    Providers.canonical_combine b (Providers.portMap schedule i) previous providers hp hps
  have hview : raw.toView b =
      ((previous.toView b).1, enteringWindow (MultiTapePTM.ofDeterministic M) b schedule i
        (fun h δ => some ((providers h δ).toView b))) :=
    Providers.toView_combine_enteringWindow (MultiTapePTM.ofDeterministic M) b schedule i
      previous providers hp hps
  rcases horigin : ScheduleRead.origin k 0 (σ, i) with ⟨positive, negative⟩
  have hinput : scheduleBlock schedule i none = (positive : ℤ) - negative := by
    have ho := ScheduleRead.origin_sub_eq_scheduleBlock (k := k) (q := q)
      σ i.val i.isLt.le none
    change (let (p, n) := ScheduleRead.origin k 0 (σ, i.val);
      (p : ℤ) - n = scheduleBlock schedule i none) at ho
    rw [horigin] at ho
    exact ho.symm
  rw [prepare_eq_of_combined_some e w.length b σ i limit counter stride raw hcombined,
    horigin, ScheduleRead.fullrow_eq_scheduleOfNat, CheckedGate.runFrom_inr]
  change (Gate.machine M e).finish ((Gate.machine M e).runFrom w
    ((positive, negative, schedule i), Load.load (w.length, b, (positive, negative), raw)) b) = _
  have hf := Gate.finish_runFrom_load M e w b positive negative (schedule i) raw
    hcanonical (scheduleBlock schedule i) hinput
  dsimp only at hf
  rw [hview] at hf
  simpa [gate, MultiTapeTM.stepCoins_ofDeterministic, schedule] using hf

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Supplier

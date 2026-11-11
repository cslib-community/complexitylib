/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplaySupplierCorrect
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayProviderLabelsCorrect

/-!
# Every-clock storage bound for the checked gate supplier

Rejected initialization retains only a slice of one actual assignment word. Accepted
initialization has canonical three-block windows and hence satisfies the native replay bound
at every clock. Scheduling context is charged explicitly; the original input remains on the
query input. The result holds for every numeric schedule and interval, without a promise that
metadata denotes a correct schedule.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Supplier

open MultiTapeTM MultiTapeNTM.ChoiceTable

variable {k s : ℕ} {Q : Type} [Finite Q]

/-- The actual previous-label slice never exceeds the requested label width. -/
theorem length_previous_label_le (limit counter stride b : ℕ) :
    ((Assignments.labels k ⟨limit, counter, stride, Encoding.width k s b⟩).previous).length ≤
      Encoding.width k s b := by
  change (Cslib.TreeEval.Ary.Packed.AssignmentLabels.label
    (limit, counter, stride, Encoding.width k s b, 0)).length ≤ _
  simp only [Cslib.TreeEval.Ary.Packed.AssignmentLabels.label, List.length_take]
  exact Nat.min_le_left _ _

/-- Native supplier storage from explicit label words is bounded at every clock, including
rejected words and clocks after halting. The previous word's length pays for the rejection
branch. -/
theorem length_runFrom_prepareWords_le (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (b : ℕ) [NeZero b] (σ i t : ℕ) (words : Assignments.Words k) :
    let (positive, negative) := ScheduleRead.origin k 0 (σ, i)
    (CheckedGate.encState ((CheckedGate.machine M e).runFrom w
      (prepareWords e (w.length, b, σ, i, words)) t)).length ≤
      (words.previous.length + 1) +
        (2 * (Gate.encContext
          (positive, negative, ScheduleRead.fullrow k (σ, i))).length + 2 +
          1024 * (k + 1) * (b + Nat.log2 w.length + Nat.card (Option Q) +
            Nat.card OutputTrack + 1)) := by
  let ports := ScheduleRead.providerMap k (σ, i)
  rcases horigin : ScheduleRead.origin k 0 (σ, i) with ⟨positive, negative⟩
  dsimp only
  cases hc : Providers.Labels.combine e (b, ports, words.previous, words.providers) with
  | none =>
    rw [prepareWords_eq_of_combined_none e w.length b σ i words hc,
      CheckedGate.runFrom_inl]
    simp only [CheckedGate.encState, encSum_inl, List.length_cons, encBits_apply]
    omega
  | some raw =>
    have hcanonical := Providers.Labels.canonical_of_combine_some e b ports
      words.previous words.providers raw hc
    rw [prepareWords_eq_of_combined_some e w.length b σ i words raw hc,
      horigin, CheckedGate.runFrom_inr]
    simp only [CheckedGate.encState, encSum_inr, List.length_cons]
    have hbound := Gate.length_runFrom_load_le M e w b positive negative
      (ScheduleRead.fullrow k (σ, i)) raw hcanonical
      (fun _ => (positive : ℤ) - negative) rfl t
    omega

/-- Native supplier storage is bounded at every clock, including rejected assignments and
clocks after halting. The extra label-width term pays for the rejection branch. -/
theorem length_runFrom_prepare_le (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (b : ℕ) [NeZero b] (σ i limit counter stride t : ℕ) :
    let (positive, negative) := ScheduleRead.origin k 0 (σ, i)
    (CheckedGate.encState ((CheckedGate.machine M e).runFrom w
      (prepare e (w.length, b, σ, i, limit, counter, stride)) t)).length ≤
      (Encoding.width k s b + 1) +
        (2 * (Gate.encContext
          (positive, negative, ScheduleRead.fullrow k (σ, i))).length + 2 +
          1024 * (k + 1) * (b + Nat.log2 w.length + Nat.card (Option Q) +
            Nat.card OutputTrack + 1)) := by
  have h := length_runFrom_prepareWords_le M e w b σ i t
    (Assignments.labels k ⟨limit, counter, stride, Encoding.width k s b⟩)
  have hw := length_previous_label_le (k := k) (s := s) limit counter stride b
  rcases horigin : ScheduleRead.origin k 0 (σ, i) with ⟨positive, negative⟩
  rw [horigin] at h
  exact h.trans (by omega)

omit [Finite Q] in
/-- Every call prepared from explicit label words is halted by its requested replay duration.
Rejected words halt immediately, while successful initialization uses the existing replay
counter. -/
theorem halted_runFrom_prepareWords (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (N b σ i : ℕ) (words : Assignments.Words k) :
    (CheckedGate.machine M e).halted ((CheckedGate.machine M e).runFrom w
      (prepareWords e (N, b, σ, i, words)) b) = true := by
  cases hc : Providers.Labels.combine e (b, ScheduleRead.providerMap k (σ, i),
      words.previous, words.providers) with
  | none =>
    rw [prepareWords_eq_of_combined_none e N b σ i words hc, CheckedGate.runFrom_inl]
    rfl
  | some raw =>
    rw [prepareWords_eq_of_combined_some e N b σ i words raw hc]
    rcases ScheduleRead.origin k 0 (σ, i) with ⟨positive, negative⟩
    rw [CheckedGate.runFrom_inr]
    exact Gate.halted_runFrom_load M e w N b positive negative _ raw

omit [Finite Q] in
/-- Every prepared local call is halted by its requested replay duration. Rejected labels
halt immediately, while successful initialization uses the existing replay counter. -/
theorem halted_runFrom_prepare (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (N b σ i limit counter stride : ℕ) :
    (CheckedGate.machine M e).halted ((CheckedGate.machine M e).runFrom w
      (prepare e (N, b, σ, i, limit, counter, stride)) b) = true :=
  halted_runFrom_prepareWords M e w N b σ i _

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Supplier

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.PMF.RecordedProcess
import Mathlib.Tactic

/-!
# Actual conditional private output and a bill retained after divergence

The first step charges six or eight according to a fair private bit. The next step silently
loses the hidden state, but appends a zero receipt and keeps the earlier invoice.
The constructed response/output laws must preserve both observations.
-/

noncomputable section
open Cslib.Probability
open scoped ENNReal NNReal
namespace CslibFrontierTests.RecordedProcess

/-- An unbounded receipt ledger and optional private state. -/
structure State where
  /-- Newest-first receipts collected since entry. -/
  records : List ℕ
  /-- Optional private output, absent after divergence. -/
  hidden : Option Bool

/-- Correlated invoice, with mean seven. -/
def invoice (bit : Bool) : ℕ := if bit then 8 else 6

/-- A private fair output after one paid response, followed by silent divergence. -/
def step (state : State) : PMF State :=
  if state.records = [] then
    (PMF.uniformOfFintype Bool).map (fun b => (⟨[invoice b], some b⟩ : State))
  else PMF.pure ⟨0 :: state.records, none⟩

private theorem step_records (state next : State) (hn : next ∈ (step state).support) :
    ∃ x, next.records = x :: state.records := by
  by_cases he : state.records = []
  · simp only [step, he, ite_true, PMF.mem_support_map_iff] at hn
    obtain ⟨b, _, rfl⟩ := hn
    exact ⟨invoice b, by simp [he]⟩
  · simp only [step, he, ite_false, PMF.mem_support_pure_iff] at hn
    subst next
    exact ⟨0, rfl⟩

/-- The first actual state law keeps the hidden fair coin. -/
theorem first_law : ObservedProcess.stateLaw step 1 (⟨[], none⟩ : State) =
    (PMF.uniformOfFintype Bool).map (fun b => (⟨[invoice b], some b⟩ : State)) := by
  simp [ObservedProcess.stateLaw, step]

/-- Conditional extraction reproduces the private fair output with its paid receipt. -/
example :
    ((PMF.seqProcess (fun _ h => RecordedProcess.response step State.records
      (⟨[], none⟩ : State) 0 (PMF.seqHistory h)) 1).map PMF.seqHistory).bind (fun h =>
        (RecordedProcess.output step State.records (⟨[], none⟩ : State) State.hidden 1 h).map
          (fun out => (h, out))) =
      (PMF.uniformOfFintype Bool).map (fun b => ([invoice b], some b)) := by
  rw [RecordedProcess.joint_law step State.records (⟨[], none⟩ : State) 0 rfl step_records]
  rw [first_law, PMF.map_comp]
  rfl

/-- Losing the final hidden state leaves the invoice in the complete record law. -/
theorem second_law : ObservedProcess.stateLaw step 2 (⟨[], none⟩ : State) =
    (PMF.uniformOfFintype Bool).map (fun b => (⟨[0, invoice b], none⟩ : State)) := by
  simp [ObservedProcess.stateLaw, step, Function.comp_def]
  rfl

/-- Divergence is an optional output, separate from the retained bill. -/
example :
    ((PMF.seqProcess (fun _ h => RecordedProcess.response step State.records
      (⟨[], none⟩ : State) 0 (PMF.seqHistory h)) 2).map PMF.seqHistory).bind (fun h =>
        (RecordedProcess.output step State.records (⟨[], none⟩ : State) State.hidden 2 h).map
          (fun out => (h, out))) =
      (PMF.uniformOfFintype Bool).map (fun b => ([0, invoice b], none)) := by
  rw [RecordedProcess.joint_law step State.records (⟨[], none⟩ : State) 0 rfl step_records,
    second_law, PMF.map_comp]
  rfl

/-- The actual expected invoice stays seven after the final optional state is lost. -/
example :
    (∑' h, PMF.seqProcess (fun _ h => RecordedProcess.response step State.records
      (⟨[], none⟩ : State) 0 (PMF.seqHistory h)) 2 h *
        (List.map (fun x : ℕ => (x : ℝ≥0∞)) (PMF.seqHistory h)).sum) = 7 := by
  rw [RecordedProcess.expected_sum step State.records (⟨[], none⟩ : State) 0 rfl step_records,
    second_law, PMF.tsum_map_mul]
  norm_num [tsum_fintype, Fintype.sum_bool, PMF.uniformOfFintype_apply, invoice]
  have he : (2 : ℝ≥0)⁻¹ * 8 + 2⁻¹ * 6 = 7 := by norm_num
  have hc := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) he
  simpa only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_inv_two,
    ENNReal.coe_ofNat] using hc

end CslibFrontierTests.RecordedProcess

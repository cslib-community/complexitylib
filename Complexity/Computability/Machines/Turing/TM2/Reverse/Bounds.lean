/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.TM2.Reverse.Execution
public import Complexity.Computability.Machines.Turing.TM2.Reverse.Cleanup

/-!
# Resource bounds for the reverse TM2 compiler

Input storage is counted, whereas the native work-space convention excludes read-only input and
write-only output. Raw work-stack lengths are bounded by the cells visited by the source heads.
The space estimates therefore apply independently of the source runtime.

## Main results

* `Turing.MultiTapeTM.ToTM2.outputsInTime`: output correspondence with a linear simulation clock.
* `Turing.MultiTapeTM.ToTM2.reachable_stack_bound`: a bound on every target configuration.
-/

public section

namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

private def stackEquiv (k : ℕ) : Stack k ≃ ((Bool ⊕ Bool) ⊕ Fin k × Bool) where
  toFun
    | .input => .inl (.inl false)
    | .before => .inl (.inl true)
    | .output => .inl (.inr false)
    | .reversed => .inl (.inr true)
    | .work i b => .inr (i, b)
  invFun
    | .inl (.inl false) => .input
    | .inl (.inl true) => .before
    | .inl (.inr false) => .output
    | .inl (.inr true) => .reversed
    | .inr (i, b) => .work i b
  left_inv s := by cases s with | work i b => cases b <;> rfl | _ => rfl
  right_inv s := by
    rcases s with ((b | b) | ⟨i, b⟩) <;> cases b <;> rfl

private theorem sum_stack (f : Stack k → ℕ) :
    ∑ s, f s = f .input + f .before + f .output + f .reversed +
      ∑ i, (f (.work i false) + f (.work i true)) := by
  rw [← (stackEquiv k).symm.sum_comp f]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, stackEquiv,
    Equiv.symm_mk, Equiv.coe_fn_mk]
  simp [add_comm, add_assoc]

/-- Stack storage at a source-step boundary, including the input and output. -/
private theorem totalStackLength_encode (d : Data k State) :
    totalStackLength (encode d) = d.input.left.length + d.input.right.length +
      (∑ i, ((d.work i).left.length + (d.work i).right.length)) + d.output.length := by
  rw [totalStackLength, sum_stack]
  simp only [encode, store, List.length_nil, List.length_reverse]
  omega

/-- A native space bound controls every encoded source configuration. -/
private theorem totalStackLength_run_le (tm : MultiTapeTM k Bool State) {input output : List Bool}
    {s : ℕ} (hc : tm.Computes input output) (hs : tm.RunsInSpace input s) (t : ℕ) :
    totalStackLength (encode (Data.run tm input t)) ≤ input.length + s + output.length := by
  rw [totalStackLength_encode]
  have hi := Data.input_length_run tm input t
  have hw := Data.sum_work_sides_run_le hs t
  have ho := Data.output_length_run_le_of_computes hc t
  omega

/-- Auxiliary storage excludes the accumulated output. -/
private theorem auxiliaryLength_store (d : Data k State) :
    auxiliaryLength (store d) = d.input.left.length + d.input.right.length +
      ∑ i, ((d.work i).left.length + (d.work i).right.length) := by
  have h := totalStackLength_encode d
  rw [totalStackLength_eq] at h
  simp only [encode, store, List.length_reverse, List.length_nil, Nat.add_zero] at h
  omega

private theorem auxiliaryLength_run_time_le (tm : MultiTapeTM k Bool State)
    (input : List Bool) (t : ℕ) :
    auxiliaryLength (store (Data.run tm input t)) ≤ input.length + k * (t + 1) := by
  rw [auxiliaryLength_store, Data.input_length_run]
  have hw := Data.sum_work_sides_run_add_eq_space tm input t
  have hs : (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg input) t).space ≤ k * t + k :=
    (MultiTapeNTM.RunPath.space_le_mul_time_add_one _).trans_eq (Nat.mul_add_one _ _)
  simp only [Nat.mul_add, Nat.mul_one]
  omega

/-- Once the source has halted, its raw output is the complete computed output. -/
private theorem output_run_of_halt (tm : MultiTapeTM k Bool State) {input output : List Bool}
    (hc : tm.Computes input output) {t : ℕ} (ht : (Data.run tm input t).state = none) :
    (Data.run tm input t).output = output := by
  obtain ⟨u, hu, hout⟩ := hc
  have hou : (Data.run tm input u).output = output := (Data.output_run tm input u).trans hout
  rcases le_total t u with htu | hut
  · rwa [Data.run_eq_of_halt tm input htu ht] at hou
  · rw [Data.run_eq_of_halt tm input hut ((Data.state_run tm input u).trans hu), hou]

/-- Every target configuration counts the stored input and output as well as native work space.
The estimate holds for arbitrary padded target time, independently of the source runtime. -/
theorem reachable_stack_bound [Fintype State] (tm : MultiTapeTM k Bool State)
    {input output : List Bool} {s : ℕ} (hc : tm.Computes input output)
    (hs : tm.RunsInSpace input s) (i : ℕ) :
    totalStackLength ((TM2.stepTotal (machine tm.q₀ tm.tr).m)^[i]
      (initList (machine tm.q₀ tm.tr) input)) ≤ input.length + s + output.length := by
  have hc' := hc
  obtain ⟨t, ht, _⟩ := hc'
  obtain ⟨u, _, hu⟩ := exists_haltsAt ht
  have hraw : (Data.run tm input u).state = none := (Data.state_run tm input u).trans hu.halted
  by_cases hi : i ≤ u
  · rw [iterate_encode tm input hu hi]
    exact totalStackLength_run_le tm hc hs i
  · have heq : i = (i - (u + 1)) + (u + 1) := by omega
    have hadd :
        (TM2.stepTotal (machine tm.q₀ tm.tr).m)^[(i - (u + 1)) + (u + 1)]
            (initList (machine tm.q₀ tm.tr) input) =
          (TM2.stepTotal (machine tm.q₀ tm.tr).m)^[i - (u + 1)]
            (TM2.stepTotal (machine tm.q₀ tm.tr).m
              ((TM2.stepTotal (machine tm.q₀ tm.tr).m)^[u]
                (initList (machine tm.q₀ tm.tr) input))) :=
      (Function.iterate_add_apply _ (i - (u + 1)) (u + 1) _).trans
        (congrArg (TM2.stepTotal (machine tm.q₀ tm.tr).m)^[i - (u + 1)]
          (Function.iterate_succ_apply' _ u _))
    rw [heq, hadd, iterate_encode tm input hu le_rfl, stepTotal_encode_halt tm _ hraw]
    exact (cleanup_stack_bound tm.q₀ tm.tr _ rfl _).trans (totalStackLength_run_le tm hc hs u)

/-- A native computation is simulated with a linear clock, including clearing every auxiliary
stack, reversing its output and restoring Mathlib's canonical halting control. -/
def outputsInTime [Fintype State] (tm : MultiTapeTM k Bool State)
    {input output : List Bool} {t : ℕ} (hc : tm.Computes input output)
    (ht : tm.RunsInTime input t) :
    TM2OutputsInTime (machine tm.q₀ tm.tr) input (some output)
      (input.length + (k + 1) * (t + 1) + output.length + 3) := by
  classical
  let hex := exists_haltsAt (runsInTime_iff_halted.mp ht)
  let u := hex.choose
  have hu := hex.choose_spec
  let d := Data.run tm input u
  have hd : d.state = none := (Data.state_run tm input u).trans hu.2.halted
  have ho : d.output = output := output_run_of_halt tm hc hd
  let cfg : (machine tm.q₀ tm.tr).Cfg :=
    ⟨some .clean, control d d.input.right.head? false, store d⟩
  have hstep : (machine tm.q₀ tm.tr).step (encode d) = some cfg := step_encode_halt tm d hd
  have hclean := cleanupEvals tm.q₀ tm.tr cfg rfl
  have htail := StateTransition.EvalsToInTime.cons hstep hclean
  change StateTransition.EvalsToInTime (machine tm.q₀ tm.tr).step (encode d)
    (some (haltList (machine tm.q₀ tm.tr) (d.output.reverse.reverse ++ [])))
    (auxiliaryLength (store d) + d.output.reverse.length + 2 + 1) at htail
  have htail' : StateTransition.EvalsToInTime (machine tm.q₀ tm.tr).step (encode d)
      (some (haltList (machine tm.q₀ tm.tr) output))
      (auxiliaryLength (store d) + d.output.length + 3) := by
    simpa only [cfg, store, List.reverse_reverse, List.append_nil, List.length_reverse,
      Nat.add_assoc, Nat.reduceAdd, ho] using htail
  have hresult := StateTransition.EvalsToInTime.trans (machine tm.q₀ tm.tr).step
    u (auxiliaryLength (store d) + d.output.length + 3) _ _ _
    (prefixEvals tm input hu.2 le_rfl) htail'
  refine hresult.mono ?_
  have ha := auxiliaryLength_run_time_le tm input u
  have hm : k * (u + 1) ≤ k * (t + 1) := Nat.mul_le_mul_left k (by omega)
  dsimp only [d] at *
  rw [ho]
  simp only [Nat.add_mul, Nat.one_mul]
  omega

/-- Terminating native computation yields terminating canonical TM2 computation. -/
def outputs [Fintype State] (tm : MultiTapeTM k Bool State) {input output : List Bool}
    (hc : tm.Computes input output) : TM2Outputs (machine tm.q₀ tm.tr) input (some output) :=
  (outputsInTime tm hc (runsInTime_iff_halted.mpr hc.choose_spec.1)).toTM2Outputs

end

end Turing.MultiTapeTM.ToTM2

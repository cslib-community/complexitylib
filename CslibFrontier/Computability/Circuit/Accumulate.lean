/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.CompositionDepth
public import CslibFrontier.Computability.Circuit.FanIn
public import CslibFrontier.Computability.Circuit.Simulation

/-!
# Accumulating circuits

A sequence of circuits `step r : Circuit σ (K₀ + w * r) (K₀ + w * r + w)` composes into
`Circuit.accumulate step R : Circuit σ K₀ (K₀ + w * R)`: round `r` reads every value produced so
far and appends `w` new ones. When each round keeps its inputs and appends a block `sel r y`
computed from the values `y` so far, the output keeps the input
(`Circuit.eval_accumulate_input`), a longer accumulation extends a shorter one
(`Circuit.eval_accumulate_prefix`), and the block of round `r` is `sel r` of the output after `r`
rounds (`Circuit.eval_accumulate_block`). Size, weighted cost, weighted depth and fan-in add up or
are inherited round by round.

Unlike `Circuit.iterate`, the width grows with every round, so later rounds can read the blocks of
all earlier ones.

## Main definitions

* `Cslib.Circuits.Circuit.accumulate`: `R` rounds composed in sequence, each appending `w` values.

## Main results

* `Cslib.Circuits.Circuit.eval_accumulate_input`, `Cslib.Circuits.Circuit.eval_accumulate_prefix`,
  `Cslib.Circuits.Circuit.eval_accumulate_block`: the semantics of an accumulation of rounds that
  keep their inputs.
* `Cslib.Circuits.Circuit.size_accumulate`, `Cslib.Circuits.Circuit.cost_program_accumulate`,
  `Cslib.Circuits.Circuit.depthWith_accumulate_le`,
  `Cslib.Circuits.Circuit.fanInAtMost_accumulate`: the measures of an accumulation.
-/

public section

namespace Cslib.Circuits

variable {σ : Signature} {K₀ w : ℕ}

/-- `R` rounds composed in sequence: round `r` maps the `K₀ + w * r` values produced so far to
`K₀ + w * r + w` values. A wiring cast realigns `K₀ + w * r + w` with `K₀ + w * (r + 1)`; it adds
no gates. -/
def Circuit.accumulate (step : ∀ r, Circuit σ (K₀ + w * r) (K₀ + w * r + w)) :
    (R : ℕ) → Circuit σ K₀ (K₀ + w * R)
  | 0 => Circuit.wiring σ (Fin.cast (by simp))
  | R + 1 =>
    (Circuit.wiring σ (Fin.cast (by rw [Nat.mul_succ, Nat.add_assoc]))).comp
      ((step R).comp (Circuit.accumulate step R))

namespace Circuit

variable (step : ∀ r, Circuit σ (K₀ + w * r) (K₀ + w * r + w))

/-- The size of an accumulation is the sum of the sizes of its rounds. -/
@[simp] theorem size_accumulate (R : ℕ) :
    (accumulate step R).size = ∑ r ∈ Finset.range R, (step r).size := by
  induction R with
  | zero => rfl
  | succ R ih => rw [accumulate, size_comp, size_comp, ih, Finset.sum_range_succ]; rfl

/-- The weighted cost of an accumulation is the sum of those of its rounds. -/
theorem cost_program_accumulate (cost : σ.Op → ℕ) (R : ℕ) :
    (accumulate step R).program.cost cost = ∑ r ∈ Finset.range R, (step r).program.cost cost := by
  induction R with
  | zero => rfl
  | succ R ih =>
    rw [accumulate, cost_program_comp, cost_program_comp, ih, Finset.sum_range_succ,
      cost_program_wiring, Nat.add_zero]

/-- Rounds of weighted depth at most `D` accumulate to weighted depth at most `R * D`. -/
theorem depthWith_accumulate_le (cost : σ.Op → ℕ) {D R : ℕ}
    (h : ∀ r < R, (step r).depthWith cost ≤ D) : (accumulate step R).depthWith cost ≤ R * D := by
  induction R with
  | zero => simp [accumulate]
  | succ R ih =>
    rw [accumulate]
    refine (depthWith_comp_le _ _ _).trans ?_
    rw [depthWith_wiring, Nat.zero_add]
    refine (depthWith_comp_le _ _ _).trans ?_
    rw [Nat.succ_mul, Nat.add_comm (R * D)]
    exact Nat.add_le_add (h R R.lt_succ_self) (ih fun r hr => h r (hr.trans R.lt_succ_self))

/-- Rounds of fan-in at most `f` accumulate to fan-in at most `f`. -/
theorem fanInAtMost_accumulate {f R : ℕ} (h : ∀ r < R, (step r).FanInAtMost f) :
    (accumulate step R).FanInAtMost f := by
  induction R with
  | zero => exact fanInAtMost_wiring _ _
  | succ R ih =>
    exact (fanInAtMost_wiring _ _).comp
      ((h R R.lt_succ_self).comp (ih fun r hr => h r (hr.trans R.lt_succ_self)))

section eval

private theorem append_of_val_eq {α : Type*} {m n : ℕ} (u : Fin m → α) (v : Fin n → α)
    (j : Fin (m + n)) (b : Fin n) (h : (j : ℕ) = m + b) : Fin.append u v j = v b := by
  rw [show j = Fin.natAdd m b from Fin.ext h, Fin.append_right]

variable {U : Type*} {I : Interpretation σ U} {step}
  {sel : ∀ r, (Fin (K₀ + w * r) → U) → Fin w → U}

/-- In an accumulation of rounds that keep their inputs and append `sel r`, the output after
`R` rounds extends the output after `r ≤ R` rounds. -/
theorem eval_accumulate_prefix (hstep : ∀ r y, (step r).eval I y = Fin.append y (sel r y))
    (x : Fin K₀ → U) {r R : ℕ} (hr : r ≤ R) (i : ℕ) (hi : i < K₀ + w * r) :
    (accumulate step R).eval I x ⟨i, hi.trans_le (by gcongr)⟩ =
      (accumulate step r).eval I x ⟨i, hi⟩ := by
  induction R, hr using Nat.le_induction with
  | base => rfl
  | succ R hrR ih =>
    have hiR : i < K₀ + w * R := hi.trans_le (by gcongr)
    rw [accumulate, eval_comp, eval_comp, eval_wiring, hstep, Function.comp_apply]
    exact (Fin.append_left _ _ ⟨i, hiR⟩).trans ih

/-- In an accumulation of rounds that keep their inputs, the output keeps the input. -/
theorem eval_accumulate_input (hstep : ∀ r y, (step r).eval I y = Fin.append y (sel r y))
    (x : Fin K₀ → U) (R : ℕ) (i : Fin K₀) :
    (accumulate step R).eval I x ⟨i, i.2.trans_le (Nat.le_add_right _ _)⟩ = x i := by
  rw [eval_accumulate_prefix hstep x (Nat.zero_le R) i (by simp)]
  rfl

/-- In an accumulation of rounds that keep their inputs and append `sel r`, the block appended in
round `r < R` is `sel r` of the output after `r` rounds. -/
theorem eval_accumulate_block (hstep : ∀ r y, (step r).eval I y = Fin.append y (sel r y))
    (x : Fin K₀ → U) {r R : ℕ} (hr : r < R) (b : Fin w) :
    (accumulate step R).eval I x
        ⟨K₀ + w * r + b, by
          have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hr)
          rw [Nat.mul_succ] at this
          omega⟩ =
      sel r ((accumulate step r).eval I x) b := by
  have hb : K₀ + w * r + b < K₀ + w * (r + 1) := by rw [Nat.mul_succ]; omega
  rw [eval_accumulate_prefix hstep x (Nat.succ_le_of_lt hr) _ hb, accumulate, eval_comp,
    eval_comp, eval_wiring, hstep, Function.comp_apply, append_of_val_eq _ _ _ b rfl]

end eval

end Circuit

end Cslib.Circuits

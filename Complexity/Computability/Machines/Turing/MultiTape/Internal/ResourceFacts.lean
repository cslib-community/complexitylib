/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
import Complexity.Computability.Machines.Turing.MultiTape.TapeLemmas
import Complexity.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Clock, output and workspace facts for plain machines

These facts are moved unchanged from the former polynomial-time bridge module. They use only
machine semantics and carry no higher computability-calculus dependency.
-/

@[expose] public section
namespace Turing.MultiTapeTM

section Machine

variable {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State}

/-- A computation within `t` steps needs no separate space bound: it visits at most `k t + k`
work-tape cells. -/
theorem ComputesInTimeAndSpace.space_linear {input output : List Symbol} {t s : ℕ}
    (h : tm.ComputesInTimeAndSpace input output t s) :
    tm.ComputesInTimeAndSpace input output t (k * t + k) :=
  ⟨h.1, h.2.1, runsInSpace_of_halted (runsInTime_iff_halted.mp h.2.1)
    ((MultiTapeNTM.RunPath.space_le_mul_time_add_one (.ofDeterministic tm _ t)).trans_eq
      (Nat.mul_add_one _ _))⟩

/-- A computation within `t` steps emits at most `t` symbols. -/
theorem ComputesInTimeAndSpace.length_output_le {input output : List Symbol} {t s : ℕ}
    (h : tm.ComputesInTimeAndSpace input output t s) : output.length ≤ t := by
  obtain ⟨⟨u, hu, rfl⟩, ht, -⟩ := h
  have ht := runsInTime_iff_halted.mp ht
  have heq : tm.runFrom (tm.initCfg input) u = tm.runFrom (tm.initCfg input) t := by
    rcases le_total u t with hut | htu
    · exact (runFrom_eq_of_halt tm _ hut hu).symm
    · exact runFrom_eq_of_halt tm _ htu ht
  rw [heq]
  simpa using tm.length_output_runFrom_le (tm.initCfg input) t

/-- **An output computed without bounds is computed within bounds**: the time at which the machine
halts, and the space it has used by then. -/
theorem Computes.exists_computesInTimeAndSpace {input output : List Symbol}
    (h : tm.Computes input output) : ∃ t s, tm.ComputesInTimeAndSpace input output t s :=
  let ⟨u, hu, _⟩ := h
  ⟨u, _, h, runsInTime_of_halted hu, runsInSpace_of_halted hu le_rfl⟩

end Machine

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- A function computable within time `t` is computable within time `t` and space `c t + c`, for
a constant `c`: the number of work tapes of the machine. -/
theorem ComputableInTimeAndSpace.exists_space_linear {t s : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s) :
    ∃ c, ComputableInTimeAndSpace f encIn encOut t fun a => c * t a + c :=
  let ⟨k, State, hfinite, tm, htm⟩ := h
  ⟨k, k, State, hfinite, tm, fun a => (htm a).space_linear⟩

/-- The encoded values of a function computable within time `t` have length at most `t`. -/
theorem ComputableInTimeAndSpace.length_le {t s : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s) (a : α) : (encOut (f a)).length ≤ t a :=
  let ⟨_, _, _, _, htm⟩ := h
  (htm a).length_output_le

end Turing.MultiTapeTM

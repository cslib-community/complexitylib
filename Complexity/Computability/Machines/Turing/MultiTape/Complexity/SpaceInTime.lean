/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace

/-!
# Time bounds for space-bounded computations

A halting computation within a space bound depending on the encoded input length can be given
a time bound depending only on that length, without increasing its space. The bound counts the
machine's readable configurations: the input head position and work-tape storage. This is the
encoded-function form of the space-to-time inclusion in cslib pull request #767, using the
configuration count of `Turing.MultiTapeTM.haltsAt_le_card`.

## Main results

* `Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_time_of_length`: replace an arbitrary
  time bound by a bound on the encoded input length.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_time_two_pow`: the time is at most
  `(n + 2) * c * 2 ^ (c * s n)` for a machine-dependent constant `c`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 4.1][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- **A computation within space `s n` halts within a time bound of `n`.** A function computable
within space `s n` on encoded inputs of length `n`, within any time bound, is computable within the
same space and the time `(n + 2) * storageBound Bool State k (s n)` of the configuration count of
its machine (`Turing.MultiTapeTM.haltsAt_le_card`), a function of `n` alone. -/
theorem ComputableInTimeAndSpace.exists_time_of_length {f : α → β} {t : α → ℕ} {s : ℕ → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t fun a => s (encIn a).length) :
    ∃ t' : ℕ → ℕ, ComputableInTimeAndSpaceOfLength f encIn encOut t' s := by
  obtain ⟨k, State, hfin, tm, htm⟩ := h
  let := Fintype.ofFinite State
  exact ⟨fun n => (n + 2) * storageBound Bool State k (s n), k, State, hfin, tm,
    fun a => (htm a).of_card⟩

/-- **The configuration-counting bound**: a function computable within space `s n` on encoded
inputs of length `n` is computable within the same space and time `(n + 2) * c * 2 ^ (c * s n)`,
for a constant `c` of the machine. -/
theorem ComputableInTimeAndSpace.exists_time_two_pow {f : α → β} {t : α → ℕ} {s : ℕ → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t fun a => s (encIn a).length) :
    ∃ c, ComputableInTimeAndSpaceOfLength f encIn encOut (fun n => (n + 2) * c * 2 ^ (c * s n))
      s := by
  obtain ⟨k, State, hfin, tm, htm⟩ := h
  let := Fintype.ofFinite State
  set c := storageBoundBase Bool State k + storageBoundExp Bool k
  have h' : tm.ComputesFunInTimeAndSpace encIn encOut f
      (fun a => ((encIn a).length + 2) * storageBound Bool State k (s (encIn a).length))
      fun a => s (encIn a).length := fun a => (htm a).of_card
  refine ⟨c, k, State, hfin, tm, h'.mono (fun a => ?_) fun _ => le_rfl⟩
  dsimp only
  rw [mul_assoc]
  refine Nat.mul_le_mul_left _ ((storageBound_le_base_mul_pow _).trans
    (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))))

end Turing.MultiTapeTM

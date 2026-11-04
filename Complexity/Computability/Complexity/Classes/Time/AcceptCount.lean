/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Time
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.AcceptCount

/-!
# Time classes through accepting choice strings

Problems in `NTIME` and `BPTIME` are decided by comparing the accepting count of a fixed
binary-choice machine (`Turing.MultiTapePTM.acceptCount`) with a threshold, at every number `τ`
of choice bits at least a linear function of the time bound. This is the normal form used by
counting simulations of nondeterministic and probabilistic time, which compute the accepting
count exactly.

* A nondeterministic decider is replayed by its choice table `Turing.MultiTapeNTM.choiceTable`,
  which encodes each choice in binary and rejects at a stuck configuration: an instance is a
  member exactly when the accepting count is positive
  (`Turing.MultiTapeNTM.DecidesInTime.mem_iff_acceptCount_choiceTable_pos`).
* A bounded-error fair-coin decider accepts a member with probability at least `2 / 3` and a
  nonmember with probability at most `1 / 3`, so an instance is a member exactly when more than
  half of the choice strings accept
  (`Turing.MultiTapePTM.DecidesWithBoundedErrorInTime.mem_iff_two_pow_lt_two_mul_acceptCount`).

Both hold for every `τ` at least the clock: a halted table ignores further bits.

## Main results

* `Turing.MultiTapeNTM.DecidesInTime.mem_iff_acceptCount_choiceTable_pos`: nondeterministic
  acceptance is a positive accepting count.
* `Turing.MultiTapePTM.DecidesWithBoundedErrorInTime.mem_iff_two_pow_lt_two_mul_acceptCount`:
  bounded-error acceptance is a strict-majority accepting count.
* `Cslib.Complexity.exists_acceptCount_of_mem_NTIME`,
  `Cslib.Complexity.exists_acceptCount_of_mem_BPTIME`: the class-level normal forms.
-/

public section

namespace Turing.MultiTapeNTM

variable {k : ℕ} {State : Type} [Finite State] {α : Type} {enc : α ↪ List Bool}

/-- **Nondeterministic acceptance is a positive accepting count.** If `ntm` decides `A` within
`t`, then `a ∈ A` exactly when some choice string of length `τ` makes the choice table accept,
for every `τ` of at least `M * t a`, where `M` is the number of actions. -/
theorem DecidesInTime.mem_iff_acceptCount_choiceTable_pos {ntm : MultiTapeNTM k Bool State}
    {A : Set α} {t : α → ℕ} (h : ntm.DecidesInTime enc A t) {a : α} {τ : ℕ}
    (hτ : Nat.card (Turing.Action k Bool State) * t a ≤ τ) :
    a ∈ A ↔ 0 < ntm.choiceTable.acceptCount (enc a) τ := by
  rw [h.mem_iff_exists_checkChoices hτ, Cslib.Complexity.acceptCount_pos_iff]
  rfl

end Turing.MultiTapeNTM

namespace Turing.MultiTapePTM

open Cslib
open scoped ENNReal

variable {k : ℕ} {State : Type} {α : Type} {enc : α ↪ List Bool}

/-- A probability of at least `2 / 3` is more than one half. -/
private theorem inv_two_lt_of_two_div_three_le {p : ℝ≥0∞} (h : 2 / 3 ≤ p) : 2⁻¹ < p := by
  refine lt_of_lt_of_le ?_ h
  rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp), ← ENNReal.div_eq_inv_mul,
    ENNReal.div_lt_iff (by simp) (by simp)]
  norm_num

/-- Two distinct outcomes have total probability at most one. -/
private theorem apply_add_apply_le_one {β : Type} (P : PMF β) {b b' : β} (hb : b ≠ b') :
    P b + P b' ≤ 1 := by
  classical
  rw [← Finset.sum_pair hb, ← P.tsum_coe]
  exact sum_le_tsum _

/-- **Bounded-error acceptance is a strict-majority accepting count.** If `machine` decides `A`
with bounded error within `t`, then `a ∈ A` exactly when more than half of the choice strings of
length `τ` accept, for every `τ` of at least `t a`. -/
theorem DecidesWithBoundedErrorInTime.mem_iff_two_pow_lt_two_mul_acceptCount
    {machine : MultiTapePTM k Bool State} {A : Set α} {t : α → ℕ}
    (h : machine.DecidesWithBoundedErrorInTime enc A t) {a : α} {τ : ℕ} (hτ : t a ≤ τ) :
    a ∈ A ↔ 2 ^ τ < 2 * machine.acceptCount (enc a) τ := by
  obtain ⟨hhalt, hprob⟩ := h a
  rw [← machine.eval_runClosed_eq_of_halted (enc a) hτ hhalt] at hprob
  rw [← half_lt_eval_runClosed_apply_iff]
  by_cases ha : a ∈ A
  · simp only [MultiTapeTM.indicator, ha] at hprob
    exact iff_of_true ha (inv_two_lt_of_two_div_three_le hprob)
  · simp only [MultiTapeTM.indicator, ha] at hprob
    refine iff_of_false ha fun htrue => ?_
    have hsum := apply_add_apply_le_one (ProbComp.eval (machine.runClosed τ (enc a)))
      (b := [true]) (b' := [false]) (by simp)
    exact absurd ((ENNReal.inv_two_add_inv_two.symm.trans_lt
      (ENNReal.add_lt_add htrue (inv_two_lt_of_two_div_three_le hprob))).trans_le hsum)
      (lt_irrefl 1)

end Turing.MultiTapePTM

namespace Cslib.Complexity

open _root_.Turing

variable {α : Type} {enc : α ↪ List Bool} {A : Set α} {t : ℕ → ℕ}

/-- **Nondeterministic time as accepting counts.** A problem in `NTIME enc t` is decided by a
fixed binary-choice machine with a binary alphabet and finitely many states: for constants `c₁`
and `c₂`, an instance is a member exactly when its accepting count on `τ` choice bits is
positive, for every `τ ≥ c₁ * t n + c₂` on instances of encoded length `n`. -/
theorem exists_acceptCount_of_mem_NTIME (h : A ∈ NTIME enc t) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapePTM k Bool State) (c₁ c₂ : ℕ),
      ∀ a τ, c₁ * t (enc a).length + c₂ ≤ τ → (a ∈ A ↔ 0 < machine.acceptCount (enc a) τ) := by
  obtain ⟨c₁, c₂, k, State, hfinite, ntm, hntm⟩ := h
  set M := Nat.card (Turing.Action k Bool State)
  refine ⟨k, _, inferInstance, ntm.choiceTable, M * c₁, M * c₂, fun a τ hτ =>
    hntm.mem_iff_acceptCount_choiceTable_pos ?_⟩
  rw [Nat.mul_add, ← Nat.mul_assoc]
  exact hτ

/-- **Bounded-error probabilistic time as accepting counts.** A problem in `BPTIME enc t` is
decided by a fixed fair-coin machine with a binary alphabet and finitely many states: for
constants `c₁` and `c₂`, an instance is a member exactly when more than half of its choice
strings of length `τ` accept, for every `τ ≥ c₁ * t n + c₂` on instances of encoded length `n`. -/
theorem exists_acceptCount_of_mem_BPTIME (h : A ∈ BPTIME enc t) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapePTM k Bool State) (c₁ c₂ : ℕ),
      ∀ a τ, c₁ * t (enc a).length + c₂ ≤ τ →
        (a ∈ A ↔ 2 ^ τ < 2 * machine.acceptCount (enc a) τ) := by
  obtain ⟨c₁, c₂, k, State, hfinite, machine, hmachine⟩ := h
  exact ⟨k, State, hfinite, machine, c₁, c₂, fun a τ hτ =>
    hmachine.mem_iff_two_pow_lt_two_mul_acceptCount hτ⟩

end Cslib.Complexity

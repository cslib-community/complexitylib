/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.InductiveCounting.Machine
import Mathlib.Tactic.Linarith

/-!
# Halting and every-prefix storage of the complement query machine

Fix a round `J₀` whose radix is closed on the input, as a space bound of the source provides.
The radix moves to the next round only after a certified overflow, so every reachable state is in
a round at most `J₀` (`Turing.InductiveCounting.round_le`). Each round's controller halts within
the instruction budget of round `J₀`, so every branch halts within a common clock
(`Turing.InductiveCounting.queryMachine_haltsWithin`). Every controller register is below a power
of two linear in `J₀` and the binary length of the input, so every prefix, including rejecting
and dishonest ones, has short encoded state (`Turing.InductiveCounting.length_run_le`).

## Main definitions

* `Turing.InductiveCounting.roundBudget`: the instruction budget of round `J₀`.
* `Turing.InductiveCounting.abstractTime`: a clock for every branch.
* `Turing.InductiveCounting.storageBound`: a bound on every encoded state.

## Main results

* `Turing.InductiveCounting.queryMachine_haltsWithin`: every branch halts within the clock.
* `Turing.InductiveCounting.length_run_le`: storage on every choice prefix.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
-/

@[expose] public section

namespace Turing.InductiveCounting

open MultiTapeTM MultiTapeNTM.ConfigurationGraph

variable {k : ℕ} {State : Type} [Fintype State] {ntm : MultiTapeNTM k Bool State}
  {input : List Bool}

private theorem two_pow_size_le (n : ℕ) : 2 ^ n.size ≤ 2 * (n + 1) := by
  by_cases h : n.size = 0
  · simp only [h, pow_zero]
    omega
  · have hp : 2 ^ (n.size - 1) ≤ n := Nat.lt_size.mp (by omega)
    rw [show n.size = n.size - 1 + 1 by omega, pow_succ]
    omega

/-- Larger radices have larger ambient graphs. -/
theorem vertexBound_mono {B B' : ℕ} (h : B ≤ B') :
    vertexBound (k := k) B ≤ vertexBound (k := k) B' :=
  Nat.pow_le_pow_left h _

theorem roundRadix_mono (n : ℕ) {j j' : ℕ} (h : j ≤ j') :
    roundRadix State n j ≤ roundRadix State n j' :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) h)

/-- **Rounds stop at a closed one**: a state's round has only unclosed rounds before it. -/
theorem round_le {J₀ j : ℕ} (hJ₀ : Closed ntm (roundRadix State input.length J₀) input)
    (hj : ∀ i < j, ¬ Closed ntm (roundRadix State input.length i) input) : j ≤ J₀ := by
  by_contra h
  exact hj J₀ (by omega) hJ₀

variable (k State) in
/-- The instruction budget of the controller on round `J₀`, which bounds every earlier round. -/
noncomputable def roundBudget (J₀ n : ℕ) : ℕ :=
  Cslib.InductiveCounting.budget (vertexBound (k := k) (roundRadix State n J₀))
    (vertexWidth k (roundRadix State n J₀))

theorem rank_install_le {J₀ n j : ℕ} (hj : j ≤ J₀) :
    Cslib.InductiveCounting.rank (vertexBound (k := k) (roundRadix State n j))
      (vertexWidth k (roundRadix State n j)) (install ntm (roundRadix State n j)) ≤
      roundBudget k State J₀ n := by
  refine Cslib.InductiveCounting.rank_initial_le_budget.trans ?_
  have hN := vertexBound_mono (k := k) (roundRadix_mono (State := State) n hj)
  have hw : vertexWidth k (roundRadix State n j) ≤ vertexWidth k (roundRadix State n J₀) :=
    Nat.size_le_size hN
  unfold roundBudget Cslib.InductiveCounting.budget
  gcongr

/-- Halted runtimes have rejected, or accepted on a checked radix. -/
private theorem not_halted_counting {B : ℕ} {chk : Bool} {c : Cslib.InductiveCounting.State}
    (h : (queryMachine ntm).halted ⟨input.length, B, chk, some c⟩ = false) :
    c.phase ≠ .reject ∧ (chk = true → c.phase ≠ .accept) := by
  simp only [queryMachine, runtimeHalted, Option.any_some, Bool.or_eq_false_iff,
    beq_eq_false_iff_ne, ne_eq, Bool.and_eq_false_iff] at h
  refine ⟨h.1, fun hc => ?_⟩
  rcases h.2 with h | h
  · simp [hc] at h
  · simpa using h

/-- On a checked radix, every branch halts within the controller's progress measure. -/
theorem halted_replay_checked {B : ℕ} {c : Cslib.InductiveCounting.State} (choices : List Bool)
    (h : Cslib.InductiveCounting.rank (vertexBound (k := k) B) (vertexWidth k B) c ≤
      choices.length) :
    (queryMachine ntm).halted
      ((queryMachine ntm).replay input choices ⟨input.length, B, true, some c⟩) = true := by
  rw [replay_checked]
  have hh := Cslib.InductiveCounting.halted_replay_of_rank_le
    (source := startID ntm B) (edge := graphEdge ntm B input)
    (bad := graphBad ntm input B true) choices h
  simp only [Cslib.InductiveCounting.halted, Bool.or_eq_true, beq_iff_eq] at hh
  simp only [queryMachine, runtimeHalted, Option.any_some, Bool.true_and, Bool.or_eq_true,
    beq_iff_eq]
  exact hh.symm

/-- On an unchecked radix of round `j`, every branch halts within the controller's progress
measure, one instruction, the budget of a checked round, and the budgets of the remaining
rounds. -/
private theorem halted_replay_unchecked {J₀ : ℕ}
    (hJ₀ : Closed ntm (roundRadix State input.length J₀) input) :
    ∀ m j, J₀ - j = m → ∀ (c : Cslib.InductiveCounting.State) (choices : List Bool),
      RuntimeInvariant ntm input
        ⟨input.length, roundRadix State input.length j, false, some c⟩ →
      Cslib.InductiveCounting.rank (vertexBound (k := k) (roundRadix State input.length j))
          (vertexWidth k (roundRadix State input.length j)) c + 1 +
          roundBudget k State J₀ input.length +
          m * (roundBudget k State J₀ input.length + 1) ≤ choices.length →
      (queryMachine ntm).halted ((queryMachine ntm).replay input choices
        ⟨input.length, roundRadix State input.length j, false, some c⟩) = true := by
  intro m
  induction m with
  | zero => ?_
  | succ m ihm => ?_
  all_goals
    intro j hm c
    induction hr : Cslib.InductiveCounting.rank (vertexBound (k := k)
      (roundRadix State input.length j)) (vertexWidth k (roundRadix State input.length j)) c
      using Nat.strong_induction_on generalizing c with
    | _ r ih =>
    intro choices hinv hlen
    obtain ⟨-, ⟨j', hj', hjs⟩, hi, hb, -⟩ := hinv
    have hjj : j = j' := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := Nat.mul_lt_mul_of_pos_right
          (Nat.pow_lt_pow_right (by omega : 1 < 4) h)
          (by have := card_lt_startRadix (State := State) input.length; omega :
            0 < startRadix State input.length)
        simp only [roundRadix] at hj'
        omega
      · have := Nat.mul_lt_mul_of_pos_right
          (Nat.pow_lt_pow_right (by omega : 1 < 4) h)
          (by have := card_lt_startRadix (State := State) input.length; omega :
            0 < startRadix State input.length)
        simp only [roundRadix] at hj'
        omega
    subst hjj
    have hjJ := round_le hJ₀ hjs
    rcases choices with _ | ⟨b, rest⟩
    · simp at hlen
    by_cases hh : (queryMachine ntm).halted
        ⟨input.length, roundRadix State input.length j, false, some c⟩ = true
    · rw [NondeterministicQueryMachine.replay_of_halted _ _ hh]
      exact hh
    have hinv : RuntimeInvariant ntm input
        ⟨input.length, roundRadix State input.length j, false, some c⟩ :=
      ⟨rfl, ⟨j, rfl, hjs⟩, hi, hb, by simp⟩
    obtain ⟨hnr, -⟩ := not_halted_counting (Bool.eq_false_iff.mpr hh)
    have hinv' := runtimeInvariant_step hinv b
    rw [NondeterministicQueryMachine.replay_cons]
    simp only [List.length_cons] at hlen
    by_cases ho : overflowed c = true
    · rw [step_overflowed ntm input ho, ← roundRadix_succ]
      rw [step_overflowed ntm input ho, ← roundRadix_succ] at hinv'
      have hncl := not_closed_of_overflowed (card_lt_roundRadix _ _)
        (by simpa only [graphBad, Bool.false_eq_true, ↓reduceIte] using hi) ho
      have hjJ' : j < J₀ := by
        by_contra h
        exact hncl (hJ₀.mono (card_lt_roundRadix _ _) (roundRadix_mono _ (by omega)))
      first
      | omega
      | exact ihm (j + 1) (by omega) _ rest hinv' (by
          have := rank_install_le (ntm := ntm) (State := State) (n := input.length)
            (show j + 1 ≤ J₀ by omega)
          nlinarith)
    by_cases ha : c.phase = .accept
    · rw [step_switch ntm input ha]
      refine halted_replay_checked rest ?_
      have := rank_install_le (ntm := ntm) (State := State) (n := input.length) hjJ
      nlinarith
    · rw [step_counting ntm input (by simp [ho]) (by simp [ha])]
      rw [step_counting ntm input (by simp [ho]) (by simp [ha])] at hinv'
      have hc : Cslib.InductiveCounting.halted c = false := by
        simp [Cslib.InductiveCounting.halted, ha, hnr]
      have hlt := Cslib.InductiveCounting.rank_advance_lt
        (N := vertexBound (k := k) (roundRadix State input.length j))
        (width := vertexWidth k (roundRadix State input.length j))
        (source := startID ntm (roundRadix State input.length j))
        (Cslib.InductiveCounting.answer (graphEdge ntm (roundRadix State input.length j) input)
          (graphBad ntm input (roundRadix State input.length j) false) c) b hc
      have hlt' : Cslib.InductiveCounting.rank (vertexBound (k := k)
          (roundRadix State input.length j)) (vertexWidth k (roundRadix State input.length j))
          (ctlStep ntm input (roundRadix State input.length j) false c b) < r := hr ▸ hlt
      exact ih _ hlt' _ rfl rest hinv' (by omega)

variable (k State) in
/-- An explicit clock for every abstract branch, including dishonest guesses, given a closed
round `J₀`. -/
noncomputable def abstractTime (J₀ n : ℕ) : ℕ :=
  n + 1 + (2 * roundBudget k State J₀ n + 1 + J₀ * (roundBudget k State J₀ n + 1))

/-- **Every branch halts within the same input-dependent clock**, given a closed round. -/
theorem queryMachine_haltsWithin {J₀ : ℕ}
    (hJ₀ : Closed ntm (roundRadix State input.length J₀) input) :
    (queryMachine ntm).HaltsWithin input (abstractTime k State J₀ input.length) := by
  intro choices hlen
  conv_lhs => rw [← List.take_append_drop (input.length + 1) choices]
  rw [NondeterministicQueryMachine.run_append, run_bootstrap ntm input _ (by
    simp only [List.length_take, hlen, abstractTime]; omega), ← roundRadix_zero]
  refine halted_replay_unchecked hJ₀ _ 0 rfl _ _
    (runtimeInvariant_install (by simp)) ?_
  have := rank_install_le (ntm := ntm) (State := State) (n := input.length) (Nat.zero_le J₀)
  simp only [List.length_drop, hlen, abstractTime, Nat.sub_zero]
  omega

/-! ### Storage -/

variable (k State) in
/-- A bound on every encoded runtime state reachable on an input of length `n`, given a closed
round `J₀`: linear in `J₀` and the binary length of `n`. -/
def storageBound (J₀ n : ℕ) : ℕ :=
  (40 * Fintype.card (Register k) + 4) *
    (2 * J₀ + Nat.log2 n + Fintype.card (Option State) + 4) + 2 * Nat.log2 n + 170

private theorem roundRadix_le_two_pow (n j : ℕ) :
    roundRadix State n j ≤ 2 ^ (2 * j + Nat.log2 n + Fintype.card (Option State) + 4) := by
  have hn : n + 2 ≤ 2 ^ (Nat.log2 n + 2) := by
    have := Nat.lt_log2_self (n := n)
    rw [pow_succ]
    omega
  have h4 : (4 : ℕ) ^ j = 2 ^ (2 * j) := by rw [pow_mul]; norm_num
  calc roundRadix State n j = 2 ^ (2 * j) * ((n + 2) * 2 ^ (Fintype.card (Option State) + 2)) := by
        rw [roundRadix, startRadix, h4]
    _ ≤ 2 ^ (2 * j) * (2 ^ (Nat.log2 n + 2) * 2 ^ (Fintype.card (Option State) + 2)) := by
        gcongr
    _ = 2 ^ (2 * j + Nat.log2 n + Fintype.card (Option State) + 4) := by
        rw [← pow_add, ← pow_add]
        ring_nf

/-- **Every state allowed by the invariant has a short encoding**, given a closed round. -/
theorem length_runtime_le {J₀ : ℕ} (hJ₀ : Closed ntm (roundRadix State input.length J₀) input)
    {s : Runtime} (h : RuntimeInvariant ntm input s) :
    (encRuntime s).length ≤ storageBound k State J₀ input.length := by
  set E := 2 * J₀ + Nat.log2 input.length + Fintype.card (Option State) + 4
  have hlen (l : ℕ) (hl : l ≤ input.length) : (encNat l).length ≤ Nat.log2 input.length + 1 :=
    length_encNat_le_log2 hl
  rcases s with ⟨l, B, chk, _ | c⟩
  · obtain ⟨hl, rfl, rfl⟩ := h
    change (encPair encNat (encPair encNat (encPair encBool (encOption encState)))
      (l, 0, false, none)).length ≤ _
    simp only [length_encPair, encOption_none, List.length_nil, encBool_apply,
      List.length_singleton]
    have := hlen l hl
    simp only [storageBound]
    have : (encNat 0).length = 0 := rfl
    nlinarith
  · obtain ⟨rfl, ⟨j, rfl, hjs⟩, -, hb, -⟩ := h
    have hjJ := round_le hJ₀ hjs
    have hB : roundRadix State input.length j ≤ 2 ^ E :=
      (roundRadix_le_two_pow input.length j).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have hBpos : 0 < roundRadix State input.length j := by
      have := card_lt_roundRadix (State := State) input.length j
      omega
    set N := vertexBound (k := k) (roundRadix State input.length j)
    have hN : N ≤ 2 ^ (E * Fintype.card (Register k)) := by
      change roundRadix State input.length j ^ Fintype.card (Register k) ≤ _
      rw [pow_mul]
      exact Nat.pow_le_pow_left hB _
    have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    have hreg : Cslib.InductiveCounting.registerBound N (vertexWidth k
        (roundRadix State input.length j)) ≤ 2 ^ (E * Fintype.card (Register k) + 3) := by
      have hsize := Nat.size_le.mpr (Nat.lt_two_pow_self (n := N))
      have hpow := two_pow_size_le N
      unfold Cslib.InductiveCounting.registerBound vertexWidth
      have hs : N.size ≤ N := Nat.size_le.mpr Nat.lt_two_pow_self
      rw [pow_add]
      change N + 2 ^ N.size + N.size + 2 ≤ _
      omega
    have hstate := length_encState_le (s := c) (L := E * Fintype.card (Register k) + 3)
      fun r hr => by
        rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
        exact (mem_registers_lt hb r hr).trans_le hreg
    have hradix : (encNat (roundRadix State input.length j)).length ≤ E + 1 := by
      rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
      exact hB.trans_lt (Nat.pow_lt_pow_right (by omega) (by omega))
    change (encPair encNat (encPair encNat (encPair encBool (encOption encState)))
      (input.length, roundRadix State input.length j, chk, some c)).length ≤ _
    simp only [length_encPair, encOption_some, List.length_cons, encBool_apply,
      List.length_nil]
    have := hlen input.length le_rfl
    simp only [storageBound]
    simp only [E] at hstate hradix
    nlinarith

/-- The encoded state bound holds on every computation prefix, including rejecting branches. -/
theorem length_run_le {J₀ : ℕ} (hJ₀ : Closed ntm (roundRadix State input.length J₀) input)
    (choices : List Bool) :
    (encRuntime ((queryMachine ntm).run input choices)).length ≤
      storageBound k State J₀ input.length :=
  length_runtime_le hJ₀ (runtimeInvariant_run choices)

end Turing.InductiveCounting

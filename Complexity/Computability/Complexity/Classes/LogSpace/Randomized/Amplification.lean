/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace.Randomized
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.OrElse

/-!
# Amplification for randomized logarithmic space with one-sided error

Running an `RL` machine again on fresh coins when it does not accept
(`Turing.MultiTapePTM.orElse`) multiplies the probabilities of not accepting. Counted on coin
strings, the probability that `first.orElse second` does not accept is the product of those of
`first` and `second` (`Turing.MultiTapePTM.acceptCoins_orElse`); in particular it accepts nothing
when neither machine accepts anything. Repeating an `RL` machine `r + 1` times therefore accepts
members on at least a `1 - 2 ^ (-r)` fraction of the coin strings and non-members on none, in
logarithmic space and with every branch halting. Only a fixed number of repetitions is needed, so
the extra work tapes and control states are a constant overhead.

This is the error reduction for one-sided error [Arora and Barak, Section 7.4.1][AroraBarak09],
carried out for logspace fair-coin machines with read-once coins. The acceptance threshold `1/2` in
the definition of `Cslib.Complexity.RL` can be replaced by any threshold `1 - 2 ^ (-r)` with
`r ≥ 1` (`Cslib.Complexity.mem_RL_iff_error_le`); with `r = 2`, members are accepted with
probability at least `3/4 ≥ 2/3`, which gives `RL ⊆ BPL`.

## Main results

* `Turing.MultiTapePTM.runsInTime_toNTM_iff`: halting on every branch is halting on every
  supported configuration of the closed fair-coin run.
* `Turing.MultiTapePTM.acceptCoins_eq_mul_eval`: `acceptCoins input t / 2 ^ t` is the probability
  that the closed fair-coin run outputs `[true]`.
* `Turing.MultiTapePTM.runsInTime_toNTM_orElse`, `Turing.MultiTapePTM.eval_runClosed_orElse_apply`,
  `Turing.MultiTapePTM.acceptCoins_orElse`: halting time, acceptance probability and rejection
  count of `orElse`.
* `Cslib.Complexity.mem_RL_iff_error_le`: one-sided error amplification for `RL`.
* `Cslib.Complexity.RL_subset_BPL`: randomized logspace with one-sided error is within `BPL`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Sections 7.4.1 and
  7.7][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k : ℕ} {State : Type} (machine : MultiTapePTM k Bool State)

/-- **Halting on every branch, in distribution.** The nondeterministic view halts within `t`
steps exactly when every configuration supported by the closed fair-coin run with clock `t` is
halted. -/
theorem runsInTime_toNTM_iff {input : List Bool} {t : ℕ} :
    machine.toNTM.RunsInTime input t ↔
      ∀ final ∈ (ProbComp.eval (machine.runClosedConfigFrom t
        (machine.initialConfig input))).support, final.tapes.state = none := by
  refine ⟨fun ht final hfinal => ?_, machine.runsInTime_toNTM⟩
  rw [eval_runClosedConfigFrom_eq_map_coins] at hfinal
  obtain ⟨coins, hcoins, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
  rw [tapes_runClosedConfigFromCoins]
  exact machine.halted_stepCoins ht (BitString.length_of_mem_support_uniformList hcoins).ge

/-- **The accepting coin strings measure the acceptance probability**: once every branch halts
within `t` steps, `acceptCoins input t / 2 ^ t` is the probability that the closed fair-coin run
outputs `[true]`. -/
theorem acceptCoins_eq_mul_eval {input : List Bool} {t : ℕ}
    (ht : machine.toNTM.RunsInTime input t) :
    (machine.acceptCoins input t : ENNReal) =
      2 ^ t * ProbComp.eval (machine.runClosed t input) [true] := by
  classical
  rw [eval_runClosed_eq_map_coins, BitString.uniformList_map_apply,
    ENNReal.mul_div_cancel (by simp) (by simp)]
  unfold acceptCoins
  congr 2
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, runClosedCoins,
    tapes_runClosedConfigFromCoins]
  exact and_iff_right_of_imp fun _ =>
    machine.halted_stepCoins (coins := List.ofFn w) ht (by simp)

end Turing.MultiTapePTM

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k₁ k₂ : ℕ} {S₁ S₂ : Type} (first : MultiTapePTM k₁ Bool S₁)
  (second : MultiTapePTM k₂ Bool S₂) {input : List Bool} {t₁ t₂ : ℕ}

/-- `first.orElse second` halts on every branch within `t₁ + (n + 2 + t₂)` steps, where `n` is the
input length. -/
theorem runsInTime_toNTM_orElse (h₁ : first.toNTM.RunsInTime input t₁)
    (h₂ : second.toNTM.RunsInTime input t₂) :
    (first.orElse second).toNTM.RunsInTime input (t₁ + (input.length + 2 + t₂)) :=
  (runsInTime_toNTM_iff _).mpr (orElse_halted first second input t₁ t₂
    ((runsInTime_toNTM_iff _).mp h₁) ((runsInTime_toNTM_iff _).mp h₂))

/-- The acceptance probability of `first.orElse second` is `q + p * (1 - q)`, where `p` and `q`
are those of `first` and `second`. -/
theorem eval_runClosed_orElse_apply (h₁ : first.toNTM.RunsInTime input t₁)
    (h₂ : second.toNTM.RunsInTime input t₂) :
    ProbComp.eval ((first.orElse second).runClosed (t₁ + (input.length + 2 + t₂)) input) [true] =
      ProbComp.eval (second.runClosed t₂ input) [true] +
        ProbComp.eval (first.runClosed t₁ input) [true] *
          (1 - ProbComp.eval (second.runClosed t₂ input) [true]) := by
  set q := ProbComp.eval (second.runClosed t₂ input) [true]
  have hq : q ≤ 1 := PMF.coe_le_one _ _
  rw [eval_runClosed_orElse first second input t₁ t₂ ((runsInTime_toNTM_iff _).mp h₁)
    ((runsInTime_toNTM_iff _).mp h₂), Probability.PMF.monad_bind_eq_bind, PMF.bind_apply]
  calc ∑' word, ProbComp.eval (first.runClosed t₁ input) word *
        (if word = [true] then pure [true] else ProbComp.eval (second.runClosed t₂ input)) [true]
      = ∑' word, (ProbComp.eval (first.runClosed t₁ input) word * q +
          if word = [true] then ProbComp.eval (first.runClosed t₁ input) [true] * (1 - q)
          else 0) := by
        refine tsum_congr fun word => ?_
        split_ifs with h
        · subst h
          rw [← mul_add, add_tsub_cancel_of_le hq]
          exact congrArg _ (PMF.pure_apply_self _)
        · rw [add_zero]
    _ = q + ProbComp.eval (first.runClosed t₁ input) [true] * (1 - q) := by
        rw [tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, tsum_ite_eq]

/-- **Rejections multiply under `orElse`.** Counted on coin strings, the probability that
`first.orElse second` does not accept is the product of the probabilities that `first` and
`second` do not accept: with `T = t₁ + (n + 2 + t₂)`,
`(2 ^ T - acc) / 2 ^ T = (2 ^ t₁ - acc₁) / 2 ^ t₁ * (2 ^ t₂ - acc₂) / 2 ^ t₂`. -/
theorem acceptCoins_orElse (h₁ : first.toNTM.RunsInTime input t₁)
    (h₂ : second.toNTM.RunsInTime input t₂) :
    (2 ^ (t₁ + (input.length + 2 + t₂)) -
        (first.orElse second).acceptCoins input (t₁ + (input.length + 2 + t₂))) *
        (2 ^ t₁ * 2 ^ t₂) =
      (2 ^ t₁ - first.acceptCoins input t₁) * (2 ^ t₂ - second.acceptCoins input t₂) *
        2 ^ (t₁ + (input.length + 2 + t₂)) := by
  set T := t₁ + (input.length + 2 + t₂)
  have hN := runsInTime_toNTM_orElse first second h₁ h₂
  set p := ProbComp.eval (first.runClosed t₁ input) [true]
  set q := ProbComp.eval (second.runClosed t₂ input) [true]
  have hq : q ≤ 1 := PMF.coe_le_one _ _
  have hreal {k : ℕ} {S : Type} (M : MultiTapePTM k Bool S) {t : ℕ}
      (ht : M.toNTM.RunsInTime input t) :
      (M.acceptCoins input t : ℝ) =
        2 ^ t * (ProbComp.eval (M.runClosed t input) [true]).toReal := by
    have := congrArg ENNReal.toReal (M.acceptCoins_eq_mul_eval ht)
    simpa [ENNReal.toReal_mul] using this
  have hpN := congrArg ENNReal.toReal (eval_runClosed_orElse_apply first second h₁ h₂)
  rw [ENNReal.toReal_add (by simp [PMF.apply_ne_top]) (ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    (by simp)), ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hq (by simp),
    ENNReal.toReal_one] at hpN
  apply Nat.cast_injective (R := ℝ)
  push_cast [Nat.cast_sub (acceptCoins_le _ _ _)]
  rw [hreal _ hN, hreal _ h₁, hreal _ h₂, hpN]
  ring

end Turing.MultiTapePTM

namespace Cslib.Complexity

open _root_.Turing

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- Repeating an `RL` machine `r + 1` times rejects members with probability at most `2 ^ (-r)`,
in the counting form `2 ^ r * (2 ^ t - acc) ≤ 2 ^ t`. -/
private theorem exists_rejectCoins_le_of_mem_RL (h : A ∈ RL enc) (r : ℕ) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapePTM k Bool State) (c : ℕ),
      ∀ a, M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1)) ∧
        ∃ t, M.toNTM.RunsInTime (enc a) t ∧
          (a ∈ A → 2 ^ r * (2 ^ t - M.acceptCoins (enc a) t) ≤ 2 ^ t) ∧
          (a ∉ A → M.acceptCoins (enc a) t = 0) := by
  obtain ⟨k, State, hfin, M, c, hM⟩ := h
  induction r with
  | zero =>
    refine ⟨k, State, hfin, M, c, fun a => ⟨(hM a).1, ?_⟩⟩
    obtain ⟨t, ht, -, hnot⟩ := (hM a).2
    exact ⟨t, ht, fun _ => by simp, hnot⟩
  | succ r ih =>
    obtain ⟨k', State', hfin', M', c', hM'⟩ := ih
    refine ⟨k + k' + 1, _, by infer_instance, M.orElse M', (k + k' + 1) * (2 * max c c' + 1),
      fun a => ⟨?_, ?_⟩⟩
    · have hspace := MultiTapePTM.runsInSpace_toNTM_orElse M M' (hM a).1 (hM' a).1
      refine hspace.mono ?_
      set L := Nat.log2 (enc a).length + 1
      have hL : 1 ≤ L := Nat.le_add_left 1 _
      have hmax : max (c * L) (c' * L) ≤ max c c' * L :=
        max_le (Nat.mul_le_mul_right L (le_max_left c c'))
          (Nat.mul_le_mul_right L (le_max_right c c'))
      rw [Nat.mul_assoc]
      refine Nat.mul_le_mul_left _ ?_
      nlinarith
    · obtain ⟨t, ht, hmem, hnot⟩ := (hM a).2
      obtain ⟨t', ht', hmem', hnot'⟩ := (hM' a).2
      have hpos : 0 < 2 ^ t * 2 ^ t' := Nat.mul_pos (Nat.two_pow_pos t) (Nat.two_pow_pos t')
      have hprod := MultiTapePTM.acceptCoins_orElse M M' ht ht'
      have hle := (M.orElse M').acceptCoins_le (enc a) (t + ((enc a).length + 2 + t'))
      refine ⟨_, MultiTapePTM.runsInTime_toNTM_orElse M M' ht ht', fun ha => ?_, fun ha => ?_⟩ <;>
        generalize t + ((enc a).length + 2 + t') = T at hprod hle ⊢
      · have h₁ : 2 * (2 ^ t - M.acceptCoins (enc a) t) ≤ 2 ^ t := by
          have := hmem ha
          have := M.acceptCoins_le (enc a) t
          omega
        refine Nat.le_of_mul_le_mul_right ?_ hpos
        calc 2 ^ (r + 1) * (2 ^ T - (M.orElse M').acceptCoins (enc a) T) * (2 ^ t * 2 ^ t')
            = (2 * (2 ^ t - M.acceptCoins (enc a) t)) *
                (2 ^ r * (2 ^ t' - M'.acceptCoins (enc a) t')) * 2 ^ T := by
              rw [Nat.mul_assoc, hprod]
              ring
          _ ≤ 2 ^ t * 2 ^ t' * 2 ^ T :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul h₁ (hmem' ha))
          _ = 2 ^ T * (2 ^ t * 2 ^ t') := by ring
      · rw [hnot ha, hnot' ha, Nat.sub_zero, Nat.sub_zero, ← Nat.mul_comm (2 ^ T)] at hprod
        have := Nat.eq_of_mul_eq_mul_right hpos hprod
        have := Nat.two_pow_pos T
        omega

/-- **One-sided error amplification for `RL`** [Arora and Barak, Section 7.4.1][AroraBarak09]: for
every `r ≥ 1`, a language is in `RL` exactly when some logspace fair-coin machine that halts on
every branch accepts members on at least a `1 - 2 ^ (-r)` fraction of the coin strings and
non-members on none. The machine for `r` runs an `RL` machine `r + 1` times on fresh work tapes and
fresh coins and accepts if some run accepts (`Turing.MultiTapePTM.orElse`). -/
theorem mem_RL_iff_error_le {r : ℕ} (hr : 1 ≤ r) :
    A ∈ RL enc ↔
      ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapePTM k Bool State) (c : ℕ),
        ∀ a, M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1)) ∧
          ∃ t, M.toNTM.RunsInTime (enc a) t ∧
            (a ∈ A → (2 ^ r - 1) * 2 ^ t ≤ 2 ^ r * M.acceptCoins (enc a) t) ∧
            (a ∉ A → M.acceptCoins (enc a) t = 0) := by
  constructor
  · intro h
    obtain ⟨k, State, hfin, M, c, hM⟩ := exists_rejectCoins_le_of_mem_RL h r
    refine ⟨k, State, hfin, M, c, fun a => ⟨(hM a).1, ?_⟩⟩
    obtain ⟨t, ht, hmem, hnot⟩ := (hM a).2
    refine ⟨t, ht, fun ha => ?_, hnot⟩
    have h₁ := hmem ha
    have hle := Nat.mul_le_mul_left (2 ^ r) (M.acceptCoins_le (enc a) t)
    rw [Nat.mul_sub] at h₁
    rw [Nat.sub_mul, Nat.one_mul]
    omega
  · rintro ⟨k, State, hfin, M, c, hM⟩
    refine ⟨k, State, hfin, M, c, fun a => ⟨(hM a).1, ?_⟩⟩
    obtain ⟨t, ht, hmem, hnot⟩ := (hM a).2
    refine ⟨t, ht, fun ha => ?_, hnot⟩
    have h₁ := hmem ha
    have h₂ : 2 * 2 ^ t ≤ 2 ^ r * 2 ^ t :=
      Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) 2 |>.trans' (by norm_num) |>.trans
        (Nat.pow_le_pow_right (by norm_num) hr))
    rw [Nat.sub_mul, Nat.one_mul] at h₁
    refine Nat.le_of_mul_le_mul_left ?_ (Nat.two_pow_pos r)
    rw [Nat.mul_left_comm]
    omega

/-- **`RL` is within `BPL`**: amplifying an `RL` machine to error at most `1/4` gives acceptance
probability at least `3/4 ≥ 2/3` on members, and `0 ≤ 1/3` on non-members. -/
theorem RL_subset_BPL : RL enc ⊆ BPL enc := by
  intro A h
  obtain ⟨k, State, hfin, M, c, hM⟩ := (mem_RL_iff_error_le (r := 2) (by norm_num)).mp h
  refine ⟨k, State, hfin, M, c, fun a => ⟨(hM a).1, ?_⟩⟩
  obtain ⟨t, ht, hmem, hnot⟩ := (hM a).2
  refine ⟨t, ht, fun ha => ?_, fun ha => by simp [hnot ha]⟩
  have := hmem ha
  norm_num at this
  omega

end Cslib.Complexity

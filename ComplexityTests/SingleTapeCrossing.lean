/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.SingleTape.BoundedCrossings
import Complexity.Computability.Machines.Turing.SingleTape.NLogNGap
import Complexity.Computability.Machines.Turing.SingleTape.Palindrome

/-!
# Tests for crossing sequences and the palindrome lower bound

A concrete single-tape machine with computed crossing sequences, the sum and halting edge cases,
translation invariance, cut-and-paste at different positions (and why the prefix hypothesis is
needed), deciders that answer under the head, nonvacuity of the regularity criteria (bounded
crossings, also with nonempty crossing sequences, the explicit `n log n` bound and `o(n log n)`
time), the hard palindrome inputs, and failing instances of both palindrome decision notions.
-/

namespace ComplexityTests.SingleTapeCrossing

open Cslib Cslib.Turing SingleTapeTM Relation

/-- A one-state machine that moves right over the input and halts on the first blank. -/
def rightMover : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _
    | some s => (⟨some s, some .right⟩, some ())
    | none => (⟨none, none⟩, none)

/-- On `[true, false]` the head crosses the boundary between cells `0` and `1` once, entering
the (only) running state; it never crosses the boundary left of the input. -/
example : (rightMover.absInit [true, false]).crossings 1 3 = [some ()] := rfl

example : (rightMover.absInit [true, false]).crossings 0 3 = [] := by decide

example : (rightMover.absInit [true, false]).crossings 2 3 = [some ()] := rfl

/-- After three steps the run has halted on the blank cell `2`. -/
example : ((rightMover.absInit [true, false]).run 3).state = none ∧
    ((rightMover.absInit [true, false]).run 3).pos = 2 := by decide

/-- Edge case: a halted configuration crosses no boundary. -/
example (a : rightMover.AbsCfg) (h : a.state = none) (k : ℤ) (t : ℕ) :
    a.crossings k t = [] :=
  AbsCfg.crossings_of_none h k t

/-- The sum lemma on three boundaries: two crossings within three steps. -/
example : ∑ k ∈ ({0, 1, 2} : Finset ℤ), ((rightMover.absInit [true, false]).crossings k 3).length
    ≤ 3 :=
  AbsCfg.sum_length_crossings_le _ _ _

/-- Translation invariance on a concrete run: shifting by `3` moves the crossing at `1` to `4`. -/
example : ((rightMover.absInit [true, false]).shift 3).crossings 4 3 = [some ()] := rfl

/-- Cut-and-paste with prefixes of different lengths: the crossing sequence after `[true]` on
`[true, false]` matches the one after `[false, true]` on `[false, true, true]`, so the run on
`[true, true]` halts within `3 + 4` steps. -/
example : ((rightMover.absInit ([true] ++ [true])).run (3 + 4)).state = none :=
  (cut_and_paste_run (u₁ := [true]) (v₁ := [false]) (u₂ := [false, true]) (v₂ := [true])
    (t₁ := 3) (t₂ := 4) (by simp) rfl rfl rfl).1

/-- A one-state machine that halts at once, leaving the tape unchanged. -/
def stayer : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ s := (⟨s, none⟩, none)

/-- Edge case: the hypothesis that the prefixes are both empty or both nonempty cannot be
dropped from `cut_and_paste_run`. With `u₁ = []`, `v₁ = [false]`, `u₂ = [false]` and
`v₂ = [true]`, both runs halt after one step without crossing the boundary after the prefix, yet
the run on `u₁ ++ v₂ = [true]` scans `true` while both original runs scan `false`. -/
example : ((stayer.absInit ([] ++ [false])).run 1).state = none ∧
    ((stayer.absInit ([false] ++ [true])).run 1).state = none ∧
    (stayer.absInit ([] ++ [false])).crossings ([] : List Bool).length 1 =
      (stayer.absInit ([false] ++ [true])).crossings [false].length 1 ∧
    ((stayer.absInit ([] ++ [true])).run (1 + 1)).scanned = some true ∧
    ((stayer.absInit ([] ++ [false])).run 1).scanned = some false ∧
    ((stayer.absInit ([false] ++ [true])).run 1).scanned = some false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Nonvacuity of `DecidesByHeadInTime`: `stayer` decides within one step the words whose first
letter is `true`, answering with the symbol it leaves under the head. -/
lemma stayer_decidesByHeadInTime :
    stayer.DecidesByHeadInTime id {w : List Bool | w.head? = some true} true fun _ => 1 := by
  intro w
  refine ⟨⟨none, BiTape.mk₁ (w.map id)⟩, RelatesWithinSteps.single ?_, rfl, ?_⟩
  · simp only [TransitionRelation, step, initCfg, stayer, List.map_id]
    rw [BiTape.write_head_self]
    rfl
  · simp only [BiTape.head_mk₁, List.map_id]
    exact Iff.rfl

/-- `stayer` never moves, so it crosses no input boundary. -/
lemma stayer_crossings (w : List Bool) (b : ℕ) (hb : 1 ≤ b) :
    (stayer.absInit w).crossings (b : ℤ) 1 = [] := by
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  simp [AbsCfg.crossings, AbsCfg.next, absInit, stayer, moveShift, IsLeftOf]

/-- Nonvacuity of `isRegular_of_crossings_le`: `stayer` satisfies its hypotheses with `K = 0`,
so the language of words starting with `true` is regular. -/
example : Language.IsRegular ({w : List Bool | w.head? = some true} : Language Bool) :=
  isRegular_of_crossings_le stayer_decidesByHeadInTime 0 fun w b hb _ => by
    simp [stayer_crossings _ b hb]

/-- A two-state machine that moves right once and halts. -/
def stepper : SingleTapeTM Bool where
  State := Bool
  q₀ := false
  tr q s := if q then (⟨s, none⟩, none) else (⟨s, some .right⟩, some true)

/-- `stepper` decides within two steps the words whose second letter is `true`. -/
lemma stepper_decidesByHeadInTime :
    stepper.DecidesByHeadInTime id {w : List Bool | w[1]? = some true} true fun _ => 2 := by
  intro w
  refine ⟨⟨none, (BiTape.mk₁ (w.map id)).moveRight⟩, ?_, rfl, ?_⟩
  · refine RelatesWithinSteps.trans (n₁ := 1) (n₂ := 1)
      (RelatesWithinSteps.single (b := ⟨some true, (BiTape.mk₁ (w.map id)).moveRight⟩) ?_)
      (RelatesWithinSteps.single ?_)
    · simp only [TransitionRelation, step, initCfg, stepper, Bool.false_eq_true, ↓reduceIte,
        BiTape.write_head_self]
      rfl
    · simp [TransitionRelation, stepper, BiTape.write_head_self, BiTape.optionMove]
  · rcases w with _ | ⟨a, _ | ⟨b, w⟩⟩ <;> rfl

/-- `stepper` crosses boundary `1` once, entering its second state, and no other boundary. -/
example : (stepper.absInit [false, true]).crossings 1 2 = [some true] := rfl

example : (stepper.absInit [false, true]).crossings 2 2 = [] := by decide

/-- Every crossing sequence of `stepper` has length at most `1`. -/
lemma stepper_crossings_le (w : List Bool) (b : ℕ) :
    ((stepper.absInit w).crossings (b : ℤ) 2).length ≤ 1 := by
  simp only [AbsCfg.crossings]
  split_ifs <;> simp_all [AbsCfg.next, absInit, stepper, moveShift]

/-- `isRegular_of_crossings_le` with a nonempty crossing sequence: `K = 1` for `stepper`. -/
example : Language.IsRegular ({w : List Bool | w[1]? = some true} : Language Bool) :=
  isRegular_of_crossings_le stepper_decidesByHeadInTime 1 fun w b _ _ => stepper_crossings_le w b

/-- Nonvacuity of `isRegular_of_time_le_mul_log`: `stayer` has one state, so `d = 2`, and
`16 ≤ n ⌊log₂ n⌋` once `n ≥ 8`. -/
example : Language.IsRegular ({w : List Bool | w.head? = some true} : Language Bool) := by
  refine isRegular_of_time_le_mul_log stayer_decidesByHeadInTime (N := 8) fun n hn => ?_
  have hd : Nat.clog 2 (Fintype.card stayer.State + 2) = 2 := by decide
  have hlog : 3 ≤ Nat.log 2 n := Nat.le_log_of_pow_le one_lt_two hn
  rw [hd]
  nlinarith

/-- Nonvacuity of `isRegular_of_isLittleO`: constant time is `o(n log n)`. -/
example : Language.IsRegular ({w : List Bool | w.head? = some true} : Language Bool) := by
  refine isRegular_of_isLittleO stayer_decidesByHeadInTime ?_
  refine Asymptotics.IsLittleO.trans_isBigO (g := fun n : ℕ => Real.log n) ?_ ?_
  · exact (Real.isLittleO_const_log_atTop (c := ((1 : ℕ) : ℝ))).comp_tendsto
      tendsto_natCast_atTop_atTop
  · refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [one_mul, norm_mul, Real.norm_natCast]
    exact le_mul_of_one_le_left (norm_nonneg _) hn'

/-- The hard inputs are palindromes. -/
example : palWord 1 [true, false] = [true, false, false, false, true] := rfl

example : (palWord 1 [true, false]).Palindrome := by
  rw [List.Palindrome.iff_reverse_eq]
  rfl

/-- A failing instance: `rightMover`, like every single-tape machine, does not decide
palindromes in linear time. -/
example : ¬ rightMover.DecidesPalindromesInTime false true true fun n => 5 * (n + 1) :=
  not_decidesPalindromesInTime_linear Bool.false_ne_true 5

/-- Nor does `stayer`, even answering under the head. -/
example : ¬ stayer.DecidesByHeadInTime id {w : List Bool | w.Palindrome} true
    fun n => 5 * (n + 1) :=
  not_decidesByHeadInTime_palindromes_linear id true 5

end ComplexityTests.SingleTapeCrossing

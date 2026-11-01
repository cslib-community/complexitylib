/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BQP.TensorContraction
import ComplexityTests.BQPTensorContraction

/-! Nondeterministic, exact and postselected quantum time: circuits accepting with probability
strictly between `0` and `1`, exact circuits whose paths interfere, a postselected circuit that
accepts only after postselection, the classes they witness, and the containments applied to them.
-/

namespace ComplexityTests.QuantumTimeClasses

open Cslib Cslib.Quantum Cslib.Complexity Cslib.Complexity.QuantumContraction Turing.MultiTapeTM
  ComplexityTests.BQPTensorContraction

/-- The encoding of the single instance of `Unit` as the empty word. -/
def encUnit : Unit ↪ List Bool := ⟨fun _ => [], fun _ _ _ => rfl⟩

/-- The family running the fixed gate codes `gs` on `n + k` qubits for inputs of length `n`. -/
def constFamily (k : ℕ) (hk : 0 < k) (gs : List GateCode)
    (hgs : ∀ g ∈ gs, ∀ n, g.WellFormed (n + k)) : UniformCircuitFamily where
  width n := n + k
  gates _ := gs
  computableInPolyTime_width := by fun_prop
  computableInPolyTime_gates := ComputableInPolyTime.const _
  le_width n := Nat.le_add_right n k
  width_pos n := by omega
  wellFormed n g hg := hgs g hg n

/-! ### Nonzero but not exact -/

/-- One Hadamard gate on qubit `0`. -/
def coin : UniformCircuitFamily :=
  constFamily 1 (by norm_num) [(true, 0, [])] fun g hg n => by
    obtain rfl := List.mem_singleton.mp hg
    simp [GateCode.WellFormed]

-- The coin accepts with probability `1 / 2`: positive, but neither `0` nor `1`.
theorem acceptProb_coin : coin.acceptProb [] = 1 / 2 := by
  change acceptProb 1 [(true, 0, [])] [] = 1 / 2
  rw [acceptProb_eq_acceptGap _ (by decide), show List.ofFn (inputState 1 []) = [false] by decide,
    show acceptGap [(true, 0, [])] [false] = 1 by decide]
  norm_num [hadamardCount]

example : 0 < coin.acceptProb [] ∧ coin.acceptProb [] ≠ 1 := by
  rw [acceptProb_coin]
  norm_num

/-- The coin puts the instance into `NQTIME`. -/
theorem univ_mem_NQTIME : (Set.univ : Set Unit) ∈ NQTIME encUnit fun _ => 1 :=
  ⟨coin, 0, 1, fun _ => le_rfl, fun _ => by
    change _ ↔ 0 < coin.acceptProb []
    rw [acceptProb_coin]
    norm_num⟩

example : (Set.univ : Set Unit) ∈ ⋃ C, DTIME encUnit fun n =>
    2 ^ (C * (n + 2) / Nat.sqrt (Nat.log 2 (n + 2))) :=
  NQTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two (T := fun n => n + 2)
    (fun n => max_le (by omega) (by omega))
    (show (Set.univ : Set Unit) ∈ NQTIME encUnit fun n => n + 2 from
      ⟨coin, 0, 1, fun _ => by simp [coin, constFamily], fun _ => by
        change _ ↔ 0 < coin.acceptProb []
        rw [acceptProb_coin]
        norm_num⟩)

/-! ### Exact -/

/-- Two Hadamard gates on qubit `0`, after a NOT gate when `flip` holds. Their paths interfere, so
the circuit accepts exactly when `flip` holds. -/
def twice (flip : Bool) : UniformCircuitFamily :=
  constFamily 1 (by norm_num)
    ((if flip then [(false, 0, [])] else []) ++ [(true, 0, []), (true, 0, [])]) fun g hg n => by
    cases flip <;> simp only [Bool.false_eq_true, ite_false, ite_true, List.nil_append,
      List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hg <;>
      rcases hg with rfl | rfl | rfl <;> simp [GateCode.WellFormed]

-- From `|0⟩` the four accepting pairs of paths cancel; after the NOT gate they add up to `2 ^ 2`.
theorem acceptProb_twice_false : (twice false).acceptProb [] = 0 := by
  change acceptProb 1 [(true, 0, []), (true, 0, [])] [] = 0
  rw [acceptProb_eq_acceptGap _ (by decide), show List.ofFn (inputState 1 []) = [false] by decide,
    show acceptGap [(true, 0, []), (true, 0, [])] [false] = 0 by decide]
  norm_num

theorem acceptProb_twice_true : (twice true).acceptProb [] = 1 := by
  change acceptProb 1 [(false, 0, []), (true, 0, []), (true, 0, [])] [] = 1
  rw [acceptProb_eq_acceptGap _ (by decide), show List.ofFn (inputState 1 []) = [false] by decide,
    show acceptGap [(false, 0, []), (true, 0, []), (true, 0, [])] [false] = 4 by decide]
  norm_num [hadamardCount]

example : (∅ : Set Unit) ∈ EQTIME encUnit fun _ => 1 :=
  ⟨twice false, 0, 2, fun _ => le_rfl, fun _ =>
    ⟨fun h => absurd h (Set.notMem_empty _), fun _ => acceptProb_twice_false⟩⟩

example : (Set.univ : Set Unit) ∈ EQTIME encUnit fun _ => 1 :=
  ⟨twice true, 0, 3, fun _ => le_rfl, fun _ =>
    ⟨fun _ => acceptProb_twice_true, fun h => absurd (Set.mem_univ _) h⟩⟩

/-- Deciding the first bit takes no gates, exactly. -/
theorem firstBit_mem_EQTIME (t : ℕ → ℕ) : FirstBit ∈ EQTIME encBits t := by
  refine ⟨readFirst, 0, 0, fun n => by simp [readFirst], fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rw [encBits_apply, acceptProb_readFirst]
    simp only [show x.headD false = true from hx, ite_true]
  · rw [encBits_apply, acceptProb_readFirst]
    simp only [show x.headD false = false from Bool.eq_false_iff.mpr hx, Bool.false_eq_true,
      ite_false]

example : FirstBit ∈ NQTIME encBits fun _ => 0 :=
  EQTIME_subset_NQTIME _ (firstBit_mem_EQTIME _)

example : FirstBit ∈ ⋃ C, DTIME encBits fun n =>
    2 ^ (C * (n + 2) / Nat.sqrt (Nat.log 2 (n + 2))) :=
  EQTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two (T := fun n => n + 2)
    (fun n => max_le (by omega) (by omega)) (firstBit_mem_EQTIME _)

/-! ### Postselection -/

/-- The gate codes of `postselect`: two fair coins on qubits `2` and `3`, and their conjunction
written into qubits `0` and `1`. -/
def postselectCodes : List GateCode :=
  [(true, 2, []), (true, 3, []), (false, 0, [2, 3]), (false, 1, [2, 3])]

/-- Two fair coins whose conjunction is written into qubits `0` and `1`: qubit `0` reads `1` with
probability `1 / 4`, but always once qubit `1` reads `1`. -/
def postselect : UniformCircuitFamily :=
  constFamily 4 (by norm_num) postselectCodes fun g hg n => by
    simp only [postselectCodes, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp [GateCode.WellFormed]

theorem onesProb_postselect (S : List ℕ) :
    postselect.onesProb S [] =
      (onesGap S postselectCodes [false, false, false, false] : ℝ) / 4 := by
  change onesProb 4 postselectCodes S [] = _
  rw [onesProb_eq_onesGap _ (by decide),
    show List.ofFn (inputState 4 []) = [false, false, false, false] by decide,
    show hadamardCount postselectCodes = 2 by decide]
  norm_num

-- Without postselection the circuit rejects: it accepts with probability `1 / 4`.
example : postselect.acceptProb [] = 1 / 4 := by
  rw [UniformCircuitFamily.acceptProb_eq_onesProb, onesProb_postselect,
    show onesGap [0] postselectCodes [false, false, false, false] = 1 by decide]
  norm_num

-- Qubit `1` reads `1` with probability `1 / 4`, and then so does qubit `0`.
theorem onesProb_postselect_one : postselect.onesProb [1] [] = 1 / 4 := by
  rw [onesProb_postselect, show onesGap [1] postselectCodes [false, false, false, false] = 1 by
    decide]
  norm_num

theorem postselectedAcceptProb_postselect : postselect.postselectedAcceptProb [] = 1 := by
  rw [UniformCircuitFamily.postselectedAcceptProb, onesProb_postselect_one, onesProb_postselect,
    show onesGap [0, 1] postselectCodes [false, false, false, false] = 1 by decide]
  norm_num

-- The simulator computes both projected gaps.
example : gapValue [0, 1] postselectCodes [false, false, false, false] = 1 := by
  rw [gapValue_eq _ (by decide)]
  decide
example : gapValue [1] postselectCodes [false, false, false, false] = 1 := by
  rw [gapValue_eq _ (by decide)]
  decide

/-- Postselection puts the instance into `PostBQTIME`. -/
theorem univ_mem_PostBQTIME (t : ℕ → ℕ) : (Set.univ : Set Unit) ∈ PostBQTIME encUnit t := by
  refine ⟨postselect, 0, 4, fun _ => by simp [postselect, constFamily, postselectCodes],
    fun _ => ⟨?_, fun _ => ?_, fun h => absurd (Set.mem_univ _) h⟩⟩
  · change 0 < postselect.onesProb [1] []
    rw [onesProb_postselect_one]
    norm_num
  · change 2 / 3 ≤ postselect.postselectedAcceptProb []
    rw [postselectedAcceptProb_postselect]
    norm_num

example : (Set.univ : Set Unit) ∈ ⋃ C, DTIME encUnit fun n =>
    2 ^ (C * (n + 2) / Nat.sqrt (Nat.log 2 (n + 2))) :=
  PostBQTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two (T := fun n => n + 2)
    (fun n => max_le (by omega) (by omega)) (univ_mem_PostBQTIME _)

end ComplexityTests.QuantumTimeClasses

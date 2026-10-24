/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.EXP
import Complexity.Computability.Complexity.Classes.Hierarchy.Time

/-! Time-constructible bounds, the clocked diagonal on concrete machines and on a word without a
short description, the time hierarchy theorem for polynomial and exponential bounds, and the
separation of polynomial from exponential time. -/

namespace ComplexityTests.HierarchyTheorems

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Filter

/-! ### Time-constructible bounds -/

example : TimeConstructible (2 ^ ·) := timeConstructible_two_pow

example : TimeConstructible fun n => (n + 1) ^ 2 := timeConstructible_succ_sq

example : TimeConstructible fun n => (n + 1) ^ 7 := timeConstructible_succ_pow (by norm_num)

example : TimeConstructible fun n => (n + 1) * 2 ^ n :=
  timeConstructible_two_pow.succ_mul fun _ => Nat.lt_two_pow_self.le

/-! ### The clocked diagonal -/

/-- The diagonal of the exponential separation is the clocked diagonal with clock `2 ^ n`. -/
example : clockedDiagonal (2 ^ ·) = diagonal := clockedDiagonal_two_pow

/-- The empty word has no short description, so the clocked diagonal rejects it. -/
example (J : ℕ → ℕ) : timeDiagonal J [] = false := rfl

/-- Halt at once with output `[b]`. -/
private def answer (b : Bool) : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ _ _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := some b, state := none }

/-- After its first step, the answering machine has halted with output `[b]`. -/
private theorem runFrom_answer (b : Bool) (x : List Bool) {t : ℕ} (ht : 1 ≤ t) :
    ((answer b).runFrom ((answer b).initCfg x) t).Halted ∧
      ((answer b).runFrom ((answer b).initCfg x) t).output = [b] := by
  have h1 : ((answer b).runFrom ((answer b).initCfg x) 1).state = none ∧
      ((answer b).runFrom ((answer b).initCfg x) 1).output = [b] := by
    change ((answer b).step _).state = none ∧ ((answer b).step _).output = [b]
    rw [MultiTapeTM.step_of_state (q := ()) rfl]
    simp [answer, Action.apply]
  rw [MultiTapeTM.runFrom_eq_of_halt _ _ ht h1.1]
  exact h1

/-- The numbering of the single state. -/
private def unitNum : Unit ↪ ℕ := ⟨fun _ => 0, fun _ _ _ => rfl⟩

/-- On the description of a machine answering `b`, padded to a short description, the clocked
diagonal with any clock `J ≥ 1` answers `!b`, so its problem is neither empty nor everything. -/
example (b : Bool) (J : ℕ → ℕ) (hJ : ∀ n, 1 ≤ J n) (pad : List Bool)
    (hpad : 2 ^ (eDesc (desc unitNum eBit (answer b))).length ≤ pad.length) :
    timeDiagonal J (frame (eDesc (desc unitNum eBit (answer b))) ++ pad) = !b := by
  have hshort : Diagonal.shortDesc (frame (eDesc (desc unitNum eBit (answer b))) ++ pad) := by
    rw [Diagonal.shortDesc, unframe_frame_append, List.length_append, length_frame]
    exact decide_eq_true (by omega)
  obtain ⟨hhalt, hout⟩ := runFrom_answer b (frame (eDesc (desc unitNum eBit (answer b))) ++ pad)
    (hJ (frame (eDesc (desc unitNum eBit (answer b))) ++ pad).length)
  simp only [timeDiagonal, hshort, ↓reduceIte]
  exact clockedDiagonal_desc unitNum (answer b) pad J hhalt hout

/-! ### The time hierarchy theorem -/

/-- A polynomial instance: time `O(n ^ 2)` is strictly within time `O(n ^ 15)`. -/
example : DTIME encBits (fun n => (n + 1) ^ 2) ⊂ DTIME encBits fun n => (n + 1) ^ 15 := by
  refine DTIME_ssubset_DTIME timeConstructible_succ_sq
    (fun n => (Nat.le_succ n).trans (Nat.le_self_pow (by norm_num) _)) ?_
  filter_upwards [eventually_ge_atTop 7] with n hn
  have h₁ : (n + 1) ^ 2 + 1 ≤ 2 * (n + 1) ^ 2 := by
    have := Nat.one_le_pow 2 (n + 1) (by omega)
    omega
  calc (n + 1) ^ 8 * ((n + 1) ^ 2 + 1) ^ 3 ≤ (n + 1) ^ 8 * (2 * (n + 1) ^ 2) ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h₁ 3)
    _ = 8 * (n + 1) ^ 14 := by ring
    _ ≤ (n + 1) * (n + 1) ^ 14 := Nat.mul_le_mul_right _ (by omega)
    _ = (n + 1) ^ 15 := by ring

/-- An exponential instance: time `O(2 ^ n)` is strictly within time `O(2 ^ (4 * n))`. -/
example : DTIME encBits (2 ^ ·) ⊂ DTIME encBits fun n => 2 ^ (4 * n) := by
  refine DTIME_ssubset_DTIME timeConstructible_two_pow (fun n => Nat.lt_two_pow_self.le) ?_
  filter_upwards [PolynomiallyBounded.eventually_lt_two_pow (f := fun n => 8 * (n + 1) ^ 8)
    (by fun_prop)] with n hn
  have h₁ : 2 ^ n + 1 ≤ 2 * 2 ^ n := by
    have := Nat.one_le_two_pow (n := n)
    omega
  calc (n + 1) ^ 8 * (2 ^ n + 1) ^ 3 ≤ (n + 1) ^ 8 * (2 * 2 ^ n) ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h₁ 3)
    _ = 8 * (n + 1) ^ 8 * (2 ^ n) ^ 3 := by ring
    _ ≤ 2 ^ n * (2 ^ n) ^ 3 := Nat.mul_le_mul_right _ hn.le
    _ = 2 ^ (4 * n) := by ring

/-! ### Polynomial and exponential time -/

example : P encBits ⊂ EXP encBits := P_ssubset_EXP

example {α : Type} (enc : α ↪ List Bool) : P enc ⊆ EXP enc := P_subset_EXP

/-- The diagonal problem is a witness: in `EXP`, not in `P`. -/
example : {x | diagonal x = true} ∈ EXP encBits ∧ {x | diagonal x = true} ∉ P encBits :=
  ⟨setOf_diagonal_mem_EXP, diagonal_notMem_P⟩

/-- `P` is the union of the classes `DTIME (n ^ k)`. -/
example {α : Type} (enc : α ↪ List Bool) (A : Set α) :
    A ∈ P enc ↔ ∃ k, A ∈ DTIME enc (· ^ k) :=
  mem_P_iff_exists_mem_DTIME

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.DTIME_ssubset_DTIME' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.DTIME_ssubset_DTIME

/--
info: 'Cslib.Complexity.DTIME_ssubset_DTIME_of_clock' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.DTIME_ssubset_DTIME_of_clock

/--
info: 'Cslib.Complexity.setOf_timeDiagonal_mem_DTIME' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.setOf_timeDiagonal_mem_DTIME

/--
info: 'Cslib.Complexity.setOf_timeDiagonal_notMem_DTIME' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.setOf_timeDiagonal_notMem_DTIME

/--
info: 'Cslib.Complexity.computableInO_timeDiagonal' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.computableInO_timeDiagonal

/--
info: 'Cslib.Complexity.timeConstructible_succ_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.timeConstructible_succ_pow

/--
info: 'Cslib.Complexity.P_ssubset_EXP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.P_ssubset_EXP

/--
info: 'Cslib.Complexity.mem_P_iff_exists_mem_DTIME' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_P_iff_exists_mem_DTIME

end ComplexityTests.HierarchyTheorems

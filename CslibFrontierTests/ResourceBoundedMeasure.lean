/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.Measure.DTIME
import CslibFrontier.Computability.Complexity.Classes.Immune
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-! The standard enumeration of words, characteristic sequences, a constant p-martingale that
succeeds nowhere, a betting p-martingale that succeeds on the universe and fails on the empty
language, the Measure Conservation Theorem, and the measure zero of `P`, of `DTIME (2 ^ (k * n))`
and of finite sets in `E`. -/

namespace ComplexityTests.ResourceBoundedMeasure

open Cslib Cslib.Complexity Cslib.Complexity.Measure Turing Turing.MultiTapeTM

/-! ### The standard enumeration -/

/-- The first words of the standard enumeration: `λ, 0, 1, 00, 01, 10, 11, 000`. -/
example : stdIndex [] = 0 ∧ stdIndex [false] = 1 ∧ stdIndex [true] = 2 ∧
    stdIndex [false, false] = 3 ∧ stdIndex [false, true] = 4 ∧ stdIndex [true, false] = 5 ∧
    stdIndex [true, true] = 6 ∧ stdIndex [false, false, false] = 7 := by
  decide

example : stdWord 4 = [false, true] ∧ stdWord 5 = [true, false] := by
  rw [stdWord_eq_iff, stdWord_eq_iff]
  decide

/-- The characteristic sequence of the empty language is all zeros, that of the universe all
ones. -/
example (n : ℕ) : charPrefix ∅ n = List.replicate n false ∧
    charPrefix Set.univ n = List.replicate n true := by
  constructor <;>
  · refine List.ext_getElem (by simp) fun j hj _ => ?_
    rw [List.getElem_replicate, Bool.eq_iff_iff, getElem_charPrefix_eq_true_iff hj]
    simp

/-! ### Martingales -/

/-- A constant martingale is a p-martingale that succeeds on no language. -/
example : IsPMartingale (fun _ => (3 : ℝ)) ∧ successSet (fun _ => (3 : ℝ)) = ∅ := by
  refine ⟨?_, successSet_const 3⟩
  exact_mod_cast isPMartingale_const 3

/-- The martingale that bets all its capital on `1` at every bit: `2 ^ |w|` on the words of ones,
`0` elsewhere. -/
noncomputable def allIn (w : List Bool) : ℝ := if w.all id then 2 ^ w.length else 0

theorem isPMartingale_allIn : IsPMartingale allIn where
  isMartingale :=
    { nonneg := fun w => by unfold allIn; split <;> positivity
      average := fun w => by
        simp only [allIn, List.all_append, List.all_cons, List.all_nil, id, Bool.and_true,
          Bool.and_false, List.length_append, List.length_singleton, pow_succ]
        split <;> simp }
  exists_approx := ⟨fun p => if p.2.all id then 2 ^ (p.1 + p.2.length) else 0, by fun_prop,
    fun r w => by
      unfold allIn
      beta_reduce
      by_cases h : w.all id = true
      · rw [ite_eq_left h, ite_eq_left h, Nat.cast_pow, Nat.cast_ofNat, pow_add,
          mul_div_cancel_left₀ _ (by positivity), sub_self, abs_zero]
        positivity
      · rw [ite_eq_right h, ite_eq_right h, Nat.cast_zero, zero_div, sub_zero, abs_zero]
        positivity⟩

/-- The betting martingale succeeds on the universe. -/
theorem univ_mem_successSet_allIn : Set.univ ∈ successSet allIn := by
  rw [mem_successSet_iff]
  intro C
  obtain ⟨n, hn⟩ := exists_nat_gt C
  refine ⟨n, ?_⟩
  have h : charPrefix Set.univ n = List.replicate n true :=
    List.ext_getElem (by simp) fun j hj _ => by
      rw [List.getElem_replicate, Bool.eq_iff_iff, getElem_charPrefix_eq_true_iff hj]
      simp
  have : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
  have hall : (List.replicate n true).all id = true := by simp
  rw [allIn, h, ite_eq_left hall, List.length_replicate]
  linarith

/-- The betting martingale fails on the empty language: it goes broke at the first bit. -/
example : ∅ ∉ successSet allIn := by
  rw [notMem_successSet_iff]
  refine ⟨1, fun n => ?_⟩
  have h : charPrefix ∅ n = List.replicate n false :=
    List.ext_getElem (by simp) fun j hj _ => by
      rw [List.getElem_replicate, Bool.eq_iff_iff, getElem_charPrefix_eq_true_iff hj]
      simp
  rcases n with _ | n
  · simp [allIn, charPrefix]
  · simp [allIn, h, List.all_replicate]

/-- So the singleton of the universe has p-measure zero. -/
example : HasPMeasureZero {Set.univ} :=
  hasPMeasureZero_iff.mpr
    ⟨allIn, isPMartingale_allIn, Set.singleton_subset_iff.mpr univ_mem_successSet_allIn⟩

/-! ### Measure in `E` -/

/-- **The Measure Conservation Theorem.** -/
example : ¬ HasPMeasureZero (E encBits) ∧ ¬ HasMeasureZeroInE (E encBits) :=
  ⟨not_hasPMeasureZero_E, not_hasMeasureZeroInE_E⟩

/-- `P`, each `DTIME (2 ^ (k * n))` and their unions have measure zero in `E`. -/
example : HasMeasureZeroInE (P encBits ∪ DTIME encBits fun n => 2 ^ (3 * n)) :=
  hasMeasureZeroInE_P.union (hasMeasureZeroInE_DTIME 3)

/-- So `E` is not `P`, and not `DTIME (2 ^ (2 * n))`. -/
example : ∃ A ∈ E encBits, A ∉ P encBits := hasMeasureZeroInE_P.exists_mem_E_notMem

example : DTIME encBits (fun n => 2 ^ (2 * n)) ⊂ E encBits := DTIME_ssubset_E 2

/-- A finite set of languages in `E` has p-measure zero. -/
example : HasPMeasureZero {∅, Set.univ} := by
  refine (Set.toFinite _).hasPMeasureZero fun A hA => ?_
  rcases hA with rfl | rfl
  · exact P_subset_E (Set.finite_empty.mem_P)
  · exact P_subset_E univ_mem_P

end ComplexityTests.ResourceBoundedMeasure

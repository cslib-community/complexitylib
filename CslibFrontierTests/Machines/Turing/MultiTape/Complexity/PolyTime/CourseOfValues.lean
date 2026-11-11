/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.CourseOfValues
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! # Tests for course-of-values stage tables and polynomial-time certificates -/

open Cslib Turing.MultiTapeTM

private def lengthStep (T : List ℕ) : ℕ := T.length

private def minLenStep (cap : ℕ) (T : List ℕ) : ℕ := min cap T.length

example :
    List.courseOfValues lengthStep 0 = [] ∧
    List.courseOfValues lengthStep 4 = [0, 1, 2, 3] ∧
    (List.courseOfValues lengthStep 4).getD 2 99 = 2 ∧
    (List.courseOfValues lengthStep 4).take 2 = List.courseOfValues lengthStep 2 ∧
    List.courseOfValues lengthStep 4 =
      List.courseOfValues (fun T : List ℕ => if T.length < 4 then T.length else 99) 4 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · decide
  · exact List.take_courseOfValues lengthStep (by decide)
  · refine List.courseOfValues_congr fun m hm => ?_
    simp [lengthStep, List.length_courseOfValues, hm]

private theorem computableInPolyTime_lengthStep :
    ComputableInPolyTime lengthStep (encList encUnary) encUnary := by
  unfold lengthStep
  fun_prop

private theorem computableInPolyTime_minLenStep :
    ComputableInPolyTime (fun p : ℕ × List ℕ => minLenStep p.1 p.2)
      (encPair encUnary (encList encUnary)) encUnary := by
  unfold minLenStep
  fun_prop

-- Framed-list unary course-of-values, final value, captured-parameter/input variants, raw
-- bit-table variants, and exponential growth failure along reachable prefixes.
example :
    ComputableInPolyTime (List.courseOfValues lengthStep) encUnary (encList encUnary) ∧
    ComputableInPolyTime (List.courseOfValuesVal lengthStep) encUnary encUnary ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => List.courseOfValues (minLenStep p.2) p.1)
      (encPair encUnary encUnary) (encList encUnary) ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => List.courseOfValues (minLenStep p.2) p.1)
      (encPair encUnary encUnary) (encList encUnary) ∧
    ComputableInPolyTime
      (fun p : ℕ × Bool => List.courseOfValues (fun T : List Bool => p.2 && T.isEmpty) p.1)
      (encPair encUnary encBool) encBits ∧
    ComputableInPolyTime (List.courseOfValues fun T : List Bool => T.isEmpty) encUnary encBits ∧
    ComputableInPolyTime (List.courseOfValuesVal fun T : List Bool => T.isEmpty) encUnary encBool ∧
    ¬ (∀ n, ∀ i < n,
      (encUnary (List.courseOfValuesVal (fun T : List ℕ => 2 ^ T.length) i)).length ≤ n + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ComputableInPolyTime.courseOfValues computableInPolyTime_lengthStep .id fun n i hi => by
      simp [List.courseOfValuesVal, lengthStep, hi.le]
  · exact ComputableInPolyTime.courseOfValuesVal computableInPolyTime_lengthStep .id
      fun n i hi => by
        simp [List.courseOfValuesVal, lengthStep, hi.le]
  · refine ComputableInPolyTime.courseOfValuesWith
      (ComputableInPolyTime.snd encUnary encUnary) (ComputableInPolyTime.fst encUnary encUnary)
      computableInPolyTime_minLenStep (elemBound := fun p => p.2) ?_ fun p i _ => by
        simp [List.courseOfValuesVal, minLenStep]
    exact (ComputableInPolyTime.snd encUnary encUnary).polyBounded
  · refine ComputableInPolyTime.courseOfValuesWithInput
      (count := Prod.fst) (step := fun p T => minLenStep p.2 T)
      (ComputableInPolyTime.fst encUnary encUnary) ?_ (elemBound := fun p => p.2) ?_
      fun p i _ => by
        simp [List.courseOfValuesVal, minLenStep]
    · unfold minLenStep; fun_prop
    · exact (ComputableInPolyTime.snd encUnary encUnary).polyBounded
  · refine ComputableInPolyTime.bitsCourseOfValuesWith
      (step := fun (q : Bool) (T : List Bool) => q && T.isEmpty)
      (ComputableInPolyTime.snd encUnary encBool) (ComputableInPolyTime.fst encUnary encBool) ?_
    fun_prop
  · refine ComputableInPolyTime.bitsCourseOfValues ?_
    fun_prop
  · refine ComputableInPolyTime.bitsCourseOfValuesVal ?_
    fun_prop
  · intro h
    have h4 := h 5 4 (by decide)
    simp [List.courseOfValuesVal, encUnary_apply, List.length_courseOfValues] at h4

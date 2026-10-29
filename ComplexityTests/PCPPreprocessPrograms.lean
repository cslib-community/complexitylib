/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Encoded.Preprocess.Programs
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.Walk
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite

/-! Preprocessing rotations preserve edge identity, orientation, return labels and runtime costs. -/

namespace ComplexityTests.PreprocessPrograms

open Cslib Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

private def reflection (n : ℕ) : RotationMap (Fin n) Bool where
  rot p := (p.1.rev, !p.2)
  rot_involutive p := by simp

private def rotateReflection (p : ℕ × (ℕ × Bool)) : ℕ × Bool :=
  (p.1 - 1 - p.2.1, !p.2.2)

private theorem rotateReflection_eq (n : ℕ) (v : Fin n) (d : Bool) :
    rotateReflection (n, v.val, d) =
      (((reflection n).rot (v, d)).1.val, ((reflection n).rot (v, d)).2) := by
  simp [rotateReflection, reflection, Nat.sub_sub, Nat.add_comm]

private theorem isPolyTime_rotateReflection :
    ComputableTidilyInPolyTime rotateReflection
      (encPair encUnary (encPair encUnary encBool)) (encPair encUnary encBool) := by
  unfold rotateReflection
  fun_prop

private def exampleGraph : Graph Bool :=
  ⟨3, [⟨0, 1, false⟩, ⟨1, 1, false⟩, ⟨0, 1, true⟩]⟩

private def original : ConstraintGraph.PreprocessLabel Bool := .inl (.inl (.inl ()))
private def cloud (d : Bool) : ConstraintGraph.PreprocessLabel Bool := .inl (.inl (.inr d))
private def whole (d : Bool) : ConstraintGraph.PreprocessLabel Bool := .inl (.inr d)
private def loop : ConstraintGraph.PreprocessLabel Bool := .inr ()

example : exampleGraph.preprocessRotation false rotateReflection ((0, false), original) =
    ((0, true), original) := by decide

example : exampleGraph.preprocessRotation false rotateReflection ((0, false), cloud false) =
    ((2, false), cloud true) := by decide

example : exampleGraph.preprocessRotation false rotateReflection ((0, false), whole false) =
    ((2, true), whole true) := by decide

example : exampleGraph.preprocessRotation false rotateReflection ((1, true), loop) =
    ((1, true), loop) := by decide

example : (Graph.mk 0 ([] : List (Edge Bool))).preprocessRotation false rotateReflection
    ((7, true), cloud false) = ((7, true), cloud true) := by decide

example : RotationMap.powRotWithInput
    (fun p : Graph Bool × ((ℕ × Bool) × ConstraintGraph.PreprocessLabel Bool) =>
      p.1.preprocessRotation false rotateReflection p.2) 3
    (exampleGraph, (0, false), ![original, cloud false, whole false]) =
    ((0, false), ![whole true, cloud true, original]) := by decide

example (g : Graph Bool) (v : Fin g.edges.length × Bool)
    (d : ConstraintGraph.PreprocessLabel Bool) :
    g.preprocessRotation false rotateReflection ((v.1.val, v.2), d) =
      let next := (g.regularPreprocess (fun c (_ _ : Bool) => c) false reflection).graph.rot (v, d)
      ((next.1.1.val, next.1.2), next.2) :=
  g.preprocessRotation_eq _ false reflection rotateReflection rotateReflection_eq v d

private def constraintEval (c a b : Bool) : Bool := c || (!a || b)

example : exampleGraph.preprocessRelation constraintEval false
    ((0, false), original) true false = false := by decide

example : exampleGraph.preprocessRelation constraintEval false
    ((0, true), original) true false = true := by decide

example : exampleGraph.preprocessRelation constraintEval false
    ((0, false), cloud false) true false = false := by decide

example : exampleGraph.preprocessRelation constraintEval false
    ((0, false), whole false) true false = true := by decide

attribute [local fun_prop] ComputableInPolyTime.tidy in
example : ComputableInPolyTime
    (fun p : Graph Bool × ((ℕ × Bool) × ConstraintGraph.PreprocessLabel Bool) =>
      p.1.preprocessRotation false rotateReflection p.2)
    (encPair (Graph.encoding encBool)
      (encPair (encPair encUnary encBool) (encFinEnum (ConstraintGraph.PreprocessLabel Bool))))
    (encPair (encPair encUnary encBool) (encFinEnum (ConstraintGraph.PreprocessLabel Bool))) := by
  have h := isPolyTime_rotateReflection
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
example : ComputableInPolyTime
    (fun g : Graph Bool => g.preprocessRotation false rotateReflection ((g.edges.length, false),
      cloud false))
    (Graph.encoding encBool)
    (encPair (encPair encUnary encBool) (encFinEnum (ConstraintGraph.PreprocessLabel Bool))) := by
  have h := isPolyTime_rotateReflection
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
private theorem isPolyTime_preprocessRotation_finEnum : ComputableInPolyTime
    (fun p : Graph Bool × ((ℕ × Bool) × ConstraintGraph.PreprocessLabel Bool) =>
      p.1.preprocessRotation false rotateReflection p.2)
    (encPair (Graph.encoding encBool)
      (encPair (encPair encUnary encBool) (encFinEnum (ConstraintGraph.PreprocessLabel Bool))))
    (encPair (encPair encUnary encBool) (encFinEnum (ConstraintGraph.PreprocessLabel Bool))) := by
  have h := isPolyTime_rotateReflection
  fun_prop

example (T : ℕ) : ComputableInPolyTime
    (RotationMap.powRotWithInput
      (fun p : Graph Bool × ((ℕ × Bool) × ConstraintGraph.PreprocessLabel Bool) =>
        p.1.preprocessRotation false rotateReflection p.2) T)
    (encPair (Graph.encoding encBool)
      (encPair (encPair encUnary encBool)
        (encPi (encFinEnum (ConstraintGraph.PreprocessLabel Bool)))))
    (encPair (encPair encUnary encBool)
      (encPi (encFinEnum (ConstraintGraph.PreprocessLabel Bool)))) := by
  have hrot := isPolyTime_preprocessRotation_finEnum
  fun_prop

end ComplexityTests.PreprocessPrograms

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Encoded.AddTrivial
import Complexity.Computability.PCP.Encoded.CloudRotation
import Complexity.Tactic.PolyTime

/-! Executable constraint graphs, boundary cases, interpretation and compositional certificates. -/

namespace ComplexityTests.PCPEncoded

open Cslib.PCP Cslib.PCP.Encoded

open Turing.MultiTapeTM

private def equalityOrTrue (c a b : Bool) : Bool :=
  c || (a == b)

private def oneEdge : Graph Bool :=
  ⟨2, [⟨0, 1, false⟩]⟩

example : oneEdge.addLoops true =
    ⟨2, [⟨0, 1, false⟩, ⟨0, 0, true⟩, ⟨1, 1, true⟩]⟩ := by decide

example : oneEdge.isWellFormed = true := by decide

example : (Graph.mk 1 [Edge.mk 0 1 false]).isWellFormed = false := by decide

example : oneEdge.WellFormed :=
  (Graph.isWellFormed_eq_true oneEdge).mp (by decide)

example : (oneEdge.addLoops true).WellFormed :=
  (Graph.isWellFormed_eq_true oneEdge).mp (by decide) |>.addLoops true

example : oneEdge.checkEdge equalityOrTrue true false [false, false] 0 = true := by decide

example : oneEdge.checkEdge equalityOrTrue true false [false, true] 0 = false := by decide

example : oneEdge.checkEdge equalityOrTrue true false [] 3 = true := by decide

example : (Graph.addLoops true ⟨0, []⟩ : Graph Bool) = ⟨0, []⟩ := by decide

example : ((oneEdge.addLoops true).toGraph equalityOrTrue).Satisfiable := by
  apply (oneEdge.satisfiable_addLoops_iff equalityOrTrue true (by intros; rfl)).mpr
  exact ⟨fun _ => false, fun i => by
    simp [Graph.toGraph, ConstraintGraph.Satisfies, oneEdge, equalityOrTrue,
      List.get_eq_getElem]⟩

example : ((oneEdge.addLoops true).toGraph equalityOrTrue).unsatVal =
    (1 : ℝ) / 3 * (oneEdge.toGraph equalityOrTrue).unsatVal := by
  have h := oneEdge.unsatVal_addLoops equalityOrTrue true (by intros; rfl)
  norm_num only [oneEdge, List.length_singleton, Nat.cast_one, Nat.cast_ofNat] at h
  simpa only [show (1 : ℝ) + 2 = 3 from by norm_num] using h

-- A positive-value instance checks the dilution formula beyond the satisfiable case.
private theorem rejectingEdge_value :
    (oneEdge.toGraph (fun c (_ _ : Bool) => c)).unsatVal = 1 := by
  have hnot : ¬ (oneEdge.toGraph (fun c (_ _ : Bool) => c)).Satisfiable := by
    rintro ⟨σ, hσ⟩
    exact Bool.false_ne_true (hσ ⟨0, by decide⟩)
  apply le_antisymm (ConstraintGraph.unsatVal_le_one _)
  simpa [oneEdge] using
    (oneEdge.toGraph (fun c (_ _ : Bool) => c)).inv_card_le_unsatVal hnot

example : ((oneEdge.addLoops true).toGraph (fun c (_ _ : Bool) => c)).unsatVal = 1 / 3 := by
  have h := oneEdge.unsatVal_addLoops (fun c (_ _ : Bool) => c) true (by intros; rfl)
  rw [rejectingEdge_value] at h
  norm_num [oneEdge] at h ⊢
  exact h

example : ComputableInPolyTime (Graph.addLoops true)
    (Graph.encoding encBool) (Graph.encoding encBool) := by polytime

example : ComputableInPolyTime (fun g : Graph Bool =>
    Graph.mk g.vertices (g.edges ++ (List.range g.vertices).map (fun v => ⟨v, v, true⟩)))
    (Graph.encoding encBool) (Graph.encoding encBool) := by polytime

example : ComputableInPolyTime (fun p : Bool × Graph Bool =>
    let g := p.2.addLoops true
    g.checkEdge equalityOrTrue true false [p.1, false] 0)
    (encPair encBool (Graph.encoding encBool)) encBool := by
  have heval : ComputableInPolyTime
      (fun p : Bool × Bool × Bool => equalityOrTrue p.1 p.2.1 p.2.2)
      (encPair encBool (encPair encBool encBool)) encBool :=
    .of_finite _
  fun_prop

example {C α : Type} (enc : C ↪ List Bool) (alphabet : α ↪ List Bool)
    (eval : C → α → α → Bool) (fallback : C) (label : α)
    (heval : ComputableInPolyTime (fun p : C × α × α => eval p.1 p.2.1 p.2.2)
      (encPair enc (encPair alphabet alphabet)) encBool) :
    ComputableInPolyTime
      (fun p : Graph C × List α × ℕ =>
        p.1.checkEdge eval fallback label p.2.1 (p.2.2 + 1))
      (encPair (Graph.encoding enc) (encPair (encList alphabet) encUnary)) encBool := by
  polytime

example : ComputableInPolyTime
    (fun p : Graph Bool × List Bool × ℕ =>
      p.1.checkEdge equalityOrTrue true false p.2.1 p.2.2)
    (encPair (Graph.encoding encBool) (encPair encBits encUnary)) encBool := by
  unfold Graph.checkEdge equalityOrTrue
  polytime

end ComplexityTests.PCPEncoded


namespace ComplexityTests.PCPEncodedCloud

open Cslib Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

-- Reflection moves vertices and exchanges the two return labels; no spectral claim is needed.
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
    ComputableInPolyTime rotateReflection
      (encPair encUnary (encPair encUnary encBool)) (encPair encUnary encBool) := by
  unfold rotateReflection
  polytime

-- A loop and parallel edges give different cloud sizes while keeping all half-edge identities.
private def cloudGraph : Graph Bool :=
  ⟨3, [⟨0, 1, false⟩, ⟨1, 1, false⟩, ⟨0, 1, true⟩]⟩

example : cloudGraph.cloud false 0 = [(0, false), (2, false)] := by decide

example : cloudGraph.cloud false 1 =
    [(0, true), (1, false), (1, true), (2, true)] := by decide

example : cloudGraph.cloud false 2 = [] := by decide

example : cloudGraph.cloudRotation false rotateReflection ((0, true), false) =
    ((2, true), true) := by decide

example : cloudGraph.cloudRotation false rotateReflection ((2, true), true) =
    ((0, true), false) := by decide

-- A malformed reply uses the original half-edge as fallback and retains the supplied return label.
example : cloudGraph.cloudRotation false (fun p => (100, !p.2.2)) ((1, false), false) =
    ((1, false), true) := by decide

example : (Graph.mk 0 ([] : List (Edge Bool))).cloudRotation false rotateReflection
    ((3, true), false) = ((3, true), true) := by decide

example : ComputableInPolyTime
    (fun p : Graph Bool × ((ℕ × Bool) × Bool) =>
      p.1.cloudRotation false rotateReflection p.2)
    (encPair (Graph.encoding encBool) (encPair (encPair encUnary encBool) encBool))
    (encPair (encPair encUnary encBool) encBool) := by
  have hrotate := isPolyTime_rotateReflection
  fun_prop

example (rotate : ℕ × (ℕ × Bool) → ℕ × Bool)
    (hrotate : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary encBool)) (encPair encUnary encBool)) :
    ComputableInPolyTime
      (fun p : Graph Bool × ((ℕ × Bool) × Bool) =>
        let members := p.1.cloud false (p.1.endpoint false p.2.1)
        let next := rotate (members.length, members.idxOf p.2.1, p.2.2)
        (members[next.1]?.getD p.2.1, next.2))
      (encPair (Graph.encoding encBool) (encPair (encPair encUnary encBool) encBool))
      (encPair (encPair encUnary encBool) encBool) := by polytime

example :
    cloudGraph.cloudRotation false rotateReflection ((0, true), false) =
      let next := (cloudGraph.cloudFamily (fun c (_ _ : Bool) => c) false reflection 1).rot
        (⟨(⟨0, by decide⟩, true), rfl⟩, false)
      ((next.1.val.1.val, next.1.val.2), next.2) := by decide

example : ((cloudGraph.cloudEquiv (fun c (_ _ : Bool) => c) false 1).symm
    ⟨(⟨1, by decide⟩, true), rfl⟩).val = 2 := by decide

end ComplexityTests.PCPEncodedCloud

/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Preprocess
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Tactic.PolyTime

/-!
# Rotation and constraint programs for preprocessing

The edge-list construction and random-walk algorithms use the same numbered half-edges.
These programs expose the complete rotation, including the return label, without rebuilding
the preprocessed edge list for each call. Cloud search, numerical family rotation, constraint
lookup and every copied runtime graph are charged by the joint certificates.

## Main definitions

* `Cslib.PCP.Encoded.Graph.preprocessRotation`: rotate on a numbered half-edge.
* `Cslib.PCP.Encoded.Graph.preprocessRelation`: evaluate the constraint on a dart.

## Main results

* `Cslib.PCP.Encoded.Graph.preprocessRotation_eq`: exact mathematical rotation and return label.
* `Cslib.PCP.Encoded.Graph.preprocessRelation_eq_true`: exact mathematical constraint.
* `Cslib.PCP.Encoded.Graph.isPolyTime_preprocessRotation`: uniform joint rotation certificate.
* `Cslib.PCP.Encoded.Graph.isPolyTime_preprocessRelation`: uniform evaluation certificate.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Turing.MultiTapeTM ConstraintGraph

variable {C α D : Type}

/-- Decode a numbered half-edge into its edge index and endpoint bit. -/
def halfEdgeOfNumber (n : ℕ) : ℕ × Bool :=
  (n / 2, decide (n % 2 = 1))

/-- Numbering retains both the edge identity and its endpoint. -/
@[simp]
theorem halfEdgeOfNumber_halfEdgeNumber (p : ℕ × Bool) :
    halfEdgeOfNumber (halfEdgeNumber p) = p := by
  rcases p with ⟨n, b⟩
  cases b <;> simp [halfEdgeOfNumber, halfEdgeNumber, Nat.add_div, Nat.add_mod]

/-- The executable inverse agrees with the finite half-edge numbering. -/
private theorem halfEdgeOfNumber_eq (edges : ℕ) (v : Fin (2 * edges)) :
    halfEdgeOfNumber v.val = ((halfEdgeEquiv edges).symm v |>.1.val,
      ((halfEdgeEquiv edges).symm v).2) := by
  rw [← Equiv.apply_symm_apply (halfEdgeEquiv edges) v, halfEdgeEquiv_val,
    halfEdgeOfNumber_halfEdgeNumber]
  simp

/-- Dividing by two and reading the low bit are polynomial-time in the unary vertex name. -/
@[fun_prop]
theorem isPolyTime_halfEdgeOfNumber : ComputableInPolyTime halfEdgeOfNumber
    encUnary (encPair encUnary encBool) := by
  unfold halfEdgeOfNumber
  fun_prop

/-- Rotate on one of the four kinds of preprocessed darts, retaining its return label. -/
def preprocessRotation (fallback : C) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (g : Graph C) (p : (ℕ × Bool) × PreprocessLabel D) :
    (ℕ × Bool) × PreprocessLabel D :=
  match p.2 with
  | .inl (.inl (.inl _)) => ((p.1.1, !p.1.2), p.2)
  | .inl (.inl (.inr d)) =>
    let next := g.cloudRotation fallback rotate (p.1, d)
    (next.1, .inl (.inl (.inr next.2)))
  | .inl (.inr d) =>
    let next := rotate (2 * g.edges.length, halfEdgeNumber p.1, d)
    (halfEdgeOfNumber next.1, .inl (.inr next.2))
  | .inr _ => p

/-- Original edges retain their orientation, cloud edges check equality, and new edges accept. -/
def preprocessRelation [DecidableEq α] (eval : C → α → α → Bool) (fallback : C)
    (g : Graph C) (p : (ℕ × Bool) × PreprocessLabel D) (a b : α) : Bool :=
  match p.2 with
  | .inl (.inl (.inl _)) =>
    let constraint := (g.edgeAt fallback p.1.1).constraint
    if p.1.2 then eval constraint b a else eval constraint a b
  | .inl (.inl (.inr _)) => decide (a = b)
  | .inl (.inr _) => true
  | .inr _ => true

/-- Exact agreement on the existing half-edges needs no claim about malformed vertex names. -/
theorem preprocessRotation_eq (g : Graph C) (eval : C → α → α → Bool) (fallback : C)
    (family : (n : ℕ) → RotationMap (Fin n) D) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
      (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))
    (v : Fin g.edges.length × Bool) (d : PreprocessLabel D) :
    g.preprocessRotation fallback rotate ((v.1.val, v.2), d) =
      let next := (g.regularPreprocess eval fallback family).graph.rot (v, d)
      ((next.1.1.val, next.1.2), next.2) := by
  rcases d with ((u | d) | d) | u
  · rfl
  · exact congrArg (fun p => (p.1, Sum.inl (Sum.inl (Sum.inr p.2))))
      (g.cloudRotation_eq eval fallback family rotate hrotate
        ((g.toGraph eval).endpoint v) ⟨v, rfl⟩ d)
  · change (halfEdgeOfNumber (rotate (2 * g.edges.length,
        halfEdgeNumber (v.1.val, v.2), d)).1,
        Sum.inl (Sum.inr (rotate (2 * g.edges.length,
          halfEdgeNumber (v.1.val, v.2), d)).2)) = _
    rw [← halfEdgeEquiv_val, hrotate, halfEdgeOfNumber_eq]
    rfl
  · rfl

/-- The executable constraint is the existing mathematical preprocessing constraint. -/
theorem preprocessRelation_eq_true [DecidableEq α] (g : Graph C)
    (eval : C → α → α → Bool) (fallback : C) (family : (n : ℕ) → RotationMap (Fin n) D)
    (v : Fin g.edges.length × Bool) (d : PreprocessLabel D) (a b : α) :
    g.preprocessRelation eval fallback ((v.1.val, v.2), d) a b = true ↔
      (g.regularPreprocess eval fallback family).rel (v, d) a b := by
  rcases d with ((u | d) | d) | u
  · rcases v with ⟨v, side⟩
    cases side <;> simp [preprocessRelation, regularPreprocess, ConstraintGraph.degreeReduce,
      RegularConstraintGraph.addLoops, RegularConstraintGraph.addTrivial,
      RegularConstraintGraph.union, edgeAt, toGraph, Function.flip_def]
  · simp [preprocessRelation, regularPreprocess, ConstraintGraph.degreeReduce,
      RegularConstraintGraph.addLoops, RegularConstraintGraph.addTrivial,
      RegularConstraintGraph.union]
  · simp [preprocessRelation, regularPreprocess, RegularConstraintGraph.addLoops,
      RegularConstraintGraph.addTrivial, RegularConstraintGraph.union,
      RegularConstraintGraph.unconstrained]
  · simp [preprocessRelation, regularPreprocess, RegularConstraintGraph.addLoops,
      RegularConstraintGraph.addTrivial, RegularConstraintGraph.union,
      RegularConstraintGraph.unconstrained]

variable {enc : C ↪ List Bool} {labelEncoding : D ↪ List Bool}
  {dartEncoding : PreprocessLabel D ↪ List Bool}

/-- A fixed finite dart label selects a branch; each branch charges the runtime graph and vertex.
The numerical rotation certificate is joint in size, vertex and edge label. -/
private theorem polytime_preprocessRotation [Finite D] (fallback : C)
    (rotate : ℕ × (ℕ × D) → ℕ × D)
    (hrotate : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary labelEncoding)) (encPair encUnary labelEncoding)) :
    ComputableInPolyTime
      (fun p : Graph C × ((ℕ × Bool) × PreprocessLabel D) =>
        p.1.preprocessRotation fallback rotate p.2)
      (encPair (encoding enc) (encPair (encPair encUnary encBool) dartEncoding))
      (encPair (encPair encUnary encBool) dartEncoding) := by
  have hbranch (d : PreprocessLabel D) : ComputableInPolyTime
      (fun p : Graph C × ((ℕ × Bool) × PreprocessLabel D) =>
        p.1.preprocessRotation fallback rotate (p.2.1, d))
      (encPair (encoding enc) (encPair (encPair encUnary encBool) dartEncoding))
      (encPair (encPair encUnary encBool) dartEncoding) := by
    rcases d with ((u | d) | d) | u
    · simp only [preprocessRotation]
      fun_prop
    · have hcloud : ComputableInPolyTime
          (fun p : Graph C × ((ℕ × Bool) × PreprocessLabel D) =>
            p.1.cloudRotation fallback rotate (p.2.1, d))
          (encPair (encoding enc) (encPair (encPair encUnary encBool) dartEncoding))
          (encPair (encPair encUnary encBool) labelEncoding) :=
        isPolyTime_cloudRotation (.fst _ _)
          (((ComputableInPolyTime.snd _ _).fst').prod (.const d)) hrotate fallback
      have hlabel : ComputableInPolyTime
          (fun d : D => (Sum.inl (Sum.inl (Sum.inr d)) : PreprocessLabel D))
          labelEncoding dartEncoding := .of_finite _
      exact hcloud.fst'.prod (hlabel.comp hcloud.snd')
    · have hnext : ComputableInPolyTime
          (fun p : Graph C × ((ℕ × Bool) × PreprocessLabel D) =>
            rotate (2 * p.1.edges.length, halfEdgeNumber p.2.1, d))
          (encPair (encoding enc) (encPair (encPair encUnary encBool) dartEncoding))
          (encPair encUnary labelEncoding) := by
        fun_prop
      have hlabel : ComputableInPolyTime
          (fun d : D => (Sum.inl (Sum.inr d) : PreprocessLabel D))
          labelEncoding dartEncoding := .of_finite _
      exact (isPolyTime_halfEdgeOfNumber.comp hnext.fst').prod (hlabel.comp hnext.snd')
    · simp only [preprocessRotation]
      fun_prop
  exact ((ComputableInPolyTime.snd _ _).snd').finite_cases hbranch

/-- Constraint evaluation charges the original descriptor and both endpoint labels. -/
private theorem polytime_preprocessRelation [Finite D] [DecidableEq α]
    {alphabet : α ↪ List Bool} (eval : C → α → α → Bool) (fallback : C)
    (heval : ComputableInPolyTime (fun p : C × (α × α) => eval p.1 p.2.1 p.2.2)
      (encPair enc (encPair alphabet alphabet)) encBool) :
    ComputableInPolyTime
      (fun p : Graph C × (((ℕ × Bool) × PreprocessLabel D) × (α × α)) =>
        p.1.preprocessRelation eval fallback p.2.1 p.2.2.1 p.2.2.2)
      (encPair (encoding enc)
        (encPair (encPair (encPair encUnary encBool) dartEncoding) (encPair alphabet alphabet)))
      encBool := by
  have hbranch (d : PreprocessLabel D) : ComputableInPolyTime
      (fun p : Graph C × (((ℕ × Bool) × PreprocessLabel D) × (α × α)) =>
        p.1.preprocessRelation eval fallback (p.2.1.1, d) p.2.2.1 p.2.2.2)
      (encPair (encoding enc)
        (encPair (encPair (encPair encUnary encBool) dartEncoding) (encPair alphabet alphabet)))
      encBool := by
    rcases d with ((u | d) | d) | u <;> simp only [preprocessRelation] <;> fun_prop
  exact ((ComputableInPolyTime.snd _ _).fst'.snd').finite_cases hbranch

/-- Computed graph and dart arguments determine their encodings before composition. -/
@[fun_prop]
theorem isPolyTime_preprocessRotation [Finite D] {Input : Type} {input : Input ↪ List Bool}
    {graph : Input → Graph C} {dart : Input → (ℕ × Bool) × PreprocessLabel D}
    {rotate : ℕ × (ℕ × D) → ℕ × D}
    (hgraph : ComputableInPolyTime graph input (encoding enc))
    (hdart : ComputableInPolyTime dart input
      (encPair (encPair encUnary encBool) dartEncoding))
    (hrotate : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary labelEncoding)) (encPair encUnary labelEncoding))
    (fallback : C) : ComputableInPolyTime
      (fun x => (graph x).preprocessRotation fallback rotate (dart x))
      input (encPair (encPair encUnary encBool) dartEncoding) := by
  have hf := polytime_preprocessRotation (enc := enc) (dartEncoding := dartEncoding)
    fallback rotate hrotate
  have hg := hgraph.prod hdart
  simpa only [Function.comp_def] using hf.comp hg

/-- Computed constraints and labels use the same evaluator under any fixed label encoding. -/
@[fun_prop]
theorem isPolyTime_preprocessRelation [Finite D] [DecidableEq α]
    {Input : Type} {input : Input ↪ List Bool} {alphabet : α ↪ List Bool}
    {graph : Input → Graph C} {dart : Input → (ℕ × Bool) × PreprocessLabel D}
    {left right : Input → α} {eval : C → α → α → Bool}
    (hgraph : ComputableInPolyTime graph input (encoding enc))
    (hdart : ComputableInPolyTime dart input
      (encPair (encPair encUnary encBool) dartEncoding))
    (heval : ComputableInPolyTime (fun p : C × (α × α) => eval p.1 p.2.1 p.2.2)
      (encPair enc (encPair alphabet alphabet)) encBool)
    (hleft : ComputableInPolyTime left input alphabet)
    (hright : ComputableInPolyTime right input alphabet) (fallback : C) :
    ComputableInPolyTime
      (fun x => (graph x).preprocessRelation eval fallback (dart x) (left x) (right x))
      input encBool :=
  (polytime_preprocessRelation (dartEncoding := dartEncoding) eval fallback heval).comp
    (hgraph.prod (hdart.prod (hleft.prod hright)))

end Cslib.PCP.Encoded.Graph

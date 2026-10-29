/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Encoded.Amplification
import ComplexityTests.PCPNumbering
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.Family
import Complexity.Tactic.PolyTime
import Mathlib.Tactic.FinCases

/-! Complete small walk enumeration, nontrivial constraints, exact interpretation and cost. -/

namespace ComplexityTests.PCPEncodedPower

open Cslib Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

private def reflection (n : ℕ) : RotationMap (Fin n) Unit where
  rot p := (p.1.rev, p.2)
  rot_involutive p := by simp

private def rotateReflection (p : ℕ × (ℕ × Unit)) : ℕ × Unit :=
  (p.1 - 1 - p.2.1, p.2.2)

private theorem rotateReflection_eq (n : ℕ) (v : Fin n) (d : Unit) :
    rotateReflection (n, v.val, d) =
      (((reflection n).rot (v, d)).1.val, ((reflection n).rot (v, d)).2) := by
  simp [rotateReflection, reflection, Nat.sub_sub, Nat.add_comm]

private theorem isPolyTime_rotateReflection :
    ComputableTidilyInPolyTime rotateReflection
      (encPair encUnary (encPair encUnary (encFinEnum Unit)))
      (encPair encUnary (encFinEnum Unit)) := by
  unfold rotateReflection
  fun_prop

private def original : ConstraintGraph.PreprocessLabel Unit := .inl (.inl (.inl ()))
private def cloud : ConstraintGraph.PreprocessLabel Unit := .inl (.inl (.inr ()))
private def whole : ConstraintGraph.PreprocessLabel Unit := .inl (.inr ())
private def loop : ConstraintGraph.PreprocessLabel Unit := .inr ()

private def allLabels : List (ConstraintGraph.PreprocessLabel Unit) :=
  [original, cloud, whole, loop]

private def walks : List (Graph.PowerLabel Unit 1 2) :=
  allLabels.flatMap fun d => [(fun _ => d, fun _ => 0), (fun _ => d, fun _ => 1)]

private theorem nodup_walks : walks.Nodup := by decide

private theorem mem_walks (d : Graph.PowerLabel Unit 1 2) : d ∈ walks := by
  rcases d with ⟨k, c⟩
  have hk : k = fun _ => k 0 := funext fun i => congrArg k (Subsingleton.elim i 0)
  have hc : c = fun _ => c 0 := funext fun i => congrArg c (Subsingleton.elim i 0)
  rw [hk, hc]
  generalize hk0 : k 0 = tag
  generalize hc0 : c 0 = signal
  fin_cases signal <;> rcases tag with ((u | u) | u) | u <;> cases u <;> decide

private def exampleGraph : Graph Bool := ⟨2, [⟨0, 1, false⟩]⟩
private def evalConstraint (constraint : Bool) (_ _ : Bool) := constraint

private def powered (g : Graph Bool) :=
  g.powerPreprocess evalConstraint false rotateReflection 1 2 walks

-- The occurrence contract keeps each half-edge's supplied walk order.
example : (exampleGraph.powerPreprocessEnumeration evalConstraint false rotateReflection 1 2
    walks nodup_walks mem_walks).equiv ⟨8, by decide⟩ =
      ((⟨0, by decide⟩, true), (fun _ => original), (fun _ => 0)) := by decide

example : (exampleGraph.powerPreprocessEnumeration evalConstraint false rotateReflection 1 2
    walks.reverse (by simpa using nodup_walks) (fun d => List.mem_reverse.mpr (mem_walks d))).equiv
      ⟨0, by decide⟩ = ((⟨0, by decide⟩, false), (fun _ => loop), (fun _ => 1)) := by decide

example : (powered exampleGraph).vertices = 2 := by decide

example : (powered exampleGraph).edges.length = 16 := by decide

/-- info: [(0, 0), (0, 1), (0, 0), (0, 0), (0, 0), (0, 1), (0, 0), (0, 0), (1, 1), (1, 0), (1, 1),
 (1, 1), (1, 1), (1, 0), (1, 1), (1, 1)] -/
#guard_msgs (whitespace := lax) in
#eval (powered exampleGraph).edges.map (fun e => (e.src, e.dst))

-- A real original constraint fails; unused steps and the added edges accept.
/-- info: [true, false, true, true, true, true, true, true, true, false, true, true, true, true, true,
 true] -/
#guard_msgs (whitespace := lax) in
#eval (powered exampleGraph).edges.map
  (fun e => e.constraint (fun _ => false) (fun _ => false))

-- Cloud equality inspects both endpoint opinion tables.
example : (exampleGraph.powerPreprocessEdge evalConstraint false rotateReflection 1 2
    ((0, false), (fun _ => cloud), (fun _ => 1))).constraint
      (fun _ => false) (fun _ => true) = false := by
  have hkill : killTime (fun _ : Fin 1 => (1 : Fin 2)) = 1 :=
    le_antisymm (killTime_le _) (Nat.succ_le_iff.mpr
      ((lt_killTime_iff _ (by decide)).mpr (by decide)))
  simp [Graph.powerPreprocessEdge, RegularConstraintGraph.powerRelationWithInput, hkill,
    Graph.preprocessRelation, cloud, List.finRange_succ, List.finRange_zero]

example : (powered (⟨0, []⟩ : Graph Bool)).edges = [] := by decide

example : (powered exampleGraph).WellFormed :=
  exampleGraph.wellFormed_powerPreprocess evalConstraint false reflection rotateReflection
    rotateReflection_eq 1 2 walks

example (g : Graph Bool) :
    (powered g).toGraph (fun table => table) =
      (((g.regularPreprocess evalConstraint false reflection).power 1 2).toConstraintGraph.map
        (fun v => Graph.halfEdgeNumber (v.1.val, v.2))).comap
          (g.powerPreprocessEnumeration evalConstraint false rotateReflection 1 2
            walks nodup_walks mem_walks).equiv :=
  g.toGraph_powerPreprocess evalConstraint false reflection rotateReflection rotateReflection_eq
    1 2 walks nodup_walks mem_walks

example (g : Graph Bool) :
    ((powered g).toGraph (fun table => table)).unsatVal =
      (RegularConstraintGraph.toConstraintGraph
        ((g.regularPreprocess evalConstraint false reflection).power 1 2)).unsatVal :=
  g.unsatVal_powerPreprocess evalConstraint false reflection rotateReflection rotateReflection_eq
    1 2 walks nodup_walks mem_walks

example (g : Graph Bool) :
    ((powered g).toGraph (fun table => table)).Satisfiable ↔
      (RegularConstraintGraph.toConstraintGraph
        ((g.regularPreprocess evalConstraint false reflection).power 1 2)).Satisfiable :=
  g.satisfiable_powerPreprocess_iff evalConstraint false reflection rotateReflection
    rotateReflection_eq 1 2 walks nodup_walks mem_walks

example : ComputableInPolyTime powered (Graph.encoding encBool)
    (Graph.encoding (encPi (encPi encBool))) := by
  have hr := isPolyTime_rotateReflection
  have he : ComputableTidilyInPolyTime
      (fun p : Bool × (Bool × Bool) => evalConstraint p.1 p.2.1 p.2.2)
      (encPair encBool (encPair encBool encBool)) encBool := by
    unfold evalConstraint
    fun_prop
  unfold powered
  fun_prop

example {Input : Type} {input : Input ↪ List Bool} {graph : Input → Graph Bool}
    (hgraph : ComputableInPolyTime graph input (Graph.encoding encBool)) :
    ComputableInPolyTime
      (fun x => (graph x).powerPreprocess evalConstraint false rotateReflection 1 2 walks)
      input (Graph.encoding (encPi (encPi encBool))) := by
  have hr := isPolyTime_rotateReflection
  have he : ComputableTidilyInPolyTime
      (fun p : Bool × (Bool × Bool) => evalConstraint p.1 p.2.1 p.2.2)
      (encPair encBool (encPair encBool encBool)) encBool := by
    unfold evalConstraint
    fun_prop
  fun_prop

-- Both ordinary let-bound spelling and missing-certificate rejection use the shared tactic.
example {Input : Type} {input : Input ↪ List Bool} {graph : Input → Graph Bool}
    (hgraph : ComputableInPolyTime graph input (Graph.encoding encBool))
    (rotate : ℕ × (ℕ × Unit) → ℕ × Unit)
    (hr : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary (encFinEnum Unit)))
      (encPair encUnary (encFinEnum Unit))) :
    ComputableInPolyTime (fun x =>
      let g := graph x
      g.powerPreprocess evalConstraint false rotate 1 2 walks)
      input (Graph.encoding (encPi (encPi encBool))) := by
  have he : ComputableTidilyInPolyTime
      (fun p : Bool × (Bool × Bool) => evalConstraint p.1 p.2.1 p.2.2)
      (encPair encBool (encPair encBool encBool)) encBool := by
    unfold evalConstraint
    fun_prop
  fail_if_success (clear hr; polytime)
  fail_if_success (clear hgraph; polytime)
  polytime


open Cslib.PCP.HadamardTester ComplexityTests.PCPNumbering

private def unitEval (constraint : Bool) (_ _ : Unit) : Bool := constraint

private def unitOpinions (D : Type) (T : ℕ) : Numbering (Graph.PowerAlphabet D Unit T) :=
  ⟨1, Equiv.ofUnique _ _⟩

-- The concrete opinion type has Unique.fintype, while the generic power proof used
-- Pi.instFintype. Their enumeration must not be unified to infer the output encoding.
example {Input : Type} {input : Input ↪ List Bool} {graph : Input → Graph Bool}
    (hgraph : ComputableInPolyTime graph input (Graph.encoding encBool))
    (rotate : ℕ × (ℕ × Fin 16) → ℕ × Fin 16)
    (hr : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary (encFinEnum (Fin 16))))
      (encPair encUnary (encFinEnum (Fin 16)))) :
    ComputableInPolyTime (fun x =>
      let powered := (graph x).powerPreprocess unitEval false rotate 4 2
        [(fun _ => .inr (), fun _ => 0)]
      powered.composeTabulated (numberSlots (unitOpinions (Fin 16) 4)).2 [default] queries)
      input (Graph.encoding (encPi (encPi encBool))) := by
  have he : ComputableTidilyInPolyTime
      (fun p : Bool × (Unit × Unit) => unitEval p.1 p.2.1 p.2.2)
      (encPair encBool (encPair (encFinEnum Unit) (encFinEnum Unit))) encBool := by
    unfold unitEval
    fun_prop
  fun_prop

-- Clients may choose any fixed encoding of the finite constraint table, independently of its
-- internal enumeration. The graph itself still ranges over arbitrarily large input data.
example {Input : Type} {input : Input ↪ List Bool} {graph : Input → Graph Bool}
    (hgraph : ComputableInPolyTime graph input (Graph.encoding encBool))
    (rotate : ℕ × (ℕ × Fin 16) → ℕ × Fin 16)
    (hr : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary (encFinEnum (Fin 16))))
      (encPair encUnary (encFinEnum (Fin 16))))
    (output : (Graph.PowerAlphabet (Fin 16) Unit 4 → Graph.PowerAlphabet (Fin 16) Unit 4 → Bool) ↪
      List Bool) :
    ComputableInPolyTime
      (fun x => (graph x).powerPreprocess unitEval false rotate 4 2
        [(fun _ => .inr (), fun _ => 0)])
      input (Graph.encoding output) := by
  have he : ComputableTidilyInPolyTime
      (fun p : Bool × (Unit × Unit) => unitEval p.1 p.2.1 p.2.2)
      (encPair encBool (encPair (encFinEnum Unit) (encFinEnum Unit))) encBool := by
    unfold unitEval
    fun_prop
  fail_if_success (clear hgraph; polytime)
  fail_if_success (clear hr; polytime)
  polytime

private def oneCoin : Rand (Graph.PowerAlphabet Unit Unit 1) :=
  ((0, 0), (0, 0), (0, 0, 0, 0, 0), (0, 0), (1, fun _ => true, 0))

-- This partial-list example evaluates selected function entries and endpoints, not the enormous
-- complete encPi output. It does not instantiate the full gap theorem.
private def selectedPartialRound (g : Graph Bool) :=
  g.amplify unitEval false rotateReflection 1 2 walks
    (numberSelectedSlots (unitOpinions Unit 1)).2 [(0, oneCoin)] selectedQueries

example : (selectedPartialRound exampleGraph).edges.length = 96 := by
  rw [selectedPartialRound, Graph.length_edges_amplify]
  decide

/-- info: (96, true) -/
#guard_msgs in
#eval ((selectedPartialRound exampleGraph).edges.length,
  (selectedPartialRound exampleGraph).isWellFormed)

example : (selectedPartialRound exampleGraph).WellFormed :=
  exampleGraph.wellFormed_amplify unitEval false reflection rotateReflection rotateReflection_eq
    1 2 walks (numberSelectedSlots (unitOpinions Unit 1)).2 [(0, oneCoin)] selectedQueries

example : ComputableInPolyTime selectedPartialRound (Graph.encoding encBool)
    (Graph.encoding (encPi (encPi encBool))) := by
  have hr := isPolyTime_rotateReflection
  have he : ComputableTidilyInPolyTime
      (fun p : Bool × (Unit × Unit) => unitEval p.1 p.2.1 p.2.2)
      (encPair encBool (encPair (encFinEnum Unit) (encFinEnum Unit))) encBool := by
    unfold unitEval
    fun_prop
  unfold selectedPartialRound Graph.amplify
  fun_prop

-- Full enumeration uses explicit finite numberings. The concrete arithmetic expander provides a
-- positive spectral gap. These lists certify the theorem's premises but are not evaluated.
private def numberFunctions {α β : Type} (domain : Numbering α) (range : Numbering β) :
    Numbering (α → β) :=
  ⟨range.1 ^ domain.1, (Equiv.arrowCongr domain.2 range.2).trans finFunctionFinEquiv⟩

private abbrev ArithmeticLabel := RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257

private def arithmeticLabels : Numbering ArithmeticLabel :=
  let field : Numbering (ZMod 257) := ⟨257, (ZMod.finEquiv 257).toEquiv.symm⟩
  let pair := numberProd field field
  let half := numberProd ⟨257 ^ 8, Equiv.refl _⟩ (numberProd pair pair)
  numberSum half half

private def preprocessedLabels : Numbering (ConstraintGraph.PreprocessLabel ArithmeticLabel) :=
  let unit : Numbering Unit := ⟨1, Equiv.ofUnique _ _⟩
  numberSum (numberSum (numberSum unit arithmeticLabels) arithmeticLabels) unit

private def arithmeticWalks : Numbering (Graph.PowerLabel ArithmeticLabel 4 2) :=
  numberProd (numberFunctions ⟨4, Equiv.refl _⟩ preprocessedLabels)
    (numberFunctions ⟨4, Equiv.refl _⟩ ⟨2, Equiv.refl _⟩)

private def fullWalks : List (Graph.PowerLabel ArithmeticLabel 4 2) :=
  List.ofFn arithmeticWalks.2.symm

private def fullCoins : List (Rand (Graph.PowerAlphabet ArithmeticLabel Unit 4)) :=
  List.ofFn (numberCoins (unitOpinions ArithmeticLabel 4)).2.symm

private def fullSelectedCoins : List (Fin 5 × Rand (Graph.PowerAlphabet ArithmeticLabel Unit 4)) :=
  List.ofFn (numberSelectedCoins (unitOpinions ArithmeticLabel 4)).2.symm

private theorem nodup_fullWalks : fullWalks.Nodup :=
  List.nodup_ofFn.mpr arithmeticWalks.2.symm.injective

private theorem mem_fullWalks (walk : Graph.PowerLabel ArithmeticLabel 4 2) :
    walk ∈ fullWalks :=
  List.mem_ofFn.mpr ⟨arithmeticWalks.2 walk, arithmeticWalks.2.symm_apply_apply walk⟩

local instance : FinEnum (ZMod 257) :=
  FinEnum.ofEquiv (Fin 257) (ZMod.finEquiv 257).toEquiv.symm

private def completeRound (g : Graph Bool) :=
  g.amplify unitEval false RotationMap.arithmeticExpanderRotate 4 2 fullWalks
    (numberSelectedSlots (unitOpinions ArithmeticLabel 4)).2 fullSelectedCoins selectedQueries

example : ComputableInPolyTime completeRound (Graph.encoding encBool)
    (Graph.encoding (encPi (encPi encBool))) := by
  have hr := RotationMap.polytime_arithmeticExpanderRotate (encFinEnum ArithmeticLabel)
  have he : ComputableTidilyInPolyTime
      (fun p : Bool × (Unit × Unit) => unitEval p.1 p.2.1 p.2.2)
      (encPair encBool (encPair (encFinEnum Unit) (encFinEnum Unit))) encBool := by
    unfold unitEval
    fun_prop
  unfold completeRound
  polytime

example {Input : Type} (input : Input ↪ List Bool) (graph : Input → Graph Bool)
    (hgraph : ComputableInPolyTime graph input (Graph.encoding encBool)) :
    ComputableInPolyTime (fun x =>
      let powered := (graph x).powerPreprocess unitEval false RotationMap.arithmeticExpanderRotate
        4 2 fullWalks
      powered.composeTabulated (numberSlots (unitOpinions ArithmeticLabel 4)).2 fullCoins queries)
      input (Graph.encoding (encPi (encPi encBool))) := by
  have hr := RotationMap.polytime_arithmeticExpanderRotate (encFinEnum ArithmeticLabel)
  have he : ComputableTidilyInPolyTime
      (fun p : Bool × (Unit × Unit) => unitEval p.1 p.2.1 p.2.2)
      (encPair encBool (encPair (encFinEnum Unit) (encFinEnum Unit))) encBool := by
    unfold unitEval
    fun_prop
  polytime

private theorem satisfiable_completeRound_iff (g : Graph Bool) :
    ((completeRound g).toGraph id).Satisfiable ↔ (g.toGraph unitEval).Satisfiable :=
  g.satisfiable_amplify_iff unitEval false RotationMap.arithmeticExpander
    RotationMap.arithmeticExpanderRotate RotationMap.arithmeticExpanderRotate_eq
    4 2 fullWalks (numberSelectedSlots (unitOpinions ArithmeticLabel 4)).2
    fullSelectedCoins selectedQueries
    nodup_fullWalks mem_fullWalks (nodup_selectedCoins _) nodup_selectedQueries
    (mem_selectedCoins _) mem_selectedQueries
    _ RotationMap.spectralExpansion_arithmeticExpander_le (by norm_num) (by decide) (by decide)

example : 0 < ((completeRound exampleGraph).toGraph id).unsatVal := by
  rw [ConstraintGraph.unsatVal_pos_iff, satisfiable_completeRound_iff]
  rintro ⟨assignment, h⟩
  have hf := h (⟨0, by decide⟩ : Fin exampleGraph.edges.length)
  simp [ConstraintGraph.Satisfies, Graph.toGraph, exampleGraph, unitEval] at hf

example (g : Graph Bool) :
    ((2 : ℕ) - 1 : ℝ) / ConstraintGraph.Amplification.denominator 840
        (Fintype.card Unit) (Fintype.card ArithmeticLabel)
        (1 - 9 / (400 * (257 : ℝ) ^ 16)) *
      min (ConstraintGraph.Amplification.retention (Fintype.card ArithmeticLabel)
        (1 - 9 / (400 * (257 : ℝ) ^ 16)) * (g.toGraph unitEval).unsatVal) (1 / (4 : ℕ) ^ 2) ≤
      ((completeRound g).toGraph id).unsatVal :=
  g.le_unsatVal_amplify unitEval false RotationMap.arithmeticExpander
        RotationMap.arithmeticExpanderRotate RotationMap.arithmeticExpanderRotate_eq
        4 2 fullWalks (numberSelectedSlots (unitOpinions ArithmeticLabel 4)).2
        fullSelectedCoins selectedQueries
        nodup_fullWalks mem_fullWalks (nodup_selectedCoins _) nodup_selectedQueries
        (mem_selectedCoins _) mem_selectedQueries
        _ RotationMap.spectralExpansion_arithmeticExpander_le (by norm_num) (by decide)
        (by simp)

end ComplexityTests.PCPEncodedPower

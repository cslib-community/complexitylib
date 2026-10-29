/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Encoded.Preprocess
import Complexity.Computability.PCP.Encoded.Constraints
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.Family
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Tactic.PolyTime

/-! Executable degree reduction and preprocessing, exact interpretations, arithmetic expansion,
and fixed-alphabet normalization that closes the descriptor type across repeated rounds. -/

namespace ComplexityTests.PCPEncodedPreprocess

open Cslib Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

-- The reflection family is executable for every cloud size; no expansion claim is made for it.
private def reflection (n : ℕ) : RotationMap (Fin n) Unit :=
  .ofInvolutive Fin.rev Fin.rev_rev

private def rotateReflection (p : ℕ × (ℕ × Unit)) : ℕ × Unit :=
  (p.1 - 1 - p.2.1, p.2.2)

private theorem rotateReflection_eq (n : ℕ) (v : Fin n) (d : Unit) :
    rotateReflection (n, v.val, d) =
      (((reflection n).rot (v, d)).1.val, ((reflection n).rot (v, d)).2) := by
  cases d
  simp [rotateReflection, reflection, RotationMap.ofInvolutive, Nat.sub_sub, Nat.add_comm]

private theorem isPolyTime_rotateReflection :
    ComputableInPolyTime rotateReflection
      (encPair encUnary (encPair encUnary (encFinEnum Unit)))
      (encPair encUnary (encFinEnum Unit)) := by
  unfold rotateReflection
  polytime

-- A loop and two parallel edges give unequal cloud sizes and distinct incident half-edges.
private def exampleGraph : Graph Bool :=
  ⟨3, [⟨0, 1, false⟩, ⟨1, 1, false⟩, ⟨0, 1, true⟩]⟩

private def reduced : Graph (Option (Bool × Bool)) :=
  exampleGraph.degreeReduce false rotateReflection [()]

-- Each half-edge's original edge occurs before its cloud edge.
example : (exampleGraph.degreeReduceEnumeration false rotateReflection [()]
    (by decide) (by intro d; cases d; simp)).equiv ⟨1, by decide⟩ =
      ((⟨0, by decide⟩, false), Sum.inr ()) := by decide

example : reduced = ⟨6,
    [⟨0, 1, some (false, false)⟩, ⟨0, 4, none⟩,
     ⟨1, 0, some (true, false)⟩, ⟨1, 5, none⟩,
     ⟨2, 3, some (false, false)⟩, ⟨2, 3, none⟩,
     ⟨3, 2, some (true, false)⟩, ⟨3, 2, none⟩,
     ⟨4, 5, some (false, true)⟩, ⟨4, 0, none⟩,
     ⟨5, 4, some (true, true)⟩, ⟨5, 1, none⟩]⟩ := by decide

example : reduced.isWellFormed = true := by decide

example : (Graph.degreeReduce false rotateReflection [()] ⟨0, []⟩).isWellFormed = true := by
  decide

private def constraintEval (c a b : Bool) : Bool :=
  c || (!a || b)

-- The reverse edge swaps the labels, retaining the original asymmetric constraint.
example : Graph.degreeReduceEval constraintEval (some (false, false)) true false = false := by
  decide

example : Graph.degreeReduceEval constraintEval (some (true, false)) true false = true := by
  decide

example : reduced.WellFormed :=
  exampleGraph.wellFormed_degreeReduce false reflection rotateReflection rotateReflection_eq [()]

example : ComputableInPolyTime (Graph.degreeReduce false rotateReflection [()])
    (Graph.encoding encBool) (Graph.encoding (encOption (encPair encBool encBool))) :=
  Graph.isPolyTime_degreeReduce false [()] rotateReflection isPolyTime_rotateReflection

example : (reduced.toGraph (Graph.degreeReduceEval constraintEval)).unsatVal =
    ((exampleGraph.toGraph constraintEval).degreeReduce
      (exampleGraph.cloudFamily constraintEval false reflection)).toConstraintGraph.unsatVal :=
  exampleGraph.unsatVal_degreeReduce constraintEval false reflection rotateReflection
    rotateReflection_eq [()] (by decide) (by intro d; cases d; simp)

example : (reduced.toGraph (Graph.degreeReduceEval constraintEval)).Satisfiable ↔
    ((exampleGraph.toGraph constraintEval).degreeReduce
      (exampleGraph.cloudFamily constraintEval false reflection)).toConstraintGraph.Satisfiable :=
  exampleGraph.satisfiable_degreeReduce_iff constraintEval false reflection rotateReflection
    rotateReflection_eq [()] (by decide) (by intro d; cases d; simp)

private def preprocessed : Graph (Option (Bool × Bool)) :=
  exampleGraph.preprocess false true rotateReflection [()]

-- Six new reflection edges and six loops are appended after the twelve degree-reduced edges.
example : preprocessed = ⟨6, reduced.edges ++
    [⟨0, 5, some (false, true)⟩, ⟨1, 4, some (false, true)⟩,
     ⟨2, 3, some (false, true)⟩, ⟨3, 2, some (false, true)⟩,
     ⟨4, 1, some (false, true)⟩, ⟨5, 0, some (false, true)⟩,
     ⟨0, 0, some (false, true)⟩, ⟨1, 1, some (false, true)⟩,
     ⟨2, 2, some (false, true)⟩, ⟨3, 3, some (false, true)⟩,
     ⟨4, 4, some (false, true)⟩, ⟨5, 5, some (false, true)⟩]⟩ := by decide

example : preprocessed.vertices = 6 ∧ preprocessed.edges.length = 24 := by decide

example : preprocessed.isWellFormed = true := by decide

example : (Graph.preprocess false true rotateReflection [()] ⟨0, []⟩) = ⟨0, []⟩ := by
  decide

-- Even malformed original bounds produce valid half-edge indices.
example : (Graph.preprocess false true rotateReflection [()]
    ⟨0, [⟨17, 23, false⟩]⟩).isWellFormed = true := by decide

example : preprocessed.WellFormed :=
  exampleGraph.wellFormed_preprocess false true reflection rotateReflection rotateReflection_eq [()]

example : ComputableInPolyTime (Graph.preprocess false true rotateReflection [()])
    (Graph.encoding encBool) (Graph.encoding (encOption (encPair encBool encBool))) :=
  Graph.isPolyTime_preprocess false true rotateReflection [()] isPolyTime_rotateReflection

-- The same ordinary functional spelling uses the shared compositional API.
example : ComputableInPolyTime (fun g : Graph Bool =>
      let reduced := g.degreeReduce false rotateReflection [()]
      (reduced.addTrivial (some (false, true))
        (Graph.rotationEdges rotateReflection [()] reduced.vertices)).addLoops
          (some (false, true)))
    (Graph.encoding encBool) (Graph.encoding (encOption (encPair encBool encBool))) := by
  have hrotate := isPolyTime_rotateReflection
  have hdegree := Graph.isPolyTime_degreeReduce (enc := encBool) false [()]
    rotateReflection hrotate
  fun_prop

-- The exact-numbering contract is inhabited; reflection has no positive expansion claim.
example : (exampleGraph.toGraph constraintEval).PreprocessExpanders Unit 1 :=
  exampleGraph.preprocessExpanders constraintEval false reflection 1
    (fun n => (reflection n).spectralExpansion_le_one)

example : ∃ e : Fin preprocessed.edges.length ≃
      (Fin exampleGraph.edges.length × Bool) × (((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit),
    preprocessed.toGraph (Graph.degreeReduceEval constraintEval) =
      ((exampleGraph.regularPreprocess constraintEval false reflection).toConstraintGraph.map
        (fun p => Graph.halfEdgeNumber (p.1.val, p.2))).comap e :=
  exampleGraph.toGraph_preprocess constraintEval false true reflection rotateReflection
    rotateReflection_eq (by simp [constraintEval]) [()] (by decide) (by intro d; cases d; simp)

example : (preprocessed.toGraph (Graph.degreeReduceEval constraintEval)).unsatVal =
    (exampleGraph.regularPreprocess constraintEval false reflection).toConstraintGraph.unsatVal :=
  exampleGraph.unsatVal_preprocess_eq constraintEval false true reflection rotateReflection
    rotateReflection_eq (by simp [constraintEval]) [()] (by decide) (by intro d; cases d; simp)

example : (preprocessed.toGraph (Graph.degreeReduceEval constraintEval)).unsatVal =
    (reduced.toGraph (Graph.degreeReduceEval constraintEval)).unsatVal / 2 :=
  exampleGraph.unsatVal_preprocess constraintEval false true rotateReflection
    (by simp [constraintEval]) [()]

-- A rejecting original edge remains two forced violations among the eight final edges.
private def rejectingGraph : Graph Bool := ⟨2, [⟨0, 1, false⟩]⟩

private theorem rejecting_reduced_value :
    ((rejectingGraph.degreeReduce false rotateReflection [()]).toGraph
      (Graph.degreeReduceEval (fun c (_ _ : Bool) => c))).unsatVal = 1 / 2 := by
  have hgraph : rejectingGraph.degreeReduce false rotateReflection [()] =
      ⟨2, [⟨0, 1, some (false, false)⟩, ⟨0, 0, none⟩,
        ⟨1, 0, some (true, false)⟩, ⟨1, 1, none⟩]⟩ := by decide
  rw [hgraph]
  let G := (Graph.mk 2 [Edge.mk 0 1 (some (false, false)), ⟨0, 0, none⟩,
      ⟨1, 0, some (true, false)⟩, ⟨1, 1, none⟩]).toGraph
        (Graph.degreeReduceEval (fun c (_ _ : Bool) => c))
  obtain ⟨σ, hσ⟩ := G.exists_unsatFrac_eq_unsatVal
  change G.unsatVal = 1 / 2
  rw [← hσ]
  have hunsat : G.unsatEdges σ = {0, 2} := by
    ext i
    fin_cases i <;> simp [G, ConstraintGraph.unsatEdges, ConstraintGraph.Satisfies,
      Graph.toGraph, Graph.degreeReduceEval, List.get_eq_getElem]
  rw [ConstraintGraph.unsatFrac, hunsat]
  norm_num [G]

example : ((rejectingGraph.preprocess false true rotateReflection [()]).toGraph
    (Graph.degreeReduceEval (fun c (_ _ : Bool) => c))).unsatVal = 1 / 4 := by
  rw [Graph.unsatVal_preprocess _ _ _ _ _ (by intros; rfl), rejecting_reduced_value]
  norm_num

end ComplexityTests.PCPEncodedPreprocess

namespace ComplexityTests.PCPEncodedArithmetic

open Cslib Cslib.PCP Cslib.PCP.Encoded Cslib.RotationMap Turing.MultiTapeTM
open ComplexityTests.PCPEncodedPreprocess

-- These lists enumerate the actual constant label type by arithmetic; no graph search is used.
-- Its enormous degree makes this an asymptotic instance, not a small runnable example.
private def fieldElements : List (ZMod 257) :=
  (List.finRange 257).map (ZMod.finEquiv 257)

private def arithmeticLabels : List (AffinePlaneFamilyLabel (ZMod 257) 257) :=
  let pair := fieldElements.product fieldElements
  let labels := (List.finRange (257 ^ 8)).product (pair.product pair)
  labels.map Sum.inl ++ labels.map Sum.inr

private theorem arithmeticLabels_nodup : arithmeticLabels.Nodup := by
  have hf : fieldElements.Nodup := (List.nodup_finRange 257).map (ZMod.finEquiv 257).injective
  have hl := (List.nodup_finRange (257 ^ 8)).product
    ((hf.product hf).product (hf.product hf))
  apply List.nodup_append.mpr
  refine ⟨hl.map Sum.inl_injective, hl.map Sum.inr_injective, ?_⟩
  simp

private theorem mem_arithmeticLabels (d : AffinePlaneFamilyLabel (ZMod 257) 257) :
    d ∈ arithmeticLabels := by
  have hf (x : ZMod 257) : x ∈ fieldElements :=
    List.mem_map.mpr ⟨(ZMod.finEquiv 257).symm x, List.mem_finRange _,
      (ZMod.finEquiv 257).apply_symm_apply x⟩
  rcases d with ⟨i, ⟨a, b⟩, c, d⟩ | ⟨i, ⟨a, b⟩, c, d⟩ <;>
    simp [arithmeticLabels, hf]

local instance : FinEnum (ZMod 257) :=
  FinEnum.ofEquiv (Fin 257) (ZMod.finEquiv 257).toEquiv.symm

example : ComputableInPolyTime
    (Graph.preprocess false true arithmeticExpanderRotate arithmeticLabels)
    (Graph.encoding encBool) (Graph.encoding (encOption (encPair encBool encBool))) :=
  Graph.isPolyTime_preprocess false true arithmeticExpanderRotate arithmeticLabels
    (polytime_arithmeticExpanderRotate (encFinEnum _))

noncomputable example :
    (exampleGraph.toGraph constraintEval).PreprocessExpanders
      (AffinePlaneFamilyLabel (ZMod 257) 257)
      (1 - 9 / (400 * (257 : ℝ) ^ 16)) :=
  exampleGraph.preprocessExpanders constraintEval false arithmeticExpander _
    spectralExpansion_arithmeticExpander_le

example :
    ((exampleGraph.preprocess false true arithmeticExpanderRotate arithmeticLabels).toGraph
      (Graph.degreeReduceEval constraintEval)).Satisfiable ↔
      (exampleGraph.toGraph constraintEval).Satisfiable :=
  exampleGraph.satisfiable_preprocess_iff constraintEval false true arithmeticExpander
    arithmeticExpanderRotate arithmeticExpanderRotate_eq (by simp [constraintEval])
    arithmeticLabels arithmeticLabels_nodup mem_arithmeticLabels
    _ spectralExpansion_arithmeticExpander_le (by norm_num)

example (g : Graph Bool) (eval : Bool → Bool → Bool → Bool)
    (htruth : ∀ a b, eval true a b = true) :
    (min 1 ((9 / (400 * (257 : ℝ) ^ 16)) *
        Fintype.card (AffinePlaneFamilyLabel (ZMod 257) 257)) /
      (4 * (1 + Fintype.card (AffinePlaneFamilyLabel (ZMod 257) 257)))) *
        (g.toGraph eval).unsatVal ≤
      ((g.preprocess false true arithmeticExpanderRotate arithmeticLabels).toGraph
        (Graph.degreeReduceEval eval)).unsatVal := by
  have h := g.le_unsatVal_preprocess eval false true arithmeticExpander arithmeticExpanderRotate
    arithmeticExpanderRotate_eq htruth arithmeticLabels arithmeticLabels_nodup mem_arithmeticLabels
    _ spectralExpansion_arithmeticExpander_le
  simpa only [sub_sub_cancel] using h

end ComplexityTests.PCPEncodedArithmetic

namespace ComplexityTests.PCPEncodedPreprocess

open Cslib Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

-- Each round returns to the same descriptor type; encoded tables discard nested descriptors.
private def tablePreprocess (g : Graph (Bool → Bool → Bool)) : Graph (Bool → Bool → Bool) :=
  (g.preprocess (fun _ _ => false) (fun _ _ => true) rotateReflection [()]).mapConstraints
    (Graph.degreeReduceEval (fun table => table))

private theorem isPolyTime_tablePreprocess : ComputableInPolyTime tablePreprocess
    (Graph.encoding (encPi (encPi encBool))) (Graph.encoding (encPi (encPi encBool))) := by
  have heval := Graph.isPolyTime_constraintTableEval encBool
  have hdegreeEval := Graph.isPolyTime_degreeReduceEval
    (eval := fun table : Bool → Bool → Bool => table) heval
  have hpre := Graph.isPolyTime_preprocess (enc := encPi (encPi encBool))
    (fun (_ _ : Bool) => false) (fun _ _ => true) rotateReflection [()]
      isPolyTime_rotateReflection
  exact (Graph.isPolyTime_tabulateConstraints hdegreeEval).comp hpre

example : ComputableInPolyTime (fun g => tablePreprocess (tablePreprocess g))
    (Graph.encoding (encPi (encPi encBool))) (Graph.encoding (encPi (encPi encBool))) := by
  have h := isPolyTime_tablePreprocess
  fun_prop

example :
    (tablePreprocess (tablePreprocess (exampleGraph.mapConstraints constraintEval))).vertices =
      48 := by decide

example :
    (tablePreprocess (tablePreprocess (exampleGraph.mapConstraints constraintEval))).edges.length =
      192 := by simp [tablePreprocess, Graph.length_edges_preprocess, exampleGraph]

example :
    ((tablePreprocess (exampleGraph.mapConstraints constraintEval)).toGraph
      (fun table => table)).unsatVal =
      (((exampleGraph.mapConstraints constraintEval).preprocess (fun _ _ => false)
        (fun _ _ => true) rotateReflection [()]).toGraph
        (Graph.degreeReduceEval (fun table => table))).unsatVal :=
  Graph.unsatVal_mapConstraints _ _ _

end ComplexityTests.PCPEncodedPreprocess

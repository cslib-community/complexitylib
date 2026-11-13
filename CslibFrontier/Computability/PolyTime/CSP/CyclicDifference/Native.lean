/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.CyclicDifference.Program
public import CslibFrontier.Computability.PolyTime.CSP.CyclicDifference.Parity
import all CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Certificate
import all CslibFrontier.Computability.PolyTime.Graph.RotationSystem
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Native supplied-rotation cyclic-difference compilation

All certificates cover every raw typed input under the original framed CSP/certificate encoding.
Fixed finite relation lookups may depend on the language, including exponentially large static
truth tables. No computability assumption on a solver, recognizer, or arbitrary semantic function
is used. Natural source labels and external certificate indices remain binary throughout.
-/

public section

namespace Cslib.Complexity.CSP.CyclicCompiler

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Table Turing.MultiTapeTM
open Graph.RotationCertificate

variable {Rel : Type}

/-- Unary fresh offset followed by a framed list of binary boundary names. -/
abbrev encParityChain := encPair encUnary (encList encNat)

/-- Native construction of the actual chain, including empty and malformed boundary lists. -/
theorem computableInPolyTime_parityChain :
    ComputableInPolyTime (fun p : ℕ × List ℕ => parityChain p.1 p.2)
      encParityChain (encCSP encTable encNat) := by
  have heq (p : ℕ × List ℕ) : parityChain p.1 p.2 =
      if p.2.isEmpty then [Constraint.mk (evenTable 0) []]
      else parityChainTail p.1 (p.2.headD 0) p.2.tail := by
    cases p.2 <;> rfl
  simp only [heq]
  apply (show ComputableInPolyTime (fun p : ℕ × List ℕ => p.2.isEmpty)
    encParityChain encBool by unfold encParityChain; fun_prop).ite (by fun_prop)
  exact computableInPolyTime_parityChainTail.comp
    (g := fun p : ℕ × List ℕ => (p.1, p.2.headD 0, p.2.tail)) (by
    unfold encParityChain encParityTail
    fun_prop)

private theorem argumentTable_polyTime (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (argumentTable (Rel := Rel)) (encCSP encRel encNat)
      (encList encNat) := by
  unfold argumentTable
  apply ComputableInPolyTime.mapWithInput (computableInPolyTime_occurrences encRel encNat)
  apply (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_to_binary).comp
  exact (argumentNextIndex_polyTime encRel encNat).comp
    (g := fun p : CSP Rel ℕ × (ℕ × ℕ × ℕ) => ((p.1, p.2.1), p.2.2.1)) (by
    unfold encOccurrenceRecord
    fun_prop)

private theorem whiteTable_polyTime (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : CSP Rel ℕ × Graph.RotationCertificate => whiteTable p.1 p.2)
      (encCSPRotationCertificate encRel encNat) (encList encNat) := by
  have ha := argumentTable_polyTime encRel
  have ho := computableInPolyTime_occurrences encRel encNat
  have hs := computableInPolyTime_successor
  unfold whiteTable
  apply ComputableInPolyTime.mapWithInput (encA := encUnary)
    (by unfold encCSPRotationCertificate; fun_prop)
  have hinv : ComputableInPolyTime
      (fun p : (CSP Rel ℕ × Graph.RotationCertificate) × ℕ =>
        p.1.2.successor.idxOf (2 * p.2))
      (encPair (encCSPRotationCertificate encRel encNat) encUnary) encUnary := by
    apply ComputableInPolyTime.of_tidy
    apply ComputableTidilyInPolyTime.idxOfWithInput (hs.tidy.comp (by fun_prop))
    exact ComputableTidilyInPolyTime.unary_to_binary.comp (by
      unfold encCSPRotationCertificate
      fun_prop)
  have hhalf : ComputableInPolyTime
      (fun p : (CSP Rel ℕ × Graph.RotationCertificate) × ℕ =>
        p.1.2.successor.idxOf (2 * p.2) / 2)
      (encPair (encCSPRotationCertificate encRel encNat) encUnary) encNat :=
    ComputableInPolyTime.binary_div.comp
      (((ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_to_binary).comp
        hinv).prod (ComputableInPolyTime.const 2))
  exact (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_to_binary).comp
    (.of_tidy (ComputableTidilyInPolyTime.idxOfWithInput (ha.tidy.comp (by fun_prop))
      hhalf.tidy))

private theorem whiteScope_polyTime (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : (CSP Rel ℕ × Graph.RotationCertificate) × ℕ =>
      whiteScope p.1.1 p.1.2 p.2)
      (encPair (encCSPRotationCertificate encRel encNat) encNat) (encList encNat) := by
  have ho := computableInPolyTime_occurrences encRel encNat
  have ht := whiteTable_polyTime encRel
  unfold whiteScope
  apply ComputableInPolyTime.filterWithInput (range_binary.comp
    (by unfold encCSPRotationCertificate; fun_prop))
  exact orbitBool_polyTime (by unfold encCSPRotationCertificate; fun_prop)
    (ht.comp (by fun_prop)) (by fun_prop) (by fun_prop)

private theorem whiteScopes_polyTime (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : CSP Rel ℕ × Graph.RotationCertificate => whiteScopes p.1 p.2)
      (encCSPRotationCertificate encRel encNat) (encList (encList encNat)) := by
  have ho := computableInPolyTime_occurrences encRel encNat
  have ht := whiteTable_polyTime encRel
  have hr : ComputableInPolyTime (fun p : CSP Rel ℕ × Graph.RotationCertificate =>
      List.range p.1.occurrences.length) (encCSPRotationCertificate encRel encNat)
      (encList encNat) := range_binary.comp (by unfold encCSPRotationCertificate; fun_prop)
  have hrep : ComputableInPolyTime
      (fun p : (CSP Rel ℕ × Graph.RotationCertificate) × ℕ =>
        faceRepBool p.1.1.occurrences.length (whiteTable p.1.1 p.1.2) p.2)
      (encPair (encCSPRotationCertificate encRel encNat) encNat) encBool := by
    unfold faceRepBool
    apply ComputableInPolyTime.allWithInput (hr.comp (by fun_prop))
    have horb : ComputableInPolyTime
        (fun p : ((CSP Rel ℕ × Graph.RotationCertificate) × ℕ) × ℕ =>
          orbitBool p.1.1.1.occurrences.length (whiteTable p.1.1.1 p.1.1.2)
            p.1.2 p.2)
        (encPair (encPair (encCSPRotationCertificate encRel encNat) encNat) encNat)
        encBool :=
      orbitBool_polyTime (by unfold encCSPRotationCertificate; fun_prop)
        (ht.comp (g := fun p : ((CSP Rel ℕ × Graph.RotationCertificate) × ℕ) × ℕ =>
          p.1.1) (by fun_prop)) (by fun_prop) (by fun_prop)
    exact ComputableInPolyTime.bool_or
      |>.comp ((ComputableInPolyTime.bool_not.comp horb).prod
        (ComputableInPolyTime.binary_le.comp
          ((show ComputableInPolyTime
            (fun p : ((CSP Rel ℕ × Graph.RotationCertificate) × ℕ) × ℕ => p.1.2)
            (encPair (encPair (encCSPRotationCertificate encRel encNat) encNat) encNat)
            encNat by fun_prop).prod (ComputableInPolyTime.snd _ _))))
  unfold whiteScopes
  exact ComputableInPolyTime.mapWithInput
    (ComputableInPolyTime.filterWithInput hr hrep) (whiteScope_polyTime encRel)

private theorem blackScope_polyTime (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : (CSP Rel ℕ × ℕ) × List ℕ =>
      blackScope p.1.1 p.1.2 p.2)
      (encPair (encPair (encCSP encRel encNat) encUnary) (encList encNat)) (encList encNat) := by
  have hp := argumentPositions_polyTime encRel encNat
  unfold blackScope
  apply ComputableInPolyTime.mapWithInput (encA := encUnary) (by fun_prop)
  exact (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_to_binary).comp
    (.of_tidy (ComputableTidilyInPolyTime.idxOfWithInput
      (hp.tidy.comp (g := fun p : ((CSP Rel ℕ × ℕ) × List ℕ) × ℕ => p.1.1.1) (by fun_prop))
      (show ComputableTidilyInPolyTime
        (fun p : ((CSP Rel ℕ × ℕ) × List ℕ) × ℕ => (p.1.1.2, p.2))
        (encPair (encPair (encPair (encCSP encRel encNat) encUnary) (encList encNat)) encUnary)
        (encPair encUnary encUnary) by fun_prop)))

private theorem blackConstraints_polyTime [Finite Rel] (encRel : Rel ↪ List Bool)
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) :
    ComputableInPolyTime (blackConstraints arity sem) (encCSP encRel encNat)
      (encCSP encTable encNat) := by
  have ht : ComputableInPolyTime (differenceTable arity sem) encRel encTable := .of_finite _
  have hz := ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.zipIdx
    (encConstraint encRel encNat))
  have hscope := blackScope_polyTime encRel
  unfold blackConstraints encCSP
  apply ComputableInPolyTime.mapWithInput
    (ComputableInPolyTime.filterWithInput hz (by fun_prop))
  exact (ht.comp (g := fun p : CSP Rel ℕ × (Constraint Rel ℕ × ℕ) => p.2.1.rel)
    (by fun_prop)).prod
    (hscope.comp (g := fun p : CSP Rel ℕ × (Constraint Rel ℕ × ℕ) =>
      ((p.1, p.2.2), p.2.1.scope)) (by fun_prop))

private theorem auxiliaryPrefix_polyTime :
    ComputableInPolyTime (fun p : List (List ℕ) × ℕ => auxiliaryPrefix p.1 p.2)
      (encPair (encList (encList encNat)) encUnary) encUnary := by
  have heq (p : List (List ℕ) × ℕ) : auxiliaryPrefix p.1 p.2 =
      ((p.1.take p.2).flatMap fun scope => scope.drop 3).length := by
    simp only [auxiliaryPrefix, List.length_flatMap, List.length_drop]
  simp only [heq]
  fun_prop

private theorem whiteConstraints_polyTime :
    ComputableInPolyTime (fun p : ℕ × List (List ℕ) => whiteConstraints p.1 p.2)
      (encPair encUnary (encList (encList encNat))) (encCSP encTable encNat) := by
  have hz : ComputableInPolyTime (fun p : ℕ × List (List ℕ) => p.2.zipIdx)
      (encPair encUnary (encList (encList encNat)))
      (encList (encPair (encList encNat) encUnary)) :=
    .of_tidy ((ComputableTidilyInPolyTime.zipIdx (encList encNat)).comp (by fun_prop))
  unfold whiteConstraints
  apply ComputableInPolyTime.flatMapWithInput hz
  have hp := auxiliaryPrefix_polyTime.comp
    (g := fun p : (ℕ × List (List ℕ)) × (List ℕ × ℕ) => (p.1.2, p.2.2))
    (show ComputableInPolyTime
      (fun p : (ℕ × List (List ℕ)) × (List ℕ × ℕ) => (p.1.2, p.2.2))
      (encPair (encPair encUnary (encList (encList encNat)))
        (encPair (encList encNat) encUnary))
      (encPair (encList (encList encNat)) encUnary) by fun_prop)
  exact computableInPolyTime_parityChain.comp
    (g := fun p : (ℕ × List (List ℕ)) × (List ℕ × ℕ) =>
      (p.1.1 + auxiliaryPrefix p.1.2 p.2.2, p.2.1)) (by
        unfold encParityChain
        fun_prop)

/-- The complete body is native polynomial time on every raw CSP/certificate pair. Fixed
finite language preprocessing is a constant of this theorem, rather than a uniform algorithm
on relation descriptions. All white-face construction cost is charged to actual input lists. -/
theorem computableInPolyTime_body [Finite Rel] (encRel : Rel ↪ List Bool)
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) :
    ComputableInPolyTime (fun p : CSP Rel ℕ × Graph.RotationCertificate =>
      body arity sem p.1 p.2) (encCSPRotationCertificate encRel encNat)
      (encCSP encTable encNat) := by
  have hb := blackConstraints_polyTime encRel arity sem
  have hw := whiteScopes_polyTime encRel
  have ho := computableInPolyTime_occurrences encRel encNat
  have harg : ComputableInPolyTime
      (fun p : CSP Rel ℕ × Graph.RotationCertificate =>
        (p.1.occurrences.length, whiteScopes p.1 p.2))
      (encCSPRotationCertificate encRel encNat)
      (encPair encUnary (encList (encList encNat))) := by
    unfold encCSPRotationCertificate
    fun_prop
  have hc := whiteConstraints_polyTime.comp harg
  unfold body
  exact .of_tidy ((ComputableTidilyInPolyTime.listAppend (encConstraint encTable encNat)).comp
    ((hb.tidy.comp (ComputableTidilyInPolyTime.fst _ _)).prod hc.tidy))

/-- Total ordinary native polynomial-time compiler under the original framed input and
explicit-table output encodings. No input-validity, positivity, semantic, or runtime premise
appears: malformed arities/rotations and huge binary names/indices are included. -/
theorem computableInPolyTime_compile [Finite Rel] (encRel : Rel ↪ List Bool)
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) :
    ComputableInPolyTime (compile arity sem) (encCSPRotationCertificate encRel encNat)
      (encCSP encTable encNat) := by
  have ha := computableInPolyTime_validArity encRel arity
  have hr := computableInPolyTime_verifyRotationCertificate encRel encNat
  have hn : ComputableInPolyTime (nonemptySymbol arity sem) encRel encBool := .of_finite _
  have hall : ComputableInPolyTime (fun p : CSP Rel ℕ × Graph.RotationCertificate =>
      p.1.all (fun c => nonemptySymbol arity sem c.rel))
      (encCSPRotationCertificate encRel encNat) encBool := by
    unfold encCSPRotationCertificate encCSP
    apply ComputableInPolyTime.allWithInput (by fun_prop)
    exact hn.comp (by fun_prop)
  unfold compile
  apply ComputableInPolyTime.ite
    (ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and'
      (ha.comp (ComputableInPolyTime.fst _ _)) hr) hall)
    (computableInPolyTime_body encRel arity sem) (ComputableInPolyTime.const rejectEdge)

/-- Full framed output length is polynomial in full framed input length, including all
explicit table rows, binary arities, dense auxiliary names and pair/list framing. -/
theorem polyBounded_length_compile [Finite Rel] (encRel : Rel ↪ List Bool)
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) :
    PolyBounded (fun p : CSP Rel ℕ × Graph.RotationCertificate =>
      (encCSPRotationCertificate encRel encNat p).length)
      (fun p => (encCSP encTable encNat (compile arity sem p)).length) :=
  (computableInPolyTime_compile encRel arity sem).polyBounded_length

end Cslib.Complexity.CSP.CyclicCompiler

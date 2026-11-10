/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.WeightedComparison.Generator
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.OfFn

/-!
# Actual binary generation of correlated weighted-comparison families

The fixed comparison family shares the original declared variables and reads its coefficient,
polarity and target records at runtime. All complete gate lists and CNF writes are certified,
without supplying output circuits. This is the fixed-family construction of
[ChenJiangZhu2027], Lemma A.1 / Corollary A.2 (PDF pp.28–29).

## Main results

* `code_polytime`, `build_polytime`: actual fixed-family binary code and full CNF writing.
* `code_ofData`, `build_ofData`: exact correspondence with the approved functional circuits.
-/

public section

namespace Cslib.Circuits.Boolean.WeightedSum.Family

open Turing.MultiTapeTM ComputableInPolyTime

/-- Shared unary declaration, explicit binary weight/polarity rows and signed binary targets. -/
abbrev Input := ℕ × (List (List (ℕ × Bool)) × List ℤ)
/-- The single original input count, shared by all comparisons. -/
@[expose] def declared (x : Input) : ℕ := x.1
/-- Actual original coefficient/polarity rows in comparison-label order. -/
@[expose] def rows (x : Input) : List (List (ℕ × Bool)) := let (_, (ws, _)) := x; ws
/-- Actual signed targets in the same fixed-label order. -/
@[expose] def targets (x : Input) : List ℤ := let (_, (_, ts)) := x; ts
/-- Full binary frame; labels/family size are fixed problem parameters. -/
abbrev encInput : Input ↪ List Bool :=
  encPair encUnary (encPair (encList (encList (encPair encNat encBool))) (encList encIntBin))
/-- Read an actual original comparison frame; missing rows/targets use zero defaults. -/
@[expose] def frame (i : ℕ) (x : Input) : BinaryFrontend.Input :=
  (declared x, ((rows x).getD i [], (targets x).getD i 0))

/-- Complete actual family code, with no independent copies of original input bits. -/
@[expose] def code {r : ℕ} (op : Fin r → Comparison) (c : ℕ) (x : Input) :
    List (Op × List ℕ) × List ℕ :=
  appendCodes (declared x) (List.ofFn fun i =>
    testCode (op i) c (BinaryFrontend.weight (frame i.val x))
      (BinaryFrontend.positive (frame i.val x)) (BinaryFrontend.target (frame i.val x)))

/-- Write every true output unit and complete gate truth table from the actual family code. -/
@[expose] def build {r : ℕ} (op : Fin r → Comparison) (c : ℕ) (x : Input) : Logic.PL.CNF ℕ :=
  FunctionalCNF.write (declared x, code op c x, List.replicate r true)

private theorem frame_polytime (i : ℕ) :
    ComputableInPolyTime (frame i) encInput BinaryFrontend.encInput := by
  unfold frame declared rows targets encInput BinaryFrontend.encInput
  fun_prop

/-- For every fixed comparison family, actual code materialization has polynomial binary time. -/
@[fun_prop] theorem code_polytime {r : ℕ} (op : Fin r → Comparison) (c : ℕ) :
    ComputableInPolyTime (code op c) encInput encCode := by
  have hn : ComputableInPolyTime declared encInput encNat := by
    apply unary_to_binary.comp
    unfold encInput
    fun_prop
  have hrows := mapConst (List.finRange r) (f := fun x i =>
    testCode (op i) c (BinaryFrontend.weight (frame i.val x))
      (BinaryFrontend.positive (frame i.val x)) (BinaryFrontend.target (frame i.val x)))
    (fun i _ => (BinaryFrontend.testCode_polytime (op i) c).comp (frame_polytime i.val))
  have h := computableInPolyTime_appendCodes hn hrows
  unfold code
  simpa only [List.finRange, List.map_ofFn, Function.comp_def] using h

/-- Polynomial binary time for the complete simultaneous-test CNF, including all output framing. -/
@[fun_prop] theorem build_polytime {r : ℕ} (op : Fin r → Comparison) (c : ℕ) :
    ComputableInPolyTime (build op c) encInput
      (encList (encList (encPair encNat encBool))) := by
  have hn : ComputableInPolyTime declared encInput encUnary := by
    unfold declared encInput
    fun_prop
  exact FunctionalCNF.write_polytime.comp (hn.prod ((code_polytime op c).prod (.const _)))

/-- Actual canonical original data, preserving every declared variable and comparison label. -/
@[expose] def ofData {n r : ℕ} (weights : Fin r → Fin n → ℕ)
    (positive : Fin r → Fin n → Bool) (target : Fin r → ℤ) : Input :=
  (n, (List.ofFn (fun i => List.ofFn fun j => (weights i j, positive i j)), List.ofFn target))

/-- Every actual family gate/output agrees with the approved typed joint circuit. -/
theorem code_ofData {n r : ℕ} (op : Fin r → Comparison) (c : ℕ)
    (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool) (target : Fin r → ℤ) :
    code op c (ofData weights positive target) =
      (joint op c weights positive target).code := by
  rw [← jointCode_eq]
  change appendCodes n (List.ofFn fun i : Fin r =>
    testCode (op i) c (BinaryFrontend.weight (frame i.val (ofData weights positive target)))
      (BinaryFrontend.positive (frame i.val (ofData weights positive target)))
      (BinaryFrontend.target (frame i.val (ofData weights positive target)))) =
    appendCodes n (List.ofFn fun i : Fin r => testCode (op i) c (weights i) (positive i) (target i))
  apply congrArg (appendCodes n)
  apply congrArg List.ofFn
  funext i
  have hw : BinaryFrontend.weight (frame i.val (ofData weights positive target)) = weights i := by
    funext (j : Fin n)
    simp only [BinaryFrontend.weight, BinaryFrontend.entry, BinaryFrontend.entries,
      frame, rows, ofData, List.getD_ofFn]
  have hp : BinaryFrontend.positive (frame i.val (ofData weights positive target)) =
      positive i := by
    funext (j : Fin n)
    simp only [BinaryFrontend.positive, BinaryFrontend.entry, BinaryFrontend.entries,
      frame, rows, ofData, List.getD_ofFn]
  have ht : BinaryFrontend.target (frame i.val (ofData weights positive target)) = target i := by
    simp only [BinaryFrontend.target, frame, targets, ofData, List.getD_ofFn]
  rw [hw, hp, ht]
  rfl

/-- Exact original-input clause correspondence, retaining correlated tests and unique extensions. -/
theorem build_ofData {n r : ℕ} (op : Fin r → Comparison) (c : ℕ)
    (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool) (target : Fin r → ℤ) :
    build op c (ofData weights positive target) = jointFormula op c weights positive target := by
  rw [build, code_ofData]
  simp only [jointFormula, FunctionalCNF.ofCircuit, List.ofFn_const]
  rfl

end Cslib.Circuits.Boolean.WeightedSum.Family

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedSum.Code
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# Binary original-input frames for polynomial-weight comparisons

The original declared count is unary; coefficients and integer targets are binary. One explicit
entry per declared input retains unused zero-weight variables. Admission checks the actual record
length and the fixed-exponent coefficient promise. `build` writes the actual comparison code/CNF;
its canonical correspondence reuses the proved grouped linear constructor, not supplied advice.
The parser/admission and dimension computations are polynomial-time. Certification
of the complete gate-list generator and Corollary A.2 counting/distribution
composition remains open.

Source: [ChenJiangZhu2027], Lemma A.1 / Corollary A.2, PDF pp.28–29.

## Main definitions

* `Input`, `encInput`, `admit`, `build`: original binary data, admission and actual construction.

## Main results

* `admit_polytime`, `width_polytime`: binary admission and derived-dimension certificates.
* `build_ofData`: exact original-input correspondence to the linear functional 3-CNF.
-/

public section

namespace Cslib.Circuits.Boolean.WeightedSum.BinaryFrontend

open Turing.MultiTapeTM

/-- Unary declared variables, explicit binary weight/polarity entries and binary integer target. -/
abbrev Input := ℕ × (List (ℕ × Bool) × ℤ)
/-- Original declared count, including zero-weight variables. -/
@[expose] def declared (x : Input) : ℕ := x.1
/-- Explicit coefficient and literal-polarity records in input-index order. -/
@[expose] def entries (x : Input) : List (ℕ × Bool) := let (_, (rows, _)) := x; rows
/-- Arbitrary binary integer target. -/
@[expose] def target (x : Input) : ℤ := let (_, (_, t)) := x; t
/-- One actual coefficient/polarity record; a missing position has zero weight. -/
@[expose] def entry (x : Input) (i : ℕ) : ℕ × Bool := (entries x).getD i (0, true)
/-- Actual original coefficient, without magnitude truncation. -/
@[expose] def weight (x : Input) (i : Fin (declared x)) : ℕ := (entry x i.val).1
/-- Actual original literal polarity. -/
@[expose] def positive (x : Input) (i : Fin (declared x)) : Bool := (entry x i.val).2
/-- Explicit framed encoding; no numeric coefficient is converted to unary. -/
@[expose] def encInput : Input ↪ List Bool :=
  encPair encUnary (encPair (encList (encPair encNat encBool)) encIntBin)

/-- Actual admission test for the original record length and all polynomially bounded weights. -/
@[expose] def admit (c : ℕ) (x : Input) : Bool :=
  decide ((entries x).length = declared x) &&
    (entries x).all (fun row => decide (row.1 ≤ declared x ^ c))

/-- The complete signed-target comparison is generated, rather than supplied with the input. -/
@[expose] def build (op : Comparison) (c : ℕ) (x : Input) : Logic.PL.CNF ℕ :=
  writeTest op c (weight x) (positive x) (target x)

/-- Canonical source instance, retaining one record for every declared variable. -/
@[expose] def ofData {n : ℕ} (weights : Fin n → ℕ) (polarity : Fin n → Bool) (t : ℤ) : Input :=
  (n, (List.ofFn (fun i => (weights i, polarity i)), t))

/-- Polynomial binary admission, including rejected huge coefficients. -/
@[fun_prop] theorem admit_polytime (c : ℕ) :
    ComputableInPolyTime (admit c) encInput encBool := by
  have hn : ComputableInPolyTime declared encInput encUnary := by
    unfold declared encInput; fun_prop
  have he : ComputableInPolyTime entries encInput (encList (encPair encNat encBool)) := by
    unfold entries encInput; fun_prop
  have hp := ComputableInPolyTime.unary_to_binary.comp
    ((ComputableInPolyTime.unary_pow c).comp hn)
  have ht : ComputableInPolyTime
      (fun p : Input × (ℕ × Bool) => decide (p.2.1 ≤ declared p.1 ^ c))
      (encPair encInput (encPair encNat encBool)) encBool := by
    have hw := (ComputableInPolyTime.snd encInput (encPair encNat encBool)).fst'
    exact ComputableInPolyTime.binary_le.comp
      (hw.prod (hp.comp (ComputableInPolyTime.fst encInput (encPair encNat encBool))))
  have ha := ComputableInPolyTime.allWithInput
    (test := fun x row => decide (row.1 ≤ declared x ^ c)) he ht
  have hl : ComputableInPolyTime
      (fun x => decide ((entries x).length = declared x)) encInput encBool := by
    fun_prop
  unfold admit
  exact ComputableInPolyTime.bool_and.comp (hl.prod ha)

/-- The actual logarithmic arithmetic word width is derived from the original input count. -/
@[fun_prop] theorem width_polytime (c : ℕ) :
    ComputableInPolyTime (fun x : Input => width (declared x) c) encInput encUnary := by
  have hn : ComputableInPolyTime declared encInput encUnary := by
    unfold declared encInput; fun_prop
  have hp := (ComputableInPolyTime.unary_pow (c + 1)).comp hn
  have hlog := (ComputableInPolyTime.unary_clog_const 2).comp
    (show ComputableInPolyTime (fun x => declared x ^ (c + 1) + 1) encInput encUnary from by
      fun_prop)
  unfold width
  fun_prop

/-- The actual original records write exactly the proved functional formula, with no free wires. -/
theorem build_ofData {n : ℕ} (op : Comparison) (c : ℕ) (weights : Fin n → ℕ)
    (polarity : Fin n → Bool) (t : ℤ) :
    build op c (ofData weights polarity t) = formula op c weights polarity t := by
  change writeTest (n := n) op c
    (fun i => ((List.ofFn (fun j => (weights j, polarity j))).getD i.val (0, true)).1)
    (fun i => ((List.ofFn (fun j => (weights j, polarity j))).getD i.val (0, true)).2) t = _
  have hw : (fun i : Fin n => ((List.ofFn (fun j => (weights j, polarity j))).getD
      i.val (0, true)).1) = weights := by
    funext i
    simp only [List.getD_ofFn]
  have hp : (fun i : Fin n => ((List.ofFn (fun j => (weights j, polarity j))).getD
      i.val (0, true)).2) = polarity := by
    funext i
    simp only [List.getD_ofFn]
  rw [hw, hp, writeTest_eq]

/-- The source coefficient promise makes the actual admission test succeed. -/
theorem admit_ofData {n : ℕ} (c : ℕ) (weights : Fin n → ℕ)
    (polarity : Fin n → Bool) (t : ℤ) (hw : ∀ i, weights i ≤ n ^ c) :
    admit c (ofData weights polarity t) = true := by
  simp [admit, entries, declared, ofData, List.all_eq_true, List.mem_ofFn, hw]

end Cslib.Circuits.Boolean.WeightedSum.BinaryFrontend

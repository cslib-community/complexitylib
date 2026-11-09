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
# Binary signed-coefficient normalization and actual comparison generation

Negative coefficients become complemented literals, with the exact negative constant removed
from the target. All magnitudes, offsets and targets stay binary. This is an explicit extension
of [ChenJiangZhu2027], Lemma A.1's nonnegative-coefficient construction (PDF pp.28–29).
The actual normalization and complete CNF generation have polynomial bit-time certificates.

## Main results

* `normalize_polytime`, `build_polytime`: actual binary signed normalization and CNF writing.
* `normalize_ofData`, `build_ofData`: exact offset and signed-circuit correspondence.
-/

public section

namespace Cslib.Circuits.Boolean.WeightedSum.SignedFrontend

open Turing.MultiTapeTM ComputableInPolyTime

/-- Unary declaration, signed binary coefficients and signed binary target. -/
abbrev Input := ℕ × (List ℤ × ℤ)
/-- Original input count; zero coefficients retain their original bits. -/
@[expose] def declared (x : Input) : ℕ := x.1
/-- Actual signed coefficients in original index order. -/
@[expose] def coefficients (x : Input) : List ℤ := let (_, (ws, _)) := x; ws
/-- Actual signed binary target. -/
@[expose] def target (x : Input) : ℤ := let (_, (_, t)) := x; t
/-- Complete original binary frame. -/
abbrev encInput := encPair encUnary (encPair (encList encIntBin) encIntBin)
/-- Compute the indispensable constant caused by negative-coefficient literal flips. -/
@[expose] def offset (x : Input) : ℤ := ((coefficients x).map (fun a => if a < 0 then a else 0)).sum
/-- Actual binary normalization; no magnitude expansion, target truncation or cancellation loss. -/
@[expose] def normalize (x : Input) : BinaryFrontend.Input :=
  (declared x, ((coefficients x).map (fun a => (a.natAbs, decide (0 ≤ a))), target x - offset x))
/-- Full actual signed comparison CNF from the original input, without supplied normalized data. -/
@[expose] def build (op : Comparison) (c : ℕ) (x : Input) : Logic.PL.CNF ℕ :=
  BinaryFrontend.build op c (normalize x)

/-- Every signed lookup, magnitude, sign test, offset addition and target subtraction is charged. -/
@[fun_prop] theorem normalize_polytime :
    ComputableInPolyTime normalize encInput BinaryFrontend.encInput := by
  have hn : ComputableInPolyTime declared encInput encUnary := by
    unfold declared encInput; fun_prop
  have hw : ComputableInPolyTime coefficients encInput (encList encIntBin) := by
    unfold coefficients encInput; fun_prop
  have ht : ComputableInPolyTime target encInput encIntBin := by
    unfold target encInput; fun_prop
  have habs : ComputableInPolyTime Int.natAbs encIntBin encNat :=
    .of_tidy ComputableTidilyInPolyTime.intBin_natAbs
  have hpos : ComputableInPolyTime (fun a : ℤ => decide (0 ≤ a)) encIntBin encBool :=
    .of_tidy (ComputableTidilyInPolyTime.intBin_le.comp
      ((ComputableTidilyInPolyTime.const 0).prod
        (ComputableTidilyInPolyTime.id' (encIn := encIntBin))))
  have hneg : ComputableInPolyTime (fun a : ℤ => decide (a < 0)) encIntBin encBool :=
    .of_tidy (ComputableTidilyInPolyTime.intBin_lt.comp
      ((ComputableTidilyInPolyTime.id' (encIn := encIntBin)).prod
        (ComputableTidilyInPolyTime.const 0)))
  have hone := hneg.ite' (id' (encIn := encIntBin)) (const 0)
  have hoff : ComputableInPolyTime offset encInput encIntBin := by
    unfold offset
    simpa only [Function.comp_def, decide_eq_true_eq] using
      ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.intBin_sum.comp
        ((hone.map.comp hw).tidy))
  have hrows := (habs.prod hpos).map.comp hw
  exact hn.prod (hrows.prod (ComputableInPolyTime.intBin_sub.comp (ht.prod hoff)))

/-- Complete actual binary signed-normalization/comparison/gate/CNF generation. -/
@[fun_prop] theorem build_polytime (op : Comparison) (c : ℕ) :
    ComputableInPolyTime (build op c) encInput
      (encList (encList (encPair encNat encBool))) :=
  (BinaryFrontend.build_polytime op c).comp normalize_polytime

/-- Canonical original signed data. -/
@[expose] def ofData {n : ℕ} (coeff : Fin n → ℤ) (t : ℤ) : Input :=
  (n, (List.ofFn coeff, t))

/-- The actual binary offset is exactly the constant in the approved signed-normalization law. -/
theorem normalize_ofData {n : ℕ} (coeff : Fin n → ℤ) (t : ℤ) :
    normalize (ofData coeff t) = BinaryFrontend.ofData
      (fun i => (coeff i).natAbs) (fun i => decide (0 ≤ coeff i)) (t - negativeOffset coeff) := by
  have he : (fun a : ℤ => if a < 0 then a else 0) = fun a => min a 0 := by
    funext a
    split_ifs with h
    · exact (min_eq_left (by omega)).symm
    · exact (min_eq_right (by omega)).symm
  simp only [normalize, ofData, declared, coefficients, target, offset, List.map_ofFn,
    Function.comp_def, he, List.sum_ofFn, negativeOffset, BinaryFrontend.ofData]

/-- Actual original-input writing agrees exactly with the previously proved signed test circuit. -/
theorem build_ofData {n : ℕ} (op : Comparison) (c : ℕ) (coeff : Fin n → ℤ) (t : ℤ) :
    build op c (ofData coeff t) = FunctionalCNF.write
      (FunctionalCNF.ofCircuit (signedTest op c coeff t) (fun _ => true)) := by
  rw [build, normalize_ofData, BinaryFrontend.build_ofData]
  rfl

end Cslib.Circuits.Boolean.WeightedSum.SignedFrontend

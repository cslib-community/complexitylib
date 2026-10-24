/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.AWPP.Amplification
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! # Nonconstant, variable-error clients for uniform AWPP amplification -/

open Cslib.Complexity Turing.MultiTapeTM

@[expose] public section

namespace Cslib.Complexity.Tests.UniformAWPP

def language : Set (List Bool) := {w | w.headD false = true}

private def numerator (w : List Bool) : ℤ := if w.headD false then 3 else 1

private theorem numerator_gap : numerator ∈ GapP encBits := by
  have h : ComputableTidilyInPolyTime
      (fun w : List Bool => if w.headD false then (3 : ℕ) else 1) encBits encNat := by fun_prop
  convert SharpP.natCast_mem_GapP (mem_SharpP_of_polyTime (.of_tidy h)) using 1
  ext w
  simp only [numerator]
  split_ifs <;> rfl

private theorem witness (w : List Bool) :
    (0 ≤ numerator w ∧ numerator w ≤ (2 : ℤ) ^ (2 : Polynomial ℕ).eval w.length) ∧
    (w ∈ language → 2 * (2 : ℤ) ^ (2 : Polynomial ℕ).eval w.length ≤ 3 * numerator w) ∧
    (w ∉ language → 3 * numerator w ≤ (2 : ℤ) ^ (2 : Polynomial ℕ).eval w.length) := by
  cases w with
  | nil => norm_num [numerator, language]
  | cons b w => cases b <;> norm_num [numerator, language]

private theorem language_mem : language ∈ AWPP encBits :=
  ⟨numerator, numerator_gap, 2, witness⟩

example : [true] ∈ language ∧ [false] ∉ language := by simp [language]

/-- The original witness has genuine error one quarter on both sides. -/
example : numerator [true] = 3 ∧ numerator [false] = 1 := by decide

/-- One GapP witness simultaneously achieves a varying exponential error bound. -/
example : ∃ G ∈ GapP encBits, ∃ P : Polynomial ℕ, ∀ w : List Bool,
    let D := (2 : ℤ) ^ P.eval w.length
    (0 ≤ G w ∧ G w ≤ D) ∧
      (w ∈ language → (2 : ℤ) ^ (w.length + 1) * (D - G w) ≤ D) ∧
      (w ∉ language → (2 : ℤ) ^ (w.length + 1) * G w ≤ D) :=
  exists_AWPP_gap_errorExponent language_mem (fun w => w.length + 1)
    (PolyBounded.self.add (.const 1))

/-- A possibly noncomputable requested rate is handled by a fixed dominating polynomial. -/
example (S : Set (List Bool)) : ∃ G ∈ GapP encBits, ∃ P : Polynomial ℕ, ∀ w : List Bool,
    let D := (2 : ℤ) ^ P.eval w.length
    let r := @ite ℕ (w ∈ S) (Classical.propDecidable _) w.length 0
    (0 ≤ G w ∧ G w ≤ D) ∧
      (w ∈ language → (2 : ℤ) ^ r * (D - G w) ≤ D) ∧
      (w ∉ language → (2 : ℤ) ^ r * G w ≤ D) := by
  classical
  apply exists_AWPP_gap_errorExponent language_mem
  exact PolyBounded.self.mono fun w => by
    simp only [encBits_apply]
    split_ifs <;> lia

/-- Zero requested exponent permits the empty majority experiment and its constant zero output. -/
example (g D : ℤ) : AWPPAmplification.majorityPolynomial g D 0 = 0 := by
  simp [AWPPAmplification.majorityPolynomial]

/-- A denominator of one is allowed, including the exact accepting endpoint. -/
example (e : ℕ) : (2 : ℤ) ^ e *
    (1 - AWPPAmplification.majorityPolynomial 1 1 (6 * e)) ≤ 1 := by
  simpa using (AWPPAmplification.majorityPolynomial_bounds
    (g := 1) (m := 0) (e := e) (by norm_num) (by norm_num)).2.1 (by norm_num)

/-- info: 'Cslib.Complexity.AWPPAmplification.amplify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.AWPPAmplification.amplify

/-- info: 'Cslib.Complexity.exists_AWPP_gap_errorExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.exists_AWPP_gap_errorExponent

end Cslib.Complexity.Tests.UniformAWPP

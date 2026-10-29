/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Approximation.Hamming
import Complexity.Computability.Circuit.Pointwise
import Cslib.Computability.Circuit.Boolean.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Two local approximation schemes for De Morgan circuits on two inputs: approximation by the
one-bit juntas, where every gate errs on at most one sample, and exact evaluation on truth tables,
where no gate errs. The first gives the lower bound of two gates for the exclusive or, in the
counting, Hamming and weighted forms of the lower-bound principle; the second makes the decoded
output equal to the target. -/

namespace ComplexityTests.CircuitHamming.Approximation

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Approximation Finset

/-! ### Approximation by one-bit juntas -/

/-- The six functions of two bits that depend on at most one bit. -/
def junta : Fin 6 → BitString 2 → Bool :=
  ![fun _ => false, fun _ => true, fun s => s 0, fun s => s 1, fun s => !s 0, fun s => !s 1]

/-- The first junta within Hamming distance one of `g`, or the constant `false`. -/
def nearest (g : BitString 2 → Bool) : Fin 6 :=
  ((List.finRange 6).find? fun i => decide (hammingDist g (junta i) ≤ 1)).getD 0

/-- Approximate a gate by the first junta within distance one of its value on the juntas. -/
def approxJunta : Interpretation signature (Fin 6) := fun op a =>
  nearest fun s => interpretation op fun i => junta (a i) s

/-- The samples on which a gate and its junta approximation differ. -/
def juntaExceptions (op : signature.Op) (a : Fin (signature.Arity op) → Fin 6) :
    Finset (BitString 2) :=
  univ.filter fun s => interpretation op (fun i => junta (a i) s) ≠ junta (approxJunta op a) s

/-- Every gate errs on at most one of the four samples. -/
theorem card_juntaExceptions_le : ∀ op a, #(juntaExceptions op a) ≤ 1 := by
  intro op
  cases op with
  | const b => cases b <;> decide
  | not => decide
  | and => decide
  | or => decide

/-- Approximation by one-bit juntas on two inputs: every gate errs on at most one sample. -/
def juntaScheme : Scheme interpretation approxJunta junta (fun s => s) ![2, 3] where
  relation := Eq
  relation_trans := Eq.trans
  map_relation _ _ _ h := congrArg _ (funext h)
  errorCost _ := 1
  exceptions := juntaExceptions
  input_correct s i := by fin_cases i <;> rfl
  gate_correct op a s hs := by simpa [juntaExceptions] using hs
  exceptions_card_le := card_juntaExceptions_le

instance : DecidableRel juntaScheme.relation := fun u v => inferInstanceAs (Decidable (u = v))

/-- The exclusive or is at Hamming distance at least two from every one-bit junta. -/
theorem le_hammingDist_xor_junta (a : Fin 6) :
    2 ≤ hammingDist (fun s : BitString 2 => s 0 ^^ s 1) (junta a) := by
  fin_cases a <;> decide

/-- A one-gate circuit for the conjunction. -/
private def andCircuit : Circuit signature 2 1 :=
  ⟨.gate .empty ⟨.and, fun a => .input a⟩, fun _ => .gate 0⟩

/-- **The lower-bound principle in Hamming, counting, and uniform-weighted terms** for the
two-input exclusive or, together with the one-gate conjunction approximation error bound. -/
example :
    2 ≤ complexity interpretation (single fun x : BitString 2 => x 0 ^^ x 1) ∧
      2 ≤ 1 * complexity interpretation (single fun x : BitString 2 => x 0 ^^ x 1) ∧
      (1 / 2 : ℝ) ≤
        1 / 4 * complexity interpretation (single fun x : BitString 2 => x 0 ^^ x 1) ∧
      hammingDist (fun s : BitString 2 => s 0 && s 1)
        (junta (andCircuit.eval approxJunta ![2, 3] 0)) ≤ 1 := by
  refine ⟨?_,
    juntaScheme.le_mul_complexity univ _ (fun _ => le_rfl) fun a => by fin_cases a <;> decide,
    ?_,
    (juntaScheme.hammingDist_le_sum_errorCost id andCircuit fun _ => rfl).trans_eq rfl⟩
  · simpa using juntaScheme.le_mul_complexity_of_le_hammingDist id _
      (fun _ => le_rfl) le_hammingDist_xor_junta
  · refine juntaScheme.le_mul_complexity_of_le_sum_failures (μ := fun _ => 1 / 4)
      (fun _ => by norm_num) univ _ (fun op a => ?_) fun a => ?_
    · have h : ((#(juntaExceptions op a) : ℕ) : ℝ) ≤ 1 := by
        exact_mod_cast card_juntaExceptions_le op a
      change ∑ s ∈ juntaExceptions op a, (1 / 4 : ℝ) ≤ 1 / 4
      rw [sum_const, nsmul_eq_mul]
      nlinarith
    · have h : 2 ≤ #(juntaScheme.failures univ a fun s : BitString 2 => s 0 ^^ s 1) := by
        fin_cases a <;> decide
      have h' : (2 : ℝ) ≤ #(juntaScheme.failures univ a fun s : BitString 2 => s 0 ^^ s 1) := by
        exact_mod_cast h
      rw [sum_const, nsmul_eq_mul]
      linarith

/-! ### Exact evaluation on truth tables -/

/-- Exact evaluation on truth tables: the pointwise lift approximates exactly, with no
exceptions. -/
def exactScheme : Scheme interpretation (interpretation.pointwise (BitString 2))
    (fun (a : BitString 2 → Bool) s => a s) (fun s => s) (fun j x => x j) where
  relation := Eq
  relation_trans := Eq.trans
  map_relation _ _ _ h := congrArg _ (funext h)
  errorCost _ := 0
  exceptions _ _ := ∅
  input_correct _ _ := rfl
  gate_correct _ _ _ _ := rfl
  exceptions_card_le _ _ := le_rfl

/-- With no local errors, the decoded output of a circuit is the function it computes. -/
example : hammingDist (fun s : BitString 2 => s 0 && s 1)
    (andCircuit.eval (interpretation.pointwise (BitString 2)) (fun j x => x j) 0) = 0 :=
  Nat.le_zero.1 <| (exactScheme.hammingDist_le_sum_errorCost id andCircuit fun _ => rfl).trans_eq
    (by simp [exactScheme, andCircuit])

end ComplexityTests.CircuitHamming.Approximation

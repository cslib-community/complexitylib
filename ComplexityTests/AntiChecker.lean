/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.MCSP.AntiChecker.Certificate
import Complexity.Computability.Circuit.Boolean.Hierarchy

/-!
# Tests for description-counting anti-checkers

The indexed family below has three descriptions but only two different functions. The concrete
MCSP checks also retain duplicate descriptions, exclude invalid output wires, and cover zero
inputs and zero gates. The final example applies the certificate-length bound to an actual
one-input function satisfying the circuit-hardness hypothesis.
-/

namespace ComplexityTests.AntiChecker

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Finset

/-- Descriptions `1` and `2` both represent the constant-true function. -/
private def repeatedEval (i : Fin 3) (_ : Bool) : Bool := decide (i ≠ 0)

-- Three descriptions, two functions, and two refuted descriptions at input `false`.
example :
    (univ : Finset (Fin 3)).card = 3 ∧
    ((univ : Finset (Fin 3)).image repeatedEval).card = 2 ∧
    #{i : Fin 3 | repeatedEval i false ≠ false} = 2 ∧
    #{i : Fin 3 | repeatedEval i true ≠ true} = 1 := by
  decide

private theorem repeatedEval_majority_ne (g : Fin 1 → Fin 3) :
    (fun x => strictMajority 1 fun i => repeatedEval (g i) x) ≠ id := by
  intro h
  exact Bool.false_ne_true ((congrFun h false).symm.trans (congrFun h true))

-- Applying the indexed theorem does not require injectivity of evaluation.
example : ∃ x : Bool, 3 ≤ 16 * #{i : Fin 3 | repeatedEval i x ≠ x} := by
  simpa using MCSP.exists_card_le_sixteen_mul_eval repeatedEval
    (by decide : 0 < 1) (by decide : Fintype.card Bool ≤ 2 ^ 1)
    (show (univ : Finset (Fin 3)).Nonempty from ⟨0, mem_univ _⟩)
    (fun g _ => repeatedEval_majority_ne g)

-- The residual bound counts all three descriptions, including both constant-true encodings.
example : ∃ S : Finset Bool, #S ≤ 1 ∧
    16 * #{i : Fin 3 | ∀ x ∈ S, repeatedEval i x = x} ≤ 45 := by
  simpa using MCSP.exists_card_filter_le_eval repeatedEval
    (by decide : 0 < 1) (by decide : Fintype.card Bool ≤ 2 ^ 1)
    (univ : Finset (Fin 3)) (fun g _ => repeatedEval_majority_ne g) 1

-- The family contains fewer than four descriptions, giving the advertised `16 * 2` bound.
example : ∃ S : Finset Bool, #S ≤ 32 ∧
    MCSP.IsAntiChecker (repeatedEval '' (Set.univ : Set (Fin 3))) id S := by
  simpa using MCSP.exists_isAntiChecker_image repeatedEval
    (by decide : 0 < 1) (by decide : Fintype.card Bool ≤ 2 ^ 1)
    (univ : Finset (Fin 3)) (fun g _ => repeatedEval_majority_ne g)
    (by decide : (univ : Finset (Fin 3)).card < 2 ^ 2)

-- A family containing the target itself cannot have an anti-checker.
example (S : Set Bool) : ¬ MCSP.IsAntiChecker {id} (id : Bool → Bool) S := by
  intro h
  obtain ⟨x, _, hx⟩ := h id (Set.mem_singleton _)
  exact hx rfl

-- For two inputs and zero gates, output-wire encodings `01` and `10` both select input `1`.
-- Encoding `11` is invalid because there are only two input wires.
private def certificate01 : BitString (certLength 2 0) := fun i => decide (i.val = 1)
private def certificate10 : BitString (certLength 2 0) := fun i => decide (i.val = 0)
private def certificate11 : BitString (certLength 2 0) := fun _ => true

example :
    certLength 2 0 = 2 ∧
    (MCSP.validCertificates 2 0).card = 3 ∧
    certificate01 ∈ MCSP.validCertificates 2 0 ∧
    certificate10 ∈ MCSP.validCertificates 2 0 ∧
    certificate11 ∉ MCSP.validCertificates 2 0 ∧
    MCSP.certificateFunction 2 0 certificate01 = MCSP.certificateFunction 2 0 certificate10 ∧
    MCSP.certificateFunction 2 0 certificate01 ![false, true] = true ∧
    MCSP.certificateFunction 2 0 certificate01 ![true, false] = false := by
  exact ⟨by decide, by decide,
    by rw [MCSP.mem_validCertificates]; decide,
    by rw [MCSP.mem_validCertificates]; decide,
    by rw [MCSP.mem_validCertificates]; decide,
    rfl, by decide, by decide⟩

-- With zero inputs and zero gates there is no output wire and hence no valid certificate.
example : MCSP.validCertificates 0 0 = ∅ := by
  decide

-- One input and zero gates give exactly the identity function.
example :
    MCSP.certificateFunction 1 0 ''
      (MCSP.validCertificates 1 0 : Set (BitString (certLength 1 0))) =
        {fun x : BitString 1 => x 0} := by
  ext f
  simp only [Set.mem_image, Finset.mem_coe, MCSP.mem_validCertificates, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw0 : w ⟨0, by decide⟩ = false := by
      cases h : w ⟨0, by decide⟩
      · rfl
      · have heq : w = ![true] := by funext i; fin_cases i; exact h
        subst w
        revert hw
        decide
    have heq : w = ![false] := by funext i; fin_cases i; exact hw0
    subst w
    decide
  · rintro rfl
    exact ⟨![false], by decide, by decide⟩

private theorem strictMajority_one_complexity :
    complexity interpretation (single (strictMajority 1)) = 0 := by
  have h : strictMajority 1 = fun x : BitString 1 => x 0 := by decide
  rw [h]
  exact complexity_wiring (I := interpretation) (fun _ : Fin 1 => (0 : Fin 1))

-- The constant-true function needs one gate, whereas a majority of one zero-gate circuit
-- needs zero gates. Thus the circuit-hardness assumptions are satisfiable.
example : ∃ S : Finset (BitString 1), #S ≤ 32 ∧
    SuccinctMCSP.Instance.ofFunction (fun _ => true) S 0 ∉ SuccinctMCSP := by
  have hf : 1 * 0 + complexity interpretation (single (strictMajority 1)) <
      complexity interpretation (single fun _ : BitString 1 => true) := by
    rw [strictMajority_one_complexity, complexity_const]
    decide
  obtain ⟨S, hS, hanti⟩ := MCSP.exists_isAntiChecker_le_certLength
    (by decide : 0 < 1) (by decide : 1 ≤ 1) hf
  exact ⟨S, hS, MCSP.isAntiChecker_computableFunctions_iff_notMem.mp hanti⟩

end ComplexityTests.AntiChecker

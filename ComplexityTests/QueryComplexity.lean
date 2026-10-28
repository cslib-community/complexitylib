/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.QueryComplexity.Measures
import Complexity.Computability.DecisionTree.Certificate
import Complexity.Computability.DecisionTree.Influence
import Complexity.Computability.DecisionTree.Parity
import Complexity.Computability.DecisionTree.Restrict
import Complexity.Computability.QueryComplexity.Restriction

/-! Joint upstream imports, native measures, and retained arbitrary-coordinate clients. -/

namespace ComplexityTests.QueryComplexity

open Cslib Cslib.BitString Cslib.QueryComplexity Finset
open scoped BigOperators

-- On 2-bit conjunction, 0-certificates have size 1 and 1-certificates have size 2, so the
-- product bound gives D(and₂) ≤ 1 * 2 = 2. In the second example, the computed
-- `certificateComplexity and₂ = 2` is the substantive check; the instantiated `C²` bound
-- `D(and₂) ≤ 4` is weaker than the trivial `complexity_le_card` bound of 2.
private def and₂ : BooleanFunction 2 := fun x => x 0 && x 1

example :
    certificateComplexityFor and₂ false = 1 ∧
      certificateComplexityFor and₂ true = 2 ∧
      DecisionTree.complexity and₂ ≤ 2 := by
  have h0 : certificateComplexityFor and₂ false = 1 := by decide
  have h1 : certificateComplexityFor and₂ true = 2 := by decide
  refine ⟨h0, h1, ?_⟩
  simpa [h0, h1] using DecisionTree.complexity_le_certificateComplexityFor_mul and₂

example :
    certificateComplexity and₂ = 2 ∧ DecisionTree.complexity and₂ ≤ 4 := by
  have hc : certificateComplexity and₂ = 2 := by decide
  refine ⟨hc, ?_⟩
  simpa [hc] using DecisionTree.complexity_le_certificateComplexity_sq and₂

example : sensitivity (parity 3) = 3 ∧ certificateComplexity (parity 3) = 3 := by decide

-- The finite minimum is executable, including empty-coordinate and missing-output cases.
example : certificateComplexityAt (parity 2) (fun _ => false) = 2 := by decide

example (f : BooleanFunction 0) : certificateComplexity f = 0 :=
  Nat.eq_zero_of_le_zero (certificateComplexity_le_card f)

example (f : BooleanFunction 0) : sensitivity f = 0 :=
  Nat.eq_zero_of_le_zero (sensitivity_le_card f)

example (f : BooleanFunction 0) : blockSensitivity f = 0 :=
  Nat.eq_zero_of_le_zero (blockSensitivity_le_card f)

example (f : BooleanFunction 0) : DecisionTree.complexity f = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using DecisionTree.complexity_le_card f

example {n : ℕ} : certificateComplexityFor (fun _ : BitString n => false) true = 0 := by
  simp [certificateComplexityFor]

example {n : ℕ} (b : Bool) : certificateComplexity (fun _ : BitString n => b) = 0 := by
  apply Nat.eq_zero_of_le_zero
  refine Finset.sup_le fun x _ => ?_
  exact (certificateComplexityAt_le (S := ∅) (fun _ _ => rfl)).trans_eq (by simp)

-- A non-Fin coordinate type and non-Boolean output still have the generic counting bound.
example : DecisionTree.complexity (fun x : Bool → Bool => x) = 2 := by
  apply (DecisionTree.complexity_eq_card_of_forall_update_ne
    (x := fun _ => false) ?_).trans (show Fintype.card Bool = 2 from rfl)
  intro i hi
  have h := congrFun hi i
  simp at h

-- For infinitely many possible coordinates, the explicit tree witness suffices.
private def natTree : DecisionTree ℕ ℕ := .node 0 (.leaf 3) (.leaf 5)

example : {0} ⊆ natTree.queries (fun _ => false) := by
  apply DecisionTree.subset_queries_of_forall_update_ne (f := natTree.eval) (fun _ => rfl)
  intro i hi
  have : i = 0 := Finset.mem_singleton.mp hi
  subst i
  decide

-- Upstream assignments and generic restrictions need no conversion or alternative encoding.
private def fixZeroFalse : Cslib.QueryComplexity.PartialAssignment 3 :=
  fun i => if i = 0 then some false else none

example :
    Cslib.QueryComplexity.Agrees fixZeroFalse ![false, true, false] ∧
      ¬ Cslib.QueryComplexity.Agrees fixZeroFalse ![true, true, false] := by
  change Cslib.BitString.PartialAssignment.Agrees fixZeroFalse ![false, true, false] ∧
    ¬ Cslib.BitString.PartialAssignment.Agrees fixZeroFalse ![true, true, false]
  rw [Cslib.BitString.PartialAssignment.agrees_iff_fill_eq,
    Cslib.BitString.PartialAssignment.agrees_iff_fill_eq]
  decide

example {n : ℕ} (C : Cslib.QueryComplexity.PartialAssignment n) :
    Cslib.QueryComplexity.support C = Cslib.BitString.PartialAssignment.support C := rfl

example {n : ℕ} (B : Finset (Fin n)) (x : BitString n) : flipOn B x = flipBlock B x := rfl

example {n : ℕ} (f : BooleanFunction n) (C : Cslib.QueryComplexity.PartialAssignment n)
    (b : Bool) (h : Forces f C b) :
    DecisionTree.complexity (f ∘ Cslib.BitString.PartialAssignment.fill C) = 0 :=
  DecisionTree.complexity_eq_zero_iff.mpr fun x y =>
    ((forces_iff_forall_fill f C b).mp h x).trans ((forces_iff_forall_fill f C b).mp h y).symm

example {n : ℕ} (x y : BitString n) (S : Finset (Fin n)) :
    Cslib.BitString.PartialAssignment.fill (Cslib.QueryComplexity.restrict x S) y =
      S.piecewise x y := by simp

example :
    2 ≤ DecisionTree.complexity (parity 3 ∘ Cslib.BitString.PartialAssignment.fill fixZeroFalse) ∧
      DecisionTree.complexity (parity 3 ∘ Cslib.BitString.PartialAssignment.fill fixZeroFalse) ≤
        3 := by
  have hfree : #(Cslib.BitString.PartialAssignment.free fixZeroFalse) = 2 := by decide
  refine ⟨?_, ?_⟩
  · simpa [hfree, Function.comp_def] using
      DecisionTree.card_free_le_complexity_parity_fill fixZeroFalse
  · exact (DecisionTree.complexity_comp_fill_le fixZeroFalse (parity 3)).trans_eq
      DecisionTree.complexity_parity

-- Generic Fourier theory and the native sensitivity corollary coexist.
example (b : Bool) : totalInfluence (fun _ : Bool → Bool => signVal b) = 0 := by
  rw [totalInfluence_signVal (fun _ : Bool → Bool => b)]
  simp

example {n : ℕ} : totalInfluence (fun x => signVal (parity n x)) = n := by
  rw [totalInfluence_eq_expect_sensitivityAt (parity n)]
  simp [sensitivityAt_parity]

example : totalInfluence (fun x => signVal (and₂ x)) ≤ 2 := by
  have hs : sensitivity and₂ = 2 := by decide
  simpa [hs] using totalInfluence_le_sensitivity and₂

end ComplexityTests.QueryComplexity

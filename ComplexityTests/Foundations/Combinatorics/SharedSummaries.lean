/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import Complexity.Foundations.Combinatorics.SharedSummaries
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.BigOperators

/-! # Shared-summary finite identity boundary cases

The representatives below are deliberately OUTSIDE the restricted local fibers. The full
measurement box also includes impossible tuples. No efficient representative oracle is asserted.
-/

@[expose] public section

open Finset Cslib.SharedSummaries
open scoped BigOperators

namespace SharedSummariesTests

/-- A zero-row measurement: both Boolean states have the same summary. -/
def zeroMeasure (_ : Bool) (_ : Bool) : Bool := false

/-- Choose false in every unrestricted fiber, ignoring restrictions. -/
def falseRepresentative (_y : Bool → Bool)
    (_ : ∀ g, ∃ u, zeroMeasure g u = _y g) : Bool → Bool := fun _ => false

/-- A different unrestricted representative, also valid when the tuple is realizable. -/
def trueRepresentative (_y : Bool → Bool)
    (_ : ∀ g, ∃ u, zeroMeasure g u = _y g) : Bool → Bool := fun _ => true

private theorem false_valid (y : Bool → Bool) (hy : ∀ g, ∃ u, zeroMeasure g u = y g)
    (g : Bool) : zeroMeasure g (falseRepresentative y hy g) = y g := by
  obtain ⟨u, hu⟩ := hy g
  exact hu

private theorem true_valid (y : Bool → Bool) (hy : ∀ g, ∃ u, zeroMeasure g u = y g)
    (g : Bool) : zeroMeasure g (trueRepresentative y hy g) = y g := by
  obtain ⟨u, hu⟩ := hy g
  exact hu

/-- A weighted local factor: the two groups assign weights three and two to their true states. -/
def weight (g : Bool) (x : Bool → Bool) : ℤ := if x g then (if g then 2 else 3) else 5

private theorem weight_locality (g : Bool) (x x' : Bool → Bool)
    (_ : ∀ h, zeroMeasure h (x h) = zeroMeasure h (x' h)) (hx : x g = x' g) :
    weight g x = weight g x' := by simp only [weight, hx]

-- The unrestricted representative is false, while the only permitted state is true.
example : falseRepresentative (fun _ => false) (by intro g; exact ⟨false, rfl⟩) false ∉
    ({true} : Finset Bool) := by decide

/-- Both local restrictions are nonempty although their chosen representatives violate them. -/
theorem restricted_contribution :
    fiberContribution zeroMeasure (fun _ => {true}) weight falseRepresentative
      (fun _ => false) = 6 := by
  norm_num [fiberContribution, zeroMeasure, falseRepresentative, weight, Fintype.prod_bool]

-- The whole supplied box contains this unrealizable tuple: it contributes zero, not an oracle.
example : fiberContribution zeroMeasure (fun _ => univ) weight falseRepresentative
    (fun _ => true) = 0 := by
  simp [fiberContribution, zeroMeasure]

-- An empty restricted fiber contributes zero even though every unrestricted fiber is nonempty.
example : fiberContribution zeroMeasure (fun g => if g then ∅ else {true}) weight
    falseRepresentative (fun _ => false) = 0 := by
  norm_num [fiberContribution, zeroMeasure, falseRepresentative, weight, Fintype.prod_bool]

-- Switching unrestricted representatives preserves the same concrete weighted answer.
example : fiberContribution zeroMeasure (fun _ => {true}) weight trueRepresentative
    (fun _ => false) = 6 := by
  rw [← fiberContribution_eq zeroMeasure (fun _ => {true}) weight weight_locality
    falseRepresentative trueRepresentative false_valid true_valid]
  exact restricted_contribution

-- All four measurement tuples are enumerated, although only the all-false tuple is realizable.
example : (∑ y ∈ Fintype.piFinset (fun _ : Bool => (univ : Finset Bool)),
    fiberContribution zeroMeasure (fun _ => {true}) weight falseRepresentative y) = 6 := by
  rw [← sum_prod_eq_sum_measurement_fibers zeroMeasure (fun _ => univ)
    (fun _ _ => mem_univ _) (fun _ => {true}) weight weight_locality
    falseRepresentative false_valid]
  simp [Fintype.piFinset_singleton, weight]

-- Zero measurement rows do not delete free Boolean choices: two groups still have four tuples.
example : (∑ y ∈ Fintype.piFinset (fun _ : Bool => (univ : Finset Bool)),
    fiberContribution zeroMeasure (fun _ => univ) (fun _ _ => (1 : ℤ)) falseRepresentative y) =
    4 := by
  rw [← sum_prod_eq_sum_measurement_fibers zeroMeasure (fun _ => univ)
    (fun _ _ => mem_univ _) (fun _ => univ) (fun _ _ => (1 : ℤ))
    (fun _ _ _ _ _ => rfl) falseRepresentative false_valid]
  calc
    _ = ∏ g : Bool, ∑ _u ∈ (univ : Finset Bool), (1 : ℤ) :=
      (Finset.prod_univ_sum (fun _ : Bool => (univ : Finset Bool))
        (fun (_ : Bool) (_ : Bool) => (1 : ℤ))).symm
    _ = 4 := by norm_num [Fintype.prod_bool]

-- With no groups there is one empty assignment and the product is one, not zero.
example : fiberContribution (G := Fin 0) (X := fun _ => Bool) (Y := fun _ => Bool)
    (fun _ b => b) (fun _ => univ) (fun _ _ => (1 : ℤ))
    (fun _ _ i => i.elim0) (fun i => i.elim0) = 1 := by
  simp [fiberContribution]

/-- A genuinely coupled factor without fiber locality; locality cannot simply be omitted. -/
def coupled (_ : Bool) (x : Bool → Bool) : ℤ := if x false = x true then 1 else 0

example : ¬(∀ g (x x' : Bool → Bool),
    (∀ h, zeroMeasure h (x h) = zeroMeasure h (x' h)) →
    x g = x' g → coupled g x = coupled g x') := by
  intro h
  have hbad := h false (fun _ => false) id (fun _ => rfl) rfl
  norm_num [coupled] at hbad

/-- With identity measurements, a valid representative is the measurement tuple itself. -/
def identityRepresentative (y : Bool → Bool) (_ : ∀ g : Bool, ∃ u : Bool, u = y g) :
    Bool → Bool := y

-- Factors really may depend on the OTHER group through its shared summary. Two equal-bit
-- assignments contribute one; the two unequal assignments contribute zero.
example : (∑ y ∈ Fintype.piFinset (fun _ : Bool => (univ : Finset Bool)),
    fiberContribution (fun (_ : Bool) (u : Bool) => u) (fun _ => univ) coupled
      identityRepresentative y) = 2 := by
  rw [← sum_prod_eq_sum_measurement_fibers (fun (_ : Bool) (u : Bool) => u)
    (fun _ => univ) (fun _ _ => mem_univ _) (fun _ => univ) coupled
    (fun g _ _ hm _ => congrArg (coupled g) (funext hm)) identityRepresentative
    (fun _ _ _ => rfl)]
  decide

-- An empty local state type gives an unrealizable tuple. No Inhabited assumption is hidden.
example : fiberContribution (G := Unit) (X := fun _ => Fin 0) (Y := fun _ => Unit)
    (fun _ _ => ()) (fun _ => ∅) (fun _ _ => (1 : ℤ))
    (fun _ hy _ => (hy ()).choose) (fun _ => ()) = 0 := by
  simp [fiberContribution]

-- The rational kernel bridge permits dependence on the other group's first coordinate,
-- while zero-summary shifts can change its second coordinate freely.
example (x x' : Bool → ℚ × ℚ) (hm : ∀ g, (x g).1 = (x' g).1)
    (hg : x false = x' false) :
    (x false).2 + (x false).1 + (x true).1 =
      (x' false).2 + (x' false).1 + (x' true).1 := by
  apply fiber_locality_of_kernel_shifts (V := fun _ : Bool => ℚ × ℚ) (W := fun _ => ℚ)
    (fun _ => LinearMap.fst ℚ ℚ ℚ)
    (fun g y => (y g).2 + (y false).1 + (y true).1) ?_ false x x' hm hg
  intro g j hj base delta hdelta
  change delta.1 = 0 at hdelta
  cases g <;> cases j <;> simp_all

end SharedSummariesTests

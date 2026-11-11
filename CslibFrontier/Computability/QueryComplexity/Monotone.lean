/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Certificate
public import CslibFrontier.Computability.QueryComplexity.OneSided
public import CslibFrontier.Foundations.Data.BitString.Weight

/-!
# Query complexity of monotone functions

For a monotone Boolean function, certificate complexity, block sensitivity and sensitivity
coincide: `C(f) = bs(f) = s(f)` [Nisan1991]. Let `f(x) = 1` and let `y ≤ x` be an input of value
`1` of least weight below `x`. Clearing any true bit of `y` gives a lighter input below `x`, which
has value `0`, so every true bit of `y` is sensitive at `y`. Conversely every input agreeing with
`x` on the true bits of `y` lies above `y`, so has value `1`. So the true bits of `y` certify `x`,
and `C(f, x) ≤ s(f, y) ≤ s₁(f)`. Dually `C(f, x) ≤ s₀(f)` when `f(x) = 0`, using an input of value
`0` of largest weight above `x`. With `D(f) ≤ C₀(f) C₁(f)` this gives `D(f) ≤ s₀(f) s₁(f) ≤ s(f)²`
for monotone `f`.

## Main results

* `Cslib.QueryComplexity.certificateComplexityFor_le_sensitivityFor_of_monotone`:
  `C_b(f) ≤ s_b(f)` for monotone `f`.
* `Cslib.QueryComplexity.certificateComplexity_eq_sensitivity_of_monotone`,
  `Cslib.QueryComplexity.blockSensitivity_eq_sensitivity_of_monotone`: `C(f) = s(f)` and
  `bs(f) = s(f)` for monotone `f`.
* `Cslib.DecisionTree.complexity_le_sensitivityFor_mul_sensitivityFor_of_monotone`,
  `Cslib.DecisionTree.complexity_le_sensitivity_sq_of_monotone`: `D(f) ≤ s₀(f) s₁(f) ≤ s(f)²` for
  monotone `f`.

## References

* [N. Nisan, *CREW PRAMs and decision trees*][Nisan1991]
* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
-/

@[expose] public section

namespace Cslib

open Finset BitString

variable {n : ℕ}

namespace QueryComplexity

variable {f : BooleanFunction n}

/-- At an input of value `1`, a monotone function has a certificate of size at most `s₁(f)`: the
true bits of an input of value `1` of least weight below it. -/
private theorem certificateComplexityAt_le_sensitivityFor_true (hf : Monotone f)
    {x : BitString n} (hx : f x = true) : certificateComplexityAt f x ≤ sensitivityFor f true := by
  obtain ⟨y, hy, hmin⟩ := exists_min_image (univ.filter fun y => y ≤ x ∧ f y = true) weight
    ⟨x, mem_filter.2 ⟨mem_univ _, le_rfl, hx⟩⟩
  obtain ⟨hyx, hfy⟩ := (mem_filter.1 hy).2
  -- clearing a true bit of `y` gives a lighter input below `x`, of value `0`
  have hsens : ∀ i ∈ univ.filter fun i => y i = true, IsSensitiveCoord f y i := by
    intro i hi
    have hyi : y i = true := (mem_filter.1 hi).2
    rw [IsSensitiveCoord, hyi, Bool.not_true, hfy]
    intro h
    have hw := weight_update_false hyi
    have := hmin _ (mem_filter.2 ⟨mem_univ _,
      (update_le_iff.2 ⟨Bool.false_le _, fun _ _ => le_rfl⟩).trans hyx, h⟩)
    omega
  -- the true bits of `y` certify the value `1`
  refine (certificateComplexityAt_le (S := univ.filter fun i => y i = true) fun z hz => ?_).trans
    ((card_le_sensitivityAt hsens).trans (sensitivityAt_le_sensitivityFor hfy))
  have hyz : y ≤ z := fun k => by
    cases hk : y k with
    | false => exact Bool.false_le _
    | true => exact hk ▸ (hyx k).trans_eq (hz k (mem_filter.2 ⟨mem_univ _, hk⟩)).symm
  have := hf hyz
  rw [hfy] at this
  rw [hx]
  exact le_antisymm (Bool.le_true _) this

/-- At an input of value `0`, a monotone function has a certificate of size at most `s₀(f)`: the
false bits of an input of value `0` of largest weight above it. -/
private theorem certificateComplexityAt_le_sensitivityFor_false (hf : Monotone f)
    {x : BitString n} (hx : f x = false) :
    certificateComplexityAt f x ≤ sensitivityFor f false := by
  obtain ⟨y, hy, hmax⟩ := exists_max_image (univ.filter fun y => x ≤ y ∧ f y = false) weight
    ⟨x, mem_filter.2 ⟨mem_univ _, le_rfl, hx⟩⟩
  obtain ⟨hxy, hfy⟩ := (mem_filter.1 hy).2
  -- setting a false bit of `y` gives a heavier input above `x`, of value `1`
  have hsens : ∀ i ∈ univ.filter fun i => y i = false, IsSensitiveCoord f y i := by
    intro i hi
    have hyi : y i = false := (mem_filter.1 hi).2
    rw [IsSensitiveCoord, hyi, Bool.not_false, hfy]
    intro h
    have hw := weight_update_true hyi
    have := hmax _ (mem_filter.2 ⟨mem_univ _,
      hxy.trans (le_update_iff.2 ⟨Bool.le_true _, fun _ _ => le_rfl⟩), by simpa using h⟩)
    omega
  -- the false bits of `y` certify the value `0`
  refine (certificateComplexityAt_le (S := univ.filter fun i => y i = false) fun z hz => ?_).trans
    ((card_le_sensitivityAt hsens).trans (sensitivityAt_le_sensitivityFor hfy))
  have hzy : z ≤ y := fun k => by
    cases hk : y k with
    | false => exact hk ▸ (hz k (mem_filter.2 ⟨mem_univ _, hk⟩)).trans_le (hxy k)
    | true => exact Bool.le_true _
  have := hf hzy
  rw [hfy] at this
  rw [hx]
  exact le_antisymm this (Bool.false_le _)

/-- For a monotone function, `C(f, x) ≤ s_{f(x)}(f)`. -/
theorem certificateComplexityAt_le_sensitivityFor_of_monotone (hf : Monotone f)
    (x : BitString n) : certificateComplexityAt f x ≤ sensitivityFor f (f x) := by
  cases hx : f x with
  | false => exact certificateComplexityAt_le_sensitivityFor_false hf hx
  | true => exact certificateComplexityAt_le_sensitivityFor_true hf hx

/-- For a monotone function, `C_b(f) ≤ s_b(f)`. -/
theorem certificateComplexityFor_le_sensitivityFor_of_monotone (hf : Monotone f) (b : Bool) :
    certificateComplexityFor f b ≤ sensitivityFor f b :=
  Finset.sup_le fun x hx => (mem_filter.1 hx).2 ▸
    certificateComplexityAt_le_sensitivityFor_of_monotone hf x

/-- **Certificate complexity of monotone functions** [Nisan1991]: `C(f) = s(f)`. -/
theorem certificateComplexity_eq_sensitivity_of_monotone (hf : Monotone f) :
    certificateComplexity f = sensitivity f :=
  le_antisymm (Finset.sup_le fun x _ =>
      (certificateComplexityAt_le_sensitivityFor_of_monotone hf x).trans
        (sensitivityFor_le_sensitivity f _))
    ((sensitivity_le_blockSensitivity f).trans (blockSensitivity_le_certificateComplexity f))

/-- **Block sensitivity of monotone functions** [Nisan1991]: `bs(f) = s(f)`. -/
theorem blockSensitivity_eq_sensitivity_of_monotone (hf : Monotone f) :
    blockSensitivity f = sensitivity f :=
  le_antisymm ((blockSensitivity_le_certificateComplexity f).trans_eq
    (certificateComplexity_eq_sensitivity_of_monotone hf)) (sensitivity_le_blockSensitivity f)

end QueryComplexity

namespace DecisionTree

open QueryComplexity

variable {f : BooleanFunction n}

/-- For a monotone function, `D(f) ≤ s₀(f) s₁(f)`. -/
theorem complexity_le_sensitivityFor_mul_sensitivityFor_of_monotone (hf : Monotone f) :
    complexity f ≤ sensitivityFor f false * sensitivityFor f true :=
  (complexity_le_certificateComplexityFor_mul f).trans
    (Nat.mul_le_mul (certificateComplexityFor_le_sensitivityFor_of_monotone hf false)
      (certificateComplexityFor_le_sensitivityFor_of_monotone hf true))

/-- For a monotone function, `D(f) ≤ s(f)²`. -/
theorem complexity_le_sensitivity_sq_of_monotone (hf : Monotone f) :
    complexity f ≤ sensitivity f ^ 2 :=
  (complexity_le_sensitivityFor_mul_sensitivityFor_of_monotone hf).trans (by
    rw [sq]
    exact Nat.mul_le_mul (sensitivityFor_le_sensitivity f _) (sensitivityFor_le_sensitivity f _))

end DecisionTree

end Cslib

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Basic

/-!
# Existential convolution on the Boolean cube

`BitString.orConvolution f g x` asks whether `x = a + b` for accepted inputs `a` of `f` and
`b` of `g`. The group operation is coordinatewise exclusive or, and the aggregation is
existential disjunction. Thus its accepted set is the sumset of the accepted sets of `f` and
`g`. It does not count representations or take their parity.

## Main definitions

* `Cslib.BitString.orConvolution`: existential convolution of Boolean functions.

## Main results

* `Cslib.BitString.orConvolution_eq_true_iff_exists_add`: the sumset characterization.
* `Cslib.BitString.orConvolution_comm`: existential convolution is commutative.
-/

public section

namespace Cslib.BitString

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Existential XOR convolution: some accepted input of `f`, added to some accepted input of
`g`, equals the requested output. -/
@[expose] def orConvolution (f g : (ι → Bool) → Bool) (x : ι → Bool) : Bool :=
  decide (∃ a, f a = true ∧ g (x + a) = true)

/-- The defining existential condition for convolution. -/
@[simp] theorem orConvolution_eq_true (f g : (ι → Bool) → Bool) (x : ι → Bool) :
    orConvolution f g x = true ↔ ∃ a, f a = true ∧ g (x + a) = true :=
  decide_eq_true_iff

/-- Existential convolution accepts exactly the sums of accepted inputs. -/
theorem orConvolution_eq_true_iff_exists_add (f g : (ι → Bool) → Bool) (x : ι → Bool) :
    orConvolution f g x = true ↔ ∃ a b, f a = true ∧ g b = true ∧ a + b = x := by
  rw [orConvolution_eq_true]
  constructor
  · rintro ⟨a, ha, hb⟩
    exact ⟨a, x + a, ha, hb, by rw [add_left_comm, BitString.add_self, add_zero]⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨a, ha, by rwa [add_right_comm, BitString.add_self, zero_add]⟩

/-- Swapping the two input functions preserves existential convolution. -/
theorem orConvolution_comm (f g : (ι → Bool) → Bool) :
    orConvolution f g = orConvolution g f := by
  funext x
  rw [Bool.eq_iff_iff, orConvolution_eq_true_iff_exists_add,
    orConvolution_eq_true_iff_exists_add]
  constructor <;> rintro ⟨a, b, ha, hb, hab⟩
  · exact ⟨b, a, hb, ha, (add_comm b a).trans hab⟩
  · exact ⟨b, a, hb, ha, (add_comm b a).trans hab⟩

/-- An empty accepted set has empty convolution with every Boolean function. -/
@[simp] theorem orConvolution_false_left (g : (ι → Bool) → Bool) :
    orConvolution (fun _ => false) g = fun _ => false := by
  funext x
  simp [orConvolution]

/-- An empty accepted set on the right also has empty convolution. -/
@[simp] theorem orConvolution_false_right (f : (ι → Bool) → Bool) :
    orConvolution f (fun _ => false) = fun _ => false := by
  rw [orConvolution_comm, orConvolution_false_left]

/-- Convolving a point indicator with `g` translates `g`. -/
@[simp] theorem orConvolution_point_left (a : ι → Bool) (g : (ι → Bool) → Bool) :
    orConvolution (fun y => decide (y = a)) g = fun x => g (x + a) := by
  funext x
  rw [Bool.eq_iff_iff, orConvolution_eq_true]
  simp

end Cslib.BitString

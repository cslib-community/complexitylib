/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Metric
public import Complexity.Computability.Circuit.Boolean.Correction

/-!
# The computational Hamming metric

Boolean functions on `n` inputs form a group under the exclusive or, which is the addition of
Mathlib's Boolean ring `Bool`, taken pointwise: `(f + g) x = f x ^^ g x`. The computational
Hamming distance `Cslib.Circuits.Boolean.circuitDist f g` is `0` when `f = g`, and otherwise the De
Morgan circuit complexity of `f + g` plus four, the cost of an exclusive or
(`Cslib.Circuits.Boolean.circuitDist_def`). It is the difference distance of
`Complexity.Computability.Circuit.Metric` for the De Morgan interpretation with `c = 4`, by
definition (`Cslib.Circuits.Boolean.circuitDist_eq_diffDist`), since `f - g = f + g` and `-f = f`.

It is a translation-invariant metric: `f + h = (f + g) + (g + h)` gives the triangle inequality
from `C(f ⊕ h) ≤ C(f ⊕ g) + C(g ⊕ h) + 4`. Circuit complexity is `1`-Lipschitz for it,
`|C(f) - C(g)| ≤ circuitDist f g` (`Cslib.Circuits.Boolean.dist_complexity_single_le_circuitDist`),
which is the correction bound `|C(f) - C(g)| ≤ C(f ⊕ g) + 4` of
`Cslib.Circuits.Boolean.dist_complexity_single_le_complexity_xor` [Jukna2012]. Unlike the
normalized Hamming distance, it does not separate functions that differ on many inputs but in a
simple way: two functions whose exclusive or is a projection are at distance four.

The same quantity is a norm, `0` at `0` and `C(f) + 4` otherwise
(`Cslib.Circuits.Boolean.circuitNorm`), and induces the metric
(`Cslib.Circuits.Boolean.dist_circuitNormedAddCommGroup`). The normed group is a definition, not an
instance, since `BooleanFunction n` is a function type. Apart from the zero function and the
offset, the minimum circuit size problem asks for membership in balls about zero:
`C(f) ≤ s` exactly when `f` lies in the closed ball of radius `s + 4` about `0`
(`Cslib.Circuits.Boolean.complexity_single_le_iff_mem_closedBall`).

## Main definitions

* `Cslib.Circuits.Boolean.circuitDist`: the computational Hamming distance.
* `Cslib.Circuits.Boolean.circuitNorm`: the corresponding norm.
* `Cslib.Circuits.Boolean.circuitNormedAddCommGroup`: the induced normed group, as a definition.

## Main results

* `Cslib.Circuits.Boolean.circuitDist_eq_zero_iff`, `Cslib.Circuits.Boolean.circuitDist_comm`,
  `Cslib.Circuits.Boolean.circuitDist_triangle`: a metric.
* `Cslib.Circuits.Boolean.circuitDist_add_right`, `Cslib.Circuits.Boolean.circuitDist_add_left`:
  translation invariance.
* `Cslib.Circuits.Boolean.dist_complexity_single_le_circuitDist`: complexity is `1`-Lipschitz.
* `Cslib.Circuits.Boolean.complexity_single_le_iff_circuitDist_le`,
  `Cslib.Circuits.Boolean.complexity_single_le_iff_mem_closedBall`: complexity bounds as balls.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

variable {n : ℕ}

/-! ### The group operations as circuits -/

/-- Adding two inputs, an exclusive or, costs four De Morgan gates. -/
theorem complexity_single_add_le :
    complexity interpretation (single fun y : Fin 2 → Bool => y 0 + y 1) ≤ 4 :=
  ((Synthesis.of_mem (s := inputs 2) ⟨0, rfl⟩).xor (Synthesis.of_mem ⟨1, rfl⟩)).complexity_le

/-- Negation is the identity on Boolean functions, so it leaves complexity unchanged. -/
theorem complexity_single_neg (f : BooleanFunction n) :
    complexity interpretation (single (-f)) = complexity interpretation (single f) :=
  rfl

/-! ### The computational Hamming distance -/

/-- The computational Hamming distance: `0` if `f = g`, and otherwise the complexity of `f + g`,
the inputs where `f` and `g` differ, plus four. -/
noncomputable def circuitDist (f g : BooleanFunction n) : ℕ :=
  diffDist interpretation 4 f g

/-- The computational Hamming distance is the difference distance with `c = 4`. -/
theorem circuitDist_eq_diffDist (f g : BooleanFunction n) :
    circuitDist f g = diffDist interpretation 4 f g :=
  rfl

/-- The computational Hamming distance is `0` when `f = g` and `C(f + g) + 4` otherwise. -/
theorem circuitDist_def (f g : BooleanFunction n) :
    circuitDist f g = if f = g then 0 else complexity interpretation (single (f + g)) + 4 := by
  by_cases h : f = g
  · simp [h, circuitDist]
  · rw [circuitDist, diffDist_of_ne h]
    simp only [h, ↓reduceIte]
    rfl

/-- The computational Hamming distance from a Boolean function to itself is zero. -/
@[simp] theorem circuitDist_self (f : BooleanFunction n) : circuitDist f f = 0 :=
  diffDist_self f

/-- Distinct functions are at distance the complexity of their exclusive or plus four. -/
theorem circuitDist_of_ne {f g : BooleanFunction n} (h : f ≠ g) :
    circuitDist f g = complexity interpretation (single fun x => f x ^^ g x) + 4 :=
  diffDist_of_ne h

/-- The computational Hamming distance between `f` and `g` is zero if and only if `f = g`. -/
theorem circuitDist_eq_zero_iff {f g : BooleanFunction n} : circuitDist f g = 0 ↔ f = g :=
  diffDist_eq_zero_iff (by norm_num)

/-- The computational Hamming distance is symmetric. -/
theorem circuitDist_comm (f g : BooleanFunction n) : circuitDist f g = circuitDist g f :=
  diffDist_comm complexity_single_neg f g

/-- **The triangle inequality**, from the cost of an exclusive or. -/
theorem circuitDist_triangle (f g h : BooleanFunction n) :
    circuitDist f h ≤ circuitDist f g + circuitDist g h :=
  diffDist_triangle complexity_single_add_le f g h

/-- The computational Hamming distance is invariant under right translation. -/
@[simp] theorem circuitDist_add_right (f g a : BooleanFunction n) :
    circuitDist (f + a) (g + a) = circuitDist f g :=
  diffDist_add_right f g a

/-- The computational Hamming distance is invariant under left translation. -/
@[simp] theorem circuitDist_add_left (a f g : BooleanFunction n) :
    circuitDist (a + f) (a + g) = circuitDist f g :=
  diffDist_add_left a f g

/-- **Circuit complexity is `1`-Lipschitz** for the computational Hamming distance. -/
theorem dist_complexity_single_le_circuitDist (f g : BooleanFunction n) :
    Nat.dist (complexity interpretation (single f)) (complexity interpretation (single g)) ≤
      circuitDist f g := by
  by_cases h : f = g
  · simp [h]
  rw [circuitDist_of_ne h]
  exact dist_complexity_single_le_complexity_xor f g

/-! ### The norm -/

/-- The computational Hamming norm: `0` at `0`, and otherwise the complexity plus four. -/
noncomputable def circuitNorm (n : ℕ) : AddGroupNorm (BooleanFunction n) :=
  diffNorm interpretation 4 (by norm_num) complexity_single_add_le complexity_single_neg

/-- The computational Hamming norm of `f` is its computational Hamming distance from `0`. -/
theorem circuitNorm_apply (f : BooleanFunction n) :
    circuitNorm n f = ((circuitDist f 0 : ℕ) : ℝ) :=
  diffNorm_apply f

/-- The normed group of Boolean functions with the computational Hamming norm. This is a
definition, not an instance, since `BooleanFunction n` is a function type. -/
noncomputable abbrev circuitNormedAddCommGroup (n : ℕ) : NormedAddCommGroup (BooleanFunction n) :=
  (circuitNorm n).toNormedAddCommGroup

/-- The normed group induces the computational Hamming distance. -/
theorem dist_circuitNormedAddCommGroup (f g : BooleanFunction n) :
    letI := circuitNormedAddCommGroup n
    dist f g = circuitDist f g :=
  dist_diffNorm _ complexity_single_add_le complexity_single_neg f g

/-! ### Complexity bounds as balls -/

/-- For `f ≠ 0`, the minimum circuit size problem is membership in a ball about `0`. -/
theorem complexity_single_le_iff_circuitDist_le {f : BooleanFunction n} (hf : f ≠ 0) (s : ℕ) :
    complexity interpretation (single f) ≤ s ↔ circuitDist f 0 ≤ s + 4 := by
  rw [circuitDist_eq_diffDist, diffDist_of_ne hf, sub_zero]
  omega

/-- For `f ≠ 0`, the minimum circuit size problem is membership in the closed ball of radius
`s + 4` about `0` for the computational Hamming norm. -/
theorem complexity_single_le_iff_mem_closedBall {f : BooleanFunction n} (hf : f ≠ 0) (s : ℕ) :
    letI := circuitNormedAddCommGroup n
    complexity interpretation (single f) ≤ s ↔ f ∈ Metric.closedBall 0 ((s : ℝ) + 4) := by
  let _ := circuitNormedAddCommGroup n
  rw [Metric.mem_closedBall, dist_circuitNormedAddCommGroup,
    complexity_single_le_iff_circuitDist_le hf]
  exact_mod_cast Iff.rfl

end Cslib.Circuits.Boolean

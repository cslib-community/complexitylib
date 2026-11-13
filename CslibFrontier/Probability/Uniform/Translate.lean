/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Uniform
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Subtracting a fixed mask from a uniform draw

On a finite group, `x ↦ x - c` and `x ↦ c - x` are bijections, so they leave a uniform draw
uniform, and an experiment that reads its uniform draw through either one is unchanged. These are
the subtraction forms of the one-time-pad lemmas `uniformOfFintype_map_add_right`,
`uniformOfFintype_map_add_left`, `uniformOfFintype_bind_add_right` and
`uniformOfFintype_bind_add_left` in `CslibFrontier.Probability.Uniform`, which this module
re-exports. They are kept in this leaf module because that file has many importers.

## Main results

* `Cslib.Probability.PMF.uniformOfFintype_map_sub_right`,
  `Cslib.Probability.PMF.uniformOfFintype_map_sub_left`: subtracting a fixed mask leaves a uniform
  group element uniform.
* `Cslib.Probability.PMF.uniformOfFintype_bind_sub_right`,
  `Cslib.Probability.PMF.uniformOfFintype_bind_sub_left`: an experiment that reads its uniform
  draw as `x - c` or `c - x` is unchanged.
-/

public section

namespace Cslib.Probability.PMF

variable {G : Type*} [AddGroup G] [Fintype G]

/-- Subtracting a fixed mask from a uniform element of a finite group leaves it uniform. -/
theorem uniformOfFintype_map_sub_right (c : G) :
    (PMF.uniformOfFintype G).map (· - c) = PMF.uniformOfFintype G :=
  uniformOfFintype_map_equiv (Equiv.subRight c)

/-- Subtracting a uniform element of a finite group from a fixed value, `x ↦ c - x`, leaves it
uniform. -/
theorem uniformOfFintype_map_sub_left (c : G) :
    (PMF.uniformOfFintype G).map (c - ·) = PMF.uniformOfFintype G :=
  uniformOfFintype_map_equiv (Equiv.subLeft c)

/-- Unmasking a uniform draw on the right does not change an experiment that consumes it. -/
theorem uniformOfFintype_bind_sub_right {β : Type*} (c : G) (f : G → PMF β) :
    (PMF.uniformOfFintype G).bind (fun x => f (x - c)) = (PMF.uniformOfFintype G).bind f := by
  conv_rhs => rw [← uniformOfFintype_map_sub_right c, PMF.bind_map]
  rfl

/-- Reading a uniform draw as `c - x` does not change an experiment that consumes it. -/
theorem uniformOfFintype_bind_sub_left {β : Type*} (c : G) (f : G → PMF β) :
    (PMF.uniformOfFintype G).bind (fun x => f (c - x)) = (PMF.uniformOfFintype G).bind f := by
  conv_rhs => rw [← uniformOfFintype_map_sub_left c, PMF.bind_map]
  rfl

end Cslib.Probability.PMF

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.OneWay
public import Complexity.Probability.Collision
import Complexity.Tactic.PPT

/-!
# Output collisions of one-way functions

Independently guessing an `n`-bit preimage inverts `f` exactly when two independent images collide.
The guesser is a uniform strict PPT program, so any OWF has negligible output collision
probability. No injectivity, regularity or length-preservation assumption is used.
This necessary entropy condition alone does not supply the surplus needed by a PRG.

## Main results

* `Cslib.Crypto.output_collision_eq_inversion`: the independent-guess experiment.
* `Cslib.Crypto.OneWay.output_collision_negligible`: negligible output collisions.

## References

The general OWF-to-PRG development follows [T. Holenstein, *Pseudorandom Generators from One-Way
Functions: A Simple Construction for Any Hardness*][Holenstein2006], Sections 4–5. This elementary
guessing argument is separate from its stronger pseudoentropy-pair construction.

Adapted from Crypto/Computational/OneWay/Collision.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the shared nonnegative game API.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Probability.PMF

/-- A fresh independent preimage guess succeeds exactly with the output collision probability. -/
theorem output_collision_eq_inversion (f : List Bool → List Bool) (n : ℕ) :
    collisionProbability ((BitString.uniformList n).map f) =
      (Game.succProbability (ProbComp.eval
        (inversionGame f (fun n _ => BitString.sampleList n) n)) : ℝ) := by
  simp only [collisionProbability_eq_probability, Game.succProbability,
    ENNReal.coe_toNNReal_eq_toReal, inversionGame, ProbComp.eval_bind, BitString.eval_sampleList,
    ProbComp.eval_pure, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def,
    beq_eq_decide, eq_comm]

/-- One-wayness forces negligible output collisions, even for variable-length images.
`Real.toNNReal` is exact here because collision probability is nonnegative. -/
theorem OneWay.output_collision_negligible {f : List Bool → List Bool} (hf : OneWay f) :
    Negligible (fun n =>
      Real.toNNReal (collisionProbability ((BitString.uniformList n).map f))) := by
  simpa only [output_collision_eq_inversion, Real.toNNReal_coe] using
    hf.inversion_negligible (fun n _ => BitString.sampleList n) (by ppt)

end Cslib.Crypto

/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Paillier.Algebra
public import CslibFrontier.Crypto.Game.Experiment
import CslibFrontier.Probability.Uniform

/-!
# The decisional composite residuosity experiments at a fixed modulus

Fix a positive modulus `N`. The decisional composite residuosity (DCR) problem
([KatzLindell2020], Definition 15.10) asks to tell a uniform `N`-th residue modulo `N ^ 2` from a
uniform unit modulo `N ^ 2`. This module states its two worlds at one modulus. The distinguisher
receives the challenge as a unit of `ZMod (N ^ 2)`; there are no encodings, security parameter or
setup. Each world is an `Experiment`, read as the challenger's steps.

The asymptotic assumption `DCR`, over a law on balanced moduli and strict-PPT distinguishers on
encoded inputs, is in `CslibFrontier/Crypto/Computational/CompositeResiduosity.lean`. Its games
`dcrRealGame` and `dcrRandomGame` draw a modulus and run these experiments.

## Main definitions

* `Cslib.Crypto.dcrRealExperiment`, `Cslib.Crypto.dcrRandomExperiment`,
  `Cslib.Crypto.dcrAdvantage`: the two worlds of the DCR problem at modulus `N` and their
  distinguishing advantage.

## Main results

* `Cslib.Crypto.eval_dcrRealExperiment`: the uniform `N`-th residue is `powSelfHom N r`, the
  `N`-th power of a uniform unit `r` modulo `N`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Chapter 15,
  Definition 15.10.
-/

public section

namespace Cslib.Crypto

open Probability Paillier
open scoped NNReal

variable (N : ℕ) [NeZero N]

/-- The real world of the decisional composite residuosity experiment ([KatzLindell2020],
Definition 15.10) at modulus `N`: the challenger draws a uniform unit `s` modulo `N ^ 2` and gives
the distinguisher the `N`-th residue `s ^ N`. -/
@[expose] noncomputable def dcrRealExperiment (D : (ZMod (N ^ 2))ˣ → Experiment) : Experiment := do
  let s ← ProbComp.uniform (ZMod (N ^ 2))ˣ
  D (s ^ N)

/-- The random world of the decisional composite residuosity experiment ([KatzLindell2020],
Definition 15.10) at modulus `N`: the challenger gives the distinguisher a uniform unit modulo
`N ^ 2`. -/
@[expose] noncomputable def dcrRandomExperiment (D : (ZMod (N ^ 2))ˣ → Experiment) :
    Experiment := do
  let y ← ProbComp.uniform (ZMod (N ^ 2))ˣ
  D y

/-- The DCR advantage of `D` at modulus `N`: its distinguishing advantage between
`dcrRealExperiment` and `dcrRandomExperiment`. -/
@[expose] noncomputable def dcrAdvantage (D : (ZMod (N ^ 2))ˣ → Experiment) : ℝ≥0 :=
  Experiment.advantage (dcrRealExperiment N D) (dcrRandomExperiment N D)

/-- In the real world the challenge is `powSelfHom N r`, the `N`-th power of a uniform unit `r`
modulo `N`. An `N`-th power modulo `N ^ 2` depends only on its base modulo `N`, and reduction
modulo `N` sends the uniform unit modulo `N ^ 2` to the uniform unit modulo `N`. -/
theorem eval_dcrRealExperiment (D : (ZMod (N ^ 2))ˣ → Experiment) :
    ProbComp.eval (dcrRealExperiment N D) =
      (PMF.uniformOfFintype (ZMod N)ˣ).bind fun r => ProbComp.eval (D (powSelfHom N r)) := by
  rw [← Probability.PMF.uniformOfFintype_map_monoidHom
    (ZMod.unitsMap (dvd_pow_self N two_ne_zero)) (ZMod.unitsMap_surjective _), PMF.bind_map]
  simp only [dcrRealExperiment, ProbComp.eval_bind, ProbComp.eval_uniform, Function.comp_def,
    powSelfHom_unitsMap]

end Cslib.Crypto

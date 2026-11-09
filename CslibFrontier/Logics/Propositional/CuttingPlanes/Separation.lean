/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
public import CslibFrontier.Logics.Propositional.CuttingPlanes.Pigeonhole
public import CslibFrontier.Logics.Propositional.Resolution.Pigeonhole
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Cutting planes are exponentially stronger than resolution

The pigeonhole formulas `PHP^{n+1}_n` (`Cslib.Logic.PL.CNF.pigeonhole (n + 1) n`) separate cutting
planes from resolution [Cook, Coullard and Turán][CookCoullardTuran1987] [Jukna, Section
19.2][Jukna2012]:

* cutting planes refute their inequalities in at most `(n + 1) (n + 2)²` lines
  (`Cslib.Logic.PL.CuttingPlanes.refutableInSize_pigeonhole_succ`);
* every resolution refutation has at least `2 ^ (n / 24)` lines ([Haken][Haken1985];
  `Cslib.Logic.PL.CNF.two_pow_le_of_refutableInSize_pigeonhole`).

Hence any translation of cutting planes refutations of `PHP^{n+1}_n` with `s` lines into resolution
refutations with `f s` lines needs `2 ^ (n / 24) ≤ f ((n + 1) (n + 2)²)`
(`Cslib.Logic.PL.CuttingPlanes.two_pow_le_of_forall_refutableInSize_pigeonhole`), so `f` grows like
`2 ^ Ω(s^{1/3})` along these sizes and is not polynomially bounded
(`Cslib.Logic.PL.CuttingPlanes.not_exists_polynomiallyBounded_refutableInSize_pigeonhole`).
Conversely, cutting planes simulate resolution with a polynomial overhead in the number of lines
(`Cslib.Logic.PL.CNF.RefutableInSize.cuttingPlanes`).

Sizes count lines on both sides. The numbers in the cutting planes refutations have absolute value
at most `2 (n + 1)`, so their bit size is also polynomial in `n`, but this file does not measure
it.

## Main results

* `Cslib.Logic.PL.CuttingPlanes.two_pow_le_of_forall_refutableInSize_pigeonhole`: the quantitative
  separation on `PHP^{n+1}_n`.
* `Cslib.Logic.PL.CuttingPlanes.not_exists_polynomiallyBounded_refutableInSize_pigeonhole`:
  resolution does not polynomially simulate cutting planes, by number of lines.

## References

* [W. Cook, C. R. Coullard, Gy. Turán, *On the complexity of cutting-plane
  proofs*][CookCoullardTuran1987]
* [A. Haken, *The intractability of resolution*][Haken1985]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Section 19.2][Jukna2012]
-/

public section

namespace Cslib.Logic.PL.CuttingPlanes

open CNF

/-- **Exponential separation of cutting planes from resolution on `PHP^{n+1}_n`**
[Cook, Coullard and Turán][CookCoullardTuran1987] [Haken][Haken1985]: if every cutting planes
refutation of `PHP^{n+1}_n` with `s` lines yields a resolution refutation with `f s` lines, then
`2 ^ (n / 24) ≤ f ((n + 1) (n + 2)²)`. -/
theorem two_pow_le_of_forall_refutableInSize_pigeonhole {f : ℕ → ℕ} {n : ℕ}
    (hf : ∀ s, RefutableInSize (pigeonhole (n + 1) n).toIneqs s →
      (pigeonhole (n + 1) n).RefutableInSize (f s)) :
    2 ^ (n / 24) ≤ f ((n + 1) * (n + 2) ^ 2) :=
  two_pow_le_of_refutableInSize_pigeonhole (hf _ (refutableInSize_pigeonhole_succ n))

/-- **Resolution does not polynomially simulate cutting planes** [Cook, Coullard and
Turán][CookCoullardTuran1987] [Haken][Haken1985]: no polynomially bounded `f` turns every cutting
planes refutation of `PHP^{n+1}_n` with `s` lines, for every `n`, into a resolution refutation with
`f s` lines. -/
theorem not_exists_polynomiallyBounded_refutableInSize_pigeonhole :
    ¬ ∃ f : ℕ → ℕ, PolynomiallyBounded f ∧ ∀ n s,
      RefutableInSize (pigeonhole (n + 1) n).toIneqs s →
        (pigeonhole (n + 1) n).RefutableInSize (f s) := by
  rintro ⟨f, hf, hsim⟩
  have hg : PolynomiallyBounded fun k => f ((24 * k + 1) * (24 * k + 2) ^ 2) :=
    hf.comp (by fun_prop)
  obtain ⟨k, hk⟩ := hg.eventually_lt_two_pow.exists
  have := two_pow_le_of_forall_refutableInSize_pigeonhole (hsim (24 * k))
  rw [show 24 * k / 24 = k by omega] at this
  exact absurd hk (not_lt.2 this)

end Cslib.Logic.PL.CuttingPlanes

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GGM.Reduction
public import Complexity.Crypto.Computational.PseudorandomGenerator
import Complexity.Crypto.Computational.Stretch
import Complexity.Tactic.PPT

/-!
# Adaptive GGM security from pseudorandom generators

The tree evaluator is a pseudorandom function whenever its two-child expansion is efficient and
pseudorandom. Each strict oracle-PPT adversary has one polynomial query budget. The single uniform
reduction loses the product of the level-selection and sample-selection ranges, which is
polynomial in the security parameter. The bound may depend on the fixed adversary.

Surplus generator bits are truncated to two labels. This preserves both security and tree
evaluation, accommodating the strict PRG convention at seed length zero.

## Main results

* `Cslib.Crypto.GGM.pseudorandomFunction_of_indistinguishable`: adaptive GGM security for efficient
  pseudorandom two-child expansions.
* `Cslib.Crypto.PseudorandomGenerator.ggm`: a generator supplying at least two labels gives a PRF.
* `Cslib.Crypto.PseudorandomGenerator.exists_pseudorandomFunction`: every uniform PRG gives a
  uniform PRF, using the existing polynomial-stretch construction.

## References

* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986],
  Sections 3.2–3.3, construction and Theorem 3.

Adapted from Crypto/Computational/GGM/Security.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the shared typed oracle and game calculus.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- The GGM tree of an efficient pseudorandom two-child expansion is secure against every
uniform strict polynomial-time adaptive oracle adversary with independent private randomness. -/
theorem GGM.pseudorandomFunction_of_indistinguishable {generator : List Bool → List Bool}
    (hgenerator : ComputableInPolyTime generator encBits encBits)
    (hlength : ∀ seed, (generator seed).length = 2 * seed.length)
    (hsecure : ComputationallyIndistinguishable (generatorEnsemble generator)
      (fun n => BitString.uniformList (2 * n))) : PseudorandomFunction (GGM.eval generator) := by
  have hgenerator := hgenerator.tidy
  refine ⟨(Crypto.GGM.computableInPolyTime_eval (.of_tidy hgenerator)), fun key query _ =>
    length_eval (fun seed => by rw [hlength]) key query, ?_⟩
  intro adversary hadversary
  obtain ⟨c, d, hqueries⟩ := hadversary.query_bounds
  let count := fun n => c * (n + 2) ^ d
  have hcount : ComputableTidilyInPolyTime count encUnary encUnary := by
    unfold count
    polytime
  have hreduce := hsecure (reduction generator adversary count)
    (isPPT_reduction (.of_tidy hgenerator) hadversary (.of_tidy hcount))
  have hloss : PolynomiallyBounded (fun n => dyadicSize n * dyadicSize (count n)) := by
    have := hcount.polynomiallyBounded
    fun_prop
  apply negligible_of_le (hreduce.polynomiallyBounded_mul hloss)
  intro n
  have hquery : (adversary n []).IsQueryBounded (count n) := by
    simpa [count] using (hqueries n []).1
  have h := reduction_advantage generator adversary count n hquery
  simpa only [distinguishingGame, PMF.monad_bind_eq_bind, ProbComp.eval_bind, ProbComp.eval_map,
    BitString.eval_sampleList,
    generatorEnsemble, Nat.cast_mul] using h.le

/-- A secure generator providing at least two full labels gives the GGM pseudorandom function.
Surplus bits are ignored; the hypothesis accommodates seed length zero. -/
theorem PseudorandomGenerator.ggm {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hgenerator : PseudorandomGenerator generator length) (hdouble : ∀ n, 2 * n ≤ length n) :
    PseudorandomFunction (GGM.eval generator) := by
  have hpoly := hgenerator.polyTime.tidy
  have hsecure := hgenerator.indistinguishable.map
    (f := fun n word => word.take (2 * n)) (by polytime)
  have htruncated : ComputationallyIndistinguishable
      (generatorEnsemble (fun seed => (generator seed).take (2 * seed.length)))
      (fun n => BitString.uniformList (2 * n)) := by
    simpa only [← generatorEnsemble_postprocess generator (fun n word => word.take (2 * n)),
      BitString.uniformList_take (hdouble _)] using hsecure
  have h := GGM.pseudorandomFunction_of_indistinguishable
    (generator := fun seed => (generator seed).take (2 * seed.length)) (.of_tidy (by polytime))
    (fun seed => by simp [hgenerator.length_eq, Nat.min_eq_left (hdouble _)]) htruncated
  simpa only [GGM.eval_truncate] using h

/-- Every uniform pseudorandom generator yields a uniform adaptive pseudorandom function.
Truncate to one extra bit, amplify to two labels plus one bit, and apply GGM. -/
theorem PseudorandomGenerator.exists_pseudorandomFunction {generator : List Bool → List Bool}
    {length : ℕ → ℕ} (hgenerator : PseudorandomGenerator generator length) :
    ∃ family : List Bool → List Bool → List Bool, PseudorandomFunction family := by
  have hone := hgenerator.truncate (fun n => n + 1) (by polytime)
    (fun n => hgenerator.stretch n) (by intro n; lia)
  have htwo := hone.amplify (fun n => 2 * n + 1) (by polytime) (by intro n; lia)
  exact ⟨_, htwo.ggm (by intro n; lia)⟩

end Cslib.Crypto

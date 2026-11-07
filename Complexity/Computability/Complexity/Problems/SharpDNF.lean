/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.FPRAS
public import Complexity.Computability.Complexity.Problems.SharpDNF.KarpLubyMadras
public import Complexity.Computability.Complexity.Problems.SharpDNF.KarpLubyMadras.PolyTime

/-!
# Counting satisfying assignments of a DNF formula: #DNF

`SharpDNF φ` is the number of satisfying assignments of a formula `φ` in disjunctive normal form
over variables numbered by `ℕ`: the assignments of the variables occurring in `φ` that satisfy it
(`Cslib.Logic.PL.DNF.modelCount`). Deciding whether a formula in disjunctive normal form is
satisfiable is easy, but counting its satisfying assignments exactly is `#P`-complete
[Valiant][Valiant1979]. It nevertheless has a fully polynomial randomized approximation scheme,
the estimator of Karp, Luby and Madras [Karp, Luby and Madras][KarpLubyMadras1989],
[Mitzenmacher and Upfal, Section 11.2][MitzenmacherUpfal2017]
(`Cslib.Complexity.SharpDNF.mem_FPRAS`).

## Main definitions

* `Cslib.Complexity.SharpDNF`: the number of satisfying assignments.

## Main results

* `Cslib.Complexity.KarpLubyMadras.isFPRAS`: the Karp–Luby–Madras estimator is a fully polynomial
  randomized approximation scheme for `#DNF`.
* `Cslib.Complexity.SharpDNF.mem_FPRAS`: `#DNF` has a fully polynomial randomized approximation
  scheme.
* `Cslib.Complexity.KarpLubyMadras.approx_estimate`: the guarantee for real relative error and
  failure probability.

## References

* [R. M. Karp, M. Luby, N. Madras, *Monte-Carlo approximation algorithms for enumeration
  problems*][KarpLubyMadras1989]
* [M. Mitzenmacher, E. Upfal, *Probability and Computing*, Section 11.2][MitzenmacherUpfal2017]
* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL

/-- **#DNF**: the number of satisfying assignments of a formula in disjunctive normal form over
variables numbered by `ℕ`, counting assignments of the variables occurring in the formula. -/
def SharpDNF (φ : DNF ℕ) : ℕ := φ.modelCount

namespace KarpLubyMadras

/-- **The Karp–Luby–Madras estimator is an FPRAS for #DNF** [Karp, Luby and
Madras][KarpLubyMadras1989]: on a formula with `m` terms, it runs `dyadicSize m * 3 (t + 1) p ^ 2`
trials and its estimate is within relative error `1 / p` of the number of models with probability
at least `1 - (1 / 2) ^ t`. -/
theorem isFPRAS : IsFPRAS encDNF SharpDNF estimate :=
  ⟨isPPTOn_estimate, fun φ _ _ hp => approxWithin_estimate φ hp _⟩

/-- **The guarantee for real parameters**: run with `p = ⌈1 / ε⌉` and `t = ⌈log₂ ⌈1 / δ⌉⌉`, the
Karp–Luby–Madras estimator is within relative error `ε` of the number of models with probability
at least `1 - δ`. -/
theorem approx_estimate (φ : DNF ℕ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    1 - δ ≤ ((ProbComp.eval (estimate φ ⌈ε⁻¹⌉₊ (Nat.clog 2 ⌈δ⁻¹⌉₊))).toOuterMeasure
      {out | 0 < out.2 ∧ |(out.1 : ℝ) / out.2 - DNF.modelCount φ| ≤
        ε * DNF.modelCount φ}).toReal :=
  isFPRAS.approx φ hε hδ

end KarpLubyMadras

namespace SharpDNF

/-- **#DNF has a fully polynomial randomized approximation scheme** [Karp, Luby and
Madras][KarpLubyMadras1989]. -/
theorem mem_FPRAS : SharpDNF ∈ FPRAS encDNF :=
  ⟨_, KarpLubyMadras.isFPRAS⟩

end SharpDNF

end Cslib.Complexity

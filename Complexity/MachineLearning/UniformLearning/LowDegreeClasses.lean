/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Noise
public import Complexity.MachineLearning.UniformLearning.LowDegree
import Complexity.Foundations.BooleanAnalysis.Concentration
import Complexity.Foundations.BooleanAnalysis.Monotone
import Mathlib.Tactic.Linarith

/-!
# Classes learned by the low-degree algorithm

The low-degree algorithm of degree `t` learns every class whose Fourier weight above degree `t`
is at most `ε / 2` (`UniformLearning.lowDegreeLearner_learns`). Bounding that weight by the total
influence or the noise sensitivity [O'Donnell, Propositions 3.2 and 3.3][ODonnell2014] gives three
natural classes it learns [O'Donnell, Section 3.4][ODonnell2014]:

* the Boolean functions of total influence at most `K`, with `ε (t + 1) ≥ 2 K`
  (`UniformLearning.lowDegreeLearner_learns_totalInfluence_le`), so in
  `(n + 1) ^ O(K / ε) · poly(1 / ε, log (1 / δ))` examples
  [O'Donnell, Corollary 3.32][ODonnell2014];
* the monotone Boolean functions, whose total influence is at most `√n`, with
  `ε (t + 1) ≥ 2 √n` (`UniformLearning.lowDegreeLearner_learns_monotone`), so in
  `(n + 1) ^ O(√n / ε) · poly(1 / ε, log (1 / δ))` examples
  [O'Donnell, Corollary 3.33][ODonnell2014];
* the Boolean functions of noise sensitivity at most `ε / 6` at a rate `η ≤ 1 / 2`, with
  `η (t + 1) ≥ 1` (`UniformLearning.lowDegreeLearner_learns_noiseSensitivity_le`), so in
  `(n + 1) ^ O(1 / η) · poly(1 / ε, log (1 / δ))` examples
  [O'Donnell, Corollary 3.34][ODonnell2014].

In each case the exact number of examples is the low-degree algorithm's `(4 N / ε) log (2 N / δ)`,
for `N ≤ (n + 1) ^ t` the number of sets of at most `t` coordinates; the shorthand above keeps its
dependence on the accuracy `ε` and the confidence `δ`. As there, only the number of
examples is bounded; the running time is not certified by a machine model.

## Main results

* `Cslib.MachineLearning.UniformLearning.lowDegreeLearner_learns_totalInfluence_le`
* `Cslib.MachineLearning.UniformLearning.lowDegreeLearner_learns_monotone`
* `Cslib.MachineLearning.UniformLearning.lowDegreeLearner_learns_noiseSensitivity_le`

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.MachineLearning.UniformLearning

open BitString Finset PACLearning

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Learning functions of small total influence**: with `ε (t + 1) ≥ 2 K`, the low-degree
algorithm of degree `t` from `m ≥ (4 N / ε) log (2 N / δ)` uniform random examples learns the
Boolean functions whose total influence, read as signs, is at most `K`, with error `ε` and
confidence `1 - δ` [O'Donnell, Corollary 3.32][ODonnell2014]. The book states the running time;
only the number of examples is bounded here. -/
theorem lowDegreeLearner_learns_totalInfluence_le {K ε δ : ℝ} {t m : ℕ} (hε : 0 < ε) (hδ : 0 < δ)
    (ht : 2 * K ≤ ε * (t + 1))
    (hm : 4 * #{S : Finset ι | #S ≤ t} / ε * Real.log (2 * #{S : Finset ι | #S ≤ t} / δ) ≤ m) :
    Learns (lowDegreeLearner ι t m) {f | totalInfluence (fun x => signVal (f x)) ≤ K} ε δ :=
  lowDegreeLearner_learns hε hδ hm fun _ hf =>
    sum_fourierCoeff_sq_le_of_totalInfluence_le hf (by linarith)

/-- **Learning monotone functions**: with `ε (t + 1) ≥ 2 √n`, the low-degree algorithm of degree `t`
from `m ≥ (4 N / ε) log (2 N / δ)` uniform random examples learns the monotone Boolean functions
of `n` coordinates, with error `ε` and confidence `1 - δ`
[O'Donnell, Corollary 3.33][ODonnell2014]. Only the number of examples is bounded. -/
theorem lowDegreeLearner_learns_monotone {ε δ : ℝ} {t m : ℕ} (hε : 0 < ε) (hδ : 0 < δ)
    (ht : 2 * √(Fintype.card ι) ≤ ε * (t + 1))
    (hm : 4 * #{S : Finset ι | #S ≤ t} / ε * Real.log (2 * #{S : Finset ι | #S ≤ t} / δ) ≤ m) :
    Learns (lowDegreeLearner ι t m) {f | Monotone f} ε δ :=
  (lowDegreeLearner_learns_totalInfluence_le hε hδ ht hm).mono
    (fun _ hf => totalInfluence_le_sqrt_card_of_monotone hf) le_rfl le_rfl

/-- **Learning noise-stable functions**: for a noise rate `η ≤ 1 / 2` with `η (t + 1) ≥ 1`, the
low-degree algorithm of degree `t` from `m ≥ (4 N / ε) log (2 N / δ)` uniform random examples
learns the Boolean functions of noise sensitivity at most `ε / 6` at rate `η`, with error `ε` and
confidence `1 - δ` [O'Donnell, Corollary 3.34][ODonnell2014]. Only the number of examples is
bounded. -/
theorem lowDegreeLearner_learns_noiseSensitivity_le {η ε δ : ℝ} {t m : ℕ} (hε : 0 < ε)
    (hδ : 0 < δ) (hη : η ≤ 1 / 2) (ht : 1 ≤ η * (t + 1))
    (hm : 4 * #{S : Finset ι | #S ≤ t} / ε * Real.log (2 * #{S : Finset ι | #S ≤ t} / δ) ≤ m) :
    Learns (lowDegreeLearner ι t m) {f | noiseSensitivity η f ≤ ε / 6} ε δ :=
  lowDegreeLearner_learns hε hδ hm fun f (hf : noiseSensitivity η f ≤ ε / 6) =>
    (sum_fourierCoeff_sq_le_three_mul_noiseSensitivity hη ht f).trans (by linarith)

end Cslib.MachineLearning.UniformLearning

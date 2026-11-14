/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.Realizable
public import CslibFrontier.MachineLearning.PACLearning.UniformConvergenceProperty
public import Cslib.MachineLearning.PACLearning.VCDimension
import CslibFrontier.MachineLearning.PACLearning.AgnosticVC
import CslibFrontier.MachineLearning.PACLearning.VCLowerBound
import CslibFrontier.MachineLearning.PACLearning.VCUpperBound
import Mathlib.Tactic.TFAE

/-!
# The fundamental theorem of PAC learning on countable domains

The fundamental theorem of statistical learning [ShalevShwartzBenDavid2014, Theorem 6.7] says
that for a binary class `C` the following are equivalent:

1. `C` has the uniform convergence property;
2. every ERM learns `C` agnostically;
3. `C` is agnostically PAC learnable;
4. `C` is PAC learnable in the realizable setting;
5. every ERM learns `C` in the realizable setting;
6. `C` has finite VC dimension.

`tfae_hasFiniteVCDim` proves this on countable domains with measurable singletons. Statement 1 is
`HasUniformConvergence C Set.univ`; statements 2 and 5 are `IsERMLearnable` and statements 3 and 4
are `IsPACLearnable`, over all distributions and over the distributions `C` realizes. Agnostic PAC
learnability implies finite VC dimension on every domain with measurable singletons.

The proof follows the source's cycle: uniform convergence makes every ERM `ε`-optimal
(`HasUniformConvergence.isERMLearnable`), the agnostic statements imply the realizable ones, and
the growth-function bound turns finite VC dimension into uniform convergence
(`hasUniformConvergence_univ_of_hasFiniteVCDim`). For realizable learnability ⇒ finite VC
dimension, the Ehrenfeucht–Haussler–Kearns–Valiant lower bound (`IsPACLearnable.hasFiniteVCDim`)
replaces the source's No-Free-Lunch argument. The separate realizable equivalences use the ε-net
upper bound (`isPACLearnable_realizableDistributions_of_hasFiniteVCDim`), and the randomized
equivalences follow because deterministic learners are randomized ones.

Not formalized here: the quantitative two-sided sample-complexity bounds of
[ShalevShwartzBenDavid2014, Theorem 6.8], and the upper bounds on uncountable domains, which need a
measurability hypothesis on the class.

## Main results

- `tfae_hasFiniteVCDim`: the six statements of [ShalevShwartzBenDavid2014, Theorem 6.7] are
  equivalent on a countable domain with measurable singletons.
- `isPACLearnable_univ_iff_hasFiniteVCDim`, `isRPACLearnable_univ_iff_hasFiniteVCDim`: a binary
  class on such a domain is agnostically PAC learnable, by deterministic or by randomized learners,
  iff it has finite VC dimension.
- `isPACLearnable_realizableDistributions_iff_hasFiniteVCDim`,
  `isRPACLearnable_realizableDistributions_iff_hasFiniteVCDim`: the same over the distributions the
  class realizes.
- `IsPACLearnable.hasFiniteVCDim_of_univ`: an agnostically PAC learnable binary class on a domain
  with measurable singletons has finite VC dimension.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory

namespace Cslib.MachineLearning.PACLearning

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **Agnostic learnability implies finite VC dimension** on every domain with measurable
singletons. -/
theorem IsPACLearnable.hasFiniteVCDim_of_univ {C : ConceptClass α Bool}
    (h : IsPACLearnable C Set.univ) : HasFiniteVCDim C :=
  h.hasFiniteVCDim (Set.subset_univ _)

variable [Countable α]

/-- **The fundamental theorem of PAC learning, realizable case** [ShalevShwartzBenDavid2014,
Theorem 6.7]: on a countable domain with measurable singletons, a binary class is PAC learnable
over the distributions it realizes iff it has finite VC dimension. -/
theorem isPACLearnable_realizableDistributions_iff_hasFiniteVCDim {C : ConceptClass α Bool} :
    IsPACLearnable C (realizableDistributions C) ↔ HasFiniteVCDim C :=
  ⟨fun h => h.hasFiniteVCDim subset_rfl, isPACLearnable_realizableDistributions_of_hasFiniteVCDim⟩

/-- **The fundamental theorem of PAC learning, realizable case, for randomized learners**: on a
countable domain with measurable singletons, a binary class is randomized PAC learnable over the
distributions it realizes iff it has finite VC dimension. -/
theorem isRPACLearnable_realizableDistributions_iff_hasFiniteVCDim {C : ConceptClass α Bool} :
    IsRPACLearnable C (realizableDistributions C) ↔ HasFiniteVCDim C :=
  ⟨fun h => h.hasFiniteVCDim subset_rfl,
    fun h => (isPACLearnable_realizableDistributions_of_hasFiniteVCDim h).toIsRPACLearnable⟩

/-- **The fundamental theorem of statistical learning** [ShalevShwartzBenDavid2014, Theorem 6.7]:
on a countable domain with measurable singletons, a binary class has the uniform convergence
property iff every ERM learns it agnostically, iff it is agnostically PAC learnable, iff it is PAC
learnable in the realizable setting, iff every ERM learns it in the realizable setting, iff it has
finite VC dimension. -/
theorem tfae_hasFiniteVCDim {C : ConceptClass α Bool} :
    List.TFAE
      [HasUniformConvergence C Set.univ,
       IsERMLearnable C Set.univ,
       IsPACLearnable C Set.univ,
       IsPACLearnable C (realizableDistributions C),
       IsERMLearnable C (realizableDistributions C),
       HasFiniteVCDim C] := by
  tfae_have 1 → 2 := HasUniformConvergence.isERMLearnable
  tfae_have 2 → 3 := IsERMLearnable.isPACLearnable
  tfae_have 3 → 4 := IsPACLearnable.antitone_family (Set.subset_univ _)
  tfae_have 2 → 5 := IsERMLearnable.antitone_family (Set.subset_univ _)
  tfae_have 5 → 4 := IsERMLearnable.isPACLearnable
  tfae_have 4 → 6 := fun h => h.hasFiniteVCDim subset_rfl
  tfae_have 6 → 1 := hasUniformConvergence_univ_of_hasFiniteVCDim
  tfae_finish

/-- **The fundamental theorem of PAC learning, agnostic case**: on a countable domain with
measurable singletons, a binary class is agnostically PAC learnable iff it has finite VC
dimension. -/
theorem isPACLearnable_univ_iff_hasFiniteVCDim {C : ConceptClass α Bool} :
    IsPACLearnable C Set.univ ↔ HasFiniteVCDim C :=
  ⟨IsPACLearnable.hasFiniteVCDim_of_univ, isPACLearnable_univ_of_hasFiniteVCDim⟩

/-- **The fundamental theorem of PAC learning, agnostic case, for randomized learners**: on a
countable domain with measurable singletons, a binary class is agnostically randomized PAC
learnable iff it has finite VC dimension. -/
theorem isRPACLearnable_univ_iff_hasFiniteVCDim {C : ConceptClass α Bool} :
    IsRPACLearnable C Set.univ ↔ HasFiniteVCDim C :=
  ⟨fun h => h.hasFiniteVCDim (Set.subset_univ _),
    fun h => (isPACLearnable_univ_of_hasFiniteVCDim h).toIsRPACLearnable⟩

end Cslib.MachineLearning.PACLearning

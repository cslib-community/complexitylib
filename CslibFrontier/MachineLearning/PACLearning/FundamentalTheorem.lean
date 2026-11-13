/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.Realizable
public import Cslib.MachineLearning.PACLearning.VCDimension
import CslibFrontier.MachineLearning.PACLearning.VCLowerBound
import CslibFrontier.MachineLearning.PACLearning.VCUpperBound

/-!
# The fundamental theorem of PAC learning: the realizable characterization

The fundamental theorem of statistical learning [ShalevShwartzBenDavid2014, Theorem 6.7] says
that for a binary class `C` the following are equivalent: `C` has the uniform convergence property,
empirical risk minimization learns `C` agnostically, `C` is agnostically PAC learnable, `C` is PAC
learnable in the realizable setting, and `C` has finite VC dimension. This module proves the
equivalence of realizable PAC learnability (deterministic or randomized) with finite VC dimension
on countable domains with measurable singletons, and that agnostic PAC learnability implies finite
VC dimension on every domain with measurable singletons.

The direction from finite VC dimension is the ε-net upper bound
(`isPACLearnable_realizableDistributions_of_hasFiniteVCDim`); the converse is the
Ehrenfeucht–Haussler–Kearns–Valiant lower bound (`IsRPACLearnable.hasFiniteVCDim`).

Not formalized here: the uniform-convergence and agnostic-ERM arms of Theorem 6.7, agnostic
learnability *from* finite VC dimension, the quantitative two-sided sample-complexity bounds of
[ShalevShwartzBenDavid2014, Theorem 6.8], and the upper bound on uncountable domains, which needs
a measurability hypothesis on the class.

## Main results

- `isPACLearnable_realizableDistributions_iff_hasFiniteVCDim`: on a countable domain with
  measurable singletons, a binary class is PAC learnable over the distributions it realizes iff it
  has finite VC dimension.
- `isRPACLearnable_realizableDistributions_iff_hasFiniteVCDim`: the same for randomized learners.
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

end Cslib.MachineLearning.PACLearning

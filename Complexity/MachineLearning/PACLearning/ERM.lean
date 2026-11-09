/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.MachineLearning.PACLearning.VersionSpace

/-! # Empirical risk minimization

A learner is an *empirical risk minimizer* (ERM) for a concept class `C` if, on every labeled
sample, it outputs a concept of `C` with the fewest sample errors among all concepts of `C`
[ShalevShwartzBenDavid2014, Section 2.3]. On a realizable sample some concept of `C` makes no
errors, so an ERM output lies in the version space: in the realizable setting every ERM learner is
a consistent learner (`IsConsistent`). Every nonempty class has both kinds of learner. These
learners are semantic: no bound on the time needed to find a minimizer is claimed.

## Main definitions

- `IsERM A C`: the learner `A` minimizes the empirical miscount over `C` on every sample.

## Main results

- `exists_isERM`: every nonempty concept class has an ERM learner.
- `IsERM.isConsistent`: an ERM learner is consistent with its class.
- `exists_isConsistent`: every nonempty concept class has a consistent learner.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

namespace Cslib.MachineLearning.PACLearning

variable {α β : Type*} {m : ℕ}

/-- The learner `A` is an *empirical risk minimizer* for the concept class `C`: on every labeled
sample `S` it outputs a concept of `C` whose number of errors on `S` is minimal among the concepts
of `C` [ShalevShwartzBenDavid2014, Section 2.3]. -/
@[expose] def IsERM [DecidableEq β] (A : Learner α β m) (C : ConceptClass α β) : Prop :=
  ∀ S, A S ∈ C ∧ ∀ h ∈ C, empiricalMiscount (A S) S ≤ empiricalMiscount h S

/-- Every nonempty concept class has an empirical risk minimizer. -/
theorem exists_isERM [DecidableEq β] {C : ConceptClass α β} (hC : C.Nonempty) :
    ∃ A : Learner α β m, IsERM A C :=
  ⟨fun S => Function.argminOn (fun h => empiricalMiscount h S) C hC, fun S =>
    ⟨Function.argminOn_mem _ _ _, fun _ hh =>
      Function.argminOn_le (fun h => empiricalMiscount h S) C hh⟩⟩

/-- **ERM is consistent in the realizable setting**: on a sample labeled by a concept of `C`, an
empirical risk minimizer makes no errors, so its output lies in the version space. -/
theorem IsERM.isConsistent [DecidableEq β] {A : Learner α β m} {C : ConceptClass α β}
    (hA : IsERM A C) : IsConsistent A C := by
  intro S ⟨c, hc, hcS⟩
  obtain ⟨hAC, hmin⟩ := hA S
  have hc0 : empiricalMiscount c S = 0 :=
    (mem_versionSpace_iff_empiricalMiscount_zero.1
      (mem_versionSpace_of_realizable hc S hcS)).2
  exact mem_versionSpace_iff_empiricalMiscount_zero.2 ⟨hAC, Nat.le_zero.1 (hc0 ▸ hmin c hc)⟩

/-- Every nonempty concept class has a consistent learner. -/
theorem exists_isConsistent {C : ConceptClass α β} (hC : C.Nonempty) :
    ∃ A : Learner α β m, IsConsistent A C := by
  classical
  obtain ⟨A, hA⟩ := exists_isERM (m := m) hC
  exact ⟨A, hA.isConsistent⟩

end Cslib.MachineLearning.PACLearning

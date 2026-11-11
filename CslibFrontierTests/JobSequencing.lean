/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.JobSequencing

/-!
# Sequencing with deadlines and penalties: tests

Total penalties of concrete orders (order dependence, boundary deadlines, repeated jobs, large
binary numbers), instances in and out of `JobSequencing`, Karp's reduction from `SubsetSum` on yes
and no instances including targets above the total, and compositional `fun_prop` synthesis.
-/

namespace CslibFrontierTests.JobSequencing

open Cslib.Complexity Turing.MultiTapeTM
open scoped List

/-- Small instances are decided by enumerating the permutations (`List.permutations'` is
structurally recursive, so the kernel evaluates it). -/
theorem mem_JobSequencing_iff_permutations {x : JobSequencingInstance} :
    x ∈ JobSequencing ↔ ∃ σ ∈ x.jobs.permutations', JobSequencing.totalPenalty σ ≤ x.bound :=
  exists_congr fun _ => and_congr_left' List.mem_permutations'.symm

/-! ### Headline results -/

example : JobSequencing ∈ NP encJobSequencing ∧
    PolyTimeReducible (encPair (encList encNat) encNat) encJobSequencing SubsetSum
      JobSequencing :=
  ⟨JobSequencing_npComplete.1, polyTimeReducible_SubsetSum_JobSequencing⟩

/-! ### Total penalties -/

-- Job `(2, 2, 7)` then `(3, 4, 10)`: the first completes at 2, on time; the second at 5, late.
example : JobSequencing.totalPenalty [⟨2, 2, 7⟩, ⟨3, 4, 10⟩] = 10 := rfl
-- In the other order the first completes at 3, on time; the second at 5, late.
example : JobSequencing.totalPenalty [⟨3, 4, 10⟩, ⟨2, 2, 7⟩] = 7 := rfl
-- Completing exactly at the deadline is on time.
example : JobSequencing.totalPenalty [⟨4, 4, 1⟩] = 0 := rfl
example : JobSequencing.totalPenalty [⟨5, 4, 1⟩] = 1 := rfl
-- Jobs of time zero complete at once.
example : JobSequencing.totalPenalty [⟨0, 0, 9⟩, ⟨0, 0, 9⟩] = 0 := rfl
-- Large numbers are added and compared in binary.
example : JobSequencing.totalPenalty [⟨2 ^ 70, 2 ^ 70, 2 ^ 90⟩, ⟨1, 2 ^ 70, 3⟩] = 3 := by decide

/-! ### Instances -/

example : (⟨[⟨2, 2, 7⟩, ⟨3, 4, 10⟩], 7⟩ : JobSequencingInstance) ∈ JobSequencing :=
  ⟨[⟨3, 4, 10⟩, ⟨2, 2, 7⟩], List.Perm.swap _ _ _, le_refl 7⟩
example : (⟨[⟨2, 2, 7⟩, ⟨3, 4, 10⟩], 6⟩ : JobSequencingInstance) ∉ JobSequencing :=
  fun h => absurd (mem_JobSequencing_iff_permutations.1 h) (by decide)

-- Boundary cases: no jobs, and repeated jobs scheduled with multiplicity.
example : (⟨[], 0⟩ : JobSequencingInstance) ∈ JobSequencing := ⟨[], List.Perm.refl _, le_refl 0⟩
example : (⟨[⟨2, 3, 5⟩, ⟨2, 3, 5⟩], 5⟩ : JobSequencingInstance) ∈ JobSequencing :=
  mem_JobSequencing_iff_permutations.2 (by decide)
example : (⟨[⟨2, 3, 5⟩, ⟨2, 3, 5⟩], 4⟩ : JobSequencingInstance) ∉ JobSequencing :=
  fun h => absurd (mem_JobSequencing_iff_permutations.1 h) (by decide)

/-! ### Karp's reduction from `SubsetSum` -/

example : SubsetSum.toJobSequencing ([3, 5], 5) = ⟨[⟨3, 5, 3⟩, ⟨5, 5, 5⟩], 3⟩ := rfl

-- `5` hits the target, so running its job first leaves penalty `3`.
example : SubsetSum.toJobSequencing ([3, 5], 5) ∈ JobSequencing :=
  ⟨[⟨5, 5, 5⟩, ⟨3, 5, 3⟩], List.Perm.swap _ _ _, le_refl 3⟩
-- No sub-multiset of `[3, 5]` sums to `4`, so every order pays more than `4`.
example : SubsetSum.toJobSequencing ([3, 5], 4) = ⟨[⟨3, 4, 3⟩, ⟨5, 4, 5⟩], 4⟩ := rfl
example : SubsetSum.toJobSequencing ([3, 5], 4) ∉ JobSequencing :=
  fun h => absurd (mem_JobSequencing_iff_permutations.1 h) (by decide)
example : ([3, 5], 4) ∉ SubsetSum := fun h => by
  obtain ⟨s, hs, hsum⟩ := mem_SubsetSum_iff_sublist.1 h
  exact absurd (⟨s, List.mem_sublists.2 hs, hsum⟩ : ∃ s ∈ [3, 5].sublists, s.sum = 4)
    (by decide)

-- Targets above the total give an instance with no feasible order.
example : SubsetSum.toJobSequencing ([3, 5], 9) = ⟨[⟨1, 0, 1⟩], 0⟩ := rfl
example : SubsetSum.toJobSequencing ([3, 5], 9) ∉ JobSequencing :=
  fun h => absurd (mem_JobSequencing_iff_permutations.1 h) (by decide)

-- The target `0` is always reachable, and so is the full total.
example : SubsetSum.toJobSequencing ([3, 5], 0) ∈ JobSequencing :=
  (SubsetSum.toJobSequencing_mem_iff _).2 ⟨0, bot_le, rfl⟩
example : SubsetSum.toJobSequencing ([3, 5], 8) ∈ JobSequencing :=
  (SubsetSum.toJobSequencing_mem_iff _).2 ⟨[3, 5], le_refl _, rfl⟩

/-! ### Compositional `fun_prop` synthesis -/

example : ComputableInPolyTime
    (fun σ : List JobSequencing.Job => JobSequencing.totalPenalty (σ ++ σ))
    (encList JobSequencing.encJob) encNat := by fun_prop

example : ComputableInPolyTime
    (fun x : JobSequencingInstance => (x.jobs.headD ⟨0, 0, 0⟩).time + x.bound)
    encJobSequencing encNat := by fun_prop

example : ComputableInPolyTime (fun x : List ℕ × ℕ => SubsetSum.toJobSequencing (x.1, x.2 + 1))
    (encPair (encList encNat) encNat) encJobSequencing := by fun_prop

example : ComputableInPolyTime
    (fun x : JobSequencingInstance =>
      (⟨x.jobs.map fun j => ⟨j.deadline, j.time, j.penalty⟩, x.bound⟩ : JobSequencingInstance))
    encJobSequencing encJobSequencing := by fun_prop

end CslibFrontierTests.JobSequencing

-- Global `fun_prop` availability without opening `Cslib.Complexity` or
-- `Cslib.Complexity.JobSequencing`.
example : Turing.MultiTapeTM.ComputableInPolyTime
    (fun x : Cslib.Complexity.JobSequencingInstance =>
      Cslib.Complexity.JobSequencingInstance.mk
        (x.jobs.map fun j => Cslib.Complexity.JobSequencing.Job.mk j.time j.deadline j.penalty)
        x.bound)
    Cslib.Complexity.encJobSequencing Cslib.Complexity.encJobSequencing := by
  fun_prop

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic
public import CslibFrontier.Computability.Complexity.Classes.Time
import CslibFrontier.Computability.Complexity.Classes.Time.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ReachableViews
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Nondeterministic space within deterministic exponential time

A nondeterministic machine within space `s` is simulated deterministically within time
`2 ^ O(log₂ n + s)` [Arora and Barak, Theorem 4.3][AroraBarak09]
[Sipser, Section 8.4][Sipser2013]: list the views reachable from the initial view by breadth-first
search until no new view appears (`Turing.MultiTapeNTM.reachableViews`), and test whether one of
them is accepting. The simulation holds for recognizers (`Turing.MultiTapeNTM.RecognizesInSpace`),
whose branches need not halt; the class `Cslib.Complexity.NSPACE` uses the deciding form, so the
inclusion holds for it a fortiori. The space bound need not be constructible: the search stops by
itself, and the bound enters only the analysis. Arora and Barak state the theorem for
space-constructible bounds, as their machines mark off the space before they run.

## Main results

* `Turing.MultiTapeNTM.RecognizesInSpace.mem_DTIME`: a problem recognized within space `s` is in
  `DTIME (2 ^ (c * (log₂ n + s n + 1)))`.
* `Cslib.Complexity.exists_mem_DTIME_of_mem_NSPACE`: `NSPACE s ⊆ DTIME (2 ^ O(log₂ n + s n))`.
* `Cslib.Complexity.exists_mem_DTIME_of_mem_NSPACE_of_log2_le`: `NSPACE s ⊆ DTIME (2 ^ O(s n))`
  when `log₂ n ≤ s n`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Theorem 4.3][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
-/

public section

namespace Turing.MultiTapeNTM

open MultiTapeTM Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {k : ℕ} {State : Type} [Finite State]
  {ntm : MultiTapeNTM k Bool State} {A : Set α}

/-- A machine accepts exactly when one of its reachable views is accepting. -/
private theorem any_acceptingView_reachableViews_iff {input : List Bool} {s : ℕ}
    (hs : ntm.RunsInSpace input s) :
    (ntm.reachableViews input).any acceptingView = true ↔ ntm.Accepts input := by
  rw [accepts_iff_reflTransGen_viewStep]
  simp only [List.any_eq_true, acceptingView, Bool.and_eq_true, decide_eq_true_eq,
    mem_reachableViews_iff hs]

/-- **Space-bounded nondeterministic recognizers are within exponential time**
[Arora and Barak, Theorem 4.3][AroraBarak09] [Sipser, Section 8.4][Sipser2013]: a problem
recognized by a nondeterministic machine within space `s n`, whose branches need not halt, is
decided deterministically within time `2 ^ (c * (log₂ n + s n + 1))` for a constant `c` of the
machine. The space bound need not be constructible. -/
theorem RecognizesInSpace.mem_DTIME {s : ℕ → ℕ}
    (h : ntm.RecognizesInSpace enc A fun a => s (enc a).length) :
    ∃ c, A ∈ DTIME enc fun n => 2 ^ (c * (Nat.log2 n + s n + 1)) := by
  obtain ⟨c, hc⟩ := exists_computableInTimeAndSpace_reachableViews (fun a => (h a).1)
    (g := fun views => views.any acceptingView)
    (ComputableInPolyTime.anyWithInput ComputableInPolyTime.id'
      (computableInPolyTime_acceptingView.comp (ComputableInPolyTime.snd _ _)))
  exact ⟨c, 1, 0, fun n => 2 ^ (c * (Nat.log2 n + s n + 1)), decidableInTimeAndSpace_iff.mpr
    ⟨_, hc.mono (fun _ => by simp) fun _ => le_rfl,
      fun a => (h a).2.trans (any_acceptingView_reachableViews_iff (h a).1).symm⟩⟩

end Turing.MultiTapeNTM

namespace Cslib.Complexity

open _root_.Turing

variable {α : Type} {enc : α ↪ List Bool}

/-- **Nondeterministic space is within deterministic exponential time**
[Arora and Barak, Theorem 4.3][AroraBarak09] [Sipser, Section 8.4][Sipser2013]:
`NSPACE s ⊆ DTIME (2 ^ O(log₂ n + s n))`. The space bound need not be constructible. -/
theorem exists_mem_DTIME_of_mem_NSPACE {s : ℕ → ℕ} {A : Set α} (h : A ∈ NSPACE enc s) :
    ∃ c, A ∈ DTIME enc fun n => 2 ^ (c * (Nat.log2 n + s n + 1)) := by
  obtain ⟨k, State, _, ntm, c₁, c₂, hA⟩ := h
  obtain ⟨c, hc⟩ := hA.recognizesInSpace.mem_DTIME (s := fun n => c₁ * s n + c₂)
  exact ⟨_, DTIME_two_pow_log2_add_mul_add_subset c c₁ c₂ s hc⟩

/-- **Nondeterministic space is within deterministic exponential time** above logarithmic space
[Arora and Barak, Theorem 4.3][AroraBarak09] [Sipser, Section 8.4][Sipser2013]:
`NSPACE s ⊆ DTIME (2 ^ O(s n))` when `log₂ n ≤ s n`. The space bound need not be
constructible. -/
theorem exists_mem_DTIME_of_mem_NSPACE_of_log2_le {s : ℕ → ℕ} {A : Set α}
    (hs : ∀ n, Nat.log2 n ≤ s n) (h : A ∈ NSPACE enc s) :
    ∃ c, A ∈ DTIME enc fun n => 2 ^ (c * s n) := by
  obtain ⟨c, hc⟩ := exists_mem_DTIME_of_mem_NSPACE h
  exact ⟨_, DTIME_two_pow_log2_add_subset hs hc⟩

end Cslib.Complexity

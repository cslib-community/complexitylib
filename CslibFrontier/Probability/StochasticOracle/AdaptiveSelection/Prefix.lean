/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.AdaptiveSelection
public import CslibFrontier.Probability.PMF.SequentialHistory
public import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Tactic

/-!
# Counts on earlier transcript prefixes

A history-dependent event count is monotone when newer responses are added.
Chronological tuple restriction corresponds to an older suffix of a newest-first transcript.
-/

public section
namespace Cslib.Probability.StochasticOracle.AdaptiveSelection
variable {Ω : Type*}

/-- At most one event is counted per response in the transcript. -/
theorem count_le_length (b : List Ω → Ω → Bool) (h : List Ω) : count b h ≤ h.length := by
  induction h with
  | nil => exact le_rfl
  | cons x h ih =>
    simp only [count, List.length_cons]
    split_ifs <;> omega

/-- Adding newer responses preserves every event counted on the older suffix. -/
theorem count_le_of_suffix (b : List Ω → Ω → Bool) {h g : List Ω} (hs : h.IsSuffix g) :
    count b h ≤ count b g := by
  obtain ⟨s, rfl⟩ := hs
  induction s with
  | nil => exact le_rfl
  | cons x s ih =>
    simp only [List.cons_append, count]
    omega

/-- Earlier chronological prefixes cannot have more counted events. -/
theorem count_take_le (b : List Ω → Ω → Bool) {n m : ℕ} (hnm : n ≤ m) (h : Fin m → Ω) :
    count b (PMF.seqHistory (Fin.take n hnm h)) ≤ count b (PMF.seqHistory h) := by
  apply count_le_of_suffix
  rw [PMF.seqHistory, PMF.seqHistory, Fin.ofFn_take_eq_take_ofFn]
  exact (List.take_prefix n (List.ofFn h)).reverse

end Cslib.Probability.StochasticOracle.AdaptiveSelection

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Record
public import CslibFrontier.Probability.StochasticOracle.AdaptiveSelection.Prefix
import Mathlib.Tactic

/-!
# Event counts in absorbing call-and-halt transcripts

A bound on issued calls limits every event that ignores halt records to the
corresponding chronological prefix. This is deterministic and shared by finite
tables and arbitrary discrete execution laws.

## Main results

* `calls_eq_length`: a transcript without halts consists entirely of calls.
* `count_eq_prefix_of_issued_bound`: later halts preserve the earlier event count.
-/

public section
namespace Cslib.Probability.StochasticOracle.SelectionPolicy
open AdaptiveSelection
variable {B R : Type}

/-- A transcript containing no halt consists entirely of issued calls. -/
theorem calls_eq_length (h : List (Record B R)) (hh : none ∉ h) :
    count issued h = h.length := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    have hn : x ≠ none ∧ none ∉ h := by simpa [eq_comm] using hh
    cases x with
    | none => exact (hn.1 rfl).elim
    | some z => simp [count, issued, ih hn.2]

/-- In an absorbing transcript with at most `v` issued calls, every event that
ignores halts has already attained its final count by prefix `v`. -/
theorem count_eq_prefix_of_issued_bound
    (f : List (Record B R) → Record B R → Bool) (hf : ∀ h, f h none = false)
    {u v : ℕ} (hvu : v ≤ u) (h : Fin u → Record B R)
    (active : ∀ t : Fin u, h t ≠ none → none ∉ PMF.seqHistory (Fin.take t.1 t.2.le h))
    (hc : count issued (PMF.seqHistory h) ≤ v) :
    count f (PMF.seqHistory h) = count f (PMF.seqHistory (Fin.take v hvu h)) := by
  have hn (t : Fin u) (hvt : v ≤ t.1) : h t = none := by
    by_contra ht
    have ha := active t ht
    have hl := calls_eq_length _ ha
    rw [PMF.length_seqHistory] at hl
    have hm := count_take_le issued (Nat.succ_le_of_lt t.2) h
    rw [Fin.take_succ_eq_snoc _ t.2, PMF.seqHistory_snoc, count] at hm
    have hi : issued (PMF.seqHistory (Fin.take t.1 t.2.le h)) (h t) = true := by
      cases he : h t with
      | none => exact (ht he).elim
      | some z => rfl
    rw [hi] at hm
    simp only [ite_true] at hm
    omega
  have he : ∀ n (hn : n ≤ u), v ≤ n →
      count f (PMF.seqHistory (Fin.take n hn h)) =
        count f (PMF.seqHistory (Fin.take v hvu h)) := by
    intro n hnu hvn
    induction n, hvn using Nat.le_induction with
    | base => rfl
    | succ n hvn ih =>
      rw [Fin.take_succ_eq_snoc _ (by omega), PMF.seqHistory_snoc, count,
        hn ⟨n, by omega⟩ hvn, hf]
      simpa only [Bool.false_eq_true, ite_false, Nat.add_zero] using ih (by omega)
  simpa only [Fin.take_eq_self] using he u le_rfl hvu

end Cslib.Probability.StochasticOracle.SelectionPolicy

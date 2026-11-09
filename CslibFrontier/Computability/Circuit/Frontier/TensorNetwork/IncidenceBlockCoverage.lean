/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceSelections
public import CslibFrontier.Foundations.Data.BitString.CombinationCoverage
import Mathlib.Data.List.Count

/-!
# Exact incidence-block selection and rejection of impossible degrees

The actual decoder selects every fixed-size incidence sublist exactly once. Reading blocks always
produces one index per block, even from an empty word, so an impossible degree is rejected rather
than disappearing through `zip`. These are the local coverage and zero-contribution obligations
in [OpenAI2026ETH], Lemma D.2, PDF pp. 55–56.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.selectBlock_coverage`: unique coverage of incidence
  sublists by actual fitting ranks.
* `Cslib.Circuits.Frontier.IncidenceNetwork.length_blockIndices`: no block is skipped.
* `Cslib.Circuits.Frontier.IncidenceNetwork.validIndices_false_of_impossible`: impossible degrees
  force rejection, independently of the supplied word.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.BitString

private theorem length_chosenBy (xs : List (ℕ × ℕ)) (w : List Bool)
    (hw : w.length = xs.length) : (chosenBy xs w).length = w.count true := by
  induction xs generalizing w with
  | nil => have : w = [] := List.length_eq_zero_iff.mp hw; simp [this, chosenBy]
  | cons a xs ih =>
    cases w with
    | nil => simp at hw
    | cons b w =>
      have ht : w.length = xs.length := by simpa using hw
      cases b
      · change (chosenBy xs w).length = (false :: w).count true
        rw [List.count_cons_of_ne (by decide)]
        exact ih w ht
      · rw [List.count_cons_self]
        change (chosenBy xs w).length + 1 = w.count true + 1
        rw [ih w ht]

private theorem chosenBy_injective (xs : List (ℕ × ℕ)) (hxs : xs.Nodup)
    (u v : List Bool) (hu : u.length = xs.length) (hv : v.length = xs.length)
    (he : chosenBy xs u = chosenBy xs v) : u = v := by
  induction xs generalizing u v with
  | nil => simp_all
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hxs
    cases u with
    | nil => simp at hu
    | cons b u =>
      cases v with
      | nil => simp at hv
      | cons c v =>
        have hu' : u.length = xs.length := by simpa using hu
        have hv' : v.length = xs.length := by simpa using hv
        cases b <;> cases c
        · change chosenBy xs u = chosenBy xs v at he
          exact congrArg (false :: ·) (ih ht u v hu' hv' he)
        · change chosenBy xs u = a :: chosenBy xs v at he
          have hm : a ∈ chosenBy xs u := he.symm ▸ List.mem_cons_self
          exact False.elim (ha ((chosenBy_sublist xs u).subset hm))
        · change a :: chosenBy xs u = chosenBy xs v at he
          have hm : a ∈ chosenBy xs v := he ▸ List.mem_cons_self
          exact False.elim (ha ((chosenBy_sublist xs v).subset hm))
        · change a :: chosenBy xs u = a :: chosenBy xs v at he
          exact congrArg (true :: ·) (ih ht u v hu' hv' (List.cons.inj he).2)

private theorem exists_chosenBy {ys xs : List (ℕ × ℕ)} (h : ys.Sublist xs) :
    ∃ w : List Bool, w.length = xs.length ∧ chosenBy xs w = ys := by
  induction h with
  | slnil => exact ⟨[], rfl, rfl⟩
  | cons a h ih =>
    obtain ⟨w, hw, he⟩ := ih
    exact ⟨false :: w, by simpa using hw, by simpa [chosenBy] using he⟩
  | cons_cons a h ih =>
    obtain ⟨w, hw, he⟩ := ih
    exact ⟨true :: w, by simpa using hw, by simpa [chosenBy] using congrArg (a :: ·) he⟩

/-- Every fixed-size incidence sublist has exactly one valid rank. No full powerset is executed. -/
theorem selectBlock_coverage (xs : List (ℕ × ℕ)) (hxs : xs.Nodup)
    (ys : List (ℕ × ℕ)) (hys : ys.Sublist xs) :
    ∃! r : Fin (xs.length.choose ys.length), selectBlock (xs, ys.length) r = ys := by
  obtain ⟨w, hw, he⟩ := exists_chosenBy hys
  have hc : w.count true = ys.length :=
    (length_chosenBy xs w hw).symm.trans (congrArg List.length he)
  obtain ⟨r, hr, _⟩ := unrankCombination_coverage w
  have hr' : r.val < xs.length.choose ys.length := by simpa only [hw, hc] using r.isLt
  have hrout : selectBlock (xs, ys.length) r = ys := by
    change chosenBy xs (unrankCombination xs.length ys.length r) = ys
    rw [← hw, ← hc, hr, he]
  refine ⟨⟨r, hr'⟩, hrout, ?_⟩
  intro s hs
  apply Fin.ext
  apply unrankCombination_injective s.isLt hr'
  apply chosenBy_injective xs hxs _ _ (length_unrankCombination _ _ _)
    (length_unrankCombination _ _ _)
  exact hs.trans hrout.symm

private theorem validIndices_false_of_mem {blocks : List Block} {idx : List ℕ}
    (hlen : idx.length = blocks.length) {b : Block} (hb : b ∈ blocks)
    (hd : b.1.length < b.2) : validIndices blocks idx = false := by
  induction blocks generalizing idx with
  | nil => simp at hb
  | cons a blocks ih =>
    cases idx with
    | nil => simp at hlen
    | cons i idx =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rcases List.mem_cons.mp hb with rfl | hb
      · simp [validIndices, Nat.choose_eq_zero_of_lt hd]
      · have hz := ih hlen hb
        change (decide (i < a.1.length.choose a.2) && validIndices blocks idx) = false
        rw [hz, Bool.and_false]

/-- A coordinate greater than its incidence capacity forces actual row rejection. -/
theorem validIndices_false_of_impossible (blocks : List Block) (bs : List Bool)
    {b : Block} (hb : b ∈ blocks) (hd : b.1.length < b.2) :
    validIndices blocks (blockIndices blocks bs) = false :=
  validIndices_false_of_mem (length_blockIndices _ _) hb hd

end Cslib.Circuits.Frontier.IncidenceNetwork

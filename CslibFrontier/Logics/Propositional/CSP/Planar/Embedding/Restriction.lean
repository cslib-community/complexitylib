/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Boundary
import Mathlib.Data.List.GetD

/-!
# Short first returns in executable boundary restrictions

These equations inspect the literal list-funded scan used by `restrictPrefix`. Its first
retained successor is read after one, two or three steps. The raw table may be malformed elsewhere;
the stated length and retained-index hypotheses are sufficient for these local equations.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

/-- A retained immediate successor is the first return, provided the table funds one step. -/
theorem getD_restrictPrefix_one (c : Graph.RotationCertificate) (darts i : ℕ)
    (hi : i < darts) (hc : 0 < c.successor.length) (hs : c.successor.getD i 0 < darts) :
    (restrictPrefix darts c).successor.getD i 0 = c.successor.getD i 0 := by
  unfold restrictPrefix
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map, List.length_range] using hi),
    List.getElem_map, List.getElem_range]
  have hlen : c.successor.length = (c.successor.length - 1) + 1 := by omega
  rw [hlen, List.range_succ_eq_map, List.map_cons]
  rw [List.find?_cons_of_pos (by simpa [Graph.RotationCertificate.walk] using hs)]
  rfl

/-- Restriction to the full table is literal identity when every successor stays within
its length. This includes the empty table, without inventing a positive scan clock. -/
theorem restrictPrefix_eq_self (c : Graph.RotationCertificate)
    (h : ∀ i < c.successor.length, c.successor.getD i 0 < c.successor.length) :
    restrictPrefix c.successor.length c = c := by
  apply congrArg Graph.RotationCertificate.mk
  refine List.ext_getElem (by
    change (restrictPrefix c.successor.length c).successor.length = c.successor.length
    rw [length_restrictPrefix]) ?_
  intro i hi hj
  change i < (restrictPrefix c.successor.length c).successor.length at hi
  change (restrictPrefix c.successor.length c).successor[i] = c.successor[i]
  rw [← List.getD_eq_getElem (restrictPrefix c.successor.length c).successor 0 hi,
    ← List.getD_eq_getElem c.successor 0 hj]
  exact getD_restrictPrefix_one c _ i hj (by omega) (h i hj)

/-- If the first successor is deleted and the second retained, two list-funded steps find
the second successor exactly. No search clock depends on the numerical table entries. -/
theorem getD_restrictPrefix_two (c : Graph.RotationCertificate) (darts i : ℕ)
    (hi : i < darts) (hc : 2 ≤ c.successor.length)
    (hs : darts ≤ c.successor.getD i 0)
    (ht : c.successor.getD (c.successor.getD i 0) 0 < darts) :
    (restrictPrefix darts c).successor.getD i 0 = c.successor.getD (c.successor.getD i 0) 0 := by
  unfold restrictPrefix
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map, List.length_range] using hi),
    List.getElem_map, List.getElem_range]
  have hlen : c.successor.length = (c.successor.length - 2) + 1 + 1 := by omega
  rw [hlen]
  simp only [List.range_succ_eq_map, List.map_cons]
  rw [List.find?_cons_of_neg (by
    change ¬ decide (c.successor.getD i 0 < darts) = true
    simp only [decide_eq_true_eq]
    omega)]
  rw [List.find?_cons_of_pos (by simpa [Graph.RotationCertificate.walk,
    Function.iterate_succ_apply'] using ht)]
  rfl

/-- If exactly the first two successors are deleted, three list-funded steps find the
third successor. In particular the clock is not funded by the deleted numerical indices. -/
theorem getD_restrictPrefix_three (c : Graph.RotationCertificate) (darts i : ℕ)
    (hi : i < darts) (hc : 3 ≤ c.successor.length)
    (hs : darts ≤ c.successor.getD i 0)
    (ht : darts ≤ c.successor.getD (c.successor.getD i 0) 0)
    (hu : c.successor.getD (c.successor.getD (c.successor.getD i 0) 0) 0 < darts) :
    (restrictPrefix darts c).successor.getD i 0 =
      c.successor.getD (c.successor.getD (c.successor.getD i 0) 0) 0 := by
  unfold restrictPrefix
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map, List.length_range] using hi),
    List.getElem_map, List.getElem_range]
  have hlen : c.successor.length = (c.successor.length - 3) + 1 + 1 + 1 := by omega
  rw [hlen]
  simp only [List.range_succ_eq_map, List.map_cons]
  rw [List.find?_cons_of_neg (by
    change ¬ decide (c.successor.getD i 0 < darts) = true
    simp only [decide_eq_true_eq]
    omega)]
  rw [List.find?_cons_of_neg (by
    change ¬ decide (c.successor.getD (c.successor.getD i 0) 0 < darts) = true
    simp only [decide_eq_true_eq]
    omega)]
  rw [List.find?_cons_of_pos (by simpa [Graph.RotationCertificate.walk,
    Function.iterate_succ_apply'] using hu)]
  rfl

/-- An intermediate restriction does not change first returns that reach the smaller
prefix in at most two steps. Both scans use their literal list-funded clocks; the raw table
may be malformed away from the stated prefix. This applies to distinct boundary markers. -/
theorem restrictPrefix_restrictPrefix_of_short_returns (c : Graph.RotationCertificate)
    (m n : ℕ) (hmn : m ≤ n) (hc : 2 ≤ c.successor.length)
    (hshort : ∀ i < m, c.successor.getD i 0 < m ∨
      c.successor.getD (c.successor.getD i 0) 0 < m) :
    restrictPrefix m (restrictPrefix n c) = restrictPrefix m c := by
  apply congrArg Graph.RotationCertificate.mk
  refine List.ext_getElem (by
    change (restrictPrefix m (restrictPrefix n c)).successor.length =
      (restrictPrefix m c).successor.length
    rw [length_restrictPrefix, length_restrictPrefix]) ?_
  intro i hi hj
  change i < (restrictPrefix m (restrictPrefix n c)).successor.length at hi
  change i < (restrictPrefix m c).successor.length at hj
  change (restrictPrefix m (restrictPrefix n c)).successor[i] = (restrictPrefix m c).successor[i]
  rw [← List.getD_eq_getElem (restrictPrefix m (restrictPrefix n c)).successor 0 hi,
    ← List.getD_eq_getElem (restrictPrefix m c).successor 0 hj]
  have him : i < m := by rwa [length_restrictPrefix] at hi
  have hin : i < n := by omega
  have hclock : 0 < (restrictPrefix n c).successor.length := by
    rw [length_restrictPrefix]
    omega
  by_cases hs : c.successor.getD i 0 < m
  · have hn : (restrictPrefix n c).successor.getD i 0 = c.successor.getD i 0 :=
      getD_restrictPrefix_one c n i hin (by omega) (by omega)
    rw [getD_restrictPrefix_one (restrictPrefix n c) m i him hclock (by rw [hn]; exact hs),
      hn, getD_restrictPrefix_one c m i him (by omega) hs]
  · have ht : c.successor.getD (c.successor.getD i 0) 0 < m := (hshort i him).resolve_left hs
    have hold := getD_restrictPrefix_two c m i him hc (by omega) ht
    by_cases hn : c.successor.getD i 0 < n
    · have h₁ := getD_restrictPrefix_one c n i hin (by omega) hn
      have h₂ := getD_restrictPrefix_one c n (c.successor.getD i 0) hn (by omega) (by omega)
      have hfund : 2 ≤ (restrictPrefix n c).successor.length := by
        rw [length_restrictPrefix]
        omega
      rw [getD_restrictPrefix_two (restrictPrefix n c) m i him hfund (by rw [h₁]; omega)
        (by rw [h₁, h₂]; exact ht), h₁, h₂, hold]
    · have h₁ := getD_restrictPrefix_two c n i hin hc (by omega) (by omega)
      rw [getD_restrictPrefix_one (restrictPrefix n c) m i him hclock (by rw [h₁]; exact ht),
        h₁, hold]

end Cslib.Complexity.CSP.OrderedBoundary

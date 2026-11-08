/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Planar.Embedding.Boundary
import Mathlib.Data.List.GetD

/-!
# Short first returns in executable boundary restrictions

These equations inspect the literal list-funded scan used by `restrictPrefix`. Its first
retained successor is read after one or two steps. The raw table may be malformed elsewhere;
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

end Cslib.Complexity.CSP.OrderedBoundary

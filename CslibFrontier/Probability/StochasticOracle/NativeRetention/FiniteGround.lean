/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.Correctness
import Mathlib.Tactic

/-!
# Finite ground labels for the original rational WSC input

The finite prefix has exactly the original dual-vector length. Incidences,
weights and dual prices are read from original runtime data; no new certificate
or optimum is supplied. [Wang2027], Section 5, PDF p. 9.

## Main results

* `image_sets`: finite ground labels recover the original incidence rows.
* `instance`: the native rational input has the corresponding finite WSC interpretation.
-/

public section
namespace Cslib.Probability.StochasticOracle.NativeRetention.FiniteGround
open Finset PartialCover

/-- Original incidence on a finite ground prefix sharing the runtime dual length. -/
@[expose] def sets (x : Input) (n : ℕ) (j : ℕ) : Finset (Fin n) :=
  univ.filter fun e => e.val ∈ x.rows.getD j []

/-- Finite-prefix incidences decode to precisely the original natural-index sets. -/
theorem image_sets (x : Input) (n : ℕ) (hn : n = x.dual.length) (j : ℕ) :
    (sets x n j).image Fin.val = elements x j := by
  ext e
  simp only [sets, elements, ground, List.mem_toFinset, List.mem_filter,
    List.mem_range, decide_eq_true_eq, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨by simpa only [← hn] using i.isLt, hi⟩
  · rintro ⟨he, hr⟩
    exact ⟨⟨e, by simpa only [hn] using he⟩, hr, rfl⟩

/-- The actual original WSC input, with finite ground and original row labels. -/
@[expose] def instanceOf (x : Input) (hx : Valid x) (n : ℕ) (hn : n = x.dual.length) :
    Instance (Fin n) (Fin x.rows.length) where
  ground := univ
  sets j := sets x n j.val
  sets_subset _ := subset_univ _
  weight j := x.weights.getD j.val 0
  weight_nonneg j := by exact_mod_cast hx.weight_nonneg j.val
  dual e := x.dual.getD e.val 0
  dual_nonneg e := by exact_mod_cast hx.dual_nonneg e.val
  dual_feasible j := by
    have hs := sum_image (s := sets x n j.val) (g := Fin.val)
      (f := fun e : ℕ => x.dual.getD e 0) (fun _ _ _ _ h => Fin.val_injective h)
    rw [image_sets x n hn j.val] at hs
    have h := hx.feasible j.val
    rw [hs] at h
    exact_mod_cast h

end Cslib.Probability.StochasticOracle.NativeRetention.FiniteGround

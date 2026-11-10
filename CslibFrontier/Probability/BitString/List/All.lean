/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.Product

/-!
# Acceptance of independent fixed-width blocks

Splitting a uniform word into equal-width rows gives independent uniform samples. Testing every
row therefore multiplies the individual acceptance probabilities, including zero rows or width.

## Main results

* `Cslib.BitString.uniformList_all_listRow_true`: the exact acceptance probability of repeated
  fixed-width Boolean checks.
-/

public section

namespace Cslib.BitString

open Probability
open scoped BigOperators

private theorem map_all_ofFn_true (count : ℕ) (p : PMF (Fin count → Bool)) :
    (p.map (fun bits => (List.ofFn bits).all id)) true = p (fun _ => true) := by
  classical
  have h (bits : Fin count → Bool) : true = (List.ofFn bits).all id ↔ bits = fun _ => true := by
    simp only [eq_comm (a := true), List.all_eq_true, List.forall_mem_ofFn_iff, id_eq,
      funext_iff]
  simp only [PMF.map_apply, h, tsum_ite_eq]

/-- Every fixed-width check accepts with the product probability of independent uniform rows. -/
theorem uniformList_all_listRow_true (count width : ℕ) (check : List Bool → Bool) :
    ((uniformList (count * width)).map
      (fun word => (List.range count).all fun i => check (listRow width i word))) true =
      ((uniformList width).map check true) ^ count := by
  have hrows : (uniformList (count * width)).map
      (fun word => (List.range count).all fun i => check (listRow width i word)) =
      (PMF.uniformOfFintype (Fin count → BitString width)).map
        (fun rows => (List.ofFn fun i => check (List.ofFn (rows i))).all id) := by
    have h := congrArg (PMF.map (fun rows : List (List Bool) => rows.all check))
      (uniformList_listRows count width)
    have hall (rows : Fin count → BitString width) :
        (List.ofFn fun i => check (List.ofFn (rows i))).all id =
          (List.ofFn fun i => List.ofFn (rows i)).all check := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, List.forall_mem_ofFn_iff, id_eq]
    simpa only [PMF.map_comp, Function.comp_def, listRows, List.all_map, hall] using h
  rw [hrows, ← PMF.pi_uniformOfFintype]
  have h := congrArg (fun p : PMF (Fin count → Bool) =>
      (p.map (fun bits => (List.ofFn bits).all id)) true)
    (PMF.pi_map (fun _ : Fin count => PMF.uniformOfFintype (BitString width))
      (fun _ bits => check (List.ofFn bits)))
  simpa only [map_all_ofFn_true, PMF.pi_apply, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, uniformList, PMF.map_comp, Function.comp_def] using h.symm

end Cslib.BitString

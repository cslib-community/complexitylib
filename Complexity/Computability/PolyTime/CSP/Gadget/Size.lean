/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CSP.Gadget
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Linear combinatorial size of fixed-gadget replacement

Relabeling preserves constraint counts and variable-occurrence counts. Each input constraint
therefore contributes exactly the fixed size of its chosen template. The number of distinct
output variables is at most the number of output occurrences. For a finite source alphabet,
the guarded compiler has a uniform linear bound on output variables plus constraints, including
malformed inputs and the empty instance.

These are combinatorial counts, not binary encoding lengths. Fresh variable names contain
constraint indices, so the binary encoding may incur an additional logarithmic factor.

## Main results

* `Cslib.Logic.PL.CSP.length_replaceGadgets`: exact output constraint count.
* `Cslib.Logic.PL.CSP.vars_length_replaceGadgets`: exact output occurrence count.
* `Cslib.Logic.PL.CSP.exists_linear_bound_replaceGadgetsGuarded`: the guarded linear bound.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Src Rel : Type}

/-- Each source constraint contributes exactly the constraints in its fixed template. -/
theorem length_replaceGadgets (B : ℕ) (templates : Src → CSP Rel (Bool × ℕ))
    (F : CSP Src ℕ) :
    (replaceGadgets B templates F).length = (F.map fun c => (templates c.1).length).sum := by
  rw [replaceGadgets, List.length_flatMap]
  conv_rhs => rw [← List.zipIdx_map_fst 0 F, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp [instantiate, relabel]

/-- Relabeling template ports preserves their occurrence count, even when ports coincide. -/
theorem vars_length_replaceGadgets (B : ℕ) (templates : Src → CSP Rel (Bool × ℕ))
    (F : CSP Src ℕ) :
    (replaceGadgets B templates F).vars.length =
      (F.map fun c => (templates c.1).vars.length).sum := by
  change ((F.zipIdx.flatMap fun p => instantiate B p.2 p.1.2 (templates p.1.1)).flatMap
    Prod.snd).length = _
  rw [List.flatMap_assoc, List.length_flatMap]
  conv_rhs => rw [← List.zipIdx_map_fst 0 F, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  change (instantiate B p.2 p.1.2 (templates p.1.1)).vars.length = _
  simp only [instantiate, vars_relabel, List.length_map, Function.comp_apply]

/-- A bound on template occurrences plus constraints bounds distinct output variables plus
constraints. No freshness or well-formedness assumption is needed for this size inequality. -/
theorem numVars_add_length_replaceGadgets_le (B : ℕ)
    (templates : Src → CSP Rel (Bool × ℕ)) (K : ℕ)
    (hK : ∀ r, (templates r).vars.length + (templates r).length ≤ K) (F : CSP Src ℕ) :
    (replaceGadgets B templates F).numVars + (replaceGadgets B templates F).length ≤
      K * F.length := by
  have hn : (replaceGadgets B templates F).numVars ≤
      (replaceGadgets B templates F).vars.length := List.toFinset_card_le _
  calc
    _ ≤ (replaceGadgets B templates F).vars.length +
        (replaceGadgets B templates F).length := Nat.add_le_add_right hn _
    _ = (F.map fun c => (templates c.1).vars.length + (templates c.1).length).sum := by
      rw [vars_length_replaceGadgets, length_replaceGadgets, List.sum_map_add]
    _ ≤ K * F.length := by
      have h := List.sum_le_sum (l := F) (g := fun _ => K) (fun c _ => hK c.1)
      simpa [Nat.mul_comm] using h

/-- Fixed finite template lookup and a fixed malformed-input reject instance give a linear
bound on distinct output variables plus constraints, for every raw input. The constant is
independent of the input and of its numeric variable labels. -/
theorem exists_linear_bound_replaceGadgetsGuarded [Finite Src]
    (srcArity : Src → ℕ) (B : ℕ) (templates : Src → CSP Rel (Bool × ℕ))
    (reject : CSP Rel ℕ) :
    ∃ C : ℕ, ∀ F : CSP Src ℕ,
      (replaceGadgetsGuarded srcArity B templates reject F).numVars +
        (replaceGadgetsGuarded srcArity B templates reject F).length ≤ C * F.length := by
  classical
  let _ : Fintype Src := Fintype.ofFinite Src
  let K := Finset.univ.sup fun r => (templates r).vars.length + (templates r).length
  have hK (r) : (templates r).vars.length + (templates r).length ≤ K :=
    Finset.le_sup (f := fun r => (templates r).vars.length + (templates r).length)
      (Finset.mem_univ r)
  let C := max K (reject.numVars + reject.length)
  refine ⟨C, fun F => ?_⟩
  unfold replaceGadgetsGuarded
  split
  · exact (numVars_add_length_replaceGadgets_le B templates K hK F).trans
      (Nat.mul_le_mul_right F.length (Nat.le_max_left _ _))
  · rename_i hvalid
    have hlen : 1 ≤ F.length := by
      cases F with
      | nil => exact (hvalid rfl).elim
      | cons c F => simp
    exact (Nat.le_max_right K (reject.numVars + reject.length)).trans
      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left C hlen)

end Cslib.Logic.PL.CSP

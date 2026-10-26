/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathAssignments
public import Complexity.Computability.Complexity.Problems.SAT.Planar.Compile
public import Complexity.Logics.Propositional.CNF.Planar.DirectedWire
import Mathlib.Data.List.GetD
import Mathlib.Tactic.SplitIfs

/-!
# Logical semantics of the actual finite planar SAT compiler

This module connects the executable placed clauses to ordinary CNF evaluation and the generic
polarity-directed wire rules. Logical conditions are kept explicit until discharged for the
actual incidence paths. No geometric planarity or machine-time claim is made here.

## Main definitions

The compiler data are defined in `PlanarCompile`; this module introduces no second compiler.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.eval_rawFormula_iff`: actual output block semantics.
* `Cslib.Complexity.SAT.PlanarCompile.crossing_boundary_eq`: opposite ports of selected sites agree.

## References

The finite assembly and its logical composition proofs are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- Forgetting geometric data gives exactly the renamed fixed crossover clauses. -/
theorem map_fst_crossingClauses (p : Point) :
    (crossingClauses p).map Prod.fst =
      Crossover.splitFormula.relabel (fun v => (p, some v)) := by
  change (Crossover.splitFormula.zipIdx.map fun c =>
    c.1.relabel (fun v => (p, some v))) = _
  calc
    _ = (Crossover.splitFormula.zipIdx.map Prod.fst).map
        (Clause.relabel (fun v => (p, some v))) := by rw [List.map_map]; rfl
    _ = _ := by rw [List.zipIdx_map_fst]; rfl

/-- The structured output is the original-clause, crossover, and directed-link blocks. -/
theorem rawFormula_eq (φ : CNF ℕ) :
    rawFormula φ =
      ((originalClauses φ (crossingSites φ)).map Prod.fst) ++
      ((crossingSites φ).flatMap fun p =>
        Crossover.splitFormula.relabel (fun v => (p, some v))) ++
      ((Cslib.Logic.PL.occurrences φ).flatMap fun o =>
        (links (crossingSites φ) o.2.2.2 (occurrencePath φ o)).map Prod.fst) := by
  simp only [rawFormula, placedClauses, List.map_append, List.map_flatMap]
  simp_rw [map_fst_crossingClauses]

/-- Evaluating the actual output checks exactly its three clause blocks. -/
theorem eval_rawFormula_iff (φ : CNF ℕ) (σ : Variable → Bool) :
    (rawFormula φ).eval σ = true ↔
      CNF.eval σ ((originalClauses φ (crossingSites φ)).map Prod.fst) = true ∧
      (∀ p ∈ crossingSites φ, Crossover.splitFormula.eval (fun v => σ (p, some v)) = true) ∧
      ∀ o ∈ Cslib.Logic.PL.occurrences φ,
        CNF.eval σ
          ((links (crossingSites φ) o.2.2.2 (occurrencePath φ o)).map Prod.fst) = true := by
  rw [rawFormula_eq]
  simp only [eval_append, Bool.and_eq_true, eval_flatMap_eq_true_iff, eval_relabel, and_assoc,
    Function.comp_def]

/-- Every selected site's actual crossover clauses force its opposite terminal values to agree. -/
theorem crossing_boundary_eq {φ : CNF ℕ} {σ : Variable → Bool}
    (h : (rawFormula φ).eval σ = true) {p : Point} (hp : p ∈ crossingSites φ) :
    σ (p, some .aLeft) = σ (p, some .aRight) ∧
      σ (p, some .bTop) = σ (p, some .bBottom) :=
  Crossover.split_boundary_eq_of_holds (((eval_rawFormula_iff φ σ).1 h).2.1 p hp)

/-- The placed intercell clauses are exactly the generic polarity-directed wire clauses. -/
theorem map_fst_links (sites : List Point) (b : Bool) (r : Route) :
    (links sites b r).map Prod.fst = CNF.DirectedWire.links b (wire sites r) := by
  apply List.ext_getElem
  · simp [links, CNF.DirectedWire.links, wire, List.consecutivePairs]
  · intro i hi hj
    have hi' : i + 2 < r.length := by
      simp only [links, List.length_map, List.consecutivePairs, List.length_zip,
        List.length_tail, List.length_dropLast] at hi
      omega
    simp only [links, CNF.DirectedWire.links, List.getElem_map, List.consecutivePairs,
      List.getElem_zip, List.getElem_tail]
    rw [getElem_wire sites r i (by omega), getElem_wire sites r (i + 1) (by omega)]
    simp only [List.getElem_dropLast]
    have hn : r.getD (i + 1) r[i] = r[i + 1] := List.getD_eq_getElem _ _ (by omega)
    have hp : r.getD (i + 1 - 1) r[i + 1] = r[i] := by
      rw [Nat.add_sub_cancel, List.getD_eq_getElem _ _ (by omega)]
    simp only [hn, hp]
    cases b <;> rfl

private theorem lastD_eq_getElem {α : Type*} (xs : List α) (d : α) (hne : xs ≠ []) :
    xs.getLastD d = xs[xs.length - 1]'(by cases xs <;> simp_all) := by
  induction xs generalizing d with
  | nil => exact False.elim (hne rfl)
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      rw [List.getLastD_cons, ih a (List.cons_ne_nil _ _)]
      simp only [List.length_cons, Nat.add_sub_cancel, List.getElem_cons_succ]

/-- The final exit of the executable cell list is the variable used by its original literal. -/
theorem last_exit_eq_lastLiteral (sites : List Point) (r : Route) (b : Bool)
    (fallback : Variable) (hlen : 2 ≤ r.length) :
    ((wire sites r).getLastD (fallback, fallback)).2 = (lastLiteral sites r b).1.1 := by
  rw [lastD_eq_getElem _ _ (wire_ne_nil sites r hlen)]
  have hi : (wire sites r).length - 1 < r.length - 1 := by rw [length_wire]; omega
  rw [getElem_wire sites r _ hi]
  simp only [length_wire]
  unfold lastLiteral
  have hp : r.getD (r.length - 2) (0, 0) = r[r.length - 1 - 1] := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    congr 1
  have hn : r.getLastD (0, 0) = r[r.length - 1] := by
    rw [lastD_eq_getElem]
    intro h
    simp [h] at hlen
  simp only [hp, hn]
  congr 1
  rw [List.getD_eq_getElem _ _ (by omega)]
  congr 1
  omega

/-- Opposite horizontal ports of a selected cell carry the same signal. -/
theorem horizontal_signal_eq {φ : CNF ℕ} {σ : Variable → Bool}
    (h : (rawFormula φ).eval σ = true) {p : Point} (hp : p ∈ crossingSites φ) :
    σ (signal (crossingSites φ) p (p - (1, 0))) =
      σ (signal (crossingSites φ) p (p + (1, 0))) := by
  have hleft : side p (p - (1, 0)) = 0 := by
    rcases p with ⟨x, y⟩
    simp only [side, Prod.fst_sub, Prod.snd_sub]
    split_ifs <;> first | rfl | omega
  have hright : side p (p + (1, 0)) = 1 := by
    rcases p with ⟨x, y⟩
    simp only [side, Prod.fst_add, Prod.snd_add]
    split_ifs <;> first | rfl | omega
  simpa only [signal, hp, ite_true, hleft, hright, Crossover.splitTerminal] using
    (crossing_boundary_eq h hp).1

/-- Opposite vertical ports of a selected cell carry the same signal. -/
theorem vertical_signal_eq {φ : CNF ℕ} {σ : Variable → Bool}
    (h : (rawFormula φ).eval σ = true) {p : Point} (hp : p ∈ crossingSites φ) :
    σ (signal (crossingSites φ) p (p - (0, 1))) =
      σ (signal (crossingSites φ) p (p + (0, 1))) := by
  have hbottom : side p (p - (0, 1)) = 2 := by
    rcases p with ⟨x, y⟩
    simp only [side, Prod.fst_sub, Prod.snd_sub]
    split_ifs <;> first | rfl | omega
  have htop : side p (p + (0, 1)) = 3 := by
    rcases p with ⟨x, y⟩
    simp only [side, Prod.fst_add, Prod.snd_add]
    split_ifs <;> first | rfl | omega
  simpa only [signal, hp, ite_true, hbottom, htop, Crossover.splitTerminal] using
    (crossing_boundary_eq h hp).2

/-- The original placed clauses use exactly the endpoint variables of the generic wires. -/
theorem map_fst_originalClauses (φ : CNF ℕ) (sites : List Point) (fallback : Variable)
    (hpaths : ∀ o ∈ Cslib.Logic.PL.occurrences φ, 2 ≤ (occurrencePath φ o).length) :
    (originalClauses φ sites).map Prod.fst =
      DirectedWire.replacementClauses φ (fun o => wire sites (occurrencePath φ o)) fallback := by
  simp only [originalClauses, DirectedWire.replacementClauses, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro c hc
  apply List.map_congr_left
  intro l hl
  have ho : (c.2, l.2, l.1) ∈ Cslib.Logic.PL.occurrences φ :=
    List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨l, hl, rfl⟩⟩
  apply Prod.ext
  · exact (last_exit_eq_lastLiteral sites _ l.1.2 fallback (hpaths _ ho)).symm
  · rfl

/-- Actual raw output satisfaction projects to the source once the actual path endpoint and
cell-value conditions are proved. These are logical obligations, not assumed planarity. -/
theorem eval_rawFormula_sound_of_cells (φ : CNF ℕ) (τ : ℕ → Bool) (σ : Variable → Bool)
    (hpaths : ∀ o ∈ Cslib.Logic.PL.occurrences φ, 2 ≤ (occurrencePath φ o).length)
    (hcells : ∀ o ∈ Cslib.Logic.PL.occurrences φ,
      ∀ c ∈ wire (crossingSites φ) (occurrencePath φ o), σ c.1 = σ c.2)
    (hfirst : ∀ o ∈ Cslib.Logic.PL.occurrences φ,
      σ ((wire (crossingSites φ) (occurrencePath φ o)).headD
        (((0, 0), none), ((0, 0), none))).1 = τ o.2.2.1)
    (h : (rawFormula φ).eval σ = true) : φ.eval τ = true := by
  have he := (eval_rawFormula_iff φ σ).1 h
  apply DirectedWire.eval_assemble_sound φ
    (fun o => wire (crossingSites φ) (occurrencePath φ o)) ((0, 0), none) τ σ
  · intro o ho
    exact wire_ne_nil _ _ (hpaths o ho)
  · exact hcells
  · exact hfirst
  · rw [DirectedWire.assemble, eval_append, Bool.and_eq_true]
    constructor
    · rw [← map_fst_originalClauses φ (crossingSites φ) ((0, 0), none) hpaths]
      exact he.1
    · apply (DirectedWire.eval_allLinks_iff φ _ σ).2
      intro o ho
      rw [← map_fst_links]
      exact he.2.2 o ho

/-- A compatible assignment satisfying the actual selected crossover blocks satisfies the
actual raw output whenever the source formula holds. Existence and compatibility of this
assignment are separate obligations. -/
theorem eval_rawFormula_complete_of_compatible (φ : CNF ℕ) (τ : ℕ → Bool)
    (σ : Variable → Bool)
    (hpaths : ∀ o ∈ Cslib.Logic.PL.occurrences φ, 2 ≤ (occurrencePath φ o).length)
    (hcompat : ∀ o ∈ Cslib.Logic.PL.occurrences φ,
      ∀ c ∈ wire (crossingSites φ) (occurrencePath φ o),
        σ c.1 = τ o.2.2.1 ∧ σ c.2 = τ o.2.2.1)
    (hcross : ∀ p ∈ crossingSites φ,
      Crossover.splitFormula.eval (fun v => σ (p, some v)) = true)
    (h : φ.eval τ = true) : (rawFormula φ).eval σ = true := by
  have he := DirectedWire.eval_assemble_complete φ
    (fun o => wire (crossingSites φ) (occurrencePath φ o)) ((0, 0), none) τ σ
    (fun o ho => wire_ne_nil _ _ (hpaths o ho)) hcompat h
  rw [DirectedWire.assemble, eval_append, Bool.and_eq_true] at he
  apply (eval_rawFormula_iff φ σ).2
  refine ⟨?_, hcross, ?_⟩
  · rw [map_fst_originalClauses φ (crossingSites φ) ((0, 0), none) hpaths]
    exact he.1
  · intro o ho
    rw [map_fst_links]
    exact (DirectedWire.eval_allLinks_iff φ _ σ).1 he.2 o ho

end Cslib.Complexity.SAT.PlanarCompile

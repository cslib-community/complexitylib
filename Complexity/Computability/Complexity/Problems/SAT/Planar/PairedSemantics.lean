/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedCompile
public import Complexity.Logics.Propositional.CNF.Planar.PairedWire
import Complexity.Logics.Propositional.CNF.Planar.CrossoverCounting
public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathAssignments
import Complexity.Foundations.Data.List.Last
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases

/-!
# Assignment semantics of the paired compiler

The actual clause blocks use ordinary CNF evaluation. Local rings and crossovers identify the
four wire values within each cell; paired links identify consecutive cell values. The source
assignment then determines every used output variable.

## Main definitions

* `Cslib.Complexity.SAT.ParsimoniousPlanar.wire`: the actual two-lane entry and exit variables.

## Main results

* `Cslib.Complexity.SAT.ParsimoniousPlanar.eval_rawFormula_iff`: exact clause-block semantics.

## References

These are original composition proofs for the finite paired compiler.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ParsimoniousPlanar

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- Every retained point contributes the entry and exit on each of its two lanes. -/
def wire (sites : List Point) (r : Route) : List (PairedWire.Cell Variable) :=
  r.dropLast.zipIdx.map fun (p, i) lane =>
    (signal sites p (r.getD (i - 1) p) lane, signal sites p (r.getD (i + 1) p) lane)

/-- A point receives an ordinary ring exactly when a retained path uses it outside a crossing. -/
theorem mem_ordinaryCells (φ : CNF ℕ) (p : Point) :
    p ∈ ordinaryCells φ ↔
      (∃ r ∈ paths φ, p ∈ r.dropLast) ∧ p ∉ crossingSites φ := by
  simp [ordinaryCells, mem_selectDistinct_replicate, List.mem_flatMap]

/-- No ordinary ring is emitted twice. -/
theorem ordinaryCells_nodup (φ : CNF ℕ) : (ordinaryCells φ).Nodup :=
  nodup_selectDistinct _ _

/-- The two local clause tables retain their exact formulas under variable tagging. -/
theorem map_fst_ordinaryClauses (p : Point) :
    (ordinaryClauses p).map Prod.fst =
      OrdinaryRing.formula.relabel (fun v => ((p, Sum.inl v) : Variable)) := by
  change (OrdinaryRing.formula.zipIdx.map fun c =>
    c.1.relabel (fun v => ((p, Sum.inl v) : Variable))) = _
  calc
    _ = (OrdinaryRing.formula.zipIdx.map Prod.fst).map
        (Clause.relabel (fun v => ((p, Sum.inl v) : Variable))) := by rw [List.map_map]; rfl
    _ = _ := by rw [List.zipIdx_map_fst]; rfl

/-- The crossover clause table is exactly the renamed paired-port formula. -/
theorem map_fst_crossingClauses (p : Point) :
    (crossingClauses p).map Prod.fst =
      PairedCrossover.formula.relabel (fun v => ((p, Sum.inr v) : Variable)) := by
  change (PairedCrossover.formula.zipIdx.map fun c =>
    c.1.relabel (fun v => ((p, Sum.inr v) : Variable))) = _
  calc
    _ = (PairedCrossover.formula.zipIdx.map Prod.fst).map
        (Clause.relabel (fun v => ((p, Sum.inr v) : Variable))) := by rw [List.map_map]; rfl
    _ = _ := by rw [List.zipIdx_map_fst]; rfl

/-- The emitted formula evaluates precisely its original, ordinary, crossing, and link blocks. -/
theorem eval_rawFormula_iff (φ : CNF ℕ) (σ : Variable → Bool) :
    (rawFormula φ).eval σ = true ↔
      CNF.eval σ ((originalClauses φ (crossingSites φ)).map Prod.fst) = true ∧
      (∀ p ∈ ordinaryCells φ,
        OrdinaryRing.formula.eval (fun v => σ (p, Sum.inl v)) = true) ∧
      (∀ p ∈ crossingSites φ,
        PairedCrossover.formula.eval (fun v => σ (p, Sum.inr v)) = true) ∧
      ∀ o ∈ Cslib.Logic.PL.occurrences φ,
        CNF.eval σ ((links (crossingSites φ) (occurrencePath φ o)).map Prod.fst) = true := by
  simp only [rawFormula, placedClauses, List.map_append, List.map_flatMap]
  simp_rw [map_fst_ordinaryClauses, map_fst_crossingClauses]
  simp only [eval_append, Bool.and_eq_true, eval_flatMap_eq_true_iff, eval_relabel,
    Function.comp_def, and_assoc]

/-- Ordinary cell ports all carry the same value. -/
theorem ordinary_port_value {φ : CNF ℕ} {σ : Variable → Bool}
    (h : (rawFormula φ).eval σ = true) {p : Point} (hp : p ∈ ordinaryCells φ)
    (s : Fin 4) (lane : Fin 2) :
    σ (port (crossingSites φ) p s lane) = σ (p, Sum.inl (0, 0)) := by
  have hn := ((mem_ordinaryCells φ p).1 hp).2
  have hr := ((eval_rawFormula_iff φ σ).1 h).2.1 p hp
  simpa only [port, hn, ↓reduceIte] using (OrdinaryRing.eval_formula_iff _).1 hr (s, lane)

/-- A crossing port carries the horizontal or vertical incoming value, independently of lane. -/
theorem crossing_port_value {φ : CNF ℕ} {σ : Variable → Bool}
    (h : (rawFormula φ).eval σ = true) {p : Point} (hp : p ∈ crossingSites φ)
    (s : Fin 4) (lane : Fin 2) :
    σ (port (crossingSites φ) p s lane) =
      if s.val < 2 then σ (p, Sum.inr (PairedCrossover.terminal 0 0))
      else σ (p, Sum.inr (PairedCrossover.terminal 2 0)) := by
  have hr := ((eval_rawFormula_iff φ σ).1 h).2.2.1 p hp
  simpa only [port, hp, ↓reduceIte] using PairedCrossover.terminal_value_of_holds hr s lane

/-- The paired wire has one cell for each retained path point. -/
theorem length_wire (sites : List Point) (r : Route) : (wire sites r).length = r.length - 1 := by
  simp [wire]

/-- The actual entry and exit variables at a retained path index. -/
theorem getElem_wire (sites : List Point) (r : Route) (i : ℕ) (hi : i < r.length - 1) :
    (wire sites r)[i]'(by simpa [wire] using hi) = fun lane =>
      (signal sites r[i] (r.getD (i - 1) r[i]) lane,
        signal sites r[i] (r.getD (i + 1) r[i]) lane) := by
  simp only [wire, List.getElem_map, List.getElem_zipIdx, Nat.zero_add, List.getElem_dropLast]

/-- An actual occurrence selects a member of the canonical path list. -/
theorem occurrencePath_mem_paths {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) : occurrencePath φ o ∈ paths φ := by
  change PlanarCompile.occurrencePath φ o ∈ PlanarCompile.paths φ
  rw [← PlanarCompile.occurrencePaths_eq_paths]
  exact List.mem_map_of_mem ho

/-- The side lookup recovers each cardinal neighbor's side. -/
theorem side_neighbor (p : Point) (s : Fin 4) :
    side p (p + PairedPorts.neighbor s) = s := by
  rcases p with ⟨x, y⟩
  fin_cases s <;> simp [side, PlanarCompile.side, PairedPorts.neighbor]

/-- All four actual entry and exit values within each retained wire cell agree. -/
theorem wire_cells_agree {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {σ : Variable → Bool} (h : (rawFormula φ).eval σ = true) :
    ∀ o ∈ Cslib.Logic.PL.occurrences φ,
      ∀ c ∈ wire (crossingSites φ) (occurrencePath φ o), c.Agree σ := by
  intro o ho c hc
  unfold wire at hc
  obtain ⟨⟨p, k⟩, hpk, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hk, heq⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hpk)
  change (occurrencePath φ o).dropLast[k] = p at heq
  have hk' : k < (occurrencePath φ o).length := by
    simp only [List.length_dropLast] at hk
    omega
  have heq' : (occurrencePath φ o)[k] = p := by
    rw [← List.getElem_dropLast hk]
    exact heq
  have hpo : p ∈ occurrencePath φ o := heq' ▸ List.getElem_mem hk'
  have hpod : p ∈ (occurrencePath φ o).dropLast := by
    rw [← heq]
    exact List.getElem_mem hk
  by_cases hp : p ∈ crossingSites φ
  · have hl : side p (p - (1, 0)) = 0 := by
      simpa [PairedPorts.neighbor, sub_eq_add_neg] using side_neighbor p 0
    have hr : side p (p + (1, 0)) = 1 := by
      simpa [PairedPorts.neighbor, sub_eq_add_neg] using side_neighbor p 1
    have hb : side p (p - (0, 1)) = 2 := by
      simpa [PairedPorts.neighbor, sub_eq_add_neg] using side_neighbor p 2
    have ht : side p (p + (0, 1)) = 3 := by
      simpa [PairedPorts.neighbor, sub_eq_add_neg] using side_neighbor p 3
    rcases PlanarCompile.occurrencePath_crossing_straight hw hv ho hp hpo with hs | hs
    · obtain ⟨_, _, hnb⟩ := hs.getD_neighbors (PlanarCompile.occurrencePath_nodup ho) hk' heq'
      rcases hnb with ⟨hprev, hnext⟩ | ⟨hprev, hnext⟩
      all_goals
        simp only [PairedWire.Cell.Agree, hprev, hnext, signal, hl, hr]
        intro lane
        rw [crossing_port_value h hp, crossing_port_value h hp, crossing_port_value h hp]
        simp
    · obtain ⟨_, _, hnb⟩ := hs.getD_neighbors (PlanarCompile.occurrencePath_nodup ho) hk' heq'
      rcases hnb with ⟨hprev, hnext⟩ | ⟨hprev, hnext⟩
      all_goals
        simp only [PairedWire.Cell.Agree, hprev, hnext, signal, hb, ht]
        intro lane
        rw [crossing_port_value h hp, crossing_port_value h hp, crossing_port_value h hp]
        simp
  · have hord : p ∈ ordinaryCells φ :=
      (mem_ordinaryCells φ p).2 ⟨⟨_, occurrencePath_mem_paths ho, hpod⟩, hp⟩
    intro lane
    change σ (signal _ _ _ lane) = σ (signal _ _ _ 0) ∧
      σ (signal _ _ _ lane) = σ (signal _ _ _ 0)
    simp [signal, ordinary_port_value h hord]

/-- Forgetting geometric annotations gives the generic paired-wire links exactly. -/
theorem map_fst_links (sites : List Point) (r : Route) :
    (links sites r).map Prod.fst = PairedWire.links (wire sites r) := by
  simp only [links, List.map_flatMap, List.map_cons, List.map_nil, PairedWire.links]
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  apply List.ext_getElem
  · simp [wire, List.consecutivePairs]
  · intro i hi hj
    have hi' : i + 2 < r.length := by
      simp only [List.length_map, List.consecutivePairs, List.length_zip,
        List.length_tail, List.length_dropLast] at hi
      omega
    simp only [List.getElem_map, List.consecutivePairs, List.getElem_zip, List.getElem_tail]
    rw [getElem_wire sites r i (by omega), getElem_wire sites r (i + 1) (by omega)]
    simp only [List.getElem_dropLast]
    have hn : r.getD (i + 1) r[i] = r[i + 1] := List.getD_eq_getElem _ _ (by omega)
    have hp : r.getD (i + 1 - 1) r[i + 1] = r[i] := by
      rw [Nat.add_sub_cancel, List.getD_eq_getElem _ _ (by omega)]
    simp only [hn, hp]
    rfl

/-- The source value is read at one fixed port of its ordinary source cell. -/
def sourceValue (φ : CNF ℕ) (σ : Variable → Bool) (v : ℕ) : Bool :=
  σ (Layout.center (φ.distinctVars.idxOf v), Sum.inl (0, 0))

/-- Actual occurrence wires are nonempty. -/
theorem wire_ne_nil {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    wire (crossingSites φ) (occurrencePath φ o) ≠ [] := by
  have hlen := PlanarCompile.occurrencePath_length_ge_two ho
  change 2 ≤ (occurrencePath φ o).length at hlen
  intro he
  have hw := length_wire (crossingSites φ) (occurrencePath φ o)
  rw [he, List.length_nil] at hw
  omega

/-- The actual first entry has the source cell's value. -/
theorem wire_first_value {φ : CNF ℕ} {σ : Variable → Bool}
    (h : (rawFormula φ).eval σ = true) {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) (fallback : PairedWire.Cell Variable) :
    σ (((wire (crossingSites φ) (occurrencePath φ o)).headD fallback 0).1) =
      sourceValue φ σ o.2.2.1 := by
  have hlen := PlanarCompile.occurrencePath_length_ge_two ho
  change 2 ≤ (occurrencePath φ o).length at hlen
  have hwpos : 0 < (wire (crossingSites φ) (occurrencePath φ o)).length := by
    rw [length_wire]
    omega
  have hhead : (wire (crossingSites φ) (occurrencePath φ o)).headD fallback =
      (wire (crossingSites φ) (occurrencePath φ o))[0] := by
    generalize hc : wire (crossingSites φ) (occurrencePath φ o) = xs at hwpos ⊢
    cases xs with
    | nil => simp at hwpos
    | cons a rest => rfl
  have hp := (PlanarCompile.occurrencePath_endpoints ho).1
  change (occurrencePath φ o).head? = _ at hp
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hp
  have hp' : (occurrencePath φ o)[0] = Layout.center (φ.distinctVars.idxOf o.2.2.1) :=
    Option.some.inj hp
  have hret : Layout.center (φ.distinctVars.idxOf o.2.2.1) ∈
      (occurrencePath φ o).dropLast := by
    rw [← hp']
    have hdrop : 0 < (occurrencePath φ o).dropLast.length := by
      simp only [List.length_dropLast]
      omega
    rw [← List.getElem_dropLast hdrop]
    exact List.getElem_mem _
  have hord := (mem_ordinaryCells φ _).2
    ⟨⟨_, occurrencePath_mem_paths ho, hret⟩, PlanarCompile.source_center_not_crossing ho⟩
  rw [hhead, getElem_wire _ _ 0 (by omega)]
  simp only [Nat.zero_sub]
  rw [List.getD_eq_getElem _ _ (by omega), hp']
  exact ordinary_port_value h hord _ 0

/-- Every actual entry and exit along an occurrence wire has exactly its source value. -/
theorem wire_values_source {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {σ : Variable → Bool} (h : (rawFormula φ).eval σ = true)
    {o : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    ∀ c ∈ wire (crossingSites φ) (occurrencePath φ o), ∀ lane,
      σ (c lane).1 = sourceValue φ σ o.2.2.1 ∧
        σ (c lane).2 = sourceValue φ σ o.2.2.1 := by
  let fallback : PairedWire.Cell Variable := fun _ => (((0, 0), Sum.inl (0, 0)),
    ((0, 0), Sum.inl (0, 0)))
  have hl := ((eval_rawFormula_iff φ σ).1 h).2.2.2 o ho
  rw [map_fst_links] at hl
  have he := PairedWire.agree_head_of_ne_nil σ fallback _ (wire_ne_nil ho)
    (wire_cells_agree hw hv h o ho) hl
  rwa [wire_first_value h ho fallback] at he

/-- Constant values along a nonempty retained wire determine its final literal. -/
theorem lastLiteral_value_of_wire (sites : List Point) (r : Route) (positive value : Bool)
    (σ : Variable → Bool) (hlen : 2 ≤ r.length)
    (hcompat : ∀ c ∈ wire sites r, ∀ lane,
      σ (c lane).1 = value ∧ σ (c lane).2 = value) :
    σ (lastLiteral sites r positive).1.1 = value := by
  have hi : r.length - 2 < r.length - 1 := by omega
  have hwi : r.length - 2 < (wire sites r).length := by rwa [length_wire]
  have hc := hcompat _ (List.getElem_mem hwi)
  rw [getElem_wire _ _ _ hi] at hc
  have hnext : r.length - 2 + 1 = r.length - 1 := by omega
  have hget (d : Point) : r.getD (r.length - 1) d = r[r.length - 1] :=
    List.getD_eq_getElem _ _ (by omega)
  simp only [hnext, hget] at hc
  have hne : r ≠ [] := by intro he; rw [he] at hlen; simp at hlen
  unfold lastLiteral
  rw [List.getD_eq_getElem _ _ (by omega), List.getLastD_eq_getElem _ _ hne]
  exact (hc _).2

/-- The literal emitted at an occurrence has precisely its source variable's value. -/
theorem lastLiteral_value {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {σ : Variable → Bool} (h : (rawFormula φ).eval σ = true)
    {o : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    σ (lastLiteral (crossingSites φ) (occurrencePath φ o) o.2.2.2).1.1 =
      sourceValue φ σ o.2.2.1 :=
  lastLiteral_value_of_wire _ _ _ _ σ (PlanarCompile.occurrencePath_length_ge_two ho)
    (wire_values_source hw hv h ho)

/-- Replacing occurrence variables by equal-valued endpoint variables preserves evaluation. -/
theorem eval_originalClauses_of_values (φ : CNF ℕ) (sites : List Point)
    (σ : Variable → Bool) (τ : ℕ → Bool)
    (hvalues : ∀ o ∈ Cslib.Logic.PL.occurrences φ,
      σ (lastLiteral sites (occurrencePath φ o) o.2.2.2).1.1 = τ o.2.2.1) :
    CNF.eval σ ((originalClauses φ sites).map Prod.fst) = φ.eval τ := by
  have hc (c : Clause ℕ × ℕ) (hc : c ∈ φ.zipIdx) :
      Clause.eval σ (c.1.zipIdx.map fun l =>
        (lastLiteral sites (occurrencePath φ (c.2, l.2, l.1)) l.1.2).1) =
          c.1.eval τ := by
    have hm :
        (c.1.zipIdx.map fun l =>
          (lastLiteral sites (occurrencePath φ (c.2, l.2, l.1)) l.1.2).1).map
            (Literal.eval σ) = c.1.map (Literal.eval τ) := by
      calc
        _ = c.1.zipIdx.map (fun l => Literal.eval τ l.1) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro l hl
          have ho : (c.2, l.2, l.1) ∈ Cslib.Logic.PL.occurrences φ :=
            List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨l, hl, rfl⟩⟩
          simp only [Function.comp_def, Literal.eval]
          rw [hvalues _ ho]
          rfl
        _ = (c.1.zipIdx.map Prod.fst).map (Literal.eval τ) := by rw [List.map_map]; rfl
        _ = _ := by rw [List.zipIdx_map_fst]
    have he := congrArg (fun bs : List Bool => bs.any id) hm
    simpa only [List.any_map, Function.comp_def, id_eq, Clause.eval] using he
  have hm : ((originalClauses φ sites).map Prod.fst).map (Clause.eval σ) =
      φ.map (Clause.eval τ) := by
    calc
      _ = φ.zipIdx.map (fun c => Clause.eval τ c.1) := by
        simp only [originalClauses, List.map_map, Function.comp_def]
        apply List.map_congr_left
        exact hc
      _ = (φ.zipIdx.map Prod.fst).map (Clause.eval τ) := by rw [List.map_map]; rfl
      _ = _ := by rw [List.zipIdx_map_fst]
  have he := congrArg (fun bs : List Bool => bs.all id) hm
  simpa only [List.all_map, Function.comp_def, id_eq, CNF.eval] using he

/-- Every satisfying output assignment projects to a satisfying source assignment. -/
theorem eval_source_of_rawFormula {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {σ : Variable → Bool} (h : (rawFormula φ).eval σ = true) :
    φ.eval (sourceValue φ σ) = true := by
  rw [← eval_originalClauses_of_values φ (crossingSites φ) σ (sourceValue φ σ)
    (fun _ ho => lastLiteral_value hw hv h ho)]
  exact ((eval_rawFormula_iff φ σ).1 h).1

/-- Lift compatible values on the original path cells to the new local templates. -/
def liftAssignment (σ : PlanarCompile.Variable → Bool) : Variable → Bool
  | (p, .inl _) => σ (p, none)
  | (p, .inr v) => PairedCrossover.canonicalExtension
      (σ (p, some .aLeft)) (σ (p, some .bTop)) v

/-- The lifted paired signal is the original signal on either lane. -/
theorem liftAssignment_signal (sites : List Point) (σ : PlanarCompile.Variable → Bool)
    (hcross : ∀ p ∈ sites, Crossover.splitFormula.eval (fun v => σ (p, some v)) = true)
    (p q : Point) (lane : Fin 2) :
    liftAssignment σ (signal sites p q lane) = σ (PlanarCompile.signal sites p q) := by
  by_cases hp : p ∈ sites
  · have heq := congrFun (Crossover.eq_canonicalSplitExtension_of_holds (hcross p hp))
      (Crossover.splitTerminal (side p q))
    simp only [signal, port, hp, ↓reduceIte, liftAssignment,
      PairedCrossover.terminal_values_canonicalExtension, PlanarCompile.signal]
    change (if (side p q).val < 2 then σ (p, some .aLeft) else σ (p, some .bTop)) =
      σ (p, some (Crossover.splitTerminal (side p q)))
    generalize hs : side p q = s at heq ⊢
    fin_cases s
    all_goals first
      | rfl
      | simpa [Crossover.splitTerminal, Crossover.canonicalSplitExtension,
          Crossover.canonicalExtension, Crossover.assignment, Function.comp_def,
          Crossover.SplitVariable.origin] using heq.symm
  · simp [signal, port, hp, liftAssignment, PlanarCompile.signal]

/-- Every source assignment has compatible values in every local template and on both lanes. -/
theorem exists_compatible_assignment {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) (τ : ℕ → Bool) :
    ∃ σ : Variable → Bool,
      (∀ o ∈ Cslib.Logic.PL.occurrences φ,
        ∀ c ∈ wire (crossingSites φ) (occurrencePath φ o), ∀ lane,
          σ (c lane).1 = τ o.2.2.1 ∧ σ (c lane).2 = τ o.2.2.1) ∧
      (∀ p ∈ ordinaryCells φ,
        OrdinaryRing.formula.eval (fun v => σ (p, Sum.inl v)) = true) ∧
      (∀ p ∈ crossingSites φ,
        PairedCrossover.formula.eval (fun v => σ (p, Sum.inr v)) = true) := by
  obtain ⟨σ, hcompat, hcross⟩ := PlanarCompile.exists_compatible_assignment hw hv τ
  refine ⟨liftAssignment σ, ?_, ?_, ?_⟩
  · intro o ho c hc lane
    unfold wire at hc
    obtain ⟨⟨p, k⟩, hpk, rfl⟩ := List.mem_map.mp hc
    dsimp only
    rw [liftAssignment_signal _ σ hcross, liftAssignment_signal _ σ hcross]
    apply hcompat o ho
      (PlanarCompile.signal (crossingSites φ) p ((occurrencePath φ o).getD (k - 1) p),
        PlanarCompile.signal (crossingSites φ) p ((occurrencePath φ o).getD (k + 1) p))
    exact List.mem_map.mpr ⟨(p, k), hpk, rfl⟩
  · intro p _
    exact OrdinaryRing.eval_constant _
  · intro p _
    exact PairedCrossover.eval_canonicalExtension _ _

/-- Compatible local assignments satisfy the actual output exactly when the source holds. -/
theorem eval_rawFormula_of_compatible {φ : CNF ℕ} (τ : ℕ → Bool) (σ : Variable → Bool)
    (hcompat : ∀ o ∈ Cslib.Logic.PL.occurrences φ,
      ∀ c ∈ wire (crossingSites φ) (occurrencePath φ o), ∀ lane,
        σ (c lane).1 = τ o.2.2.1 ∧ σ (c lane).2 = τ o.2.2.1)
    (hord : ∀ p ∈ ordinaryCells φ,
      OrdinaryRing.formula.eval (fun v => σ (p, Sum.inl v)) = true)
    (hcross : ∀ p ∈ crossingSites φ,
      PairedCrossover.formula.eval (fun v => σ (p, Sum.inr v)) = true)
    (h : φ.eval τ = true) : (rawFormula φ).eval σ = true := by
  apply (eval_rawFormula_iff φ σ).2
  refine ⟨?_, hord, hcross, ?_⟩
  · rw [eval_originalClauses_of_values φ (crossingSites φ) σ τ ?_]
    · exact h
    · intro o ho
      exact lastLiteral_value_of_wire _ _ _ _ σ
        (PlanarCompile.occurrencePath_length_ge_two ho) (hcompat o ho)
  · intro o ho
    rw [map_fst_links]
    exact PairedWire.eval_links_of_constant σ (τ o.2.2.1) _ (hcompat o ho)






end Cslib.Complexity.SAT.ParsimoniousPlanar

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ModelCount
public import Mathlib.Data.List.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Bool.Basic

/-!
# Directed wires for CNF substitution

A wire lists pairs of cell entry and exit variables, from its source to its clause. Local
constraints must equate the two values in each cell. One binary implication joins each exit
to the next entry. Positive literals direct that implication backwards; negative literals
direct it forwards. In either case, a true literal at the final exit implies the source literal.
Constant values satisfy every link.

These are conditional composition rules. They construct no layout and do not establish that
any particular generator satisfies the local equalities or endpoint conditions.

## Main definitions

* `Cslib.Logic.PL.CNF.DirectedWire.links`: one directed binary clause per cell gap.
* `Cslib.Logic.PL.CNF.DirectedWire.assemble`: endpoint clauses and links for indexed occurrences.

## Main results

* `Cslib.Logic.PL.CNF.DirectedWire.propagate`: literal truth propagates from final exit to entry.
* `Cslib.Logic.PL.CNF.DirectedWire.eval_links_of_constant`: constant signals satisfy the links.
* `Cslib.Logic.PL.CNF.DirectedWire.length_links`: exact clause count, including empty wires.
* `Cslib.Logic.PL.CNF.DirectedWire.eval_assemble_sound`: projection under local constraints.
* `Cslib.Logic.PL.CNF.DirectedWire.eval_assemble_complete`: compatibility-based completeness.
* `Cslib.Logic.PL.CNF.DirectedWire.length_assemble`,
  `Cslib.Logic.PL.CNF.DirectedWire.length_vars_assemble`: exact total resource counts.

## References

The polarity-directed composition and cell-pair construction are original.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.DirectedWire

variable {V W : Type*}

/-- A positive literal propagates truth backwards; a negative literal propagates falsity
backwards by a forward implication. This reuses the ordinary implication-clause constructor. -/
def link (b : Bool) (previous next : V) : Clause V :=
  if b then Clause.imp [next] previous else Clause.imp [previous] next

/-- One binary implication between each consecutive pair of cells, using its exit and entry. -/
def links (b : Bool) (cells : List (V × V)) : CNF V :=
  cells.consecutivePairs.map fun p => link b p.1.2 p.2.1

/-- A link enforces exactly the direction needed for its literal's truth. -/
theorem eval_link_iff (σ : V → Bool) (b : Bool) (previous next : V) :
    (link b previous next).eval σ = true ↔ (σ next = b → σ previous = b) := by
  cases b <;> cases hp : σ previous <;> cases hn : σ next <;>
    simp [link, Clause.eval_imp, hp, hn]

/-- All links hold exactly when literal truth propagates across every gap. -/
theorem eval_links_iff (σ : V → Bool) (b : Bool) (cells : List (V × V)) :
    (links b cells).eval σ = true ↔
      ∀ p ∈ cells.consecutivePairs, σ p.2.1 = b → σ p.1.2 = b := by
  simp only [links, eval_map_eq_true_iff, eval_link_iff]

/-- Empty and singleton cell lists have no intercell clauses. -/
@[simp] theorem links_nil (b : Bool) : links b ([] : List (V × V)) = [] := rfl

/-- A single cell needs only its own local equality, with no additional wire clauses. -/
@[simp] theorem links_singleton (b : Bool) (cell : V × V) : links b [cell] = [] := rfl

/-- Splitting off the first gap leaves the links of the nonempty tail. -/
theorem links_cons_cons (b : Bool) (first next : V × V) (rest : List (V × V)) :
    links b (first :: next :: rest) = link b first.2 next.1 :: links b (next :: rest) := rfl

/-- Given local entry/exit equality in each cell, final literal truth implies initial truth. -/
theorem propagate (σ : V → Bool) (b : Bool) (first : V × V) (rest : List (V × V))
    (hcells : ∀ c ∈ first :: rest, σ c.1 = σ c.2)
    (hlinks : (links b (first :: rest)).eval σ = true)
    (hlast : σ ((first :: rest).getLastD first).2 = b) : σ first.1 = b := by
  induction rest generalizing first with
  | nil => exact (hcells first List.mem_cons_self).trans hlast
  | cons next rest ih =>
    rw [links_cons_cons, eval_cons, Bool.and_eq_true] at hlinks
    have hn : σ next.1 = b := ih next
      (fun c hc => hcells c (List.mem_cons_of_mem _ hc)) hlinks.2
      (by simpa only [List.getLastD_cons] using hlast)
    exact (hcells first List.mem_cons_self).trans ((eval_link_iff σ b _ _).1 hlinks.1 hn)

/-- The propagation rule for a possibly empty list, with nonemptiness stated explicitly.
The fallback only makes the endpoint expressions total; it is unused under this hypothesis. -/
theorem propagate_of_ne_nil (σ : V → Bool) (b : Bool) (fallback : V)
    (cells : List (V × V)) (hne : cells ≠ [])
    (hcells : ∀ c ∈ cells, σ c.1 = σ c.2)
    (hlinks : (links b cells).eval σ = true)
    (hlast : σ (cells.getLastD (fallback, fallback)).2 = b) :
    σ (cells.headD (fallback, fallback)).1 = b := by
  cases cells with
  | nil => exact False.elim (hne rfl)
  | cons first rest =>
    apply propagate σ b first rest hcells hlinks
    simpa only [List.getLastD_cons] using hlast

/-- Assigning a common value to all entries and exits satisfies every directed link. -/
theorem eval_links_of_constant (σ : V → Bool) (b value : Bool) (cells : List (V × V))
    (h : ∀ c ∈ cells, σ c.1 = value ∧ σ c.2 = value) :
    (links b cells).eval σ = true := by
  apply (eval_links_iff σ b cells).2
  intro p hp hn
  have hm := List.of_mem_zip hp
  rw [(h p.1 hm.1).2, ← (h p.2 (List.mem_of_mem_tail hm.2)).1]
  exact hn

/-- There is exactly one clause per consecutive gap. -/
theorem length_links_eq_gaps (b : Bool) (cells : List (V × V)) :
    (links b cells).length = cells.consecutivePairs.length := List.length_map _

/-- A nonempty wire has one fewer link than cells; an empty wire has zero links. -/
theorem length_links (b : Bool) (cells : List (V × V)) :
    (links b cells).length = cells.length - 1 := by
  simp [links, List.consecutivePairs]

/-- Every directed link has exactly two literals, even if its endpoints coincide. -/
theorem length_link (b : Bool) (previous next : V) : (link b previous next).length = 2 := by
  cases b <;> rfl

/-- Every clause of the wire is binary. -/
theorem length_of_mem_links (b : Bool) (cells : List (V × V)) {c : Clause V}
    (hc : c ∈ links b cells) : c.length = 2 := by
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc
  exact length_link b _ _

/-- There are exactly two literal occurrences per gap, with multiplicities retained. -/
theorem length_vars_links (b : Bool) (cells : List (V × V)) :
    (links b cells).vars.length = 2 * (cells.length - 1) := by
  rw [CNF.length_vars, links, List.map_map]
  simp only [Function.comp_def, length_link]
  simp [List.consecutivePairs, Nat.mul_comm]

/-- Replace each original literal by the final exit variable on its occurrence's wire,
retaining its polarity and its clause/literal position. -/
def replacementClauses (φ : CNF V) (wire : Occurrence V → List (W × W))
    (fallback : W) : CNF W :=
  φ.zipIdx.map fun c => c.1.zipIdx.map fun l =>
    ((wire (c.2, l.2, l.1)).getLastD (fallback, fallback) |>.2, l.1.2)

/-- The directed-link clauses for every original literal occurrence, including duplicates. -/
def allLinks (φ : CNF V) (wire : Occurrence V → List (W × W)) : CNF W :=
  (Cslib.Logic.PL.occurrences φ).flatMap fun o => links o.2.2.2 (wire o)

/-- Original clauses at their wire endpoints, followed by all directed links.
Local cell constraints, such as crossover formulas, are supplied separately by the caller. -/
def assemble (φ : CNF V) (wire : Occurrence V → List (W × W)) (fallback : W) : CNF W :=
  replacementClauses φ wire fallback ++ allLinks φ wire

/-- Evaluation of the replacement clauses, indexed by the original clause and literal positions. -/
theorem eval_replacementClauses_iff (φ : CNF V) (wire : Occurrence V → List (W × W))
    (fallback : W) (σ : W → Bool) :
    (replacementClauses φ wire fallback).eval σ = true ↔
      ∀ c ∈ φ.zipIdx, ∃ l ∈ c.1.zipIdx,
        σ ((wire (c.2, l.2, l.1)).getLastD (fallback, fallback)).2 = l.1.2 := by
  rw [replacementClauses, eval_map_eq_true_iff]
  apply forall₂_congr fun c _ => ?_
  rw [Clause.eval_eq_true_iff]
  constructor
  · rintro ⟨lit, hmem, htruth⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hmem
    exact ⟨l, hl, htruth⟩
  · rintro ⟨l, hl, htruth⟩
    exact ⟨_, List.mem_map.mpr ⟨l, hl, rfl⟩, htruth⟩

/-- The global link block holds exactly when every occurrence's wire links hold. -/
theorem eval_allLinks_iff (φ : CNF V) (wire : Occurrence V → List (W × W)) (σ : W → Bool) :
    (allLinks φ wire).eval σ = true ↔
      ∀ o ∈ Cslib.Logic.PL.occurrences φ, (links o.2.2.2 (wire o)).eval σ = true := by
  exact eval_flatMap_eq_true_iff σ _ _

private theorem occurrence_mem {φ : CNF V} {c : Clause V × ℕ} (hc : c ∈ φ.zipIdx)
    {l : Literal V × ℕ} (hl : l ∈ c.1.zipIdx) :
    (c.2, l.2, l.1) ∈ Cslib.Logic.PL.occurrences φ := by
  exact List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨l, hl, rfl⟩⟩

/-- Satisfaction projects back to the ordinary source formula when the caller proves local
cell equality and agreement between the first entries and source variable values. -/
theorem eval_assemble_sound (φ : CNF V) (wire : Occurrence V → List (W × W))
    (fallback : W) (τ : V → Bool) (σ : W → Bool)
    (hne : ∀ o ∈ Cslib.Logic.PL.occurrences φ, wire o ≠ [])
    (hcells : ∀ o ∈ Cslib.Logic.PL.occurrences φ, ∀ c ∈ wire o, σ c.1 = σ c.2)
    (hfirst : ∀ o ∈ Cslib.Logic.PL.occurrences φ,
      σ ((wire o).headD (fallback, fallback)).1 = τ o.2.2.1)
    (h : (assemble φ wire fallback).eval σ = true) : φ.eval τ = true := by
  have h' := h
  rw [assemble, eval_append, Bool.and_eq_true] at h'
  have hr := (eval_replacementClauses_iff φ wire fallback σ).1 h'.1
  have hw := (eval_allLinks_iff φ wire σ).1 h'.2
  rw [← List.zipIdx_map_fst 0 φ, eval_map_eq_true_iff]
  intro c hc
  obtain ⟨l, hl, hv⟩ := hr c hc
  have ho := occurrence_mem hc hl
  apply (Clause.eval_eq_true_iff τ c.1).2
  refine ⟨l.1, List.fst_mem_of_mem_zipIdx hl, ?_⟩
  have hp := propagate_of_ne_nil σ l.1.2 fallback (wire (c.2, l.2, l.1))
    (hne _ ho) (hcells _ ho) (hw _ ho) hv
  exact (hfirst _ ho).symm.trans hp

/-- A source satisfying assignment extends through the link assembly whenever the caller
supplies one compatible target assignment constant along each occurrence's nonempty wire.
This is an assignment-level conditional result, not an existence theorem for such a target. -/
theorem eval_assemble_complete (φ : CNF V) (wire : Occurrence V → List (W × W))
    (fallback : W) (τ : V → Bool) (σ : W → Bool)
    (hne : ∀ o ∈ Cslib.Logic.PL.occurrences φ, wire o ≠ [])
    (hcompat : ∀ o ∈ Cslib.Logic.PL.occurrences φ, ∀ c ∈ wire o,
      σ c.1 = τ o.2.2.1 ∧ σ c.2 = τ o.2.2.1)
    (h : φ.eval τ = true) : (assemble φ wire fallback).eval σ = true := by
  rw [assemble, eval_append, Bool.and_eq_true]
  constructor
  · apply (eval_replacementClauses_iff φ wire fallback σ).2
    intro c hc
    have hclause := (eval_eq_true_iff τ φ).1 h c.1 (List.fst_mem_of_mem_zipIdx hc)
    obtain ⟨l, hl, hv⟩ := (Clause.eval_eq_true_iff τ c.1).1 hclause
    rw [← List.zipIdx_map_fst 0 c.1] at hl
    obtain ⟨li, hli, rfl⟩ := List.mem_map.mp hl
    refine ⟨li, hli, ?_⟩
    have ho := occurrence_mem hc hli
    have hm : (wire (c.2, li.2, li.1)).getLastD (fallback, fallback) ∈
        wire (c.2, li.2, li.1) := by
      cases hw : wire (c.2, li.2, li.1) with
      | nil => exact False.elim (hne _ ho hw)
      | cons a rest =>
        rw [List.getLastD_cons]
        exact List.getLastD_mem_cons
    exact (hcompat _ ho _ hm).2.trans hv
  · apply (eval_allLinks_iff φ wire σ).2
    intro o ho
    exact eval_links_of_constant σ o.2.2.2 (τ o.2.2.1) (wire o) (hcompat o ho)

/-- Clause replacement preserves all original clause widths. -/
theorem map_length_replacementClauses (φ : CNF V) (wire : Occurrence V → List (W × W))
    (fallback : W) : (replacementClauses φ wire fallback).map List.length = φ.map List.length := by
  simp only [replacementClauses, List.map_map, Function.comp_def, List.length_map,
    List.length_zipIdx]
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map List.length) (List.zipIdx_map_fst 0 φ)

/-- The link block has one clause per gap of each occurrence's wire. -/
theorem length_allLinks (φ : CNF V) (wire : Occurrence V → List (W × W)) :
    (allLinks φ wire).length =
      ((Cslib.Logic.PL.occurrences φ).map fun o => (wire o).length - 1).sum := by
  simp [allLinks, List.length_flatMap, length_links]

/-- Exact total clause count: original clauses plus all intercell gaps. -/
theorem length_assemble (φ : CNF V) (wire : Occurrence V → List (W × W)) (fallback : W) :
    (assemble φ wire fallback).length = φ.length +
      ((Cslib.Logic.PL.occurrences φ).map fun o => (wire o).length - 1).sum := by
  simp [assemble, replacementClauses, length_allLinks]

/-- Endpoint replacement preserves the number of source literal occurrences. -/
theorem length_vars_replacementClauses (φ : CNF V) (wire : Occurrence V → List (W × W))
    (fallback : W) : (replacementClauses φ wire fallback).vars.length = φ.vars.length := by
  rw [CNF.length_vars, map_length_replacementClauses, ← CNF.length_vars]

/-- The global link block contributes exactly two literals per gap. -/
theorem length_vars_allLinks (φ : CNF V) (wire : Occurrence V → List (W × W)) :
    (allLinks φ wire).vars.length =
      2 * ((Cslib.Logic.PL.occurrences φ).map fun o => (wire o).length - 1).sum := by
  have total (os : List (Occurrence V)) :
      (CNF.vars (os.flatMap fun o => links o.2.2.2 (wire o))).length =
        2 * (os.map fun o => (wire o).length - 1).sum := by
    induction os with
    | nil => rfl
    | cons o os ih =>
      simp only [List.flatMap_cons, CNF.vars, List.flatten_append, List.map_append,
        List.length_append]
      change (links o.2.2.2 (wire o)).vars.length +
        (CNF.vars (os.flatMap fun o => links o.2.2.2 (wire o))).length = _
      rw [length_vars_links, ih]
      simp only [List.map_cons, List.sum_cons, Nat.mul_add]
  exact total _

/-- Exact total literal count, with no distinctness assumptions on signal variables. -/
theorem length_vars_assemble (φ : CNF V) (wire : Occurrence V → List (W × W)) (fallback : W) :
    (assemble φ wire fallback).vars.length = φ.vars.length +
      2 * ((Cslib.Logic.PL.occurrences φ).map fun o => (wire o).length - 1).sum := by
  unfold assemble
  simp only [CNF.vars, List.flatten_append, List.map_append, List.length_append]
  change (replacementClauses φ wire fallback).vars.length + (allLinks φ wire).vars.length = _
  rw [length_vars_replacementClauses, length_vars_allLinks]
  rfl

/-- Source clause widths are preserved and every added clause is binary. -/
theorem width_assemble (φ : CNF V) (wire : Occurrence V → List (W × W)) (fallback : W)
    {k : ℕ} (hwidth : ∀ c ∈ φ, c.length ≤ k) :
    ∀ c ∈ assemble φ wire fallback, c.length ≤ max k 2 := by
  intro c hc
  change c ∈ replacementClauses φ wire fallback ++ allLinks φ wire at hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have h := hwidth d.1 (List.fst_mem_of_mem_zipIdx hd)
    calc
      _ = d.1.length := by simp only [List.length_map, List.length_zipIdx]
      _ ≤ k := h
      _ ≤ max k 2 := Nat.le_max_left _ _
  · obtain ⟨o, _, hc⟩ := List.mem_flatMap.mp hc
    rw [length_of_mem_links _ _ hc]
    exact Nat.le_max_right _ _

end Cslib.Logic.PL.CNF.DirectedWire

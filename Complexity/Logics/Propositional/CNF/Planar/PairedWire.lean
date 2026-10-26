/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
public import Mathlib.Data.List.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Bool.Basic

/-!
# Paired implication wires

Each cell has two lanes, each with an entry and an exit. Local constraints must equate all
four port values. Across a gap, lane zero implies the next entry from the previous exit;
lane one implies the previous exit from the next entry. These implications use separate
ports. Under the local equalities, they force the representative values of consecutive cells
to agree. Thus every port of a nonempty wire has the value of its first lane-zero entry.

This module uses ordinary CNF semantics. It supplies no local cell constraints or geometry.
The two clauses and four literal positions per gap are counted with multiplicity, without
distinctness assumptions on the port variables.

## Main definitions

* `Cell`, `Cell.Agree`: two entry/exit pairs and equality of all four values.
* `gapClauses`, `links`: opposite implications across one gap and all consecutive gaps.

## Main results

* `eval_links_iff`: under local agreement, the links equate consecutive representatives.
* `agree_head`, `agree_head_of_ne_nil`: every entry and exit has the first entry's value.
* `eval_links_of_constant`: constant port values satisfy every link.
* `length_links`, `length_vars_links`, `length_of_mem_links`: exact sizes and binary width.

## References

The paired-port composition and equality argument are original.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.PairedWire

variable {V : Type*}

/-- Two lanes of entry/exit variables. Lane zero's entry represents the cell's value. -/
abbrev Cell (V : Type*) := Fin 2 → V × V

/-- All four port values agree with the lane-zero entry. Local cell constraints must provide
this property; the wire clauses alone do not impose it. -/
def Cell.Agree (cell : Cell V) (σ : V → Bool) : Prop :=
  ∀ lane, σ (cell lane).1 = σ (cell 0).1 ∧ σ (cell lane).2 = σ (cell 0).1

/-- Across one gap, lane zero points forward and lane one points backward. -/
def gapClauses (previous next : Cell V) : CNF V :=
  [Clause.imp [(previous 0).2] (next 0).1,
    Clause.imp [(next 1).1] (previous 1).2]

/-- Two opposite implications across every consecutive pair of cells. -/
def links (cells : List (Cell V)) : CNF V :=
  cells.consecutivePairs.flatMap fun p => gapClauses p.1 p.2

/-- With local agreement, the two implications equate the neighboring cell values. -/
theorem eval_gapClauses_iff (σ : V → Bool) (previous next : Cell V)
    (hp : previous.Agree σ) (hn : next.Agree σ) :
    (gapClauses previous next).eval σ = true ↔ σ (previous 0).1 = σ (next 0).1 := by
  simp only [gapClauses, eval_cons, eval_nil, Bool.and_true, Bool.and_eq_true,
    Clause.eval_imp, List.forall_mem_singleton, (hp 0).2, (hp 1).2, (hn 1).1]
  cases σ (previous 0).1 <;> cases σ (next 0).1 <;> simp

/-- Under local agreement in every cell, the links hold exactly when consecutive lane-zero
entries agree. -/
theorem eval_links_iff (σ : V → Bool) (cells : List (Cell V))
    (hcells : ∀ c ∈ cells, c.Agree σ) :
    (links cells).eval σ = true ↔
      ∀ p ∈ cells.consecutivePairs, σ (p.1 0).1 = σ (p.2 0).1 := by
  rw [links, eval_flatMap_eq_true_iff]
  apply forall₂_congr fun p hp => ?_
  have hm := List.of_mem_zip hp
  exact eval_gapClauses_iff σ p.1 p.2 (hcells _ hm.1)
    (hcells _ (List.mem_of_mem_tail hm.2))

/-- Empty wires have no gap clauses. -/
@[simp] theorem links_nil : links ([] : List (Cell V)) = [] := rfl

/-- A single cell has no gap clauses. -/
@[simp] theorem links_singleton (cell : Cell V) : links [cell] = [] := rfl

/-- Remove the first gap, leaving the links of the nonempty tail. -/
theorem links_cons_cons (first next : Cell V) (rest : List (Cell V)) :
    links (first :: next :: rest) = gapClauses first next ++ links (next :: rest) := rfl

/-- Under local agreement and satisfied links, all entries and exits have the value of the
first lane-zero entry, including for a singleton wire. -/
theorem agree_head (σ : V → Bool) (first : Cell V) (rest : List (Cell V))
    (hcells : ∀ c ∈ first :: rest, c.Agree σ)
    (hlinks : (links (first :: rest)).eval σ = true) :
    ∀ c ∈ first :: rest, ∀ lane,
      σ (c lane).1 = σ (first 0).1 ∧ σ (c lane).2 = σ (first 0).1 := by
  induction rest generalizing first with
  | nil =>
    intro c hc lane
    rw [List.mem_singleton.1 hc]
    exact hcells first List.mem_cons_self lane
  | cons next rest ih =>
    rw [links_cons_cons, eval_append, Bool.and_eq_true] at hlinks
    have he := (eval_gapClauses_iff σ first next (hcells _ List.mem_cons_self)
      (hcells _ (List.mem_cons_of_mem _ List.mem_cons_self))).1 hlinks.1
    intro c hc lane
    rcases List.mem_cons.1 hc with he | hc
    · rw [he]
      exact hcells first List.mem_cons_self lane
    · have h := ih next (fun c hc => hcells c (List.mem_cons_of_mem _ hc)) hlinks.2 c hc lane
      exact ⟨h.1.trans he.symm, h.2.trans he.symm⟩

/-- The head-agreement rule for a list with an explicit nonemptiness hypothesis. The fallback
only makes `headD` total and does not affect the result. -/
theorem agree_head_of_ne_nil (σ : V → Bool) (fallback : Cell V) (cells : List (Cell V))
    (hne : cells ≠ []) (hcells : ∀ c ∈ cells, c.Agree σ)
    (hlinks : (links cells).eval σ = true) :
    ∀ c ∈ cells, ∀ lane,
      σ (c lane).1 = σ (cells.headD fallback 0).1 ∧
        σ (c lane).2 = σ (cells.headD fallback 0).1 := by
  cases cells with
  | nil => exact False.elim (hne rfl)
  | cons first rest => exact agree_head σ first rest hcells hlinks

/-- A common value on every entry and exit satisfies all paired links. -/
theorem eval_links_of_constant (σ : V → Bool) (value : Bool) (cells : List (Cell V))
    (h : ∀ c ∈ cells, ∀ lane, σ (c lane).1 = value ∧ σ (c lane).2 = value) :
    (links cells).eval σ = true := by
  have hcells : ∀ c ∈ cells, c.Agree σ := fun c hc lane =>
    ⟨(h c hc lane).1.trans (h c hc 0).1.symm, (h c hc lane).2.trans (h c hc 0).1.symm⟩
  apply (eval_links_iff σ cells hcells).2
  intro p hp
  have hm := List.of_mem_zip hp
  exact (h p.1 hm.1 0).1.trans (h p.2 (List.mem_of_mem_tail hm.2) 0).1.symm

/-- There are exactly two clauses per gap. -/
theorem length_gapClauses (previous next : Cell V) :
    (gapClauses previous next).length = 2 := rfl

/-- Each gap clause is binary, even if some port variables coincide. -/
theorem length_of_mem_gapClauses (previous next : Cell V) {c : Clause V}
    (hc : c ∈ gapClauses previous next) : c.length = 2 := by
  simp only [gapClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> rfl

/-- A gap contributes four literal positions, counted with multiplicity. -/
theorem length_vars_gapClauses (previous next : Cell V) :
    (gapClauses previous next).vars.length = 4 := rfl

/-- There are exactly two clauses for each consecutive pair of cells. -/
theorem length_links_eq_gaps (cells : List (Cell V)) :
    (links cells).length = 2 * cells.consecutivePairs.length := by
  simp [links, List.length_flatMap, length_gapClauses, Nat.mul_comm]

/-- A wire with `n` cells has `2 (n - 1)` clauses, with truncated subtraction for `n = 0`. -/
theorem length_links (cells : List (Cell V)) :
    (links cells).length = 2 * (cells.length - 1) := by
  rw [length_links_eq_gaps]
  simp [List.consecutivePairs]

/-- Every clause of a paired wire has exactly two literal positions. -/
theorem length_of_mem_links (cells : List (Cell V)) {c : Clause V}
    (hc : c ∈ links cells) : c.length = 2 := by
  obtain ⟨p, _, hc⟩ := List.mem_flatMap.1 hc
  exact length_of_mem_gapClauses p.1 p.2 hc

/-- Paired links have width at most two. -/
theorem width_links (cells : List (Cell V)) : ∀ c ∈ links cells, c.length ≤ 2 :=
  fun _ hc => Nat.le_of_eq (length_of_mem_links cells hc)

/-- There are exactly four literal positions per gap. -/
theorem length_vars_links (cells : List (Cell V)) :
    (links cells).vars.length = 4 * (cells.length - 1) := by
  have h : (links cells).map List.length = List.replicate (links cells).length 2 := by
    apply List.map_eq_replicate_iff.2
    exact fun c hc => length_of_mem_links cells hc
  rw [CNF.length_vars, h]
  simp [length_links, Nat.mul_right_comm]

end Cslib.Logic.PL.CNF.PairedWire

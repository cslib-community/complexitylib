/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.PartitionFunction
public import Mathlib.Data.Finset.Powerset
import Complexity.Foundations.Data.List.Boole
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The hard-core model as a weighted CSP

The hard-core instance of a graph on the vertices `0, …, n - 1` with edge list `E`
(`CSP.hardCore n E`) has a vertex constraint `(false, [v])` for every vertex and an edge
constraint `(true, [u, v])` for every edge `(u, v)`. Under the hard-core weights with fugacity `t`
(`CSP.hardCoreWeight t`), a vertex constraint weighs `t` when its variable is `true`, and an edge
constraint weighs zero when both its variables are `true`. So the partition function is the sum of
`t ^ |S|` over the independent sets `S` of the graph (`CSP.partitionFunction_hardCore`); with
`t = 1` it is the number of independent sets.

Every vertex occurs once in its vertex constraint and once per incident edge, so a graph of
maximum degree `Δ` gives an instance in which every variable occurs at most `Δ + 1` times
(`CSP.count_vars_hardCore`).

## Main definitions

* `Cslib.Logic.PL.CSP.hardCoreWeight`: the hard-core weights.
* `Cslib.Logic.PL.CSP.hardCore`: the hard-core instance of a graph.

## Main results

* `Cslib.Logic.PL.CSP.partitionFunction_hardCore`: the partition function is the weighted count of
  independent sets.
* `Cslib.Logic.PL.CSP.numVars_hardCore`, `Cslib.Logic.PL.CSP.count_vars_hardCore`: its variables
  and their occurrences.
-/

public section

namespace Cslib.Logic.PL.CSP

/-- The hard-core weights with fugacity `t`: a vertex constraint (`false`) weighs `t` at `[true]`
and one otherwise; an edge constraint (`true`) weighs zero at `[true, true]` and one otherwise. -/
@[expose] def hardCoreWeight (t : ℕ) (R : Bool) (w : List Bool) : ℕ :=
  if R then (if w = [true, true] then 0 else 1) else (if w = [true] then t else 1)

/-- The hard-core instance of the graph on the vertices `0, …, n - 1` with edge list `E`: a vertex
constraint for every vertex and an edge constraint for every edge. -/
@[expose] def hardCore (n : ℕ) (E : List (ℕ × ℕ)) : CSP Bool ℕ :=
  (List.range n).map (fun v => (false, [v])) ++ E.map fun e => (true, [e.1, e.2])

variable {n : ℕ} {E : List (ℕ × ℕ)}

theorem vars_hardCore (n : ℕ) (E : List (ℕ × ℕ)) :
    (hardCore n E).vars = List.range n ++ E.flatMap fun e => [e.1, e.2] := by
  simp only [hardCore, vars, List.flatMap_append, List.flatMap_map]
  congr 1
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, List.flatMap_append, ih]

/-- The variables of the hard-core instance are the vertices, when the edges join vertices. -/
theorem mem_vars_hardCore (hE : ∀ e ∈ E, e.1 < n ∧ e.2 < n) {v : ℕ} :
    v ∈ (hardCore n E).vars ↔ v < n := by
  rw [vars_hardCore, List.mem_append, List.mem_range, List.mem_flatMap]
  constructor
  · rintro (h | ⟨e, he, hv⟩)
    · exact h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      exacts [(hE e he).1, (hE e he).2]
  · exact Or.inl

theorem numVars_hardCore (hE : ∀ e ∈ E, e.1 < n ∧ e.2 < n) : (hardCore n E).numVars = n := by
  rw [numVars, show (hardCore n E).vars.toFinset = Finset.range n by
    ext v
    rw [List.mem_toFinset, mem_vars_hardCore hE, Finset.mem_range], Finset.card_range]

/-- A vertex occurs once in its vertex constraint and once per incident edge. -/
theorem count_vars_hardCore (n : ℕ) (E : List (ℕ × ℕ)) (v : ℕ) :
    (hardCore n E).vars.count v ≤ 1 + (E.flatMap fun e => [e.1, e.2]).count v := by
  rw [vars_hardCore, List.count_append]
  exact Nat.add_le_add_right (List.nodup_iff_count_le_one.mp List.nodup_range v) _

/-- The weight of an assignment: `t` to the number of `true` vertices, if no edge has two `true`
ends, and zero otherwise. -/
theorem weight_hardCore (t : ℕ) (σ : ℕ → Bool) :
    (hardCore n E).weight (hardCoreWeight t) σ =
      t ^ ((Finset.range n).filter fun v => σ v = true).card *
        if ∀ e ∈ E, ¬(σ e.1 = true ∧ σ e.2 = true) then 1 else 0 := by
  have hv : ((List.range n).map fun v => hardCoreWeight t false [σ v]).prod =
      t ^ ((Finset.range n).filter fun v => σ v = true).card := by
    rw [List.map_congr_left (g := fun v => if σ v = true then t else 1) fun v _ => by
        cases σ v <;> rfl,
      ← List.prod_toFinset _ List.nodup_range,
      show (List.range n).toFinset = Finset.range n by ext; simp, Finset.prod_ite,
      Finset.prod_const, Finset.prod_const_one, Nat.mul_one]
  have he : (E.map fun e => hardCoreWeight t true [σ e.1, σ e.2]).prod =
      if ∀ e ∈ E, ¬(σ e.1 = true ∧ σ e.2 = true) then 1 else 0 := by
    rw [List.map_congr_left (g := fun e => if ¬(σ e.1 = true ∧ σ e.2 = true) then 1 else 0)
      fun e _ => by cases σ e.1 <;> cases σ e.2 <;> rfl, List.prod_map_boole]
  rw [weight, hardCore, List.map_append, List.map_map, List.map_map, List.prod_append, ← hv, ← he]
  rfl

/-- **The hard-core partition function** is the sum of `t ^ |S|` over the independent sets `S` of
the graph, when its edges join vertices `0, …, n - 1`. -/
theorem partitionFunction_hardCore (t : ℕ) (hE : ∀ e ∈ E, e.1 < n ∧ e.2 < n) :
    (hardCore n E).partitionFunction (hardCoreWeight t) =
      ∑ S ∈ (Finset.range n).powerset with ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S), t ^ S.card := by
  have hmem : ∀ v, v ∈ (hardCore n E).vars.toFinset ↔ v < n := fun v => by
    rw [List.mem_toFinset, mem_vars_hardCore hE]
  have hext : ∀ (τ : (hardCore n E).vars.toFinset → Bool) (v : ℕ) (hv : v < n),
      (if h : v ∈ (hardCore n E).vars.toFinset then τ ⟨v, h⟩ else default) =
        τ ⟨v, (hmem v).mpr hv⟩ :=
    fun τ v hv => by simp only [(hmem v).mpr hv, ↓reduceDIte]
  rw [Finset.sum_filter, partitionFunction]
  refine Finset.sum_nbij' (fun τ => (Finset.range n).filter fun v =>
      (if h : v ∈ (hardCore n E).vars.toFinset then τ ⟨v, h⟩ else default) = true)
    (fun S x => decide (x.1 ∈ S)) (fun τ _ => ?_)
    (fun S _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun τ _ => ?_) (fun S hS => ?_)
    (fun τ _ => ?_)
  · exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  · funext x
    have hx : x.1 < n := (hmem x.1).mp x.2
    simp only [Finset.mem_filter, Finset.mem_range, hx, true_and, hext τ x.1 hx, Subtype.coe_eta,
      Bool.decide_eq_true]
  · have hS' := Finset.mem_powerset.mp (Finset.mem_coe.mp hS)
    ext v
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hv, h⟩
      simpa only [(hmem v).mpr hv, ↓reduceDIte, decide_eq_true_eq] using h
    · intro hv
      have hvn := Finset.mem_range.mp (hS' hv)
      exact ⟨hvn, by simpa only [(hmem v).mpr hvn, ↓reduceDIte, decide_eq_true_eq] using hv⟩
  · rw [weight_hardCore]
    split_ifs with h₁ h₂ h₂
    · exact Nat.mul_one _
    · refine absurd (fun e he hS => h₁ e he ?_) h₂
      simpa only [Finset.mem_filter, Finset.mem_range, (hE e he).1, (hE e he).2, true_and]
        using hS
    · refine absurd (fun e he hσ => h₂ e he ?_) h₁
      simpa only [Finset.mem_filter, Finset.mem_range, (hE e he).1, (hE e he).2, true_and]
        using hσ
    · exact Nat.mul_zero _

end Cslib.Logic.PL.CSP

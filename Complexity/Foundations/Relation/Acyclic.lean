/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Relation.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Cycle
public import Mathlib.Logic.Relation
import Mathlib.Data.List.Duplicate

/-!
# Acyclic relations: simple cycles and topological numberings

A relation `r` is *acyclic* (cslib's `Relation.Acyclic r`) when its transitive closure is
irreflexive, that is, when `r` has no closed walk. This file gives two equivalent forms of
acyclicity:

* **Simple cycles.** A closed walk is a nonempty list whose consecutive elements, read cyclically
  (`Cycle.Chain`), are related. Every closed walk contains a simple one, without repeated
  elements: cut the walk at a repeated element and keep the closed walk between its two
  occurrences. So `r` is acyclic exactly when it has no simple cycle
  (`Relation.acyclic_iff_forall_nodup_not_cycle_chain`), the form in which feedback vertex and arc
  sets are stated.
* **Topological numberings.** When the related elements lie in a finite set `V`, `r` is acyclic
  exactly when some numbering `f : α → ℕ` strictly increases along every step of `r`
  (`Relation.acyclic_iff_exists_rank`). The numbering may be taken below the number of
  elements of `V`, which makes it a certificate of polynomial size: number each element by how many
  elements of `V` reach it.

## Main results

* `Relation.exists_nodup_of_cycle_chain`: a closed walk contains a simple cycle.
* `Relation.exists_cycle_chain_of_transGen`, `Relation.transGen_of_cycle_chain`: closed walks are
  the transitive closure relating an element to itself.
* `Relation.acyclic_iff_forall_nodup_not_cycle_chain`: acyclicity as the absence of simple cycles.
* `Relation.Acyclic.exists_rank`, `Relation.acyclic_of_rank`, `Relation.acyclic_iff_exists_rank`:
  acyclicity on a finite set as a topological numbering bounded by the number of elements.
* `Relation.not_transGen_of_rank`: a strictly increasing numbering excludes closed walks.
-/

public section

namespace Relation

variable {α : Type*} {r : α → α → Prop}

/-! ### Closed walks and simple cycles -/

/-- A duplicated element splits a list around two of its occurrences. -/
private theorem exists_eq_append_cons_of_duplicate {x : α} :
    ∀ {l : List α}, List.Duplicate x l → ∃ s t, l = s ++ x :: t ∧ x ∈ t
  | _, .cons_mem h => ⟨[], _, rfl, h⟩
  | _, .cons_duplicate (y := y) h => by
    obtain ⟨s, t, rfl, ht⟩ := exists_eq_append_cons_of_duplicate h
    exact ⟨y :: s, t, rfl, ht⟩

/-- **A closed walk contains a simple cycle**: a nonempty closed chain contains a nonempty closed
chain without repetitions, all of whose elements are elements of the walk. -/
theorem exists_nodup_of_cycle_chain {l : List α} (hne : l ≠ []) (hch : (l : Cycle α).Chain r) :
    ∃ c : List α, c ≠ [] ∧ c.Nodup ∧ c ⊆ l ∧ (c : Cycle α).Chain r := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
  by_cases hnd : l.Nodup
  · exact ⟨l, hne, hnd, List.Subset.refl _, hch⟩
  obtain ⟨x, hx⟩ := List.exists_duplicate_iff_not_nodup.2 hnd
  obtain ⟨s, t, rfl, hxt⟩ := exists_eq_append_cons_of_duplicate hx
  obtain ⟨b, d, rfl⟩ := List.append_of_mem hxt
  -- Rotate the walk to start at the first `x`, and keep the closed walk up to the second `x`.
  have hrot : ((s ++ x :: (b ++ x :: d) : List α) : Cycle α) =
      ((x :: (b ++ x :: (d ++ s)) : List α) : Cycle α) := by
    rw [Cycle.coe_eq_coe]
    simpa using List.isRotated_append (l := s) (l' := x :: (b ++ x :: d))
  rw [hrot, Cycle.chain_coe_cons] at hch
  have hsub : (x :: (b ++ [x])).IsChain r := hch.infix ⟨[], d ++ s ++ [x], by simp⟩
  obtain ⟨c, hcne, hcnd, hcsub, hcch⟩ := ih (x :: b).length (by simp at h ⊢; omega)
    (List.cons_ne_nil _ _) (by rw [Cycle.chain_coe_cons]; simpa using hsub) rfl
  exact ⟨c, hcne, hcnd, fun y hy => by have := hcsub hy; simp at this ⊢; tauto, hcch⟩

/-- A closed walk through `a` gives a closed chain containing `a`. -/
theorem exists_cycle_chain_of_transGen {a : α} (h : TransGen r a a) :
    ∃ c : List α, a ∈ c ∧ (c : Cycle α).Chain r := by
  obtain ⟨b, hab, hba⟩ := TransGen.head'_iff.1 h
  obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen hba
  have ha : a ∈ b :: l := by
    rw [← hlast]
    exact List.getLast_mem _
  refine ⟨b :: l, ha, ?_⟩
  rw [Cycle.chain_coe_cons, ← List.cons_append, List.isChain_append]
  refine ⟨hl, .singleton _, fun x hx y hy => ?_⟩
  rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hlast, Option.mem_some_iff] at hx
  rw [List.head?_cons, Option.mem_some_iff] at hy
  rw [← hx, ← hy]
  exact hab

/-- Every element of a closed chain lies on a closed walk. -/
theorem transGen_of_cycle_chain {c : List α} (hch : (c : Cycle α).Chain r) {a : α}
    (ha : a ∈ c) : TransGen r a a :=
  Cycle.chain_iff_pairwise.1 (hch.imp fun _ _ => TransGen.single) a ha a ha

/-- **Acyclicity as the absence of simple cycles**: no element lies on a closed walk exactly when
there is no nonempty closed chain without repetitions. -/
theorem acyclic_iff_forall_nodup_not_cycle_chain :
    Acyclic r ↔ ∀ c : List α, c ≠ [] → c.Nodup → ¬(c : Cycle α).Chain r := by
  constructor
  · intro h c hne _ hch
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil c hne
    exact h.irrefl a (transGen_of_cycle_chain hch ha)
  · refine fun h => ⟨fun a ha => ?_⟩
    obtain ⟨l, hal, hch⟩ := exists_cycle_chain_of_transGen ha
    obtain ⟨c, hcne, hcnd, -, hcch⟩ := exists_nodup_of_cycle_chain (List.ne_nil_of_mem hal) hch
    exact h c hcne hcnd hcch

/-! ### Topological numberings -/

/-- **Topological numbering.** If every step of `r` is between elements of a finite set `V` and
`r` is acyclic, then numbering each element by the number of elements of `V` that reach it gives
numbers below the number of elements of `V` that strictly increase along every step.

The hypothesis `hV` says that `V` contains the *support* of `r`: both ends of every step. Elements
outside `V` are related to nothing, so their numbers are unconstrained. -/
theorem Acyclic.exists_rank (hr : Acyclic r) (V : Finset α) (hV : ∀ a b, r a b → a ∈ V ∧ b ∈ V) :
    ∃ f : α → ℕ, (∀ a ∈ V, f a < V.card) ∧ ∀ a b, r a b → f a < f b := by
  classical
  refine ⟨fun a => (V.filter fun u => TransGen r u a).card, fun a ha => ?_, fun a b hab => ?_⟩
  · exact Finset.card_lt_card (Finset.filter_ssubset.2 ⟨a, ha, hr.irrefl a⟩)
  · refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun u hu => ?_).2 ⟨a, ?_, ?_⟩)
    · simp only [Finset.mem_filter] at hu ⊢
      exact ⟨hu.1, hu.2.tail hab⟩
    · simp only [Finset.mem_filter]
      exact ⟨(hV a b hab).1, TransGen.single hab⟩
    · simp only [Finset.mem_filter, not_and]
      exact fun _ => hr.irrefl a

/-- A numbering that strictly increases along every step of `r` excludes closed walks. -/
theorem not_transGen_of_rank {f : α → ℕ} (hf : ∀ a b, r a b → f a < f b) (a : α) :
    ¬TransGen r a a := by
  suffices ∀ b, TransGen r a b → f a < f b from fun h => (this a h).false
  intro b h
  induction h with
  | single h => exact hf _ _ h
  | tail _ h ih => exact ih.trans (hf _ _ h)

/-- A relation with a numbering that strictly increases along every step is acyclic. -/
theorem acyclic_of_rank {f : α → ℕ} (hf : ∀ a b, r a b → f a < f b) : Acyclic r :=
  ⟨not_transGen_of_rank hf⟩

/-- **Acyclicity on a finite set as a topological numbering**: when every step of `r` is between
elements of a finite set `V` (the hypothesis `hV`), `r` is acyclic exactly when some numbering
below the number of elements of `V` strictly increases along every step. -/
theorem acyclic_iff_exists_rank (V : Finset α) (hV : ∀ a b, r a b → a ∈ V ∧ b ∈ V) :
    Acyclic r ↔ ∃ f : α → ℕ, (∀ a ∈ V, f a < V.card) ∧ ∀ a b, r a b → f a < f b :=
  ⟨fun hr => hr.exists_rank V hV, fun ⟨_, _, hf⟩ => acyclic_of_rank hf⟩

end Relation

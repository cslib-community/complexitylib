/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.DropRight

/-!
# List append boundaries and unary delimiters

## Main results

* `List.rdropWhile_append`: drop matching suffix elements across an append boundary.
* `List.zip_tail_append_cons`: split adjacent pairs at a shared boundary element.
* `List.append_cons_inj_of_notMem_prefix`: two splits of a list at an element that occurs in
  neither prefix coincide.
* `List.exists_eq_append_cons_of_exists_mem`: a list with an element satisfying `p` splits at its
  first such element.
* `List.flatMap_singleton_injective`: a substitution by singletons is injective on words whenever
  the underlying map is injective.
* `List.replicate_not_append_cons_inj`, `List.replicate_true_append_false_inj`: a unary block
  followed by its delimiter determines both its length and the remaining suffix.
* `List.idxOf_replicate_append_cons_of_ne`, `List.idxOf_false_replicate_append`,
  `List.idxOf_true_replicate_false_append`: the index of a delimiter following a unary block.
* `List.eq_replicate_idxOf_false`, `List.eq_replicate_idxOf_true`: canonical decomposition of a
  word by its first delimiter.
-/

@[expose] public section

/-- Dropping from the right of an appended list drops from the suffix first. -/
theorem List.rdropWhile_append {α : Type*} (p : α → Bool) (l₁ l₂ : List α) :
    (l₁ ++ l₂).rdropWhile p =
      if l₂.rdropWhile p = [] then l₁.rdropWhile p else l₁ ++ l₂.rdropWhile p := by
  simp only [List.rdropWhile, List.reverse_append, List.dropWhile_append]
  by_cases h : l₂.reverse.dropWhile p = []
  · simp [h]
  · simp [h]

/-- Split consecutive pairs at a boundary element shared by the two list segments. -/
theorem List.zip_tail_append_cons {α : Type*} (before : List α) (middle : α)
    (after : List α) :
    (before ++ middle :: after).zip (before ++ middle :: after).tail =
      (before ++ [middle]).zip (before ++ [middle]).tail ++ (middle :: after).zip after := by
  induction before with
  | nil => simp
  | cons first before ih =>
    cases before with
    | nil => simp
    | cons second before =>
      simpa only [List.cons_append, List.tail_cons, List.zip_cons_cons] using
        congrArg (List.cons (first, second)) ih

/-- Two splits of a list at an element `a` that occurs in neither prefix coincide. -/
theorem List.append_cons_inj_of_notMem_prefix {α : Type*} {a : α} {x₁ x₂ z₁ z₂ : List α}
    (h₁ : a ∉ x₁) (h₂ : a ∉ x₂) : x₁ ++ a :: z₁ = x₂ ++ a :: z₂ ↔ x₁ = x₂ ∧ z₁ = z₂ := by
  refine ⟨fun h => ?_, fun ⟨hx, hz⟩ => hx ▸ hz ▸ rfl⟩
  induction x₁ generalizing x₂ with
  | nil =>
    cases x₂ with
    | nil => exact ⟨rfl, (List.cons.inj h).2⟩
    | cons b x₂ =>
      obtain ⟨rfl, -⟩ := List.cons.inj h
      exact absurd List.mem_cons_self h₂
  | cons b x₁ ih =>
    cases x₂ with
    | nil =>
      obtain ⟨rfl, -⟩ := List.cons.inj h
      exact absurd List.mem_cons_self h₁
    | cons c x₂ =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl⟩ := ih (List.not_mem_of_not_mem_cons h₁) (List.not_mem_of_not_mem_cons h₂) h
      exact ⟨rfl, rfl⟩

/-- A list with an element satisfying `p` splits at its first such element. -/
theorem List.exists_eq_append_cons_of_exists_mem {α : Type*} {p : α → Prop} {l : List α}
    (h : ∃ x ∈ l, p x) : ∃ u x v, l = u ++ x :: v ∧ p x ∧ ∀ y ∈ u, ¬p y := by
  classical
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr (by simpa only [decide_eq_true_eq] using h) :
      (l.find? fun x => decide (p x)).isSome)
  obtain ⟨hpx, u, v, rfl, hu⟩ := List.find?_eq_some_iff_append.mp hx
  exact ⟨u, x, v, rfl, of_decide_eq_true hpx, fun y hy => by simpa using hu y hy⟩

/-- A substitution by singletons is injective on words whenever the underlying map is injective. -/
theorem List.flatMap_singleton_injective {α β : Type*} {f : α → β} (hf : Function.Injective f) :
    Function.Injective fun w : List α => w.flatMap fun a => [f a] := by
  intro u v h
  simp only [← List.map_eq_flatMap] at h
  exact List.map_injective_iff.mpr hf h

/-- A unary block of copies of `!a` followed by the delimiter `a` determines both its length and the
remaining suffix. -/
theorem List.replicate_not_append_cons_inj {a : Bool} {m m' : ℕ} {l l' : List Bool}
    (h : List.replicate m (!a) ++ a :: l = List.replicate m' (!a) ++ a :: l') :
    m = m' ∧ l = l' := by
  induction m generalizing m' <;> cases m' <;> simp_all [List.replicate_succ]

/-- A unary block of `true` bits followed by `false` determines both its length and the remaining
suffix. -/
theorem List.replicate_true_append_false_inj {m m' : ℕ} {l l' : List Bool}
    (h : List.replicate m true ++ false :: l = List.replicate m' true ++ false :: l') :
    m = m' ∧ l = l' :=
  List.replicate_not_append_cons_inj (a := false) h

/-- The first occurrence of `b` in `(replicate k a ++ b :: l)` is at index `k`, provided `a ≠ b`. -/
theorem List.idxOf_replicate_append_cons_of_ne {α : Type*} [DecidableEq α] {a b : α}
    (hab : a ≠ b) (k : ℕ) (l : List α) :
    (List.replicate k a ++ b :: l).idxOf b = k := by
  rw [List.idxOf_append_of_notMem (by simp [hab.symm]), List.length_replicate,
    List.idxOf_cons_self, Nat.add_zero]

/-- The first occurrence of `false` in a list beginning with `k` `true`s is at index `k`. -/
@[simp]
theorem List.idxOf_false_replicate_append (k : ℕ) (l : List Bool) :
    (List.replicate k true ++ false :: l).idxOf false = k :=
  List.idxOf_replicate_append_cons_of_ne (by decide) k l

/-- The first occurrence of `true` in a list beginning with `k` `false`s is at index `k`. -/
@[simp]
theorem List.idxOf_true_replicate_false_append (k : ℕ) (l : List Bool) :
    (List.replicate k false ++ true :: l).idxOf true = k :=
  List.idxOf_replicate_append_cons_of_ne (by decide) k l

/-- A Boolean word containing `false` decomposes into a unary run of `true`s up to the first
`false`, and the remaining suffix. -/
theorem List.eq_replicate_idxOf_false {l : List Bool} (hl : false ∈ l) :
    l = List.replicate (l.idxOf false) true ++ false :: l.drop (l.idxOf false + 1) := by
  induction l with
  | nil => simp at hl
  | cons b l ih =>
    cases b
    · simp
    · rw [List.idxOf_cons_ne _ (by decide), List.replicate_succ, List.cons_append,
        List.drop_succ_cons, ← ih (by simpa using hl)]

/-- A Boolean word containing `true` decomposes into a unary run of `false`s up to the first
`true`, and the remaining suffix. -/
theorem List.eq_replicate_idxOf_true {l : List Bool} (hl : true ∈ l) :
    l = List.replicate (l.idxOf true) false ++ true :: l.drop (l.idxOf true + 1) := by
  induction l with
  | nil => simp at hl
  | cons b l ih =>
    cases b
    · rw [List.idxOf_cons_ne _ (by decide), List.replicate_succ, List.cons_append,
        List.drop_succ_cons, ← ih (by simpa using hl)]
    · simp

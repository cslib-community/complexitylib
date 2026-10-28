/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
import Mathlib.Data.List.Count

/-!
# Exact-one semantics for clauses

`Clause.evalOne` counts true literal occurrences, including repeated occurrences of the same
variable. `CNF.evalOne` requires exactly one true literal in every clause. This reuses the
existing signed CNF representation; positivity and clause-size restrictions are separate.

`CNF.oneEncoding` expresses these semantics with ordinary CNF clauses and no new variables.
Unlike `CNF.exactlyOne`, which constrains distinct variables, this encoding counts positions.

## Main definitions

* `Clause.evalOne`, `CNF.evalOne`, `CNF.OneSatisfiable`: exact-one semantics.
* `Clause.oneEncoding`, `CNF.oneEncoding`: the ordinary CNF encoding.

## Main results

* `CNF.eval_oneEncoding`: correctness of the encoding under the same assignment.
* `CNF.mem_vars_oneEncoding`: the encoding has exactly the source variables.

## References

* [Hunt, Marathe, Radhakrishnan and Stearns][HuntMaratheRadhakrishnanStearns1998],
  Definition 2.9.
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {V W : Type*}

/-- Exactly one literal occurrence of the clause is true. -/
def Clause.evalOne (σ : V → Bool) (c : Clause V) : Bool :=
  c.countP (Literal.eval σ) == 1

/-- Every clause has exactly one true literal occurrence. -/
def CNF.evalOne (σ : V → Bool) (φ : CNF V) : Bool := φ.all (Clause.evalOne σ)

/-- Some assignment gives exactly one true literal occurrence in every clause. -/
def CNF.OneSatisfiable (φ : CNF V) : Prop := ∃ σ : V → Bool, φ.evalOne σ = true

/-- The empty clause cannot have exactly one true literal. -/
@[simp] theorem Clause.evalOne_nil (σ : V → Bool) : Clause.evalOne σ [] = false := rfl

/-- A singleton exact-one clause has the same semantics as its literal. -/
@[simp] theorem Clause.evalOne_singleton (σ : V → Bool) (l : Literal V) :
    Clause.evalOne σ [l] = Literal.eval σ l := by
  cases h : Literal.eval σ l <;> simp [Clause.evalOne, h]

/-- Exact-one satisfaction is the occurrence-count equation. -/
theorem Clause.evalOne_eq_true_iff (σ : V → Bool) (c : Clause V) :
    c.evalOne σ = true ↔ c.countP (Literal.eval σ) = 1 := by
  simp [Clause.evalOne]

/-- An assignment satisfies the exact-one formula when it satisfies every exact-one clause. -/
theorem CNF.evalOne_eq_true_iff (σ : V → Bool) (φ : CNF V) :
    φ.evalOne σ = true ↔ ∀ c ∈ φ, c.evalOne σ = true := by
  simp [CNF.evalOne]

/-- The empty exact-one formula is true. -/
@[simp] theorem CNF.evalOne_nil (σ : V → Bool) : CNF.evalOne σ [] = true := rfl

/-- A cons of exact-one clauses evaluates conjunctively. -/
@[simp] theorem CNF.evalOne_cons (σ : V → Bool) (c : Clause V) (φ : CNF V) :
    CNF.evalOne σ (c :: φ) = (c.evalOne σ && φ.evalOne σ) := rfl

/-- Appending exact-one formulas conjoins their values. -/
@[simp] theorem CNF.evalOne_append (σ : V → Bool) (φ ψ : CNF V) :
    CNF.evalOne σ (φ ++ ψ) = (φ.evalOne σ && ψ.evalOne σ) := by
  simp [CNF.evalOne]

/-- A blockwise exact-one formula holds when every block does. -/
theorem CNF.evalOne_flatMap_eq_true_iff {ι : Type*} (σ : V → Bool) (l : List ι)
    (f : ι → CNF V) :
    CNF.evalOne σ (l.flatMap f) = true ↔ ∀ i ∈ l, (f i).evalOne σ = true := by
  simp only [CNF.evalOne_eq_true_iff, List.mem_flatMap, forall_exists_index, and_imp]
  exact ⟨fun h i hi c hc => h c i hi hc, fun h c i hi hc => h i hi c hc⟩

/-- Clause exact-one evaluation depends only on the variables occurring in it. -/
theorem Clause.evalOne_congr {σ τ : V → Bool} {c : Clause V}
    (h : ∀ l ∈ c, σ l.1 = τ l.1) : c.evalOne σ = c.evalOne τ := by
  unfold Clause.evalOne
  congr 1
  apply List.countP_congr
  intro l hl
  simp only [Literal.eval, h l hl]

/-- Formula exact-one evaluation depends only on its variables. -/
theorem CNF.evalOne_congr {σ τ : V → Bool} {φ : CNF V}
    (h : ∀ v ∈ φ.vars, σ v = τ v) : φ.evalOne σ = φ.evalOne τ := by
  rw [Bool.eq_iff_iff, CNF.evalOne_eq_true_iff, CNF.evalOne_eq_true_iff]
  refine forall₂_congr fun c hc => ?_
  rw [Clause.evalOne_congr (fun l hl => h l.1 ?_)]
  exact CNF.mem_vars.mpr ⟨c, hc, l.2, hl⟩

/-- Exact-one clause evaluation commutes with relabelling. -/
@[simp] theorem Clause.evalOne_relabel (f : V → W) (σ : W → Bool) (c : Clause V) :
    (c.relabel f).evalOne σ = c.evalOne (σ ∘ f) := by
  unfold Clause.evalOne Clause.relabel
  rw [List.countP_map]
  rfl

/-- Exact-one formula evaluation commutes with relabelling. -/
@[simp] theorem CNF.evalOne_relabel (f : V → W) (σ : W → Bool) (φ : CNF V) :
    (φ.relabel f).evalOne σ = φ.evalOne (σ ∘ f) := by
  simp [CNF.evalOne, CNF.relabel, List.all_map, Function.comp_def]

/-- Clauses forbidding simultaneous truth of each pair of literal positions. -/
def Clause.atMostOneOccurrences : Clause V → CNF V
  | [] => []
  | l :: c => c.map (fun k => [Std.Sat.Literal.negate l, Std.Sat.Literal.negate k]) ++
      atMostOneOccurrences c

/-- Express exact-one clause semantics with ordinary clauses and no new variables. -/
def Clause.oneEncoding (c : Clause V) : CNF V := [c] ++ c.atMostOneOccurrences

/-- Express exact-one formula semantics with ordinary clauses and no new variables. -/
def CNF.oneEncoding (φ : CNF V) : CNF V := φ.flatMap Clause.oneEncoding

/-- The pair clauses constrain the true occurrence count to be at most one. -/
theorem Clause.eval_atMostOneOccurrences (σ : V → Bool) (c : Clause V) :
    c.atMostOneOccurrences.eval σ = true ↔ c.countP (Literal.eval σ) ≤ 1 := by
  induction c with
  | nil => simp [Clause.atMostOneOccurrences]
  | cons l c ih =>
    have head (l : Literal V) :
        CNF.eval σ (c.map fun k => [Std.Sat.Literal.negate l, Std.Sat.Literal.negate k]) =
          true ↔ (Literal.eval σ l = true → c.countP (Literal.eval σ) = 0) := by
      cases h : Literal.eval σ l <;>
        simp [CNF.eval, Clause.eval, List.countP_eq_zero, h]
    rw [Clause.atMostOneOccurrences, CNF.eval_append, Bool.and_eq_true, head, ih]
    cases h : Literal.eval σ l <;>
      simp only [List.countP_cons, h, Bool.false_eq_true, ↓reduceIte,
        false_implies, true_implies, true_and] <;> omega

/-- Exact-one clause encoding preserves evaluation under the same assignment. -/
@[simp] theorem Clause.eval_oneEncoding (σ : V → Bool) (c : Clause V) :
    c.oneEncoding.eval σ = c.evalOne σ := by
  rw [Bool.eq_iff_iff, Clause.oneEncoding, CNF.eval_append, Bool.and_eq_true]
  rw [CNF.eval_cons, CNF.eval_nil, Bool.and_true, Clause.eval_atMostOneOccurrences,
    Clause.evalOne_eq_true_iff]
  have hpos : c.eval σ = true ↔ 0 < c.countP (Literal.eval σ) := by
    simp [Clause.eval, List.countP_pos_iff]
  rw [hpos]
  omega

/-- Exact-one formula encoding preserves evaluation under the same assignment. -/
@[simp] theorem CNF.eval_oneEncoding (σ : V → Bool) (φ : CNF V) :
    φ.oneEncoding.eval σ = φ.evalOne σ := by
  rw [Bool.eq_iff_iff, CNF.oneEncoding, CNF.eval_flatMap_eq_true_iff,
    CNF.evalOne_eq_true_iff]
  simp

/-- The ordinary encoding is satisfiable exactly when the exact-one source is. -/
theorem CNF.satisfiable_oneEncoding (φ : CNF V) :
    φ.oneEncoding.Satisfiable ↔ φ.OneSatisfiable := by
  simp [CNF.Satisfiable, CNF.OneSatisfiable]

/-- A variable in a pair clause already occurs in the source clause. -/
theorem Clause.fst_mem_of_mem_atMostOneOccurrences {c : Clause V} {d : Clause V}
    (hd : d ∈ c.atMostOneOccurrences) {l : Literal V} (hl : l ∈ d) :
    ∃ k ∈ c, l.1 = k.1 := by
  induction c with
  | nil => simp [Clause.atMostOneOccurrences] at hd
  | cons k c ih =>
    simp only [Clause.atMostOneOccurrences, List.mem_append, List.mem_map] at hd
    rcases hd with ⟨k', hk', rfl⟩ | hd
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact ⟨k, List.mem_cons_self, rfl⟩
      · exact ⟨k', List.mem_cons_of_mem _ hk', rfl⟩
    · obtain ⟨k', hk', he⟩ := ih hd
      exact ⟨k', List.mem_cons_of_mem _ hk', he⟩

/-- The encoding has exactly the variables of the source, irrespective of repetitions. -/
theorem CNF.mem_vars_oneEncoding {φ : CNF V} {v : V} :
    v ∈ φ.oneEncoding.vars ↔ v ∈ φ.vars := by
  constructor
  · intro hv
    obtain ⟨d, hd, b, hl⟩ := CNF.mem_vars.mp hv
    obtain ⟨c, hc, hd⟩ := List.mem_flatMap.mp hd
    rcases List.mem_append.mp hd with hd | hd
    · have hd' : d = c := List.mem_singleton.mp hd
      subst d
      exact CNF.mem_vars.mpr ⟨c, hc, b, hl⟩
    · obtain ⟨k, hk, he⟩ := Clause.fst_mem_of_mem_atMostOneOccurrences hd hl
      have hk' : (v, k.2) = k := Prod.ext he rfl
      exact CNF.mem_vars.mpr ⟨c, hc, k.2, hk'.symm ▸ hk⟩
  · intro hv
    obtain ⟨c, hc, b, hl⟩ := CNF.mem_vars.mp hv
    exact CNF.mem_vars.mpr ⟨c, List.mem_flatMap.mpr
      ⟨c, hc, List.mem_append.mpr (Or.inl (List.mem_singleton_self _))⟩, b, hl⟩

/-- The pair encoding commutes with renaming variables. -/
theorem Clause.atMostOneOccurrences_relabel (f : V → W) (c : Clause V) :
    (c.relabel f).atMostOneOccurrences = c.atMostOneOccurrences.relabel f := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [Clause.relabel, CNF.relabel] at ih
    simp [Clause.relabel, Clause.atMostOneOccurrences, CNF.relabel, ih,
      List.map_map, Function.comp_def, Std.Sat.Literal.negate]

/-- The clause encoding commutes with renaming variables. -/
theorem Clause.oneEncoding_relabel (f : V → W) (c : Clause V) :
    (c.relabel f).oneEncoding = c.oneEncoding.relabel f := by
  simp [Clause.oneEncoding, Clause.atMostOneOccurrences_relabel, CNF.relabel]

/-- The formula encoding commutes with renaming variables. -/
theorem CNF.oneEncoding_relabel (f : V → W) (φ : CNF V) :
    (φ.relabel f).oneEncoding = φ.oneEncoding.relabel f := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [CNF.relabel, CNF.oneEncoding] at ih
    simp [CNF.relabel, CNF.oneEncoding, Clause.oneEncoding_relabel, ih]

end Cslib.Logic.PL

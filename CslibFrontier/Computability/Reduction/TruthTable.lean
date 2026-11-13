/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Reduction.ManyOne
public import Mathlib.Data.List.OfFn

/-!
# Truth-table reductions by admissible data

A truth-table reduction of `A` to `B` fixes, for each input `a`, a number `r a` of queries
`q (a, 0), …, q (a, r a - 1)` and decides `a ∈ A` by applying a combiner `d` to `a` and the answer
word `truthTableAnswers (q ⁻¹' B) r a`. Disjunctive and conjunctive reductions replace the combiner
by "some query is in `B`" and "every query is in `B`". Here the admissible data `(r, q, d)` or
`(r, q)` are an arbitrary predicate `Good`. No machine model or encoding is built in. The
polynomial-time and logspace truth-table families instantiate these definitions, as polynomial-time
and logspace many-one reductions instantiate `Cslib.Complexity.ManyOneReducibleBy`.

## Main definitions

* `Cslib.Complexity.truthTableAnswers`: the answer word of an indexed batch of queries.
* `Cslib.Complexity.TruthTableReducibleBy`: truth-table reducibility by admissible data.
* `Cslib.Complexity.DTTReducibleBy`, `Cslib.Complexity.CTTReducibleBy`: disjunctive and
  conjunctive truth-table reducibility by admissible data.

## Main results

* `Cslib.Complexity.TruthTableReducibleBy.mono`, `Cslib.Complexity.DTTReducibleBy.mono`,
  `Cslib.Complexity.CTTReducibleBy.mono`: more admissible data give more reductions.
* `Cslib.Complexity.TruthTableReducibleBy.compl_left`,
  `Cslib.Complexity.TruthTableReducibleBy.compl_right`: negating the combiner, or the answers it
  reads, reduces `Aᶜ` to `B`, or `A` to `Bᶜ`.
* `Cslib.Complexity.ManyOneReducibleBy.truthTableReducibleBy`,
  `Cslib.Complexity.ManyOneReducibleBy.dttReducibleBy`,
  `Cslib.Complexity.ManyOneReducibleBy.cttReducibleBy`: a many-one reduction asks one query.
* `Cslib.Complexity.DTTReducibleBy.truthTableReducibleBy`,
  `Cslib.Complexity.CTTReducibleBy.truthTableReducibleBy`: disjunctive and conjunctive reductions
  are truth-table reductions with combiner `List.any id` or `List.all id`.
* `Cslib.Complexity.dttReducibleBy_iff_cttReducibleBy_compl`: De Morgan duality.

## References

* [R. E. Ladner, N. A. Lynch, A. L. Selman, *A comparison of polynomial time
  reducibilities*][LadnerLynchSelman1975]
-/

@[expose] public section

namespace Cslib.Complexity

universe u v

variable {α : Type u} {β : Type v}

open Classical in
/-- The semantic answers to a fixed indexed batch, in increasing index order. This definition
does not assert that membership in the indexed language is computable. -/
noncomputable def truthTableAnswers (A : Set (α × ℕ)) (r : α → ℕ) (a : α) : List Bool :=
  List.ofFn fun i : Fin (r a) => decide ((a, i.1) ∈ A)

/-- The answer word has one bit per query. -/
@[simp]
theorem length_truthTableAnswers (A : Set (α × ℕ)) (r : α → ℕ) (a : α) :
    (truthTableAnswers A r a).length = r a := by
  simp [truthTableAnswers]

/-- For a decidable indexed family, the answer word is the decided membership of each index below
the query count. -/
theorem truthTableAnswers_eq_map_range (A : Set (α × ℕ)) [DecidablePred (· ∈ A)] (r : α → ℕ)
    (a : α) : truthTableAnswers A r a = (List.range (r a)).map fun i => decide ((a, i) ∈ A) := by
  apply List.ext_getElem (by simp [truthTableAnswers])
  intro i hi₁ hi₂
  simp [truthTableAnswers]

/-- Answers for the complemented family are the negated answers. -/
theorem truthTableAnswers_compl (A : Set (α × ℕ)) (r : α → ℕ) (a : α) :
    truthTableAnswers Aᶜ r a = (truthTableAnswers A r a).map (!·) := by
  classical
  apply List.ext_getElem (by simp [truthTableAnswers])
  intro i hi₁ hi₂
  simp [truthTableAnswers]

/-- `A` truth-table reduces to `B` by admissible data: some query count `r`, query map `q` and
combiner `d` satisfying `Good` decide `a ∈ A` from `a` and the answers to `q (a, i)`, `i < r a`. -/
def TruthTableReducibleBy (Good : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop)
    (A : Set α) (B : Set β) : Prop :=
  ∃ r q d, Good r q d ∧ ∀ a, a ∈ A ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true

/-- `A` disjunctively reduces to `B` by admissible data: `a ∈ A` exactly when some query
`q (a, i)` with `i < r a` is in `B`. -/
def DTTReducibleBy (Good : (α → ℕ) → (α × ℕ → β) → Prop) (A : Set α) (B : Set β) : Prop :=
  ∃ r q, Good r q ∧ ∀ a, a ∈ A ↔ ∃ i < r a, q (a, i) ∈ B

/-- `A` conjunctively reduces to `B` by admissible data: `a ∈ A` exactly when every query
`q (a, i)` with `i < r a` is in `B`. -/
def CTTReducibleBy (Good : (α → ℕ) → (α × ℕ → β) → Prop) (A : Set α) (B : Set β) : Prop :=
  ∃ r q, Good r q ∧ ∀ a, a ∈ A ↔ ∀ i < r a, q (a, i) ∈ B

variable {A : Set α} {B : Set β}

namespace TruthTableReducibleBy

variable {Good : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}

/-- More admissible data give more reductions. -/
theorem mono {Good' : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}
    (hle : ∀ r q d, Good r q d → Good' r q d) (h : TruthTableReducibleBy Good A B) :
    TruthTableReducibleBy Good' A B :=
  let ⟨r, q, d, hg, hA⟩ := h
  ⟨r, q, d, hle r q d hg, hA⟩

/-- Negating the combiner reduces `Aᶜ` to `B`, when negated combiners are admissible. -/
theorem compl_left (hneg : ∀ r q d, Good r q d → Good r q fun x => !d x)
    (h : TruthTableReducibleBy Good A B) : TruthTableReducibleBy Good Aᶜ B :=
  let ⟨r, q, d, hg, hA⟩ := h
  ⟨r, q, _, hneg r q d hg, fun a => by simp [hA a]⟩

/-- Negating the answers before the combiner reads them reduces `A` to `Bᶜ`, when such
combiners are admissible. -/
theorem compl_right (hneg : ∀ r q d, Good r q d → Good r q fun x => d (x.1, x.2.map (!·)))
    (h : TruthTableReducibleBy Good A B) : TruthTableReducibleBy Good A Bᶜ :=
  let ⟨r, q, d, hg, hA⟩ := h
  ⟨r, q, _, hneg r q d hg, fun a => by
    rw [hA a, show q ⁻¹' Bᶜ = (q ⁻¹' B)ᶜ from rfl, truthTableAnswers_compl]
    simp [List.map_map, Function.comp_def]⟩

end TruthTableReducibleBy

/-- A many-one reduction is a truth-table reduction asking the single query `f a` and returning
its answer, when that data is admissible. -/
theorem ManyOneReducibleBy.truthTableReducibleBy {GoodF : (α → β) → Prop}
    {Good : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}
    (hgood : ∀ f, GoodF f → Good (fun _ => 1) (fun x => f x.1) fun x => x.2.headD false)
    (h : ManyOneReducibleBy GoodF A B) : TruthTableReducibleBy Good A B :=
  let ⟨f, hf, hA⟩ := h
  ⟨_, _, _, hgood f hf, fun a => by simp [truthTableAnswers, hA a]⟩

namespace DTTReducibleBy

variable {Good : (α → ℕ) → (α × ℕ → β) → Prop}

/-- More admissible data give more reductions. -/
theorem mono {Good' : (α → ℕ) → (α × ℕ → β) → Prop} (hle : ∀ r q, Good r q → Good' r q)
    (h : DTTReducibleBy Good A B) : DTTReducibleBy Good' A B :=
  let ⟨r, q, hg, hA⟩ := h
  ⟨r, q, hle r q hg, hA⟩

/-- A disjunctive reduction is a truth-table reduction with combiner `List.any id`, when that
combiner is admissible. -/
theorem truthTableReducibleBy
    {Good' : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}
    (hgood : ∀ r q, Good r q → Good' r q fun x => x.2.any id) (h : DTTReducibleBy Good A B) :
    TruthTableReducibleBy Good' A B :=
  let ⟨r, q, hg, hA⟩ := h
  ⟨r, q, _, hgood r q hg, fun a => by
    simp [hA a, truthTableAnswers, List.any_eq_true, List.mem_ofFn, Fin.exists_iff]⟩

end DTTReducibleBy

namespace CTTReducibleBy

variable {Good : (α → ℕ) → (α × ℕ → β) → Prop}

/-- More admissible data give more reductions. -/
theorem mono {Good' : (α → ℕ) → (α × ℕ → β) → Prop} (hle : ∀ r q, Good r q → Good' r q)
    (h : CTTReducibleBy Good A B) : CTTReducibleBy Good' A B :=
  let ⟨r, q, hg, hA⟩ := h
  ⟨r, q, hle r q hg, hA⟩

/-- A conjunctive reduction is a truth-table reduction with combiner `List.all id`, when that
combiner is admissible. -/
theorem truthTableReducibleBy
    {Good' : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}
    (hgood : ∀ r q, Good r q → Good' r q fun x => x.2.all id) (h : CTTReducibleBy Good A B) :
    TruthTableReducibleBy Good' A B :=
  let ⟨r, q, hg, hA⟩ := h
  ⟨r, q, _, hgood r q hg, fun a => by
    simp [hA a, truthTableAnswers, List.all_eq_true, List.mem_ofFn, Fin.forall_iff]⟩

end CTTReducibleBy

/-- A many-one reduction is a disjunctive reduction asking the single query `f a`, when that data
is admissible. -/
theorem ManyOneReducibleBy.dttReducibleBy {GoodF : (α → β) → Prop}
    {Good : (α → ℕ) → (α × ℕ → β) → Prop} (hgood : ∀ f, GoodF f → Good (fun _ => 1) fun x => f x.1)
    (h : ManyOneReducibleBy GoodF A B) : DTTReducibleBy Good A B :=
  let ⟨f, hf, hA⟩ := h
  ⟨_, _, hgood f hf, fun a => by simp [hA a]⟩

/-- A many-one reduction is a conjunctive reduction asking the single query `f a`, when that data
is admissible. -/
theorem ManyOneReducibleBy.cttReducibleBy {GoodF : (α → β) → Prop}
    {Good : (α → ℕ) → (α × ℕ → β) → Prop} (hgood : ∀ f, GoodF f → Good (fun _ => 1) fun x => f x.1)
    (h : ManyOneReducibleBy GoodF A B) : CTTReducibleBy Good A B :=
  let ⟨f, hf, hA⟩ := h
  ⟨_, _, hgood f hf, fun a => by simp [hA a]⟩

/-- **De Morgan duality.** The disjunctive reductions of `A` to `B` are the conjunctive reductions
of `Aᶜ` to `Bᶜ`, with the same data. -/
theorem dttReducibleBy_iff_cttReducibleBy_compl {Good : (α → ℕ) → (α × ℕ → β) → Prop} :
    DTTReducibleBy Good A B ↔ CTTReducibleBy Good Aᶜ Bᶜ :=
  exists₂_congr fun _ _ => and_congr_right fun _ => forall_congr' fun _ =>
    ⟨fun h => by simp [h], fun h => by simpa [not_forall] using not_congr h⟩

end Cslib.Complexity

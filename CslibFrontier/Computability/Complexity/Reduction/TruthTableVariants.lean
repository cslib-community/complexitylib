/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction.TruthTable
import CslibFrontier.Computability.Complexity.Reduction.TruthTable.Composition
import CslibFrontier.Foundations.Data.List.Filter
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup

/-!
# Bounded, disjunctive, conjunctive and positive truth-table reductions

Restrictions of polynomial-time truth-table reductions
(`Cslib.Complexity.PolyTimeTruthTableReducible`) [Ladner, Lynch and Selman][LadnerLynchSelman1975]:

* a **`k`-truth-table** reduction makes at most `k` queries, and a **bounded truth-table**
  reduction makes at most `k` queries for some fixed `k`;
* a **disjunctive** (**conjunctive**) truth-table reduction accepts exactly when some (every)
  query is in the target set, so it needs no combiner;
* a **positive** truth-table reduction has a combiner that is monotone in the answers. Positivity
  is taken semantically, as a monotone polynomial-time combiner; it is not the syntactic notion
  of a Boolean formula built from `∧` and `∨`.

Each definition is by definition an instance of a resource-free kernel of
`CslibFrontier.Computability.Reduction.TruthTable` (`Cslib.Complexity.TruthTableReducibleBy`,
`Cslib.Complexity.DTTReducibleBy` or `Cslib.Complexity.CTTReducibleBy`), with the query bound or
monotonicity condition grouped with the resource conditions. The inclusions, complementation and
duality below are applications of the kernel lemmas.

## Main definitions

* `Cslib.Complexity.PolyTimeKTruthTableReducible`, `Cslib.Complexity.PolyTimeBTTReducible`.
* `Cslib.Complexity.PolyTimeDTTReducible`, `Cslib.Complexity.PolyTimeCTTReducible`.
* `Cslib.Complexity.PolyTimePTTReducible`.

## Main results

* The hierarchy `≤ₘ ⇒ ≤₁-tt ⇒ ≤ₖ-tt ⇒ ≤btt ⇒ ≤tt` and `≤ₘ ⇒ ≤dtt, ≤ctt ⇒ ≤ptt ⇒ ≤tt`:
  `Cslib.Complexity.PolyTimeReducible.polyTimeKTruthTableReducible_one`,
  `Cslib.Complexity.PolyTimeKTruthTableReducible.mono`,
  `Cslib.Complexity.PolyTimeKTruthTableReducible.polyTimeBTTReducible`,
  `Cslib.Complexity.PolyTimeBTTReducible.polyTimeTruthTableReducible`,
  `Cslib.Complexity.PolyTimeReducible.polyTimeDTTReducible`,
  `Cslib.Complexity.PolyTimeReducible.polyTimeCTTReducible`,
  `Cslib.Complexity.PolyTimeDTTReducible.polyTimePTTReducible`,
  `Cslib.Complexity.PolyTimeCTTReducible.polyTimePTTReducible`,
  `Cslib.Complexity.PolyTimePTTReducible.polyTimeTruthTableReducible`.
* `Cslib.Complexity.polyTimeDTTReducible_iff_polyTimeCTTReducible_compl`: disjunctive reductions
  of `L` to `B` are the conjunctive reductions of `Lᶜ` to `Bᶜ`.
* Transitivity: `Cslib.Complexity.PolyTimeTruthTableReducible.trans`,
  `Cslib.Complexity.PolyTimeKTruthTableReducible.trans` (`k`- and `k'`-query reductions compose to a
  `k * k'`-query reduction), `Cslib.Complexity.PolyTimeBTTReducible.trans`,
  `Cslib.Complexity.PolyTimeDTTReducible.trans`, `Cslib.Complexity.PolyTimeCTTReducible.trans`,
  `Cslib.Complexity.PolyTimePTTReducible.trans`.
* Reflexivity of bounded, disjunctive and conjunctive truth-table reducibility:
  `Cslib.Complexity.PolyTimeBTTReducible.refl`, `Cslib.Complexity.PolyTimeDTTReducible.refl`,
  `Cslib.Complexity.PolyTimeCTTReducible.refl`.
* Closure of `P` under bounded, disjunctive, conjunctive and positive truth-table reductions:
  `Cslib.Complexity.PolyTimeBTTReducible.mem_P`, `Cslib.Complexity.PolyTimeDTTReducible.mem_P`,
  `Cslib.Complexity.PolyTimeCTTReducible.mem_P`, `Cslib.Complexity.PolyTimePTTReducible.mem_P`.

## References

* [R. E. Ladner, N. A. Lynch, A. L. Selman, *A comparison of polynomial time
  reducibilities*][LadnerLynchSelman1975]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {L : Set α} {B : Set β}

/-! ### Bounded truth-table reductions -/

/-- A truth-table reduction making at most `k` queries on every input. -/
def PolyTimeKTruthTableReducible (k : ℕ) (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (L : Set α) (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β) (d : α × List Bool → Bool),
    (ComputableInPolyTime r encA encUnary ∧
      ComputableInPolyTime q (encPair encA encUnary) encB ∧
      ComputableInPolyTime d (encPair encA encBits) encBool ∧
      ∀ a, r a ≤ k) ∧
    ∀ a, a ∈ L ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true

/-- A truth-table reduction making a bounded number of queries. -/
def PolyTimeBTTReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (L : Set α)
    (B : Set β) : Prop :=
  ∃ k, PolyTimeKTruthTableReducible k encA encB L B

/-- A many-one reduction is a `1`-truth-table reduction. -/
theorem PolyTimeReducible.polyTimeKTruthTableReducible_one (h : PolyTimeReducible encA encB L B) :
    PolyTimeKTruthTableReducible 1 encA encB L B :=
  ManyOneReducibleBy.truthTableReducibleBy
    (fun _ hf => ⟨by fun_prop, by fun_prop, by fun_prop, fun _ => le_rfl⟩) h

/-- Allowing more queries. -/
theorem PolyTimeKTruthTableReducible.mono {k k' : ℕ}
    (h : PolyTimeKTruthTableReducible k encA encB L B) (hk : k ≤ k') :
    PolyTimeKTruthTableReducible k' encA encB L B :=
  TruthTableReducibleBy.mono
    (fun _ _ _ ⟨hr, hq, hd, hrk⟩ => ⟨hr, hq, hd, fun a => (hrk a).trans hk⟩) h

/-- A `k`-truth-table reduction is a bounded truth-table reduction. -/
theorem PolyTimeKTruthTableReducible.polyTimeBTTReducible {k : ℕ}
    (h : PolyTimeKTruthTableReducible k encA encB L B) : PolyTimeBTTReducible encA encB L B :=
  ⟨k, h⟩

/-- A bounded truth-table reduction is a truth-table reduction. -/
theorem PolyTimeBTTReducible.polyTimeTruthTableReducible (h : PolyTimeBTTReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB L B :=
  let ⟨_, h⟩ := h
  TruthTableReducibleBy.mono (fun _ _ _ ⟨hr, hq, hd, _⟩ => ⟨hr, hq, hd⟩) h

/-- A many-one reduction is a bounded truth-table reduction. -/
theorem PolyTimeReducible.polyTimeBTTReducible (h : PolyTimeReducible encA encB L B) :
    PolyTimeBTTReducible encA encB L B :=
  h.polyTimeKTruthTableReducible_one.polyTimeBTTReducible

/-- Bounded truth-table reducibility is reflexive. -/
@[refl]
theorem PolyTimeBTTReducible.refl (encA : α ↪ List Bool) (L : Set α) :
    PolyTimeBTTReducible encA encA L L :=
  (PolyTimeReducible.refl encA L).polyTimeBTTReducible

/-- Negating the combiner keeps the queries, so a `k`-truth-table reduction from `L` to `B` gives
one from `Lᶜ` to `B`. -/
theorem PolyTimeKTruthTableReducible.compl_left {k : ℕ}
    (h : PolyTimeKTruthTableReducible k encA encB L B) :
    PolyTimeKTruthTableReducible k encA encB Lᶜ B :=
  TruthTableReducibleBy.compl_left (fun _ _ _ ⟨hr, hq, hd, hrk⟩ => ⟨hr, hq, by fun_prop, hrk⟩) h

/-- `P` is closed under bounded truth-table reductions. -/
theorem PolyTimeBTTReducible.mem_P (h : PolyTimeBTTReducible encA encB L B) (hB : B ∈ P encB) :
    L ∈ P encA :=
  h.polyTimeTruthTableReducible.mem_P hB

variable {γ : Type} {encC : γ ↪ List Bool} {C : Set γ}

/-! ### Composition of truth-table reductions

The composite of `(r, q, d)` from `L` to `B` and `(r', q', d')` from `B` to `C` asks, for each
first-stage query `q (a, i)`, its second-stage queries in a block of `M a ≥ r' (q (a, i))`
positions starting at `i * M a`, and combines the answers with `truthTableCompCombiner`, whose
correctness is `mem_iff_truthTableCompCombiner`. -/

/-- Queries of the composite: every second-stage query of every first-stage query, in blocks of
`M a` (some may be unused). -/
private def ttCompQueries (r : α → ℕ) (q : α × ℕ → β) (q' : β × ℕ → γ) (M : α → ℕ) (a : α) :
    List γ :=
  (List.range (r a)).flatMap fun i => (List.range (M a)).map fun j => q' (q (a, i), j)

private def ttCompQuery (r : α → ℕ) (q : α × ℕ → β) (q' : β × ℕ → γ) (M : α → ℕ) (x : α × ℕ) : γ :=
  (ttCompQueries r q q' M x.1)[x.2]?.getD (q' (q (x.1, 0), 0))

/-- Block `i` of the composite queries lists the second-stage queries of `q (a, i)`. -/
private theorem ttCompQuery_mul_add {r : α → ℕ} {q : α × ℕ → β} {r' : β → ℕ}
    {q' : β × ℕ → γ} {M : α → ℕ} (hM : ∀ a, ∀ i < r a, r' (q (a, i)) ≤ M a) (a : α) (i : ℕ)
    (hi : i < r a) (j : ℕ) (hj : j < r' (q (a, i))) :
    ttCompQuery r q q' M (a, i * M a + j) = q' (q (a, i), j) := by
  have hjM : j < M a := hj.trans_le (hM a i hi)
  simp only [ttCompQuery, ttCompQueries]
  rw [List.getElem?_flatMap_mul_add _ _ (M a) (fun _ _ => by simp) (by simpa using hi) hjM]
  simp [hjM]

private theorem computableInPolyTime_ttCompQuery {r : α → ℕ} {q : α × ℕ → β} {q' : β × ℕ → γ}
    {M : α → ℕ} (hr : ComputableInPolyTime r encA encUnary)
    (hq : ComputableInPolyTime q (encPair encA encUnary) encB)
    (hq' : ComputableInPolyTime q' (encPair encB encUnary) encC)
    (hM : ComputableInPolyTime M encA encUnary) :
    ComputableInPolyTime (ttCompQuery r q q' M) (encPair encA encUnary) encC := by
  unfold ttCompQuery ttCompQueries
  fun_prop

private theorem computableInPolyTime_truthTableCompCombiner {r : α → ℕ} {q : α × ℕ → β}
    {d : α × List Bool → Bool} {r' : β → ℕ} {d' : β × List Bool → Bool} {M : α → ℕ}
    (hr : ComputableInPolyTime r encA encUnary)
    (hq : ComputableInPolyTime q (encPair encA encUnary) encB)
    (hd : ComputableInPolyTime d (encPair encA encBits) encBool)
    (hr' : ComputableInPolyTime r' encB encUnary)
    (hd' : ComputableInPolyTime d' (encPair encB encBits) encBool)
    (hM : ComputableInPolyTime M encA encUnary) :
    ComputableInPolyTime (truthTableCompCombiner r q d r' d' M) (encPair encA encBits)
      encBool := by
  unfold truthTableCompCombiner
  fun_prop

/-- A polynomial-time block size `M` bounding the number of second-stage queries of every
first-stage query. -/
private theorem exists_ttComp_bound {r : α → ℕ} {q : α × ℕ → β} {r' : β → ℕ}
    (hr : ComputableInPolyTime r encA encUnary)
    (hq : ComputableInPolyTime q (encPair encA encUnary) encB)
    (hr' : ComputableInPolyTime r' encB encUnary) :
    ∃ M : α → ℕ, ComputableInPolyTime M encA encUnary ∧ ∀ a, ∀ i < r a, r' (q (a, i)) ≤ M a :=
  ⟨fun a => ((List.range (r a)).flatMap fun i => List.range (r' (q (a, i)))).length,
    by fun_prop, fun a i hi => by
      simp only [List.length_flatMap, List.length_range]
      exact List.le_sum_of_mem (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)⟩

/-- **Truth-table reductions compose.** -/
@[trans]
theorem PolyTimeTruthTableReducible.trans (hLB : PolyTimeTruthTableReducible encA encB L B)
    (hBC : PolyTimeTruthTableReducible encB encC B C) :
    PolyTimeTruthTableReducible encA encC L C := by
  obtain ⟨r, q, d, ⟨hr, hq, hd⟩, hL⟩ := hLB
  obtain ⟨r', q', d', ⟨hr', hq', hd'⟩, hB⟩ := hBC
  obtain ⟨M, hM, hcM⟩ := exists_ttComp_bound hr hq hr'
  exact ⟨fun a => r a * M a, ttCompQuery r q q' M, truthTableCompCombiner r q d r' d' M,
    ⟨by fun_prop, computableInPolyTime_ttCompQuery hr hq hq' hM,
      computableInPolyTime_truthTableCompCombiner hr hq hd hr' hd' hM⟩,
    mem_iff_truthTableCompCombiner hL hB hcM (ttCompQuery_mul_add hcM)⟩

/-- Composing a `k`-truth-table and a `k'`-truth-table reduction gives a `k * k'`-truth-table
reduction. -/
theorem PolyTimeKTruthTableReducible.trans {k k' : ℕ}
    (hLB : PolyTimeKTruthTableReducible k encA encB L B)
    (hBC : PolyTimeKTruthTableReducible k' encB encC B C) :
    PolyTimeKTruthTableReducible (k * k') encA encC L C := by
  obtain ⟨r, q, d, ⟨hr, hq, hd, hrk⟩, hL⟩ := hLB
  obtain ⟨r', q', d', ⟨hr', hq', hd', hrk'⟩, hB⟩ := hBC
  have hM : ComputableInPolyTime (fun _ : α => k') encA encUnary := .const k'
  have hcM : ∀ a, ∀ i < r a, r' (q (a, i)) ≤ k' := fun _ _ _ => hrk' _
  exact ⟨fun a => r a * k', ttCompQuery r q q' fun _ => k',
    truthTableCompCombiner r q d r' d' fun _ => k',
    ⟨by fun_prop, computableInPolyTime_ttCompQuery hr hq hq' hM,
      computableInPolyTime_truthTableCompCombiner hr hq hd hr' hd' hM,
      fun a => Nat.mul_le_mul_right k' (hrk a)⟩,
    mem_iff_truthTableCompCombiner hL hB hcM (ttCompQuery_mul_add hcM)⟩

/-- **Bounded truth-table reductions compose.** -/
@[trans]
theorem PolyTimeBTTReducible.trans (hLB : PolyTimeBTTReducible encA encB L B)
    (hBC : PolyTimeBTTReducible encB encC B C) : PolyTimeBTTReducible encA encC L C :=
  let ⟨_, h₁⟩ := hLB
  let ⟨_, h₂⟩ := hBC
  ⟨_, h₁.trans h₂⟩

/-! ### Disjunctive and conjunctive truth-table reductions -/

/-- `a ∈ L` exactly when some of the `r a` queries `q (a, i)` is in `B`. -/
def PolyTimeDTTReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (L : Set α)
    (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β),
    (ComputableInPolyTime r encA encUnary ∧ ComputableInPolyTime q (encPair encA encUnary) encB) ∧
    ∀ a, a ∈ L ↔ ∃ i < r a, q (a, i) ∈ B

/-- `a ∈ L` exactly when every one of the `r a` queries `q (a, i)` is in `B`. -/
def PolyTimeCTTReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (L : Set α)
    (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β),
    (ComputableInPolyTime r encA encUnary ∧ ComputableInPolyTime q (encPair encA encUnary) encB) ∧
    ∀ a, a ∈ L ↔ ∀ i < r a, q (a, i) ∈ B

/-- Disjunctive reductions of `L` to `B` are the conjunctive reductions of `Lᶜ` to `Bᶜ`, with the
same queries. -/
theorem polyTimeDTTReducible_iff_polyTimeCTTReducible_compl :
    PolyTimeDTTReducible encA encB L B ↔ PolyTimeCTTReducible encA encB Lᶜ Bᶜ :=
  dttReducibleBy_iff_cttReducibleBy_compl

/-- A many-one reduction is a disjunctive reduction with one query. -/
theorem PolyTimeReducible.polyTimeDTTReducible (h : PolyTimeReducible encA encB L B) :
    PolyTimeDTTReducible encA encB L B :=
  ManyOneReducibleBy.dttReducibleBy (fun _ hf => ⟨by fun_prop, by fun_prop⟩) h

/-- A many-one reduction is a conjunctive reduction with one query. -/
theorem PolyTimeReducible.polyTimeCTTReducible (h : PolyTimeReducible encA encB L B) :
    PolyTimeCTTReducible encA encB L B :=
  ManyOneReducibleBy.cttReducibleBy (fun _ hf => ⟨by fun_prop, by fun_prop⟩) h

/-- Disjunctive truth-table reducibility is reflexive. -/
@[refl]
theorem PolyTimeDTTReducible.refl (encA : α ↪ List Bool) (L : Set α) :
    PolyTimeDTTReducible encA encA L L :=
  (PolyTimeReducible.refl encA L).polyTimeDTTReducible

/-- Conjunctive truth-table reducibility is reflexive. -/
@[refl]
theorem PolyTimeCTTReducible.refl (encA : α ↪ List Bool) (L : Set α) :
    PolyTimeCTTReducible encA encA L L :=
  (PolyTimeReducible.refl encA L).polyTimeCTTReducible

/-- Composing disjunctive reductions: the queries of the composite are all second-stage queries of
all first-stage queries, listed in order; the composite accepts when one of them is in `C`. -/
@[trans]
theorem PolyTimeDTTReducible.trans
    (hLB : PolyTimeDTTReducible encA encB L B) (hBC : PolyTimeDTTReducible encB encC B C) :
    PolyTimeDTTReducible encA encC L C := by
  obtain ⟨r, q, ⟨hr, hq⟩, hL⟩ := hLB
  obtain ⟨r', q', ⟨hr', hq'⟩, hB⟩ := hBC
  let Q : α → List γ := fun a => (List.range (r a)).flatMap fun i =>
    (List.range (r' (q (a, i)))).map fun j => q' (q (a, i), j)
  have hQ : ComputableInPolyTime Q encA (encList encC) := by fun_prop
  refine ⟨fun a => (Q a).length, fun x => (Q x.1)[x.2]?.getD (q' (q (x.1, 0), 0)),
    ⟨by fun_prop, by fun_prop⟩, fun a => ?_⟩
  have hmem : (∃ c ∈ Q a, c ∈ C) ↔ ∃ t < (Q a).length, (Q a)[t]?.getD (q' (q (a, 0), 0)) ∈ C := by
    constructor
    · rintro ⟨c, hc, hcC⟩
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hc
      exact ⟨t, ht, by simpa [List.getElem?_eq_getElem ht] using hcC⟩
    · rintro ⟨t, ht, htC⟩
      exact ⟨_, List.getElem_mem ht, by simpa [List.getElem?_eq_getElem ht] using htC⟩
  rw [← hmem, hL a]
  simp only [Q, List.mem_flatMap, List.mem_range, List.mem_map, hB]
  constructor
  · rintro ⟨i, hi, j, hj, hjC⟩
    exact ⟨_, ⟨i, hi, j, hj, rfl⟩, hjC⟩
  · rintro ⟨c, ⟨i, hi, j, hj, rfl⟩, hcC⟩
    exact ⟨i, hi, j, hj, hcC⟩

/-- Composing conjunctive reductions, by duality with disjunctive reductions. -/
@[trans]
theorem PolyTimeCTTReducible.trans
    (hLB : PolyTimeCTTReducible encA encB L B) (hBC : PolyTimeCTTReducible encB encC B C) :
    PolyTimeCTTReducible encA encC L C := by
  have h := polyTimeDTTReducible_iff_polyTimeCTTReducible_compl (encA := encA) (encB := encC)
    (L := Lᶜ) (B := Cᶜ)
  rw [compl_compl, compl_compl] at h
  refine h.mp (PolyTimeDTTReducible.trans (encB := encB) (B := Bᶜ) ?_ ?_)
  · rwa [polyTimeDTTReducible_iff_polyTimeCTTReducible_compl, compl_compl, compl_compl]
  · rwa [polyTimeDTTReducible_iff_polyTimeCTTReducible_compl, compl_compl, compl_compl]

/-! ### Positive truth-table reductions -/

/-- A truth-table reduction whose combiner is monotone in the answers: turning answers from
`false` to `true` never turns acceptance into rejection. -/
def PolyTimePTTReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (L : Set α)
    (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β) (d : α × List Bool → Bool),
    (ComputableInPolyTime r encA encUnary ∧
      ComputableInPolyTime q (encPair encA encUnary) encB ∧
      ComputableInPolyTime d (encPair encA encBits) encBool ∧
      ∀ a u v, List.Forall₂ (· ≤ ·) u v → d (a, u) ≤ d (a, v)) ∧
    ∀ a, a ∈ L ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true

/-- A positive truth-table reduction is a truth-table reduction. -/
theorem PolyTimePTTReducible.polyTimeTruthTableReducible (h : PolyTimePTTReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB L B :=
  TruthTableReducibleBy.mono (fun _ _ _ ⟨hr, hq, hd, _⟩ => ⟨hr, hq, hd⟩) h

/-- A disjunctive reduction is positive, with the disjunction of the answers as combiner. -/
theorem PolyTimeDTTReducible.polyTimePTTReducible (h : PolyTimeDTTReducible encA encB L B) :
    PolyTimePTTReducible encA encB L B :=
  DTTReducibleBy.truthTableReducibleBy
    (fun _ _ ⟨hr, hq⟩ => ⟨hr, hq, by fun_prop, fun _ _ _ => List.any_id_le_of_forall₂⟩) h

/-- A conjunctive reduction is positive, with the conjunction of the answers as combiner. -/
theorem PolyTimeCTTReducible.polyTimePTTReducible (h : PolyTimeCTTReducible encA encB L B) :
    PolyTimePTTReducible encA encB L B :=
  CTTReducibleBy.truthTableReducibleBy
    (fun _ _ ⟨hr, hq⟩ => ⟨hr, hq, by fun_prop, fun _ _ _ => List.all_id_le_of_forall₂⟩) h

/-- A disjunctive truth-table reduction is a truth-table reduction. -/
theorem PolyTimeDTTReducible.polyTimeTruthTableReducible (h : PolyTimeDTTReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB L B :=
  h.polyTimePTTReducible.polyTimeTruthTableReducible

/-- A conjunctive truth-table reduction is a truth-table reduction. -/
theorem PolyTimeCTTReducible.polyTimeTruthTableReducible (h : PolyTimeCTTReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB L B :=
  h.polyTimePTTReducible.polyTimeTruthTableReducible

/-- `P` is closed under disjunctive truth-table reductions. -/
theorem PolyTimeDTTReducible.mem_P (h : PolyTimeDTTReducible encA encB L B) (hB : B ∈ P encB) :
    L ∈ P encA :=
  h.polyTimeTruthTableReducible.mem_P hB

/-- `P` is closed under conjunctive truth-table reductions. -/
theorem PolyTimeCTTReducible.mem_P (h : PolyTimeCTTReducible encA encB L B) (hB : B ∈ P encB) :
    L ∈ P encA :=
  h.polyTimeTruthTableReducible.mem_P hB

/-- `P` is closed under positive truth-table reductions. -/
theorem PolyTimePTTReducible.mem_P (h : PolyTimePTTReducible encA encB L B) (hB : B ∈ P encB) :
    L ∈ P encA :=
  h.polyTimeTruthTableReducible.mem_P hB

/-- **Positive truth-table reductions compose.** -/
@[trans]
theorem PolyTimePTTReducible.trans (hLB : PolyTimePTTReducible encA encB L B)
    (hBC : PolyTimePTTReducible encB encC B C) : PolyTimePTTReducible encA encC L C := by
  obtain ⟨r, q, d, ⟨hr, hq, hd, hdm⟩, hL⟩ := hLB
  obtain ⟨r', q', d', ⟨hr', hq', hd', hdm'⟩, hB⟩ := hBC
  obtain ⟨M, hM, hcM⟩ := exists_ttComp_bound hr hq hr'
  exact ⟨fun a => r a * M a, ttCompQuery r q q' M, truthTableCompCombiner r q d r' d' M,
    ⟨by fun_prop, computableInPolyTime_ttCompQuery hr hq hq' hM,
      computableInPolyTime_truthTableCompCombiner hr hq hd hr' hd' hM,
      truthTableCompCombiner_mono hdm hdm'⟩,
    mem_iff_truthTableCompCombiner hL hB hcM (ttCompQuery_mul_add hcM)⟩

end Cslib.Complexity

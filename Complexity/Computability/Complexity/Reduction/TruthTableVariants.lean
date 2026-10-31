/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction.TruthTable
import Complexity.Foundations.Data.List.Filter
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup

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
* Reflexivity and closure of `P` for each reducibility.

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
    ComputableInPolyTime r encA encUnary ∧
    ComputableInPolyTime q (encPair encA encUnary) encB ∧
    ComputableInPolyTime d (encPair encA encBits) encBool ∧
    (∀ a, r a ≤ k) ∧ ∀ a, a ∈ L ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true

/-- A truth-table reduction making a bounded number of queries. -/
def PolyTimeBTTReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (L : Set α)
    (B : Set β) : Prop :=
  ∃ k, PolyTimeKTruthTableReducible k encA encB L B

/-- A many-one reduction is a `1`-truth-table reduction. -/
theorem PolyTimeReducible.polyTimeKTruthTableReducible_one (h : PolyTimeReducible encA encB L B) :
    PolyTimeKTruthTableReducible 1 encA encB L B := by
  obtain ⟨f, hf, hL⟩ := h
  refine ⟨fun _ => 1, fun x => f x.1, fun x => x.2.headD false, by fun_prop, by fun_prop,
    by fun_prop, fun _ => le_rfl, fun a => ?_⟩
  rw [hL a]
  simp [truthTableAnswers]

/-- Allowing more queries. -/
theorem PolyTimeKTruthTableReducible.mono {k k' : ℕ}
    (h : PolyTimeKTruthTableReducible k encA encB L B) (hk : k ≤ k') :
    PolyTimeKTruthTableReducible k' encA encB L B :=
  let ⟨r, q, d, hr, hq, hd, hrk, hL⟩ := h
  ⟨r, q, d, hr, hq, hd, fun a => (hrk a).trans hk, hL⟩

/-- A `k`-truth-table reduction is a bounded truth-table reduction. -/
theorem PolyTimeKTruthTableReducible.polyTimeBTTReducible {k : ℕ}
    (h : PolyTimeKTruthTableReducible k encA encB L B) : PolyTimeBTTReducible encA encB L B :=
  ⟨k, h⟩

/-- A bounded truth-table reduction is a truth-table reduction. -/
theorem PolyTimeBTTReducible.polyTimeTruthTableReducible (h : PolyTimeBTTReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB L B :=
  let ⟨_, r, q, d, hr, hq, hd, _, hL⟩ := h
  ⟨r, q, d, hr, hq, hd, hL⟩

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
    PolyTimeKTruthTableReducible k encA encB Lᶜ B := by
  obtain ⟨r, q, d, hr, hq, hd, hrk, hL⟩ := h
  refine ⟨r, q, fun x => !d x, hr, hq, by fun_prop, hrk, fun a => ?_⟩
  simp [Set.mem_compl_iff, hL a]

/-- `P` is closed under bounded truth-table reductions. -/
theorem PolyTimeBTTReducible.mem_P (h : PolyTimeBTTReducible encA encB L B) (hB : B ∈ P encB) :
    L ∈ P encA :=
  h.polyTimeTruthTableReducible.mem_P hB

variable {γ : Type} {encC : γ ↪ List Bool} {C : Set γ}

/-! ### Composition of truth-table reductions

The composite of `(r, q, d)` from `L` to `B` and `(r', q', d')` from `B` to `C` asks, for each
first-stage query `q (a, i)`, its second-stage queries in a block of `M a ≥ r' (q (a, i))`
positions starting at `i * M a`, and evaluates `d'` on each block and `d` on the results. -/

/-- Indexing a flattened list whose blocks all have length `M`. -/
private theorem getElem?_flatMap_of_length_eq {ι δ : Type*} (l : List ι) (f : ι → List δ) (M : ℕ)
    (hf : ∀ x ∈ l, (f x).length = M) {i j : ℕ} (hi : i < l.length) (hj : j < M) :
    (l.flatMap f)[i * M + j]? = (f l[i])[j]? := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x l ih =>
    have hx := hf x (by simp)
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      simp only [zero_mul, zero_add, List.getElem_cons_zero]
      rw [List.getElem?_append_left (by omega)]
    | succ i =>
      rw [List.getElem?_append_right (by rw [hx]; nlinarith), hx]
      have : (i + 1) * M + j - M = i * M + j := by rw [Nat.succ_mul]; omega
      rw [this, ih (fun y hy => hf y (by simp [hy])) (by simpa using hi)]
      simp

/-- A block of a word of answers. -/
private theorem take_drop_ofFn {n : ℕ} (g : Fin n → Bool) (s c : ℕ) (h : s + c ≤ n) :
    ((List.ofFn g).drop s).take c = List.ofFn fun j : Fin c => g ⟨s + j, by omega⟩ := by
  apply List.ext_getElem
  · simp; omega
  · intro k h₁ h₂
    simp [List.getElem_take, List.getElem_drop]

/-- Queries of the composite: every second-stage query of every first-stage query, in blocks of
`M a` (some may be unused). -/
private def ttCompQueries (r : α → ℕ) (q : α × ℕ → β) (q' : β × ℕ → γ) (M : α → ℕ) (a : α) :
    List γ :=
  (List.range (r a)).flatMap fun i => (List.range (M a)).map fun j => q' (q (a, i), j)

private def ttCompQuery (r : α → ℕ) (q : α × ℕ → β) (q' : β × ℕ → γ) (M : α → ℕ) (x : α × ℕ) : γ :=
  (ttCompQueries r q q' M x.1)[x.2]?.getD (q' (q (x.1, 0), 0))

private def ttCompCombiner (r : α → ℕ) (q : α × ℕ → β) (d : α × List Bool → Bool) (r' : β → ℕ)
    (d' : β × List Bool → Bool) (M : α → ℕ) (x : α × List Bool) : Bool :=
  d (x.1, (List.range (r x.1)).map fun i =>
    d' (q (x.1, i), (x.2.drop (i * M x.1)).take (r' (q (x.1, i)))))

private theorem ttComp_spec {r : α → ℕ} {q : α × ℕ → β} {d : α × List Bool → Bool} {r' : β → ℕ}
    {q' : β × ℕ → γ} {d' : β × List Bool → Bool} {M : α → ℕ}
    (hL : ∀ a, a ∈ L ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true)
    (hB : ∀ b, b ∈ B ↔ d' (b, truthTableAnswers (q' ⁻¹' C) r' b) = true)
    (hM : ∀ a, ∀ i < r a, r' (q (a, i)) ≤ M a) (a : α) :
    a ∈ L ↔ ttCompCombiner r q d r' d' M
      (a, truthTableAnswers (ttCompQuery r q q' M ⁻¹' C) (fun a => r a * M a) a) = true := by
  classical
  rw [hL a, ttCompCombiner, truthTableAnswers_eq_map_range]
  dsimp only
  suffices hmap : ((List.range (r a)).map fun i => d' (q (a, i),
      ((truthTableAnswers (ttCompQuery r q q' M ⁻¹' C) (fun a => r a * M a) a).drop
        (i * M a)).take (r' (q (a, i))))) =
      (List.range (r a)).map fun i => decide ((a, i) ∈ q ⁻¹' B) by rw [hmap]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  have hlen : ∀ x ∈ List.range (r a),
      ((List.range (M a)).map fun j => q' (q (a, x), j)).length = M a :=
    fun _ _ => by simp
  have hblock : ((truthTableAnswers (ttCompQuery r q q' M ⁻¹' C) (fun a => r a * M a) a).drop
      (i * M a)).take (r' (q (a, i))) = truthTableAnswers (q' ⁻¹' C) r' (q (a, i)) := by
    rw [truthTableAnswers, take_drop_ofFn _ _ _ (by have := hM a i hi; nlinarith)]
    apply List.ofFn_inj.mpr
    funext j
    have hj : j.1 < M a := lt_of_lt_of_le j.2 (hM a i hi)
    simp only [Set.mem_preimage, ttCompQuery, ttCompQueries]
    rw [getElem?_flatMap_of_length_eq _ _ _ hlen (by simpa using hi) hj]
    simp [hj]
  rw [hblock]
  cases h : d' (q (a, i), truthTableAnswers (q' ⁻¹' C) r' (q (a, i))) <;> simp [hB, h]

private theorem computableInPolyTime_ttCompQuery {r : α → ℕ} {q : α × ℕ → β} {q' : β × ℕ → γ}
    {M : α → ℕ} (hr : ComputableInPolyTime r encA encUnary)
    (hq : ComputableInPolyTime q (encPair encA encUnary) encB)
    (hq' : ComputableInPolyTime q' (encPair encB encUnary) encC)
    (hM : ComputableInPolyTime M encA encUnary) :
    ComputableInPolyTime (ttCompQuery r q q' M) (encPair encA encUnary) encC := by
  unfold ttCompQuery ttCompQueries
  fun_prop

private theorem computableInPolyTime_ttCompCombiner {r : α → ℕ} {q : α × ℕ → β}
    {d : α × List Bool → Bool} {r' : β → ℕ} {d' : β × List Bool → Bool} {M : α → ℕ}
    (hr : ComputableInPolyTime r encA encUnary)
    (hq : ComputableInPolyTime q (encPair encA encUnary) encB)
    (hd : ComputableInPolyTime d (encPair encA encBits) encBool)
    (hr' : ComputableInPolyTime r' encB encUnary)
    (hd' : ComputableInPolyTime d' (encPair encB encBits) encBool)
    (hM : ComputableInPolyTime M encA encUnary) :
    ComputableInPolyTime (ttCompCombiner r q d r' d' M) (encPair encA encBits) encBool := by
  unfold ttCompCombiner
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
  obtain ⟨r, q, d, hr, hq, hd, hL⟩ := hLB
  obtain ⟨r', q', d', hr', hq', hd', hB⟩ := hBC
  obtain ⟨M, hM, hcM⟩ := exists_ttComp_bound hr hq hr'
  exact ⟨fun a => r a * M a, ttCompQuery r q q' M, ttCompCombiner r q d r' d' M, by fun_prop,
    computableInPolyTime_ttCompQuery hr hq hq' hM,
    computableInPolyTime_ttCompCombiner hr hq hd hr' hd' hM, ttComp_spec hL hB hcM⟩

/-- Composing a `k`-truth-table and a `k'`-truth-table reduction gives a `k * k'`-truth-table
reduction. -/
theorem PolyTimeKTruthTableReducible.trans {k k' : ℕ}
    (hLB : PolyTimeKTruthTableReducible k encA encB L B)
    (hBC : PolyTimeKTruthTableReducible k' encB encC B C) :
    PolyTimeKTruthTableReducible (k * k') encA encC L C := by
  obtain ⟨r, q, d, hr, hq, hd, hrk, hL⟩ := hLB
  obtain ⟨r', q', d', hr', hq', hd', hrk', hB⟩ := hBC
  have hM : ComputableInPolyTime (fun _ : α => k') encA encUnary := .const k'
  exact ⟨fun a => r a * k', ttCompQuery r q q' fun _ => k', ttCompCombiner r q d r' d' fun _ => k',
    by fun_prop, computableInPolyTime_ttCompQuery hr hq hq' hM,
    computableInPolyTime_ttCompCombiner hr hq hd hr' hd' hM,
    fun a => Nat.mul_le_mul_right k' (hrk a), ttComp_spec hL hB fun _ _ _ => hrk' _⟩

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
  ∃ (r : α → ℕ) (q : α × ℕ → β), ComputableInPolyTime r encA encUnary ∧
    ComputableInPolyTime q (encPair encA encUnary) encB ∧
    ∀ a, a ∈ L ↔ ∃ i < r a, q (a, i) ∈ B

/-- `a ∈ L` exactly when every one of the `r a` queries `q (a, i)` is in `B`. -/
def PolyTimeCTTReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (L : Set α)
    (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β), ComputableInPolyTime r encA encUnary ∧
    ComputableInPolyTime q (encPair encA encUnary) encB ∧
    ∀ a, a ∈ L ↔ ∀ i < r a, q (a, i) ∈ B

/-- Disjunctive reductions of `L` to `B` are the conjunctive reductions of `Lᶜ` to `Bᶜ`, with the
same queries. -/
theorem polyTimeDTTReducible_iff_polyTimeCTTReducible_compl :
    PolyTimeDTTReducible encA encB L B ↔ PolyTimeCTTReducible encA encB Lᶜ Bᶜ := by
  constructor
  · rintro ⟨r, q, hr, hq, hL⟩
    exact ⟨r, q, hr, hq, fun a => by simp [hL a]⟩
  · rintro ⟨r, q, hr, hq, hL⟩
    refine ⟨r, q, hr, hq, fun a => ?_⟩
    have := not_congr (hL a)
    simp only [Set.mem_compl_iff, not_not, not_forall, exists_prop] at this
    exact this

/-- A many-one reduction is a disjunctive reduction with one query. -/
theorem PolyTimeReducible.polyTimeDTTReducible (h : PolyTimeReducible encA encB L B) :
    PolyTimeDTTReducible encA encB L B := by
  obtain ⟨f, hf, hL⟩ := h
  exact ⟨fun _ => 1, fun x => f x.1, by fun_prop, by fun_prop, fun a => by simp [hL a]⟩

/-- A many-one reduction is a conjunctive reduction with one query. -/
theorem PolyTimeReducible.polyTimeCTTReducible (h : PolyTimeReducible encA encB L B) :
    PolyTimeCTTReducible encA encB L B := by
  obtain ⟨f, hf, hL⟩ := h
  exact ⟨fun _ => 1, fun x => f x.1, by fun_prop, by fun_prop, fun a => by simp [hL a]⟩

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
  obtain ⟨r, q, hr, hq, hL⟩ := hLB
  obtain ⟨r', q', hr', hq', hB⟩ := hBC
  let Q : α → List γ := fun a => (List.range (r a)).flatMap fun i =>
    (List.range (r' (q (a, i)))).map fun j => q' (q (a, i), j)
  have hQ : ComputableInPolyTime Q encA (encList encC) := by fun_prop
  refine ⟨fun a => (Q a).length, fun x => (Q x.1)[x.2]?.getD (q' (q (x.1, 0), 0)),
    by fun_prop, by fun_prop, fun a => ?_⟩
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
    ComputableInPolyTime r encA encUnary ∧
    ComputableInPolyTime q (encPair encA encUnary) encB ∧
    ComputableInPolyTime d (encPair encA encBits) encBool ∧
    (∀ a u v, List.Forall₂ (· ≤ ·) u v → d (a, u) ≤ d (a, v)) ∧
    ∀ a, a ∈ L ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true

/-- A positive truth-table reduction is a truth-table reduction. -/
theorem PolyTimePTTReducible.polyTimeTruthTableReducible (h : PolyTimePTTReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB L B :=
  let ⟨r, q, d, hr, hq, hd, _, hL⟩ := h
  ⟨r, q, d, hr, hq, hd, hL⟩

/-- A disjunctive reduction is positive, with the disjunction of the answers as combiner. -/
theorem PolyTimeDTTReducible.polyTimePTTReducible (h : PolyTimeDTTReducible encA encB L B) :
    PolyTimePTTReducible encA encB L B := by
  obtain ⟨r, q, hr, hq, hL⟩ := h
  refine ⟨r, q, fun x => x.2.any id, hr, hq, by fun_prop,
    fun _ _ _ huv => List.any_id_le_of_forall₂ huv, fun a => ?_⟩
  rw [hL a]
  simp [truthTableAnswers, List.any_eq_true, List.mem_ofFn, Fin.exists_iff]

/-- A conjunctive reduction is positive, with the conjunction of the answers as combiner. -/
theorem PolyTimeCTTReducible.polyTimePTTReducible (h : PolyTimeCTTReducible encA encB L B) :
    PolyTimePTTReducible encA encB L B := by
  obtain ⟨r, q, hr, hq, hL⟩ := h
  refine ⟨r, q, fun x => x.2.all id, hr, hq, by fun_prop,
    fun _ _ _ huv => List.all_id_le_of_forall₂ huv, fun a => ?_⟩
  rw [hL a]
  simp [truthTableAnswers, List.all_eq_true, List.mem_ofFn, Fin.forall_iff]

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

/-- The composite combiner is monotone when both combiners are. -/
private theorem ttCompCombiner_mono {r : α → ℕ} {q : α × ℕ → β} {d : α × List Bool → Bool}
    {r' : β → ℕ} {d' : β × List Bool → Bool} {M : α → ℕ}
    (hd : ∀ a u v, List.Forall₂ (· ≤ ·) u v → d (a, u) ≤ d (a, v))
    (hd' : ∀ b u v, List.Forall₂ (· ≤ ·) u v → d' (b, u) ≤ d' (b, v)) (a : α)
    (u v : List Bool) (huv : List.Forall₂ (· ≤ ·) u v) :
    ttCompCombiner r q d r' d' M (a, u) ≤ ttCompCombiner r q d r' d' M (a, v) := by
  refine hd _ _ _ ?_
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun i _ => hd' _ _ _ ?_
  exact List.forall₂_take _ (List.forall₂_drop _ huv)

/-- **Positive truth-table reductions compose.** -/
@[trans]
theorem PolyTimePTTReducible.trans (hLB : PolyTimePTTReducible encA encB L B)
    (hBC : PolyTimePTTReducible encB encC B C) : PolyTimePTTReducible encA encC L C := by
  obtain ⟨r, q, d, hr, hq, hd, hdm, hL⟩ := hLB
  obtain ⟨r', q', d', hr', hq', hd', hdm', hB⟩ := hBC
  obtain ⟨M, hM, hcM⟩ := exists_ttComp_bound hr hq hr'
  exact ⟨fun a => r a * M a, ttCompQuery r q q' M, ttCompCombiner r q d r' d' M, by fun_prop,
    computableInPolyTime_ttCompQuery hr hq hq' hM,
    computableInPolyTime_ttCompCombiner hr hq hd hr' hd' hM,
    ttCompCombiner_mono hdm hdm', ttComp_spec hL hB hcM⟩

end Cslib.Complexity

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction.TruthTable
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Bounded, disjunctive, conjunctive and positive truth-table reductions

Restrictions of polynomial-time truth-table reductions
(`Cslib.Complexity.PolyTimeTruthTableReducible`) [Ladner, Lynch and Selman][LadnerLynchSelman1975]:

* a **`k`-truth-table** reduction makes at most `k` queries, and a **bounded truth-table**
  reduction makes at most `k` queries for some fixed `k`;
* a **disjunctive** (**conjunctive**) truth-table reduction accepts exactly when some (every)
  query is in the target set, so it needs no combiner;
* a **positive** truth-table reduction has a combiner that is monotone in the answers.

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
* `Cslib.Complexity.polyTimeDTTReducible_compl_iff`: disjunctive reductions of `L` to `B` are the
  conjunctive reductions of `Lᶜ` to `Bᶜ`.
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

theorem PolyTimeKTruthTableReducible.polyTimeBTTReducible {k : ℕ}
    (h : PolyTimeKTruthTableReducible k encA encB L B) : PolyTimeBTTReducible encA encB L B :=
  ⟨k, h⟩

theorem PolyTimeBTTReducible.polyTimeTruthTableReducible (h : PolyTimeBTTReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB L B :=
  let ⟨_, r, q, d, hr, hq, hd, _, hL⟩ := h
  ⟨r, q, d, hr, hq, hd, hL⟩

theorem PolyTimeReducible.polyTimeBTTReducible (h : PolyTimeReducible encA encB L B) :
    PolyTimeBTTReducible encA encB L B :=
  h.polyTimeKTruthTableReducible_one.polyTimeBTTReducible

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

theorem PolyTimeBTTReducible.mem_P (h : PolyTimeBTTReducible encA encB L B) (hB : B ∈ P encB) :
    L ∈ P encA :=
  h.polyTimeTruthTableReducible.mem_P hB

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
theorem polyTimeDTTReducible_compl_iff :
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

@[refl]
theorem PolyTimeDTTReducible.refl (encA : α ↪ List Bool) (L : Set α) :
    PolyTimeDTTReducible encA encA L L :=
  (PolyTimeReducible.refl encA L).polyTimeDTTReducible

@[refl]
theorem PolyTimeCTTReducible.refl (encA : α ↪ List Bool) (L : Set α) :
    PolyTimeCTTReducible encA encA L L :=
  (PolyTimeReducible.refl encA L).polyTimeCTTReducible

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

theorem PolyTimePTTReducible.polyTimeTruthTableReducible (h : PolyTimePTTReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB L B :=
  let ⟨r, q, d, hr, hq, hd, _, hL⟩ := h
  ⟨r, q, d, hr, hq, hd, hL⟩

/-- The disjunction of an answer word is computable in polynomial time. -/
private theorem computableInPolyTime_any_answers :
    ComputableInPolyTime (fun x : α × List Bool => x.2.any id) (encPair encA encBits) encBool :=
  .of_tidy (ComputableTidilyInPolyTime.anyWithEncoding (encA := encBool) (encL := encBits)
    (test := fun p : α × Bool => p.2) (.snd encA encBool) (.fst encA encBits)
    (.snd encA encBits))

/-- The conjunction of an answer word is computable in polynomial time. -/
private theorem computableInPolyTime_all_answers :
    ComputableInPolyTime (fun x : α × List Bool => x.2.all id) (encPair encA encBits) encBool :=
  .of_tidy (ComputableTidilyInPolyTime.allWithEncoding (encA := encBool) (encL := encBits)
    (test := fun p : α × Bool => p.2) (.snd encA encBool) (.fst encA encBits)
    (.snd encA encBits))

private theorem any_id_le_of_forall₂ {u v : List Bool} (h : List.Forall₂ (· ≤ ·) u v) :
    u.any id ≤ v.any id := by
  induction h with
  | nil => exact le_rfl
  | cons hab _ ih =>
    simp only [List.any_cons, id]
    exact max_le_max hab ih

private theorem all_id_le_of_forall₂ {u v : List Bool} (h : List.Forall₂ (· ≤ ·) u v) :
    u.all id ≤ v.all id := by
  induction h with
  | nil => exact le_rfl
  | cons hab _ ih =>
    simp only [List.all_cons, id]
    exact min_le_min hab ih

/-- A disjunctive reduction is positive, with the disjunction of the answers as combiner. -/
theorem PolyTimeDTTReducible.polyTimePTTReducible (h : PolyTimeDTTReducible encA encB L B) :
    PolyTimePTTReducible encA encB L B := by
  obtain ⟨r, q, hr, hq, hL⟩ := h
  refine ⟨r, q, fun x => x.2.any id, hr, hq, computableInPolyTime_any_answers,
    fun _ _ _ huv => any_id_le_of_forall₂ huv, fun a => ?_⟩
  rw [hL a]
  simp [truthTableAnswers, List.any_eq_true, List.mem_ofFn, Fin.exists_iff]

/-- A conjunctive reduction is positive, with the conjunction of the answers as combiner. -/
theorem PolyTimeCTTReducible.polyTimePTTReducible (h : PolyTimeCTTReducible encA encB L B) :
    PolyTimePTTReducible encA encB L B := by
  obtain ⟨r, q, hr, hq, hL⟩ := h
  refine ⟨r, q, fun x => x.2.all id, hr, hq, computableInPolyTime_all_answers,
    fun _ _ _ huv => all_id_le_of_forall₂ huv, fun a => ?_⟩
  rw [hL a]
  simp [truthTableAnswers, List.all_eq_true, List.mem_ofFn, Fin.forall_iff]

theorem PolyTimeDTTReducible.polyTimeTruthTableReducible (h : PolyTimeDTTReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB L B :=
  h.polyTimePTTReducible.polyTimeTruthTableReducible

theorem PolyTimeCTTReducible.polyTimeTruthTableReducible (h : PolyTimeCTTReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB L B :=
  h.polyTimePTTReducible.polyTimeTruthTableReducible

theorem PolyTimeDTTReducible.mem_P (h : PolyTimeDTTReducible encA encB L B) (hB : B ∈ P encB) :
    L ∈ P encA :=
  h.polyTimeTruthTableReducible.mem_P hB

theorem PolyTimeCTTReducible.mem_P (h : PolyTimeCTTReducible encA encB L B) (hB : B ∈ P encB) :
    L ∈ P encA :=
  h.polyTimeTruthTableReducible.mem_P hB

theorem PolyTimePTTReducible.mem_P (h : PolyTimePTTReducible encA encB L B) (hB : B ∈ P encB) :
    L ∈ P encA :=
  h.polyTimeTruthTableReducible.mem_P hB

end Cslib.Complexity

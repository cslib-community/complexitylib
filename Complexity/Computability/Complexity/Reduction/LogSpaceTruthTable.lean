/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace
public import Complexity.Computability.Complexity.Reduction.TruthTable
public import Complexity.Computability.Complexity.Reduction.TruthTableVariants
import Complexity.Foundations.Data.List.Filter
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Words
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words

/-!
# Logspace truth-table reductions and restricted variants

A logspace truth-table reduction (`LogSpaceTruthTableReducible`, $A \le_{tt}^L B$) is a
nonadaptive oracle reduction in logarithmic space: on input `a : α`, a logspace count map
`r : α → ℕ` (with unary output `encUnary`) and a logspace indexed query generator
`q : α × ℕ → β` determine the queries `q (a, 0), …, q (a, r a - 1)` before any oracle answer is
seen, and a logspace evaluator `d : α × List Bool → Bool` combines `a` and the answer bit
vector `truthTableAnswers (q ⁻¹' B) r a` into the decision for `a`
(adapting the polynomial-time scheme of [Ladner, Lynch and Selman][LadnerLynchSelman1975] to
logarithmic space).

**Design choice.** The literature uses two inequivalent conventions for logspace truth-table
evaluation: requiring the evaluator `d` to be computable in logarithmic space (`L`), or restricting
truth tables to Boolean formulas / `NC¹` evaluators. This module adopts the `L`-evaluator
convention so that both query generation and truth-table evaluation lie in `L`, ensuring that
bounded-query truth-table reductions preserve membership in `L` and compose in `L`. No equivalence
with the formula/`NC¹` convention is claimed.

This module also defines the standard restricted logspace truth-table notions mirroring
`TruthTableVariants`:

* **`k`-query truth-table** (`LogSpaceKTruthTableReducible k`): at most `k` nonadaptive queries per
  input (`∀ a, r a ≤ k`).
* **Bounded truth-table** (`LogSpaceBTTReducible`): `k`-query truth-table for some constant `k`.
* **Disjunctive truth-table** (`LogSpaceDTTReducible`): accepts iff at least one query lies in `B`.
* **Conjunctive truth-table** (`LogSpaceCTTReducible`): accepts iff every query lies in `B`.
* **Positive truth-table** (`LogSpacePTTReducible`): the evaluator is monotone in the answer bit
  vector with respect to `List.Forall₂ (· ≤ ·)`.

## Main definitions

* `Cslib.Complexity.LogSpaceTruthTableReducible`: logspace nonadaptive reduction.
* `Cslib.Complexity.LogSpaceKTruthTableReducible`: at most `k` logspace nonadaptive queries.
* `Cslib.Complexity.LogSpaceBTTReducible`: bounded-query logspace truth-table reduction.
* `Cslib.Complexity.LogSpaceDTTReducible`: logspace disjunctive truth-table reduction.
* `Cslib.Complexity.LogSpaceCTTReducible`: logspace conjunctive truth-table reduction.
* `Cslib.Complexity.LogSpacePTTReducible`: logspace positive truth-table reduction.

## Main results

* Inclusions within logspace:
  `LogSpaceReducible.logSpaceKTruthTableReducible_one`,
  `LogSpaceKTruthTableReducible.mono`,
  `LogSpaceKTruthTableReducible.logSpaceBTTReducible`,
  `LogSpaceBTTReducible.logSpaceTruthTableReducible`,
  `LogSpaceReducible.logSpaceBTTReducible`,
  `LogSpaceReducible.logSpaceTruthTableReducible`,
  `LogSpaceReducible.logSpaceDTTReducible`,
  `LogSpaceReducible.logSpaceCTTReducible`,
  `LogSpaceDTTReducible.logSpacePTTReducible`,
  `LogSpaceCTTReducible.logSpacePTTReducible`,
  `LogSpacePTTReducible.logSpaceTruthTableReducible`,
  `LogSpaceDTTReducible.logSpaceTruthTableReducible`,
  `LogSpaceCTTReducible.logSpaceTruthTableReducible`.
* Embeddings into polynomial-time reductions and `P`-closure:
  `LogSpaceTruthTableReducible.polyTimeTruthTableReducible`,
  `LogSpaceKTruthTableReducible.polyTimeKTruthTableReducible`,
  `LogSpaceBTTReducible.polyTimeBTTReducible`,
  `LogSpaceDTTReducible.polyTimeDTTReducible`,
  `LogSpaceCTTReducible.polyTimeCTTReducible`,
  `LogSpacePTTReducible.polyTimePTTReducible`, and `.mem_P` for each variant.
* Reflexivity and complementation:
  `refl` for `LogSpaceTruthTableReducible`, `LogSpaceBTTReducible`, `LogSpaceDTTReducible`,
  `LogSpaceCTTReducible`, `LogSpacePTTReducible`;
  `compl_left`, `compl_right`, `compl` for `LogSpaceTruthTableReducible`,
  `LogSpaceKTruthTableReducible`, `LogSpaceBTTReducible`;
  `logSpaceDTTReducible_iff_logSpaceCTTReducible_compl`.
* Closure of `L` and transitivity for bounded-query reductions:
  `kTruthTable_mem_L`, `LogSpaceKTruthTableReducible.mem_L`, `LogSpaceBTTReducible.mem_L`,
  `LogSpaceKTruthTableReducible.trans`, `LogSpaceBTTReducible.trans`.

## References

* [R. E. Ladner, N. A. Lynch, A. L. Selman, *A comparison of polynomial time
  reducibilities*][LadnerLynchSelman1975]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.5][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {A : Set α} {B : Set β} {C : Set γ}

/-! ### Definitions -/

/-- `A` truth-table reduces to `B` in logarithmic space: a logspace query count `r` (with unary
output `encUnary`), a logspace indexed query generator `q` producing `q (a, i)` for `i < r a`,
and a logspace evaluator `d` decide `a ∈ A` from `a` and the answer word
`truthTableAnswers (q ⁻¹' B) r a`. -/
def LogSpaceTruthTableReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α)
    (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β) (d : α × List Bool → Bool),
    ComputableInLogSpace r encA encUnary ∧
    ComputableInLogSpace q (encPair encA encUnary) encB ∧
    ComputableInLogSpace d (encPair encA encBits) encBool ∧
    ∀ a, a ∈ A ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true

/-- `A` `k`-truth-table reduces to `B` in logarithmic space: a logspace truth-table reduction
asking at most `k` queries on every input. -/
def LogSpaceKTruthTableReducible (k : ℕ) (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (A : Set α) (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β) (d : α × List Bool → Bool),
    ComputableInLogSpace r encA encUnary ∧
    ComputableInLogSpace q (encPair encA encUnary) encB ∧
    ComputableInLogSpace d (encPair encA encBits) encBool ∧
    (∀ a, r a ≤ k) ∧
    ∀ a, a ∈ A ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true

/-- `A` bounded-truth-table reduces to `B` in logarithmic space: it `k`-truth-table reduces to `B`
in logarithmic space for some constant `k`. -/
def LogSpaceBTTReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α)
    (B : Set β) : Prop :=
  ∃ k, LogSpaceKTruthTableReducible k encA encB A B

/-- `A` disjunctive-truth-table reduces to `B` in logarithmic space: a logspace query generator
`q (a, i)` for `i < r a` such that `a ∈ A` iff at least one query is in `B`. -/
def LogSpaceDTTReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α)
    (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β),
    ComputableInLogSpace r encA encUnary ∧
    ComputableInLogSpace q (encPair encA encUnary) encB ∧
    ∀ a, a ∈ A ↔ ∃ i < r a, q (a, i) ∈ B

/-- `A` conjunctive-truth-table reduces to `B` in logarithmic space: a logspace query generator
`q (a, i)` for `i < r a` such that `a ∈ A` iff every query is in `B`. -/
def LogSpaceCTTReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α)
    (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β),
    ComputableInLogSpace r encA encUnary ∧
    ComputableInLogSpace q (encPair encA encUnary) encB ∧
    ∀ a, a ∈ A ↔ ∀ i < r a, q (a, i) ∈ B

/-- `A` positive-truth-table reduces to `B` in logarithmic space: a logspace truth-table reduction
whose evaluator is monotone in the answer word with respect to `List.Forall₂ (· ≤ ·)`. -/
def LogSpacePTTReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α)
    (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β) (d : α × List Bool → Bool),
    ComputableInLogSpace r encA encUnary ∧
    ComputableInLogSpace q (encPair encA encUnary) encB ∧
    ComputableInLogSpace d (encPair encA encBits) encBool ∧
    (∀ a u v, List.Forall₂ (· ≤ ·) u v → d (a, u) ≤ d (a, v)) ∧
    ∀ a, a ∈ A ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true

/-! ### Inclusions within logarithmic space -/

/-- A logspace many-one reduction is a `1`-truth-table reduction: one query `f a`, with the first
answer bit returned directly. -/
theorem LogSpaceReducible.logSpaceKTruthTableReducible_one
    (h : LogSpaceReducible encA encB A B) : LogSpaceKTruthTableReducible 1 encA encB A B := by
  obtain ⟨f, hf, hA⟩ := h
  refine ⟨fun _ => 1, fun p => f p.1, fun p => p.2.headD false,
    ComputableInLogSpace.const 1, by fun_prop, by fun_prop, fun _ => le_rfl, fun a => ?_⟩
  rw [hA a]
  simp [truthTableAnswers]

/-- `k`-truth-table reducibility in logarithmic space is monotone in the query bound `k`. -/
theorem LogSpaceKTruthTableReducible.mono {k k' : ℕ}
    (h : LogSpaceKTruthTableReducible k encA encB A B) (hk : k ≤ k') :
    LogSpaceKTruthTableReducible k' encA encB A B :=
  let ⟨r, q, d, hr, hq, hd, hrk, hA⟩ := h
  ⟨r, q, d, hr, hq, hd, fun a => (hrk a).trans hk, hA⟩

/-- A `k`-truth-table reduction in logarithmic space is a bounded-truth-table reduction. -/
theorem LogSpaceKTruthTableReducible.logSpaceBTTReducible {k : ℕ}
    (h : LogSpaceKTruthTableReducible k encA encB A B) : LogSpaceBTTReducible encA encB A B :=
  ⟨k, h⟩

/-- A bounded-truth-table reduction in logarithmic space is a truth-table reduction. -/
theorem LogSpaceBTTReducible.logSpaceTruthTableReducible
    (h : LogSpaceBTTReducible encA encB A B) : LogSpaceTruthTableReducible encA encB A B :=
  let ⟨_, r, q, d, hr, hq, hd, _, hA⟩ := h
  ⟨r, q, d, hr, hq, hd, hA⟩

/-- A logspace many-one reduction is a logspace bounded-truth-table reduction. -/
theorem LogSpaceReducible.logSpaceBTTReducible (h : LogSpaceReducible encA encB A B) :
    LogSpaceBTTReducible encA encB A B :=
  h.logSpaceKTruthTableReducible_one.logSpaceBTTReducible

/-- A logspace many-one reduction is a logspace truth-table reduction. -/
theorem LogSpaceReducible.logSpaceTruthTableReducible (h : LogSpaceReducible encA encB A B) :
    LogSpaceTruthTableReducible encA encB A B :=
  h.logSpaceBTTReducible.logSpaceTruthTableReducible

/-- A logspace many-one reduction is a logspace disjunctive truth-table reduction. -/
theorem LogSpaceReducible.logSpaceDTTReducible (h : LogSpaceReducible encA encB A B) :
    LogSpaceDTTReducible encA encB A B := by
  obtain ⟨f, hf, hA⟩ := h
  exact ⟨fun _ => 1, fun p => f p.1, ComputableInLogSpace.const 1, by fun_prop,
    fun a => by simp [hA a]⟩

/-- A logspace many-one reduction is a logspace conjunctive truth-table reduction. -/
theorem LogSpaceReducible.logSpaceCTTReducible (h : LogSpaceReducible encA encB A B) :
    LogSpaceCTTReducible encA encB A B := by
  obtain ⟨f, hf, hA⟩ := h
  exact ⟨fun _ => 1, fun p => f p.1, ComputableInLogSpace.const 1, by fun_prop,
    fun a => by simp [hA a]⟩

/-- A logspace disjunctive truth-table reduction is a logspace positive truth-table reduction,
evaluated by `List.any id`. -/
theorem LogSpaceDTTReducible.logSpacePTTReducible (h : LogSpaceDTTReducible encA encB A B) :
    LogSpacePTTReducible encA encB A B := by
  obtain ⟨r, q, hr, hq, hA⟩ := h
  refine ⟨r, q, fun p => p.2.any id, hr, hq, by fun_prop,
    fun _ _ _ huv => List.any_id_le_of_forall₂ huv, fun a => ?_⟩
  rw [hA a]
  simp [truthTableAnswers, List.any_eq_true, List.mem_ofFn, Fin.exists_iff]

/-- A logspace conjunctive truth-table reduction is a logspace positive truth-table reduction,
evaluated by `List.all id`. -/
theorem LogSpaceCTTReducible.logSpacePTTReducible (h : LogSpaceCTTReducible encA encB A B) :
    LogSpacePTTReducible encA encB A B := by
  obtain ⟨r, q, hr, hq, hA⟩ := h
  refine ⟨r, q, fun p => p.2.all id, hr, hq, by fun_prop,
    fun _ _ _ huv => List.all_id_le_of_forall₂ huv, fun a => ?_⟩
  rw [hA a]
  simp [truthTableAnswers, List.all_eq_true, List.mem_ofFn, Fin.forall_iff]

/-- A logspace positive truth-table reduction is a logspace truth-table reduction. -/
theorem LogSpacePTTReducible.logSpaceTruthTableReducible
    (h : LogSpacePTTReducible encA encB A B) : LogSpaceTruthTableReducible encA encB A B :=
  let ⟨r, q, d, hr, hq, hd, _, hA⟩ := h
  ⟨r, q, d, hr, hq, hd, hA⟩

/-- A logspace disjunctive truth-table reduction is a logspace truth-table reduction. -/
theorem LogSpaceDTTReducible.logSpaceTruthTableReducible
    (h : LogSpaceDTTReducible encA encB A B) : LogSpaceTruthTableReducible encA encB A B :=
  h.logSpacePTTReducible.logSpaceTruthTableReducible

/-- A logspace conjunctive truth-table reduction is a logspace truth-table reduction. -/
theorem LogSpaceCTTReducible.logSpaceTruthTableReducible
    (h : LogSpaceCTTReducible encA encB A B) : LogSpaceTruthTableReducible encA encB A B :=
  h.logSpacePTTReducible.logSpaceTruthTableReducible

/-! ### Embeddings into polynomial-time reductions and `P`-closure -/

/-- Every logspace truth-table reduction is a polynomial-time truth-table reduction. -/
theorem LogSpaceTruthTableReducible.polyTimeTruthTableReducible
    (h : LogSpaceTruthTableReducible encA encB A B) :
    PolyTimeTruthTableReducible encA encB A B := by
  obtain ⟨r, q, d, hr, hq, hd, hA⟩ := h
  exact ⟨r, q, d, hr.computableInPolyTime, hq.computableInPolyTime,
    hd.computableInPolyTime, hA⟩

/-- Every logspace `k`-truth-table reduction is a polynomial-time `k`-truth-table reduction. -/
theorem LogSpaceKTruthTableReducible.polyTimeKTruthTableReducible {k : ℕ}
    (h : LogSpaceKTruthTableReducible k encA encB A B) :
    PolyTimeKTruthTableReducible k encA encB A B := by
  obtain ⟨r, q, d, hr, hq, hd, hrk, hA⟩ := h
  exact ⟨r, q, d, hr.computableInPolyTime, hq.computableInPolyTime,
    hd.computableInPolyTime, hrk, hA⟩

/-- Every logspace bounded-truth-table reduction is a polynomial-time bounded-truth-table
reduction. -/
theorem LogSpaceBTTReducible.polyTimeBTTReducible (h : LogSpaceBTTReducible encA encB A B) :
    PolyTimeBTTReducible encA encB A B :=
  let ⟨k, hk⟩ := h
  ⟨k, hk.polyTimeKTruthTableReducible⟩

/-- Every logspace disjunctive truth-table reduction is a polynomial-time disjunctive truth-table
reduction. -/
theorem LogSpaceDTTReducible.polyTimeDTTReducible (h : LogSpaceDTTReducible encA encB A B) :
    PolyTimeDTTReducible encA encB A B := by
  obtain ⟨r, q, hr, hq, hA⟩ := h
  exact ⟨r, q, hr.computableInPolyTime, hq.computableInPolyTime, hA⟩

/-- Every logspace conjunctive truth-table reduction is a polynomial-time conjunctive truth-table
reduction. -/
theorem LogSpaceCTTReducible.polyTimeCTTReducible (h : LogSpaceCTTReducible encA encB A B) :
    PolyTimeCTTReducible encA encB A B := by
  obtain ⟨r, q, hr, hq, hA⟩ := h
  exact ⟨r, q, hr.computableInPolyTime, hq.computableInPolyTime, hA⟩

/-- Every logspace positive truth-table reduction is a polynomial-time positive truth-table
reduction. -/
theorem LogSpacePTTReducible.polyTimePTTReducible (h : LogSpacePTTReducible encA encB A B) :
    PolyTimePTTReducible encA encB A B := by
  obtain ⟨r, q, d, hr, hq, hd, hmono, hA⟩ := h
  exact ⟨r, q, d, hr.computableInPolyTime, hq.computableInPolyTime,
    hd.computableInPolyTime, hmono, hA⟩

/-- `P` is closed under logspace truth-table reductions. -/
theorem LogSpaceTruthTableReducible.mem_P (h : LogSpaceTruthTableReducible encA encB A B)
    (hB : B ∈ P encB) : A ∈ P encA :=
  h.polyTimeTruthTableReducible.mem_P hB

/-- `P` is closed under logspace `k`-truth-table reductions. -/
theorem LogSpaceKTruthTableReducible.mem_P {k : ℕ}
    (h : LogSpaceKTruthTableReducible k encA encB A B) (hB : B ∈ P encB) : A ∈ P encA :=
  h.logSpaceBTTReducible.logSpaceTruthTableReducible.mem_P hB

/-- `P` is closed under logspace bounded-truth-table reductions. -/
theorem LogSpaceBTTReducible.mem_P (h : LogSpaceBTTReducible encA encB A B) (hB : B ∈ P encB) :
    A ∈ P encA :=
  h.polyTimeBTTReducible.mem_P hB

/-- `P` is closed under logspace disjunctive truth-table reductions. -/
theorem LogSpaceDTTReducible.mem_P (h : LogSpaceDTTReducible encA encB A B) (hB : B ∈ P encB) :
    A ∈ P encA :=
  h.polyTimeDTTReducible.mem_P hB

/-- `P` is closed under logspace conjunctive truth-table reductions. -/
theorem LogSpaceCTTReducible.mem_P (h : LogSpaceCTTReducible encA encB A B) (hB : B ∈ P encB) :
    A ∈ P encA :=
  h.polyTimeCTTReducible.mem_P hB

/-- `P` is closed under logspace positive truth-table reductions. -/
theorem LogSpacePTTReducible.mem_P (h : LogSpacePTTReducible encA encB A B) (hB : B ∈ P encB) :
    A ∈ P encA :=
  h.polyTimePTTReducible.mem_P hB

/-! ### Reflexivity and complementation -/

/-- Every problem truth-table reduces to itself in logarithmic space. -/
@[refl]
theorem LogSpaceTruthTableReducible.refl (encA : α ↪ List Bool) (A : Set α) :
    LogSpaceTruthTableReducible encA encA A A :=
  (LogSpaceReducible.refl encA A).logSpaceTruthTableReducible

/-- Every problem bounded-truth-table reduces to itself in logarithmic space. -/
@[refl]
theorem LogSpaceBTTReducible.refl (encA : α ↪ List Bool) (A : Set α) :
    LogSpaceBTTReducible encA encA A A :=
  (LogSpaceReducible.refl encA A).logSpaceBTTReducible

/-- Every problem disjunctive-truth-table reduces to itself in logarithmic space. -/
@[refl]
theorem LogSpaceDTTReducible.refl (encA : α ↪ List Bool) (A : Set α) :
    LogSpaceDTTReducible encA encA A A :=
  (LogSpaceReducible.refl encA A).logSpaceDTTReducible

/-- Every problem conjunctive-truth-table reduces to itself in logarithmic space. -/
@[refl]
theorem LogSpaceCTTReducible.refl (encA : α ↪ List Bool) (A : Set α) :
    LogSpaceCTTReducible encA encA A A :=
  (LogSpaceReducible.refl encA A).logSpaceCTTReducible

/-- Every problem positive-truth-table reduces to itself in logarithmic space. -/
@[refl]
theorem LogSpacePTTReducible.refl (encA : α ↪ List Bool) (A : Set α) :
    LogSpacePTTReducible encA encA A A :=
  (LogSpaceDTTReducible.refl encA A).logSpacePTTReducible

/-- Negating the evaluator turns a logspace truth-table reduction from `A` to `B` into one from
`Aᶜ` to `B`. -/
theorem LogSpaceTruthTableReducible.compl_left (h : LogSpaceTruthTableReducible encA encB A B) :
    LogSpaceTruthTableReducible encA encB Aᶜ B := by
  obtain ⟨r, q, d, hr, hq, hd, hA⟩ := h
  refine ⟨r, q, fun p => !d p, hr, hq, by fun_prop, fun a => ?_⟩
  simp [Set.mem_compl_iff, hA a]

/-- Negating the answer bits before evaluation turns a logspace truth-table reduction from `A` to
`B` into one from `A` to `Bᶜ`. -/
theorem LogSpaceTruthTableReducible.compl_right (h : LogSpaceTruthTableReducible encA encB A B) :
    LogSpaceTruthTableReducible encA encB A Bᶜ := by
  obtain ⟨r, q, d, hr, hq, hd, hA⟩ := h
  refine ⟨r, q, fun p => d (p.1, p.2.map (!·)), hr, hq, by fun_prop, fun a => ?_⟩
  rw [hA a, show q ⁻¹' Bᶜ = (q ⁻¹' B)ᶜ from rfl, truthTableAnswers_compl]
  simp [List.map_map, Function.comp_def]

/-- A logspace truth-table reduction from `A` to `B` gives one from `Aᶜ` to `Bᶜ`. -/
theorem LogSpaceTruthTableReducible.compl (h : LogSpaceTruthTableReducible encA encB A B) :
    LogSpaceTruthTableReducible encA encB Aᶜ Bᶜ :=
  h.compl_left.compl_right

/-- Negating the evaluator turns a logspace `k`-truth-table reduction from `A` to `B` into one from
`Aᶜ` to `B`. -/
theorem LogSpaceKTruthTableReducible.compl_left {k : ℕ}
    (h : LogSpaceKTruthTableReducible k encA encB A B) :
    LogSpaceKTruthTableReducible k encA encB Aᶜ B := by
  obtain ⟨r, q, d, hr, hq, hd, hrk, hA⟩ := h
  refine ⟨r, q, fun p => !d p, hr, hq, by fun_prop, hrk, fun a => ?_⟩
  simp [Set.mem_compl_iff, hA a]

/-- Negating the answer bits before evaluation turns a logspace `k`-truth-table reduction from `A`
to `B` into one from `A` to `Bᶜ`. -/
theorem LogSpaceKTruthTableReducible.compl_right {k : ℕ}
    (h : LogSpaceKTruthTableReducible k encA encB A B) :
    LogSpaceKTruthTableReducible k encA encB A Bᶜ := by
  obtain ⟨r, q, d, hr, hq, hd, hrk, hA⟩ := h
  refine ⟨r, q, fun p => d (p.1, p.2.map (!·)), hr, hq, by fun_prop, hrk, fun a => ?_⟩
  rw [hA a, show q ⁻¹' Bᶜ = (q ⁻¹' B)ᶜ from rfl, truthTableAnswers_compl]
  simp [List.map_map, Function.comp_def]

/-- A logspace `k`-truth-table reduction from `A` to `B` gives one from `Aᶜ` to `Bᶜ`. -/
theorem LogSpaceKTruthTableReducible.compl {k : ℕ}
    (h : LogSpaceKTruthTableReducible k encA encB A B) :
    LogSpaceKTruthTableReducible k encA encB Aᶜ Bᶜ :=
  h.compl_left.compl_right

/-- Negating the evaluator turns a logspace bounded-truth-table reduction from `A` to `B` into one
from `Aᶜ` to `B`. -/
theorem LogSpaceBTTReducible.compl_left (h : LogSpaceBTTReducible encA encB A B) :
    LogSpaceBTTReducible encA encB Aᶜ B :=
  let ⟨k, hk⟩ := h
  ⟨k, hk.compl_left⟩

/-- Negating the answer bits before evaluation turns a logspace bounded-truth-table reduction from
`A` to `B` into one from `A` to `Bᶜ`. -/
theorem LogSpaceBTTReducible.compl_right (h : LogSpaceBTTReducible encA encB A B) :
    LogSpaceBTTReducible encA encB A Bᶜ :=
  let ⟨k, hk⟩ := h
  ⟨k, hk.compl_right⟩

/-- A logspace bounded-truth-table reduction from `A` to `B` gives one from `Aᶜ` to `Bᶜ`. -/
theorem LogSpaceBTTReducible.compl (h : LogSpaceBTTReducible encA encB A B) :
    LogSpaceBTTReducible encA encB Aᶜ Bᶜ :=
  let ⟨k, hk⟩ := h
  ⟨k, hk.compl⟩

/-- De Morgan duality for logspace disjunctive and conjunctive truth-table reductions: `A`
disjunctively reduces to `B` iff `Aᶜ` conjunctively reduces to `Bᶜ`, by the same queries. -/
theorem logSpaceDTTReducible_iff_logSpaceCTTReducible_compl :
    LogSpaceDTTReducible encA encB A B ↔ LogSpaceCTTReducible encA encB Aᶜ Bᶜ := by
  refine ⟨fun ⟨r, q, hr, hq, hA⟩ => ⟨r, q, hr, hq, fun a => by simp [hA a]⟩,
    fun ⟨r, q, hr, hq, hA⟩ => ⟨r, q, hr, hq, fun a => ?_⟩⟩
  have := not_congr (hA a)
  simpa [not_forall] using this

/-! ### Closure of `L` and transitivity for bounded-query truth-table reductions -/

/-- Kernel for `L`-closure under `k`-query logspace truth-table reductions: evaluating at most `k`
queries of a language in `L` and combining the answers in logspace keeps the language in `L`. -/
theorem kTruthTable_mem_L {k : ℕ} {r : α → ℕ} {q : α × ℕ → β} {d : α × List Bool → Bool}
    (hr : ComputableInLogSpace r encA encUnary)
    (hq : ComputableInLogSpace q (encPair encA encUnary) encB)
    (hd : ComputableInLogSpace d (encPair encA encBits) encBool)
    (hrk : ∀ a, r a ≤ k)
    (hA : ∀ a, a ∈ A ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true)
    (hB : B ∈ L encB) : A ∈ L encA := by
  classical
  obtain ⟨decB, hdecB, hBmem⟩ := hB
  have hans : ComputableInLogSpace
      (fun a => (List.range (r a)).map fun i => decB (q (a, i))) encA encBits :=
    ComputableInLogSpace.mapToBits_range_of_le k hr hrk (hdecB.comp hq)
  refine ⟨fun a => d (a, (List.range (r a)).map fun i => decB (q (a, i))),
    hd.comp (ComputableInLogSpace.pair .id hans), fun a => ?_⟩
  have hdec_eq : ∀ b, decB b = decide (b ∈ B) := fun b =>
    Bool.eq_iff_iff.mpr (by simp [← hBmem b])
  rw [hA a, truthTableAnswers_eq_map_range]
  simp [hdec_eq]

/-- `L` is closed under logspace `k`-truth-table reductions. -/
theorem LogSpaceKTruthTableReducible.mem_L {k : ℕ}
    (h : LogSpaceKTruthTableReducible k encA encB A B) (hB : B ∈ L encB) : A ∈ L encA := by
  obtain ⟨r, q, d, hr, hq, hd, hrk, hA⟩ := h
  exact kTruthTable_mem_L hr hq hd hrk hA hB

/-- `L` is closed under logspace bounded-truth-table reductions. -/
theorem LogSpaceBTTReducible.mem_L (h : LogSpaceBTTReducible encA encB A B) (hB : B ∈ L encB) :
    A ∈ L encA :=
  let ⟨_, hk⟩ := h
  hk.mem_L hB

/-- **Logspace `k`-truth-table reductions compose**, multiplying the query bounds: a `k₁`-query
reduction followed by a `k₂`-query reduction yields a `(k₁ * k₂)`-query reduction. Each of the
`r₁ a` outer queries is expanded into a block of `k₂` inner queries, and the outer evaluator
combines the `r₁ a` inner decisions computed from the corresponding slices of the oracle answer
vector. -/
@[trans]
theorem LogSpaceKTruthTableReducible.trans {k₁ k₂ : ℕ}
    (hAB : LogSpaceKTruthTableReducible k₁ encA encB A B)
    (hBC : LogSpaceKTruthTableReducible k₂ encB encC B C) :
    LogSpaceKTruthTableReducible (k₁ * k₂) encA encC A C := by
  classical
  obtain ⟨r₁, q₁, d₁, hr₁, hq₁, hd₁, hr₁k, hA⟩ := hAB
  obtain ⟨r₂, q₂, d₂, hr₂, hq₂, hd₂, hr₂k, hB⟩ := hBC
  let r (a : α) : ℕ := r₁ a * k₂
  let q (p : α × ℕ) : γ :=
    q₂ (q₁ (p.1, min p.2 (k₁ * k₂) / k₂), min p.2 (k₁ * k₂) % k₂)
  let innerAns (p : (α × List Bool) × ℕ) : Bool :=
    let b := q₁ (p.1.1, p.2)
    d₂ (b, (p.1.2.drop (p.2 * k₂)).take (r₂ b))
  let d (p : α × List Bool) : Bool :=
    d₁ (p.1, (List.range (r₁ p.1)).map fun i => innerAns (p, i))
  have hr : ComputableInLogSpace r encA encUnary := by
    simp only [r]
    fun_prop
  have hq : ComputableInLogSpace q (encPair encA encUnary) encC := by
    simp only [q]
    fun_prop
  have h_innerAns : ComputableInLogSpace innerAns
      (encPair (encPair encA encBits) encUnary) encBool := by
    simp only [innerAns]
    fun_prop
  have h_outerList : ComputableInLogSpace
      (fun p : α × List Bool => (List.range (r₁ p.1)).map fun i => innerAns (p, i))
      (encPair encA encBits) encBits :=
    ComputableInLogSpace.mapToBits_range_of_le k₁ (by fun_prop) (fun p => hr₁k p.1) h_innerAns
  have hd : ComputableInLogSpace d (encPair encA encBits) encBool := by
    simp only [d]
    fun_prop
  refine ⟨r, q, d, hr, hq, hd, fun a => Nat.mul_le_mul_right k₂ (hr₁k a), fun a => ?_⟩
  rw [hA a, truthTableAnswers_eq_map_range]
  dsimp only [d]
  suffices hmap :
      ((List.range (r₁ a)).map fun i =>
          innerAns ((a, truthTableAnswers (q ⁻¹' C) r a), i)) =
        (List.range (r₁ a)).map fun i => decide ((a, i) ∈ q₁ ⁻¹' B) by
    rw [hmap]
  refine List.map_congr_left fun i hi => ?_
  have hi_lt : i < r₁ a := List.mem_range.mp hi
  have hslice_eq :
      ((truthTableAnswers (q ⁻¹' C) r a).drop (i * k₂)).take (r₂ (q₁ (a, i))) =
        truthTableAnswers (q₂ ⁻¹' C) r₂ (q₁ (a, i)) := by
    rw [truthTableAnswers_eq_map_range, truthTableAnswers_eq_map_range]
    have h_end : i * k₂ + r₂ (q₁ (a, i)) ≤ r a := by
      calc i * k₂ + r₂ (q₁ (a, i))
          ≤ i * k₂ + k₂ := Nat.add_le_add_left (hr₂k _) _
        _ = (i + 1) * k₂ := by ring
        _ ≤ r₁ a * k₂ := Nat.mul_le_mul_right k₂ (Nat.succ_le_of_lt hi_lt)
    refine List.ext_getElem ?_ fun j hj₁ hj₂ => ?_
    · simp only [List.length_take, List.length_drop, List.length_map, List.length_range]
      omega
    · simp only [List.length_map, List.length_range] at hj₂
      have hk₂_pos : 0 < k₂ := lt_of_le_of_lt (Nat.zero_le j) (lt_of_lt_of_le hj₂ (hr₂k _))
      have hj_lt_k₂ : j < k₂ := lt_of_lt_of_le hj₂ (hr₂k _)
      have hm_lt_r : i * k₂ + j < r a := lt_of_lt_of_le (Nat.add_lt_add_left hj₂ _) h_end
      have hm_le_M : i * k₂ + j ≤ k₁ * k₂ :=
        le_trans (le_of_lt hm_lt_r) (Nat.mul_le_mul_right k₂ (hr₁k a))
      have hdiv_eq : (i * k₂ + j) / k₂ = i := by
        rw [mul_comm i k₂, Nat.mul_add_div hk₂_pos, Nat.div_eq_of_lt hj_lt_k₂, add_zero]
      have hmod_eq : (i * k₂ + j) % k₂ = j := by
        rw [mul_comm i k₂, Nat.mul_add_mod, Nat.mod_eq_of_lt hj_lt_k₂]
      simp [q, Nat.min_eq_left hm_le_M, hdiv_eq, hmod_eq]
  simp only [innerAns, hslice_eq]
  exact Bool.eq_iff_iff.mpr (by simpa using (hB (q₁ (a, i))).symm)

/-- **Logspace bounded-truth-table reductions compose.** -/
@[trans]
theorem LogSpaceBTTReducible.trans (hAB : LogSpaceBTTReducible encA encB A B)
    (hBC : LogSpaceBTTReducible encB encC B C) : LogSpaceBTTReducible encA encC A C :=
  let ⟨k₁, hk₁⟩ := hAB
  let ⟨k₂, hk₂⟩ := hBC
  ⟨k₁ * k₂, hk₁.trans hk₂⟩

end Cslib.Complexity

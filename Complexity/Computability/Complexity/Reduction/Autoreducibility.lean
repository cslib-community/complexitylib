/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace
public import Complexity.Computability.Complexity.Reduction.TruthTableVariants
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Resource-bounded autoreducibility and mitoticity

A set is **autoreducible** if it reduces to itself by a reduction that never queries its own
input [Ambos-Spies][AmbosSpies1984]. Autoreducibility is the core notion of information redundancy:
can membership of `a` be computed from membership of other instances?

A set is **mitotic** if it can be split by an easy separator `S` into two disjoint pieces,
`A ∩ S` and `A ∖ S`, each computationally equivalent to the whole set
[Ambos-Spies][AmbosSpies1984]. Mitoticity is the structural splitting property of complete sets
[Glaßer, Pavan, Selman and Zhang][GlasserPavanSelmanZhang2008].

## Main definitions

* `Cslib.Complexity.PolyTimeManyOneAutoreducible`: polynomial-time many-one autoreducibility.
* `Cslib.Complexity.LogSpaceManyOneAutoreducible`: logarithmic-space many-one autoreducibility.
* `Cslib.Complexity.PolyTimeKTruthTableAutoreducible`, `Cslib.Complexity.PolyTimeBTTAutoreducible`.
* `Cslib.Complexity.PolyTimeDTTAutoreducible`, `Cslib.Complexity.PolyTimeCTTAutoreducible`.
* `Cslib.Complexity.PolyTimeTruthTableAutoreducible`.
* `Cslib.Complexity.ReducibleEquiv`: mutual reducibility under a binary relation.
* `Cslib.Complexity.MitoticWith`: mitoticity with respect to a class of separators and a reduction.
* `Cslib.Complexity.PolyTimeManyOneMitotic`, `Cslib.Complexity.LogSpaceManyOneMitotic`.
* `Cslib.Complexity.PolyTimeKTruthTableMitotic`, `Cslib.Complexity.PolyTimeDTTMitotic`.
* `Cslib.Complexity.PolyTimeBTTMitotic`, `Cslib.Complexity.PolyTimeTruthTableMitotic`.

## Main results

* The autoreducibility hierarchy:
  `≤ᴸ_m,auto ⇒ ≤ᵖ_m,auto ⇒ ≤ᵖ_1-tt,auto ⇒ ≤ᵖ_k-tt,auto ⇒ ≤ᵖ_btt,auto ⇒ ≤ᵖ_tt,auto` and
  `≤ᵖ_m,auto ⇒ ≤ᵖ_dtt,auto, ≤ᵖ_ctt,auto ⇒ ≤ᵖ_tt,auto`.
* Complements: closure of many-one, `k`-truth-table, bounded truth-table, and truth-table
  autoreducibility under complement, and
  `polyTimeDTTAutoreducible_iff_polyTimeCTTAutoreducible_compl`.
* Sets in `P` and `L`: every problem in `P` is `0-tt` (and hence `k-tt`, `btt`, `tt`)
  autoreducible without any non-triviality assumption.
* Degenerate obstructions: singleton and co-singleton sets are strictly not many-one autoreducible
  (`not_polyTimeManyOneAutoreducible_singleton`,
  `not_polyTimeManyOneAutoreducible_compl_singleton`).
* Exact characterizations: a set in `P` (or `L`) is many-one autoreducible if and only if neither
  it nor its complement is a singleton.
* Mitoticity implies autoreducibility (standard argument of [Ambos-Spies 1984][AmbosSpies1984]
  adapted to truth-table reductions): every `dtt`-, `k-tt`-, `btt`-, or `tt`-mitotic set is
  correspondingly `dtt`-, `k-tt`-, `btt`-, or `tt`-autoreducible unconditionally, and a
  polynomial-time many-one mitotic set is many-one autoreducible if and only if its complement
  is not a singleton.

## References

* [K. Ambos-Spies, *P-mitotic sets*][AmbosSpies1984]
* [C. Gla{\ss}er, A. Pavan, A. L. Selman, L. Zhang, *Splitting NP-complete
  sets*][GlasserPavanSelmanZhang2008]
* [R. E. Ladner, N. A. Lynch, A. L. Selman, *A comparison of polynomial time
  reducibilities*][LadnerLynchSelman1975]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α}

/-! ### Many-one autoreducibility -/

/-- `A` is polynomial-time many-one autoreducible: a polynomial-time map `f` with `∀ a, f a ≠ a`
reduces `A` to itself. -/
def PolyTimeManyOneAutoreducible (encA : α ↪ List Bool) (A : Set α) : Prop :=
  ∃ f : α → α, (ComputableInPolyTime f encA encA ∧ ∀ a, f a ≠ a) ∧ ∀ a, a ∈ A ↔ f a ∈ A

/-- Polynomial-time many-one autoreducibility is many-one reducibility of `A` to itself by a
fixed-point-free polynomial-time map. -/
theorem polyTimeManyOneAutoreducible_iff_manyOneReducibleBy :
    PolyTimeManyOneAutoreducible encA A ↔
      ManyOneReducibleBy (fun f => ComputableInPolyTime f encA encA ∧ ∀ a, f a ≠ a) A A :=
  Iff.rfl

/-- An autoreduction is an ordinary many-one reduction. -/
theorem PolyTimeManyOneAutoreducible.polyTimeReducible (h : PolyTimeManyOneAutoreducible encA A) :
    PolyTimeReducible encA encA A A :=
  let ⟨f, ⟨hf, _⟩, hA⟩ := h
  ⟨f, hf, hA⟩

/-- `A` is logspace many-one autoreducible: a logarithmic-space map `f` with `∀ a, f a ≠ a`
reduces `A` to itself. -/
def LogSpaceManyOneAutoreducible (encA : α ↪ List Bool) (A : Set α) : Prop :=
  ∃ f : α → α, (ComputableInLogSpace f encA encA ∧ ∀ a, f a ≠ a) ∧ ∀ a, a ∈ A ↔ f a ∈ A

/-- Logspace many-one autoreducibility is many-one reducibility of `A` to itself by a
fixed-point-free logspace map. -/
theorem logSpaceManyOneAutoreducible_iff_manyOneReducibleBy :
    LogSpaceManyOneAutoreducible encA A ↔
      ManyOneReducibleBy (fun f => ComputableInLogSpace f encA encA ∧ ∀ a, f a ≠ a) A A :=
  Iff.rfl

/-- A logspace autoreduction is an ordinary logspace reduction. -/
theorem LogSpaceManyOneAutoreducible.logSpaceReducible (h : LogSpaceManyOneAutoreducible encA A) :
    LogSpaceReducible encA encA A A :=
  let ⟨f, ⟨hf, _⟩, hA⟩ := h
  ⟨f, hf, hA⟩

/-- **Logspace many-one autoreducibility implies polynomial-time many-one autoreducibility.** -/
theorem LogSpaceManyOneAutoreducible.polyTimeManyOneAutoreducible
    (h : LogSpaceManyOneAutoreducible encA A) : PolyTimeManyOneAutoreducible encA A :=
  ManyOneReducibleBy.mono (fun _ hf => ⟨hf.1.computableInPolyTime, hf.2⟩) h

/-- Many-one autoreducibility is preserved under taking complements. -/
theorem PolyTimeManyOneAutoreducible.compl (h : PolyTimeManyOneAutoreducible encA A) :
    PolyTimeManyOneAutoreducible encA Aᶜ :=
  ManyOneReducibleBy.compl h

/-- Logspace many-one autoreducibility is preserved under taking complements. -/
theorem LogSpaceManyOneAutoreducible.compl (h : LogSpaceManyOneAutoreducible encA A) :
    LogSpaceManyOneAutoreducible encA Aᶜ :=
  ManyOneReducibleBy.compl h

/-! ### Truth-table autoreducibility variants -/

/-- `A` is `k`-truth-table autoreducible: a `k`-truth-table reduction whose query generator never
queries the input instance `a`. -/
def PolyTimeKTruthTableAutoreducible (k : ℕ) (encA : α ↪ List Bool) (A : Set α) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → α) (d : α × List Bool → Bool),
    ComputableInPolyTime r encA encUnary ∧
    ComputableInPolyTime q (encPair encA encUnary) encA ∧
    ComputableInPolyTime d (encPair encA encBits) encBool ∧
    (∀ a, r a ≤ k) ∧ (∀ a i, i < r a → q (a, i) ≠ a) ∧
    ∀ a, a ∈ A ↔ d (a, truthTableAnswers (q ⁻¹' A) r a) = true

/-- A `k`-truth-table autoreduction is a `k`-truth-table reduction. -/
theorem PolyTimeKTruthTableAutoreducible.polyTimeKTruthTableReducible {k : ℕ}
    (h : PolyTimeKTruthTableAutoreducible k encA A) :
    PolyTimeKTruthTableReducible k encA encA A A :=
  let ⟨r, q, d, hr, hq, hd, hrk, _, hA⟩ := h
  ⟨r, q, d, hr, hq, hd, hrk, hA⟩

/-- `A` is bounded truth-table autoreducible. -/
def PolyTimeBTTAutoreducible (encA : α ↪ List Bool) (A : Set α) : Prop :=
  ∃ k, PolyTimeKTruthTableAutoreducible k encA A

/-- A bounded truth-table autoreduction is a bounded truth-table reduction. -/
theorem PolyTimeBTTAutoreducible.polyTimeBTTReducible (h : PolyTimeBTTAutoreducible encA A) :
    PolyTimeBTTReducible encA encA A A :=
  let ⟨k, h⟩ := h
  ⟨k, h.polyTimeKTruthTableReducible⟩

/-- `A` is disjunctive truth-table autoreducible: accepting exactly when some query is in `A`,
without querying `a`. -/
def PolyTimeDTTAutoreducible (encA : α ↪ List Bool) (A : Set α) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → α),
    ComputableInPolyTime r encA encUnary ∧
    ComputableInPolyTime q (encPair encA encUnary) encA ∧
    (∀ a i, i < r a → q (a, i) ≠ a) ∧ ∀ a, a ∈ A ↔ ∃ i < r a, q (a, i) ∈ A

/-- A disjunctive truth-table autoreduction is a disjunctive truth-table reduction. -/
theorem PolyTimeDTTAutoreducible.polyTimeDTTReducible (h : PolyTimeDTTAutoreducible encA A) :
    PolyTimeDTTReducible encA encA A A :=
  let ⟨r, q, hr, hq, _, hA⟩ := h
  ⟨r, q, hr, hq, hA⟩

/-- `A` is conjunctive truth-table autoreducible: accepting exactly when every query is in `A`,
without querying `a`. -/
def PolyTimeCTTAutoreducible (encA : α ↪ List Bool) (A : Set α) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → α),
    ComputableInPolyTime r encA encUnary ∧
    ComputableInPolyTime q (encPair encA encUnary) encA ∧
    (∀ a i, i < r a → q (a, i) ≠ a) ∧ ∀ a, a ∈ A ↔ ∀ i < r a, q (a, i) ∈ A

/-- A conjunctive truth-table autoreduction is a conjunctive truth-table reduction. -/
theorem PolyTimeCTTAutoreducible.polyTimeCTTReducible (h : PolyTimeCTTAutoreducible encA A) :
    PolyTimeCTTReducible encA encA A A :=
  let ⟨r, q, hr, hq, _, hA⟩ := h
  ⟨r, q, hr, hq, hA⟩

/-- `A` is polynomial-time truth-table autoreducible: a truth-table reduction whose query generator
never queries the input instance. -/
def PolyTimeTruthTableAutoreducible (encA : α ↪ List Bool) (A : Set α) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → α) (d : α × List Bool → Bool),
    ComputableInPolyTime r encA encUnary ∧
    ComputableInPolyTime q (encPair encA encUnary) encA ∧
    ComputableInPolyTime d (encPair encA encBits) encBool ∧
    (∀ a i, i < r a → q (a, i) ≠ a) ∧
    ∀ a, a ∈ A ↔ d (a, truthTableAnswers (q ⁻¹' A) r a) = true

/-- A truth-table autoreduction is a truth-table reduction. -/
theorem PolyTimeTruthTableAutoreducible.polyTimeTruthTableReducible
    (h : PolyTimeTruthTableAutoreducible encA A) :
    PolyTimeTruthTableReducible encA encA A A :=
  let ⟨r, q, d, hr, hq, hd, _, hA⟩ := h
  ⟨r, q, d, hr, hq, hd, hA⟩

/-- A many-one autoreduction is a `1`-truth-table autoreduction. -/
theorem PolyTimeManyOneAutoreducible.polyTimeKTruthTableAutoreducible_one
    (h : PolyTimeManyOneAutoreducible encA A) : PolyTimeKTruthTableAutoreducible 1 encA A := by
  obtain ⟨f, ⟨hf, hne⟩, hA⟩ := h
  refine ⟨fun _ => 1, fun x => f x.1, fun x => x.2.headD false, by fun_prop, by fun_prop,
    by fun_prop, fun _ => le_rfl, fun a _ _ => hne a, fun a => ?_⟩
  rw [hA a]
  simp [truthTableAnswers]

/-- A many-one autoreduction is a disjunctive truth-table autoreduction. -/
theorem PolyTimeManyOneAutoreducible.polyTimeDTTAutoreducible
    (h : PolyTimeManyOneAutoreducible encA A) : PolyTimeDTTAutoreducible encA A := by
  obtain ⟨f, ⟨hf, hne⟩, hA⟩ := h
  exact ⟨fun _ => 1, fun x => f x.1, by fun_prop, by fun_prop, fun a _ _ => hne a,
    fun a => by simp [hA a]⟩

/-- A many-one autoreduction is a conjunctive truth-table autoreduction. -/
theorem PolyTimeManyOneAutoreducible.polyTimeCTTAutoreducible
    (h : PolyTimeManyOneAutoreducible encA A) : PolyTimeCTTAutoreducible encA A := by
  obtain ⟨f, ⟨hf, hne⟩, hA⟩ := h
  exact ⟨fun _ => 1, fun x => f x.1, by fun_prop, by fun_prop, fun a _ _ => hne a,
    fun a => by simp [hA a]⟩

/-- Allowing more queries in a `k`-truth-table autoreduction. -/
theorem PolyTimeKTruthTableAutoreducible.mono {k k' : ℕ}
    (h : PolyTimeKTruthTableAutoreducible k encA A) (hk : k ≤ k') :
    PolyTimeKTruthTableAutoreducible k' encA A :=
  let ⟨r, q, d, hr, hq, hd, hrk, hne, hA⟩ := h
  ⟨r, q, d, hr, hq, hd, fun a => (hrk a).trans hk, hne, hA⟩

/-- A `k`-truth-table autoreduction is a bounded truth-table autoreduction. -/
theorem PolyTimeKTruthTableAutoreducible.polyTimeBTTAutoreducible {k : ℕ}
    (h : PolyTimeKTruthTableAutoreducible k encA A) : PolyTimeBTTAutoreducible encA A :=
  ⟨k, h⟩

/-- A bounded truth-table autoreduction is a truth-table autoreduction. -/
theorem PolyTimeBTTAutoreducible.polyTimeTruthTableAutoreducible
    (h : PolyTimeBTTAutoreducible encA A) : PolyTimeTruthTableAutoreducible encA A :=
  let ⟨_, r, q, d, hr, hq, hd, _, hne, hA⟩ := h
  ⟨r, q, d, hr, hq, hd, hne, hA⟩

/-- A many-one autoreduction is a bounded truth-table autoreduction. -/
theorem PolyTimeManyOneAutoreducible.polyTimeBTTAutoreducible
    (h : PolyTimeManyOneAutoreducible encA A) : PolyTimeBTTAutoreducible encA A :=
  h.polyTimeKTruthTableAutoreducible_one.polyTimeBTTAutoreducible

/-- A many-one autoreduction is a truth-table autoreduction. -/
theorem PolyTimeManyOneAutoreducible.polyTimeTruthTableAutoreducible
    (h : PolyTimeManyOneAutoreducible encA A) : PolyTimeTruthTableAutoreducible encA A :=
  h.polyTimeBTTAutoreducible.polyTimeTruthTableAutoreducible

private theorem computableInPolyTime_any_answers :
    ComputableInPolyTime (fun x : α × List Bool => x.2.any id) (encPair encA encBits) encBool :=
  ComputableInPolyTime.anyWithEncoding (encA := encBool) (encL := encBits)
    (test := fun p : α × Bool => p.2) (.snd encA encBool) (.fst encA encBits)
    (.snd encA encBits)

private theorem computableInPolyTime_all_answers :
    ComputableInPolyTime (fun x : α × List Bool => x.2.all id) (encPair encA encBits) encBool :=
  ComputableInPolyTime.allWithEncoding (encA := encBool) (encL := encBits)
    (test := fun p : α × Bool => p.2) (.snd encA encBool) (.fst encA encBits)
    (.snd encA encBits)

/-- A disjunctive truth-table autoreduction is a truth-table autoreduction. -/
theorem PolyTimeDTTAutoreducible.polyTimeTruthTableAutoreducible
    (h : PolyTimeDTTAutoreducible encA A) : PolyTimeTruthTableAutoreducible encA A := by
  obtain ⟨r, q, hr, hq, hne, hA⟩ := h
  refine ⟨r, q, fun x => x.2.any id, hr, hq, computableInPolyTime_any_answers, hne, fun a => ?_⟩
  rw [hA a]
  simp [truthTableAnswers, List.any_eq_true, List.mem_ofFn, Fin.exists_iff]

/-- A conjunctive truth-table autoreduction is a truth-table autoreduction. -/
theorem PolyTimeCTTAutoreducible.polyTimeTruthTableAutoreducible
    (h : PolyTimeCTTAutoreducible encA A) : PolyTimeTruthTableAutoreducible encA A := by
  obtain ⟨r, q, hr, hq, hne, hA⟩ := h
  refine ⟨r, q, fun x => x.2.all id, hr, hq, computableInPolyTime_all_answers, hne, fun a => ?_⟩
  rw [hA a]
  simp [truthTableAnswers, List.all_eq_true, List.mem_ofFn, Fin.forall_iff]

/-- Complement duality between disjunctive and conjunctive truth-table autoreducibility. -/
theorem polyTimeDTTAutoreducible_iff_polyTimeCTTAutoreducible_compl :
    PolyTimeDTTAutoreducible encA A ↔ PolyTimeCTTAutoreducible encA Aᶜ := by
  constructor
  · rintro ⟨r, q, hr, hq, hne, hA⟩
    exact ⟨r, q, hr, hq, hne, fun a => by simp [hA a]⟩
  · rintro ⟨r, q, hr, hq, hne, hA⟩
    refine ⟨r, q, hr, hq, hne, fun a => ?_⟩
    have := not_congr (hA a)
    simp only [Set.mem_compl_iff, not_not, not_forall, exists_prop] at this
    exact this

private theorem computableInPolyTime_negate_combiner {d : α × List Bool → Bool}
    (hd : ComputableInPolyTime d (encPair encA encBits) encBool) :
    ComputableInPolyTime (fun x : α × List Bool => !d (x.1, x.2.map (!·)))
      (encPair encA encBits) encBool := by
  have hmap : ComputableInPolyTime (fun x : α × List Bool => x.2.map (!·))
      (encPair encA encBits) encBits :=
    ComputableInPolyTime.bitsMapWithInput (f := fun _ b => !b)
      (.snd encA encBits) (by fun_prop)
  have hd' : ComputableInPolyTime (fun x : α × List Bool => d (x.1, x.2.map (!·)))
      (encPair encA encBits) encBool := by fun_prop
  fun_prop

/-- `k`-truth-table autoreducibility is preserved under taking complements. -/
theorem PolyTimeKTruthTableAutoreducible.compl {k : ℕ}
    (h : PolyTimeKTruthTableAutoreducible k encA A) :
    PolyTimeKTruthTableAutoreducible k encA Aᶜ := by
  obtain ⟨r, q, d, hr, hq, hd, hrk, hne, hA⟩ := h
  refine ⟨r, q, fun x => !d (x.1, x.2.map (!·)), hr, hq,
    computableInPolyTime_negate_combiner hd, hrk, hne, fun a => ?_⟩
  rw [Set.mem_compl_iff, hA a, show q ⁻¹' Aᶜ = (q ⁻¹' A)ᶜ from rfl, truthTableAnswers_compl]
  simp [List.map_map, Function.comp_def]

/-- Bounded truth-table autoreducibility is preserved under taking complements. -/
theorem PolyTimeBTTAutoreducible.compl (h : PolyTimeBTTAutoreducible encA A) :
    PolyTimeBTTAutoreducible encA Aᶜ :=
  let ⟨k, hk⟩ := h
  ⟨k, hk.compl⟩

/-- Truth-table autoreducibility is preserved under taking complements. -/
theorem PolyTimeTruthTableAutoreducible.compl (h : PolyTimeTruthTableAutoreducible encA A) :
    PolyTimeTruthTableAutoreducible encA Aᶜ := by
  obtain ⟨r, q, d, hr, hq, hd, hne, hA⟩ := h
  refine ⟨r, q, fun x => !d (x.1, x.2.map (!·)), hr, hq,
    computableInPolyTime_negate_combiner hd, hne, fun a => ?_⟩
  rw [Set.mem_compl_iff, hA a, show q ⁻¹' Aᶜ = (q ⁻¹' A)ᶜ from rfl, truthTableAnswers_compl]
  simp [List.map_map, Function.comp_def]

/-! ### Autoreducibility of sets in `P` and degenerate obstructions -/

/-- **Every problem in `P` is `0-tt` autoreducible**, making 0 queries and deciding `a ∈ A`
internally in polynomial time. -/
theorem PolyTimeKTruthTableAutoreducible.of_mem_P (k : ℕ) (hA : A ∈ P encA) :
    PolyTimeKTruthTableAutoreducible k encA A := by
  obtain ⟨g, hg, hAg⟩ := hA
  exact ⟨fun _ => 0, fun x => x.1, fun x => g x.1, by fun_prop, by fun_prop, by fun_prop,
    fun _ => Nat.zero_le _, fun _ _ hi => (Nat.not_lt_zero _ hi).elim, hAg⟩

/-- Every problem in `P` is bounded truth-table autoreducible. -/
theorem PolyTimeBTTAutoreducible.of_mem_P (hA : A ∈ P encA) :
    PolyTimeBTTAutoreducible encA A :=
  (PolyTimeKTruthTableAutoreducible.of_mem_P 0 hA).polyTimeBTTAutoreducible

/-- Every problem in `P` is truth-table autoreducible. -/
theorem PolyTimeTruthTableAutoreducible.of_mem_P (hA : A ∈ P encA) :
    PolyTimeTruthTableAutoreducible encA A :=
  (PolyTimeBTTAutoreducible.of_mem_P hA).polyTimeTruthTableAutoreducible

/-- A many-one autoreducible set cannot be a singleton, since its element would have no distinct
target member. -/
theorem PolyTimeManyOneAutoreducible.exists_mem_ne (h : PolyTimeManyOneAutoreducible encA A) :
    ∀ a ∈ A, ∃ y ∈ A, y ≠ a := by
  obtain ⟨f, ⟨-, hne⟩, hA⟩ := h
  intro a ha
  exact ⟨f a, (hA a).mp ha, hne a⟩

/-- A many-one autoreducible set cannot have a singleton complement. -/
theorem PolyTimeManyOneAutoreducible.exists_notMem_ne (h : PolyTimeManyOneAutoreducible encA A) :
    ∀ a ∉ A, ∃ n ∉ A, n ≠ a := by
  have hc := h.compl
  exact fun a ha => hc.exists_mem_ne a ha

/-- A logspace many-one autoreducible set cannot be a singleton. -/
theorem LogSpaceManyOneAutoreducible.exists_mem_ne (h : LogSpaceManyOneAutoreducible encA A) :
    ∀ a ∈ A, ∃ y ∈ A, y ≠ a :=
  h.polyTimeManyOneAutoreducible.exists_mem_ne

/-- A logspace many-one autoreducible set cannot have a singleton complement. -/
theorem LogSpaceManyOneAutoreducible.exists_notMem_ne (h : LogSpaceManyOneAutoreducible encA A) :
    ∀ a ∉ A, ∃ n ∉ A, n ≠ a :=
  h.polyTimeManyOneAutoreducible.exists_notMem_ne

/-- A singleton is strictly not polynomial-time many-one autoreducible. -/
theorem not_polyTimeManyOneAutoreducible_singleton (a₀ : α) :
    ¬ PolyTimeManyOneAutoreducible encA {a₀} := by
  intro h
  obtain ⟨y, hy, hne⟩ := h.exists_mem_ne a₀ (Set.mem_singleton a₀)
  exact hne (Set.mem_singleton_iff.mp hy)

/-- A co-singleton is strictly not polynomial-time many-one autoreducible. -/
theorem not_polyTimeManyOneAutoreducible_compl_singleton (a₀ : α) :
    ¬ PolyTimeManyOneAutoreducible encA {a₀}ᶜ := by
  intro h
  have hc := h.compl
  rw [compl_compl] at hc
  exact not_polyTimeManyOneAutoreducible_singleton a₀ hc

/-- A singleton is strictly not logspace many-one autoreducible. -/
theorem not_logSpaceManyOneAutoreducible_singleton (a₀ : α) :
    ¬ LogSpaceManyOneAutoreducible encA {a₀} :=
  fun h => not_polyTimeManyOneAutoreducible_singleton a₀ h.polyTimeManyOneAutoreducible

/-- A co-singleton is strictly not logspace many-one autoreducible. -/
theorem not_logSpaceManyOneAutoreducible_compl_singleton (a₀ : α) :
    ¬ LogSpaceManyOneAutoreducible encA {a₀}ᶜ :=
  fun h => not_polyTimeManyOneAutoreducible_compl_singleton a₀ h.polyTimeManyOneAutoreducible

/-! ### Construction of many-one autoreductions for sets in `L` and `P` -/

private theorem computableInLogSpace_of_exists_finite_ne {f : α → β}
    (h : ∃ b : β, {a : α | f a ≠ b}.Finite) :
    ComputableInLogSpace f encA encB :=
  let ⟨_, h⟩ := computableInTimeAndSpace_of_exists_finite_ne h
  ⟨_, 0, h.mono (fun _ => le_rfl) fun _ => Nat.zero_le _⟩

open scoped Classical in
private theorem computableInLogSpace_decide_eq (x₀ : α) :
    ComputableInLogSpace (fun a => decide (a = x₀)) encA encBool := by
  apply computableInLogSpace_of_exists_finite_ne
  refine ⟨false, (Set.finite_singleton x₀).subset fun a ha => ?_⟩
  by_contra h
  simp [Set.mem_singleton_iff.not.mp h] at ha

open scoped Classical in
private theorem computableInLogSpace_alt (encA : α ↪ List Bool) (x₀ x₁ : α) :
    ComputableInLogSpace (fun a => if a = x₀ then x₁ else x₀) encA encA := by
  apply computableInLogSpace_of_exists_finite_ne
  refine ⟨x₀, (Set.finite_singleton x₀).subset fun a ha => ?_⟩
  by_contra h
  simp [Set.mem_singleton_iff.not.mp h] at ha

open scoped Classical in
private theorem computableInPolyTime_alt (encA : α ↪ List Bool) (x₀ x₁ : α) :
    ComputableInPolyTime (fun a => if a = x₀ then x₁ else x₀) encA encA :=
  (computableInLogSpace_alt encA x₀ x₁).computableInPolyTime

/-- A set in `L` with at least two members and at least two non-members is logspace many-one
autoreducible. -/
theorem LogSpaceManyOneAutoreducible.of_two_mem_two_notMem (hA : A ∈ L encA)
    {y₀ y₁ : α} (hy₀ : y₀ ∈ A) (hy₁ : y₁ ∈ A) (hyne : y₀ ≠ y₁)
    {n₀ n₁ : α} (hn₀ : n₀ ∉ A) (hn₁ : n₁ ∉ A) (hnne : n₀ ≠ n₁) :
    LogSpaceManyOneAutoreducible encA A := by
  classical
  obtain ⟨d, hd, hAd⟩ := hA
  let eqY := computableInLogSpace_decide_eq y₀ (encA := encA)
  let eqN := computableInLogSpace_decide_eq n₀ (encA := encA)
  let eqs := eqY.pair eqN
  let tagged := hd.pair eqs
  let choose : Bool × (Bool × Bool) → α :=
    fun p => if p.1 then (if p.2.1 then y₁ else y₀) else (if p.2.2 then n₁ else n₀)
  have hchoose : ComputableInLogSpace choose
      (encPair encBool (encPair encBool encBool)) encA :=
    ComputableInLogSpace.of_finite choose
  have hf : ComputableInLogSpace (choose ∘ fun a => (d a, (decide (a = y₀), decide (a = n₀))))
      encA encA := hchoose.comp tagged
  refine ⟨_, ⟨hf, fun a => ?_⟩, fun a => ?_⟩
  · dsimp only [choose, Function.comp_apply]
    cases hda : d a
    · simp only [Bool.false_eq_true, ↓reduceIte]
      split_ifs with ha
      · intro heq; simp only [decide_eq_true_eq] at ha; subst ha; exact hnne heq.symm
      · intro heq; exact ha (decide_eq_true heq.symm)
    · simp only [↓reduceIte]
      split_ifs with ha
      · intro heq; simp only [decide_eq_true_eq] at ha; subst ha; exact hyne heq.symm
      · intro heq; exact ha (decide_eq_true heq.symm)
  · dsimp only [choose, Function.comp_apply]
    cases hda : d a
    · have haA : a ∉ A := fun ha => by have := (hAd a).mp ha; rw [hda] at this; contradiction
      simp only [Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> simp [haA, hn₀, hn₁]
    · have haA : a ∈ A := (hAd a).mpr hda
      simp only [↓reduceIte]
      split_ifs <;> simp [haA, hy₀, hy₁]

private theorem logSpaceManyOneAutoreducible_of_univ {y₀ y₁ : α} (hyne : y₀ ≠ y₁)
    (hUniv : A = Set.univ) : LogSpaceManyOneAutoreducible encA A := by
  classical
  let choose : Bool → α := fun b => if b then y₁ else y₀
  have hchoose : ComputableInLogSpace choose encBool encA := ComputableInLogSpace.of_finite choose
  have hf := hchoose.comp (computableInLogSpace_decide_eq y₀ (encA := encA))
  refine ⟨_, ⟨hf, fun a => ?_⟩, fun a => ?_⟩
  · dsimp only [choose, Function.comp_apply]
    split_ifs with ha
    · intro heq; simp only [decide_eq_true_eq] at ha; subst ha; exact hyne heq.symm
    · intro heq; exact ha (decide_eq_true heq.symm)
  · simp [hUniv]

private theorem logSpaceManyOneAutoreducible_of_empty {n₀ n₁ : α} (hnne : n₀ ≠ n₁)
    (hEmpty : A = ∅) : LogSpaceManyOneAutoreducible encA A := by
  classical
  let choose : Bool → α := fun b => if b then n₁ else n₀
  have hchoose : ComputableInLogSpace choose encBool encA := ComputableInLogSpace.of_finite choose
  have hf := hchoose.comp (computableInLogSpace_decide_eq n₀ (encA := encA))
  refine ⟨_, ⟨hf, fun a => ?_⟩, fun a => ?_⟩
  · dsimp only [choose, Function.comp_apply]
    split_ifs with ha
    · intro heq; simp only [decide_eq_true_eq] at ha; subst ha; exact hnne heq.symm
    · intro heq; exact ha (decide_eq_true heq.symm)
  · simp [hEmpty]

/-- **A set in `L` is logspace many-one autoreducible if and only if neither it nor its complement
is a singleton.** -/
theorem logSpaceManyOneAutoreducible_iff_of_mem_L (hA : A ∈ L encA) :
    LogSpaceManyOneAutoreducible encA A ↔
      (∀ a ∈ A, ∃ y ∈ A, y ≠ a) ∧ (∀ a ∉ A, ∃ n ∉ A, n ≠ a) := by
  refine ⟨fun h => ⟨h.exists_mem_ne, h.exists_notMem_ne⟩, fun ⟨hMem, hNotMem⟩ => ?_⟩
  by_cases hEmpty : A = ∅
  · by_cases hα : IsEmpty α
    · exact ⟨id, ⟨ComputableInLogSpace.id, fun a => (IsEmpty.false a).elim⟩, fun _ => Iff.rfl⟩
    · obtain ⟨a₀⟩ := not_isEmpty_iff.mp hα
      have ha₀ : a₀ ∉ A := by subst hEmpty; exact fun h => h
      obtain ⟨n₁, hn₁, hne⟩ := hNotMem a₀ ha₀
      exact logSpaceManyOneAutoreducible_of_empty hne.symm hEmpty
  · by_cases hUniv : A = Set.univ
    · obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
      obtain ⟨y₁, hy₁, hne⟩ := hMem a₀ ha₀
      exact logSpaceManyOneAutoreducible_of_univ hne.symm hUniv
    · obtain ⟨y₀, hy₀⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
      obtain ⟨y₁, hy₁, hyne⟩ := hMem y₀ hy₀
      obtain ⟨n₀, hn₀⟩ := Set.nonempty_compl.mpr hUniv
      obtain ⟨n₁, hn₁, hnne⟩ := hNotMem n₀ hn₀
      exact LogSpaceManyOneAutoreducible.of_two_mem_two_notMem hA hy₀ hy₁ hyne.symm hn₀ hn₁
        hnne.symm

/-- A set in `P` with at least two members and at least two non-members is polynomial-time many-one
autoreducible. -/
theorem PolyTimeManyOneAutoreducible.of_two_mem_two_notMem (hA : A ∈ P encA)
    {y₀ y₁ : α} (hy₀ : y₀ ∈ A) (hy₁ : y₁ ∈ A) (hyne : y₀ ≠ y₁)
    {n₀ n₁ : α} (hn₀ : n₀ ∉ A) (hn₁ : n₁ ∉ A) (hnne : n₀ ≠ n₁) :
    PolyTimeManyOneAutoreducible encA A := by
  classical
  obtain ⟨d, hd, hAd⟩ := hA
  have hy_comp := computableInPolyTime_alt encA y₀ y₁
  have hn_comp := computableInPolyTime_alt encA n₀ n₁
  have hf := ComputableInPolyTime.ite hd hy_comp hn_comp
  refine ⟨_, ⟨hf, fun a => ?_⟩, fun a => ?_⟩
  · by_cases hda : d a = true
    · simp only [hda, ↓reduceIte]
      split_ifs with ha
      · intro heq; subst ha; exact hyne heq.symm
      · intro heq; exact ha heq.symm
    · simp only [hda, Bool.false_eq_true, ↓reduceIte]
      split_ifs with ha
      · intro heq; subst ha; exact hnne heq.symm
      · intro heq; exact ha heq.symm
  · by_cases hda : d a = true
    · simp only [hda, ↓reduceIte]
      have haA : a ∈ A := (hAd a).mpr hda
      split_ifs <;> simp [haA, hy₀, hy₁]
    · simp only [hda, Bool.false_eq_true, ↓reduceIte]
      have haA : a ∉ A := fun h => hda ((hAd a).mp h)
      split_ifs <;> simp [haA, hn₀, hn₁]

/-- **A set in `P` is polynomial-time many-one autoreducible if and only if neither it nor its
complement is a singleton.** -/
theorem polyTimeManyOneAutoreducible_iff_of_mem_P (hA : A ∈ P encA) :
    PolyTimeManyOneAutoreducible encA A ↔
      (∀ a ∈ A, ∃ y ∈ A, y ≠ a) ∧ (∀ a ∉ A, ∃ n ∉ A, n ≠ a) := by
  refine ⟨fun h => ⟨h.exists_mem_ne, h.exists_notMem_ne⟩, fun ⟨hMem, hNotMem⟩ => ?_⟩
  by_cases hEmpty : A = ∅
  · by_cases hα : IsEmpty α
    · exact ⟨id, ⟨ComputableInPolyTime.id', fun a => (IsEmpty.false a).elim⟩, fun _ => Iff.rfl⟩
    · obtain ⟨a₀⟩ := not_isEmpty_iff.mp hα
      have ha₀ : a₀ ∉ A := by subst hEmpty; exact fun h => h
      obtain ⟨n₁, hn₁, hne⟩ := hNotMem a₀ ha₀
      exact (logSpaceManyOneAutoreducible_of_empty hne.symm hEmpty).polyTimeManyOneAutoreducible
  · by_cases hUniv : A = Set.univ
    · obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
      obtain ⟨y₁, hy₁, hne⟩ := hMem a₀ ha₀
      exact (logSpaceManyOneAutoreducible_of_univ hne.symm hUniv).polyTimeManyOneAutoreducible
    · obtain ⟨y₀, hy₀⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
      obtain ⟨y₁, hy₁, hyne⟩ := hMem y₀ hy₀
      obtain ⟨n₀, hn₀⟩ := Set.nonempty_compl.mpr hUniv
      obtain ⟨n₁, hn₁, hnne⟩ := hNotMem n₀ hn₀
      exact PolyTimeManyOneAutoreducible.of_two_mem_two_notMem hA hy₀ hy₁ hyne.symm hn₀ hn₁
        hnne.symm

/-- A set in `L` with no unique member or non-member is logspace many-one autoreducible. -/
theorem LogSpaceManyOneAutoreducible.of_mem_L (hA : A ∈ L encA)
    (hMem : ∀ a ∈ A, ∃ y ∈ A, y ≠ a) (hNotMem : ∀ a ∉ A, ∃ n ∉ A, n ≠ a) :
    LogSpaceManyOneAutoreducible encA A :=
  (logSpaceManyOneAutoreducible_iff_of_mem_L hA).mpr ⟨hMem, hNotMem⟩

/-- A set in `P` with no unique member or non-member is polynomial-time many-one autoreducible. -/
theorem PolyTimeManyOneAutoreducible.of_mem_P (hA : A ∈ P encA)
    (hMem : ∀ a ∈ A, ∃ y ∈ A, y ≠ a) (hNotMem : ∀ a ∉ A, ∃ n ∉ A, n ≠ a) :
    PolyTimeManyOneAutoreducible encA A :=
  (polyTimeManyOneAutoreducible_iff_of_mem_P hA).mpr ⟨hMem, hNotMem⟩

/-! ### Mitoticity -/

/-- Mutual reducibility under a binary relation `R`. -/
def ReducibleEquiv (R : Set α → Set α → Prop) (A B : Set α) : Prop :=
  R A B ∧ R B A

/-- `A` is mitotic with respect to the separating problems `𝒞` and the reduction `R`: some
`S ∈ 𝒞` splits `A` into `A ∩ S` and `A ∖ S`, each `R`-equivalent to `A` (hence to each other
when `R` is transitive) [Ambos-Spies 1984][AmbosSpies1984]. -/
def MitoticWith (𝒞 : Set (Set α)) (R : Set α → Set α → Prop) (A : Set α) : Prop :=
  ∃ S ∈ 𝒞, ReducibleEquiv R A (A ∩ S) ∧ ReducibleEquiv R A (A \ S)

/-- `A` is polynomial-time many-one mitotic [Ambos-Spies 1984][AmbosSpies1984]. -/
def PolyTimeManyOneMitotic (encA : α ↪ List Bool) (A : Set α) : Prop :=
  MitoticWith (P encA) (PolyTimeReducible encA encA) A

/-- `A` is logspace many-one mitotic. -/
def LogSpaceManyOneMitotic (encA : α ↪ List Bool) (A : Set α) : Prop :=
  MitoticWith (L encA) (LogSpaceReducible encA encA) A

/-- `A` is `k`-truth-table mitotic.

Note that for `k ≥ 2`, `PolyTimeKTruthTableReducible k` is not transitive (composition uses up to
`k²` queries), so this definition via `MitoticWith` requires only `A ≡ᵖ_k-tt A ∩ S` and
`A ≡ᵖ_k-tt A \ S` rather than pairwise three-way equivalence `A ≡ᵖ_k-tt A ∩ S ≡ᵖ_k-tt A \ S`.
This weaker hypothesis suffices for
`PolyTimeKTruthTableMitotic.polyTimeKTruthTableAutoreducible`. -/
def PolyTimeKTruthTableMitotic (k : ℕ) (encA : α ↪ List Bool) (A : Set α) : Prop :=
  MitoticWith (P encA) (PolyTimeKTruthTableReducible k encA encA) A

/-- `A` is disjunctive truth-table mitotic. -/
def PolyTimeDTTMitotic (encA : α ↪ List Bool) (A : Set α) : Prop :=
  MitoticWith (P encA) (PolyTimeDTTReducible encA encA) A

/-- `A` is bounded truth-table mitotic. -/
def PolyTimeBTTMitotic (encA : α ↪ List Bool) (A : Set α) : Prop :=
  MitoticWith (P encA) (PolyTimeBTTReducible encA encA) A

/-- `A` is truth-table mitotic. -/
def PolyTimeTruthTableMitotic (encA : α ↪ List Bool) (A : Set α) : Prop :=
  MitoticWith (P encA) (PolyTimeTruthTableReducible encA encA) A

/-- A logspace mitotic set is polynomial-time mitotic. -/
theorem LogSpaceManyOneMitotic.polyTimeManyOneMitotic (h : LogSpaceManyOneMitotic encA A) :
    PolyTimeManyOneMitotic encA A := by
  obtain ⟨S, hS, h₁, h₂⟩ := h
  exact ⟨S, L_subset_P hS,
    ⟨h₁.1.polyTimeReducible, h₁.2.polyTimeReducible⟩,
    ⟨h₂.1.polyTimeReducible, h₂.2.polyTimeReducible⟩⟩

/-- Many-one mitoticity implies `1`-truth-table mitoticity. -/
theorem PolyTimeManyOneMitotic.polyTimeKTruthTableMitotic_one (h : PolyTimeManyOneMitotic encA A) :
    PolyTimeKTruthTableMitotic 1 encA A := by
  obtain ⟨S, hS, h₁, h₂⟩ := h
  exact ⟨S, hS,
    ⟨h₁.1.polyTimeKTruthTableReducible_one, h₁.2.polyTimeKTruthTableReducible_one⟩,
    ⟨h₂.1.polyTimeKTruthTableReducible_one, h₂.2.polyTimeKTruthTableReducible_one⟩⟩

/-- Many-one mitoticity implies disjunctive truth-table mitoticity. -/
theorem PolyTimeManyOneMitotic.polyTimeDTTMitotic (h : PolyTimeManyOneMitotic encA A) :
    PolyTimeDTTMitotic encA A := by
  obtain ⟨S, hS, h₁, h₂⟩ := h
  exact ⟨S, hS,
    ⟨h₁.1.polyTimeDTTReducible, h₁.2.polyTimeDTTReducible⟩,
    ⟨h₂.1.polyTimeDTTReducible, h₂.2.polyTimeDTTReducible⟩⟩

/-- Allowing more queries in `k`-truth-table mitoticity. -/
theorem PolyTimeKTruthTableMitotic.mono {k k' : ℕ}
    (h : PolyTimeKTruthTableMitotic k encA A) (hk : k ≤ k') :
    PolyTimeKTruthTableMitotic k' encA A := by
  obtain ⟨S, hS, h₁, h₂⟩ := h
  exact ⟨S, hS, ⟨h₁.1.mono hk, h₁.2.mono hk⟩, ⟨h₂.1.mono hk, h₂.2.mono hk⟩⟩

/-- `k`-truth-table mitoticity implies bounded truth-table mitoticity. -/
theorem PolyTimeKTruthTableMitotic.polyTimeBTTMitotic {k : ℕ}
    (h : PolyTimeKTruthTableMitotic k encA A) : PolyTimeBTTMitotic encA A := by
  obtain ⟨S, hS, h₁, h₂⟩ := h
  exact ⟨S, hS,
    ⟨h₁.1.polyTimeBTTReducible, h₁.2.polyTimeBTTReducible⟩,
    ⟨h₂.1.polyTimeBTTReducible, h₂.2.polyTimeBTTReducible⟩⟩

/-- Many-one mitoticity implies bounded truth-table mitoticity. -/
theorem PolyTimeManyOneMitotic.polyTimeBTTMitotic (h : PolyTimeManyOneMitotic encA A) :
    PolyTimeBTTMitotic encA A :=
  h.polyTimeKTruthTableMitotic_one.polyTimeBTTMitotic

/-- Disjunctive truth-table mitoticity implies truth-table mitoticity. -/
theorem PolyTimeDTTMitotic.polyTimeTruthTableMitotic (h : PolyTimeDTTMitotic encA A) :
    PolyTimeTruthTableMitotic encA A := by
  obtain ⟨S, hS, h₁, h₂⟩ := h
  exact ⟨S, hS,
    ⟨h₁.1.polyTimeTruthTableReducible, h₁.2.polyTimeTruthTableReducible⟩,
    ⟨h₂.1.polyTimeTruthTableReducible, h₂.2.polyTimeTruthTableReducible⟩⟩

/-- Bounded truth-table mitoticity implies truth-table mitoticity. -/
theorem PolyTimeBTTMitotic.polyTimeTruthTableMitotic (h : PolyTimeBTTMitotic encA A) :
    PolyTimeTruthTableMitotic encA A := by
  obtain ⟨S, hS, h₁, h₂⟩ := h
  exact ⟨S, hS,
    ⟨h₁.1.polyTimeTruthTableReducible, h₁.2.polyTimeTruthTableReducible⟩,
    ⟨h₂.1.polyTimeTruthTableReducible, h₂.2.polyTimeTruthTableReducible⟩⟩

/-- Many-one mitoticity implies truth-table mitoticity. -/
theorem PolyTimeManyOneMitotic.polyTimeTruthTableMitotic (h : PolyTimeManyOneMitotic encA A) :
    PolyTimeTruthTableMitotic encA A :=
  h.polyTimeBTTMitotic.polyTimeTruthTableMitotic

/-! ### Mitotic implies autoreducible -/

/-- Filtered query indices for a mitotic reduction: keeps only those indices `i < r₀ a` whose
query `q₀ (a, i)` lands on the opposite side of the separator `s` from `a`. -/
private def mitoticKeptIndices (s : α → Bool) (r₀ : α → ℕ) (q₀ : α × ℕ → α) (a : α) : List ℕ :=
  (List.range (r₀ a)).filter fun i => (s (q₀ (a, i)) != s a)

private def mitoticQueryCount (s : α → Bool) (r₀ : α → ℕ) (q₀ : α × ℕ → α) (a : α) : ℕ :=
  (mitoticKeptIndices s r₀ q₀ a).length

private def mitoticQuery (s : α → Bool) (r₀ : α → ℕ) (q₀ : α × ℕ → α) (x : α × ℕ) : α :=
  ((mitoticKeptIndices s r₀ q₀ x.1).map fun i => q₀ (x.1, i))[x.2]?.getD x.1

private def mitoticCombiner (s : α → Bool) (r₀ : α → ℕ) (q₀ : α × ℕ → α)
    (d₀ : α × List Bool → Bool) (x : α × List Bool) : Bool :=
  d₀ (x.1, (List.range (r₀ x.1)).map fun i =>
    if (s (q₀ (x.1, i)) != s x.1) then
      (x.2.drop ((List.range i).filter fun j => (s (q₀ (x.1, j)) != s x.1)).length).headD false
    else false)

private theorem computableInPolyTime_mitoticQueryCount {s : α → Bool} {r₀ : α → ℕ}
    {q₀ : α × ℕ → α} (hs : ComputableInPolyTime s encA encBool)
    (hr₀ : ComputableInPolyTime r₀ encA encUnary)
    (hq₀ : ComputableInPolyTime q₀ (encPair encA encUnary) encA) :
    ComputableInPolyTime (mitoticQueryCount s r₀ q₀) encA encUnary := by
  unfold mitoticQueryCount mitoticKeptIndices
  fun_prop

private theorem computableInPolyTime_mitoticQuery {s : α → Bool} {r₀ : α → ℕ}
    {q₀ : α × ℕ → α} (hs : ComputableInPolyTime s encA encBool)
    (hr₀ : ComputableInPolyTime r₀ encA encUnary)
    (hq₀ : ComputableInPolyTime q₀ (encPair encA encUnary) encA) :
    ComputableInPolyTime (mitoticQuery s r₀ q₀) (encPair encA encUnary) encA := by
  unfold mitoticQuery mitoticKeptIndices
  fun_prop

private theorem computableInPolyTime_mitoticCombiner {s : α → Bool} {r₀ : α → ℕ}
    {q₀ : α × ℕ → α} {d₀ : α × List Bool → Bool}
    (hs : ComputableInPolyTime s encA encBool)
    (hr₀ : ComputableInPolyTime r₀ encA encUnary)
    (hq₀ : ComputableInPolyTime q₀ (encPair encA encUnary) encA)
    (hd₀ : ComputableInPolyTime d₀ (encPair encA encBits) encBool) :
    ComputableInPolyTime (mitoticCombiner s r₀ q₀ d₀) (encPair encA encBits) encBool := by
  unfold mitoticCombiner
  fun_prop

private theorem mitoticQueryCount_le {s : α → Bool} {r₀ : α → ℕ} {q₀ : α × ℕ → α} (a : α) :
    mitoticQueryCount s r₀ q₀ a ≤ r₀ a := by
  simpa [mitoticQueryCount, mitoticKeptIndices] using
    List.length_filter_le (fun i => (s (q₀ (a, i)) != s a)) (List.range (r₀ a))

private theorem mitoticQuery_ne {s : α → Bool} {r₀ : α → ℕ} {q₀ : α × ℕ → α} {a : α} {j : ℕ}
    (hj : j < mitoticQueryCount s r₀ q₀ a) :
    mitoticQuery s r₀ q₀ (a, j) ≠ a := by
  have hj' : j < ((mitoticKeptIndices s r₀ q₀ a).map fun i => q₀ (a, i)).length := by
    simpa [mitoticQueryCount] using hj
  have hmem : mitoticQuery s r₀ q₀ (a, j) ∈
      (mitoticKeptIndices s r₀ q₀ a).map fun i => q₀ (a, i) := by
    simp only [mitoticQuery, List.getElem?_eq_getElem hj', Option.getD_some]
    exact List.getElem_mem hj'
  obtain ⟨i, hi, hq⟩ := List.mem_map.mp hmem
  obtain ⟨-, hkeep⟩ := List.mem_filter.mp hi
  intro heq
  rw [hq, heq, bne_self_eq_false] at hkeep
  contradiction

private theorem getElem?_filter_range {n i : ℕ} (p : ℕ → Bool) (hi : i < n) (hpi : p i = true) :
    ((List.range n).filter p)[((List.range i).filter p).length]? = some i := by
  have hsplit : List.range n = List.range i ++ i :: (List.range n).drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i (List.range n)]
    rw [List.take_range, Nat.min_eq_left hi.le,
      List.drop_eq_getElem_cons (by simp [hi]), List.getElem_range]
  rw [hsplit, List.filter_append, List.filter_cons_of_pos hpi,
    List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero]

private theorem headD_drop (l : List Bool) (k : ℕ) :
    (l.drop k).headD false = l[k]?.getD false := by
  rw [← List.head?_drop]
  cases l.drop k <;> rfl

open scoped Classical in
private theorem truthTableAnswers_mitoticQuery (s : α → Bool) (r₀ : α → ℕ) (q₀ : α × ℕ → α)
    (A : Set α) (a : α) :
    truthTableAnswers (mitoticQuery s r₀ q₀ ⁻¹' A) (mitoticQueryCount s r₀ q₀) a =
      (mitoticKeptIndices s r₀ q₀ a).map fun i => decide (q₀ (a, i) ∈ A) := by
  apply List.ext_getElem
  · simp [truthTableAnswers, mitoticQueryCount]
  · intro j h₁ h₂
    simp only [truthTableAnswers, List.getElem_ofFn, Set.mem_preimage, mitoticQuery,
      List.getElem_map]
    have hj : j < ((mitoticKeptIndices s r₀ q₀ a).map fun i => q₀ (a, i)).length := by
      simpa [mitoticQueryCount] using h₁
    simp [List.getElem?_eq_getElem hj]

private theorem mitoticCombiner_spec {S : Set α} {s : α → Bool} (hsS : ∀ a, a ∈ S ↔ s a = true)
    {r₁ r₂ : α → ℕ} {q₁ q₂ : α × ℕ → α} {d₁ d₂ : α × List Bool → Bool}
    (hA₁ : ∀ a, a ∈ A ↔ d₁ (a, truthTableAnswers (q₁ ⁻¹' (A ∩ S)) r₁ a) = true)
    (hA₂ : ∀ a, a ∈ A ↔ d₂ (a, truthTableAnswers (q₂ ⁻¹' (A \ S)) r₂ a) = true) (a : α) :
    let r₀ := fun x => if s x then r₂ x else r₁ x
    let q₀ := fun x : α × ℕ => if s x.1 then q₂ x else q₁ x
    let d₀ := fun x : α × List Bool => if s x.1 then d₂ x else d₁ x
    a ∈ A ↔ mitoticCombiner s r₀ q₀ d₀
      (a, truthTableAnswers (mitoticQuery s r₀ q₀ ⁻¹' A) (mitoticQueryCount s r₀ q₀) a) = true := by
  classical
  intro r₀ q₀ d₀
  rw [mitoticCombiner, truthTableAnswers_mitoticQuery]
  dsimp only
  have hmap_eq :
      ((List.range (r₀ a)).map fun i =>
        if (s (q₀ (a, i)) != s a) = true then
          (((mitoticKeptIndices s r₀ q₀ a).map fun k => decide (q₀ (a, k) ∈ A)).drop
            ((List.range i).filter fun j => s (q₀ (a, j)) != s a).length).headD false
        else false) =
      (List.range (r₀ a)).map fun i => (s (q₀ (a, i)) != s a) && decide (q₀ (a, i) ∈ A) := by
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    split_ifs with hkeep
    · rw [hkeep, Bool.true_and, headD_drop, List.getElem?_map, mitoticKeptIndices,
        getElem?_filter_range (fun j => s (q₀ (a, j)) != s a) hi hkeep,
        Option.map_some, Option.getD_some]
    · rw [Bool.eq_false_iff.mpr hkeep, Bool.false_and]
  rw [hmap_eq]
  cases hsa : s a
  · rw [hA₁ a, truthTableAnswers_eq_map_range]
    simp only [d₀, r₀, q₀, hsa, Bool.false_eq_true, ↓reduceIte, Bool.bne_false]
    suffices h : ((List.range (r₁ a)).map fun i => s (q₁ (a, i)) && decide (q₁ (a, i) ∈ A)) =
        (List.range (r₁ a)).map fun i => decide ((a, i) ∈ q₁ ⁻¹' (A ∩ S)) by rw [h]
    refine List.map_congr_left fun i _ => ?_
    simp only [Set.mem_preimage, Set.mem_inter_iff, hsS (q₁ (a, i))]
    by_cases hqA : q₁ (a, i) ∈ A <;> cases hqS : s (q₁ (a, i)) <;> simp [hqA]
  · rw [hA₂ a, truthTableAnswers_eq_map_range]
    simp only [d₀, r₀, q₀, hsa, ↓reduceIte, Bool.bne_true]
    suffices h : ((List.range (r₂ a)).map fun i => (!s (q₂ (a, i))) && decide (q₂ (a, i) ∈ A)) =
        (List.range (r₂ a)).map fun i => decide ((a, i) ∈ q₂ ⁻¹' (A \ S)) by rw [h]
    refine List.map_congr_left fun i _ => ?_
    simp only [Set.mem_preimage, Set.mem_sdiff, hsS (q₂ (a, i))]
    by_cases hqA : q₂ (a, i) ∈ A <;> cases hqS : s (q₂ (a, i)) <;> simp [hqA]

/-- **Every polynomial-time disjunctive truth-table mitotic set is disjunctive truth-table
autoreducible**, unconditionally (standard argument of [Ambos-Spies 1984][AmbosSpies1984] adapted
to `dtt` reductions). Queries landing on the same side of the separator `S` as the input `a`
cannot belong to the opposite piece (`A ∩ S` when `a ∉ S`, or `A ∖ S` when `a ∈ S`) and are
filtered out before querying `A`. -/
theorem PolyTimeDTTMitotic.polyTimeDTTAutoreducible (h : PolyTimeDTTMitotic encA A) :
    PolyTimeDTTAutoreducible encA A := by
  obtain ⟨S, ⟨s, hs, hsS⟩, ⟨⟨r₁, q₁, hr₁, hq₁, hA₁⟩, -⟩, ⟨⟨r₂, q₂, hr₂, hq₂, hA₂⟩, -⟩⟩ := h
  let r₀ : α → ℕ := fun a => if s a then r₂ a else r₁ a
  have hr₀ : ComputableInPolyTime r₀ encA encUnary := ComputableInPolyTime.ite hs hr₂ hr₁
  let q₀ : α × ℕ → α := fun x => if s x.1 then q₂ x else q₁ x
  have hq₀ : ComputableInPolyTime q₀ (encPair encA encUnary) encA := by
    dsimp only [q₀]; fun_prop
  refine ⟨mitoticQueryCount s r₀ q₀, mitoticQuery s r₀ q₀,
    computableInPolyTime_mitoticQueryCount hs hr₀ hq₀,
    computableInPolyTime_mitoticQuery hs hr₀ hq₀,
    fun a j hj => mitoticQuery_ne hj, fun a => ?_⟩
  have hexists : (∃ j < mitoticQueryCount s r₀ q₀ a, mitoticQuery s r₀ q₀ (a, j) ∈ A) ↔
      ∃ i < r₀ a, (s (q₀ (a, i)) != s a) = true ∧ q₀ (a, i) ∈ A := by
    constructor
    · rintro ⟨j, hj, hjA⟩
      have hj' : j < ((mitoticKeptIndices s r₀ q₀ a).map fun i => q₀ (a, i)).length := by
        simpa [mitoticQueryCount] using hj
      have hmem : (mitoticQuery s r₀ q₀ (a, j)) ∈
          (mitoticKeptIndices s r₀ q₀ a).map fun i => q₀ (a, i) := by
        simp only [mitoticQuery, List.getElem?_eq_getElem hj', Option.getD_some]
        exact List.getElem_mem hj'
      obtain ⟨i, hi, hqi⟩ := List.mem_map.mp hmem
      obtain ⟨hir, hkeep⟩ := List.mem_filter.mp hi
      exact ⟨i, List.mem_range.mp hir, hkeep, hqi ▸ hjA⟩
    · rintro ⟨i, hi, hkeep, hiA⟩
      have hi_mem : i ∈ mitoticKeptIndices s r₀ q₀ a :=
        List.mem_filter.mpr ⟨List.mem_range.mpr hi, hkeep⟩
      obtain ⟨j, hj, hij⟩ := List.getElem_of_mem hi_mem
      refine ⟨j, hj, ?_⟩
      have hj' : j < ((mitoticKeptIndices s r₀ q₀ a).map fun k => q₀ (a, k)).length := by
        simpa using hj
      simp [mitoticQuery, List.getElem?_eq_getElem hj', hij, hiA]
  rw [hexists]
  cases hsa : s a
  · rw [hA₁ a]
    simp only [r₀, q₀, hsa, Bool.false_eq_true, ↓reduceIte, Bool.bne_false,
      Set.mem_inter_iff, hsS, and_comm]
  · rw [hA₂ a]
    simp only [r₀, q₀, hsa, ↓reduceIte, Bool.bne_true, Bool.not_eq_true',
      Set.mem_sdiff, hsS, Bool.not_eq_true, and_comm]

/-- **Every polynomial-time `k`-truth-table mitotic set is `k`-truth-table autoreducible**,
unconditionally (standard argument of [Ambos-Spies 1984][AmbosSpies1984] adapted to `k-tt`
reductions). -/
theorem PolyTimeKTruthTableMitotic.polyTimeKTruthTableAutoreducible {k : ℕ}
    (h : PolyTimeKTruthTableMitotic k encA A) :
    PolyTimeKTruthTableAutoreducible k encA A := by
  obtain ⟨S, ⟨s, hs, hsS⟩, ⟨⟨r₁, q₁, d₁, hr₁, hq₁, hd₁, hrk₁, hA₁⟩, -⟩,
    ⟨⟨r₂, q₂, d₂, hr₂, hq₂, hd₂, hrk₂, hA₂⟩, -⟩⟩ := h
  let r₀ : α → ℕ := fun a => if s a then r₂ a else r₁ a
  have hr₀ : ComputableInPolyTime r₀ encA encUnary := ComputableInPolyTime.ite hs hr₂ hr₁
  let q₀ : α × ℕ → α := fun x => if s x.1 then q₂ x else q₁ x
  have hq₀ : ComputableInPolyTime q₀ (encPair encA encUnary) encA := by
    dsimp only [q₀]; fun_prop
  let d₀ : α × List Bool → Bool := fun x => if s x.1 then d₂ x else d₁ x
  have hd₀ : ComputableInPolyTime d₀ (encPair encA encBits) encBool := by
    dsimp only [d₀]; fun_prop
  refine ⟨mitoticQueryCount s r₀ q₀, mitoticQuery s r₀ q₀, mitoticCombiner s r₀ q₀ d₀,
    computableInPolyTime_mitoticQueryCount hs hr₀ hq₀,
    computableInPolyTime_mitoticQuery hs hr₀ hq₀,
    computableInPolyTime_mitoticCombiner hs hr₀ hq₀ hd₀,
    fun a => (mitoticQueryCount_le a).trans
      (by dsimp only [r₀]; split_ifs <;> [exact hrk₂ a; exact hrk₁ a]),
    fun a j hj => mitoticQuery_ne hj,
    fun a => mitoticCombiner_spec hsS hA₁ hA₂ a⟩

/-- **Every polynomial-time bounded truth-table mitotic set is bounded truth-table autoreducible**,
unconditionally (standard argument of [Ambos-Spies 1984][AmbosSpies1984] adapted to `btt`
reductions). -/
theorem PolyTimeBTTMitotic.polyTimeBTTAutoreducible (h : PolyTimeBTTMitotic encA A) :
    PolyTimeBTTAutoreducible encA A := by
  obtain ⟨S, hS, ⟨⟨k₁, h₁⟩, ⟨k₁', h₁'⟩⟩, ⟨⟨k₂, h₂⟩, ⟨k₂', h₂'⟩⟩⟩ := h
  let k := max (max k₁ k₁') (max k₂ k₂')
  have hmit : PolyTimeKTruthTableMitotic k encA A :=
    ⟨S, hS,
      ⟨h₁.mono ((le_max_left _ _).trans (le_max_left _ _)),
       h₁'.mono ((le_max_right _ _).trans (le_max_left _ _))⟩,
      ⟨h₂.mono ((le_max_left _ _).trans (le_max_right _ _)),
       h₂'.mono ((le_max_right _ _).trans (le_max_right _ _))⟩⟩
  exact ⟨k, hmit.polyTimeKTruthTableAutoreducible⟩

/-- **Every polynomial-time truth-table mitotic set is truth-table autoreducible**,
unconditionally (standard argument of [Ambos-Spies 1984][AmbosSpies1984] adapted to `tt`
reductions). -/
theorem PolyTimeTruthTableMitotic.polyTimeTruthTableAutoreducible
    (h : PolyTimeTruthTableMitotic encA A) :
    PolyTimeTruthTableAutoreducible encA A := by
  obtain ⟨S, ⟨s, hs, hsS⟩, ⟨⟨r₁, q₁, d₁, hr₁, hq₁, hd₁, hA₁⟩, -⟩,
    ⟨⟨r₂, q₂, d₂, hr₂, hq₂, hd₂, hA₂⟩, -⟩⟩ := h
  let r₀ : α → ℕ := fun a => if s a then r₂ a else r₁ a
  have hr₀ : ComputableInPolyTime r₀ encA encUnary := ComputableInPolyTime.ite hs hr₂ hr₁
  let q₀ : α × ℕ → α := fun x => if s x.1 then q₂ x else q₁ x
  have hq₀ : ComputableInPolyTime q₀ (encPair encA encUnary) encA := by
    dsimp only [q₀]; fun_prop
  let d₀ : α × List Bool → Bool := fun x => if s x.1 then d₂ x else d₁ x
  have hd₀ : ComputableInPolyTime d₀ (encPair encA encBits) encBool := by
    dsimp only [d₀]; fun_prop
  exact ⟨mitoticQueryCount s r₀ q₀, mitoticQuery s r₀ q₀, mitoticCombiner s r₀ q₀ d₀,
    computableInPolyTime_mitoticQueryCount hs hr₀ hq₀,
    computableInPolyTime_mitoticQuery hs hr₀ hq₀,
    computableInPolyTime_mitoticCombiner hs hr₀ hq₀ hd₀,
    fun a j hj => mitoticQuery_ne hj,
    fun a => mitoticCombiner_spec hsS hA₁ hA₂ a⟩

/-- **Every polynomial-time many-one mitotic set is disjunctive truth-table autoreducible**,
unconditionally [Ambos-Spies 1984][AmbosSpies1984]. -/
theorem PolyTimeManyOneMitotic.polyTimeDTTAutoreducible (h : PolyTimeManyOneMitotic encA A) :
    PolyTimeDTTAutoreducible encA A :=
  h.polyTimeDTTMitotic.polyTimeDTTAutoreducible

/-- **Every polynomial-time many-one mitotic set is `1`-truth-table autoreducible**,
unconditionally [Ambos-Spies 1984][AmbosSpies1984]. -/
theorem PolyTimeManyOneMitotic.polyTimeKTruthTableAutoreducible_one
    (h : PolyTimeManyOneMitotic encA A) : PolyTimeKTruthTableAutoreducible 1 encA A :=
  h.polyTimeKTruthTableMitotic_one.polyTimeKTruthTableAutoreducible

/-- Every polynomial-time many-one mitotic set is bounded truth-table autoreducible. -/
theorem PolyTimeManyOneMitotic.polyTimeBTTAutoreducible (h : PolyTimeManyOneMitotic encA A) :
    PolyTimeBTTAutoreducible encA A :=
  h.polyTimeBTTMitotic.polyTimeBTTAutoreducible

/-- Every polynomial-time many-one mitotic set is truth-table autoreducible. -/
theorem PolyTimeManyOneMitotic.polyTimeTruthTableAutoreducible
    (h : PolyTimeManyOneMitotic encA A) : PolyTimeTruthTableAutoreducible encA A :=
  h.polyTimeTruthTableMitotic.polyTimeTruthTableAutoreducible

private theorem mitotic_candidate_ne {s : α → Bool} {f₁ f₂ : α → α} {a : α}
    (hg : (s (if s a then f₁ a else f₂ a) != s a) = true) :
    (if s a then f₁ a else f₂ a) ≠ a := by
  intro heq
  rw [heq, bne_self_eq_false] at hg
  contradiction

private theorem mitotic_candidate_mem_iff {S : Set α} {s : α → Bool} (hsS : ∀ a, a ∈ S ↔ s a = true)
    {f₁ f₂ : α → α} (hAf₁ : ∀ a, a ∈ A ↔ f₁ a ∈ A \ S) (hAf₂ : ∀ a, a ∈ A ↔ f₂ a ∈ A ∩ S) {a : α}
    (hg : (s (if s a then f₁ a else f₂ a) != s a) = true) :
    a ∈ A ↔ (if s a then f₁ a else f₂ a) ∈ A := by
  cases hs_a : s a
  · simp only [hs_a, Bool.bne_false, Bool.false_eq_true, ↓reduceIte] at hg ⊢
    rw [hAf₂ a, Set.mem_inter_iff]
    exact and_iff_left ((hsS (f₂ a)).mpr hg)
  · simp only [hs_a, ↓reduceIte] at hg ⊢
    have hf₁S : f₁ a ∉ S := fun hS' => by
      have := (hsS (f₁ a)).mp hS'; rw [this] at hg; contradiction
    rw [hAf₁ a, Set.mem_sdiff]
    exact and_iff_left hf₁S

private theorem mitotic_candidate_notMem {S : Set α} {s : α → Bool} (hsS : ∀ a, a ∈ S ↔ s a = true)
    {f₁ f₂ : α → α} (hAf₁ : ∀ a, a ∈ A ↔ f₁ a ∈ A \ S) (hAf₂ : ∀ a, a ∈ A ↔ f₂ a ∈ A ∩ S) {a : α}
    (hg : ¬ (s (if s a then f₁ a else f₂ a) != s a) = true) :
    a ∉ A := by
  intro ha
  cases hs_a : s a
  · simp only [hs_a, Bool.bne_false, Bool.false_eq_true, ↓reduceIte] at hg
    exact hg ((hsS (f₂ a)).mp ((hAf₂ a).mp ha).2)
  · simp only [hs_a, ↓reduceIte] at hg
    have haS := (hAf₁ a).mp ha
    have hS' : f₁ a ∈ S := by
      cases hsf : s (f₁ a)
      · exact False.elim (hg (by simp [hsf]))
      · exact (hsS (f₁ a)).mpr hsf
    exact haS.2 hS'

private theorem PolyTimeManyOneMitotic.exists_candidate (h : PolyTimeManyOneMitotic encA A) :
    ∃ (candidate : α → α) (good : α → Bool),
      ComputableInPolyTime candidate encA encA ∧
      ComputableInPolyTime good encA encBool ∧
      (∀ a, good a = true → candidate a ≠ a) ∧
      (∀ a, good a = true → (a ∈ A ↔ candidate a ∈ A)) ∧
      (∀ a, ¬ good a = true → a ∉ A) := by
  obtain ⟨S, ⟨s, hs, hsS⟩, ⟨⟨f₂, hf₂, hAf₂⟩, -⟩, ⟨⟨f₁, hf₁, hAf₁⟩, -⟩⟩ := h
  let candidate : α → α := fun a => if s a then f₁ a else f₂ a
  have hcand : ComputableInPolyTime candidate encA encA :=
    ComputableInPolyTime.ite hs hf₁ hf₂
  let good : α → Bool := fun a => (s (candidate a) != s a)
  have hgood : ComputableInPolyTime good encA encBool := by fun_prop
  exact ⟨candidate, good, hcand, hgood,
    fun a hg => mitotic_candidate_ne hg,
    fun a hg => mitotic_candidate_mem_iff hsS hAf₁ hAf₂ hg,
    fun a hg => mitotic_candidate_notMem hsS hAf₁ hAf₂ hg⟩

/-- **A polynomial-time many-one mitotic set is many-one autoreducible provided its complement
is not a singleton** [Ambos-Spies 1984][AmbosSpies1984]. -/
theorem PolyTimeManyOneMitotic.polyTimeManyOneAutoreducible (h : PolyTimeManyOneMitotic encA A)
    (hCompl : ∀ a ∉ A, ∃ n ∉ A, n ≠ a) : PolyTimeManyOneAutoreducible encA A := by
  classical
  obtain ⟨candidate, good, hcand, hgood, hne, hmem, hnotMem⟩ := h.exists_candidate
  by_cases hUniv : ∀ a, a ∈ A
  · refine ⟨candidate, ⟨hcand, fun a => ?_⟩, fun a => by simp [hUniv (candidate a), hUniv a]⟩
    have hg : good a = true := by
      by_contra hbad
      exact (hnotMem a hbad) (hUniv a)
    exact hne a hg
  · obtain ⟨n₀, hn₀⟩ : ∃ n, n ∉ A := by
      by_contra hc
      apply hUniv
      intro a
      by_contra ha
      exact hc ⟨a, ha⟩
    obtain ⟨n₁, hn₁, hnne⟩ := hCompl n₀ hn₀
    have hfall := computableInPolyTime_alt encA n₀ n₁
    let f : α → α := fun a => if good a then candidate a else (if a = n₀ then n₁ else n₀)
    have hf : ComputableInPolyTime f encA encA := ComputableInPolyTime.ite hgood hcand hfall
    refine ⟨f, ⟨hf, fun a => ?_⟩, fun a => ?_⟩
    · dsimp only [f]
      by_cases hg : good a = true
      · simp only [hg, ↓reduceIte]
        exact hne a hg
      · simp only [hg, Bool.false_eq_true, ↓reduceIte]
        split_ifs with ha
        · intro heq; subst ha; exact hnne heq
        · intro heq; exact ha heq.symm
    · dsimp only [f]
      by_cases hg : good a = true
      · simp only [hg, ↓reduceIte]
        exact hmem a hg
      · simp only [hg, Bool.false_eq_true, ↓reduceIte]
        have haA := hnotMem a hg
        split_ifs with ha <;> simp [haA, hn₀, hn₁]

/-- **A polynomial-time many-one mitotic set is many-one autoreducible if and only if its
complement is not a singleton** [Ambos-Spies 1984][AmbosSpies1984]. -/
theorem PolyTimeManyOneMitotic.polyTimeManyOneAutoreducible_iff
    (h : PolyTimeManyOneMitotic encA A) :
    PolyTimeManyOneAutoreducible encA A ↔ ∀ a ∉ A, ∃ n ∉ A, n ≠ a :=
  ⟨fun hauto => hauto.exists_notMem_ne, fun hCompl => h.polyTimeManyOneAutoreducible hCompl⟩

end Cslib.Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Complexity.Reduction.TruthTableVariants
import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Closure of NP and coNP under truth-table reduction variants

`NP` is closed under polynomial-time positive truth-table reductions
(`Cslib.Complexity.PolyTimePTTReducible.mem_NP`), whose combiner is monotone in the answers. A
certificate lists one string per query. The queries whose listed string is a valid witness are
answered `true` and the others `false`; these answers lie below the true ones, so monotonicity makes
every accepted certificate sound. Disjunctive and conjunctive reductions are positive, so `NP` is
closed under both (`Cslib.Complexity.PolyTimeDTTReducible.mem_NP`,
`Cslib.Complexity.PolyTimeCTTReducible.mem_NP`).

By duality (`Cslib.Complexity.polyTimeDTTReducible_iff_polyTimeCTTReducible_compl`), `coNP` is
closed under both as well (`Cslib.Complexity.PolyTimeCTTReducible.mem_coNP`,
`Cslib.Complexity.PolyTimeDTTReducible.mem_coNP`).

This does not extend to bounded or general truth-table reductions: `NP` is closed under those only
if `NP = coNP`, because a one-query reduction can negate its answer.

## Main results

* `Cslib.Complexity.PolyTimePTTReducible.mem_NP`: `NP` is closed under positive truth-table
  reductions.
* `Cslib.Complexity.PolyTimeDTTReducible.mem_NP`, `Cslib.Complexity.PolyTimeCTTReducible.mem_NP`:
  `NP` is closed under disjunctive and conjunctive truth-table reductions.
* `Cslib.Complexity.PolyTimeCTTReducible.mem_coNP`,
  `Cslib.Complexity.PolyTimeDTTReducible.mem_coNP`: `coNP` is closed under conjunctive and
  disjunctive truth-table reductions.

## References

* [R. E. Ladner, N. A. Lynch, A. L. Selman, *A comparison of polynomial time
  reducibilities*][LadnerLynchSelman1975]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}

open scoped Classical in
/-- The canonical certificate for a positive truth-table reduction: for each query in `B`, a
witness of the exact length `pB` prescribes, and the empty string for every other query. -/
private noncomputable def canonicalWitnesses {B : Set β} {pB : Polynomial ℕ}
    {VB : β × List Bool → Bool}
    (hVspec : ∀ b, b ∈ B ↔ ∃ w : List Bool, w.length = pB.eval (encB b).length ∧ VB (b, w) = true)
    (r : α → ℕ) (q : α × ℕ → β) (a : α) : List (List Bool) :=
  (List.range (r a)).map fun i =>
    if h : q (a, i) ∈ B then Classical.choose ((hVspec _).1 h) else []

/-- **NP is closed under polynomial-time positive truth-table reductions.** A certificate lists one
string per query; the queries whose listed string is a valid `B`-witness are answered `true` and
the others `false`. These answers lie below the true answers, so the combiner's monotonicity makes
every accepted certificate sound, and listing a witness for every query in `B` is complete. -/
theorem PolyTimePTTReducible.mem_NP {L : Set α} {B : Set β}
    (h : PolyTimePTTReducible encA encB L B) (hB : B ∈ NP encB) : L ∈ NP encA := by
  classical
  obtain ⟨r, q, d, hr, hq, hd, hmono, hL⟩ := h
  obtain ⟨pB, VB, hVB, hVspec⟩ := hB
  -- Whether the `i`-th listed string is a valid witness for the query `q (a, i)`.
  let confirmed : α → List (List Bool) → ℕ → Bool := fun a ws i =>
    decide ((ws.getD i []).length = pB.eval (encB (q (a, i))).length) &&
      VB (q (a, i), ws.getD i [])
  let answers : α → List (List Bool) → List Bool := fun a ws =>
    (List.range (r a)).map (confirmed a ws)
  let check : α × List (List Bool) → Bool := fun p => d (p.1, answers p.1 p.2)
  have hconfirmed_poly : ComputableInPolyTime
      (fun x : (α × List (List Bool)) × ℕ => confirmed x.1.1 x.1.2 x.2)
      (encPair (encPair encA (encList encBits)) encUnary) encBool := by
    dsimp only [confirmed]
    fun_prop
  have hcheck : ComputableInPolyTime check (encPair encA (encList encBits)) encBool := by
    have hrange : ComputableInPolyTime (fun p : α × List (List Bool) => List.range (r p.1))
        (encPair encA (encList encBits)) (encList encUnary) := by
      fun_prop
    exact hd.comp ((ComputableInPolyTime.fst encA (encList encBits)).prod
      (ComputableInPolyTime.mapToBitsWithInput hrange hconfirmed_poly))
  have htrue : ∀ a, truthTableAnswers (q ⁻¹' B) r a =
      (List.range (r a)).map fun i => decide (q (a, i) ∈ B) := fun a => by
    rw [truthTableAnswers_eq_map_range]
    rfl
  have hconfirmed : ∀ a ws i, confirmed a ws i = true → q (a, i) ∈ B := by
    intro a ws i hi
    simp only [confirmed, Bool.and_eq_true, decide_eq_true_eq] at hi
    exact (hVspec _).2 ⟨_, hi⟩
  have hbelow : ∀ a ws, d (a, answers a ws) ≤ d (a, truthTableAnswers (q ⁻¹' B) r a) := by
    intro a ws
    refine hmono a _ _ ?_
    rw [htrue a]
    refine List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (List.forall₂_same.2 ?_))
    intro i _
    cases hc : confirmed a ws i
    · exact Bool.false_le _
    · simp [hconfirmed a ws i hc]
  have hcanonical : ∀ a, answers a (canonicalWitnesses hVspec r q a) =
      truthTableAnswers (q ⁻¹' B) r a := by
    intro a
    rw [htrue a]
    refine List.map_congr_left fun i hi => ?_
    have hi : i < r a := List.mem_range.1 hi
    simp only [confirmed, canonicalWitnesses, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi, Option.map_some, Option.getD_some]
    by_cases hqB : q (a, i) ∈ B
    · have hw := Classical.choose_spec ((hVspec _).1 hqB)
      simp [hqB, hw.1, hw.2]
    · have hnot : ¬ ([].length = pB.eval (encB (q (a, i))).length ∧ VB (q (a, i), []) = true) :=
        fun hw => hqB ((hVspec _).2 ⟨[], hw⟩)
      simpa [hqB, Bool.and_eq_true] using hnot
  -- A polynomial bound on the length of the canonical certificate.
  let bound : α → ℕ := fun a =>
    ((List.range (r a)).flatMap fun i =>
      List.range (2 * pB.eval (encB (q (a, i))).length + 1)).length
  have hbound : ComputableInPolyTime bound encA encUnary := by
    dsimp only [bound]
    fun_prop
  obtain ⟨p, hp⟩ := hbound.polyBounded.exists_polynomial
  have hcanonical_len : ∀ a,
      (encList encBits (canonicalWitnesses hVspec r q a)).length ≤ bound a := by
    intro a
    simp only [bound, length_encList, canonicalWitnesses, List.map_map, List.length_flatMap,
      List.length_range]
    refine List.sum_le_sum fun i _ => ?_
    by_cases hqB : q (a, i) ∈ B
    · have hw := Classical.choose_spec ((hVspec _).1 hqB)
      simp [hqB, hw.1]
    · simp [hqB]
  have hmem : {a | ∃ ws, check (a, ws) = true} ∈ NP encA := by
    refine mem_NP_of_witness (p := p) (Decoder.list Decoder.bits) hcheck (fun _ _ => Iff.rfl)
      (fun a ws hws => ⟨canonicalWitnesses hVspec r q a, ?_, (hcanonical_len a).trans (hp a)⟩)
    change d (a, answers a _) = true
    rw [hcanonical a]
    exact le_antisymm (Bool.le_true _) (hws ▸ hbelow a ws)
  have heq : {a | ∃ ws, check (a, ws) = true} = L := by
    ext a
    simp only [Set.mem_ofPred_eq, hL a]
    constructor
    · rintro ⟨ws, hws⟩
      exact le_antisymm (Bool.le_true _) (hws ▸ hbelow a ws)
    · intro ha
      exact ⟨canonicalWitnesses hVspec r q a, by
        change d (a, answers a _) = true
        rw [hcanonical a]
        exact ha⟩
  rwa [heq] at hmem

/-- **NP is closed under polynomial-time disjunctive truth-table reductions**: a certificate is a
witness for one query in `B`. -/
theorem PolyTimeDTTReducible.mem_NP {L : Set α} {B : Set β}
    (h : PolyTimeDTTReducible encA encB L B) (hB : B ∈ NP encB) : L ∈ NP encA :=
  h.polyTimePTTReducible.mem_NP hB

/-- **NP is closed under polynomial-time conjunctive truth-table reductions**: a certificate lists
a witness for every query. -/
theorem PolyTimeCTTReducible.mem_NP {L : Set α} {B : Set β}
    (h : PolyTimeCTTReducible encA encB L B) (hB : B ∈ NP encB) : L ∈ NP encA :=
  h.polyTimePTTReducible.mem_NP hB

/-- **coNP is closed under polynomial-time conjunctive truth-table reductions.** -/
theorem PolyTimeCTTReducible.mem_coNP {L : Set α} {B : Set β}
    (h : PolyTimeCTTReducible encA encB L B) (hB : B ∈ coNP encB) :
    L ∈ coNP encA := by
  change Lᶜ ∈ NP encA
  change Bᶜ ∈ NP encB at hB
  have h_dual := polyTimeDTTReducible_iff_polyTimeCTTReducible_compl
    (encA := encA) (encB := encB) (L := Lᶜ) (B := Bᶜ)
  rw [compl_compl, compl_compl] at h_dual
  have hdtt : PolyTimeDTTReducible encA encB Lᶜ Bᶜ := h_dual.mpr h
  exact hdtt.mem_NP hB

/-- **coNP is closed under polynomial-time disjunctive truth-table reductions**, dually to
`Cslib.Complexity.PolyTimeCTTReducible.mem_NP`. -/
theorem PolyTimeDTTReducible.mem_coNP {L : Set α} {B : Set β}
    (h : PolyTimeDTTReducible encA encB L B) (hB : B ∈ coNP encB) : L ∈ coNP encA := by
  change Lᶜ ∈ NP encA
  change Bᶜ ∈ NP encB at hB
  exact (polyTimeDTTReducible_iff_polyTimeCTTReducible_compl.mp h).mem_NP hB

end Cslib.Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomial-time truth-table reductions

A nonadaptive reduction uses a uniformly computed indexed batch of queries, a unary query count,
and a polynomial-time Boolean combiner. The combiner receives the original input and all answers.
The query generator is total even outside the used range; unused outputs do not affect semantics.

## Main definitions

* `truthTableAnswers`: the semantic answer word for an indexed family.
* `PolyTimeTruthTableReducible`: polynomial-time nonadaptive reduction of encoded languages.

## Main results

* `truthTable_mem_P`, `PolyTimeTruthTableReducible.mem_P`: `P` is closed under polynomial-time
  truth-table reductions.
* `PolyTimeReducible.polyTimeTruthTableReducible`: every polynomial-time many-one reduction is a
  polynomial-time truth-table reduction.
* `PolyTimeTruthTableReducible.refl`: polynomial-time truth-table reducibility is reflexive.
* `PolyTimeTruthTableReducible.compl_left`, `PolyTimeTruthTableReducible.compl_right`,
  `PolyTimeTruthTableReducible.compl`: polynomial-time truth-table reductions are closed under
  complementing either or both languages.

## References

* [H. Spakowski, M. Thakur, R. Tripathi, *Quantum and classical complexity
  classes*][SpakowskiThakurTripathi2005], Theorem 5.6(a).
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

open Classical in
/-- The semantic answers to a fixed indexed batch, in increasing index order. This definition
does not assert that membership in the indexed language is computable. -/
noncomputable def truthTableAnswers {α : Type} (A : Set (α × ℕ)) (r : α → ℕ) (a : α) : List Bool :=
  List.ofFn fun i : Fin (r a) => decide ((a, i.1) ∈ A)

/-- The answer word has one bit per query. -/
@[simp]
theorem length_truthTableAnswers {α : Type} (A : Set (α × ℕ)) (r : α → ℕ) (a : α) :
    (truthTableAnswers A r a).length = r a := by
  simp [truthTableAnswers]

/-- For a decidable indexed family, the answer word is the decided membership of each index below
the query count. -/
theorem truthTableAnswers_eq_map_range {α : Type} (A : Set (α × ℕ)) [DecidablePred (· ∈ A)]
    (r : α → ℕ) (a : α) :
    truthTableAnswers A r a = (List.range (r a)).map fun i => decide ((a, i) ∈ A) := by
  apply List.ext_getElem (by simp [truthTableAnswers])
  intro i hi₁ hi₂
  simp [truthTableAnswers]

/-- Answers for the complemented family are the negated answers. -/
theorem truthTableAnswers_compl {α : Type} (A : Set (α × ℕ)) (r : α → ℕ) (a : α) :
    truthTableAnswers Aᶜ r a = (truthTableAnswers A r a).map (!·) := by
  classical
  apply List.ext_getElem (by simp [truthTableAnswers])
  intro i hi₁ hi₂
  simp [truthTableAnswers]

variable {α : Type}

/-- A polynomial-time truth-table reduction generates all queries without access to their
answers, then applies a polynomial-time Boolean combiner to the input and answer word.
The count is computed in unary; query lengths and counts may vary at fixed input length. -/
def PolyTimeTruthTableReducible {β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (L : Set α) (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β) (d : α × List Bool → Bool),
    ComputableInPolyTime r encA encUnary ∧
    ComputableInPolyTime q (encPair encA encUnary) encB ∧
    ComputableInPolyTime d (encPair encA encBits) encBool ∧
    ∀ a, a ∈ L ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true

variable {β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {L : Set α} {B : Set β}

/-- Every polynomial-time many-one reduction is a polynomial-time truth-table reduction making a
single query. -/
theorem PolyTimeReducible.polyTimeTruthTableReducible
    (h : PolyTimeReducible encA encB L B) : PolyTimeTruthTableReducible encA encB L B := by
  obtain ⟨f, hf, hL⟩ := h
  refine ⟨fun _ => 1, fun x => f x.1, fun x => x.2.headD false, by fun_prop, by fun_prop,
    by fun_prop, fun a => ?_⟩
  rw [hL a]
  simp [truthTableAnswers]

/-- Every problem reduces to itself under polynomial-time truth-table reductions. -/
@[refl]
theorem PolyTimeTruthTableReducible.refl (encA : α ↪ List Bool) (L : Set α) :
    PolyTimeTruthTableReducible encA encA L L :=
  (PolyTimeReducible.refl encA L).polyTimeTruthTableReducible

/-- Negating the Boolean combiner reduces the complement `Lᶜ` to `B`. -/
theorem PolyTimeTruthTableReducible.compl_left
    (h : PolyTimeTruthTableReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB Lᶜ B := by
  obtain ⟨r, q, d, hr, hq, hd, hL⟩ := h
  refine ⟨r, q, fun x => !d x, hr, hq, by fun_prop, fun a => ?_⟩
  simp [Set.mem_compl_iff, hL a]

/-- Negating each answer bit before invoking the combiner reduces `L` to `Bᶜ`. -/
theorem PolyTimeTruthTableReducible.compl_right
    (h : PolyTimeTruthTableReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB L Bᶜ := by
  obtain ⟨r, q, d, hr, hq, hd, hL⟩ := h
  have hmap : ComputableTidilyInPolyTime (fun x : α × List Bool => x.2.map (!·))
      (encPair encA encBits) encBits :=
    ComputableTidilyInPolyTime.bitsMapWithInput (f := fun _ b => !b) (.snd encA encBits)
      (by fun_prop)
  refine ⟨r, q, fun x => d (x.1, x.2.map (!·)), hr, hq,
    hd.comp (.of_tidy ((ComputableTidilyInPolyTime.fst encA encBits).prod hmap)), fun a => ?_⟩
  rw [hL a, show q ⁻¹' Bᶜ = (q ⁻¹' B)ᶜ from rfl, truthTableAnswers_compl]
  simp [List.map_map, Function.comp_def]

/-- A polynomial-time truth-table reduction from `L` to `B` also reduces `Lᶜ` to `Bᶜ`. -/
theorem PolyTimeTruthTableReducible.compl
    (h : PolyTimeTruthTableReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB Lᶜ Bᶜ :=
  h.compl_left.compl_right

/-- A jointly polynomial-time decidable family supports any polynomial-time Boolean combination of
a computed unary batch of queries. -/
theorem truthTable_mem_P {A : Set (α × ℕ)} {r : α → ℕ} {d : α × List Bool → Bool}
    (hA : A ∈ P (encPair encA encUnary))
    (hr : ComputableInPolyTime r encA encUnary)
    (hd : ComputableInPolyTime d (encPair encA encBits) encBool) :
    {a | d (a, truthTableAnswers A r a) = true} ∈ P encA := by
  have hr := hr.tidy
  have hd := hd.tidy
  classical
  obtain ⟨f, hf, hAf⟩ := mem_P.mp hA
  have hans : ComputableTidilyInPolyTime
      (fun a => (List.range (r a)).map fun i => f (a, i)) encA encBits :=
    ComputableTidilyInPolyTime.mapToBitsWithInput (ComputableTidilyInPolyTime.range.comp hr) hf.tidy
  refine mem_P.mpr ⟨fun a => d (a, (List.range (r a)).map fun i => f (a, i)),
    .of_tidy (hd.comp (ComputableTidilyInPolyTime.id'.prod hans)), fun a => ?_⟩
  simp [truthTableAnswers_eq_map_range, hAf]

/-- **`P` is closed under polynomial-time truth-table reductions.** -/
theorem PolyTimeTruthTableReducible.mem_P
    (h : PolyTimeTruthTableReducible encA encB L B) (hB : B ∈ P encB) : L ∈ P encA := by
  obtain ⟨r, q, d, hr, hq, hd, hL⟩ := h
  have hqB : q ⁻¹' B ∈ P (encPair encA encUnary) :=
    PolyTimeReducible.mem_P ⟨q, hq, fun _ => Iff.rfl⟩ hB
  convert truthTable_mem_P hqB hr hd using 1
  ext a
  exact hL a

end Cslib.Complexity

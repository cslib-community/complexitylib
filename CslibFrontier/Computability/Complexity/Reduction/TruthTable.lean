/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import CslibFrontier.Computability.Reduction.TruthTable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomial-time truth-table reductions

A nonadaptive reduction uses a uniformly computed indexed batch of queries, a unary query count,
and a polynomial-time Boolean combiner. The combiner receives the original input and all answers.
The query generator is total even outside the used range; unused outputs do not affect semantics.
The answer word `truthTableAnswers` and the resource-free kernel `TruthTableReducibleBy` live in
`CslibFrontier.Computability.Reduction.TruthTable`, publicly re-exported here.
`PolyTimeTruthTableReducible` is by definition `TruthTableReducibleBy` with polynomial-time data,
so the kernel lemmas prove its complementation and many-one embedding below.

## Main definitions

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

variable {α : Type}

/-- A polynomial-time truth-table reduction generates all queries without access to their
answers, then applies a polynomial-time Boolean combiner to the input and answer word.
The count is computed in unary; query lengths and counts may vary at fixed input length. -/
def PolyTimeTruthTableReducible {β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (L : Set α) (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β) (d : α × List Bool → Bool),
    (ComputableInPolyTime r encA encUnary ∧
      ComputableInPolyTime q (encPair encA encUnary) encB ∧
      ComputableInPolyTime d (encPair encA encBits) encBool) ∧
    ∀ a, a ∈ L ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true

variable {β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {L : Set α} {B : Set β}

/-- Every polynomial-time many-one reduction is a polynomial-time truth-table reduction making a
single query. -/
theorem PolyTimeReducible.polyTimeTruthTableReducible
    (h : PolyTimeReducible encA encB L B) : PolyTimeTruthTableReducible encA encB L B :=
  ManyOneReducibleBy.truthTableReducibleBy (fun _ hf => ⟨by fun_prop, by fun_prop, by fun_prop⟩) h

/-- Every problem reduces to itself under polynomial-time truth-table reductions. -/
@[refl]
theorem PolyTimeTruthTableReducible.refl (encA : α ↪ List Bool) (L : Set α) :
    PolyTimeTruthTableReducible encA encA L L :=
  (PolyTimeReducible.refl encA L).polyTimeTruthTableReducible

/-- Negating the Boolean combiner reduces the complement `Lᶜ` to `B`. -/
theorem PolyTimeTruthTableReducible.compl_left
    (h : PolyTimeTruthTableReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB Lᶜ B :=
  TruthTableReducibleBy.compl_left (fun _ _ _ ⟨hr, hq, hd⟩ => ⟨hr, hq, by fun_prop⟩) h

/-- Negating each answer bit before invoking the combiner reduces `L` to `Bᶜ`. -/
theorem PolyTimeTruthTableReducible.compl_right
    (h : PolyTimeTruthTableReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB L Bᶜ :=
  TruthTableReducibleBy.compl_right (fun _ _ _ ⟨hr, hq, hd⟩ => ⟨hr, hq, by fun_prop⟩) h

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
  classical
  obtain ⟨f, hf, hAf⟩ := mem_P.mp hA
  have hans : ComputableInPolyTime
      (fun a => (List.range (r a)).map fun i => f (a, i)) encA encBits :=
    ComputableInPolyTime.mapToBitsWithInput (ComputableInPolyTime.range.comp hr) hf
  refine mem_P.mpr ⟨fun a => d (a, (List.range (r a)).map fun i => f (a, i)),
    hd.comp (ComputableInPolyTime.id'.prod hans), fun a => ?_⟩
  simp [truthTableAnswers_eq_map_range, hAf]

/-- **`P` is closed under polynomial-time truth-table reductions.** -/
theorem PolyTimeTruthTableReducible.mem_P
    (h : PolyTimeTruthTableReducible encA encB L B) (hB : B ∈ P encB) : L ∈ P encA := by
  obtain ⟨r, q, d, ⟨hr, hq, hd⟩, hL⟩ := h
  have hqB : q ⁻¹' B ∈ P (encPair encA encUnary) :=
    PolyTimeReducible.mem_P ⟨q, hq, fun _ => Iff.rfl⟩ hB
  convert truthTable_mem_P hqB hr hd using 1
  ext a
  exact hL a

end Cslib.Complexity

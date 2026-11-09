/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic
public import CslibFrontier.Computability.Circuit.Boolean.PPoly

/-!
# Promise problems solved by circuits

`PromiseSIZE s` and `PromisePPoly` lift the circuit classes `SIZE s` and `P/poly`
(`Cslib.Circuits.Boolean.SIZE`, `Cslib.Circuits.Boolean.PPoly`) to promise problems over words
(`Cslib.Complexity.promiseClass`). A family of circuits, one for each input length, solves a
promise problem when the circuit for each length gives the right answer on the promised words of
that length; what it computes on the other words does not matter. The lifted classes consist
exactly of the promise problems solved by circuit families of the given size
(`mem_PromiseSIZE_iff`, `mem_PromisePPoly_iff`).

## Main definitions

* `Cslib.Complexity.PromiseSIZE`, `Cslib.Complexity.PromisePPoly`.

## Main results

* `Cslib.Complexity.mem_PromiseSIZE_iff`: a promise problem is in `PromiseSIZE s` exactly when a
  family of circuits of size at most `s n` on inputs of length `n` solves it.
* `Cslib.Complexity.mem_PromisePPoly_iff`: a promise problem is in `PromisePPoly` exactly when a
  family of circuits of polynomial size solves it.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
* [O. Goldreich, *On promise problems: a survey*][Goldreich2006]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Circuits Cslib.Circuits.Boolean PromiseProblem

/-- The promise problems over words solved by circuits of size at most `s n` on the inputs of
length `n`: the lift of `SIZE s`. -/
def PromiseSIZE (s : ℕ → ℕ) : Set (PromiseProblem (List Bool)) := promiseClass (SIZE s)

/-- The promise problems over words solved by circuits of polynomial size: the lift of
`P/poly`. -/
def PromisePPoly : Set (PromiseProblem (List Bool)) := promiseClass PPoly

variable {Q : PromiseProblem (List Bool)} {C : ∀ n, Circuit signature n 1} {L : Language Bool}

/-- A family of circuits computing the slices of `L` accepts exactly the words of `L`. -/
private theorem eval_eq_true_iff (hC : ∀ n, (C n).Computes interpretation (single (L.slice n)))
    (w : List Bool) : (C w.length).eval interpretation (w[·]) 0 = true ↔ w ∈ L := by
  rw [hC, single_apply, Language.slice_eq_true_iff]
  simp only [Fin.getElem_fin, List.ofFn_getElem]

/-- A family of circuits computing the slices of a completion of `Q` solves `Q`. -/
private theorem solvedBy_of_computes (hC : ∀ n, (C n).Computes interpretation (single (L.slice n)))
    (hyes : Q.yes ⊆ L) (hno : Disjoint (L : Set (List Bool)) Q.no) :
    Q.SolvedBy fun w => (C w.length).eval interpretation (w[·]) 0 :=
  ⟨fun w hw => (eval_eq_true_iff hC w).2 (hyes hw), fun w hw =>
    Bool.eq_false_iff.2 fun h => Set.disjoint_right.1 hno hw ((eval_eq_true_iff hC w).1 h)⟩

/-- The language accepted by a family of circuits with one output. -/
private def familyLanguage (C : ∀ n, Circuit signature n 1) : Language Bool :=
  Language.ofSlices fun n x => (C n).eval interpretation x 0

private theorem computes_familyLanguage (n : ℕ) :
    (C n).Computes interpretation (single ((familyLanguage C).slice n)) :=
  Circuit.computes_single_iff.2 fun _ => by rw [familyLanguage, Language.slice_ofSlices]

/-- A family of circuits that solves `Q` accepts a completion of `Q`. -/
private theorem familyLanguage_separates
    (h : Q.SolvedBy fun w => (C w.length).eval interpretation (w[·]) 0) :
    Q.yes ⊆ familyLanguage C ∧ Disjoint (familyLanguage C : Set (List Bool)) Q.no :=
  ⟨fun w hw => Language.mem_ofSlices.2 (h.1 w hw), Set.disjoint_right.2 fun w hw hL =>
    Bool.false_ne_true ((h.2 w hw).symm.trans (Language.mem_ofSlices.1 hL))⟩

/-- **Promise `SIZE` is solvability by circuits on the promise.** A promise problem is in
`PromiseSIZE s` exactly when a family of circuits of size at most `s n` on inputs of length `n`
answers correctly on every promised word. -/
theorem mem_PromiseSIZE_iff {s : ℕ → ℕ} :
    Q ∈ PromiseSIZE s ↔ ∃ C : ∀ n, Circuit signature n 1, (∀ n, (C n).size ≤ s n) ∧
      Q.SolvedBy fun w => (C w.length).eval interpretation (w[·]) 0 := by
  constructor
  · rintro ⟨L, hL, hyes, hno⟩
    choose C hC hs using fun n => complexity_le_iff.1 (hL n)
    exact ⟨C, hs, solvedBy_of_computes (L := L) hC hyes hno⟩
  · rintro ⟨C, hs, h⟩
    exact ⟨familyLanguage C,
      fun n => (complexity_le_of_computes _ (computes_familyLanguage n)).trans (hs n),
      familyLanguage_separates h⟩

/-- **Promise `P/poly` is solvability by polynomial-size circuits on the promise.** A promise
problem is in `PromisePPoly` exactly when a family of circuits of polynomial size answers correctly
on every promised word. -/
theorem mem_PromisePPoly_iff :
    Q ∈ PromisePPoly ↔ ∃ (C : ∀ n, Circuit signature n 1) (p : ℕ → ℕ), PolynomiallyBounded p ∧
      (∀ n, (C n).size ≤ p n) ∧ Q.SolvedBy fun w => (C w.length).eval interpretation (w[·]) 0 := by
  constructor
  · rintro ⟨L, hL, hyes, hno⟩
    obtain ⟨C, p, hp, hC⟩ := mem_PPoly_iff_exists_circuits.1 hL
    exact ⟨C, p, hp, fun n => (hC n).1, solvedBy_of_computes (L := L) (fun n => (hC n).2) hyes hno⟩
  · rintro ⟨C, p, hp, hs, h⟩
    exact ⟨familyLanguage C,
      mem_PPoly_iff_exists_circuits.2 ⟨C, p, hp, fun n => ⟨hs n, computes_familyLanguage n⟩⟩,
      familyLanguage_separates h⟩

/-- A language is in the lift of `SIZE s` exactly when it is in `SIZE s`. -/
@[simp] theorem ofSet_mem_PromiseSIZE {s : ℕ → ℕ} :
    ofSet (L : Set (List Bool)) ∈ PromiseSIZE s ↔ L ∈ SIZE s :=
  ofSet_mem_promiseClass

/-- A language is in the lift of `P/poly` exactly when it is in `P/poly`. -/
@[simp] theorem ofSet_mem_PromisePPoly : ofSet (L : Set (List Bool)) ∈ PromisePPoly ↔ L ∈ PPoly :=
  ofSet_mem_promiseClass

end Cslib.Complexity

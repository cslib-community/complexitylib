/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Problems.SAT.Paddable
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Complexity.Reduction.Nontrivial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# The Berman–Hartmanis isomorphism conjecture

The Berman–Hartmanis conjecture says that all `NP`-complete languages are polynomial-time
isomorphic [Berman and Hartmanis][BermanHartmanis1975]. It is stated here, as a hypothesis, for
languages of bit strings: `Cslib.Complexity.BermanHartmanisConjecture`.

Following the source, the conjecture is stated for languages of strings, here bit strings. Like
the source's, it implies `P ≠ NP` (`Cslib.Complexity.BermanHartmanisConjecture.P_ne_NP`).

## Source and adaptations

The source version is the 1975 Cornell technical report
[Berman and Hartmanis][BermanHartmanis1975], §I (printed p. 2), which states the conjecture and
its `P ≠ NP` consequence. Locators in this file refer to that report; the numbering of the 1977
journal version [Berman and Hartmanis][BermanHartmanis1977] has not been checked. The report's
languages are sets of strings; here the alphabet is fixed to `Bool`, with instances `List Bool`
under `encBits`, and `NP`-completeness and `≅ᵖ` are the library's
(`Cslib.Complexity.NPComplete`, `Cslib.Complexity.PolyTimeIsomorphic`). The proof of the `P ≠ NP`
consequence given here, through a singleton and its complement, and the equivalence with
paddability are derived in this library from the formal statements and are not transcriptions
of arguments in the report.

## Main definitions

* `Cslib.Complexity.BermanHartmanisConjecture`: all `NP`-complete languages of bit strings are
  pairwise polynomial-time isomorphic.

## Main results

* `Cslib.Complexity.bermanHartmanisConjecture_iff_paddable`: the conjecture holds exactly when
  every `NP`-complete language of bit strings is paddable.
* `Cslib.Complexity.BermanHartmanisConjecture.SAT_notMem_P`,
  `Cslib.Complexity.BermanHartmanisConjecture.P_ne_NP`: the conjecture implies `P ≠ NP`, since if
  `P = NP` then a singleton and its complement are both `NP`-complete.

## References

* [L. Berman, J. Hartmanis, *On isomorphisms and density of NP and other complete
  sets*][BermanHartmanis1975], Cornell TR75-260 (1975), §I
* [L. Berman, J. Hartmanis, *On isomorphisms and density of NP and other complete
  sets*][BermanHartmanis1977], journal version (numbering not checked)
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- **The Berman–Hartmanis isomorphism conjecture**, as a hypothesis: any two `NP`-complete
languages of bit strings are polynomial-time isomorphic
([Berman and Hartmanis][BermanHartmanis1975], §I, for languages of strings). The body is exposed
so that clients can apply the hypothesis to particular languages. -/
@[expose] def BermanHartmanisConjecture : Prop :=
  ∀ A B : Set (List Bool), NPComplete encBits A → NPComplete encBits B →
    PolyTimeIsomorphic encBits encBits A B

/-- **The conjecture is paddability of every `NP`-complete language** of bit strings. The words
that decode to satisfiable formulas form a paddable `NP`-complete language, and paddable
`NP`-complete languages are isomorphic ([Berman and Hartmanis][BermanHartmanis1975], §III,
Theorem 1, Lemmas 3 and 5 and Theorem 7). -/
theorem bermanHartmanisConjecture_iff_paddable :
    BermanHartmanisConjecture ↔
      ∀ A : Set (List Bool), NPComplete encBits A → Paddable encBits A := by
  constructor
  · intro h A hA
    have hS := CookLevin.SAT_npComplete.preimage_decode cnfDecoder
    exact (h A _ hA hS).paddable (SAT_paddable.preimage_decode cnfDecoder)
  · intro h A B hA hB
    exact hA.polyTimeIsomorphic_of_paddable hB (h A hA) (h B hB) .bits .bits

namespace BermanHartmanisConjecture

/-- **The conjecture puts `SAT` outside `P`.** If `SAT ∈ P`, then `P = NP`, so the languages
`{[]}` and its complement are both `NP`-complete; they cannot be isomorphic, since the inverse
isomorphism would send the two distinct nonempty words `[true]` and `[false]` to the only member
`[]` of the singleton. -/
theorem SAT_notMem_P (h : BermanHartmanisConjecture) : SAT ∉ P encCNF := by
  intro hSAT
  have hPNP : P encBits = NP encBits := CookLevin.SAT_npComplete.P_eq_NP_of_mem_P hSAT encBits
  have hdec : ComputableInPolyTime (fun w : List Bool => decide (w = [])) encBits encBool :=
    ComputableInPolyTime.decide_eq' .id' (.const [])
  have h₀ : ({[]} : Set (List Bool)) ∈ P encBits :=
    ⟨fun w => decide (w = []), hdec, fun w => by
      simp only [Set.mem_singleton_iff, decide_eq_true_eq]⟩
  have hc : ∀ {L : Set (List Bool)}, L ∈ P encBits → ∀ {b₁ b₀ : List Bool}, b₁ ∈ L → b₀ ∉ L →
      NPComplete encBits L := fun hL _ _ hb₁ hb₀ =>
    ⟨hPNP ▸ hL, fun _ enc _ hA' =>
      polyTimeReducible_of_mem_P (CookLevin.SAT_npComplete.P_eq_NP_of_mem_P hSAT enc ▸ hA')
        hb₁ hb₀⟩
  have hnil : ([] : List Bool) ∈ ({[]} : Set (List Bool)) := rfl
  have htrue : [true] ∉ ({[]} : Set (List Bool)) := by
    rw [Set.mem_singleton_iff]
    decide
  obtain ⟨e, -, he⟩ := h _ _ (hc h₀ hnil htrue) (hc (compl_mem_P h₀) htrue (not_not.2 hnil))
  have key : ∀ b : List Bool, b ≠ [] → e.symm b = [] := fun b hb => by
    have := he (e.symm b)
    rw [Equiv.apply_symm_apply, Set.mem_singleton_iff, Set.mem_compl_iff,
      Set.mem_singleton_iff] at this
    exact this.2 hb
  have := e.symm.injective ((key [true] (by decide)).trans (key [false] (by decide)).symm)
  exact absurd this (by decide)

/-- **The conjecture implies `P ≠ NP`**, for formulas and for bit strings
([Berman and Hartmanis][BermanHartmanis1975], §I). -/
theorem P_ne_NP (h : BermanHartmanisConjecture) :
    P encCNF ≠ NP encCNF ∧ P encBits ≠ NP encBits := by
  refine ⟨fun hP => h.SAT_notMem_P (hP ▸ CookLevin.SAT_npComplete.1), fun hP => h.SAT_notMem_P ?_⟩
  have hS := CookLevin.SAT_npComplete.preimage_decode cnfDecoder
  have hmem : cnfDecoder.decode ⁻¹' SAT ∈ P encBits := hP ▸ hS.1
  refine PolyTimeReducible.mem_P ⟨fun φ => encCNF φ, ComputableInPolyTime.id'.of_enc_eq
    fun _ => rfl, fun φ => ?_⟩ hmem
  simp only [Set.mem_preimage, cnfDecoder.decode_enc]

end BermanHartmanisConjecture

end Cslib.Complexity

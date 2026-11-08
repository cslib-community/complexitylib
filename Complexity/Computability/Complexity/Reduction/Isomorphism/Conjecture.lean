/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Problems.SAT.Paddable
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# The Berman–Hartmanis isomorphism conjecture

The Berman–Hartmanis conjecture says that all `NP`-complete languages are polynomial-time
isomorphic [Berman and Hartmanis][BermanHartmanis1977]. It is stated here, as a hypothesis, for
languages of bit strings: `Cslib.Complexity.BermanHartmanisConjecture`.

The string model is essential. Over instance types other than bit strings, a statement for all
`NP`-complete languages fails trivially when `P = NP`, because every nontrivial language in `P`
is then `NP`-complete, including languages over finite types, which cannot be in bijection with
an infinite type.

## Main definitions

* `Cslib.Complexity.BermanHartmanisConjecture`: all `NP`-complete languages of bit strings are
  pairwise polynomial-time isomorphic.

## Main results

* `Cslib.Complexity.polyTimeReducible_of_mem_P`: every language in `P` reduces to every language
  with a member and a nonmember.
* `Cslib.Complexity.bermanHartmanisConjecture_iff_paddable`: the conjecture holds exactly when
  every `NP`-complete language of bit strings is paddable.
* `Cslib.Complexity.BermanHartmanisConjecture.SAT_notMem_P`,
  `Cslib.Complexity.BermanHartmanisConjecture.P_ne_NP`: the conjecture implies `P ≠ NP`, since if
  `P = NP` then a singleton and its complement are both `NP`-complete.

## References

* [L. Berman, J. Hartmanis, *On isomorphisms and density of NP and other complete
  sets*][BermanHartmanis1977]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- **The Berman–Hartmanis isomorphism conjecture**, as a hypothesis: any two `NP`-complete
languages of bit strings are polynomial-time isomorphic
[Berman and Hartmanis][BermanHartmanis1977]. -/
def BermanHartmanisConjecture : Prop :=
  ∀ A B : Set (List Bool), NPComplete encBits A → NPComplete encBits B →
    PolyTimeIsomorphic encBits encBits A B

/-- Every language in `P` reduces to every language with a member `b₁` and a nonmember `b₀`:
decide membership and output `b₁` or `b₀`. -/
theorem polyTimeReducible_of_mem_P {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (hA : A ∈ P encA) {b₁ b₀ : β} (h₁ : b₁ ∈ B) (h₀ : b₀ ∉ B) :
    PolyTimeReducible encA encB A B := by
  obtain ⟨f, hf, hfA⟩ := hA
  refine ⟨fun a => if f a then b₁ else b₀, hf.ite (.const b₁) (.const b₀), fun a => ?_⟩
  rw [hfA a]
  cases hfa : f a
  · simp only [hfa, Bool.false_eq_true, ↓reduceIte, h₀]
  · simp only [hfa, ↓reduceIte, h₁]

/-- **The conjecture is paddability of every `NP`-complete language** of bit strings
[Berman and Hartmanis][BermanHartmanis1977]. The words that decode to satisfiable formulas form a
paddable `NP`-complete language, and paddable `NP`-complete languages are isomorphic. -/
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
[Berman and Hartmanis][BermanHartmanis1977]. -/
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

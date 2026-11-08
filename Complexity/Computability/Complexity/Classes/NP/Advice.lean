/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.GetD

/-!
# NP with polynomial advice

A problem is in `NP/poly` when it is verified in nondeterministic polynomial time with the help of
an advice string that depends only on the length of the instance and has polynomial length
[Karp and Lipton][KarpLipton1980]. As for `Cslib.Circuits.Boolean.PAdvice`, the advice is paired
with the instance: `A ∈ NPPoly enc` when there are advice `adv : ℕ → List Bool` of polynomial
length and a problem `B ∈ NP` of pairs, for the encoding `frame u ++ enc a` of `(u, a)`, such that
`a ∈ A` exactly when `(adv (enc a).length, a) ∈ B`. `coNP/poly` consists of the complements
(`Cslib.Complexity.coNPPoly`).

`NP ⊆ NP/poly` with empty advice (`Cslib.Complexity.NP_subset_NPPoly`). `NP/poly` is closed under
polynomial-time reductions (`Cslib.Complexity.PolyTimeReducible.mem_NPPoly`): the advice for
instances of length `n` lists the advice of the target problem for every length up to a polynomial
bound on the length of the reduced instances, and the verifier selects the entry for the length of
the reduced instance. In particular, if one `coNP`-complete problem is in `NP/poly`, then so is
every problem in `coNP` (`Cslib.Complexity.coNP_subset_NPPoly_of_coNPComplete`), and
`coNP ⊆ NP/poly` exactly when `NP ⊆ coNP/poly` (`Cslib.Complexity.coNP_subset_NPPoly_iff`).

`coNP ⊆ NP/poly` is the conclusion of the theorem of Fortnow and Santhanam on OR-distillations
(`Complexity.Computability.Complexity.Parameterized.Distillation`), and the hypothesis of Yap's
theorem that it collapses the polynomial hierarchy to its third level [Yap][Yap1983], which is not
formalized here.

## Main definitions

* `Cslib.Complexity.NPPoly`, `Cslib.Complexity.coNPPoly`.

## Main results

* `Cslib.Complexity.NP_subset_NPPoly`, `Cslib.Complexity.coNP_subset_coNPPoly`.
* `Cslib.Complexity.PolyTimeReducible.mem_NPPoly`,
  `Cslib.Complexity.PolyTimeReducible.mem_coNPPoly`: closure under polynomial-time reductions.
* `Cslib.Complexity.coNP_subset_NPPoly_of_coNPComplete`: a `coNP`-complete problem in `NP/poly`
  puts all of `coNP` in `NP/poly`.
* `Cslib.Complexity.coNP_subset_NPPoly_iff`: `coNP ⊆ NP/poly` exactly when `NP ⊆ coNP/poly`.

## References

* [R. M. Karp, R. J. Lipton, *Some connections between nonuniform and uniform complexity
  classes*][KarpLipton1980]
* [C.-K. Yap, *Some consequences of non-uniform conditions on uniform classes*][Yap1983]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}

/-- **NP with polynomial advice** [Karp and Lipton][KarpLipton1980]: the problems `A` with advice
`adv` of polynomial length and a problem `B ∈ NP` of pairs, for the encoding `frame u ++ enc a` of
`(u, a)`, such that `a ∈ A` exactly when `(adv (enc a).length, a) ∈ B`. -/
def NPPoly (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ adv : ℕ → List Bool, PolynomiallyBounded (fun n => (adv n).length) ∧
    ∃ B ∈ NP (encPair encBits enc), ∀ a, a ∈ A ↔ (adv (enc a).length, a) ∈ B}

/-- The problems whose complements are in `NP/poly`. -/
def coNPPoly (enc : α ↪ List Bool) : Set (Set α) := {A | Aᶜ ∈ NPPoly enc}

theorem mem_coNPPoly : A ∈ coNPPoly enc ↔ Aᶜ ∈ NPPoly enc := Iff.rfl

/-- **`NP ⊆ NP/poly`**: an `NP` verifier ignores empty advice. -/
theorem NP_subset_NPPoly : NP enc ⊆ NPPoly enc := by
  intro A hA
  refine ⟨fun _ => [], by simpa using PolynomiallyBounded.const 0, Prod.snd ⁻¹' A, ?_,
    fun a => Iff.rfl⟩
  exact PolyTimeReducible.mem_NP ⟨Prod.snd, snd encBits enc, fun _ => Iff.rfl⟩ hA

/-- **`coNP ⊆ coNP/poly`**. -/
theorem coNP_subset_coNPPoly : coNP enc ⊆ coNPPoly enc := fun _ hA => NP_subset_NPPoly hA

/-- The sum of `2 * |w| + 1` over the advice strings for the lengths below `N` is at most
`N * (2 * M + 1)` when each of them has length at most `M`. -/
private theorem sum_map_range_le (adv : ℕ → List Bool) (N M : ℕ)
    (h : ∀ m < N, (adv m).length ≤ M) :
    ((List.range N).map fun m => 2 * (adv m).length + 1).sum ≤ N * (2 * M + 1) := by
  have := List.sum_le_length_nsmul ((List.range N).map fun m => 2 * (adv m).length + 1)
    (2 * M + 1) (by
      simp only [List.mem_map, List.mem_range]
      rintro _ ⟨m, hm, rfl⟩
      have := h m hm
      omega)
  simpa using this

/-- **`NP/poly` is closed under polynomial-time reductions.** The advice for instances of length
`n` lists the advice of the target problem for every length up to a polynomial bound on the length
of the reduced instances; the verifier decodes this list and selects the entry for the length of
the reduced instance. -/
theorem PolyTimeReducible.mem_NPPoly (h : PolyTimeReducible enc encB A B)
    (hB : B ∈ NPPoly encB) : A ∈ NPPoly enc := by
  obtain ⟨f, hf, hAB⟩ := h
  obtain ⟨adv, hadv, B', hB', hBB'⟩ := hB
  obtain ⟨q, hq⟩ := ((encoding_length encB).comp hf).polyBounded.exists_polynomial
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.1 hadv
  -- the advice: the target advice for all lengths up to `q n`
  let adv' : ℕ → List Bool := fun n => encList encBits ((List.range (q.eval n + 1)).map adv)
  let D := Decoder.list Decoder.bits
  let g : List Bool × α → List Bool × β :=
    fun x => ((D.decode x.1).getD (encB (f x.2)).length [], f x.2)
  have hg : ComputableInPolyTime g (encPair encBits enc) (encPair encBits encB) := by
    refine ComputableInPolyTime.prod ?_ (hf.comp (snd encBits enc))
    exact listGetDWithInput (D.computableInPolyTime.comp (fst encBits enc))
      ((encoding_length encB).comp (hf.comp (snd encBits enc))) []
  refine ⟨adv', ?_, g ⁻¹' B', PolyTimeReducible.mem_NP ⟨g, hg, fun _ => Iff.rfl⟩ hB',
    fun a => ?_⟩
  · refine PolynomiallyBounded.mono_of_le (g := fun n =>
      (q.eval n + 1) * (2 * (c * (q.eval n + 1) ^ d) + 1)) (by fun_prop) fun n => ?_
    simp only [adv', length_encList, List.map_map, Function.comp_def]
    refine sum_map_range_le adv _ _ fun m hm => (hcd m).trans ?_
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d)
  · have hlt : (encB (f a)).length < ((List.range (q.eval (enc a).length + 1)).map adv).length := by
      simpa using Nat.lt_succ_of_le (hq a)
    have hdec : D.decode (adv' (enc a).length) =
        (List.range (q.eval (enc a).length + 1)).map adv := D.decode_enc _
    change a ∈ A ↔ g (adv' (enc a).length, a) ∈ B'
    simp only [g, hdec, List.getD_eq_getElem _ _ hlt, List.getElem_map, List.getElem_range]
    exact (hAB a).trans (hBB' (f a))

/-- `coNP/poly` is closed under polynomial-time reductions. -/
theorem PolyTimeReducible.mem_coNPPoly (h : PolyTimeReducible enc encB A B)
    (hB : B ∈ coNPPoly encB) : A ∈ coNPPoly enc :=
  h.compl.mem_NPPoly hB

/-- If a `coNP`-complete problem is in `NP/poly`, then so is every problem in `coNP`, for every
encoding of its instances. -/
theorem coNP_subset_NPPoly_of_coNPComplete (hB : coNPComplete encB B) (hBP : B ∈ NPPoly encB)
    {γ : Type} (encC : γ ↪ List Bool) : coNP encC ⊆ NPPoly encC :=
  fun _ hC => (hB.2 encC _ hC).mem_NPPoly hBP

/-- **`coNP ⊆ NP/poly` exactly when `NP ⊆ coNP/poly`**, for any encoding: both say that the
complement of every problem in `NP` is in `NP/poly`. -/
theorem coNP_subset_NPPoly_iff : coNP enc ⊆ NPPoly enc ↔ NP enc ⊆ coNPPoly enc := by
  refine ⟨fun h A hA => h (show Aᶜ ∈ coNP enc by rwa [mem_coNP, compl_compl]),
    fun h A hA => ?_⟩
  simpa [mem_coNPPoly] using h hA

end Cslib.Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Multigraph.CutSpace
public import Complexity.Logics.Propositional.Algebraic.SumOfSquares.Parity
import Complexity.Foundations.Data.Finset.SymmDiff

/-!
# Grigoriev's sum-of-squares degree lower bound for Tseitin parity systems

Let `ends : E → Sym2 V` be a connected multigraph with expansion `e(G)`
(`Cslib.Multigraph.minBalancedCut`): the least number of edges leaving a set of between a third and
two thirds of the vertices. Every equation obtained by summing vertex equations of a Tseitin parity
system is the equation of the edge cut of the set `U` of summed vertices, with right-hand side the
total charge of `U`. Below width `e(G)`, the dichotomy
`Cslib.Multigraph.three_mul_card_lt_of_card_edgeCut_lt` keeps `U` smaller than a third of the
vertices along every width-`d` derivation, so `0 = 1`, the equation of the cut of the set of all
vertices, is never reached (`Cslib.Logic.PL.ParitySystem.not_derives_tseitin_empty_true`). This is
the argument of [Ben-Sasson and Wigderson][BenSassonWigderson2001] for resolution width, run on
parity equations.

With Schoenebeck's lemma (`Cslib.Logic.PL.ParitySystem.not_sos_refutableInDegree_toPolys`) it gives
**Grigoriev's theorem**: the `±1` encoding of a Tseitin parity system on a connected multigraph has
no sum-of-squares refutation of degree less than `e(G)`
(`Cslib.Logic.PL.Tseitin.minBalancedCut_le_of_sos_refutableInDegree`), over every strictly ordered
commutative ring. Linear degree lower bounds of this kind for Positivstellensatz refutations of
parity systems are due to [Grigoriev][Grigoriev2001] (whose text was not consulted for this file).
[Barak and Steurer, lecture "Higher-degree integrality gaps", Lemma 24][BarakSteurer2016] state the
Tseitin case for a `(1 + ε)`-vertex-expanding `d`-regular graph on `n` vertices, all charges `1`
and the `0/1` encoding, with a pseudo-distribution of degree `n / 4`. The statement here instead
measures expansion by `e(G)`, allows any multigraph and any charges, and uses the `±1` encoding.
The proof follows the pseudo-expectation of [Schoenebeck, Lemma 13][Schoenebeck2008], as
presented for random `3`-XOR in [Barak and Steurer, lecture "Higher-degree integrality gaps",
Theorem 2 and Lemma 7][BarakSteurer2016]; random `3`-XOR itself is not treated.

## Main results

* `Cslib.Logic.PL.ParitySystem.not_derives_tseitin_empty_true`: on a connected multigraph,
  width-`d` derivations from a Tseitin parity system do not reach `0 = 1` when `d < e(G)`.
* `Cslib.Logic.PL.Tseitin.not_sos_refutableInDegree_of_lt_minBalancedCut`,
  `Cslib.Logic.PL.Tseitin.minBalancedCut_le_of_sos_refutableInDegree`: **Grigoriev's theorem**,
  sum-of-squares refutations of Tseitin parity systems have degree at least `e(G)`.

## References

* [D. Grigoriev, *Linear lower bound on degrees of Positivstellensatz calculus proofs for the
  parity*][Grigoriev2001]
* [G. Schoenebeck, *Linear level Lasserre lower bounds for certain k-CSPs*][Schoenebeck2008]
* [B. Barak, D. Steurer, *Proofs, beliefs, and algorithms through the lens of sum-of-squares*,
  lecture notes][BarakSteurer2016]
* [E. Ben-Sasson, A. Wigderson, *Short proofs are narrow—resolution made
  simple*][BenSassonWigderson2001]
-/

public section

namespace Cslib.Logic.PL

open Finset
open scoped symmDiff

namespace ParitySystem

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {ends : E → Sym2 V} {χ : V → Bool}

/-- Below width `e(G)`, every equation derived from a Tseitin parity system is the equation of the
edge cut of a set `U` of fewer than a third of the vertices, with right-hand side the total charge
of `U`. -/
private theorem exists_of_derives {d : ℕ} (hd : d < Multigraph.minBalancedCut ends) {T : Finset E}
    {c : Bool} (h : (tseitin ends χ).Derives d T c) :
    ∃ U, Multigraph.edgeCut ends U = T ∧ parityOn U χ = c ∧ 3 * #U < Fintype.card V := by
  have hV : 2 ≤ Fintype.card V := by
    by_contra hV
    have : Subsingleton V := Fintype.card_le_one_iff_subsingleton.1 (by omega)
    rw [Multigraph.minBalancedCut_eq_zero_of_subsingleton] at hd
    omega
  induction h with
  | empty => exact ⟨∅, Multigraph.edgeCut_empty ends, parityOn_empty χ, by simp; omega⟩
  | mem he hS =>
    obtain ⟨v, hv⟩ := mem_tseitin.1 he
    simp only [Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    refine ⟨{v}, Multigraph.edgeCut_singleton ends v, parityOn_singleton v χ, ?_⟩
    refine Multigraph.three_mul_card_lt_of_card_edgeCut_lt (ends := ends) (S := {v}) ?_
      (by rw [Finset.card_singleton]; omega)
    rw [Multigraph.edgeCut_singleton]
    omega
  | symmDiff _ _ hST ih₁ ih₂ =>
    obtain ⟨U₁, rfl, rfl, h₁⟩ := ih₁
    obtain ⟨U₂, rfl, rfl, h₂⟩ := ih₂
    refine ⟨U₁ ∆ U₂, Multigraph.edgeCut_symmDiff ends U₁ U₂, parityOn_symmDiff U₁ U₂ χ, ?_⟩
    refine Multigraph.three_mul_card_lt_of_card_edgeCut_lt (ends := ends) ?_ ?_
    · rw [Multigraph.edgeCut_symmDiff]
      omega
    · have := card_symmDiff_le U₁ U₂
      omega

/-- **Width-`d` derivations from Tseitin parity systems do not reach `0 = 1` below `e(G)`**: on a
connected multigraph, if `d < e(G)` then `0 = 1` is not derivable in width `d` from the Tseitin
parity system, whatever the charges. -/
theorem not_derives_tseitin_empty_true (hG : (Multigraph.toSimpleGraph ends).Connected) {d : ℕ}
    (hd : d < Multigraph.minBalancedCut ends) : ¬ (tseitin ends χ).Derives d ∅ true := by
  intro h
  obtain ⟨U, hU, hc, hcard⟩ := exists_of_derives hd h
  rcases Multigraph.eq_empty_or_eq_univ_of_edgeCut_eq_empty hG hU with rfl | rfl
  · rw [parityOn_empty] at hc
    exact Bool.false_ne_true hc
  · rw [card_univ] at hcard
    omega

end ParitySystem

namespace Tseitin

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
  {ends : E → Sym2 V} {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **Grigoriev's theorem** [Grigoriev][Grigoriev2001] (compare [Barak and Steurer, lecture
"Higher-degree integrality gaps", Lemma 24][BarakSteurer2016]), through Schoenebeck's
pseudo-expectation [Schoenebeck, Lemma 13][Schoenebeck2008]: over a strictly ordered commutative
ring, the `±1` encoding of a Tseitin parity system on a connected multigraph, with any charges, has
no sum-of-squares refutation of degree less than `e(G)`. -/
theorem not_sos_refutableInDegree_of_lt_minBalancedCut
    (hG : (Multigraph.toSimpleGraph ends).Connected) (χ : V → Bool) {d : ℕ}
    (hd : d < Multigraph.minBalancedCut ends) :
    ¬ SOS.RefutableInDegree ((ParitySystem.tseitin ends χ).toPolys R) d := by
  classical
  exact ParitySystem.not_sos_refutableInDegree_toPolys
    (ParitySystem.not_derives_tseitin_empty_true hG hd)

/-- **Grigoriev's theorem**, in the form `e(G) ≤ d`: a sum-of-squares refutation of degree at most
`d` of the `±1` encoding of a Tseitin parity system on a connected multigraph has
`e(G) ≤ d`. -/
theorem minBalancedCut_le_of_sos_refutableInDegree
    (hG : (Multigraph.toSimpleGraph ends).Connected) {χ : V → Bool} {d : ℕ}
    (h : SOS.RefutableInDegree ((ParitySystem.tseitin ends χ).toPolys R) d) :
    Multigraph.minBalancedCut ends ≤ d :=
  not_lt.1 fun hd => not_sos_refutableInDegree_of_lt_minBalancedCut hG χ hd h

end Tseitin

end Cslib.Logic.PL

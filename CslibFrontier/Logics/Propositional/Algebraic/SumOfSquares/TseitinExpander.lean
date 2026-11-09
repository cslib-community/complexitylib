/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Multigraph
public import CslibFrontier.Logics.Propositional.Algebraic.SumOfSquares.Tseitin
import CslibFrontier.Foundations.Combinatorics.Expander.MultigraphExistence

/-!
# Tseitin parity systems on expanders need linear sum-of-squares degree

A rotation map `G` (`Cslib.RotationMap`) with edge expansion `h(G) > 0` is a connected multigraph
with `h(G) |V| / 3 ≤ e(G)` (`Cslib.RotationMap.edgeExpansion_mul_card_div_three_le_minBalancedCut`),
so by Grigoriev's theorem (`Cslib.Logic.PL.Tseitin.minBalancedCut_le_of_sos_refutableInDegree`)
sum-of-squares refutations of its Tseitin parity systems have degree at least `h(G) |V| / 3`
(`Cslib.Logic.PL.Tseitin.edgeExpansion_mul_card_div_three_le_of_sos_refutableInDegree`).

Constant-degree expanders (`Cslib.RotationMap.expander`) have `120` labels and edge expansion at
least `1 / 6000` (`Cslib.RotationMap.le_edgeExpansion_expander`). Their Tseitin parity systems with
a single charged vertex form **a family of unsatisfiable parity systems with `n` equations of
constant width on `O(n)` variables whose sum-of-squares refutations need degree `Ω(n)`**
(`Cslib.Logic.PL.ParitySystem.exists_forall_sos_refutableInDegree_le`). The linear degree bound is
Grigoriev's [Grigoriev][Grigoriev2001]; the explicit constants `120` and `18000` are not from that
source but from this library's expanders and the bound `h(G) |V| / 3 ≤ e(G)`. The expanders, and
so the systems, are obtained non-constructively, from a counting argument
(`Cslib.RotationMap.exists_spectralExpansion_le`).

## Main results

* `Cslib.Logic.PL.Tseitin.edgeExpansion_mul_card_div_three_le_of_sos_refutableInDegree`: the degree
  lower bound for Tseitin parity systems on rotation maps, in terms of edge expansion.
* `Cslib.Logic.PL.ParitySystem.exists_forall_sos_refutableInDegree_le`: for every `n ≥ 2`, an
  unsatisfiable parity system with `n` equations of at most `120` variables each, on at most
  `120 n` variables, whose sum-of-squares refutations have degree at least `n / 18000`.

## References

* [D. Grigoriev, *Linear lower bound on degrees of Positivstellensatz calculus proofs for the
  parity*][Grigoriev2001]
* [G. Schoenebeck, *Linear level Lasserre lower bounds for certain k-CSPs*][Schoenebeck2008]
* [B. Barak, D. Steurer, *Proofs, beliefs, and algorithms through the lens of sum-of-squares*,
  lecture notes][BarakSteurer2016]
-/

public section

namespace Cslib.Logic.PL

universe u

open Finset

namespace Tseitin

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]
  (G : RotationMap V D)

/-- **The sum-of-squares degree lower bound for Tseitin parity systems on rotation maps**: if
`h(G) > 0`, every sum-of-squares refutation of degree at most `d` of the `±1` encoding of a
Tseitin parity system on `G`, over a strictly ordered commutative ring, has
`h(G) |V| / 3 ≤ d`. -/
theorem edgeExpansion_mul_card_div_three_le_of_sos_refutableInDegree {R : Type*} [CommRing R]
    [LinearOrder R] [IsStrictOrderedRing R] (hG : 0 < G.edgeExpansion) {χ : V → Bool} {d : ℕ}
    (h : SOS.RefutableInDegree ((ParitySystem.tseitin G.edgeEnds χ).toPolys R) d) :
    G.edgeExpansion * Fintype.card V / 3 ≤ d := by
  have hc := G.connected_toSimpleGraph_of_edgeExpansion_pos hG
  rw [← G.toSimpleGraph_edgeEnds] at hc
  exact G.edgeExpansion_mul_card_div_three_le_minBalancedCut.trans
    (by exact_mod_cast minBalancedCut_le_of_sos_refutableInDegree hc h)

end Tseitin

namespace ParitySystem

/-- **Unsatisfiable parity systems of constant width need linear sum-of-squares degree.** For
every `n ≥ 2` there is an unsatisfiable parity system with `n` equations, each on at most `120`
variables, on at most `120 n` variables, such that over every strictly ordered commutative ring,
every sum-of-squares refutation of degree at most `d` of its `±1` encoding has `n ≤ 18000 d`. It
is the Tseitin parity system, with a single charged vertex, of a `120`-regular expander on `n`
vertices (`Cslib.RotationMap.expander`), whose existence is proved non-constructively.

The `Ω(n)` degree bound for Tseitin systems on expanders is Grigoriev's [Grigoriev][Grigoriev2001].
The constants `120` and `18000` are not from that source: they come from this library's expanders,
which have `120` labels and edge expansion at least `1 / 6000`
(`Cslib.RotationMap.le_edgeExpansion_expander`), together with `h(G) |V| / 3 ≤ e(G)`. -/
theorem exists_forall_sos_refutableInDegree_le :
    ∀ n ≥ 2, ∃ m ≤ 120 * n, ∃ P : ParitySystem (Fin m),
      P.length = n ∧ (∀ e ∈ P, #e.1 ≤ 120) ∧ (∀ a, ¬ P.Holds a) ∧
      ∀ (R : Type u) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (d : ℕ),
        SOS.RefutableInDegree (P.toPolys R) d → n ≤ 18000 * d := by
  intro n hn
  have : NeZero n := ⟨by omega⟩
  obtain ⟨m, hm, ends, hdeg, hG, hcut⟩ := Multigraph.exists_expander n hn
  let χ : Fin n → Bool := fun v => decide (v = 0)
  refine ⟨m, hm, tseitin ends χ, by simp, fun e he => ?_,
    not_holds_tseitin (by simp [χ, parityOn, filter_eq']), fun R _ _ _ d hd => ?_⟩
  · obtain ⟨v, rfl⟩ := mem_tseitin.1 he
    exact hdeg v
  have h' : (Multigraph.minBalancedCut ends : ℝ) ≤ d := by
    exact_mod_cast Tseitin.minBalancedCut_le_of_sos_refutableInDegree hG hd
  have : (n : ℝ) ≤ 18000 * d := by linarith
  exact_mod_cast this

end ParitySystem

end Cslib.Logic.PL

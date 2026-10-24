/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Fusion.Encoding
public import Complexity.Computability.Circuit.Fusion.Graph
public import Complexity.Probability.PMF
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Uniform
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Linear cover complexity of random bipartite graphs

Every graph on `N` vertices per side has an unrestricted pair cover of length `N`.
In the uniform distribution over all `2^(N²)` such graphs, covers of length at most `N/16`
have probability at most `2⁻ᴺ`, for `N ≥ 16`. The proof counts inclusion-pattern descriptions;
it makes no unproved assumption about graph encodability or incompressibility.

## Main definitions

* `Cslib.Circuits.Fusion.Graph.rowPairs`: the row-and-neighborhood pair for each left vertex.
* `Cslib.Circuits.Fusion.Graph.rowCover`: a worst-case cover with one pair per row.
* `Cslib.Circuits.Fusion.Graph.smallCoverProbability`: uniform probability of a small cover.

## Main results

* `Cslib.Circuits.Fusion.Graph.pairCoverComplexity_le_card`: the matching linear upper bound.
* `Cslib.Circuits.Fusion.Graph.smallCoverProbability_le`: the explicit finite counting bound.
* `Cslib.Circuits.Fusion.Graph.random_cover_complexity`: the quantitative high-probability bound.

## References

* [B. P. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and Two-Dimensional Cover
  Problems*, Theorem 37][CavalarOliveira2025].
-/

@[expose] public section

namespace Cslib.Circuits.Fusion.Graph

open Cslib.Probability

variable {V : Type*} [Fintype V]

/-- Pair each row with the columns neighboring that row, restricted to the graph complement. -/
def rowPairs (graph : Set (V × V)) :
    Fin (Fintype.card V) → Set ↥(graphᶜ) × Set ↥(graphᶜ) :=
  fun i => (Subtype.val ⁻¹' sources (Fin.castAdd (Fintype.card V) i),
    {x | ((Fintype.equivFin V).symm i, x.val.2) ∈ graph})

/-- Every bipartite graph has a cover with one pair per row. -/
def rowCover (graph : Set (V × V)) : PairCover graph sources :=
  PairCover.ofDerivesEmpty (List.ofFn (rowPairs graph)) (fun point hp => by
    let i := Fintype.equivFin V point.1
    have hr : PairDerivation graph sources (List.ofFn (rowPairs graph)) point
        (rowPairs graph i).1 :=
      .input (Fin.castAdd _ i) (by rw [row_source]; rfl)
    have hc : PairDerivation graph sources (List.ofFn (rowPairs graph)) point
        (Subtype.val ⁻¹' sources (Fin.natAdd (Fintype.card V)
          (Fintype.equivFin V point.2))) :=
      .input _ (by rw [column_source]; rfl)
    have hn : PairDerivation graph sources (List.ofFn (rowPairs graph)) point
        (rowPairs graph i).2 := hc.mono (by
      intro y hy
      rw [column_source] at hy
      change y.val.2 = point.2 at hy
      simpa only [rowPairs, i, Equiv.symm_apply_apply, Set.mem_ofPred_eq, hy, Prod.eta] using hp)
    exact (PairDerivation.inter (rowPairs graph i) (List.mem_ofFn.mpr ⟨i, rfl⟩) hr hn).mono
      (by
        intro y hy
        have hyrow : y.val.1 = point.1 := by
          have := hy.1
          change y.val ∈ sources (Fin.castAdd (Fintype.card V) i) at this
          rw [row_source] at this
          exact this
        have hygraph : (point.1, y.val.2) ∈ graph := by
          simpa only [rowPairs, i, Equiv.symm_apply_apply, Set.mem_ofPred_eq] using hy.2
        exact (y.property (by simpa only [← hyrow, Prod.eta] using hygraph)).elim))

/-- The row cover charges exactly one pair for each vertex on the left. -/
@[simp] theorem length_rowCover (graph : Set (V × V)) :
    (rowCover graph).pairs.length = Fintype.card V := by
  simp [rowCover]

/-- The worst-case graph cover complexity is at most the number of rows, including zero. -/
theorem pairCoverComplexity_le_card (graph : Set (V × V)) :
    pairCoverComplexity graph sources ≤ Fintype.card V := by
  simpa only [length_rowCover] using pairCoverComplexity_le (rowCover graph)

/-- Probability that a uniformly chosen labelled bipartite graph has cover complexity at most
`t`. All graphs are equally likely; the two vertex sets are both `Fin N`. -/
noncomputable def smallCoverProbability (N t : ℕ) : ℝ :=
  ((PMF.uniformOfFintype (Set (Fin N × Fin N))).toOuterMeasure
    {graph | pairCoverComplexity graph sources ≤ t}).toReal

/-- Explicit finite counting bound for uniform labelled bipartite graphs. -/
theorem smallCoverProbability_le (N t : ℕ) :
    smallCoverProbability N t ≤
      (2 : ℝ) ^ ((2 * t + 1) * (2 * N + t + 1)) / 2 ^ (N ^ 2) := by
  classical
  rw [smallCoverProbability, PMF.toOuterMeasure_uniformOfFintype_toReal]
  have h := card_small_covers_le (sources (V := Fin N)) t
  simp only [Fintype.card_fin] at h
  have hreal : ((Finset.univ.filter (fun graph : Set (Fin N × Fin N) =>
      pairCoverComplexity graph sources ≤ t)).card : ℝ) ≤
        2 ^ ((2 * t + 1) * (2 * N + t + 1)) := by
    exact_mod_cast (by simpa only [two_mul] using h)
  simpa only [Fintype.card_set, Fintype.card_prod, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat, pow_two, Set.mem_ofPred_eq] using div_le_div_of_nonneg_right hreal
      (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (N * N))

private theorem codeBits_add_le_sq {N : ℕ} (hN : 16 ≤ N) :
    (2 * (N / 16) + 1) * (2 * N + N / 16 + 1) + N ≤ N ^ 2 := by
  have ht : 16 * (N / 16) ≤ N := Nat.mul_div_le N 16
  have hprod := Nat.mul_le_mul ht ht
  have hmix := Nat.mul_le_mul_left N ht
  have hlarge : 16 * N ≤ N * N := Nat.mul_le_mul_right N hN
  nlinarith

/-- A linear budget `N/16` fails except with probability at most `2⁻ᴺ`, once `N ≥ 16`. -/
theorem smallCoverProbability_le_half_pow {N : ℕ} (hN : 16 ≤ N) :
    smallCoverProbability N (N / 16) ≤ (1 / 2 : ℝ) ^ N := by
  apply (smallCoverProbability_le N (N / 16)).trans
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (N ^ 2))).mpr
  rw [div_pow, one_pow]
  rw [div_mul_eq_mul_div, one_mul]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ N)).mpr
  rw [← pow_add]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (codeBits_add_le_sq hN)

/-- **Random graph cover complexity is linear.** With probability at least `1 - 2⁻ᴺ`,
a uniform labelled `N`-by-`N` bipartite graph has cover complexity strictly above `⌊N/16⌋`
and at most `N`. This is a finite quantitative form of Theorem 37. -/
theorem random_cover_complexity {N : ℕ} (hN : 16 ≤ N) :
    1 - (1 / 2 : ℝ) ^ N ≤
      ((PMF.uniformOfFintype (Set (Fin N × Fin N))).toOuterMeasure
        {graph | ((N / 16 : ℕ) : ℕ∞) < pairCoverComplexity graph sources ∧
          pairCoverComplexity graph sources ≤ N}).toReal := by
  have h := PMF.toOuterMeasure_toReal_add_compl
    (PMF.uniformOfFintype (Set (Fin N × Fin N)))
    {graph | pairCoverComplexity graph sources ≤ (N / 16 : ℕ)}
  have heq : ({graph : Set (Fin N × Fin N) |
      pairCoverComplexity graph sources ≤ (N / 16 : ℕ)}ᶜ) =
      {graph | ((N / 16 : ℕ) : ℕ∞) < pairCoverComplexity graph sources ∧
        pairCoverComplexity graph sources ≤ N} := by
    ext graph
    have upper : pairCoverComplexity graph sources ≤ (N : ℕ∞) := by
      simpa only [Fintype.card_fin] using pairCoverComplexity_le_card graph
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, upper, and_true]
  rw [heq] at h
  have hb := smallCoverProbability_le_half_pow hN
  change _ + _ = 1 at h
  unfold smallCoverProbability at hb
  linarith

end Cslib.Circuits.Fusion.Graph

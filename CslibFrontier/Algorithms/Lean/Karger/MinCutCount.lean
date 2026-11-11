/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Karger.Contraction

/-!
# At most `C(n, 2)` minimum cuts

One run of Karger's contraction algorithm outputs one cut (`Cslib.Algorithms.Lean.Karger.cutLaw`,
the block of the second of the two supervertices it leaves), and each fixed minimum cut `{C, Cᶜ}`
is that cut with probability at least `2 / (n (n - 1)) = 1 / C(n, 2)`
(`Cslib.Algorithms.Lean.Karger.two_div_le_cutLaw`, Theorem 2.2 of [KargerStein1996]). Since each
run outputs one cut, the events for distinct minimum cuts are disjoint, so there are at most
`C(n, 2)` minimum cuts (`card_minCuts_le_choose_two`).

Source map ([KargerStein1996], author copy dated 6 August 1996): the count of minimum cuts,
attributed in the proof of Theorem 4.4 to Dinitz, Karzanov and Lomonosov (1976), is
`card_minCuts_le_choose_two`, by the disjointness argument of the proof of Theorem 8.4 (stated
there for `α`-minimal cuts) applied to Theorem 2.2. The `n`-cycle attains it, as remarked after
Theorem 2.2; `CslibFrontierTests.KargerMinCutCount` checks `n = 4` and `5`.

Scope: weights are natural numbers (`Cslib.WeightedCut.IsMultigraph`), and the graph is connected
(`0 < minCut W₀`), without which the count fails (the empty graph on four vertices has seven
non-trivial minimum cuts). A minimum cut `{C, Cᶜ}` is counted once, by its side `C` that avoids a
fixed vertex `x₀`. Not formalized here: the `O((2n)^(2α))` bound on `α`-minimal cuts
(Theorem 8.4), the enumeration and cactus representation of all minimum cuts, and the per-cut
bound for the recursive Karger–Stein algorithm.

## Main results

* `card_minCuts_le_choose_two`: at most `n.choose 2` minimum cuts.

## References

* [D. R. Karger and C. Stein, *A New Approach to the Minimum Cut Problem*][KargerStein1996]
-/

public section

namespace Cslib.Algorithms.Lean.Karger

open scoped ENNReal
open Cslib.WeightedCut

/-- **At most `C(n, 2)` minimum cuts** [KargerStein1996]. A connected multigraph on `Fin n` has at
most `n.choose 2` minimum cuts: at most `n.choose 2` vertex sets `C` with `x₀ ∉ C` and
`cutWeight W₀ C = minCut W₀`. Each such `C` is a non-trivial cut, since `0 < minCut W₀`, and each
minimum cut `{C, Cᶜ}` has exactly one side without `x₀`. The bound is due to Dinitz, Karzanov and
Lomonosov (1976); this is the proof of [KargerStein1996], from the disjointness of the events
that `karger` outputs each minimum cut. -/
theorem card_minCuts_le_choose_two {n : ℕ} {W₀ : Fin n → Fin n → ℕ} (hW₀ : IsMultigraph W₀)
    (hmin : 0 < minCut W₀) (x₀ : Fin n) :
    (Finset.univ.filter fun C : Finset (Fin n) =>
      x₀ ∉ C ∧ cutWeight W₀ C = minCut W₀).card ≤ n.choose 2 := by
  set F := Finset.univ.filter fun C : Finset (Fin n) => x₀ ∉ C ∧ cutWeight W₀ C = minCut W₀
  have hnt : ∀ C ∈ F, IsNonTrivialCut C := by
    intro C hC
    obtain ⟨-, hx₀, hcw⟩ := Finset.mem_filter.mp hC
    refine ⟨Finset.nonempty_iff_ne_empty.mpr fun h => ?_, fun h => hx₀ (h ▸ Finset.mem_univ x₀)⟩
    have h0 : cutWeight W₀ ∅ = 0 := by simp [cutWeight]
    rw [h, h0] at hcw
    omega
  rcases F.eq_empty_or_nonempty with hF | ⟨C₁, hC₁⟩
  · rw [hF, Finset.card_empty]
    exact Nat.zero_le _
  have hn : 2 ≤ n := by
    have := (isNonTrivialCut_iff_card C₁).mp (hnt C₁ hC₁)
    rw [Fintype.card_fin] at this
    omega
  have hpair : ∀ C ∈ F, (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) ≤
      cutLaw W₀ C + cutLaw W₀ (Finset.univ \ C) := by
    intro C hC
    have hx₀ := (Finset.mem_filter.mp hC).2.1
    have hne : C ≠ Finset.univ \ C := fun h =>
      hx₀ (h ▸ Finset.mem_sdiff.mpr ⟨Finset.mem_univ x₀, hx₀⟩)
    have h := two_div_le_cutLaw hW₀ hmin (hnt C hC) (Finset.mem_filter.mp hC).2.2
    rwa [← Finset.coe_pair, PMF.toOuterMeasure_apply_finset, Finset.sum_pair hne] at h
  have hdisj : Disjoint F (F.image (Finset.univ \ ·)) := by
    rw [Finset.disjoint_left]
    intro C hC hC'
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC'
    exact (Finset.mem_filter.mp hC).2.1
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hD).2.1⟩)
  have hinj : Set.InjOn (Finset.univ \ ·) (F : Set (Finset (Fin n))) := by
    intro D₁ _ D₂ _ h
    have := congrArg (Finset.univ \ ·) h
    simpa using this
  have hsum : ∑ C ∈ F, (cutLaw W₀ C + cutLaw W₀ (Finset.univ \ C)) ≤ 1 := by
    rw [Finset.sum_add_distrib, ← Finset.sum_image (f := fun C => cutLaw W₀ C) hinj,
      ← Finset.sum_union hdisj]
    calc ∑ C ∈ F ∪ F.image (Finset.univ \ ·), cutLaw W₀ C ≤ ∑' C, cutLaw W₀ C :=
          sum_le_tsum _
      _ = 1 := PMF.tsum_coe _
  have hle : (F.card : ℝ≥0∞) * ((2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) ≤ 1 := by
    calc (F.card : ℝ≥0∞) * ((2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞))
        = ∑ _C ∈ F, (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ C ∈ F, (cutLaw W₀ C + cutLaw W₀ (Finset.univ \ C)) := Finset.sum_le_sum hpair
      _ ≤ 1 := hsum
  have hpos : ((n * (n - 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (by omega) (by omega)).ne'
  rw [← mul_div_assoc, ENNReal.div_le_iff hpos (ENNReal.natCast_ne_top _), one_mul] at hle
  have hnat : F.card * 2 ≤ n * (n - 1) := by exact_mod_cast hle
  rw [Nat.choose_two_right]
  exact (Nat.le_div_iff_mul_le (by norm_num)).mpr hnat

end Cslib.Algorithms.Lean.Karger

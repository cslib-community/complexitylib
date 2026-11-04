/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.PolynomialAtomRows.Relative
public import Complexity.Foundations.Analysis.RowCompression.FalseOverflow
import Complexity.Foundations.Analysis.RowCompression.PreloadedIteration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial row comparison after the actual first overflow

The local relative-stability estimate is applied at the actual first overflow in group `j`.
Its initial state is the already-added input of group `j`, with a zero first local increment.
The error hypotheses therefore concern precisely the raw group inputs from `j` onward. No
error bound for the preceding global prefix is required. The local adjacent-prefix budget is
bounded by four times the `28`-weighted tail sum, without a horizon factor.

The reference is the constructed stationary continuation: it has the true row plus the
actual pre-overflow compression loss, the actual default at group `j`, the remaining real
capacities and floors, and zero further increments. A separate corollary adds the proved
weighted preloss comparison to the true output. Its tail coefficient depends only on the
chosen row function and support scale; its preloss coefficient may also depend on the
compression scale.

These are the relative-stability and weighted-preloss portions of
[OpenAI2026LogSpace, Section 8.3] for the concrete polynomial fourth-root family. Normalized
main atoms, the full estimator's recursive moment bound, and machine-space certificates are
separate obligations.

## Main results

* `Cslib.PolynomialAtomRow.exists_firstOverflow_root_bound`: actual-to-reference root error
  is bounded using only the actual raw input errors at and after the first overflow.
* `Cslib.PolynomialAtomRow.exists_firstOverflow_truth_root_bound`: actual-to-truth comparison
  combines that tail estimate with the weighted preloss sum.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.3, Lemmas 8.2--8.3, specialized to the polynomial fourth-root family
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.PolynomialAtomRow

open Finset RowCompression

variable (kind : PolynomialAtomRow) {θ : ℝ}

/-- **Relative stability from the actual first overflow.** The coefficient depends only on
the concrete function and `θ`. All error hypotheses are confined to groups `j ≤ i < m`; in
particular the raw prefix before adding group `j` needs no error estimate. -/
theorem exists_firstOverflow_root_bound (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} (s : Finset ι) (n : ℕ → ℕ)
      (Δ : ℕ → ι → Fin 2 → ℝ) (a : State ι) (truth : ι → Fin 2 → ℝ) (η : ℝ) (K : ℕ),
      0 < η → η ≤ θ / 10000 → 0 < K → a.defaultValue = 0 →
      ∀ (m j : ℕ), j < m →
      IsFirstOverflow s n (fun _ => K) (dyadicFloor η m) Δ a j →
      (∀ y ∈ s, 0 ≤ truth y 0) → (∀ y ∈ s, |truth y 1| ≤ η / 2) →
      (∀ i, j ≤ i → i < m → K ≤ n i) →
      ∀ (ε : ℕ → ℝ), (∀ i, j ≤ i → i < m → 0 ≤ ε i) →
      (∀ i, j ≤ i → i < m → ∀ y ∈ s,
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ a.row (i + 1) y) ≤ ε i) →
      ∀ y ∈ s,
      |kind.stateRootError θ s K (iterate s n (fun _ => K) (dyadicFloor η m) Δ a m)
        (stationaryContinuation s n K (dyadicFloor η m) Δ a truth j (m - j)) y| ≤
        C * ∑ i ∈ Ico j m, 28 ^ (m - i) * ε i := by
  obtain ⟨C, hC, hbound⟩ := kind.exists_iterate_root_bound hθ
  refine ⟨4 * C, by positivity, ?_⟩
  intro ι s n Δ a truth η K hη hmargin hK ha m j hj hover hfirst hsecond hn ε hε herr y hy
  let ρ := dyadicFloor η m
  let run := iterate s n (fun _ => K) ρ Δ a
  let raw₀ := uncompressedRow Δ a.row (j + 1)
  let loss := fun y ν => (run j).row y ν - uncompressedRow Δ a.row j y ν
  let z := (run j).defaultValue
  have hr : 0 < m - j := Nat.sub_pos_of_lt hj
  have hjr : j + (m - j) = m := Nat.add_sub_of_le hj.le
  have hz : z ≤ η := stationaryState_defaultValue_le_dyadic (truth := truth) hη.le
    (by rw [ha]) (by rw [ha]; linarith) m j hj.le hover.1
  have hloss (y : ι) (_hy : y ∈ s) (ν : Fin 2) : |loss y ν| ≤ η / 2 := by
    have h := abs_stationaryState_row_sub_le_dyadic (truth := truth) hη.le m j hj.le
      hover.1 y ν
    rw [stationaryState_row_sub] at h
    change |loss y ν| ≤ η / 100 at h
    linarith
  have hlocalε (i : ℕ) (hi : i ≤ m - j) : 0 ≤ preloadedError ε j i := by
    cases i with
    | zero => exact hε j (le_refl j) hj
    | succ i => exact hε (j + i) (Nat.le_add_right _ _) (by omega)
  have hlocalerr (i : ℕ) (hi : i ≤ m - j) (y : ι) (hy : y ∈ s) :
      clippedError (truth y 0) (truth y 1)
        (uncompressedRow (preloadedIncrement Δ j) raw₀ i y) ≤ preloadedError ε j i := by
    cases i with
    | zero =>
      simpa only [uncompressedRow_zero, preloadedError_zero, raw₀] using
        (herr j (le_refl j) hj y hy)
    | succ i =>
      dsimp only [raw₀]
      rw [uncompressedRow_preloadedIncrement j (Nat.succ_pos i), preloadedError_succ]
      simpa only [Nat.add_assoc] using herr (j + i) (Nat.le_add_right _ _) (by omega) y hy
  have hrow : raw₀ + loss = inputRow s n (fun _ => K) ρ Δ a j := by
    funext y ν
    dsimp only [raw₀, loss, run, inputRow, Pi.add_apply]
    rw [uncompressedRow_succ]
    ring
  have hactual : iterate s (fun i => n (j + i)) (fun _ => K) (fun i => ρ (j + i))
      (preloadedIncrement Δ j) ⟨z, raw₀ + loss⟩ (m - j) = run m := by
    rw [hrow]
    simpa only [hjr] using iterate_preloadedIncrement (s := s) (n := n) (K := fun _ => K)
      (ρ := ρ) (Δ := Δ) (a := a) j hr
  have hlocal := hbound s (fun i => n (j + i)) (fun i => ρ (j + i))
    (preloadedIncrement Δ j) truth raw₀ loss z η K hη hmargin hz hK (m - j) hr
    (fun i hi => hn (j + i) (Nat.le_add_right _ _) (by omega))
    (fun i _ => by have h := dyadicFloor_le_scale_div hη.le m (j + i); dsimp only [ρ]; linarith)
    hfirst hsecond hloss (preloadedError ε j) hlocalε hlocalerr y hy
  rw [hactual] at hlocal
  have hbudget := prefixErrorBudget_preloadedError_le j hr
    (fun i hi => hε i (mem_Ico.mp hi).1 (by have := (mem_Ico.mp hi).2; omega))
  rw [hjr] at hbudget
  calc
    _ ≤ C * prefixErrorBudget (preloadedError ε j) (m - j) := hlocal
    _ ≤ C * (4 * ∑ i ∈ Ico j m, 28 ^ (m - i) * ε i) :=
      mul_le_mul_of_nonneg_left hbudget hC
    _ = (4 * C) * ∑ i ∈ Ico j m, 28 ^ (m - i) * ε i := by ring

/-- The actual compressed output is compared with the true zero-padded row by adding the
weighted preloss estimate to the relative tail estimate. The tail coefficient is fixed before
choosing the compression scale. Before overflow only true first entries at least `η / 2`
need a clipped-error bound; after overflow the retained-row envelope is used. -/
theorem exists_firstOverflow_truth_root_bound (hθ : 0 < θ) :
    ∃ Ctail : ℝ, 0 ≤ Ctail ∧ ∀ (η : ℝ), 0 < η → η ≤ θ / 10000 →
      ∃ Cpre : ℝ, 0 ≤ Cpre ∧ ∀ {ι : Type*} (s : Finset ι) (n : ℕ → ℕ)
        (Δ : ℕ → ι → Fin 2 → ℝ) (a : State ι) (truth : ι → Fin 2 → ℝ) (K : ℕ),
        0 < K → a.defaultValue = 0 → ∀ (m j : ℕ), j < m →
        IsFirstOverflow s n (fun _ => K) (dyadicFloor η m) Δ a j →
        (∀ y ∈ s, 0 ≤ truth y 0) → (∀ y ∈ s, |truth y 1| ≤ η / 2) →
        (∀ i, j ≤ i → i < m → K ≤ n i) →
        ∀ (ε : ℕ → ℝ), (∀ i < m, 0 ≤ ε i) →
        (∀ i < j, ∀ y ∈ s, η / 2 ≤ truth y 0 →
          clippedError (truth y 0) (truth y 1) (uncompressedRow Δ a.row (i + 1) y) ≤ ε i) →
        (∀ i, j ≤ i → i < m → ∀ y ∈ s,
          clippedError (truth y 0) (truth y 1) (uncompressedRow Δ a.row (i + 1) y) ≤ ε i) →
        ∀ y ∈ s,
        |kind.stateRootError θ s K (iterate s n (fun _ => K) (dyadicFloor η m) Δ a m)
          ⟨0, truth⟩ y| ≤ Cpre * ∑ i ∈ range j, dyadicFloor η m i * ε i +
            Ctail * ∑ i ∈ Ico j m, 28 ^ (m - i) * ε i := by
  obtain ⟨Ctail, hCtail, htail⟩ := kind.exists_firstOverflow_root_bound hθ
  refine ⟨Ctail, hCtail, ?_⟩
  intro η hη hmargin
  obtain ⟨Cpre, hCpre, hpre⟩ := kind.exists_stationaryContinuation_root_bound hθ hη hmargin
  refine ⟨Cpre, hCpre, ?_⟩
  intro ι s n Δ a truth K hK ha m j hj hover hfirst hsecond hn ε hε herrpre herrtail y hy
  let c := stationaryContinuation s n K (dyadicFloor η m) Δ a truth j (m - j)
  have hrelative := htail s n Δ a truth η K hη hmargin hK ha m j hj hover
    hfirst hsecond hn ε (fun i _ hi => hε i hi) herrtail y hy
  have hreference := hpre s n Δ a truth K hK (by rw [ha]) (by rw [ha]; linarith)
    m j (m - j) (by omega) hover.1 hfirst hsecond hn ε
    (fun i hi => hε i (hi.trans hj)) herrpre y hy
  change |kind.stateRootError θ s K c ⟨0, truth⟩ y| ≤ _ at hreference
  calc
    _ ≤ |kind.stateRootError θ s K (iterate s n (fun _ => K) (dyadicFloor η m) Δ a m) c y| +
        |kind.stateRootError θ s K c ⟨0, truth⟩ y| := abs_sub_le _ _ _
    _ ≤ Ctail * ∑ i ∈ Ico j m, 28 ^ (m - i) * ε i +
        Cpre * ∑ i ∈ range j, dyadicFloor η m i * ε i := add_le_add hrelative hreference
    _ = _ := add_comm _ _

end Cslib.PolynomialAtomRow

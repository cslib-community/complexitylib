/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

import Complexity.Probability.PairwiseIndependentHash.ProductValidatedWords
import Complexity.Probability.PairwiseIndependentHash.SliceFourthMoment

/-!
# Multi-component product validated walk words tests

Concrete alphabet cardinalities, step wraps, and ambient permutations on a two-channel (`𝔽₅`, `𝔽₇`)
plus torus (`(ZMod 8) ^ 3`) environment, together with `L²` and `L⁴` concentration clients for the
explicit length-`t` validated-word estimator without passing retained identifiers across walk steps.
-/

namespace ComplexityTests.ProductValidatedWords

open Cslib Cslib.Probability Cslib.RotationMap Finset
open scoped BigOperators

/-- Explicit bounded alphabet sizes at `H = 3, J = 2`: `7 ^ 3 = 343` wrap vectors per step and
`4 * (2 + 1) * 3 ^ 2 = 108` lazy product edge labels per step. -/
example : #(affineWrapBox 3) = 343 ∧ Fintype.card (ComponentLazyStep 3 2) = 108 := by
  rw [card_affineWrapBox, card_componentLazyStep]
  decide

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

instance (j : Fin 2) : Fact (![5, 7] j).Prime := by
  fin_cases j
  exacts [⟨Nat.prime_five⟩, ⟨by decide⟩]

instance (j : Fin 2) : NeZero (![3, 4] j) := by
  fin_cases j
  exacts [⟨by norm_num⟩, ⟨by norm_num⟩]

/-- Channel `0` (`𝔽₅`, box `{0, 1, 2} ^ 3`): constant `(0, 2, 1)` and basis frame `(1, 0, 0)`. -/
def sampleChan0 : FrameChannel 5 3 1 :=
  (![0, 2, 1], Frame.equivNeZero.symm ⟨![1, 0, 0], by decide⟩)

/-- Channel `1` (`𝔽₇`, box `{0, 1, 2, 3} ^ 3`): constant `(3, 0, 1)` and basis frame `(1, 0, 0)`. -/
def sampleChan1 : FrameChannel 7 3 1 :=
  (![3, 0, 1], Frame.equivNeZero.symm ⟨![1, 0, 0], by decide⟩)

/-- Sample ambient environment in `ComponentSpace 3 8 ![5, 7]` with torus vector `(4, 7, 1)`. -/
def sampleEnv : ComponentSpace 3 8 ![5, 7] :=
  (fun
    | ⟨0, _⟩ => sampleChan0
    | ⟨1, _⟩ => sampleChan1,
   ![4, 7, 1])

/-- Sample retained identifiers `y = (0, 0)` on the two channels. -/
def sampleIds : ∀ j : Fin 2, ZMod (![5, 7] j) := fun _ ↦ 0

/-- An inverse translation along coordinate `0` in channel `0` sends `(0, 2, 1)` to `(-1, 2, 1)`,
so the unique valid step wrap is `![1, 0, 0] ∈ affineWrapBox 3`. -/
def chan0InvTrans0 : ComponentLazyStep 3 2 := .inl (.inl ⟨0, .inr 0⟩, true)

example : componentStepWrap ![3, 4] sampleIds chan0InvTrans0 sampleEnv = ![1, 0, 0] ∧
    IsValidComponentStep ![3, 4] sampleIds chan0InvTrans0 ![1, 0, 0] sampleEnv := by
  decide

/-- Torus moves and lazy self-loops require wrap vector `0`, shifting only the torus or acting as
the identity respectively. -/
def torusTrans0 : ComponentLazyStep 3 2 := .inl (.inr (.inr 0), false)
def lazyLoop0 : ComponentLazyStep 3 2 := .inr (.inr (.inr 0), false)

example :
    componentStepWrap ![3, 4] sampleIds torusTrans0 sampleEnv = 0 ∧
      (componentStepPerm ![3, 4] torusTrans0 0 sampleEnv).2 = ![5, 7, 1] ∧
      componentStepPerm ![3, 4] lazyLoop0 0 sampleEnv = sampleEnv := by
  decide

/-- **Uniform-measure invariance and unique wrap word** on `ComponentSpace 3 8 ![5, 7]`. -/
example {t : ℕ} (w : Fin t → ComponentLazyStep 3 2) (z : Fin t → Fin 3 → ℤ)
    (g : ComponentSpace 3 8 ![5, 7] → ℝ) :
    (𝔼 A, g (componentWordPerm ![3, 4] w z A) = 𝔼 A, g A) ∧
      ∀ A : ComponentSpace 3 8 ![5, 7],
        ∃! z' : Fin t → Fin 3 → ℤ, IsValidComponentWord ![3, 4] sampleIds w z' A :=
  ⟨expect_componentWordPerm ![3, 4] w z g, existsUnique_isValidComponentWord sampleIds w⟩

/-- **`L²` concentration of the multi-component validated-word estimator**: for all `H ≥ 3`, `J`
channels with `1 ≤ L j ≤ P j`, free bits in `(ZMod M) ^ H`, retained identifiers `y`, and observable
`f : ComponentSpace H M P → ℝ`, the length-`t` validated-word estimator has conditional variance at
most `(1 - 1 / (155648 (J + 1) H ^ 4)) ^ (2 t)` times the conditional variance of `f`. -/
theorem variance_validatedWord_estimator_le {H M J : ℕ} {P L : Fin J → ℕ}
    [∀ j, Fact (P j).Prime] [∀ j, NeZero (L j)] [NeZero M]
    (hH : 3 ≤ H) (hL : ∀ j, L j ≤ P j) (y : ∀ j, ZMod (P j))
    (f : ComponentSpace H M P → ℝ) (t : ℕ) :
    𝔼 A : ComponentSlice H M P L y,
        ((𝔼 w : Fin t → ComponentLazyStep H J,
            ∑ z ∈ Fintype.piFinset (fun _ : Fin t ↦ affineWrapBox H),
              if IsValidComponentWord L y w z (componentSliceVal A)
              then f (componentWordPerm L w z (componentSliceVal A)) else 0) -
          𝔼 B : ComponentSlice H M P L y, f (componentSliceVal B)) ^ 2 ≤
      (1 - 1 / (155648 * (J + 1) * H ^ 4)) ^ (2 * t) *
        𝔼 A : ComponentSlice H M P L y,
          (f (componentSliceVal A) -
            𝔼 B : ComponentSlice H M P L y, f (componentSliceVal B)) ^ 2 := by
  have h := expect_walk_pow_componentMove_sub_expect_sq_le (M := M) hH hL y
    (fun B ↦ f (componentSliceVal B)) t
  simpa only [walk_pow_componentMove_eq_expect_word hL f t] using h

/-- **Concrete `L⁴` concentration of the validated-word estimator over two channels and free bits**,
with every hypothesis discharged (`155648 * 3 * 3 ^ 4 = 37822464`). -/
example (y : ∀ j : Fin 2, ZMod (![5, 7] j)) (f : ComponentSpace 3 8 ![5, 7] → ℝ) (t : ℕ) :
    𝔼 A : ComponentSlice 3 8 ![5, 7] ![3, 4] y,
        ((𝔼 w : Fin (2 * t) → ComponentLazyStep 3 2,
            ∑ z ∈ Fintype.piFinset (fun _ : Fin (2 * t) ↦ affineWrapBox 3),
              if IsValidComponentWord ![3, 4] y w z (componentSliceVal A)
              then f (componentWordPerm ![3, 4] w z (componentSliceVal A)) else 0) -
          𝔼 B : ComponentSlice 3 8 ![5, 7] ![3, 4] y, f (componentSliceVal B)) ^ 4 ≤
      2 * (1 - 1 / 37822464) ^ (2 * t) *
        𝔼 A : ComponentSlice 3 8 ![5, 7] ![3, 4] y,
          (f (componentSliceVal A) -
            𝔼 B : ComponentSlice 3 8 ![5, 7] ![3, 4] y, f (componentSliceVal B)) ^ 4 := by
  have hL : ∀ j : Fin 2, ![3, 4] j ≤ ![5, 7] j := fun j ↦ by fin_cases j <;> decide
  have h := expect_walk_pow_componentMove_sub_expect_pow_four_le (M := 8) le_rfl hL y
    (fun B ↦ f (componentSliceVal B)) t
  simp only [walk_pow_componentMove_eq_expect_word hL f (2 * t)] at h
  norm_num at h ⊢
  exact h

end ComplexityTests.ProductValidatedWords

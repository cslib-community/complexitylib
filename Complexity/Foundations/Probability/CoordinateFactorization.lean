/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.CoordinateExpectation

/-!
# Factoring a terminal coordinate from a conditioned finite product

Split one actual product, retaining every other coordinate. A function on the remaining
coordinates may correlate arbitrarily with the source and midpoint. Only a function of
the split terminal coordinate factors. Empty source and terminal events are included.
-/
public section
open Finset
open scoped BigOperators

namespace Finset

/-- Factor a terminal-only value from a function of all other coordinates, conditioning
on an old source event and a terminal event. This never introduces a second full seed. -/
theorem expect_pi_split_mul_filter {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [Nonempty A] (s t : R) (hst : s ≠ t)
    (p q : A → Prop) [DecidablePred p] [DecidablePred q]
    (L : ({j : R // j ≠ t} → A) → ℝ) (G : A → ℝ) :
    (𝔼 σ ∈ ({σ : R → A | p (σ s) ∧ q (σ t)} : Finset _),
      L (fun j => σ j) * G (σ t)) =
    (𝔼 σ ∈ ({σ : R → A | p (σ s)} : Finset _), L (fun j => σ j)) *
      (𝔼 a ∈ ({a | q a} : Finset A), G a) := by
  classical
  let e := (Equiv.piSplitAt t (fun _ : R => A)).trans (Equiv.prodComm _ _)
  have hpair : (𝔼 σ ∈ ({σ : R → A | p (σ s) ∧ q (σ t)} : Finset _),
      L (fun j => σ j) * G (σ t)) =
      𝔼 z ∈ ({rest | p (rest ⟨s, hst⟩)} : Finset ({j : R // j ≠ t} → A)) ×ˢ
        ({a | q a} : Finset A), L z.1 * G z.2 := by
    apply expect_equiv e
    · intro σ
      simp [e]
    · intro σ _
      rfl
  have hsource : (𝔼 σ ∈ ({σ : R → A | p (σ s)} : Finset _), L (fun j => σ j)) =
      𝔼 rest ∈ ({rest | p (rest ⟨s, hst⟩)} : Finset ({j : R // j ≠ t} → A)), L rest := by
    calc
      _ = 𝔼 z ∈ ({rest | p (rest ⟨s, hst⟩)} : Finset ({j : R // j ≠ t} → A)) ×ˢ
          (univ : Finset A), L z.1 := by
        apply expect_equiv e
        · intro σ
          simp [e]
        · intro σ _
          rfl
      _ = _ := by rw [expect_product]; simp
  rw [hpair, hsource, expect_product]
  simp_rw [← mul_expect]
  rw [← expect_mul]

end Finset

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.CoordinateExpectation

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

/-- Splitting a product at `t` turns the event `p (σ s) ∧ v (σ t)` into a product of an event
on the other coordinates and an event on `t`. -/
private theorem expect_filter_eq_expect_product {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] {s t : R} (hst : s ≠ t) (p v : A → Prop) [DecidablePred p] [DecidablePred v]
    (F : (R → A) → ℝ) (f : (({j : R // j ≠ t} → A) × A) → ℝ)
    (hF : ∀ σ, F σ = f ((Equiv.piSplitAt t (fun _ : R => A)).trans (Equiv.prodComm _ _) σ)) :
    (𝔼 σ ∈ ({σ : R → A | p (σ s) ∧ v (σ t)} : Finset _), F σ) =
      𝔼 z ∈ ({rest | p (rest ⟨s, hst⟩)} : Finset ({j : R // j ≠ t} → A)) ×ˢ
        ({a | v a} : Finset A), f z :=
  expect_equiv _ (fun σ => by simp) fun σ _ => hF σ

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
  have hpair := expect_filter_eq_expect_product hst p q (fun σ => L (fun j => σ j) * G (σ t))
    (fun z => L z.1 * G z.2) fun _ => rfl
  have hsource := expect_filter_eq_expect_product hst p (fun _ => True)
    (fun σ => L (fun j => σ j)) (fun z => L z.1) fun _ => rfl
  simp only [and_true, filter_true_of_mem, mem_univ, forall_const, expect_product,
    Fintype.expect_const] at hsource
  rw [hpair, hsource, expect_product]
  simp_rw [← mul_expect]
  rw [← expect_mul]

/-- Restrict a source-conditioned full product to a terminal event containing the support.
The terminal density is the exact change of conditioning, including empty events. -/
theorem expect_pi_supported_terminal {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [Nonempty A] (s t : R) (hst : s ≠ t)
    (p q : A → Prop) [DecidablePred p] [DecidablePred q]
    (F : (R → A) → ℝ) (hF : ∀ σ, ¬ q (σ t) → F σ = 0) :
    (𝔼 σ ∈ ({σ : R → A | p (σ s) ∧ q (σ t)} : Finset _),
      (dens {a | q a} : ℝ) * F σ) =
    𝔼 σ ∈ ({σ : R → A | p (σ s)} : Finset _), F σ := by
  classical
  let e := (Equiv.piSplitAt t (fun _ : R => A)).trans (Equiv.prodComm _ _)
  have split (v : A → Prop) [DecidablePred v] :=
    expect_filter_eq_expect_product hst p v F (fun z => F (e.symm z))
      fun σ => (congrArg F (e.symm_apply_apply σ)).symm
  rw [← mul_expect, split q, expect_product]
  have hs := split (fun _ => True)
  simp only [and_true, filter_true_of_mem, mem_univ, forall_const] at hs
  rw [hs, expect_product, mul_expect]
  apply expect_congr rfl
  intro rest _
  symm
  have hz (a : A) : F (e.symm (rest, a)) =
      if a ∈ ({a | q a} : Finset A) then F (e.symm (rest, a)) else 0 := by
    split_ifs with ha
    · rfl
    · exact hF _ (by simpa [e] using ha)
  calc
    _ = 𝔼 a, if a ∈ ({a | q a} : Finset A) then F (e.symm (rest, a)) else 0 :=
      expect_congr rfl (fun a _ => hz a)
    _ = _ := by simpa only [NNRat.smul_def] using
      (Fintype.expect_ite_mem {a | q a} (fun a => F (e.symm (rest, a))))

end Finset

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.Abel

/-!
# Finite factorization through shared summaries

This is the finite-sum identity underlying Lemma 3.2 (pp. 22–23) of [OpenAI2026ETH],
*The Exponential Time Hypothesis is False*, manuscript revised October 25, 2026,
source `openai/math@7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`.

A factor may depend on all coordinates, provided that inside a fixed measurement fiber it
depends only on its own coordinate. We enumerate a supplied finite measurement box, including
unrealizable tuples. Representatives come from unrestricted fibers, not from the local
restrictions. Empty restricted fibers contribute zero; unrealizable tuples also contribute zero.

These are mathematical finite sums. A representative-selection function is explicit data, not
an efficient oracle or a machine certificate. The kernel-shift lemma supplies the rational
locality implication. Integer box bounds and
scan/runtime analysis remain separate obligations.

## Main definitions

* `Cslib.SharedSummaries.fiberContribution`: a product of restricted local sums, or zero for an
  unrealizable measurement tuple.

## Main results

* `Cslib.SharedSummaries.fiberContribution_eq`: the contribution is independent of valid
  unrestricted representatives.
* `Cslib.SharedSummaries.sum_prod_eq_sum_measurement_fibers`: factorization over the full
  supplied finite measurement box.
* `Cslib.SharedSummaries.fiber_locality_of_kernel_shifts`: the paper’s rational-kernel
  invariance implies fiber locality.
-/

public section

namespace Cslib.SharedSummaries

open Finset
open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]
  {X Y : G → Type*} [∀ g, Fintype (X g)] [∀ g, DecidableEq (Y g)]
  {A : Type*} [CommRing A]

/-- The contribution at `y`, using representatives of its unrestricted measurement fibers.
The selector need not respect `allowed`. No selector is invoked for an unrealizable tuple. -/
@[expose] noncomputable def fiberContribution
    (measure : ∀ g, X g → Y g) (allowed : ∀ g, Finset (X g))
    (factor : G → (∀ g, X g) → A)
    (representative : ∀ y : (∀ g, Y g), (∀ g, ∃ u, measure g u = y g) → ∀ g, X g)
    (y : ∀ g, Y g) : A := by
  classical
  exact if hy : ∀ g, ∃ u, measure g u = y g then
    ∏ g, ∑ u ∈ (allowed g).filter (fun u => measure g u = y g),
      factor g (Function.update (representative y hy) g u)
  else 0

/-- On a fixed fiber, changing the unrestricted representatives does not change the contribution.
Only the full measurement tuple and the local coordinate may affect a factor. -/
theorem fiberContribution_eq
    (measure : ∀ g, X g → Y g) (allowed : ∀ g, Finset (X g))
    (factor : G → (∀ g, X g) → A)
    (locality : ∀ g x x', (∀ h, measure h (x h) = measure h (x' h)) →
      x g = x' g → factor g x = factor g x')
    (representative representative' :
      ∀ y : (∀ g, Y g), (∀ g, ∃ u, measure g u = y g) → ∀ g, X g)
    (valid : ∀ y hy g, measure g (representative y hy g) = y g)
    (valid' : ∀ y hy g, measure g (representative' y hy g) = y g)
    (y : ∀ g, Y g) :
    fiberContribution measure allowed factor representative y =
      fiberContribution measure allowed factor representative' y := by
  classical
  unfold fiberContribution
  split_ifs with hy
  · apply Finset.prod_congr rfl
    intro g _
    apply Finset.sum_congr rfl
    intro u hu
    apply locality
    · intro h
      by_cases hh : h = g
      · subst h
        simp
      · simp only [Function.update_of_ne hh]
        rw [valid, valid']
    · simp
  · rfl

/-- Finite shared-summary factorization. Every measurement tuple in the supplied box is
examined, including tuples with an empty unrestricted fiber. Local restrictions are imposed
only inside the sums; representatives need not satisfy them. -/
theorem sum_prod_eq_sum_measurement_fibers
    (measure : ∀ g, X g → Y g) (box : ∀ g, Finset (Y g))
    (covers : ∀ g u, measure g u ∈ box g)
    (allowed : ∀ g, Finset (X g)) (factor : G → (∀ g, X g) → A)
    (locality : ∀ g x x', (∀ h, measure h (x h) = measure h (x' h)) →
      x g = x' g → factor g x = factor g x')
    (representative : ∀ y : (∀ g, Y g), (∀ g, ∃ u, measure g u = y g) → ∀ g, X g)
    (valid : ∀ y hy g, measure g (representative y hy g) = y g) :
    (∑ x ∈ Fintype.piFinset allowed, ∏ g, factor g x) =
      ∑ y ∈ Fintype.piFinset box,
        fiberContribution measure allowed factor representative y := by
  classical
  let measurements : (∀ g, X g) → (∀ g, Y g) := fun x g => measure g (x g)
  have hcover : ∀ x ∈ Fintype.piFinset allowed,
      measurements x ∈ Fintype.piFinset box := by
    intro x _
    exact Fintype.mem_piFinset.mpr fun g => covers g (x g)
  rw [← Finset.sum_fiberwise_of_maps_to hcover (fun x => ∏ g, factor g x)]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : ∀ g, ∃ u, measure g u = y g
  · simp only [fiberContribution, dite_eq_left hy]
    let localChoices : ∀ g, Finset (X g) := fun g => (allowed g).filter (fun u => measure g u = y g)
    have hfiber : ((Fintype.piFinset allowed).filter fun x => measurements x = y) =
        Fintype.piFinset localChoices := by
      ext x
      simp only [Finset.mem_filter, Fintype.mem_piFinset, localChoices, measurements,
        funext_iff, forall_and]
    rw [hfiber, Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.prod_congr rfl
    intro g _
    apply locality
    · intro h
      have hxh := (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hx h)).2
      by_cases hh : h = g
      · subst h
        simp
      · simp only [Function.update_of_ne hh]
        rw [hxh, valid]
    · simp
  · have hempty : ((Fintype.piFinset allowed).filter fun x => measurements x = y) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxy := (Finset.mem_filter.mp hx).2
      exact hy fun g => ⟨x g, congrFun hxy g⟩
    simp only [hempty, Finset.sum_empty, fiberContribution, dite_eq_right hy]

omit [CommRing A] [Fintype G] in
/-- Kernel-shift invariance implies fiber locality. Each change in another group is extended
by zero to the full tuple. This is the rational linear-summary hypothesis of Lemma 3.2;
no rank, representative-selection or runtime assumption is needed. -/
theorem fiber_locality_of_kernel_shifts [Finite G]
    {V W : G → Type*} [∀ g, AddCommGroup (V g)] [∀ g, Module ℚ (V g)]
    [∀ g, AddCommGroup (W g)] [∀ g, Module ℚ (W g)]
    (measure : ∀ g, V g →ₗ[ℚ] W g) (factor : G → (∀ g, V g) → A)
    (shift : ∀ g h, h ≠ g → ∀ x delta, measure h delta = 0 →
      factor g (x + Pi.single h delta) = factor g x)
    (g : G) (x x' : ∀ h, V h)
    (sameMeasurements : ∀ h, measure h (x h) = measure h (x' h))
    (sameCoordinate : x g = x' g) : factor g x = factor g x' := by
  classical
  let _ := Fintype.ofFinite G
  let delta := x' - x
  have hdelta (h : G) : measure h (delta h) = 0 := by
    dsimp [delta]
    rw [map_sub, sameMeasurements h, sub_self]
  have hzero : delta g = 0 := by simp [delta, sameCoordinate]
  have hsum (s : Finset G) : ∀ base : (∀ h, V h),
      factor g (base + ∑ h ∈ s, Pi.single h (delta h)) = factor g base := by
    induction s using Finset.induction_on with
    | empty => intro base; simp
    | @insert h s hs ih =>
      intro base
      rw [Finset.sum_insert hs]
      have hrearrange : base + (Pi.single h (delta h) + ∑ j ∈ s, Pi.single j (delta j)) =
          (base + ∑ j ∈ s, Pi.single j (delta j)) + Pi.single h (delta h) := by abel
      rw [hrearrange]
      by_cases hh : h = g
      · subst h
        simpa only [hzero, Pi.single_zero, add_zero] using ih base
      · rw [shift g h hh _ _ (hdelta h), ih]
  have hdecompose : (∑ h : G, Pi.single h (delta h)) = delta := by
    funext h
    simp
  have hfinish : x + delta = x' := by dsimp [delta]; abel
  have h := hsum Finset.univ x
  rw [hdecompose, hfinish] at h
  exact h.symm

end Cslib.SharedSummaries

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.PMF.Filter
import Complexity.Probability.Product.Split
import Complexity.Probability.StatisticalDistance.Event

/-! # Conditioning, splitting and relabeling discrete distributions

Conditioning two independent fair bits on the first being `true` leaves the second bit uniform,
and conditioning them on both being `true` gives the point mass at `(true, true)`. Splitting off
the first of two independent fair bits leaves the other one an independent fair bit. Relabeling two
point masses injectively keeps them at distance one.
-/

namespace ComplexityTests.PMFConditioning

open Cslib.Probability.PMF
open scoped Cslib.Probability.PMF

/-- Two independent fair bits. -/
noncomputable abbrev twoBits : PMF (Bool × Bool) :=
  (uniformOfFintype Bool).bind fun a => (uniformOfFintype Bool).map (a, ·)

theorem true_mem : ∃ b ∈ ({true} : Set Bool), b ∈ (uniformOfFintype Bool).support :=
  ⟨true, rfl, by simp⟩

-- Conditioning on the first bit leaves the second bit uniform.
example (h : ∃ z ∈ ({true} : Set Bool) ×ˢ (Set.univ : Set Bool), z ∈ twoBits.support) :
    (twoBits.filter (({true} : Set Bool) ×ˢ Set.univ) h).map Prod.snd = uniformOfFintype Bool := by
  rw [map_snd_filter_bind_pair_prod _ _ _ _ _ ⟨true, trivial, by simp⟩,
    filter_eq_self_of_support_subset _ _ _ (Set.subset_univ _)]

-- Conditioning on both bits being `true` gives the point mass at `(true, true)`.
example (h : ∃ z ∈ ({true} : Set Bool) ×ˢ ({true} : Set Bool), z ∈ twoBits.support) :
    twoBits.filter (({true} : Set Bool) ×ˢ {true}) h = PMF.pure (true, true) := by
  have hpure : (uniformOfFintype Bool).filter {true} true_mem = PMF.pure true := by
    ext b
    cases b <;> simp [PMF.filter_apply, Set.indicator, uniformOfFintype_apply,
      ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
  rw [filter_bind_pair_prod _ _ _ _ h true_mem true_mem, hpure, PMF.pure_bind,
    PMF.pure_map]

-- Injective relabeling keeps two distinct point masses at distance one.
example : dist ((PMF.pure true).map some) ((PMF.pure false).map some) = 1 := by
  rw [dist_map_of_injective _ _ (Option.some_injective Bool)]
  exact dist_eq_one_of_disjoint_support (by simp)

-- Splitting off the first of two independent fair bits leaves the other one a fair bit.
example : ((pi fun _ : Fin 2 => uniformOfFintype Bool).map
      (Equiv.piEquivPiSubtypeProd (· = (0 : Fin 2)) _)).map Prod.snd =
    pi fun _ : {i : Fin 2 // ¬i = 0} => uniformOfFintype Bool := by
  have hk : ∀ a : {i : Fin 2 // i = 0} → Bool,
      ((pi fun _ : {i : Fin 2 // ¬i = 0} => uniformOfFintype Bool).map (a, ·)).map Prod.snd =
        pi fun _ : {i : Fin 2 // ¬i = 0} => uniformOfFintype Bool := fun a =>
    (PMF.map_comp _ _ _).trans (PMF.map_id _)
  rw [pi_map_piEquivPiSubtypeProd, PMF.map_bind]
  simp only [hk, PMF.bind_const]

end ComplexityTests.PMFConditioning

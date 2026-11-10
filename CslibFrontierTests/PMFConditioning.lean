/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Probability.PMF.Coin
import CslibFrontier.Probability.PMF.Filter
import CslibFrontier.Probability.Product.Event
import CslibFrontier.Probability.Product.Split
import CslibFrontier.Probability.StatisticalDistance.Event

/-! # Conditioning, splitting and relabeling discrete distributions

Conditioning two independent fair bits on the first being `true` leaves the second bit uniform,
and conditioning them on both being `true` gives the point mass at `(true, true)`. Splitting off
the first of two independent fair bits leaves the other one an independent fair bit. Relabeling two
point masses injectively keeps them at distance one. Restricting independent coins of different
biases, reading them along an injection or currying them keeps them independent, three coins of
bias `p` all show `true` with probability `p³`, and a coin of bias `1/2` is fair.
-/

namespace CslibFrontierTests.PMFConditioning

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

-- Restricting independent coins to the coordinates other than `0` keeps the other coins.
example (q : Fin 3 → unitInterval) :
    (pi fun i => coin (q i)).map (fun a (i : {i : Fin 3 // i ≠ 0}) => a i) =
      pi fun i : {i : Fin 3 // i ≠ 0} => coin (q i) :=
  pi_map_restrict _ _

-- Reading three independent coins along the injection `Fin.succ` keeps the last two coins.
example (q : Fin 3 → unitInterval) :
    (pi fun i => coin (q i)).map (fun a (k : Fin 2) => a k.succ) = pi fun k => coin (q k.succ) :=
  pi_map_comp_injective _ (Fin.succ_injective 2)

-- Currying independent coins indexed by pairs gives independent blocks of coins.
example (q : Fin 2 × Fin 3 → unitInterval) :
    (pi fun ik => coin (q ik)).map Function.curry = pi fun i => pi fun k => coin (q (i, k)) :=
  pi_map_curry _

-- Three independent coins of bias `p` all show `true` with probability `p³`.
example (p : unitInterval) :
    (pi fun _ : Fin 3 => coin p).toOuterMeasure {u | ∀ i, u i ∈ ({true} : Set Bool)} =
      ENNReal.ofReal p ^ 3 := by
  rw [toOuterMeasure_pi_forall]
  simp [coin_apply]

-- A coin of bias `1/2` is fair.
example : coin ⟨1 / 2, by norm_num, by norm_num⟩ = uniformOfFintype Bool :=
  coin_eq_uniformOfFintype rfl

end CslibFrontierTests.PMFConditioning

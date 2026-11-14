/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
import CslibFrontier.Foundations.Combinatorics.Expander.VisitCount

set_option linter.privateModule false
open Cslib Finset
open scoped BigOperators

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  [DecidableEq V] (G : RotationMap V D) (W : Finset V)

-- Nonconsecutive selected times, excluding the initial vertex.
example : (dens {p : V × (Fin 4 → D) |
    ∀ i ∈ ({1, 3} : Finset ℕ), G.walkAt p i ∈ W} : ℝ) ≤
    ((dens W : ℝ) + G.spectralExpansion ^ 2) ^ ((2 : ℝ) / 2) := by
  simpa using G.dens_filter_selected_walkAt_mem_le W 4 {1, 3} (by decide)

example (t : ℕ) : (dens {p : V × (Fin t → D) |
    ∀ i ∈ (∅ : Finset ℕ), G.walkAt p i ∈ W} : ℝ) ≤ 1 := by
  simpa only [card_empty, Nat.cast_zero, zero_div, Real.rpow_zero] using
    G.dens_filter_selected_walkAt_mem_le W t ∅ (empty_subset _)

example {t : ℕ} (p : V × (Fin t → D)) : G.visitCount ∅ p = 0 := by
  simp

example {t : ℕ} (p : V × (Fin t → D)) : G.visitCount univ p = t + 1 := by
  simp

example (p : V × (Fin 0 → D)) : G.visitCount W p = if p.1 ∈ W then 1 else 0 := by
  exact G.visitCount_zero W p

-- Impossible threshold and m=0 both instantiate the same public theorem.
example (t : ℕ) : (dens {p : V × (Fin t → D) |
    t + 2 ≤ G.visitCount W p} : ℝ) ≤ 0 := by
  simpa using G.dens_filter_visitCount_ge_le W t (t + 2)

example (t : ℕ) : (dens {p : V × (Fin t → D) |
    0 ≤ G.visitCount W p} : ℝ) ≤ 1 := by
  simpa only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, zero_div,
    Real.rpow_zero, one_mul] using G.dens_filter_visitCount_ge_le W t 0

-- Majority bad samples application: no sampler construction or runtime is assumed.
example (n : ℕ) (h : G.spectralExpansion < Real.sqrt (dens W : ℝ)) :
    (dens {p : V × (Fin (2 * n) → D) | n < G.visitCount W p} : ℝ) <
      (32 * (dens W : ℝ)) ^ (((2 * n + 1 : ℕ) : ℝ) / 4) := by
  have heq : (2 * n + 1) / 2 = n := by omega
  simpa only [heq] using G.dens_filter_visitCount_half_lt W (2 * n) h

example (n : ℕ) (h : G.spectralExpansion < Real.sqrt (dens W : ℝ)) :
    (dens {p : V × (Fin (2 * n + 1) → D) | n + 1 < G.visitCount W p} : ℝ) <
      (32 * (dens W : ℝ)) ^ (((2 * n + 2 : ℕ) : ℝ) / 4) := by
  simpa [Nat.add_assoc] using G.dens_filter_visitCount_half_lt W (2 * n + 1) h

private def completeTwo : RotationMap (Fin 2) (Fin 2) where
  rot := Prod.swap
  rot_involutive := Prod.swap_swap

-- An actual computed count: vertices 0,1,0,1.
example : completeTwo.visitCount {1} (0, ![1, 0, 1]) = 2 := by decide +kernel

-- Source parameter transport, preserving the explicit lambda/d convention.
example (t : ℕ) (lambda d : ℝ) (h : G.spectralExpansion ≤ lambda / d) :
    (dens {p : V × (Fin t → D) | ∀ i ∈ ({0} : Finset ℕ), G.walkAt p i ∈ W} : ℝ) ≤
      ((dens W : ℝ) + (lambda / d) ^ 2) ^ ((1 : ℝ) / 2) := by
  simpa only [card_singleton, Nat.cast_one] using
    G.dens_filter_selected_walkAt_mem_le_of_spectralExpansion_le W t {0}
      (by simp) lambda d h

example (h : G.spectralExpansion < Real.sqrt (dens W : ℝ)) :
    (dens {p : V × (Fin 0 → D) | 0 < G.visitCount W p} : ℝ) <
      (32 * (dens W : ℝ)) ^ ((1 : ℝ) / 4) := by
  simpa only [Nat.zero_add, Nat.cast_one, Nat.reduceDiv] using
    G.dens_filter_visitCount_half_lt W 0 h

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/ShannonCapacity.lean`)

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.SimpleGraph.StrongProduct
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Subadditive

/-!
# The Shannon capacity of a graph

Let `G` be the confusability graph of a noisy channel with input alphabet `V`: two letters are
adjacent when the channel can map them to the same output. A zero-error code of block length `k`
is an independent set of the strong power `G.strongPow k`, so `α(Gᵏ)^(1/k)` letters per symbol can
be sent without error. The *Shannon capacity* (zero-error capacity) of `G` is
`Θ(G) = sup_{k ≥ 1} α(Gᵏ)^(1/k)` [Shannon1956], [Lovasz1979].

Since `α(Gᵐ⁺ⁿ) ≥ α(Gᵐ) α(Gⁿ)`, the sequence `1 / α(Gᵏ)` is submultiplicative and Fekete's lemma
(Mathlib's `Submultiplicative.tendsto_lim`) shows that the supremum is also the limit
(`SimpleGraph.tendsto_shannonCapacity`); Lovász takes the limit as the definition [Lovasz1979].
We define `Θ(G)` as the supremum over `k + 1`, which gives the same value.

## Main definitions

* `SimpleGraph.shannonCapacity`: `Θ(G) = ⨆ k, α(Gᵏ⁺¹)^(1/(k+1))`.

## Main results

* `SimpleGraph.indepNum_le_shannonCapacity`: `α(G) ≤ Θ(G)`.
* `SimpleGraph.shannonCapacity_le`: `Θ(G) ≤ t` when `α(Gᵏ) ≤ tᵏ` for every `k ≥ 1`.
* `SimpleGraph.shannonCapacity_le_natCard`: `Θ(G) ≤ |V|`.
* `SimpleGraph.tendsto_shannonCapacity`: `α(Gᵏ)^(1/k) → Θ(G)` (Fekete).
-/

public section

open Filter Topology

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The **Shannon capacity** of `G`: the supremum of `α(Gᵏ)^(1/k)` over the strong powers
`Gᵏ = G.strongPow k`, `k ≥ 1`. It is also the limit of this sequence
(`SimpleGraph.tendsto_shannonCapacity`). -/
noncomputable def shannonCapacity (G : SimpleGraph V) : ℝ :=
  ⨆ k : ℕ, ((G.strongPow (k + 1)).indepNum : ℝ) ^ ((k + 1 : ℝ)⁻¹)

private theorem pow_rpow_inv_succ {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (x ^ (k + 1)) ^ ((k + 1 : ℝ)⁻¹) = x := by
  simpa using Real.pow_rpow_inv_natCast hx (Nat.succ_ne_zero k)

theorem rpow_indepNum_strongPow_le_natCard [Finite V] (k : ℕ) :
    ((G.strongPow (k + 1)).indepNum : ℝ) ^ ((k + 1 : ℝ)⁻¹) ≤ Nat.card V := by
  have h : ((G.strongPow (k + 1)).indepNum : ℝ) ≤ (Nat.card V : ℝ) ^ (k + 1) := by
    exact_mod_cast indepNum_strongPow_le (k + 1)
  calc ((G.strongPow (k + 1)).indepNum : ℝ) ^ ((k + 1 : ℝ)⁻¹)
      ≤ ((Nat.card V : ℝ) ^ (k + 1)) ^ ((k + 1 : ℝ)⁻¹) := by gcongr
    _ = Nat.card V := pow_rpow_inv_succ (Nat.cast_nonneg _) k

theorem bddAbove_range_rpow_indepNum_strongPow [Finite V] :
    BddAbove (Set.range fun k : ℕ => ((G.strongPow (k + 1)).indepNum : ℝ) ^ ((k + 1 : ℝ)⁻¹)) :=
  ⟨Nat.card V, by rintro _ ⟨k, rfl⟩; exact rpow_indepNum_strongPow_le_natCard k⟩

theorem rpow_indepNum_strongPow_le_shannonCapacity [Finite V] (k : ℕ) :
    ((G.strongPow (k + 1)).indepNum : ℝ) ^ ((k + 1 : ℝ)⁻¹) ≤ G.shannonCapacity :=
  le_ciSup bddAbove_range_rpow_indepNum_strongPow k

theorem shannonCapacity_nonneg : 0 ≤ G.shannonCapacity :=
  Real.iSup_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- The independence number is a lower bound for the Shannon capacity (codes of block length
one). -/
theorem indepNum_le_shannonCapacity [Finite V] : (G.indepNum : ℝ) ≤ G.shannonCapacity := by
  simpa [indepNum_strongPow_one] using rpow_indepNum_strongPow_le_shannonCapacity (G := G) 0

/-- To bound the Shannon capacity by `t` it suffices that `α(Gᵏ) ≤ tᵏ` for every `k ≥ 1`. -/
theorem shannonCapacity_le {t : ℝ}
    (h : ∀ k : ℕ, ((G.strongPow (k + 1)).indepNum : ℝ) ≤ t ^ (k + 1)) :
    G.shannonCapacity ≤ t := by
  have ht : 0 ≤ t := by simpa using (Nat.cast_nonneg _).trans (h 0)
  refine ciSup_le fun k => ?_
  calc ((G.strongPow (k + 1)).indepNum : ℝ) ^ ((k + 1 : ℝ)⁻¹)
      ≤ (t ^ (k + 1)) ^ ((k + 1 : ℝ)⁻¹) := by gcongr; exact h k
    _ = t := pow_rpow_inv_succ ht k

theorem shannonCapacity_le_natCard [Finite V] : G.shannonCapacity ≤ Nat.card V :=
  ciSup_le rpow_indepNum_strongPow_le_natCard

theorem shannonCapacity_eq_zero_of_isEmpty [IsEmpty V] : G.shannonCapacity = 0 :=
  le_antisymm (by simpa using G.shannonCapacity_le_natCard) shannonCapacity_nonneg

/-- **Fekete's lemma for the Shannon capacity**: `α(Gᵏ)^(1/k)` converges to `Θ(G)`. -/
theorem tendsto_shannonCapacity [Finite V] :
    Tendsto (fun k : ℕ => ((G.strongPow (k + 1)).indepNum : ℝ) ^ ((k + 1 : ℝ)⁻¹)) atTop
      (𝓝 G.shannonCapacity) := by
  rcases isEmpty_or_nonempty V with hV | hV
  · rw [shannonCapacity_eq_zero_of_isEmpty]
    refine tendsto_const_nhds.congr fun k => ?_
    have h0 : (G.strongPow (k + 1)).indepNum = 0 := by
      simpa using indepNum_strongPow_le (G := G) (k + 1)
    rw [h0, Nat.cast_zero, Real.zero_rpow (by positivity)]
  set a : ℕ → ℝ := fun n => ((G.strongPow n).indepNum : ℝ) with ha
  have hapos : ∀ n, 0 < a n := fun n => by
    simp only [ha, Nat.cast_pos]
    exact one_le_indepNum
  set u : ℕ → ℝ := fun n => (a n)⁻¹ with hu
  have hsub : Submultiplicative u := fun m n => by
    simp only [hu, ← mul_inv]
    refine inv_anti₀ (mul_pos (hapos m) (hapos n)) ?_
    simp only [ha]
    exact_mod_cast indepNum_strongPow_add m n
  have hunn : ∀ n, 0 ≤ u n := fun n => (inv_pos.2 (hapos n)).le
  have hcard : (0 : ℝ) < Nat.card V := by exact_mod_cast Nat.card_pos
  -- the limit of `u n ^ (1 / n)` is at least `1 / |V|`, hence positive
  have hlow : (Nat.card V : ℝ)⁻¹ ≤ hsub.lim := by
    change _ ≤ sInf _
    refine le_csInf (Set.nonempty_Ici.image _) ?_
    rintro _ ⟨n, hn, rfl⟩
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.1 hn
    have h1 : (Nat.card V : ℝ)⁻¹ ^ n ≤ u n := by
      simp only [hu, ha]
      rw [inv_pow]
      refine inv_anti₀ (hapos n) ?_
      exact_mod_cast indepNum_strongPow_le (G := G) n
    calc (Nat.card V : ℝ)⁻¹ = ((Nat.card V : ℝ)⁻¹ ^ n) ^ (n : ℝ)⁻¹ :=
          (Real.pow_rpow_inv_natCast (by positivity) hn0).symm
      _ ≤ u n ^ (n : ℝ)⁻¹ := by gcongr
  have hLpos : 0 < hsub.lim := lt_of_lt_of_le (by positivity) hlow
  have hT : Tendsto (fun n => a n ^ (n : ℝ)⁻¹) atTop (𝓝 hsub.lim⁻¹) := by
    refine ((hsub.tendsto_lim hunn).inv₀ hLpos.ne').congr fun n => ?_
    simp only [hu]
    rw [Real.inv_rpow (hapos n).le, inv_inv]
  have hT' : Tendsto (fun k : ℕ => a (k + 1) ^ ((k + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 hsub.lim⁻¹) :=
    (tendsto_add_atTop_iff_nat 1).2 hT
  have hS : G.shannonCapacity = hsub.lim⁻¹ := by
    refine le_antisymm (ciSup_le fun k => ?_) (le_of_tendsto' hT' fun k => ?_)
    · have h2 := inv_anti₀ hLpos (hsub.lim_le_rpow hunn (Nat.succ_ne_zero k))
      simp only [hu] at h2
      rw [Real.inv_rpow (hapos _).le, inv_inv] at h2
      simpa [ha] using h2
    · simpa [ha] using rpow_indepNum_strongPow_le_shannonCapacity (G := G) k
  rw [hS]
  simpa [ha] using hT'

end SimpleGraph

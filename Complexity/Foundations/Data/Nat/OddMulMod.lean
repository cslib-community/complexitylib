/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Finset/Card.lean`)

public import Complexity.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith

/-!
# Quotient Fiber Bound for Odd Multiples Modulo Powers of Two

For any positive multiplier `Δ > 0`, exponent `M : ℕ`, and target residue `r : ℕ`, at most `Δ`
indices `s : Fin (2 ^ (M - 1))` satisfy `(Δ * (2 * s.val + 1)) % 2 ^ M = r`. For `M ≥ 1`, every
`s : Fin (2 ^ (M - 1))` satisfies `2 * s.val + 1 < 2 ^ M`, so the Euclidean quotient
`(Δ * (2 * s.val + 1)) / 2 ^ M` lies in `Finset.range Δ` and injects on the residue fiber.

## Main results

* `Nat.card_odd_mul_mod_eq_le`:
  `((Finset.univ : Finset (Fin (2 ^ (M - 1)))).filter`
  `(fun s => (Δ * (2 * s.val + 1)) % 2 ^ M = r)).card ≤ Δ` for `0 < Δ`.
-/

@[expose] public section

namespace Nat

/-- **Quotient fiber bound for odd multiples modulo `2 ^ M`**: for any `0 < Δ`, at most `Δ`
elements `s : Fin (2 ^ (M - 1))` satisfy `(Δ * (2 * s.val + 1)) % 2 ^ M = r`. -/
theorem card_odd_mul_mod_eq_le (M Δ r : ℕ) (hΔ : 0 < Δ) :
    ((Finset.univ : Finset (Fin (2 ^ (M - 1)))).filter
      (fun s => (Δ * (2 * s.val + 1)) % (2 ^ M) = r)).card ≤ Δ := by
  cases M with
  | zero =>
    calc ((Finset.univ : Finset (Fin (2 ^ (0 - 1)))).filter
          (fun s => (Δ * (2 * s.val + 1)) % (2 ^ 0) = r)).card
        ≤ (Finset.univ : Finset (Fin 1)).card := Finset.card_filter_le _ _
      _ = 1 := by simp
      _ ≤ Δ := hΔ
  | succ m =>
    let S := (Finset.univ : Finset (Fin (2 ^ m))).filter
      (fun s => (Δ * (2 * s.val + 1)) % (2 ^ (m + 1)) = r)
    have hmaps : ∀ s ∈ S, (Δ * (2 * s.val + 1)) / (2 ^ (m + 1)) ∈ Finset.range Δ := by
      intro s _
      rw [Finset.mem_range]
      have hs : 2 * s.val + 1 < 2 ^ (m + 1) := by
        have hlt := s.isLt
        rw [Nat.pow_succ']
        omega
      exact Nat.div_lt_of_lt_mul (by nlinarith)
    have hinj : Set.InjOn (fun s : Fin (2 ^ m) => (Δ * (2 * s.val + 1)) / (2 ^ (m + 1))) S := by
      intro s₁ hs₁ s₂ hs₂ hq
      have hmod₁ : (Δ * (2 * s₁.val + 1)) % (2 ^ (m + 1)) = r :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hs₁)).2
      have hmod₂ : (Δ * (2 * s₂.val + 1)) % (2 ^ (m + 1)) = r :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hs₂)).2
      have h1 := Nat.div_add_mod (Δ * (2 * s₁.val + 1)) (2 ^ (m + 1))
      have h2 := Nat.div_add_mod (Δ * (2 * s₂.val + 1)) (2 ^ (m + 1))
      dsimp only at hq
      have hmul : Δ * (2 * s₁.val + 1) = Δ * (2 * s₂.val + 1) := by
        rw [← h1, ← h2, hq, hmod₁, hmod₂]
      have hodd : 2 * s₁.val + 1 = 2 * s₂.val + 1 := Nat.eq_of_mul_eq_mul_left hΔ hmul
      ext
      omega
    simpa [S] using Finset.card_le_card_of_injOn _ hmaps hinj

end Nat

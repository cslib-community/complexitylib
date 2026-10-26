/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Kolmogorov.MKtP
public import Complexity.Computability.Kolmogorov.MINcKT

/-!
# Tests for `MKtP`, `condUniversalTM`, and `MINcKT`

Concrete non-vacuity checks for `Complexity.Computability.Kolmogorov.MKtP`,
`Complexity.Computability.Kolmogorov.Conditional`, and
`Complexity.Computability.Kolmogorov.MINcKT`.
-/

@[expose] public section

namespace Cslib.Kolmogorov.Tests

open Cslib.Complexity Cslib.Kolmogorov Cslib.Kolmogorov.DescriptionMethod
open _root_.Turing.MultiTapeTM

/-! ### `MKtP` non-vacuity checks -/

-- Concrete yes-instance of `MKtP` from the trivial upper bound `levinKt_le_length_add`.
example (x : List Bool) :
    (x, x.length + copyOverhead + Nat.clog 2 (x.length + 1)) ∈ MKtP :=
  levinKt_le_length_add x

-- `LiuPass2021Crypto, Fact 3.1`: at least one string of length `n` has an optimal `Kt`-witness
-- running in at most `2 ^ (copyOverhead + Nat.clog 2 (n + 1) + 1)` steps when `1 ≤ n`.
example (n : ℕ) (hn : 1 ≤ n) :
    0 < {x : List Bool | x.length = n ∧
      ∃ (p : List Bool) (s : ℕ),
        x ∈ (universalTM.run p).runFor s ∧
          p.length + Nat.clog 2 s ≤ levinKtNat x ∧
            s ≤ 2 ^ (copyOverhead + Nat.clog 2 (n + 1) + 1)}.ncard := by
  have h := two_pow_lt_ncard_setOf_exists_optimal_levinKt_le_two_pow hn
  have hpow : 2 ^ (n - 1) < 2 ^ n :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-! ### `condUniversalTM` and `MINcKT` non-vacuity checks -/

-- At 0 steps, no instance belongs to `MINcKT`, and `MINcKT.check` returns `false`.
example (x y : List Bool) (s : ℕ) : (⟨x, y, 0, s⟩ : MINcKT.Instance) ∉ MINcKT := by
  simp [MINcKT.mk_mem_iff]

example (x y p : List Bool) (s : ℕ) :
    MINcKT.check (⟨x, y, 0, s⟩, p) = false := by
  simp [MINcKT.check]

-- Concrete yes-instances of `MINcKT` from self-conditioning (`exists_condTimeBoundedAt_self_le`).
example : ∃ (q : Polynomial ℕ) (c : ℕ), ∀ y : List Bool,
    (⟨y, y, q.eval (y.length + 1), c⟩ : MINcKT.Instance) ∈ MINcKT := by
  obtain ⟨q, c, _, _, hbound, _⟩ := exists_condTimeBoundedAt_self_le
  exact ⟨q, c, fun y => MINcKT.mk_mem_iff.mpr (hbound y le_rfl)⟩

-- Concrete no-instances of `MINcKT` from conditional incompressibility
-- (`exists_length_eq_forall_le_condTimeBoundedAt`).
example (y : List Bool) (n t : ℕ) (hn : 1 ≤ n) :
    ∃ x : List Bool, x.length = n ∧ (⟨x, y, t, n - 1⟩ : MINcKT.Instance) ∉ MINcKT := by
  obtain ⟨x, hx, hall⟩ := exists_length_eq_forall_le_condTimeBoundedAt y n
  refine ⟨x, hx, ?_⟩
  rw [MINcKT.mk_mem_iff]
  intro hle
  have h1 : (n : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞) := (hall t).trans hle
  have h2 : n ≤ n - 1 := ENat.natCast_le_natCast.mp h1
  omega

end Cslib.Kolmogorov.Tests

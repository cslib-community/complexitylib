/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Communication.NOF.Grolmusz

/-!
# Tests for Grolmusz's protocol

Checked instances of the telescoping chain, the upper bounds in block, arithmetic and explicit
form, the sandwich with the Babai–Nisan–Szegedy lower bound, and the one-player edge case, where
no protocol computes the generalized inner product of a single bit, so the hypothesis `k ≠ 0` of
`NOF.Grolmusz.ecomplexityFun_gip_le` cannot be dropped.
-/

open Cslib Cslib.Communication Cslib.Communication.NOF Finset BitString

namespace CommunicationNOFGrolmuszTests

/-! ### The chain -/

/-- The column `(1, 1, 1)` against the pattern `z = (0, 1)`: the two bits add up to `1`. -/
example : ∑ t, Grolmusz.chainTerm ![false, true] true ![true, true] t = true := by
  rw [Grolmusz.sum_chainTerm _ _ _ (by decide)]
  decide

/-- The column `(1, 0, 0)` against the pattern `z = (0, 1)`: the bits add up to `0`. -/
example : ∑ t, Grolmusz.chainTerm ![false, true] true ![false, false] t = false := by
  rw [Grolmusz.sum_chainTerm _ _ _ (by decide)]
  decide

/-! ### Upper bounds -/

/-- Three players with three bits each: one block of `3 < 2 ^ 2` columns, so `2 (1 + 1)` bits. -/
example : Protocol.ecomplexityFun (gip : (Fin 3 → BitString 3) → Bool) ≤ 4 :=
  Grolmusz.ecomplexityFun_gip_le_of_le_mul (B := 1) (by decide)

/-- Five players with `100` bits each: blocks of `15` columns, so `4 (100 / 15 + 2) = 32` bits,
fewer than the `101` bits of the trivial protocol. -/
example : Protocol.ecomplexityFun (gip : (Fin 5 → BitString 100) → Bool) ≤ 32 :=
  Grolmusz.ecomplexityFun_gip_le (k := 4) (by decide) 100

/-- Any partition into small blocks works, not only runs of consecutive columns: here the even and
the odd columns of `6`, for three players. -/
example : Protocol.ecomplexityFun (gip : (Fin 3 → BitString 6) → Bool) ≤ 6 :=
  Grolmusz.ecomplexityFun_gip_le_of_block (k := 2) (B := 2) (fun r => ⟨r % 2, Nat.mod_lt _ two_pos⟩)
    (by decide)

/-! ### The sandwich with the lower bound -/

/-- Grolmusz's upper bound and the Babai–Nisan–Szegedy lower bound together:
`D(GIP) ≤ k (n / (2 ^ k - 1) + 2)`, and every bound `c` on `D(GIP)` has `2 n ≤ 4 ^ (k + 1) c`. -/
example {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    2 * n ≤ 4 ^ (k + 1) * (k * (n / (2 ^ k - 1) + 2)) := by
  have h := Protocol.two_mul_le_four_pow_mul_of_ecomplexityFun_gip_le
    (Grolmusz.ecomplexityFun_gip_le hk n)
  simpa only [Fintype.card_fin] using h

/-! ### One player -/

/-- A single player sees nothing, so every protocol computes a constant. -/
theorem run_eq_of_card_one {X : Fin 1 → Type} {Z : Type} (p : Protocol X Z) (x y : ∀ i, X i) :
    p.run x = p.run y := by
  induction p with
  | output z => rfl
  | speak i send p₀ p₁ ih₀ ih₁ =>
    have hv : view i x = view i y := funext fun j => absurd (Subsingleton.elim j.1 i) j.2
    simp only [Protocol.run_speak, hv, ih₀, ih₁]

/-- No protocol computes the generalized inner product of one bit held by one player: its
communication complexity is `⊤`. -/
example : Protocol.ecomplexityFun (gip : (Fin 1 → BitString 1) → Bool) = ⊤ := by
  refine top_le_iff.mp (Protocol.le_ecomplexityFun_iff.mpr fun p hp => ?_)
  have h := run_eq_of_card_one p (fun _ _ => false) (fun _ _ => true)
  rw [hp] at h
  exact absurd h (by decide)

end CommunicationNOFGrolmuszTests

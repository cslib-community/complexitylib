/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring

/-!
# Powers of two by doubling

Doubling a counter once per element of a list multiplies it by `2 ^ length`
(`List.foldl_add_self_eq_mul_two_pow`), and the least power of two above `n`, `2 ^ Nat.size n`,
is at most `2 * n + 1` (`Nat.two_pow_size_le`). Together they bound unary counters built by
doubling once per binary digit.

## Main results

* `List.foldl_add_self_eq_mul_two_pow`: `l.foldl (fun m _ => m + m) m = m * 2 ^ l.length`.
* `Nat.two_pow_size_le`: `2 ^ Nat.size n ≤ 2 * n + 1`.
-/

public section

namespace List

/-- Doubling a counter once per element of a list multiplies it by `2 ^ length`. -/
theorem foldl_add_self_eq_mul_two_pow {α : Type*} (l : List α) (m : ℕ) :
    l.foldl (fun m _ => m + m) m = m * 2 ^ l.length := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.length_cons, pow_succ]
    ring

end List

namespace Nat

/-- `2 ^ Nat.size n` is the least power of two above `n`, so it is at most `2 * n + 1`. -/
theorem two_pow_size_le (n : ℕ) : 2 ^ n.size ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨s, hs⟩ : ∃ s, n.size = s + 1 := ⟨n.size - 1, by have := Nat.size_pos.mpr hn; omega⟩
    have : 2 ^ s ≤ n := Nat.lt_size.mp (by omega)
    rw [hs, pow_succ]
    omega

end Nat

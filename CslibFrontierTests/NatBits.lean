/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Data.Nat.Bits

/-! The binary-digit round trip and its simp attribute need only the foundational import. -/

example (n : ℕ) : n.bits.foldr Nat.bit 0 = n := Nat.foldr_bit_bits n

example (n : ℕ) : n.bits.foldr Nat.bit 0 + 7 = n + 7 := by simp

example : (0 : ℕ).bits.foldr Nat.bit 0 = 0 := by simp

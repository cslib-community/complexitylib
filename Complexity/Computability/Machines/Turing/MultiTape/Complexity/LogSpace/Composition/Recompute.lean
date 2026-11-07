/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.SmallSpace
import Mathlib.Data.Nat.Size

/-!
# Logspace functions compose

Logspace functions compose without storing the intermediate value
(`Turing.MultiTapeTM.ComputableInLogSpace.comp`): Christian Reitwiessner's composition within
small space (`Turing.MultiTapeTM.ComputableInTimeAndSpace.comp_space`) recomputes each symbol of
the intermediate value when the second machine reads it, and stores only the two machines' work
tapes and counters of logarithmic length [Sipser, Section 8.5][Sipser2013].

The composed machine simulates both machines through the universal machine, so this directory,
unlike the base logspace API, depends on `Universal`. This module also registers the composition
rule of `fun_prop` for `ComputableInLogSpace`.

## Main results

* `Turing.MultiTapeTM.ComputableInLogSpace.comp`: logspace functions compose.
* `Turing.MultiTapeTM.ComputableInLogSpace.comp'`,
  `Turing.MultiTapeTM.ComputableInLogSpace.bool_not`: composition and negation in the form used by
  `fun_prop`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.5][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β γ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- The binary length of `m + 1` is at least `log₂ m + 1`. -/
private theorem log2_succ_le_length_encNat (m : ℕ) : Nat.log2 m + 1 ≤ (encNat (m + 1)).length := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.succ_le_iff, Nat.lt_size]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · exact (Nat.log2_self_le hm.ne').trans (Nat.le_succ m)

/-- The binary length of `m + 1` is logarithmic in `n` when `m` is polynomial in `n`. -/
private theorem length_encNat_succ_le {m n C d : ℕ} (h : m ≤ C * (n + 1) ^ d) :
    (encNat (m + 1)).length ≤ (Nat.size (C + 1) + d) * (Nat.log2 n + 1) := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
  have hpos : 0 < (n + 1) ^ d := Nat.pow_pos (Nat.succ_pos n)
  have hn : (n + 1) ^ d ≤ 2 ^ (d * (Nat.log2 n + 1)) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_log2_self d
  calc m + 1 ≤ (C + 1) * (n + 1) ^ d := by nlinarith
    _ < 2 ^ Nat.size (C + 1) * 2 ^ (d * (Nat.log2 n + 1)) :=
        Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self _) hn (Nat.two_pow_pos _)
    _ = 2 ^ (Nat.size (C + 1) + d * (Nat.log2 n + 1)) := (pow_add ..).symm
    _ ≤ 2 ^ ((Nat.size (C + 1) + d) * (Nat.log2 n + 1)) :=
        Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- **Logspace functions compose**, without storing the intermediate value: each of its symbols is
recomputed when the second machine reads it (`ComputableInTimeAndSpace.comp_space`). The
counters for positions in the input and in the intermediate value have logarithmic length, since
the intermediate value is polynomially long. -/
theorem ComputableInLogSpace.comp {g : β → γ} {f : α → β}
    (hg : ComputableInLogSpace g encMid encOut) (hf : ComputableInLogSpace f encIn encMid) :
    ComputableInLogSpace (g ∘ f) encIn encOut := by
  obtain ⟨C, d, hlen⟩ := hf.polyBounded_length.exists_le
  obtain ⟨tf, cf, hf⟩ := hf
  obtain ⟨tg, cg, hg⟩ := hg
  obtain ⟨c, h⟩ := hf.comp_space hg
  obtain ⟨K, hK⟩ : ∃ K, Nat.size (C + 1) + d = K := ⟨_, rfl⟩
  refine ⟨_, c * (cf + cg * K + Nat.size 2 + 1 + K + 1), h.mono (fun _ => le_rfl) fun a => ?_⟩
  have hm := hK ▸ length_encNat_succ_le (hlen a)
  have hn := length_encNat_succ_le (m := (encIn a).length) (n := (encIn a).length) (C := 1)
    (d := 1) (by simp)
  have hg' := Nat.mul_le_mul_left cg ((log2_succ_le_length_encNat (encMid (f a)).length).trans hm)
  rw [mul_assoc]
  refine Nat.mul_le_mul_left c ?_
  have hL : 1 ≤ Nat.log2 (encIn a).length + 1 := Nat.le_add_left _ _
  generalize Nat.log2 (encIn a).length + 1 = L at *
  generalize (encNat ((encIn a).length + 1)).length = A at *
  generalize (encNat ((encMid (f a)).length + 1)).length = B at *
  nlinarith

/-- Composition, in the form used by `fun_prop`. -/
@[fun_prop]
theorem ComputableInLogSpace.comp' {g : β → γ} {f : α → β}
    (hg : ComputableInLogSpace g encMid encOut) (hf : ComputableInLogSpace f encIn encMid) :
    ComputableInLogSpace (fun a => g (f a)) encIn encOut :=
  hg.comp hf

/-- Negating a computed Boolean, in the form used by `fun_prop`. -/
@[fun_prop]
theorem ComputableInLogSpace.bool_not {c : α → Bool} (hc : ComputableInLogSpace c encIn encBool) :
    ComputableInLogSpace (fun a => !c a) encIn encBool :=
  (ComputableInLogSpace.of_finite (encIn := encBool) not).comp' hc

end Turing.MultiTapeTM

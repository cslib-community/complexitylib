/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.TinyDesc
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Shared bounds for the space diagonals

The diagonal arguments for deterministic and nondeterministic space share two steps. They run a
machine on its own description, padded to a long enough word on which the description is tiny,
and they bound the size of the configurations of its simulation by the budget `G n`.

## Main results

* `Cslib.Complexity.Diagonal.exists_decodeDesc_tinyCut_eq`: every description is the tiny
  description at the start of arbitrarily long words.
* `Cslib.Complexity.Diagonal.eventually_cfgSpaceBound_le`: if every `c * f n + c` is eventually
  below `G n` and `4 * log₂ n ≤ G n`, the size bound
  `Turing.MultiTapeTM.Universal.cfgSpaceBound` of the configurations of a description within space
  `c₁ * f n + c₂` is eventually below `G n`.
-/

public section

namespace Cslib.Complexity.Diagonal

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal Filter

/-- **Every description is tiny at the start of arbitrarily long words**: padded to a doubly
exponential length beyond `N`, its framed encoding is tiny and decodes back to it. -/
theorem exists_decodeDesc_tinyCut_eq (d : Desc) (N : ℕ) :
    ∃ x : List Bool, N ≤ x.length ∧ tinyDesc x = true ∧ decodeDesc (tinyCut x) = d := by
  have htiny : tinyDesc (frame (eDesc d) ++ List.replicate (N + 2 ^ 2 ^ (eDesc d).length) false) =
      true := tinyDesc_frame_append (by rw [List.length_replicate]; exact Nat.le_add_left _ _)
  refine ⟨_, ?_, htiny, ?_⟩
  · rw [List.length_append, List.length_replicate]
    exact (Nat.le_add_right N _).trans (Nat.le_add_left _ _)
  · rw [tinyCut_of_tinyDesc htiny, decodeDesc_unframe_frame_append]

/-- **The configurations of a simulation within space `O(f)` eventually fit within `G n` bits**
when every `c * f n + c` is eventually below `G n` and `4 * log₂ n ≤ G n`: for a description of
length `D` with at most `D` work tapes, the size bound `Turing.MultiTapeTM.Universal.cfgSpaceBound`
is `O(D * f n + log n)`. -/
theorem eventually_cfgSpaceBound_le {f G : ℕ → ℕ} (hlog : ∀ n, 4 * Nat.log2 n ≤ G n)
    (hfG : ∀ c, ∀ᶠ n in atTop, c * f n + c ≤ G n) (D c₁ c₂ : ℕ) :
    ∀ᶠ n in atTop, ∀ k ≤ D, cfgSpaceBound D n k (c₁ * f n + c₂) ≤ G n := by
  set P := 6 * (2 * D + 5) * (c₁ + c₂) + 3 * D + 8 with hP
  filter_upwards [hfG (2 * P)] with n h₁ k hk
  have hl := hlog n
  have hn : (encNat (n + 1)).length ≤ Nat.log2 n + 2 := length_encNat_le_log2_add_two le_rfl
  set s := c₁ * f n + c₂ with hs
  have hsf : s ≤ (c₁ + c₂) * (f n + 1) := by rw [hs]; nlinarith
  have hP' : 6 * (2 * D + 5) * s + 3 * D + 8 ≤ P * (f n + 1) := by
    have := Nat.mul_le_mul_left (6 * (2 * D + 5)) hsf
    have e₁ : P * (f n + 1) = 6 * (2 * D + 5) * ((c₁ + c₂) * (f n + 1)) +
        (3 * D + 8) * (f n + 1) := by rw [hP]; ring
    have : 3 * D + 8 ≤ (3 * D + 8) * (f n + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have e₂ : 2 * P * f n + 2 * P = 2 * (P * (f n + 1)) := by ring
  have e₃ : 3 * (2 * D + 5) * 2 * s = 6 * (2 * D + 5) * s := by ring
  simp only [cfgSpaceBound]
  omega

end Cslib.Complexity.Diagonal

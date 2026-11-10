/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingInput
public import CslibFrontier.Computability.WordRAM.Width
import Mathlib.Data.List.GetD

/-!
# Polynomial native preprocessing intermediates at every admitted width

The program never reads physical width. Its complete execution at the derived minimum width
therefore identifies every prefix at every larger admitted width. Every actual register and
memory word, including address and arithmetic temporaries, has polynomial magnitude throughout.

## Main results

* `two_pow_width_le`: the minimum-width word universe has polynomial magnitude.
* `intermediates_polynomial`: uniform polynomial bounds on every actual run-prefix word.
* `space_polynomial`: every actual run prefix has zero memory beyond the same polynomial range.

These native representation bounds are original and use the generic width-prefix API.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM

/-- The derived minimum-width word universe is bounded by a fixed polynomial. -/
theorem two_pow_width_le (κ n : ℕ) :
    2 ^ width κ n ≤ (n + 2) ^ (2720 * κ + 16456) := by
  have hw : width κ n ≤ 17 * Frontend.width κ n := by
    dsimp only [width, Frontend.width]
    omega
  calc 2 ^ width κ n ≤ 2 ^ (17 * Frontend.width κ n) := Nat.pow_le_pow_right (by decide) hw
    _ = (2 ^ Frontend.width κ n) ^ 17 := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ ((n + 2) ^ (160 * κ + 968)) ^ 17 :=
      Nat.pow_le_pow_left (Frontend.two_pow_width_le κ n) 17
    _ = _ := by
      rw [← pow_mul]
      exact congrArg (fun e : ℕ => (n + 2) ^ e) (by omega)

/-- Every register, temporary and memory word has polynomial magnitude at every admitted width. -/
theorem intermediates_polynomial {κ w : ℕ} (input : List ℤ)
    (hw : width κ input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ))
    {s : State 128} {steps : ℕ}
    (hr : Runs w (flatProgram κ) (State.init (input.map Signed.encode)) s steps) :
    (∀ i, s.data.regs i < (input.length + 2) ^ (2720 * κ + 16456)) ∧
      ∀ a, s.data.mem a < (input.length + 2) ^ (2720 * κ + 16456) := by
  obtain ⟨_, _, _, he, _, _, _, _, _, _, _, _⟩ := runs_input input le_rfl hvalues
  obtain ⟨regs, mem, -⟩ := hr.prefix_bounds_init
    (Code.not_readsWidth_program (not_readsWidth κ) Traversal.outputCount) hw
    (input_fits input le_rfl hvalues) he (two_pow_width_le κ input.length)
  exact ⟨regs, mem⟩

/-- Every prefix uses a polynomial initial interval of memory, even at wider physical widths. -/
theorem space_polynomial {κ w : ℕ} (input : List ℤ)
    (hw : width κ input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ))
    {s : State 128} {steps a : ℕ}
    (hr : Runs w (flatProgram κ) (State.init (input.map Signed.encode)) s steps)
    (ha : (input.length + 2) ^ (2720 * κ + 16456) ≤ a) : s.data.mem a = 0 := by
  obtain ⟨_, _, _, he, _, _, _, _, _, _, _, _⟩ := runs_input input le_rfl hvalues
  exact (hr.prefix_bounds_init
    (Code.not_readsWidth_program (not_readsWidth κ) Traversal.outputCount) hw
    (input_fits input le_rfl hvalues) he (two_pow_width_le κ input.length)).2.2 a ha

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Protocols.PIR.CoveringCode

/-!
# Tests: covering-code schemes for private information retrieval

* **Corollary 2.** Two servers read `27` bits with `38` bits of communication, and four servers
  read `81` bits with `88`. For `n = 2 ^ 30`, the two-server covering-code scheme communicates
  `12 290` bits, against `131 076` for the `√n` scheme of `PIR.hasScheme_two_sqrt`.
* **Balance.** The two covers of Corollary 2 give exactly Theorem 1's count. The repetition code
  `{000, 111}` is a radius-`1` covering code, so `PIR.RadiusOneCover.hasScheme_of_hammingDist` gives
  the same `38` bits. The two-word code `{0000, 1111}` is not a radius-`1` covering code, and one
  server emulating three neighbours cannot cover the three-bit cube (the volume bound).
-/

namespace ComplexityTests.Crypto.PIRCoveringCode

open Cslib.Crypto.Protocols.PIR

/-! ### Corollary 2 -/

example : HasScheme (Fin 27) 2 38 := hasScheme_two_of_le_pow_three (ℓ := 3) (by norm_num)

example : HasScheme (Fin 81) 4 88 := hasScheme_four_of_le_pow_four (ℓ := 3) (by norm_num)

/-- For `n = 2 ^ 30`, two servers with `12 · 2 ^ 10 + 2` bits. -/
example : HasScheme (Fin (2 ^ 30)) 2 12290 :=
  hasScheme_two_of_le_pow_three (ℓ := 2 ^ 10) (by norm_num)

/-- The `√n` scheme for the same database communicates `4 (2 ^ 15 + 1)` bits. -/
example : HasScheme (Fin (2 ^ 30)) 2 131076 := by
  have h := hasScheme_two_sqrt (2 ^ 30)
  rwa [show Nat.sqrt (2 ^ 30) = 2 ^ 15 from Nat.sqrt_eq' (2 ^ 15)] at h

/-! ### Balance and the volume bound -/

/-- The two-server cover is balanced, so the scheme communicates Theorem 1's
`k + (2 ^ d + (d - 1) k) ℓ` bits. -/
example (ι : Type) [Fintype ι] [DecidableEq ι] :
    communication Bool (Fin 3 → ι → Bool) (Bool × (Fin 3 → ι → Bool)) =
      2 + (2 ^ 3 + (3 - 1) * 2) * Fintype.card ι := by
  have h := RadiusOneCover.communication_scheme_of_balanced (S := Bool) (D := Fin 3)
    (M := Fin 3) (ι := ι) (by decide) (by decide)
  simpa only [Fintype.card_bool, Fintype.card_fin] using h

/-- The four-server cover is balanced as well. -/
example (ι : Type) [Fintype ι] [DecidableEq ι] :
    communication (Bool × Bool) (Fin 4 → ι → Bool) (Bool × (Fin 3 → ι → Bool)) =
      4 + (2 ^ 4 + (4 - 1) * 4) * Fintype.card ι := by
  have h := RadiusOneCover.communication_scheme_of_balanced (S := Bool × Bool) (D := Fin 4)
    (M := Fin 3) (ι := ι) (by decide) (by decide)
  simpa only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] using h

/-- The repetition code `{000, 111}` is a radius-`1` covering code. -/
theorem hammingDist_repetition (w : Fin 3 → Bool) :
    ∃ b : Bool, hammingDist (fun _ : Fin 3 => b) w ≤ 1 := by
  revert w
  decide

/-- Emulating all neighbours of a perfect code gives the same `38` bits for `27` bits. -/
example : HasScheme (Fin 27) 2 38 := by
  have h := RadiusOneCover.hasScheme_of_hammingDist (n := 27) (ℓ := 3) hammingDist_repetition
    (by decide)
  simpa only [Fintype.card_bool, Fintype.card_fin] using h

/-- The two-word code `{0000, 1111}` is not a radius-`1` covering code: `0011` is at distance `2`
from both codewords. -/
example : ¬ ∀ w : Fin 4 → Bool, ∃ b : Bool, hammingDist (fun _ : Fin 4 => b) w ≤ 1 := by
  decide

/-- One server emulating three neighbours cannot cover the three-bit cube: `2 ^ 3 > 1 · 4`. -/
example : IsEmpty (RadiusOneCover Unit (Fin 3) (Fin 3)) :=
  ⟨fun K => absurd K.two_pow_card_le (by decide)⟩

end ComplexityTests.Crypto.PIRCoveringCode

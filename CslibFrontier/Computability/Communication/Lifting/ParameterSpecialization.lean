/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.GeneralParameters
import Mathlib.Tactic.NormNum

/-!
# A polynomial-alphabet parameter certificate

The elementary fourth-power XOR bound admits a concrete polynomial-size specialization.
For an ambient bound `B ≥ n`, use alphabet size `B^2048`, speaker density `B^1984`, other
speaker density `B^2016`, and target density `B^1984`. Uniform gadget discrepancy at most
`B^(-1024)` suffices. The constants are deliberately loose; this certificate does not claim
the sharper parameters of the original lifting theorem.
-/

public section

namespace Cslib.Communication.Lifting

/-- Explicit scalar parameters for the rare-danger theorem, with the speaker density equal
to the target density as needed by the alternating simulation. -/
theorem polynomial_parameter_certificate {B N D : ℝ} (hB : 2 ≤ B)
    (hN : 2 ≤ N) (hNB : N ≤ B) (hD : D ≤ (B ^ 1024)⁻¹) :
    16 * N ^ 2 ≤ B ^ 2016 / B ^ 1984 ∧
    N ^ (2 * 16) ≤ B ^ 2016 / B ^ 1984 ∧
    1 ≤ B ^ 129 ∧
    N * B ^ 2048 ≤ (B ^ 129) ^ 16 ∧
    0 < 1 / (4 * B ^ 131) ∧
    N * (N + 1) * B ^ 129 * (1 / (4 * B ^ 131)) ≤ 1 / 2 ∧
    16384 * ((B ^ 2048) ^ 2 * N ^ 2 / (B ^ 1984 * B ^ 2016)) ^ 4 * D ≤
      ((1 / (4 * B ^ 131)) / (2 * N)) ^ 4 := by
  simpa using general_parameter_certificate (a := 1984) (k := 1) (by decide) (by decide)
    hB hN hNB hD

/-- The polynomial parameters leave strict density headroom at both levels, and each query
contributes at least a factor `B^31` to the simulation's potential budget. -/
theorem polynomial_density_ratios {B : ℝ} (hB : 2 ≤ B) :
    0 < B ^ 1984 ∧ B ^ 1984 < B ^ 2016 ∧ B ^ 2016 < B ^ 2048 ∧
      B ^ 31 ≤ B ^ 2048 / (2 * B ^ 2016) := by
  simpa using general_density_ratios (a := 1984) (k := 1) (by decide) hB

end Cslib.Communication.Lifting

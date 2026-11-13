/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.SmallBias.Pointwise
import Mathlib.Tactic.Linarith

/-!
# Full range from parity estimates

For independent finite sources, sufficiently small biases of all nonempty output parities
force every output string to have a preimage in the product of the source supports. This is
the pointwise-Fourier step used in low-discrepancy lifting. The hypotheses here are explicit
parity estimates; obtaining them from discrepancy and blockwise density is a separate step.
No protocol-to-query simulation is asserted by this module.
-/

public section

namespace Cslib.Communication.Lifting

open Finset BitString Probability

variable {X Y ι : Type*} [Fintype X] [Fintype Y] [Fintype ι]

/-- Pointwise Fourier estimates yield a preimage for every output string. The two sources may
have arbitrary dependence among their own coordinates; independence is only between players. -/
theorem exists_pair_of_parity_bias_le (p : PMF X) (q : PMF Y) (F : X → Y → ι → Bool)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hbias : ∀ S : Finset ι, S.Nonempty →
      |∑ x, ∑ y, (p x).toReal * (q y).toReal * signVal (parityOn S (F x y))| ≤
        ε * (1 / (2 * Fintype.card ι) : ℝ) ^ S.card)
    (z : ι → Bool) : ∃ x ∈ p.support, ∃ y ∈ q.support, F x y = z := by
  classical
  let law := p.bind fun x => q.map (F x)
  have hbound := abs_mul_mass_sub_one_le_of_bias_le law hε (fun S hS => by
    rw [bias_bind_map_eq]
    exact hbias S hS) z
  have hz : z ∈ law.support := by
    by_contra hn
    rw [(law.apply_eq_zero_iff z).mpr hn, ENNReal.toReal_zero, mul_zero] at hbound
    norm_num at hbound
    linarith
  obtain ⟨x, hx, hz⟩ := (PMF.mem_support_bind_iff p (fun x => q.map (F x)) z).mp hz
  obtain ⟨y, hy, heq⟩ := (PMF.mem_support_map_iff (F x) q z).mp hz
  exact ⟨x, hx, y, hy, heq⟩

end Cslib.Communication.Lifting

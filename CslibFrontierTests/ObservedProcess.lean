/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.PMF.ObservedProcess
import Mathlib.Tactic

/-!
# Complete observed-history conditioning with infinite hidden state type

An initially revealed fair bit disappears from the current observation and is
revealed again later. Public path laws must retain that correlation rather than
replace the hidden bit by a fresh sample from its current-observation marginal.
-/

noncomputable section
open Cslib.Probability
namespace CslibFrontierTests.ObservedProcess

/-- An infinite hidden state type, with a persistent private bit after the first draw. -/
def step : ℕ × Bool → PMF (ℕ × Bool)
  | (0, _) => (PMF.uniformOfFintype Bool).map (fun b => (1, b))
  | (n + 1, b) => PMF.pure (n + 2, b)

/-- At stage two the observation forgets the bit; the full history remembers it. -/
def observe (state : ℕ × Bool) : Bool :=
  if state.1 = 1 ∨ state.1 = 3 then state.2 else false

/-- The constructed behavioral law preserves the entire repeated-bit path. -/
theorem observed_path : ObservedProcess.publicLaw step observe 3 (0, false) =
    (PMF.uniformOfFintype Bool).map (fun b => [b, false, b, false]) := by
  rw [ObservedProcess.public_eq_observed]
  simp [ObservedProcess.privateLaw, step, observe, Function.comp_def, PMF.map]

/-- The shared last observation alone cannot justify an independent later bit. -/
example : ObservedProcess.publicLaw step observe 3 (0, false) [false, false, true, false] = 0 := by
  rw [observed_path]
  norm_num [PMF.map_apply, tsum_fintype, Fintype.sum_bool, PMF.uniformOfFintype_apply]

example : ObservedProcess.publicLaw step observe 3 (0, false) [true, false, true, false] = 2⁻¹ := by
  rw [observed_path]
  norm_num [PMF.map_apply, tsum_fintype, Fintype.sum_bool, PMF.uniformOfFintype_apply]

/-- Null observations use a harmless completion even for an infinite hidden type. -/
example : PMF.posterior (PMF.pure (2 : ℕ)) (fun n => n % 2) 1 = PMF.pure 2 := by
  norm_num [PMF.posterior, PMF.mem_support_pure_iff]

/-- The null branch contributes no mass in the proved disintegration identity. -/
example : ((PMF.pure (2 : ℕ)).map (fun n => n % 2)) 1 *
    PMF.posterior (PMF.pure 2) (fun n => n % 2) 1 2 = 0 := by
  rw [PMF.posterior_factor]
  norm_num

end CslibFrontierTests.ObservedProcess

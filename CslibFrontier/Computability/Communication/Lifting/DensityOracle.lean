/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.DensitySimulation

/-! # Local density simulation guarantees -/

@[expose] public section
namespace Cslib.Communication.Lifting
variable {n m : ℕ}

/-- Local ingredients for simulation, with the speaker's density lower than the listener's.
This interface does not assume any recursively simulated protocol. -/
structure DensityOracle (g : Fin m → Fin m → Bool) (τ σ : ℝ) : Prop where
  /-- Obtain one valid step for any message function. -/
  step : ∀ (F : Finset (Fin n)) (X Y : Finset (Fin n → Fin m)),
    X.Nonempty → Y.Nonempty → IsDense σ F X → IsDense τ F Y →
    ∀ send, ∃ st : DensityStep n m, st.Valid g τ σ F X Y send
  /-- Realize any prescribed output on the residual free coordinates. -/
  full : ∀ (F : Finset (Fin n)) (X Y : Finset (Fin n → Fin m)),
    X.Nonempty → Y.Nonempty → IsDense σ F X → IsDense τ F Y →
    ∀ z : Fin n → Bool, ∃ x ∈ X, ∃ y ∈ Y, ∀ i ∈ F, g (x i) (y i) = z i


end Cslib.Communication.Lifting

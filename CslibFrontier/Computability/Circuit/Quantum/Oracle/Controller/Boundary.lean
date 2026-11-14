/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.Handler
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Interaction

/-!
# Compatibility with one classical-query boundary

The retained-state sampler used by the device has exactly the conditional states of
`UniformOracleCircuitFamily.runClassicalQuery`. Reading a finite prefix, retaining its complete
joint state, and applying the existing reply-averaged native continuation therefore gives the
same terminal POVM law as that API.

This is semantic compatibility, not a generic compiler between register layouts. In particular,
`resumeRun` initializes a fresh classical input block around the entire saved quantum register.
Compiling arbitrary such layouts onto one fixed device requires an additional preallocation and
relocation certificate. Concrete compatible layouts can be implemented with existing gate codes.

## Main results

* `Cslib.Quantum.UniformOracleCircuitFamily.measureDensity_runClassicalQuery_deviceState`:
  the one-boundary API equals supported device-state readout followed by its native continuation.
-/

public section

namespace Cslib.Quantum.UniformOracleCircuitFamily

variable {a b L₁ L₂ : ℕ → ℕ}
    (F G : UniformOracleCircuitFamily)
    (hF : F.HasOracleSignature a b L₁) (hG : G.HasOracleSignature a b L₂)
    (n : ℕ) (x : List Bool) (hx : x.length ≤ L₁ n) (s : ℕ)
    (hnext : x.length + (F.description n x.length).outputWidth + s ≤ L₂ n)
    (hkeep : (G.description n
      (x.length + (F.description n x.length).outputWidth + s)).quantumInputWidth =
      (F.description n x.length).width)
    (H : (Fin (a n) → Bool) → Fin (b n) → Bool)
    (service : ((Fin (a n) → Bool) → Fin (b n) → Bool) →
      (Fin (F.description n x.length).outputWidth → Bool) → PMF (Fin s → Bool))
    (κ : Type) [Fintype κ] [DecidableEq κ]

/-- The existing one-boundary terminal law is exactly the finite-prefix device measurement,
with the whole conditional joint density passed to the existing native second stage. -/
theorem measureDensity_runClassicalQuery_deviceState {B : Type} [Fintype B]
    (M : POVM B ((Fin (G.description n
      (x.length + (F.description n x.length).outputWidth + s)).width → Bool) × κ))
    (ρ) (hρ : IsDensityMatrix ρ) :
    let initial : DeviceState (F.description n x.length).width κ Unit :=
      ⟨F.runDensityWithReference n x (hF.oracle n x.length hx H) κ ρ,
        F.isDensityMatrix_runDensityWithReference n x (hF.oracle n x.length hx H) κ hρ, ()⟩
    let read := fun z => fun i => z (Fin.castLEEmb (F.wellFormed n x.length).output_le i)
    M.measureDensity (G.runClassicalQuery hG n x H κ F hF hx s hnext hkeep service ρ)
      (G.isDensityMatrix_runClassicalQuery hG n x H κ F hF hx s hnext hkeep service hρ) =
      (initial.measure read).bind fun p =>
        M.measureDensity
          (G.resumeDensity hG n x hnext hkeep H κ p.1 (service H p.1) p.2.density)
          (G.isDensityMatrix_resumeDensity hG n x hnext hkeep H κ p.1
            (service H p.1) p.2.isDensityMatrix) := by
  dsimp only
  rw [G.measureDensity_runClassicalQuery_eq hG n x H κ F hF hx s hnext hkeep service M ρ hρ]
  rw [DeviceState.measure_bind (next := fun request state =>
    M.measureDensity
      (G.resumeDensity hG n x hnext hkeep H κ request (service H request) state.density)
      (G.isDensityMatrix_resumeDensity hG n x hnext hkeep H κ request
        (service H request) state.isDensityMatrix))]
  rfl

end Cslib.Quantum.UniformOracleCircuitFamily

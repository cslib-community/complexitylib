/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.GateMatrix
public import Complexity.Foundations.Quantum.Bell
public import Complexity.Foundations.Quantum.Bipartite
public import Complexity.Foundations.Quantum.Register
public import Cslib.Probability.PMF

/-!
# Quantum teleportation

**Teleportation** [Bennett et al.][BennettBrassardCrepeauJozsaPeresWootters1993];
[de Wolf][deWolf2019], Section 1.5. Alice holds an unknown qubit `ψ` and shares a Bell state
`|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` with Bob. The three qubits are indexed by `(Bool × Bool) × Bool`:
Alice's input qubit and her half of the Bell state, then Bob's half. The protocol:

1. Alice applies a CNOT to her two qubits (her input is the control), then a Hadamard to her input
   qubit (`Cslib.Quantum.teleportUnitary`). The joint state is
   `½ ∑_{a,b} |a, b⟩ ⊗ X^b Z^a ψ` (`Cslib.Quantum.teleportState_apply`).
2. Alice measures her two qubits in the computational basis. Each outcome `(a, b)` has probability
   `1/4`, whatever `ψ` is (`Cslib.Quantum.measure_teleportState_map_fst`), and leaves Bob's qubit in
   the post-measurement state `X^b Z^a ψ` (`Cslib.Quantum.postMeasure`).
3. Alice sends `(a, b)` to Bob, who applies the correction `Z^a X^b`
   (`Cslib.Quantum.teleportCorrection`): first `X` if `b = 1`, then `Z` if `a = 1`. He holds `ψ`
   (`Cslib.Quantum.teleportCorrection_postMeasure`).

`Cslib.Quantum.teleportation` states the result. The measurement is the computational-basis
measurement of `Complexity/Foundations/Quantum/Measurement.lean`, read on Alice's qubits through the
marginal `PMF.map Prod.fst`. Bob's corrected state is the corresponding post-measurement state of
`Complexity/Foundations/Quantum/Bipartite.lean`.

Scope: pure states only, with a single input qubit that is not entangled with a further reference
system. Teleportation of one half of an entangled state is not formalized here.

## Main definitions

* `Cslib.Quantum.teleportInput`: the initial state `ψ ⊗ Φ⁺`.
* `Cslib.Quantum.teleportUnitary`: Alice's unitary, the CNOT and then the Hadamard.
* `Cslib.Quantum.teleportState`: the joint state before Alice's measurement.
* `Cslib.Quantum.teleportCorrection`: Bob's correction `Z^a X^b`.

## Main results

* `Cslib.Quantum.teleportState_apply`: the amplitudes of the joint state before measurement.
* `Cslib.Quantum.measure_teleportState_map_fst`: Alice's outcome is uniform on `Bool × Bool`.
* `Cslib.Quantum.teleportCorrection_postMeasure`: Bob's corrected post-measurement state is `ψ`.
* `Cslib.Quantum.teleportation`: both together.

## References

* [C. H. Bennett, G. Brassard, C. Crépeau, R. Jozsa, A. Peres, W. K. Wootters, *Teleporting an
  unknown quantum state via dual classical and Einstein-Podolsky-Rosen
  channels*][BennettBrassardCrepeauJozsaPeresWootters1993]
* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

namespace Cslib.Quantum

open Matrix Gate
open scoped Kronecker

/-- The initial state `ψ ⊗ Φ⁺` of teleportation, indexed by
`((Alice's input, Alice's Bell half), Bob's Bell half)`. -/
noncomputable def teleportInput (ψ : EuclideanSpace ℂ Bool) :
    EuclideanSpace ℂ ((Bool × Bool) × Bool) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.prodAssoc Bool Bool Bool).symm (prodState ψ bell)

theorem teleportInput_apply (ψ : EuclideanSpace ℂ Bool) (a b c : Bool) :
    (teleportInput ψ).ofLp ((a, b), c) = ψ.ofLp a * bell.ofLp (b, c) :=
  prodState_apply ψ bell (a, (b, c))

theorem norm_teleportInput (ψ : EuclideanSpace ℂ Bool) : ‖teleportInput ψ‖ = ‖ψ‖ := by
  rw [teleportInput, LinearIsometryEquiv.norm_map, norm_prodState, norm_bell, mul_one]

/-- Alice's unitary in teleportation: a CNOT on her two qubits, controlled by her input qubit,
followed by a Hadamard on her input qubit. -/
noncomputable def teleportUnitary : unitaryGroup ((Bool × Bool) × Bool) ℂ :=
  onFirst (onFirst ⟨hadamardMatrix, hadamardMatrix_mem_unitaryGroup⟩) *
    onFirst ⟨cnotMatrix, cnotMatrix_mem_unitaryGroup⟩

/-- The joint state of teleportation before Alice's measurement. -/
noncomputable def teleportState (ψ : EuclideanSpace ℂ Bool) :
    EuclideanSpace ℂ ((Bool × Bool) × Bool) :=
  unitaryEquiv teleportUnitary (teleportInput ψ)

theorem norm_teleportState (ψ : EuclideanSpace ℂ Bool) : ‖teleportState ψ‖ = ‖ψ‖ := by
  rw [teleportState, LinearIsometryEquiv.norm_map, norm_teleportInput]

/-- The joint state before Alice's measurement is `½ ∑_{a,b} |a, b⟩ ⊗ X^b Z^a ψ`: its amplitude at
`|a, b, c⟩` is `½ (-1)^{a (b ⊕ c)} ψ_{b ⊕ c}` [de Wolf][deWolf2019], Section 1.5. -/
theorem teleportState_apply (ψ : EuclideanSpace ℂ Bool) (a b c : Bool) :
    (teleportState ψ).ofLp ((a, b), c) =
      (1 / 2 : ℂ) * ((if a && (b ^^ c) then -1 else 1) * ψ.ofLp (b ^^ c)) := by
  have hs : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [← hs]
  simp only [teleportState, teleportUnitary, unitaryEquiv_apply, Submonoid.coe_mul, coe_onFirst,
    ← mulVec_mulVec, kronecker_one_mulVec_apply, hadamardMatrix_mulVec, cnotMatrix_mulVec,
    teleportInput_apply, bell_apply]
  cases a <;> cases b <;> cases c <;> simp <;> ring

/-- Bob's correction `Z^a X^b` in teleportation: first `X` if `b = 1`, then `Z` if `a = 1`. -/
noncomputable def teleportCorrection (a b : Bool) : unitaryGroup Bool ℂ :=
  (if a then ⟨pauliZ, pauliZ_mem_unitaryGroup⟩ else 1) *
    (if b then ⟨pauliX, pauliX_mem_unitaryGroup⟩ else 1)

/-- Bob's correction maps `v` to `((-1)^{a c} v_{c ⊕ b})_c`. -/
theorem teleportCorrection_mulVec (a b : Bool) (v : Bool → ℂ) (c : Bool) :
    ((teleportCorrection a b : Matrix Bool Bool ℂ) *ᵥ v) c =
      (if a && c then -1 else 1) * v (c ^^ b) := by
  cases a <;> cases b <;> cases c <;> simp [teleportCorrection, ← mulVec_mulVec]

/-- Bob's correction maps the unnormalized post-measurement state of outcome `(a, b)` to `ψ/2`. -/
theorem teleportCorrection_condState (ψ : EuclideanSpace ℂ Bool) (a b : Bool) :
    unitaryEquiv (teleportCorrection a b) (condState (a, b) (teleportState ψ)) =
      (1 / 2 : ℂ) • ψ := by
  ext c
  rw [unitaryEquiv_apply, teleportCorrection_mulVec, condState_apply, teleportState_apply]
  cases a <;> cases b <;> cases c <;> simp

theorem norm_condState_teleportState (ψ : EuclideanSpace ℂ Bool) (a b : Bool) :
    ‖condState (a, b) (teleportState ψ)‖ = ‖ψ‖ / 2 := by
  rw [← LinearIsometryEquiv.norm_map (unitaryEquiv (teleportCorrection a b)),
    teleportCorrection_condState, norm_smul, norm_div, norm_one, RCLike.norm_ofNat]
  ring

/-- In teleportation of a unit qubit, each outcome `(a, b)` of Alice's measurement has
probability `1/4`. -/
theorem measure_teleportState_map_fst_apply (ψ : EuclideanSpace ℂ Bool) (hψ : ‖ψ‖ = 1)
    (a b : Bool) :
    (measure (teleportState ψ) ((norm_teleportState ψ).trans hψ)).map Prod.fst (a, b) = 4⁻¹ := by
  rw [measure_map_fst_apply _ ((norm_teleportState ψ).trans hψ), norm_condState_teleportState, hψ,
    show ((1 : ℝ) / 2) ^ 2 = (4 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- In teleportation of a unit qubit, Alice's measurement outcome is uniform on `Bool × Bool`,
independently of the teleported qubit. -/
theorem measure_teleportState_map_fst (ψ : EuclideanSpace ℂ Bool) (hψ : ‖ψ‖ = 1) :
    (measure (teleportState ψ) ((norm_teleportState ψ).trans hψ)).map Prod.fst =
      Cslib.Probability.PMF.uniformOfFintype (Bool × Bool) := by
  ext ⟨a, b⟩
  rw [measure_teleportState_map_fst_apply ψ hψ, Cslib.Probability.PMF.uniformOfFintype_apply,
    Fintype.card_prod, Fintype.card_bool]
  norm_num

/-- After outcome `(a, b)` of Alice's measurement, Bob's correction `Z^a X^b` turns his
post-measurement qubit into the teleported qubit `ψ`. -/
theorem teleportCorrection_postMeasure (ψ : EuclideanSpace ℂ Bool) (hψ : ‖ψ‖ = 1) (a b : Bool) :
    unitaryEquiv (teleportCorrection a b) (postMeasure (a, b) (teleportState ψ)) = ψ := by
  rw [postMeasure_def, LinearIsometryEquiv.map_smul, teleportCorrection_condState,
    norm_condState_teleportState, hψ, smul_smul]
  norm_num

/-- **Quantum teleportation** [Bennett et al.][BennettBrassardCrepeauJozsaPeresWootters1993];
[de Wolf][deWolf2019], Section 1.5. Alice holds a unit qubit `ψ` and shares the Bell state with
Bob. She applies a CNOT and then a Hadamard to her two qubits and measures them. Her outcome
`(a, b)` is uniformly distributed, and for every outcome Bob's correction `Z^a X^b` turns his
post-measurement qubit into `ψ`. -/
theorem teleportation (ψ : EuclideanSpace ℂ Bool) (hψ : ‖ψ‖ = 1) :
    (measure (teleportState ψ) ((norm_teleportState ψ).trans hψ)).map Prod.fst =
        Cslib.Probability.PMF.uniformOfFintype (Bool × Bool) ∧
      ∀ a b : Bool,
        unitaryEquiv (teleportCorrection a b) (postMeasure (a, b) (teleportState ψ)) = ψ :=
  ⟨measure_teleportState_map_fst ψ hψ, teleportCorrection_postMeasure ψ hψ⟩

end Cslib.Quantum

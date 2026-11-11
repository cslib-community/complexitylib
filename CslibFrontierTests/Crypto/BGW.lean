/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Protocols.MPC.BGW
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete Tests for Shamir Secret-Sharing Homomorphisms and BGW Arithmetic MPC Gates

Non-vacuous concrete evaluations and end-to-end protocol instantiations over `ZMod 5` (`p = 5`,
`m = 3`, threshold `t = 1` with `2 * t = 2 < 3 = m`, evaluation points `1, 2, 3 : ZMod 5`)
exercising `CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Linear` and
`CslibFrontier.Crypto.Protocols.MPC.BGW`:

1. **Shamir parameters, linear homomorphisms, and Lagrange weights (`ZMod 5`, `m = 3`, `t = 1`):**
   explicit 3-party degree-1 Shamir parameter bundle `params3`, additive and scalar-multiplicative
   share homomorphisms, and secret recovery on 2-of-3 authorized coalitions `{0, 1}` and `{1, 2}`.
2. **Multiplicative property and BGW degree reduction (`2 * t = 2 < 3`):**
   reconstructing pointwise products `share params3 rA 3 i * share params3 rB 4 i` and degree-2
   zero-randomized products `bgwMulStep`, plus degree reduction via `bgwDegreeReduceShare` and
   2-party reconstruction of `3 * 4 = 2 : ZMod 5` on `{0, 2}`.
3. **Unauthorized-coalition marginal uniformity (`|I| ≤ 1`):**
   exact uniformity of singleton (`{0}`) and empty (`∅`) coalition views.
4. **End-to-end `bgwDegreeReductionProtocol` and `bgwSumProtocol` executions and $t$-privacy:**
   supported executions, authorized output reconstruction, coalition view simulation, full joint
   view-and-output $1$-privacy, and zero `semiHonestAdvantage`.
-/

namespace CslibFrontierTests.Crypto.BGW

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto
open Cslib.Crypto.Protocols.MPC Cslib.Crypto.Protocols.MPC.BGW
open Cslib.Crypto.Protocols.SecretSharing Cslib.Crypto.Protocols.SecretSharing.Shamir

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Canonical 3-party degree-1 Shamir parameters over `ZMod 5` with nonzero evaluation points
`point i = i.val + 1 ∈ {1, 2, 3}` and threshold `t = 1` (`2 * t = 2 < 3`). -/
def params3 : Params (ZMod 5) (Fin 3) where
  threshold := 1
  threshold_lt_card := by decide
  point i := (i.val + 1 : ZMod 5)
  point_injective := by decide
  point_nonzero := by decide

instance (s : Finset (Fin 3)) : Decidable (authorized params3 s) :=
  inferInstanceAs (Decidable (params3.threshold + 1 ≤ s.card))

/-- Degree-1 randomness `rA = ![2]` for secret `a = 3` (`P_A(X) = 3 + 2X`). -/
def rA : Randomness params3 := ![2]

/-- Degree-1 randomness `rB = ![4]` for secret `b = 4` (`P_B(X) = 4 + 4X`). -/
def rB : Randomness params3 := ![4]

/-- Degree-2 zero-masking randomness `rZ = ![1, 3]` for `bgwMulStep`. -/
def rZ : Fin (2 * params3.threshold) → ZMod 5 := ![1, 3]

/-- Per-party degree-1 resharing randomness for BGW degree reduction. -/
def rSub : Fin 3 → Randomness params3 := ![![1], ![2], ![4]]

/-- Concrete 3-party input vector `![3, 4, 2]` with sum `3 + 4 + 2 = 4 : ZMod 5`. -/
def sampleInputs3 : Fin 3 → ZMod 5 := ![3, 4, 2]

/-! ### 1. Linear homomorphisms and authorized reconstruction -/

/-- Concrete evaluation of `share params3 0 3`: sharing `3` with zero randomness gives
`![3, 3, 3]`. -/
example : (fun i : Fin 3 => share params3 0 3 i) = ![3, 3, 3] := by
  ext i
  rw [share_zero_randomness]
  fin_cases i <;> rfl

/-- Reconstructing `share params3 rA 3` on the 2-party coalition `{0, 1}` recovers `3 : ZMod 5`
directly via `reconstruct_share_eq_secret`. -/
example :
    reconstruct params3 ({0, 1} : Finset (Fin 3))
      (fun i : ({0, 1} : Finset (Fin 3)) => share params3 rA 3 i) = 3 :=
  reconstruct_share_eq_secret params3 rA 3 (by decide)

/-- Any 2-party coalition is authorized for `params3` (`threshold + 1 = 2`). -/
example : authorized params3 ({0, 1} : Finset (Fin 3)) := by
  decide

/-- Reconstructing pointwise share sums over the 2-party coalition `{0, 1}` recovers
`3 + 4 = 2 : ZMod 5`. -/
example :
    reconstruct params3 ({0, 1} : Finset (Fin 3))
      (fun i : ({0, 1} : Finset (Fin 3)) =>
        share params3 rA 3 i + share params3 rB 4 i) = (2 : ZMod 5) :=
  reconstruct_share_add params3 rA rB 3 4 (by decide)

/-- Reconstructing scalar-multiplied shares over `{1, 2}` recovers `2 * 3 = 1 : ZMod 5`. -/
example :
    reconstruct params3 ({1, 2} : Finset (Fin 3))
      (fun i : ({1, 2} : Finset (Fin 3)) =>
        (2 : ZMod 5) * share params3 rA 3 i) = (1 : ZMod 5) :=
  reconstruct_share_smul params3 2 rA 3 (by decide)

/-- Additivity of `Shamir.reconstruct` on concrete share vectors over `{0, 1}`. -/
example (σ₁ σ₂ : ({0, 1} : Finset (Fin 3)) → ZMod 5) :
    reconstruct params3 ({0, 1} : Finset (Fin 3)) (σ₁ + σ₂) =
      reconstruct params3 ({0, 1} : Finset (Fin 3)) σ₁ +
        reconstruct params3 ({0, 1} : Finset (Fin 3)) σ₂ :=
  reconstruct_add params3 ({0, 1} : Finset (Fin 3)) σ₁ σ₂

/-! ### 2. Multiplicative property and BGW degree reduction (`2 * t < 3`) -/

/-- Reconstructing the pointwise product of degree-1 shares across all 3 parties recovers
`3 * 4 = 2 : ZMod 5`. -/
example :
    Polynomial.reconstruct params3.point
      (fun i : Fin 3 => share params3 rA 3 i * share params3 rB 4 i) = (2 : ZMod 5) :=
  reconstruct_mul_share_eq_mul params3 (by decide) rA rB 3 4

/-- Reconstructing the degree-2 zero-randomized product `bgwMulStep` across all 3 parties recovers
`3 * 4 = 2 : ZMod 5`. -/
example :
    Polynomial.reconstruct params3.point
      (bgwMulStep params3 rA 3 rB 4 rZ) = (2 : ZMod 5) :=
  reconstruct_bgwMulStep_eq_mul params3 (by decide) rA 3 rB 4 rZ

/-- After BGW degree reduction, the 2-party coalition `{0, 2}` reconstructs `3 * 4 = 2 : ZMod 5`
from the degree-1 reduced shares. -/
example :
    reconstruct params3 ({0, 2} : Finset (Fin 3))
      (fun i : ({0, 2} : Finset (Fin 3)) =>
        bgwDegreeReduceShare params3
          (fun j k => share params3 (rSub j)
            (share params3 rA 3 j * share params3 rB 4 j) k) i) = (2 : ZMod 5) :=
  reconstruct_bgwDegreeReduceShare_mul_eq_mul params3 (by decide) rA rB 3 4 rSub (by decide)

/-! ### 3. Unauthorized-coalition marginal uniformity -/

/-- Singleton coalition `{0}` (`|{0}| = 1 ≤ threshold`) has a uniform marginal share distribution
for any secret in `ZMod 5`. -/
example (secret : ZMod 5) :
    (PMF.uniformOfFintype (Randomness params3)).map
      (fun coeffs (i : ({0} : Finset (Fin 3))) => share params3 coeffs secret i) =
    PMF.uniformOfFintype (({0} : Finset (Fin 3)) → ZMod 5) :=
  uniformOfFintype_map_restrict_share params3 {0} (by decide) secret

/-- Empty coalition `∅` marginal share distribution is uniform. -/
example (secret : ZMod 5) :
    (PMF.uniformOfFintype (Randomness params3)).map
      (fun coeffs (i : (∅ : Finset (Fin 3))) => share params3 coeffs secret i) =
    PMF.uniformOfFintype ((∅ : Finset (Fin 3)) → ZMod 5) :=
  uniformOfFintype_map_restrict_share params3 ∅ (by decide) secret

/-! ### 4. Synchronous BGW protocols: end-to-end execution and $1$-privacy -/

/-- End-to-end execution of `bgwDegreeReductionProtocol params3` on degree-1 shares of `3` and `4`:
a supported outcome exists and the 2-party coalition `{0, 1}` reconstructs `3 * 4 = 2 : ZMod 5`
from the protocol outputs. -/
example :
    ∃ res ∈ ((bgwDegreeReductionProtocol params3).evalWith noOracleWorld
        (fun i => (share params3 rA 3 i, share params3 rB 4 i))).support,
      reconstruct params3 ({0, 1} : Finset (Fin 3))
        (({0, 1} : Finset (Fin 3)).restrict res.2) = (2 : ZMod 5) := by
  obtain ⟨res, hres⟩ :=
    PMF.support_nonempty ((bgwDegreeReductionProtocol params3).evalWith noOracleWorld
      (fun i => (share params3 rA 3 i, share params3 rB 4 i)))
  refine ⟨res, hres, ?_⟩
  exact reconstruct_output_bgwDegreeReductionProtocol_eq_mul (s := {0, 1}) params3 (by decide)
    rA rB 3 4 hres (by decide)

/-- Coalition view simulation for `bgwDegreeReductionProtocol params3` on singleton coalition
`{0}`. -/
example (uv : Fin 3 → ZMod 5 × ZMod 5) :
    let I : Finset (Fin 3) := {0}
    ((bgwDegreeReductionProtocol params3).evalWith noOracleWorld uv).map (fun r => I.restrict r.1) =
      ProbComp.eval (bgwDegreeReductionViewSim params3 I (I.restrict uv)) :=
  map_restrict_evalWith_bgwDegreeReductionProtocol params3 {0} (by decide) uv

/-- End-to-end execution of `bgwSumProtocol params3` on `sampleInputs3 = ![3, 4, 2]`: a supported
execution exists and every party outputs `3 + 4 + 2 = 4 : ZMod 5`. -/
example :
    ∃ res ∈ ((bgwSumProtocol params3).evalWith noOracleWorld sampleInputs3).support,
      res.2 = ![4, 4, 4] := by
  obtain ⟨res, hres⟩ :=
    PMF.support_nonempty ((bgwSumProtocol params3).evalWith noOracleWorld sampleInputs3)
  refine ⟨res, hres, ?_⟩
  rw [output_bgwSumProtocol params3 sampleInputs3 hres]
  decide

/-- Full joint view-and-output $1$-privacy of `bgwSumProtocol params3` on singleton coalition `{1}`
and inputs `sampleInputs3`. -/
example :
    let I : Finset (Fin 3) := {1}
    ProbComp.eval (idealJoint (bgwSumFunctionality 3) I (bgwSumSim params3 I) sampleInputs3) =
      (bgwSumProtocol params3).realJoint noOracleWorld I sampleInputs3 :=
  perfectSemiHonestPrivateLe_bgwSum params3 {1} (by decide) sampleInputs3

/-- Edge case `I = ∅` for `perfectSemiHonestPrivateLe_bgwSum`. -/
example :
    let I : Finset (Fin 3) := ∅
    ProbComp.eval (idealJoint (bgwSumFunctionality 3) I (bgwSumSim params3 I) sampleInputs3) =
      (bgwSumProtocol params3).realJoint noOracleWorld I sampleInputs3 :=
  perfectSemiHonestPrivateLe_bgwSum params3 ∅ (by decide) sampleInputs3

/-- Zero `semiHonestAdvantage` for any distinguisher `D` against singleton coalition `{2}` in
`bgwSumProtocol params3`. -/
example (D : ((i : ({2} : Finset (Fin 3))) →
      PartyView (fun _ => ZMod 5) (fun _ => Randomness params3)
        (bgwSumSchedule 3 (ZMod 5)) i) × (Fin 3 → ZMod 5) → ProbComp Bool) :
    semiHonestAdvantage (bgwSumProtocol params3) noOracleWorld (bgwSumFunctionality 3)
      {2} (bgwSumSim params3 {2}) sampleInputs3 D = 0 :=
  (perfectSemiHonestPrivateLe_bgwSum params3).semiHonestAdvantage_eq_zero
    (by decide) sampleInputs3 D

end CslibFrontierTests.Crypto.BGW

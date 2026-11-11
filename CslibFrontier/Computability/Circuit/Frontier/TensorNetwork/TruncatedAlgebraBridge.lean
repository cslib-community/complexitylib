/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Cslib, bridge between `Polynomial.Truncated` and `TruncatedRing`)

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.TruncatedRing
public import CslibFrontier.Foundations.Data.Polynomial.TruncatedAlgebra
-- `import all` only to unfold unexposed `truncHom` and `truncRingHom` in bridge proofs.
import all CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Truncated
import all CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.TruncatedRing

/-!
# Bridge between `Polynomial.Truncated` and `B_{P,ℓ}`

Connects `Polynomial.Truncated (ZMod (2 ^ P)) ℓ` to `Cslib.Circuits.Frontier.truncHom P ℓ` and
`GaloisRingArith.Ring P (truncFl ℓ)` (`B_{P,ℓ} = (ℤ / 2 ^ P)[V] / (V ^ ℓ)` from
`TruncatedRing.lean`).

## Main definitions

* `Cslib.Circuits.Frontier.truncEquivTruncated`: ring isomorphism
  `Polynomial.Truncated (ZMod (2 ^ P)) ℓ ≃+* GaloisRingArith.Ring P (truncFl ℓ)`.

## Main results

* `Cslib.Circuits.Frontier.truncHom_eq_mk`: `truncHom P ℓ p = Polynomial.Truncated.mk ℓ (p.map _)`.
* `Cslib.Circuits.Frontier.truncEquivTruncated_mk`: compatibility with `truncRingHom P ℓ`.
-/

public section

namespace Cslib.Circuits.Frontier

open Polynomial GaloisRingArith

noncomputable section

/-- `truncHom P ℓ` lands directly in `Polynomial.Truncated (ZMod (2 ^ P)) ℓ` via
`Polynomial.Truncated.mk`. -/
theorem truncHom_eq_mk (P ℓ : ℕ) (p : ℕ[X]) :
    truncHom P ℓ p =
      Polynomial.Truncated.mk ℓ (p.map (Nat.castRingHom (ZMod (2 ^ P)))) := by
  rw [truncHom, RingHom.comp_apply, Polynomial.Truncated.mk_apply, Polynomial.coe_mapRingHom]

private noncomputable def toTruncatedRingHom (P ℓ : ℕ) :
    Polynomial.Truncated (ZMod (2 ^ P)) ℓ →+* Ring P (truncFl ℓ) :=
  Ideal.Quotient.lift (Ideal.span {(X : (ZMod (2 ^ P))[X]) ^ ℓ}) (AdjoinRoot.mk _) fun p hp => by
    rw [Ideal.mem_span_singleton] at hp
    rcases hp with ⟨q, rfl⟩
    rw [map_mul, ← map_monicOf_truncFl, AdjoinRoot.mk_self, zero_mul]

/-- Ring isomorphism between `Polynomial.Truncated (ZMod (2 ^ P)) ℓ` and
`GaloisRingArith.Ring P (truncFl ℓ) = B_{P,ℓ}`. -/
def truncEquivTruncated (P ℓ : ℕ) :
    Polynomial.Truncated (ZMod (2 ^ P)) ℓ ≃+* Ring P (truncFl ℓ) :=
  let invFun : Ring P (truncFl ℓ) →+* Polynomial.Truncated (ZMod (2 ^ P)) ℓ :=
    AdjoinRoot.lift (algebraMap (ZMod (2 ^ P)) _) (Polynomial.Truncated.var (ZMod (2 ^ P)) ℓ)
      (by simp [map_monicOf_truncFl, Polynomial.eval₂_X_pow])
  { toFun := toTruncatedRingHom P ℓ
    invFun := invFun
    left_inv x := by
      induction x using Polynomial.Truncated.induction_on with
      | hp p =>
        have hto : toTruncatedRingHom P ℓ (Polynomial.Truncated.mk ℓ p) = AdjoinRoot.mk _ p := by
          rw [toTruncatedRingHom, Polynomial.Truncated.mk_apply, Ideal.Quotient.lift_mk]
        change invFun (toTruncatedRingHom P ℓ (Polynomial.Truncated.mk ℓ p)) =
          Polynomial.Truncated.mk ℓ p
        rw [hto]
        change AdjoinRoot.lift (algebraMap (ZMod (2 ^ P)) _)
          (Polynomial.Truncated.var (ZMod (2 ^ P)) ℓ) _ (AdjoinRoot.mk _ p) =
            Polynomial.Truncated.mk ℓ p
        rw [AdjoinRoot.lift_mk, ← Polynomial.aeval_def, Polynomial.Truncated.var_eq_mk_X,
          Polynomial.aeval_algHom_apply (Polynomial.Truncated.mk ℓ) X p, Polynomial.aeval_X_left]
        rfl
    right_inv y := by
      induction y using AdjoinRoot.induction_on with
      | ih p =>
        have hinv : invFun (AdjoinRoot.mk _ p) = Polynomial.Truncated.mk ℓ p := by
          change AdjoinRoot.lift (algebraMap (ZMod (2 ^ P)) _)
            (Polynomial.Truncated.var (ZMod (2 ^ P)) ℓ) _ (AdjoinRoot.mk _ p) =
              Polynomial.Truncated.mk ℓ p
          rw [AdjoinRoot.lift_mk, ← Polynomial.aeval_def, Polynomial.Truncated.var_eq_mk_X,
            Polynomial.aeval_algHom_apply (Polynomial.Truncated.mk ℓ) X p, Polynomial.aeval_X_left]
          rfl
        change toTruncatedRingHom P ℓ (invFun (AdjoinRoot.mk _ p)) = AdjoinRoot.mk _ p
        rw [hinv, toTruncatedRingHom, Polynomial.Truncated.mk_apply, Ideal.Quotient.lift_mk]
    map_mul' := (toTruncatedRingHom P ℓ).map_mul
    map_add' := (toTruncatedRingHom P ℓ).map_add }

@[simp]
theorem truncEquivTruncated_mk (P ℓ : ℕ) (p : ℤ[X]) :
    truncEquivTruncated P ℓ
        (Polynomial.Truncated.mk ℓ (p.map (Int.castRingHom (ZMod (2 ^ P))))) =
      truncRingHom P ℓ p := by
  change toTruncatedRingHom P ℓ (Polynomial.Truncated.mk ℓ _) = truncRingHom P ℓ p
  rw [toTruncatedRingHom, Polynomial.Truncated.mk_apply, Ideal.Quotient.lift_mk, truncRingHom,
    RingHom.comp_apply, Polynomial.coe_mapRingHom]

end

end Cslib.Circuits.Frontier

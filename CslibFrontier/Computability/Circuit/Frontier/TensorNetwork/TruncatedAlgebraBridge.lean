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

private noncomputable def adjoinRootCongr {R : Type*} [CommRing R] {f g : R[X]} (h : f = g) :
    AdjoinRoot f ≃+* AdjoinRoot g :=
  h ▸ RingEquiv.refl (AdjoinRoot f)

private theorem adjoinRootCongr_mk {R : Type*} [CommRing R] {f g : R[X]} (h : f = g) (p : R[X]) :
    adjoinRootCongr h (AdjoinRoot.mk f p) = AdjoinRoot.mk g p := by
  subst h
  rfl

/-- Ring isomorphism between `Polynomial.Truncated (ZMod (2 ^ P)) ℓ` and
`GaloisRingArith.Ring P (truncFl ℓ) = B_{P,ℓ}`. -/
def truncEquivTruncated (P ℓ : ℕ) :
    Polynomial.Truncated (ZMod (2 ^ P)) ℓ ≃+* Ring P (truncFl ℓ) :=
  (Polynomial.Truncated.equivAdjoinRoot (ZMod (2 ^ P)) ℓ).toRingEquiv.trans
    (adjoinRootCongr map_monicOf_truncFl.symm)

@[simp]
theorem truncEquivTruncated_mk_zmod (P ℓ : ℕ) (p : (ZMod (2 ^ P))[X]) :
    truncEquivTruncated P ℓ (Polynomial.Truncated.mk ℓ p) =
      AdjoinRoot.mk (Polynomial.map (Int.castRingHom (ZMod (2 ^ P))) (monicOf (truncFl ℓ))) p := by
  simp [truncEquivTruncated, adjoinRootCongr_mk]

@[simp]
theorem truncEquivTruncated_symm_mk (P ℓ : ℕ) (p : (ZMod (2 ^ P))[X]) :
    (truncEquivTruncated P ℓ).symm
        (AdjoinRoot.mk
          (Polynomial.map (Int.castRingHom (ZMod (2 ^ P))) (monicOf (truncFl ℓ))) p) =
      Polynomial.Truncated.mk ℓ p :=
  (truncEquivTruncated P ℓ).symm_apply_eq.mpr (truncEquivTruncated_mk_zmod P ℓ p).symm

theorem truncEquivTruncated_mk (P ℓ : ℕ) (p : ℤ[X]) :
    truncEquivTruncated P ℓ
        (Polynomial.Truncated.mk ℓ (p.map (Int.castRingHom (ZMod (2 ^ P))))) =
      truncRingHom P ℓ p := by
  rw [truncEquivTruncated_mk_zmod, truncRingHom, RingHom.comp_apply, Polynomial.coe_mapRingHom]

end

end Cslib.Circuits.Frontier

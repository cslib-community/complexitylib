/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Circuit.Signature
public import Mathlib.Basic.FunLike.Basic

/-!
# Maps of signatures

A map of signatures `φ : σ.Hom τ` sends each operation of `σ` to an operation of `τ` of the same
arity. It is a map of the operation symbols, unlike cslib's `Homomorphism`, which maps the carriers
of two interpretations of one signature. `Signature.Hom.Preserves` asks that `φ` keep the meaning of
every operation. Circuits and formulas are translated along such maps in
`Cslib.Circuits.Circuit.mapOp`; word-RAM programs in `Cslib.WordRAM.Program.mapOp`.

## Main definitions

* `Cslib.Circuits.Signature.Hom`: an arity-preserving map of operations, with `Hom.id` and
  `Hom.comp`.
* `Cslib.Circuits.Signature.Hom.Preserves`: a map of operations keeps their meaning.

## Main results

* `Cslib.Circuits.Signature.Hom.comp_assoc`, `Cslib.Circuits.Signature.Hom.id_comp`,
  `Cslib.Circuits.Signature.Hom.comp_id`: maps of signatures form a category.
* `Cslib.Circuits.Signature.Hom.Preserves.comp`: meaning-preserving maps compose.
-/

@[expose] public section

namespace Cslib.Circuits

/-- A map of signatures: an arity-preserving map of operations. -/
structure Signature.Hom (σ τ : Signature) where
  /-- The image of each operation. -/
  toFun : σ.Op → τ.Op
  /-- Operations keep their arity. -/
  arity_eq : ∀ op, τ.Arity (toFun op) = σ.Arity op


variable {σ τ υ : Signature} {U : Type*}

namespace Signature.Hom

/-- Maps of signatures are applied like functions. -/
instance : FunLike (σ.Hom τ) σ.Op τ.Op where
  coe φ := φ.toFun
  coe_injective φ ψ h := by
    cases φ
    cases ψ
    congr

/-- `φ.toFun` is equal to the `FunLike` coercion `⇑φ`. -/
@[simp] theorem toFun_eq_coe (φ : σ.Hom τ) : φ.toFun = ⇑φ :=
  rfl

/-- Two maps of signatures agreeing on every operation are equal. -/
@[ext] theorem ext {φ ψ : σ.Hom τ} (h : ∀ op, φ op = ψ op) : φ = ψ :=
  DFunLike.ext φ ψ h

/-- The identity map of a signature. -/
protected def id (σ : Signature) : σ.Hom σ :=
  ⟨_root_.id, fun _ => rfl⟩

/-- The composition of maps of signatures. -/
def comp (ψ : τ.Hom υ) (φ : σ.Hom τ) : σ.Hom υ :=
  ⟨ψ ∘ φ, fun op => (ψ.arity_eq (φ op)).trans (φ.arity_eq op)⟩

/-- Applying the identity signature map returns the operation unchanged. -/
@[simp] theorem id_apply (op : σ.Op) : Hom.id σ op = op :=
  rfl

/-- Applying a composition of signature maps applies them in turn. -/
@[simp] theorem comp_apply (ψ : τ.Hom υ) (φ : σ.Hom τ) (op : σ.Op) : ψ.comp φ op = ψ (φ op) :=
  rfl

/-- Composing a signature map with the identity on the left gives the same map. -/
@[simp] theorem id_comp (φ : σ.Hom τ) : (Hom.id τ).comp φ = φ :=
  rfl

/-- Composing a signature map with the identity on the right gives the same map. -/
@[simp] theorem comp_id (φ : σ.Hom τ) : φ.comp (Hom.id σ) = φ :=
  rfl

/-- Composition of maps of signatures is associative. -/
theorem comp_assoc {ω : Signature} (χ : υ.Hom ω) (ψ : τ.Hom υ) (φ : σ.Hom τ) :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) :=
  rfl

/-- `φ` keeps the meaning of every operation: `op` means under `I` what `φ op` means under `J`. -/
class Preserves (φ : σ.Hom τ) (I : Interpretation σ U) (J : Interpretation τ U) : Prop where
  /-- The operation `φ op` means under `J` what `op` means under `I`. -/
  interpret_eq : ∀ op (x : Fin (σ.Arity op) → U),
    J (φ op) (fun a => x (Fin.cast (φ.arity_eq op) a)) = I op x

/-- The identity signature map preserves every interpretation. -/
instance preserves_id (I : Interpretation σ U) : (Hom.id σ).Preserves I I :=
  ⟨fun _ _ => rfl⟩

/-- A composition of meaning-preserving maps preserves meaning. -/
theorem Preserves.comp {I : Interpretation σ U} {J : Interpretation τ U}
    {K : Interpretation υ U} {ψ : τ.Hom υ} {φ : σ.Hom τ} (hψ : ψ.Preserves J K)
    (hφ : φ.Preserves I J) : (ψ.comp φ).Preserves I K :=
  ⟨fun op x => (hψ.interpret_eq (φ op) _).trans (hφ.interpret_eq op x)⟩

end Signature.Hom

end Cslib.Circuits

end

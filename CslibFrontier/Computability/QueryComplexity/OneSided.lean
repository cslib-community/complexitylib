/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.QueryComplexity.Measures

/-!
# One-sided query complexity measures and negation

For a value `b`, the one-sided measures `s_b(f)`, `bs_b(f)` and `C_b(f)` are the largest
sensitivity, block sensitivity and certificate complexity of `f` at an input of value `b`
(`BitString.sensitivityFor`, `QueryComplexity.blockSensitivityFor`,
`QueryComplexity.certificateComplexityFor`) [BuhrmanDeWolf2002].

Negation keeps sensitive coordinates, sensitive blocks and certificates, so it preserves `s`, `bs`
and `C` and exchanges the two values of the one-sided measures
(`BitString.sensitivityFor_not`, `QueryComplexity.blockSensitivityFor_not`,
`QueryComplexity.certificateComplexityFor_not`).

## Main definitions

* `Cslib.BitString.sensitivityFor`: the sensitivity `s_b(f)` of the inputs where `f` has value
  `b`.
* `Cslib.QueryComplexity.blockSensitivityFor`: the block sensitivity `bs_b(f)` of the inputs
  where `f` has value `b`.
* `Cslib.QueryComplexity.certificateComplexityFor`: the certificate complexity `C_b(f)` of the
  inputs where `f` has value `b`.

## Main results

* `Cslib.BitString.sensitivity_not`, `Cslib.QueryComplexity.blockSensitivity_not`,
  `Cslib.QueryComplexity.certificateComplexity_not`: negation preserves `s`, `bs` and `C`.
* `Cslib.BitString.sensitivityFor_not`, `Cslib.QueryComplexity.blockSensitivityFor_not`,
  `Cslib.QueryComplexity.certificateComplexityFor_not`: negation exchanges the two values of the
  one-sided measures.

## References

* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
-/

@[expose] public section

namespace Cslib

open Finset

variable {n : ℕ}

/-- Negation exchanges the inputs of value `b` and those of value `!b`. -/
private theorem filter_not_eq (f : BooleanFunction n) (b : Bool) :
    (univ.filter fun x => (!f x) = b) = univ.filter fun x => f x = !b := by
  ext x
  cases f x <;> cases b <;> simp

namespace BitString

/-- `s_b(f)`: the largest sensitivity of `f` at an input where it has value `b`. -/
def sensitivityFor (f : BooleanFunction n) (b : Bool) : ℕ :=
  (univ.filter fun x => f x = b).sup (sensitivityAt f)

/-- The sensitivity at an input of value `b` is at most `s_b(f)`. -/
theorem sensitivityAt_le_sensitivityFor {f : BooleanFunction n} {x : BitString n}
    {b : Bool} (h : f x = b) : sensitivityAt f x ≤ sensitivityFor f b :=
  le_sup (f := sensitivityAt f) (mem_filter.2 ⟨mem_univ x, h⟩)

/-- `s_b(f) ≤ s(f)`. -/
theorem sensitivityFor_le_sensitivity (f : BooleanFunction n) (b : Bool) :
    sensitivityFor f b ≤ sensitivity f :=
  sup_mono (filter_subset _ _)

/-- Negating a function keeps its sensitive coordinates. -/
@[simp]
theorem isSensitiveCoord_not {f : BooleanFunction n} {x : BitString n} {i : Fin n} :
    IsSensitiveCoord (fun y => !f y) x i ↔ IsSensitiveCoord f x i := by
  simp [IsSensitiveCoord]

/-- Negation preserves the sensitivity at an input. -/
theorem sensitivityAt_not (f : BooleanFunction n) (x : BitString n) :
    sensitivityAt (fun y => !f y) x = sensitivityAt f x := by
  unfold sensitivityAt sensitiveCoords
  congr 1
  ext i
  simp

/-- Negation preserves sensitivity. -/
theorem sensitivity_not (f : BooleanFunction n) :
    sensitivity (fun y => !f y) = sensitivity f := by
  rw [sensitivity, sensitivity, funext (sensitivityAt_not f)]

/-- Negation exchanges `s₀` and `s₁`. -/
theorem sensitivityFor_not (f : BooleanFunction n) (b : Bool) :
    sensitivityFor (fun y => !f y) b = sensitivityFor f (!b) := by
  rw [sensitivityFor, sensitivityFor, filter_not_eq, funext (sensitivityAt_not f)]

end BitString

open BitString

namespace QueryComplexity

variable {f : BooleanFunction n} {x : BitString n}

/-- `bs_b(f)`: the largest block sensitivity of `f` at an input where it has value `b`. -/
def blockSensitivityFor (f : BooleanFunction n) (b : Bool) : ℕ :=
  (univ.filter fun x => f x = b).sup (blockSensitivityAt f)

/-- The block sensitivity at an input of value `b` is at most `bs_b(f)`. -/
theorem blockSensitivityAt_le_blockSensitivityFor {b : Bool} (h : f x = b) :
    blockSensitivityAt f x ≤ blockSensitivityFor f b :=
  le_sup (f := blockSensitivityAt f) (mem_filter.2 ⟨mem_univ x, h⟩)

/-- `bs_b(f) ≤ bs(f)`. -/
theorem blockSensitivityFor_le_blockSensitivity (f : BooleanFunction n) (b : Bool) :
    blockSensitivityFor f b ≤ blockSensitivity f :=
  sup_mono (filter_subset _ _)

/-- `C_b(f)`: the largest certificate complexity of `f` at an input where it has value `b`. -/
def certificateComplexityFor (f : BooleanFunction n) (b : Bool) : ℕ :=
  (univ.filter fun x => f x = b).sup (certificateComplexityAt f)

/-- The certificate complexity at an input of value `b` is at most `C_b(f)`. -/
theorem certificateComplexityAt_le_certificateComplexityFor {b : Bool} (h : f x = b) :
    certificateComplexityAt f x ≤ certificateComplexityFor f b :=
  le_sup (f := certificateComplexityAt f) (mem_filter.2 ⟨mem_univ x, h⟩)

/-- `C_b(f) ≤ C(f)`. -/
theorem certificateComplexityFor_le_certificateComplexity (f : BooleanFunction n) (b : Bool) :
    certificateComplexityFor f b ≤ certificateComplexity f :=
  sup_mono (filter_subset _ _)

/-- Negating a function keeps its sensitive blocks. -/
@[simp]
theorem isSensitiveBlock_not {B : Block n} :
    IsSensitiveBlock (fun y => !f y) x B ↔ IsSensitiveBlock f x B := by
  simp [IsSensitiveBlock]

/-- Negating a function keeps its certificates. -/
@[simp]
theorem isCertificate_not {S : Finset (Fin n)} :
    IsCertificate (fun y => !f y) x S ↔ IsCertificate f x S := by
  simp [IsCertificate]

/-- Negation preserves the block sensitivity at an input. -/
theorem blockSensitivityAt_not (f : BooleanFunction n) (x : BitString n) :
    blockSensitivityAt (fun y => !f y) x = blockSensitivityAt f x := by
  have : sensitiveFamilies (fun y => !f y) x = sensitiveFamilies f x := by
    ext F
    simp [IsSensitiveFamily]
  rw [blockSensitivityAt, blockSensitivityAt, this]

/-- Negation preserves the certificate complexity at an input. -/
theorem certificateComplexityAt_not (f : BooleanFunction n) (x : BitString n) :
    certificateComplexityAt (fun y => !f y) x = certificateComplexityAt f x := by
  obtain ⟨S, hS, hSc⟩ := exists_isCertificate_card_eq f x
  obtain ⟨T, hT, hTc⟩ := exists_isCertificate_card_eq (fun y => !f y) x
  exact le_antisymm ((certificateComplexityAt_le (isCertificate_not.2 hS)).trans hSc.le)
    ((certificateComplexityAt_le (isCertificate_not.1 hT)).trans hTc.le)

/-- Negation preserves block sensitivity. -/
theorem blockSensitivity_not (f : BooleanFunction n) :
    blockSensitivity (fun y => !f y) = blockSensitivity f := by
  rw [blockSensitivity, blockSensitivity, funext (blockSensitivityAt_not f)]

/-- Negation preserves certificate complexity. -/
theorem certificateComplexity_not (f : BooleanFunction n) :
    certificateComplexity (fun y => !f y) = certificateComplexity f := by
  rw [certificateComplexity, certificateComplexity, funext (certificateComplexityAt_not f)]

/-- Negation exchanges `bs₀` and `bs₁`. -/
theorem blockSensitivityFor_not (f : BooleanFunction n) (b : Bool) :
    blockSensitivityFor (fun y => !f y) b = blockSensitivityFor f (!b) := by
  rw [blockSensitivityFor, blockSensitivityFor, filter_not_eq, funext (blockSensitivityAt_not f)]

/-- Negation exchanges `C₀` and `C₁`. -/
theorem certificateComplexityFor_not (f : BooleanFunction n) (b : Bool) :
    certificateComplexityFor (fun y => !f y) b = certificateComplexityFor f (!b) := by
  rw [certificateComplexityFor, certificateComplexityFor, filter_not_eq,
    funext (certificateComplexityAt_not f)]

end QueryComplexity

end Cslib

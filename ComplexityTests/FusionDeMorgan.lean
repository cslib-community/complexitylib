/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Fusion.DeMorgan

/-!
# Fusion bounds for De Morgan circuits

Two-gate De Morgan circuits compute NAND and NOR by negating an internal AND or OR gate. Only one
gate is binary, so the lower bound gives cover complexity at most one in both cases. A projection
has an empty cover, so the upper bound gives a De Morgan circuit within the stated budget. The
headline bounds are instantiated for an arbitrary function, and the dual-rail input circuit's
evaluation theorem is instantiated at `n = 2`.
-/

namespace ComplexityTests.FusionDeMorgan

open Cslib Cslib.Circuits Cslib.Circuits.Fusion Cslib.Circuits.Boolean

private def nand : BooleanFunction 2 := fun x => !(x 0 && x 1)

private def nandCircuit : Circuit Boolean.signature 2 1 :=
  ⟨(((Program.empty : Program Boolean.signature 2 0).gate ⟨.and, ![.input 0, .input 1]⟩).gate
    ⟨.not, ![.gate 0]⟩), fun _ => .gate 1⟩

private theorem nandCircuit_computes :
    nandCircuit.Computes Boolean.interpretation (single nand) := by
  unfold Circuit.Computes
  decide

example : nandCircuit.size = 2 := rfl

/-- Translating an internal negation does not increase the AND cost. -/
example : (Monotone.dualRail nandCircuit).program.cost Monotone.andCost = 1 := by
  rw [Monotone.cost_dualRail]
  rfl

/-- A negation of an internal gate is allowed by the De Morgan lower bound. -/
example : pairCoverComplexity {x | nand x = true}
    (fun i => {x | AltFormula.literals x i = true}) ≤ 1 :=
  pairCoverComplexity_le_binaryCost nandCircuit nandCircuit_computes

/-- The lower bound also holds for semi-ultrafilters. -/
example : pairCoverComplexity {x | nand x = true}
    (fun i => {x | AltFormula.literals x i = true}) Semifilter.IsUltra ≤ 1 :=
  pairCoverComplexity_le_binaryCost nandCircuit nandCircuit_computes _

/-- The ordinary gate-count bound no longer loses a factor of two. -/
example : pairCoverComplexity {x | nand x = true}
    (fun i => {x | AltFormula.literals x i = true}) ≤ 2 :=
  pairCoverComplexity_le_size nandCircuit nandCircuit_computes

private def nor : BooleanFunction 2 := fun x => !(x 0 || x 1)

private def norCircuit : Circuit Boolean.signature 2 1 :=
  ⟨(((Program.empty : Program Boolean.signature 2 0).gate ⟨.or, ![.input 0, .input 1]⟩).gate
    ⟨.not, ![.gate 0]⟩), fun _ => .gate 1⟩

private theorem norCircuit_computes :
    norCircuit.Computes Boolean.interpretation (single nor) := by
  unfold Circuit.Computes
  decide

/-- The negative rail of an OR contributes the one AND gate needed by NOR. -/
example : (Monotone.dualRail norCircuit).program.cost Monotone.andCost = 1 := by
  rw [Monotone.cost_dualRail]
  rfl

example : pairCoverComplexity {x | nor x = true}
    (fun i => {x | AltFormula.literals x i = true}) ≤ 1 :=
  pairCoverComplexity_le_binaryCost norCircuit norCircuit_computes

private def proj : BooleanFunction 1 := fun x => x 0

/-- The positive literal is exactly the target, so no witness exists and the empty list covers. -/
private def projCover : PairCover {x | proj x = true}
    (fun i => {x | AltFormula.literals x i = true}) where
  pairs := []
  isCover w _ := w.filter.not_apply_empty (by
    have h := w.above 0 w.point.property
    have hempty : Subtype.val ⁻¹' {x : BitString 1 | AltFormula.literals x 0 = true} =
        (∅ : Set ↥({x | proj x = true}ᶜ)) := by
      ext ⟨x, hx⟩
      have hx' : x 0 = false := by simpa [proj] using hx
      have hlit : AltFormula.literals x 0 = x 0 := rfl
      simp [hlit, hx']
    rwa [hempty] at h)

example : ∃ d : Circuit Boolean.signature 1 1, d.Computes Boolean.interpretation (single proj) ∧
    d.size ≤ 13 :=
  projCover.exists_computes_size_le

example (n : ℕ) (f : BooleanFunction n) :
    ∃ t : ℕ, pairCoverComplexity {x | f x = true}
        (fun i => {x | AltFormula.literals x i = true}) = t ∧
      t ≤ complexity Boolean.interpretation (single f) ∧
      complexity Boolean.interpretation (single f) ≤ 4 * (t + 1) ^ 2 * (2 * n + t + 1) + n :=
  pairCoverComplexity_complexity_bounds f

/-- Monotone AND complexity from literals is at most the square of the cover bound. -/
example : ecomplexityFrom Monotone.interpretation Monotone.andCost
    (fun x (_ : Fin 1) => nand x) AltFormula.literals ≤ 1 := by
  have h : pairCoverComplexity {x | nand x = true}
      (fun i => {x | AltFormula.literals x i = true}) ≤ 1 :=
    pairCoverComplexity_le_binaryCost nandCircuit nandCircuit_computes
  calc _ ≤ _ := (ecomplexityFrom_literals_bounds nand).2
    _ ≤ 1 ^ 2 := pow_le_pow_left₀ zero_le h 2
    _ = 1 := by norm_num

/-- The evaluation theorem of the dual-rail input circuit, instantiated at `n = 2`. -/
example : ∀ x : BitString 2, (Monotone.literalsRailCircuit 2).eval Monotone.interpretation
    (AltFormula.literals x) = Monotone.railBitString x :=
  Monotone.eval_literalsRailCircuit

example : (Monotone.literalsRailCircuit 3).program.cost Monotone.andCost = 0 :=
  Monotone.cost_literalsRailCircuit

end ComplexityTests.FusionDeMorgan

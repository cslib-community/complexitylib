/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.MCSP.Multi

/-!
# Tests: Multi-output MCSP and the constant-free De Morgan basis

Small instances of `MultiMCSP`: the component-major table bits and the length of the Definition 1
encoding, membership by an input wire and by one gate over every De Morgan basis, a negation that
needs a gate over every basis, and a constant that separates the constant-free basis from cslib's
basis with constants.
-/

namespace CslibFrontierTests.MultiMCSP

open Cslib Cslib.Circuits Cslib.MultiMCSP Turing.MultiTapeTM

/-! ### Table bits and the encoding -/

/-- Two components on one input, with threshold `1`. -/
def twoInst : MultiMCSP.Instance := ⟨1, 2, 1, ![![false, true], ![true, false]]⟩

/-- The table bits list component `0`, then component `1`. -/
example : twoInst.tableBits = [false, true, true, false] := by decide

/-- The encoding is `n`, `m` and `s` in unary, each framed, then the table bits. -/
example : encInstance twoInst =
    frame [true] ++ (frame [true, true] ++ (frame [true] ++ [false, true, true, false])) := by
  decide

/-- Its length is `2n + 2m + 2s + 3 + m · 2^n = 2 + 4 + 2 + 3 + 4`. -/
example : (encInstance twoInst).length = 15 := by
  rw [length_encInstance]
  rfl

example : twoInst.Positive := by decide

/-! ### Membership -/

/-- The projection `y ↦ y₀` on one input, as one component, with threshold `0`. -/
def projInst : MultiMCSP.Instance := ⟨1, 1, 0, fun _ => MCSP.truthTable 1 fun y => y 0⟩

/-- An input wire computes the projection without gates, over every basis. -/
example {σ : Signature} (I : Interpretation σ Bool) : projInst ∈ MultiMCSP I := by
  rw [mem_iff_exists_program_wires]
  exact ⟨0, .empty, le_rfl, fun _ => ⟨.input (0 : Fin 1),
    funext fun y => (congrFun ((MCSP.truthTable 1).symm_apply_apply fun y => y 0) y).symm⟩⟩

/-- Threshold `0` is not positive: `projInst` lies outside Definition 1 proper. -/
example : ¬ projInst.Positive := by decide

/-- Negation on one input, as one component, with threshold `s`. -/
def notInst (s : ℕ) : MultiMCSP.Instance := ⟨1, 1, s, fun _ => MCSP.truthTable 1 fun y => !y 0⟩

/-- Negation needs a gate over every basis: without gates every wire is an input. -/
example {σ : Signature} (I : Interpretation σ Bool) : notInst 0 ∉ MultiMCSP I := by
  rw [mem_iff_exists_program_wires]
  rintro ⟨g, p, hg, hw⟩
  obtain rfl : g = 0 := Nat.le_zero.1 hg
  obtain ⟨w, hw⟩ := hw (0 : Fin 1)
  cases w with
  | gate i => exact i.elim0
  | input j =>
    rw [Program.wireFunction_input] at hw
    have h := congrFun hw fun _ => false
    simp [notInst] at h

/-- The one-gate negation circuit over the constant-free basis. -/
def notCircuit : Circuit Boolean.DeMorgan.signature 1 1 :=
  ⟨Program.empty.gate ⟨.not, ![Wire.input 0]⟩, fun _ => Wire.gate 0⟩

theorem notCircuit_computes :
    notCircuit.Computes Boolean.DeMorgan.interpretation (notInst 1).function := by
  intro x
  funext i
  change _ = (MCSP.truthTable 1).symm (MCSP.truthTable 1 fun y => !y 0) x
  rw [Equiv.symm_apply_apply]
  exact Program.eval_gate_last Program.empty _ _ x

/-- One gate suffices for negation over every De Morgan basis, through its NOT gate. -/
example {σ : Signature} (I : Interpretation σ Bool) [Boolean.DeMorganBasis I] :
    notInst 1 ∈ MultiMCSP I :=
  mem_iff_exists_circuit.2
    ⟨notCircuit.mapOp (Boolean.DeMorganBasis.hom (I := I)), notCircuit_computes.mapOp, le_rfl⟩

/-! ### Constants and the two bases -/

/-- The constant `true` on zero inputs, as one component, with threshold `s`. -/
def constInst (s : ℕ) : MultiMCSP.Instance := ⟨0, 1, s, fun _ _ => true⟩

/-- Without constants and without inputs nothing is computable, at any threshold. -/
example (s : ℕ) : constInst s ∉ MultiMCSP Boolean.DeMorgan.interpretation := by
  intro h
  have htop : ecomplexity Boolean.DeMorgan.interpretation (constInst s).function = ⊤ :=
    Boolean.DeMorgan.ecomplexity_eq_top (m := 1) Nat.one_pos _
  have h' := mem_iff.1 h
  rw [htop] at h'
  exact absurd h' (by simp [constInst])

/-- With constants, one constant gate computes it. -/
example : constInst 1 ∈ MultiMCSP Boolean.interpretation :=
  mem_iff_exists_circuit.2
    ⟨⟨Program.empty.gate ⟨.const true, ![]⟩, fun _ => Wire.gate 0⟩, fun _ => funext fun _ => rfl,
      le_rfl⟩

/-- The constant-free basis is not complete. -/
example : ¬ Boolean.DeMorgan.interpretation.IsComplete := Boolean.DeMorgan.not_isComplete

/-! ### One output -/

/-- A single-output MCSP instance read through `ofMCSP`: the projection is in MCSP. -/
example : (⟨1, MCSP.truthTable 1 fun y => y 0, 0⟩ : MCSP.Instance) ∈ MCSP := by
  refine ofMCSP_mem_iff.1 (mem_iff_exists_program_wires.2 ?_)
  exact ⟨0, .empty, le_rfl, fun _ => ⟨.input (0 : Fin 1),
    funext fun y => (congrFun ((MCSP.truthTable 1).symm_apply_apply fun y => y 0) y).symm⟩⟩

end CslibFrontierTests.MultiMCSP

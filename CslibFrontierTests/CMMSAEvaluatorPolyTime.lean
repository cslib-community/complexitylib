/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.MCSP.PartialHardness.EvaluatorPolyTime

/-! Tests for the polynomial-time CMMSA table evaluator. -/

public section

namespace CslibFrontierTests.CMMSAEvaluatorPolyTime

open Cslib Cslib.Complexity Cslib.PartialMCSP.FromCMMSA Turing.MultiTapeTM

/-- With every variable function constantly `false`, the empty list has the table of every
variable, so the partial MCSP instance is polynomial-time in the CMMSA instance alone. -/
example (Δ k P : ℕ) :
    ComputableInPolyTime (fun I : CMMSAInstance => toInstance I Δ k 1 P fun _ _ => false)
      CMMSAInstance.encoding PartialMCSP.enc :=
  computableInPolyTime_toInstance (T := fun _ => []) Δ k P ComputableInPolyTime.id'
    (ComputableInPolyTime.const 1) (ComputableInPolyTime.const []) fun _ v y => by
      simp [evalVar]

/-- The per-entry parity composes with projections out of a larger context by `fun_prop`: here the
instance, `λ` and the tables form one component and the input `x` and the term `t` another. -/
example (Δ k : ℕ) :
    ComputableInPolyTime
      (fun p : ((CMMSAInstance × ℕ) × List (List Bool)) × (ℕ × ℕ) =>
        termParityN p.1.1.1 Δ k p.1.1.2 p.1.2 p.2.1 p.2.2)
      (encPair (encPair (encPair CMMSAInstance.encoding encUnary) (encList encBits))
        (encPair encNat encUnary)) encBool := by
  fun_prop

/-- The same context gives the entries. -/
example (Δ k : ℕ) :
    ComputableInPolyTime
      (fun p : ((CMMSAInstance × ℕ) × List (List Bool)) × ℕ =>
        entryN p.1.1.1 Δ k p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair CMMSAInstance.encoding encUnary) (encList encBits)) encNat)
      (encOption encBool) := by
  fun_prop

/-- The shape a client mapping over the entries meets: an abstract context with the instance,
`λ` and the tables given by certificates, and the input `x` arriving in unary from `mapWithInput`
over `List.range`. -/
example {γ : Type} {enc : γ ↪ List Bool} {I : γ → CMMSAInstance} {lam : γ → ℕ}
    {T : γ → List (List Bool)} (Δ k : ℕ)
    (hI : ComputableInPolyTime I enc CMMSAInstance.encoding)
    (hlam : ComputableInPolyTime lam enc encUnary)
    (hT : ComputableInPolyTime T enc (encList encBits)) :
    ComputableInPolyTime
      (fun p : γ × (ℕ × ℕ) => termParityN (I p.1) Δ k (lam p.1) (T p.1) p.2.1 p.2.2)
      (encPair enc (encPair encUnary encUnary)) encBool := by
  fun_prop

/-- The bound on the number of entries holds for every instance, here one with no formulas and a
weight of `0`. -/
example (Δ k lam : ℕ) : 2 ^ inputLength ⟨[0], 0, []⟩ Δ k lam ≤ 2 * (2 ^ k * 2) ^ (Δ * Δ) := by
  have h : maxWeight ⟨[0], 0, []⟩ = 0 := Nat.le_zero.1 (maxWeight_le (by simp))
  simpa [h] using two_pow_inputLength_le ⟨[0], 0, []⟩ Δ k lam

end CslibFrontierTests.CMMSAEvaluatorPolyTime

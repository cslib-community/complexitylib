/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

import Complexity.Computability.Complexity.FineGrained.CountingEndpoint
import Complexity.Computability.Complexity.FineGrained.CountingSparsification
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Private downstream preparation for the native counting endpoint

Unaggregated author preparation under #1226. The accepted guarded declared-count contract,
including independent time and polynomial space in the original external input, remains an
explicit premise. No counter or unconditional complexity-class endpoint is supplied here.

The preparation `φ ↦ (φ.numVars, φ)` is charged in `encCNF φ`. Its semantics are used only on
dense formulas; the existing `CountingEndpoint` bridge performs dense relabeling for arbitrary
variable labels. Independent resource bounds are widened only for this downstream bridge.
All definitions and results below are private, pending the final unconditional construction.
-/

namespace Cslib.Complexity.CountingNativeEndpointConsequencesPrep

open Cslib.Logic.PL Turing.MultiTapeTM CountingSparsify SubexponentialSAT
open Cslib.Logic.PL.CNF (validDeclaredInput validDeclaredInput_eq_true_iff)

private abbrev Input := ℕ × CNF ℕ
private abbrev encInput := encPair encUnary encCNF
private def declareInput (φ : CNF ℕ) : Input := (φ.numVars, φ)

private theorem computableInPolyTime_declareInput :
    ComputableInPolyTime declareInput encCNF encInput := by
  unfold declareInput
  fun_prop

private theorem length_declareInput (φ : CNF ℕ) :
    (encInput (declareInput φ)).length + 1 ≤ 3 * ((encCNF φ).length + 1) := by
  have hn := φ.numVars_le_length_vars.trans (SAT.length_vars_le φ)
  simp only [declareInput, encInput, length_encPair, encUnary_apply, List.length_replicate]
  omega

private theorem dense_spec {k : ℕ} {count : Input → ℕ}
    (hspec : ∀ x, count x = if validDeclaredInput k x.1 x.2 then
      x.2.modelCountOn (Finset.range x.1) else 0)
    {ψ : CNF ℕ} (hw : ∀ cl ∈ ψ, cl.length ≤ k)
    (hdense : ψ.vars.toFinset = Finset.range ψ.numVars) :
    count (declareInput ψ) = ψ.modelCountOn (Finset.range ψ.numVars) := by
  have hv := validDeclaredInput_eq_true_iff.mpr ⟨hw, hdense.subset⟩
  simpa only [declareInput, hv, ↓reduceIte] using hspec (declareInput ψ)

/-- Construct the common allowance needed by the existing dense-counting bridge only after
charging preparation and transferring the independent workspace bound to `encCNF`. -/
private theorem exists_common_dense_resources {count : Input → ℕ} {T S : Input → ℕ}
    (hcount : ComputableInO count encInput encNat T S) {A c e a b : ℕ}
    (hT : ∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
      (((encInput x).length : ℝ) + 1) ^ e) + c)
    (hS : ∀ x, S x ≤ a * ((encInput x).length + 1) ^ b) :
    ∃ t : CNF ℕ → ℕ, ∃ C E : ℕ,
      ComputableInO (fun φ => count (declareInput φ)) encCNF encNat t t ∧
      ∀ φ, (t φ : ℝ) ≤ C * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars) *
        (((encCNF φ).length : ℝ) + 1) ^ E) + C := by
  obtain ⟨d, _, hp⟩ := computableInPolyTime_declareInput.tidy.exists_degree
  have hcomp := hcount.comp (ComputableInO.of_tidy hp.inO)
  let P (φ : CNF ℕ) := ((encCNF φ).length + 1) ^ d + S (declareInput φ)
  have hspace : PolyBounded (fun x => (encInput x).length) S :=
    PolyBounded.of_forall_le a b hS
  have hP : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) P :=
    ((PolyBounded.self.add (.const 1)).pow d).add
      (hspace.comp computableInPolyTime_declareInput.polyBounded_length)
  obtain ⟨p, q, hP⟩ := hP.exists_le
  let t (φ : CNF ℕ) := P φ + T (declareInput φ)
  let C := p + c * 3 ^ e + c
  refine ⟨t, C, q + e, hcomp.mono_le (fun φ => ?_) (fun φ => ?_), fun φ => ?_⟩
  · dsimp only [t, P]
    omega
  · dsimp only [t, P]
    omega
  · let Y : ℝ := (encCNF φ).length + 1
    let X : ℝ := (2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars)
    have hY : 1 ≤ Y := by dsimp [Y]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hX : 1 ≤ X :=
      Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg A) (interpolationScale_nonneg _))
    have hYq : Y ^ q ≤ Y ^ (q + e) := pow_le_pow_right₀ hY (by omega)
    have hYe : Y ^ e ≤ Y ^ (q + e) := pow_le_pow_right₀ hY (by omega)
    have hYP : Y ^ (q + e) ≤ X * Y ^ (q + e) :=
      le_mul_of_one_le_left (by positivity) hX
    have hPr : (P φ : ℝ) ≤ p * Y ^ q := by
      dsimp only [Y]
      exact_mod_cast hP φ
    have hlen : ((encInput (declareInput φ)).length : ℝ) + 1 ≤ 3 * Y := by
      dsimp only [Y]
      exact_mod_cast length_declareInput φ
    have hpower : (((encInput (declareInput φ)).length : ℝ) + 1) ^ e ≤
        (3 : ℝ) ^ e * Y ^ (q + e) := by
      calc
        _ ≤ (3 * Y) ^ e := pow_le_pow_left₀ (by positivity) hlen e
        _ = 3 ^ e * Y ^ e := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hYe (by positivity)
    have hPfinal : (P φ : ℝ) ≤ p * (X * Y ^ (q + e)) :=
      hPr.trans (mul_le_mul_of_nonneg_left (hYq.trans hYP) (Nat.cast_nonneg p))
    have hTfinal : (T (declareInput φ) : ℝ) ≤
        (c : ℝ) * 3 ^ e * (X * Y ^ (q + e)) + c := by
      have hT' := hT (declareInput φ)
      change (T (declareInput φ) : ℝ) ≤
        c * (X * (((encInput (declareInput φ)).length : ℝ) + 1) ^ e) + c at hT'
      refine hT'.trans ?_
      have hmul := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpower (by positivity : 0 ≤ X)) (Nat.cast_nonneg c)
      nlinarith
    have hc : (c : ℝ) ≤ C := by exact_mod_cast (show c ≤ C by dsimp [C]; omega)
    have hcoeff : (p : ℝ) + c * 3 ^ e ≤ C := by
      exact_mod_cast (show p + c * 3 ^ e ≤ C by dsimp [C]; omega)
    have hfactor : 0 ≤ X * Y ^ (q + e) := by positivity
    change ((P φ + T (declareInput φ) : ℕ) : ℝ) ≤ C * (X * Y ^ (q + e)) + C
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hcoeff hfactor]

private theorem KSAT_of_declared_contract {k : ℕ} {count : Input → ℕ} {T S : Input → ℕ}
    (hcount : ComputableInO count encInput encNat T S)
    (hspec : ∀ x, count x = if validDeclaredInput k x.1 x.2 then
      x.2.modelCountOn (Finset.range x.1) else 0) {A c e a b : ℕ}
    (hT : ∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
      (((encInput x).length : ℝ) + 1) ^ e) + c)
    (hS : ∀ x, S x ≤ a * ((encInput x).length + 1) ^ b) :
    DecidableInSubexpTime (KSAT k) encCNF CNF.numVars := by
  obtain ⟨t, C, E, hc, ht⟩ := exists_common_dense_resources hcount hT hS
  exact DecidableInSubexpTime.KSAT_of_dense_modelCount_interpolationScale hc
    (fun _ hw hdense => dense_spec hspec hw hdense) ht

/-- The complete accepted contract is still a premise here. These downstream consequences become
unconditional only when the native construction supplies that contract for every fixed width. -/
private theorem consequences_of_declared_contract
    (h : ∀ k : ℕ, ∃ count : Input → ℕ, ∃ T S : Input → ℕ, ∃ A c e a b : ℕ,
      ComputableInO count encInput encNat T S ∧
      (∀ x, count x = if validDeclaredInput k x.1 x.2 then
        x.2.modelCountOn (Finset.range x.1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
        (((encInput x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encInput x).length + 1) ^ b)) :
    (∀ k, satExponent k = 0) ∧ ¬ETH ∧ ¬SETH := by
  have hSAT (k : ℕ) : DecidableInSubexpTime (KSAT k) encCNF CNF.numVars := by
    obtain ⟨count, T, S, A, c, e, a, b, hc, hspec, hT, hS⟩ := h k
    exact KSAT_of_declared_contract hc hspec hT hS
  exact ⟨fun k => satExponent_eq_zero_of_decidableInSubexpTime (hSAT k),
    not_ETH_of_decidableInSubexpTime (hSAT 3), not_SETH_of_forall_decidableInSubexpTime hSAT⟩

end Cslib.Complexity.CountingNativeEndpointConsequencesPrep

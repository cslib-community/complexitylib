/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.ProofSystem
import Complexity.Computability.Complexity.Problems.SAT.PolyTime

/-!
# Tests: proof systems

A concrete proof system on all words and its simulations; the proof system of the `SAT` verifier
on accepted and rejected certificates; total decoding of a malformed word; the existence of a
polynomially bounded proof system for `SAT`; and the axioms of the headline theorems.
-/

namespace ComplexityTests.ProofComplexity

open Cslib Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Proof systems and simulations -/

/-- Every word proves itself: a polynomially bounded proof system for the set of all words. -/
def wordsProofSystem : ProofSystem encBits Set.univ where
  toFun π := π
  computable := .id'
  range_eq := Set.range_id

example : wordsProofSystem [true, false] = [true, false] := rfl

example : wordsProofSystem.PolynomiallyBounded :=
  ⟨.X, fun a _ => ⟨a, rfl, by simp [encBits]⟩⟩

example : wordsProofSystem.PSimulates wordsProofSystem := .refl

/-- A polynomial-time translation gives a p-simulation. -/
example : wordsProofSystem.PSimulates wordsProofSystem :=
  ⟨id, .id', fun _ => rfl⟩

example : wordsProofSystem.Simulates wordsProofSystem := ProofSystem.PSimulates.refl.simulates

/-! ### The proof system of the `SAT` verifier -/

/-- `(x₀ ∨ ¬x₁) ∧ x₁`. -/
private def φ : CNF ℕ := [[(0, true), (1, false)], [(1, true)]]

/-- `x₀ ∧ ¬x₀`. -/
private def ψ : CNF ℕ := [[(0, true)], [(0, false)]]

/-- Proofs of satisfiability: a formula followed by an assignment, in order of first occurrence,
padded to the length of the encoded formula. A proof the verifier rejects proves `φ`. -/
private noncomputable def satProofSystem : ProofSystem encCNF SAT :=
  .ofVerifier cnfDecoder SAT.computableInPolyTime_verifier SAT.isVerifier
    (a₀ := φ) ⟨fun _ => true, rfl⟩

/-- The assignment `x₀ ↦ true`, `x₁ ↦ true`, padded, proves `φ`. -/
example : satProofSystem (frame (encCNF φ) ++
    ([true, true] ++ List.replicate ((encCNF φ).length - 2) false)) = φ :=
  ProofSystem.ofVerifier_frame_append _ _ _ _ (by
    have h : 2 ≤ (encCNF φ).length := by decide
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate,
      Polynomial.eval_X]
    omega) rfl

/-- No certificate satisfies `ψ`, so a word starting with `ψ` proves the default formula `φ`. -/
example (w : List Bool) : satProofSystem (frame (encCNF ψ) ++ w) = φ := by
  have hψ : ¬ ψ.Satisfiable := fun ⟨σ, h⟩ => by
    cases h0 : σ 0 <;> simp [ψ, CNF.eval, Clause.eval, Literal.eval, h0] at h
  change (if _ then _ else _) = φ
  rw [ite_eq_right_iff]
  simp only [ProofSystem.verifierAccepts, ProofSystem.verifierInstance, unframe_frame_append,
    cnfDecoder.decode_enc, dropFrame_frame_append, Bool.and_eq_true]
  exact fun h => absurd ⟨_, h.1⟩ hψ

/-- `SAT` has a polynomially bounded proof system. -/
example : ∃ P : ProofSystem encCNF SAT, P.PolynomiallyBounded :=
  (ProofSystem.exists_polynomiallyBounded_iff_mem_NP (L := SAT) cnfDecoder
    ⟨φ, fun _ => true, rfl⟩).2
    SAT.mem_NP

/-! ### Total decoding of malformed words -/

private def bitsDecoder : Decoder encBits where
  decode := id
  decode_enc _ := rfl
  computable := ⟨1, 1, .of_eq fun _ => rfl⟩

private theorem isVerifier_univ :
    IsVerifier encBits 0 (fun _ => true) (Set.univ : Set (List Bool)) := by
  intro a
  constructor
  · intro _
    exact ⟨[], by simp, rfl⟩
  · intro _
    trivial

/-- Every decoded word is accepted with an empty certificate; the default is `[true]`. -/
private noncomputable def decodedWordsProofSystem : ProofSystem encBits Set.univ :=
  .ofVerifier bitsDecoder (.const true) isVerifier_univ (a₀ := [true]) (Set.mem_univ _)

/-- The empty word has no framed instance, but total decoding still accepts it. -/
example : ¬ ∃ a w : List Bool, frame a ++ w = [] := by
  rintro ⟨a, w, h⟩
  have := congrArg List.length h
  simp [length_frame] at this

private theorem decodedWordsProofSystem_nil : decodedWordsProofSystem [] = [] := by
  change (if ProofSystem.verifierAccepts bitsDecoder 0 (fun _ => true) [] then _ else _) = []
  simp [ProofSystem.verifierAccepts, ProofSystem.verifierInstance, dropFrame, unframe,
    bitsDecoder]

/-- A malformed proof can prove the decoded instance instead of the default. -/
example : decodedWordsProofSystem [] ≠ [true] := by
  rw [decodedWordsProofSystem_nil]
  decide

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.ProofSystem.NP_eq_coNP_iff_exists_polynomiallyBounded' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ProofSystem.NP_eq_coNP_iff_exists_polynomiallyBounded

/--
info: 'Cslib.Complexity.ProofSystem.coNP_subset_NP_iff_exists_polynomiallyBounded' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ProofSystem.coNP_subset_NP_iff_exists_polynomiallyBounded

/--
info: 'Cslib.Complexity.ProofSystem.exists_polynomiallyBounded_iff_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ProofSystem.exists_polynomiallyBounded_iff_mem_NP

/--
info: 'Cslib.Complexity.ProofSystem.PolynomiallyBounded.of_simulates' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ProofSystem.PolynomiallyBounded.of_simulates

/--
info: 'Cslib.Complexity.ProofSystem.PSimulates.simulates' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ProofSystem.PSimulates.simulates

end ComplexityTests.ProofComplexity

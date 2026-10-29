/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.Leveled.Bootstrapping
import Complexity.Crypto.Computational.Homomorphic.FixedKey.Bootstrapping
import ComplexityTests.Crypto.HomomorphicExample

/-!
Clients of the conditional bootstrapping endpoints. Arbitrary bounded depth families need no
computability assumption, and a polynomial majorant must cover their finite prefixes. Security
is assumed only for a generic base scheme. The explicitly insecure tagged fixture separately
inhabits the correctness, native runtime and compactness hypotheses; it is never assumed secure.
The common decryption witnesses precede the quantifier over all budgets and cover malformed
words of the prescribed lengths.
-/

namespace ComplexityTests.Bootstrapping

open Cslib Cslib.Circuits Cslib.Crypto Cslib.Crypto.Homomorphic Cslib.Probability
  Turing.MultiTapeTM
open ComplexityTests.HomomorphicExample

open scoped Classical in
private noncomputable def predicateDepth (P : ℕ → Prop) (n : ℕ) : ℕ :=
  if P n then n + 1 else 0

private theorem predicateDepth_bounded (P : ℕ → Prop) :
    PolynomiallyBounded (predicateDepth P) := by
  refine (show PolynomiallyBounded (fun n => n + 1) by fun_prop).mono_of_le ?_
  intro n
  classical
  simp only [predicateDepth]
  split_ifs <;> omega

-- The eventual bound below sees none of this large finite prefix.
private def spikedDepth (n : ℕ) : ℕ := if n < 100 then 1000000000000 else n

private theorem spikedDepth_bounded : PolynomiallyBounded spikedDepth := by
  refine ⟨1, Filter.eventually_atTop.2 ⟨100, ?_⟩⟩
  intro n hn
  simp [spikedDepth, Nat.not_lt.mpr hn]

section ConditionalSecurity

variable {E : Scheme} {secretWidth ciphertextWidth : ℕ → ℕ}
  (D : DecryptionCircuits E secretWidth ciphertextWidth)
  (hE : E.Correct) (hwidth : E.FixedWidth secretWidth ciphertextWidth)
  (hboot : Scheme.Bootstrappable D)
  (hsecure : Encryption.INDCPA E.keyGen E.encrypt)
  (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
  (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => E.encrypt p.1 p.2.1 p.2.2))
  (hevaluate : IsPPTOn
    (encPair encUnary (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))))
    encBits (fun p => E.evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
  (hD : ComputableInPolyTime
    (fun n => (⟨_, D.circuit n⟩ : Σ m, Circuit Boolean.signature m 1))
    encUnary (Boolean.encCircuit 1))

-- P is arbitrary: no decidability, computability or native certificate is required for it.
-- All properties concern the same constructed scheme, with ordinary base IND-CPA only.
example (P : ℕ → Prop) :
    ∃ budget : ℕ → ℕ,
      ComputableInPolyTime budget encUnary encUnary ∧
      (∀ n, predicateDepth P n ≤ budget n) ∧
      (Leveled.scheme D budget).Correct ∧
      (∀ n c, c.2.depth ≤ predicateDepth P n → (Leveled.scheme D budget).permitted n c) ∧
      (Leveled.scheme D budget).FixedWidth (fun n => 3 * secretWidth n + 1)
        (fun n => ciphertextWidth n + 1) ∧
      PolynomiallyBounded (fun n => 3 * secretWidth n + 1) ∧
      PolynomiallyBounded (fun n => ciphertextWidth n + 1) ∧
      IsPPTOn encUnary (encPair encBits encBits) (Leveled.scheme D budget).keyGen ∧
      IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
        (fun p => (Leveled.scheme D budget).encrypt p.1 p.2.1 p.2.2) ∧
      ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => (Leveled.scheme D budget).decrypt p.1 p.2.1 p.2.2)
        (encPair encUnary (encPair encBits encBits)) encBool ∧
      IsPPTOn
        (encPair encUnary (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))))
        encBits (fun p => (Leveled.scheme D budget).evaluate p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
      Encryption.INDCPA (Leveled.scheme D budget).keyGen (Leveled.scheme D budget).encrypt :=
  Leveled.exists_scheme_of_polynomiallyBounded D hE hwidth hboot hsecure hkeyGen hencrypt
    hevaluate hD (predicateDepth_bounded P)

-- An eventual degree-one bound cannot justify silently discarding the first 100 parameters.
example : ∃ budget : ℕ → ℕ,
    ComputableInPolyTime budget encUnary encUnary ∧
    1000000000000 ≤ budget 0 ∧
    (∀ n, spikedDepth n ≤ budget n) ∧
    (Leveled.scheme D budget).Correct ∧
    Encryption.INDCPA (Leveled.scheme D budget).keyGen (Leveled.scheme D budget).encrypt := by
  obtain ⟨budget, hbudget, hdom, hcorrect, _, _, _, _, _, _, _, _, hsecurity⟩ :=
    Leveled.exists_scheme_of_polynomiallyBounded D hE hwidth hboot hsecure hkeyGen hencrypt
      hevaluate hD spikedDepth_bounded
  exact ⟨budget, hbudget, by simpa [spikedDepth] using hdom 0, hdom, hcorrect, hsecurity⟩

-- Without a separate computability hypothesis on `secretWidth`, `exists_decrypt_circuits` still
-- gives a single polynomial-size decryption circuit family across all budgets.
example (P : ℕ → Prop) :
    ∃ circuits : ∀ n, Circuit Boolean.signature
        ((3 * secretWidth n + 1) + (ciphertextWidth n + 1)) 1,
      PolynomiallyBounded (fun n => (circuits n).size) ∧
      ∀ n (sk ciphertext : List Bool),
        sk.length = 3 * secretWidth n + 1 →
        ciphertext.length = ciphertextWidth n + 1 →
        (circuits n).eval Boolean.interpretation
            (BitString.ofList ((3 * secretWidth n + 1) + (ciphertextWidth n + 1))
              (sk ++ ciphertext)) 0 =
          (Leveled.scheme D (predicateDepth P)).decrypt n sk ciphertext := by
  obtain ⟨circuits, hsize, hcorrect⟩ := Leveled.exists_decrypt_circuits D hD
  exact ⟨circuits, hsize, hcorrect (predicateDepth P)⟩

end ConditionalSecurity

-- This fixture is insecure. These are concrete instances of every non-security input
-- hypothesis, including an actual uniformly generated decryption circuit.
example : tagged.Correct ∧ tagged.FixedWidth (fun _ => 1) (fun _ => 2) ∧
    Scheme.Bootstrappable decryptionCircuits ∧
    IsPPTOn encUnary (encPair encBits encBits) tagged.keyGen ∧
    IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => tagged.encrypt p.1 p.2.1 p.2.2) ∧
    IsPPTOn
      (encPair encUnary (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))))
      encBits (fun p => tagged.evaluate p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
    ComputableInPolyTime
      (fun n => (⟨_, decryptionCircuits.circuit n⟩ : Σ m, Circuit Boolean.signature m 1))
      encUnary (Boolean.encCircuit 1) :=
  ⟨tagged_correct, tagged_width, tagged_bootstrappable, keyGen_ppt, encrypt_ppt,
    evaluate_ppt, circuits_poly⟩

-- Actual correctness and exact compact widths hold even for a predicate-dependent budget.
example (P : ℕ → Prop) :
    (Leveled.scheme decryptionCircuits (predicateDepth P)).Correct ∧
    (Leveled.scheme decryptionCircuits (predicateDepth P)).FixedWidth (fun _ => 4) (fun _ => 3) :=
  ⟨Leveled.correct decryptionCircuits tagged_correct tagged_width tagged_bootstrappable _,
    Leveled.fixedWidth decryptionCircuits tagged_correct tagged_width tagged_bootstrappable _⟩

-- One native decryption certificate works across all budgets and all input serializations.
example : ∃ (time space : ℕ × List Bool × List Bool → ℕ) (bound : ℕ → ℕ),
    PolynomiallyBounded bound ∧
    (∀ budget : ℕ → ℕ, ComputableInTimeAndSpace
      (fun p : ℕ × List Bool × List Bool =>
        (Leveled.scheme decryptionCircuits budget).decrypt p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBool time space) ∧
    ∀ n (sk ciphertext : List Bool), sk.length = 4 → ciphertext.length = 3 →
      time (n, sk, ciphertext) ≤ bound n ∧ space (n, sk, ciphertext) ≤ bound n :=
  Leveled.exists_decrypt_parameter_bound decryptionCircuits circuits_poly

-- The same uniformly generated polynomial-size circuit family implements the complete decoder
-- and tag selection for every budget, not only the base XOR circuit or only supported secrets.
example : ∃ circuits : ℕ → Circuit Boolean.signature 7 1,
    ComputableInPolyTime
      (fun n => (⟨7, circuits n⟩ : Σ m, Circuit Boolean.signature m 1))
      encUnary (Boolean.encCircuit 1) ∧
    PolynomiallyBounded (fun n => (circuits n).size) ∧
    ∀ (budget : ℕ → ℕ) n (sk ciphertext : List Bool),
      sk.length = 4 → ciphertext.length = 3 →
      (circuits n).eval Boolean.interpretation (BitString.ofList 7 (sk ++ ciphertext)) 0 =
        (Leveled.scheme decryptionCircuits budget).decrypt n sk ciphertext :=
  Leveled.exists_uniform_decrypt_circuits decryptionCircuits circuits_poly (by fun_prop)

private def malformedSecret : List Bool := [true, true, true, true]

-- The four-bit word has the required total length but no terminating frame marker. Its
-- decoded endpoints have lengths two and zero, not the base scheme's required one and one.
example : malformedSecret.length = 4 ∧
    Leveled.secretKeyDecoder.decode malformedSecret = ([true, true], []) := by
  decide +kernel

example : ∃ circuits : ℕ → Circuit Boolean.signature 7 1,
    ComputableInPolyTime
      (fun n => (⟨7, circuits n⟩ : Σ m, Circuit Boolean.signature m 1))
      encUnary (Boolean.encCircuit 1) ∧
    PolynomiallyBounded (fun n => (circuits n).size) ∧
    ∀ (budget : ℕ → ℕ) n,
      (circuits n).eval Boolean.interpretation
          (BitString.ofList 7 (malformedSecret ++ [true, true, false])) 0 =
        (Leveled.scheme decryptionCircuits budget).decrypt n malformedSecret
          [true, true, false] := by
  obtain ⟨circuits, hgen, hsize, hcorrect⟩ :=
    Leveled.exists_uniform_decrypt_circuits decryptionCircuits circuits_poly
      (by fun_prop)
  exact ⟨circuits, hgen, hsize, fun budget n => hcorrect budget n _ _ rfl rfl⟩

end ComplexityTests.Bootstrapping

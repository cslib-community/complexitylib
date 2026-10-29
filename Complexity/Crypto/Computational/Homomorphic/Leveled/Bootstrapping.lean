/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Leveled.Correctness
public import Complexity.Crypto.Computational.Homomorphic.Leveled.Security
public import Complexity.Crypto.Computational.Homomorphic.Leveled.Compactness

/-!
# Correct, compact and secure acyclic leveled encryption

The independently proved correctness, exact width, native runtime and IND-CPA results apply to
the same constructed scheme. This module assembles correctness, budget-independent polynomial
widths and security without assuming those conclusions for the output scheme. Native certificates
for its algorithms remain available in `Leveled.PolyTime`.

`Leveled.exists_decrypt_circuits`, `Leveled.exists_uniform_decrypt_circuits` and
`Leveled.exists_decrypt_parameter_bound` give one decryption circuit family (with a native
polynomial-time circuit generator when `secretWidth` is computable in polynomial time in unary) and
one parameter-only resource bound shared by all budgets. These include the complete tagged decoder
and are chosen independently of the requested depth family.

The contract evaluates fresh ciphertexts under an efficiently computed unary depth budget. It
does not promise arbitrary reuse of evaluated wrapper ciphertexts, circuit privacy, a concrete
base scheme, or fixed-key evaluation without a predetermined budget.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.correct_fixedWidth_indCPA`: a correct, secure constructed
  scheme with exact polynomial secret and ciphertext widths independent of the depth budget.
* `Cslib.Crypto.Homomorphic.Leveled.exists_scheme_of_polynomiallyBounded`: every polynomially
  bounded depth family is covered by an actual efficient and secure scheme, without requiring
  the requested family to be computable.
* `Cslib.Crypto.Homomorphic.Leveled.schemeFamily_spec`: the depth-indexed family
  `fun d => scheme D (fun _ => d)` satisfies Gentry's Definition 3 with one uniform polynomial
  clock in `(n, d)` jointly across all depths.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2,
  Theorems 3 and 4][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Circuits Probability Turing.MultiTapeTM

/-- Assemble the actual construction's correctness, exact compact widths and IND-CPA security.
The native decryption-circuit generator bounds both widths; no output property is an input
hypothesis. Evaluation runtime additionally uses the base evaluator certificate, as stated by
`isPPTOn_scheme_evaluate`. -/
theorem correct_fixedWidth_indCPA {E : Scheme} {secretWidth ciphertextWidth budget : ℕ → ℕ}
    (D : DecryptionCircuits E secretWidth ciphertextWidth)
    (hE : E.Correct) (hwidth : E.FixedWidth secretWidth ciphertextWidth)
    (hboot : Scheme.Bootstrappable D)
    (hsecure : Encryption.INDCPA E.keyGen E.encrypt)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => E.encrypt p.1 p.2.1 p.2.2))
    (hD : ComputableInPolyTime
      (fun n => (⟨_, D.circuit n⟩ : Σ m, Circuit Boolean.signature m 1))
      encUnary (Boolean.encCircuit 1))
    (hbudget : ComputableInPolyTime budget encUnary encUnary) :
    (scheme D budget).Correct ∧
      (scheme D budget).FixedWidth (fun n => 3 * secretWidth n + 1)
        (fun n => ciphertextWidth n + 1) ∧
      PolynomiallyBounded (fun n => 3 * secretWidth n + 1) ∧
      PolynomiallyBounded (fun n => ciphertextWidth n + 1) ∧
      Encryption.INDCPA (scheme D budget).keyGen (scheme D budget).encrypt := by
  exact ⟨correct D hE hwidth hboot budget, fixedWidth D hE hwidth hboot budget,
    (polynomiallyBounded_widths D hD).1, (polynomiallyBounded_widths D hD).2,
    indCPA_scheme hsecure hkeyGen hencrypt hwidth.secret_length hbudget D⟩

/-- Every polynomially bounded depth family is covered by one actual leveled scheme with
polynomial widths, native algorithms and IND-CPA security. The selected unary budget dominates
the requested depth at every parameter, including its finite prefix. The requested depth family
itself need not be computable: only the selected polynomial majorant is executed. -/
theorem exists_scheme_of_polynomiallyBounded {E : Scheme}
    {secretWidth ciphertextWidth depth : ℕ → ℕ}
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
      encUnary (Boolean.encCircuit 1)) (hdepth : PolynomiallyBounded depth) :
    ∃ budget : ℕ → ℕ,
      ComputableInPolyTime budget encUnary encUnary ∧
      (∀ n, depth n ≤ budget n) ∧
      (scheme D budget).Correct ∧
      (∀ n c, c.2.depth ≤ depth n → (scheme D budget).permitted n c) ∧
      (scheme D budget).FixedWidth (fun n => 3 * secretWidth n + 1)
        (fun n => ciphertextWidth n + 1) ∧
      PolynomiallyBounded (fun n => 3 * secretWidth n + 1) ∧
      PolynomiallyBounded (fun n => ciphertextWidth n + 1) ∧
      IsPPTOn encUnary (encPair encBits encBits) (scheme D budget).keyGen ∧
      IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
        (fun p => (scheme D budget).encrypt p.1 p.2.1 p.2.2) ∧
      ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => (scheme D budget).decrypt p.1 p.2.1 p.2.2)
        (encPair encUnary (encPair encBits encBits)) encBool ∧
      IsPPTOn
        (encPair encUnary (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))))
        encBits (fun p => (scheme D budget).evaluate p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
      Encryption.INDCPA (scheme D budget).keyGen (scheme D budget).encrypt := by
  obtain ⟨coefficient, degree, hmajorant⟩ := polynomiallyBounded_iff_le.mp hdepth
  let budget := fun n => coefficient * (n + 1) ^ degree
  have hbudget : ComputableInPolyTime budget encUnary encUnary := by
    dsimp only [budget]
    fun_prop
  refine ⟨budget, hbudget, hmajorant, correct D hE hwidth hboot budget,
    (fun n c hc => hc.trans (hmajorant n)), fixedWidth D hE hwidth hboot budget,
    (polynomiallyBounded_widths D hD).1, (polynomiallyBounded_widths D hD).2,
    isPPTOn_scheme_keyGen hkeyGen hencrypt D budget hbudget,
    isPPTOn_scheme_encrypt hencrypt D budget,
    computableInPolyTime_scheme_decrypt D hD budget,
    isPPTOn_scheme_evaluate hencrypt D hD hevaluate budget hbudget,
    indCPA_scheme hsecure hkeyGen hencrypt hwidth.secret_length hbudget D⟩

/-- The depth-indexed family `fun d => scheme D (fun _ => d)` (`{E^(d) : d ∈ ℕ}` in
[Gentry2009, Definition 3, p. 170]) shares one uniform strict PPT clock jointly in `(n, d)`
for key generation, encryption and evaluation, and one deterministic polynomial clock jointly in
`(n, d)` for decryption. Any budget-specific scheme `scheme D budget` is obtained by substituting
`d = budget n` at each parameter `n`. -/
theorem schemeFamily_spec {E : Scheme} {secretWidth ciphertextWidth : ℕ → ℕ}
    (D : DecryptionCircuits E secretWidth ciphertextWidth)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => E.encrypt p.1 p.2.1 p.2.2))
    (hevaluate : IsPPTOn
      (encPair encUnary (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))))
      encBits (fun p => E.evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hD : ComputableInPolyTime
      (fun n => (⟨_, D.circuit n⟩ : Σ m, Circuit Boolean.signature m 1))
      encUnary (Boolean.encCircuit 1)) :
    PolynomiallyBounded (fun n => 3 * secretWidth n + 1) ∧
      PolynomiallyBounded (fun n => ciphertextWidth n + 1) ∧
      IsPPTOn (encPair encUnary encUnary) (encPair encBits encBits)
        (fun p : ℕ × ℕ => (scheme D (fun _ => p.2)).keyGen p.1) ∧
      IsPPTOn
        (encPair encUnary (encPair encUnary (encPair encBits encBool)))
        encBits
        (fun p => (scheme D (fun _ => p.2.1)).encrypt p.1 p.2.2.1 p.2.2.2) ∧
      ComputableInPolyTime
        (fun p : ℕ × ℕ × List Bool × List Bool =>
          (scheme D (fun _ => p.2.1)).decrypt p.1 p.2.2.1 p.2.2.2)
        (encPair encUnary (encPair encUnary (encPair encBits encBits))) encBool ∧
      IsPPTOn
        (encPair encUnary (encPair encUnary
          (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits)))))
        encBits
        (fun p => (scheme D (fun _ => p.2.1)).evaluate p.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  refine ⟨(polynomiallyBounded_widths D hD).1, (polynomiallyBounded_widths D hD).2,
    isPPTOn_keyGen hkeyGen hencrypt (by fun_prop) (by fun_prop),
    isPPTOn_encrypt hencrypt (by fun_prop) (by fun_prop) (by fun_prop),
    (computableInPolyTime_decrypt D hD
      (by fun_prop) (by fun_prop) (by fun_prop)),
    isPPTOn_evaluate hencrypt D hD hevaluate (by fun_prop) (by fun_prop)
      (by fun_prop) (by fun_prop) (by fun_prop)⟩

end Cslib.Crypto.Homomorphic.Leveled

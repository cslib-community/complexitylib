/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Leveled.PolyTime
import Complexity.Computability.Circuit.Boolean.PolynomialTime
import Complexity.Computability.Complexity.Problems.CircuitValue.Compilation

/-!
# Compact decryption for the leveled construction

The actual leveled decryption algorithm decodes two secret endpoints, chooses one using the
ciphertext tag, and evaluates the base decryption circuit. Its circuit bound must include this
wrapper, not just the base circuit. We apply `P ⊆ P/poly` to the complete native algorithm and
fix the unary security parameter by a substitution. Framing the secret-key input and fixing the
parameter together cost four gates.

The resulting family depends only on the security parameter, not on the depth budget. It agrees
with decryption on all words of the prescribed lengths, including malformed secret-key encodings.
This establishes the common-decryption-circuit condition in Gentry's Definition 3. When the base
secret width is also computable in polynomial time in unary, `exists_uniform_decrypt_circuits`
compiles the native decryption algorithm via `CircuitValue.exists_uniformCircuitFamily` to provide
a native polynomial-time circuit generator.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.exists_decrypt_circuits`: polynomial-size circuits for the
  complete tagged decryption algorithm, with one family shared by every depth budget.
* `Cslib.Crypto.Homomorphic.Leveled.exists_uniform_decrypt_circuits`: uniformly generated
  polynomial-size circuits for the complete tagged decryption algorithm when `secretWidth` is
  computable in polynomial time in unary.
* `Cslib.Crypto.Homomorphic.Leveled.exists_decrypt_parameter_bound`: a native time and space bound
  depending only on the security parameter at the prescribed widths, shared by every budget.

## References

* [C. Gentry, *Fully Homomorphic Encryption Using Ideal Lattices*, Sections 1.1 and 2][Gentry2009]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Circuits Turing.MultiTapeTM

variable {E : Scheme} {secretWidth ciphertextWidth : ℕ → ℕ}
  (D : DecryptionCircuits E secretWidth ciphertextWidth)
  (hD : ComputableInPolyTime
    (fun n => (⟨_, D.circuit n⟩ : Σ m, Circuit Boolean.signature m 1))
    encUnary (Boolean.encCircuit 1))

include hD in
/-- The native decryption computation has one time and space certificate for every depth budget.
On all words of the derived widths, both resources are bounded by a polynomial in the security
parameter alone. The native certificate itself covers arbitrary input words. -/
theorem exists_decrypt_parameter_bound :
    ∃ (time space : ℕ × List Bool × List Bool → ℕ) (bound : ℕ → ℕ),
      PolynomiallyBounded bound ∧
        (∀ budget : ℕ → ℕ, ComputableInTimeAndSpace
          (fun p : ℕ × List Bool × List Bool => (scheme D budget).decrypt p.1 p.2.1 p.2.2)
          (encPair encUnary (encPair encBits encBits)) encBool time space) ∧
        ∀ n (sk ciphertext : List Bool),
          sk.length = 3 * secretWidth n + 1 →
          ciphertext.length = ciphertextWidth n + 1 →
          time (n, sk, ciphertext) ≤ bound n ∧ space (n, sk, ciphertext) ≤ bound n := by
  obtain ⟨time, space, ht, hs, hdecrypt⟩ :=
    computableInPolyTime_scheme_decrypt D hD (fun _ => 0)
  obtain ⟨ct, dt, ht⟩ := polynomiallyBounded_iff_le.mp ht
  obtain ⟨cs, ds, hs⟩ := polynomiallyBounded_iff_le.mp hs
  obtain ⟨hkey, hciphertext⟩ := polynomiallyBounded_widths D hD
  let N := fun n => 2 * n + 1 + (2 * (3 * secretWidth n + 1) + 1 +
    (ciphertextWidth n + 1))
  have hN : PolynomiallyBounded N := by dsimp [N]; fun_prop
  let bound := fun n => ct * (N n + 1) ^ dt + cs * (N n + 1) ^ ds
  refine ⟨fun p => time ((encPair encUnary (encPair encBits encBits)) p).length,
    fun p => space ((encPair encUnary (encPair encBits encBits)) p).length,
    bound, by dsimp [bound]; fun_prop, fun _ => hdecrypt, ?_⟩
  intro n sk ciphertext hsk hc
  have hlength : (encPair encUnary (encPair encBits encBits) (n, sk, ciphertext)).length =
      N n := by simp [N, hsk, hc]
  constructor
  · exact (ht (((encPair encUnary (encPair encBits encBits)) (n, sk, ciphertext)).length)).trans
      (by rw [hlength]; exact Nat.le_add_right _ _)
  · exact (hs (((encPair encUnary (encPair encBits encBits)) (n, sk, ciphertext)).length)).trans
      (by rw [hlength]; exact Nat.le_add_left _ _)

include hD in
/-- The actual decoder, tag selection and base-circuit evaluation have polynomial-size circuits
on the derived key and ciphertext widths. One circuit family works for every depth budget, and
its specification includes every word of those widths, without a support or validity premise.
This is nonuniform circuit existence, not a circuit-generation certificate; see
`exists_uniform_decrypt_circuits` when `secretWidth` is computable in polynomial time in unary. -/
theorem exists_decrypt_circuits :
    ∃ circuits : ∀ n, Circuit Boolean.signature
        ((3 * secretWidth n + 1) + (ciphertextWidth n + 1)) 1,
      PolynomiallyBounded (fun n => (circuits n).size) ∧
        ∀ (budget : ℕ → ℕ) n (sk ciphertext : List Bool),
          sk.length = 3 * secretWidth n + 1 →
          ciphertext.length = ciphertextWidth n + 1 →
          (circuits n).eval Boolean.interpretation
              (BitString.ofList ((3 * secretWidth n + 1) + (ciphertextWidth n + 1))
                (sk ++ ciphertext)) 0 =
            (scheme D budget).decrypt n sk ciphertext := by
  have hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt D p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBool := by
    apply computableInPolyTime_decrypt D hD <;> fun_prop
  obtain ⟨L, hL, hdecryptL⟩ := Boolean.PPoly.exists_of_polyTime hdecrypt
  obtain ⟨c, p, hp, hc⟩ := Boolean.mem_PPoly_iff_exists_circuits.mp hL
  let K := fun n => 3 * secretWidth n + 1
  let C := fun n => ciphertextWidth n + 1
  let N := fun n => 2 * n + 1 + (2 * K n + 1 + C n)
  let parameter := fun n => BitString.ofList (2 * n + 1) (frame (encUnary n))
  let circuits := fun n =>
    ((c (N n)).comp (Boolean.substituteCircuit (Boolean.prependInputs (parameter n)))).comp
      (Boolean.substituteCircuit (Boolean.frameWiring (K n) (C n)))
  refine ⟨circuits, ?_, ?_⟩
  · obtain ⟨hK, hC⟩ := polynomiallyBounded_widths D hD
    have hN : PolynomiallyBounded N := by dsimp [N, K, C]; fun_prop
    have hbound : PolynomiallyBounded (fun n => 2 + (2 + p (N n))) := by fun_prop
    refine hbound.mono_of_le fun n => ?_
    change 2 + (2 + (c (N n)).size) ≤ 2 + (2 + p (N n))
    exact Nat.add_le_add_left (Nat.add_le_add_left (hc (N n)).1 2) 2
  · intro budget n sk ciphertext hsk hciphertext
    simp only [circuits, Circuit.eval_comp, Boolean.eval_substituteCircuit]
    rw [(hc (N n)).2]
    change L.slice (N n) _ = decrypt D n sk ciphertext
    rw [Bool.eq_iff_iff, Language.slice_eq_true_iff]
    rw [BitString.ofList_append hsk hciphertext, Boolean.substitute_prependInputs,
      List.ofFn_fin_append, Boolean.ofFn_substitute_frameWiring,
      BitString.ofFn_ofList hsk, BitString.ofFn_ofList hciphertext]
    have hparameter : List.ofFn (parameter n) = frame (encUnary n) :=
      BitString.ofFn_ofList (by simp)
    rw [hparameter]
    exact (hdecryptL (n, sk, ciphertext)).symm

include hD in
/-- When the base secret width is computable in polynomial time in unary, the actual decoder, tag
selection and base-circuit evaluation have a uniformly generated family of polynomial-size circuits
on the derived key and ciphertext widths. One circuit family and one native polynomial-time
generator work for every depth budget, and the specification covers all words of the prescribed
widths, without a support or validity premise. Since `hD` determines only the sum
`secretWidth n + ciphertextWidth n`, computing the wrapper arity
`(3 * secretWidth n + 1) + (ciphertextWidth n + 1)` and the split point between the secret key and
ciphertext uses `hsecret`. -/
theorem exists_uniform_decrypt_circuits
    (hsecret : ComputableInPolyTime secretWidth encUnary encUnary) :
    ∃ circuits : ∀ n, Circuit Boolean.signature
        ((3 * secretWidth n + 1) + (ciphertextWidth n + 1)) 1,
      ComputableInPolyTime
        (fun n => (⟨_, circuits n⟩ : Σ m, Circuit Boolean.signature m 1))
        encUnary (Boolean.encCircuit 1) ∧
      PolynomiallyBounded (fun n => (circuits n).size) ∧
      ∀ (budget : ℕ → ℕ) n (sk ciphertext : List Bool),
        sk.length = 3 * secretWidth n + 1 →
        ciphertext.length = ciphertextWidth n + 1 →
        (circuits n).eval Boolean.interpretation
            (BitString.ofList ((3 * secretWidth n + 1) + (ciphertextWidth n + 1))
              (sk ++ ciphertext)) 0 =
          (scheme D budget).decrypt n sk ciphertext := by
  have hview : ComputableInPolyTime
      (fun c : Σ m, Circuit Boolean.signature m 1 => (c.1, c.2.code))
      (Boolean.encCircuit 1) (encPair encUnary Boolean.encCode) := .of_eq fun _ => rfl
  have htotal : ComputableInPolyTime
      (fun n => secretWidth n + ciphertextWidth n) encUnary encUnary :=
    hview.fst'.comp hD
  have hciph : ComputableInPolyTime ciphertextWidth encUnary encUnary := by
    simpa only [Nat.add_sub_cancel_left] using
      (show ComputableInPolyTime
        (fun n => (secretWidth n + ciphertextWidth n) - secretWidth n) encUnary encUnary by
        fun_prop)
  let K := fun n => 3 * secretWidth n + 1
  let W := fun n => K n + (ciphertextWidth n + 1)
  have hK : ComputableInPolyTime K encUnary encUnary := by dsimp [K]; fun_prop
  have hW : ComputableInPolyTime W encUnary encUnary := by dsimp [W]; fun_prop
  let decryptConcat (p : ℕ × List Bool) : Bool :=
    decrypt D p.1 (p.2.take (K p.1)) (p.2.drop (K p.1))
  have hdecryptConcat : ComputableInPolyTime decryptConcat (encPair encUnary encBits) encBool := by
    have hklen : ComputableInPolyTime (fun p : ℕ × List Bool => K p.1)
        (encPair encUnary encBits) encUnary :=
      hK.comp (ComputableInPolyTime.fst encUnary encBits)
    have hw : ComputableInPolyTime (Prod.snd : ℕ × List Bool → List Bool)
        (encPair encUnary encBits) encBits :=
      ComputableInPolyTime.snd encUnary encBits
    exact computableInPolyTime_decrypt D hD
      (ComputableInPolyTime.fst encUnary encBits)
      (ComputableInPolyTime.bitsTakeWithInput hw hklen)
      (ComputableInPolyTime.bitsDropWithInput hw hklen)
  let F (p : ℕ × List Bool) : List Bool := [decryptConcat p]
  have hF : ComputableInPolyTime F (encPair encUnary encBits) encBits :=
    hdecryptConcat.of_enc_eq fun _ => rfl
  obtain ⟨circuits, hcode, hcorrect⟩ :=
    Complexity.CircuitValue.exists_uniformCircuitFamily
      (n := W) (m := fun _ => 1) hW (by fun_prop) hF
  have hgen : ComputableInPolyTime
      (fun n => (⟨W n, circuits n⟩ : Σ m, Circuit Boolean.signature m 1))
      encUnary (Boolean.encCircuit 1) :=
    (hW.prod hcode).of_enc_eq fun n => by simp only [Boolean.encCircuit_apply]
  have hsize : PolynomiallyBounded (fun n => (circuits n).size) := by
    have hlen_unary : ComputableInPolyTime (fun n => (circuits n).code.1.length)
        encUnary encUnary :=
      (ComputableInPolyTime.length_list Boolean.encGate).comp hcode.fst'
    have hlength : PolynomiallyBounded (fun n => (circuits n).code.1.length) :=
      (show PolyBounded (fun n : ℕ => n) (fun n => (circuits n).code.1.length) by
        simpa only [encUnary_apply, List.length_replicate] using
          hlen_unary.polyBounded_length).polynomiallyBounded
    exact hlength.mono_of_le fun n => (Circuit.length_code_fst (circuits n)).ge
  refine ⟨circuits, hgen, hsize, ?_⟩
  intro budget n sk ciphertext hsk hciphertext
  have hwlen : (sk ++ ciphertext).length = W n := by simp [W, K, hsk, hciphertext]
  have h := hcorrect n (BitString.ofList (W n) (sk ++ ciphertext)) 0
  simp only [F, decryptConcat, K, BitString.ofFn_ofList hwlen, List.take_left' hsk,
    List.drop_left' hsk, Fin.val_zero, List.getD_cons_zero] at h
  exact h

end Cslib.Crypto.Homomorphic.Leveled

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.GSWFHEAbstract

/-! # Clients of the GSW fully homomorphic encryption abstract

The leveled theorem quantifies over depth budgets computable in unary polynomial time; every
polynomial budget `c (security + 1) ^ e` qualifies, so the hypothesis is satisfiable. The
abstract's framing decoders invert the shared framing, so the fixed algorithms read the keys the
way their docstrings describe: the self-loop public key yields its GSW public key, the leveled
public key its first key, and the leveled secret key its two endpoint keys. On a secret key of
the GSW width, decryption of the joined word is GSW decryption.
-/

namespace ComplexityTests.Abstracts.GSWFHETests

open ComplexityTests.Abstracts
open ComplexityTests.Abstracts.GSWFHEAbstract

/-- Every polynomial depth budget satisfies the hypothesis of `leveled`. -/
example (c e : ℕ) :
    Computation.PolyTime (fun security : ℕ => c * (security + 1) ^ e)
      Encoding.encUnary Encoding.encUnary :=
  CryptographyBridge.polyTime_iff.mpr (by fun_prop)

/-- `leveled` yields a uniformly generated decryption circuit family `circuit`, a depth-indexed
scheme family `E` with joint polynomial runtime in `(security, d)` (`NativeInDepth E`) and, for
every unary-polynomial depth budget `budget`, a scheme `S` obtained by substituting
`d = budget security` into `E`. -/
example (hLWE : DecisionLWE) :
    ∃ (circuit : ∀ security, Cslib.Circuits.Circuit Cslib.Circuits.Boolean.signature
        ((3 * secretWidth security + 1) + (ciphertextWidth security + 1)) 1)
      (E : ℕ → Cslib.Crypto.Homomorphic.Scheme),
      Computation.PolyTime
        (fun security =>
          (⟨(3 * secretWidth security + 1) + (ciphertextWidth security + 1), circuit security⟩ :
            Σ k, Cslib.Circuits.Circuit Cslib.Circuits.Boolean.signature k 1))
        Encoding.encUnary (Cslib.Circuits.Boolean.encCircuit 1) ∧
      NativeInDepth E ∧
      ∀ d : ℕ,
        DecryptsWith (E d) (fun security => 3 * secretWidth security + 1)
          (fun security => ciphertextWidth security + 1) circuit ∧
        Homomorphic (E d) (fun _ C => C.2.depth ≤ d) ∧
        ChosenMessageSecure (E d) := by
  obtain ⟨circuit, E, hgen, -, -, -, hjoint, hd, -⟩ := leveled hLWE
  exact ⟨circuit, E, hgen, hjoint, fun d => ⟨(hd d).2.2.1, (hd d).2.2.2.1, (hd d).2.2.2.2.2.2⟩⟩

/-- `unframe` reads back a framed word, whatever follows it. -/
theorem unframe_frame_append (u v : List Bool) : unframe (Encoding.frame u ++ v) = u := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    simp only [Encoding.frame, List.flatMap_cons, List.cons_append, List.nil_append,
      List.append_assoc, unframe] at ih ⊢
    rw [ih]

/-- `dropFrame` returns what follows a framed word. -/
theorem dropFrame_frame_append (u v : List Bool) : dropFrame (Encoding.frame u ++ v) = v := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    simpa only [Encoding.frame, List.flatMap_cons, List.cons_append, List.nil_append,
      List.append_assoc, dropFrame] using ih

/-- Self-loop encryption uses the GSW public key of a self-loop public key. -/
example (security : ℕ) (publicKey : List Bool) (encryptedKey : List (List Bool)) (bit : Bool) :
    selfLoopEncryption security
        (Encoding.encPair Encoding.encBits (Encoding.encList Encoding.encBits)
          (publicKey, encryptedKey)) bit =
      encryption security publicKey bit := by
  simp only [selfLoopEncryption, Encoding.encPair, Encoding.encodePair, Encoding.encBits,
    Function.Embedding.coeFn_mk, Function.Embedding.refl_apply, unframe_frame_append]

/-- Leveled encryption uses the first public key of a framed list of public keys. -/
example (security : ℕ) (first : List Bool) (rest : List (List Bool)) (links : List Bool)
    (bit : Bool) :
    leveledEncryption security
        (Encoding.encPair (Encoding.encList Encoding.encBits) Encoding.encBits
          (first :: rest, links)) bit =
      (encryption security first bit).map (List.cons false) := by
  simp only [leveledEncryption, Encoding.encPair, Encoding.encodePair, Encoding.encList,
    Encoding.encodeList, Encoding.encBits, Function.Embedding.coeFn_mk,
    Function.Embedding.refl_apply, Function.comp_apply, List.flatMap_cons,
    unframe_frame_append]

/-- On a GSW secret key of the right width, decryption of the joined word is GSW decryption. -/
theorem decryptionWord_append (security : ℕ) (secret ciphertext : List Bool)
    (hsecret : secret.length = secretWidth security) :
    decryptionWord security (secret ++ ciphertext) = decryption security secret ciphertext := by
  rw [decryptionWord, List.take_left' hsecret, List.drop_left' hsecret]

/-- Leveled decryption of a fresh (`false`-tagged) ciphertext uses the first endpoint key, and of
an evaluated (`true`-tagged) ciphertext the last. -/
example (security : ℕ) (first last ciphertext : List Bool)
    (hfirst : first.length = secretWidth security) (hlast : last.length = secretWidth security) :
    leveledDecryption security (Encoding.encPair Encoding.encBits Encoding.encBits (first, last))
        (false :: ciphertext) = decryption security first ciphertext ∧
      leveledDecryption security (Encoding.encPair Encoding.encBits Encoding.encBits (first, last))
        (true :: ciphertext) = decryption security last ciphertext := by
  simp only [leveledDecryption, Encoding.encPair, Encoding.encodePair, Encoding.encBits,
    Function.Embedding.coeFn_mk, Function.Embedding.refl_apply, List.headD_cons, List.tail_cons,
    Bool.false_eq_true, ite_false, ite_true, unframe_frame_append, dropFrame_frame_append,
    decryptionWord_append security _ _ hfirst, decryptionWord_append security _ _ hlast,
    and_self]

end ComplexityTests.Abstracts.GSWFHETests

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Encryption.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Tactic.PolyTime

/-!
# Bounds for supported decryption replies

A native key generator bounds the supported secret-key length. Composing that bound with a
native optional decryptor bounds its encoded replies using only the security parameter and
query word. No oracle assumption or correctness premise is needed.

## Main results

* `Cslib.Crypto.Encryption.exists_decryption_length_bound`: a unary-computable reply cap.
-/

public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- A native decryptor has a unary-computable reply cap on every supported secret key and
every query word. The cap includes the option tag, so rejection and empty successful replies
are both fully readable. -/
theorem exists_decryption_length_bound {Out : Type} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hdecrypt : ComputableInPolyTime (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encPair encUnary (encPair encBits encBits)) (encOption encOut)) :
    ∃ bound : ℕ → List Bool → ℕ,
      ComputableInPolyTime (fun p : ℕ × List Bool => bound p.1 p.2)
        (encPair encUnary encBits) encUnary ∧
      ∀ n keys, keys ∈ (ProbComp.eval (keyGen n)).support →
        ∀ ct, (encOption encOut (decrypt n keys.2 ct)).length ≤ bound n ct := by
  obtain ⟨ck, dk, hlenKey⟩ := hkeyGen.length_le
  obtain ⟨cd, dd, hlenDec⟩ := hdecrypt.tidy.polyBounded_length.exists_le
  let bound : ℕ → List Bool → ℕ :=
    fun n req => cd * (2 * n + 2 * (ck * (n + 1) ^ dk) + req.length + 5) ^ dd
  refine ⟨bound, ?_, ?_⟩
  · dsimp only [bound]
    exact ComputableInPolyTime.of_tidy (by fun_prop)
  · intro n keys hkeys req
    have hk := hlenKey n keys hkeys
    have hd := hlenDec (n, keys.2, req)
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hk hd
    exact hd.trans (Nat.mul_le_mul_left cd (Nat.pow_le_pow_left (by omega) dd))

end Cslib.Crypto.Encryption

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/


import Complexity.Computability.GenericRAM.Native.IndexFold
import Mathlib.Data.Nat.Size

/-! # Streaming binary-index fold controls

The range list appears only in specifications and these small tests. The implementation retains
one index and one accumulator. No finite, inhabited, or standard-encoding assumption is imposed
on the generic accumulator.
-/


open Cslib.GenericRAM Turing.MultiTapeTM
open Cslib.GenericRAM.IndexFold

-- The empty enumeration never evaluates its body, even when that body changes every state.
example : run (fun p : ℕ × ℕ => p.1 + p.2 + 100) 0 7 = (0, 7) := rfl

-- The body sees the OLD index, starting at zero, exactly once and in ascending order.
example : run (fun p : ℕ × List ℕ => p.2 ++ [p.1]) 5 [] =
    (5, [0, 1, 2, 3, 4]) := by decide

-- Carry across 7 to 8 does not skip or duplicate an index.
example : run (fun p : ℕ × ℕ => p.2 + p.1) 9 0 = (9, 36) := by decide

-- A noncommutative accumulator distinguishes the traversal from reversed traversal.
example : run (fun p : ℕ × ℕ => 10 * p.2 + p.1) 4 0 = (4, 123) := by decide

-- A single round calls index zero, rather than index one.
example : run (fun p : ℕ × ℕ => p.1) 1 99 = (1, 0) := rfl

-- Captured data can be retained in the accumulator and is not reconstructed from the index.
example : run (fun p : ℕ × (ℕ × List ℕ) =>
    (p.2.1, p.2.2 ++ [p.1 + p.2.1])) 3 (7, []) = (3, (7, [7, 8, 9])) := by decide

-- The prefix contract is fully generic, including infinite accumulator types.
example {β : Type} (body : ℕ × β → β) (initial : β) (n : ℕ) :
    run body n initial =
      (n, (List.range n).foldl (fun acc i => body (i, acc)) initial) :=
  run_eq body n initial

-- Arbitrary encodings and every reachable prefix, not only the final state.
example {β : Type} (enc : β ↪ List Bool) (body : ℕ × β → β) (initial : β)
    (n B : ℕ) (h : ∀ j ≤ n, (enc (run body j initial).2).length ≤ B) :
    ∀ j ≤ n, (encPair encNat enc (run body j initial)).length ≤
      2 * (encNat n).length + 1 + B := by
  intro j hj
  exact length_run_le body initial hj (h j hj)

-- Exponentially many visits can still retain only a linear-size binary index.
example {β : Type} (enc : β ↪ List Bool) (body : ℕ × β → β) (initial : β)
    (k j B : ℕ) (hj : j ≤ 2 ^ k) (h : (enc (run body j initial).2).length ≤ B) :
    (encPair encNat enc (run body j initial)).length ≤ 2 * (k + 1) + 1 + B := by
  have hb := length_run_le body initial hj h
  have hlen : (encNat (2 ^ k)).length = k + 1 := by
    change (2 ^ k).bits.length = k + 1
    rw [Nat.size_eq_bits_len, Nat.size_pow]
  rw [hlen] at hb
  exact hb

-- No native implementation of the body is inferred merely from its mathematical function.
example {α β : Type} {input : α ↪ List Bool} {enc : β ↪ List Bool}
    {n : α → ℕ} {initial : α → β} {_body : ℕ × β → β}
    (_cn : NativeCertificate n input encNat)
    (_ci : NativeCertificate initial input enc) : True := by
  fail_if_success
    have : IsComputable (fun a => run _body (n a) (initial a)) input
        (encPair encNat enc) := by
      exact (certificate _cn _ci (by assumption)).isComputable
  trivial

-- The native endpoint consumes the COMPLETE supplied callback certificate at its original
-- pair encoding. Count, initialization, callback and all runtime captured data remain generic.
example {α β : Type} {input : α ↪ List Bool} {enc : β ↪ List Bool}
    {n : α → ℕ} {initial : α → β} {body : ℕ × β → β}
    (cn : NativeCertificate n input encNat) (ci : NativeCertificate initial input enc)
    (cb : NativeCertificate body (encPair encNat enc) enc) :
    IsComputable (fun a => run body (n a) (initial a)) input (encPair encNat enc) :=
  (certificate cn ci cb).isComputable

-- A full-state bound cannot be inferred from a final-state bound alone.
example {β : Type} (enc : β ↪ List Bool) (body : ℕ × β → β) (initial : β)
    (n j B : ℕ) (_hj : j ≤ n) (_hfinal : (enc (run body n initial).2).length ≤ B) : True := by
  fail_if_success
    have : (encPair encNat enc (run body j initial)).length ≤
        2 * (encNat n).length + 1 + B := by
      exact length_run_le body initial _hj (by assumption)
  trivial

-- A real native callback, not a hypothesized efficient enumerator. Its full pair input is
-- charged, even though this particular callback only retains the Boolean accumulator.
private noncomputable def keepCertificate :
    NativeCertificate (fun p : ℕ × Bool => p.2) (encPair encNat encBool) encBool :=
  NativeCertificate.linear (ComputableInO.snd encNat encBool)

-- Binary carry has quadratic successor TIME and linear charged WORKSPACE, kept independent.
example : (roundCertificate keepCertificate).time (7, true) = 32 := by decide
example : (roundCertificate keepCertificate).space (7, true) = 20 := by decide

-- The final pair, not only its accumulator, is covered by the native output charge.
example : IsComputable (fun n : ℕ => run (fun p : ℕ × Bool => p.2) n true)
    encNat (encPair encNat encBool) := by
  exact (certificate (NativeCertificate.linear (ComputableInO.of_linear (.of_eq fun _ => rfl)))
    (NativeCertificate.const true) keepCertificate).isComputable

-- With a Boolean accumulator the live-state invariant is unconditional, even over 2^k visits.
example (body : ℕ × Bool → Bool) (k j : ℕ) (hj : j ≤ 2 ^ k) :
    (encPair encNat encBool (run body j true)).length ≤ 2 * (k + 1) + 2 := by
  have hb := length_run_le (encB := encBool) body true hj (B := 1) (by simp [encBool_apply])
  have hlen : (encNat (2 ^ k)).length = k + 1 := by
    change (2 ^ k).bits.length = k + 1
    rw [Nat.size_eq_bits_len, Nat.size_pow]
  rw [hlen] at hb
  simpa [Nat.add_assoc] using hb

-- Instantiate the independent resource theorem with an actual native callback, not assumed
-- prefix bounds. The Boolean value always occupies exactly one bit. R and Q charge the full
-- index/Boolean pair; the counted-loop theorem supplies its additional binary-counter costs.
example : ∃ T S, ComputableInO
    (fun n : ℕ => run (fun p : ℕ × Bool => p.2) n true)
    encNat (encPair encNat encBool) T S := by
  let cn := NativeCertificate.linear
    (ComputableInO.of_linear (.of_eq (encIn := encNat) (f := id) fun _ => rfl))
  let ci := NativeCertificate.const (ei := encNat) (em := encBool) true
  refine ⟨_, _, computableInO cn ci keepCertificate
    (fun n => 2 * (encNat n).length + 2)
    (fun n => 2 * (encNat n).length + 2) (fun _ => 1) ?_ ?_ ?_⟩
  · intro n j hj
    change (encPair encNat encBool (run (fun p => p.2) j true)).length ≤ _
    simpa [Nat.add_assoc] using length_run_le (encB := encBool) (fun p : ℕ × Bool => p.2) true hj
      (B := 1) (by simp [encBool_apply])
  · intro n j hj
    change (encPair encNat encBool (run (fun p => p.2) j true)).length ≤ _
    simpa [Nat.add_assoc] using length_run_le (encB := encBool) (fun p : ℕ × Bool => p.2) true hj
      (B := 1) (by simp [encBool_apply])
  · intro _ _ _
    simp [encBool_apply]

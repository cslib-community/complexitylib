/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BQP.Sampling.Resources
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List

/-!
# Quantum decoder bounds measured before drawing its seed

The native decoder also accepts arbitrary seed words, and its general resource bound charges their
encoded length. Here the input is restricted to seeds of exactly one bit per Hadamard gate. The
restriction retains the existing pair encoding and the same machine; its proof is not encoded.

The seed has at most as many bits as the circuit has gates. For polynomial-time supplied circuits,
that count is polynomially bounded by the original input length. Both resource bounds can therefore
be stated in that original length, excluding the random seed, while retaining the same exponential
factor in the original gate count. In particular, an original input may explicitly encode the
well-formed gate list and the complete computational-basis register.

## Main definitions

* `Cslib.Complexity.QuantumContraction.SeededInput`: an input with a correctly sized seed.
* `Cslib.Complexity.QuantumContraction.SeededInput.encoding`: restriction of the existing pair
  encoding, with no encoded validity proof.

## Main results

* `Cslib.Complexity.QuantumContraction.exists_computableInO_decodeOutput_seeded`: one native
  decoder whose worst-case time and simultaneous workspace are bounded using the original input
  length, uniformly over every correctly sized seed.
-/

public section

namespace Cslib.Complexity.QuantumContraction

open Quantum Turing.MultiTapeTM

variable {α : Type}

/-- An original input paired with a seed of one bit per Hadamard gate. -/
abbrev SeededInput (gs : α → List GateCode) :=
  {p : α × List Bool // p.2.length = hadamardCount (gs p.1)}

namespace SeededInput

/-- The original input, before drawing the seed. -/
abbrev input {gs : α → List GateCode} : SeededInput gs → α
  | ⟨(a, _), _⟩ => a

/-- The correctly sized fair-bit seed. -/
abbrev seed {gs : α → List GateCode} : SeededInput gs → List Bool
  | ⟨(_, bits), _⟩ => bits

/-- The seed length is exactly the Hadamard count of the supplied circuit. -/
theorem seed_length {gs : α → List GateCode} (p : SeededInput gs) :
    p.seed.length = hadamardCount (gs p.input) := p.property

/-- Restrict the ordinary input/seed pair encoding; validity proofs contribute no symbols. -/
@[expose] def encoding (enc : α ↪ List Bool) (gs : α → List GateCode) :
    SeededInput gs ↪ List Bool :=
  (Function.Embedding.subtype _).trans (encPair enc encBits)

/-- A valid seeded input has exactly the existing pair's encoded word. -/
@[simp] theorem encoding_apply (enc : α ↪ List Bool) (gs : α → List GateCode)
    (p : SeededInput gs) : encoding enc gs p = encPair enc encBits (p.input, p.seed) := rfl

/-- The only added data are pair framing and the prescribed number of seed bits. -/
theorem length_encoding (enc : α ↪ List Bool) (gs : α → List GateCode) (p : SeededInput gs) :
    (encoding enc gs p).length =
      2 * (enc p.input).length + 1 + hadamardCount (gs p.input) := by
  rw [encoding_apply, length_encPair, encBits_apply, seed_length]

end SeededInput

/-- **Native decoder resources excluding the sampled seed.** There is one machine working on the
ordinary encoded input/seed pair. For every seed of exactly the circuit's Hadamard count, its time
is `2 ^ O((L+1)/√log(L+2))` times a polynomial in the original encoded input length, and its
simultaneous workspace is polynomial in that same original length. The original input supplies a
well-formed circuit and its full computational-basis register in polynomial time. -/
theorem exists_computableInO_decodeOutput_seeded {enc : α ↪ List Bool}
    {gs : α → List GateCode} {X : α → List Bool}
    (hgs : ComputableInPolyTime gs enc (encList encGateCode))
    (hX : ComputableInPolyTime X enc encBits)
    (hwf : ∀ a, ∀ g ∈ gs a, g.WellFormed (X a).length) :
    ∃ A e : ℕ, ComputableInO
      (fun p : SeededInput gs => decodeOutput (gs p.input) (X p.input) p.seed)
      (SeededInput.encoding enc gs) encBits
      (fun p => 2 ^ (A * ((gs p.input).length + 1) /
        Nat.sqrt (Nat.log 2 ((gs p.input).length + 2))) * ((enc p.input).length + 1) ^ e)
      (fun p => ((enc p.input).length + 1) ^ e) := by
  obtain ⟨A, e, hmachine⟩ := exists_computableInO_decodeOutput
    (hgs.comp (ComputableInPolyTime.fst enc encBits))
    (hX.comp (ComputableInPolyTime.fst enc encBits))
    (ComputableInPolyTime.snd enc encBits) (fun p => hwf p.1)
  have hrestricted := hmachine.of_encIn_eq (encD := SeededInput.encoding enc gs)
    (fun p : SeededInput gs => p.val) (fun _ => rfl)
  obtain ⟨C, d, hcodes⟩ := hgs.polyBounded_length.exists_le
  have hseed (p : SeededInput gs) :
      p.seed.length ≤ C * ((enc p.input).length + 1) ^ d := by
    rw [SeededInput.seed_length]
    have hh : hadamardCount (gs p.input) ≤ (gs p.input).length := by
      rw [hadamardCount_eq_countP]
      exact List.countP_le_length
    exact hh.trans ((length_le_length_encList encGateCode (gs p.input)).trans (hcodes p.input))
  have hpair (p : SeededInput gs) :
      (encPair enc encBits p.val).length + 1 ≤
        (C + 2) * ((enc p.input).length + 1) ^ (d + 1) := by
    have hbase : (enc p.input).length + 1 ≤ ((enc p.input).length + 1) ^ (d + 1) := by
      simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos (enc p.input).length)
        (show 1 ≤ d + 1 by omega)
    have hpow : ((enc p.input).length + 1) ^ d ≤
        ((enc p.input).length + 1) ^ (d + 1) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ d)
    rw [length_encPair, encBits_apply]
    change 2 * (enc p.input).length + 1 + p.seed.length + 1 ≤ _
    have hs := hseed p
    nlinarith
  have hpower (p : SeededInput gs) :
      ((encPair enc encBits p.val).length + 1) ^ e ≤
        (C + 2) ^ e * ((enc p.input).length + 1) ^ ((d + 1) * e) := by
    calc _ ≤ ((C + 2) * ((enc p.input).length + 1) ^ (d + 1)) ^ e :=
        Nat.pow_le_pow_left (hpair p) e
      _ = _ := by rw [mul_pow, ← pow_mul]
  refine ⟨A, (d + 1) * e, hrestricted.mono ((C + 2) ^ e) ?_ ?_⟩
  · intro p
    calc _ ≤ 2 ^ (A * ((gs p.input).length + 1) /
          Nat.sqrt (Nat.log 2 ((gs p.input).length + 2))) *
          ((C + 2) ^ e * ((enc p.input).length + 1) ^ ((d + 1) * e)) :=
        Nat.mul_le_mul_left _ (hpower p)
      _ = (C + 2) ^ e * (2 ^ (A * ((gs p.input).length + 1) /
          Nat.sqrt (Nat.log 2 ((gs p.input).length + 2))) *
          ((enc p.input).length + 1) ^ ((d + 1) * e)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_succ _)
  · intro p
    exact (hpower p).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))

end Cslib.Complexity.QuantumContraction

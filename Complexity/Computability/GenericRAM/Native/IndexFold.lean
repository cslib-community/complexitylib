/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.GenericRAM.Native.Combinators
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Size

/-!
# Streaming folds over binary indices

`IndexFold.run` calls a body at indices `0, …, n - 1`, retaining only its binary index and
accumulator. `List.range` occurs only in the correctness specification. The native certificate
uses the existing binary-counted iterator, not a unary clock or a materialized range.

This is an enumeration building block for the local-assignment and measurement loops of
[OpenAI2026ETH], Lemma 3.2 and Proposition 3.4 (pp. 22–26). It does not yet decode indices into
Boolean vectors or mixed-radix tuples. A callback may retain captured inputs in its accumulator;
its certificate must cover the full index/accumulator encoding. Arbitrary callbacks need not
have small outputs: the reachable-prefix size bound is an explicit hypothesis of the resource
bound below. No polynomial-time claim is made for an exponentially long whole loop.
-/

@[expose] public section

namespace Cslib.GenericRAM.IndexFold

open Turing.MultiTapeTM

variable {β α : Type}

/-- Advance the binary index after applying the body to the old index and accumulator. -/
def step (body : ℕ × β → β) (p : ℕ × β) : ℕ × β :=
  (p.1 + 1, body p)

/-- A streaming prefix, including its next index. No list of visited indices is constructed. -/
def run (body : ℕ × β → β) (n : ℕ) (initial : β) : ℕ × β :=
  (step body)^[n] (0, initial)

/-- The empty prefix invokes no callback. -/
@[simp] theorem run_zero (body : ℕ × β → β) (initial : β) :
    run body 0 initial = (0, initial) := rfl

/-- A prefix is extended by exactly one callback at the current index. -/
theorem run_succ (body : ℕ × β → β) (n : ℕ) (initial : β) :
    run body (n + 1) initial = step body (run body n initial) := by
  exact Function.iterate_succ_apply' _ _ _

/-- Every prefix has the expected next index, including the final prefix. -/
@[simp] theorem run_index (body : ℕ × β → β) (n : ℕ) (initial : β) :
    (run body n initial).1 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [run_succ, step, ih]

/-- The accumulator agrees with the ordered range fold. The list is specification-only. -/
theorem run_accumulator (body : ℕ × β → β) (n : ℕ) (initial : β) :
    (run body n initial).2 =
      (List.range n).foldl (fun acc i => body (i, acc)) initial := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp : run body n initial =
        (n, (List.range n).foldl (fun acc i => body (i, acc)) initial) :=
      Prod.ext (run_index body n initial) ih
    simp only [run_succ, step, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    rw [hp]

/-- The exact ordered state of every prefix. In particular, no index is skipped or repeated. -/
theorem run_eq (body : ℕ × β → β) (n : ℕ) (initial : β) :
    run body n initial =
      (n, (List.range n).foldl (fun acc i => body (i, acc)) initial) := by
  exact Prod.ext (run_index _ _ _) (run_accumulator _ _ _)

variable {encB : β ↪ List Bool}

/-- The binary index adds only its encoded length to the live accumulator. -/
theorem length_run (body : ℕ × β → β) (n : ℕ) (initial : β) :
    (encPair encNat encB (run body n initial)).length =
      2 * (encNat n).length + 1 + (encB (run body n initial).2).length := by
  rw [length_encPair, run_index]

/-- A common prefix accumulator bound gives a common full-state bound, without multiplying
workspace by the number of visited indices. -/
theorem length_run_le (body : ℕ × β → β) {n j B : ℕ} (initial : β)
    (hj : j ≤ n) (hB : (encB (run body j initial).2).length ≤ B) :
    (encPair encNat encB (run body j initial)).length ≤
      2 * (encNat n).length + 1 + B := by
  rw [length_run]
  have : (encNat j).length ≤ (encNat n).length := by
    simpa [Nat.size_eq_bits_len] using Nat.size_le_size hj
  omega

/-- The native round is constructed from the existing binary successor and the actual callback
certificate. Its input contains both the complete binary index and the complete accumulator. -/
def roundCertificate {body : ℕ × β → β}
    (cb : NativeCertificate body (encPair encNat encB) encB) :
    NativeCertificate (step body) (encPair encNat encB) (encPair encNat encB) where
  time p := (encPair encNat encB p).length + ((encNat p.1).length + 1) ^ 2 + cb.time p
  space p := (encPair encNat encB p).length + ((encNat p.1).length + 1) + cb.space p
  computes := (ComputableInO.natSucc.comp (ComputableInO.fst encNat encB)).prod cb.computes

/-- One fixed native machine streams a runtime binary number of indices. Its bound is the
existing iterator's trajectory-max bound; neither a finite state type nor a machine is selected
separately for each runtime `n`. -/
noncomputable def certificate {encIn : α ↪ List Bool} {count : α → ℕ}
    {initial : α → β} {body : ℕ × β → β}
    (cn : NativeCertificate count encIn encNat)
    (ci : NativeCertificate initial encIn encB)
    (cb : NativeCertificate body (encPair encNat encB) encB) :
    NativeCertificate (fun a => run body (count a) (initial a))
      encIn (encPair encNat encB) :=
  NativeCertificate.iterate cn ((NativeCertificate.const (em := encNat) 0).prod ci)
    (roundCertificate cb)

/-- Independent time/workspace bounds under explicit reachable-prefix callback and accumulator
bounds. The runtime count stays binary. These are charged native `O` bounds, not exact clocks.
`R`, `Q`, and `B` need not be polynomial; a polynomial live-state invariant can be supplied without
asserting that the entire exponentially long computation is polynomial-time. -/
theorem computableInO {encIn : α ↪ List Bool} {count : α → ℕ} {initial : α → β}
    {body : ℕ × β → β} (cn : NativeCertificate count encIn encNat)
    (ci : NativeCertificate initial encIn encB)
    (cb : NativeCertificate body (encPair encNat encB) encB)
    (R Q B : α → ℕ)
    (hR : ∀ a j, j ≤ count a → cb.time (run body j (initial a)) ≤ R a)
    (hQ : ∀ a j, j ≤ count a → cb.space (run body j (initial a)) ≤ Q a)
    (hB : ∀ a j, j ≤ count a → (encB (run body j (initial a)).2).length ≤ B a) :
    ComputableInO (fun a => run body (count a) (initial a)) encIn (encPair encNat encB)
      (fun a => cn.time a + ((encIn a).length + ci.time a) +
        (count a + 1) *
          ((2 * (encNat (count a)).length + 1 + B a +
            ((encNat (count a)).length + 1) ^ 2 + R a) +
            (2 * (encNat (count a)).length + 1 + B a) +
            ((encNat (count a)).length + 1) ^ 2))
      (fun a => cn.space a + ((encIn a).length + ci.space a) +
        (2 * (encNat (count a)).length + 1 + B a +
          ((encNat (count a)).length + 1) + Q a) +
        (2 * (encNat (count a)).length + 1 + B a) +
        (encNat (count a)).length) := by
  rcases isEmpty_or_nonempty β with h | ⟨⟨b⟩⟩
  · exact (((NativeCertificate.const (em := encNat) 0).prod ci).computes.mono_le
      (fun _ => by simp only [NativeCertificate.prod_time, NativeCertificate.const_time]; omega)
      (fun _ => by simp only [NativeCertificate.prod_space, NativeCertificate.const_space]; omega)
      ).of_enc_eq fun a => isEmptyElim (initial a)
  let : Inhabited β := ⟨b⟩
  apply ComputableInO.iterate cn.computes
    ((NativeCertificate.const (em := encNat) 0).prod ci).computes (roundCertificate cb).computes
  · intro a j hj
    change (encPair encNat encB (run body j (initial a))).length +
      ((encNat (run body j (initial a)).1).length + 1) ^ 2 +
      cb.time (run body j (initial a)) ≤ _
    rw [run_index]
    have hs := length_run_le body (initial a) hj (hB a j hj)
    have hn : (encNat j).length ≤ (encNat (count a)).length := by
      simpa [Nat.size_eq_bits_len] using Nat.size_le_size hj
    have hp := Nat.pow_le_pow_left (by omega :
      (encNat j).length + 1 ≤ (encNat (count a)).length + 1) 2
    have := hR a j hj
    omega
  · intro a j hj
    change (encPair encNat encB (run body j (initial a))).length +
      ((encNat (run body j (initial a)).1).length + 1) +
      cb.space (run body j (initial a)) ≤ _
    rw [run_index]
    have hs := length_run_le body (initial a) hj (hB a j hj)
    have hn : (encNat j).length ≤ (encNat (count a)).length := by
      simpa [Nat.size_eq_bits_len] using Nat.size_le_size hj
    have := hQ a j hj
    omega
  · intro a j hj
    exact length_run_le body (initial a) hj (hB a j hj)

end Cslib.GenericRAM.IndexFold

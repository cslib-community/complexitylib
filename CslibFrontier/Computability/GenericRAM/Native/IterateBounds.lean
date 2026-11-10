/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.GenericRAM.Native.IndexFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts

/-!
# Trajectory bounds for native iteration

`NativeCertificate.iterate` charges every round at the trajectory maxima `maxRoundTime`,
`maxRoundSpace` and `maxStateLength`. A client usually knows only a bound on each reachable round
and state. The lemmas here turn such reachable-prefix bounds into explicit time and space bounds,
for the plain iterator and for the binary-indexed `IndexFold.certificate`, whose rounds also
advance and store the index.

The iterator, its trajectory maxima and `IndexFold` are Samuel Schlesinger's
(`GenericRAM/Native/Combinators.lean`, `GenericRAM/Native/IndexFold.lean`); this module only
states their resource bounds once.

## Main results

* `NativeCertificate.iterate_time_le`, `NativeCertificate.iterate_space_le`: resource bounds for
  `iterate` from per-round and per-state bounds along the first `n a + 1` iterates.
* `IndexFold.certificate_time_le`, `IndexFold.certificate_space_le`: resource bounds for an index
  fold from callback bounds, a bound on each reachable index/accumulator encoding, and a bound on
  the length of the binary count.
-/

public section

namespace Cslib.GenericRAM

open Turing.MultiTapeTM

variable {α β : Type} {ei : α ↪ List Bool} {eb : β ↪ List Bool}

namespace NativeCertificate

/-- **Time of an iteration from reachable bounds.** If every round among the first `n a + 1`
iterates takes time at most `R` and every such state has encoded length at most `B`, then the
iteration takes time at most `cn.time a + cinit.time a + (n a + 1) * (R + B + (|n a| + 1) ^ 2)`,
where `|n a|` is the length of the binary count. -/
theorem iterate_time_le {n : α → ℕ} {init : α → β} {step : β → β}
    (cn : NativeCertificate n ei encNat) (cinit : NativeCertificate init ei eb)
    (cstep : NativeCertificate step eb eb) (a : α) {R B : ℕ}
    (hR : ∀ j ≤ n a, cstep.time (step^[j] (init a)) ≤ R)
    (hB : ∀ j ≤ n a, (eb (step^[j] (init a))).length ≤ B) :
    (iterate cn cinit cstep).time a ≤ cn.time a + cinit.time a +
      (n a + 1) * (R + B + ((encNat (n a)).length + 1) ^ 2) := by
  rw [iterate_time]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right
    (Nat.add_le_add (maxRoundTime_le cstep _ _ hR) (maxStateLength_le eb step _ _ hB)) _)) _

/-- **Space of an iteration from reachable bounds.** If every round among the first `n a + 1`
iterates uses space at most `Q` and every such state has encoded length at most `B`, then the
iteration uses space at most `cn.space a + cinit.space a + Q + B + |n a|`, where `|n a|` is the
length of the binary count. -/
theorem iterate_space_le {n : α → ℕ} {init : α → β} {step : β → β}
    (cn : NativeCertificate n ei encNat) (cinit : NativeCertificate init ei eb)
    (cstep : NativeCertificate step eb eb) (a : α) {Q B : ℕ}
    (hQ : ∀ j ≤ n a, cstep.space (step^[j] (init a)) ≤ Q)
    (hB : ∀ j ≤ n a, (eb (step^[j] (init a))).length ≤ B) :
    (iterate cn cinit cstep).space a ≤ cn.space a + cinit.space a + Q + B +
      (encNat (n a)).length := by
  rw [iterate_space]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left
    (maxRoundSpace_le cstep _ _ hQ) _) (maxStateLength_le eb step _ _ hB)) _

end NativeCertificate

namespace IndexFold

variable {encB : β ↪ List Bool}

/-- **Time of an index fold from reachable bounds.** Suppose that for every prefix
`j ≤ count a` the callback takes time at most `R` and the index/accumulator pair has encoded
length at most `B`, and that the binary count has length at most `I`. Then the fold takes time at
most `cn.time a + (|input| + ci.time a) + (count a + 1) * (2 * B + 2 * (I + 1) ^ 2 + R)`: each
round reads the pair, advances the binary index and runs the callback, and the iterator charges
the stored state and its own counter on top. -/
theorem certificate_time_le {encIn : α ↪ List Bool} {count : α → ℕ} {initial : α → β}
    {body : ℕ × β → β} (cn : NativeCertificate count encIn encNat)
    (ci : NativeCertificate initial encIn encB)
    (cb : NativeCertificate body (encPair encNat encB) encB) (a : α) {R B I : ℕ}
    (hR : ∀ j ≤ count a, cb.time (run body j (initial a)) ≤ R)
    (hB : ∀ j ≤ count a, (encPair encNat encB (run body j (initial a))).length ≤ B)
    (hI : (encNat (count a)).length ≤ I) :
    (certificate cn ci cb).time a ≤ cn.time a + ((encIn a).length + ci.time a) +
      (count a + 1) * (2 * B + 2 * (I + 1) ^ 2 + R) := by
  have hsq (j : ℕ) (hj : j ≤ count a) : ((encNat j).length + 1) ^ 2 ≤ (I + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right ((length_encNat_mono hj).trans hI) 1) 2
  have h := NativeCertificate.iterate_time_le cn
    ((NativeCertificate.const (em := encNat) 0).prod ci) (roundCertificate cb) a
    (R := B + (I + 1) ^ 2 + R) (B := B) (fun j hj => by
      change (encPair encNat encB (run body j (initial a))).length +
        ((encNat (run body j (initial a)).1).length + 1) ^ 2 +
        cb.time (run body j (initial a)) ≤ _
      rw [run_index]
      have := hB j hj; have := hsq j hj; have := hR j hj
      omega) hB
  simp only [NativeCertificate.prod_time, NativeCertificate.const_time] at h
  have hmul := Nat.mul_le_mul_left (count a + 1)
    (show B + (I + 1) ^ 2 + R + B + ((encNat (count a)).length + 1) ^ 2 ≤
      2 * B + 2 * (I + 1) ^ 2 + R by have := hsq (count a) le_rfl; omega)
  exact h.trans (by omega)

/-- **Space of an index fold from reachable bounds.** Under the hypotheses of
`certificate_time_le`, with the callback's space bounded by `Q`, the fold uses space at most
`cn.space a + (|input| + ci.space a) + (2 * B + 2 * I + 1 + Q)`. The count does not multiply the
space. -/
theorem certificate_space_le {encIn : α ↪ List Bool} {count : α → ℕ} {initial : α → β}
    {body : ℕ × β → β} (cn : NativeCertificate count encIn encNat)
    (ci : NativeCertificate initial encIn encB)
    (cb : NativeCertificate body (encPair encNat encB) encB) (a : α) {Q B I : ℕ}
    (hQ : ∀ j ≤ count a, cb.space (run body j (initial a)) ≤ Q)
    (hB : ∀ j ≤ count a, (encPair encNat encB (run body j (initial a))).length ≤ B)
    (hI : (encNat (count a)).length ≤ I) :
    (certificate cn ci cb).space a ≤ cn.space a + ((encIn a).length + ci.space a) +
      (2 * B + 2 * I + 1 + Q) := by
  have h := NativeCertificate.iterate_space_le cn
    ((NativeCertificate.const (em := encNat) 0).prod ci) (roundCertificate cb) a
    (Q := B + (I + 1) + Q) (B := B) (fun j hj => by
      change (encPair encNat encB (run body j (initial a))).length +
        ((encNat (run body j (initial a)).1).length + 1) +
        cb.space (run body j (initial a)) ≤ _
      rw [run_index]
      have := hB j hj; have := (length_encNat_mono hj).trans hI; have := hQ j hj
      omega) hB
  simp only [NativeCertificate.prod_space, NativeCertificate.const_space] at h
  exact h.trans (by omega)

end IndexFold

end Cslib.GenericRAM

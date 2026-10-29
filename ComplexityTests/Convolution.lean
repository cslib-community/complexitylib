/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Convolution

/-!
Concrete existential-convolution values, boundary cases, and a client of the shared-translation
circuit compiler. In particular, two witnesses still produce `true`: the aggregation is OR.
-/

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open scoped Pointwise

-- There are two witnesses for this output, so this distinguishes OR from parity convolution.
example : BitString.orConvolution (fun _ : BitString 1 => true) (fun _ => true)
    (fun _ => false) = true := by
  decide

-- The sum of the singleton accepted set {1} with itself is {0}.
example : BitString.orConvolution (fun x : BitString 1 => x 0) (fun x => x 0)
    (fun _ => false) = true := by
  decide

example : BitString.orConvolution (fun x : BitString 1 => x 0) (fun x => x 0)
    (fun _ => true) = false := by
  decide

-- Zero coordinates leave one assignment, so convolution is conjunction of the two constants.
example (a b : Bool) : BitString.orConvolution (fun _ : BitString 0 => a) (fun _ => b)
    Fin.elim0 = (a && b) := by
  cases a <;> cases b <;> decide

-- Two differently translated copies of a projection can share the single input negation.
example : ∃ c : Circuit signature 1 1,
    c.Computes interpretation
      (single fun x : BitString 1 => decide (∃ b : Bool, (x 0 ^^ b) = true)) ∧
      c.size ≤ 4 := by
  apply complexity_le_iff.mp
  have h := complexity_exists_translate_le (n := 1) Finset.univ
    (fun _ : Bool => fun x : BitString 1 => x 0) (fun b _ => b)
  simpa only [Finset.mem_univ, true_and, Pi.add_apply, Bool.add_eq_xor,
    complexity_single_proj, zero_add, Finset.sum_const, Finset.card_univ,
    Fintype.card_bool, smul_eq_mul] using h

-- An empty translate family still supplies the constant-false circuit.
example : ∃ c : Circuit signature 0 1,
    c.Computes interpretation (single fun _ : BitString 0 => false) ∧ c.size ≤ 1 := by
  apply complexity_le_iff.mp
  have h := complexity_exists_translate_le (n := 0) (∅ : Finset Bool)
    (fun _ _ => false) (fun _ => Fin.elim0)
  simpa using h

-- A concrete cover, with no right representatives, compiles the sumset {00} + {11}.
example : ∃ c : Circuit signature 2 1,
    c.Computes interpretation (single fun x : BitString 2 => decide (x = 1)) ∧
      c.size ≤ 9 := by
  have hpoint : complexity interpretation (single fun x : BitString 2 => decide (x = 1)) ≤ 5 :=
    (synthesis_minterm id (1 : BitString 2)).complexity_le
  have h := complexity_sumset_le_of_cover ({0} : Finset (BitString 2)) {1} {0} ∅ (by simp)
  simp only [Finset.singleton_add_singleton, zero_add, Finset.mem_singleton,
    Finset.card_singleton, Finset.card_empty, one_mul, zero_mul, Nat.add_zero] at h
  exact complexity_le_iff.mp
    (h.trans (Nat.add_le_add_right (Nat.add_le_add_left hpoint 2) 2))

-- The complete abstract argument produces a circuit for a concrete convolution, with no cover
-- supplied by the caller. Convolving the one-bit projection with itself gives its negation.
example : ∃ c : Circuit signature 1 1,
    c.Computes interpretation (single fun x : BitString 1 => !x 0) ∧ c.size ≤ 5 := by
  have heq : BitString.orConvolution (fun x : BitString 1 => x 0) (fun x => x 0) =
      fun x => !x 0 := by
    decide
  have h := exists_orConvolution_circuit (fun x : BitString 1 => x 0) (fun x => x 0)
  simpa [heq, complexity_single_proj] using h

-- The integer exponent corollary certifies a strict saving at a concrete input length.
example : complexity interpretation (single (BitString.orConvolution
    (fun x : BitString 21 => x 0) (fun x => x 1))) < 2 ^ 21 := by
  have h := complexity_orConvolution_sub_pow_three_mul_four_pow_le
    (fun x : BitString 21 => x 0) (fun x => x 1)
  simp only [complexity_single_proj, max_self, zero_add] at h
  by_contra hlarge
  have hlower := Nat.sub_le_sub_right (Nat.le_of_not_gt hlarge) 22
  have hcube := Nat.mul_le_mul_right (4 ^ 21) (Nat.pow_le_pow_left hlower 3)
  have hcontr := hcube.trans h
  norm_num at hcontr

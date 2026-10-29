/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.PP
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# A PP decision as one bit of a counting function

If a verifier accepts `c` of its `2 ^ p(n)` random strings, strict majority is the bit at
position `p(n) + 1` of `2 * c + (2 ^ p(n) - 1)`. The shift is nonnegative and computable in
polynomial time with binary output, so the shifted count remains in `#P`.
This includes zero random bits and a tie is rejected.

## Main results

* `Cslib.Complexity.exists_SharpP_testBit_of_mem_PP`: a PP problem is decided by one bit of
  a counting function at a polynomially determined position.

## References

* [J. Gill, *Computational complexity of probabilistic Turing machines*][Gill1977].
* [L. Fortnow, *Counting Complexity*][Fortnow1997], Section 4.1, for the relation between
  PP decisions and counting-function bits. The explicit shifted count is the construction here.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

private theorem majority_iff_shifted_testBit {c p : ℕ} (hc : c ≤ 2 ^ p) :
    2 ^ p < 2 * c ↔ (2 * c + (2 ^ p - 1)).testBit (p + 1) = true := by
  have hpos := Nat.one_le_two_pow (n := p)
  have hupper : 2 * c + (2 ^ p - 1) < 2 ^ (p + 1 + 1) := by
    simp only [pow_succ]
    lia
  by_cases h : 2 ^ p < 2 * c
  · exact ⟨fun _ => Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (by
      simp only [pow_succ]
      lia) hupper, fun _ => h⟩
  · have hlow : 2 * c + (2 ^ p - 1) < 2 ^ (p + 1) := by
      simp only [pow_succ]
      lia
    simp only [h, Nat.testBit_lt_two_pow hlow, Bool.false_eq_true]

/-- Every PP problem is decided by one bit of a `#P` function at a polynomial position.
The bit index is zero-based and computed from the length of the encoded instance. -/
theorem exists_SharpP_testBit_of_mem_PP {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ PP enc) :
    ∃ f ∈ SharpP enc, ∃ q : Polynomial ℕ,
      ∀ a, a ∈ A ↔ (f a).testBit (q.eval (enc a).length) = true := by
  obtain ⟨p, V, hV, h⟩ := hA
  let count := fun a => acceptCount V a (p.eval (enc a).length)
  have hcount : count ∈ SharpP enc := ⟨p, V, hV, fun _ => rfl⟩
  have hshift : (fun a => 2 ^ p.eval (enc a).length - 1) ∈ SharpP enc :=
    mem_SharpP_of_polyTime (((ComputableInPolyTime.binary_two_pow.comp
      (by fun_prop : ComputableInPolyTime
        (fun a => p.eval (enc a).length) enc encUnary)).binary_sub' (.const 1)))
  refine ⟨count + count + (fun a => 2 ^ p.eval (enc a).length - 1),
    SharpP.add_mem (SharpP.add_mem hcount hcount) hshift, p + 1, fun a => ?_⟩
  rw [h a]
  simpa only [Polynomial.eval_add, Polynomial.eval_one, Pi.add_apply, count, two_mul] using
    (majority_iff_shifted_testBit (c := count a) (p := p.eval (enc a).length)
      acceptCount_le_two_pow)

end Cslib.Complexity

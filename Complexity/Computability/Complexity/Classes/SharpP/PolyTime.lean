/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP.Closure
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Polynomial-time functions and tests in counting classes

Binary-encoded natural outputs of polynomial-time functions are in #P; binary-encoded integer
outputs are in GapP [Fortnow, Theorem 3.5][Fortnow1997]. The verifier guesses a fixed-width
binary word and accepts just those representing values below the computed output. The witness
width bounds the binary output length, not its potentially exponential numeric value.

Polynomial-time Boolean control also permits selection between two counting functions. The
control certificate is separate from the branches' counting-class membership.

## Main results

* `mem_SharpP_of_polyTime`: polynomial-time binary natural functions are in #P.
* `mem_GapP_of_polyTime`: polynomial-time binary integer functions are in GapP.
* `SharpP.ite_mem`, `GapP.ite_mem`: selection by a polynomial-time Boolean test.

## References

* [L. Fortnow, *Counting Complexity*][Fortnow1997], Theorem 3.5.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- A polynomial-time function with binary natural output is a #P function. -/
theorem mem_SharpP_of_polyTime {f : α → ℕ} (hf : ComputableInPolyTime f enc encNat) :
    f ∈ SharpP enc := by
  obtain ⟨p, hb⟩ := hf.polyBounded_length.exists_polynomial
  refine ⟨p, fun x => decide (BitString.binaryValue x.2 < f x.1), ?_, fun a => ?_⟩
  · exact ComputableInPolyTime.binary_lt.comp
      ((ComputableInPolyTime.bitsBinaryValue.comp (.snd enc encBits)).prod
        (hf.comp (.fst enc encBits)))
  · symm
    unfold acceptCount
    simp only [decide_eq_true_eq]
    apply BitString.card_filter_binaryValue_lt
    have hsize : (f a).size ≤ p.eval (enc a).length := by
      simpa only [encNat_apply, Nat.size_eq_bits_len] using hb a
    exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by lia) hsize)

/-- A polynomial-time function with binary integer output is a GapP function. -/
theorem mem_GapP_of_polyTime {f : α → ℤ} (hf : ComputableInPolyTime f enc encIntBin) :
    f ∈ GapP enc := by
  have hp := mem_SharpP_of_polyTime (ComputableInPolyTime.intBin_toNat.comp hf)
  have hn := mem_SharpP_of_polyTime
    (ComputableInPolyTime.intBin_toNat.comp
      (ComputableInPolyTime.intBin_sub.comp ((ComputableInPolyTime.const 0).prod hf)))
  exact ⟨_, hp, _, hn, fun a => by simp only [Function.comp_apply, zero_sub]; lia⟩

/-- A polynomial-time Boolean test may select between two #P functions on the same input.
Its two Boolean masks are polynomial-time functions; multiplication and addition select the
corresponding count exactly. -/
theorem SharpP.ite_mem {c : α → Bool} {f g : α → ℕ}
    (hc : ComputableInPolyTime c enc encBool)
    (hf : f ∈ SharpP enc) (hg : g ∈ SharpP enc) :
    (fun a => if c a then f a else g a) ∈ SharpP enc := by
  have htrue : (fun a => (c a).toNat) ∈ SharpP enc :=
    mem_SharpP_of_polyTime ((ComputableInPolyTime.of_finite Bool.toNat).comp hc)
  have hfalse : (fun a => (!c a).toNat) ∈ SharpP enc :=
    mem_SharpP_of_polyTime
      ((ComputableInPolyTime.of_finite (fun b : Bool => (!b).toNat)).comp hc)
  convert SharpP.add_mem (SharpP.mul_mem htrue hf) (SharpP.mul_mem hfalse hg) using 1
  funext a
  cases h : c a <;> simp [h]

/-- A polynomial-time Boolean test may select between two GapP functions on the same input.
Apply #P selection to the positive and negative counting functions of each branch. -/
theorem GapP.ite_mem {c : α → Bool} {f g : α → ℤ}
    (hc : ComputableInPolyTime c enc encBool)
    (hf : f ∈ GapP enc) (hg : g ∈ GapP enc) :
    (fun a => if c a then f a else g a) ∈ GapP enc := by
  obtain ⟨f₁, hf₁, f₂, hf₂, hf⟩ := hf
  obtain ⟨g₁, hg₁, g₂, hg₂, hg⟩ := hg
  refine ⟨_, SharpP.ite_mem hc hf₁ hg₁, _, SharpP.ite_mem hc hf₂ hg₂, fun a => ?_⟩
  cases h : c a
  · simpa only [h, Bool.false_eq_true, ↓reduceIte] using hg a
  · simpa only [h, ↓reduceIte] using hf a

end Cslib.Complexity

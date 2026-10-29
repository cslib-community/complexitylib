/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.AWPP
public import Complexity.Computability.Complexity.Classes.WPP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Wide gaps are almost-wide gaps

The containment WPP ⊆ AWPP is classical [Fenner et al., Section 6][FennerEtAl2003].
Here we square the signed WPP target, normalize by its binary length, and apply
`x ↦ 2x - x²`. A member's normalized value lies in `[1/2, 1]`, so its transformed
value lies in `[3/4, 1]`; nonmembers remain zero. Dyadic exponent padding supplies
AWPP's length-dependent denominator. This proof uses the verifier-based classes
and does not claim a nondeterministic counting-machine characterization.

## Main results

* `WPP_subset_AWPP`, `LWPP_subset_AWPP`.

## References

* [S. Fenner, L. Fortnow, S. Kurtz, L. Li, *An Oracle Builder's Toolkit*][FennerEtAl2003]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- Exact wide gaps can be normalized to bounded-error dyadic gaps. -/
theorem WPP_subset_AWPP : WPP enc ⊆ AWPP enc := by
  rintro A ⟨g, hg, f, hf, hf0, hrange, hA⟩
  let k a := (f a * f a).toNat
  have hk : ComputableInPolyTime k enc encNat :=
    ComputableInPolyTime.intBin_toNat.comp (hf.intBin_mul' hf)
  let r a := (encNat (k a)).length
  have hr : ComputableInPolyTime r enc encUnary :=
    (ComputableInPolyTime.encoding_length encNat).comp hk
  let D a : ℤ := 2 ^ r a
  have hD : D ∈ GapP enc := by
    have := SharpP.natCast_mem_GapP
      (mem_SharpP_of_polyTime ((ComputableInPolyTime.binary_two_pow.comp hr)))
    simpa only [Function.comp_apply, Nat.cast_pow, Nat.cast_ofNat, D] using this
  let G := g * g
  have hG : G ∈ GapP enc := GapP.mul_mem hg hg
  have hnum := GapP.sub_mem' (GapP.add_mem (GapP.mul_mem hG hD) (GapP.mul_mem hG hD))
    (GapP.mul_mem hG hG)
  refine mem_AWPP_of_polyTime_exponent hnum
    ((ComputableInPolyTime.unary_add.comp (hr.prod hr))) (fun a => ?_)
  have hkcast : (k a : ℤ) = f a * f a := Int.toNat_of_nonneg (mul_self_nonneg _)
  have hkpos : 0 < k a := by
    have := mul_self_pos.mpr (hf0 a)
    lia
  have hrs : r a = (k a).size := by simp [r, encNat_apply, Nat.size_eq_bits_len]
  have hlow : (2 : ℤ) ^ r a ≤ 2 * (k a : ℤ) := by
    have hs := Nat.size_pos.mpr hkpos
    have hl := Nat.lt_size.mp (show (k a).size - 1 < (k a).size by lia)
    have he : 2 ^ (k a).size = 2 * 2 ^ ((k a).size - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hs]
    rw [hrs]
    exact_mod_cast (show 2 ^ (k a).size ≤ 2 * k a by lia)
  have hupp : (k a : ℤ) ≤ (2 : ℤ) ^ r a := by
    rw [hrs]
    exact_mod_cast (Nat.lt_size_self (k a)).le
  have hDpos : 0 < D a := by dsimp [D]; positivity
  change (0 ≤ G a * D a + G a * D a - G a * G a ∧ _) ∧ _
  simp only [Function.comp_apply, pow_add]
  change (0 ≤ G a * D a + G a * D a - G a * G a ∧
      G a * D a + G a * D a - G a * G a ≤ D a * D a) ∧
    (a ∈ A → 2 * (D a * D a) ≤ 3 * (G a * D a + G a * D a - G a * G a)) ∧
    (a ∉ A → 3 * (G a * D a + G a * D a - G a * G a) ≤ D a * D a)
  change D a ≤ 2 * (k a : ℤ) at hlow
  change (k a : ℤ) ≤ D a at hupp
  rcases hrange a with hz | ht
  · have hn : a ∉ A := by rw [hA a, hz]; exact (hf0 a).symm
    have hG0 : G a = 0 := by simp [G, hz]
    simp [hG0, hn, mul_self_nonneg]
  · have hy : a ∈ A := (hA a).mpr ht
    have hGk : G a = (k a : ℤ) := by simp [G, ht, hkcast]
    rw [hGk]
    have hk0 : (0 : ℤ) ≤ k a := by positivity
    have hsq := sq_nonneg (D a - (k a : ℤ))
    have hprod := mul_nonneg (show 0 ≤ 2 * (k a : ℤ) - D a by lia)
      (show 0 ≤ D a - (k a : ℤ) by lia)
    have hmul := mul_nonneg hk0 (show 0 ≤ D a - (k a : ℤ) by lia)
    constructor
    · constructor <;> nlinarith
    · constructor
      · intro _
        nlinarith [sq_nonneg (k a : ℤ)]
      · exact fun hn => False.elim (hn hy)

/-- Length-dependent wide gaps are a special case of wide gaps. -/
theorem LWPP_subset_AWPP : LWPP enc ⊆ AWPP enc := fun _ h =>
  WPP_subset_AWPP (LWPP_subset_WPP h)

end Cslib.Complexity

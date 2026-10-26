/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.DiscreteLog
import Complexity.Tactic.PolyTime

/-!
# Polynomial Bit-Length Bounds for Encoded Group Elements

From the polynomial-time certificates for `order`, `generator`, and `smul` on a
`PrimeOrderGroupFamily`, together with generator surjectivity `smul_generator_surjective`, every
encoded group element `F.encode d x` has bit-length bounded by a fixed polynomial in the
description length `(F.encDesc d).length`.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.exists_length_encode_le`: uniform polynomial bound on
  `(F.encode d x).length` in terms of `(F.encDesc d).length`.
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Turing.MultiTapeTM

variable (F : PrimeOrderGroupFamily)

private theorem length_encNat_mono {m n : ℕ} (h : m ≤ n) :
    (encNat m).length ≤ (encNat n).length := by
  simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le_size h

/-- Every encoded group element `F.encode d x` has bit-length polynomially bounded in
`(F.encDesc d).length`. -/
theorem exists_length_encode_le :
    ∃ c k : ℕ, ∀ d : F.Desc, ∀ x : F.Carrier d,
      (F.encode d x).length ≤ c * ((F.encDesc d).length + 1) ^ k := by
  obtain ⟨co, ko, hord⟩ := F.computableInPolyTime_order.tidy.polyBounded_length.exists_le
  obtain ⟨cg, kg, hgen⟩ := F.computableInPolyTime_generator.tidy.polyBounded_length.exists_le
  obtain ⟨cs, ks, hsmul⟩ := F.computableInPolyTime_smul.tidy.polyBounded_length.exists_le
  have hpoly : PolynomiallyBounded
      (fun L => cs * (2 * L + 4 * (co * (L + 1) ^ ko) + 4 * (cg * (L + 1) ^ kg) + 7) ^ ks) := by
    fun_prop
  obtain ⟨c, k, hck⟩ := polynomiallyBounded_iff_le.mp hpoly
  refine ⟨c, k, fun d x => ?_⟩
  obtain ⟨α, rfl⟩ := F.smul_generator_surjective d x
  have hsmul_eq : F.encode d (α • F.generator d) =
      F.smul (d, α.val, F.encode d (F.generator d)) := by
    rw [F.smul_encode, ZMod.natCast_zmod_val]
  rw [hsmul_eq]
  have h1 := hsmul (d, α.val, F.encode d (F.generator d))
  simp only [encBits_apply] at h1 hgen
  have hα : (encNat α.val).length ≤ co * ((F.encDesc d).length + 1) ^ ko :=
    (length_encNat_mono (Nat.le_of_lt (ZMod.val_lt α))).trans (hord d)
  have hg := hgen d
  have hlen :
      (encPair F.encDesc (encPair encNat encBits)
        (d, α.val, F.encode d (F.generator d))).length + 1 ≤
      2 * (F.encDesc d).length + 4 * (co * ((F.encDesc d).length + 1) ^ ko) +
        4 * (cg * ((F.encDesc d).length + 1) ^ kg) + 7 := by
    simp only [length_encPair, encBits_apply]
    lia
  calc (F.smul (d, α.val, F.encode d (F.generator d))).length
      ≤ cs * ((encPair F.encDesc (encPair encNat encBits)
          (d, α.val, F.encode d (F.generator d))).length + 1) ^ ks := h1
    _ ≤ cs * (2 * (F.encDesc d).length + 4 * (co * ((F.encDesc d).length + 1) ^ ko) +
          4 * (cg * ((F.encDesc d).length + 1) ^ kg) + 7) ^ ks := by
        gcongr
    _ ≤ c * ((F.encDesc d).length + 1) ^ k := hck (F.encDesc d).length

end Cslib.Crypto.PrimeOrderGroupFamily

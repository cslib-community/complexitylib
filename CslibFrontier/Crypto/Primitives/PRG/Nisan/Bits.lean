/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRG.Nisan
public import CslibFrontier.Foundations.Data.BitString.Block
public import CslibFrontier.Probability.BitString.ToeplitzHash
public import Cslib.Foundations.Data.BitString
import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.Sampling
import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# Nisan's generator on bit strings

With the blocks the bit strings of length `n` and the Toeplitz hash family over `Bool`
(`Cslib.BitString.isPairwiseIndependentHash_toeplitzHash_bool`), Nisan's generator
`Cslib.Crypto.PRG.Nisan.bitGenerator n k` stretches a seed of `n + k (3 n - 1)` bits
(`Cslib.Crypto.PRG.Nisan.card_bitSeed`) into `2 ^ k n` bits, the `2 ^ k` blocks of
`Cslib.Crypto.PRG.Nisan.blocks` concatenated in order by `Cslib.BitString.blocksEquiv.symm`. A
read-once branching program on `2 ^ k n` bits regroups into a program on `2 ^ k` blocks of `n` bits
with the same states (`Cslib.BranchingPrograms.ReadOnceProgram.blocks`), so the generator fools
read-once branching programs of width `w` on bits with error `(2 ^ k - 1) w / (2 √(2 ^ n))`
(`Cslib.Crypto.PRG.Nisan.secure_bitGenerator`). For `n = 2 (k + a + d)` this is at most `2 ^ (-d)`
for width up to `2 ^ a` (`Cslib.Crypto.PRG.Nisan.secure_bitGenerator_of_le`): `O((k + a + d) k)`
seed bits fool programs of length `2 ^ k n`, width `2 ^ a` and error `2 ^ (-d)`. For width `w`,
length `R` and error `ε`, this is the seed length `O(log (w R / ε) log R)` of Nisan's generator
[Nisan1992], [Arora and Barak, Theorem 16.48][AroraBarak07], [Vadhan, Section 8.2.1][Vadhan2012],
the parametrized seed length of [Hatami and Hoza, Theorem 3.8][HatamiHoza2024], which the remark
after that theorem attributes to Nisan as well.

## Main definitions

* `Cslib.Crypto.PRG.Nisan.BitSeed`: the seeds of Nisan's generator on bit strings.
* `Cslib.Crypto.PRG.Nisan.bitGenerator`: Nisan's generator on bit strings.

## Main results

* `Cslib.Crypto.PRG.Nisan.card_bitSeed`: seeds have `n + k (3 n - 1)` bits.
* `Cslib.Crypto.PRG.Nisan.secure_bitGenerator`: Nisan's generator on bit strings is secure against
  read-once branching programs.
* `Cslib.Crypto.PRG.Nisan.secure_bitGenerator_of_le`: the parameters of Nisan's theorem.

## References

* [N. Nisan, *Pseudorandom generators for space-bounded computation*][Nisan1992]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak07], Section 16.7
* [S. Vadhan, *Pseudorandomness*][Vadhan2012], Section 8.2.1
* [P. Hatami, W. Hoza, *Paradigms for Unconditional Pseudorandom Generators*][HatamiHoza2024]
-/

@[expose] public section

namespace Cslib.Crypto.PRG.Nisan

open Cslib.BitString Cslib.BranchingPrograms Cslib.Probability Finset
open scoped NNReal

/-- The seeds of Nisan's generator on bit strings of length `n` with `k` hash seeds: a block of
`n` bits and `k` seeds of the Toeplitz hash, each a Toeplitz matrix of `2 n - 1` bits and an offset
of `n` bits. -/
abbrev BitSeed (n k : ℕ) : Type :=
  BitString n × (Fin k → (Fin (n + n - 1) → Bool) × BitString n)

/-- **The seed length of Nisan's generator on bit strings**: `n + k (3 n - 1)` bits. -/
theorem card_bitSeed (n k : ℕ) : Fintype.card (BitSeed n k) = 2 ^ (n + k * (3 * n - 1)) := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
    ← pow_add, ← pow_mul, ← pow_add]
  rw [show n + n - 1 + n = 3 * n - 1 by omega, Nat.mul_comm]

/-- **Nisan's generator on bit strings**: the `2 ^ k` blocks of `n` bits of Nisan's generator with
the Toeplitz hash family over `Bool`, concatenated in order. -/
def bitGenerator (n k : ℕ) : Generator (BitSeed n k) (BitString (2 ^ k * n)) :=
  ⟨fun z => blocksEquiv.symm (blocks toeplitzHash k z.1 z.2)⟩

@[simp] theorem bitGenerator_apply (n k : ℕ) (z : BitSeed n k) :
    bitGenerator n k z = blocksEquiv.symm (blocks toeplitzHash k z.1 z.2) :=
  rfl

/-- **Nisan's generator on bit strings fools read-once branching programs** [Nisan1992]: no
read-once branching program of width `w` on `2 ^ k n` bits distinguishes the output of
`bitGenerator n k` from a uniform bit string with advantage more than
`(2 ^ k - 1) w / (2 √(2 ^ n))`. -/
theorem secure_bitGenerator (n k w : ℕ) :
    (bitGenerator n k).Secure (IsReadOnceTest w)
      ((2 ^ k - 1) * w / (2 * NNReal.sqrt (2 ^ n))) := by
  rintro _ ⟨P, rfl⟩
  rw [Generator.advantage, Generator.toReal_realExperiment_pure,
    Generator.toReal_idealExperiment_pure]
  have huni : (dens {y : BitString (2 ^ k * n) | P.eval y = true} : ℝ) =
      dens {u : Fin (2 ^ k) → BitString n | P.blocks.eval u = true} := by
    simp only [← Fintype.expect_boole, ReadOnceProgram.eval_blocks]
    exact (Fintype.expect_equiv blocksEquiv.symm
      (fun u => if P.eval (blocksEquiv.symm u) = true then (1 : ℝ) else 0)
      (fun y => if P.eval y = true then (1 : ℝ) else 0) fun _ => rfl).symm
  have hgen : (dens {z : BitSeed n k | P.eval (bitGenerator n k z) = true} : ℝ) =
      dens {z : BitSeed n k | P.blocks.eval (blocks toeplitzHash k z.1 z.2) = true} := by
    simp only [ReadOnceProgram.eval_blocks]
    rfl
  have hk : (1 : ℝ≥0) ≤ 2 ^ k := one_le_pow₀ one_le_two
  have := abs_dens_eval_blocks_sub_le isPairwiseIndependentHash_toeplitzHash_bool k P.blocks
  rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
  rw [hgen, huni]
  simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_sub hk, NNReal.coe_pow, NNReal.coe_ofNat,
    NNReal.coe_one, NNReal.coe_natCast, Real.coe_sqrt]
  exact_mod_cast this

/-- **Nisan's generator on bit strings of even length**: for `n = 2 m`, the advantage of read-once
branching programs of width `w` is at most `(2 ^ k - 1) w / 2 ^ (m + 1)`. -/
theorem secure_bitGenerator_two_mul (m k w : ℕ) :
    (bitGenerator (2 * m) k).Secure (IsReadOnceTest w) ((2 ^ k - 1) * w / 2 ^ (m + 1)) := by
  have hsqrt : NNReal.sqrt (2 ^ (2 * m)) = 2 ^ m := by
    rw [Nat.mul_comm, pow_mul, NNReal.sqrt_sq]
  have h := secure_bitGenerator (2 * m) k w
  rwa [hsqrt, ← pow_succ'] at h

/-- **The parameters of Nisan's generator** [Nisan1992]: with blocks of `n = 2 (k + a + d)` bits,
Nisan's generator on bit strings stretches `O((k + a + d) k)` seed bits into `2 ^ k n` bits that
fool every read-once branching program of width at most `2 ^ a` with error `2 ^ (-d)`. -/
theorem secure_bitGenerator_of_le (k a d w : ℕ) (hw : w ≤ 2 ^ a) :
    (bitGenerator (2 * (k + a + d)) k).Secure (IsReadOnceTest w) (2 ^ d)⁻¹ := by
  refine fun A hA => (secure_bitGenerator_two_mul (k + a + d) k w A hA).trans ?_
  have hk : (1 : ℝ≥0) ≤ 2 ^ k := one_le_pow₀ one_le_two
  have hw' : (w : ℝ≥0) ≤ 2 ^ a := by exact_mod_cast hw
  have hle : ((2 ^ k - 1) * w / 2 ^ (k + a + d + 1) : ℝ≥0) ≤ (2 ^ d)⁻¹ := by
    rw [div_le_iff₀ (by positivity), pow_succ, pow_add, pow_add, inv_mul_eq_div]
    calc (2 ^ k - 1) * (w : ℝ≥0) ≤ 2 ^ k * 2 ^ a :=
          mul_le_mul tsub_le_self hw' (by positivity) (by positivity)
      _ ≤ 2 ^ k * 2 ^ a * 2 ^ d * 2 / 2 ^ d := by
          rw [mul_assoc (2 ^ k * 2 ^ a), mul_div_assoc, mul_div_cancel_left₀ _ (by positivity)]
          exact le_mul_of_one_le_right (by positivity) one_le_two
  exact_mod_cast hle

end Cslib.Crypto.PRG.Nisan

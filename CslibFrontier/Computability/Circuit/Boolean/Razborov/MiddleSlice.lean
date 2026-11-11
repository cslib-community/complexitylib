/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Razborov.RankProperty
public import CslibFrontier.Computability.Complexity.Classes.P.Slices
public import Mathlib.Data.Nat.Sqrt
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# A middle slice in P but not in AC⁰[2]

The **middle slice** (`middleSlice`) accepts the `n`-bit strings with exactly `a(n)` zeros, where
`a(n) = ⌈n / 2⌉ - ⌊√(n + 1)⌋ / 10` (`sliceLevel`). It passes Razborov's rank test at level `a(n)`
(`middleSlice_mem_rankTest`), so the size–depth tradeoff of the rank test
(`two_mul_two_pow_le_size_of_mem_rankTest`) bounds every constant-depth circuit for it with `MOD_2`
gates from below by `2 ^ Ω(n ^ (1 / (2 d)))`. Hence the middle slice is not in AC⁰[2]
(`middleSlice_notMem_AC0Mod_two`) [Razborov1987]. It is in `P`, by counting the true bits and
comparing with `a(n)` computed in unary from the length (`middleSlice_mem_P`), which separates
`P` from AC⁰[2] (`exists_mem_P_notMem_AC0Mod_two`).

`Cslib.Circuits.Boolean.exists_mem_P_notMem_AC0Mod` gives the separation for odd primes through
parity; this module covers `p = 2`, where parity is a single gate.

The lower bound follows the rank argument as recorded by
[Razborov and Rudich, §3.2][RazborovRudich1997] and sketched for `p = 2` by
[Carmosino et al., p. 10:20][CarmosinoImpagliazzoKabanetsKolokolova2016],
in the variant described in `Cslib.Circuits.Boolean.Razborov.RankProperty`. The choice of slice
(an exact-weight function at distance about `√n / 10` below the middle) is made so that the
parameters of that variant apply; Razborov's original argument [Razborov1987] was not checked for
its choice of hard function.

## Main definitions

* `Cslib.Circuits.Boolean.Razborov.sliceGap`: the gap `⌊√(n + 1)⌋ / 10`.
* `Cslib.Circuits.Boolean.Razborov.sliceLevel`: the level `⌈n / 2⌉ - ⌊√(n + 1)⌋ / 10`.
* `Cslib.Circuits.Boolean.Razborov.middleSlice`: the strings with exactly `sliceLevel n` zeros.

## Main results

* `Cslib.Circuits.Boolean.Razborov.middleSlice_mem_rankTest`: the slice passes the rank test.
* `Cslib.Circuits.Boolean.Razborov.middleSlice_notMem_AC0Mod_two`: the slice is not in AC⁰[2].
* `Cslib.Circuits.Boolean.Razborov.middleSlice_mem_P`: the slice is in `P`.
* `Cslib.Circuits.Boolean.Razborov.exists_mem_P_notMem_AC0Mod_two`: `P ⊄ AC⁰[2]`.

## References

* [A. A. Razborov, *Lower bounds on the size of bounded depth circuits over a complete basis with
  logical addition*][Razborov1987]
* [A. A. Razborov, S. Rudich, *Natural proofs*][RazborovRudich1997]
* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016]
-/

public section

namespace Cslib.Circuits.Boolean.Razborov

open BitString Cslib.Complexity Turing.MultiTapeTM

/-- The gap of the middle slice below the middle, `⌊√(n + 1)⌋ / 10`. -/
def sliceGap (n : ℕ) : ℕ := Nat.sqrt (n + 1) / 10

/-- The level of the middle slice, `⌈n / 2⌉ - ⌊√(n + 1)⌋ / 10`. -/
def sliceLevel (n : ℕ) : ℕ := (n + 1) / 2 - sliceGap n

/-- The **middle slice**: the `n`-bit strings with exactly `sliceLevel n` zeros, that is, of
weight `n - sliceLevel n`. -/
def middleSlice (n : ℕ) : BooleanFunction n := exactWeight (n - sliceLevel n)

/-- The level of the middle slice, unfolded. -/
theorem sliceLevel_eq (n : ℕ) : sliceLevel n = (n + 1) / 2 - Nat.sqrt (n + 1) / 10 := by
  rw [sliceLevel, sliceGap]

/-- The middle slice holds exactly at the points of weight `n - sliceLevel n`. -/
@[simp] theorem middleSlice_eq_true_iff {n : ℕ} {x : BitString n} :
    middleSlice n x = true ↔ weight x = n - sliceLevel n := by
  rw [middleSlice, exactWeight_eq_true_iff]

/-- The gap satisfies `100 · gap² ≤ n + 1`. -/
private theorem hundred_mul_sliceGap_sq_le (n : ℕ) : 100 * sliceGap n ^ 2 ≤ n + 1 := by
  have h10 : 10 * sliceGap n ≤ Nat.sqrt (n + 1) := by
    rw [sliceGap, mul_comm]
    exact Nat.div_mul_le_self _ 10
  calc 100 * sliceGap n ^ 2 = (10 * sliceGap n) ^ 2 := by ring
    _ ≤ Nat.sqrt (n + 1) ^ 2 := Nat.pow_le_pow_left h10 2
    _ ≤ n + 1 := Nat.sqrt_le' (n + 1)

/-- When `100 m² ≤ n + 1`, the gap is at least `m`. -/
private theorem le_sliceGap {m n : ℕ} (hn : 100 * m ^ 2 ≤ n + 1) : m ≤ sliceGap n := by
  have h : 10 * m ≤ Nat.sqrt (n + 1) :=
    Nat.le_sqrt'.mpr (by rw [show (10 * m) ^ 2 = 100 * m ^ 2 by ring]; exact hn)
  rw [sliceGap]
  exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)

/-- The middle slice passes the rank test at level `sliceLevel n`. -/
theorem middleSlice_mem_rankTest (n : ℕ) : middleSlice n ∈ rankTest n (sliceLevel n) :=
  exactWeight_mem_rankTest _

/-- **The middle slice is not in AC⁰[2]** [Razborov1987]: constant-depth, polynomial-size circuits
of negations, unbounded fan-in conjunctions and disjunctions, and `MOD_2` gates do not decide it. -/
theorem middleSlice_notMem_AC0Mod_two : Language.ofSlices middleSlice ∉ AC0Mod 2 := by
  intro h
  obtain ⟨d, size, hsize, hC⟩ := ConstDepth.mem_iff.1 h
  -- the size bound at the lengths `100 (ℓ ^ d + 1)²` is a polynomial in `ℓ`
  have hpoly : PolynomiallyBounded fun ℓ =>
      5 * (100 * (ℓ ^ d + 1) ^ 2 + 1) * size (100 * (ℓ ^ d + 1) ^ 2) :=
    PolynomiallyBounded.mul (by fun_prop) (hsize.comp (by fun_prop))
  obtain ⟨ℓ, hlt, hℓ⟩ := (hpoly.eventually_lt_two_pow.and (Filter.eventually_ge_atTop 1)).exists
  set n := 100 * (ℓ ^ d + 1) ^ 2 with hn
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  rw [Language.slice_ofSlices] at hCc
  have hgap : ℓ ^ d + 1 ≤ sliceGap n := le_sliceGap (by omega)
  have hdepth : ℓ ^ C.depth ≤ ℓ ^ d := Nat.pow_le_pow_right hℓ hCd
  have htrade := two_mul_two_pow_le_size_of_mem_rankTest (by omega) (hundred_mul_sliceGap_sq_le n)
    (middleSlice_mem_rankTest n) hCc hℓ (by omega)
  have hsz : 5 * (n + 1) * C.size ≤ 5 * (n + 1) * size n := Nat.mul_le_mul_left _ hCs
  have hlt' : 5 * (n + 1) * size n < 2 ^ ℓ := hlt
  omega

/-- The list evaluator of the middle slice: count the true bits and compare with
`n - sliceLevel n`, where `n` is the length. -/
private theorem middleSlice_ofList (x : List Bool) :
    middleSlice x.length (ofList x.length x) =
      decide (x.count true = x.length - ((x.length + 1) / 2 - Nat.sqrt (x.length + 1) / 10)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, middleSlice_eq_true_iff, ← count_true_ofFn,
    ofFn_ofList rfl, sliceLevel_eq]

/-- **The middle slice is in `P`**: count the true bits in unary and compare with
`n - sliceLevel n`, computed in unary from the length `n` (the square root in binary). -/
theorem middleSlice_mem_P : (Language.ofSlices middleSlice : Set (List Bool)) ∈ P encBits := by
  refine ofSlices_mem_P ?_
  simp only [middleSlice_ofList]
  have hlen : ComputableInPolyTime (fun x : List Bool => x.length) encBits encUnary :=
    ComputableInPolyTime.length_bits
  have hsucc : ComputableInPolyTime (fun x : List Bool => x.length + 1) encBits encUnary :=
    ComputableInPolyTime.unary_add' hlen (.const 1)
  have hsqrt : ComputableInPolyTime (fun x : List Bool => Nat.sqrt (x.length + 1)) encBits
      encUnary :=
    ComputableInPolyTime.binary_to_unary_bounded
      (ComputableInPolyTime.binary_sqrt' (ComputableInPolyTime.unary_to_binary.comp hsucc)) hsucc
      fun x => Nat.sqrt_le_self _
  have hgap : ComputableInPolyTime (fun x : List Bool => Nat.sqrt (x.length + 1) / 10) encBits
      encUnary :=
    ComputableInPolyTime.unary_div' hsqrt (.const 10)
  have hlevel : ComputableInPolyTime
      (fun x : List Bool => (x.length + 1) / 2 - Nat.sqrt (x.length + 1) / 10) encBits encUnary :=
    ComputableInPolyTime.unary_sub' (ComputableInPolyTime.unary_div' hsucc (.const 2)) hgap
  have hcount : ComputableInPolyTime (fun x : List Bool => x.count true) encBits encUnary :=
    ComputableInPolyTime.bitsCountWithInput ComputableInPolyTime.id' (.const true)
  exact ComputableInPolyTime.unary_eq' hcount (ComputableInPolyTime.unary_sub' hlen hlevel)

/-- **Unconditional separation `P ⊄ AC⁰[2]`**: the middle slice is in `P` and not in AC⁰[2]
[Razborov1987]. Together with `Cslib.Circuits.Boolean.exists_mem_P_notMem_AC0Mod` for odd primes,
`P ⊄ AC⁰[p]` holds for every prime `p`. -/
theorem exists_mem_P_notMem_AC0Mod_two :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧ L ∉ AC0Mod 2 :=
  ⟨_, middleSlice_mem_P, middleSlice_notMem_AC0Mod_two⟩

end Cslib.Circuits.Boolean.Razborov

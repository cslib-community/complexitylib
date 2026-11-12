/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.NaturalProof.ConstDepth
public import CslibFrontier.Computability.Circuit.Boolean.Razborov.MiddleSlice
public import CslibFrontier.Computability.Circuit.Boolean.Razborov.Natural
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# The rank property is useful against AC⁰[2]

Along the level `sliceLevel n = ⌈n / 2⌉ - ⌊√(n + 1)⌋ / 10`, the rank property
`Cslib.Circuits.Boolean.Razborov.rankProperty` is useful against AC⁰[2]: for every depth and
polynomial size bound, eventually no circuit with `MOD_2` gates of that depth and size computes a
function passing the rank test (`isUseful_AC0Mod_two_rankProperty`). With
`Cslib.Circuits.Boolean.Razborov.isNatural_PPoly_rankProperty`, the rank property is a
`P/poly`-natural property useful against AC⁰[2]
(`isNatural_PPoly_and_isUseful_AC0Mod_two_rankProperty`).

The explicit form says how many input variables suffice. For depth `d` and size `2 ^ x`, at the
input length `rankLength d x` no circuit of depth at most `d` and at most `2 ^ x` gates computes a
member of the rank property (`notMem_rankProperty_rankLength_of_computes`), and for `x ≥ 1` that
input length is polylogarithmic in the size:
`rankLength d x + 1 ≤ 401 · 2 ^ (2 d (2 d + 7)) · x ^ (2 d)` (`rankLength_add_one_le`). So for
fixed `d` the truth tables, of length `2 ^ rankLength d x`, have length `2 ^ O((log S) ^ (2 d))`,
quasi-polynomial in the size `S`. This is the explicit form of the usefulness bound
`2 ^ Ω(n ^ (1 / (2 d)))` of
[Carmosino et al., Theorem 5.3][CarmosinoImpagliazzoKabanetsKolokolova2016].

Labels. The property is this library's variant of Razborov's rank property (one square matrix, the
threshold `C(n, a) / 2`, the level above), described in
`Cslib.Circuits.Boolean.Razborov.RankProperty`. Constructivity is circuit size only (`P/poly`,
De Morgan circuits of size `173 · 8 ^ n`), not the `NC²` of the sources; depth is not certified.
Only `p = 2` is covered. The constants are this library's.

The learning consequence for `p = 2`, Corollary 5.4 of
[Carmosino et al.][CarmosinoImpagliazzoKabanetsKolokolova2016] with queries and hypothesis size
counted, is `CslibFrontier.MachineLearning.UniformLearning.CIKK.AC0Mod`. Their Theorem 5.1 in its
abstract form, from any natural property useful against a class, stays open under
[#798](https://github.com/cslib-community/cslib-frontier/issues/798).

## Main definitions

* `Cslib.Circuits.Boolean.Razborov.rankLength d x`: an input length (number of variables) at which
  the rank test rejects every circuit of depth at most `d` and at most `2 ^ x` gates.

## Main results

* `Cslib.Circuits.Boolean.Razborov.isUseful_AC0Mod_two_rankProperty`: usefulness against AC⁰[2].
* `Cslib.Circuits.Boolean.Razborov.isNatural_PPoly_and_isUseful_AC0Mod_two_rankProperty`: the rank
  property is `P/poly`-natural and useful against AC⁰[2].
* `Cslib.Circuits.Boolean.Razborov.notMem_rankProperty_rankLength_of_computes`: explicit
  usefulness at the length `rankLength d x`.
* `Cslib.Circuits.Boolean.Razborov.rankLength_add_one_le`: for `x ≥ 1`, that input length is
  polylogarithmic in the size.

## References

* [A. A. Razborov, S. Rudich, *Natural proofs*, §3.2][RazborovRudich1997]
* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*, Theorem 5.3 (p. 10:19) and the `p = 2` property (p. 10:20)]
  [CarmosinoImpagliazzoKabanetsKolokolova2016]
-/

public section

namespace Cslib.Circuits.Boolean.Razborov

open Filter NaturalProof

/-! ### Usefulness -/

/-- **The rank property is useful against AC⁰[2]** [RazborovRudich1997]
[CarmosinoImpagliazzoKabanetsKolokolova2016]: along the level `sliceLevel`, the slices of every
language in AC⁰[2] eventually fail the rank test. -/
theorem isUseful_AC0Mod_two_rankProperty : IsUseful (AC0Mod 2) (rankProperty sliceLevel) := by
  refine IsUseful.of_eventually_constDepth (I := Unbounded.extInterpretation (modGate 2))
    fun d s hs => ?_
  obtain ⟨c, k, hsk⟩ := polynomiallyBounded_iff_le.1 hs
  -- the size bound in terms of `ℓ`, where `m + 1 ≤ 100 ((ℓ + 1) ^ (d + 1) + 1) ^ 2 + 1`
  have hpoly : PolynomiallyBounded fun ℓ =>
      5 * (100 * ((ℓ + 1) ^ (d + 1) + 1) ^ 2 + 1) *
        (c * (100 * ((ℓ + 1) ^ (d + 1) + 1) ^ 2 + 1) ^ k) := by
    fun_prop
  obtain ⟨L, hL⟩ := eventually_atTop.1
    (hpoly.eventually_lt_two_pow.and (eventually_ge_atTop 1))
  filter_upwards [eventually_ge_atTop (100 * (L ^ (d + 1) + 1) ^ 2 + L)] with m hm Cm hCd hCs f hf
    hCc
  -- the largest `ℓ ≤ m` with `100 (ℓ ^ (d + 1) + 1) ^ 2 ≤ m + 1`
  set j := Nat.findGreatest (fun ℓ => 100 * (ℓ ^ (d + 1) + 1) ^ 2 ≤ m + 1) m with hj
  have hPL : 100 * (L ^ (d + 1) + 1) ^ 2 ≤ m + 1 := by omega
  have hLj : L ≤ j := Nat.le_findGreatest (by omega) hPL
  have hjm : 100 * (j ^ (d + 1) + 1) ^ 2 ≤ m + 1 := by
    rw [hj]
    exact Nat.findGreatest_spec (P := fun ℓ => 100 * (ℓ ^ (d + 1) + 1) ^ 2 ≤ m + 1) (m := L)
      (by omega) hPL
  -- maximality: `m + 1 ≤ Q`
  have hQ : m + 1 ≤ 100 * ((j + 1) ^ (d + 1) + 1) ^ 2 + 1 := by
    rcases Nat.lt_or_ge j m with hlt | hge
    · have := Nat.findGreatest_is_greatest (P := fun ℓ => 100 * (ℓ ^ (d + 1) + 1) ^ 2 ≤ m + 1)
        (n := m) (k := j + 1) (by rw [← hj]; omega) (by omega)
      simp only [not_le] at this
      omega
    · have : j + 1 ≤ (j + 1) ^ (d + 1) := Nat.le_self_pow (by omega) _
      have : (j + 1) ^ (d + 1) + 1 ≤ ((j + 1) ^ (d + 1) + 1) ^ 2 :=
        Nat.le_self_pow (by omega) _
      omega
  obtain ⟨hlt, hj1⟩ := hL j hLj
  rw [rankProperty_apply] at hf
  have htrade := two_mul_two_pow_le_size_of_mem_rankTest_sliceLevel hj1 hjm hf hCc
    (hCd.trans (Nat.le_succ d))
  have hsize : Cm.size ≤ c * (100 * ((j + 1) ^ (d + 1) + 1) ^ 2 + 1) ^ k :=
    hCs.trans ((hsk m).trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left hQ k)))
  have : 5 * (m + 1) * Cm.size ≤
      5 * (100 * ((j + 1) ^ (d + 1) + 1) ^ 2 + 1) *
        (c * (100 * ((j + 1) ^ (d + 1) + 1) ^ 2 + 1) ^ k) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 5 hQ) hsize
  have h2 : 2 ^ j ≤ 2 * 2 ^ j := Nat.le_mul_of_pos_left _ (by norm_num)
  omega

/-- **The rank property is a natural property useful against AC⁰[2]**
[RazborovRudich1997] [CarmosinoImpagliazzoKabanetsKolokolova2016]: along the level `sliceLevel`,
it is `P/poly`-natural and useful against AC⁰[2]. -/
theorem isNatural_PPoly_and_isUseful_AC0Mod_two_rankProperty :
    IsNatural PPoly (rankProperty sliceLevel) ∧ IsUseful (AC0Mod 2) (rankProperty sliceLevel) :=
  ⟨isNatural_PPoly_rankProperty sliceLevel, isUseful_AC0Mod_two_rankProperty⟩

/-! ### Explicit usefulness -/

/-- The exponent `⌊log₂ x⌋ + 2 d + 7` of the parameter `ℓ = 2 ^ rankExponent d x`. -/
private def rankExponent (d x : ℕ) : ℕ := Nat.log 2 x + 2 * d + 7

/-- An input length (number of variables) for depth `d` and size `2 ^ x`: `100 (ℓ ^ d + 1)²` with
`ℓ = 2 ^ (⌊log₂ x⌋ + 2 d + 7)`. Truth tables at this length have `2 ^ rankLength d x` entries. -/
def rankLength (d x : ℕ) : ℕ := 100 * ((2 ^ rankExponent d x) ^ d + 1) ^ 2

/-- `(d + 1)² ≤ 4 ^ d`. -/
private theorem add_one_sq_le_two_pow_mul_two_pow (d : ℕ) : (d + 1) ^ 2 ≤ 2 ^ d * 2 ^ d := by
  have h : d + 1 ≤ 2 ^ d := Nat.lt_two_pow_self
  rw [sq]
  exact Nat.mul_le_mul h h

/-- The length `rankLength d x` beats the size `2 ^ x`: `5 (m + 1) 2 ^ x < 2 · 2 ^ ℓ`. -/
private theorem five_mul_rankLength_lt (d x : ℕ) :
    5 * (rankLength d x + 1) * 2 ^ x < 2 * 2 ^ (2 ^ rankExponent d x) := by
  unfold rankLength rankExponent
  set g := Nat.log 2 x
  have hx : x + 1 ≤ 2 ^ (g + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  have hg : g + 2 ≤ 2 ^ (g + 1) := Nat.lt_two_pow_self
  have hD := add_one_sq_le_two_pow_mul_two_pow d
  set P := 2 ^ (g + 1)
  set U := 2 ^ d * 2 ^ d
  have hT : 2 ^ (g + 2 * d + 7) = P * 64 * U := by
    simp only [P, U, ← pow_add]
    rw [show 64 = 2 ^ 6 by norm_num, ← pow_add, ← pow_add]
    ring_nf
  -- the key exponent bound: `10 + 2 d t + x ≤ 2 ^ t` for `t = g + 2 d + 7`
  have hkey : 10 + 2 * d * (g + 2 * d + 7) + x ≤ P * 64 * U := by
    have hP : 1 ≤ P := Nat.one_le_two_pow
    have h1 : d * g ≤ d * P := Nat.mul_le_mul_left d (by omega)
    have h2 : (d + 1) ^ 2 * P ≤ U * P := Nat.mul_le_mul_right P hD
    have h3 : d * d ≤ d * d * P := Nat.le_mul_of_pos_right _ (by omega)
    have h4 : d ≤ d * P := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  set w := (2 ^ (g + 2 * d + 7)) ^ d
  rw [hT]
  have hw : 1 ≤ w := Nat.one_le_pow _ _ (by positivity)
  have hw2 : w * w = 2 ^ (2 * d * (g + 2 * d + 7)) := by
    simp only [w, ← pow_mul, ← pow_add]
    ring_nf
  have hsq : 100 * (w + 1) ^ 2 + 1 ≤ 401 * (w * w) := by nlinarith
  calc 5 * (100 * (w + 1) ^ 2 + 1) * 2 ^ x
      ≤ 5 * (401 * (w * w)) * 2 ^ x := by gcongr
    _ < 2 ^ 11 * 2 ^ (2 * d * (g + 2 * d + 7)) * 2 ^ x := by
        rw [hw2]
        have : 0 < 2 ^ (2 * d * (g + 2 * d + 7)) * 2 ^ x := by positivity
        nlinarith
    _ = 2 ^ (11 + 2 * d * (g + 2 * d + 7) + x) := by rw [pow_add, pow_add]
    _ ≤ 2 ^ (1 + P * 64 * U) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 * 2 ^ (P * 64 * U) := by rw [pow_add, pow_one]

/-- **Explicit usefulness against AC⁰[2]**: at the input length `rankLength d x`, no circuit with
`MOD_2` gates of depth at most `d` and at most `2 ^ x` gates computes a function of the rank
property. -/
theorem notMem_rankProperty_rankLength_of_computes {d x : ℕ}
    {C : Circuit Unbounded.extSignature (rankLength d x) 1} (hCd : C.depth ≤ d)
    (hCs : C.size ≤ 2 ^ x) {f : BooleanFunction (rankLength d x)}
    (hC : C.Computes (Unbounded.extInterpretation (modGate 2)) (single f)) :
    f ∉ rankProperty sliceLevel (rankLength d x) := by
  intro hf
  rw [rankProperty_apply] at hf
  have hℓ : 1 ≤ 2 ^ rankExponent d x := Nat.one_le_two_pow
  have hm : 100 * ((2 ^ rankExponent d x) ^ d + 1) ^ 2 ≤ rankLength d x + 1 := by
    unfold rankLength
    omega
  have htrade := two_mul_two_pow_le_size_of_mem_rankTest_sliceLevel hℓ hm hf hC hCd
  have hlt := five_mul_rankLength_lt d x
  have : 5 * (rankLength d x + 1) * C.size ≤ 5 * (rankLength d x + 1) * 2 ^ x :=
    Nat.mul_le_mul_left _ hCs
  omega

/-- **The input length is polylogarithmic in the size**: for `x ≥ 1`,
`rankLength d x + 1 ≤ 401 · 2 ^ (2 d (2 d + 7)) · x ^ (2 d)`, so truth tables of length
`2 ^ rankLength d x` are quasi-polynomial in the size `2 ^ x`. -/
theorem rankLength_add_one_le {d x : ℕ} (hx : 1 ≤ x) :
    rankLength d x + 1 ≤ 401 * 2 ^ (2 * d * (2 * d + 7)) * x ^ (2 * d) := by
  unfold rankLength rankExponent
  have hlog : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 (by omega)
  have hℓ : 2 ^ (Nat.log 2 x + 2 * d + 7) ≤ x * 2 ^ (2 * d + 7) := by
    rw [show Nat.log 2 x + 2 * d + 7 = Nat.log 2 x + (2 * d + 7) by ring, pow_add]
    exact Nat.mul_le_mul_right _ hlog
  set w := (2 ^ (Nat.log 2 x + 2 * d + 7)) ^ d
  have hw : 1 ≤ w := Nat.one_le_pow _ _ (by positivity)
  have hww : w * w ≤ (x * 2 ^ (2 * d + 7)) ^ (2 * d) := by
    rw [← sq, ← pow_mul, mul_comm d 2]
    exact Nat.pow_le_pow_left hℓ _
  calc 100 * (w + 1) ^ 2 + 1 ≤ 401 * (w * w) := by nlinarith
    _ ≤ 401 * (x * 2 ^ (2 * d + 7)) ^ (2 * d) := Nat.mul_le_mul_left _ hww
    _ = 401 * 2 ^ (2 * d * (2 * d + 7)) * x ^ (2 * d) := by
        rw [mul_pow, ← pow_mul]
        ring_nf

end Cslib.Circuits.Boolean.Razborov

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.RelativeRank
public import Complexity.Computability.Circuit.Arithmetic.Word
public import Complexity.Computability.Circuit.Arithmetic.VP
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexity.Foundations.LinearAlgebra.Matrix.ListProd

/-!
# Word polynomials and iterated matrix multiplication

The hard polynomials of Limaye, Srinivasan and Tavenas [LimayeSrinivasanTavenas2021, §2.2]. A
*word* is a tuple `w : Fin d → ℤ` (`Cslib.Circuits.Arithmetic.Word`). Its variables `X(w)`
(`WordVar w`) form `d` blocks, block `i` having `2 ^ |w i|` variables labelled by the bit strings
of length `|w i|`; here a bit string of length `a` is a number below `2 ^ a`, its first bit the
least significant. The blocks with `0 ≤ w i` are *positive* (`wordPos w`), the others *negative*
(`wordNeg w`). A set-multilinear monomial `m` on all blocks (`WordChoice w`) has a *positive
string* `σ(m⁺)`, the labels of its positive variables concatenated in order, and a *negative
string* `σ(m⁻)`. LST's word polynomial `P_w` is the sum of the monomials whose two strings are
prefix-related: the shorter is a prefix of the longer (`wordPolyAllSinks`).

The word polynomial *with sink `τ`* (`wordPoly K w τ`) is the sum of the monomials whose shorter
string is a prefix of the longer one with rest exactly `τ`: `σ(m⁺) = σ(m⁻) τ` when
`∑ i, w i ≥ 0`, and `σ(m⁻) = σ(m⁺) τ` otherwise. LST's `P_w` is the sum of these over all `τ` of
length `|∑ i, w i|` (`sum_wordPoly`).

* **Full rank** (LST §2.2, p. 7, "the matrices `M_w(P_w)` are full-rank"). For each sink, the
  relative-rank matrix of `wordPoly K w τ` with rows the positive and columns the negative blocks
  has rank equal to the smaller of its dimensions (`rank_relMatrix_wordPoly`), so its relative rank
  is `2 ^ (-|∑ i, w i| / 2)` (`relRank_wordPoly`), the largest value LST Claim 7(1) allows.
* **Lemma 8** (LST §2.2 and §8). If `w` is `b`-unbiased (`IsUnbiased w b`: every prefix sum has
  absolute value at most `b`) and `2 ^ b ≤ n`, then `wordPoly K w τ` is a projection of the
  iterated matrix multiplication polynomial `imm K n d`, the entry `(0, 0)` of the product of `d`
  generic `n × n` matrices (`isProjection_wordPoly_imm`). The substitution `wordSubst` maps each
  variable of matrix `i` to a variable of block `i` of `X(w)` or to `0` (`wordSubst_eq_inl`,
  `wordSubst_eq_inr`), so it maps set-multilinear computations to set-multilinear computations.

The proof follows LST's branching program (Lemma 22): after reading the first `i` blocks, the
state is the unmatched rest of the longer string (`wordRestAt`), a string of length
`|∑ j < i, w j| ≤ b`, and each block changes it by one step (`wordStep`, `wordRestAt_succ`), whose
label is determined by its two ends (`wordStep_inj`). Expanding the entry of the matrix product as
a sum over paths (`Matrix.list_prod_ofFn_apply`), exactly one path of states contributes each
monomial with rest `τ`, and none contributes the others.

**Original.** LST's branching program identifies all the vertices of its last layer, so the last
matrix of their substitution has sums of variables as entries and the substitution is linear, not
a projection (their proof of Lemma 8, §8, p. 20, speaks of "linear substitutions"). Fixing one
sink `τ` keeps one vertex of the last layer instead: the substitution becomes a projection, and
full rank holds for every sink. The fixed-sink polynomial, the numeric encoding of bit strings,
the step function `wordStep` and the non-asymptotic hypotheses `IsUnbiased w b` and `2 ^ b ≤ n`
are original to this formalization.

## Main definitions

* `Cslib.Circuits.Arithmetic.prefixRest`: comparison of two bit strings.
* `Cslib.Circuits.Arithmetic.wordStringLen`, `Cslib.Circuits.Arithmetic.wordStringVal`,
  `Cslib.Circuits.Arithmetic.wordPrefixSum`: the lengths and values of the strings read from the
  first blocks of a word, and its prefix sums.
* `Cslib.Circuits.Arithmetic.wordRest`: comparison of the positive and negative strings of a
  monomial.
* `Cslib.Circuits.Arithmetic.wordPoly`: the word polynomial with sink `τ`.
* `Cslib.Circuits.Arithmetic.wordPolyAllSinks`: LST's word polynomial `P_w`.
* `Cslib.Circuits.Arithmetic.imm`: the iterated matrix multiplication polynomial `IMM_{n,d}`.
* `Cslib.Circuits.Arithmetic.wordSubst`: the substitution of Lemma 8.

## Main results

* `Cslib.Circuits.Arithmetic.coeff_wordPoly`: the coefficients of the word polynomial.
* `Cslib.Circuits.Arithmetic.isSetMultilinear_wordPoly`: it is set-multilinear on all blocks.
* `Cslib.Circuits.Arithmetic.sum_wordPoly`: `P_w` is the sum of the word polynomials with
  the sinks of length `|∑ i, w i|`.
* `Cslib.Circuits.Arithmetic.rank_relMatrix_wordPoly`,
  `Cslib.Circuits.Arithmetic.relRank_wordPoly`: full rank.
* `Cslib.Circuits.Arithmetic.projection_imm`: a projection of `IMM_{n,d}` as a sum over paths.
* `Cslib.Circuits.Arithmetic.projection_wordSubst_imm`,
  `Cslib.Circuits.Arithmetic.isProjection_wordPoly_imm`: LST Lemma 8, fixed-sink form.

## References

* [N. Limaye, S. Srinivasan, S. Tavenas, *Superpolynomial lower bounds against low-depth algebraic
  circuits*][LimayeSrinivasanTavenas2021], ECCC TR21-081 revision 1, §2 (words, unbiasedness),
  §2.2 (word polynomials, full rank, Lemma 8) and §8 (Lemma 22 and the proof of Lemma 8).
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

/-! ### Bit strings as numbers -/

section Strings

/-- A number below `2 ^ a` and a multiple of `2 ^ a` determine their sum. -/
private theorem add_two_pow_mul_inj {a x x' y y' : ℕ} (hx : x < 2 ^ a) (hx' : x' < 2 ^ a)
    (h : x + 2 ^ a * y = x' + 2 ^ a * y') : x = x' ∧ y = y' := by
  have hp : 0 < 2 ^ a := Nat.two_pow_pos a
  have h1 := congrArg (· % 2 ^ a) h
  have h2 := congrArg (· / 2 ^ a) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hx'] at h1
  simp only [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hx',
    zero_add] at h2
  exact ⟨h1, h2⟩

/-- Appending a string of length `k` to a string of length `a` gives a string of length
`a + k`. -/
private theorem add_two_pow_mul_lt {a k x y : ℕ} (hx : x < 2 ^ a) (hy : y < 2 ^ k) :
    x + 2 ^ a * y < 2 ^ (a + k) := by
  rw [pow_add]
  calc x + 2 ^ a * y < 2 ^ a + 2 ^ a * y := by omega
    _ = 2 ^ a * (y + 1) := by ring
    _ ≤ 2 ^ a * 2 ^ k := Nat.mul_le_mul_left _ hy

/-- The comparison of two bit strings. A bit string of length `a` is encoded as a number below
`2 ^ a`, its first bit least significant: the concatenation of `A` (length `a`) and `B` is
`A + 2 ^ a * B`, the prefix of length `b` of `A` is `A % 2 ^ b`, and the rest is `A / 2 ^ b`.
When the shorter of the strings `A` (length `a`) and `B` (length `b`) is a prefix of the longer,
`prefixRest A a B b` is `some` of the rest of the longer one, a string of length `|a - b|`;
otherwise it is `none`. -/
def prefixRest (A a B b : ℕ) : Option ℕ :=
  if b ≤ a then if A % 2 ^ b = B then some (A / 2 ^ b) else none
  else if B % 2 ^ a = A then some (B / 2 ^ a) else none

/-- When `a ≤ b`, `prefixRest` compares `A` with the prefix of `B`; for `a = b` both forms
agree. -/
private theorem prefixRest_of_le {A a B b : ℕ} (hA : A < 2 ^ a) (hB : B < 2 ^ b) (hab : a ≤ b) :
    prefixRest A a B b = if B % 2 ^ a = A then some (B / 2 ^ a) else none := by
  rcases hab.lt_or_eq with hab | rfl
  · rw [prefixRest, ite_eq_right (by omega)]
  · rw [prefixRest, ite_eq_left le_rfl, Nat.mod_eq_of_lt hA, Nat.div_eq_of_lt hA,
      Nat.mod_eq_of_lt hB, Nat.div_eq_of_lt hB]
    by_cases h : A = B
    · simp [h]
    · simp [h, Ne.symm h]

/-- `prefixRest` is symmetric in its two strings. -/
private theorem prefixRest_comm {A a B b : ℕ} (hA : A < 2 ^ a) (hB : B < 2 ^ b) :
    prefixRest A a B b = prefixRest B b A a := by
  rcases le_total a b with h | h
  · rw [prefixRest_of_le hA hB h, prefixRest, ite_eq_left h]
  · rw [prefixRest_of_le hB hA h, prefixRest, ite_eq_left h]

/-- The rest of the longer string has length `|a - b|`. -/
private theorem prefixRest_lt {A a B b s : ℕ} (hA : A < 2 ^ a) (hB : B < 2 ^ b)
    (h : prefixRest A a B b = some s) : s < 2 ^ ((a : ℤ) - b).natAbs := by
  unfold prefixRest at h
  split_ifs at h with hab h'
  · obtain rfl := Option.some.inj h
    rw [show ((a : ℤ) - b).natAbs = a - b by omega, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b),
      ← pow_add, Nat.sub_add_cancel hab]
    exact hA
  · obtain rfl := Option.some.inj h
    rw [show ((a : ℤ) - b).natAbs = b - a by omega, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos a),
      ← pow_add, Nat.sub_add_cancel (by omega)]
    exact hB

/-- A string `x` followed by `t`, compared with `y` when `y` is no longer: the rest is `t` exactly
when `y = x`. -/
private theorem prefixRest_add_left {a b x y t : ℕ} (hx : x < 2 ^ b) (hba : b ≤ a) :
    prefixRest (x + 2 ^ b * t) a y b = if x = y then some t else none := by
  rw [prefixRest, ite_eq_left hba, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos b), Nat.div_eq_of_lt hx, zero_add]

/-- A string `y` compared with `x` followed by `t`, when `y` is shorter: the rest is `t` exactly
when `y = x`. -/
private theorem prefixRest_add_right {a b x y t : ℕ} (hx : x < 2 ^ a) (hab : a < b) :
    prefixRest y a (x + 2 ^ a * t) b = if x = y then some t else none := by
  rw [prefixRest, ite_eq_right (by omega), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos a), Nat.div_eq_of_lt hx, zero_add]

/-- One step of the branching program for word polynomials. The state is the unmatched rest `s`
of the longer string read so far, `e` is the signed excess (the length of the positive string
read minus that of the negative one, so `s < 2 ^ |e|`), and the next block has signed length `k`
and label `β`. A block on the side of the excess is appended to the rest; a block on the other
side must agree with the beginning of the rest, or, when it is longer, begin with the rest, and
the unmatched part of the longer one remains. -/
def wordStep (e : ℤ) (s : ℕ) (k : ℤ) (β : ℕ) : Option ℕ :=
  if 0 ≤ e * k then some (s + 2 ^ e.natAbs * β)
  else if k.natAbs ≤ e.natAbs then
    if s % 2 ^ k.natAbs = β then some (s / 2 ^ k.natAbs) else none
  else if β % 2 ^ e.natAbs = s then some (β / 2 ^ e.natAbs) else none

private theorem wordStep_neg (e : ℤ) (s : ℕ) (k : ℤ) (β : ℕ) :
    wordStep (-e) s k β = wordStep e s (-k) β := by
  simp only [wordStep, Int.natAbs_neg, neg_mul, mul_neg]

/-- A step is determined by its source and target: at most one label leads from `s` to `t`. -/
private theorem wordStep_inj {e : ℤ} {s : ℕ} {k : ℤ} {β β' t : ℕ} (h : wordStep e s k β = some t)
    (h' : wordStep e s k β' = some t) : β = β' := by
  unfold wordStep at h h'
  by_cases h₁ : 0 ≤ e * k
  · rw [ite_eq_left h₁, Option.some.injEq] at h h'
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) (Nat.add_left_cancel (h.trans h'.symm))
  rw [ite_eq_right h₁] at h h'
  by_cases h₂ : k.natAbs ≤ e.natAbs
  · rw [ite_eq_left h₂] at h h'
    by_cases h₃ : s % 2 ^ k.natAbs = β
    · by_cases h₄ : s % 2 ^ k.natAbs = β'
      · exact h₃.symm.trans h₄
      · rw [ite_eq_right h₄] at h'
        cases h'
    · rw [ite_eq_right h₃] at h
      cases h
  · rw [ite_eq_right h₂] at h h'
    by_cases h₃ : β % 2 ^ e.natAbs = s
    · by_cases h₄ : β' % 2 ^ e.natAbs = s
      · rw [ite_eq_left h₃, Option.some.injEq] at h
        rw [ite_eq_left h₄, Option.some.injEq] at h'
        rw [← Nat.mod_add_div β (2 ^ e.natAbs), ← Nat.mod_add_div β' (2 ^ e.natAbs), h₃, h₄, h,
          h']
      · rw [ite_eq_right h₄] at h'
        cases h'
    · rw [ite_eq_right h₃] at h
      cases h

/-- **Appending a positive block**: comparing after appending `β` (length `k`) to the first string
is one `wordStep` after comparing before. -/
private theorem prefixRest_append {A a B b β k : ℕ} (hA : A < 2 ^ a) (hB : B < 2 ^ b)
    (hβ : β < 2 ^ k) :
    prefixRest (A + 2 ^ a * β) (a + k) B b =
      (prefixRest A a B b).bind fun s => wordStep ((a : ℤ) - b) s k β := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain rfl : β = 0 := by simpa using hβ
    simp only [mul_zero, add_zero, wordStep, Nat.cast_zero, le_refl, ite_true]
    cases prefixRest A a B b <;> rfl
  rcases le_or_gt b a with hba | hab
  · have hpow : 2 ^ a = 2 ^ b * 2 ^ (a - b) := by rw [← pow_add, Nat.add_sub_cancel' hba]
    have hstep (s : ℕ) : wordStep ((a : ℤ) - b) s k β = some (s + 2 ^ (a - b) * β) := by
      rw [wordStep, ite_eq_left (mul_nonneg (by omega) (by omega)),
        show ((a : ℤ) - b).natAbs = a - b by omega]
    rw [prefixRest, ite_eq_left (by omega), prefixRest, ite_eq_left hba, hpow, mul_assoc,
      Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ (Nat.two_pow_pos b)]
    split_ifs <;> simp [hstep]
  · have hneg : ¬ 0 ≤ ((a : ℤ) - b) * k :=
      not_le.mpr (mul_neg_of_neg_of_pos (by omega) (by omega))
    have he : ((a : ℤ) - b).natAbs = b - a := by omega
    have hk' : ((k : ℤ)).natAbs = k := Int.natAbs_natCast k
    have hpre : prefixRest A a B b = if B % 2 ^ a = A then some (B / 2 ^ a) else none := by
      rw [prefixRest, ite_eq_right (by omega)]
    rw [hpre]
    rcases le_or_gt k (b - a) with hkb | hkb
    · have hstep (s : ℕ) : wordStep ((a : ℤ) - b) s k β =
          if s % 2 ^ k = β then some (s / 2 ^ k) else none := by
        rw [wordStep, ite_eq_right hneg, he, hk', ite_eq_left hkb]
      rw [prefixRest_of_le (add_two_pow_mul_lt hA hβ) hB (by omega), pow_add, Nat.mod_mul,
        ← Nat.div_div_eq_div_mul]
      have key : B % 2 ^ a + 2 ^ a * (B / 2 ^ a % 2 ^ k) = A + 2 ^ a * β ↔
          B % 2 ^ a = A ∧ B / 2 ^ a % 2 ^ k = β :=
        ⟨fun h => add_two_pow_mul_inj (Nat.mod_lt _ (Nat.two_pow_pos a)) hA h,
          fun ⟨h₁, h₂⟩ => by rw [h₁, h₂]⟩
      simp only [key]
      by_cases h₁ : B % 2 ^ a = A <;> by_cases h₂ : B / 2 ^ a % 2 ^ k = β <;>
        simp [h₁, h₂, hstep]
    · have hstep (s : ℕ) : wordStep ((a : ℤ) - b) s k β =
          if β % 2 ^ (b - a) = s then some (β / 2 ^ (b - a)) else none := by
        rw [wordStep, ite_eq_right hneg, he, hk', ite_eq_right (by omega)]
      have hpow : 2 ^ b = 2 ^ a * 2 ^ (b - a) := by
        rw [← pow_add, Nat.add_sub_cancel' hab.le]
      have hq : (A + 2 ^ a * β) / 2 ^ a = β := by
        rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos a), Nat.div_eq_of_lt hA, zero_add]
      have hr : (A + 2 ^ a * β) % 2 ^ a = A := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hA]
      rw [prefixRest, ite_eq_left (by omega), hpow, Nat.mod_mul, ← Nat.div_div_eq_div_mul, hq, hr]
      have key : A + 2 ^ a * (β % 2 ^ (b - a)) = B ↔
          B % 2 ^ a = A ∧ β % 2 ^ (b - a) = B / 2 ^ a := by
        conv_lhs => rw [← Nat.mod_add_div B (2 ^ a)]
        exact ⟨fun h => by
            obtain ⟨h₁, h₂⟩ := add_two_pow_mul_inj hA (Nat.mod_lt _ (Nat.two_pow_pos a)) h
            exact ⟨h₁.symm, h₂⟩,
          fun ⟨h₁, h₂⟩ => by rw [h₁, h₂]⟩
      simp only [key]
      by_cases h₁ : B % 2 ^ a = A <;> by_cases h₂ : β % 2 ^ (b - a) = B / 2 ^ a <;>
        simp [h₁, h₂, hstep]

/-- **Appending a negative block**: comparing after appending `β` (length `k`) to the second
string is one `wordStep`, with signed length `-k`, after comparing before. -/
private theorem prefixRest_append_right {A a B b β k : ℕ} (hA : A < 2 ^ a) (hB : B < 2 ^ b)
    (hβ : β < 2 ^ k) :
    prefixRest A a (B + 2 ^ b * β) (b + k) =
      (prefixRest A a B b).bind fun s => wordStep ((a : ℤ) - b) s (-(k : ℤ)) β := by
  rw [prefixRest_comm hA (add_two_pow_mul_lt hB hβ), prefixRest_append hB hA hβ,
    prefixRest_comm hB hA]
  congr 1
  funext s
  rw [← wordStep_neg, neg_sub]

end Strings

/-! ### Prefixes of a word -/

section Prefixes

variable (p : ℤ → Prop) [DecidablePred p] (W : ℕ → ℤ) (D : ℕ → ℕ)

/-- The total length of the blocks `j < i` whose signed length `W j` satisfies `p`: with `p` the
nonnegative (negative) integers, the length of the positive (negative) string read from the first
`i` blocks of a word. -/
def wordStringLen (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, if p (W j) then (W j).natAbs else 0

/-- The concatenation of the labels `D j` of the blocks `j < i` whose signed length satisfies
`p`, as a number with the first bit least significant. -/
def wordStringVal (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, if p (W j) then 2 ^ wordStringLen p W j * D j else 0

/-- The signed length `∑ j < i, W j` of the first `i` blocks. -/
def wordPrefixSum (i : ℕ) : ℤ :=
  ∑ j ∈ Finset.range i, W j

/-- The comparison of the positive and the negative strings read from the first `i` blocks. -/
def wordRestAt (i : ℕ) : Option ℕ :=
  prefixRest (wordStringVal (0 ≤ ·) W D i) (wordStringLen (0 ≤ ·) W i)
    (wordStringVal (· < 0) W D i) (wordStringLen (· < 0) W i)

variable {p W D}

private theorem wordStringLen_succ (i : ℕ) :
    wordStringLen p W (i + 1) = wordStringLen p W i + if p (W i) then (W i).natAbs else 0 :=
  Finset.sum_range_succ _ i

private theorem wordStringVal_succ (i : ℕ) :
    wordStringVal p W D (i + 1) =
      wordStringVal p W D i + if p (W i) then 2 ^ wordStringLen p W i * D i else 0 :=
  Finset.sum_range_succ _ i

/-- The string read from the first `i` blocks has the length `wordStringLen`. -/
private theorem wordStringVal_lt (hD : ∀ j, D j < 2 ^ (W j).natAbs) (i : ℕ) :
    wordStringVal p W D i < 2 ^ wordStringLen p W i := by
  induction i with
  | zero => simp [wordStringVal, wordStringLen]
  | succ i ih =>
    rw [wordStringVal_succ, wordStringLen_succ]
    split_ifs
    · exact add_two_pow_mul_lt ih (hD i)
    · simpa using ih

/-- The signed excess of the positive string over the negative string is the prefix sum. -/
private theorem wordStringLen_sub (i : ℕ) :
    (wordStringLen (0 ≤ ·) W i : ℤ) - wordStringLen (· < 0) W i = wordPrefixSum W i := by
  induction i with
  | zero => simp [wordStringLen, wordPrefixSum]
  | succ i ih =>
    rw [wordStringLen_succ, wordStringLen_succ, wordPrefixSum, Finset.sum_range_succ,
      ← wordPrefixSum, ← ih]
    split_ifs <;> omega

@[simp]
private theorem wordRestAt_zero : wordRestAt W D 0 = some 0 := by
  simp [wordRestAt, wordStringVal, wordStringLen, prefixRest]

/-- **The branching program reads a word**: comparing the strings of the first `i + 1` blocks is
one `wordStep` after comparing those of the first `i`. -/
private theorem wordRestAt_succ (hD : ∀ j, D j < 2 ^ (W j).natAbs) (i : ℕ) :
    wordRestAt W D (i + 1) =
      (wordRestAt W D i).bind fun s => wordStep (wordPrefixSum W i) s (W i) (D i) := by
  have hP := wordStringVal_lt (p := (0 ≤ ·)) hD i
  have hN := wordStringVal_lt (p := (· < 0)) hD i
  rw [wordRestAt, wordStringVal_succ, wordStringVal_succ, wordStringLen_succ, wordStringLen_succ,
    wordRestAt, ← wordStringLen_sub]
  by_cases h : 0 ≤ W i
  · simp only [ite_eq_left h, ite_eq_right (not_lt.mpr h), add_zero]
    rw [prefixRest_append hP hN (hD i)]
    congr 1
    funext s
    rw [Int.natAbs_of_nonneg h]
  · simp only [ite_eq_right h, ite_eq_left (not_le.mp h), add_zero]
    rw [prefixRest_append_right hP hN (hD i)]
    congr 1
    funext s
    congr 1
    omega

/-- The rest after the first `i` blocks has length `|∑ j < i, W j|`. -/
private theorem wordRestAt_lt (hD : ∀ j, D j < 2 ^ (W j).natAbs) {i s : ℕ}
    (h : wordRestAt W D i = some s) : s < 2 ^ (wordPrefixSum W i).natAbs := by
  rw [← wordStringLen_sub]
  exact prefixRest_lt (wordStringVal_lt hD i) (wordStringVal_lt hD i) h

/-- Once the strings disagree, they disagree on every longer prefix. -/
private theorem wordRestAt_eq_none (hD : ∀ j, D j < 2 ^ (W j).natAbs) {i j : ℕ}
    (h : wordRestAt W D i = none) (hij : i ≤ j) : wordRestAt W D j = none := by
  induction j, hij using Nat.le_induction with
  | base => exact h
  | succ j _ ih => rw [wordRestAt_succ hD, ih, Option.bind_none]

end Prefixes

/-! ### The word polynomial -/

variable {d : ℕ}

/-- A word `w : Fin d → ℤ`, extended by zeros to a sequence. -/
def wordSeq (w : Fin d → ℤ) (j : ℕ) : ℤ :=
  if h : j < d then w ⟨j, h⟩ else 0

@[simp]
theorem wordSeq_val (w : Fin d → ℤ) (i : Fin d) : wordSeq w i = w i := by
  simp [wordSeq]

variable {w : Fin d → ℤ}

/-- The labels of a choice, extended by zeros to a sequence. -/
def WordChoice.digits (x : WordChoice w) (j : ℕ) : ℕ :=
  if h : j < d then x ⟨j, h⟩ else 0

theorem WordChoice.digits_lt (x : WordChoice w) (j : ℕ) :
    x.digits j < 2 ^ (wordSeq w j).natAbs := by
  unfold WordChoice.digits wordSeq
  split_ifs
  · exact (x _).isLt
  · simp

@[simp]
theorem WordChoice.digits_val (x : WordChoice w) (i : Fin d) : x.digits i = x i := by
  simp [WordChoice.digits]

variable (w) in
/-- The comparison of the positive string `σ(m⁺)` and the negative string `σ(m⁻)` of the
monomial `m` chosen by `x`: `σ(m⁺)` concatenates the labels of the positive blocks in order, and
`σ(m⁻)` those of the negative blocks. It is `some τ` when the shorter string is a prefix of the
longer one, with rest `τ`, and `none` otherwise. -/
def wordRest (x : WordChoice w) : Option ℕ :=
  wordRestAt (wordSeq w) x.digits d

/-- **The word polynomial with sink `τ`**: the sum of the set-multilinear monomials
`m = ∏ i, x_i` of `X(w)` whose positive string `σ(m⁺)` and negative string `σ(m⁻)` are
prefix-related with rest `τ`, so that `σ(m⁺) = σ(m⁻) τ` when `∑ i, w i ≥ 0` and
`σ(m⁻) = σ(m⁺) τ` otherwise. The word polynomial `P_w` of LST §2.2 is the sum of these over all
`τ`; fixing the sink is original (see the module docstring). -/
noncomputable def wordPoly (K : Type*) [CommSemiring K] (w : Fin d → ℤ) (τ : ℕ) :
    MvPolynomial (WordVar w) K :=
  ∑ x : WordChoice w, if wordRest w x = some τ then ∏ i, X ⟨i, x i⟩ else 0

/-- The exponent vector of the monomial chosen by `x`. -/
noncomputable def wordMono (x : WordChoice w) : WordVar w →₀ ℕ :=
  ∑ i, Finsupp.single ⟨i, x i⟩ 1

theorem wordMono_apply (x : WordChoice w) (j : Fin d) (β : Fin (2 ^ (w j).natAbs)) :
    wordMono x ⟨j, β⟩ = if x j = β then 1 else 0 := by
  classical
  rw [wordMono, Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · simp [Finsupp.single_apply]
  · intro i _ hij
    rw [Finsupp.single_apply, ite_eq_right fun h => hij (congrArg Sigma.fst h)]
  · simp

theorem wordMono_injective : Function.Injective (wordMono (w := w)) := by
  intro x y h
  funext i
  have := congrArg (· ⟨i, x i⟩) h
  rw [wordMono_apply, wordMono_apply, ite_eq_left rfl] at this
  by_contra h'
  rw [ite_eq_right (Ne.symm h')] at this
  exact one_ne_zero this

theorem prod_X_eq_monomial {K : Type*} [CommSemiring K] (x : WordChoice w) :
    ∏ i, (X ⟨i, x i⟩ : MvPolynomial (WordVar w) K) = monomial (wordMono x) 1 := by
  rw [wordMono, monomial_sum_one]
  rfl

variable {K : Type*} [CommSemiring K]

/-- The coefficients of the word polynomial: a set-multilinear monomial has coefficient `1` when
its strings are prefix-related with rest `τ`, and `0` otherwise. -/
theorem coeff_wordPoly (τ : ℕ) (y : WordChoice w) :
    (wordPoly K w τ).coeff (wordMono y) = if wordRest w y = some τ then 1 else 0 := by
  classical
  rw [wordPoly, coeff_sum, Finset.sum_eq_single y]
  · split_ifs <;> simp [prod_X_eq_monomial]
  · intro x _ hxy
    split_ifs <;> simp [prod_X_eq_monomial, coeff_monomial, wordMono_injective.ne hxy]
  · simp

/-- A product of one variable from each block of `s` is set-multilinear on `s`. -/
theorem isSetMultilinear_prod_X (x : WordChoice w) (s : Finset (Fin d)) :
    IsSetMultilinear Sigma.fst s (∏ i ∈ s, (X ⟨i, x i⟩ : MvPolynomial (WordVar w) K)) := by
  induction s using Finset.induction_on with
  | empty => simpa using isSetMultilinear_C (K := K) (Sigma.fst : WordVar w → Fin d) 1
  | insert a s ha ih =>
    have h := (isSetMultilinear_X (K := K) (Sigma.fst : WordVar w → Fin d) ⟨a, x a⟩).mul ih
      (Finset.disjoint_singleton_left.mpr ha)
    rw [Finset.prod_insert ha, Finset.insert_eq]
    exact h

/-- The word polynomial is set-multilinear on all blocks of `X(w)`. -/
theorem isSetMultilinear_wordPoly (τ : ℕ) :
    IsSetMultilinear Sigma.fst Finset.univ (wordPoly K w τ) := by
  refine Finset.sum_induction _ _ (fun _ _ => IsSetMultilinear.add) IsSetMultilinear.zero
    fun x _ => ?_
  split_ifs
  · exact isSetMultilinear_prod_X x _
  · exact IsSetMultilinear.zero

/-- **LST's word polynomial** `P_w` (LST §2.2): the sum of the set-multilinear monomials of `X(w)`
whose positive and negative strings are prefix-related. -/
noncomputable def wordPolyAllSinks (K : Type*) [CommSemiring K] (w : Fin d → ℤ) :
    MvPolynomial (WordVar w) K :=
  ∑ x : WordChoice w, if (wordRest w x).isSome then ∏ i, X ⟨i, x i⟩ else 0

/-- The rest of a monomial's strings has length `|∑ i, w i|`. -/
theorem wordRest_lt {x : WordChoice w} {τ : ℕ} (h : wordRest w x = some τ) :
    τ < 2 ^ (∑ i, w i).natAbs := by
  have := wordRestAt_lt x.digits_lt h
  rwa [wordPrefixSum, ← Fin.sum_univ_eq_sum_range, Finset.sum_congr rfl fun i _ => wordSeq_val w i]
    at this

/-- LST's word polynomial `P_w` is the sum of the word polynomials with the sinks of length
`|∑ i, w i|`. -/
theorem sum_wordPoly :
    ∑ τ ∈ Finset.range (2 ^ (∑ i, w i).natAbs), wordPoly K w τ = wordPolyAllSinks K w := by
  simp only [wordPoly]
  rw [Finset.sum_comm, wordPolyAllSinks]
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases h : wordRest w x with _ | s
  · simp
  · simp [wordRest_lt h]

/-! ### Full rank -/

section Rank

/-- The variable chosen in block `j` by a choice `r` on a set of blocks containing `j`. -/
private def blockDigit {S : Finset (Fin d)} (r : BlockChoice (Sigma.fst : WordVar w → Fin d) S)
    (j : Fin d) (h : j ∈ S) : Fin (2 ^ (w j).natAbs) :=
  Equiv.sigmaSubtype j (r ⟨j, h⟩)

@[simp]
private theorem blockDigit_spec {S : Finset (Fin d)}
    (r : BlockChoice (Sigma.fst : WordVar w → Fin d) S) (j : Fin d) (h : j ∈ S) :
    (r ⟨j, h⟩ : WordVar w) = ⟨j, blockDigit r j h⟩ := by
  conv_lhs => rw [← (Equiv.sigmaSubtype j).symm_apply_apply (r ⟨j, h⟩)]
  rfl

/-- The choice on all blocks made of a choice `r` on the positive and `c` on the negative
blocks. -/
private def wordMerge (r : BlockChoice (Sigma.fst : WordVar w → Fin d) (wordPos w))
    (c : BlockChoice (Sigma.fst : WordVar w → Fin d) (wordNeg w)) : WordChoice w :=
  fun i => if h : 0 ≤ w i then blockDigit r i (mem_wordBlocks.mpr h)
    else blockDigit c i (mem_wordBlocks.mpr (not_le.mp h))

private theorem blockMonomial_add_blockMonomial (r : BlockChoice (Sigma.fst : WordVar w → Fin d)
    (wordPos w)) (c : BlockChoice (Sigma.fst : WordVar w → Fin d) (wordNeg w)) :
    blockMonomial Sigma.fst (wordPos w) r + blockMonomial Sigma.fst (wordNeg w) c =
      wordMono (wordMerge r c) := by
  classical
  ext ⟨j, β⟩
  rw [Finsupp.add_apply, blockMonomial_apply, blockMonomial_apply, wordMono_apply]
  by_cases h : 0 ≤ w j
  · have hP : j ∈ wordPos w := mem_wordBlocks.mpr h
    have hN : j ∉ wordNeg w := fun h' => (not_lt.mpr h) (mem_wordBlocks.mp h')
    rw [dite_eq_left hP, dite_eq_right hN, add_zero, wordMerge, dite_eq_left h, blockDigit_spec]
    simp
  · have hP : j ∉ wordPos w := fun h' => h (mem_wordBlocks.mp h')
    have hN : j ∈ wordNeg w := mem_wordBlocks.mpr (not_le.mp h)
    rw [dite_eq_right hP, dite_eq_left hN, zero_add, wordMerge, dite_eq_right h, blockDigit_spec]
    simp

variable (w) in
/-- The size `2 ^ |w j|` of block `j` if its signed length satisfies `p`, and `1` otherwise. -/
private def sideSize (p : ℤ → Prop) [DecidablePred p] (j : Fin d) : ℕ :=
  2 ^ (if p (w j) then (w j).natAbs else 0)

private theorem prod_sideSize (p : ℤ → Prop) [DecidablePred p] :
    ∏ j, sideSize w p j = 2 ^ wordStringLen p (wordSeq w) d := by
  simp only [sideSize]
  rw [Finset.prod_pow_eq_pow_sum, wordStringLen, ← Fin.sum_univ_eq_sum_range]
  simp

/-- The labels of a choice `x` in the blocks whose signed length satisfies `p`, and `0`
elsewhere. -/
private def sideDigits (p : ℤ → Prop) [DecidablePred p] (x : WordChoice w) (j : Fin d) :
    Fin (sideSize w p j) :=
  ⟨if p (w j) then x j else 0, by
    unfold sideSize
    split_ifs
    · exact (x j).isLt
    · simp⟩

/-- The mixed-radix value of the labels on one side is the string of that side. -/
private theorem finPiFinEquiv_sideDigits (p : ℤ → Prop) [DecidablePred p] (x : WordChoice w) :
    (finPiFinEquiv (sideDigits p x) : ℕ) = wordStringVal p (wordSeq w) x.digits d := by
  rw [finPiFinEquiv_apply, wordStringVal, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hlen : ∏ j : Fin i, sideSize w p (Fin.castLE i.is_lt.le j) =
      2 ^ wordStringLen p (wordSeq w) i := by
    simp only [sideSize]
    rw [Finset.prod_pow_eq_pow_sum, wordStringLen, ← Fin.sum_univ_eq_sum_range]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have : wordSeq w j = w (Fin.castLE i.is_lt.le j) := wordSeq_val w (Fin.castLE i.is_lt.le j)
    rw [this]
  rw [hlen, sideDigits, wordSeq_val, WordChoice.digits_val]
  split_ifs <;> simp [mul_comm]

/-- The labels of a choice `r` on the blocks satisfying `p`, as a tuple with the factor `1` in the
other blocks. -/
private def choiceDigits (p : ℤ → Prop) [DecidablePred p]
    (r : BlockChoice (Sigma.fst : WordVar w → Fin d) (wordBlocks w p)) (j : Fin d) :
    Fin (sideSize w p j) :=
  if h : p (w j) then
    ⟨blockDigit r j (mem_wordBlocks.mpr h), by
      unfold sideSize
      rw [ite_eq_left h]
      exact (blockDigit r j _).isLt⟩
  else ⟨0, by simp [sideSize, h]⟩

private theorem choiceDigits_injective (p : ℤ → Prop) [DecidablePred p] :
    Function.Injective (choiceDigits (w := w) p) := by
  intro r r' h
  funext ⟨j, hj⟩
  have hp : p (w j) := mem_wordBlocks.mp hj
  have := congrArg (fun y => (y j : ℕ)) h
  simp only [choiceDigits, dite_eq_left hp] at this
  apply Subtype.ext
  rw [blockDigit_spec r j hj, blockDigit_spec r' j hj, Fin.ext this]

private theorem choiceDigits_surjective (p : ℤ → Prop) [DecidablePred p] :
    Function.Surjective (choiceDigits (w := w) p) := by
  intro y
  refine ⟨fun j => (Equiv.sigmaSubtype (j : Fin d)).symm
    ⟨y j, by simpa [sideSize, mem_wordBlocks.mp j.2] using (y j).isLt⟩, ?_⟩
  funext j
  by_cases h : p (w j)
  · ext
    simp [choiceDigits, h, blockDigit]
  · have : (y j : ℕ) = 0 := by simpa [sideSize, h] using (y j).isLt
    ext
    simp [choiceDigits, h, this]

private theorem sideDigits_wordMerge_pos
    (r : BlockChoice (Sigma.fst : WordVar w → Fin d) (wordPos w))
    (c : BlockChoice (Sigma.fst : WordVar w → Fin d) (wordNeg w)) :
    sideDigits (0 ≤ ·) (wordMerge r c) = choiceDigits (0 ≤ ·) r := by
  funext j
  ext
  by_cases h : 0 ≤ w j
  · simp [sideDigits, choiceDigits, wordMerge, h]
  · simp [sideDigits, choiceDigits, h]

private theorem sideDigits_wordMerge_neg
    (r : BlockChoice (Sigma.fst : WordVar w → Fin d) (wordPos w))
    (c : BlockChoice (Sigma.fst : WordVar w → Fin d) (wordNeg w)) :
    sideDigits (· < 0) (wordMerge r c) = choiceDigits (· < 0) c := by
  funext j
  ext
  by_cases h : 0 ≤ w j
  · simp [sideDigits, choiceDigits, not_lt.mpr h]
  · simp [sideDigits, choiceDigits, wordMerge, h, not_le.mp h]

/-- The number encoding the string chosen by `r` on the blocks satisfying `p`. -/
private def choiceValue (p : ℤ → Prop) [DecidablePred p]
    (r : BlockChoice (Sigma.fst : WordVar w → Fin d) (wordBlocks w p)) : ℕ :=
  finPiFinEquiv (choiceDigits p r)

private theorem choiceValue_lt (p : ℤ → Prop) [DecidablePred p]
    (r : BlockChoice (Sigma.fst : WordVar w → Fin d) (wordBlocks w p)) :
    choiceValue p r < 2 ^ wordStringLen p (wordSeq w) d :=
  prod_sideSize (w := w) p ▸ (finPiFinEquiv (choiceDigits p r)).isLt

private theorem choiceValue_injective (p : ℤ → Prop) [DecidablePred p] :
    Function.Injective (choiceValue (w := w) p) :=
  fun _ _ h => choiceDigits_injective p (finPiFinEquiv.injective (Fin.ext h))

private theorem exists_choiceValue_eq (p : ℤ → Prop) [DecidablePred p] {v : ℕ}
    (hv : v < 2 ^ wordStringLen p (wordSeq w) d) : ∃ r, choiceValue (w := w) p r = v := by
  obtain ⟨r, hr⟩ := choiceDigits_surjective (w := w) p
    (finPiFinEquiv.symm ⟨v, (prod_sideSize (w := w) p).symm ▸ hv⟩)
  exact ⟨r, by rw [choiceValue, hr, Equiv.apply_symm_apply]⟩

private theorem card_blockChoice_wordBlocks (p : ℤ → Prop) [DecidablePred p] :
    Fintype.card (BlockChoice (Sigma.fst : WordVar w → Fin d) (wordBlocks w p)) =
      2 ^ wordStringLen p (wordSeq w) d := by
  rw [Fintype.card_of_bijective ⟨choiceDigits_injective (w := w) p,
    choiceDigits_surjective p⟩, Fintype.card_pi]
  simp [prod_sideSize]

/-- The relative-rank matrix of the word polynomial: the entry for the choices `r` on the positive
and `c` on the negative blocks is `1` when their strings are prefix-related with rest `τ`. -/
private theorem relMatrix_wordPoly_apply (τ : ℕ)
    (r : BlockChoice (Sigma.fst : WordVar w → Fin d) (wordPos w))
    (c : BlockChoice (Sigma.fst : WordVar w → Fin d) (wordNeg w)) :
    relMatrix Sigma.fst (wordPos w) (wordNeg w) (wordPoly K w τ) r c =
      if prefixRest (choiceValue (0 ≤ ·) r) (wordStringLen (0 ≤ ·) (wordSeq w) d)
          (choiceValue (· < 0) c) (wordStringLen (· < 0) (wordSeq w) d) = some τ then 1 else 0 := by
  rw [relMatrix_apply, blockMonomial_add_blockMonomial, coeff_wordPoly, wordRest, wordRestAt,
    ← finPiFinEquiv_sideDigits, ← finPiFinEquiv_sideDigits, sideDigits_wordMerge_pos,
    sideDigits_wordMerge_neg]
  rfl

/-- A matrix containing an identity submatrix has rank at least its size. -/
private theorem card_le_rank_of_submatrix_eq_one {α β γ F : Type*} [Field F] [Fintype β]
    [Fintype γ] [DecidableEq γ] (M : Matrix α β F) (f : γ → α) (g : γ → β)
    (h : M.submatrix f g = 1) : Fintype.card γ ≤ M.rank := by
  rw [← Matrix.rank_one (R := F) (n := γ), ← h]
  exact Matrix.rank_submatrix_le _ _ _

/-- **Full rank** (LST §2.2): the relative-rank matrix of the word polynomial with sink `τ` has
rank equal to the smaller of its numbers of rows and columns, for every sink `τ` of the right
length `|∑ i, w i|`. -/
theorem rank_relMatrix_wordPoly {K : Type*} [Field K] {τ : ℕ}
    (hτ : τ < 2 ^ (∑ i, w i).natAbs) :
    (relMatrix Sigma.fst (wordPos w) (wordNeg w) (wordPoly K w τ)).rank =
      min (Fintype.card (BlockChoice (Sigma.fst : WordVar w → Fin d) (wordPos w)))
        (Fintype.card (BlockChoice (Sigma.fst : WordVar w → Fin d) (wordNeg w))) := by
  set a := wordStringLen (0 ≤ ·) (wordSeq w) d
  set b := wordStringLen (· < 0) (wordSeq w) d
  have hsum : (∑ i, w i) = (a : ℤ) - b := by
    rw [wordStringLen_sub, wordPrefixSum, ← Fin.sum_univ_eq_sum_range]
    simp
  rw [hsum] at hτ
  rw [card_blockChoice_wordBlocks, card_blockChoice_wordBlocks]
  refine le_antisymm (le_min ((Matrix.rank_le_card_height _).trans
    (card_blockChoice_wordBlocks _).le) ((Matrix.rank_le_card_width _).trans
    (card_blockChoice_wordBlocks _).le)) ?_
  rcases le_or_gt b a with hba | hab
  · rw [min_eq_right (Nat.pow_le_pow_right two_pos hba), ← card_blockChoice_wordBlocks]
    have hτ' : τ < 2 ^ (a - b) := by rwa [show ((a : ℤ) - b).natAbs = a - b by omega] at hτ
    have hrow (c : BlockChoice (Sigma.fst : WordVar w → Fin d) (wordNeg w)) :
        ∃ r : BlockChoice (Sigma.fst : WordVar w → Fin d) (wordPos w),
          choiceValue (0 ≤ ·) r = choiceValue (· < 0) c + 2 ^ b * τ := by
      have hlt : choiceValue (w := w) (· < 0) c + 2 ^ b * τ < 2 ^ (b + (a - b)) :=
        add_two_pow_mul_lt (choiceValue_lt _ c) hτ'
      rw [Nat.add_sub_cancel' hba] at hlt
      exact exists_choiceValue_eq (w := w) _ hlt
    choose g hg using hrow
    refine card_le_rank_of_submatrix_eq_one _ g id ?_
    ext c c'
    rw [Matrix.submatrix_apply, relMatrix_wordPoly_apply, hg, id,
      prefixRest_add_left (choiceValue_lt _ c) hba, Matrix.one_apply]
    by_cases h : c = c'
    · simp [h]
    · simp [h, (choiceValue_injective _).ne h]
  · rw [min_eq_left (Nat.pow_le_pow_right two_pos hab.le), ← card_blockChoice_wordBlocks]
    have hτ' : τ < 2 ^ (b - a) := by rwa [show ((a : ℤ) - b).natAbs = b - a by omega] at hτ
    have hcol (r : BlockChoice (Sigma.fst : WordVar w → Fin d) (wordPos w)) :
        ∃ c : BlockChoice (Sigma.fst : WordVar w → Fin d) (wordNeg w),
          choiceValue (· < 0) c = choiceValue (0 ≤ ·) r + 2 ^ a * τ := by
      have hlt : choiceValue (w := w) (0 ≤ ·) r + 2 ^ a * τ < 2 ^ (a + (b - a)) :=
        add_two_pow_mul_lt (choiceValue_lt _ r) hτ'
      rw [Nat.add_sub_cancel' hab.le] at hlt
      exact exists_choiceValue_eq (w := w) _ hlt
    choose g hg using hcol
    refine card_le_rank_of_submatrix_eq_one _ id g ?_
    ext r r'
    rw [Matrix.submatrix_apply, relMatrix_wordPoly_apply, hg, id,
      prefixRest_add_right (choiceValue_lt _ r') hab, Matrix.one_apply]
    by_cases h : r = r'
    · simp [h]
    · simp [h, (choiceValue_injective _).ne (Ne.symm h)]

/-- **Relative rank of the word polynomial** (LST §2.2): it is `2 ^ (-|∑ i, w i| / 2)`, the
largest value the imbalance bound allows. -/
theorem relRank_wordPoly {K : Type*} [Field K] {τ : ℕ} (hτ : τ < 2 ^ (∑ i, w i).natAbs) :
    relRank Sigma.fst (wordPos w) (wordNeg w) (wordPoly K w τ) =
      (2 : ℝ) ^ (-((∑ i, w i).natAbs : ℝ) / 2) := by
  set a := wordStringLen (0 ≤ ·) (wordSeq w) d
  set b := wordStringLen (· < 0) (wordSeq w) d
  have hsum : (∑ i, w i) = (a : ℤ) - b := by
    rw [wordStringLen_sub, wordPrefixSum, ← Fin.sum_univ_eq_sum_range]
    simp
  rw [relRank, rank_relMatrix_wordPoly hτ, card_blockChoice_wordBlocks,
    card_blockChoice_wordBlocks, hsum]
  have h2 : (0 : ℝ) < 2 := two_pos
  have hsqrt : √(((2 ^ a * 2 ^ b : ℕ) : ℝ)) = (2 : ℝ) ^ (((a : ℝ) + b) / 2) := by
    rw [Real.sqrt_eq_rpow, ← pow_add, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
      ← Real.rpow_mul h2.le]
    congr 1
    push_cast
    ring
  rw [hsqrt]
  rcases le_total b a with h | h
  · rw [min_eq_right (Nat.pow_le_pow_right two_pos h), Nat.cast_pow, Nat.cast_ofNat,
      ← Real.rpow_natCast, ← Real.rpow_sub h2, show ((a : ℤ) - b).natAbs = a - b by omega]
    congr 1
    push_cast [h]
    ring
  · rw [min_eq_left (Nat.pow_le_pow_right two_pos h), Nat.cast_pow, Nat.cast_ofNat,
      ← Real.rpow_natCast, ← Real.rpow_sub h2, show ((a : ℤ) - b).natAbs = b - a by omega]
    congr 1
    push_cast [h]
    ring

end Rank

/-! ### Iterated matrix multiplication -/

section IMM

/-- The generic matrix `X_i` of iterated matrix multiplication: its entry `(a, c)` is the variable
`(i, a, c)`. -/
noncomputable def immMatrix (K : Type*) [CommSemiring K] (n d : ℕ) (i : Fin d) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin d × Fin n × Fin n) K) :=
  Matrix.of fun a c => X (i, a, c)

/-- **Iterated matrix multiplication** `IMM_{n,d}`: the entry `(0, 0)` of the product
`X_0 X_1 ⋯ X_{d-1}` of `d` generic `n × n` matrices on disjoint sets of variables. Its variables
`(i, a, c)` are split into the `d` blocks `i`, the entries of `X_i`. -/
noncomputable def imm (K : Type*) [CommSemiring K] (n d : ℕ) [NeZero n] :
    MvPolynomial (Fin d × Fin n × Fin n) K :=
  (List.ofFn (immMatrix K n d)).prod 0 0

/-- A projection of `IMM_{n,d}` is a sum over the paths `0 = p 0, p 1, …, p d = 0` of products of
the substituted entries. -/
theorem projection_imm {σ : Type*} {n : ℕ} [NeZero n] (ρ : Fin d × Fin n × Fin n → σ ⊕ K) :
    projection ρ (imm K n d) = ∑ p : Fin (d + 1) → Fin n,
      if p 0 = 0 ∧ p (Fin.last d) = 0 then
        ∏ i : Fin d, Sum.elim X (fun a => C a) (ρ (i, p i.castSucc, p i.succ)) else 0 := by
  change ((projection ρ).mapMatrix (List.ofFn (immMatrix K n d)).prod) 0 0 = _
  rw [map_list_prod, List.map_ofFn, Matrix.list_prod_ofFn_apply]
  simp only [Function.comp_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, immMatrix,
    Matrix.of_apply, projection_X]

end IMM

/-! ### Word polynomials are projections of IMM -/

section Projection

private theorem wordPrefixSum_wordSeq {t : ℕ} (ht : t ≤ d) :
    wordPrefixSum (wordSeq w) t = ∑ i : Fin d with i.val < t, w i := by
  have h : ∑ i : Fin d, (if i.val < t then w i else 0) =
      ∑ i : Fin d, (fun j : ℕ => if j < t then wordSeq w j else 0) i :=
    Finset.sum_congr rfl fun i _ => by simp
  rw [Finset.sum_filter, h,
    Fin.sum_univ_eq_sum_range (fun j => if j < t then wordSeq w j else 0), ← Finset.sum_filter,
    wordPrefixSum]
  congr 1
  ext j
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

/-- The rest after one more block, for a word indexed by `Fin d`. -/
private theorem wordRestAt_castSucc (x : WordChoice w) (i : Fin d) :
    wordRestAt (wordSeq w) x.digits ((i : ℕ) + 1) =
      (wordRestAt (wordSeq w) x.digits i).bind
        fun s => wordStep (wordPrefixSum (wordSeq w) i) s (w i) (x i) := by
  rw [wordRestAt_succ x.digits_lt, wordSeq_val, WordChoice.digits_val]

/-- The state at layer `i + 1` that the column `c` of matrix `i` stands for: the sink `τ` at the
last layer, and `c` itself elsewhere. -/
def wordTarget (τ : ℕ) (i : Fin d) (c : ℕ) : ℕ :=
  if (i : ℕ) + 1 = d then τ else c

/-- **The substitution of Lemma 8**: the variable `(i, a, c)` of `IMM_{n,d}` becomes the variable
`⟨i, β⟩` of block `i` of `X(w)` when the branching program for the word polynomial with sink `τ`
has an edge labelled `β` from state `a` at layer `i` to state `wordTarget τ i c` at layer `i + 1`,
and `0` when it has no such edge. -/
noncomputable def wordSubst (w : Fin d → ℤ) (τ n : ℕ) (K : Type*) [Zero K] :
    Fin d × Fin n × Fin n → WordVar w ⊕ K :=
  fun v => if h : ∃ β : Fin (2 ^ (w v.1).natAbs),
      wordStep (wordPrefixSum (wordSeq w) v.1) v.2.1 (w v.1) β = some (wordTarget τ v.1 v.2.2)
    then Sum.inl ⟨v.1, h.choose⟩ else Sum.inr 0

/-- The substitution of Lemma 8 respects the blocks: a variable of block `i` of `IMM_{n,d}`
becomes a variable of block `i` of `X(w)`. -/
theorem wordSubst_eq_inl {τ n : ℕ} {i : Fin d} {a c : Fin n} {v : WordVar w}
    (h : wordSubst w τ n K (i, a, c) = Sum.inl v) : v.1 = i := by
  rw [wordSubst] at h
  dsimp only at h
  split_ifs at h
  obtain rfl := Sum.inl.inj h
  rfl

/-- The substitution of Lemma 8 substitutes no constant but `0`. -/
theorem wordSubst_eq_inr {τ n : ℕ} {i : Fin d} {a c : Fin n} {k : K}
    (h : wordSubst w τ n K (i, a, c) = Sum.inr k) : k = 0 := by
  rw [wordSubst] at h
  dsimp only at h
  split_ifs at h
  exact (Sum.inr.inj h).symm

/-- The substituted entry `(a, c)` of matrix `i` is the label of the edge from `a` to
`wordTarget τ i c`, written as a sum over the possible labels. -/
private theorem elim_wordSubst (τ : ℕ) {n : ℕ} (i : Fin d) (a c : Fin n) :
    Sum.elim X (fun k => C k) (wordSubst w τ n K (i, a, c)) =
      ∑ β : Fin (2 ^ (w i).natAbs),
        if wordStep (wordPrefixSum (wordSeq w) i) a (w i) β = some (wordTarget τ i c) then
          (X ⟨i, β⟩ : MvPolynomial (WordVar w) K) else 0 := by
  rw [wordSubst]
  dsimp only
  split_ifs with h
  · rw [Sum.elim_inl, Finset.sum_eq_single h.choose, ite_eq_left h.choose_spec]
    · intro β _ hβ
      exact ite_eq_right fun h' => hβ (Fin.ext (wordStep_inj h' h.choose_spec))
    · simp
  · push Not at h
    rw [Sum.elim_inr, map_zero]
    exact (Finset.sum_eq_zero fun β _ => ite_eq_right (h β)).symm

variable {n : ℕ} [NeZero n]

/-- A path of states through the branching program of the word polynomial with sink `τ` that
reads the choice `x`, as a path through the indices of `IMM_{n,d}` from `0` to `0`. -/
private def IsWordPath (τ : ℕ) (x : WordChoice w) (p : Fin (d + 1) → Fin n) : Prop :=
  (p 0 = 0 ∧ p (Fin.last d) = 0) ∧ ∀ i : Fin d,
    wordStep (wordPrefixSum (wordSeq w) i) (p i.castSucc) (w i) (x i) =
      some (wordTarget τ i (p i.succ))

private theorem IsWordPath.wordRestAt_eq {τ : ℕ} {x : WordChoice w} {p : Fin (d + 1) → Fin n}
    (hp : IsWordPath τ x p) :
    ∀ (i : ℕ) (hi : i < d), wordRestAt (wordSeq w) x.digits i = some (p ⟨i, by omega⟩).val
  | 0, _ => by
    rw [wordRestAt_zero, show (⟨0, _⟩ : Fin (d + 1)) = 0 from rfl, hp.1.1, Fin.val_zero]
  | i + 1, hi => by
    have h := hp.2 ⟨i, by omega⟩
    rw [wordTarget, ite_eq_right (show ¬(i + 1 = d) by omega)] at h
    rw [wordRestAt_castSucc x ⟨i, by omega⟩, IsWordPath.wordRestAt_eq hp i (by omega),
      Option.bind_some]
    exact h

private theorem IsWordPath.wordRest {τ : ℕ} {x : WordChoice w} {p : Fin (d + 1) → Fin n}
    (hp : IsWordPath τ x p) (hτ : τ < 2 ^ (∑ i, w i).natAbs) : wordRest w x = some τ := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Int.natAbs_zero, pow_zero,
      Nat.lt_one_iff] at hτ
    rw [hτ, wordRest, wordRestAt_zero]
  · obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have h := hp.2 (Fin.last d)
    rw [wordTarget, ite_eq_left (by simp)] at h
    have := wordRestAt_castSucc x (Fin.last d)
    rw [Fin.val_last] at this
    rw [wordRest, this, hp.wordRestAt_eq d (by omega), Option.bind_some]
    exact h

private theorem IsWordPath.unique {τ : ℕ} {x : WordChoice w} {p q : Fin (d + 1) → Fin n}
    (hp : IsWordPath τ x p) (hq : IsWordPath τ x q) : p = q := by
  funext j
  by_cases hj : (j : ℕ) = d
  · obtain rfl : j = Fin.last d := Fin.ext hj
    exact hp.1.2.trans hq.1.2.symm
  · have h := (hp.wordRestAt_eq j (by omega)).symm.trans (hq.wordRestAt_eq j (by omega))
    exact Fin.ext (Option.some.inj h)

/-- When the strings of `x` are prefix-related with rest `τ`, the states of the branching program
form a path through the indices of `IMM_{n,d}`. -/
private theorem exists_isWordPath {b : ℕ} (hw : IsUnbiased w b) (hn : 2 ^ b ≤ n) {τ : ℕ}
    {x : WordChoice w} (hx : wordRest w x = some τ) : ∃ p : Fin (d + 1) → Fin n,
      IsWordPath τ x p := by
  have hsome (i : ℕ) (hi : i ≤ d) : ∃ s, wordRestAt (wordSeq w) x.digits i = some s := by
    rcases h : wordRestAt (wordSeq w) x.digits i with _ | s
    · rw [wordRest, wordRestAt_eq_none x.digits_lt h hi] at hx
      exact absurd hx (by simp)
    · exact ⟨s, rfl⟩
  have hlt (i : ℕ) (hi : i ≤ d) : (wordRestAt (wordSeq w) x.digits i).getD 0 < n := by
    obtain ⟨s, hs⟩ := hsome i hi
    rw [hs, Option.getD_some]
    refine (wordRestAt_lt x.digits_lt hs).trans_le (le_trans ?_ hn)
    refine Nat.pow_le_pow_right two_pos ?_
    rw [wordPrefixSum_wordSeq hi]
    exact hw i hi
  refine ⟨fun j => if (j : ℕ) = d then 0 else
    ⟨(wordRestAt (wordSeq w) x.digits j).getD 0, hlt j (by omega)⟩, ⟨⟨?_, by simp⟩, ?_⟩⟩
  · ext
    dsimp only
    split_ifs <;> simp
  · intro i
    obtain ⟨s, hs⟩ := hsome i (by omega)
    have hstep := wordRestAt_castSucc x i
    rw [hs, Option.bind_some] at hstep
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.ne_of_lt i.isLt, ↓reduceIte, hs,
      Option.getD_some]
    rw [← hstep, wordTarget]
    split_ifs with h
    · rw [h]
      exact hx
    · obtain ⟨s', hs'⟩ := hsome (i + 1) (by omega)
      simp only [hs', Option.getD_some]

/-- **LST Lemma 8, fixed-sink form** (the substitution): substituting `wordSubst` into
`IMM_{n,d}` gives the word polynomial with sink `τ`, for a `b`-unbiased word and `2 ^ b ≤ n`. -/
theorem projection_wordSubst_imm {b : ℕ} (hw : IsUnbiased w b) (hn : 2 ^ b ≤ n)
    {τ : ℕ} (hτ : τ < 2 ^ (∑ i, w i).natAbs) :
    projection (wordSubst w τ n K) (imm K n d) = wordPoly K w τ := by
  rw [projection_imm]
  simp only [elim_wordSubst, Finset.prod_univ_sum, Fintype.piFinset_univ, Fintype.prod_ite_zero,
    Finset.ite_sum_zero]
  rw [Finset.sum_comm, wordPoly]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : wordRest w x = some τ
  · obtain ⟨p₀, hp₀⟩ := exists_isWordPath hw hn hx
    rw [ite_eq_left hx, Finset.sum_eq_single p₀, ite_eq_left hp₀.1, ite_eq_left hp₀.2]
    · intro p _ hp
      split_ifs with h₁ h₂ <;> first | rfl | exact absurd (IsWordPath.unique ⟨h₁, h₂⟩ hp₀) hp
    · simp
  · rw [ite_eq_right hx]
    refine Finset.sum_eq_zero fun p _ => ?_
    split_ifs with h₁ h₂ <;>
      first | rfl | exact absurd (IsWordPath.wordRest (p := p) ⟨h₁, h₂⟩ hτ) hx

/-- **LST Lemma 8, fixed-sink form**: the word polynomial with sink `τ` of a `b`-unbiased word is
a projection of `IMM_{n,d}` for every `n ≥ 2 ^ b`. The substitution `wordSubst` maps each variable
of block `i` of `IMM_{n,d}` to a variable of block `i` of `X(w)` or to `0`
(`wordSubst_eq_inl`, `wordSubst_eq_inr`). -/
theorem isProjection_wordPoly_imm {b : ℕ} (hw : IsUnbiased w b) (hn : 2 ^ b ≤ n)
    {τ : ℕ} (hτ : τ < 2 ^ (∑ i, w i).natAbs) :
    IsProjection (wordPoly K w τ) (imm K n d) :=
  ⟨wordSubst w τ n K, projection_wordSubst_imm hw hn hτ⟩

end Projection

end Cslib.Circuits.Arithmetic

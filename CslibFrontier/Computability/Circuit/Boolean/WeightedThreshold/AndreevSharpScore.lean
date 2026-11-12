/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
import Mathlib.Tactic.LinearCombination

/-!
# The sharper score for Andreev's function

This module proves the score identity behind the exact depth-two threshold circuit for Andreev's
function with `(5/16 + o(1)) n ^ 2` gates (`AndreevSharp`), stated over the table bits
`x : BitString b → Bool` and the block counts `s : Fin b → ℕ` only. The source is the preprint
cited in [#4640](https://github.com/cslib-community/cslib-frontier/issues/4640) (C. Reitwiessner,
*Depth-Two Threshold Circuits for Andreev's Function*, November 2026, Theorem 5 and Appendix A).
It is unpublished, so the source correspondence below refers to that version.

With `N = 2 ^ b`, block parities `p` (`blockParities`), `α = ⌊(m - 1) / 2⌋`, multipliers
`μ_c` (`0` at `c = 0`, `1 + α` at the weight-one addresses `e_i`, `1` elsewhere),
`W_S = ∑_{S · c odd} μ_c x_c`, `t_S = ∑_{i ∈ S} s_i`, `w = 2 ∑_c μ_c x_c + ∑_i s_i` and
`R = 2 (N - 1) + 2 α b + b m`, the score `andreevSharpScore` is the preprint's
`P = 2N + ∑_S r_S(2 W_S + t_S) + (N / 2)(w² + ∑ s_i²) + 4 N z - 2 N (α² + 1) E - 2 α N σ
  + 2 N (1 + α) ∑_i x_{e_i} s_i - N (R + 4) x_0 [p = 0]`
with the ridge `r_S(u) = -8 ⌈u/2⌉² + κ_S ⌈u/2⌉`, `κ_S = -4 (2α + 1)(b - 2|S|)`.

The proof is by character sums. The odd-parity form `L_f(S) = ∑_c f(c) [S · c odd]` satisfies
`2 ∑_S L_f(S) = N (∑ f - f 0)` and the bilinear identity
`4 ∑_S L_f(S) L_h(S) = N ((F - f 0)(H - h 0) + ∑_c f c h c - f 0 h 0)`. Writing
`4 r_S(2 W_S + t_S) = -8 G_S² + 2 κ_S G_S` with `G_S = 2 W_S + t_S + (t_S mod 2)`, an odd-parity
form, collapses the sum over `S` to a closed form. Deviation from the preprint: the closed form
is proved in one uniform expression (`andreevSharpScore_eq`) rather than through the three
displayed identities of Appendix A, and the sum over `S` includes `S = ∅`, which contributes
`r(0) = 0`.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.oddForm`: odd-parity forms on the cube.
* `Cslib.Circuits.Boolean.WeightedThreshold.unitAddr`,
  `Cslib.Circuits.Boolean.WeightedThreshold.spread`: weight-one addresses and functions supported
  on them.
* `Cslib.Circuits.Boolean.WeightedThreshold.andreevSharpScore` and its ingredients
  `andreevSharpAmp`, `andreevSharpMult`, `andreevSharpW`, `andreevSharpLoad`, `andreevSharpRange`,
  `andreevSharpKappa`, `andreevRidge`, `blockParities`.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.four_mul_sum_toNat_parityOn_mul`,
  `Cslib.Circuits.Boolean.WeightedThreshold.two_mul_sum_oddForm`,
  `Cslib.Circuits.Boolean.WeightedThreshold.four_mul_sum_oddForm_mul_oddForm`: the character sums.
* `Cslib.Circuits.Boolean.WeightedThreshold.andreevSharpScore_eq`: the closed form of the score
  (preprint, equation `eq:bestclosed`).
* `Cslib.Circuits.Boolean.WeightedThreshold.andreevSharpScore_margin`: if every block count is at
  most `m`, then `P ≥ N` when the selected table bit is `false` and `P ≤ -N` when it is `true`.

## References

* [cslib-frontier#4640](https://github.com/cslib-community/cslib-frontier/issues/4640):
  C. Reitwiessner, *Depth-Two Threshold Circuits for Andreev's Function* (unpublished preprint,
  November 2026), Theorem 5 and Appendix A.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open BitString Finset

/-! ### Odd-parity forms and their character sums -/

section OddForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- The indicator `[S · c odd]` is `(1 - χ_S(c)) / 2`. -/
theorem two_mul_toNat_parityOn (S : Finset ι) (c : ι → Bool) :
    2 * ((parityOn S c).toNat : ℝ) = 1 - chi ℝ S c := by
  rw [chi_eq_signVal_parityOn]
  cases parityOn S c <;> norm_num [signVal]

omit [DecidableEq ι] in
/-- Summed over all sets, the characters at `c` detect `c = 0`. -/
theorem sum_chi_eq_ite (c : ι → Bool) :
    ∑ S, chi ℝ S c = if c = 0 then 2 ^ Fintype.card ι else 0 := by
  simpa only [chi_zero, mul_one] using sum_chi_mul_chi c 0

omit [Fintype ι] [DecidableEq ι] in
private theorem add_eq_zero_iff_eq' {c d : ι → Bool} : c + d = 0 ↔ c = d := by
  have hb : ∀ a b : Bool, a + b = 0 ↔ a = b := by decide
  simp only [funext_iff, Pi.add_apply, Pi.zero_apply, hb]

omit [DecidableEq ι] in
/-- **Pair counts of odd sets.** The number of sets `S` with both `S · c` and `S · d` odd,
times four, is `2 ^ |ι| * (1 - [c = 0] - [d = 0] + [c = d])`. -/
theorem four_mul_sum_toNat_parityOn_mul (c d : ι → Bool) :
    4 * ∑ S, ((parityOn S c).toNat : ℝ) * (parityOn S d).toNat =
      2 ^ Fintype.card ι * (1 - (if c = 0 then 1 else 0) - (if d = 0 then 1 else 0) +
        (if c = d then 1 else 0)) := by
  have h (S : Finset ι) : 4 * (((parityOn S c).toNat : ℝ) * (parityOn S d).toNat) =
      1 - chi ℝ S c - chi ℝ S d + chi ℝ S (c + d) := by
    rw [chi_add]
    linear_combination (2 * ((parityOn S d).toNat : ℝ)) * two_mul_toNat_parityOn S c +
      (1 - chi ℝ S c) * two_mul_toNat_parityOn S d
  rw [mul_sum, sum_congr rfl fun S _ => h S, sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
    sum_chi_eq_ite, sum_chi_eq_ite, sum_chi_eq_ite]
  simp only [sum_const, card_univ, Fintype.card_finset, nsmul_eq_mul, mul_one, Nat.cast_pow,
    Nat.cast_ofNat, add_eq_zero_iff_eq']
  split_ifs <;> ring

omit [DecidableEq ι] in
/-- The number of sets `S` with `S · c` odd, times two, is `2 ^ |ι| * (1 - [c = 0])`. -/
theorem two_mul_sum_toNat_parityOn (c : ι → Bool) :
    2 * ∑ S, ((parityOn S c).toNat : ℝ) = 2 ^ Fintype.card ι * (1 - if c = 0 then 1 else 0) := by
  rw [mul_sum, sum_congr rfl fun S _ => two_mul_toNat_parityOn S c, sum_sub_distrib,
    sum_chi_eq_ite]
  simp only [sum_const, card_univ, Fintype.card_finset, nsmul_eq_mul, mul_one, Nat.cast_pow,
    Nat.cast_ofNat]
  split_ifs <;> ring

/-- The odd-parity form `L_f(S) = ∑_c f(c) [S · c odd]` of a function on the cube. -/
def oddForm (f : (ι → Bool) → ℝ) (S : Finset ι) : ℝ :=
  ∑ c, f c * (parityOn S c).toNat

/-- **Sum of an odd-parity form** over all sets. -/
theorem two_mul_sum_oddForm (f : (ι → Bool) → ℝ) :
    2 * ∑ S, oddForm f S = 2 ^ Fintype.card ι * (∑ c, f c - f 0) := by
  have hexp : 2 * ∑ S, oddForm f S =
      ∑ c, f c * (2 * ∑ S, ((parityOn S c).toNat : ℝ)) := by
    simp only [oddForm, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun c _ => sum_congr rfl fun S _ => by ring
  rw [hexp]
  simp_rw [two_mul_sum_toNat_parityOn]
  have h (c : ι → Bool) : f c * (2 ^ Fintype.card ι * (1 - if c = 0 then (1 : ℝ) else 0)) =
      2 ^ Fintype.card ι * f c - if c = 0 then 2 ^ Fintype.card ι * f 0 else 0 := by
    split_ifs with hc <;> [subst hc; skip] <;> ring
  simp_rw [h, sum_sub_distrib, sum_ite_eq', mem_univ, ite_true, ← mul_sum]
  ring

/-- **Bilinear character sum.** For functions `f, h` on the cube,
`4 ∑_S L_f(S) L_h(S) = 2 ^ |ι| ((F - f 0)(H - h 0) + ∑_c f c h c - f 0 h 0)` with `F = ∑ f` and
`H = ∑ h`. -/
theorem four_mul_sum_oddForm_mul_oddForm (f h : (ι → Bool) → ℝ) :
    4 * ∑ S, oddForm f S * oddForm h S =
      2 ^ Fintype.card ι * ((∑ c, f c - f 0) * (∑ c, h c - h 0) + ∑ c, f c * h c - f 0 * h 0) := by
  have hexp : 4 * ∑ S, oddForm f S * oddForm h S =
      ∑ c, ∑ d, f c * h d * (4 * ∑ S, ((parityOn S c).toNat : ℝ) * (parityOn S d).toNat) := by
    calc 4 * ∑ S, oddForm f S * oddForm h S
        = ∑ S, ∑ c, ∑ d, f c * h d * (4 * (((parityOn S c).toNat : ℝ) * (parityOn S d).toNat)) := by
          rw [mul_sum]
          refine sum_congr rfl fun S _ => ?_
          rw [oddForm, oddForm, sum_mul_sum, mul_sum]
          exact sum_congr rfl fun c _ => by
            rw [mul_sum]; exact sum_congr rfl fun d _ => by ring
      _ = _ := by
          rw [sum_comm]
          refine sum_congr rfl fun c _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun d _ => ?_
          simp only [mul_sum]
  rw [hexp]
  simp_rw [four_mul_sum_toNat_parityOn_mul]
  set N : ℝ := 2 ^ Fintype.card ι
  have h1 (c d : ι → Bool) : f c * h d * (N * (1 - (if c = 0 then 1 else 0) -
      (if d = 0 then 1 else 0) + (if c = d then 1 else 0))) =
      N * (f c * h d) - (if 0 = c then N * (f c * h d) else 0) -
        (if 0 = d then N * (f c * h d) else 0) + (if c = d then N * (f c * h d) else 0) := by
    simp only [eq_comm (a := (0 : ι → Bool))]
    split_ifs <;> ring
  simp_rw [h1, sum_add_distrib, sum_sub_distrib, sum_ite_eq, mem_univ, ite_true]
  simp only [sum_ite_irrel, sum_const_zero, sum_ite_eq, mem_univ, ite_true]
  simp only [← mul_sum, ← sum_mul]
  ring

end OddForm


/-! ### Unit addresses and spread functions -/

section Unit

variable {b : ℕ}

/-- The address `e_i` whose only `true` coordinate is `i`. -/
def unitAddr (i : Fin b) : BitString b :=
  fun j => decide (j = i)

/-- `unitAddr` is injective. -/
theorem unitAddr_injective : Function.Injective (unitAddr (b := b)) := fun i j h => by
  simpa [unitAddr] using (congrFun h i).symm

/-- A unit address is nonzero. -/
theorem unitAddr_ne_zero (i : Fin b) : unitAddr i ≠ 0 := fun h => by
  simpa [unitAddr] using congrFun h i

/-- The parity of `e_i` on `S` is membership of `i` in `S`. -/
theorem parityOn_unitAddr (S : Finset (Fin b)) (i : Fin b) :
    parityOn S (unitAddr i) = decide (i ∈ S) := by
  have hf : ({j ∈ S | unitAddr i j = true} : Finset (Fin b)) = if i ∈ S then {i} else ∅ := by
    ext j
    split_ifs with hi <;> simp [unitAddr] <;> grind
  rw [parityOn, hf]
  split_ifs with hi <;> simp [hi]

/-- An address has weight one if it is some `e_i`. -/
def IsUnitAddr (c : BitString b) : Prop :=
  ∃ i, c = unitAddr i

instance (c : BitString b) : Decidable (IsUnitAddr c) :=
  inferInstanceAs (Decidable (∃ i, c = unitAddr i))

/-- The function on addresses that is `a i` at `e_i` and `0` elsewhere. -/
def spread (a : Fin b → ℝ) (c : BitString b) : ℝ :=
  ∑ i, if c = unitAddr i then a i else 0

/-- `spread a` takes the value `a i` at `e_i`. -/
@[simp]
theorem spread_unitAddr (a : Fin b → ℝ) (i : Fin b) : spread a (unitAddr i) = a i := by
  simp [spread, unitAddr_injective.eq_iff, eq_comm (a := i)]

/-- `spread a` vanishes off the unit addresses. -/
theorem spread_of_not_isUnitAddr (a : Fin b → ℝ) {c : BitString b} (hc : ¬IsUnitAddr c) :
    spread a c = 0 :=
  sum_eq_zero fun i _ => ite_eq_right_iff.mpr fun h => (hc ⟨i, h⟩).elim

/-- `spread a` vanishes at the zero address. -/
@[simp]
theorem spread_zero (a : Fin b → ℝ) : spread a 0 = 0 :=
  spread_of_not_isUnitAddr a fun ⟨i, h⟩ => unitAddr_ne_zero i h.symm

/-- Summing against `spread a` evaluates at the unit addresses. -/
theorem sum_spread_mul (a : Fin b → ℝ) (F : BitString b → ℝ) :
    ∑ c, spread a c * F c = ∑ i, a i * F (unitAddr i) := by
  simp only [spread, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  simp

/-- The indicator of weight-one addresses is `spread 1`. -/
theorem ite_isUnitAddr_eq_spread (c : BitString b) :
    (if IsUnitAddr c then (1 : ℝ) else 0) = spread 1 c := by
  split_ifs with hc
  · obtain ⟨i, rfl⟩ := hc
    simp
  · rw [spread_of_not_isUnitAddr _ hc]

/-- The odd-parity form of `spread a` is the block sum `∑_{i ∈ S} a i`. -/
theorem oddForm_spread (a : Fin b → ℝ) (S : Finset (Fin b)) :
    oddForm (spread a) S = ∑ i ∈ S, a i := by
  rw [oddForm, sum_spread_mul]
  have h (i : Fin b) : a i * ((decide (i ∈ S)).toNat : ℝ) = if i ∈ S then a i else 0 := by
    split_ifs <;> simp [*]
  simp only [parityOn_unitAddr, h, sum_ite_mem, univ_inter]

end Unit

/-! ### The sharper score -/

section Score

variable (b m : ℕ)

/-- The amplification `α = ⌊(m - 1) / 2⌋` (with `α = 0` for `m = 0`). -/
def andreevSharpAmp (m : ℕ) : ℕ :=
  (m - 1) / 2

/-- The table multiplier `μ_c`: `0` at the zero address, `1 + α` at weight-one addresses and `1`
elsewhere. -/
def andreevSharpMult (c : BitString b) : ℕ :=
  if c = 0 then 0 else if IsUnitAddr c then 1 + andreevSharpAmp m else 1

/-- `W_S = ∑_{c : S · c odd} μ_c x_c`, the amplified count of table ones at odd addresses. -/
def andreevSharpW (x : BitString b → Bool) (S : Finset (Fin b)) : ℕ :=
  ∑ c, andreevSharpMult b m c * (x c).toNat * (parityOn S c).toNat

/-- The global load `w = 2 ∑_c μ_c x_c + ∑_i s_i`, which equals `2 z + 2 α E + σ`. -/
def andreevSharpLoad (x : BitString b → Bool) (s : Fin b → ℕ) : ℕ :=
  2 * (∑ c, andreevSharpMult b m c * (x c).toNat) + ∑ i, s i

/-- The range `R = 2 (2 ^ b - 1) + 2 α b + b m` of the load. -/
def andreevSharpRange : ℕ :=
  2 * (2 ^ b - 1) + 2 * andreevSharpAmp m * b + b * m

/-- The coefficient shift `κ_S = -4 (2 α + 1) (b - 2 |S|)`. -/
def andreevSharpKappa (S : Finset (Fin b)) : ℤ :=
  -4 * (2 * andreevSharpAmp m + 1) * (b - 2 * #S)

/-- The ridge function `r_κ(u) = -8 ⌈u / 2⌉ ^ 2 + κ ⌈u / 2⌉`. -/
def andreevRidge (κ u : ℤ) : ℤ :=
  -8 * ((u + 1) / 2) ^ 2 + κ * ((u + 1) / 2)

/-- The parity vector of block counts. -/
def blockParities (s : Fin b → ℕ) : BitString b :=
  fun i => decide (s i % 2 = 1)

variable {b} in
/-- A truth-table bit as a real number. -/
abbrev tableVal (x : BitString b → Bool) (c : BitString b) : ℝ :=
  (x c).toNat

/-- **The sharper score** (preprint, Appendix A, equation `eq:bestscore`): for table bits `x` and
block counts `s`,
`P = 2N + ∑_S r_S(2 W_S + t_S) + (N / 2)(w² + ∑ s_i²) + 4 N z - 2 N (α² + 1) E - 2 α N σ
  + 2 N (1 + α) ∑_i x_{e_i} s_i - N (R + 4) x_0 [b = 0]`.
The sum runs over all `S`; the empty set contributes `r(0) = 0`. -/
noncomputable def andreevSharpScore (x : BitString b → Bool) (s : Fin b → ℕ) : ℝ :=
  let N : ℝ := 2 ^ b
  let α : ℝ := andreevSharpAmp m
  2 * N + (∑ S, (andreevRidge (andreevSharpKappa b m S)
      (2 * andreevSharpW b m x S + ∑ i ∈ S, s i) : ℝ)) +
    N / 2 * ((andreevSharpLoad b m x s : ℝ) ^ 2 + ∑ i, (s i : ℝ) ^ 2) +
    4 * N * (∑ c, if c = 0 then 0 else tableVal x c) -
    2 * N * (α ^ 2 + 1) * (∑ i, tableVal x (unitAddr i)) - 2 * α * N * (∑ i, (s i : ℝ)) +
    2 * N * (1 + α) * (∑ i, tableVal x (unitAddr i) * s i) -
    N * (andreevSharpRange b m + 4) * tableVal x 0 *
      (if blockParities b s = 0 then 1 else 0)

end Score

/-! ### Closed form of the score -/

section ClosedForm

variable {b m : ℕ}

/-- `4 r_κ(u) = -8 G ^ 2 + 2 κ G` with `G = u + (u mod 2) = 2 ⌈u / 2⌉`. -/
theorem four_mul_andreevRidge (κ : ℤ) (u : ℕ) :
    4 * andreevRidge κ u = -8 * ((u + u % 2 : ℕ) : ℤ) ^ 2 + 2 * κ * (u + u % 2 : ℕ) := by
  have h : ((u + u % 2 : ℕ) : ℤ) = 2 * (((u : ℤ) + 1) / 2) := by push_cast; omega
  rw [h, andreevRidge]
  ring

/-- The parity of a block sum is the parity of the block parities. -/
theorem sum_mod_two_eq_toNat_parityOn (s : Fin b → ℕ) (S : Finset (Fin b)) :
    (∑ i ∈ S, s i) % 2 = (parityOn S (blockParities b s)).toNat := by
  induction S using Finset.induction_on with
  | empty => simp [parityOn]
  | insert i S hi ih =>
    rw [sum_insert hi, parityOn_insert hi, Nat.add_mod, ih]
    simp only [blockParities]
    rcases Nat.mod_two_eq_zero_or_one (s i) with h | h <;>
      cases parityOn S (blockParities b s) <;> simp [h]

/-- The real multiplier: `μ_c = [c ≠ 0] + α [c has weight one]`. -/
theorem cast_andreevSharpMult (c : BitString b) :
    (andreevSharpMult b m c : ℝ) =
      (if c = 0 then 0 else 1) + andreevSharpAmp m * spread 1 c := by
  rw [← ite_isUnitAddr_eq_spread, andreevSharpMult]
  by_cases h0 : c = 0
  · subst h0
    have : ¬IsUnitAddr (0 : BitString b) := fun ⟨i, h⟩ => unitAddr_ne_zero i h.symm
    simp [this]
  · by_cases hu : IsUnitAddr c <;> simp [h0, hu]

/-- The squared multiplier: `μ_c ^ 2 = [c ≠ 0] + (2 α + α ^ 2) [c has weight one]`. -/
theorem cast_andreevSharpMult_sq (c : BitString b) :
    (andreevSharpMult b m c : ℝ) ^ 2 =
      (if c = 0 then 0 else 1) + (2 * andreevSharpAmp m + andreevSharpAmp m ^ 2) * spread 1 c := by
  rw [← ite_isUnitAddr_eq_spread, andreevSharpMult]
  by_cases h0 : c = 0
  · subst h0
    have : ¬IsUnitAddr (0 : BitString b) := fun ⟨i, h⟩ => unitAddr_ne_zero i h.symm
    simp [this]
  · by_cases hu : IsUnitAddr c <;> simp [h0, hu]
    ring

@[simp]
private theorem andreevSharpMult_unitAddr (i : Fin b) :
    andreevSharpMult b m (unitAddr i) = 1 + andreevSharpAmp m := by
  have : IsUnitAddr (unitAddr i) := ⟨i, rfl⟩
  simp [andreevSharpMult, unitAddr_ne_zero, this]

private theorem tableVal_sq (x : BitString b → Bool) (c : BitString b) :
    tableVal x c ^ 2 = tableVal x c := by
  simp only [tableVal]
  cases x c <;> simp

/-- **Closed form of the sharper score** (preprint, Appendix A, equation `eq:bestclosed`, in a
uniform shape): with `p` the block parities, `I₀ = [p = 0]` and `μ_p` the multiplier,
`P = 2N + N w I₀ - N (1 - I₀) - 2 N μ_p x_p - N s̃_p + (2α + 1) N [p has weight one]
  - N (R + 4) x_0 I₀`,
where `s̃_p` is `s_i` if `p = e_i` and `0` otherwise. -/
theorem andreevSharpScore_eq (x : BitString b → Bool) (s : Fin b → ℕ) :
    andreevSharpScore b m x s =
      2 * 2 ^ b + 2 ^ b * andreevSharpLoad b m x s *
          (if blockParities b s = 0 then 1 else 0) -
        2 ^ b * (1 - if blockParities b s = 0 then 1 else 0) -
        2 * 2 ^ b * andreevSharpMult b m (blockParities b s) * tableVal x (blockParities b s) -
        2 ^ b * spread (fun i => (s i : ℝ)) (blockParities b s) +
        (2 * andreevSharpAmp m + 1) * 2 ^ b * spread 1 (blockParities b s) -
        2 ^ b * (andreevSharpRange b m + 4) * tableVal x 0 *
          (if blockParities b s = 0 then 1 else 0) := by
  set p := blockParities b s with hp
  set N : ℝ := 2 ^ b with hN
  set α : ℝ := (andreevSharpAmp m : ℝ) with hα
  set X := tableVal x with hX
  set a : BitString b → ℝ := fun c => (andreevSharpMult b m c : ℝ) * X c with ha
  set st : BitString b → ℝ := spread fun i => (s i : ℝ) with hst
  set ε : BitString b → ℝ := spread 1 with hε
  set δ : BitString b → ℝ := fun c => if c = p then 1 else 0 with hδ
  set g : BitString b → ℝ := fun c => 2 * a c + st c + δ c with hg
  set z : ℝ := ∑ c, if c = 0 then 0 else X c with hz
  set E : ℝ := ∑ i, X (unitAddr i) with hE
  set σ : ℝ := ∑ i, (s i : ℝ) with hσ
  set I0 : ℝ := if p = 0 then 1 else 0 with hI0
  -- the per-set ridge terms as odd-parity forms
  have hG (S : Finset (Fin b)) :
      ((2 * andreevSharpW b m x S + ∑ i ∈ S, s i +
        (2 * andreevSharpW b m x S + ∑ i ∈ S, s i) % 2 : ℕ) : ℝ) = oddForm g S := by
    have hmod : (2 * andreevSharpW b m x S + ∑ i ∈ S, s i) % 2 = (∑ i ∈ S, s i) % 2 := by
      omega
    rw [hmod, sum_mod_two_eq_toNat_parityOn, ← hp]
    have hW : (andreevSharpW b m x S : ℝ) = ∑ c, a c * (parityOn S c).toNat := by
      simp only [andreevSharpW, ha, hX, tableVal]
      push_cast
      rfl
    have ht : ((∑ i ∈ S, s i : ℕ) : ℝ) = ∑ c, st c * (parityOn S c).toNat := by
      have h := oddForm_spread (fun i => (s i : ℝ)) S
      rw [oddForm] at h
      rw [hst, h]
      push_cast
      rfl
    simp only [oddForm, hg, add_mul, sum_add_distrib, hδ, ite_mul, one_mul, zero_mul,
      sum_ite_eq', mem_univ, ite_true]
    push_cast
    rw [hW, ← ht]
    push_cast
    simp only [mul_sum, mul_assoc]
  have hcard (S : Finset (Fin b)) : (#S : ℝ) = oddForm ε S := by
    rw [hε, oddForm_spread]
    simp
  have hkappa (S : Finset (Fin b)) : (andreevSharpKappa b m S : ℝ) =
      -4 * (2 * α + 1) * b + 8 * (2 * α + 1) * oddForm ε S := by
    rw [← hcard, andreevSharpKappa]
    push_cast
    ring
  have hridge : 4 * ∑ S, (andreevRidge (andreevSharpKappa b m S)
      (2 * andreevSharpW b m x S + ∑ i ∈ S, s i) : ℝ) =
      -2 * (4 * ∑ S, oddForm g S * oddForm g S) - 4 * (2 * α + 1) * b * (2 * ∑ S, oddForm g S) +
        4 * (2 * α + 1) * (4 * ∑ S, oddForm ε S * oddForm g S) := by
    simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun S _ => ?_
    set u := 2 * andreevSharpW b m x S + ∑ i ∈ S, s i with hu'
    have hu : (2 * (andreevSharpW b m x S : ℤ) + ((∑ i ∈ S, s i : ℕ) : ℤ)) = (u : ℤ) := by
      rw [hu']
      push_cast
      ring
    have h4 : (4 : ℝ) * (andreevRidge (andreevSharpKappa b m S) (u : ℤ) : ℝ) =
        -8 * ((u + u % 2 : ℕ) : ℝ) ^ 2 +
          2 * (andreevSharpKappa b m S : ℝ) * ((u + u % 2 : ℕ) : ℝ) := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) (four_mul_andreevRidge (andreevSharpKappa b m S) u)
      simp only [Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_neg, Int.cast_ofNat,
        Int.cast_natCast] at h
      exact h
    rw [hu, h4, hG S, hkappa]
    ring
  rw [two_mul_sum_oddForm, four_mul_sum_oddForm_mul_oddForm,
    four_mul_sum_oddForm_mul_oddForm] at hridge
  simp only [Fintype.card_fin] at hridge
  -- basic inner products
  have hX2 (c : BitString b) : X c * X c = X c := by rw [← sq, hX, tableVal_sq]
  have ha0 : a 0 = 0 := by simp [ha, andreevSharpMult]
  have hst0 : st 0 = 0 := spread_zero _
  have hε0 : ε 0 = 0 := spread_zero _
  have hδ0 : δ 0 = I0 := by simp only [hδ, hI0, eq_comm]
  have hsa : ∑ c, a c = z + α * E := by
    simp only [ha, cast_andreevSharpMult, add_mul, sum_add_distrib, ite_mul, zero_mul, one_mul,
      mul_assoc, ← mul_sum, sum_spread_mul, Pi.one_apply, hz, hE, hα]
  have hsaa : ∑ c, a c * a c = z + (2 * α + α ^ 2) * E := by
    have h (c : BitString b) : a c * a c = (andreevSharpMult b m c : ℝ) ^ 2 * X c := by
      rw [ha]
      dsimp only
      rw [show (andreevSharpMult b m c : ℝ) * X c * ((andreevSharpMult b m c : ℝ) * X c) =
        (andreevSharpMult b m c : ℝ) ^ 2 * (X c * X c) by ring, hX2]
    simp only [h, cast_andreevSharpMult_sq, add_mul, sum_add_distrib, ite_mul, zero_mul, one_mul,
      mul_assoc, ← mul_sum, sum_spread_mul, Pi.one_apply, hz, hE, hα]
  have hsast : ∑ c, a c * st c = (1 + α) * ∑ i, X (unitAddr i) * s i := by
    rw [hst, show (∑ c, a c * spread (fun i => (s i : ℝ)) c) =
        ∑ c, spread (fun i => (s i : ℝ)) c * a c from sum_congr rfl fun c _ => mul_comm _ _,
      sum_spread_mul, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [ha, andreevSharpMult_unitAddr]
    push_cast
    ring
  have hsum_δ (F : BitString b → ℝ) : ∑ c, F c * δ c = F p := by
    simp [hδ]
  have hsst : ∑ c, st c = σ := by
    have := sum_spread_mul (fun i => (s i : ℝ)) fun _ => 1
    simpa [hσ] using this
  have hsstst : ∑ c, st c * st c = ∑ i, (s i : ℝ) ^ 2 := by
    rw [hst, sum_spread_mul]
    simp [sq]
  have hsδ : ∑ c, δ c = 1 := by simp [hδ]
  have hsε : ∑ c, ε c = b := by
    have := sum_spread_mul (1 : Fin b → ℝ) fun _ => 1
    simpa [hε] using this
  have hsεa : ∑ c, ε c * a c = (1 + α) * E := by
    rw [hε, sum_spread_mul]
    simp [ha, hE, mul_sum, hα]
  have hsεst : ∑ c, ε c * st c = σ := by
    rw [hε, sum_spread_mul]
    simp [hst, hσ]
  have hsεδ : ∑ c, ε c * δ c = ε p := hsum_δ ε
  have hsg : ∑ c, g c = 2 * (z + α * E) + σ + 1 := by
    simp only [hg, sum_add_distrib, ← mul_sum, hsa, hsst, hsδ]
  have hg0 : g 0 = I0 := by simp only [hg, ha0, hst0, hδ0]; ring
  have hsgg : ∑ c, g c * g c = 4 * (z + (2 * α + α ^ 2) * E) + ∑ i, (s i : ℝ) ^ 2 + 1 +
      4 * ((1 + α) * ∑ i, X (unitAddr i) * s i) + 4 * a p + 2 * st p := by
    have h (c : BitString b) : g c * g c = 4 * (a c * a c) + st c * st c + δ c * δ c +
        4 * (a c * st c) + 4 * (a c * δ c) + 2 * (st c * δ c) := by
      simp only [hg]; ring
    have hδδ : ∑ c, δ c * δ c = 1 := by rw [hsum_δ]; simp [hδ]
    simp only [h, sum_add_distrib, ← mul_sum, hsaa, hsstst, hδδ, hsast, hsum_δ]
  have hsεg : ∑ c, ε c * g c = 2 * ((1 + α) * E) + σ + ε p := by
    have h (c : BitString b) : ε c * g c = 2 * (ε c * a c) + ε c * st c + ε c * δ c := by
      simp only [hg]; ring
    simp only [h, sum_add_distrib, ← mul_sum, hsεa, hsεst, hsεδ]
  rw [hsg, hg0, hsgg, hsε, hε0, hsεg] at hridge
  -- the load
  have hload : (andreevSharpLoad b m x s : ℝ) = 2 * (z + α * E) + σ := by
    rw [andreevSharpLoad, ← hsa]
    push_cast
    simp [ha, hX, hσ]
  have hap : a p = (andreevSharpMult b m p : ℝ) * X p := rfl
  -- assemble
  have hscore : 4 * andreevSharpScore b m x s = 4 * (2 * N) +
      4 * ∑ S, (andreevRidge (andreevSharpKappa b m S)
        (2 * andreevSharpW b m x S + ∑ i ∈ S, s i) : ℝ) +
      4 * (N / 2 * ((2 * (z + α * E) + σ) ^ 2 + ∑ i, (s i : ℝ) ^ 2) + 4 * N * z -
        2 * N * (α ^ 2 + 1) * E - 2 * α * N * σ + 2 * N * (1 + α) * ∑ i, X (unitAddr i) * s i -
        N * (andreevSharpRange b m + 4) * X 0 * I0) := by
    rw [andreevSharpScore, ← hload]
    simp only [hN, hα, hX, hz, hE, hσ, hI0, hp]
    ring
  rw [hridge] at hscore
  have h4 : andreevSharpScore b m x s = (4 * andreevSharpScore b m x s) / 4 := by ring
  rw [h4, hscore, hload, hap, ← hN]
  by_cases hp0 : p = 0
  · have h1 : I0 = 1 := by simp [hI0, hp0]
    rw [h1]
    ring
  · have h1 : I0 = 0 := by simp [hI0, hp0]
    rw [h1]
    ring

/-- The load is at most the range: `w ≤ R`. -/
theorem andreevSharpLoad_le (x : BitString b → Bool) (s : Fin b → ℕ) (hs : ∀ i, s i ≤ m) :
    andreevSharpLoad b m x s ≤ andreevSharpRange b m := by
  have hμ : ∑ c, andreevSharpMult b m c * (x c).toNat ≤ ∑ c, andreevSharpMult b m c :=
    sum_le_sum fun c _ => by cases x c <;> simp
  have hsum : (∑ c, (andreevSharpMult b m c : ℝ)) = (2 ^ b - 1) + andreevSharpAmp m * b := by
    simp only [cast_andreevSharpMult, sum_add_distrib, ← mul_sum]
    have h1 := sum_spread_mul (1 : Fin b → ℝ) fun _ => 1
    simp only [mul_one, Pi.one_apply, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    rw [h1]
    have h2 : ∑ c : BitString b, (if c = 0 then (0 : ℝ) else 1) = 2 ^ b - 1 := by
      have h (c : BitString b) : (if c = 0 then (0 : ℝ) else 1) = 1 - if c = 0 then 1 else 0 := by
        split_ifs <;> norm_num
      simp [h, sum_sub_distrib]
    rw [h2]
  have hpow : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hμN : ∑ c, andreevSharpMult b m c = (2 ^ b - 1) + andreevSharpAmp m * b := by
    have : ((∑ c, andreevSharpMult b m c : ℕ) : ℝ) =
        (((2 ^ b - 1) + andreevSharpAmp m * b : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hpow]
      exact hsum
    exact_mod_cast this
  have hσ : ∑ i, s i ≤ b * m := (sum_le_sum fun i _ => hs i).trans (by simp)
  rw [andreevSharpLoad, andreevSharpRange]
  have := hμ.trans hμN.le
  nlinarith

/-- The real load is `2 (z + α E) + σ`. -/
theorem cast_andreevSharpLoad (x : BitString b → Bool) (s : Fin b → ℕ) :
    (andreevSharpLoad b m x s : ℝ) = 2 * ((∑ c, if c = 0 then 0 else tableVal x c) +
      andreevSharpAmp m * ∑ i, tableVal x (unitAddr i)) + ∑ i, (s i : ℝ) := by
  rw [andreevSharpLoad]
  push_cast
  simp only [cast_andreevSharpMult, add_mul, sum_add_distrib, ite_mul, zero_mul, one_mul,
    mul_assoc, ← mul_sum, sum_spread_mul, Pi.one_apply]

/-- **The score has margin `N`** (preprint, Appendix A): if every block count is at most `m`,
the score is at least `2 ^ b` when the selected table bit is `false` and at most `-2 ^ b` when it
is `true`. -/
theorem andreevSharpScore_margin (x : BitString b → Bool) (s : Fin b → ℕ)
    (hs : ∀ i, s i ≤ m) :
    (x (blockParities b s) = false → (2 : ℝ) ^ b ≤ andreevSharpScore b m x s) ∧
      (x (blockParities b s) = true → andreevSharpScore b m x s ≤ -(2 : ℝ) ^ b) := by
  rw [andreevSharpScore_eq]
  set p := blockParities b s with hp
  have hN : (0 : ℝ) < 2 ^ b := by positivity
  by_cases hp0 : p = 0
  · have hw := andreevSharpLoad_le x s hs
    have hw' : (andreevSharpLoad b m x s : ℝ) ≤ andreevSharpRange b m := by exact_mod_cast hw
    have hw0 : (0 : ℝ) ≤ andreevSharpLoad b m x s := Nat.cast_nonneg _
    simp only [hp0, ↓reduceIte, spread_zero, andreevSharpMult, mul_one, sub_self, mul_zero,
      Nat.cast_zero, sub_zero, add_zero]
    constructor <;> intro hx <;> simp only [tableVal, hx, Bool.toNat_false, Bool.toNat_true,
      Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, sub_zero] <;> nlinarith
  · simp only [hp0, ↓reduceIte, mul_zero, sub_zero, add_zero]
    by_cases hu : IsUnitAddr p
    · obtain ⟨i, hi⟩ := hu
      have hpi : p i = true := by simp [hi, unitAddr]
      have hsi : s i % 2 = 1 := by simpa [hp, blockParities] using hpi
      have hsim := hs i
      have hα : s i ≤ 2 * andreevSharpAmp m + 1 := by rw [andreevSharpAmp]; omega
      have hα' : (s i : ℝ) ≤ 2 * andreevSharpAmp m + 1 := by exact_mod_cast hα
      have hs1 : (1 : ℝ) ≤ s i := by exact_mod_cast (show 1 ≤ s i by omega)
      rw [hi, spread_unitAddr, spread_unitAddr, andreevSharpMult_unitAddr]
      push_cast
      have h1 := mul_le_mul_of_nonneg_left hα' hN.le
      have h2 := mul_le_mul_of_nonneg_left hs1 hN.le
      constructor <;> intro hx <;> simp only [tableVal, hx, Bool.toNat_false,
        Bool.toNat_true, Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, sub_zero,
        Pi.one_apply] <;> nlinarith
    · have hm : andreevSharpMult b m p = 1 := by simp [andreevSharpMult, hp0, hu]
      rw [spread_of_not_isUnitAddr _ hu, spread_of_not_isUnitAddr _ hu, hm]
      constructor <;> intro hx <;> simp only [tableVal, hx, Bool.toNat_false, Bool.toNat_true,
        Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, sub_zero] <;> nlinarith

end ClosedForm

end Cslib.Circuits.Boolean.WeightedThreshold

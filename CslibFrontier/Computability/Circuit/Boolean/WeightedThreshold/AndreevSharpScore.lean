/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.OddForm
import Mathlib.Tactic.LinearCombination

/-!
# The sharper score for Andreev's function

This module proves the score identity behind the exact depth-two threshold circuit for Andreev's
function with `(5/16 + o(1)) n ^ 2` gates (`AndreevSharp`), stated over the table bits
`x : BitString b → Bool` and the block counts `s : Fin b → ℕ` only. The mathematics is original,
AI-assisted work under [#4640](https://github.com/cslib-community/cslib-frontier/issues/4640).
Statement numbers and labels refer to the author's unpublished draft (C. Reitwiessner,
*Depth-Two Threshold Circuits for Andreev's Function*, Theorem 5 and Appendix A), which is not
publicly accessible; the correspondence with it is not verifiable by third parties.

With `N = 2 ^ b`, block parities `p` (`blockParities`), `α = ⌊(m - 1) / 2⌋`, multipliers
`μ_c` (`0` at `c = 0`, `1 + α` at the weight-one addresses `e_i`, `1` elsewhere),
`W_S = ∑_{S · c odd} μ_c x_c`, `t_S = ∑_{i ∈ S} s_i`, `w = 2 ∑_c μ_c x_c + ∑_i s_i` and
`R = 2 (N - 1) + 2 α b + b m`, the score `andreevSharpScore` is the preprint's
`P = 2N + ∑_S r_S(2 W_S + t_S) + (N / 2)(w² + ∑ s_i²) + 4 N z - 2 N (α² + 1) E - 2 α N σ
  + 2 N (1 + α) ∑_i x_{e_i} s_i - N (R + 4) x_0 [p = 0]`
with the ridge `r_S(u) = -8 ⌈u/2⌉² + κ_S ⌈u/2⌉`, `κ_S = -4 (2α + 1)(b - 2|S|)`.

The proof is by character sums over the odd-parity forms of
`Foundations.BooleanAnalysis.OddForm`: the form `L_f(S) = ∑_c f(c) [S · c odd]` satisfies
`2 ∑_S L_f(S) = N (∑ f - f 0)` and the bilinear identity
`4 ∑_S L_f(S) L_h(S) = N ((F - f 0)(H - h 0) + ∑_c f c h c - f 0 h 0)`. Writing
`4 r_S(2 W_S + t_S) = -8 G_S² + 2 κ_S G_S` with `G_S = 2 W_S + t_S + (t_S mod 2)`, an odd-parity
form, collapses the sum over `S` to a closed form. Deviation from the preprint: the closed form
is proved in one uniform expression (`andreevSharpScore_eq`) rather than through the three
displayed identities of Appendix A, and the sum over `S` includes `S = ∅`, which contributes
`r(0) = 0`.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.andreevSharpScore` and its ingredients
  `andreevSharpAmp`, `andreevSharpMult`, `andreevSharpW`, `andreevSharpLoad`, `andreevSharpRange`,
  `andreevSharpKappa`, `andreevRidge`, `blockParities`.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.andreevSharpScore_eq`: the closed form of the score
  (preprint, equation `eq:bestclosed`).
* `Cslib.Circuits.Boolean.WeightedThreshold.andreevSharpScore_margin`: if every block count is at
  most `m`, then `P ≥ N` when the selected table bit is `false` and `P ≤ -N` when it is `true`.

## References

* [cslib-frontier#4640](https://github.com/cslib-community/cslib-frontier/issues/4640):
  original AI-assisted work, following C. Reitwiessner, *Depth-Two Threshold Circuits for
  Andreev's Function* (unpublished draft, not publicly accessible), Theorem 5 and Appendix A.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open BitString Finset

/-! ### The sharper score -/

section Score

variable (b m : ℕ)

/-- The amplification `α = ⌊(m - 1) / 2⌋` (with `α = 0` for `m = 0`). -/
def andreevSharpAmp (m : ℕ) : ℕ :=
  (m - 1) / 2

/-- The table multiplier `μ_c`: `0` at the zero address, `1 + α` at weight-one addresses and `1`
elsewhere. -/
def andreevSharpMult (c : BitString b) : ℕ :=
  if c = 0 then 0 else if IsSingle c then 1 + andreevSharpAmp m else 1

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
    2 * N * (α ^ 2 + 1) * (∑ i, tableVal x (Pi.single i true)) - 2 * α * N * (∑ i, (s i : ℝ)) +
    2 * N * (1 + α) * (∑ i, tableVal x (Pi.single i true) * s i) -
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
      (if c = 0 then 0 else 1) + andreevSharpAmp m * onSingles 1 c := by
  rw [← ite_isSingle_eq_onSingles, andreevSharpMult]
  by_cases h0 : c = 0
  · subst h0
    simp [not_isSingle_zero]
  · by_cases hu : IsSingle c <;> simp [h0, hu]

/-- The squared multiplier: `μ_c ^ 2 = [c ≠ 0] + (2 α + α ^ 2) [c has weight one]`, from
`cast_andreevSharpMult` since both indicators are idempotent and the second implies the first. -/
theorem cast_andreevSharpMult_sq (c : BitString b) :
    (andreevSharpMult b m c : ℝ) ^ 2 =
      (if c = 0 then 0 else 1) +
        (2 * andreevSharpAmp m + andreevSharpAmp m ^ 2) * onSingles 1 c := by
  have h1 : onSingles 1 c * onSingles 1 c = onSingles 1 c := by
    rw [← ite_isSingle_eq_onSingles]
    split_ifs <;> norm_num
  have h2 : (if c = 0 then (0 : ℝ) else 1) * onSingles 1 c = onSingles 1 c := by
    split_ifs with h <;> simp [h]
  have h3 : (if c = 0 then (0 : ℝ) else 1) ^ 2 = if c = 0 then 0 else 1 := by
    split_ifs <;> norm_num
  rw [cast_andreevSharpMult]
  linear_combination h3 + 2 * (andreevSharpAmp m : ℝ) * h2 + (andreevSharpAmp m : ℝ) ^ 2 * h1

@[simp]
private theorem andreevSharpMult_single (i : Fin b) :
    andreevSharpMult b m (Pi.single i true) = 1 + andreevSharpAmp m := by
  have : IsSingle (Pi.single i true) := ⟨i, rfl⟩
  simp [andreevSharpMult, this]

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
        2 ^ b * onSingles (fun i => (s i : ℝ)) (blockParities b s) +
        (2 * andreevSharpAmp m + 1) * 2 ^ b * onSingles 1 (blockParities b s) -
        2 ^ b * (andreevSharpRange b m + 4) * tableVal x 0 *
          (if blockParities b s = 0 then 1 else 0) := by
  set p := blockParities b s with hp
  set N : ℝ := 2 ^ b with hN
  set α : ℝ := (andreevSharpAmp m : ℝ) with hα
  set X := tableVal x with hX
  set a : BitString b → ℝ := fun c => (andreevSharpMult b m c : ℝ) * X c with ha
  set st : BitString b → ℝ := onSingles fun i => (s i : ℝ) with hst
  set ε : BitString b → ℝ := onSingles 1 with hε
  set δ : BitString b → ℝ := fun c => if c = p then 1 else 0 with hδ
  set g : BitString b → ℝ := fun c => 2 * a c + st c + δ c with hg
  set z : ℝ := ∑ c, if c = 0 then 0 else X c with hz
  set E : ℝ := ∑ i, X (Pi.single i true) with hE
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
      have h := oddForm_onSingles (fun i => (s i : ℝ)) S
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
    rw [hε, oddForm_onSingles]
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
  have hst0 : st 0 = 0 := onSingles_zero _
  have hε0 : ε 0 = 0 := onSingles_zero _
  have hδ0 : δ 0 = I0 := by simp only [hδ, hI0, eq_comm]
  have hsa : ∑ c, a c = z + α * E := by
    simp only [ha, cast_andreevSharpMult, add_mul, sum_add_distrib, ite_mul, zero_mul, one_mul,
      mul_assoc, ← mul_sum, sum_onSingles_mul, Pi.one_apply, hz, hE, hα]
  have hsaa : ∑ c, a c * a c = z + (2 * α + α ^ 2) * E := by
    have h (c : BitString b) : a c * a c = (andreevSharpMult b m c : ℝ) ^ 2 * X c := by
      rw [ha]
      dsimp only
      rw [show (andreevSharpMult b m c : ℝ) * X c * ((andreevSharpMult b m c : ℝ) * X c) =
        (andreevSharpMult b m c : ℝ) ^ 2 * (X c * X c) by ring, hX2]
    simp only [h, cast_andreevSharpMult_sq, add_mul, sum_add_distrib, ite_mul, zero_mul, one_mul,
      mul_assoc, ← mul_sum, sum_onSingles_mul, Pi.one_apply, hz, hE, hα]
  have hsast : ∑ c, a c * st c = (1 + α) * ∑ i, X (Pi.single i true) * s i := by
    rw [hst, show (∑ c, a c * onSingles (fun i => (s i : ℝ)) c) =
        ∑ c, onSingles (fun i => (s i : ℝ)) c * a c from sum_congr rfl fun c _ => mul_comm _ _,
      sum_onSingles_mul, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [ha, andreevSharpMult_single]
    push_cast
    ring
  have hsum_δ (F : BitString b → ℝ) : ∑ c, F c * δ c = F p := by
    simp [hδ]
  have hsst : ∑ c, st c = σ := by
    have := sum_onSingles_mul (fun i => (s i : ℝ)) fun _ => 1
    simpa [hσ] using this
  have hsstst : ∑ c, st c * st c = ∑ i, (s i : ℝ) ^ 2 := by
    rw [hst, sum_onSingles_mul]
    simp [sq]
  have hsδ : ∑ c, δ c = 1 := by simp [hδ]
  have hsε : ∑ c, ε c = b := by
    have := sum_onSingles_mul (1 : Fin b → ℝ) fun _ => 1
    simpa [hε] using this
  have hsεa : ∑ c, ε c * a c = (1 + α) * E := by
    rw [hε, sum_onSingles_mul]
    simp [ha, hE, mul_sum, hα]
  have hsεst : ∑ c, ε c * st c = σ := by
    rw [hε, sum_onSingles_mul]
    simp [hst, hσ]
  have hsεδ : ∑ c, ε c * δ c = ε p := hsum_δ ε
  have hsg : ∑ c, g c = 2 * (z + α * E) + σ + 1 := by
    simp only [hg, sum_add_distrib, ← mul_sum, hsa, hsst, hsδ]
  have hg0 : g 0 = I0 := by simp only [hg, ha0, hst0, hδ0]; ring
  have hsgg : ∑ c, g c * g c = 4 * (z + (2 * α + α ^ 2) * E) + ∑ i, (s i : ℝ) ^ 2 + 1 +
      4 * ((1 + α) * ∑ i, X (Pi.single i true) * s i) + 4 * a p + 2 * st p := by
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
        2 * N * (α ^ 2 + 1) * E - 2 * α * N * σ +
        2 * N * (1 + α) * ∑ i, X (Pi.single i true) * s i -
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
    have h1 := sum_onSingles_mul (1 : Fin b → ℝ) fun _ => 1
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
      andreevSharpAmp m * ∑ i, tableVal x (Pi.single i true)) + ∑ i, (s i : ℝ) := by
  rw [andreevSharpLoad]
  push_cast
  simp only [cast_andreevSharpMult, add_mul, sum_add_distrib, ite_mul, zero_mul, one_mul,
    mul_assoc, ← mul_sum, sum_onSingles_mul, Pi.one_apply]

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
    simp only [hp0, ↓reduceIte, onSingles_zero, andreevSharpMult, mul_one, sub_self, mul_zero,
      Nat.cast_zero, sub_zero, add_zero]
    constructor <;> intro hx <;> simp only [tableVal, hx, Bool.toNat_false, Bool.toNat_true,
      Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, sub_zero] <;> nlinarith
  · simp only [hp0, ↓reduceIte, mul_zero, sub_zero, add_zero]
    by_cases hu : IsSingle p
    · obtain ⟨i, hi⟩ := hu
      have hpi : p i = true := by simp [hi]
      have hsi : s i % 2 = 1 := by simpa [hp, blockParities] using hpi
      have hsim := hs i
      have hα : s i ≤ 2 * andreevSharpAmp m + 1 := by rw [andreevSharpAmp]; omega
      have hα' : (s i : ℝ) ≤ 2 * andreevSharpAmp m + 1 := by exact_mod_cast hα
      have hs1 : (1 : ℝ) ≤ s i := by exact_mod_cast (show 1 ≤ s i by omega)
      rw [hi, onSingles_single, onSingles_single, andreevSharpMult_single]
      push_cast
      have h1 := mul_le_mul_of_nonneg_left hα' hN.le
      have h2 := mul_le_mul_of_nonneg_left hs1 hN.le
      constructor <;> intro hx <;> simp only [tableVal, hx, Bool.toNat_false,
        Bool.toNat_true, Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, sub_zero,
        Pi.one_apply] <;> nlinarith
    · have hm : andreevSharpMult b m p = 1 := by simp [andreevSharpMult, hp0, hu]
      rw [onSingles_of_not_isSingle _ hu, onSingles_of_not_isSingle _ hu, hm]
      constructor <;> intro hx <;> simp only [tableVal, hx, Bool.toNat_false, Bool.toNat_true,
        Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, sub_zero] <;> nlinarith

end ClosedForm

end Cslib.Circuits.Boolean.WeightedThreshold

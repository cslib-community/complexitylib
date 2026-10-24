/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.MassProduction.Basic
public import Complexity.Computability.Circuit.Boolean.MassProduction.Uhlig.Layer
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Filter.AtTopBot.Basic
import Cslib.Computability.Circuit.Boolean.Lupanov
import Cslib.Foundations.Data.Nat.Asymptotics
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Data.ENat.Basic

/-!
# Uhlig's mass-production theorem

Every Boolean function on `n` inputs can be evaluated on `2 ^ d(n)` independent inputs with
`(1 + o(1)) 2 ^ n / n` gates, as long as `d(n) log₂ n = o(n)` [Uhlig1992]. This is Lupanov's
worst-case bound for a single copy: up to this many copies of any function fit within the
asymptotic single-copy ceiling `2 ^ n / n`. The theorem does not compare them with the complexity
of the particular function.

`d` layers of `Uhlig.complexity_directProduct_two_mul_le` with prefixes of `p` bits turn single
copies on `m` inputs into `2 ^ d` copies on `d p + m` inputs, multiplying the size by
`(2 ^ p + 1) ^ d` and adding at most `(2 ^ p + 1) ^ d d 2 ^ d` times the overhead of one pair
(`complexity_directProduct_two_pow_le`). With `p = 2 log₂ n + 2` and Lupanov's synthesis on the
remaining `m` inputs, the leading term is `(2 ^ p + 1) ^ d 2 ^ m / m = (1 + o(1)) 2 ^ n / n`,
and every overhead is `2 ^ (o(n))`.

The statements are denominator-free: for every precision `P`, eventually
`P * n * cost ≤ (P + 1) * 2 ^ n`. For `P > 0` this is `cost ≤ (1 + 1 / P) 2 ^ n / n`; the
precision `P = 0` is allowed but says nothing. The copy count may be any number up to
`2 ^ d(n)`, including zero. Sizes count all gates; `massComplexity` charges NOT, AND and OR
once and constants never. These are bounds on circuit size, not on the running time of a circuit
constructor.

## Main definitions

* `Cslib.Circuits.Boolean.MassProduction.IsUhligDepth`: `d(n) log₂ n = o(n)`, discretely.

## Main results

* `Cslib.Circuits.Boolean.MassProduction.complexity_directProduct_two_pow_le`: the finite
  recursion.
* `Cslib.Circuits.Boolean.MassProduction.mul_complexity_directProduct_le`: the finite theorem,
  with every parameter condition explicit.
* `Cslib.Circuits.Boolean.MassProduction.eventually_mul_complexity_directProduct_le`: Uhlig's
  theorem for circuit size.
* `Cslib.Circuits.Boolean.MassProduction.eventually_mul_massComplexity_le`: Uhlig's theorem for
  mass complexity.

## References

* [D. Uhlig, *Networks computing Boolean functions for multiple input values*][Uhlig1992].
* [I. Wegener, *The Complexity of Boolean Functions*][Wegener1987], Theorem 10.2.3.
* [O. B. Lupanov, *On a Method of Circuit Synthesis*][Lupanov1958], for single copies.
* Simplifies MassProduction/UhligRecursion.lean, MassProduction/UhligParameters.lean,
  MassProduction/UhligAsymptoticBounds.lean, MassProduction/UhligTheorem.lean and
  MassProduction/LupanovSynthesis.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction

open Filter Uhlig

/-! ### The finite recursion -/

theorem layerOverhead_mono {p w w' : ℕ} (h : w ≤ w') : layerOverhead p w ≤ layerOverhead p w' := by
  unfold layerOverhead
  gcongr

/-- A crude polynomial bound on the overhead of one pair. -/
private theorem layerOverhead_le (p w : ℕ) :
    layerOverhead p w ≤ 32 * 8 ^ p * (p + 1) * (w + 2) := by
  have h8 : 8 ^ p = 2 ^ p * 2 ^ p * 2 ^ p := by
    rw [show 8 = 2 * 2 * 2 by rfl, mul_pow, mul_pow]
  unfold layerOverhead selectorCost
  rw [h8, pow_add]
  generalize hA : 2 ^ p = A
  have hA1 : 1 ≤ A := hA ▸ Nat.one_le_two_pow
  have hX : A ≤ A * A * A * (p + 1) := by
    calc A = A * 1 * 1 * 1 := by ring
      _ ≤ A * A * A * (p + 1) := by gcongr; omega
  have f2 : A * (w + 2) ≤ A * A * A * (p + 1) * (w + 2) := Nat.mul_le_mul_right _ hX
  have f3 : 1 ≤ A * A * A * (p + 1) * (w + 2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h1 : A + 1 ≤ 2 * A := by omega
  calc (A + 1) * (w * (2 * (A * A * (2 * (p + p) + 2) + 1) + 4) +
        2 * (A * A * (2 * (p + p) + 2) + 1 + 5)) + 2
      = (A + 1) * (A * A * (4 * (2 * p + 1)) * (w + 1) + 6 * (w + 2)) + 2 := by ring
    _ ≤ (2 * A) * (A * A * (8 * (p + 1)) * (w + 2) + 6 * (w + 2)) + 2 := by
        gcongr ?_ * (?_ + _) + _
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    _ ≤ 32 * (A * A * A) * (p + 1) * (w + 2) := by nlinarith

/-- **Iterated Uhlig layers.** If every function on `m` inputs has a single copy of size at
most `L`, then every function on `d * p + m` inputs has `2 ^ d` copies of size at most
`(2 ^ p + 1) ^ d * (L + d * 2 ^ d * H)`, where `H` bounds the overhead of each layer. -/
theorem complexity_directProduct_two_pow_le {p m L H : ℕ}
    (hL : ∀ g : BooleanFunction m, complexity interpretation (directProduct g 1) ≤ L) :
    ∀ (d n : ℕ), n = d * p + m → (∀ e < d, layerOverhead p (e * p + m) ≤ H) →
      ∀ f : BooleanFunction n, complexity interpretation (directProduct f (2 ^ d)) ≤
        (2 ^ p + 1) ^ d * (L + d * 2 ^ d * H) := by
  intro d
  induction d with
  | zero =>
    intro n hn _ f
    obtain rfl : n = m := by simpa using hn
    simpa using hL f
  | succ d ih =>
    intro n hn hH f
    obtain rfl : n = p + (d * p + m) := by rw [hn]; ring
    have hlayer := complexity_directProduct_two_mul_le (t := 2 ^ d)
      (ih (d * p + m) rfl fun e he => hH e (Nat.lt_succ_of_lt he)) f
    rw [show 2 ^ (d + 1) = 2 * 2 ^ d from pow_succ' 2 d]
    refine hlayer.trans ?_
    have hHd := hH d (Nat.lt_succ_self d)
    rw [pow_succ']
    have hApos : 0 < (2 ^ p + 1) ^ d := by positivity
    generalize (2 ^ p + 1) ^ d = A at *
    generalize 2 ^ d = T at *
    have hK : 1 ≤ 2 ^ p + 1 := Nat.le_add_left 1 _
    generalize 2 ^ p + 1 = K at *
    have hKA : 1 ≤ K * A := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    calc K * (A * (L + d * T * H)) + T * layerOverhead p (d * p + m)
        ≤ K * (A * (L + d * T * H)) + K * A * (T * H) := by
          refine Nat.add_le_add_left ?_ _
          calc T * layerOverhead p (d * p + m) ≤ 1 * (T * H) := by
                rw [one_mul]; exact Nat.mul_le_mul_left _ hHd
            _ ≤ K * A * (T * H) := Nat.mul_le_mul_right _ hKA
      _ = K * A * (L + (d + 1) * T * H) := by ring
      _ ≤ K * A * (L + (d + 1) * (2 * T) * H) := by gcongr; omega

/-! ### Arithmetic estimates -/

/-- `(1 + 1 / M) ^ d ≤ 1 + 1 / R` when `(R + 1) d ≤ M`, without denominators. -/
private theorem mul_add_one_pow_le {R M d : ℕ} (h : (R + 1) * d ≤ M) :
    R * (M + 1) ^ d ≤ (R + 1) * M ^ d := by
  -- `(M + 1) ^ d * (M - d) ≤ M ^ (d + 1)` by induction.
  have key : ∀ e : ℕ, e ≤ M → (M + 1) ^ e * (M - e) ≤ M ^ (e + 1) := by
    intro e
    induction e with
    | zero => intro _; simp
    | succ e ih =>
      intro he
      have ih := ih (by omega)
      have hstep : (M + 1) * (M - (e + 1)) ≤ M * (M - e) := by
        obtain ⟨r, rfl⟩ : ∃ r, M = e + 1 + r := ⟨M - (e + 1), by omega⟩
        rw [show e + 1 + r - (e + 1) = r by omega, show e + 1 + r - e = r + 1 by omega]
        nlinarith
      calc (M + 1) ^ (e + 1) * (M - (e + 1)) = (M + 1) ^ e * ((M + 1) * (M - (e + 1))) := by
            ring
        _ ≤ (M + 1) ^ e * (M * (M - e)) := Nat.mul_le_mul_left _ hstep
        _ = M * ((M + 1) ^ e * (M - e)) := by ring
        _ ≤ M * M ^ (e + 1) := Nat.mul_le_mul_left _ ih
        _ = M ^ (e + 1 + 1) := by ring
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · simp
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hdM : d < M := by nlinarith
  have hpos : 0 < M - d := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc R * (M + 1) ^ d * (M - d) = R * ((M + 1) ^ d * (M - d)) := by ring
    _ ≤ R * M ^ (d + 1) := Nat.mul_le_mul_left _ (key d hdM.le)
    _ = M ^ d * (R * M) := by ring
    _ ≤ M ^ d * ((R + 1) * (M - d)) := by
        refine Nat.mul_le_mul_left _ ?_
        obtain ⟨r, rfl⟩ : ∃ r, M = d + r := ⟨M - d, by omega⟩
        rw [show d + r - d = r by omega]
        nlinarith
    _ = (R + 1) * M ^ d * (M - d) := by ring

/-! ### Asymptotics -/

/-- Lupanov's bound for single copies, without denominators: for every precision `Q`,
eventually `Q * m * size ≤ (Q + 1) * 2 ^ m` for every function on `m` inputs. -/
theorem eventually_mul_complexity_single_le (Q : ℕ) :
    ∀ᶠ m in atTop, ∀ g : BooleanFunction m,
      Q * m * complexity interpretation (single g) ≤ (Q + 1) * 2 ^ m := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · exact Eventually.of_forall fun m g => by simp
  obtain ⟨m₀, hm₀⟩ := Lupanov.complexity_le (1 / Q) (by positivity)
  filter_upwards [eventually_ge_atTop (max m₀ 1)] with m hm g
  have h := hm₀ m (le_of_max_le_left hm) g
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [le_div_iff₀ hmpos] at h
  have : (Q : ℝ) * m * complexity interpretation (single g) ≤ (Q + 1) * 2 ^ m :=
    calc (Q : ℝ) * m * complexity interpretation (single g) =
          Q * (complexity interpretation (single g) * m) := by ring
      _ ≤ Q * ((1 + 1 / Q) * 2 ^ m) := by gcongr
      _ = (Q + 1) * 2 ^ m := by field_simp
  exact_mod_cast this

/-- The per-layer overhead with prefixes of `2 log₂ n + 2` bits is eventually below
`2 ^ (n / 2)`, even after multiplication by `4 P n`. -/
private theorem eventually_overhead_le (P : ℕ) : ∀ᶠ n in atTop,
    4 * P * n * (32 * 8 ^ (2 * Nat.log 2 n + 2) * (2 * Nat.log 2 n + 3) * (n + 2)) ≤
      2 ^ (n / 2) := by
  have htend : Tendsto (fun n : ℕ => n / 2) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨2 * b, fun n hn => by omega⟩
  have h := htend.eventually
    (Nat.eventually_mul_pow_le_pow (73728 * P * 3 ^ 9) 9 (b := 2) (by norm_num))
  filter_upwards [h, eventually_ge_atTop 2] with n hn h2
  have hpow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hlog : Nat.log 2 n < n := (Nat.lt_two_pow_self).trans_le hpow
  have h8 : 8 ^ (2 * Nat.log 2 n + 2) ≤ 64 * n ^ 6 := by
    calc 8 ^ (2 * Nat.log 2 n + 2) = 64 * (2 ^ Nat.log 2 n) ^ 6 := by
          rw [show 8 = 2 ^ 3 by rfl, ← pow_mul, ← pow_mul]
          rw [show 3 * (2 * Nat.log 2 n + 2) = Nat.log 2 n * 6 + 6 by ring, pow_add]
          ring
      _ ≤ 64 * n ^ 6 := by gcongr
  calc 4 * P * n * (32 * 8 ^ (2 * Nat.log 2 n + 2) * (2 * Nat.log 2 n + 3) * (n + 2))
      ≤ 4 * P * n * (32 * (64 * n ^ 6) * (3 * n) * (3 * n)) := by
        gcongr <;> omega
    _ = 73728 * P * n ^ 9 := by ring
    _ ≤ 73728 * P * (3 * (n / 2)) ^ 9 := by gcongr; omega
    _ = 73728 * P * 3 ^ 9 * (n / 2) ^ 9 := by ring
    _ ≤ 2 ^ (n / 2) := hn

/-- The slack `X = 8 (P + 1)` in each of three factors costs less than `1 / (2 P)`. -/
private theorem two_mul_mul_succ_pow_three_le (P : ℕ) :
    2 * P * (8 * (P + 1) + 1) ^ 3 ≤ (2 * P + 1) * (8 * (P + 1)) ^ 3 := by
  nlinarith [Nat.zero_le (P ^ 3), Nat.zero_le (P ^ 2), Nat.zero_le P, Nat.zero_le (P ^ 4)]

/-- Discrete form of `d(n) log₂ n = o(n)`: for every multiplier `c`, eventually
`c * d n * log₂ n ≤ n`. -/
def IsUhligDepth (depth : ℕ → ℕ) : Prop :=
  ∀ c : ℕ, ∀ᶠ n in atTop, c * depth n * Nat.log 2 n ≤ n

/-- **Finite form of Uhlig's theorem.** Split `n = d * p + m` inputs into `d` prefixes of `p`
bits and `m > 0` remaining inputs, and let `X` be a slack with
`2 P (X + 1) ^ 3 ≤ (2 P + 1) X ^ 3`. Suppose the prefixes use at most a `1 / (X + 1)` fraction
of the input, the `2 ^ p` assignments of one prefix number at least `(X + 1) d`, single copies
on `m` inputs have size at most `(1 + 1 / X) 2 ^ m / m`, and the overhead of all layers is
negligible. Then every function on `n` inputs has `k ≤ 2 ^ d` independent copies of size `s`
with `P * n * s ≤ (P + 1) * 2 ^ n`, that is, at most `(1 + 1 / P) 2 ^ n / n` when `P > 0`. -/
theorem mul_complexity_directProduct_le {P X n d p m : ℕ}
    (hX : 2 * P * (X + 1) ^ 3 ≤ (2 * P + 1) * X ^ 3) (hX0 : 0 < X)
    (hnm : n = d * p + m) (hm : 0 < m)
    (hdp : (X + 1) * (d * p) ≤ n) (hd : (X + 1) * d ≤ 2 ^ p)
    (hL : ∀ g : BooleanFunction m,
      X * m * complexity interpretation (single g) ≤ (X + 1) * 2 ^ m)
    (hH : 4 * P * n * layerOverhead p n * 2 ^ (p * d + (d + d)) ≤ 2 ^ n)
    (f : BooleanFunction n) {k : ℕ} (hk : k ≤ 2 ^ d) :
    P * n * complexity interpretation (directProduct f k) ≤ (P + 1) * 2 ^ n := by
  -- Single copies on `m` inputs.
  set L := (X + 1) * 2 ^ m / (X * m) with hLdef
  have hXm : 0 < X * m := Nat.mul_pos hX0 hm
  have hL' : ∀ g : BooleanFunction m, complexity interpretation (directProduct g 1) ≤ L :=
    fun g => complexity_directProduct_one_le.trans <| (Nat.le_div_iff_mul_le hXm).mpr <| by
      calc complexity interpretation (single g) * (X * m) =
            X * m * complexity interpretation (single g) := by ring
        _ ≤ (X + 1) * 2 ^ m := hL g
  have hLspec : X * m * L ≤ (X + 1) * 2 ^ m := by
    rw [mul_comm]
    exact Nat.div_mul_le_self _ _
  -- `d` layers.
  set H := layerOverhead p n with hHdef
  have hH' : ∀ e < d, layerOverhead p (e * p + m) ≤ H := fun e he =>
    layerOverhead_mono (by have := Nat.mul_le_mul_right p he.le; omega)
  have hT := complexity_directProduct_two_pow_le hL' d n hnm hH' f
  have hmono := complexity_directProduct_mono (I := interpretation) (f := f) hk
  set K := 2 ^ p + 1 with hKdef
  have h2n : 2 ^ n = 2 ^ (p * d) * 2 ^ m := by rw [← pow_add, hnm, mul_comm d p]
  have hKX : X * K ^ d ≤ (X + 1) * 2 ^ (p * d) := by
    have := mul_add_one_pow_le (R := X) (M := 2 ^ p) (d := d) hd
    rwa [← pow_mul] at this
  have hK1 : K ^ d ≤ 2 * 2 ^ (p * d) := by
    have := mul_add_one_pow_le (R := 1) (M := 2 ^ p) (d := d)
      (le_trans (Nat.mul_le_mul_right d (by omega : 1 + 1 ≤ X + 1)) hd)
    rw [← pow_mul, ← hKdef] at this
    omega
  have hXn : X * n ≤ (X + 1) * m := by
    generalize hD : d * p = D at hnm hdp
    have e1 : X * n = X * D + X * m := by rw [hnm]; ring
    have e2 : (X + 1) * D = X * D + D := by ring
    have e3 : (X + 1) * m = X * m + m := by ring
    omega
  -- The leading term.
  have main : 2 * P * n * (K ^ d * L) ≤ (2 * P + 1) * 2 ^ n := by
    have h3 : X ^ 3 * (n * K ^ d * L) ≤ (X + 1) ^ 3 * 2 ^ n := by
      refine Nat.le_of_mul_le_mul_right ?_ hm
      calc X ^ 3 * (n * K ^ d * L) * m = (X * n) * (X * K ^ d) * (X * m * L) := by ring
        _ ≤ ((X + 1) * m) * ((X + 1) * 2 ^ (p * d)) * ((X + 1) * 2 ^ m) :=
          Nat.mul_le_mul (Nat.mul_le_mul hXn hKX) hLspec
        _ = (X + 1) ^ 3 * 2 ^ n * m := by rw [h2n]; ring
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < X ^ 3 by positivity)
    calc X ^ 3 * (2 * P * n * (K ^ d * L)) = 2 * P * (X ^ 3 * (n * K ^ d * L)) := by ring
      _ ≤ 2 * P * ((X + 1) ^ 3 * 2 ^ n) := Nat.mul_le_mul_left _ h3
      _ = 2 * P * (X + 1) ^ 3 * 2 ^ n := by ring
      _ ≤ (2 * P + 1) * X ^ 3 * 2 ^ n := Nat.mul_le_mul_right _ hX
      _ = X ^ 3 * ((2 * P + 1) * 2 ^ n) := by ring
  -- The overhead.
  have over : 2 * P * n * (K ^ d * (d * 2 ^ d * H)) ≤ 2 ^ n := by
    have hd2 : d * 2 ^ d ≤ 2 ^ d * 2 ^ d := Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    calc 2 * P * n * (K ^ d * (d * 2 ^ d * H))
        ≤ 2 * P * n * ((2 * 2 ^ (p * d)) * (2 ^ d * 2 ^ d * H)) := by gcongr
      _ = 4 * P * n * H * 2 ^ (p * d + (d + d)) := by rw [pow_add, pow_add]; ring
      _ ≤ 2 ^ n := hH
  calc P * n * complexity interpretation (directProduct f k)
      ≤ P * n * (K ^ d * (L + d * 2 ^ d * H)) := Nat.mul_le_mul_left _ (hmono.trans hT)
    _ ≤ (P + 1) * 2 ^ n := by
      have e1 : 2 * (P * n * (K ^ d * (L + d * 2 ^ d * H))) =
          2 * P * n * (K ^ d * L) + 2 * P * n * (K ^ d * (d * 2 ^ d * H)) := by ring
      have e2 : 2 * ((P + 1) * 2 ^ n) = (2 * P + 1) * 2 ^ n + 2 ^ n := by ring
      omega

/-- **Uhlig's theorem** for circuit size. If `d(n) log₂ n = o(n)`, then for every precision `P`,
eventually every function on `n` inputs has `k ≤ 2 ^ d(n)` independent copies of size `s` with
`P * n * s ≤ (P + 1) * 2 ^ n`: for `P > 0`, at most `(1 + 1 / P) 2 ^ n / n`. The case `P = 0`
holds trivially. Prefixes have `2 log₂ n + 2` bits. -/
theorem eventually_mul_complexity_directProduct_le {depth : ℕ → ℕ}
    (hdepth : IsUhligDepth depth) (P : ℕ) :
    ∀ᶠ n in atTop, ∀ (f : BooleanFunction n) (k : ℕ), k ≤ 2 ^ depth n →
      P * n * complexity interpretation (directProduct f k) ≤ (P + 1) * 2 ^ n := by
  set X := 8 * (P + 1) with hXdef
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (eventually_mul_complexity_single_le X)
  filter_upwards [hdepth (4 * (X + 1)), eventually_overhead_le P,
    eventually_ge_atTop (2 * m₀ + X + 2)] with n hD hpoly hn f k hk
  set ℓ := Nat.log 2 n with hℓdef
  set d := depth n with hddef
  set p := 2 * ℓ + 2 with hpdef
  have hℓ : 1 ≤ ℓ := Nat.log_pos (by norm_num) (by omega)
  have hltℓ : n < 2 * 2 ^ ℓ := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    rw [← hℓdef, pow_succ] at this
    omega
  have hdp : (X + 1) * (d * p) ≤ n :=
    calc (X + 1) * (d * p) ≤ (X + 1) * (d * (4 * ℓ)) := by gcongr; omega
      _ = 4 * (X + 1) * d * ℓ := by ring
      _ ≤ n := hD
  have h9 : 9 * (d * p) ≤ n := le_trans (Nat.mul_le_mul_right _ (by omega)) hdp
  have hdn : d ≤ n := by
    have : d ≤ d * p := Nat.le_mul_of_pos_right _ (by omega)
    omega
  refine mul_complexity_directProduct_le (X := X) (d := d) (p := p) (m := n - d * p)
    (hXdef ▸ two_mul_mul_succ_pow_three_le P) (by omega) (by omega) (by omega) hdp ?_
    (hm₀ _ (by omega)) ?_ f hk
  · calc (X + 1) * d ≤ n * n := Nat.mul_le_mul (by omega) hdn
      _ ≤ (2 * 2 ^ ℓ) * (2 * 2 ^ ℓ) := Nat.mul_le_mul hltℓ.le hltℓ.le
      _ = 2 ^ p := by rw [hpdef]; ring
  · have hexp : n / 2 + (p * d + (d + d)) ≤ n := by
      have h4d : 4 * d ≤ d * p := by rw [mul_comm d p]; exact Nat.mul_le_mul_right d (by omega)
      rw [mul_comm p d]
      omega
    calc 4 * P * n * layerOverhead p n * 2 ^ (p * d + (d + d))
        ≤ 2 ^ (n / 2) * 2 ^ (p * d + (d + d)) :=
          Nat.mul_le_mul_right _ ((Nat.mul_le_mul_left _ (layerOverhead_le p n)).trans hpoly)
      _ = 2 ^ (n / 2 + (p * d + (d + d))) := by rw [← pow_add]
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hexp

/-- **Uhlig's theorem** for mass complexity, which charges NOT, AND and OR once and constants
never. If `d(n) log₂ n = o(n)`, then for every precision `P`, eventually
`P * n * massComplexity f k ≤ (P + 1) * 2 ^ n` for every function `f` on `n` inputs and every
number of copies `k ≤ 2 ^ d(n)`. For `P > 0` the bound is `(1 + 1 / P) 2 ^ n / n`; the case
`P = 0` holds trivially. -/
theorem eventually_mul_massComplexity_le {depth : ℕ → ℕ} (hdepth : IsUhligDepth depth)
    (P : ℕ) :
    ∀ᶠ n in atTop, ∀ (f : BooleanFunction n) (k : ℕ), k ≤ 2 ^ depth n →
      (P * n : ℕ∞) * massComplexity f k ≤ ((P + 1) * 2 ^ n : ℕ) := by
  filter_upwards [eventually_mul_complexity_directProduct_le hdepth P] with n h f k hk
  calc (P * n : ℕ∞) * massComplexity f k
      ≤ (P * n : ℕ∞) * (complexity interpretation (directProduct f k) : ℕ) := by
        gcongr
        exact massComplexity_le_complexity
    _ = ((P * n * complexity interpretation (directProduct f k) : ℕ) : ℕ∞) := by push_cast; ring
    _ ≤ ((P + 1) * 2 ^ n : ℕ) := by exact_mod_cast h f k hk

end Cslib.Circuits.Boolean.MassProduction

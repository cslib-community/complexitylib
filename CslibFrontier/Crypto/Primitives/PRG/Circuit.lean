/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.Basic
public import Cslib.Crypto.Primitives.PRG.Defs
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import CslibFrontier.Foundations.Data.Finset.Expect
import Cslib.Crypto.Primitives.PRG.Basic

/-!
# Pseudorandomness against circuits

Concrete security of generators (`Cslib.Crypto.PRG.Generator.Secure`) is relative to a class of
admissible tests. This module supplies the nonuniform class: the deterministic tests computed by
De Morgan circuits with at most `t` gates (`IsCircuitTest`), where every AND, OR, NOT and constant
gate counts. It states the security notions used by the natural proofs barrier
[RazborovRudich1997, Section 4]:

* a keyed family of Boolean functions is pseudorandom against circuits when the generator mapping
  a key to the truth table of its function is (`truthTableGenerator`). The tests read the whole
  truth table, that is they query the function at every input. The family is *exponentially
  secure* when it resists circuits of size `2 ^ (c n)` with error `2 ^ (-c n)` for every `c`
  (`IsExponentiallySecure`);
* a family of length-doubling generators is *subexponentially secure* when, for all long seeds of
  length `k`, it resists circuits of size `2 ^ m` with error `2 ^ (-m)` for `m ^ d ≤ k`
  (`IsSubexponentiallySecure`). Security against circuits of size `2 ^ (k ^ ε)` with error
  `2 ^ (-k ^ ε)` gives it for `d ε ≥ 1` (`IsSubexponentiallySecure.of_rpow`).

It also proves the hybrid argument for independent samples in the form of averages
(`abs_expect_comp_sub_expect_le`): replacing `|ι|` independent outputs of a function by uniform
values, one coordinate at a time, costs at most `|ι|` times the cost of one replacement with all
other coordinates fixed.

## Main definitions

* `Cslib.Crypto.PRG.IsCircuitTest`: the tests computed by circuits with at most `t` gates.
* `Cslib.Crypto.PRG.truthTableGenerator`: a keyed family of Boolean functions, as a generator of
  truth tables.
* `Cslib.Crypto.PRG.IsExponentiallySecure`: keyed families pseudorandom against circuits of size
  `2 ^ (c n)` with error `2 ^ (-c n)`, for every `c`.
* `Cslib.Crypto.PRG.IsSubexponentiallySecure`: length-doubling generators resisting circuits of
  size `2 ^ (k ^ (1 / d))`.

## Main results

* `Cslib.Crypto.PRG.IsSubexponentiallySecure.of_rpow`: security against circuits of size
  `2 ^ (k ^ ε)` gives subexponential security.
* `Cslib.Crypto.PRG.abs_expect_comp_sub_expect_le`: the hybrid argument for independent samples.

## References

* [A. A. Razborov, S. Rudich, *Natural proofs*][RazborovRudich1997]
-/

@[expose] public section

namespace Cslib.Crypto.PRG

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.MCSP Filter Finset Function
open scoped BigOperators NNReal

/-! ### Tests computed by circuits -/

/-- The tests on `m`-bit strings computed by De Morgan circuits with at most `t` gates: the
deterministic tests whose circuit complexity is at most `t`. As the admissible adversaries of
`Cslib.Crypto.PRG.Generator.Secure`, they express security against circuits of size `t`. -/
def IsCircuitTest {m : ℕ} (t : ℕ) (adversary : Adversary (BitString m)) : Prop :=
  ∃ test : BooleanFunction m, complexity interpretation (single test) ≤ t ∧
    adversary = fun x => PMF.pure (test x)

section Generator

variable {Key : Type*} {n : ℕ}

/-- The generator mapping a key to the truth table of the function `F key`. Its security against
`IsCircuitTest t` is the pseudorandomness of the keyed family `F` against circuits with at most
`t` gates that read the whole truth table, that is that query the function at every input. -/
def truthTableGenerator (F : Key → BooleanFunction n) : Generator Key (BitString (2 ^ n)) :=
  ⟨fun key => truthTable n (F key)⟩

@[simp] theorem truthTableGenerator_apply (F : Key → BooleanFunction n) (key : Key) :
    truthTableGenerator F key = truthTable n (F key) :=
  rfl

end Generator

section Family

variable {Key : ℕ → Type*} [∀ n, Fintype (Key n)] [∀ n, Nonempty (Key n)]

/-- A keyed family `F` of Boolean functions is *exponentially secure* against circuits when, for
every `c`, eventually no test computed with at most `2 ^ (c n)` gates distinguishes the truth
table of `F n key`, for a uniformly random key, from a uniformly random truth table with advantage
more than `2 ^ (-c n)`. This is the hypothesis of the natural proofs barrier
[RazborovRudich1997, Section 4]. The tests read the whole truth table, that is they query the
function at every input. -/
def IsExponentiallySecure (F : ∀ n, Key n → BooleanFunction n) : Prop :=
  ∀ c, ∀ᶠ n in atTop,
    (truthTableGenerator (F n)).Secure (IsCircuitTest (2 ^ (c * n))) (2 ^ (c * n))⁻¹

end Family

/-- A family of length-doubling generators is *subexponentially secure* against circuits, with
exponent `1 / d`, when for all sufficiently long seeds, of length `k`, no test computed with at
most `2 ^ m` gates has advantage more than `2 ^ (-m)` against `G k`, for every `m` with
`m ^ d ≤ k`. Up to rounding, `G k` resists circuits of size `2 ^ (k ^ ε)` with advantage
`2 ^ (-k ^ ε)` for `ε = 1 / d`, the hypothesis of [RazborovRudich1997, Section 4]. -/
def IsSubexponentiallySecure (G : ∀ k, Generator (BitString k) (BitString (2 * k))) (d : ℕ) :
    Prop :=
  ∀ᶠ k in atTop, ∀ m, m ^ d ≤ k → (G k).Secure (IsCircuitTest (2 ^ m)) (2 ^ m)⁻¹

/-- A generator family that, for all long seeds, resists circuits of size `2 ^ (k ^ ε)` with
advantage `2 ^ (-k ^ ε)`, for some `ε > 0`, is subexponentially secure with exponent `1 / d` for
every `d ≥ 1 / ε`. -/
theorem IsSubexponentiallySecure.of_rpow {G : ∀ k, Generator (BitString k) (BitString (2 * k))}
    {ε : ℝ} {d : ℕ} (hd : 1 ≤ d * ε)
    (hG : ∀ᶠ k in atTop, (G k).Secure (IsCircuitTest ⌊(2 : ℝ) ^ ((k : ℝ) ^ ε)⌋₊)
      ((2 : ℝ≥0) ^ ((k : ℝ) ^ ε))⁻¹) :
    IsSubexponentiallySecure G d := by
  filter_upwards [hG] with k hk m hm
  have hmk : (m : ℝ) ≤ (k : ℝ) ^ ε := by
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp only [CharP.cast_eq_zero]; positivity
    have hε : 0 < ε := by
      rcases le_or_gt ε 0 with h | h
      · nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
      · exact h
    calc (m : ℝ) = (m : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (m : ℝ) ^ ((d : ℝ) * ε) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm0) hd
      _ = ((m : ℝ) ^ d) ^ ε := by rw [Real.rpow_mul (by positivity), Real.rpow_natCast]
      _ ≤ (k : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hm) hε.le
  have hsize : 2 ^ m ≤ ⌊(2 : ℝ) ^ ((k : ℝ) ^ ε)⌋₊ := by
    refine Nat.le_floor ?_
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two hmk
  have herr : ((2 : ℝ≥0) ^ ((k : ℝ) ^ ε))⁻¹ ≤ (2 ^ m)⁻¹ := by
    refine inv_anti₀ (by positivity) ?_
    rw [← NNReal.rpow_natCast]
    exact NNReal.rpow_le_rpow_of_exponent_le one_le_two hmk
  exact (hk.of_admissible fun A ⟨test, htest, hA⟩ => ⟨test, htest.trans hsize, hA⟩).mono herr

/-! ### The hybrid argument for independent samples -/

section Independent

variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α] [Fintype β]
  [Nonempty β]

/-- **The hybrid argument for independent samples.** Let `T` be a statistic of `ι`-indexed tuples
in `β`. If, with all other coordinates fixed, replacing `g a` for a uniform `a` by a uniform `b` at
one coordinate changes the average of `T` by at most `ε`, then replacing every coordinate changes
it by at most `|ι| ε`. For `T` the acceptance probability of a test, this is the security of
independent copies of a generator `g` with loss `|ι|`. -/
theorem abs_expect_comp_sub_expect_le (g : α → β) (T : (ι → β) → ℝ) {ε : ℝ}
    (hT : ∀ (c : ι → β) (i : ι), |𝔼 a, T (update c i (g a)) - 𝔼 b, T (update c i b)| ≤ ε) :
    |𝔼 s : ι → α, T (fun i => g (s i)) - 𝔼 y : ι → β, T y| ≤ Fintype.card ι * ε := by
  -- the hybrid in which the coordinates in `S` are uniform
  let v : Finset ι → (ι → α) → (ι → β) → ι → β := fun S s y j => if j ∈ S then y j else g (s j)
  let H : Finset ι → ℝ := fun S => 𝔼 s, 𝔼 y, T (v S s y)
  have hstep (i : ι) (S : Finset ι) (hi : i ∉ S) : |H S - H (insert i S)| ≤ ε := by
    have hS : H S = 𝔼 s, 𝔼 y, 𝔼 a, T (update (v S s y) i (g a)) := by
      change 𝔼 s, 𝔼 y, T (v S s y) = _
      rw [← Fintype.expect_expect_update (fun s => 𝔼 y, T (v S s y)) i]
      refine expect_congr rfl fun s _ => ?_
      rw [expect_comm]
      refine expect_congr rfl fun y _ => expect_congr rfl fun a _ => congrArg T ?_
      funext j
      by_cases hj : j = i
      · subst hj; simp [v, hi]
      · simp [v, hj]
    have hS' : H (insert i S) = 𝔼 s, 𝔼 y, 𝔼 b, T (update (v S s y) i b) := by
      change 𝔼 s, 𝔼 y, T (v (insert i S) s y) = _
      refine expect_congr rfl fun s _ => ?_
      rw [← Fintype.expect_expect_update (fun y => T (v (insert i S) s y)) i]
      refine expect_congr rfl fun y _ => expect_congr rfl fun b _ => congrArg T ?_
      funext j
      by_cases hj : j = i
      · subst hj; simp [v]
      · simp [v, hj]
    rw [hS, hS', ← expect_sub_distrib]
    refine (abs_expect_le _ _).trans ?_
    refine (expect_le_expect fun s _ => ?_).trans_eq (Fintype.expect_const ε)
    rw [← expect_sub_distrib]
    refine (abs_expect_le _ _).trans ?_
    refine (expect_le_expect fun y _ => ?_).trans_eq (Fintype.expect_const ε)
    exact hT _ i
  have hind (S : Finset ι) : |H ∅ - H S| ≤ S.card * ε := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert i S hi ih =>
      calc |H ∅ - H (insert i S)| ≤ |H ∅ - H S| + |H S - H (insert i S)| := abs_sub_le _ _ _
        _ ≤ S.card * ε + ε := add_le_add ih (hstep i S hi)
        _ = (insert i S).card * ε := by rw [card_insert_of_notMem hi]; push_cast; ring
  have h0 : H ∅ = 𝔼 s : ι → α, T (fun i => g (s i)) := by
    simp only [H, v, notMem_empty, ite_false, Fintype.expect_const]
  have h1 : H univ = 𝔼 y : ι → β, T y := by
    simp only [H, v, mem_univ, ite_true, Fintype.expect_const]
  simpa only [h0, h1, card_univ] using hind univ

end Independent

end Cslib.Crypto.PRG

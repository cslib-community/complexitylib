/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Totient
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.FieldTheory.Finite.Basic

/-!
# The AKS primality criterion

Agrawal, Kayal and Saxena's polynomial identity generalizes Fermat's little theorem: for `n ≥ 2`
and `a` coprime to `n`, `n` is prime exactly when `(X + a)^n = X^n + a` in `(ℤ / n)[X]`
(`Cslib.AKS.prime_iff_add_pow_eq`) [Agrawal, Kayal, Saxena, Lemma 2.1][AKS2004]. If `n` is prime,
the identity is the Frobenius endomorphism together with `a^n = a`. If `n` is composite with a
prime factor `q < n`, the coefficient `C(n, q) a^{n - q}` of `X^q` is nonzero modulo `n`, because
`q · C(n, q) = n · C(n - 1, q - 1)` and Lucas's theorem gives `C(n - 1, q - 1) ≡ 1 (mod q)`.

Checking the identity directly takes `n` coefficients. The AKS algorithm checks it only modulo
`X^r - 1`, for a small `r`, and for a few values of `a`. Given `r`, the algorithm outputs PRIME
exactly when `n` is not a perfect power, no `a ≤ r` has `1 < gcd(a, n) < n`, and either `n ≤ r` or
`(X + a)^n ≡ X^n + a (mod X^r - 1, n)` for every `1 ≤ a ≤ ⌊√φ(r) log₂ n⌋`
(`Cslib.AKS.Passes`). `Cslib.AKS.PassesUpTo n r A` states the same tests with the congruence
checked for `1 ≤ a ≤ A`, and `Passes n r` is its case `A = ⌊√φ(r) log₂ n⌋`. Every prime passes,
for every `r` and `A` (`Cslib.AKS.passesUpTo_of_prime`, `Cslib.AKS.passes_of_prime`): this is the
easy direction of [Agrawal, Kayal, Saxena, Theorem 4.1][AKS2004]. The converse, for `r` with
multiplicative order of `n` modulo `r` above `log₂² n`, is the substance of their theorem.

## Main definitions

* `Cslib.AKS.IsPerfectPower`: `n = a ^ b` for some `b > 1`.
* `Cslib.AKS.numTests`: the number `⌊√φ(r) log₂ n⌋` of tested values of `a`.
* `Cslib.AKS.Congruence`: `(X + a)^n ≡ X^n + a (mod X^r - 1, n)`.
* `Cslib.AKS.PassesUpTo`: the AKS tests, with the congruence checked for `1 ≤ a ≤ A`.
* `Cslib.AKS.Passes`: the conditions under which the AKS algorithm, given `r`, outputs PRIME.

## Main results

* `Cslib.AKS.not_dvd_choose_of_prime_dvd`: a composite `n` does not divide `C(n, q)` for a prime
  factor `q < n`.
* `Cslib.AKS.prime_iff_add_pow_eq`: the AKS identity characterizes primes.
* `Cslib.AKS.passesUpTo_of_prime`, `Cslib.AKS.passes_of_prime`: every prime passes the AKS tests.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.AKS

open Polynomial

/-! ### The polynomial identity -/

/-- For a prime factor `q < n` of `n`, `n` does not divide `C(n, q)`. Indeed
`n · C(n - 1, q - 1) = q · C(n, q)`, and `C(n - 1, q - 1) ≡ 1 (mod q)` by Lucas's theorem, since
`n - 1 ≡ q - 1 (mod q)`. -/
theorem not_dvd_choose_of_prime_dvd {n q : ℕ} (hq : q.Prime) (hqn : q ∣ n) (hlt : q < n) :
    ¬ n ∣ n.choose q := by
  rintro ⟨m, hm⟩
  have hq1 : 1 ≤ q := hq.one_lt.le
  obtain ⟨k, rfl⟩ := hqn
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hlt
    · exact hk
  -- `n · C(n - 1, q - 1) = C(n, q) · q`.
  have hid := Nat.add_one_mul_choose_eq (q * k - 1) (q - 1)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hq.ne_zero (by omega))),
    Nat.sub_add_cancel hq1, hm] at hid
  -- Hence `C(n - 1, q - 1) = m q`.
  have hdiv : q ∣ (q * k - 1).choose (q - 1) := by
    refine ⟨m, Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hq.pos (by omega : 0 < k)) ?_⟩
    rw [hid]
    ring
  -- But Lucas's theorem gives `C(n - 1, q - 1) ≡ 1 (mod q)`.
  have := Fact.mk hq
  have hlucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := q * k - 1) (k := q - 1)
    (p := q)
  have hmod : (q * k - 1) % q = q - 1 := by
    have : q * k - 1 = (q - 1) + q * (k - 1) := by
      rw [Nat.mul_sub, mul_one]
      have : q ≤ q * k := Nat.le_mul_of_pos_right q hk
      omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [hmod, Nat.mod_eq_of_lt (by omega : q - 1 < q), Nat.div_eq_of_lt (by omega : q - 1 < q),
    Nat.choose_self, Nat.choose_zero_right, mul_one] at hlucas
  have h1 := (Nat.modEq_zero_iff_dvd.mpr hdiv).symm.trans hlucas
  rw [Nat.ModEq, Nat.zero_mod, Nat.mod_eq_of_lt hq.one_lt] at h1
  exact absurd h1 (by norm_num)

/-- **Freshman's dream modulo a prime.** For a prime `p`, `(X + a)^p = X^p + a` in `(ℤ / p)[X]`. -/
theorem add_pow_eq_of_prime {p : ℕ} (hp : p.Prime) (a : ZMod p) :
    (X + C a) ^ p = X ^ p + C a := by
  have := Fact.mk hp
  rw [add_pow_char, ← C_pow, ZMod.pow_card]

/-- If `(X + a)^n = X^n + a` in `(ℤ / n)[X]` for a unit `a` and `n ≥ 2`, then `n` is prime: for a
prime factor `q < n`, the coefficient `a^{n - q} C(n, q)` of `X^q` would vanish. -/
theorem prime_of_add_pow_eq {n : ℕ} (hn : 2 ≤ n) {a : ZMod n} (ha : IsUnit a)
    (h : (X + C a) ^ n = X ^ n + C a) : n.Prime := by
  by_contra hnp
  set q := n.minFac
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hqlt : q < n := (Nat.not_prime_iff_minFac_lt hn).mp hnp
  have hcoeff := congrArg (fun f => f.coeff q) h
  simp only [coeff_X_add_C_pow, coeff_add, coeff_X_pow, coeff_C, hqlt.ne, hq.ne_zero,
    ite_false, add_zero] at hcoeff
  have hchoose : ((n.choose q : ℕ) : ZMod n) = 0 :=
    (ha.pow (n - q)).mul_right_eq_zero.mp hcoeff
  exact not_dvd_choose_of_prime_dvd hq (Nat.minFac_dvd n) hqlt
    ((ZMod.natCast_eq_zero_iff _ _).mp hchoose)

/-- **The AKS identity** [Agrawal, Kayal, Saxena, Lemma 2.1][AKS2004]: for `n ≥ 2` and a unit `a`
of `ℤ / n`, `n` is prime exactly when `(X + a)^n = X^n + a` in `(ℤ / n)[X]`. -/
theorem prime_iff_add_pow_eq {n : ℕ} (hn : 2 ≤ n) {a : ZMod n} (ha : IsUnit a) :
    n.Prime ↔ (X + C a) ^ n = X ^ n + C a :=
  ⟨fun hp => add_pow_eq_of_prime hp a, prime_of_add_pow_eq hn ha⟩

/-! ### The tests of the AKS algorithm -/

/-- `n` is a perfect power: `n = a ^ b` for some `a` and some `b > 1`. -/
def IsPerfectPower (n : ℕ) : Prop := ∃ a b : ℕ, 1 < b ∧ a ^ b = n

/-- The number `⌊√φ(r) log₂ n⌋` of values of `a` for which the AKS algorithm tests its
congruence. -/
noncomputable def numTests (n r : ℕ) : ℕ :=
  ⌊Real.sqrt (Nat.totient r) * Real.logb 2 n⌋₊

/-- The AKS congruence `(X + a)^n ≡ X^n + a (mod X^r - 1, n)`, stated in the quotient ring
`(ℤ / n)[X] / (X^r - 1)`. -/
def Congruence (n r a : ℕ) : Prop :=
  AdjoinRoot.mk (X ^ r - 1 : (ZMod n)[X]) ((X + C (a : ZMod n)) ^ n) =
    AdjoinRoot.mk (X ^ r - 1 : (ZMod n)[X]) (X ^ n + C (a : ZMod n))

/-- **The AKS tests with the congruence checked up to `A`**: `n` is not a perfect power (step 1),
every `1 ≤ a ≤ r` has `gcd(a, n) = 1` or `gcd(a, n) = n` (step 3; for `n ≥ 1`, no `a ≤ r` has
`1 < gcd(a, n) < n`), and either `n ≤ r` (step 4) or the congruence holds for every `1 ≤ a ≤ A`
(step 5). -/
def PassesUpTo (n r A : ℕ) : Prop :=
  ¬ IsPerfectPower n ∧ (∀ a, 1 ≤ a → a ≤ r → a.gcd n = 1 ∨ a.gcd n = n) ∧
    (n ≤ r ∨ ∀ a, 1 ≤ a → a ≤ A → Congruence n r a)

/-- **The conditions under which the AKS algorithm outputs PRIME**, given `r`
[Agrawal, Kayal, Saxena, Section 4][AKS2004]: the tests of `PassesUpTo`, with the congruence
checked for every `1 ≤ a ≤ ⌊√φ(r) log₂ n⌋` in step 5. The algorithm chooses `r` as the least
number for which the multiplicative order of `n` modulo `r` exceeds `log₂² n` (step 2). -/
def Passes (n r : ℕ) : Prop := PassesUpTo n r (numTests n r)

/-- A prime is not a perfect power. -/
theorem not_isPerfectPower_of_prime {p : ℕ} (hp : p.Prime) : ¬ IsPerfectPower p := by
  rintro ⟨a, b, hb, hab⟩
  exact absurd ((hp.pow_eq_iff).mp hab).2 (by omega)

/-- The AKS identity for a prime holds modulo `X^r - 1`. -/
theorem congruence_of_prime {p : ℕ} (hp : p.Prime) (r a : ℕ) : Congruence p r a := by
  rw [Congruence, add_pow_eq_of_prime hp]

/-- **Every prime passes the AKS tests**, for every `r` and every bound `A` on the tested `a`:
the easy direction of [Agrawal, Kayal, Saxena, Theorem 4.1][AKS2004]. -/
theorem passesUpTo_of_prime {p : ℕ} (hp : p.Prime) (r A : ℕ) : PassesUpTo p r A := by
  refine ⟨not_isPerfectPower_of_prime hp, fun a _ _ => ?_, Or.inr fun a _ _ =>
    congruence_of_prime hp r a⟩
  rcases (Nat.coprime_or_dvd_of_prime hp a) with h | h
  · exact Or.inl (Nat.Coprime.symm h)
  · exact Or.inr (Nat.gcd_eq_right h)

/-- **Every prime passes the AKS tests**, for every `r`: the easy direction of
[Agrawal, Kayal, Saxena, Theorem 4.1][AKS2004]. -/
theorem passes_of_prime {p : ℕ} (hp : p.Prime) (r : ℕ) : Passes p r :=
  passesUpTo_of_prime hp r (numTests p r)

end Cslib.AKS

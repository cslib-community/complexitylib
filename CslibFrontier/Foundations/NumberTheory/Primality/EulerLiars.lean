/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/NumberTheory/` next to `FermatPsp`)

public import CslibFrontier.Foundations.NumberTheory.Primality.Witness
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.FieldTheory.Finite.Basic

/-!
# Euler liars and the Solovay–Strassen bound

The Solovay–Strassen test [Solovay and Strassen][SolovayStrassen1977] declares an odd `n > 1`
composite when a random base `a` has `a ^ ((n - 1) / 2) ≠ J(a | n)` modulo `n`, where `J(a | n)`
is the Jacobi symbol. By Euler's criterion every unit passes modulo an odd prime. The units that
pass modulo `n`, the **Euler liars**, form a subgroup of `(ZMod n)ˣ`, the equalizer of two
homomorphisms; modulo an odd composite this subgroup is proper, so at most half of the units are
Euler liars.

## Main definitions

* `ZMod.jacobiSymUnit`: the Jacobi symbol `J(· | n)` as a homomorphism `(ZMod n)ˣ →* ℤˣ`.
* `ZMod.eulerLiars`: the subgroup of Euler liars modulo `n`.

## Main results

* `ZMod.mem_eulerLiars`: the membership condition `a ^ ((n - 1) / 2) = J(a | n)`.
* `ZMod.eulerLiars_eq_top`: modulo an odd prime every unit is an Euler liar (Euler's criterion).
* `ZMod.eulerLiars_ne_top`: modulo an odd composite some unit is not an Euler liar.
* `ZMod.two_mul_card_eulerLiars_le`: modulo an odd composite `n`, twice the number of Euler liars
  is at most `φ(n)`.

## References

* [R. Solovay, V. Strassen, *A fast Monte-Carlo test for primality*][SolovayStrassen1977]
* [R. Motwani, P. Raghavan, *Randomized Algorithms*][MotwaniRaghavan95]
-/

public section

open scoped NumberTheorySymbols

namespace ZMod

/-- The Jacobi symbol depends only on the residue: reducing modulo a divisor. -/
theorem jacobiSym_val_castHom {n q : ℕ} [NeZero n] [NeZero q] (hq : q ∣ n) (z : ZMod n) :
    J(((castHom hq (ZMod q) z).val : ℤ) | q) = J((z.val : ℤ) | q) := by
  apply jacobiSym.mod_left'
  rw [← ZMod.intCast_eq_intCast_iff', Int.cast_natCast, Int.cast_natCast, natCast_zmod_val,
    castHom_apply, ← ZMod.natCast_val (R := ZMod q) z]

/-- The Jacobi symbol `J(a | n)` of a unit `a` modulo `n`, as a unit of `ℤ`. -/
def jacobiSymUnit (n : ℕ) : (ZMod n)ˣ →* ℤˣ where
  toFun a :=
    have h : J(((a : ZMod n).val : ℤ) | n) * J(((a : ZMod n).val : ℤ) | n) = 1 := by
      rw [← sq]
      exact jacobiSym.sq_one (by rw [Int.gcd_natCast_natCast]; exact val_coe_unit_coprime a)
    ⟨J(((a : ZMod n).val : ℤ) | n), J(((a : ZMod n).val : ℤ) | n), h, h⟩
  map_one' := by
    ext
    simp only [Units.val_one]
    rw [val_one_eq_one_mod, Int.natCast_mod, Nat.cast_one, ← jacobiSym.mod_left,
      jacobiSym.one_left]
  map_mul' a b := by
    ext
    simp only [Units.val_mul, val_mul]
    rw [Int.natCast_mod, ← jacobiSym.mod_left, Nat.cast_mul, jacobiSym.mul_left]

@[simp] theorem val_jacobiSymUnit (n : ℕ) (a : (ZMod n)ˣ) :
    (jacobiSymUnit n a : ℤ) = J(((a : ZMod n).val : ℤ) | n) := by
  simp only [jacobiSymUnit, MonoidHom.coe_mk, OneHom.coe_mk]

/-- The **Euler liars** modulo `n`: the units `a` with `a ^ ((n - 1) / 2) = J(a | n)`, the bases
on which the Solovay–Strassen test fails to detect that `n` is composite. -/
def eulerLiars (n : ℕ) : Subgroup (ZMod n)ˣ :=
  MonoidHom.eqLocus (powMonoidHom ((n - 1) / 2))
    ((Units.map (Int.castRingHom (ZMod n)).toMonoidHom).comp (jacobiSymUnit n))

theorem mem_eulerLiars {n : ℕ} {a : (ZMod n)ˣ} :
    a ∈ eulerLiars n ↔
      (a : ZMod n) ^ ((n - 1) / 2) = (J(((a : ZMod n).val : ℤ) | n) : ZMod n) := by
  change powMonoidHom _ a = _ ↔ _
  rw [Units.ext_iff]
  simp [jacobiSymUnit]

/-- **Euler's criterion**: modulo an odd prime, every unit is an Euler liar. -/
theorem eulerLiars_eq_top {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : eulerLiars p = ⊤ := by
  rw [eq_top_iff]
  intro a _
  rw [mem_eulerLiars, ← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_pow, Int.cast_natCast,
    natCast_zmod_val]
  congr 1
  have := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨k, hk⟩ := this
  omega

/-- **Euler liars of a composite**: modulo an odd composite `n`, some unit is not an Euler liar.
If `p ^ 2 ∣ n` for an odd prime `p`, the unit `1 + n / p` has no power `-1` and its powers equal to
`1` have exponents divisible by `p`, which is coprime to `n - 1`. Otherwise `n = p q` with `p` an
odd prime coprime to `q > 1`, and the unit that is a quadratic non-residue modulo `p` and `1` modulo
`q` has Jacobi symbol `-1` while its power is `1` modulo `q`. -/
theorem eulerLiars_ne_top {n : ℕ} [NeZero n] (hodd : Odd n) (h1 : 1 < n) (hn : ¬ n.Prime) :
    eulerLiars n ≠ ⊤ := by
  intro htop
  have hall : ∀ a : (ZMod n)ˣ, (a : ZMod n) ^ ((n - 1) / 2) =
      (J(((a : ZMod n).val : ℤ) | n) : ZMod n) := fun a => mem_eulerLiars.1 (htop ▸ trivial)
  have hpm : ∀ a : (ZMod n)ˣ, (a : ZMod n) ^ ((n - 1) / 2) = 1 ∨
      (a : ZMod n) ^ ((n - 1) / 2) = -1 := fun a => by
    rw [hall a]
    rcases jacobiSym.eq_one_or_neg_one (a := ((a : ZMod n).val : ℤ)) (b := n)
      (by rw [Int.gcd_natCast_natCast]; exact val_coe_unit_coprime a) with h | h <;>
      simp only [h, Int.cast_one, Int.cast_neg, true_or, or_true]
  rcases Nat.exists_sq_dvd_or_eq_mul_coprime hodd h1 hn with ⟨p, hp, hp2, hpn⟩ |
    ⟨p, q, rfl, hp, hp2, hpq, hqodd, hq1⟩
  · obtain ⟨c, hc1, hcn⟩ := exists_unit_pow_of_sq_dvd hp hp2 (NeZero.ne n) hpn
    rcases hpm c with h | h
    · have hdvd : p ∣ n - 1 := by
        obtain ⟨k, hk⟩ := hodd
        have := hc1 _ h
        rw [show n - 1 = 2 * ((n - 1) / 2) by omega]
        exact Dvd.dvd.mul_left this 2
      have hpn' : p ∣ n := (Dvd.intro_left _ rfl : p ∣ p ^ 2).trans hpn
      have : p ∣ 1 := by
        have := Nat.dvd_sub hpn' hdvd
        rwa [show n - (n - 1) = 1 by omega] at this
      exact hp.one_lt.ne' (Nat.dvd_one.1 this)
    · exact hcn _ h
  · have : Fact p.Prime := ⟨hp⟩
    have : NeZero q := ⟨by omega⟩
    obtain ⟨g, hg⟩ := quadraticChar_exists_neg_one (F := ZMod p)
      (by rw [ringChar_zmod_n]; exact hp2)
    have hg0 : g ≠ 0 := by rintro rfl; simp at hg
    obtain ⟨c, hcp, hcq⟩ := exists_unit_castHom_eq hpq (Units.mk0 g hg0) 1
    have hJ : J(((c : ZMod (p * q)).val : ℤ) | p * q) = -1 := by
      rw [jacobiSym.mul_right, ← jacobiSym_val_castHom (dvd_mul_right p q),
        ← jacobiSym_val_castHom (dvd_mul_left q p), hcp, hcq, Units.val_one, val_one_eq_one_mod,
        Int.natCast_mod, Nat.cast_one, ← jacobiSym.mod_left, jacobiSym.one_left, mul_one,
        Units.val_mk0, ← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast,
        natCast_zmod_val, hg]
    have h := hall c
    rw [hJ] at h
    have h' := congrArg (castHom (dvd_mul_left q p) (ZMod q)) h
    rw [map_pow, hcq, Units.val_one, one_pow, Int.cast_neg, Int.cast_one, map_neg, map_one] at h'
    exact neg_one_ne_one_of_odd hqodd hq1 h'.symm

/-- **The Solovay–Strassen bound**: modulo an odd composite `n`, at most half of the units are
Euler liars. -/
theorem two_mul_card_eulerLiars_le {n : ℕ} [NeZero n] (hodd : Odd n) (h1 : 1 < n)
    (hn : ¬ n.Prime) : 2 * Nat.card (eulerLiars n) ≤ n.totient := by
  rw [← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
  exact Subgroup.two_mul_card_le_of_ne_top (eulerLiars_ne_top hodd h1 hn)

end ZMod

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/NumberTheory/` next to `FermatPsp`)

public import Complexity.Foundations.NumberTheory.Primality.Witness
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic

/-!
# Strong liars and the Miller–Rabin bound

Write `n - 1 = 2 ^ s * t` with `t` odd. The Miller–Rabin test [Rabin][Rabin1980] declares an odd
`n > 1` composite when a random base `a` has `a ^ t ≠ 1` and `a ^ (2 ^ i * t) ≠ -1` for every
`i < s` modulo `n`. The bases that pass are the **strong liars**. Modulo a prime every nonzero
residue is a strong liar, because the only square roots of `1` are `±1`. Modulo an odd composite
`n`, the strong liars lie in a proper subgroup of `(ZMod n)ˣ`: for the largest `j < s` such that
some unit has `b ^ (2 ^ j * t) = -1`, the units whose `2 ^ j * t`-th power is `±1`. Hence at most
half of the units are strong liars. The sharper bound `φ(n) / 4` of Rabin and Monier is not
formalized here.

## Main definitions

* `ZMod.IsStrongLiar n a`: `a` passes the Miller–Rabin test modulo `n`.

## Main results

* `ZMod.isStrongLiar_of_prime`: modulo a prime, every nonzero residue is a strong liar.
* `ZMod.IsStrongLiar.isUnit`: for `n > 1`, a strong liar is a unit.
* `ZMod.exists_subgroup_ne_top_isStrongLiar`: modulo an odd composite, the strong liars lie in a
  proper subgroup of the units.
* `ZMod.two_mul_card_isStrongLiar_le`: modulo an odd composite `n`, twice the number of strong
  liars is at most `φ(n)`.

## References

* [M. O. Rabin, *Probabilistic algorithm for testing primality*][Rabin1980]
* [R. Motwani, P. Raghavan, *Randomized Algorithms*][MotwaniRaghavan95]
-/

public section

namespace ZMod

/-- `a` is a **strong liar** for `n`: writing `n - 1 = 2 ^ s * t` with `t` odd, `a ^ t = 1` or
`a ^ (2 ^ i * t) = -1` for some `i < s`. -/
def IsStrongLiar (n : ℕ) (a : ZMod n) : Prop :=
  a ^ ordCompl[2] (n - 1) = 1 ∨
    ∃ i < (n - 1).factorization 2, a ^ (2 ^ i * ordCompl[2] (n - 1)) = -1

theorem isStrongLiar_iff {n : ℕ} {a : ZMod n} :
    IsStrongLiar n a ↔ a ^ ordCompl[2] (n - 1) = 1 ∨
      ∃ i < (n - 1).factorization 2, a ^ (2 ^ i * ordCompl[2] (n - 1)) = -1 :=
  Iff.rfl

instance (n : ℕ) : DecidablePred (IsStrongLiar n) := fun _ =>
  decidable_of_iff' _ isStrongLiar_iff

/-- For `n > 1`, a strong liar is a unit. -/
theorem IsStrongLiar.isUnit {n : ℕ} (h1 : 1 < n) {a : ZMod n} (h : IsStrongLiar n a) :
    IsUnit a := by
  have ht : ordCompl[2] (n - 1) ≠ 0 := (Nat.ordCompl_pos 2 (by omega)).ne'
  rcases h with h | ⟨i, _, h⟩
  · exact IsUnit.of_pow_eq_one h ht
  · exact (isUnit_pow_iff (by positivity)).1 (h ▸ isUnit_one.neg)

/-- **Strong liars modulo a prime**: modulo a prime, every nonzero residue is a strong liar. Going
down from `a ^ (p - 1) = 1` by square roots, each is `1` or `-1`. -/
theorem isStrongLiar_of_prime {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    IsStrongLiar p a := by
  have key : ∀ j ≤ (p - 1).factorization 2,
      a ^ (2 ^ j * ordCompl[2] (p - 1)) = 1 → IsStrongLiar p a := by
    intro j
    induction j with
    | zero => intro _ h; left; simpa using h
    | succ j ih =>
      intro hj h
      have hsq : a ^ (2 ^ j * ordCompl[2] (p - 1)) * a ^ (2 ^ j * ordCompl[2] (p - 1)) = 1 := by
        rw [← pow_add, ← h]
        ring_nf
      rcases mul_self_eq_one_iff.1 hsq with h1 | h1
      · exact ih (by omega) h1
      · exact Or.inr ⟨j, by omega, h1⟩
  apply key _ le_rfl
  rw [Nat.ordProj_mul_ordCompl_eq_self]
  exact ZMod.pow_card_sub_one_eq_one ha

/-- The units whose `m`-th power is `1` or `-1`. -/
private def powEqOneOrNegOne (n m : ℕ) : Subgroup (ZMod n)ˣ where
  carrier := {a | a ^ m = 1 ∨ a ^ m = -1}
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb) <;> simp [mul_pow, ha, hb]
  one_mem' := by simp
  inv_mem' := by
    rintro a (ha | ha) <;> simp [inv_pow, ha]

/-- **Strong liars of a composite**: modulo an odd composite `n`, the strong liars lie in a proper
subgroup of the units. With `n - 1 = 2 ^ s * t`, take the largest `j < s` such that some unit `b`
has `b ^ (2 ^ j * t) = -1` (`j = 0` works with `b = -1`), and the subgroup of units whose
`2 ^ j * t`-th power is `±1`. It contains every strong liar. If `p ^ 2 ∣ n` for an odd prime `p`,
the unit `1 + n / p` is outside it. Otherwise `n = p q` with `p` an odd prime coprime to `q > 1`,
and the unit that agrees with `b` modulo `p` and is `1` modulo `q` is outside it. -/
theorem exists_subgroup_ne_top_isStrongLiar {n : ℕ} [NeZero n] (hodd : Odd n) (h1 : 1 < n)
    (hn : ¬ n.Prime) :
    ∃ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ ∧ ∀ a : (ZMod n)ˣ, IsStrongLiar n a → a ∈ H := by
  classical
  have hst : 2 ^ (n - 1).factorization 2 * ordCompl[2] (n - 1) = n - 1 :=
    Nat.ordProj_mul_ordCompl_eq_self (n - 1) 2
  have htodd : ¬ 2 ∣ ordCompl[2] (n - 1) := Nat.not_dvd_ordCompl Nat.prime_two (by omega)
  have hs0 : 0 < (n - 1).factorization 2 := by
    refine Nat.Prime.factorization_pos_of_dvd Nat.prime_two (by omega) ?_
    obtain ⟨k, rfl⟩ := hodd
    exact ⟨k, by omega⟩
  set s := (n - 1).factorization 2 with hs
  set t := ordCompl[2] (n - 1) with ht
  let S := (Finset.range s).filter fun i => ∃ b : (ZMod n)ˣ, b ^ (2 ^ i * t) = -1
  have h0S : 0 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    refine ⟨hs0, -1, ?_⟩
    rw [pow_zero, one_mul]
    exact Odd.neg_one_pow (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 htodd))
  set j := S.max' ⟨0, h0S⟩
  have hjS : j ∈ S := S.max'_mem _
  have hjmax : ∀ i ∈ S, i ≤ j := fun i hi => S.le_max' i hi
  obtain ⟨hjs, b, hb⟩ : j < s ∧ ∃ b : (ZMod n)ˣ, b ^ (2 ^ j * t) = -1 := by
    simpa [S] using hjS
  refine ⟨powEqOneOrNegOne n (2 ^ j * t), ?_, fun a ha => ?_⟩
  · have hm : 2 ^ j * t ∣ n - 1 := by
      rw [← hst]
      exact Nat.mul_dvd_mul_right (Nat.pow_dvd_pow 2 hjs.le) t
    intro htop
    rcases Nat.exists_sq_dvd_or_eq_mul_coprime hodd h1 hn with ⟨p, hp, hp2, hpn⟩ |
      ⟨p, q, rfl, hp, hp2, hpq, hqodd, hq1⟩
    · obtain ⟨c, hc1, hcn⟩ := exists_unit_pow_of_sq_dvd hp hp2 (NeZero.ne n) hpn
      have hc : c ∈ powEqOneOrNegOne n (2 ^ j * t) := htop ▸ Subgroup.mem_top c
      rcases hc with hc | hc
      · have hpm := (hc1 _ (by simpa using congrArg Units.val hc)).trans hm
        have hpn' : p ∣ n := (Dvd.intro_left _ rfl : p ∣ p ^ 2).trans hpn
        have : p ∣ 1 := by
          have := Nat.dvd_sub hpn' hpm
          rwa [show n - (n - 1) = 1 by omega] at this
        exact hp.one_lt.ne' (Nat.dvd_one.1 this)
      · exact hcn _ (by simpa using congrArg Units.val hc)
    · have : NeZero q := ⟨by omega⟩
      obtain ⟨c, hcp, hcq⟩ := exists_unit_castHom_eq hpq
        (Units.map (castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom b) 1
      have hc : c ∈ powEqOneOrNegOne (p * q) (2 ^ j * t) := htop ▸ Subgroup.mem_top c
      rcases hc with hc | hc
      · have h' := congrArg (fun u : (ZMod (p * q))ˣ =>
          castHom (dvd_mul_right p q) (ZMod p) (u : ZMod (p * q))) hc
        have hb' := congrArg (fun u : (ZMod (p * q))ˣ =>
          castHom (dvd_mul_right p q) (ZMod p) (u : ZMod (p * q))) hb
        simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one, Units.val_neg,
          map_neg] at h' hb'
        rw [hcp, Units.coe_map] at h'
        simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] at h'
        exact neg_one_ne_one_of_odd (hp.odd_of_ne_two hp2) hp.one_lt (hb'.symm.trans h')
      · have h' := congrArg (fun u : (ZMod (p * q))ˣ =>
          castHom (dvd_mul_left q p) (ZMod q) (u : ZMod (p * q))) hc
        simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one, Units.val_neg,
          map_neg, hcq, one_pow] at h'
        exact neg_one_ne_one_of_odd hqodd hq1 h'.symm
  · rcases ha with ha | ⟨i, his, hi⟩
    · left
      have : a ^ t = 1 := Units.ext (by simpa using ha)
      rw [mul_comm, pow_mul, this, one_pow]
    · have hi' : a ^ (2 ^ i * t) = -1 := Units.ext (by simpa using hi)
      have hij : i ≤ j := hjmax i (by
        simp only [S, Finset.mem_filter, Finset.mem_range]
        exact ⟨his, a, hi'⟩)
      rcases hij.lt_or_eq with hlt | rfl
      · left
        obtain ⟨d, hd⟩ : ∃ d, j = i + 1 + d := ⟨j - (i + 1), by omega⟩
        rw [hd, show 2 ^ (i + 1 + d) * t = (2 ^ i * t) * (2 * 2 ^ d) by ring, pow_mul, hi',
          pow_mul]
        simp
      · right
        exact hi'

/-- **The Miller–Rabin bound**: modulo an odd composite `n`, at most half of the units are strong
liars. -/
theorem two_mul_card_isStrongLiar_le {n : ℕ} [NeZero n] (hodd : Odd n) (h1 : 1 < n)
    (hn : ¬ n.Prime) : 2 * (Finset.univ.filter (IsStrongLiar n)).card ≤ n.totient := by
  classical
  obtain ⟨H, hH, hsub⟩ := exists_subgroup_ne_top_isStrongLiar hodd h1 hn
  let f : {a // IsStrongLiar n a} → H := fun a =>
    ⟨(a.2.isUnit h1).unit, hsub _ (by simpa using a.2)⟩
  have hf : Function.Injective f := fun a b h => Subtype.ext (by
    have := congrArg (fun x : H => ((x : (ZMod n)ˣ) : ZMod n)) h
    simpa [f] using this)
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hle
  have := Subgroup.two_mul_card_le_of_ne_top hH
  rw [Nat.card_eq_fintype_card (α := (ZMod n)ˣ), ZMod.card_units_eq_totient] at this
  have hle' : (Finset.univ.filter (IsStrongLiar n)).card ≤ Nat.card H := by
    convert hle using 2
  omega

end ZMod

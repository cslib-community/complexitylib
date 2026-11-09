/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/NumberTheory/` next to `FermatPsp`)

public import CslibFrontier.Foundations.NumberTheory.Primality.StrongLiars
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# The Rabin–Monier bound

Modulo an odd composite `n ≠ 9`, at most a quarter of the units are strong liars for the
Miller–Rabin test (`ZMod.IsStrongLiar`). Rabin [Rabin][Rabin1980] and Monier [Monier][Monier1980]
proved this independently. Crandall and Pomerance [Crandall and Pomerance][CrandallPomerance2005]
state it as Theorem 3.5.4 for odd composite `n > 9`; this locator comes from secondary sources and
has not been checked against the book. The modulus `9` is a genuine exception: its strong liars are
`±1`, two of the `φ(9) = 6` units.

The proof here is group-theoretic and avoids Monier's exact count. By
`ZMod.exists_pow_eq_neg_one_forall_isStrongLiar`, there is an `m` with `2 m ∣ n - 1` and a unit `b`
with `b ^ m = -1` such that every strong liar lies in `K = {a : a ^ m = ±1}`. It remains to show
that `K` has index at least `4`.

* If `n = p ^ e` with `e ≥ 2`, the units with `a ^ (2 m) = 1` contain `K` and have order coprime
  to `p`: an element of order `p` would give `p ∣ 2 m ∣ n - 1`. Since `p ^ (e - 1) ∣ φ(n)`, the
  index is at least `p ^ (e - 1)`, which is at least `4` unless `n = 9`.
* Otherwise `n = A B` with `A, B > 1` odd and coprime. The units `J` with `a ^ m ≡ ±1` modulo `A`
  and modulo `B` separately contain `K`. The unit that is `b` modulo `A` and `1` modulo `B` is in
  `J` but not in `K`. The subgroup `J` is proper because one of the factors has a unit whose
  `m`-th power is not `±1`: the unit `1 + A / p` if `p ^ 2 ∣ A`; the unit that is `b` modulo one
  factor and `1` modulo another if `B` splits further; and, for `n = p q` with distinct primes,
  a generator modulo `p` or `q`, since `p - 1 ∣ 2 m` and `q - 1 ∣ 2 m` would force `p = q`.

## Main results

* `ZMod.four_mul_card_powEqOneOrNegOne_le`: modulo an odd composite `n ≠ 9`, the subgroup
  `powEqOneOrNegOne n m` of the strong-liar exponent `m` has at most a quarter of the units.
* `ZMod.four_mul_card_isStrongLiar_le`: **the Rabin–Monier bound**: modulo an odd composite
  `n ≠ 9`, four times the number of strong liars is at most `φ(n)`.

## References

* [M. O. Rabin, *Probabilistic algorithm for testing primality*][Rabin1980]
* [L. Monier, *Evaluation and comparison of two efficient probabilistic primality testing
  algorithms*][Monier1980]
* [R. Crandall, C. Pomerance, *Prime Numbers: A Computational Perspective*][CrandallPomerance2005]
-/

public section

namespace ZMod

/-- A strict chain `K < J < G` of subgroups of a finite group gives `K` index at least `4`. -/
private theorem four_le_index {G : Type*} [Group G] [Finite G] {K J : Subgroup G} (hKJ : K ≤ J)
    (hJK : ¬ J ≤ K) (hJ : J ≠ ⊤) : 4 ≤ K.index := by
  have hmul := Subgroup.relIndex_mul_index hKJ
  have hJ2 := Subgroup.one_lt_index_of_ne_top hJ
  have hK0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hr1 : K.relIndex J ≠ 1 := fun h => hJK (Subgroup.relIndex_eq_one.1 h)
  have hr0 : K.relIndex J ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact hK0 hmul.symm
  rw [← hmul]
  nlinarith [Nat.two_le_iff _ |>.2 ⟨hr0, hr1⟩]

/-- A subgroup of index at least `4` has at most a quarter of the elements. -/
private theorem four_mul_card_le_of_four_le_index {G : Type*} [Group G] {K : Subgroup G}
    (h : 4 ≤ K.index) : 4 * Nat.card K ≤ Nat.card G := by
  rw [← K.card_mul_index, mul_comm 4]
  exact Nat.mul_le_mul_left _ h

private theorem unitsMap_neg_one {A n : ℕ} (h : A ∣ n) : unitsMap h (-1) = -1 :=
  Units.ext (by simp [unitsMap_def])

/-- The Chinese remainder theorem for units, through `unitsMap`. -/
private theorem exists_unitsMap_eq {A B : ℕ} (h : A.Coprime B) (u : (ZMod A)ˣ) (v : (ZMod B)ˣ) :
    ∃ c : (ZMod (A * B))ˣ, unitsMap (dvd_mul_right A B) c = u ∧
      unitsMap (dvd_mul_left B A) c = v := by
  obtain ⟨c, hcA, hcB⟩ := exists_unit_castHom_eq h u v
  exact ⟨c, Units.ext (by simpa [unitsMap_val] using hcA),
    Units.ext (by simpa [unitsMap_val] using hcB)⟩

private theorem units_neg_one_ne_one {A : ℕ} (hA : Odd A) (h1 : 1 < A) :
    (-1 : (ZMod A)ˣ) ≠ 1 := fun h =>
  neg_one_ne_one_of_odd hA h1 (by simpa using congrArg Units.val h)

/-- **The chain for a coprime splitting.** Let `n = A B` with `A, B > 1` odd and coprime, let
`b ^ m = -1` for a unit `b` modulo `n`, and suppose that some unit modulo `A` or modulo `B` has
`m`-th power different from `±1`. Then `powEqOneOrNegOne n m` has index at least `4`: it lies
strictly inside the subgroup of units whose `m`-th powers are `±1` modulo `A` and modulo `B`, which
is proper. -/
private theorem four_le_index_of_coprime {A B n m : ℕ} (hn : A * B = n) (hA : Odd A) (hB : Odd B)
    (hA1 : 1 < A) (hB1 : 1 < B) (hAB : A.Coprime B) {b : (ZMod n)ˣ} (hb : b ^ m = -1)
    (hw : (∃ w : (ZMod A)ˣ, w ∉ powEqOneOrNegOne A m) ∨
      ∃ w : (ZMod B)ˣ, w ∉ powEqOneOrNegOne B m) :
    4 ≤ (powEqOneOrNegOne n m).index := by
  subst hn
  have : NeZero (A * B) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  let J : Subgroup (ZMod (A * B))ˣ :=
    (powEqOneOrNegOne A m).comap (unitsMap (dvd_mul_right A B)) ⊓
      (powEqOneOrNegOne B m).comap (unitsMap (dvd_mul_left B A))
  have hJ : ∀ a, a ∈ J ↔ unitsMap (dvd_mul_right A B) a ∈ powEqOneOrNegOne A m ∧
      unitsMap (dvd_mul_left B A) a ∈ powEqOneOrNegOne B m := fun a => Iff.rfl
  refine four_le_index (J := J) (fun a ha => ?_) (fun hle => ?_) (fun htop => ?_)
  · rw [hJ, mem_powEqOneOrNegOne, mem_powEqOneOrNegOne, ← map_pow, ← map_pow]
    rcases mem_powEqOneOrNegOne.1 ha with ha | ha
    · rw [ha, map_one, map_one]
      exact ⟨Or.inl rfl, Or.inl rfl⟩
    · rw [ha, unitsMap_neg_one, unitsMap_neg_one]
      exact ⟨Or.inr rfl, Or.inr rfl⟩
  · obtain ⟨c, hcA, hcB⟩ := exists_unitsMap_eq hAB (unitsMap (dvd_mul_right A B) b) 1
    have hcJ : c ∈ J := by
      rw [hJ, mem_powEqOneOrNegOne, mem_powEqOneOrNegOne, hcA, hcB, ← map_pow, hb,
        unitsMap_neg_one, one_pow]
      exact ⟨Or.inr rfl, Or.inl rfl⟩
    rcases mem_powEqOneOrNegOne.1 (hle hcJ) with hc | hc
    · have h' := congrArg (unitsMap (dvd_mul_right A B)) hc
      rw [map_pow, hcA, ← map_pow, hb, unitsMap_neg_one, map_one] at h'
      exact units_neg_one_ne_one hA hA1 h'
    · have h' := congrArg (unitsMap (dvd_mul_left B A)) hc
      rw [map_pow, hcB, one_pow, unitsMap_neg_one] at h'
      exact units_neg_one_ne_one hB hB1 h'.symm
  · rcases hw with ⟨w, hw⟩ | ⟨w, hw⟩
    · obtain ⟨d, hdA, -⟩ := exists_unitsMap_eq hAB w 1
      have hd : d ∈ J := by rw [htop]; exact Subgroup.mem_top d
      exact hw (hdA ▸ ((hJ d).1 hd).1)
    · obtain ⟨d, -, hdB⟩ := exists_unitsMap_eq hAB 1 w
      have hd : d ∈ J := by rw [htop]; exact Subgroup.mem_top d
      exact hw (hdB ▸ ((hJ d).1 hd).2)

/-- **The witness for a square factor.** If `p ^ 2 ∣ A ∣ n` for an odd prime `p` and
`2 m ∣ n - 1`, the unit `1 + A / p` modulo `A` has `m`-th power different from `±1`. -/
private theorem exists_not_mem_of_sq_dvd {A n m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpA : p ^ 2 ∣ A) (hAn : A ∣ n) (h1 : 1 < n) (hm : 2 * m ∣ n - 1) :
    ∃ w : (ZMod A)ˣ, w ∉ powEqOneOrNegOne A m := by
  have hA0 : A ≠ 0 := by
    rintro rfl
    exact absurd (Nat.eq_zero_of_zero_dvd hAn) (by omega)
  obtain ⟨c, hc1, hcn⟩ := exists_unit_pow_of_sq_dvd hp hp2 hA0 hpA
  refine ⟨c, fun hc => ?_⟩
  rcases mem_powEqOneOrNegOne.1 hc with hc | hc
  · have hpm : p ∣ n - 1 :=
      (hc1 m (by simpa using congrArg Units.val hc)).trans ((Dvd.intro_left 2 rfl).trans hm)
    have hpn : p ∣ n := ((Dvd.intro_left _ rfl : p ∣ p ^ 2).trans hpA).trans hAn
    exact hp.not_dvd_one (Nat.sub_sub_self h1.le ▸ Nat.dvd_sub hpn hpm)
  · exact hcn m (by simpa using congrArg Units.val hc)

/-- If `p - 1` and `q - 1` both divide `p q - 1`, then `p = q`: `p q - 1 = q (p - 1) + (q - 1)`
gives `p - 1 ∣ q - 1`, and symmetrically. -/
private theorem eq_of_sub_one_dvd {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (h1 : p - 1 ∣ p * q - 1)
    (h2 : q - 1 ∣ p * q - 1) : p = q := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le' hp
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le' hq
  rw [Nat.add_sub_cancel] at h1 h2
  have he1 : (p + 1) * (q + 1) - 1 = p * (q + 1) + q := by
    rw [show (p + 1) * (q + 1) = p * (q + 1) + q + 1 by ring, Nat.add_sub_cancel]
  have he2 : (p + 1) * (q + 1) - 1 = q * (p + 1) + p := by
    rw [show (p + 1) * (q + 1) = q * (p + 1) + p + 1 by ring, Nat.add_sub_cancel]
  rw [he1] at h1
  rw [he2] at h2
  have hpq : p ∣ q := (Nat.dvd_add_right (dvd_mul_right p (q + 1))).1 h1
  have hqp : q ∣ p := (Nat.dvd_add_right (dvd_mul_right q (p + 1))).1 h2
  rw [Nat.dvd_antisymm hpq hqp]

/-- **The Korselt witness.** For distinct primes `p` and `q` with `2 m ∣ p q - 1`, some unit
modulo `p` or modulo `q` has `m`-th power different from `±1`. Otherwise the cyclic groups
`(ZMod p)ˣ` and `(ZMod q)ˣ` have exponents `p - 1` and `q - 1` dividing `2 m`. -/
private theorem exists_not_mem_of_prime_mul_prime {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hm : 2 * m ∣ p * q - 1) :
    (∃ w : (ZMod p)ˣ, w ∉ powEqOneOrNegOne p m) ∨ ∃ w : (ZMod q)ˣ, w ∉ powEqOneOrNegOne q m := by
  by_contra! h
  have key : ∀ r : ℕ, r.Prime → (∀ w : (ZMod r)ˣ, w ∈ powEqOneOrNegOne r m) → r - 1 ∣ 2 * m := by
    intro r hr hall
    have : Fact r.Prime := ⟨hr⟩
    have hexp : Monoid.exponent (ZMod r)ˣ ∣ 2 * m := by
      refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun w => ?_
      rw [pow_mul']
      rcases mem_powEqOneOrNegOne.1 (hall w) with hw | hw <;> rw [hw] <;> simp
    rwa [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units] at hexp
  exact hpq (eq_of_sub_one_dvd hp.one_lt.le hq.one_lt.le ((key p hp h.1).trans hm)
    ((key q hq h.2).trans hm))

/-- **The witness for a further splitting.** If `B = C D` with `C, D > 1` odd and coprime, and some
unit `u` modulo `C` has `u ^ m = -1`, then the unit modulo `B` that is `u` modulo `C` and `1`
modulo `D` has `m`-th power different from `±1`. -/
private theorem exists_not_mem_of_eq_mul {B C D m : ℕ} (hB : C * D = B) (hC : Odd C) (hD : Odd D)
    (hC1 : 1 < C) (hD1 : 1 < D) (hCD : C.Coprime D) {u : (ZMod C)ˣ} (hu : u ^ m = -1) :
    ∃ w : (ZMod B)ˣ, w ∉ powEqOneOrNegOne B m := by
  subst hB
  obtain ⟨c, hcC, hcD⟩ := exists_unitsMap_eq hCD u 1
  refine ⟨c, fun hc => ?_⟩
  rcases mem_powEqOneOrNegOne.1 hc with hc | hc
  · have h' := congrArg (unitsMap (dvd_mul_right C D)) hc
    rw [map_pow, hcC, hu, map_one] at h'
    exact units_neg_one_ne_one hC hC1 h'
  · have h' := congrArg (unitsMap (dvd_mul_left D C)) hc
    rw [map_pow, hcD, one_pow, unitsMap_neg_one] at h'
    exact units_neg_one_ne_one hD hD1 h'.symm

/-- **The prime-power count.** If `p ^ e ∣ n` for a prime `p` and `e ≥ 1`, and `2 m ∣ n - 1`, the
units with `a ^ (2 m) = 1` have order coprime to `p`: an element of order `p` would give
`p ∣ 2 m ∣ n - 1`. Since `p ^ (e - 1) ∣ φ(n)`, their number times `p ^ (e - 1)` divides `φ(n)`. -/
private theorem card_ker_mul_pow_dvd_totient {n m p e : ℕ} [NeZero n] (hp : p.Prime) (he : 1 ≤ e)
    (hpe : p ^ e ∣ n) (h1 : 1 < n) (hm : 2 * m ∣ n - 1) :
    Nat.card (powMonoidHom (2 * m) : (ZMod n)ˣ →* (ZMod n)ˣ).ker * p ^ (e - 1) ∣ n.totient := by
  set T := (powMonoidHom (2 * m) : (ZMod n)ˣ →* (ZMod n)ˣ).ker
  have : Fact p.Prime := ⟨hp⟩
  have hpn : p ∣ n := (dvd_pow_self p (by omega)).trans hpe
  have hcop : (Nat.card T).Coprime (p ^ (e - 1)) := by
    refine Nat.Coprime.pow_right _ ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2
      fun hdvd => ?_)))
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hx2 : (x : (ZMod n)ˣ) ^ (2 * m) = 1 := x.2
    have hpm : p ∣ n - 1 := by
      rw [← hx, ← Subgroup.orderOf_coe]
      exact (orderOf_dvd_of_pow_eq_one hx2).trans hm
    have : p ∣ 1 := by
      have := Nat.dvd_sub hpn hpm
      rwa [show n - (n - 1) = 1 by omega] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  refine hcop.mul_dvd_of_dvd_of_dvd ?_ ?_
  · rw [← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card T
  · refine Dvd.dvd.trans ?_ (Nat.totient_dvd_of_dvd hpe)
    rw [Nat.totient_prime_pow hp (by omega)]
    exact dvd_mul_right _ _

/-- **The index bound behind the Rabin–Monier theorem.** Modulo an odd composite `n ≠ 9`, for
`m` with `2 m ∣ n - 1` and a unit `b` with `b ^ m = -1` (as provided by
`exists_pow_eq_neg_one_forall_isStrongLiar`), the subgroup `powEqOneOrNegOne n m` of units whose
`m`-th power is `±1` has at most a quarter of the units. -/
theorem four_mul_card_powEqOneOrNegOne_le {n m : ℕ} [NeZero n] (hodd : Odd n) (h1 : 1 < n)
    (hn : ¬ n.Prime) (h9 : n ≠ 9) (hm : 2 * m ∣ n - 1) {b : (ZMod n)ˣ} (hb : b ^ m = -1) :
    4 * Nat.card (powEqOneOrNegOne n m) ≤ n.totient := by
  rw [← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hp2 : p ≠ 2 := by
    intro h
    have : 2 ∣ n := h ▸ Nat.minFac_dvd n
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 this)
  set e := n.factorization p with hedef
  have he : 1 ≤ e := hp.factorization_pos_of_dvd (NeZero.ne n) (Nat.minFac_dvd n)
  set B := ordCompl[p] n with hBdef
  have hn_eq : p ^ e * B = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hpB : p.Coprime B := Nat.coprime_ordCompl hp (NeZero.ne n)
  have hB0 : B ≠ 0 := (Nat.ordCompl_pos p (NeZero.ne n)).ne'
  have hBodd : Odd B := Odd.of_dvd_nat hodd ⟨p ^ e, by rw [← hn_eq, mul_comm]⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  clear_value B e p
  rcases Nat.lt_or_ge 1 B with hB1 | hB1
  · -- `n = p ^ e B` with `B > 1`: the chain for a coprime splitting.
    refine four_mul_card_le_of_four_le_index (four_le_index_of_coprime hn_eq (hpodd.pow)
      hBodd (Nat.one_lt_pow (by omega) hp.one_lt) hB1 (Nat.Coprime.pow_left e hpB) hb ?_)
    rcases Nat.lt_or_ge e 2 with he2 | he2
    · have he1 : e = 1 := by omega
      set q := B.minFac with hqdef
      have hq : q.Prime := Nat.minFac_prime (by omega)
      have hqodd : Odd q := Odd.of_dvd_nat hBodd (Nat.minFac_dvd B)
      set f := B.factorization q with hfdef
      have hf : 1 ≤ f := hq.factorization_pos_of_dvd hB0 (Nat.minFac_dvd B)
      set D := ordCompl[q] B with hDdef
      have hB_eq : q ^ f * D = B := Nat.ordProj_mul_ordCompl_eq_self B q
      have hqD : q.Coprime D := Nat.coprime_ordCompl hq hB0
      have hDodd : Odd D := Odd.of_dvd_nat hBodd ⟨q ^ f, by rw [← hB_eq, mul_comm]⟩
      have hqf1 : 1 < q ^ f := Nat.one_lt_pow (by omega) hq.one_lt
      have hD0 : D ≠ 0 := (Nat.ordCompl_pos q hB0).ne'
      clear_value D f q
      rcases Nat.lt_or_ge 1 D with hD1 | hD1
      · -- `B = q ^ f D` with `D > 1`: split `B` further.
        right
        have hqfn : q ^ f ∣ n := ⟨D * p ^ e, by rw [← hn_eq, ← hB_eq]; ring⟩
        exact exists_not_mem_of_eq_mul hB_eq hqodd.pow hDodd hqf1 hD1
          (Nat.Coprime.pow_left f hqD) (u := unitsMap hqfn b) (by rw [← map_pow, hb,
            unitsMap_neg_one])
      · have hD : D = 1 := by
          omega
        rcases Nat.lt_or_ge f 2 with hf2 | hf2
        · -- `n = p q` with distinct primes `p`, `q`: the Korselt witness.
          have hf1 : f = 1 := by omega
          have hBq : B = q := by rw [← hB_eq, hD, hf1, pow_one, mul_one]
          rw [he1, pow_one] at hn_eq ⊢
          rw [hBq] at hn_eq hpB ⊢
          have hpq : p ≠ q := fun h => by
            rw [h, Nat.coprime_self] at hpB
            exact hq.one_lt.ne' hpB
          exact exists_not_mem_of_prime_mul_prime hp hq hpq (hn_eq ▸ hm)
        · -- `q ^ 2 ∣ B`.
          right
          exact exists_not_mem_of_sq_dvd hq
            (fun h => (Nat.not_even_iff_odd.2 hqodd) (h ▸ even_two))
            ((Nat.pow_dvd_pow q hf2).trans ⟨D, hB_eq.symm⟩) ⟨p ^ e, by rw [← hn_eq, mul_comm]⟩
            h1 hm
    · -- `p ^ 2 ∣ p ^ e`.
      left
      exact exists_not_mem_of_sq_dvd hp hp2 (Nat.pow_dvd_pow p he2) ⟨B, hn_eq.symm⟩ h1 hm
  · -- `n = p ^ e` is a prime power with `e ≥ 2`: the prime-power count.
    have hB : B = 1 := by omega
    rw [hB, mul_one] at hn_eq
    have he2 : 2 ≤ e := by
      by_contra! h
      have he1 : e = 1 := by omega
      rw [he1, pow_one] at hn_eq
      exact hn (hn_eq ▸ hp)
    have hp4 : 4 ≤ p ^ (e - 1) := by
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      rcases Nat.lt_or_ge e 3 with he3 | he3
      · have he2' : e = 2 := by omega
        rw [he2', show 2 - 1 = 1 from rfl, pow_one]
        by_contra! h
        have : p = 3 := by omega
        exact h9 (by rw [← hn_eq, he2', this]; rfl)
      · calc 4 ≤ 3 ^ 2 := by norm_num
          _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
          _ ≤ p ^ (e - 1) := Nat.pow_le_pow_right hp.pos (by omega)
    have hT : powEqOneOrNegOne n m ≤ (powMonoidHom (2 * m) : (ZMod n)ˣ →* (ZMod n)ˣ).ker :=
      fun a ha => by
        change a ^ (2 * m) = 1
        rw [pow_mul']
        rcases mem_powEqOneOrNegOne.1 ha with ha | ha <;> rw [ha] <;> simp
    have hdvd := card_ker_mul_pow_dvd_totient hp he (hn_eq ▸ dvd_rfl) h1 hm
    have hpos : 0 < n.totient := Nat.totient_pos.2 (by omega)
    have hle := Nat.le_of_dvd hpos hdvd
    rw [Nat.card_eq_fintype_card (α := (ZMod n)ˣ), ZMod.card_units_eq_totient]
    calc 4 * Nat.card (powEqOneOrNegOne n m)
        ≤ p ^ (e - 1) * Nat.card (powMonoidHom (2 * m) : (ZMod n)ˣ →* (ZMod n)ˣ).ker :=
          Nat.mul_le_mul hp4 (Subgroup.card_le_of_le hT)
      _ ≤ n.totient := by rw [mul_comm]; exact hle

/-- **The Rabin–Monier bound** [Rabin][Rabin1980] [Monier][Monier1980]: modulo an odd composite
`n ≠ 9`, at most a quarter of the units are strong liars. For `n = 9` the strong liars are `±1`,
and `4 · 2 > φ(9) = 6`. -/
theorem four_mul_card_isStrongLiar_le {n : ℕ} [NeZero n] (hodd : Odd n) (h1 : 1 < n)
    (hn : ¬ n.Prime) (h9 : n ≠ 9) :
    4 * (Finset.univ.filter (IsStrongLiar n)).card ≤ n.totient := by
  obtain ⟨m, hm, ⟨b, hb⟩, hliar⟩ := exists_pow_eq_neg_one_forall_isStrongLiar hodd h1
  have hle := card_isStrongLiar_le_card h1 hliar
  have := four_mul_card_powEqOneOrNegOne_le hodd h1 hn h9 hm hb
  omega

end ZMod

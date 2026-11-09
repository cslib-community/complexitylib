/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/Polynomial/Roots.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Foundations.Data.ZMod.Multiples
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Pow

/-!
# Root counts of polynomials over `ZMod n`

Over a field, a nonzero polynomial has at most `natDegree` roots (`Polynomial.card_roots'`). Over
`ZMod n` with composite `n` it can have many more: `(n / p) * X` vanishes on every multiple of a
prime `p ∣ n`. This file proves the general bound: a nonzero `f : (ZMod n)[X]` has at most
`f.natDegree * (n / n.minFac)` roots. The proof writes an integer lift of `f` as `p ^ j * G` for a
prime `p ∣ n` such that `G` is nonzero modulo `p`, and counts the residues of `ZMod n` above the at
most `f.natDegree` roots of `G` in `ZMod p`.

## Main results

* `ZMod.card_filter_castHom_eq`: every fibre of the reduction `ZMod n → ZMod d`, for `d ∣ n`, has
  `n / d` elements.
* `ZMod.card_filter_eval_eq_zero_le`: the root bound `f.natDegree * (n / n.minFac)`.
* `Nat.minFac_mul_pow`: for primes `p < q` and `ζ ≠ 0`, the smallest prime factor of `(p * q) ^ ζ`
  is `p`, which evaluates the bound for the moduli of Damgård–Jurik encryption. Its Mathlib
  destination is `Mathlib/Data/Nat/Prime/Pow.lean`, beside `Nat.pow_minFac`.
-/

public section

open Finset Polynomial

namespace ZMod

/-- Reducing `ZMod n` modulo a divisor `d` has fibres of size exactly `n / d`. The fibre over `0`
is `ZMod.card_filter_dvd_val`; the others are its translates. -/
theorem card_filter_castHom_eq {n d : ℕ} [NeZero n] (hd : d ∣ n) (r : ZMod d) :
    #{x : ZMod n | castHom hd (ZMod d) x = r} = n / d := by
  have : NeZero d := ⟨fun h0 => NeZero.ne n (Nat.eq_zero_of_zero_dvd (h0 ▸ hd))⟩
  rw [← card_filter_dvd_val hd]
  refine card_equiv (Equiv.addRight (-(r.val : ZMod n))) fun x => ?_
  have key : ∀ y : ZMod n, d ∣ y.val ↔ castHom hd (ZMod d) y = 0 := fun y => by
    rw [castHom_apply, cast_eq_val, natCast_eq_zero_iff]
  simp only [mem_filter, mem_univ, true_and, Equiv.coe_addRight]
  rw [key, map_add, map_neg, map_natCast, natCast_zmod_val, add_neg_eq_zero]

/-- An integer not divisible by `n ≠ 0` is not divisible by some prime power dividing `n`. -/
private theorem exists_prime_pow_dvd_not_dvd {n : ℕ} {c : ℤ} (hn0 : n ≠ 0) (hc : ¬(n : ℤ) ∣ c) :
    ∃ p e : ℕ, p.Prime ∧ p ^ e ∣ n ∧ ¬(p : ℤ) ^ e ∣ c := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (dvd_zero _)
  have hm : ¬n ∣ c.natAbs := fun h => hc (Int.natCast_dvd.mpr h)
  rw [← Nat.factorization_le_iff_dvd hn0 (Int.natAbs_ne_zero.mpr hc0), Finsupp.le_def] at hm
  push Not at hm
  obtain ⟨p, hp⟩ := hm
  have hpp : p.Prime := by
    by_contra hnp
    rw [Nat.factorization_eq_zero_of_not_prime n hnp] at hp
    omega
  refine ⟨p, n.factorization p, hpp, Nat.ordProj_dvd n p, fun h => ?_⟩
  have h' : p ^ n.factorization p ∣ c.natAbs := by
    rw [← Int.natCast_dvd]
    exact_mod_cast h
  rw [hpp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr hc0)] at h'
  omega

/-- **Root bound over `ZMod n`.** A nonzero polynomial `f` over `ZMod n` has at most
`f.natDegree * (n / n.minFac)` roots. For prime `n` this is the usual bound `f.natDegree`. -/
theorem card_filter_eval_eq_zero_le {n : ℕ} [NeZero n] {f : (ZMod n)[X]} (hf : f ≠ 0) :
    #{x : ZMod n | f.eval x = 0} ≤ f.natDegree * (n / n.minFac) := by
  classical
  obtain ⟨F, hFmap, hFdeg⟩ : ∃ F : ℤ[X], F.map (Int.castRingHom (ZMod n)) = f ∧
      F.degree = f.degree :=
    exists_degree_eq_of_mem_lifts ((lifts_iff_coeff_lifts f).2 fun k =>
      ZMod.intCast_surjective (f.coeff k))
  have hFnat : F.natDegree = f.natDegree := natDegree_eq_of_degree_eq hFdeg
  obtain ⟨i, hi⟩ : ∃ i, ¬(n : ℤ) ∣ F.coeff i := by
    by_contra h
    push Not at h
    apply hf
    rw [← hFmap]
    ext i
    simp [coeff_map, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (h i)]
  obtain ⟨p, e, hp, hpe, hnot⟩ := exists_prime_pow_dvd_not_dvd (NeZero.ne n) hi
  have : Fact p.Prime := ⟨hp⟩
  -- The largest power `p ^ (k - 1)` with `C (p ^ (k - 1)) ∣ F` has `k ≤ e`.
  have hex : ∃ k, ¬C ((p : ℤ) ^ k) ∣ F :=
    ⟨e, fun h => hnot ((C_dvd_iff_dvd_coeff _ _).1 h i)⟩
  set k := Nat.find hex with hk
  have hk0 : k ≠ 0 := by
    intro h0
    have h := Nat.find_spec hex
    rw [← hk, h0, pow_zero, map_one] at h
    exact h (one_dvd _)
  have hke : k ≤ e := Nat.find_min' hex fun h => hnot ((C_dvd_iff_dvd_coeff _ _).1 h i)
  have hdvd : C ((p : ℤ) ^ (k - 1)) ∣ F := by
    simpa using Nat.find_min hex (show k - 1 < Nat.find hex by omega)
  obtain ⟨G, hG⟩ := hdvd
  have hpow0 : (p : ℤ) ^ (k - 1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hGmap : G.map (Int.castRingHom (ZMod p)) ≠ 0 := by
    intro h0
    have hpG : C (p : ℤ) ∣ G := by
      rw [C_dvd_iff_dvd_coeff]
      intro j
      have h := congrArg (fun g => g.coeff j) h0
      simp only [coeff_map, eq_intCast, coeff_zero] at h
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h
    apply Nat.find_spec hex
    rw [← hk, hG, show k = (k - 1) + 1 by omega, pow_succ, C_mul]
    exact mul_dvd_mul_left _ hpG
  have hGdeg : (G.map (Int.castRingHom (ZMod p))).natDegree ≤ f.natDegree := by
    rw [← hFnat, hG, natDegree_C_mul hpow0]
    exact natDegree_map_le
  have hpn : p ∣ n := dvd_trans (dvd_pow_self p (by omega)) hpe
  -- Every root of `f` lies above a root of `G` modulo `p`.
  have hfib : ∀ x : ZMod n, f.eval x = 0 →
      ZMod.castHom hpn (ZMod p) x ∈ (G.map (Int.castRingHom (ZMod p))).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hGmap, IsRoot, ZMod.castHom_apply, ZMod.cast_eq_val,
      ← Int.cast_natCast, eval_intCast_map, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hx' : (n : ℤ) ∣ F.eval (x.val : ℤ) := by
      have h := congrArg (fun g => g.eval ((x.val : ℤ) : ZMod n)) hFmap
      simp only [eval_intCast_map, eq_intCast] at h
      have hxc : ((x.val : ℤ) : ZMod n) = x := by
        rw [Int.cast_natCast, ZMod.natCast_zmod_val]
      rw [hxc, hx] at h
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast h
    have h1 : (p : ℤ) ^ (k - 1) * p ∣ (p : ℤ) ^ (k - 1) * G.eval (x.val : ℤ) := by
      rw [← pow_succ, ← eval_C (a := (p : ℤ) ^ (k - 1)) (x := (x.val : ℤ)), ← eval_mul, ← hG]
      refine dvd_trans (pow_dvd_pow (p : ℤ) (show k - 1 + 1 ≤ e by omega)) (dvd_trans ?_ hx')
      exact_mod_cast hpe
    exact (mul_dvd_mul_iff_left hpow0).1 h1
  set g := ZMod.castHom hpn (ZMod p)
  set s : Finset (ZMod n) := {x : ZMod n | f.eval x = 0}
  have h1 : s.card ≤ n / p * (s.image g).card :=
    Finset.card_le_mul_card_image s _ fun a _ =>
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ s))).trans
        (card_filter_castHom_eq hpn a).le
  have h2 : (s.image g).card ≤ f.natDegree := by
    refine (Finset.card_le_card ?_).trans ((Multiset.toFinset_card_le _).trans
      ((card_roots' _).trans hGdeg))
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    exact hfib x (Finset.mem_filter.mp hx).2
  have h3 : n / p ≤ n / n.minFac :=
    Nat.div_le_div_left (Nat.minFac_le_of_dvd hp.two_le hpn) (Nat.minFac_pos n)
  calc s.card ≤ n / p * f.natDegree := h1.trans (Nat.mul_le_mul_left _ h2)
    _ ≤ f.natDegree * (n / n.minFac) := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ h3

end ZMod

/-- For primes `p < q` and `ζ ≠ 0`, the smallest prime factor of `(p * q) ^ ζ` is `p`. -/
theorem Nat.minFac_mul_pow {p q ζ : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hζ : ζ ≠ 0) :
    ((p * q) ^ ζ).minFac = p := by
  rw [Nat.pow_minFac hζ]
  have hne : p * q ≠ 1 := (one_lt_mul_of_lt_of_le hp.one_lt hq.one_lt.le).ne'
  have hmin := Nat.minFac_prime hne
  rcases (Nat.Prime.dvd_mul hmin).1 (Nat.minFac_dvd _) with h | h
  · exact (Nat.prime_dvd_prime_iff_eq hmin hp).1 h
  · have hle : (p * q).minFac ≤ p := Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p q)
    have := (Nat.prime_dvd_prime_iff_eq hmin hq).1 h
    omega

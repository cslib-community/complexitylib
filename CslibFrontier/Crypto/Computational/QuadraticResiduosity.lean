/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Game
public import Mathlib.Algebra.Group.Subgroup.Even
public import Mathlib.Data.ZMod.Units
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PPT
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Quadratic residuosity, Jacobi symbols, and Blum integers

Quadratic residues in `(ZMod (p * q))ˣ` (building on Mathlib's `IsSquare` and `Subgroup.square`),
the composite Jacobi symbol `J_N(x) = (x / p)(x / q)` for distinct odd primes `p ≠ q`, the sign
sets `J_N^{+1}`, `J_N^{-1}`, and `QNR_N^{+1}`, Blum integers (`p ≡ q ≡ 3 (mod 4)`), and the
computational quadratic residuosity assumption.

## Main definitions

* `Cslib.Crypto.jacobiSymbol`: the composite Jacobi symbol on `(ZMod (p * q))ˣ`.
* `Cslib.Crypto.jacobiPosSet`, `Cslib.Crypto.jacobiNegSet`, `Cslib.Crypto.quadResidueSet`,
  `Cslib.Crypto.positiveNonresidues`: the Jacobi sign sets, quadratic residues, and
  quadratic nonresidues with Jacobi symbol `+1`.
* `Cslib.Crypto.IsBlumPrime`, `Cslib.Crypto.IsBlumModulus`, `Cslib.Crypto.blumSqrt`: Blum primes,
  Blum moduli, and principal square-root extraction.
* `Cslib.Crypto.ModulusDesc`, `Cslib.Crypto.qrRealGame`, `Cslib.Crypto.qrIdealGame`,
  `Cslib.Crypto.QuadraticResiduosityHard`: the computational quadratic residuosity experiment and
  assumption.

## Main results

* `Cslib.Crypto.jacobiSymbol_eq_jacobiSym`: `jacobiSymbol p q x` agrees with Mathlib's
  `jacobiSym (x.val.val : ℤ) (p * q)`.
* `Cslib.Crypto.jacobiPosSet_eq_disjoint_union`: `J_N^{+1} = QR_N ⊔ QNR_N^{+1}`.
* `Cslib.Crypto.card_quadResidueSet_eq_card_positiveNonresidues`: `|QR_N| = |QNR_N^{+1}|` for
  distinct odd primes `p ≠ q`.
* `Cslib.Crypto.neg_one_mem_positiveNonresidues`: `-1 ∈ QNR_N^{+1}` for any Blum modulus.
* `Cslib.Crypto.blumSqrt_sq`, `Cslib.Crypto.sq_bijOn_quadResidueSet`: squaring is a bijection
  on `QR_N` for any Blum modulus, with inverse `blumSqrt p q`.

## Implementation notes

Quadratic residues and their subgroup in a commutative group use Mathlib's `IsSquare` and
`Subgroup.square` (`Subgroup.mem_square`). The computational games `qrRealGame` and `qrIdealGame`
and assumption `QuadraticResiduosityHard` are parameterized by an arbitrary generator family
`setup : ℕ → PMF ModulusDesc` over pairs of distinct odd primes `(p, q)` (efficient sampling of
`(p, q)` and bit-length bounds in `n` are not bundled in `ModulusDesc`), and quantify over
uniform native strict-PPT distinguishers (`IsPPTOn`) taking `(1^n, (N, y))` with binary `encNat`
encodings.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020],
  Section 15.4 (Sections 15.4.1–15.4.3, Proposition 15.23 and Definition 15.27: quadratic
  residues modulo a prime and a composite, and the quadratic residuosity assumption).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-! ### Composite Jacobi symbol and sign sets -/

/-- The composite Jacobi symbol `J_{p*q}(x) = (x / p) * (x / q)` for units modulo `p * q`. -/
def jacobiSymbol (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (x : (ZMod (p * q))ˣ) : ℤ :=
  legendreSym p (x.val.val : ℤ) * legendreSym q (x.val.val : ℤ)

private instance neZero_mul_of_prime (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] :
    NeZero (p * q) :=
  ⟨Nat.mul_ne_zero hp.out.ne_zero hq.out.ne_zero⟩

/-- `jacobiSymbol p q x` agrees with Mathlib's Jacobi symbol `jacobiSym (x.val.val : ℤ) (p * q)`. -/
theorem jacobiSymbol_eq_jacobiSym (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (x : (ZMod (p * q))ˣ) :
    jacobiSymbol p q x = jacobiSym (x.val.val : ℤ) (p * q) := by
  rw [jacobiSymbol, jacobiSym.legendreSym.to_jacobiSym, jacobiSym.legendreSym.to_jacobiSym,
    ← jacobiSym.mul_right' _ (Fact.out : p.Prime).ne_zero (Fact.out : q.Prime).ne_zero]

/-- For primes `p, q`, `jacobiSymbol p q x` takes values in `{1, -1}`. -/
theorem jacobiSymbol_cases (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (x : (ZMod (p * q))ˣ) :
    jacobiSymbol p q x = 1 ∨ jacobiSymbol p q x = -1 := by
  rw [jacobiSymbol_eq_jacobiSym]
  exact jacobiSym.eq_one_or_neg_one
    ((Int.gcd_natCast_natCast _ _).trans (ZMod.val_coe_unit_coprime x))

/-- Every quadratic residue modulo `p * q` has Jacobi symbol `1`. -/
theorem jacobiSymbol_eq_one_of_isSquare (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    {x : (ZMod (p * q))ˣ} (hx : IsSquare x) :
    jacobiSymbol p q x = 1 := by
  rcases hx with ⟨r, rfl⟩
  rw [jacobiSymbol_eq_jacobiSym, Units.val_mul, ZMod.val_mul]
  push_cast
  rw [← Nat.cast_mul p q, ← jacobiSym.mod_left, ← sq]
  exact jacobiSym.sq_one'
    ((Int.gcd_natCast_natCast _ _).trans (ZMod.val_coe_unit_coprime r))

/-- Units modulo `p * q` with Jacobi symbol `+1`. -/
def jacobiPosSet (p q : ℕ) [Fact p.Prime] [Fact q.Prime] : Finset (ZMod (p * q))ˣ :=
  Finset.univ.filter fun x => jacobiSymbol p q x = 1

/-- Units modulo `p * q` with Jacobi symbol `-1`. -/
def jacobiNegSet (p q : ℕ) [Fact p.Prime] [Fact q.Prime] : Finset (ZMod (p * q))ˣ :=
  Finset.univ.filter fun x => jacobiSymbol p q x = -1

open Classical in
/-- Quadratic residues in `(ZMod (p * q))ˣ`. -/
def quadResidueSet (p q : ℕ) [NeZero (p * q)] : Finset (ZMod (p * q))ˣ :=
  Finset.univ.filter fun x => IsSquare x

/-- Membership in `quadResidueSet p q` is equivalent to membership in `Subgroup.square`. -/
theorem mem_quadResidueSet_iff (p q : ℕ) [NeZero (p * q)] (x : (ZMod (p * q))ˣ) :
    x ∈ quadResidueSet p q ↔ x ∈ Subgroup.square (ZMod (p * q))ˣ := by
  simp [quadResidueSet, Subgroup.mem_square]

open Classical in
/-- Quadratic nonresidues in `(ZMod (p * q))ˣ` with Jacobi symbol `+1` (`QNR_N^{+1}`). -/
def positiveNonresidues (p q : ℕ) [Fact p.Prime] [Fact q.Prime] : Finset (ZMod (p * q))ˣ :=
  Finset.univ.filter fun x => ¬ IsSquare x ∧ jacobiSymbol p q x = 1

/-- Every quadratic residue has Jacobi symbol `+1`. -/
theorem quadResidueSet_subset_jacobiPosSet (p q : ℕ) [Fact p.Prime] [Fact q.Prime] :
    quadResidueSet p q ⊆ jacobiPosSet p q := by
  intro x hx
  simp only [quadResidueSet, jacobiPosSet, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, jacobiSymbol_eq_one_of_isSquare p q hx.2⟩

/-- `J_N^{+1}` partitions into `QR_N` and `QNR_N^{+1}`. -/
theorem jacobiPosSet_eq_disjoint_union (p q : ℕ) [Fact p.Prime] [Fact q.Prime] :
    jacobiPosSet p q = quadResidueSet p q ∪ positiveNonresidues p q ∧
      Disjoint (quadResidueSet p q) (positiveNonresidues p q) := by
  classical
  refine ⟨?_, ?_⟩
  · ext x
    simp only [jacobiPosSet, quadResidueSet, positiveNonresidues, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_cases hsq : IsSquare x
      · exact Or.inl hsq
      · exact Or.inr ⟨hsq, h⟩
    · rintro (hsq | ⟨_, h⟩)
      · exact jacobiSymbol_eq_one_of_isSquare p q hsq
      · exact h
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [quadResidueSet, positiveNonresidues, Finset.mem_filter] at hx1 hx2
    exact hx2.2.1 hx1.2

private def crtUnitsEquiv (p q : ℕ) (hpq : Nat.Coprime p q) :
    (ZMod (p * q))ˣ ≃* (ZMod p)ˣ × (ZMod q)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder hpq).toMulEquiv).trans MulEquiv.prodUnits

private theorem isSquare_crt_iff (p q : ℕ) (hpq : Nat.Coprime p q) (x : (ZMod (p * q))ˣ) :
    IsSquare x ↔
      IsSquare (crtUnitsEquiv p q hpq x).1 ∧ IsSquare (crtUnitsEquiv p q hpq x).2 := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨⟨(crtUnitsEquiv p q hpq r).1, by simp⟩, ⟨(crtUnitsEquiv p q hpq r).2, by simp⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨(crtUnitsEquiv p q hpq).symm (a, b), ?_⟩
    apply (crtUnitsEquiv p q hpq).injective
    ext <;> simp [ha, hb]

/-- The Legendre symbol at `p` of a residue modulo `m` is that of its image under any ring map
`ZMod m →+* ZMod p`. -/
private theorem legendreSym_val_map {m p : ℕ} [NeZero m] [Fact p.Prime] (f : ZMod m →+* ZMod p)
    (x : ZMod m) : legendreSym p (x.val : ℤ) = legendreSym p ((f x).val : ℤ) := by
  have hmod : (x.val : ℤ) ≡ ((f x).val : ℤ) [ZMOD p] := by
    rw [← ZMod.intCast_eq_intCast_iff, Int.cast_natCast, Int.cast_natCast,
      ZMod.natCast_zmod_val (f x), ← map_natCast f, ZMod.natCast_zmod_val]
  rw [legendreSym.mod p _, hmod, ← legendreSym.mod]

private theorem legendreSym_crt_fst (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : Nat.Coprime p q) (x : (ZMod (p * q))ˣ) :
    legendreSym p (x.val.val : ℤ) =
      legendreSym p (((crtUnitsEquiv p q hpq x).1 : ZMod p).val : ℤ) :=
  legendreSym_val_map (p := p) ((RingHom.fst (ZMod p) (ZMod q)).comp
    (ZMod.chineseRemainder hpq : ZMod (p * q) →+* ZMod p × ZMod q)) x

private theorem legendreSym_crt_snd (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : Nat.Coprime p q) (x : (ZMod (p * q))ˣ) :
    legendreSym q (x.val.val : ℤ) =
      legendreSym q (((crtUnitsEquiv p q hpq x).2 : ZMod q).val : ℤ) :=
  legendreSym_val_map (p := q) ((RingHom.snd (ZMod p) (ZMod q)).comp
    (ZMod.chineseRemainder hpq : ZMod (p * q) →+* ZMod p × ZMod q)) x

private theorem isSquare_unit_iff_legendreSym (p : ℕ) [Fact p.Prime] (_hp : p ≠ 2)
    (u : (ZMod p)ˣ) :
    IsSquare u ↔ legendreSym p ((u : ZMod p).val : ℤ) = 1 := by
  have hu0 : (((u : ZMod p).val : ℤ) : ZMod p) ≠ 0 := by
    simp [u.ne_zero]
  rw [legendreSym.eq_one_iff p hu0]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨(r : ZMod p), by simp⟩
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hr
      exact u.ne_zero hr
    exact ⟨Units.mk0 r hr0, Units.ext hr⟩

private theorem card_squares_prime_units (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    2 * (Finset.univ.filter fun u : (ZMod p)ˣ => IsSquare u).card = Fintype.card (ZMod p)ˣ := by
  have hrange : (Finset.univ.filter fun u : (ZMod p)ˣ => IsSquare u).card =
      Nat.card (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range := by
    rw [Nat.card_eq_fintype_card]
    symm
    apply Fintype.card_of_subtype
    intro u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, MonoidHom.mem_range,
      powMonoidHom_apply, isSquare_iff_exists_sq, eq_comm]
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
  have hdvd : 2 ∣ p - 1 := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two (by omega))
    omega
  rw [hrange, IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, hcard,
    Nat.gcd_eq_right hdvd]
  omega

/-- Half of the units modulo an odd prime are nonsquares. -/
private theorem card_nonsquares_prime_units (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    (Finset.univ.filter fun u : (ZMod p)ˣ => ¬ IsSquare u).card =
      (Finset.univ.filter fun u : (ZMod p)ˣ => IsSquare u).card := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun u : (ZMod p)ˣ => IsSquare u)
  rw [Finset.card_univ] at h
  have := card_squares_prime_units p hp
  omega

/-- For distinct odd primes `p ≠ q`, `|QR_N| = |QNR_N^{+1}|`. -/
theorem card_quadResidueSet_eq_card_positiveNonresidues (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hp : 2 < p) (hq : 2 < q) :
    (quadResidueSet p q).card = (positiveNonresidues p q).card := by
  classical
  have hcop : Nat.Coprime p q := (Nat.coprime_primes Fact.out Fact.out).mpr hpq
  -- Through the CRT, `QR_N` is `S_p × S_q` and `QNR_N^{+1}` is `N_p × N_q`, where `S` are the
  -- squares and `N` the nonsquares among the units modulo each prime.
  have hQR : (quadResidueSet p q).card = ((Finset.univ.filter fun u : (ZMod p)ˣ => IsSquare u) ×ˢ
      (Finset.univ.filter fun v : (ZMod q)ˣ => IsSquare v)).card :=
    Finset.card_bijective _ (crtUnitsEquiv p q hcop).bijective fun x => by
      simp [quadResidueSet, isSquare_crt_iff p q hcop x]
  have hQNR : (positiveNonresidues p q).card =
      ((Finset.univ.filter fun u : (ZMod p)ˣ => ¬ IsSquare u) ×ˢ
        (Finset.univ.filter fun v : (ZMod q)ˣ => ¬ IsSquare v)).card := by
    refine Finset.card_bijective _ (crtUnitsEquiv p q hcop).bijective fun x => ?_
    -- Both sides speak about the Legendre symbols of the CRT components: a component is a
    -- square iff its symbol is `1`, and the Jacobi symbol is their product.
    simp only [positiveNonresidues, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [isSquare_crt_iff p q hcop x, jacobiSymbol, legendreSym_crt_fst p q hcop x,
      legendreSym_crt_snd p q hcop x]
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
      isSquare_unit_iff_legendreSym p (by omega), isSquare_unit_iff_legendreSym q (by omega)]
    -- Each symbol is `±1`.
    rcases legendreSym.eq_one_or_neg_one p
        (a := ((crtUnitsEquiv p q hcop x).1 : ZMod p).val) (by simp) with h | h <;>
      rcases legendreSym.eq_one_or_neg_one q
        (a := ((crtUnitsEquiv p q hcop x).2 : ZMod q).val) (by simp) with h' | h' <;>
      simp only [h, h'] <;> norm_num
  rw [hQR, hQNR, Finset.card_product, Finset.card_product, card_nonsquares_prime_units p hp,
    card_nonsquares_prime_units q hq]

/-! ### Blum integers and principal square roots -/

/-- A prime `p` is a Blum prime if `p ≡ 3 (mod 4)`. -/
def IsBlumPrime (p : ℕ) : Prop := p.Prime ∧ p % 4 = 3

/-- A Blum modulus `(p, q)` consists of two distinct Blum primes. -/
def IsBlumModulus (p q : ℕ) : Prop := IsBlumPrime p ∧ IsBlumPrime q ∧ p ≠ q

/-- `-1` has Legendre symbol `-1` at every prime `r ≡ 3 (mod 4)` dividing `N`. -/
private theorem legendreSym_neg_one_unit {N r : ℕ} [NeZero N] [Fact r.Prime] (hr : r % 4 = 3)
    (hrN : (N : ZMod r) = 0) : legendreSym r ((-1 : (ZMod N)ˣ).val.val : ℤ) = -1 := by
  have hmod : (((-1 : (ZMod N)ˣ).val.val : ℤ)) ≡ (-1 : ℤ) [ZMOD r] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    simp [ZMod.natCast_val, ZMod.cast_neg_one, hrN]
  rw [legendreSym.mod r _, hmod, ← legendreSym.mod r _, legendreSym.at_neg_one (by omega)]
  simp [ZMod.χ₄_nat_three_mod_four hr]

/-- For any Blum modulus, `-1` is a quadratic nonresidue with Jacobi symbol `+1`. -/
theorem neg_one_mem_positiveNonresidues (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (h : IsBlumModulus p q) :
    (-1 : (ZMod (p * q))ˣ) ∈ positiveNonresidues p q := by
  have hp2 : p ≠ 2 := by have := h.1.2; omega
  have hp_neg := legendreSym_neg_one_unit (N := p * q) h.1.2 (by simp)
  have hq_neg := legendreSym_neg_one_unit (N := p * q) h.2.1.2 (by simp)
  simp only [positiveNonresidues, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, by unfold jacobiSymbol; rw [hp_neg, hq_neg]; norm_num⟩
  intro hsq
  have hcop : Nat.Coprime p q := (Nat.coprime_primes h.1.1 h.2.1.1).mpr h.2.2
  have h1 := ((isSquare_crt_iff p q hcop (-1)).mp hsq).1
  have hp_eq := (isSquare_unit_iff_legendreSym p hp2 (crtUnitsEquiv p q hcop (-1)).1).mp h1
  rw [← legendreSym_crt_fst p q hcop (-1)] at hp_eq
  omega

/-- Principal square root in `(ZMod (p * q))ˣ` for a Blum modulus:
`y ^ (((p - 1)(q - 1) + 4) / 8)`. -/
def blumSqrt (p q : ℕ) (y : (ZMod (p * q))ˣ) : (ZMod (p * q))ˣ :=
  y ^ (((p - 1) * (q - 1) + 4) / 8)

private theorem blum_exponent_eq (p q : ℕ) (hp : p % 4 = 3) (hq : q % 4 = 3) :
    2 * (((p - 1) * (q - 1) + 4) / 8) = ((p - 1) * (q - 1)) / 4 + 1 := by
  have hp1 : p - 1 = 4 * (p / 4) + 2 := by omega
  have hq1 : q - 1 = 4 * (q / 4) + 2 := by omega
  rw [hp1, hq1]
  ring_nf
  omega

private theorem blum_sq_pow_eq_one (p q : ℕ) (h : IsBlumModulus p q) (u : (ZMod (p * q))ˣ) :
    (u ^ 2) ^ (((p - 1) * (q - 1)) / 4) = 1 := by
  have hpPrime : Fact p.Prime := ⟨h.1.1⟩
  have hqPrime : Fact q.Prime := ⟨h.2.1.1⟩
  have hp1 : p - 1 = 4 * (p / 4) + 2 := by have := h.1.2; omega
  have hq1 : q - 1 = 4 * (q / 4) + 2 := by have := h.2.1.2; omega
  have hcop : Nat.Coprime p q := (Nat.coprime_primes h.1.1 h.2.1.1).mpr h.2.2
  -- Twice the exponent is a multiple of `p - 1` and of `q - 1`, the orders of the CRT components.
  have hk : ∀ r s : ℕ, r - 1 = 4 * (r / 4) + 2 → s - 1 = 4 * (s / 4) + 2 →
      2 * (((r - 1) * (s - 1)) / 4) = (r - 1) * (2 * (s / 4) + 1) := by
    intro r s hr hs
    rw [hr, hs, show (4 * (r / 4) + 2) * (4 * (s / 4) + 2) =
      4 * ((2 * (r / 4) + 1) * (2 * (s / 4) + 1)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    ring
  rw [← pow_mul]
  apply (crtUnitsEquiv p q hcop).injective
  rw [map_pow, map_one]
  refine Prod.ext ?_ ?_
  · rw [Prod.pow_fst, Prod.fst_one, hk p q hp1 hq1, pow_mul,
      ZMod.units_pow_card_sub_one_eq_one, one_pow]
  · rw [Prod.pow_snd, Prod.snd_one, Nat.mul_comm (p - 1), hk q p hq1 hp1, pow_mul,
      ZMod.units_pow_card_sub_one_eq_one, one_pow]

/-- For a Blum modulus, `blumSqrt p q y` is a square root of `y` whenever `y ∈ QR_N`, and lies
in `QR_N`. -/
theorem blumSqrt_sq (p q : ℕ) [NeZero (p * q)] (h : IsBlumModulus p q) {y : (ZMod (p * q))ˣ}
    (hy : y ∈ quadResidueSet p q) :
    (blumSqrt p q y) ^ 2 = y ∧ blumSqrt p q y ∈ quadResidueSet p q := by
  simp only [quadResidueSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  obtain ⟨x, rfl⟩ := hy
  have hp4 : p % 4 = 3 := h.1.2
  have hq4 : q % 4 = 3 := h.2.1.2
  have hexp : 2 * (((p - 1) * (q - 1) + 4) / 8) = ((p - 1) * (q - 1)) / 4 + 1 :=
    blum_exponent_eq p q hp4 hq4
  have hsq_eq : (blumSqrt p q (x * x)) ^ 2 = x * x := by
    unfold blumSqrt
    rw [← pow_two, ← pow_mul, mul_comm (((p - 1) * (q - 1) + 4) / 8) 2, hexp, pow_add, pow_one,
      blum_sq_pow_eq_one p q h x, one_mul]
  refine ⟨hsq_eq, ?_⟩
  simp only [quadResidueSet, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨x ^ (((p - 1) * (q - 1) + 4) / 8), ?_⟩
  unfold blumSqrt
  exact mul_pow x x (((p - 1) * (q - 1) + 4) / 8)

/-- For a Blum modulus, `blumSqrt p q (x ^ 2) = x` whenever `x ∈ QR_N`. -/
theorem blumSqrt_sq_self (p q : ℕ) [NeZero (p * q)] (h : IsBlumModulus p q) {x : (ZMod (p * q))ˣ}
    (hx : x ∈ quadResidueSet p q) :
    blumSqrt p q (x ^ 2) = x := by
  simp only [quadResidueSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨u, rfl⟩ := hx
  have hexp : 2 * (((p - 1) * (q - 1) + 4) / 8) = ((p - 1) * (q - 1)) / 4 + 1 :=
    blum_exponent_eq p q h.1.2 h.2.1.2
  unfold blumSqrt
  rw [← pow_mul, hexp, pow_add, pow_one]
  have hpow : (u * u) ^ (((p - 1) * (q - 1)) / 4) = 1 := by
    rw [← pow_two]
    exact blum_sq_pow_eq_one p q h u
  rw [hpow, one_mul]

/-- For a Blum modulus, squaring `x ↦ x ^ 2` is a bijection from `QR_N` onto `QR_N`. -/
theorem sq_bijOn_quadResidueSet (p q : ℕ) [NeZero (p * q)] (h : IsBlumModulus p q) :
    Set.BijOn (fun x : (ZMod (p * q))ˣ => x ^ 2)
      (quadResidueSet p q : Set (ZMod (p * q))ˣ)
      (quadResidueSet p q : Set (ZMod (p * q))ˣ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x _
    simp only [Finset.mem_coe, quadResidueSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, pow_two x⟩
  · intro x hx y hy hxy
    change x ^ 2 = y ^ 2 at hxy
    calc x = blumSqrt p q (x ^ 2) := (blumSqrt_sq_self p q h (Finset.mem_coe.mp hx)).symm
      _ = blumSqrt p q (y ^ 2) := by rw [hxy]
      _ = y := blumSqrt_sq_self p q h (Finset.mem_coe.mp hy)
  · intro y hy
    exact ⟨blumSqrt p q y, Finset.mem_coe.mpr (blumSqrt_sq p q h (Finset.mem_coe.mp hy)).2,
      (blumSqrt_sq p q h (Finset.mem_coe.mp hy)).1⟩

/-! ### Computational quadratic residuosity assumption -/

/-- Valid RSA/QR modulus parameters `(p, q)` with distinct odd primes. -/
structure ModulusDesc where
  /-- First odd prime factor. -/
  p : ℕ
  /-- Second odd prime factor. -/
  q : ℕ
  /-- `p` is prime. -/
  prime_p : p.Prime
  /-- `q` is prime. -/
  prime_q : q.Prime
  /-- `p` and `q` are distinct. -/
  ne_pq : p ≠ q
  /-- `p` is odd. -/
  two_lt_p : 2 < p
  /-- `q` is odd. -/
  two_lt_q : 2 < q

instance (d : ModulusDesc) : Fact d.p.Prime := ⟨d.prime_p⟩
instance (d : ModulusDesc) : Fact d.q.Prime := ⟨d.prime_q⟩

noncomputable instance (d : ModulusDesc) : Nonempty (quadResidueSet d.p d.q) :=
  ⟨⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ 1, ⟨1, (one_mul 1).symm⟩⟩⟩⟩

noncomputable instance (d : ModulusDesc) : Nonempty (positiveNonresidues d.p d.q) := by
  have hcard : 0 < (positiveNonresidues d.p d.q).card := by
    rw [← card_quadResidueSet_eq_card_positiveNonresidues d.p d.q d.ne_pq d.two_lt_p d.two_lt_q]
    exact Finset.card_pos.mpr
      ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ 1, ⟨1, (one_mul 1).symm⟩⟩⟩
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hcard
  exact ⟨⟨x, hx⟩⟩

/-- Real quadratic residuosity experiment: sample `N = p * q` and a uniform quadratic residue
`y ∈ QR_N`, and give `(N, y)` to the distinguisher. -/
noncomputable def qrRealGame (setup : ℕ → PMF ModulusDesc)
    (adversary : ℕ → ℕ × ℕ → ProbComp Bool) (n : ℕ) : Game := do
  let d ← setup n
  let y ← PMF.uniformOfFintype (quadResidueSet d.p d.q)
  ProbComp.eval (adversary n (d.p * d.q, y.1.val.val))

/-- Ideal quadratic residuosity experiment: sample `N = p * q` and a uniform quadratic
nonresidue `y ∈ QNR_N^{+1}` with Jacobi symbol `+1`, and give `(N, y)` to the distinguisher. -/
noncomputable def qrIdealGame (setup : ℕ → PMF ModulusDesc)
    (adversary : ℕ → ℕ × ℕ → ProbComp Bool) (n : ℕ) : Game := do
  let d ← setup n
  let y ← PMF.uniformOfFintype (positiveNonresidues d.p d.q)
  ProbComp.eval (adversary n (d.p * d.q, y.1.val.val))

/-- The computational quadratic residuosity assumption: no uniform strict PPT distinguisher
can distinguish a random quadratic residue in `QR_N` from a random quadratic nonresidue in
`QNR_N^{+1}` given `N = p * q`. -/
def QuadraticResiduosityHard (setup : ℕ → PMF ModulusDesc) : Prop :=
  Game.Indistinguishable
    (fun adversary n => qrRealGame setup adversary n)
    (fun adversary n => qrIdealGame setup adversary n)
    (fun adversary =>
      IsPPTOn (encPair encUnary (encPair encNat encNat)) encBool
        (fun input => adversary input.1 input.2))

end Cslib.Crypto

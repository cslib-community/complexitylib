/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ActiveCall
public import Complexity.Computability.PolyTime.GaloisRingSeries
import Mathlib.Data.List.GetD

/-!
# Native tapered recovery (Lemma D.5) on coefficient lists

This file gives the native procedure behind the recovery step of the contraction algorithm of
[OpenAI2026ETH] (§D.4.4, Lemma D.5, pp. 60–61), and proves that it computes the mathematical
recovery `Cslib.Circuits.Frontier.recoverFromValues` of
`Complexity/Computability/Circuit/Frontier/TensorNetwork/ActiveCall.lean`.

**Input.** A precision `p`, a shift `Δ`, the monic polynomial `fl` of
`Complexity/Computability/PolyTime/GaloisRingArithmetic.lean`, the parameters `a, u, h`, the
interpolation points `ζ` and, for each node index `k < 2 ^ (a + 1)`, `k ≠ 2 ^ a` (the node
`t = k - 2 ^ a`, `NativeRecovery.node`), the values at the points. All arithmetic is in
`A_N = (ℤ / 2 ^ N)[U] / (f)` with `N = p + Δ`.

**Procedure** (`NativeRecovery.recover`). For each node `t` of multiplicity `J = q_t`:

1. interpolate the values (`GaloisRingArith.interp`);
2. multiply by the reciprocal of `E_t(t + α z)` below `z ^ J` (`NativeRecovery.recip`). Each factor
   of `E_t(t + α z)` is a power of `1 + c_q z` with `c_q = α / (t - q)`, a `2`-adic integer
   (`NativeRecovery.slopeConst`), whose reciprocal is the geometric series of `-c_q`;
3. combine the `J` coefficients with the multipliers `2 ^ Δ E_t(0) (-t / α) ^ j`
   (`NativeRecovery.coeffMult`). Since `E_t(0) = ∏_q (-q c_q / α) ^ (q_q)`, the multiplier is
   `2 ^ (Δ - (a + 1)(M_t + j)) ∏_q (-q c_q) ^ (q_q) (-t) ^ j` with `M_t = ∑_q q_q`, a `2`-adic
   integer once `Δ ≥ (a + 1)(M_t + j)`.

The sum over the nodes is `2 ^ Δ` times the recovered value. Dividing its coordinates by
`2 ^ Δ` (`GaloisRingArith.shiftDown`) gives the recovered value modulo `2 ^ p`.

**Precision.** The values at node `t` need only be known modulo `2 ^ p_t`: the multipliers have
`2`-adic valuation at least `Δ + p - p_t` when `p + 6 h D_t + q_t (a + 1) ≤ p_t`
((D.10) and the evaluation loss), so the error is killed in `A_N`. This is the precision estimate
of Lemma D.5 (`Cslib.Circuits.Frontier.exists_taperedRecovery_eq_add`), carried out natively.

**Status.** This file proves the components: the constants, the reciprocal, the multipliers and
the precision estimate, each against an arbitrary ring homomorphism `ρ : ℤ_(2) → A_N`. The
assembly into `recover = recoverFromValues mod 2 ^ p` (through a reduction `B → A_N` and the
interpolation of `GaloisRingArith.interp`) and the polynomial-time certificate are not yet done.

## Main definitions

* `Cslib.Circuits.Frontier.NativeRecovery.slopeConst`: the constant `α / (t - q)`.
* `Cslib.Circuits.Frontier.NativeRecovery.recip`: the truncated reciprocal of `E_t(t + α z)`.
* `Cslib.Circuits.Frontier.NativeRecovery.coeffMult`: the multipliers.
* `Cslib.Circuits.Frontier.NativeRecovery.recover`: native tapered recovery.
* `Cslib.Circuits.Frontier.NativeRecovery.recipSeries`,
  `Cslib.Circuits.Frontier.NativeRecovery.gamma`: the reciprocal and the multipliers over
  `ℤ_(2)`.

## Main results

* `Cslib.Circuits.Frontier.NativeRecovery.val_slopeConst`: the constant `α / (t - q)` is correct.
* `Cslib.Circuits.Frontier.NativeRecovery.val_recip`: the native reciprocal is correct below
  `z ^ J`.
* `Cslib.Circuits.Frontier.NativeRecovery.val_coeffMult`,
  `Cslib.Circuits.Frontier.NativeRecovery.coe_gamma`: the native multiplier is the image of
  `2 ^ Δ E_t(0) (-t / α) ^ j`.
* `Cslib.Circuits.Frontier.NativeRecovery.gamma_mul_two_pow_eq_zero`: under the precision
  hypothesis of Lemma D.5, the multipliers annihilate `2 ^ p_t` in `A_(p + Δ)`.
* `Cslib.Circuits.Frontier.NativeRecovery.sum_recoveryNodes`,
  `Cslib.Circuits.Frontier.NativeRecovery.prod_others`: sums and products over the nodes as
  iterations over node indices.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.4, Lemma D.5,
  (D.9)–(D.10), pp. 60–61.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.NativeRecovery

open Cslib.GaloisRingArith Polynomial Finset

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

/-! ### Nodes -/

/-- The node `t = k - 2 ^ a` of index `k`. -/
def node (a k : ℕ) : ℤ := (k : ℤ) - 2 ^ a

/-- The `2`-adic valuation of `d`, by at most `b` halvings: `v₂ d` when `d < 2 ^ b`
(`NativeRecovery.twoVal_eq`), and `0` for `d = 0`. -/
def twoVal : ℕ → ℕ → ℕ
  | 0, _ => 0
  | b + 1, d => if d ≠ 0 ∧ d % 2 = 0 then twoVal b (d / 2) + 1 else 0

theorem twoVal_eq : ∀ {b d : ℕ}, d < 2 ^ b → twoVal b d = padicValNat 2 d
  | 0, d, hd => by rw [pow_zero] at hd; obtain rfl : d = 0 := by omega
                   simp [twoVal]
  | b + 1, d, hd => by
    rw [twoVal]
    split_ifs with h
    · obtain ⟨hd0, h2⟩ := h
      have hd' : d = 2 * (d / 2) := by omega
      rw [twoVal_eq (by rw [pow_succ] at hd; omega)]
      conv_rhs => rw [hd']
      rw [padicValNat.mul (by norm_num) (by omega), padicValNat_self, add_comm]
    · rcases Nat.eq_zero_or_pos d with rfl | hpos
      · simp
      · exact (padicValNat.eq_zero_of_not_dvd (by omega)).symm

/-- The multiplicity `q_t = h (u - v₂ t)` of the node of index `k`. -/
def mult (a u h k : ℕ) : ℕ := h * (u - twoVal (a + 1) (k - 2 ^ a + (2 ^ a - k)))

theorem mult_eq {a k : ℕ} (u h : ℕ) (hk : k < 2 ^ (a + 1)) :
    mult a u h k = taperMult u h (node a k) := by
  have : ((k : ℤ) - 2 ^ a).natAbs = k - 2 ^ a + (2 ^ a - k) := by
    rw [show (2 : ℤ) ^ a = ((2 ^ a : ℕ) : ℤ) by push_cast; rfl]
    omega
  rw [mult, taperMult, node, padicValInt, this, twoVal_eq (by rw [pow_succ] at hk ⊢; omega)]

/-- The indices of the nodes other than the node of index `k`. -/
def others (a k : ℕ) : List ℕ :=
  (List.range (2 ^ (a + 1))).filter fun k' => k' ≠ 2 ^ a ∧ k' ≠ k

/-- The total multiplicity `M_t = ∑_{q ≠ t} q_q` of the other nodes. -/
def multSum (a u h k : ℕ) : ℕ := ((others a k).map (mult a u h)).sum

/-! ### Constants -/

/-- The integer `x - y` as a constant of `A_N`. -/
def diffConst (N : ℕ) (fl : List ℕ) (x y : ℕ) : List ℕ :=
  if x < y then neg N fl [y - x] else [x - y]

/-- The `2`-adic integer `2 ^ (a + 1) / (x - y)` as a constant of `A_N`, for
`0 < |x - y| ≤ 2 ^ (a + 1)`: with `|x - y| = 2 ^ v o`, `o` odd, it is
`± 2 ^ (a + 1 - v) o⁻¹`. -/
def slopeConst (N : ℕ) (fl : List ℕ) (a x y : ℕ) : List ℕ :=
  let d := x - y + (y - x)
  let v := twoVal (a + 1) d
  let w := mul N fl [2 ^ (a + 1 - v)] (inv N fl [d / 2 ^ v])
  if x < y then neg N fl w else w

/-! ### The reciprocal of `E_t(t + α z)` -/

/-- The geometric series `∑_{i < J} (-c) ^ i z ^ i`, the reciprocal of `1 + c z` below
`z ^ J`. -/
def geom (N : ℕ) (fl : List ℕ) (J : ℕ) (c : List ℕ) : List (List ℕ) :=
  (List.range J).map fun i => pow N fl (neg N fl c) i

/-- Multiply by the reciprocal of `(1 + c z) ^ m` below `z ^ J`. -/
def mulGeomPow (N : ℕ) (fl : List ℕ) (J : ℕ) (c : List ℕ) (m : ℕ) (R : List (List ℕ)) :
    List (List ℕ) :=
  (List.range m).foldl (fun R _ => tmul N fl J R (geom N fl J c)) R

/-- **The reciprocal of `E_t(t + α z)` below `z ^ J`**, for the node of index `k`: the product of
the reciprocals of `(1 + c_q z) ^ (q_q)` over the other nodes `q`, `c_q = α / (t - q)`. -/
def recip (N : ℕ) (fl : List ℕ) (a u h k J : ℕ) : List (List ℕ) :=
  (others a k).foldl (fun R k' => mulGeomPow N fl J (slopeConst N fl a k k') (mult a u h k') R)
    [one fl]

/-! ### The multipliers -/

/-- `∏_{q ≠ t} (-q c_q) ^ (q_q)` for the node of index `k`. -/
def basisNum (N : ℕ) (fl : List ℕ) (a u h k : ℕ) : List ℕ :=
  (others a k).foldl (fun acc k' => mul N fl acc
    (pow N fl (mul N fl (diffConst N fl (2 ^ a) k') (slopeConst N fl a k k')) (mult a u h k')))
    (one fl)

/-- The multiplier `2 ^ Δ E_t(0) (-t / α) ^ j` of the coefficient of `z ^ j` at the node of
index `k`, as `2 ^ (Δ - (a + 1)(M_t + j)) ∏_{q ≠ t} (-q c_q) ^ (q_q) (-t) ^ j`. -/
def coeffMult (N : ℕ) (fl : List ℕ) (a u h Δ k j : ℕ) : List ℕ :=
  mul N fl (mul N fl [2 ^ (Δ - (a + 1) * (multSum a u h k + j))] (basisNum N fl a u h k))
    (pow N fl (diffConst N fl (2 ^ a) k) j)

/-! ### Recovery -/

/-- The contribution of the node of index `k`, from its values `w` at the points `ζ`:
interpolate, divide by `E_t(t + α z)` below `z ^ q_t`, and combine the coefficients with the
multipliers. -/
def nodeTerm (N : ℕ) (fl : List ℕ) (a u h Δ : ℕ) (ζ : List (List ℕ)) (k : ℕ)
    (w : List (List ℕ)) : List ℕ :=
  let J := mult a u h k
  let Q := tmul N fl J (interp N fl ζ w) (recip N fl a u h k J)
  (List.range J).foldl (fun S j => add N fl S (mul N fl (coeffMult N fl a u h Δ k j) (Q.getD j [])))
    (zero fl)

/-- **Native tapered recovery.** From the values `W.getD k []` at the points `ζ` for each node
index `k`, the value recovered modulo `2 ^ p`, computing in `A_(p + Δ)` and dividing by
`2 ^ Δ` at the end. -/
def recover (p Δ : ℕ) (fl : List ℕ) (a u h : ℕ) (ζ : List (List ℕ)) (W : List (List (List ℕ))) :
    List ℕ :=
  shiftDown Δ ((List.range (2 ^ (a + 1))).foldl (fun S k =>
    if k = 2 ^ a then S else add (p + Δ) fl S (nodeTerm (p + Δ) fl a u h Δ ζ k (W.getD k [])))
    (zero fl))

/-! ### Correctness of the constants -/

variable {N : ℕ} {fl : List ℕ}

theorem val_diffConst (x y : ℕ) :
    val N fl (diffConst N fl x y) = (((x : ℤ) - y : ℤ) : Ring N fl) := by
  unfold diffConst
  split_ifs with h
  · rw [val_neg, val_singleton, Nat.cast_sub h.le]
    push_cast
    ring
  · rw [val_singleton, Nat.cast_sub (not_lt.mp h)]
    push_cast
    ring

/-- The `2`-adic integer `2 ^ (a + 1) / (t - q)` for distinct grid points. -/
noncomputable def slope (a : ℕ) {t q : ℤ} (ht : t ∈ cauchyGrid (2 ^ a))
    (hq : q ∈ cauchyGrid (2 ^ a)) (hne : q ≠ t) : ℤ₍₂₎ :=
  ⟨2 ^ (a + 1) / ((t : ℚ) - q), padicValuation_two_pow_div_le_one ht hq hne⟩

theorem node_mem_cauchyGrid {a k : ℕ} (hk : k < 2 ^ (a + 1)) : node a k ∈ cauchyGrid (2 ^ a) := by
  rw [cauchyGrid_two_pow, mem_Ico, node]
  have : (k : ℤ) < 2 ^ (a + 1) := by exact_mod_cast hk
  rw [pow_succ] at this
  constructor <;> omega

theorem node_injective (a : ℕ) : Function.Injective (node a) := fun k k' h => by
  unfold node at h
  omega

/-- **The slope constant is correct**: for every ring homomorphism `ρ` from `ℤ_(2)`, it is the
image of `2 ^ (a + 1) / (t - q)`. -/
theorem val_slopeConst (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2))))
    (ρ : ℤ₍₂₎ →+* Ring N fl) {a k k' : ℕ} (hk : k < 2 ^ (a + 1)) (hk' : k' < 2 ^ (a + 1))
    (hne : k' ≠ k) :
    val N fl (slopeConst N fl a k k') =
      ρ (slope a (node_mem_cauchyGrid hk) (node_mem_cauchyGrid hk')
        (fun h => hne (node_injective a h))) := by
  set d := k - k' + (k' - k)
  set v := padicValNat 2 d
  set o := d / 2 ^ v
  have hd0 : d ≠ 0 := by omega
  have hdlt : d < 2 ^ (a + 1) := by omega
  have hdv : d = 2 ^ v * o := (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
  have hodd : Odd o := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    have hnd : ¬ 2 ^ (v + 1) ∣ d := pow_succ_padicValNat_not_dvd hd0
    refine hnd ?_
    have h' : 2 ^ (v + 1) ∣ 2 ^ v * o := by
      rw [pow_succ]; exact Nat.mul_dvd_mul_left _ h2
    rwa [← hdv] at h'
  have hva : v ≤ a + 1 := by
    have : 2 ^ v ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) pow_padicValNat_dvd
    have : v < a + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp (this.trans_lt hdlt)
    omega
  have hunit := isUnit_natCast_of_odd (p := N) (fl := fl) hodd
  -- In `ℤ_(2)`, `slope * o = ± 2 ^ (a + 1 - v)`.
  set c := slope a (node_mem_cauchyGrid hk) (node_mem_cauchyGrid hk')
    (fun h => hne (node_injective a h))
  have hc : c * (o : ℤ₍₂₎) = if k < k' then -((2 ^ (a + 1 - v) : ℕ) : ℤ₍₂₎)
      else ((2 ^ (a + 1 - v) : ℕ) : ℤ₍₂₎) := by
    apply Subtype.val_injective
    have hdiff : ((node a k : ℤ) : ℚ) - (node a k' : ℤ) =
        if k < k' then -((2 : ℚ) ^ v * o) else (2 : ℚ) ^ v * o := by
      have : ((d : ℕ) : ℚ) = (2 : ℚ) ^ v * o := by exact_mod_cast hdv
      rw [← this]
      simp only [node, d]
      split_ifs with h
      · rw [Nat.cast_add, Nat.cast_sub h.le, Nat.sub_eq_zero_of_le h.le]; push_cast; ring
      · rw [Nat.sub_eq_zero_of_le (not_lt.mp h), Nat.cast_add, Nat.cast_sub (not_lt.mp h)]
        push_cast; ring
    have ho : (o : ℚ) ≠ 0 := by exact_mod_cast hodd.pos.ne'
    have h2v : (2 : ℚ) ^ (a + 1) = 2 ^ (a + 1 - v) * 2 ^ v := by
      rw [← pow_add, Nat.sub_add_cancel hva]
    simp only [slope, c, Subring.coe_mul, Subring.coe_natCast, apply_ite Subtype.val,
      Subring.coe_neg]
    rw [hdiff]
    split_ifs
    · push_cast
      field_simp
      rw [h2v]
      ring
    · push_cast
      field_simp
      rw [h2v]
      ring
  have hρ := congrArg ρ hc
  rw [map_mul, map_natCast] at hρ
  have hρc : ρ c = ρ (if k < k' then -((2 ^ (a + 1 - v) : ℕ) : ℤ₍₂₎)
      else ((2 ^ (a + 1 - v) : ℕ) : ℤ₍₂₎)) *
      _root_.Ring.inverse (o : Ring N fl) := by
    rw [← hρ, mul_assoc, _root_.Ring.mul_inverse_cancel _ hunit, mul_one]
  rw [hρc]
  have hw : val N fl (mul N fl [2 ^ (a + 1 - v)] (inv N fl [o])) =
      ((2 ^ (a + 1 - v) : ℕ) : Ring N fl) * _root_.Ring.inverse (o : Ring N fl) := by
    rw [val_mul, val_singleton, val_inv_of_isUnit hirr (by rwa [val_singleton]), val_singleton]
  simp only [slopeConst]
  rw [show twoVal (a + 1) (k - k' + (k' - k)) = v from twoVal_eq hdlt]
  split_ifs with h
  · rw [val_neg, hw, map_neg, map_natCast, neg_mul]
  · rw [hw, map_natCast]

/-- The slope `2 ^ (a + 1) / (t - q)` for node indices `k, k'`, and `0` off the grid. -/
noncomputable def slope' (a k k' : ℕ) : ℤ₍₂₎ :=
  if h : k < 2 ^ (a + 1) ∧ k' < 2 ^ (a + 1) ∧ k' ≠ k then
    slope a (node_mem_cauchyGrid h.1) (node_mem_cauchyGrid h.2.1)
      (fun e => h.2.2 (node_injective a e))
  else 0

theorem val_slopeConst' (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2))))
    (ρ : ℤ₍₂₎ →+* Ring N fl) {a k k' : ℕ} (hk : k < 2 ^ (a + 1)) (hk' : k' < 2 ^ (a + 1))
    (hne : k' ≠ k) : val N fl (slopeConst N fl a k k') = ρ (slope' a k k') := by
  rw [val_slopeConst hirr ρ hk hk' hne, slope', dite_eq_left_of_eq_true (eq_true ⟨hk, hk', hne⟩)]

/-! ### Correctness of the reciprocal -/

/-- The geometric series `∑ (-c) ^ i z ^ i`, the inverse of `1 + c z`. -/
noncomputable def geomSeries {R : Type*} [CommRing R] (c : R) : PowerSeries R :=
  PowerSeries.mk fun i => (-c) ^ i

theorem one_add_mul_geomSeries {R : Type*} [CommRing R] (c : R) :
    (1 + PowerSeries.C c * PowerSeries.X) * geomSeries c = 1 := by
  ext n
  rw [add_mul, one_mul, map_add, PowerSeries.coeff_one, mul_assoc]
  rcases n with _ | n
  · simp [geomSeries]
  · rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
    simp only [geomSeries, PowerSeries.coeff_mk, pow_succ]
    simp only [Nat.succ_ne_zero, ↓reduceIte, mul_neg]
    ring

/-- The reciprocal of `E_t(t + α z)` over `ℤ_(2)` for the node of index `k`, in the order of
`NativeRecovery.recip`. -/
noncomputable def recipSeries (a u h k : ℕ) : PowerSeries ℤ₍₂₎ :=
  (others a k).foldl (fun ψ k' => ψ * geomSeries (slope' a k k') ^ mult a u h k') 1

theorem mem_others {a k k' : ℕ} : k' ∈ others a k ↔ k' < 2 ^ (a + 1) ∧ k' ≠ 2 ^ a ∧ k' ≠ k := by
  simp [others]

/-- A truncated product computes the coefficients of the product of power series. -/
theorem val_tmul_eq {ρ : ℤ₍₂₎ →+* Ring N fl} {J : ℕ} {P G : List (List ℕ)}
    {φ χ : PowerSeries ℤ₍₂₎} (hP : ∀ i < J, val N fl (P.getD i []) = ρ (PowerSeries.coeff i φ))
    (hG : ∀ i < J, val N fl (G.getD i []) = ρ (PowerSeries.coeff i χ)) {i : ℕ} (hi : i < J) :
    val N fl ((tmul N fl J P G).getD i []) = ρ (PowerSeries.coeff i (φ * χ)) := by
  rw [val_tmul _ _ hi, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun l m => PowerSeries.coeff l φ * PowerSeries.coeff m χ), map_sum]
  refine sum_congr rfl fun l hl => ?_
  have hl' := mem_range.mp hl
  rw [hP l (by omega), hG (i - l) (by omega), map_mul]

theorem val_geom {ρ : ℤ₍₂₎ →+* Ring N fl} {J : ℕ} {c : List ℕ} {γ : ℤ₍₂₎}
    (hc : val N fl c = ρ γ) {i : ℕ} (hi : i < J) :
    val N fl ((geom N fl J c).getD i []) = ρ (PowerSeries.coeff i (geomSeries γ)) := by
  rw [geom, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range,
    val_pow, val_neg, hc, geomSeries, PowerSeries.coeff_mk, map_pow, map_neg]

/-- **The native reciprocal is correct**: its coefficients below `z ^ J` are the images of those
of `NativeRecovery.recipSeries`. -/
theorem val_recip (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2))))
    (ρ : ℤ₍₂₎ →+* Ring N fl) {a u h k J : ℕ} (hk : k < 2 ^ (a + 1)) {i : ℕ} (hi : i < J) :
    val N fl ((recip N fl a u h k J).getD i []) =
      ρ (PowerSeries.coeff i (recipSeries a u h k)) := by
  -- The invariant of the fold over the other nodes.
  suffices H : ∀ (l : List ℕ), (∀ k' ∈ l, k' < 2 ^ (a + 1) ∧ k' ≠ k) →
      ∀ (R : List (List ℕ)) (ψ : PowerSeries ℤ₍₂₎),
      (∀ i < J, val N fl (R.getD i []) = ρ (PowerSeries.coeff i ψ)) →
      ∀ i < J, val N fl ((l.foldl (fun R k' =>
        mulGeomPow N fl J (slopeConst N fl a k k') (mult a u h k') R) R).getD i []) =
        ρ (PowerSeries.coeff i (l.foldl (fun ψ k' => ψ * geomSeries (slope' a k k') ^
          mult a u h k') ψ)) by
    refine H _ (fun k' hk' => ⟨(mem_others.mp hk').1, (mem_others.mp hk').2.2⟩) _ _ ?_ i hi
    intro i _
    rcases i with _ | i
    · simp [PowerSeries.coeff_one]
    · rw [List.getD_cons_succ, List.getD_nil, val_nil, PowerSeries.coeff_one,
        ite_eq_right_of_eq_false _ _ (eq_false (Nat.succ_ne_zero i)), map_zero]
  intro l
  induction l with
  | nil => intro _ R ψ hR; simpa using hR
  | cons k' l ih =>
    intro hl R ψ hR
    rw [List.foldl_cons, List.foldl_cons]
    refine ih (fun k'' hk'' => hl k'' (List.mem_cons_of_mem _ hk'')) _ _ ?_
    obtain ⟨hk', hne⟩ := hl k' List.mem_cons_self
    have hc := val_slopeConst' hirr ρ hk hk' hne
    -- `m` multiplications by the geometric series.
    have hm (m : ℕ) : ∀ i < J, val N fl ((mulGeomPow N fl J (slopeConst N fl a k k') m R).getD
        i []) = ρ (PowerSeries.coeff i (ψ * geomSeries (slope' a k k') ^ m)) := by
      induction m with
      | zero => simpa [mulGeomPow] using hR
      | succ m ihm =>
        intro i hi
        rw [mulGeomPow, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
          ← mulGeomPow, pow_succ, ← mul_assoc]
        exact val_tmul_eq ihm (fun i hi => val_geom hc hi) hi
    exact hm _

/-! ### Products over the nodes -/

/-- The other nodes, as integers, are the nonzero grid points other than `t`. -/
theorem prod_others {M : Type*} [CommMonoid M] (f : ℤ → M) {a k : ℕ} :
    ((others a k).map fun k' => f (node a k')).prod =
      ∏ q ∈ (recoveryNodes a).erase (node a k), f q := by
  have hnd : ((others a k).map (node a)).Nodup :=
    (List.nodup_range.filter _).map (node_injective a)
  have hset : ((others a k).map (node a)).toFinset = (recoveryNodes a).erase (node a k) := by
    ext q
    simp only [List.mem_toFinset, List.mem_map, mem_others, recoveryNodes_eq, mem_erase, mem_Ico]
    obtain ⟨L, hL⟩ : ∃ L : ℕ, 2 ^ a = L := ⟨_, rfl⟩
    have hLz : (2 : ℤ) ^ a = (L : ℤ) := by rw [← hL]; push_cast; rfl
    have hL2 : (2 : ℕ) ^ (a + 1) = 2 * L := by rw [← hL]; ring
    simp only [node, hLz, hL, hL2]
    constructor
    · rintro ⟨k', ⟨hk'1, hk'2, hk'3⟩, rfl⟩
      omega
    · rintro ⟨hqk, hq0, hq1, hq2⟩
      exact ⟨(q + L).toNat, ⟨by omega, by omega, by omega⟩, by omega⟩
  rw [← hset, List.prod_toFinset _ hnd, List.map_map]
  rfl

/-- The nodes are the images of the indices `k < 2 ^ (a + 1)`, `k ≠ 2 ^ a`. -/
theorem recoveryNodes_eq_image (a : ℕ) :
    recoveryNodes a = ((range (2 ^ (a + 1))).filter (· ≠ 2 ^ a)).image (node a) := by
  ext q
  simp only [recoveryNodes_eq, mem_erase, mem_Ico, mem_image, mem_filter, mem_range]
  obtain ⟨L, hL⟩ : ∃ L : ℕ, 2 ^ a = L := ⟨_, rfl⟩
  have hLz : (2 : ℤ) ^ a = (L : ℤ) := by rw [← hL]; push_cast; rfl
  have hL2 : (2 : ℕ) ^ (a + 1) = 2 * L := by rw [← hL]; ring
  simp only [node, hLz, hL, hL2]
  constructor
  · rintro ⟨hq0, hq1, hq2⟩
    exact ⟨(q + L).toNat, ⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨k', ⟨hk'1, hk'2⟩, rfl⟩
    omega

/-- A sum over the nodes is a sum over the node indices. -/
theorem sum_recoveryNodes {M : Type*} [AddCommMonoid M] (f : ℤ → M) (a : ℕ) :
    ∑ t ∈ recoveryNodes a, f t =
      ∑ k ∈ range (2 ^ (a + 1)), if k = 2 ^ a then 0 else f (node a k) := by
  rw [recoveryNodes_eq_image, sum_image fun _ _ _ _ e => node_injective a e, sum_ite,
    sum_const_zero, zero_add]

/-! ### Correctness of the multipliers -/

/-- A fold of multiplications is a product. -/
theorem val_foldl_mul {ι : Type*} (g : ι → List ℕ) (l : List ι) (c : List ℕ) :
    val N fl (l.foldl (fun acc x => mul N fl acc (g x)) c) =
      val N fl c * (l.map fun x => val N fl (g x)).prod := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, val_mul, List.map_cons, List.prod_cons, mul_assoc]

/-- The multiplier `2 ^ Δ E_t(0) (-t / α) ^ j` as a `2`-adic integer:
`2 ^ (Δ - (a + 1)(M_t + j)) ∏_{q ≠ t} (-q c_q) ^ (q_q) (-t) ^ j`. -/
noncomputable def gamma (a u h Δ k j : ℕ) : ℤ₍₂₎ :=
  ((2 ^ (Δ - (a + 1) * (multSum a u h k + j)) : ℕ) : ℤ₍₂₎) *
    ((others a k).map fun k' : ℕ =>
      (((((2 ^ a : ℕ) : ℤ) - (k' : ℤ) : ℤ) : ℤ₍₂₎) * slope' a k k') ^ mult a u h k').prod *
    ((((2 ^ a : ℕ) : ℤ) - k : ℤ) : ℤ₍₂₎) ^ j

/-- **The native multiplier is correct.** -/
theorem val_coeffMult (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2))))
    (ρ : ℤ₍₂₎ →+* Ring N fl) {a u h Δ k : ℕ} (hk : k < 2 ^ (a + 1)) (j : ℕ) :
    val N fl (coeffMult N fl a u h Δ k j) = ρ (gamma a u h Δ k j) := by
  rw [coeffMult, val_mul, val_mul, val_singleton, val_pow, val_diffConst, basisNum,
    val_foldl_mul, val_one, one_mul, gamma, map_mul, map_mul, map_natCast, map_pow, map_intCast,
    map_list_prod, List.map_map]
  congr 2
  refine congrArg List.prod (List.map_congr_left fun k' hk' => ?_)
  obtain ⟨hk'1, -, hk'3⟩ := mem_others.mp hk'
  simp only [Function.comp_apply, val_pow, val_mul, val_diffConst, val_slopeConst' hirr ρ hk hk'1
    hk'3, map_pow, map_mul, map_intCast]

/-- The value `E_t(0)` over `ℚ` as a product over the other node indices. -/
theorem eval_zero_hermiteBasis_eq_prod (a u h k : ℕ) :
    (hermiteBasis (recoveryNodes a) (fun q : ℤ => (q : ℚ)) (taperMult u h) (node a k)).eval 0 =
      ((others a k).map fun k' =>
        (_root_.Ring.inverse ((node a k : ℚ) - node a k') * (0 - node a k')) ^
          mult a u h k').prod := by
  rw [eval_hermiteBasis, ← prod_others]
  refine congrArg List.prod (List.map_congr_left fun k' hk' => ?_)
  rw [mult_eq u h (mem_others.mp hk').1]

/-- **The multiplier is `2 ^ Δ E_t(0) (-t / α) ^ j`.** -/
theorem coe_gamma {a u h Δ k j : ℕ} (hk : k < 2 ^ (a + 1))
    (hΔ : (a + 1) * (multSum a u h k + j) ≤ Δ) :
    ((gamma a u h Δ k j : ℤ₍₂₎) : ℚ) = 2 ^ Δ *
      (hermiteBasis (recoveryNodes a) (fun q : ℤ => (q : ℚ)) (taperMult u h) (node a k)).eval 0 *
        (-(node a k : ℚ) / 2 ^ (a + 1)) ^ j := by
  rw [eval_zero_hermiteBasis_eq_prod]
  -- Each factor is `(-q c_q / α) ^ (q_q)`.
  set X : ℕ → ℚ := fun k' => ((((((2 ^ a : ℕ) : ℤ) - (k' : ℤ) : ℤ) : ℤ₍₂₎) * slope' a k k' :
    ℤ₍₂₎) : ℚ)
  have hfac : ∀ k' ∈ others a k,
      (_root_.Ring.inverse ((node a k : ℚ) - node a k') * (0 - node a k')) ^ mult a u h k' =
        X k' ^ mult a u h k' / (2 ^ (a + 1)) ^ mult a u h k' := by
    intro k' hk'
    obtain ⟨hk'1, -, hk'3⟩ := mem_others.mp hk'
    have hne : (node a k : ℚ) - node a k' ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast fun e => hk'3 (node_injective a e).symm
    have hs : ((slope' a k k' : ℤ₍₂₎) : ℚ) = 2 ^ (a + 1) / ((node a k : ℚ) - node a k') := by
      rw [slope', dite_eq_left_of_eq_true (eq_true ⟨hk, hk'1, hk'3⟩)]; rfl
    rw [← div_pow]
    congr 1
    simp only [X, Subring.coe_mul, hs, Subring.coe_intCast, _root_.Ring.inverse_eq_inv']
    have hq : ((Int.cast (((2 ^ a : ℕ) : ℤ) - (k' : ℤ))) : ℚ) = -(node a k' : ℚ) := by
      simp only [node]; push_cast; ring
    rw [hq, zero_sub]
    field_simp
  have hprod : ∀ l : List ℕ, (l.map fun k' => X k' ^ mult a u h k' /
      (2 ^ (a + 1) : ℚ) ^ mult a u h k').prod =
        (l.map fun k' => X k' ^ mult a u h k').prod /
          (2 ^ (a + 1) : ℚ) ^ (l.map (mult a u h)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih => rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons,
        List.map_cons, List.sum_cons, div_mul_div_comm, ← pow_add]
  rw [List.map_congr_left hfac, hprod, gamma, Subring.coe_mul, Subring.coe_mul, Subring.coe_pow,
    Subring.coe_natCast, Subring.coe_intCast]
  have hlist : ((((others a k).map fun k' : ℕ =>
      (((((2 ^ a : ℕ) : ℤ) - (k' : ℤ) : ℤ) : ℤ₍₂₎) * slope' a k k') ^ mult a u h k').prod :
        ℤ₍₂₎) : ℚ) = ((others a k).map fun k' => X k' ^ mult a u h k').prod := by
    refine (map_list_prod (ℤ₍₂₎).subtype _).trans ?_
    rw [List.map_map]
    rfl
  rw [hlist, ← multSum]
  have h2 : (2 : ℚ) ^ Δ = 2 ^ (Δ - (a + 1) * (multSum a u h k + j)) *
      ((2 : ℚ) ^ (a + 1)) ^ (multSum a u h k + j) := by
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hΔ]
  rw [h2, show (-(node a k : ℚ)) = ((Int.cast (((2 ^ a : ℕ) : ℤ) - (k : ℤ))) : ℚ) by
    simp only [node]; push_cast; ring, div_pow, pow_add]
  field_simp
  push_cast
  ring

/-! ### Precision -/

theorem node_mem_recoveryNodes {a k : ℕ} (hk : k < 2 ^ (a + 1)) (hkL : k ≠ 2 ^ a) :
    node a k ∈ recoveryNodes a := by
  rw [recoveryNodes_eq_image]
  exact mem_image_of_mem _ (mem_filter.mpr ⟨mem_range.mpr hk, hkL⟩)

/-- **The multipliers kill the input error.** If `p + 6 h D_t + q_t (a + 1) ≤ p_t`, the
multiplier of every coefficient below `z ^ q_t` is divisible by `2 ^ (N - p_t)` in `ℤ_(2)`,
`N = p + Δ`, so it annihilates `2 ^ p_t` in `A_N`. -/
theorem gamma_mul_two_pow_eq_zero (ρ : ℤ₍₂₎ →+* Ring N fl) {a u h Δ p pt k j : ℕ}
    (hk : k < 2 ^ (a + 1)) (hkL : k ≠ 2 ^ a) (hj : j < mult a u h k)
    (hΔ : (a + 1) * (multSum a u h k + j) ≤ Δ)
    (hpt : p + 6 * h * 2 ^ (a - padicValInt 2 (node a k)) + mult a u h k * (a + 1) ≤ pt)
    (hN : N = p + Δ) : ρ (gamma a u h Δ k j) * 2 ^ pt = 0 := by
  rcases le_or_gt N pt with hle | hlt
  · rw [show (2 : Ring N fl) ^ pt = ((2 ^ pt : ℕ) : Ring N fl) by push_cast; rfl,
      ← Nat.sub_add_cancel hle, pow_add, Nat.cast_mul, natCast_two_pow, mul_zero, mul_zero]
  set e := N - pt
  have ht := node_mem_recoveryNodes hk hkL
  set E0 := (hermiteBasis (recoveryNodes a) (fun q : ℤ => (q : ℚ)) (taperMult u h)
    (node a k)).eval 0
  have hE0 : E0 ≠ 0 := eval_zero_hermiteBasis_ne_zero a u h
  have ht0 : (node a k : ℚ) ≠ 0 := by exact_mod_cast ne_of_mem_erase ht
  have hx0 : (-(node a k : ℚ) / 2 ^ (a + 1)) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr ht0) (by positivity)
  have hγ := coe_gamma (u := u) (h := h) hk hΔ
  have hγ0 : ((gamma a u h Δ k j : ℤ₍₂₎) : ℚ) ≠ 0 := by
    rw [hγ]; exact mul_ne_zero (mul_ne_zero (by positivity) hE0) (pow_ne_zero _ hx0)
  -- The valuation of the multiplier is at least `e`.
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by exact_mod_cast padicValRat.self (p := 2) one_lt_two
  have hvE : -(6 * (h : ℤ) * 2 ^ (a - padicValInt 2 (node a k))) ≤ padicValRat 2 E0 := by
    have := neg_le_padicValRat_eval_zero_hermiteBasis_taper (a := a) u h
      (mem_of_mem_erase (by rw [← recoveryNodes_eq]; exact ht)) (ne_of_mem_erase ht)
    rw [← recoveryNodes_eq] at this
    exact this
  have hvx : -((a : ℤ) + 1) ≤ padicValRat 2 (-(node a k : ℚ) / 2 ^ (a + 1)) := by
    rw [padicValRat.div (neg_ne_zero.mpr ht0) (by positivity), padicValRat.neg,
      padicValRat.of_int, padicValRat.pow, h2]
    push_cast
    omega
  have hv : (e : ℤ) ≤ padicValRat 2 ((gamma a u h Δ k j : ℤ₍₂₎) : ℚ) := by
    rw [hγ, padicValRat.mul (mul_ne_zero (by positivity) hE0) (pow_ne_zero _ hx0),
      padicValRat.mul (by positivity) hE0, padicValRat.pow, padicValRat.pow, h2]
    have hjv : (j : ℤ) * padicValRat 2 (-(node a k : ℚ) / 2 ^ (a + 1)) ≥
        -((mult a u h k : ℤ) * ((a : ℤ) + 1)) := by
      have : (j : ℤ) ≤ mult a u h k := by exact_mod_cast hj.le
      nlinarith
    have hpt' : (p : ℤ) + 6 * h * 2 ^ (a - padicValInt 2 (node a k)) +
        (mult a u h k : ℤ) * (a + 1) ≤ pt := by exact_mod_cast hpt
    have he : (e : ℤ) = N - pt := by omega
    rw [he, hN]
    push_cast
    linarith
  -- So `γ = 2 ^ e γ'` with `γ' ∈ ℤ_(2)`.
  have hmem : ((gamma a u h Δ k j : ℤ₍₂₎) : ℚ) / 2 ^ e ∈ ℤ₍₂₎ := by
    have hne : ((gamma a u h Δ k j : ℤ₍₂₎) : ℚ) / 2 ^ e ≠ 0 := div_ne_zero hγ0 (by positivity)
    have hval : 0 ≤ padicValRat 2 (((gamma a u h Δ k j : ℤ₍₂₎) : ℚ) / 2 ^ e) := by
      rw [padicValRat.div hγ0 (by positivity), padicValRat.pow, h2]
      omega
    change Rat.padicValuation 2 _ ≤ 1
    simp only [Rat.padicValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      hne, ↓reduceIte]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hsplit : gamma a u h Δ k j = ((2 ^ e : ℕ) : ℤ₍₂₎) * ⟨_, hmem⟩ := by
    apply Subtype.val_injective
    simp only [Subring.coe_mul, Subring.coe_natCast]
    push_cast
    field_simp
  rw [hsplit, map_mul, map_natCast, mul_comm, ← mul_assoc,
    show (2 : Ring N fl) ^ pt = ((2 ^ pt : ℕ) : Ring N fl) by push_cast; rfl, ← Nat.cast_mul,
    ← pow_add, show pt + e = N by omega, natCast_two_pow, zero_mul]

end Cslib.Circuits.Frontier.NativeRecovery

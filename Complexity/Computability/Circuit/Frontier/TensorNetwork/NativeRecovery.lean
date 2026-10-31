/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ActiveCall
public import Complexity.Computability.PolyTime.GaloisRingSeries

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

## Main definitions

* `Cslib.Circuits.Frontier.NativeRecovery.slopeConst`: the constant `α / (t - q)`.
* `Cslib.Circuits.Frontier.NativeRecovery.recip`: the truncated reciprocal of `E_t(t + α z)`.
* `Cslib.Circuits.Frontier.NativeRecovery.coeffMult`: the multipliers.
* `Cslib.Circuits.Frontier.NativeRecovery.recover`: native tapered recovery.

## Main results

* `Cslib.Circuits.Frontier.NativeRecovery.val_slopeConst`: the constant is correct.

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

/-- The multiplicity `q_t = h (u - v₂ t)` of the node of index `k`. -/
def mult (a u h k : ℕ) : ℕ := h * (u - padicValNat 2 (k - 2 ^ a + (2 ^ a - k)))

theorem mult_eq (a u h k : ℕ) : mult a u h k = taperMult u h (node a k) := by
  have : ((k : ℤ) - 2 ^ a).natAbs = k - 2 ^ a + (2 ^ a - k) := by
    rw [show (2 : ℤ) ^ a = ((2 ^ a : ℕ) : ℤ) by push_cast; rfl]
    omega
  rw [mult, taperMult, node, padicValInt, this]

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
  let v := padicValNat 2 d
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
  unfold slopeConst
  split_ifs with h
  · rw [val_neg, hw, map_neg, map_natCast, neg_mul]
  · rw [hw, map_natCast]

end Cslib.Circuits.Frontier.NativeRecovery

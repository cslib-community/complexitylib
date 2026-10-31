/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ActiveCall
public import Complexity.Computability.PolyTime.GaloisRingSeries
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Mathlib.Data.List.GetD

/-!
# Native tapered recovery (Lemma D.5) on coefficient lists

This file gives the native procedure behind the recovery step of the contraction algorithm of
[OpenAI2026ETH] (§D.4.4, Lemma D.5, pp. 60–61), and proves that it computes the mathematical
recovery `Cslib.Circuits.Frontier.recoverFromValues` of
`Complexity/Computability/Circuit/Frontier/TensorNetwork/ActiveCall.lean` modulo `2 ^ p`.

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

**Correctness.** Let `π : B → A_N` be a ring homomorphism from a subring `B ⊇ ℤ_(2)` of a
`ℚ`-algebra `K` (in the manuscript, `B = O`). The native interpolant is the image of the
interpolant over `B` modulo `2 ^ p_t` (`NativeRecovery.exists_pval_interp_eq_add`), the Hermite
quotient over `K` of a polynomial over `B` is the image of its product with the reciprocal series
(`NativeRecovery.hermiteQuotient_map_subtype`), and `2 ^ Δ` times the recovered value is the sum
of the node contributions over `B` (`NativeRecovery.two_pow_mul_recoverFromValues`). So when the
recovered value `recoverFromValues B a u h ζ v` lies in `B`, native recovery computes its image
modulo `2 ^ p` (`NativeRecovery.val_recover`).

**Polynomial time.** Every loop is a fold over a range or over the other node indices, so native
recovery is polynomial-time with the precision, the shift, the parameters and `2 ^ a` in unary
(`NativeRecovery.computableInPolyTime_recover`).

## Main definitions

* `Cslib.Circuits.Frontier.NativeRecovery.slopeConst`: the constant `α / (t - q)`.
* `Cslib.Circuits.Frontier.NativeRecovery.recip`: the truncated reciprocal of `E_t(t + α z)`.
* `Cslib.Circuits.Frontier.NativeRecovery.coeffMult`: the multipliers.
* `Cslib.Circuits.Frontier.NativeRecovery.recover`: native tapered recovery.
* `Cslib.Circuits.Frontier.NativeRecovery.storeValue`: storing a value in the table that `recover`
  reads, the accumulator update of a recursive call.
* `Cslib.Circuits.Frontier.NativeRecovery.recipSeries`,
  `Cslib.Circuits.Frontier.NativeRecovery.gamma`: the reciprocal and the multipliers over
  `ℤ_(2)`.
* `Cslib.Circuits.Frontier.NativeRecovery.nodeSum`: the contribution of a node over `B`.

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
* `Cslib.Circuits.Frontier.NativeRecovery.exists_pval_interp_eq_add`: the interpolation bridge.
* `Cslib.Circuits.Frontier.NativeRecovery.invOfUnit_hermiteBasis_comp`,
  `Cslib.Circuits.Frontier.NativeRecovery.hermiteQuotient_map_subtype`: the reciprocal series
  inverts `E_t(t + α z)`, so the Hermite quotient of a polynomial over `B` is integral.
* `Cslib.Circuits.Frontier.NativeRecovery.two_pow_mul_recoverFromValues`: `2 ^ Δ` times the
  recovered value as a sum over `B`.
* `Cslib.Circuits.Frontier.NativeRecovery.val_recover`,
  `Cslib.Circuits.Frontier.NativeRecovery.val_recover_of_eq_add`: native recovery computes the
  mathematical recovery modulo `2 ^ p`.
* `Cslib.Circuits.Frontier.NativeRecovery.computableInPolyTime_recover`: native recovery is
  polynomial-time.
* `Cslib.Circuits.Frontier.NativeRecovery.getD_foldl_storeValue`,
  `Cslib.Circuits.Frontier.NativeRecovery.computableInPolyTime_storeValue`: storing a sequence of
  values gives each node index its values in order, in polynomial time.

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

/-- The `2`-adic valuation of `d`, capped at `b`: the number of `i < b` with `2 ^ (i + 1) ∣ d`,
and `0` for `d = 0`. It is `v₂ d` when `d < 2 ^ b` (`NativeRecovery.twoVal_eq`). -/
def twoVal (b d : ℕ) : ℕ :=
  if d = 0 then 0 else ((List.range b).filter fun i => d % 2 ^ (i + 1) = 0).length

theorem twoVal_eq {b d : ℕ} (hd : d < 2 ^ b) : twoVal b d = padicValNat 2 d := by
  rw [twoVal]
  split_ifs with h0
  · simp [h0]
  set v := padicValNat 2 d
  have hvb : v < b := by
    have : 2 ^ v ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) pow_padicValNat_dvd
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (this.trans_lt hd)
  have key (m : ℕ) : ((List.range m).filter fun i => d % 2 ^ (i + 1) = 0).length = min m v := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.filter_append, List.length_append, ih]
      have hiff : d % 2 ^ (m + 1) = 0 ↔ m + 1 ≤ v := by
        rw [← Nat.dvd_iff_mod_eq_zero]
        exact padicValNat_dvd_iff_le h0
      rw [List.filter_singleton]
      by_cases hm : m + 1 ≤ v
      · rw [decide_eq_true (hiff.mpr hm), Bool.cond_true, List.length_singleton]
        omega
      · rw [decide_eq_false (mt hiff.mp hm), Bool.cond_false, List.length_nil]
        omega
  rw [key, min_eq_right hvb.le]

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

/-! ### Storing the values -/

/-- Store the value `y` at node index `k`, after the values already stored there. This is the
accumulator update of a recursive call once the value at an interpolation point is complete;
`NativeRecovery.recover` reads the table. -/
def storeValue (W : List (List (List ℕ))) (k : ℕ) (y : List ℕ) : List (List (List ℕ)) :=
  (List.range (max W.length (k + 1))).map fun k' =>
    if k' = k then W.getD k' [] ++ [y] else W.getD k' []

theorem getD_storeValue (W : List (List (List ℕ))) (k : ℕ) (y : List ℕ) (k' : ℕ) :
    (storeValue W k y).getD k' [] = if k' = k then W.getD k [] ++ [y] else W.getD k' [] := by
  unfold storeValue
  by_cases hk' : k' < max W.length (k + 1)
  · rw [List.getD_eq_getElem _ _ (by simpa using hk'), List.getElem_map, List.getElem_range]
    split_ifs with h
    · rw [h]
    · rfl
  · have hne : k' ≠ k := by omega
    rw [List.getD_eq_default _ _ (by rw [List.length_map, List.length_range]; omega),
      ite_eq_right_of_eq_false _ _ (eq_false hne), List.getD_eq_default _ _ (by omega)]

/-- **Storing a sequence of values**: each node index receives its values in order. -/
theorem getD_foldl_storeValue (W : List (List (List ℕ))) (l : List (ℕ × List ℕ)) (k : ℕ) :
    (l.foldl (fun W e => storeValue W e.1 e.2) W).getD k [] =
      W.getD k [] ++ (l.filter fun e => e.1 = k).map Prod.snd := by
  induction l generalizing W with
  | nil => simp
  | cons e l ih =>
    rw [List.foldl_cons, ih, getD_storeValue, List.filter_cons]
    by_cases h : e.1 = k
    · simp [h]
    · simp [h, Ne.symm h]

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
@[to_additive /-- The other nodes, as integers, are the nonzero grid points other than `t`. -/]
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

/-! ### The interpolation bridge -/

/-- The coefficients of a polynomial over `A_N` given by a list of coefficient lists. -/
theorem coeff_pval (P : List (List ℕ)) (l : ℕ) :
    (pval N fl P).coeff l = val N fl (P.getD l []) := by
  rw [pval, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_range]
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (by omega), val_nil]

/-- Interpolation at `n` nodes has degree below `n`. -/
theorem degree_pval_interp_lt (ζl w : List (List ℕ)) :
    (pval N fl (interp N fl ζl w)).degree < ζl.length := by
  rw [← mem_degreeLT, pval_interp]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [← smul_eq_C_mul]
  refine Submodule.smul_mem _ _ (mem_degreeLT.mpr ((degree_le_natDegree).trans_lt ?_))
  have hle : (∏ j ∈ (range ζl.length).erase i, (X - C (val N fl (ζl.getD j [])))).natDegree ≤
      #((range ζl.length).erase i) :=
    (natDegree_prod_le _ _).trans ((sum_le_sum fun j _ => natDegree_X_sub_C_le _).trans_eq
      (card_eq_sum_ones _).symm)
  rw [card_erase_of_mem hi, card_range] at hle
  have := mem_range.mp hi
  exact_mod_cast (show _ < ζl.length by omega)

/-- **The interpolation bridge.** Let `π : B → A_N` be a ring homomorphism, and let the native
nodes `ζl` represent the images of nodes `ζ i ∈ B` with unit differences. If the native values
`w` agree with the images of `r i ∈ B` modulo `2 ^ e`, then the native interpolant agrees with the
image of the interpolant of `r` over `B` modulo `2 ^ e`. -/
theorem exists_pval_interp_eq_add (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2))))
    {B : Type*} [CommRing B] (π : B →+* Ring N fl) {n : ℕ} (ζ : Fin n → B)
    (hζ : Pairwise fun k l => IsUnit (ζ k - ζ l)) (ζl : List (List ℕ)) (hlen : ζl.length = n)
    (hζl : ∀ i : Fin n, val N fl (ζl.getD i []) = π (ζ i)) (r : Fin n → B)
    (w : List (List ℕ)) (e : ℕ)
    (hw : ∀ i : Fin n, ∃ c, val N fl (w.getD i []) = π (r i) + 2 ^ e * c) :
    ∃ g : (Ring N fl)[X],
      pval N fl (interp N fl ζl w) = (Lagrange.ringInterpolate univ ζ r).map π + C (2 ^ e) * g := by
  subst hlen
  have hvs : ((univ : Finset (Fin ζl.length)) : Set (Fin ζl.length)).Pairwise
      fun i j => IsUnit (π (ζ i) - π (ζ j)) := fun i _ j _ hij => by
    simp only
    rw [← map_sub]; exact (hζ hij).map π
  -- The native interpolant is the interpolant of the native values at the images of the nodes.
  have hinv : ∀ i < ζl.length, val N fl (basisDen N fl ζl i) *
      val N fl (inv N fl (basisDen N fl ζl i)) = 1 := fun i hi => by
    refine val_mul_inv_of_isUnit hirr ?_
    rw [val_basisDen, IsUnit.prod_iff]
    intro j hj
    have hj' := mem_range.mp (mem_of_mem_erase hj)
    rw [show i = ((⟨i, hi⟩ : Fin ζl.length) : ℕ) from rfl, hζl,
      show j = ((⟨j, hj'⟩ : Fin ζl.length) : ℕ) from rfl, hζl]
    exact hvs (mem_univ _) (mem_univ _) fun h => ne_of_mem_erase hj (congrArg Fin.val h).symm
  have hnat : pval N fl (interp N fl ζl w) =
      Lagrange.ringInterpolate univ (fun i => π (ζ i)) fun i => val N fl (w.getD i []) := by
    conv_lhs => rw [Lagrange.eq_ringInterpolate (f := pval N fl (interp N fl ζl w)) hvs (by
      rw [card_univ, Fintype.card_fin]; exact degree_pval_interp_lt ζl w)]
    congr 1
    funext i
    rw [← hζl, eval_pval_interp ζl w hinv i.2]
  -- The image of the interpolant over `B` takes the values `π (r i)`.
  have hdeg : ((Lagrange.ringInterpolate univ ζ r).map π).degree <
      #(univ : Finset (Fin ζl.length)) :=
    (degree_map_le).trans_lt (Lagrange.degree_ringInterpolate_lt r)
  obtain ⟨g, hg⟩ := Lagrange.exists_ringInterpolate_eq_add hvs hdeg (π := 2 ^ e)
    (r := fun i => val N fl (w.getD i [])) fun i _ => by
      obtain ⟨c, hc⟩ := hw i
      refine ⟨c, ?_⟩
      rw [hc, eval_map, eval₂_at_apply,
        Lagrange.eval_ringInterpolate_at_node (fun i _ j _ hij => hζ hij) r (mem_univ i)]
  exact ⟨g, hnat.trans hg⟩

/-! ### The Hermite quotient over `B` -/

/-- A fold of multiplications is a list product. -/
@[to_additive /-- A fold of additions is a list sum. -/]
theorem foldl_mul_eq {M ι : Type*} [CommMonoid M] (g : ι → M) (l : List ι) (c : M) :
    l.foldl (fun x y => x * g y) c = c * (l.map g).prod := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]

theorem map_geomSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : R) :
    PowerSeries.map f (geomSeries c) = geomSeries (f c) := by
  ext n
  simp [geomSeries, PowerSeries.coeff_map]

theorem coe_slope' {a k k' : ℕ} (hk : k < 2 ^ (a + 1)) (hk' : k' < 2 ^ (a + 1)) (hne : k' ≠ k) :
    ((slope' a k k' : ℤ₍₂₎) : ℚ) = 2 ^ (a + 1) / ((node a k : ℚ) - node a k') := by
  rw [slope', dite_eq_left_of_eq_true (eq_true ⟨hk, hk', hne⟩)]
  rfl

/-- Over `ℚ`, `E_t(t + α z)` times the reciprocal series is one. -/
theorem coe_hermiteBasis_comp_mul_recipSeries {a k : ℕ} (u h : ℕ) (hk : k < 2 ^ (a + 1)) :
    ((hermiteBasis (recoveryNodes a) (fun q : ℤ => (q : ℚ)) (taperMult u h) (node a k)).comp
        (C (node a k : ℚ) + C (2 ^ (a + 1)) * X) : PowerSeries ℚ) *
      PowerSeries.map (ℤ₍₂₎).subtype (recipSeries a u h k) = 1 := by
  rw [hermiteBasis_comp_rat, ← prod_others (fun q : ℤ =>
      (1 + C ((2 : ℚ) ^ (a + 1) / ((node a k : ℚ) - q)) * X) ^ taperMult u h q),
    recipSeries, foldl_mul_eq, one_mul, ← Polynomial.coeToPowerSeries.ringHom_apply, map_list_prod,
    map_list_prod, List.map_map, List.map_map, ← List.prod_map_mul]
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hx
  obtain ⟨hk'1, -, hk'3⟩ := mem_others.mp hk'
  simp only [Function.comp_apply, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_X, map_geomSeries, Subring.coe_subtype,
    coe_slope' hk hk'1 hk'3, ← mult_eq u h hk'1]
  rw [← mul_pow, one_add_mul_geomSeries, one_pow]

section Hermite

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- **The reciprocal series is the inverse of `E_t(t + α z)`** over every `ℚ`-algebra. -/
theorem invOfUnit_hermiteBasis_comp {a k : ℕ} (u h : ℕ) (hk : k < 2 ^ (a + 1))
    (hkL : k ≠ 2 ^ a) :
    PowerSeries.invOfUnit (((hermiteBasis (recoveryNodes a) (fun q : ℤ => (q : K))
        (taperMult u h) (node a k)).comp (C (node a k : K) + C (2 ^ (a + 1)) * X) : K[X]) :
          PowerSeries K) 1 =
      PowerSeries.map ((algebraMap ℚ K).comp (ℤ₍₂₎).subtype) (recipSeries a u h k) := by
  have ht := node_mem_recoveryNodes hk hkL
  set φ : PowerSeries K := (((hermiteBasis (recoveryNodes a) (fun q : ℤ => (q : K))
    (taperMult u h) (node a k)).comp (C (node a k : K) + C (2 ^ (a + 1)) * X) : K[X]) :
      PowerSeries K)
  have hv : (fun q : ℤ => algebraMap ℚ K (q : ℚ)) = fun q : ℤ => (q : K) :=
    funext fun q => map_intCast _ q
  have hlin : (C (node a k : ℚ) + C ((2 : ℚ) ^ (a + 1)) * X).map (algebraMap ℚ K) =
      C (node a k : K) + C (2 ^ (a + 1)) * X := by
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_X, map_intCast, map_pow, map_ofNat]
  have hφ : φ = PowerSeries.map (algebraMap ℚ K)
      (((hermiteBasis (recoveryNodes a) (fun q : ℤ => (q : ℚ)) (taperMult u h) (node a k)).comp
        (C (node a k : ℚ) + C (2 ^ (a + 1)) * X) : ℚ[X]) : PowerSeries ℚ) := by
    rw [← Polynomial.polynomial_map_coe, Polynomial.map_comp,
      map_hermiteBasis _ (pairwise_isUnit_sub _) ht, hv, hlin]
  have h1 : φ * PowerSeries.invOfUnit φ 1 = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by
      rw [Polynomial.constantCoeff_coe, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_C,
        eval_mul, eval_C, eval_X, mul_zero, add_zero,
        eval_hermiteBasis_self (pairwise_isUnit_sub _) ht, Units.val_one])
  have h2 : φ * PowerSeries.map ((algebraMap ℚ K).comp (ℤ₍₂₎).subtype) (recipSeries a u h k) =
      1 := by
    rw [hφ, PowerSeries.map_comp, RingHom.comp_apply, ← map_mul,
      coe_hermiteBasis_comp_mul_recipSeries u h hk, map_one]
  calc PowerSeries.invOfUnit φ 1
      = PowerSeries.invOfUnit φ 1 * (φ * PowerSeries.map ((algebraMap ℚ K).comp (ℤ₍₂₎).subtype)
          (recipSeries a u h k)) := by rw [h2, mul_one]
    _ = _ := by rw [← mul_assoc, mul_comm _ φ, h1, one_mul]

/-- **The Hermite quotient over `B`.** For a polynomial `P` over `B`, the Hermite quotient over
`K` at the node of index `k` is the image of the truncation below `z ^ q_t` of the product of `P`
with the reciprocal series. -/
theorem hermiteQuotient_map_subtype (B : Subring K) (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B)
    {a k : ℕ} (u h : ℕ) (hk : k < 2 ^ (a + 1)) (hkL : k ≠ 2 ^ a) (P : B[X]) :
    hermiteQuotient (recoveryNodes a) (fun q : ℤ => (q : K)) (taperMult u h) (2 ^ (a + 1))
        (node a k) ((P.map B.subtype : K[X]) : PowerSeries K) =
      (PowerSeries.trunc (mult a u h k) ((P : PowerSeries B) *
        PowerSeries.map (integerHom B hB) (recipSeries a u h k))).map B.subtype := by
  rw [hermiteQuotient, invOfUnit_hermiteBasis_comp u h hk hkL, ← subtype_comp_integerHom B hB,
    PowerSeries.map_comp, RingHom.comp_apply, Polynomial.polynomial_map_coe, ← map_mul,
    PowerSeries.trunc_map, mult_eq u h hk]

/-! ### Assembly -/

/-- The contribution of the node of index `k` to `2 ^ Δ` times the recovered value, over `B`:
`∑_{j < q_t} γ_{t,j} c_j`, where `c_j` is the coefficient of `z ^ j` in the product of `P` with
the reciprocal series and `γ_{t,j} = 2 ^ Δ E_t(0) (-t / α) ^ j` (`NativeRecovery.gamma`). -/
noncomputable def nodeSum (B : Subring K) (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B)
    (a u h Δ k : ℕ) (P : B[X]) : B :=
  ∑ j ∈ range (mult a u h k), integerHom B hB (gamma a u h Δ k j) *
    PowerSeries.coeff j ((P : PowerSeries B) *
      PowerSeries.map (integerHom B hB) (recipSeries a u h k))

theorem multSum_add_mult {a k : ℕ} (u h : ℕ) (hk : k < 2 ^ (a + 1)) (hkL : k ≠ 2 ^ a) :
    multSum a u h k + mult a u h k = ∑ t ∈ recoveryNodes a, taperMult u h t := by
  rw [multSum, List.map_congr_left (g := fun k' => taperMult u h (node a k'))
      fun k' hk' => mult_eq u h (mem_others.mp hk').1,
    sum_others (fun q => taperMult u h q), mult_eq u h hk,
    sum_erase_add _ _ (node_mem_recoveryNodes hk hkL)]

theorem le_of_lt_mult {a u h Δ k j : ℕ} (hk : k < 2 ^ (a + 1)) (hkL : k ≠ 2 ^ a)
    (hj : j < mult a u h k) (hΔ : (a + 1) * ∑ t ∈ recoveryNodes a, taperMult u h t ≤ Δ) :
    (a + 1) * (multSum a u h k + j) ≤ Δ :=
  (Nat.mul_le_mul_left _ (by rw [← multSum_add_mult u h hk hkL]; omega)).trans hΔ

/-- **`2 ^ Δ` times the recovered value lies in `B`**, as the sum of the node contributions
`NativeRecovery.nodeSum`, once `Δ ≥ (a + 1) ∑_t q_t`. -/
theorem two_pow_mul_recoverFromValues (B : Subring K) (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B)
    {a u h Δ : ℕ} (hΔ : (a + 1) * ∑ t ∈ recoveryNodes a, taperMult u h t ≤ Δ) {n : ℕ}
    (ζ : Fin n → B) (v : ℤ → Fin n → B) :
    2 ^ Δ * recoverFromValues B a u h ζ v =
      ((∑ k ∈ range (2 ^ (a + 1)), if k = 2 ^ a then 0 else
        nodeSum B hB a u h Δ k (Lagrange.ringInterpolate univ ζ (v (node a k))) : B) : K) := by
  rw [recoverFromValues_def, taperedRecovery_def, sum_recoveryNodes, mul_sum,
    AddSubmonoidClass.coe_finsetSum]
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  split_ifs with hkL
  · simp
  rw [hermiteQuotient_map_subtype B hB u h hk' hkL, eval_map,
    PowerSeries.eval₂_trunc_eq_sum_range, eval_zero_hermiteBasis_eq a u h
      (node_mem_recoveryNodes hk' hkL), nodeSum, AddSubmonoidClass.coe_finsetSum, mul_sum,
    mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hγ := coe_gamma (u := u) (h := h) hk' (le_of_lt_mult hk' hkL (mem_range.mp hj) hΔ)
  have hint : ((integerHom B hB (gamma a u h Δ k j) : B) : K) =
      algebraMap ℚ K ((gamma a u h Δ k j : ℤ₍₂₎) : ℚ) := rfl
  rw [Subring.coe_mul, hint, hγ, Subring.coe_subtype]
  simp only [map_mul, map_pow, map_ofNat]
  ring

/-- A fold that adds a term at each index of a range sums the terms. -/
theorem val_foldl_range (F : List ℕ → ℕ → List ℕ) (g : ℕ → Ring N fl)
    (hF : ∀ S k, val N fl (F S k) = val N fl S + g k) (c : List ℕ) (m : ℕ) :
    val N fl ((List.range m).foldl F c) = val N fl c + ∑ k ∈ range m, g k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hF, ih,
      sum_range_succ, add_assoc]

/-- **The native contribution of a node is correct**: if the native values agree with the
images of `r i` modulo `2 ^ p_t`, where `p + 6 h D_t + q_t (a + 1) ≤ p_t`, then the native
contribution of the node of index `k` is the image of `NativeRecovery.nodeSum`. -/
theorem val_nodeTerm (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2))))
    (B : Subring K) (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B) (π : B →+* Ring N fl)
    {p a u h Δ pt k : ℕ} (hk : k < 2 ^ (a + 1)) (hkL : k ≠ 2 ^ a)
    (hΔ : (a + 1) * ∑ t ∈ recoveryNodes a, taperMult u h t ≤ Δ) (hN : N = p + Δ)
    (hpt : 0 < mult a u h k →
      p + 6 * h * 2 ^ (a - padicValInt 2 (node a k)) + mult a u h k * (a + 1) ≤ pt)
    {n : ℕ} (ζ : Fin n → B) (hζ : Pairwise fun k l => IsUnit (ζ k - ζ l))
    (ζl : List (List ℕ)) (hlen : ζl.length = n)
    (hζl : ∀ i : Fin n, val N fl (ζl.getD i []) = π (ζ i)) (r : Fin n → B) (w : List (List ℕ))
    (hw : 0 < mult a u h k → ∀ i : Fin n, ∃ c, val N fl (w.getD i []) = π (r i) + 2 ^ pt * c) :
    val N fl (nodeTerm N fl a u h Δ ζl k w) =
      π (nodeSum B hB a u h Δ k (Lagrange.ringInterpolate univ ζ r)) := by
  rcases Nat.eq_zero_or_pos (mult a u h k) with h0 | hpos
  · simp [nodeTerm, nodeSum, h0]
  obtain ⟨g, hg⟩ := exists_pval_interp_eq_add hirr π ζ hζ ζl hlen hζl r w pt (hw hpos)
  set ρ := π.comp (integerHom B hB)
  set P := Lagrange.ringInterpolate univ ζ r
  rw [nodeTerm, val_foldl_range _ (fun j => val N fl (coeffMult N fl a u h Δ k j) *
      val N fl ((tmul N fl (mult a u h k) (interp N fl ζl w)
        (recip N fl a u h k (mult a u h k))).getD j []))
      (fun S j => by rw [val_add, val_mul]), val_zero, zero_add, nodeSum, map_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.mp hj
  have hcoef : ∀ l, val N fl ((interp N fl ζl w).getD l []) = π (P.coeff l) + 2 ^ pt * g.coeff l :=
    fun l => by rw [← coeff_pval, hg, coeff_add, coeff_map, coeff_C_mul]
  have hconv : π (PowerSeries.coeff j ((P : PowerSeries B) *
      PowerSeries.map (integerHom B hB) (recipSeries a u h k))) =
        ∑ l ∈ range (j + 1),
          π (P.coeff l) * ρ (PowerSeries.coeff (j - l) (recipSeries a u h k)) := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun l m =>
      PowerSeries.coeff l (P : PowerSeries B) *
        PowerSeries.coeff m (PowerSeries.map (integerHom B hB) (recipSeries a u h k))), map_sum]
    refine sum_congr rfl fun l _ => ?_
    rw [Polynomial.coeff_coe, PowerSeries.coeff_map, map_mul]
    rfl
  have hkill : ρ (gamma a u h Δ k j) * 2 ^ pt = 0 :=
    gamma_mul_two_pow_eq_zero ρ hk hkL hj' (le_of_lt_mult hk hkL hj' hΔ) (hpt hpos) hN
  rw [val_coeffMult hirr ρ hk j, val_tmul _ _ hj', map_mul, hconv,
    sum_congr rfl fun l hl => by
      rw [hcoef l, val_recip hirr ρ hk (show j - l < mult a u h k by omega)]]
  simp only [add_mul, sum_add_distrib, mul_add, mul_assoc]
  rw [← mul_sum, ← mul_assoc, hkill, zero_mul, add_zero]
  rfl


/-- **Native recovery computes the mathematical recovery modulo `2 ^ p`.** Let `π : B → A_N`,
`N = p + Δ`, be a ring homomorphism, with `Δ ≥ (a + 1) ∑_t q_t`. Let the native points `ζl`
represent the images of points `ζ i ∈ B` with unit differences, and at every node index `k` of
positive multiplicity let the native values `W.getD k []` agree with the images of the values
`v t i` at `t = node a k` modulo `2 ^ p_t`, where `p + 6 h D_t + q_t (a + 1) ≤ p_t`. If the
recovered value `recoverFromValues B a u h ζ v` is an element `R` of `B`, then native recovery
computes the reduction of `π R` modulo `2 ^ p`. -/
theorem val_recover (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2))))
    (B : Subring K) (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B) {p Δ : ℕ}
    (π : B →+* Ring (p + Δ) fl) {a u h : ℕ}
    (hΔ : (a + 1) * ∑ t ∈ recoveryNodes a, taperMult u h t ≤ Δ) (pt : ℤ → ℕ)
    (hpt : ∀ t ∈ recoveryNodes a, 0 < taperMult u h t →
      p + 6 * h * 2 ^ (a - padicValInt 2 t) + taperMult u h t * (a + 1) ≤ pt t)
    {n : ℕ} (ζ : Fin n → B) (hζ : Pairwise fun k l => IsUnit (ζ k - ζ l))
    (ζl : List (List ℕ)) (hlen : ζl.length = n)
    (hζl : ∀ i : Fin n, val (p + Δ) fl (ζl.getD i []) = π (ζ i)) (v : ℤ → Fin n → B)
    (W : List (List (List ℕ)))
    (hW : ∀ k < 2 ^ (a + 1), k ≠ 2 ^ a → 0 < mult a u h k → ∀ i : Fin n, ∃ c,
      val (p + Δ) fl ((W.getD k []).getD i []) = π (v (node a k) i) + 2 ^ pt (node a k) * c)
    {R : B} (hR : recoverFromValues B a u h ζ v = R) :
    val p fl (recover p Δ fl a u h ζl W) = reduce (Nat.le_add_right p Δ) fl (π R) := by
  refine val_shiftDown ?_
  have hsum := two_pow_mul_recoverFromValues B hB hΔ ζ v
  rw [hR] at hsum
  have hsum' : (2 : B) ^ Δ * R = _ := Subtype.val_injective (by push_cast; exact hsum)
  rw [← map_ofNat π, ← map_pow, ← map_mul, hsum',
    val_foldl_range _ (fun k => if k = 2 ^ a then 0 else
      val (p + Δ) fl (nodeTerm (p + Δ) fl a u h Δ ζl k (W.getD k []))) (fun S k => by
        split_ifs <;> simp [val_add]), val_zero, zero_add, map_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  split_ifs with hkL
  · rw [map_zero]
  have ht := node_mem_recoveryNodes hk' hkL
  exact val_nodeTerm hirr B hB π hk' hkL hΔ rfl
    (fun hq => by rw [mult_eq u h hk'] at hq ⊢; exact hpt _ ht hq) ζ hζ ζl hlen hζl _ _
    (hW k hk' hkL)

/-- **Native recovery is correct modulo `2 ^ p`.** Under the hypotheses of
`NativeRecovery.val_recover`, if the recovered value agrees with an element `x` of `B` modulo
`2 ^ p` (as `TensorNetwork.exists_recoverFromValues_eq_add_of_children` gives for the
contraction), then native recovery computes the reduction of `π x` modulo `2 ^ p`. -/
theorem val_recover_of_eq_add
    (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2))))
    (B : Subring K) (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B) {p Δ : ℕ}
    (π : B →+* Ring (p + Δ) fl) {a u h : ℕ}
    (hΔ : (a + 1) * ∑ t ∈ recoveryNodes a, taperMult u h t ≤ Δ) (pt : ℤ → ℕ)
    (hpt : ∀ t ∈ recoveryNodes a, 0 < taperMult u h t →
      p + 6 * h * 2 ^ (a - padicValInt 2 t) + taperMult u h t * (a + 1) ≤ pt t)
    {n : ℕ} (ζ : Fin n → B) (hζ : Pairwise fun k l => IsUnit (ζ k - ζ l))
    (ζl : List (List ℕ)) (hlen : ζl.length = n)
    (hζl : ∀ i : Fin n, val (p + Δ) fl (ζl.getD i []) = π (ζ i)) (v : ℤ → Fin n → B)
    (W : List (List (List ℕ)))
    (hW : ∀ k < 2 ^ (a + 1), k ≠ 2 ^ a → 0 < mult a u h k → ∀ i : Fin n, ∃ c,
      val (p + Δ) fl ((W.getD k []).getD i []) = π (v (node a k) i) + 2 ^ pt (node a k) * c)
    (x : B) {b : K} (hb : b ∈ B) (hx : recoverFromValues B a u h ζ v = (x : K) + 2 ^ p * b) :
    val p fl (recover p Δ fl a u h ζl W) = reduce (Nat.le_add_right p Δ) fl (π x) := by
  rw [val_recover hirr B hB π hΔ pt hpt ζ hζ ζl hlen hζl v W hW (R := x + 2 ^ p * ⟨b, hb⟩)
    (by rw [hx]; rfl), map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_ofNat,
    map_ofNat, show (2 : Ring p fl) ^ p = ((2 ^ p : ℕ) : Ring p fl) by push_cast; rfl,
    natCast_two_pow, zero_mul, add_zero]

end Hermite

/-! ### Polynomial time -/

section PolyTime

open Turing.MultiTapeTM

variable {α : Type} {encIn : α ↪ List Bool}

private theorem lengthPolyTime {β : Type} {encB : β ↪ List Bool} {l : α → List β}
    (hl : ComputableInPolyTime l encIn (encList encB)) :
    ComputableInPolyTime (fun x => (l x).length) encIn encUnary :=
  (ComputableInPolyTime.length_list encB).comp hl

private theorem getDPolyTime {P : α → List (List ℕ)} {k : α → ℕ}
    (hP : ComputableInPolyTime P encIn (encList (encList encNat)))
    (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun x => (P x).getD (k x) []) encIn (encList encNat) :=
  (ComputableInPolyTime.listGetD (encA := encList encNat) []).comp (hP.prod hk)

/-- A unary natural as a one-coordinate list. -/
private theorem singletonPolyTime {n : α → ℕ} (hn : ComputableInPolyTime n encIn encNat) :
    ComputableInPolyTime (fun x => [n x]) encIn (encList encNat) :=
  ComputableInPolyTime.cons' hn (ComputableInPolyTime.const [])

/-- A coefficient list as a one-element list. -/
private theorem singletonPolyTime' {c : α → List ℕ}
    (hc : ComputableInPolyTime c encIn (encList encNat)) :
    ComputableInPolyTime (fun x => [c x]) encIn (encList (encList encNat)) :=
  ComputableInPolyTime.cons' hc (ComputableInPolyTime.const [])

private theorem polyBounded_unary {n : α → ℕ} (hn : ComputableInPolyTime n encIn encUnary) :
    PolyBounded (fun x => (encIn x).length) n := by
  simpa using ComputableInPolyTime.polyBounded_length hn

/-- The length of a polynomial with `J` small coefficients is polynomially bounded. -/
private theorem polyBounded_polyLength {p J : α → ℕ} {fl : α → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hJ : ComputableInPolyTime J encIn encUnary) :
    PolyBounded (fun x => (encIn x).length)
      (fun x => J x * (2 * ((fl x).length * (2 * (p x + 1) + 1)) + 1)) := by
  have hpl := polyBounded_unary hp
  have hfll : PolyBounded (fun x => (encIn x).length) fun x => (fl x).length :=
    (lengthPolyTime hfl).polyBounded_length.mono fun x => by simp
  exact (polyBounded_unary hJ).mul (((PolyBounded.const 2).mul (hfll.mul (((PolyBounded.const 2).mul
    (hpl.add (PolyBounded.const 1))).add (PolyBounded.const 1)))).add (PolyBounded.const 1))

private theorem length_encList_mul_le (N : ℕ) (fl c d : List ℕ) :
    (encList encNat (mul N fl c d)).length ≤ fl.length * (2 * N + 1) :=
  length_encList_le (length_mul N fl c d) fun _ h => lt_of_mem_mul h

private theorem length_encList_add_le (N : ℕ) (fl c d : List ℕ) :
    (encList encNat (add N fl c d)).length ≤ fl.length * (2 * N + 1) :=
  length_encList_le (length_add N fl c d) fun _ h => lt_of_mem_add h

/-- **The capped `2`-adic valuation is polynomial-time**, in unary. -/
@[fun_prop]
theorem computableInPolyTime_twoVal {b d : α → ℕ} (hb : ComputableInPolyTime b encIn encUnary)
    (hd : ComputableInPolyTime d encIn encUnary) :
    ComputableInPolyTime (fun x => twoVal (b x) (d x)) encIn encUnary := by
  have h1 := ComputableInPolyTime.fst encIn encUnary
  have h2 := ComputableInPolyTime.snd encIn encUnary
  have htest : ComputableInPolyTime (fun q : α × ℕ => d q.1 % 2 ^ (q.2 + 1) == 0)
      (encPair encIn encUnary) encBool :=
    ComputableInPolyTime.beq (ComputableInPolyTime.binary_mod.comp
      ((ComputableInPolyTime.unary_to_binary.comp (hd.comp h1)).prod
        (ComputableInPolyTime.binary_two_pow.comp
          (ComputableInPolyTime.unary_add' h2 (ComputableInPolyTime.const 1)))))
      (ComputableInPolyTime.const 0)
  refine (ComputableInPolyTime.ite (ComputableInPolyTime.beq hd (ComputableInPolyTime.const 0))
    (ComputableInPolyTime.const 0) (lengthPolyTime (ComputableInPolyTime.filterWithInput
      (test := fun x i => d x % 2 ^ (i + 1) == 0) (ComputableInPolyTime.range.comp hb)
      htest))).of_enc_eq fun x => ?_
  by_cases h : d x = 0 <;> simp [twoVal, h, beq_eq_decide]

/-- `2 ^ (a + 1)` in unary, from `2 ^ a` in unary. -/
private theorem twoPowSuccPolyTime {a : α → ℕ}
    (hL : ComputableInPolyTime (fun x => 2 ^ a x) encIn encUnary) :
    ComputableInPolyTime (fun x => 2 ^ (a x + 1)) encIn encUnary :=
  (ComputableInPolyTime.unary_add' hL hL).of_enc_eq fun x => by rw [pow_succ, mul_two]

/-- **The multiplicities are polynomial-time**, in unary, given `2 ^ a` in unary. -/
@[fun_prop]
theorem computableInPolyTime_mult {a u h k : α → ℕ}
    (ha : ComputableInPolyTime a encIn encUnary)
    (hL : ComputableInPolyTime (fun x => 2 ^ a x) encIn encUnary)
    (hu : ComputableInPolyTime u encIn encUnary) (hh : ComputableInPolyTime h encIn encUnary)
    (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun x => mult (a x) (u x) (h x) (k x)) encIn encUnary :=
  ComputableInPolyTime.unary_mul' hh (ComputableInPolyTime.unary_sub' hu
    (computableInPolyTime_twoVal (ComputableInPolyTime.unary_add' ha (ComputableInPolyTime.const 1))
      (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_sub' hk hL)
        (ComputableInPolyTime.unary_sub' hL hk))))

/-- **The other node indices are polynomial-time**, given `2 ^ a` in unary. -/
@[fun_prop]
theorem computableInPolyTime_others {a k : α → ℕ}
    (hL : ComputableInPolyTime (fun x => 2 ^ a x) encIn encUnary)
    (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun x => others (a x) (k x)) encIn (encList encUnary) := by
  have h1 := ComputableInPolyTime.fst encIn encUnary
  have h2 := ComputableInPolyTime.snd encIn encUnary
  refine (ComputableInPolyTime.filterWithInput
    (test := fun x k' => !(k' == 2 ^ a x) && !(k' == k x))
    (ComputableInPolyTime.range.comp (twoPowSuccPolyTime hL))
    (ComputableInPolyTime.bool_and'
      (ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.beq h2 (hL.comp h1)))
      (ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.beq h2 (hk.comp h1))))).of_enc_eq
    fun x => ?_
  congr 1

/-- **The total multiplicity of the other nodes is polynomial-time**, in unary. -/
@[fun_prop]
theorem computableInPolyTime_multSum {a u h k : α → ℕ}
    (ha : ComputableInPolyTime a encIn encUnary)
    (hL : ComputableInPolyTime (fun x => 2 ^ a x) encIn encUnary)
    (hu : ComputableInPolyTime u encIn encUnary) (hh : ComputableInPolyTime h encIn encUnary)
    (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun x => multSum (a x) (u x) (h x) (k x)) encIn encUnary := by
  have hq := ComputableInPolyTime.fst (encPair encIn encUnary) encUnary
  have hx := (ComputableInPolyTime.fst encIn encUnary).comp hq
  have hs := (ComputableInPolyTime.snd encIn encUnary).comp hq
  have hk' := ComputableInPolyTime.snd (encPair encIn encUnary) encUnary
  have hfold := ComputableInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encUnary) (encL := encList encUnary)
    (step := fun x s k' => s + mult (a x) (u x) (h x) k') (ComputableInPolyTime.const 0)
    ⟨computableInPolyTime_others hL hk, ComputableInPolyTime.unary_add' hs
      (computableInPolyTime_mult (ha.comp hx) (hL.comp hx) (hu.comp hx) (hh.comp hx) hk'),
      inferInstance, inferInstance⟩
    ⟨(polyBounded_unary hh).mul (polyBounded_unary hu), fun x s k' _ => by
      have : mult (a x) (u x) (h x) k' ≤ h x * u x :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      simp only [encUnary_apply, List.length_replicate]
      omega⟩
  refine hfold.of_enc_eq fun x => ?_
  rw [multSum, foldl_add_eq, zero_add]

/-- **Integer differences as constants are polynomial-time**, with `x, y` in unary. -/
@[fun_prop]
theorem computableInPolyTime_diffConst {N x y : α → ℕ} {fl : α → List ℕ}
    (hN : ComputableInPolyTime N encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hx : ComputableInPolyTime x encIn encUnary) (hy : ComputableInPolyTime y encIn encUnary) :
    ComputableInPolyTime (fun z => diffConst (N z) (fl z) (x z) (y z)) encIn (encList encNat) :=
  ComputableInPolyTime.ite (ComputableInPolyTime.unary_lt' hx hy)
    (computableInPolyTime_neg hN hfl (singletonPolyTime
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.unary_sub' hy hx))))
    (singletonPolyTime (ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.unary_sub' hx hy))) |>.of_enc_eq fun z => by simp [diffConst]

/-- **The slope constants are polynomial-time**, with `a, x, y` in unary. -/
@[fun_prop]
theorem computableInPolyTime_slopeConst {N a x y : α → ℕ} {fl : α → List ℕ}
    (hN : ComputableInPolyTime N encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (ha : ComputableInPolyTime a encIn encUnary)
    (hx : ComputableInPolyTime x encIn encUnary) (hy : ComputableInPolyTime y encIn encUnary) :
    ComputableInPolyTime (fun z => slopeConst (N z) (fl z) (a z) (x z) (y z)) encIn
      (encList encNat) := by
  have hd := ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_sub' hx hy)
    (ComputableInPolyTime.unary_sub' hy hx)
  have ha1 := ComputableInPolyTime.unary_add' ha (ComputableInPolyTime.const 1)
  have hv := computableInPolyTime_twoVal ha1 hd
  have hw := computableInPolyTime_mul hN hfl
    (singletonPolyTime (ComputableInPolyTime.binary_two_pow.comp
      (ComputableInPolyTime.unary_sub' ha1 hv)))
    (computableInPolyTime_inv hN hfl (singletonPolyTime (ComputableInPolyTime.binary_div.comp
      ((ComputableInPolyTime.unary_to_binary.comp hd).prod
        (ComputableInPolyTime.binary_two_pow.comp hv)))))
  exact (ComputableInPolyTime.ite (ComputableInPolyTime.unary_lt' hx hy)
    (computableInPolyTime_neg hN hfl hw) hw).of_enc_eq fun z => by simp [slopeConst]

/-- **Truncated geometric series are polynomial-time**, with `J` in unary. -/
@[fun_prop]
theorem computableInPolyTime_geom {N J : α → ℕ} {fl c : α → List ℕ}
    (hN : ComputableInPolyTime N encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hJ : ComputableInPolyTime J encIn encUnary)
    (hc : ComputableInPolyTime c encIn (encList encNat)) :
    ComputableInPolyTime (fun x => geom (N x) (fl x) (J x) (c x)) encIn
      (encList (encList encNat)) := by
  have h1 := ComputableInPolyTime.fst encIn encUnary
  have h2 := ComputableInPolyTime.snd encIn encUnary
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hJ)
    (computableInPolyTime_pow (hN.comp h1) (hfl.comp h1)
      (computableInPolyTime_neg (hN.comp h1) (hfl.comp h1) (hc.comp h1)) h2)

theorem mulGeomPow_succ (N : ℕ) (fl : List ℕ) (J : ℕ) (c : List ℕ) (m : ℕ)
    (R : List (List ℕ)) :
    mulGeomPow N fl J c (m + 1) R = tmul N fl J (mulGeomPow N fl J c m R) (geom N fl J c) := by
  rw [mulGeomPow, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
    ← mulGeomPow]

/-- A multiplication by a power of a geometric series is the input or a truncated product. -/
theorem mulGeomPow_eq_or (N : ℕ) (fl : List ℕ) (J : ℕ) (c : List ℕ) (m : ℕ)
    (R : List (List ℕ)) : mulGeomPow N fl J c m R = R ∨
      ∃ R', mulGeomPow N fl J c m R = tmul N fl J R' (geom N fl J c) := by
  rcases m with _ | m
  · exact Or.inl (by simp [mulGeomPow])
  · exact Or.inr ⟨_, mulGeomPow_succ N fl J c m R⟩

/-- The encoded length of a truncated product is bounded. -/
private theorem length_encPoly_tmul_le (N : ℕ) (fl : List ℕ) (J : ℕ) (P R : List (List ℕ)) :
    (encList (encList encNat) (tmul N fl J P R)).length ≤
      J * (2 * (fl.length * (2 * (N + 1) + 1)) + 1) :=
  length_encPoly_le (length_tmul J P R).le fun _ hc => small_of_mem_tmul hc

/-- **Multiplication by a power of a geometric series is polynomial-time**, with `J, m` in
unary. -/
@[fun_prop]
theorem computableInPolyTime_mulGeomPow {N J m : α → ℕ} {fl c : α → List ℕ}
    {R : α → List (List ℕ)}
    (hN : ComputableInPolyTime N encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hJ : ComputableInPolyTime J encIn encUnary)
    (hc : ComputableInPolyTime c encIn (encList encNat))
    (hm : ComputableInPolyTime m encIn encUnary)
    (hR : ComputableInPolyTime R encIn (encList (encList encNat))) :
    ComputableInPolyTime (fun x => mulGeomPow (N x) (fl x) (J x) (c x) (m x) (R x)) encIn
      (encList (encList encNat)) := by
  let encS := encList (encList encNat)
  have hq := ComputableInPolyTime.fst (encPair encIn encS) encUnary
  have hx := (ComputableInPolyTime.fst encIn encS).comp hq
  have hP := (ComputableInPolyTime.snd encIn encS).comp hq
  exact ComputableInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encUnary) (encL := encList encUnary)
    (step := fun x R _ => tmul (N x) (fl x) (J x) R (geom (N x) (fl x) (J x) (c x))) hR
    ⟨ComputableInPolyTime.range.comp hm, computableInPolyTime_tmul (hN.comp hx) (hfl.comp hx)
      (hJ.comp hx) hP (computableInPolyTime_geom (hN.comp hx) (hfl.comp hx) (hJ.comp hx)
        (hc.comp hx)), inferInstance, inferInstance⟩
    ⟨polyBounded_polyLength hN hfl hJ, fun x R _ _ => by
      have := length_encPoly_tmul_le (N x) (fl x) (J x) R (geom (N x) (fl x) (J x) (c x))
      omega⟩

/-- **The truncated reciprocal of `E_t(t + α z)` is polynomial-time**, given `2 ^ a` in
unary. -/
@[fun_prop]
theorem computableInPolyTime_recip {N a u h k J : α → ℕ} {fl : α → List ℕ}
    (hN : ComputableInPolyTime N encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (ha : ComputableInPolyTime a encIn encUnary)
    (hL : ComputableInPolyTime (fun x => 2 ^ a x) encIn encUnary)
    (hu : ComputableInPolyTime u encIn encUnary) (hh : ComputableInPolyTime h encIn encUnary)
    (hk : ComputableInPolyTime k encIn encUnary) (hJ : ComputableInPolyTime J encIn encUnary) :
    ComputableInPolyTime (fun x => recip (N x) (fl x) (a x) (u x) (h x) (k x) (J x)) encIn
      (encList (encList encNat)) := by
  let encS := encList (encList encNat)
  have hq := ComputableInPolyTime.fst (encPair encIn encS) encUnary
  have hx := (ComputableInPolyTime.fst encIn encS).comp hq
  have hP := (ComputableInPolyTime.snd encIn encS).comp hq
  have hk' := ComputableInPolyTime.snd (encPair encIn encS) encUnary
  exact ComputableInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encUnary) (encL := encList encUnary)
    (step := fun x R k' => mulGeomPow (N x) (fl x) (J x) (slopeConst (N x) (fl x) (a x) (k x) k')
      (mult (a x) (u x) (h x) k') R)
    (ComputableInPolyTime.cons' (computableInPolyTime_one hfl) (ComputableInPolyTime.const []))
    ⟨computableInPolyTime_others hL hk, computableInPolyTime_mulGeomPow (hN.comp hx)
      (hfl.comp hx) (hJ.comp hx) (computableInPolyTime_slopeConst (hN.comp hx) (hfl.comp hx)
        (ha.comp hx) (hk.comp hx) hk')
      (computableInPolyTime_mult (ha.comp hx) (hL.comp hx) (hu.comp hx) (hh.comp hx) hk') hP,
      inferInstance, inferInstance⟩
    ⟨polyBounded_polyLength hN hfl hJ, fun x R k' _ => by
      rcases mulGeomPow_eq_or (N x) (fl x) (J x) (slopeConst (N x) (fl x) (a x) (k x) k')
        (mult (a x) (u x) (h x) k') R with h0 | ⟨R', h1⟩
      · rw [h0]; omega
      · have := length_encPoly_tmul_le (N x) (fl x) (J x) R'
          (geom (N x) (fl x) (J x) (slopeConst (N x) (fl x) (a x) (k x) k'))
        rw [h1]; omega⟩

/-- **The products `∏_q (-q c_q) ^ (q_q)` are polynomial-time**, given `2 ^ a` in unary. -/
@[fun_prop]
theorem computableInPolyTime_basisNum {N a u h k : α → ℕ} {fl : α → List ℕ}
    (hN : ComputableInPolyTime N encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (ha : ComputableInPolyTime a encIn encUnary)
    (hL : ComputableInPolyTime (fun x => 2 ^ a x) encIn encUnary)
    (hu : ComputableInPolyTime u encIn encUnary) (hh : ComputableInPolyTime h encIn encUnary)
    (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun x => basisNum (N x) (fl x) (a x) (u x) (h x) (k x)) encIn
      (encList encNat) := by
  have hq := ComputableInPolyTime.fst (encPair encIn (encList encNat)) encUnary
  have hx := (ComputableInPolyTime.fst encIn (encList encNat)).comp hq
  have hacc := (ComputableInPolyTime.snd encIn (encList encNat)).comp hq
  have hk' := ComputableInPolyTime.snd (encPair encIn (encList encNat)) encUnary
  have hN' := hN.comp hx
  have hfl' := hfl.comp hx
  exact ComputableInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encUnary) (encL := encList encUnary)
    (step := fun x acc k' => mul (N x) (fl x) acc (pow (N x) (fl x)
      (mul (N x) (fl x) (diffConst (N x) (fl x) (2 ^ a x) k')
        (slopeConst (N x) (fl x) (a x) (k x) k')) (mult (a x) (u x) (h x) k')))
    (computableInPolyTime_one hfl)
    ⟨computableInPolyTime_others hL hk, computableInPolyTime_mul hN' hfl' hacc
      (computableInPolyTime_pow hN' hfl' (computableInPolyTime_mul hN' hfl'
        (computableInPolyTime_diffConst hN' hfl' (hL.comp hx) hk')
        (computableInPolyTime_slopeConst hN' hfl' (ha.comp hx) (hk.comp hx) hk'))
        (computableInPolyTime_mult (ha.comp hx) (hL.comp hx) (hu.comp hx) (hh.comp hx) hk')),
      inferInstance, inferInstance⟩
    ⟨polyBounded_reducedLength hN hfl, fun x acc k' _ =>
      (length_encList_mul_le _ _ _ _).trans (Nat.le_add_left _ _)⟩

/-- **The multipliers are polynomial-time**, given `2 ^ a` in unary. -/
@[fun_prop]
theorem computableInPolyTime_coeffMult {N a u h Δ k j : α → ℕ} {fl : α → List ℕ}
    (hN : ComputableInPolyTime N encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (ha : ComputableInPolyTime a encIn encUnary)
    (hL : ComputableInPolyTime (fun x => 2 ^ a x) encIn encUnary)
    (hu : ComputableInPolyTime u encIn encUnary) (hh : ComputableInPolyTime h encIn encUnary)
    (hΔ : ComputableInPolyTime Δ encIn encUnary) (hk : ComputableInPolyTime k encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => coeffMult (N x) (fl x) (a x) (u x) (h x) (Δ x) (k x) (j x))
      encIn (encList encNat) :=
  computableInPolyTime_mul hN hfl (computableInPolyTime_mul hN hfl
    (singletonPolyTime (ComputableInPolyTime.binary_two_pow.comp
      (ComputableInPolyTime.unary_sub' hΔ (ComputableInPolyTime.unary_mul'
        (ComputableInPolyTime.unary_add' ha (ComputableInPolyTime.const 1))
        (ComputableInPolyTime.unary_add' (computableInPolyTime_multSum ha hL hu hh hk) hj)))))
    (computableInPolyTime_basisNum hN hfl ha hL hu hh hk))
    (computableInPolyTime_pow hN hfl (computableInPolyTime_diffConst hN hfl hL hk) hj)

/-- **The contribution of a node is polynomial-time**, given `2 ^ a` in unary. -/
@[fun_prop]
theorem computableInPolyTime_nodeTerm {N a u h Δ k : α → ℕ} {fl : α → List ℕ}
    {ζ w : α → List (List ℕ)}
    (hN : ComputableInPolyTime N encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (ha : ComputableInPolyTime a encIn encUnary)
    (hL : ComputableInPolyTime (fun x => 2 ^ a x) encIn encUnary)
    (hu : ComputableInPolyTime u encIn encUnary) (hh : ComputableInPolyTime h encIn encUnary)
    (hΔ : ComputableInPolyTime Δ encIn encUnary)
    (hζ : ComputableInPolyTime ζ encIn (encList (encList encNat)))
    (hk : ComputableInPolyTime k encIn encUnary)
    (hw : ComputableInPolyTime w encIn (encList (encList encNat))) :
    ComputableInPolyTime (fun x => nodeTerm (N x) (fl x) (a x) (u x) (h x) (Δ x) (ζ x) (k x) (w x))
      encIn (encList encNat) := by
  have hJ := computableInPolyTime_mult ha hL hu hh hk
  have hQ := computableInPolyTime_tmul hN hfl hJ (computableInPolyTime_interp hN hfl hζ hw)
    (computableInPolyTime_recip hN hfl ha hL hu hh hk hJ)
  have hq := ComputableInPolyTime.fst (encPair encIn (encList encNat)) encUnary
  have hx := (ComputableInPolyTime.fst encIn (encList encNat)).comp hq
  have hS := (ComputableInPolyTime.snd encIn (encList encNat)).comp hq
  have hj := ComputableInPolyTime.snd (encPair encIn (encList encNat)) encUnary
  exact ComputableInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encUnary) (encL := encList encUnary)
    (step := fun x S j => add (N x) (fl x) S (mul (N x) (fl x)
      (coeffMult (N x) (fl x) (a x) (u x) (h x) (Δ x) (k x) j)
      ((tmul (N x) (fl x) (mult (a x) (u x) (h x) (k x)) (interp (N x) (fl x) (ζ x) (w x))
        (recip (N x) (fl x) (a x) (u x) (h x) (k x) (mult (a x) (u x) (h x) (k x)))).getD j [])))
    (computableInPolyTime_zero hfl)
    ⟨ComputableInPolyTime.range.comp hJ, computableInPolyTime_add (hN.comp hx) (hfl.comp hx) hS
      (computableInPolyTime_mul (hN.comp hx) (hfl.comp hx)
        (computableInPolyTime_coeffMult (hN.comp hx) (hfl.comp hx) (ha.comp hx) (hL.comp hx)
          (hu.comp hx) (hh.comp hx) (hΔ.comp hx) (hk.comp hx) hj)
        (getDPolyTime (hQ.comp hx) hj)), inferInstance, inferInstance⟩
    ⟨polyBounded_reducedLength hN hfl, fun x S j _ =>
      (length_encList_add_le _ _ _ _).trans (Nat.le_add_left _ _)⟩

/-- **Native tapered recovery is polynomial-time**, with the precision `p`, the shift `Δ`, the
parameters `a, u, h` and `2 ^ a` in unary, and the points and values as coefficient lists. -/
@[fun_prop]
theorem computableInPolyTime_recover {p Δ a u h : α → ℕ} {fl : α → List ℕ}
    {ζ : α → List (List ℕ)} {W : α → List (List (List ℕ))}
    (hp : ComputableInPolyTime p encIn encUnary) (hΔ : ComputableInPolyTime Δ encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (ha : ComputableInPolyTime a encIn encUnary)
    (hL : ComputableInPolyTime (fun x => 2 ^ a x) encIn encUnary)
    (hu : ComputableInPolyTime u encIn encUnary) (hh : ComputableInPolyTime h encIn encUnary)
    (hζ : ComputableInPolyTime ζ encIn (encList (encList encNat)))
    (hW : ComputableInPolyTime W encIn (encList (encList (encList encNat)))) :
    ComputableInPolyTime (fun x => recover (p x) (Δ x) (fl x) (a x) (u x) (h x) (ζ x) (W x))
      encIn (encList encNat) := by
  have hN := ComputableInPolyTime.unary_add' hp hΔ
  have hq := ComputableInPolyTime.fst (encPair encIn (encList encNat)) encUnary
  have hx := (ComputableInPolyTime.fst encIn (encList encNat)).comp hq
  have hS := (ComputableInPolyTime.snd encIn (encList encNat)).comp hq
  have hk := ComputableInPolyTime.snd (encPair encIn (encList encNat)) encUnary
  have hstep : ComputableInPolyTime (fun q : (α × List ℕ) × ℕ =>
      if (q.2 == 2 ^ a q.1.1) = true then q.1.2 else add (p q.1.1 + Δ q.1.1) (fl q.1.1) q.1.2
        (nodeTerm (p q.1.1 + Δ q.1.1) (fl q.1.1) (a q.1.1) (u q.1.1) (h q.1.1) (Δ q.1.1)
          (ζ q.1.1) q.2 ((W q.1.1).getD q.2 [])))
      (encPair (encPair encIn (encList encNat)) encUnary) (encList encNat) :=
    ComputableInPolyTime.ite (ComputableInPolyTime.beq hk (hL.comp hx)) hS
      (computableInPolyTime_add (hN.comp hx) (hfl.comp hx) hS
        (computableInPolyTime_nodeTerm (hN.comp hx) (hfl.comp hx) (ha.comp hx) (hL.comp hx)
          (hu.comp hx) (hh.comp hx) (hΔ.comp hx) (hζ.comp hx) hk
          ((ComputableInPolyTime.listGetD (encA := encList (encList encNat)) []).comp
            ((hW.comp hx).prod hk))))
  have hfold := ComputableInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encUnary) (encL := encList encUnary)
    (step := fun x S k => if (k == 2 ^ a x) = true then S else add (p x + Δ x) (fl x) S
      (nodeTerm (p x + Δ x) (fl x) (a x) (u x) (h x) (Δ x) (ζ x) k ((W x).getD k [])))
    (computableInPolyTime_zero hfl)
    ⟨ComputableInPolyTime.range.comp (twoPowSuccPolyTime hL), hstep, inferInstance,
      inferInstance⟩
    ⟨polyBounded_reducedLength hN hfl, fun x S k _ => by
      split
      · omega
      · exact (length_encList_add_le _ _ _ _).trans (Nat.le_add_left _ _)⟩
  refine (computableInPolyTime_shiftDown hΔ hfold).of_enc_eq fun x => ?_
  simp only [recover, beq_iff_eq, Function.comp_apply]

/-- **Storing a value is polynomial-time**, with the node index in unary. -/
@[fun_prop]
theorem computableInPolyTime_storeValue {W : α → List (List (List ℕ))} {k : α → ℕ}
    {y : α → List ℕ}
    (hW : ComputableInPolyTime W encIn (encList (encList (encList encNat))))
    (hk : ComputableInPolyTime k encIn encUnary)
    (hy : ComputableInPolyTime y encIn (encList encNat)) :
    ComputableInPolyTime (fun x => storeValue (W x) (k x) (y x)) encIn
      (encList (encList (encList encNat))) := by
  have h1 := ComputableInPolyTime.fst encIn encUnary
  have h2 := ComputableInPolyTime.snd encIn encUnary
  have hrow := (ComputableInPolyTime.listGetD (encA := encList (encList encNat)) []).comp
    ((hW.comp h1).prod h2)
  have hlen := lengthPolyTime hW
  have hmax : ComputableInPolyTime (fun x => max (W x).length (k x + 1)) encIn encUnary :=
    (ComputableInPolyTime.unary_add' hlen (ComputableInPolyTime.unary_sub'
      (ComputableInPolyTime.unary_add' hk (ComputableInPolyTime.const 1)) hlen)).of_enc_eq
      fun x => by congr 1; omega
  refine (ComputableInPolyTime.mapWithInput
    (f := fun x k' => if (k' == k x) = true then (W x).getD k' [] ++ [y x] else (W x).getD k' [])
    (ComputableInPolyTime.range.comp hmax)
    (ComputableInPolyTime.ite (ComputableInPolyTime.beq h2 (hk.comp h1))
      (ComputableInPolyTime.listAppend' hrow (singletonPolyTime' (hy.comp h1))) hrow)).of_enc_eq
    fun x => ?_
  simp only [storeValue, beq_iff_eq, Function.comp_apply]

end PolyTime

end Cslib.Circuits.Frontier.NativeRecovery

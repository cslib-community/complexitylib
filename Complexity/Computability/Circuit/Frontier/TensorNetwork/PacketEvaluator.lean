/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.KernelProduct
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.PacketEntry
public import Complexity.Computability.PolyTime.GaloisRingArithmetic
public import Complexity.Foundations.NumberTheory.Padics.RatValuation
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.GetD

/-!
# Evaluating packet entries on coefficient lists

The packet tensors of the child networks of the contraction algorithm of [OpenAI2026ETH] are
implicit: an entry is computed from the data of its packet (§D.4.6, p. 63). This file gives that
computation on the coefficient lists of `A_p = (ℤ / 2 ^ p)[U] / (f)`, with the arithmetic of
`Cslib.GaloisRingArith`, and proves that it is `TensorNetwork.packetEntry` in `A_p`, so in every
ring that `A_p` maps to.

* **Scalars.** `ℤ_(2)` reduces to `A_p` (`NativePacket.scalarHom`), and any two ring maps from
  `ℤ_(2)` to a ring in which `2` is nilpotent agree (`padicInteger_ringHom_ext`). An integer is a
  constant list (`NativePacket.intConst`).
* **Kernel values** (`NativePacket.kernelValueList`) follow Lemma D.4's evaluation
  (`kernelValue_eq_prod`, p. 60), over the grid of `L = 2 ^ a` slots, with `L` a parameter so that
  it can be read in unary: the inverse of the odd part of `C'(0)`, times
  `2 ^ (a + 1 - v_d) ζ` when `d ≠ t`, times the `2 ^ (a + 1) - 2` linear factors
  `u_q + 2 ^ (a + 1 - v_q) ζ`. The odd part of `C'(0)` is a product of odd integers, so it is `1`
  modulo `2` and `GaloisRingArith.inv` inverts it.
* **Cross ratios** (`NativePacket.crossRatioList`) invert `u₀ + 2 ^ (a + 1 - v) ζ`, which is `1`
  modulo `2` since `u₀` is odd and `v ≤ i ≤ a`.
* **Local forms, mode coefficients, mode values and row terms** follow
  `TensorNetwork.packetLocalForm`, `TensorNetwork.packetModeCoeff`,
  `TensorNetwork.packetModeValue` and `TensorNetwork.packetRowTerm`, with a mode `(y₀, b)` given
  by its dense index `b + nb y₀`, its number under `finProdFinEquiv`.
* **Coefficient extraction** (`NativePacket.listCoeffList`) is the recursion
  `TensorNetwork.listCoeff` on coefficient lists, along a duplicate-free list of modes.

The main result (`NativePacket.val_packetEntryList`) is that the value of
`NativePacket.packetEntryList` in `A_p` is `TensorNetwork.packetEntry` at the reduction of
`ℤ_(2)` and the value of `ζ`. Transported along a ring map `ψ : A_p → S` with `2` nilpotent in
`S` (`NativePacket.map_val_packetEntryList`), it is the packet entry over `S` at any ring map
`ℤ_(2) → S`; with `TensorNetwork.child_tensor_inr_cauchyModeSplitting`, it is the entry of a
packet vertex of a child network, for instance over `B ⧸ (2 ^ p)`.

These are functions on lists of natural numbers with explicit recursion; their certificates of
time `exp(O(L log s))` and polynomial space are separate.

## Main definitions

* `Cslib.Circuits.Frontier.NativePacket.scalarHom`: the reduction `ℤ_(2) → A_p`.
* `Cslib.Circuits.Frontier.NativePacket.kernelValueList`,
  `Cslib.Circuits.Frontier.NativePacket.crossRatioList`: kernel values and cross ratios.
* `Cslib.Circuits.Frontier.NativePacket.listCoeffList`: coefficient extraction.
* `Cslib.Circuits.Frontier.NativePacket.packetEntryList`: the entry of a packet vertex.

## Main results

* `Cslib.Circuits.Frontier.padicInteger_ringHom_ext`: ring maps from `ℤ_(2)` are unique when `2`
  is nilpotent.
* `Cslib.Circuits.Frontier.NativePacket.val_kernelValueList`,
  `Cslib.Circuits.Frontier.NativePacket.val_crossRatioList`,
  `Cslib.Circuits.Frontier.NativePacket.val_listCoeffList`: correctness of the parts.
* `Cslib.Circuits.Frontier.NativePacket.val_packetEntryList`,
  `Cslib.Circuits.Frontier.NativePacket.map_val_packetEntryList`: packet entries.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Lemma D.4 and its
  evaluation (pp. 59–60), §D.4.1 (p. 57) and §D.4.6 (p. 63).
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Finset

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

/-- An odd natural number is a unit of a ring in which `2` is nilpotent. -/
private theorem isUnit_natCast_of_odd {S : Type*} [CommRing S] {n : ℕ} (hn : (2 : S) ^ n = 0)
    {m : ℕ} (hm : Odd m) : IsUnit (m : S) := by
  obtain ⟨k, rfl⟩ := hm
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, add_comm]
  exact IsNilpotent.isUnit_one_add ⟨n, by rw [mul_pow, hn, zero_mul]⟩

/-- **Ring maps from `ℤ_(2)` are unique** into a ring in which `2` is nilpotent: an element
times its odd denominator is its numerator. -/
theorem padicInteger_ringHom_ext {S : Type*} [CommRing S] {n : ℕ} (hn : (2 : S) ^ n = 0)
    (φ ψ : ℤ₍₂₎ →+* S) : φ = ψ := by
  ext x
  have hden : ¬ 2 ∣ (x : ℚ).den := Rat.padicValuation_le_one_iff.mp x.2
  have h : x * ((x : ℚ).den : ℤ₍₂₎) = ((x : ℚ).num : ℤ₍₂₎) :=
    Subtype.ext (by push_cast; exact Rat.mul_den_eq_num _)
  have h1 := congrArg φ h
  have h2 := congrArg ψ h
  rw [map_mul, map_natCast, map_intCast] at h1 h2
  exact (isUnit_natCast_of_odd hn (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hden))).mul_right_cancel
    (h1.trans h2.symm)

namespace NativePacket

open GaloisRingArith TensorNetwork

variable {p : ℕ} {fl : List ℕ}

/-! ### Scalars -/

/-- The reduction `ℤ_(2) → A_p`, through `ℤ / 2 ^ p`. -/
noncomputable def scalarHom (p : ℕ) (fl : List ℕ) : ℤ₍₂₎ →+* Ring p fl :=
  (algebraMap (ZMod (2 ^ p)) (Ring p fl)).comp (Rat.padicIntegerToZModPow 2 p)

/-- `2 ^ p = 0` in `A_p`. -/
theorem two_pow_eq_zero : (2 : Ring p fl) ^ p = 0 := by
  have h := natCast_two_pow (p := p) (fl := fl)
  push_cast at h
  exact h

/-- With no coordinates, `A_p` is the zero ring. -/
theorem subsingleton_of_length_eq_zero (h : fl.length = 0) : Subsingleton (Ring p fl) := by
  set f := (monicOf fl).map (Int.castRingHom (ZMod (2 ^ p)))
  have hf : f = 1 := by
    simp only [f, List.length_eq_zero_iff.mp h, monicOf, List.length_nil, pow_zero, range_zero,
      sum_empty, add_zero, Polynomial.map_one]
  have h1 : AdjoinRoot.mk f f = AdjoinRoot.mk f 1 := congrArg _ hf
  rw [AdjoinRoot.mk_self, map_one] at h1
  exact subsingleton_of_zero_eq_one h1

/-- The value of a tabulated list. -/
theorem val_tabulate (g : ℕ → ℕ) :
    val p fl ((List.range fl.length).map g) =
      ∑ i ∈ range fl.length, (g i : Ring p fl) * AdjoinRoot.root _ ^ i := by
  refine sum_congr rfl fun i hi => ?_
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

/-- An integer as a constant coefficient list: its residue modulo `2 ^ p` in the first of the `e`
coordinates. -/
def intConst (p : ℕ) (fl : List ℕ) (n : ℤ) : List ℕ :=
  (List.range fl.length).map fun j => if j = 0 then (n % 2 ^ p).toNat else 0

/-- The value of a constant list is the integer. -/
@[simp] theorem val_intConst (n : ℤ) : val p fl (intConst p fl n) = n := by
  rcases Nat.eq_zero_or_pos fl.length with h | h
  · have := subsingleton_of_length_eq_zero (p := p) h
    exact Subsingleton.elim _ _
  rw [intConst, val_tabulate, sum_eq_single 0 (fun j _ hj => by simp [hj])
    (fun h0 => absurd (mem_range.mpr h) h0)]
  have hnn : 0 ≤ n % 2 ^ p := Int.emod_nonneg _ (pow_ne_zero _ two_ne_zero)
  have h2 : ((2 ^ p : ℤ) : Ring p fl) = 0 := by
    rw [Int.cast_pow, Int.cast_ofNat]; exact two_pow_eq_zero
  simp only [↓reduceIte, pow_zero, mul_one]
  rw [show (((n % 2 ^ p).toNat : ℕ) : Ring p fl) = ((n % 2 ^ p : ℤ) : Ring p fl) by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]]
  rw [Int.emod_def, Int.cast_sub, Int.cast_mul, h2, zero_mul, sub_zero]

/-- The product of a list of coefficient lists. -/
def prodList (p : ℕ) (fl : List ℕ) (cs : List (List ℕ)) : List ℕ :=
  cs.foldl (mul p fl) (one fl)

/-- The sum of a list of coefficient lists. -/
def sumList (p : ℕ) (fl : List ℕ) (cs : List (List ℕ)) : List ℕ :=
  cs.foldl (add p fl) (zero fl)

private theorem val_foldl_mul (cs : List (List ℕ)) (c : List ℕ) :
    val p fl (cs.foldl (mul p fl) c) = val p fl c * (cs.map (val p fl)).prod := by
  induction cs generalizing c with
  | nil => simp
  | cons d cs ih => rw [List.foldl_cons, ih, val_mul, List.map_cons, List.prod_cons, mul_assoc]

private theorem val_foldl_add (cs : List (List ℕ)) (c : List ℕ) :
    val p fl (cs.foldl (add p fl) c) = val p fl c + (cs.map (val p fl)).sum := by
  induction cs generalizing c with
  | nil => simp
  | cons d cs ih => rw [List.foldl_cons, ih, val_add, List.map_cons, List.sum_cons, add_assoc]

@[simp] theorem val_prodList (cs : List (List ℕ)) :
    val p fl (prodList p fl cs) = (cs.map (val p fl)).prod := by
  rw [prodList, val_foldl_mul, val_one, one_mul]

@[simp] theorem val_sumList (cs : List (List ℕ)) :
    val p fl (sumList p fl cs) = (cs.map (val p fl)).sum := by
  rw [sumList, val_foldl_add, val_zero, zero_add]

/-! ### Inverting elements that are one modulo two -/

/-- Products of elements `1 + 2 x` have this form. -/
private theorem exists_prod_eq_one_add_two_mul {R : Type*} [CommRing R] (l : List R)
    (hl : ∀ y ∈ l, ∃ w, y = 1 + 2 * w) : ∃ w, l.prod = 1 + 2 * w := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons y l ih =>
    obtain ⟨u, hu⟩ := hl y List.mem_cons_self
    obtain ⟨w, hw⟩ := ih fun z hz => hl z (List.mem_cons_of_mem _ hz)
    exact ⟨u + w + 2 * u * w, by rw [List.prod_cons, hu, hw]; ring⟩

/-- **Inversion of an element that is one modulo two**: Newton's inversion needs no further
hypothesis. -/
theorem val_mul_inv_of_eq (c : List ℕ) {w : Ring p fl} (h : val p fl c = 1 + 2 * w) :
    val p fl c * val p fl (inv p fl c) = 1 := by
  obtain ⟨y, hy⟩ := exists_prod_eq_one_add_two_mul
    (List.replicate (2 ^ fl.length - 2) (val p fl c)) fun z hz => ⟨w, by
      rw [List.eq_of_mem_replicate hz, h]⟩
  rw [List.prod_replicate] at hy
  refine val_mul_inv c (w := w + y + 2 * w * y) ?_
  rw [hy, h]
  ring

/-- An inverse is unique. -/
private theorem eq_of_mul_eq_one {R : Type*} [CommRing R] {a b c : R} (hb : a * b = 1)
    (hc : c * a = 1) : b = c := by
  calc b = (c * a) * b := by rw [hc, one_mul]
    _ = c * (a * b) := mul_assoc _ _ _
    _ = c := by rw [hb, mul_one]

/-- An odd integer is `1 + 2 w`. -/
private theorem intCast_odd {R : Type*} [CommRing R] {u : ℤ} (hu : Odd u) :
    ∃ w : R, (u : R) = 1 + 2 * w := by
  obtain ⟨m, rfl⟩ := hu
  exact ⟨m, by push_cast; ring⟩

/-! ### Odd parts -/

/-- An integer is `2 ^ v₂(n)` times its odd part. -/
private theorem two_pow_mul_ediv (n : ℤ) : 2 ^ padicValInt 2 n * (n / 2 ^ padicValInt 2 n) = n :=
  Int.mul_ediv_cancel' (by exact_mod_cast padicValInt_dvd (p := 2) n)

/-- The odd part of a nonzero integer is odd. -/
theorem odd_ediv_two_pow {n : ℤ} (hn : n ≠ 0) : Odd (n / 2 ^ padicValInt 2 n) := by
  rw [← Int.not_even_iff_odd, even_iff_two_dvd]
  rintro ⟨c, hc⟩
  have h2 : (2 : ℤ) ^ (padicValInt 2 n + 1) ∣ n := ⟨c, by
    calc n = 2 ^ padicValInt 2 n * (n / 2 ^ padicValInt 2 n) := (two_pow_mul_ediv n).symm
      _ = 2 ^ (padicValInt 2 n + 1) * c := by rw [hc, pow_succ]; ring⟩
  have h := (padicValInt_dvd_iff (p := 2) (padicValInt 2 n + 1) n).mp (by exact_mod_cast h2)
  omega

/-- The odd part of a nonzero integer is nonzero. -/
private theorem ediv_two_pow_ne_zero {n : ℤ} (hn : n ≠ 0) : n / 2 ^ padicValInt 2 n ≠ 0 := by
  intro h
  exact hn (by rw [← two_pow_mul_ediv n, h, mul_zero])

/-- An integer not divisible by `2 ^ (i + 1)` has valuation at most `i`. -/
theorem padicValInt_le_of_not_dvd {n : ℤ} {i : ℕ} (hn : ¬ (2 : ℤ) ^ (i + 1) ∣ n) :
    padicValInt 2 n ≤ i := by
  by_contra h
  exact hn ((pow_dvd_pow (2 : ℤ) (show i + 1 ≤ padicValInt 2 n by omega)).trans
    (by exact_mod_cast padicValInt_dvd (p := 2) n))

/-! ### The `2`-adic valuation, computably -/

/-- The `2`-adic valuation of `m`, halving at most `k` times. -/
def twoValAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, m => if m ≠ 0 ∧ m % 2 = 0 then twoValAux k (m / 2) + 1 else 0

/-- The `2`-adic valuation of an integer, by repeated halving: `padicValInt 2` (`twoVal_eq`). -/
def twoVal (n : ℤ) : ℕ := twoValAux n.natAbs n.natAbs

theorem twoValAux_eq : ∀ (k m : ℕ), m ≤ k → twoValAux k m = padicValNat 2 m
  | 0, m, h => by rw [Nat.le_zero.mp h, twoValAux]; simp
  | k + 1, m, h => by
    rw [twoValAux]
    split_ifs with hm
    · obtain ⟨hm0, hm2⟩ := hm
      have hm' : m = 2 * (m / 2) := by omega
      rw [twoValAux_eq k (m / 2) (by omega)]
      conv_rhs => rw [hm', padicValNat.mul two_ne_zero (by omega), padicValNat_self, add_comm]
    · by_cases hm0 : m = 0
      · rw [hm0]; simp
      · exact (padicValNat.eq_zero_of_not_dvd fun h2 => hm ⟨hm0, by omega⟩).symm

/-- **The valuation by halving is `padicValInt 2`.** -/
@[simp] theorem twoVal_eq (n : ℤ) : twoVal n = padicValInt 2 n :=
  twoValAux_eq _ _ le_rfl

/-! ### Kernel values -/

/-- The linear factor `u + 2 ^ k ζ`. -/
def linFactor (p : ℕ) (fl : List ℕ) (u : ℤ) (k : ℕ) (ζ : List ℕ) : List ℕ :=
  add p fl (intConst p fl u) (mul p fl (intConst p fl (2 ^ k)) ζ)

@[simp] theorem val_linFactor (u : ℤ) (k : ℕ) (ζ : List ℕ) :
    val p fl (linFactor p fl u k ζ) = (u : Ring p fl) + 2 ^ k * val p fl ζ := by
  simp only [linFactor, val_add, val_mul, val_intConst]
  push_cast
  ring

/-- A linear factor with an odd constant and `k ≥ 1` is one modulo two. -/
theorem exists_val_linFactor_eq {u : ℤ} (hu : Odd u) {k : ℕ} (hk : 1 ≤ k) (ζ : List ℕ) :
    ∃ w : Ring p fl, val p fl (linFactor p fl u k ζ) = 1 + 2 * w := by
  obtain ⟨w, hw⟩ := intCast_odd (R := Ring p fl) hu
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
  exact ⟨w + 2 ^ k' * val p fl ζ, by rw [val_linFactor, hw, pow_add]; ring⟩

/-- The grid `[-L, L)` of `L` slots, in increasing order. The number of slots is a parameter, in
place of `2 ^ a`, so that it can be read in unary. -/
def gridList (L : ℕ) : List ℤ :=
  (List.range (2 * L)).map fun j : ℕ => (j : ℤ) - (L : ℤ)

theorem nodup_gridList (L : ℕ) : (gridList L).Nodup :=
  List.Nodup.map (fun x y h => by simpa using h) List.nodup_range

theorem mem_gridList {L : ℕ} {q : ℤ} : q ∈ gridList L ↔ q ∈ cauchyGrid L := by
  rw [gridList, List.mem_map, mem_cauchyGrid]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [List.mem_range] at hj
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨(q + L).toNat, List.mem_range.mpr ?_, ?_⟩ <;> omega

/-- The odd part of `C'(0) = ∏_{q ≠ 0} (0 - q)`, as a coefficient list. -/
def kernelUnitDen (p : ℕ) (fl : List ℕ) (L : ℕ) : List ℕ :=
  prodList p fl (((gridList L).filter (· ≠ 0)).map fun q =>
    intConst p fl ((0 - q) / 2 ^ twoVal (0 - q)))

/-- `κ (kernelUnit a)`, the inverse of the odd part of `C'(0)`. -/
def kernelUnitList (p : ℕ) (fl : List ℕ) (L : ℕ) : List ℕ :=
  inv p fl (kernelUnitDen p fl L)

/-- The value of `kernelUnitDen`. -/
private theorem val_kernelUnitDen (L : ℕ) :
    val p fl (kernelUnitDen p fl L) = ∏ q ∈ (cauchyGrid L).erase 0,
      (((0 - q) / 2 ^ padicValInt 2 (0 - q) : ℤ) : Ring p fl) := by
  simp only [kernelUnitDen, twoVal_eq]
  rw [val_prodList, List.map_map, ← List.prod_toFinset _
    ((nodup_gridList L).filter _)]
  refine prod_congr ?_ fun q _ => val_intConst _
  ext q
  simp only [List.mem_toFinset, List.mem_filter, mem_gridList, mem_erase, decide_eq_true_eq]
  tauto

/-- **The kernel unit**: `kernelUnitList` is the reduction of `kernelUnit a`. -/
theorem val_kernelUnitList {a L : ℕ} (hL : L = 2 ^ a) :
    val p fl (kernelUnitList p fl L) = scalarHom p fl (kernelUnit a) := by
  subst hL
  have hne (q : ℤ) (hq : q ∈ (cauchyGrid (2 ^ a)).erase 0) : (0 : ℤ) - q ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (ne_of_mem_erase hq))
  -- The odd part of `C'(0)` is one modulo two.
  obtain ⟨w, hw⟩ := exists_prod_eq_one_add_two_mul
    (((cauchyGrid (2 ^ a)).erase 0).toList.map fun q =>
      (((0 - q) / 2 ^ padicValInt 2 (0 - q) : ℤ) : Ring p fl)) fun y hy => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
      exact intCast_odd (odd_ediv_two_pow (hne q (Finset.mem_toList.mp hq)))
  rw [Finset.prod_map_toList] at hw
  have hinv := val_mul_inv_of_eq (kernelUnitDen p fl (2 ^ a)) (w := w)
    (by rw [val_kernelUnitDen, hw])
  refine eq_of_mul_eq_one hinv ?_
  -- `kernelUnit a` inverts the odd part of `C'(0)` in `ℤ_(2)`.
  have hunit : kernelUnit a * ∏ q ∈ (cauchyGrid (2 ^ a)).erase 0,
      (((0 - q) / 2 ^ padicValInt 2 (0 - q) : ℤ) : ℤ₍₂₎) = 1 := by
    refine Subtype.val_injective ?_
    change (ℤ₍₂₎).subtype (kernelUnit a * _) = (ℤ₍₂₎).subtype 1
    rw [map_mul, map_prod, map_one]
    change ((kernelUnit a : ℤ₍₂₎) : ℚ) * _ = 1
    rw [coe_kernelUnit]
    simp only [map_intCast]
    refine inv_mul_cancel₀ (prod_ne_zero_iff.mpr fun q hq => ?_)
    exact_mod_cast ediv_two_pow_ne_zero (hne q hq)
  rw [val_kernelUnitDen]
  have := congrArg (scalarHom p fl) hunit
  rw [map_mul, map_prod, map_one] at this
  simpa only [map_intCast] using this

/-- **Kernel values on coefficient lists** (Lemma D.4's evaluation, p. 60): the kernel unit,
times `2 ^ (a + 1 - v_d) ζ` when `d ≠ t`, times the linear factors `u_q + 2 ^ (a + 1 - v_q) ζ`
over the grid points `q ≠ d, t`. -/
def kernelValueList (p : ℕ) (fl : List ℕ) (a L : ℕ) (t d : ℤ) (ζ : List ℕ) : List ℕ :=
  mul p fl (mul p fl (kernelUnitList p fl L)
      (if d = t then one fl else
        mul p fl (intConst p fl (2 ^ (a + 1 - twoVal (t - d)))) ζ))
    (prodList p fl (((gridList L).filter fun q => q ≠ d ∧ q ≠ t).map fun q =>
      linFactor p fl ((t - q) / 2 ^ twoVal (t - q)) (a + 1 - twoVal (t - q)) ζ))

/-- **Kernel values are correct**: for grid points `t` and `d`, the value is
`kernelValue` at the reduction of `ℤ_(2)` and the value of `ζ`. -/
theorem val_kernelValueList {a L : ℕ} (hL : L = 2 ^ a) {t d : ℤ} (ht : t ∈ cauchyGrid (2 ^ a))
    (hd : d ∈ cauchyGrid (2 ^ a)) (ζ : List ℕ) :
    val p fl (kernelValueList p fl a L t d ζ) =
      kernelValue (scalarHom p fl) (val p fl ζ) a t d := by
  subst hL
  simp only [kernelValueList, twoVal_eq]
  rw [kernelValue_eq_prod _ _ ht hd, val_mul, val_mul, val_kernelUnitList rfl,
    val_prodList, List.map_map, ← List.prod_toFinset _ ((nodup_gridList _).filter _)]
  congr 1
  · congr 1
    split_ifs
    · exact val_one
    · rw [val_mul, val_intConst]; push_cast; rfl
  · refine prod_congr ?_ fun q _ => val_linFactor _ _ _
    ext q
    simp only [List.mem_toFinset, List.mem_filter, mem_gridList, mem_erase, decide_eq_true_eq]
    tauto

/-! ### Cross ratios -/

/-- **Cross ratios on coefficient lists**: `2 ^ (i + 1 - v)` times the inverse of
`u₀ + 2 ^ (a + 1 - v) ζ`, where `t - d₀ = 2 ^ v u₀`. -/
def crossRatioList (p : ℕ) (fl : List ℕ) (a i : ℕ) (t d₀ : ℤ) (ζ : List ℕ) : List ℕ :=
  mul p fl (intConst p fl (2 ^ (i + 1 - twoVal (t - d₀))))
    (inv p fl (linFactor p fl ((t - d₀) / 2 ^ twoVal (t - d₀)) (a + 1 - twoVal (t - d₀)) ζ))

/-- **Cross ratios are correct** when `2 ^ (i + 1) ∤ t - d₀` and `i ≤ a`: the inverted factor is
one modulo two. -/
theorem val_crossRatioList {a i : ℕ} (hia : i ≤ a) {t d₀ : ℤ}
    (hcross : ¬ (2 : ℤ) ^ (i + 1) ∣ t - d₀) (ζ : List ℕ) :
    val p fl (crossRatioList p fl a i t d₀ ζ) = crossRatio a i t d₀ (val p fl ζ) := by
  have hv := padicValInt_le_of_not_dvd hcross
  have hn : t - d₀ ≠ 0 := by rintro h; exact hcross (h ▸ dvd_zero _)
  obtain ⟨w, hw⟩ := exists_val_linFactor_eq (p := p) (fl := fl) (odd_ediv_two_pow hn)
    (show 1 ≤ a + 1 - padicValInt 2 (t - d₀) by omega) ζ
  have hinv := val_mul_inv_of_eq _ hw
  have hU := IsUnit.of_mul_eq_one _ hinv
  simp only [crossRatioList, twoVal_eq]
  rw [crossRatio, val_mul, val_intConst, ← val_linFactor]
  congr 1
  · push_cast; rfl
  · calc val p fl (inv p fl _) = (Ring.inverse (val p fl _) * val p fl _) * val p fl (inv p fl _) :=
          by rw [Ring.inverse_mul_cancel _ hU, one_mul]
      _ = Ring.inverse (val p fl _) := by rw [mul_assoc, hinv, mul_one]

/-! ### The terms of a packet entry -/

/-- The local form of a row port in slot `x`: the sum of the kernel values at the column ports
set to one. -/
def localFormList (p : ℕ) (fl : List ℕ) (a L : ℕ) (t : ℤ) (cols : List (ℕ × Bool)) (x : ℕ)
    (ζ : List ℕ) : List ℕ :=
  sumList p fl (cols.map fun c => if c.2 then kernelValueList p fl a L t ((c.1 : ℤ) - x) ζ
    else zero fl)

theorem val_localFormList {a L : ℕ} (hL : L = 2 ^ a) {t : ℤ} (ht : t ∈ cauchyGrid (2 ^ a))
    {cols : List (ℕ × Bool)} (hcols : ∀ c ∈ cols, c.1 < 2 ^ a) {x : ℕ} (hx : x < 2 ^ a)
    (ζ : List ℕ) :
    val p fl (localFormList p fl a L t cols x ζ) =
      packetLocalForm (scalarHom p fl) (val p fl ζ) a t cols x := by
  rw [localFormList, val_sumList, List.map_map, packetLocalForm]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  simp only [Function.comp_apply]
  split_ifs
  · exact val_kernelValueList hL ht (sub_mem_cauchyGrid hx (hcols c hc)) ζ
  · exact val_zero

/-- The coefficient of the mode `(y₀, b)` in the form of a row port in slot `x`. -/
def modeCoeffList (p : ℕ) (fl : List ℕ) (a L i : ℕ) (t : ℤ) (differ : Bool) (x y₀ b : ℕ)
    (ζ : List ℕ) : List ℕ :=
  if differ = true ∧ x.testBit i = y₀.testBit i then
    mul p fl (kernelValueList p fl a L t ((y₀ : ℤ) - x) ζ)
      (pow p fl (crossRatioList p fl a i t ((y₀ : ℤ) - x) ζ) b)
  else zero fl

theorem val_modeCoeffList {a L i : ℕ} (hL : L = 2 ^ a) (hia : i < a) {t : ℤ}
    (ht : t ∈ cauchyGrid (2 ^ a))
    (hti : (2 : ℤ) ^ i ∣ t) (hti' : ¬ (2 : ℤ) ^ (i + 1) ∣ t) (differ : Bool) {x : ℕ}
    (hx : x < 2 ^ a) {nb : ℕ} (Z : Fin (2 ^ (i + 1)) × Fin nb) (ζ : List ℕ) :
    val p fl (modeCoeffList p fl a L i t differ x Z.1 Z.2 ζ) =
      packetModeCoeff (scalarHom p fl) (val p fl ζ) a i t differ x Z := by
  have hy : (Z.1 : ℕ) < 2 ^ a :=
    Z.1.isLt.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [modeCoeffList, packetModeCoeff]
  split_ifs with h
  · rw [val_mul, val_pow, val_kernelValueList hL ht (sub_mem_cauchyGrid hx hy),
      val_crossRatioList hia.le (not_dvd_sub_sub_of_testBit_eq hti hti' Z.1.isLt h.2)]
  · exact val_zero

/-- The value of the mode `(y₀, b)` on the column ports: the sum of `j ^ b` over the column ports
in slots `y₀ + 2 ^ (i + 1) j` set to one, when the symbols of the packet differ. -/
def modeValueList (p : ℕ) (fl : List ℕ) (i : ℕ) (differ : Bool) (cols : List (ℕ × Bool))
    (y₀ b : ℕ) : List ℕ :=
  sumList p fl (cols.map fun c =>
    if c.2 = true ∧ differ = true ∧ c.1 % 2 ^ (i + 1) = y₀ then
      pow p fl (intConst p fl ((c.1 / 2 ^ (i + 1) : ℕ) : ℤ)) b
    else zero fl)

theorem val_modeValueList (i : ℕ) (differ : Bool) (cols : List (ℕ × Bool)) {nb : ℕ}
    (Z : Fin (2 ^ (i + 1)) × Fin nb) :
    val p fl (modeValueList p fl i differ cols Z.1 Z.2) =
      packetModeValue (Ring p fl) i differ cols Z := by
  rw [modeValueList, val_sumList, List.map_map, packetModeValue]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  simp only [Function.comp_apply]
  split_ifs
  · rw [val_pow, val_intConst, Int.cast_natCast]
  · exact val_zero

/-- The tile of the dense index `b + nb y₀` of a mode `(y₀, b)`. -/
private theorem finProdFinEquiv_div {m n : ℕ} (Z : Fin m × Fin n) :
    (finProdFinEquiv Z : ℕ) / n = Z.1 :=
  congrArg (fun W => (W.1 : ℕ)) (finProdFinEquiv.symm_apply_apply Z)

/-- The exponent of the dense index `b + nb y₀` of a mode `(y₀, b)`. -/
private theorem finProdFinEquiv_mod {m n : ℕ} (Z : Fin m × Fin n) :
    (finProdFinEquiv Z : ℕ) % n = Z.2 :=
  congrArg (fun W => (W.2 : ℕ)) (finProdFinEquiv.symm_apply_apply Z)

/-- The terms of the affine factor of a row port `r = (x, Y_x)`: its local term at `none`, and
the coefficient of the mode `(k / nb, k % nb)` at `some k` (zero when there are no exponents,
`nb = 0`, so that the exponent `k % nb` stays below `nb`). -/
def rowTermList (p : ℕ) (fl : List ℕ) (a L i : ℕ) (t : ℤ) (nb : ℕ) (differ : Bool)
    (cols : List (ℕ × Bool)) (ζ : List ℕ) (r : ℕ × Bool) : Option ℕ → List ℕ
  | none => if r.2 then localFormList p fl a L t cols r.1 ζ
      else sub p fl (one fl) (localFormList p fl a L t cols r.1 ζ)
  | some k => if nb = 0 then zero fl else
      if r.2 then modeCoeffList p fl a L i t differ r.1 (k / nb) (k % nb) ζ
      else neg p fl (modeCoeffList p fl a L i t differ r.1 (k / nb) (k % nb) ζ)

/-- Row terms are correct, at the dense indices of the modes of the packet. -/
theorem val_rowTermList {a L i : ℕ} (hL : L = 2 ^ a) (hia : i < a) {t : ℤ}
    (ht : t ∈ cauchyGrid (2 ^ a))
    (hti : (2 : ℤ) ^ i ∣ t) (hti' : ¬ (2 : ℤ) ^ (i + 1) ∣ t) (nb : ℕ) (differ : Bool)
    {cols : List (ℕ × Bool)} (hcols : ∀ c ∈ cols, c.1 < 2 ^ a) {r : ℕ × Bool} (hr : r.1 < 2 ^ a)
    (ζ : List ℕ) :
    (fun o => val p fl (rowTermList p fl a L i t nb differ cols ζ r o)) ∘
        Option.map (finProdFinEquiv.toEmbedding.trans Fin.valEmbedding) =
      packetRowTerm (p := nb) (scalarHom p fl) (val p fl ζ) a i t differ cols r := by
  funext o
  cases o with
  | none =>
    simp only [Function.comp_apply, Option.map_none, rowTermList, packetRowTerm, affineFactor]
    split_ifs
    · exact val_localFormList hL ht hcols hr ζ
    · rw [val_sub, val_one, val_localFormList hL ht hcols hr ζ]
  | some Z =>
    simp only [Function.comp_apply, Option.map_some, rowTermList, packetRowTerm, affineSign,
      Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Fin.valEmbedding_apply,
      finProdFinEquiv_div, finProdFinEquiv_mod,
      Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt Z.2.isLt), ↓reduceIte]
    have h := val_modeCoeffList (p := p) (fl := fl) hL hia ht hti hti' differ hr Z ζ
    split_ifs
    · rw [one_mul]; exact h
    · rw [val_neg, h, neg_one_mul]

/-! ### Coefficient extraction -/

/-- **Coefficient extraction on coefficient lists**, `TensorNetwork.listCoeff` along a list of
modes: the first factor contributes its local term, or one of the modes still needed. -/
def listCoeffList (p : ℕ) (fl : List ℕ) {M : Type} [DecidableEq M] (modes : List M) :
    List (Option M → List ℕ) → (M → ℕ) → List ℕ
  | [], γ => if ∀ Z ∈ modes, γ Z = 0 then one fl else zero fl
  | T :: ts, γ => add p fl (mul p fl (T none) (listCoeffList p fl modes ts γ))
      (sumList p fl (modes.map fun Z => if γ Z = 0 then zero fl else
        mul p fl (T (some Z)) (listCoeffList p fl modes ts (Function.update γ Z (γ Z - 1)))))

/-- **Coefficient extraction is correct**, along a duplicate-free list of modes. -/
theorem val_listCoeffList {M : Type} [DecidableEq M] {modes : List M} (hm : modes.Nodup) :
    ∀ (ts : List (Option M → List ℕ)) (γ : M → ℕ),
      val p fl (listCoeffList p fl modes ts γ) =
        TensorNetwork.listCoeff modes.toFinset (ts.map fun T o => val p fl (T o)) γ
  | [], γ => by
    rw [listCoeffList, List.map_nil, TensorNetwork.listCoeff_nil]
    simp only [List.mem_toFinset]
    split_ifs
    · exact val_one
    · exact val_zero
  | T :: ts, γ => by
    rw [listCoeffList, List.map_cons, TensorNetwork.listCoeff_cons, val_add, val_mul,
      val_listCoeffList hm ts γ, val_sumList, List.map_map, ← List.sum_toFinset _ hm]
    congr 1
    refine sum_congr rfl fun Z _ => ?_
    simp only [Function.comp_apply]
    split_ifs
    · exact val_zero
    · rw [val_mul, val_listCoeffList hm ts]

/-! ### Packet entries -/

/-- The dense indices below `2 ^ (i + 1) nb` whose tile has a property, as the image of the
modes of the packet. -/
private theorem toFinset_filter_range (i nb : ℕ) (P : ℕ → Bool) :
    ((List.range (2 ^ (i + 1) * nb)).filter fun k => P (k / nb)).toFinset =
      ({Z | P Z.1 = true} : Finset (Fin (2 ^ (i + 1)) × Fin nb)).map
        (finProdFinEquiv.toEmbedding.trans Fin.valEmbedding) := by
  ext k
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, mem_map, mem_filter, mem_univ,
    true_and, Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨hk, h⟩
    exact ⟨finProdFinEquiv.symm ⟨k, hk⟩, h, congrArg Fin.val (finProdFinEquiv.apply_symm_apply _)⟩
  · rintro ⟨Z, h, rfl⟩
    exact ⟨(finProdFinEquiv Z).isLt, by rw [finProdFinEquiv_div]; exact h⟩

/-- **The entry of a packet vertex on coefficient lists** (§D.4.6, p. 63): coefficient extraction
along the row terms, at the exponents `β` of the modes targeting the group, times the powers of
the values of the modes with the group as source. A mode `(y₀, b)` is its dense index
`b + nb y₀` (`finProdFinEquiv`), so `β` is read at dense indices, as from a dense list of
exponents. -/
def packetEntryList (p : ℕ) (fl : List ℕ) (a L i : ℕ) (t : ℤ) (nb : ℕ) (e₁ e₂ differ : Bool)
    (β : ℕ → ℕ) (rows cols : List (ℕ × Bool)) (ζ : List ℕ) : List ℕ :=
  mul p fl
    (listCoeffList p fl ((List.range (2 ^ (i + 1) * nb)).filter fun k =>
        modeTargets i e₁ e₂ (k / nb))
      (rows.map (rowTermList p fl a L i t nb differ cols ζ)) β)
    (prodList p fl (((List.range (2 ^ (i + 1) * nb)).filter fun k =>
        modeSources i e₁ e₂ (k / nb)).map fun k =>
      pow p fl (modeValueList p fl i differ cols (k / nb) (k % nb)) (β k)))

/-- **Packet entries are correct.** For a grid point `t` of valuation `i < a` and ports in slots
below `2 ^ a`, the value of `packetEntryList` in `A_p` is `packetEntry` at the reduction of
`ℤ_(2)`, the value of `ζ` and the exponents `β` at the dense indices of the modes. -/
theorem val_packetEntryList {a L i : ℕ} (hL : L = 2 ^ a) (hia : i < a) {t : ℤ}
    (ht : t ∈ cauchyGrid (2 ^ a))
    (hti : (2 : ℤ) ^ i ∣ t) (hti' : ¬ (2 : ℤ) ^ (i + 1) ∣ t) (nb : ℕ) (e₁ e₂ differ : Bool)
    (β : ℕ → ℕ) {rows cols : List (ℕ × Bool)} (hrows : ∀ r ∈ rows, r.1 < 2 ^ a)
    (hcols : ∀ c ∈ cols, c.1 < 2 ^ a) (ζ : List ℕ) :
    val p fl (packetEntryList p fl a L i t nb e₁ e₂ differ β rows cols ζ) =
      packetEntry (p := nb) (scalarHom p fl) (val p fl ζ) a i t e₁ e₂ differ
        (fun Z => β (finProdFinEquiv Z)) rows cols := by
  rw [packetEntryList, packetEntry, val_mul]
  congr 1
  · rw [val_listCoeffList (List.nodup_range.filter _), toFinset_filter_range,
      TensorNetwork.listCoeff_map, List.map_map, List.map_map]
    refine congrArg₂ _ (List.map_congr_left fun r hr => ?_) rfl
    exact val_rowTermList hL hia ht hti hti' nb differ hcols (hrows r hr) ζ
  · rw [val_prodList, List.map_map, ← List.prod_toFinset _ (List.nodup_range.filter _),
      toFinset_filter_range, prod_map]
    refine prod_congr rfl fun Z _ => ?_
    simp only [Function.comp_apply, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
      Fin.valEmbedding_apply, finProdFinEquiv_div, finProdFinEquiv_mod]
    rw [val_pow, val_modeValueList]

/-- **Packet entries in every ring receiving `A_p`.** Along a ring map `ψ : A_p → S` with `2`
nilpotent in `S`, the value of `packetEntryList` is `packetEntry` over `S` at any ring map
`κ : ℤ_(2) → S` and at the image of `ζ`. -/
theorem map_val_packetEntryList {S : Type*} [CommRing S] (ψ : Ring p fl →+* S) {n : ℕ}
    (hn : (2 : S) ^ n = 0) (κ : ℤ₍₂₎ →+* S) {a L i : ℕ} (hL : L = 2 ^ a) (hia : i < a) {t : ℤ}
    (ht : t ∈ cauchyGrid (2 ^ a)) (hti : (2 : ℤ) ^ i ∣ t) (hti' : ¬ (2 : ℤ) ^ (i + 1) ∣ t)
    (nb : ℕ) (e₁ e₂ differ : Bool) (β : ℕ → ℕ) {rows cols : List (ℕ × Bool)}
    (hrows : ∀ r ∈ rows, r.1 < 2 ^ a) (hcols : ∀ c ∈ cols, c.1 < 2 ^ a) (ζ : List ℕ) :
    ψ (val p fl (packetEntryList p fl a L i t nb e₁ e₂ differ β rows cols ζ)) =
      packetEntry (p := nb) κ (ψ (val p fl ζ)) a i t e₁ e₂ differ (fun Z => β (finProdFinEquiv Z))
        rows cols := by
  rw [val_packetEntryList hL hia ht hti hti' nb e₁ e₂ differ β hrows hcols ζ,
    map_packetEntry ψ two_pow_eq_zero _ _ hia.le hti hti',
    padicInteger_ringHom_ext hn (ψ.comp (scalarHom p fl)) κ]

end NativePacket

end Cslib.Circuits.Frontier

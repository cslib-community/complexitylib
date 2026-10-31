/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.AdjoinRoot
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Size

/-!
# Arithmetic modulo `2 ^ p` and a monic polynomial, on coefficient lists

The coefficient rings of the contraction algorithm of [OpenAI2026ETH] (Appendix D.4.1, p. 57) are
`A_p = (ℤ / 2 ^ p)[U] / (f)` for a monic `f ∈ ℤ[U]` of degree `e`. An element is represented in the
basis `1, U, …, U ^ (e - 1)` by its list of coordinates, each an integer residue modulo `2 ^ p`.
The monic polynomial is given by the list `fl` of its coefficients below the leading one
(`GaloisRingArith.monicOf`), so `e` is the length of `fl`. With `f` irreducible modulo `2`, `A_p` is
the Galois ring `(ℤ / 2 ^ p)[U] / (f)`; nothing here needs irreducibility.

The value of a coefficient list `c` is `∑ i < e, c i U ^ i` in `A_p` (`GaloisRingArith.val`).

* **Addition** (`GaloisRingArith.add`) adds coordinates modulo `2 ^ p`.
* **Multiplication by `U`** (`GaloisRingArith.mulX`) shifts the coordinates up and subtracts the top
  coordinate times `f`, reducing `U ^ e = -∑ i < e, fl i U ^ i`.
* **Multiplication** (`GaloisRingArith.mul`) is shift-and-add: `c d = ∑ i < e, c i (U ^ i d)`,
  accumulating `c i` times the current `U ^ i d` and multiplying it by `U`, `e` times.
* **Powers** (`GaloisRingArith.pow`) `c ^ k` take `k` multiplications from `GaloisRingArith.one`,
  with `k` in unary. In the source the exponents of the mode substitutions are below the
  precision (Appendix D.4.6, p. 63), so they are polynomial.
* **Inversion** (`GaloisRingArith.inv`) starts from the seed `x ^ (2 ^ e - 2)`, a product of `e - 1`
  repeated squares (`GaloisRingArith.seed`), and takes `p` Newton steps `y ↦ y (2 - x y)`, each
  squaring the defect `x y - 1` (`GaloisRingArith.val_mul_newton`). When the seed inverts `x`
  modulo `2`, the result is the inverse (`GaloisRingArith.val_mul_inv`). In a Galois ring, with
  `f` irreducible modulo `2`, this holds for every unit, since the residue field has `2 ^ e`
  elements; that bridge is not made here.

Each operation is correct (`GaloisRingArith.val_add`, `GaloisRingArith.val_mulX`,
`GaloisRingArith.val_mul`) and polynomial-time, with the precision `p` in unary and the
coordinates and the coefficients of `f` in binary (`GaloisRingArith.computableInPolyTime_add`,
`GaloisRingArith.computableInPolyTime_mul`). Their outputs are reduced, with `e` coordinates below
`2 ^ p` (`GaloisRingArith.length_mul`, `GaloisRingArith.lt_of_mem_mul`). These are the
polynomial-time arithmetic claims of Appendix D.4.1 for addition and multiplication, in the case
`ℓ = 1` of the source, where `A = O` has no `V`-coordinates, together with the inversion of units
by inversion modulo two and Newton lifting that the source names (Appendix D.4.1, p. 58).

## Main definitions

* `Cslib.GaloisRingArith.monicOf`: the monic polynomial with given lower coefficients.
* `Cslib.GaloisRingArith.val`: the value of a coefficient list.
* `Cslib.GaloisRingArith.add`, `Cslib.GaloisRingArith.mulX`, `Cslib.GaloisRingArith.mul`,
  `Cslib.GaloisRingArith.one`, `Cslib.GaloisRingArith.pow`, `Cslib.GaloisRingArith.neg`,
  `Cslib.GaloisRingArith.sub`: addition, multiplication by `U`, multiplication, the unit, powers,
  negation and subtraction.
* `Cslib.GaloisRingArith.seed`, `Cslib.GaloisRingArith.newton`, `Cslib.GaloisRingArith.inv`:
  inversion.

## Main results

* `Cslib.GaloisRingArith.val_add`, `Cslib.GaloisRingArith.val_mulX`,
  `Cslib.GaloisRingArith.val_mul`, `Cslib.GaloisRingArith.val_one`,
  `Cslib.GaloisRingArith.val_pow`, `Cslib.GaloisRingArith.val_neg`,
  `Cslib.GaloisRingArith.val_sub`, `Cslib.GaloisRingArith.val_seed`,
  `Cslib.GaloisRingArith.val_mul_inv`: correctness.
* `Cslib.GaloisRingArith.computableInPolyTime_add`,
  `Cslib.GaloisRingArith.computableInPolyTime_mulX`,
  `Cslib.GaloisRingArith.computableInPolyTime_mul`,
  `Cslib.GaloisRingArith.computableInPolyTime_pow`,
  `Cslib.GaloisRingArith.computableInPolyTime_inv`: polynomial time.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.4.1 (p. 57).
-/

@[expose] public section

namespace Cslib.GaloisRingArith

open Polynomial Finset

/-- The monic polynomial `U ^ e + ∑ i < e, fl i U ^ i` of degree `e = fl.length`. -/
noncomputable def monicOf (fl : List ℕ) : ℤ[X] :=
  X ^ fl.length + ∑ i ∈ range fl.length, C (fl.getD i 0 : ℤ) * X ^ i

/-- `monicOf fl` is monic, of degree `fl.length`. -/
theorem monic_monicOf (fl : List ℕ) : (monicOf fl).Monic := by
  unfold monicOf
  apply monic_X_pow_add
  refine (degree_sum_le _ _).trans_lt ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro i hi
  exact (degree_C_mul_X_pow_le _ _).trans_lt (WithBot.coe_lt_coe.mpr (mem_range.mp hi))

/-- The ring `A_p = (ℤ / 2 ^ p)[U] / (f)` for `f = monicOf fl`. -/
abbrev Ring (p : ℕ) (fl : List ℕ) : Type :=
  AdjoinRoot ((monicOf fl).map (Int.castRingHom (ZMod (2 ^ p))))

/-- The value `∑ i < e, c i U ^ i` of a coefficient list in `A_p`, with `e = fl.length`.
Coordinates past `e` are ignored and missing ones are zero. -/
noncomputable def val (p : ℕ) (fl c : List ℕ) : Ring p fl :=
  ∑ i ∈ range fl.length, ((c.getD i 0 : ℕ) : Ring p fl) * AdjoinRoot.root _ ^ i

/-- Coordinatewise sum modulo `2 ^ p`. -/
def add (p : ℕ) (fl c d : List ℕ) : List ℕ :=
  (List.range fl.length).map fun i => (c.getD i 0 + d.getD i 0) % 2 ^ p

/-- Add `k` times `d` to `c`, coordinatewise modulo `2 ^ p`. -/
def addSmul (p : ℕ) (fl c : List ℕ) (k : ℕ) (d : List ℕ) : List ℕ :=
  (List.range fl.length).map fun i => (c.getD i 0 + k * d.getD i 0) % 2 ^ p

/-- Multiplication by `U`: shift the coordinates up and subtract the top coordinate times the
lower coefficients of `f`, modulo `2 ^ p`. -/
def mulX (p : ℕ) (fl c : List ℕ) : List ℕ :=
  (List.range fl.length).map fun i =>
    ((0 :: c).getD i 0 + (2 ^ p - c.getD (fl.length - 1) 0 * fl.getD i 0 % 2 ^ p)) % 2 ^ p

/-- The zero element, with `e` coordinates. -/
def zero (fl : List ℕ) : List ℕ := (List.range fl.length).map fun _ => 0

/-- One step of shift-and-add multiplication by `c`: from `(U ^ i d, ∑ j < i, c j U ^ j d)`,
add `c i U ^ i d` to the accumulator and multiply the current power by `U`. -/
def mulStep (p : ℕ) (fl c : List ℕ) (s : List ℕ × List ℕ) (i : ℕ) : List ℕ × List ℕ :=
  (mulX p fl s.1, addSmul p fl s.2 (c.getD i 0) s.1)

/-- **Multiplication** by shift-and-add. -/
def mul (p : ℕ) (fl c d : List ℕ) : List ℕ :=
  ((List.range fl.length).foldl (mulStep p fl c) (d, zero fl)).2

/-- The unit element `1`, with `e` coordinates. -/
def one (fl : List ℕ) : List ℕ := (List.range fl.length).map fun i => if i = 0 then 1 else 0

/-- **Powers** `c ^ k`, by `k` multiplications; the exponent is read in unary. -/
def pow (p : ℕ) (fl c : List ℕ) (k : ℕ) : List ℕ :=
  (List.range k).foldl (fun acc _ => mul p fl acc c) (one fl)

/-- Negation, coordinatewise modulo `2 ^ p`. -/
def neg (p : ℕ) (fl c : List ℕ) : List ℕ :=
  (List.range fl.length).map fun i => (2 ^ p - c.getD i 0 % 2 ^ p) % 2 ^ p

/-- Subtraction. -/
def sub (p : ℕ) (fl c d : List ℕ) : List ℕ := add p fl c (neg p fl d)

/-- One step of the seed of inversion: from `(x ^ 2 ^ j, x ^ (2 ^ (j + 1) - 2))`, square the power
and multiply it in. -/
def seedStep (p : ℕ) (fl : List ℕ) (s : List ℕ × List ℕ) : List ℕ × List ℕ :=
  (mul p fl s.1 s.1, mul p fl s.2 (mul p fl s.1 s.1))

/-- The seed `x ^ (2 ^ e - 2) = x ^ 2 x ^ 4 ⋯ x ^ (2 ^ (e - 1))` of inversion, by `e - 1`
squarings. In a Galois ring it inverts `x` modulo `2`, since the residue field has `2 ^ e`
elements. -/
def seed (p : ℕ) (fl x : List ℕ) : List ℕ :=
  ((List.range (fl.length - 1)).foldl (fun s _ => seedStep p fl s) (x, one fl)).2

/-- One Newton step `y (2 - x y)` towards the inverse of `x`. -/
def newton (p : ℕ) (fl x y : List ℕ) : List ℕ :=
  mul p fl y (sub p fl (add p fl (one fl) (one fl)) (mul p fl x y))

/-- **Inversion**: `p` Newton steps from the seed. It is the inverse of `x` whenever the seed
inverts `x` modulo `2` (`val_mul_inv`), in particular for every unit of a Galois ring. -/
def inv (p : ℕ) (fl x : List ℕ) : List ℕ :=
  (List.range p).foldl (fun y _ => newton p fl x y) (seed p fl x)

/-! ### Correctness -/

section Correctness

variable {p : ℕ} {fl : List ℕ}

theorem natCast_two_pow : ((2 ^ p : ℕ) : Ring p fl) = 0 := by
  rw [← map_natCast (algebraMap (ZMod (2 ^ p)) (Ring p fl)), ZMod.natCast_self, map_zero]

theorem natCast_mod_two_pow (x : ℕ) : ((x % 2 ^ p : ℕ) : Ring p fl) = (x : Ring p fl) := by
  conv_rhs => rw [← Nat.mod_add_div x (2 ^ p)]
  rw [Nat.cast_add, Nat.cast_mul, natCast_two_pow, zero_mul, add_zero]

/-- The root satisfies `U ^ e = -∑ i < e, fl i U ^ i`. -/
theorem root_pow_length :
    (AdjoinRoot.root _ : Ring p fl) ^ fl.length =
      -∑ i ∈ range fl.length, ((fl.getD i 0 : ℕ) : Ring p fl) * AdjoinRoot.root _ ^ i := by
  have hmap : (monicOf fl).map (Int.castRingHom (ZMod (2 ^ p))) = X ^ fl.length +
      ∑ i ∈ range fl.length, C ((fl.getD i 0 : ℕ) : ZMod (2 ^ p)) * X ^ i := by
    simp [monicOf, Polynomial.map_sum]
  have h := AdjoinRoot.eval₂_root ((monicOf fl).map (Int.castRingHom (ZMod (2 ^ p))))
  conv at h => lhs; arg 3; rw [hmap]
  simp only [eval₂_add, eval₂_finsetSum, eval₂_mul, eval₂_natCast, eval₂_X_pow,
    map_natCast] at h
  exact eq_neg_of_add_eq_zero_left h

@[simp] theorem val_zero : val p fl (zero fl) = 0 := by
  refine sum_eq_zero fun i hi => ?_
  rw [zero, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

/-- **Addition is correct.** -/
theorem val_add (c d : List ℕ) : val p fl (add p fl c d) = val p fl c + val p fl d := by
  rw [val, val, val, ← sum_add_distrib]
  refine sum_congr rfl fun i hi => ?_
  rw [add, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range, natCast_mod_two_pow, Nat.cast_add, add_mul]

/-- **Adding a multiple is correct.** -/
theorem val_addSmul (c : List ℕ) (k : ℕ) (d : List ℕ) :
    val p fl (addSmul p fl c k d) = val p fl c + (k : Ring p fl) * val p fl d := by
  rw [val, val, val, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i hi => ?_
  rw [addSmul, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range, natCast_mod_two_pow, Nat.cast_add,
    Nat.cast_mul]
  ring

/-- Shifting coordinates and subtracting the top one times the lower coefficients of `f` is
multiplication by a root of `f`, in any commutative ring. -/
private theorem shift_sub_mul_sum {R : Type*} [CommRing R] (r : R) (cs fs : ℕ → R) (e : ℕ)
    (hroot : r ^ (e + 1) = -∑ i ∈ range (e + 1), fs i * r ^ i) :
    ∑ i ∈ range (e + 1), ((if i = 0 then 0 else cs (i - 1)) - cs e * fs i) * r ^ i =
      r * ∑ i ∈ range (e + 1), cs i * r ^ i := by
  simp only [sub_mul, sum_sub_distrib]
  rw [sum_range_succ' (fun i => (if i = 0 then 0 else cs (i - 1)) * r ^ i)]
  simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, ite_false, ite_true, zero_mul, add_zero]
  rw [mul_sum, sum_range_succ (fun i => r * (cs i * r ^ i)),
    show r * (cs e * r ^ e) = cs e * r ^ (e + 1) by ring, hroot, mul_neg, mul_sum,
    ← sub_eq_add_neg]
  congr 1
  · exact sum_congr rfl fun i _ => by ring
  · exact sum_congr rfl fun i _ => by ring

/-- **Multiplication by `U` is correct.** -/
theorem val_mulX (c : List ℕ) :
    val p fl (mulX p fl c) = AdjoinRoot.root _ * val p fl c := by
  -- Each coordinate is the shifted coordinate minus the top coordinate times `fl i`.
  have hcoord (i : ℕ) (hi : i < fl.length) : (((mulX p fl c).getD i 0 : ℕ) : Ring p fl) =
      (if i = 0 then 0 else (c.getD (i - 1) 0 : Ring p fl)) -
        (c.getD (fl.length - 1) 0 : Ring p fl) * (fl.getD i 0 : Ring p fl) := by
    rw [mulX, List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_map, List.getElem_range, natCast_mod_two_pow, Nat.cast_add]
    rw [Nat.cast_sub (Nat.mod_lt _ (Nat.two_pow_pos p)).le, natCast_two_pow, natCast_mod_two_pow,
      Nat.cast_mul]
    rcases i with _ | i <;> simp [sub_eq_add_neg]
  rcases Nat.eq_zero_or_pos fl.length with he | he
  · simp [val, he]
  obtain ⟨e, he'⟩ := Nat.exists_eq_add_of_lt he
  rw [Nat.zero_add] at he'
  have hroot := root_pow_length (p := p) (fl := fl)
  rw [val, val, sum_congr rfl fun i hi => by rw [hcoord i (mem_range.mp hi)]]
  rw [he', Nat.add_sub_cancel] at *
  exact shift_sub_mul_sum _ (fun i => (c.getD i 0 : Ring p fl)) (fun i => (fl.getD i 0 : Ring p fl))
    e hroot

/-- **Multiplication is correct.** -/
theorem val_mul (c d : List ℕ) : val p fl (mul p fl c d) = val p fl c * val p fl d := by
  -- After `j` steps the state is `(U ^ j d, ∑ i < j, c i U ^ i d)`.
  have hinv (j : ℕ) :
      val p fl ((List.range j).foldl (mulStep p fl c) (d, zero fl)).1 =
          AdjoinRoot.root _ ^ j * val p fl d ∧
        val p fl ((List.range j).foldl (mulStep p fl c) (d, zero fl)).2 =
          (∑ i ∈ range j, ((c.getD i 0 : ℕ) : Ring p fl) * AdjoinRoot.root _ ^ i) * val p fl d := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, mulStep]
      refine ⟨?_, ?_⟩
      · rw [val_mulX, ih.1, pow_succ]; ring
      · rw [val_addSmul, ih.1, ih.2, sum_range_succ]; ring
  rw [mul, (hinv fl.length).2]
  rfl

/-- **The unit is correct.** -/
@[simp] theorem val_one : val p fl (one fl) = 1 := by
  rcases Nat.eq_zero_or_pos fl.length with he | he
  · -- The defining polynomial is `1`, so the ring is trivial.
    have h1 : (monicOf fl).map (Int.castRingHom (ZMod (2 ^ p))) = 1 := by
      simp [monicOf, he]
    have h : (1 : Ring p fl) = 0 := by
      rw [← map_one (AdjoinRoot.mk ((monicOf fl).map (Int.castRingHom (ZMod (2 ^ p))))),
        AdjoinRoot.mk_eq_zero, h1]
    simp [val, he, h]
  · obtain ⟨e, he'⟩ := Nat.exists_eq_add_of_lt he
    rw [Nat.zero_add] at he'
    rw [val, he', sum_range_succ']
    simp only [one, he']
    rw [sum_eq_zero fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp at hi ⊢; omega)]
      simp]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp

/-- **Powers are correct.** -/
theorem val_pow (c : List ℕ) (k : ℕ) : val p fl (pow p fl c k) = val p fl c ^ k := by
  rw [pow]
  induction k with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      val_mul, ih, pow_succ]

/-- **Negation is correct.** -/
theorem val_neg (c : List ℕ) : val p fl (neg p fl c) = -val p fl c := by
  rw [val, val, ← sum_neg_distrib]
  refine sum_congr rfl fun i hi => ?_
  rw [neg, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range, natCast_mod_two_pow]
  rw [Nat.cast_sub (Nat.mod_lt _ (Nat.two_pow_pos p)).le, natCast_two_pow, natCast_mod_two_pow]
  ring

/-- **Subtraction is correct.** -/
theorem val_sub (c d : List ℕ) : val p fl (sub p fl c d) = val p fl c - val p fl d := by
  rw [sub, val_add, val_neg, sub_eq_add_neg]

/-- **The seed is the power `x ^ (2 ^ e - 2)`.** -/
theorem val_seed (x : List ℕ) : val p fl (seed p fl x) = val p fl x ^ (2 ^ fl.length - 2) := by
  have hinv (j : ℕ) :
      val p fl ((List.range j).foldl (fun s _ => seedStep p fl s) (x, one fl)).1 =
          val p fl x ^ 2 ^ j ∧
        val p fl ((List.range j).foldl (fun s _ => seedStep p fl s) (x, one fl)).2 =
          val p fl x ^ (2 ^ (j + 1) - 2) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, seedStep]
      refine ⟨?_, ?_⟩
      · rw [val_mul, ih.1, ← pow_add, ← two_mul, ← pow_succ']
      · rw [val_mul, val_mul, ih.1, ih.2, ← pow_add, ← pow_add]
        congr 1
        have : 2 ≤ 2 ^ (j + 1) := by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ 2 (j + 1)]
        omega
  rw [seed, (hinv _).2]
  rcases Nat.eq_zero_or_pos fl.length with he | he
  · simp [he]
  · rw [Nat.sub_add_cancel he]

/-- **Newton's step squares the defect**: if `x y = 1 + 2 ^ m w` then
`x (y (2 - x y)) = 1 + 2 ^ (2 m) (-w ^ 2)`. -/
theorem val_mul_newton (x y : List ℕ) {m : ℕ} {w : Ring p fl}
    (h : val p fl x * val p fl y = 1 + 2 ^ m * w) :
    val p fl x * val p fl (newton p fl x y) = 1 + 2 ^ (2 * m) * -w ^ 2 := by
  rw [newton, val_mul, val_sub, val_add, val_mul, val_one]
  have : val p fl x * (val p fl y * (1 + 1 - val p fl x * val p fl y)) =
      (val p fl x * val p fl y) * (2 - val p fl x * val p fl y) := by ring
  rw [this, h, show (2 : Ring p fl) ^ (2 * m) = 2 ^ m * 2 ^ m by rw [two_mul, pow_add]]
  ring

/-- **Inversion is correct** when the seed inverts `x` modulo `2`. -/
theorem val_mul_inv (x : List ℕ) {w : Ring p fl}
    (h : val p fl x * val p fl x ^ (2 ^ fl.length - 2) = 1 + 2 * w) :
    val p fl x * val p fl (inv p fl x) = 1 := by
  have hstep (k : ℕ) : ∃ w' : Ring p fl, val p fl x *
      val p fl ((List.range k).foldl (fun y _ => newton p fl x y) (seed p fl x)) =
        1 + 2 ^ 2 ^ k * w' := by
    induction k with
    | zero => exact ⟨w, by rw [List.range_zero, List.foldl_nil, val_seed, h, pow_zero, pow_one]⟩
    | succ k ih =>
      obtain ⟨w', hw'⟩ := ih
      refine ⟨-w' ^ 2, ?_⟩
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        val_mul_newton _ _ hw', show 2 ^ (k + 1) = 2 * 2 ^ k by ring]
  obtain ⟨w', hw'⟩ := hstep p
  rw [inv, hw']
  have hp : (2 : Ring p fl) ^ 2 ^ p = 0 := by
    have h2p : (2 : Ring p fl) ^ p = 0 := by
      rw [show (2 : Ring p fl) ^ p = ((2 ^ p : ℕ) : Ring p fl) by push_cast; rfl,
        natCast_two_pow]
    exact pow_eq_zero_of_le Nat.lt_two_pow_self.le h2p
  rw [hp, zero_mul, add_zero]

end Correctness

/-! ### Reduced outputs -/

@[simp] theorem length_add (p : ℕ) (fl c d : List ℕ) : (add p fl c d).length = fl.length := by
  simp [add]

@[simp] theorem length_addSmul (p : ℕ) (fl c : List ℕ) (k : ℕ) (d : List ℕ) :
    (addSmul p fl c k d).length = fl.length := by
  simp [addSmul]

@[simp] theorem length_mulX (p : ℕ) (fl c : List ℕ) : (mulX p fl c).length = fl.length := by
  simp [mulX]

@[simp] theorem length_zero (fl : List ℕ) : (zero fl).length = fl.length := by simp [zero]

theorem lt_of_mem_add {p : ℕ} {fl c d : List ℕ} {x : ℕ} (hx : x ∈ add p fl c d) : x < 2 ^ p := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  exact Nat.mod_lt _ (Nat.two_pow_pos p)

theorem lt_of_mem_addSmul {p : ℕ} {fl c : List ℕ} {k : ℕ} {d : List ℕ} {x : ℕ}
    (hx : x ∈ addSmul p fl c k d) : x < 2 ^ p := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  exact Nat.mod_lt _ (Nat.two_pow_pos p)

theorem lt_of_mem_mulX {p : ℕ} {fl c : List ℕ} {x : ℕ} (hx : x ∈ mulX p fl c) : x < 2 ^ p := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  exact Nat.mod_lt _ (Nat.two_pow_pos p)

theorem length_mul (p : ℕ) (fl c d : List ℕ) : (mul p fl c d).length = fl.length := by
  rcases Nat.eq_zero_or_pos fl.length with he | he
  · simp [mul, he, zero]
  obtain ⟨e, he'⟩ := Nat.exists_eq_add_of_lt he
  rw [mul, Nat.zero_add] at *
  rw [he', List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, mulStep,
    length_addSmul, he']

theorem lt_of_mem_mul {p : ℕ} {fl c d : List ℕ} {x : ℕ} (hx : x ∈ mul p fl c d) : x < 2 ^ p := by
  rcases Nat.eq_zero_or_pos fl.length with he | he
  · simp [mul, he, zero] at hx
  obtain ⟨e, he'⟩ := Nat.exists_eq_add_of_lt he
  rw [Nat.zero_add] at he'
  rw [mul, he', List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
    mulStep] at hx
  exact lt_of_mem_addSmul hx

/-! ### Polynomial time -/

section PolyTime

open Turing.MultiTapeTM

variable {α : Type} {encIn : α ↪ List Bool}

/-- Reduction modulo `2 ^ p`, with `p` in unary. -/
@[fun_prop]
theorem computableInPolyTime_mod_two_pow {x p : α → ℕ}
    (hx : ComputableInPolyTime x encIn encNat) (hp : ComputableInPolyTime p encIn encUnary) :
    ComputableInPolyTime (fun a => x a % 2 ^ p a) encIn encNat :=
  ComputableInPolyTime.binary_mod.comp (hx.prod (ComputableInPolyTime.binary_two_pow.comp hp))

/-- A coordinate, at a unary index. -/
theorem computableInPolyTime_getD {c : α → List ℕ} {i : α → ℕ}
    (hc : ComputableInPolyTime c encIn (encList encNat))
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun a => (c a).getD (i a) 0) encIn encNat :=
  (ComputableInPolyTime.listGetD (encA := encNat) 0).comp (hc.prod hi)

/-- Tabulating `e` coordinates, for a unary `e`. -/
theorem computableInPolyTime_tabulate {n : α → ℕ} {g : α → ℕ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hg : ComputableInPolyTime (fun q : α × ℕ => g q.1 q.2) (encPair encIn encUnary) encNat) :
    ComputableInPolyTime (fun x => (List.range (n x)).map (g x)) encIn (encList encNat) :=
  ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hn) hg

private theorem length_polyTime {fl : α → List ℕ}
    (hfl : ComputableInPolyTime fl encIn (encList encNat)) :
    ComputableInPolyTime (fun x => (fl x).length) encIn encUnary :=
  (ComputableInPolyTime.length_list encNat).comp hfl

/-- **Addition is polynomial-time**, with the precision in unary. -/
@[fun_prop]
theorem computableInPolyTime_add {p : α → ℕ} {fl c d : α → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hc : ComputableInPolyTime c encIn (encList encNat))
    (hd : ComputableInPolyTime d encIn (encList encNat)) :
    ComputableInPolyTime (fun x => add (p x) (fl x) (c x) (d x)) encIn (encList encNat) := by
  have h1 := ComputableInPolyTime.fst encIn encUnary
  have h2 := ComputableInPolyTime.snd encIn encUnary
  exact computableInPolyTime_tabulate (length_polyTime hfl)
    (computableInPolyTime_mod_two_pow (ComputableInPolyTime.binary_add.comp
      ((computableInPolyTime_getD (hc.comp h1) h2).prod
        (computableInPolyTime_getD (hd.comp h1) h2))) (hp.comp h1))

/-- **Adding a multiple is polynomial-time**, with the precision in unary. -/
@[fun_prop]
theorem computableInPolyTime_addSmul {p k : α → ℕ} {fl c d : α → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hc : ComputableInPolyTime c encIn (encList encNat))
    (hk : ComputableInPolyTime k encIn encNat)
    (hd : ComputableInPolyTime d encIn (encList encNat)) :
    ComputableInPolyTime (fun x => addSmul (p x) (fl x) (c x) (k x) (d x)) encIn
      (encList encNat) := by
  have h1 := ComputableInPolyTime.fst encIn encUnary
  have h2 := ComputableInPolyTime.snd encIn encUnary
  exact computableInPolyTime_tabulate (length_polyTime hfl)
    (computableInPolyTime_mod_two_pow (ComputableInPolyTime.binary_add.comp
      ((computableInPolyTime_getD (hc.comp h1) h2).prod
        (ComputableInPolyTime.binary_mul' (hk.comp h1)
          (computableInPolyTime_getD (hd.comp h1) h2)))) (hp.comp h1))

/-- **Multiplication by `U` is polynomial-time**, with the precision in unary. -/
@[fun_prop]
theorem computableInPolyTime_mulX {p : α → ℕ} {fl c : α → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hc : ComputableInPolyTime c encIn (encList encNat)) :
    ComputableInPolyTime (fun x => mulX (p x) (fl x) (c x)) encIn (encList encNat) := by
  have h1 := ComputableInPolyTime.fst encIn encUnary
  have h2 := ComputableInPolyTime.snd encIn encUnary
  have hshift := computableInPolyTime_getD
    (ComputableInPolyTime.cons' (ComputableInPolyTime.const 0) (hc.comp h1)) h2
  have htop := computableInPolyTime_getD (hc.comp h1)
    (ComputableInPolyTime.unary_sub' (length_polyTime (hfl.comp h1))
      (ComputableInPolyTime.const 1))
  have hsub := computableInPolyTime_mod_two_pow
    (ComputableInPolyTime.binary_mul' htop (computableInPolyTime_getD (hfl.comp h1) h2))
    (hp.comp h1)
  exact computableInPolyTime_tabulate (length_polyTime hfl)
    (computableInPolyTime_mod_two_pow (ComputableInPolyTime.binary_add.comp (hshift.prod
      (ComputableInPolyTime.binary_sub' (ComputableInPolyTime.binary_two_pow.comp (hp.comp h1))
        hsub))) (hp.comp h1))

/-- A reduced coefficient list, with `e` coordinates below `2 ^ p`, is at most
`e (2 p + 1)` long in binary. -/
theorem length_encList_le {p e : ℕ} {c : List ℕ} (hlen : c.length = e)
    (hlt : ∀ x ∈ c, x < 2 ^ p) : (encList encNat c).length ≤ e * (2 * p + 1) := by
  rw [length_encList]
  calc (c.map fun x => 2 * (encNat x).length + 1).sum
      ≤ (c.map fun x => 2 * (encNat x).length + 1).length • (2 * p + 1) :=
        List.sum_le_length_nsmul _ _ fun n hn => by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hn
          have : (encNat x).length ≤ p := by
            change x.bits.length ≤ p
            rw [Nat.size_eq_bits_len] at *
            exact (Nat.size_eq_bits_len x ▸ Nat.size_le.mpr (hlt x hx))
          omega
    _ = e * (2 * p + 1) := by rw [List.length_map, hlen, smul_eq_mul]

/-- The unit is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_one {fl : α → List ℕ}
    (hfl : ComputableInPolyTime fl encIn (encList encNat)) :
    ComputableInPolyTime (fun x => one (fl x)) encIn (encList encNat) := by
  have h2 := ComputableInPolyTime.snd encIn encUnary
  refine computableInPolyTime_tabulate (g := fun _ i => if i = 0 then 1 else 0)
    (length_polyTime hfl) ?_
  refine (ComputableInPolyTime.ite (encMid := encNat) (c := fun q : α × ℕ => q.2 == 0)
    ((ComputableInPolyTime.beq (h2) (ComputableInPolyTime.const 0)))
    (ComputableInPolyTime.const 1) (ComputableInPolyTime.const 0)).of_enc_eq fun q => ?_
  by_cases h : q.2 = 0 <;> simp [h]

/-- The length bound shared by the folds below: a pair of reduced lists. -/
private theorem polyBounded_reduced {p : α → ℕ} {fl : α → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat)) :
    PolyBounded (fun x => (encIn x).length)
      (fun x => 3 * ((fl x).length * (2 * p x + 1)) + 1) := by
  have hpl := (ComputableInPolyTime.polyBounded_length hp)
  have hfll := (ComputableInPolyTime.polyBounded_length hfl)
  refine (((PolyBounded.const 3).mul (hfll.mul (((PolyBounded.const 2).mul hpl).add
    (PolyBounded.const 1)))).add (PolyBounded.const 1)).mono fun x => ?_
  have h1 : p x ≤ (encUnary (p x)).length := by simp
  have h2 : (fl x).length ≤ (encList encNat (fl x)).length := by
    rw [length_encList]
    calc (fl x).length = ((fl x).map fun _ => 1).sum := by simp
      _ ≤ ((fl x).map fun a => 2 * (encNat a).length + 1).sum :=
        List.sum_le_sum fun a _ => by omega
  have := Nat.mul_le_mul h2 (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h1) 1)
  omega

/-- **Multiplication is polynomial-time**, with the precision in unary. Every intermediate pair is
reduced after its first step, so its length is bounded by the precision and the degree. -/
@[fun_prop]
theorem computableInPolyTime_mul {p : α → ℕ} {fl c d : α → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hc : ComputableInPolyTime c encIn (encList encNat))
    (hd : ComputableInPolyTime d encIn (encList encNat)) :
    ComputableInPolyTime (fun x => mul (p x) (fl x) (c x) (d x)) encIn (encList encNat) := by
  let encS := encPair (encList encNat) (encList encNat)
  have hinit : ComputableInPolyTime (fun x => (d x, zero (fl x))) encIn encS :=
    hd.prod (computableInPolyTime_tabulate (g := fun _ _ => 0) (length_polyTime hfl)
      (ComputableInPolyTime.const 0))
  have hrange : ComputableInPolyTime (fun x => List.range (fl x).length) encIn
      (encList encUnary) :=
    ComputableInPolyTime.range.comp (length_polyTime hfl)
  -- The step, on the input, the state and the unary index.
  have hstep : ComputableInPolyTime
      (fun q : (α × (List ℕ × List ℕ)) × ℕ => mulStep (p q.1.1) (fl q.1.1) (c q.1.1) q.1.2 q.2)
      (encPair (encPair encIn encS) encUnary) encS := by
    have hq := ComputableInPolyTime.fst (encPair encIn encS) encUnary
    have hx := (ComputableInPolyTime.fst encIn encS).comp hq
    have hs := (ComputableInPolyTime.snd encIn encS).comp hq
    have hi := ComputableInPolyTime.snd (encPair encIn encS) encUnary
    have hcur := (ComputableInPolyTime.fst (encList encNat) (encList encNat)).comp hs
    have hacc := (ComputableInPolyTime.snd (encList encNat) (encList encNat)).comp hs
    exact (computableInPolyTime_mulX (hp.comp hx) (hfl.comp hx) hcur).prod
      (computableInPolyTime_addSmul (hp.comp hx) (hfl.comp hx) hacc
        (computableInPolyTime_getD (hc.comp hx) hi) hcur)
  -- Every step's output is reduced, hence of bounded length.
  have hgrowth := polyBounded_reduced hp hfl
  have hfold := ComputableInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encUnary) (encL := encList encUnary)
    (step := fun x s i => mulStep (p x) (fl x) (c x) s i) hinit
    ⟨hrange, hstep, inferInstance, inferInstance⟩ ⟨hgrowth, fun x s i _ => ?_⟩
  · exact (ComputableInPolyTime.snd (encList encNat) (encList encNat)).comp hfold
  · have hcur := length_encList_le (length_mulX (p x) (fl x) s.1) fun _ h => lt_of_mem_mulX h
    have hacc := length_encList_le (length_addSmul (p x) (fl x) s.2 ((c x).getD i 0) s.1)
      fun _ h => lt_of_mem_addSmul h
    simp only [mulStep, encS, length_encPair]
    omega

/-- **Powers are polynomial-time**, with the precision and the exponent in unary. -/
@[fun_prop]
theorem computableInPolyTime_pow {p k : α → ℕ} {fl c : α → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hc : ComputableInPolyTime c encIn (encList encNat))
    (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun x => pow (p x) (fl x) (c x) (k x)) encIn (encList encNat) := by
  have hone := computableInPolyTime_one hfl
  have hstep : ComputableInPolyTime (fun q : (α × List ℕ) × ℕ => mul (p q.1.1) (fl q.1.1) q.1.2
      (c q.1.1)) (encPair (encPair encIn (encList encNat)) encUnary) (encList encNat) := by
    have hq := ComputableInPolyTime.fst (encPair encIn (encList encNat)) encUnary
    have hx := (ComputableInPolyTime.fst encIn (encList encNat)).comp hq
    have hacc := (ComputableInPolyTime.snd encIn (encList encNat)).comp hq
    exact computableInPolyTime_mul (hp.comp hx) (hfl.comp hx) hacc (hc.comp hx)
  have hgrowth := polyBounded_reduced hp hfl
  have hfold := ComputableInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encUnary) (encL := encList encUnary)
    (step := fun x acc _ => mul (p x) (fl x) acc (c x)) hone
    ⟨ComputableInPolyTime.range.comp hk, hstep, inferInstance, inferInstance⟩
    ⟨hgrowth, fun x acc _ _ => ?_⟩
  · exact hfold
  · have := length_encList_le (length_mul (p x) (fl x) acc (c x)) fun _ h => lt_of_mem_mul h
    omega

/-- **Negation is polynomial-time**, with the precision in unary. -/
@[fun_prop]
theorem computableInPolyTime_neg {p : α → ℕ} {fl c : α → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hc : ComputableInPolyTime c encIn (encList encNat)) :
    ComputableInPolyTime (fun x => neg (p x) (fl x) (c x)) encIn (encList encNat) := by
  have h1 := ComputableInPolyTime.fst encIn encUnary
  have h2 := ComputableInPolyTime.snd encIn encUnary
  exact computableInPolyTime_tabulate (length_polyTime hfl)
    (computableInPolyTime_mod_two_pow (ComputableInPolyTime.binary_sub'
      (ComputableInPolyTime.binary_two_pow.comp (hp.comp h1))
      (computableInPolyTime_mod_two_pow (computableInPolyTime_getD (hc.comp h1) h2)
        (hp.comp h1))) (hp.comp h1))

/-- **Subtraction is polynomial-time**, with the precision in unary. -/
@[fun_prop]
theorem computableInPolyTime_sub {p : α → ℕ} {fl c d : α → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hc : ComputableInPolyTime c encIn (encList encNat))
    (hd : ComputableInPolyTime d encIn (encList encNat)) :
    ComputableInPolyTime (fun x => sub (p x) (fl x) (c x) (d x)) encIn (encList encNat) :=
  computableInPolyTime_add hp hfl hc (computableInPolyTime_neg hp hfl hd)

/-- **A Newton step is polynomial-time**, with the precision in unary. -/
@[fun_prop]
theorem computableInPolyTime_newton {p : α → ℕ} {fl x y : α → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hx : ComputableInPolyTime x encIn (encList encNat))
    (hy : ComputableInPolyTime y encIn (encList encNat)) :
    ComputableInPolyTime (fun a => newton (p a) (fl a) (x a) (y a)) encIn (encList encNat) :=
  computableInPolyTime_mul hp hfl hy (computableInPolyTime_sub hp hfl
    (computableInPolyTime_add hp hfl (computableInPolyTime_one hfl)
      (computableInPolyTime_one hfl)) (computableInPolyTime_mul hp hfl hx hy))

/-- **The seed of inversion is polynomial-time**, with the precision in unary. -/
@[fun_prop]
theorem computableInPolyTime_seed {p : α → ℕ} {fl x : α → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hx : ComputableInPolyTime x encIn (encList encNat)) :
    ComputableInPolyTime (fun a => seed (p a) (fl a) (x a)) encIn (encList encNat) := by
  let encS := encPair (encList encNat) (encList encNat)
  have hstep : ComputableInPolyTime
      (fun q : (α × (List ℕ × List ℕ)) × ℕ => seedStep (p q.1.1) (fl q.1.1) q.1.2)
      (encPair (encPair encIn encS) encUnary) encS := by
    have hq := ComputableInPolyTime.fst (encPair encIn encS) encUnary
    have ha := (ComputableInPolyTime.fst encIn encS).comp hq
    have hs := (ComputableInPolyTime.snd encIn encS).comp hq
    have h1 := (ComputableInPolyTime.fst (encList encNat) (encList encNat)).comp hs
    have h2 := (ComputableInPolyTime.snd (encList encNat) (encList encNat)).comp hs
    have hsq := computableInPolyTime_mul (hp.comp ha) (hfl.comp ha) h1 h1
    exact hsq.prod (computableInPolyTime_mul (hp.comp ha) (hfl.comp ha) h2 hsq)
  have hfold := ComputableInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encUnary) (encL := encList encUnary)
    (step := fun a s _ => seedStep (p a) (fl a) s)
    (hx.prod (computableInPolyTime_one hfl))
    ⟨ComputableInPolyTime.range.comp (ComputableInPolyTime.unary_sub' (length_polyTime hfl)
      (ComputableInPolyTime.const 1)), hstep, inferInstance, inferInstance⟩
    ⟨polyBounded_reduced hp hfl, fun a s _ _ => ?_⟩
  · exact (ComputableInPolyTime.snd (encList encNat) (encList encNat)).comp hfold
  · have h1 := length_encList_le (length_mul (p a) (fl a) s.1 s.1) fun _ h => lt_of_mem_mul h
    have h2 := length_encList_le (length_mul (p a) (fl a) s.2 (mul (p a) (fl a) s.1 s.1))
      fun _ h => lt_of_mem_mul h
    simp only [seedStep, length_encPair]
    omega

/-- **Inversion is polynomial-time**, with the precision in unary. -/
@[fun_prop]
theorem computableInPolyTime_inv {p : α → ℕ} {fl x : α → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hx : ComputableInPolyTime x encIn (encList encNat)) :
    ComputableInPolyTime (fun a => inv (p a) (fl a) (x a)) encIn (encList encNat) := by
  have hstep : ComputableInPolyTime
      (fun q : (α × List ℕ) × ℕ => newton (p q.1.1) (fl q.1.1) (x q.1.1) q.1.2)
      (encPair (encPair encIn (encList encNat)) encUnary) (encList encNat) := by
    have hq := ComputableInPolyTime.fst (encPair encIn (encList encNat)) encUnary
    have ha := (ComputableInPolyTime.fst encIn (encList encNat)).comp hq
    have hy := (ComputableInPolyTime.snd encIn (encList encNat)).comp hq
    exact computableInPolyTime_newton (hp.comp ha) (hfl.comp ha) (hx.comp ha) hy
  exact ComputableInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encUnary) (encL := encList encUnary)
    (step := fun a y _ => newton (p a) (fl a) (x a) y) (computableInPolyTime_seed hp hfl hx)
    ⟨ComputableInPolyTime.range.comp hp, hstep, inferInstance, inferInstance⟩
    ⟨polyBounded_reduced hp hfl, fun a y _ _ => by
      have := length_encList_le (length_mul (p a) (fl a) y
        (sub (p a) (fl a) (add (p a) (fl a) (one (fl a)) (one (fl a))) (mul (p a) (fl a) (x a) y)))
        fun _ h => lt_of_mem_mul h
      simp only [newton]
      omega⟩

end PolyTime

end Cslib.GaloisRingArith

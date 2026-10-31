/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.GaloisRingInterpolation
public import Complexity.Computability.PolyTime.GaloisRingUnits
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Mathlib.Data.List.GetD

/-!
# Coordinates, precision changes and truncated products over `(ℤ / 2 ^ p)[U] / (f)`

Supporting operations on the coefficient lists of
`Complexity/Computability/PolyTime/GaloisRingArithmetic.lean`, for the native recovery step of
the contraction algorithm of [OpenAI2026ETH] (Appendix D.4.4, pp. 60–61).

* **Coordinates.** The coordinates of an element of `A_p` in the basis `1, U, …, U ^ (e - 1)` are
  determined modulo `2 ^ p` (`GaloisRingArith.mod_eq_of_val_eq`), and every element is the value
  of a reduced coefficient list (`GaloisRingArith.exists_val_eq`).
* **Precision.** Reduction `A_N → A_n` for `n ≤ N` (`GaloisRingArith.reduce`) keeps the
  coordinates (`GaloisRingArith.reduce_val`), and its kernel is `2 ^ n A_N`
  (`GaloisRingArith.exists_eq_add_of_reduce_eq`). Dividing the coordinates of `2 ^ Δ y` by `2 ^ Δ`
  gives `y` modulo `2 ^ (N - Δ)` (`GaloisRingArith.val_shiftDown`): this is how a sum that is
  known to be divisible by `2 ^ Δ` loses its common power of two.
* **Truncated products** (`GaloisRingArith.tmul`) of polynomials in `z` over `A_p`: the first
  `J` coefficients of a product, by the Cauchy formula (`GaloisRingArith.val_tmul`).

Truncated products and `GaloisRingArith.shiftDown` are polynomial-time, with the precision, the
length and the shift in unary (`GaloisRingArith.computableInPolyTime_tmul`,
`GaloisRingArith.computableInPolyTime_shiftDown`).

## Main definitions

* `Cslib.GaloisRingArith.reduce`: reduction to a lower precision.
* `Cslib.GaloisRingArith.shiftDown`: division of the coordinates by `2 ^ Δ`.
* `Cslib.GaloisRingArith.tmul`: truncated products.

## Main results

* `Cslib.GaloisRingArith.mod_eq_of_val_eq`, `Cslib.GaloisRingArith.exists_val_eq`: coordinates.
* `Cslib.GaloisRingArith.val_shiftDown`: cancelling a common power of two.
* `Cslib.GaloisRingArith.exists_eq_add_of_reduce_eq`,
  `Cslib.GaloisRingArith.exists_val_eq_add_of_val_eq`: the kernel of reduction is `2 ^ n A_N`.
* `Cslib.GaloisRingArith.val_tmul`: truncated products are correct.
* `Cslib.GaloisRingArith.computableInPolyTime_tmul`,
  `Cslib.GaloisRingArith.computableInPolyTime_shiftDown`: polynomial time.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.4.1 and D.4.4
  (pp. 57–61).
-/

@[expose] public section

namespace Cslib.GaloisRingArith

open Polynomial Finset

variable {p : ℕ} {fl : List ℕ}

/-! ### Coordinates -/

/-- `A_0` is the zero ring. -/
theorem subsingleton_ring_zero : Subsingleton (Ring 0 fl) := by
  have : Subsingleton (ZMod (2 ^ 0)) := by rw [pow_zero]; infer_instance
  exact (AdjoinRoot.of ((monicOf fl).map (Int.castRingHom (ZMod (2 ^ 0))))).codomain_trivial

private theorem nontrivial_zmod (hp : 0 < p) : Nontrivial (ZMod (2 ^ p)) :=
  have : Fact (1 < 2 ^ p) := ⟨Nat.one_lt_two_pow hp.ne'⟩
  ZMod.nontrivial _

/-- A coefficient list is the class of the polynomial with those coefficients. -/
theorem val_eq_mk (c : List ℕ) : val p fl c = AdjoinRoot.mk _
    (∑ i ∈ range fl.length, C ((c.getD i 0 : ℕ) : ZMod (2 ^ p)) * X ^ i) := by
  simp only [val, map_sum, map_mul, map_pow, AdjoinRoot.mk_X, map_natCast]

/-- The single coordinate list `[c]` has value `c`. -/
@[simp] theorem val_singleton (c : ℕ) : val p fl [c] = (c : Ring p fl) := by
  rcases Nat.eq_zero_or_pos fl.length with he | he
  · -- The defining polynomial is `1`, so the ring is trivial.
    have h1 : (monicOf fl).map (Int.castRingHom (ZMod (2 ^ p))) = 1 := by simp [monicOf, he]
    have h : (1 : Ring p fl) = 0 := by
      rw [← map_one (AdjoinRoot.mk ((monicOf fl).map (Int.castRingHom (ZMod (2 ^ p))))),
        AdjoinRoot.mk_eq_zero, h1]
    exact (subsingleton_of_zero_eq_one h.symm).elim _ _
  · rw [val, ← sum_range_add_sum_Ico _ he, sum_range_one, sum_eq_zero fun i hi => by
      rw [List.getD_eq_default _ _ (by simp at hi ⊢; omega)]; simp]
    simp

/-- The coordinates of the value of a coefficient list, read off by division by the monic
polynomial. -/
theorem coeff_modByMonicHom_val (c : List ℕ) (i : ℕ) :
    (AdjoinRoot.modByMonicHom ((monic_monicOf fl).map (Int.castRingHom (ZMod (2 ^ p))))
      (val p fl c)).coeff i = if i < fl.length then ((c.getD i 0 : ℕ) : ZMod (2 ^ p)) else 0 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have : Subsingleton (ZMod (2 ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  have := nontrivial_zmod hp
  rw [val_eq_mk, AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff ((monic_monicOf fl).map _)).mpr]
  · simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
      sum_ite_eq, mem_range]
  · rw [(monic_monicOf fl).degree_map, degree_eq_natDegree (monic_monicOf fl).ne_zero,
      natDegree_monicOf]
    refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
      fun i hi => ?_)
    exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast mem_range.mp hi)

/-- **Coordinates are determined modulo `2 ^ p`.** -/
theorem mod_eq_of_val_eq {c d : List ℕ} (h : val p fl c = val p fl d) {i : ℕ}
    (hi : i < fl.length) : c.getD i 0 % 2 ^ p = d.getD i 0 % 2 ^ p := by
  have := congrArg (fun y => (AdjoinRoot.modByMonicHom
    ((monic_monicOf fl).map (Int.castRingHom (ZMod (2 ^ p)))) y).coeff i) h
  simp only [coeff_modByMonicHom_val, hi, ↓reduceIte] at this
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp this

/-- **Every element is the value of a reduced coefficient list.** -/
theorem exists_val_eq (y : Ring p fl) :
    ∃ r : List ℕ, r.length = fl.length ∧ (∀ x ∈ r, x < 2 ^ p) ∧ val p fl r = y := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have := subsingleton_ring_zero (fl := fl)
    exact ⟨zero fl, by simp, by simp [zero], Subsingleton.elim _ _⟩
  have := nontrivial_zmod hp
  have hg : ((monicOf fl).map (Int.castRingHom (ZMod (2 ^ p)))).Monic := (monic_monicOf fl).map _
  have he : ((monicOf fl).map (Int.castRingHom (ZMod (2 ^ p)))).natDegree = fl.length := by
    rw [(monic_monicOf fl).natDegree_map, natDegree_monicOf]
  set P := AdjoinRoot.modByMonicHom hg y
  refine ⟨(List.range fl.length).map fun i => (P.coeff i).val, by simp, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact ZMod.val_lt _
  · have hsum := (AdjoinRoot.powerBasis' hg).basis.sum_repr y
    have hrepr : ∀ i, (AdjoinRoot.powerBasis' hg).basis.repr y i = P.coeff i := fun _ => rfl
    rw [PowerBasis.coe_basis] at hsum
    simp only [AdjoinRoot.powerBasis'_gen, hrepr] at hsum
    rw [Fin.sum_univ_eq_sum_range (fun i => P.coeff i • AdjoinRoot.root _ ^ i),
      AdjoinRoot.powerBasis'_dim, he] at hsum
    conv_rhs => rw [← hsum]
    rw [val]
    refine sum_congr rfl fun i hi => ?_
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range,
      Algebra.smul_def, ← map_natCast (algebraMap (ZMod (2 ^ p)) _), ZMod.natCast_zmod_val]

/-- Mapping a function that fixes `0` commutes with reading a coordinate. -/
theorem getD_map_of_map_zero {f : ℕ → ℕ} (hf : f 0 = 0) (c : List ℕ) (i : ℕ) :
    (c.map f).getD i 0 = f (c.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases c[i]? <;> simp [hf]

/-- Scaling every coordinate by `k` multiplies the value by `k`. -/
theorem val_map_mul (k : ℕ) (c : List ℕ) : val p fl (c.map (k * ·)) = k * val p fl c := by
  rw [val, val, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [getD_map_of_map_zero (mul_zero k)]
  push_cast
  ring

/-! ### Changing the precision -/

/-- Reduction `A_N → A_n` from a higher precision to a lower one. -/
noncomputable def reduce {n N : ℕ} (h : n ≤ N) (fl : List ℕ) : Ring N fl →+* Ring n fl :=
  AdjoinRoot.map (ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ n))) _ _
    (GaloisRing.map_castHom_map (monicOf fl) (pow_dvd_pow 2 h)).symm.dvd

/-- **Reduction keeps the coordinates.** -/
theorem reduce_val {n N : ℕ} (h : n ≤ N) (c : List ℕ) :
    reduce h fl (val N fl c) = val n fl c := by
  simp only [reduce, val, map_sum, map_mul, map_pow, map_natCast, AdjoinRoot.map_root]

/-- **Equal reductions differ by a multiple of `2 ^ n`**: the kernel of reduction
`A_N → A_n` is `2 ^ n A_N`. -/
theorem exists_eq_add_of_reduce_eq {n N : ℕ} (h : n ≤ N) {x y : Ring N fl}
    (hxy : reduce h fl x = reduce h fl y) : ∃ c, x = y + 2 ^ n * c := by
  obtain ⟨r, -, -, rfl⟩ := exists_val_eq x
  obtain ⟨s, -, -, rfl⟩ := exists_val_eq y
  rw [reduce_val, reduce_val] at hxy
  choose! q hq using fun i (hi : i < fl.length) => Nat.modEq_iff_dvd.mp (mod_eq_of_val_eq hxy hi)
  refine ⟨-∑ i ∈ range fl.length, ((q i : ℤ) : Ring N fl) * AdjoinRoot.root _ ^ i, ?_⟩
  rw [val, val, mul_neg, mul_sum, ← sub_eq_add_neg, ← sum_sub_distrib]
  refine sum_congr rfl fun i hi => ?_
  have hi' := congrArg (Int.cast : ℤ → Ring N fl) (hq i (mem_range.mp hi))
  push_cast at hi'
  linear_combination (-(AdjoinRoot.root _ ^ i : Ring N fl)) * hi'

/-- **A value at a lower precision lifts with an error divisible by `2 ^ n`**: a coefficient list
whose value in `A_n` is the reduction of `y ∈ A_N` has value `y + 2 ^ n c` in `A_N`. -/
theorem exists_val_eq_add_of_val_eq {n N : ℕ} (h : n ≤ N) {w : List ℕ} {y : Ring N fl}
    (hw : val n fl w = reduce h fl y) : ∃ c, val N fl w = y + 2 ^ n * c :=
  exists_eq_add_of_reduce_eq h (by rw [reduce_val, hw])

/-- Division of each coordinate by `2 ^ Δ`. -/
def shiftDown (Δ : ℕ) (c : List ℕ) : List ℕ := c.map (· / 2 ^ Δ)

/-- **Cancelling a common power of two.** If a coefficient list has value `2 ^ Δ y` at precision
`n + Δ`, dividing its coordinates by `2 ^ Δ` gives the reduction of `y` to precision `n`. -/
theorem val_shiftDown {n Δ : ℕ} {s : List ℕ} {y : Ring (n + Δ) fl}
    (h : val (n + Δ) fl s = 2 ^ Δ * y) :
    val n fl (shiftDown Δ s) = reduce (Nat.le_add_right n Δ) fl y := by
  obtain ⟨r, -, -, rfl⟩ := exists_val_eq y
  rw [reduce_val, val, val]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  have hmod := mod_eq_of_val_eq (h.trans (by
    rw [show (2 : Ring (n + Δ) fl) ^ Δ = ((2 ^ Δ : ℕ) : Ring (n + Δ) fl) by push_cast; rfl,
      ← val_map_mul])) hi'
  rw [getD_map_of_map_zero (mul_zero _), pow_add, mul_comm (2 ^ n),
    Nat.mul_mod_mul_left] at hmod
  rw [shiftDown, getD_map_of_map_zero (f := (· / 2 ^ Δ)) (Nat.zero_div _)]
  congr 1
  set x := s.getD i 0
  -- `x = 2 ^ Δ (r_i mod 2 ^ n) + 2 ^ Δ 2 ^ n k`.
  have hx : x = 2 ^ Δ * (r.getD i 0 % 2 ^ n + 2 ^ n * (x / (2 ^ Δ * 2 ^ n))) := by
    conv_lhs => rw [← Nat.mod_add_div x (2 ^ Δ * 2 ^ n), hmod]
    ring
  rw [hx, Nat.mul_div_cancel_left _ (Nat.two_pow_pos Δ), Nat.cast_add, natCast_mod_two_pow,
    Nat.cast_mul, natCast_two_pow, zero_mul, add_zero]

/-! ### Truncated products -/

/-- The coefficient of `z ^ j` in the product of two polynomials over `A_p`, by the Cauchy
formula `∑ i ≤ j, P_i R_(j - i)`. -/
def cauchyCoeff (p : ℕ) (fl : List ℕ) (P R : List (List ℕ)) (j : ℕ) : List ℕ :=
  (List.range (j + 1)).foldl
    (fun acc i => add p fl acc (mul p fl (P.getD i []) (R.getD (j - i) []))) (zero fl)

/-- The **truncated product**: the first `J` coefficients of the product of two polynomials over
`A_p`. -/
def tmul (p : ℕ) (fl : List ℕ) (J : ℕ) (P R : List (List ℕ)) : List (List ℕ) :=
  (List.range J).map (cauchyCoeff p fl P R)

theorem val_cauchyCoeff (P R : List (List ℕ)) (j : ℕ) :
    val p fl (cauchyCoeff p fl P R j) =
      ∑ i ∈ range (j + 1), val p fl (P.getD i []) * val p fl (R.getD (j - i) []) := by
  have h (m : ℕ) : val p fl ((List.range m).foldl
      (fun acc i => add p fl acc (mul p fl (P.getD i []) (R.getD (j - i) []))) (zero fl)) =
        ∑ i ∈ range m, val p fl (P.getD i []) * val p fl (R.getD (j - i) []) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, val_add, val_mul,
        ih, sum_range_succ]
  exact h _

@[simp] theorem length_tmul (J : ℕ) (P R : List (List ℕ)) : (tmul p fl J P R).length = J := by
  simp [tmul]

/-- **Truncated products are correct**: below `z ^ J` the coefficients are those of the product. -/
theorem val_tmul {J : ℕ} (P R : List (List ℕ)) {j : ℕ} (hj : j < J) :
    val p fl ((tmul p fl J P R).getD j []) =
      ∑ i ∈ range (j + 1), val p fl (P.getD i []) * val p fl (R.getD (j - i) []) := by
  rw [tmul, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range,
    val_cauchyCoeff]

/-! ### Odd scalars are units -/

/-- An odd natural number is a unit of `A_p`. -/
theorem isUnit_natCast_of_odd {o : ℕ} (ho : Odd o) : IsUnit (o : Ring p fl) := by
  have hcop : Nat.Coprime o (2 ^ p) := (Nat.coprime_two_right.mpr ho).pow_right p
  have := (ZMod.unitOfCoprime o hcop).isUnit.map (algebraMap (ZMod (2 ^ p)) (Ring p fl))
  simpa using this

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

/-- The zero element is polynomial-time. -/
theorem computableInPolyTime_zero {fl : α → List ℕ}
    (hfl : ComputableInPolyTime fl encIn (encList encNat)) :
    ComputableInPolyTime (fun x => zero (fl x)) encIn (encList encNat) :=
  computableInPolyTime_tabulate (g := fun _ _ => 0) (lengthPolyTime hfl)
    (ComputableInPolyTime.const 0)

/-- The length `e (2 p + 1)` of a reduced coefficient list is polynomially bounded. -/
theorem polyBounded_reducedLength {p : α → ℕ} {fl : α → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat)) :
    PolyBounded (fun x => (encIn x).length) (fun x => (fl x).length * (2 * p x + 1)) := by
  have hpl : PolyBounded (fun x => (encIn x).length) p := by
    simpa using (ComputableInPolyTime.polyBounded_length hp)
  have hfll : PolyBounded (fun x => (encIn x).length) fun x => (fl x).length :=
    (lengthPolyTime hfl).polyBounded_length.mono fun x => by simp
  exact hfll.mul (((PolyBounded.const 2).mul hpl).add (PolyBounded.const 1))

/-- **Division of the coordinates by `2 ^ Δ` is polynomial-time**, with `Δ` in unary. -/
@[fun_prop]
theorem computableInPolyTime_shiftDown {Δ : α → ℕ} {c : α → List ℕ}
    (hΔ : ComputableInPolyTime Δ encIn encUnary)
    (hc : ComputableInPolyTime c encIn (encList encNat)) :
    ComputableInPolyTime (fun x => shiftDown (Δ x) (c x)) encIn (encList encNat) :=
  ComputableInPolyTime.mapWithInput hc (ComputableInPolyTime.binary_div.comp
    ((ComputableInPolyTime.snd encIn encNat).prod (ComputableInPolyTime.binary_two_pow.comp
      (hΔ.comp (ComputableInPolyTime.fst encIn encNat)))))

theorem lt_of_mem_cauchyCoeff {P R : List (List ℕ)} {j x : ℕ} (hx : x ∈ cauchyCoeff p fl P R j) :
    x < 2 ^ p := by
  rw [cauchyCoeff, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hx
  exact lt_of_mem_add hx

theorem length_cauchyCoeff (P R : List (List ℕ)) (j : ℕ) :
    (cauchyCoeff p fl P R j).length = fl.length := by
  rw [cauchyCoeff, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
    length_add]

/-- **Cauchy coefficients are polynomial-time**, with the precision and the index in unary. -/
@[fun_prop]
theorem computableInPolyTime_cauchyCoeff {p j : α → ℕ} {fl : α → List ℕ}
    {P R : α → List (List ℕ)}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hP : ComputableInPolyTime P encIn (encList (encList encNat)))
    (hR : ComputableInPolyTime R encIn (encList (encList encNat)))
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => cauchyCoeff (p x) (fl x) (P x) (R x) (j x)) encIn
      (encList encNat) := by
  have hstep : ComputableInPolyTime (fun q : (α × List ℕ) × ℕ =>
      add (p q.1.1) (fl q.1.1) q.1.2 (mul (p q.1.1) (fl q.1.1) ((P q.1.1).getD q.2 [])
        ((R q.1.1).getD (j q.1.1 - q.2) [])))
      (encPair (encPair encIn (encList encNat)) encUnary) (encList encNat) := by
    have hq := ComputableInPolyTime.fst (encPair encIn (encList encNat)) encUnary
    have hx := (ComputableInPolyTime.fst encIn (encList encNat)).comp hq
    have hacc := (ComputableInPolyTime.snd encIn (encList encNat)).comp hq
    have hi := ComputableInPolyTime.snd (encPair encIn (encList encNat)) encUnary
    exact computableInPolyTime_add (hp.comp hx) (hfl.comp hx) hacc
      (computableInPolyTime_mul (hp.comp hx) (hfl.comp hx) (getDPolyTime (hP.comp hx) hi)
        (getDPolyTime (hR.comp hx) (ComputableInPolyTime.unary_sub' (hj.comp hx) hi)))
  exact ComputableInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encUnary) (encL := encList encUnary)
    (step := fun x acc i => add (p x) (fl x) acc (mul (p x) (fl x) ((P x).getD i [])
      ((R x).getD (j x - i) [])))
    (computableInPolyTime_zero hfl)
    ⟨ComputableInPolyTime.range.comp
      (ComputableInPolyTime.unary_add' hj (ComputableInPolyTime.const 1)),
      hstep, inferInstance, inferInstance⟩
    ⟨polyBounded_reducedLength hp hfl, fun x acc i _ => by
      have := length_encList_le (length_add (p x) (fl x) acc (mul (p x) (fl x) ((P x).getD i [])
        ((R x).getD (j x - i) []))) fun _ h => lt_of_mem_add h
      omega⟩

/-- **Truncated products are polynomial-time**, with the precision and the length in unary. -/
@[fun_prop]
theorem computableInPolyTime_tmul {p J : α → ℕ} {fl : α → List ℕ} {P R : α → List (List ℕ)}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hJ : ComputableInPolyTime J encIn encUnary)
    (hP : ComputableInPolyTime P encIn (encList (encList encNat)))
    (hR : ComputableInPolyTime R encIn (encList (encList encNat))) :
    ComputableInPolyTime (fun x => tmul (p x) (fl x) (J x) (P x) (R x)) encIn
      (encList (encList encNat)) := by
  have h1 := ComputableInPolyTime.fst encIn encUnary
  have h2 := ComputableInPolyTime.snd encIn encUnary
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hJ)
    (computableInPolyTime_cauchyCoeff (hp.comp h1) (hfl.comp h1) (hP.comp h1) (hR.comp h1) h2)

/-- Every coefficient of a truncated product is small. -/
theorem small_of_mem_tmul {J : ℕ} {P R : List (List ℕ)} {c : List ℕ}
    (hc : c ∈ tmul p fl J P R) : Small p fl c := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hc
  exact small_of_lt (length_cauchyCoeff P R j) fun _ h => lt_of_mem_cauchyCoeff h

end PolyTime

end Cslib.GaloisRingArith

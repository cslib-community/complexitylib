/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.GaloisRingArithmetic
public import Mathlib.Algebra.Polynomial.BigOperators
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Size

/-!
# Polynomials over `(ℤ / 2 ^ p)[U] / (f)` and Lagrange interpolation, on coefficient lists

Polynomials in `z` over the coefficient ring `A_p = (ℤ / 2 ^ p)[U] / (f)` of
`Complexity/Computability/PolyTime/GaloisRingArithmetic.lean` are lists of coefficients,
constant first, each a coefficient list of `A_p` (`GaloisRingArith.pval`).

* **Addition** (`GaloisRingArith.padd`), **scaling** (`GaloisRingArith.psmul`) and
  **multiplication by `z - v`** (`GaloisRingArith.pmulLinear`).
* **Evaluation** (`GaloisRingArith.peval`) by Horner's rule.
* **Lagrange interpolation** (`GaloisRingArith.interp`) at nodes `v₀, …, v_{n-1}`: the sum of
  `y_i (∏_{j ≠ i} (v_i - v_j))⁻¹ ∏_{j ≠ i} (z - v_j)`, with the inverses of
  `GaloisRingArith.inv`. When those inverses are correct, for instance at nodes with unit
  differences in a Galois ring, the result takes the value `y_i` at `v_i`
  (`GaloisRingArith.eval_pval_interp`). It has at most `n + 1` coefficients and degree below `n`
  (`GaloisRingArith.pval_interp`); at nodes with unit differences, a polynomial of degree below
  `n` is determined by its values there.

Every operation is polynomial-time, with the precision in unary
(`GaloisRingArith.computableInPolyTime_interp` and the rules before it).

This is the interpolation step of the contraction algorithm of [OpenAI2026ETH]
(Appendix D.4.4, p. 61), which recovers `F (t + α z)` modulo `2 ^ p_t` from its values at
`M (2 L - 1) + 1` binary-coordinate lifts.

## Main definitions

* `Cslib.GaloisRingArith.pval`: the polynomial of a list of coefficient lists.
* `Cslib.GaloisRingArith.padd`, `Cslib.GaloisRingArith.psmul`, `Cslib.GaloisRingArith.pmulLinear`,
  `Cslib.GaloisRingArith.peval`: polynomial arithmetic.
* `Cslib.GaloisRingArith.interp`: Lagrange interpolation.

## Main results

* `Cslib.GaloisRingArith.pval_padd`, `Cslib.GaloisRingArith.pval_psmul`,
  `Cslib.GaloisRingArith.pval_pmulLinear`, `Cslib.GaloisRingArith.peval_eq`: correctness.
* `Cslib.GaloisRingArith.eval_pval_interp`: interpolation takes the given values.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.4.4 (p. 61).
-/

@[expose] public section

namespace Cslib.GaloisRingArith

open Polynomial Finset

variable {p : ℕ} {fl : List ℕ}

/-- The polynomial `∑ k, P_k z ^ k` over `A_p` of a list of coefficient lists. -/
noncomputable def pval (p : ℕ) (fl : List ℕ) (P : List (List ℕ)) : (Ring p fl)[X] :=
  ∑ k ∈ range P.length, C (val p fl (P.getD k [])) * X ^ k

/-- The empty coefficient list has value zero. -/
@[simp] theorem val_nil : val p fl [] = 0 := by simp [val]

/-- Coefficientwise sum, of length the longer length. -/
def padd (p : ℕ) (fl : List ℕ) (P Q : List (List ℕ)) : List (List ℕ) :=
  (List.range (max P.length Q.length)).map fun k => add p fl (P.getD k []) (Q.getD k [])

/-- Scaling by an element of `A_p`. -/
def psmul (p : ℕ) (fl c : List ℕ) (P : List (List ℕ)) : List (List ℕ) :=
  P.map fun a => mul p fl c a

/-- Multiplication by `z - v`. -/
def pmulLinear (p : ℕ) (fl v : List ℕ) (P : List (List ℕ)) : List (List ℕ) :=
  (List.range (P.length + 1)).map fun k =>
    sub p fl (([] :: P).getD k []) (mul p fl v (P.getD k []))

/-- Evaluation at `z` by Horner's rule. -/
def peval (p : ℕ) (fl : List ℕ) (P : List (List ℕ)) (z : List ℕ) : List ℕ :=
  P.foldr (fun a acc => add p fl a (mul p fl z acc)) (zero fl)

/-- Extending a polynomial by zero coefficients does not change it. -/
theorem pval_eq_sum_of_le (P : List (List ℕ)) {n : ℕ} (h : P.length ≤ n) :
    pval p fl P = ∑ k ∈ range n, C (val p fl (P.getD k [])) * X ^ k := by
  rw [pval, ← sum_range_add_sum_Ico _ h]
  rw [sum_eq_zero (s := Ico _ _) fun k hk => by
    rw [List.getD_eq_default _ _ (by simp at hk; omega), val_nil, C_0, zero_mul], add_zero]

/-- **Addition is correct.** -/
theorem pval_padd (P Q : List (List ℕ)) :
    pval p fl (padd p fl P Q) = pval p fl P + pval p fl Q := by
  rw [pval_eq_sum_of_le P (le_max_left P.length Q.length),
    pval_eq_sum_of_le Q (le_max_right P.length Q.length), ← sum_add_distrib, pval]
  simp only [padd, List.length_map, List.length_range]
  refine sum_congr rfl fun k hk => ?_
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp [val_add, add_mul]

/-- **Scaling is correct.** -/
theorem pval_psmul (c : List ℕ) (P : List (List ℕ)) :
    pval p fl (psmul p fl c P) = C (val p fl c) * pval p fl P := by
  rw [pval, pval, mul_sum]
  simp only [psmul, List.length_map]
  refine sum_congr rfl fun k hk => ?_
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ (by simpa using hk)]
  simp [val_mul, mul_assoc]

/-- **Multiplication by `z - v` is correct.** -/
theorem pval_pmulLinear (v : List ℕ) (P : List (List ℕ)) :
    pval p fl (pmulLinear p fl v P) = (X - C (val p fl v)) * pval p fl P := by
  have hcoeff (k : ℕ) (hk : k < P.length + 1) :
      val p fl ((pmulLinear p fl v P).getD k []) =
        val p fl (([] :: P).getD k []) - val p fl v * val p fl (P.getD k []) := by
    rw [pmulLinear, List.getD_eq_getElem _ _ (by simpa using hk)]
    simp [val_sub, val_mul]
  rw [pval, show (pmulLinear p fl v P).length = P.length + 1 by simp [pmulLinear],
    sum_congr rfl fun k hk => by rw [hcoeff k (mem_range.mp hk)]]
  rw [sub_mul, pval, mul_sum, mul_sum]
  simp only [map_sub, map_mul, sub_mul, sum_sub_distrib]
  congr 1
  · rw [sum_range_succ']
    simp only [List.getD_cons_zero, val_nil, C_0, zero_mul, add_zero, List.getD_cons_succ]
    refine sum_congr rfl fun k _ => by ring
  · rw [sum_range_succ, List.getD_eq_default _ _ le_rfl, val_nil, C_0, mul_zero, zero_mul,
      add_zero]
    refine sum_congr rfl fun k _ => by ring

/-- **Evaluation is correct.** -/
theorem peval_eq (P : List (List ℕ)) (z : List ℕ) :
    val p fl (peval p fl P z) = (pval p fl P).eval (val p fl z) := by
  induction P with
  | nil => simp [peval, pval]
  | cons a P ih =>
    rw [peval, List.foldr_cons, ← peval, val_add, val_mul, ih]
    simp only [pval, List.length_cons, sum_range_succ', List.getD_cons_succ, List.getD_cons_zero,
      eval_add, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, pow_zero, mul_one, pow_succ,
      mul_sum]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun k _ => by ring

/-! ### Lagrange interpolation -/

/-- The numerator `∏_{j < n, j ≠ i} (z - v_j)` of the `i`-th Lagrange basis polynomial. -/
def basisNum (p : ℕ) (fl : List ℕ) (v : List (List ℕ)) (i : ℕ) : List (List ℕ) :=
  (List.range v.length).foldl
    (fun P j => if j = i then P else pmulLinear p fl (v.getD j []) P) [one fl]

/-- The denominator `∏_{j < n, j ≠ i} (v_i - v_j)` of the `i`-th Lagrange basis polynomial. -/
def basisDen (p : ℕ) (fl : List ℕ) (v : List (List ℕ)) (i : ℕ) : List ℕ :=
  (List.range v.length).foldl
    (fun d j => if j = i then d else mul p fl d (sub p fl (v.getD i []) (v.getD j []))) (one fl)

/-- **Lagrange interpolation** of the values `y` at the nodes `v`. -/
def interp (p : ℕ) (fl : List ℕ) (v : List (List ℕ)) (y : List (List ℕ)) : List (List ℕ) :=
  (List.range v.length).foldl (fun P i =>
    padd p fl P (psmul p fl (mul p fl (y.getD i []) (inv p fl (basisDen p fl v i)))
      (basisNum p fl v i))) []

theorem pval_basisNum (v : List (List ℕ)) (i : ℕ) :
    pval p fl (basisNum p fl v i) =
      ∏ j ∈ (range v.length).erase i, (X - C (val p fl (v.getD j []))) := by
  have h (m : ℕ) (hm : m ≤ v.length) : pval p fl ((List.range m).foldl
      (fun P j => if j = i then P else pmulLinear p fl (v.getD j []) P) [one fl]) =
        ∏ j ∈ (range m).erase i, (X - C (val p fl (v.getD j []))) := by
    induction m with
    | zero => simp [pval]
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, range_add_one]
      by_cases hmi : m = i
      · subst hmi
        simp only [↓reduceIte]
        rw [ih (by omega), erase_insert (by simp), Finset.erase_eq_of_notMem (by simp)]
      · simp only [hmi, ↓reduceIte]
        rw [pval_pmulLinear, ih (by omega), erase_insert_of_ne hmi, prod_insert (by simp)]
  exact h _ le_rfl

theorem val_basisDen (v : List (List ℕ)) (i : ℕ) :
    val p fl (basisDen p fl v i) =
      ∏ j ∈ (range v.length).erase i, (val p fl (v.getD i []) - val p fl (v.getD j [])) := by
  have h (m : ℕ) : val p fl ((List.range m).foldl
      (fun d j => if j = i then d else mul p fl d (sub p fl (v.getD i []) (v.getD j [])))
      (one fl)) = ∏ j ∈ (range m).erase i, (val p fl (v.getD i []) - val p fl (v.getD j [])) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, range_add_one]
      by_cases hmi : m = i
      · subst hmi
        simp only [↓reduceIte]
        rw [ih, erase_insert (by simp), Finset.erase_eq_of_notMem (by simp)]
      · simp only [hmi, ↓reduceIte]
        rw [val_mul, val_sub, ih, erase_insert_of_ne hmi, prod_insert (by simp), mul_comm]
  exact h _

/-- **Interpolation is the Lagrange formula**, with the computed inverses of the denominators. -/
theorem pval_interp (v y : List (List ℕ)) :
    pval p fl (interp p fl v y) = ∑ i ∈ range v.length,
      C (val p fl (y.getD i []) * val p fl (inv p fl (basisDen p fl v i))) *
        ∏ j ∈ (range v.length).erase i, (X - C (val p fl (v.getD j []))) := by
  have h (m : ℕ) (hm : m ≤ v.length) : pval p fl ((List.range m).foldl (fun P i =>
      padd p fl P (psmul p fl (mul p fl (y.getD i []) (inv p fl (basisDen p fl v i)))
        (basisNum p fl v i))) []) = ∑ i ∈ range m,
      C (val p fl (y.getD i []) * val p fl (inv p fl (basisDen p fl v i))) *
        ∏ j ∈ (range v.length).erase i, (X - C (val p fl (v.getD j []))) := by
    induction m with
    | zero => simp [pval]
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, sum_range_succ,
        pval_padd, ih (by omega), pval_psmul, val_mul, pval_basisNum]
  exact h _ le_rfl

/-- **Interpolation takes the given values** at the nodes, given correct inverses of the
denominators. -/
theorem eval_pval_interp (v y : List (List ℕ))
    (hinv : ∀ i < v.length, val p fl (basisDen p fl v i) *
      val p fl (inv p fl (basisDen p fl v i)) = 1) {k : ℕ} (hk : k < v.length) :
    (pval p fl (interp p fl v y)).eval (val p fl (v.getD k [])) = val p fl (y.getD k []) := by
  rw [pval_interp v y, eval_finsetSum, sum_eq_single k]
  · rw [eval_mul, eval_C, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    rw [← val_basisDen, mul_assoc, mul_comm (val p fl (inv p fl _)), hinv k hk, mul_one]
  · intro i hi hik
    rw [eval_mul, eval_prod, prod_eq_zero (i := k) (mem_erase.mpr ⟨Ne.symm hik, mem_range.mpr hk⟩)
      (by simp), mul_zero]
  · intro hk'
    exact absurd (mem_range.mpr hk) hk'

/-! ### Sizes -/

/-- A coefficient list is *small* when it has `e` coordinates below `2 ^ (p + 1)`: reduced
coordinates and the unit both are. -/
def Small (p : ℕ) (fl c : List ℕ) : Prop := c.length = fl.length ∧ ∀ a ∈ c, a < 2 ^ (p + 1)

theorem small_of_lt {c : List ℕ} (hlen : c.length = fl.length) (hlt : ∀ a ∈ c, a < 2 ^ p) :
    Small p fl c :=
  ⟨hlen, fun a ha => (hlt a ha).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))⟩

theorem small_add (c d : List ℕ) : Small p fl (add p fl c d) :=
  small_of_lt (length_add p fl c d) fun _ h => lt_of_mem_add h

theorem small_mul (c d : List ℕ) : Small p fl (mul p fl c d) :=
  small_of_lt (length_mul p fl c d) fun _ h => lt_of_mem_mul h

theorem small_sub (c d : List ℕ) : Small p fl (sub p fl c d) := small_add _ _

theorem small_one : Small p fl (one fl) := by
  refine ⟨by simp [one], fun a ha => ?_⟩
  simp only [one, List.mem_map, List.mem_range] at ha
  obtain ⟨i, -, rfl⟩ := ha
  have : 1 < 2 ^ (p + 1) := Nat.one_lt_two_pow (by omega)
  split <;> omega

theorem length_encList_le_of_small {c : List ℕ} (h : Small p fl c) :
    (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat c).length ≤
      fl.length * (2 * (p + 1) + 1) :=
  length_encList_le h.1 h.2

/-- A list of small coefficient lists of length at most `n` is at most
`n (2 e (2 p + 3) + 1)` long. -/
theorem length_encPoly_le {P : List (List ℕ)} {n : ℕ} (hlen : P.length ≤ n)
    (h : ∀ c ∈ P, Small p fl c) :
    (Turing.MultiTapeTM.encList (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat) P).length ≤
      n * (2 * (fl.length * (2 * (p + 1) + 1)) + 1) := by
  rw [Turing.MultiTapeTM.length_encList]
  calc (P.map fun c => 2 * (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat c).length + 1).sum
      ≤ (P.map fun c => 2 * (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat c).length +
          1).length • (2 * (fl.length * (2 * (p + 1) + 1)) + 1) :=
        List.sum_le_length_nsmul _ _ fun m hm => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
          have := length_encList_le_of_small (h c hc)
          omega
    _ ≤ n * (2 * (fl.length * (2 * (p + 1) + 1)) + 1) := by
      rw [List.length_map, smul_eq_mul]
      exact Nat.mul_le_mul_right _ hlen

@[simp] theorem length_padd (P Q : List (List ℕ)) :
    (padd p fl P Q).length = max P.length Q.length := by simp [padd]

@[simp] theorem length_psmul (c : List ℕ) (P : List (List ℕ)) :
    (psmul p fl c P).length = P.length := by simp [psmul]

@[simp] theorem length_pmulLinear (v : List ℕ) (P : List (List ℕ)) :
    (pmulLinear p fl v P).length = P.length + 1 := by simp [pmulLinear]

theorem small_of_mem_padd {P Q : List (List ℕ)} {c : List ℕ} (h : c ∈ padd p fl P Q) :
    Small p fl c := by
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp h
  exact small_add _ _

theorem small_of_mem_psmul {c' : List ℕ} {P : List (List ℕ)} {c : List ℕ}
    (h : c ∈ psmul p fl c' P) : Small p fl c := by
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp h
  exact small_mul _ _

theorem small_of_mem_pmulLinear {v : List ℕ} {P : List (List ℕ)} {c : List ℕ}
    (h : c ∈ pmulLinear p fl v P) : Small p fl c := by
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp h
  exact small_sub _ _

theorem length_basisNum_le (v : List (List ℕ)) (i : ℕ) :
    (basisNum p fl v i).length ≤ v.length + 1 := by
  have h (m : ℕ) : ((List.range m).foldl
      (fun P j => if j = i then P else pmulLinear p fl (v.getD j []) P) [one fl]).length ≤
        m + 1 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      split
      · omega
      · rw [length_pmulLinear]; omega
  exact h _

theorem small_of_mem_basisNum {v : List (List ℕ)} {i : ℕ} {c : List ℕ}
    (h : c ∈ basisNum p fl v i) : Small p fl c := by
  have key (m : ℕ) : ∀ c ∈ (List.range m).foldl
      (fun P j => if j = i then P else pmulLinear p fl (v.getD j []) P) [one fl], Small p fl c := by
    induction m with
    | zero => simp [small_one]
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      split
      · exact ih
      · exact fun c hc => small_of_mem_pmulLinear hc
  exact key _ c h

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

/-- **Addition of polynomials is polynomial-time**, with the precision in unary. -/
@[fun_prop]
theorem computableInPolyTime_padd {p : α → ℕ} {fl : α → List ℕ} {P Q : α → List (List ℕ)}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hP : ComputableInPolyTime P encIn (encList (encList encNat)))
    (hQ : ComputableInPolyTime Q encIn (encList (encList encNat))) :
    ComputableInPolyTime (fun x => padd (p x) (fl x) (P x) (Q x)) encIn
      (encList (encList encNat)) := by
  have h1 := ComputableInPolyTime.fst encIn encUnary
  have h2 := ComputableInPolyTime.snd encIn encUnary
  have hmax : ComputableInPolyTime (fun x => max (P x).length (Q x).length) encIn encUnary :=
    (ComputableInPolyTime.unary_add' (lengthPolyTime hP)
      (ComputableInPolyTime.unary_sub' (lengthPolyTime hQ) (lengthPolyTime hP))).of_enc_eq
      fun x => by congr 1; omega
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hmax)
    (computableInPolyTime_add (hp.comp h1) (hfl.comp h1) (getDPolyTime (hP.comp h1) h2)
      (getDPolyTime (hQ.comp h1) h2))

/-- **Scaling a polynomial is polynomial-time**, with the precision in unary. -/
@[fun_prop]
theorem computableInPolyTime_psmul {p : α → ℕ} {fl c : α → List ℕ} {P : α → List (List ℕ)}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hc : ComputableInPolyTime c encIn (encList encNat))
    (hP : ComputableInPolyTime P encIn (encList (encList encNat))) :
    ComputableInPolyTime (fun x => psmul (p x) (fl x) (c x) (P x)) encIn
      (encList (encList encNat)) := by
  have h1 := ComputableInPolyTime.fst encIn (encList encNat)
  have h2 := ComputableInPolyTime.snd encIn (encList encNat)
  exact ComputableInPolyTime.mapWithInput hP
    (computableInPolyTime_mul (hp.comp h1) (hfl.comp h1) (hc.comp h1) h2)

/-- **Multiplication by `z - v` is polynomial-time**, with the precision in unary. -/
@[fun_prop]
theorem computableInPolyTime_pmulLinear {p : α → ℕ} {fl v : α → List ℕ}
    {P : α → List (List ℕ)}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hv : ComputableInPolyTime v encIn (encList encNat))
    (hP : ComputableInPolyTime P encIn (encList (encList encNat))) :
    ComputableInPolyTime (fun x => pmulLinear (p x) (fl x) (v x) (P x)) encIn
      (encList (encList encNat)) := by
  have h1 := ComputableInPolyTime.fst encIn encUnary
  have h2 := ComputableInPolyTime.snd encIn encUnary
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp
    (ComputableInPolyTime.unary_add' (lengthPolyTime hP) (ComputableInPolyTime.const 1)))
    (computableInPolyTime_sub (hp.comp h1) (hfl.comp h1)
      (getDPolyTime (ComputableInPolyTime.cons' (ComputableInPolyTime.const [])
        (hP.comp h1)) h2)
      (computableInPolyTime_mul (hp.comp h1) (hfl.comp h1) (hv.comp h1)
        (getDPolyTime (hP.comp h1) h2)))

private theorem polyBounded_small {p : α → ℕ} {fl : α → List ℕ} {n : α → ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hn : PolyBounded (fun x => (encIn x).length) n) :
    PolyBounded (fun x => (encIn x).length)
      (fun x => n x * (2 * ((fl x).length * (2 * (p x + 1) + 1)) + 1)) := by
  have hpl : PolyBounded (fun x => (encIn x).length) p := by
    simpa using (ComputableInPolyTime.polyBounded_length hp)
  have hfll : PolyBounded (fun x => (encIn x).length) fun x => (fl x).length :=
    (lengthPolyTime hfl).polyBounded_length.mono fun x => by simp
  exact hn.mul (((PolyBounded.const 2).mul (hfll.mul (((PolyBounded.const 2).mul
    (hpl.add (PolyBounded.const 1))).add (PolyBounded.const 1)))).add (PolyBounded.const 1))

/-- **Evaluation is polynomial-time**, with the precision in unary. -/
@[fun_prop]
theorem computableInPolyTime_peval {p : α → ℕ} {fl z : α → List ℕ} {P : α → List (List ℕ)}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hP : ComputableInPolyTime P encIn (encList (encList encNat)))
    (hz : ComputableInPolyTime z encIn (encList encNat)) :
    ComputableInPolyTime (fun x => peval (p x) (fl x) (P x) (z x)) encIn (encList encNat) := by
  simp only [peval, List.foldr_eq_foldl_reverse]
  have hstep : ComputableInPolyTime
      (fun q : (α × List ℕ) × List ℕ => add (p q.1.1) (fl q.1.1) q.2 (mul (p q.1.1) (fl q.1.1)
        (z q.1.1) q.1.2)) (encPair (encPair encIn (encList encNat)) (encList encNat))
      (encList encNat) := by
    have hq := ComputableInPolyTime.fst (encPair encIn (encList encNat)) (encList encNat)
    have ha := (ComputableInPolyTime.fst encIn (encList encNat)).comp hq
    have hacc := (ComputableInPolyTime.snd encIn (encList encNat)).comp hq
    have hc := ComputableInPolyTime.snd (encPair encIn (encList encNat)) (encList encNat)
    exact computableInPolyTime_add (hp.comp ha) (hfl.comp ha) hc
      (computableInPolyTime_mul (hp.comp ha) (hfl.comp ha) (hz.comp ha) hacc)
  have hzero : ComputableInPolyTime (fun x => zero (fl x)) encIn (encList encNat) :=
    computableInPolyTime_tabulate (g := fun _ _ => 0) (lengthPolyTime hfl)
      (ComputableInPolyTime.const 0)
  exact ComputableInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encList encNat) (encL := encList (encList encNat))
    (step := fun x acc a => add (p x) (fl x) a (mul (p x) (fl x) (z x) acc)) hzero
    ⟨ComputableInPolyTime.listReverseWithInput hP, hstep, inferInstance, inferInstance⟩
    ⟨(polyBounded_small hp hfl (PolyBounded.const 1)), fun x acc a _ => by
      have := length_encList_le_of_small (small_add (p := p x) (fl := fl x) a
        (mul (p x) (fl x) (z x) acc))
      omega⟩

/-- **Lagrange numerators are polynomial-time**, with the precision and the index in unary. -/
@[fun_prop]
theorem computableInPolyTime_basisNum {p : α → ℕ} {fl : α → List ℕ} {v : α → List (List ℕ)}
    {i : α → ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hv : ComputableInPolyTime v encIn (encList (encList encNat)))
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => basisNum (p x) (fl x) (v x) (i x)) encIn
      (encList (encList encNat)) := by
  let encS := encList (encList encNat)
  have hstep : ComputableInPolyTime
      (fun q : (α × List (List ℕ)) × ℕ => if q.2 = i q.1.1 then q.1.2
        else pmulLinear (p q.1.1) (fl q.1.1) ((v q.1.1).getD q.2 []) q.1.2)
      (encPair (encPair encIn encS) encUnary) encS := by
    have hq := ComputableInPolyTime.fst (encPair encIn encS) encUnary
    have ha := (ComputableInPolyTime.fst encIn encS).comp hq
    have hP := (ComputableInPolyTime.snd encIn encS).comp hq
    have hj := ComputableInPolyTime.snd (encPair encIn encS) encUnary
    refine (ComputableInPolyTime.ite (ComputableInPolyTime.beq hj (hi.comp ha)) hP
      (computableInPolyTime_pmulLinear (hp.comp ha) (hfl.comp ha) (getDPolyTime (hv.comp ha) hj)
        hP)).of_enc_eq fun q => ?_
    by_cases h : q.2 = i q.1.1 <;> simp [h]
  have hfold := ComputableInPolyTime.foldlWith_spec (encA := encUnary)
    (encL := encList encUnary) (par := fun x => x)
    (step := fun x P j => if j = i x then P else pmulLinear (p x) (fl x) ((v x).getD j []) P)
    ComputableInPolyTime.id' (ComputableInPolyTime.range.comp (lengthPolyTime hv))
    (ComputableInPolyTime.cons' (computableInPolyTime_one hfl) (ComputableInPolyTime.const []))
    hstep (fun x consumed P => P.length ≤ consumed.length + 1 ∧ ∀ c ∈ P, Small (p x) (fl x) c)
    (fun x => ⟨by simp, by simp [small_one]⟩)
    (fun x consumed P j _ hP => by
      refine ⟨?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        split
        · omega
        · rw [length_pmulLinear]; omega
      · split
        · exact hP.2
        · exact fun c hc => small_of_mem_pmulLinear hc)
    (polyBounded_small hp hfl ((lengthPolyTime hv).polyBounded_length.add (PolyBounded.const 1)))
    (fun x consumed P hpre hP => by
      have hlen : consumed.length ≤ (v x).length := by
        simpa using hpre.length_le
      refine (length_encPoly_le (n := (v x).length + 1) (by omega) hP.2).trans ?_
      simp [encUnary_apply])
  exact hfold.1

/-- **Lagrange denominators are polynomial-time**, with the precision and the index in unary. -/
@[fun_prop]
theorem computableInPolyTime_basisDen {p : α → ℕ} {fl : α → List ℕ} {v : α → List (List ℕ)}
    {i : α → ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hv : ComputableInPolyTime v encIn (encList (encList encNat)))
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => basisDen (p x) (fl x) (v x) (i x)) encIn (encList encNat) := by
  have hstep : ComputableInPolyTime
      (fun q : (α × List ℕ) × ℕ => if q.2 = i q.1.1 then q.1.2
        else mul (p q.1.1) (fl q.1.1) q.1.2 (sub (p q.1.1) (fl q.1.1) ((v q.1.1).getD (i q.1.1) [])
          ((v q.1.1).getD q.2 [])))
      (encPair (encPair encIn (encList encNat)) encUnary) (encList encNat) := by
    have hq := ComputableInPolyTime.fst (encPair encIn (encList encNat)) encUnary
    have ha := (ComputableInPolyTime.fst encIn (encList encNat)).comp hq
    have hd := (ComputableInPolyTime.snd encIn (encList encNat)).comp hq
    have hj := ComputableInPolyTime.snd (encPair encIn (encList encNat)) encUnary
    refine (ComputableInPolyTime.ite (ComputableInPolyTime.beq hj (hi.comp ha)) hd
      (computableInPolyTime_mul (hp.comp ha) (hfl.comp ha) hd
        (computableInPolyTime_sub (hp.comp ha) (hfl.comp ha)
          (getDPolyTime (hv.comp ha) (hi.comp ha)) (getDPolyTime (hv.comp ha) hj)))).of_enc_eq
      fun q => ?_
    by_cases h : q.2 = i q.1.1 <;> simp [h]
  exact ComputableInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encUnary) (encL := encList encUnary)
    (step := fun x d j => if j = i x then d
      else mul (p x) (fl x) d (sub (p x) (fl x) ((v x).getD (i x) []) ((v x).getD j [])))
    (computableInPolyTime_one hfl)
    ⟨ComputableInPolyTime.range.comp (lengthPolyTime hv), hstep, inferInstance, inferInstance⟩
    ⟨polyBounded_small hp hfl (PolyBounded.const 1), fun x d j _ => by
      split
      · omega
      · have := length_encList_le_of_small (small_mul (p := p x) (fl := fl x) d
          (sub (p x) (fl x) ((v x).getD (i x) []) ((v x).getD j [])))
        omega⟩

/-- **Lagrange interpolation is polynomial-time**, with the precision in unary and the nodes and
values as lists of coefficient lists. -/
@[fun_prop]
theorem computableInPolyTime_interp {p : α → ℕ} {fl : α → List ℕ} {v y : α → List (List ℕ)}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hv : ComputableInPolyTime v encIn (encList (encList encNat)))
    (hy : ComputableInPolyTime y encIn (encList (encList encNat))) :
    ComputableInPolyTime (fun x => interp (p x) (fl x) (v x) (y x)) encIn
      (encList (encList encNat)) := by
  let encS := encList (encList encNat)
  have hstep : ComputableInPolyTime
      (fun q : (α × List (List ℕ)) × ℕ => padd (p q.1.1) (fl q.1.1) q.1.2
        (psmul (p q.1.1) (fl q.1.1) (mul (p q.1.1) (fl q.1.1) ((y q.1.1).getD q.2 [])
          (inv (p q.1.1) (fl q.1.1) (basisDen (p q.1.1) (fl q.1.1) (v q.1.1) q.2)))
          (basisNum (p q.1.1) (fl q.1.1) (v q.1.1) q.2)))
      (encPair (encPair encIn encS) encUnary) encS := by
    have hq := ComputableInPolyTime.fst (encPair encIn encS) encUnary
    have ha := (ComputableInPolyTime.fst encIn encS).comp hq
    have hP := (ComputableInPolyTime.snd encIn encS).comp hq
    have hj := ComputableInPolyTime.snd (encPair encIn encS) encUnary
    have hp' := hp.comp ha
    have hfl' := hfl.comp ha
    exact computableInPolyTime_padd hp' hfl' hP (computableInPolyTime_psmul hp' hfl'
      (computableInPolyTime_mul hp' hfl' (getDPolyTime (hy.comp ha) hj)
        (computableInPolyTime_inv hp' hfl'
          (computableInPolyTime_basisDen hp' hfl' (hv.comp ha) hj)))
      (computableInPolyTime_basisNum hp' hfl' (hv.comp ha) hj))
  have hfold := ComputableInPolyTime.foldlWith_spec (encA := encUnary)
    (encL := encList encUnary) (par := fun x => x)
    (step := fun x P i => padd (p x) (fl x) P
      (psmul (p x) (fl x) (mul (p x) (fl x) ((y x).getD i []) (inv (p x) (fl x)
        (basisDen (p x) (fl x) (v x) i))) (basisNum (p x) (fl x) (v x) i)))
    ComputableInPolyTime.id' (ComputableInPolyTime.range.comp (lengthPolyTime hv))
    (ComputableInPolyTime.const []) hstep
    (fun x _ P => P.length ≤ (v x).length + 1 ∧ ∀ c ∈ P, Small (p x) (fl x) c)
    (fun x => ⟨by simp, by simp⟩)
    (fun x consumed P j _ hP => by
      refine ⟨?_, fun c hc => small_of_mem_padd hc⟩
      rw [length_padd, length_psmul]
      exact max_le hP.1 (length_basisNum_le _ _))
    (polyBounded_small hp hfl ((lengthPolyTime hv).polyBounded_length.add (PolyBounded.const 1)))
    (fun x consumed P _ hP => by
      refine (length_encPoly_le hP.1 hP.2).trans ?_
      simp [encUnary_apply])
  exact hfold.1

end PolyTime

end Cslib.GaloisRingArith

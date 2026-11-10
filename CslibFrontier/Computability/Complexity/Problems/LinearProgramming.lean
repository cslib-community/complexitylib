/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.BasicSolution
public import Mathlib.Tactic.Matrix.ListMatrix
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.PolyTime.Int.Compare
import CslibFrontier.Computability.PolyTime.Int.DotProduct
import CslibFrontier.Foundations.Data.List.Blocks
import CslibFrontier.Foundations.Data.List.DotProduct
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Rational linear-programming feasibility is in `NP ∩ coNP`

`LPFeasibility` is the set of finite systems of linear inequalities `∑ j, a j * x j ≤ t` with
integer coefficients that have a rational solution, encoded by `LPFeasibility.encSystem` as lists
of pairs `(a, t)` with signed-binary integers. A system with rational coefficients is equivalent
to an integer one after clearing denominators row by row.

Both a solution and a proof of infeasibility have polynomial-size certificates:

* **`NP`.** A feasible system has a solution `w / d` with integers `w j` and `d > 0` of absolute
  value at most `2 ^ ((3L + 3) * 6L)`, where `L` is the length of the encoded system, by the
  basic-solution bound `Matrix.exists_int_mulVec_le`. `LPFeasibility.check` verifies
  `∑ j, a j * w j ≤ d * t` for every row in polynomial time.
* **`coNP`.** By Farkas' lemma (`Matrix.not_exists_mulVec_le_iff`) an infeasible system has a
  nonnegative combination of its rows that reads `0 ≤ s` with `s < 0`; by
  `Matrix.exists_int_farkas_certificate` it has one with integer multipliers bounded by the same
  `2 ^ ((3L + 3) * 6L)`.
  `LPFeasibility.certCheck` verifies such a certificate in polynomial time.

The verifiers are integer computations, proved polynomial-time with the plain
`ComputableInPolyTime` calculus. Whether `LPFeasibility` is in `P` (Khachiyan's ellipsoid method,
or interior-point methods) is not formalized here.

## Main definitions

* `Cslib.Complexity.LPFeasibility`, with the instance encoding
  `Cslib.Complexity.LPFeasibility.encSystem`.
* `Cslib.Complexity.LPFeasibility.check`, `Cslib.Complexity.LPFeasibility.certCheck`: the
  certificate checks for feasibility and infeasibility.

## Main results

* `Cslib.Complexity.LPFeasibility.mem_iff_exists_mulVec_le`: the matrix form of a system.
* `Cslib.Complexity.LPFeasibility.mem_of_check`,
  `Cslib.Complexity.LPFeasibility.notMem_of_certCheck`: soundness of the checks.
* `Cslib.Complexity.LPFeasibility.computableInPolyTime_check`,
  `Cslib.Complexity.LPFeasibility.computableInPolyTime_certCheck`: the checks are polynomial-time.
* `Cslib.Complexity.LPFeasibility.mem_NP`, `Cslib.Complexity.LPFeasibility.mem_coNP`,
  `Cslib.Complexity.LPFeasibility.mem_NP_inter_coNP`: `LPFeasibility ∈ NP ∩ coNP`.

## References

* [Schrijver1986], Sections 3.2 and 10.1
-/

public section

open scoped Nat

namespace Cslib.Complexity

open Finset Matrix Turing.MultiTapeTM ComputableInPolyTime Mathlib.Tactic.Matrix

/-- **Rational linear-programming feasibility**: the systems of linear inequalities with integer
coefficients that have a rational solution. A constraint `(a, t)` asks for
`∑ j < a.length, a[j] * x j ≤ t`; missing coefficients are zero. -/
@[expose] def LPFeasibility : Set (List (List ℤ × ℤ)) :=
  {C | ∃ x : ℕ → ℚ, ∀ c ∈ C, ∑ j ∈ range c.1.length, (c.1.getD j 0 : ℚ) * x j ≤ c.2}

namespace LPFeasibility

/-- The instance encoding of `LPFeasibility`: a framed list of rows, each a framed signed-binary
list of coefficients followed by the signed-binary bound. -/
abbrev encSystem : List (List ℤ × ℤ) ↪ List Bool :=
  encList (encPair (encList encIntBin) encIntBin)

/-- The constraint matrix of `C` with `n` columns, missing coefficients read as zero. -/
@[expose] def matrix (C : List (List ℤ × ℤ)) (n : ℕ) : Matrix (Fin C.length) (Fin n) ℤ :=
  of fun i j => (C[i.1]).1.getD j 0

/-- The right-hand side of `C`. -/
@[expose] def rhs (C : List (List ℤ × ℤ)) : Fin C.length → ℤ := fun i => (C[i.1]).2

/-- A sum over `Fin n` of a function vanishing from `k` on is a sum over `range k`. -/
private theorem sum_fin_eq_sum_range {M : Type*} [AddCommMonoid M] {n k : ℕ} (hk : k ≤ n)
    (f : ℕ → M) (hf : ∀ j, k ≤ j → f j = 0) :
    ∑ j : Fin n, f j = ∑ j ∈ range k, f j := by
  rw [Fin.sum_univ_eq_sum_range f n, ← Finset.sum_range_add_sum_Ico _ hk]
  rw [Finset.sum_eq_zero (s := Ico k n) fun j hj => hf j (Finset.mem_Ico.1 hj).1, add_zero]

/-- **The matrix form.** When every row has at most `n` coefficients, `C` is feasible iff
`matrix C n *ᵥ x ≤ rhs C` has a rational solution. -/
theorem mem_iff_exists_mulVec_le {C : List (List ℤ × ℤ)} {n : ℕ} (hn : ∀ c ∈ C, c.1.length ≤ n) :
    C ∈ LPFeasibility ↔
      ∃ x : Fin n → ℚ, (matrix C n).map (Int.cast : ℤ → ℚ) *ᵥ x ≤ fun i => (rhs C i : ℚ) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun j => x j, fun i => ?_⟩
    have h := hx _ (List.getElem_mem i.2)
    simp only [mulVec, dotProduct, map_apply, matrix, of_apply, rhs]
    rw [sum_fin_eq_sum_range (hn _ (List.getElem_mem i.2))
      (fun j => ((C[i.1].1.getD j 0 : ℤ) : ℚ) * x j)
      fun j hj => by rw [List.getD_eq_default _ _ hj, Int.cast_zero, zero_mul]]
    exact h
  · rintro ⟨x, hx⟩
    refine ⟨fun j => if h : j < n then x ⟨j, h⟩ else 0, fun c hc => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have h := hx ⟨i, hi⟩
    simp only [mulVec, dotProduct, map_apply, matrix, of_apply, rhs] at h
    have h' : ∑ j : Fin n, ((C[i].1.getD j 0 : ℤ) : ℚ) *
        (if h : (j : ℕ) < n then x ⟨j, h⟩ else 0) ≤ C[i].2 := by
      simpa only [Fin.is_lt, dite_true, Fin.eta] using h
    rwa [sum_fin_eq_sum_range (hn _ hc) (fun j => ((C[i].1.getD j 0 : ℤ) : ℚ) *
      if h : j < n then x ⟨j, h⟩ else 0)
      fun j hj => by rw [List.getD_eq_default _ _ hj, Int.cast_zero, zero_mul]] at h'

/-- A padded list dot product as a sum over the first list's length. -/
private theorem dotProduct_eq_sum_range {R : Type*} [CommSemiring R] (a w : List R) :
    ListMatrix.dotProduct a.length a w = ∑ j ∈ range a.length, a.getD j 0 * w.getD j 0 := by
  rw [ListMatrix.dotProduct_eq_sum_map_range, List.sum_map_range_eq_sum_range]

/-- The `NP` check: `d > 0` and `w / d` satisfies every constraint, as
`∑ j < a.length, a[j] * w[j] ≤ d * t`. -/
@[expose] def check (x : List (List ℤ × ℤ) × (ℤ × List ℤ)) : Bool :=
  decide (0 < x.2.1) &&
    x.1.all fun c => decide (ListMatrix.dotProduct c.1.length c.1 x.2.2 ≤ x.2.1 * c.2)

/-- **Soundness of the `NP` check.** -/
theorem mem_of_check {C : List (List ℤ × ℤ)} {d : ℤ} {w : List ℤ}
    (h : check (C, (d, w)) = true) : C ∈ LPFeasibility := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hd, hc⟩ := h
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  refine ⟨fun j => (w.getD j 0 : ℚ) / d, fun c hcC => ?_⟩
  have h1 := hc c hcC
  rw [dotProduct_eq_sum_range] at h1
  have key : (∑ j ∈ range c.1.length, (c.1.getD j 0 : ℚ) * ((w.getD j 0 : ℚ) / d)) * d =
      ((∑ j ∈ range c.1.length, c.1.getD j 0 * w.getD j 0 : ℤ) : ℚ) := by
    rw [Finset.sum_mul]
    push_cast
    exact Finset.sum_congr rfl fun j _ => by rw [mul_assoc, div_mul_cancel₀ _ hdQ.ne']
  have h3 : ((∑ j ∈ range c.1.length, c.1.getD j 0 * w.getD j 0 : ℤ) : ℚ) ≤ c.2 * d := by
    rw [mul_comm]
    exact_mod_cast h1
  exact le_of_mul_le_mul_right (key ▸ h3) hdQ

/-- The size bound of a basic solution, in the encoded length `L`. -/
private theorem factorial_mul_pow_le {k l L B : ℕ} (hk : k ≤ 3 * L) (hl : l ≤ L + 1)
    (hB : B + 1 ≤ 2 ^ (L + 1)) :
    k ! * (l * (B + 1) ^ 2 + 1) ^ k ≤ 2 ^ ((3 * L + 3) * (6 * L)) := by
  set T := 2 ^ (3 * L + 3) with hT
  have hT1 : 1 ≤ T := Nat.one_le_two_pow
  have hkT : k ≤ T := by
    calc k ≤ 3 * L + 3 := by omega
      _ ≤ T := Nat.lt_two_pow_self.le
  have hbase : l * (B + 1) ^ 2 + 1 ≤ T := by
    have h1 : l * (B + 1) ^ 2 + 1 ≤ (l + 1) * (B + 1) ^ 2 := by
      have : 1 ≤ (B + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
      nlinarith
    have h2 : l + 1 ≤ 2 ^ (L + 1) := by
      calc l + 1 ≤ L + 2 := by omega
        _ ≤ 2 ^ (L + 1) := Nat.lt_two_pow_self
    have h3 : (B + 1) ^ 2 ≤ 2 ^ (2 * L + 2) := by
      calc (B + 1) ^ 2 ≤ (2 ^ (L + 1)) ^ 2 := Nat.pow_le_pow_left hB 2
        _ = 2 ^ (2 * L + 2) := by rw [← pow_mul]; ring_nf
    calc l * (B + 1) ^ 2 + 1 ≤ (l + 1) * (B + 1) ^ 2 := h1
      _ ≤ 2 ^ (L + 1) * 2 ^ (2 * L + 2) := Nat.mul_le_mul h2 h3
      _ = T := by rw [hT, ← pow_add]; ring_nf
  calc k ! * (l * (B + 1) ^ 2 + 1) ^ k ≤ T ^ k * T ^ k :=
        Nat.mul_le_mul ((Nat.factorial_le_pow k).trans (Nat.pow_le_pow_left hkT k))
          (Nat.pow_le_pow_left hbase k)
    _ = T ^ (2 * k) := by rw [← pow_add]; ring_nf
    _ ≤ T ^ (6 * L) := Nat.pow_le_pow_right hT1 (by omega)
    _ = 2 ^ ((3 * L + 3) * (6 * L)) := by rw [hT, ← pow_mul]

/-- Every coefficient of a system has absolute value below `2 ^ L`, `L` its encoded length. -/
private theorem abs_le_two_pow {C : List (List ℤ × ℤ)} {c : List ℤ × ℤ} (hc : c ∈ C)
    {z : ℤ} (hz : z ∈ c.1 ∨ z = c.2) :
    |z| ≤ ((2 ^ (encSystem C).length : ℕ) : ℤ) := by
  have hlen :
      (encIntBin z).length ≤ (encSystem C).length := by
    refine le_trans ?_ (length_le_encList_of_mem _ hc)
    rcases hz with hz | rfl
    · exact (length_le_encList_of_mem _ hz).trans (length_le_encPair_left _ _ c)
    · exact length_le_encPair_right _ _ c
  rw [length_encIntBin] at hlen
  rw [Int.abs_eq_natAbs]
  have : z.natAbs < 2 ^ z.natAbs.size := Nat.lt_size_self _
  have h2 : 2 ^ z.natAbs.size ≤ 2 ^ (encSystem C).length :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  exact_mod_cast (this.trans_le h2).le

/-- Every row has at most `L` coefficients, `L` the encoded length. -/
private theorem length_le_encLength {C : List (List ℤ × ℤ)} {c : List ℤ × ℤ} (hc : c ∈ C) :
    c.1.length ≤ (encSystem C).length :=
  (length_le_length_encList _ _).trans
    ((length_le_encPair_left _ _ c).trans (length_le_encList_of_mem _ hc))

private theorem abs_matrix_le (C : List (List ℤ × ℤ)) (n : ℕ) (i : Fin C.length) (j : Fin n) :
    |matrix C n i j| ≤
      ((2 ^ (encSystem C).length : ℕ) : ℤ) := by
  simp only [matrix, of_apply]
  by_cases hj : (j : ℕ) < C[i.1].1.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact abs_le_two_pow (List.getElem_mem i.2) (Or.inl (List.getElem_mem hj))
  · rw [List.getD_eq_default _ _ (not_lt.1 hj), abs_zero]
    positivity

private theorem abs_rhs_le (C : List (List ℤ × ℤ)) (i : Fin C.length) :
    |rhs C i| ≤ ((2 ^ (encSystem C).length : ℕ) : ℤ) :=
  abs_le_two_pow (List.getElem_mem i.2) (Or.inr rfl)

/-- An integer of absolute value at most `2 ^ E` has an encoding of length at most `E + 2`. -/
private theorem length_encIntBin_le {z : ℤ} {E : ℕ} (hz : |z| ≤ ((2 ^ E : ℕ) : ℤ)) :
    (encIntBin z).length ≤ E + 2 := by
  rw [length_encIntBin]
  have h1 : z.natAbs ≤ 2 ^ E := by grind
  have : z.natAbs.size ≤ E + 1 :=
    Nat.size_le.2 (h1.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  omega

private theorem length_encList_le_of_abs_le {l : List ℤ} {E : ℕ}
    (hl : ∀ z ∈ l, |z| ≤ ((2 ^ E : ℕ) : ℤ)) :
    (encList encIntBin l).length ≤ l.length * (2 * E + 5) := by
  refine (length_encList_le encIntBin l (b := E + 2) fun z hz =>
    length_encIntBin_le (hl z hz)).trans (le_of_eq ?_)
  ring

/-- The polynomial bounding the encoded witnesses and certificates. -/
private noncomputable def witnessPoly : Polynomial ℕ :=
  (Polynomial.X + 1) * (2 * ((3 * Polynomial.X + 3) * (6 * Polynomial.X)) + 5)

private theorem eval_witnessPoly (L : ℕ) :
    witnessPoly.eval L = (L + 1) * (2 * ((3 * L + 3) * (6 * L)) + 5) := by
  simp [witnessPoly]

/-- **Small witnesses.** A feasible system has a witness accepted by `check` of polynomial
size, by `Matrix.exists_int_mulVec_le`. -/
private theorem exists_check_of_mem {C : List (List ℤ × ℤ)} (hC : C ∈ LPFeasibility) :
    ∃ w : ℤ × List ℤ, check (C, w) = true ∧ (encPair encIntBin (encList encIntBin) w).length ≤
      witnessPoly.eval (encSystem C).length := by
  set L := (encSystem C).length with hL
  have hrow : ∀ c ∈ C, c.1.length ≤ L := fun c hc => length_le_encLength hc
  have hm : C.length ≤ L := length_le_length_encList _ _
  obtain ⟨x, hx⟩ := (mem_iff_exists_mulVec_le hrow).1 hC
  obtain ⟨d, p, hd, hAp, hdN, hpN⟩ :=
    exists_int_mulVec_le (abs_matrix_le C L) (abs_rhs_le C) hx
  simp only [Fintype.card_fin] at hdN hpN
  set E := (3 * L + 3) * (6 * L) with hE
  have h2L : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  have hN : ((2 * L + C.length)! * (C.length * (2 ^ L + 1) ^ 2 + 1) ^ (2 * L + C.length) : ℕ) ≤
      2 ^ E :=
    factorial_mul_pow_le (by omega) (by omega) (by rw [pow_succ]; omega)
  have hNE : (((2 * L + C.length)! * (C.length * (2 ^ L + 1) ^ 2 + 1) ^ (2 * L + C.length) : ℕ) :
      ℤ) ≤ ((2 ^ E : ℕ) : ℤ) := by exact_mod_cast hN
  refine ⟨(d, List.ofFn p), ?_, ?_⟩
  · simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨hd, fun c hc => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have h := hAp ⟨i, hi⟩
    simp only [mulVec, dotProduct, matrix, of_apply, rhs, Pi.smul_apply, smul_eq_mul] at h
    rw [dotProduct_eq_sum_range]
    have h' : ∑ j : Fin L, C[i].1.getD (j : ℕ) 0 * (List.ofFn p).getD (j : ℕ) 0 ≤ d * C[i].2 := by
      simpa only [List.getD_ofFn] using h
    rwa [sum_fin_eq_sum_range (hrow _ hc) (fun j => C[i].1.getD j 0 * (List.ofFn p).getD j 0)
      fun j hj => by rw [List.getD_eq_default _ _ hj, zero_mul]] at h'
  · rw [length_encPair, eval_witnessPoly]
    dsimp only
    have h1 : (encIntBin d).length ≤ E + 2 :=
      length_encIntBin_le (by rw [abs_of_pos hd]; exact hdN.trans hNE)
    have h2 : (encList encIntBin (List.ofFn p)).length ≤ L * (2 * E + 5) := by
      refine (length_encList_le_of_abs_le (E := E) fun z hz => ?_).trans ?_
      · obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hz
        exact (hpN j).trans hNE
      · rw [List.length_ofFn]
    nlinarith

/-- A sum over `range n` of a function vanishing on `[k, n)` is a sum over `range k`. -/
private theorem sum_range_eq_of_vanish {M : Type*} [AddCommMonoid M] {k n : ℕ} (hk : k ≤ n)
    (f : ℕ → M) (hf : ∀ j, k ≤ j → f j = 0) : ∑ j ∈ range n, f j = ∑ j ∈ range k, f j := by
  rw [← Finset.sum_range_add_sum_Ico _ hk,
    Finset.sum_eq_zero (s := Ico k n) fun j hj => hf j (Finset.mem_Ico.1 hj).1, add_zero]

/-- The padded dot product of `C.map f` with `q`, as a sum over the rows. -/
private theorem dotProduct_map_eq_sum_fin (C : List (List ℤ × ℤ)) (f : List ℤ × ℤ → ℤ)
    (q : List ℤ) :
    ListMatrix.dotProduct q.length (C.map f) q = ∑ i : Fin C.length, q.getD i 0 * f C[i.1] := by
  rw [ListMatrix.dotProduct_eq_sum_map_range, List.sum_map_range_eq_sum_range]
  have h1 : ∑ i : Fin C.length, q.getD i 0 * f C[i.1] =
      ∑ i ∈ range C.length, (C.map f).getD i 0 * q.getD i 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (C.map f).getD i 0 * q.getD i 0)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [List.getD_eq_getElem (C.map f) 0 (by rw [List.length_map]; exact i.2), List.getElem_map,
      mul_comm]
  rw [h1]
  have hext : ∀ k, C.length ≤ k ∨ q.length ≤ k → (C.map f).getD k 0 * q.getD k 0 = 0 := by grind
  rw [← sum_range_eq_of_vanish (Nat.le_add_right q.length C.length)
      (fun k => (C.map f).getD k 0 * q.getD k 0) fun k hk => hext k (Or.inr hk),
    ← sum_range_eq_of_vanish (Nat.le_add_left C.length q.length)
      (fun k => (C.map f).getD k 0 * q.getD k 0) fun k hk => hext k (Or.inl hk)]

/-- The `coNP` check: `q ≥ 0`, every column of `∑ i, q[i] * C[i]` vanishes and
`∑ i, q[i] * t[i] < 0`, the integer Farkas certificate of infeasibility. -/
@[expose] def certCheck (x : List (List ℤ × ℤ) × List ℤ) : Bool :=
  x.2.all (fun z => decide (0 ≤ z)) &&
    (x.1.all fun c => (List.range c.1.length).all fun j =>
      decide (ListMatrix.dotProduct x.2.length (x.1.map fun c' => c'.1.getD j 0) x.2 = 0)) &&
    decide (ListMatrix.dotProduct x.2.length (x.1.map Prod.snd) x.2 < 0)

/-- **Soundness of the `coNP` check**, by Farkas' lemma (`Matrix.not_exists_mulVec_le_iff`). -/
theorem notMem_of_certCheck {C : List (List ℤ × ℤ)} {q : List ℤ}
    (h : certCheck (C, q) = true) : C ∉ LPFeasibility := by
  simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨hq, hcol⟩, hrhs⟩ := h
  set L := (encSystem C).length
  intro hC
  obtain ⟨x, hx⟩ := (mem_iff_exists_mulVec_le fun c hc => length_le_encLength hc).1 hC
  refine (not_exists_mulVec_le_iff ((matrix C L).map (Int.cast : ℤ → ℚ)) fun i => (rhs C i : ℚ)).2
    ⟨fun i => (q.getD i 0 : ℚ), ?_, ?_, ?_⟩ ⟨x, hx⟩
  · intro i
    have : 0 ≤ q.getD i 0 := by
      by_cases hi : (i : ℕ) < q.length
      · rw [List.getD_eq_getElem _ _ hi]
        exact hq _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (not_lt.1 hi)]
    simp only [Pi.zero_apply]
    exact_mod_cast this
  · funext j
    have hz : ∑ i : Fin C.length, q.getD i 0 * C[i.1].1.getD j 0 = 0 := by
      rw [← dotProduct_map_eq_sum_fin C (fun c => c.1.getD j 0) q]
      by_cases hj : ∃ c ∈ C, (j : ℕ) < c.1.length
      · obtain ⟨c, hc, hjc⟩ := hj
        exact hcol c hc j hjc
      · push Not at hj
        rw [ListMatrix.dotProduct_eq_sum_map_range, List.sum_map_range_eq_sum_range]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : k < C.length
        · rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
            List.getD_eq_default _ _ (hj _ (List.getElem_mem hk)), zero_mul]
        · rw [List.getD_eq_default _ _ (by simpa using not_lt.1 hk), zero_mul]
    simp only [vecMul, dotProduct, map_apply, matrix, of_apply, Pi.zero_apply]
    exact_mod_cast hz
  · have hz : ∑ i : Fin C.length, q.getD i 0 * C[i.1].2 < 0 := by
      rw [← dotProduct_map_eq_sum_fin C Prod.snd q]
      exact hrhs
    simp only [dotProduct, rhs]
    exact_mod_cast hz

/-- **Small certificates.** An infeasible system has a certificate accepted by `certCheck` of
polynomial size, by `Matrix.exists_int_farkas_certificate`. -/
private theorem exists_certCheck_of_notMem {C : List (List ℤ × ℤ)} (hC : C ∉ LPFeasibility) :
    ∃ q : List ℤ, certCheck (C, q) = true ∧ (encList encIntBin q).length ≤
      witnessPoly.eval (encSystem C).length := by
  set L := (encSystem C).length with hL
  have hrow : ∀ c ∈ C, c.1.length ≤ L := fun c hc => length_le_encLength hc
  have hm : C.length ≤ L := length_le_length_encList _ _
  have hno : ¬∃ x : Fin L → ℚ, (matrix C L).map (Int.cast : ℤ → ℚ) *ᵥ x ≤
      fun i => (rhs C i : ℚ) := fun h => hC ((mem_iff_exists_mulVec_le hrow).2 h)
  obtain ⟨y, hy, hyA, hyb, hyN⟩ :=
    exists_int_farkas_certificate (abs_matrix_le C L) (abs_rhs_le C) hno
  simp only [Fintype.card_fin] at hyN
  set E := (3 * L + 3) * (6 * L) with hE
  have h2L : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  have hN : (C.length ! * ((L + 1) * (2 ^ L + 1) ^ 2 + 1) ^ C.length : ℕ) ≤ 2 ^ E :=
    factorial_mul_pow_le (by omega) le_rfl (by rw [pow_succ]; omega)
  have hNE : ((C.length ! * ((L + 1) * (2 ^ L + 1) ^ 2 + 1) ^ C.length : ℕ) : ℤ) ≤
      ((2 ^ E : ℕ) : ℤ) := by exact_mod_cast hN
  refine ⟨List.ofFn y, ?_, ?_⟩
  · simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range]
    refine ⟨⟨fun z hz => ?_, fun c hc j hj => ?_⟩, ?_⟩
    · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hz
      exact hy i
    · have h := congrFun hyA ⟨j, hj.trans_le (hrow c hc)⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
      simp only [vecMul, dotProduct, matrix, of_apply, Pi.zero_apply] at h
      rw [dotProduct_map_eq_sum_fin]
      simpa only [List.getD_ofFn] using h
    · rw [dotProduct_map_eq_sum_fin]
      simpa only [List.getD_ofFn, dotProduct, rhs] using hyb
  · rw [eval_witnessPoly]
    refine (length_encList_le_of_abs_le (E := E) fun z hz => ?_).trans ?_
    · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hz
      rw [abs_of_nonneg (hy i)]
      exact (hyN i).trans hNE
    · rw [List.length_ofFn]
      exact Nat.mul_le_mul_right _ (by omega)

/-! ### Polynomial-time checks -/

private theorem listDotProduct_polyTime {α : Type} {input : α ↪ List Bool} {n : α → ℕ}
    {l w : α → List ℤ} (hn : ComputableInPolyTime n input encUnary)
    (hl : ComputableInPolyTime l input (encList encIntBin))
    (hw : ComputableInPolyTime w input (encList encIntBin)) :
    ComputableInPolyTime (fun a => ListMatrix.dotProduct (n a) (l a) (w a)) input encIntBin :=
  listDotProduct.comp (hn.prod (hl.prod hw))

attribute [local fun_prop] listDotProduct_polyTime

/-- The `NP` check is polynomial-time. -/
theorem computableInPolyTime_check : ComputableInPolyTime check
    (encPair (encSystem)
      (encPair encIntBin (encList encIntBin))) encBool := by
  unfold check
  apply bool_and' (by fun_prop)
  apply allWithInput (by fun_prop)
  fun_prop

/-- The `coNP` check is polynomial-time. -/
theorem computableInPolyTime_certCheck : ComputableInPolyTime certCheck
    (encPair (encSystem) (encList encIntBin)) encBool := by
  unfold certCheck
  apply bool_and' (bool_and' ?_ ?_) (by fun_prop)
  · apply allWithInput (by fun_prop)
    fun_prop
  · apply allWithInput (by fun_prop)
    apply allWithInput (by fun_prop)
    fun_prop

/-- Membership in `NP` from a sound and complete polynomial-time check with short witnesses. -/
private theorem mem_NP_of_check {α β : Type} {enc : α ↪ List Bool} {encW : β ↪ List Bool}
    (D : Decoder encW) {A : Set α} {chk : α × β → Bool} {p : Polynomial ℕ}
    (hchk : ComputableInPolyTime chk (encPair enc encW) encBool)
    (hsound : ∀ a b, chk (a, b) = true → a ∈ A)
    (hcomplete : ∀ a ∈ A, ∃ b, chk (a, b) = true ∧ (encW b).length ≤ p.eval (enc a).length) :
    A ∈ NP enc := by
  have hA : A = {a | ∃ b, chk (a, b) = true} := by
    ext a
    exact ⟨fun ha => (hcomplete a ha).imp fun _ hb => hb.1, fun ⟨b, hb⟩ => hsound a b hb⟩
  rw [hA]
  exact mem_NP_of_witness D hchk (fun _ _ => Iff.rfl) fun a b hb => hcomplete a (hsound a b hb)

/-- **Rational LP feasibility is in `NP`.** -/
theorem mem_NP : LPFeasibility ∈ NP (encSystem) :=
  mem_NP_of_check (.pair .intBin (.list .intBin)) computableInPolyTime_check
    (fun _ _ h => mem_of_check h) fun _ hC => exists_check_of_mem hC

/-- **Rational LP feasibility is in `coNP`.** -/
theorem mem_coNP : LPFeasibility ∈ coNP (encSystem) :=
  mem_NP_of_check (.list .intBin) computableInPolyTime_certCheck
    (fun _ _ h => notMem_of_certCheck h) fun _ hC => exists_certCheck_of_notMem hC

/-- **Rational LP feasibility is in `NP ∩ coNP`** [Schrijver1986, Section 10.1]. -/
theorem mem_NP_inter_coNP : LPFeasibility ∈ NP (encSystem) ∩
    coNP (encSystem) :=
  ⟨mem_NP, mem_coNP⟩

end LPFeasibility


end Cslib.Complexity

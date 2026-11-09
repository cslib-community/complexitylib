/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.Int.RowBasis
public import CslibFrontier.Foundations.LinearAlgebra.RowSelection
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Foundations.Data.Int.Order
import Mathlib.Data.List.GetD

/-!
# Binary rectangular linear-system recovery

`rectangularCertificate` selects original rows by the division-free Gram scan,
solves their nonsingular row Gram system by `cramerCertificate`, and multiplies
back by the transpose of the selected matrix. The result is a common-denominator
rational candidate for a general rectangular system. `rectangularConsistent`
checks that candidate against every original row. Width is explicit and unary;
missing entries are zero, and columns after the declared width are ignored.

This original implementation addresses the rectangular selection and consistency
step in [ChenJiangZhu2027], Lemma 3.1, PDF pp. 10–11. It uses polynomially many
Gram/Bird determinants, not a search through all minors. It is separate from the
existing rational query compiler until the composition theorem is supplied.
The source allows rational inputs after clearing denominators. This program takes
binary integers directly; a rational-input denominator-clearing compiler is not
part of its encoding theorem.

## Main results

* `rectangularConsistent_correct`: exact rational consistency for all rectangular inputs.
* `rectangularPoint_correct`: the recovered point satisfies every original row on acceptance.
* `rectangular_unique`: full computed column rank implies uniqueness.
* `rectangularBoolean_correct`: exact Boolean feasibility on full-column-rank systems.
* `rectangularCertificate_polytime`, `rectangularConsistent_polytime`: uniform binary time.
* `rectangularCertificate_bits_le`: explicit polynomial output coefficient widths.

## Main definitions

* `rectangularCertificate`: a denominator and one integer numerator per column.
* `rectangularConsistent`: check the actual scaled candidate on every original row.
-/

public section

namespace Cslib.LinearSystem

open Matrix Circuits.Rational Turing.MultiTapeTM

/-- Rectangular system: framed (framed unary width, binary integer row table), followed
by the framed-list binary integer right-hand side. Missing entries default to zero. -/
abbrev encRectangularSystem : ((ℕ × List (List ℤ)) × List ℤ) ↪ List Bool :=
  encPair (encPair encUnary encIntRows) (encList encIntBin)

/-- Multiply a selected-row vector by the transpose of its original coefficient
matrix, materializing exactly the declared number of columns. -/
@[expose] def transposeNumerators (n : ℕ) (A : List (List ℤ)) (ids : List ℕ)
    (y : List ℤ) : List ℤ :=
  (List.range n).map fun c => ((List.range ids.length).map fun i =>
    rowEntry A (ids.getD i 0) c * y.getD i 0).sum

/-- Solve the nonsingular row Gram system of the computed basis and multiply back.
The denominator is nonzero even when the rectangular input has dependent rows. -/
@[expose] def rectangularCertificate (n : ℕ) (A : List (List ℤ)) (b : List ℤ) : ℤ × List ℤ :=
  let ids := gramRowBasis n A
  let cert := cramerCertificate (rowGram n A ids) (ids.map fun i => b.getD i 0)
  (cert.1, transposeNumerators n A ids cert.2)

/-- Check every original equation in the integer common-denominator representation. -/
@[expose] def rectangularConsistent (n : ℕ) (A : List (List ℤ)) (b : List ℤ) : Bool :=
  let cert := rectangularCertificate n A b
  (List.range A.length).all fun i =>
    ((List.range n).map fun j => rowEntry A i j * cert.2.getD j 0).sum ==
      cert.1 * b.getD i 0

/-- Transpose recovery is polynomial-time jointly in all tables and indices. -/
@[fun_prop] theorem computableInPolyTime_transposeNumerators
    {α : Type} {enc : α ↪ List Bool} {n : α → ℕ} {A : α → List (List ℤ)}
    {ids : α → List ℕ} {y : α → List ℤ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hA : ComputableInPolyTime A enc encIntRows)
    (hi : ComputableInPolyTime ids enc (encList encUnary))
    (hy : ComputableInPolyTime y enc (encList encIntBin)) :
    ComputableInPolyTime (fun x => transposeNumerators (n x) (A x) (ids x) (y x))
      enc (encList encIntBin) := by
  unfold transposeNumerators
  fun_prop

/-- General rectangular recovery is uniformly polynomial binary time. Width is
unary, all matrix and RHS integers are binary, and no rank/basis advice is input. -/
@[fun_prop] theorem rectangularCertificate_polytime :
    ComputableInPolyTime (fun p : (ℕ × List (List ℤ)) × List ℤ =>
      rectangularCertificate p.1.1 p.1.2 p.2)
      encRectangularSystem
      (encPair encIntBin (encList encIntBin)) := by
  unfold rectangularCertificate
  have hi : ComputableInPolyTime (fun p : (ℕ × List (List ℤ)) × List ℤ =>
      gramRowBasis p.1.1 p.1.2)
      encRectangularSystem
      (encList encUnary) := gramRowBasis_polytime.comp (by fun_prop)
  have hG := computableInPolyTime_rowGram
    (show ComputableInPolyTime (fun p : (ℕ × List (List ℤ)) × List ℤ => p.1.1)
      encRectangularSystem
      encUnary from by fun_prop)
    (show ComputableInPolyTime (fun p : (ℕ × List (List ℤ)) × List ℤ => p.1.2)
      encRectangularSystem
      encIntRows from by fun_prop) hi
  have hr : ComputableInPolyTime (fun p : (ℕ × List (List ℤ)) × List ℤ =>
      (gramRowBasis p.1.1 p.1.2).map fun i => p.2.getD i 0)
      encRectangularSystem
      (encList encIntBin) := by
    apply ComputableInPolyTime.mapWithInput hi
    fun_prop
  have hc := cramerCertificate_polytime.comp (hG.prod hr)
  exact hc.fst'.prod (computableInPolyTime_transposeNumerators
    (by fun_prop) (by fun_prop) hi hc.snd')

/-- Checking every original equation includes the cost of rectangular recovery. -/
@[fun_prop] theorem rectangularConsistent_polytime :
    ComputableInPolyTime (fun p : (ℕ × List (List ℤ)) × List ℤ =>
      rectangularConsistent p.1.1 p.1.2 p.2)
      encRectangularSystem
      encBool := by
  unfold rectangularConsistent
  have hc := rectangularCertificate_polytime
  fun_prop

/-- Recovery materializes every declared coordinate, including unused columns. -/
@[simp] theorem length_rectangularCertificate (n : ℕ) (A : List (List ℤ)) (b : List ℤ) :
    (rectangularCertificate n A b).2.length = n := by
  simp [rectangularCertificate, transposeNumerators]

/-- The selected Gram denominator never vanishes; zero-dimensional systems use
its empty determinant one. No rectangular nonsingularity hypothesis is required. -/
theorem rectangularCertificate_den_ne_zero (n : ℕ) (A : List (List ℤ)) (b : List ℤ) :
    (rectangularCertificate n A b).1 ≠ 0 :=
  (rowGram_ne_zero_iff n A (gramRowBasis n A)).mpr (gramRowBasis_independent n A)

private theorem transposeNumerators_getD (n : ℕ) (A : List (List ℤ)) (ids : List ℕ)
    (y : List ℤ) (j : Fin n) :
    (transposeNumerators n A ids y).getD j 0 =
      ∑ i : Fin ids.length, rowEntry A (ids.getD i 0) j * y.getD i 0 := by
  simp [transposeNumerators, List.getD_eq_getElem?_getD, j.isLt, List.sum_map_range]

/-- The actual integer numerator satisfies every selected original equation after
scaling by the computed denominator. -/
theorem rectangularCertificate_selected (n : ℕ) (A : List (List ℤ)) (b : List ℤ)
    (i : Fin (gramRowBasis n A).length) :
    (∑ j : Fin n, rowEntry A ((gramRowBasis n A).getD i 0) j *
      (rectangularCertificate n A b).2.getD j 0) =
      (rectangularCertificate n A b).1 * b.getD ((gramRowBasis n A).getD i 0) 0 := by
  let ids := gramRowBasis n A
  let G := rowGram n A ids
  let rhs := ids.map fun i => b.getD i 0
  let cert := cramerCertificate G rhs
  have hlen : G.length = ids.length := by simp [G, rowGram]
  have hi : (i : ℕ) < ids.length := i.isLt
  have h := cramerCertificate_correct G rhs ⟨i, hlen.symm ▸ hi⟩
  have hsum := Fin.sum_univ_eq_sum_range
    (fun k => rowEntry G i k * cert.2.getD k 0) G.length
  have hnat := hsum.symm.trans h
  change _ = cert.1 * rhs.getD (i : ℕ) 0 at hnat
  rw [hlen] at hnat
  have hb : rhs.getD i 0 = b.getD (ids.getD i 0) 0 := by
    simp [rhs, List.getD_eq_getElem?_getD, hi]
  rw [hb] at hnat
  change (∑ j : Fin n, rowEntry A (ids.getD i 0) j *
    (transposeNumerators n A ids cert.2).getD j 0) = cert.1 * _
  simp only [transposeNumerators_getD, Finset.mul_sum]
  rw [Finset.sum_comm]
  have he : (∑ k : Fin ids.length, ∑ j : Fin n,
      rowEntry A (ids.getD i 0) j * (rowEntry A (ids.getD k 0) j * cert.2.getD k 0)) =
      ∑ k : Fin ids.length, rowEntry G i k * cert.2.getD k 0 := by
    apply Finset.sum_congr rfl
    intro k _
    simp [G, rowGram, rowEntry_tabulateTable, hi, k.isLt, List.sum_map_range,
      Finset.sum_mul, mul_assoc]
  rw [he]
  exact (Fin.sum_univ_eq_sum_range
    (fun k => rowEntry G i k * cert.2.getD k 0) ids.length).trans hnat

/-- Every partial sum in the transpose recovery has polynomial binary width. -/
theorem transposeNumerators_partial_sum_natAbs_lt (n : ℕ) (A : List (List ℤ))
    (ids : List ℕ) (y : List ℤ) (β γ c k : ℕ) (hs : ids.length ≤ n)
    (hA : ∀ i j, (rowEntry A i j).natAbs < 2 ^ β)
    (hy : ∀ i, (y.getD i 0).natAbs < 2 ^ γ) :
    ((((List.range ids.length).map fun i => rowEntry A (ids.getD i 0) c *
      y.getD i 0).take k).sum).natAbs < 2 ^ (n + β + γ) := by
  have hb := List.natAbs_sum_take_le_length_mul
    (l := (List.range ids.length).map fun i => rowEntry A (ids.getD i 0) c * y.getD i 0)
    (C := 2 ^ β * 2 ^ γ) (by
      intro z hz
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hA _ _).le (hy _).le) k
  simp only [List.length_map, List.length_range] at hb
  calc _ ≤ ids.length * (2 ^ β * 2 ^ γ) := hb
       _ ≤ n * (2 ^ β * 2 ^ γ) := Nat.mul_le_mul_right _ hs
       _ < 2 ^ n * (2 ^ β * 2 ^ γ) :=
         Nat.mul_lt_mul_of_pos_right (Nat.lt_two_pow_self (n := n)) (by positivity)
       _ = 2 ^ (n + β + γ) := by simp only [pow_add, mul_assoc]

/-- Explicit polynomial output widths for general rectangular recovery. With
`g = n + 2β` and `B = g + n(1+n+g)+2`, the denominator has at most `B` bits and
all final numerators at most `n+β+B+1` bits. Gram partial sums, every Bird stage,
and transpose partial sums have separate certificates above/in `RowBasis`.
The hypotheses bound only the original input integers. -/
theorem rectangularCertificate_bits_le (n : ℕ) (A : List (List ℤ)) (b : List ℤ) (β : ℕ)
    (hA : ∀ i j, (rowEntry A i j).natAbs < 2 ^ β)
    (hb : ∀ i, (b.getD i 0).natAbs < 2 ^ β) :
    let g := n + 2 * β
    let B := g + n * (1 + n + g) + 2
    intBits (rectangularCertificate n A b).1 ≤ B ∧
      ∀ z ∈ (rectangularCertificate n A b).2, intBits z ≤ n + β + B + 1 := by
  let ids := gramRowBasis n A
  let G := rowGram n A ids
  let rhs := ids.map fun i => b.getD i 0
  let g := n + 2 * β
  let B := g + n * (1 + n + g) + 2
  have hs : ids.length ≤ n := gramRowBasis_length n A
  have hlen : G.length = ids.length := by simp [G, rowGram]
  have hg : β ≤ g := by dsimp [g]; omega
  have hr : ∀ i, (rhs.getD i 0).natAbs < 2 ^ g := by
    intro i
    by_cases hi : i < ids.length
    · have he : rhs.getD i 0 = b.getD (ids.getD i 0) 0 := by
        simp [rhs, List.getD_eq_getElem?_getD, hi]
      rw [he]
      exact (hb _).trans_le (Nat.pow_le_pow_right (by decide) hg)
    · rw [List.getD_eq_default _ _ (by simpa [rhs] using Nat.le_of_not_lt hi)]
      exact Nat.two_pow_pos _
  have hcert := cramerCertificate_bits_le G rhs g (rowGram_natAbs_lt n A ids β hA) hr
  have hbound : g + G.length * (1 + G.length + g) + 2 ≤ B := by
    rw [hlen]
    exact Nat.add_le_add_right (Nat.add_le_add_left
      (Nat.mul_le_mul hs (by omega)) g) 2
  have hy : ∀ i, ((cramerCertificate G rhs).2.getD i 0).natAbs < 2 ^ B := by
    intro i
    by_cases hi : i < (cramerCertificate G rhs).2.length
    · rw [List.getD_eq_getElem _ _ hi]
      apply (intBits_le_iff _ B).mp
      exact (hcert.2 _ (List.getElem_mem hi)).trans (hbound.trans (Nat.le_succ B))
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
      exact Nat.two_pow_pos _
  refine ⟨hcert.1.trans hbound, ?_⟩
  intro z hz
  change z ∈ transposeNumerators n A ids (cramerCertificate G rhs).2 at hz
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hz
  apply (intBits_le_iff _ (n + β + B)).mpr
  have h := transposeNumerators_partial_sum_natAbs_lt n A ids
    (cramerCertificate G rhs).2 β B c ids.length hs hA hy
  rw [List.take_of_length_le (by simp)] at h
  exact h

/-- The common-denominator certificate interpreted as a rational point; no rational
normalization occurs inside the binary-certified program. -/
@[expose] def rectangularPoint (n : ℕ) (A : List (List ℤ)) (b : List ℤ) : Fin n → ℚ :=
  fun j => ((rectangularCertificate n A b).2.getD j 0 : ℚ) /
    (rectangularCertificate n A b).1

private theorem rectangularPoint_equation_iff (n : ℕ) (A : List (List ℤ)) (b : List ℤ)
    (i : ℕ) :
    (fun j : Fin n => (rowEntry A i j : ℚ)) ⬝ᵥ rectangularPoint n A b = b.getD i 0 ↔
      (∑ j : Fin n, rowEntry A i j * (rectangularCertificate n A b).2.getD j 0) =
        (rectangularCertificate n A b).1 * b.getD i 0 := by
  have hd : ((rectangularCertificate n A b).1 : ℚ) ≠ 0 := by
    exact_mod_cast rectangularCertificate_den_ne_zero n A b
  simp only [dotProduct, rectangularPoint, ← mul_div_assoc, ← Finset.sum_div]
  rw [div_eq_iff hd]
  rw [mul_comm (b.getD i 0 : ℚ)]
  exact_mod_cast Iff.rfl

/-- The actual recovered rational point satisfies all selected original equations. -/
theorem rectangularPoint_selected (n : ℕ) (A : List (List ℤ)) (b : List ℤ)
    (i : Fin (gramRowBasis n A).length) :
    (indexedRows n A (gramRowBasis n A)).row i ⬝ᵥ rectangularPoint n A b =
      b.getD ((gramRowBasis n A).getD i 0) 0 :=
  (rectangularPoint_equation_iff n A b _).mpr (rectangularCertificate_selected n A b i)

/-- The binary test detects rational consistency of any rectangular integer system.
In particular, singular square inputs and dependent or contradictory extra rows are
handled without a nonsingularity, supplied-basis or correctness premise. -/
theorem rectangularConsistent_correct (n : ℕ) (A : List (List ℤ)) (b : List ℤ) :
    rectangularConsistent n A b = true ↔ ∃ x : Fin n → ℚ,
      ∀ i : Fin A.length, (fun j : Fin n => (rowEntry A i j : ℚ)) ⬝ᵥ x = b.getD i 0 := by
  have htest : rectangularConsistent n A b = true ↔
      ∀ i : Fin A.length,
        (fun j : Fin n => (rowEntry A i j : ℚ)) ⬝ᵥ rectangularPoint n A b = b.getD i 0 := by
    simp only [rectangularConsistent, List.all_eq_true, beq_iff_eq]
    constructor
    · intro h i
      apply (rectangularPoint_equation_iff n A b i).mpr
      simpa only [List.sum_map_range] using h i (List.mem_range.mpr i.isLt)
    · intro h i hi
      have he := (rectangularPoint_equation_iff n A b i).mp (h ⟨i, List.mem_range.mp hi⟩)
      simpa only [List.sum_map_range] using he
  rw [htest]
  constructor
  · intro h; exact ⟨rectangularPoint n A b, h⟩
  · rintro ⟨x₀, hx₀⟩
    exact (gramRowBasis_selected_iff n A b x₀ hx₀ (rectangularPoint n A b)).mp
      (rectangularPoint_selected n A b)

/-- An accepting execution returns an actual rational solution of every original
equation, not merely some existential consistency certificate. -/
theorem rectangularPoint_correct (n : ℕ) (A : List (List ℤ)) (b : List ℤ)
    (hc : rectangularConsistent n A b = true) :
    ∀ i : Fin A.length, (fun j : Fin n => (rowEntry A i j : ℚ)) ⬝ᵥ
      rectangularPoint n A b = b.getD i 0 := by
  obtain ⟨x₀, hx₀⟩ := (rectangularConsistent_correct n A b).mp hc
  exact (gramRowBasis_selected_iff n A b x₀ hx₀ _).mp (rectangularPoint_selected n A b)

/-- Full computed column rank gives uniqueness, with arbitrary numbers of original
rows. The rank condition is checked by the executable selector's output length. -/
theorem rectangular_unique (n : ℕ) (A : List (List ℤ)) (b : List ℤ)
    (hfull : (gramRowBasis n A).length = n) (x y : Fin n → ℚ)
    (hx : ∀ i : Fin A.length, (fun j : Fin n => (rowEntry A i j : ℚ)) ⬝ᵥ x = b.getD i 0)
    (hy : ∀ i : Fin A.length, (fun j : Fin n => (rowEntry A i j : ℚ)) ⬝ᵥ y = b.getD i 0) :
    x = y := by
  apply solution_eq_of_span_eq_top _ (fun i : Fin A.length => (b.getD i 0 : ℚ)) _ hx hy
  apply Submodule.eq_top_of_finrank_eq
  rw [← gramRowBasis_rank, hfull]
  simp

/-- Test whether the computed consistent candidate is Boolean. This decides Boolean
feasibility on full-column-rank inputs. On deficient inputs a different Boolean
solution may exist, so this test alone is not a feasibility decision procedure. -/
@[expose] def rectangularBoolean (n : ℕ) (A : List (List ℤ)) (b : List ℤ) : Bool :=
  let cert := rectangularCertificate n A b
  rectangularConsistent n A b && cert.2.all (fun z => z == 0 || z == cert.1)

/-- Candidate Booleanity testing is uniformly polynomial binary time. -/
@[fun_prop] theorem rectangularBoolean_polytime :
    ComputableInPolyTime (fun p : (ℕ × List (List ℤ)) × List ℤ =>
      rectangularBoolean p.1.1 p.1.2 p.2)
      encRectangularSystem
      encBool := by
  unfold rectangularBoolean
  have hbool : ComputableInPolyTime (fun cert : ℤ × List ℤ =>
      cert.2.all (fun z => z == 0 || z == cert.1))
      (encPair encIntBin (encList encIntBin)) encBool := by fun_prop
  exact rectangularConsistent_polytime.bool_and' (hbool.comp rectangularCertificate_polytime)

/-- Exact Boolean feasibility for arbitrary rectangular full-column-rank inputs.
The rank hypothesis refers to the executed row count, identified with mathematical
rank by `gramRowBasis_rank`. Consistency is tested, rather than assumed. -/
theorem rectangularBoolean_correct (n : ℕ) (A : List (List ℤ)) (b : List ℤ)
    (hfull : (gramRowBasis n A).length = n) :
    rectangularBoolean n A b = true ↔ ∃ x : Fin n → Bool,
      ∀ i : Fin A.length, (∑ j : Fin n,
        rowEntry A i j * (if x j then (1 : ℤ) else 0)) = b.getD i 0 := by
  let cert := rectangularCertificate n A b
  have hd : (cert.1 : ℚ) ≠ 0 := by exact_mod_cast rectangularCertificate_den_ne_zero n A b
  have hcoord (j : Fin n) : cert.2.getD j 0 ∈ cert.2 := by
    have hj : (j : ℕ) < cert.2.length := by simp [cert]
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  constructor
  · intro h
    have ht : rectangularConsistent n A b = true ∧
        ∀ z ∈ cert.2, z = 0 ∨ z = cert.1 := by
      simpa only [rectangularBoolean, Bool.and_eq_true, List.all_eq_true,
        Bool.or_eq_true, beq_iff_eq] using h
    let x : Fin n → Bool := fun j => decide (cert.2.getD j 0 = cert.1)
    have hx (j : Fin n) : rectangularPoint n A b j = (if x j then (1 : ℚ) else 0) := by
      change (cert.2.getD j 0 : ℚ) / cert.1 = _
      rcases ht.2 _ (hcoord j) with hz | hz
      · have hd' : cert.1 ≠ 0 := rectangularCertificate_den_ne_zero n A b
        simp only [x, hz, decide_eq_true_eq, ite_eq_right (Ne.symm hd'), Int.cast_zero, zero_div]
      · simp only [x, hz, decide_true, ite_true, div_self hd]
    refine ⟨x, fun i => ?_⟩
    have he := rectangularPoint_correct n A b ht.1 i
    simp only [dotProduct, hx] at he
    exact_mod_cast he
  · rintro ⟨x, hx⟩
    have he : ∀ i : Fin A.length, (fun j : Fin n => (rowEntry A i j : ℚ)) ⬝ᵥ
        (fun j => if x j then (1 : ℚ) else 0) = b.getD i 0 := by
      intro i
      dsimp only [dotProduct]
      exact_mod_cast hx i
    have hc : rectangularConsistent n A b = true :=
      (rectangularConsistent_correct n A b).mpr ⟨_, he⟩
    have hu := rectangular_unique n A b hfull (rectangularPoint n A b) _
      (rectangularPoint_correct n A b hc) he
    have hz : ∀ z ∈ cert.2, z = 0 ∨ z = cert.1 := by
      intro z hz
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz
      have hj' : j < n := by simpa [cert] using hj
      have hh := congrFun hu ⟨j, hj'⟩
      change (cert.2.getD j 0 : ℚ) / cert.1 = _ at hh
      rw [List.getD_eq_getElem _ _ hj, div_eq_iff hd] at hh
      cases hb : x ⟨j, hj'⟩
      · have hh' : (cert.2[j] : ℚ) = 0 := by simpa only [hb, Bool.false_eq_true,
          ite_false, zero_mul] using hh
        exact Or.inl (by exact_mod_cast hh')
      · have hh' : (cert.2[j] : ℚ) = cert.1 := by simpa only [hb, ite_true, one_mul] using hh
        exact Or.inr (by exact_mod_cast hh')
    simpa only [rectangularBoolean, Bool.and_eq_true, List.all_eq_true,
      Bool.or_eq_true, beq_iff_eq] using And.intro hc hz

end Cslib.LinearSystem

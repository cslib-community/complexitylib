/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Rational.Runtime.Determinant
public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.List.GetD
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Binary Cramer certificates using division-free determinants

A square integer system is represented by lists of binary sign-magnitude integers.
`cramerCertificate` computes a common denominator and all numerator coordinates by
Bird's division-free determinant program. Dimensions come from the input row count;
missing entries are zero and extra columns are ignored, as in `Rational.detRows`.

This supplies a controlled alternative for square-system recovery in the row-selection
step of [ChenJiangZhu2027], Lemma 3.1, PDF pp. 10–11. It does not select independent
rows of a rectangular system or certify the existing rational elimination program.
The runtime theorem includes binary arithmetic, rather than unit-cost determinants.

## Main definitions

* `cramerColumnRows`: replace a column of the square normalization by a right-hand side.
* `cramerCertificate`: common denominator and numerator list.

## Main results

* `cramerCertificate_correct`: the computed integers satisfy the scaled input equations.
* `cramerCertificate_polytime`: uniform polynomial binary time, with input-varying dimension.
* `cramerCertificate_bits_le`: polynomial encoded width of the actual emitted integers.
* `cramerBoolean_correct`: exact Boolean feasibility for nonsingular square inputs.
* `cramerBoolean_polytime`: polynomial binary time for the Booleanity test.
-/

public section

namespace Cslib.LinearSystem

open Circuits.Rational Matrix
open Turing.MultiTapeTM

/-- Replace column `c` of the square normalization of `A` by `b` (defaulting to zero). -/
@[expose] def cramerColumnRows (A : List (List ℤ)) (b : List ℤ) (c : ℕ) : List (List ℤ) :=
  tabulateTable A.length A.length fun i j => if j = c then b.getD i 0 else rowEntry A i j

/-- The determinant denominator and all Cramer numerators, computed without rational
intermediates. A zero denominator marks a singular square system. -/
@[expose] def cramerCertificate (A : List (List ℤ)) (b : List ℤ) : ℤ × List ℤ :=
  (detRows A, (List.range A.length).map fun c => detRows (cramerColumnRows A b c))

/-- Column replacement agrees with the mathematical matrix update. -/
theorem detRows_cramerColumnRows (A : List (List ℤ)) (b : List ℤ) (c : Fin A.length) :
    detRows (cramerColumnRows A b c) =
      ((ofRows A).updateCol c (fun i => b.getD i 0)).det := by
  apply detRows_eq_det_of_rowEntry
  · simp [cramerColumnRows, tabulateTable]
  · intro i j
    simp [cramerColumnRows, rowEntry_tabulateTable, Matrix.updateCol_apply,
      ofRows, Fin.ext_iff]

/-- The computed numerators have exactly one coordinate per input row. -/
@[simp] theorem length_cramerCertificate (A : List (List ℤ)) (b : List ℤ) :
    (cramerCertificate A b).2.length = A.length := by
  simp [cramerCertificate]

/-- The integer certificate is precisely the adjugate/Cramer vector. -/
theorem cramerCertificate_numerator (A : List (List ℤ)) (b : List ℤ)
    (i : Fin A.length) :
    (cramerCertificate A b).2.getD i 0 = (ofRows A).cramer (fun j => b.getD j 0) i := by
  simp [cramerCertificate, List.getD_eq_getElem?_getD, detRows_cramerColumnRows,
    Matrix.cramer_apply]

/-- Every computed certificate satisfies `A n = d b`, including singular systems.
For nonzero `d` the quotients are therefore an actual rational solution. -/
theorem cramerCertificate_correct (A : List (List ℤ)) (b : List ℤ) (i : Fin A.length) :
    (∑ j : Fin A.length, rowEntry A i j * (cramerCertificate A b).2.getD j 0) =
      (cramerCertificate A b).1 * b.getD i 0 := by
  simp only [cramerCertificate_numerator]
  have h := congrFun (Matrix.mulVec_cramer (ofRows A) (fun j => b.getD j 0)) i
  simpa [Matrix.mulVec, dotProduct, ofRows, cramerCertificate, detRows_eq_det_ofRows] using h

/-- Constructing a column-replaced square is polynomial-time under explicit binary
integer encodings and unary column indices. -/
@[fun_prop] theorem computableInPolyTime_cramerColumnRows
    {α : Type} {enc : α ↪ List Bool} {A : α → List (List ℤ)} {b : α → List ℤ} {c : α → ℕ}
    (hA : ComputableInPolyTime A enc (encList (encList encIntBin)))
    (hb : ComputableInPolyTime b enc (encList encIntBin))
    (hc : ComputableInPolyTime c enc encUnary) :
    ComputableInPolyTime (fun x => cramerColumnRows (A x) (b x) (c x))
      enc (encList (encList encIntBin)) := by
  unfold cramerColumnRows
  apply computableInPolyTime_tabulateTable (by fun_prop) (by fun_prop)
  dsimp only [TableIndex.ctx, TableIndex.row, TableIndex.col, TableIndex.rowCtx]
  fun_prop

/-- The complete certificate is uniformly polynomial-time on framed lists of binary
integers. The dimension is the row count of `A`, not a fixed external parameter.
The determinant certificate already controls all Bird-stage intermediate bit lengths. -/
@[fun_prop] theorem cramerCertificate_polytime :
    ComputableInPolyTime (fun p : List (List ℤ) × List ℤ => cramerCertificate p.1 p.2)
      (encPair (encList (encList encIntBin)) (encList encIntBin))
      (encPair encIntBin (encList encIntBin)) := by
  unfold cramerCertificate
  apply ComputableInPolyTime.prod
  · fun_prop
  · apply ComputableInPolyTime.mapWithInput (by fun_prop)
    exact detRows_polytime.comp (computableInPolyTime_cramerColumnRows
      (by fun_prop) (by fun_prop) (by fun_prop))

/-- All intermediate entries of every numerator determinant have polynomially
many bits in the input entry width and row count, including singular inputs. The
same determinant module also bounds the partial sums and products of each stage. -/
theorem cramerColumnRows_stage_bits_le (A : List (List ℤ)) (b : List ℤ) (β c k i j : ℕ)
    (hA : ∀ i j, (rowEntry A i j).natAbs < 2 ^ β)
    (hb : ∀ i, (b.getD i 0).natAbs < 2 ^ β) :
    intBits (rowEntry (stagesRows (cramerColumnRows A b c) k) i j) ≤
      β + k * (1 + A.length + β) + 1 := by
  have hcol : ∀ i j, (rowEntry (cramerColumnRows A b c) i j).natAbs < 2 ^ β := by
    intro i j
    simp only [cramerColumnRows, rowEntry_tabulateTable]
    split_ifs
    · exact hb i
    · exact hA i j
    · exact Nat.two_pow_pos β
  simpa [cramerColumnRows, tabulateTable] using
    intBits_rowEntry_stagesRows_le (fun i j => (intBits_le_iff _ _).mpr (hcol i j)) k i j

/-- Every integer in the computed certificate has polynomial encoded width;
no hypothesis about an output or an elimination runtime is used. -/
theorem cramerCertificate_bits_le (A : List (List ℤ)) (b : List ℤ) (β : ℕ)
    (hA : ∀ i j, (rowEntry A i j).natAbs < 2 ^ β)
    (hb : ∀ i, (b.getD i 0).natAbs < 2 ^ β) :
    intBits (cramerCertificate A b).1 ≤ β + A.length * (1 + A.length + β) + 2 ∧
      ∀ z ∈ (cramerCertificate A b).2,
        intBits z ≤ β + A.length * (1 + A.length + β) + 2 := by
  refine ⟨detRows_bits_le A β hA, ?_⟩
  intro z hz
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hz
  have hcol : ∀ i j, (rowEntry (cramerColumnRows A b c) i j).natAbs < 2 ^ β := by
    intro i j
    simp only [cramerColumnRows, rowEntry_tabulateTable]
    split_ifs
    · exact hb i
    · exact hA i j
    · exact Nat.two_pow_pos β
  simpa [cramerColumnRows, tabulateTable] using detRows_bits_le _ β hcol

/-- Check Booleanity directly in the common-denominator representation. Singular
inputs are rejected; they need the rectangular selection/consistency algorithm. -/
@[expose] def cramerBoolean (A : List (List ℤ)) (b : List ℤ) : Bool :=
  let cert := cramerCertificate A b
  cert.1 != 0 && cert.2.all (fun z => z == 0 || z == cert.1)

/-- Booleanity testing includes the cost of constructing every numerator. -/
@[fun_prop] theorem cramerBoolean_polytime :
    ComputableInPolyTime (fun p : List (List ℤ) × List ℤ => cramerBoolean p.1 p.2)
      (encPair (encList (encList encIntBin)) (encList encIntBin)) encBool := by
  unfold cramerBoolean
  fun_prop

/-- Any integer solution determines the certificate numerators, without dividing. -/
theorem cramerCertificate_of_solution (A : List (List ℤ)) (b : List ℤ)
    (x : Fin A.length → ℤ) (hx : (ofRows A) *ᵥ x = fun i : Fin A.length => b.getD i 0)
    (i : Fin A.length) :
    (cramerCertificate A b).2.getD i 0 = (cramerCertificate A b).1 * x i := by
  rw [cramerCertificate_numerator, ← hx, Matrix.cramer_eq_adjugate_mulVec,
    Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp [cramerCertificate, detRows_eq_det_ofRows]

/-- A nonzero denominator allows at most one integer solution, hence at most
one Boolean solution. This uses integer cancellation without rational normalization. -/
theorem cramerCertificate_unique (A : List (List ℤ)) (b : List ℤ)
    (hd : detRows A ≠ 0) (x y : Fin A.length → ℤ)
    (hx : (ofRows A) *ᵥ x = fun i : Fin A.length => b.getD i 0)
    (hy : (ofRows A) *ᵥ y = fun i : Fin A.length => b.getD i 0) : x = y := by
  funext i
  exact mul_left_cancel₀ hd ((cramerCertificate_of_solution A b x hx i).symm.trans
    (cramerCertificate_of_solution A b y hy i))

/-- On a nonsingular square system, the native test accepts exactly when the
integer equations have a Boolean solution. It makes no promise about singular
systems, which can have zero, one or many Boolean solutions. -/
theorem cramerBoolean_correct (A : List (List ℤ)) (b : List ℤ)
    (hd : detRows A ≠ 0) :
    cramerBoolean A b = true ↔ ∃ x : Fin A.length → Bool,
      ∀ i : Fin A.length, (∑ j : Fin A.length,
        rowEntry A i j * (if x j then (1 : ℤ) else 0)) = b.getD i 0 := by
  have hden : (cramerCertificate A b).1 ≠ 0 := hd
  constructor
  · intro h
    have hz : ∀ z ∈ (cramerCertificate A b).2,
        z = 0 ∨ z = (cramerCertificate A b).1 := by
      exact (show (cramerCertificate A b).1 ≠ 0 ∧ _ by
        simpa [cramerBoolean, Bool.and_eq_true, List.all_eq_true] using h).2
    let x : Fin A.length → Bool := fun j =>
      decide ((cramerCertificate A b).2.getD j 0 = (cramerCertificate A b).1)
    have hn (j : Fin A.length) : (cramerCertificate A b).2.getD j 0 =
        (cramerCertificate A b).1 * (if x j then (1 : ℤ) else 0) := by
      have hj : j.val < (cramerCertificate A b).2.length := by simp
      have hm : (cramerCertificate A b).2.getD j 0 ∈ (cramerCertificate A b).2 := by
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      rcases hz _ hm with h0 | he
      · simp only [x, h0]
        simp [Ne.symm hden]
      · simp only [x, he]
        simp
    refine ⟨x, fun i => ?_⟩
    have hc := cramerCertificate_correct A b i
    simp only [hn, mul_left_comm (rowEntry A i _) (cramerCertificate A b).1,
      ← Finset.mul_sum] at hc
    exact mul_left_cancel₀ hden hc
  · rintro ⟨x, hx⟩
    have he : (ofRows A) *ᵥ (fun j => if x j then (1 : ℤ) else 0) =
        fun i : Fin A.length => b.getD i 0 := by
      funext i
      exact hx i
    have hz : ∀ z ∈ (cramerCertificate A b).2,
        z = 0 ∨ z = (cramerCertificate A b).1 := by
      intro z hz
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz
      have hj' : j < A.length := by simpa using hj
      have heq := cramerCertificate_of_solution A b _ he ⟨j, hj'⟩
      rw [List.getD_eq_getElem _ _ hj] at heq
      cases h : x ⟨j, hj'⟩ <;> simp [h] at heq <;> simp [heq]
    simpa [cramerBoolean, Bool.and_eq_true, List.all_eq_true, hden] using hz

end Cslib.LinearSystem

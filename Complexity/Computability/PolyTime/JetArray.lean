/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.PolyTime.Int.Table
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Size
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.Int.Order
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.GetD

/-!
# Dense truncated bivariate jet arrays in polynomial time

Appendix B.2 of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] represents
elements of the truncated bivariate polynomial ring `ℤ[V]/(V^ℓ)[z]/(z^J)` as dense `J × ℓ`
tables of integer coefficients, stored in their unique representative modulo `(z^J, V^ℓ)`.

Building on the rectangular integer table primitives (`Cslib.IsTableShape`, `Cslib.rowEntry`,
`Cslib.tabulateTable`) in `Complexity/Computability/PolyTime/Int/Table.lean`, this module provides
executable truncated jet operations on `List (List ℤ)` (`Cslib.JetRows`), proves exact coefficient
formulas and commutative-ring laws on `(J, ℓ)`-shaped arrays, establishes `ℓ₁` coefficient-norm and
binary bit-length bounds for truncated 2D convolution, and certifies that every operation is
computable in polynomial time on multi-tape Turing machines
(`Turing.MultiTapeTM.ComputableInPolyTime`) with dimensions `(J, ℓ)` in unary and coefficient
tables in `encList (encList encIntBin)`.

## Main definitions

* `Cslib.JetRows`: alias `List (List ℤ)` for dense `J × ℓ` coefficient tables.
* `Cslib.zeroJet`, `Cslib.constJet`, `Cslib.zJet`, `Cslib.vJet`: zero, constant, and generator
  jet arrays.
* `Cslib.addJet`, `Cslib.negJet`, `Cslib.subJet`, `Cslib.smulJet`: linear operations on `J × ℓ`
  jet arrays.
* `Cslib.shiftZJet`, `Cslib.shiftVJet`: multiplication by `z` modulo `z^J` and by `V` modulo `V^ℓ`.
* `Cslib.convEntry`, `Cslib.convJet`: truncated 2D Cauchy product in `O(J^2 ℓ^2)` integer
  operations.
* `Cslib.jetL1Norm`: the `ℓ₁` coefficient norm `∑ |c_{j, u}|` of a list of rows.

## Main results

* `Cslib.rowEntry_zeroJet`, `Cslib.rowEntry_constJet`, `Cslib.rowEntry_addJet`,
  `Cslib.rowEntry_negJet`, `Cslib.rowEntry_subJet`, `Cslib.rowEntry_smulJet`,
  `Cslib.rowEntry_shiftZJet`, `Cslib.rowEntry_shiftVJet`, `Cslib.rowEntry_convJet`: exact in-bounds
  coefficient formulas.
* `Cslib.addJet_comm`, `Cslib.addJet_assoc`, `Cslib.convJet_comm`, `Cslib.convJet_assoc`,
  `Cslib.convJet_addJet`, `Cslib.addJet_convJet`, `Cslib.constJet_one_convJet`,
  `Cslib.convJet_constJet_one`: commutative-ring identities on `(J, ℓ)`-shaped arrays.
* `Cslib.jetL1Norm_addJet_le`, `Cslib.jetL1Norm_convJet_le`: subadditivity and submultiplicativity
  of the `ℓ₁` coefficient norm under truncated addition and 2D convolution.
* `Cslib.size_natAbs_rowEntry_convJet_le`, `Cslib.length_encIntBin_mem_convJet_le`: binary
  magnitude and encoded bit-length bounds on entries of `convJet`.
* `Cslib.computableInPolyTime_zeroJet`, `Cslib.computableInPolyTime_constJet`,
  `Cslib.computableInPolyTime_addJet`, `Cslib.computableInPolyTime_negJet`,
  `Cslib.computableInPolyTime_subJet`, `Cslib.computableInPolyTime_smulJet`,
  `Cslib.computableInPolyTime_shiftZJet`, `Cslib.computableInPolyTime_shiftVJet`,
  `Cslib.computableInPolyTime_convJet`: plain `ComputableInPolyTime` composition rules and
  direct certificates (`zeroJet_polytime`, …, `convJet_polytime`).

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
-/

@[expose] public section

namespace Cslib

/-- Dense list-of-rows representation of truncated bivariate jets in `ℤ[V]/(V^ℓ)[z]/(z^J)`. -/
abbrev JetRows : Type := List (List ℤ)

/-! ### Executable jet operations -/

/-- The `J × ℓ` zero jet array. -/
def zeroJet (J ℓ : ℕ) : List (List ℤ) :=
  tabulateTable J ℓ fun _ _ => 0

/-- The constant jet `c` placed at `(0, 0)` and `0` elsewhere, truncated to `J × ℓ`. -/
def constJet (J ℓ : ℕ) (c : ℤ) : List (List ℤ) :=
  tabulateTable J ℓ fun j u => if j = 0 ∧ u = 0 then c else 0

/-- The generator `z` in `ℤ[V]/(V^ℓ)[z]/(z^J)` (`1` at `(1, 0)` when in range). -/
def zJet (J ℓ : ℕ) : List (List ℤ) :=
  tabulateTable J ℓ fun j u => if j = 1 ∧ u = 0 then 1 else 0

/-- The generator `V` in `ℤ[V]/(V^ℓ)[z]/(z^J)` (`1` at `(0, 1)` when in range). -/
def vJet (J ℓ : ℕ) : List (List ℤ) :=
  tabulateTable J ℓ fun j u => if j = 0 ∧ u = 1 then 1 else 0

/-- Entrywise addition of two jet arrays, normalized to shape `J × ℓ`. -/
def addJet (J ℓ : ℕ) (A B : List (List ℤ)) : List (List ℤ) :=
  tabulateTable J ℓ fun j u => rowEntry A j u + rowEntry B j u

/-- Entrywise negation of a jet array, normalized to shape `J × ℓ`. -/
def negJet (J ℓ : ℕ) (A : List (List ℤ)) : List (List ℤ) :=
  tabulateTable J ℓ fun j u => -rowEntry A j u

/-- Entrywise subtraction of two jet arrays, normalized to shape `J × ℓ`. -/
def subJet (J ℓ : ℕ) (A B : List (List ℤ)) : List (List ℤ) :=
  tabulateTable J ℓ fun j u => rowEntry A j u - rowEntry B j u

/-- Entrywise integer scalar multiplication of a jet array, normalized to shape `J × ℓ`. -/
def smulJet (J ℓ : ℕ) (c : ℤ) (A : List (List ℤ)) : List (List ℤ) :=
  tabulateTable J ℓ fun j u => c * rowEntry A j u

/-- Multiplication by `z` modulo `z^J`, shifting row index up by `1` and dropping row `J - 1`. -/
def shiftZJet (J ℓ : ℕ) (A : List (List ℤ)) : List (List ℤ) :=
  tabulateTable J ℓ fun j u => if j = 0 then 0 else rowEntry A (j - 1) u

/-- Multiplication by `V` modulo `V^ℓ`, shifting column index up by `1` and dropping `ℓ - 1`. -/
def shiftVJet (J ℓ : ℕ) (A : List (List ℤ)) : List (List ℤ) :=
  tabulateTable J ℓ fun j u => if u = 0 then 0 else rowEntry A j (u - 1)

/-- Coefficient `(j, u)` of the 2D Cauchy product of `A` and `B`, computed over `List.range`. -/
def convEntry (A B : List (List ℤ)) (j u : ℕ) : ℤ :=
  ((List.range (j + 1)).map fun j₁ =>
    ((List.range (u + 1)).map fun u₁ =>
      rowEntry A j₁ u₁ * rowEntry B (j - j₁) (u - u₁)).sum).sum

/-- Truncated 2D convolution in `ℤ[V]/(V^ℓ)[z]/(z^J)` using `O(J^2 ℓ^2)` integer operations. -/
def convJet (J ℓ : ℕ) (A B : List (List ℤ)) : List (List ℤ) :=
  tabulateTable J ℓ (convEntry A B)

/-! ### Output shape and exact coefficient semantics -/

theorem isTableShape_zeroJet (J ℓ : ℕ) : IsTableShape J ℓ (zeroJet J ℓ) :=
  isTableShape_tabulateTable J ℓ _

theorem isTableShape_constJet (J ℓ : ℕ) (c : ℤ) : IsTableShape J ℓ (constJet J ℓ c) :=
  isTableShape_tabulateTable J ℓ _

theorem isTableShape_zJet (J ℓ : ℕ) : IsTableShape J ℓ (zJet J ℓ) :=
  isTableShape_tabulateTable J ℓ _

theorem isTableShape_vJet (J ℓ : ℕ) : IsTableShape J ℓ (vJet J ℓ) :=
  isTableShape_tabulateTable J ℓ _

theorem isTableShape_addJet (J ℓ : ℕ) (A B : List (List ℤ)) : IsTableShape J ℓ (addJet J ℓ A B) :=
  isTableShape_tabulateTable J ℓ _

theorem isTableShape_negJet (J ℓ : ℕ) (A : List (List ℤ)) : IsTableShape J ℓ (negJet J ℓ A) :=
  isTableShape_tabulateTable J ℓ _

theorem isTableShape_subJet (J ℓ : ℕ) (A B : List (List ℤ)) : IsTableShape J ℓ (subJet J ℓ A B) :=
  isTableShape_tabulateTable J ℓ _

theorem isTableShape_smulJet (J ℓ : ℕ) (c : ℤ) (A : List (List ℤ)) :
    IsTableShape J ℓ (smulJet J ℓ c A) :=
  isTableShape_tabulateTable J ℓ _

theorem isTableShape_shiftZJet (J ℓ : ℕ) (A : List (List ℤ)) : IsTableShape J ℓ (shiftZJet J ℓ A) :=
  isTableShape_tabulateTable J ℓ _

theorem isTableShape_shiftVJet (J ℓ : ℕ) (A : List (List ℤ)) : IsTableShape J ℓ (shiftVJet J ℓ A) :=
  isTableShape_tabulateTable J ℓ _

theorem isTableShape_convJet (J ℓ : ℕ) (A B : List (List ℤ)) : IsTableShape J ℓ (convJet J ℓ A B) :=
  isTableShape_tabulateTable J ℓ _

lemma convEntry_eq_sum (A B : List (List ℤ)) (j u : ℕ) :
    convEntry A B j u =
      ∑ j₁ ∈ Finset.range (j + 1), ∑ u₁ ∈ Finset.range (u + 1),
        rowEntry A j₁ u₁ * rowEntry B (j - j₁) (u - u₁) := by
  simp only [convEntry, List.sum_map_range, Finset.sum_range]

@[simp]
theorem rowEntry_zeroJet (J ℓ j u : ℕ) : rowEntry (zeroJet J ℓ) j u = 0 := by
  simp [zeroJet, rowEntry_tabulateTable]

theorem rowEntry_constJet {J ℓ : ℕ} (c : ℤ) {j u : ℕ} (hj : j < J) (hu : u < ℓ) :
    rowEntry (constJet J ℓ c) j u = if j = 0 ∧ u = 0 then c else 0 :=
  rowEntry_tabulateTable_of_lt _ hj hu

theorem rowEntry_zJet {J ℓ : ℕ} {j u : ℕ} (hj : j < J) (hu : u < ℓ) :
    rowEntry (zJet J ℓ) j u = if j = 1 ∧ u = 0 then 1 else 0 :=
  rowEntry_tabulateTable_of_lt _ hj hu

theorem rowEntry_vJet {J ℓ : ℕ} {j u : ℕ} (hj : j < J) (hu : u < ℓ) :
    rowEntry (vJet J ℓ) j u = if j = 0 ∧ u = 1 then 1 else 0 :=
  rowEntry_tabulateTable_of_lt _ hj hu

theorem rowEntry_addJet {J ℓ : ℕ} (A B : List (List ℤ)) {j u : ℕ} (hj : j < J) (hu : u < ℓ) :
    rowEntry (addJet J ℓ A B) j u = rowEntry A j u + rowEntry B j u :=
  rowEntry_tabulateTable_of_lt _ hj hu

theorem rowEntry_negJet {J ℓ : ℕ} (A : List (List ℤ)) {j u : ℕ} (hj : j < J) (hu : u < ℓ) :
    rowEntry (negJet J ℓ A) j u = -rowEntry A j u :=
  rowEntry_tabulateTable_of_lt _ hj hu

theorem rowEntry_subJet {J ℓ : ℕ} (A B : List (List ℤ)) {j u : ℕ} (hj : j < J) (hu : u < ℓ) :
    rowEntry (subJet J ℓ A B) j u = rowEntry A j u - rowEntry B j u :=
  rowEntry_tabulateTable_of_lt _ hj hu

theorem rowEntry_smulJet {J ℓ : ℕ} (c : ℤ) (A : List (List ℤ)) {j u : ℕ} (hj : j < J) (hu : u < ℓ) :
    rowEntry (smulJet J ℓ c A) j u = c * rowEntry A j u :=
  rowEntry_tabulateTable_of_lt _ hj hu

theorem rowEntry_shiftZJet {J ℓ : ℕ} (A : List (List ℤ)) {j u : ℕ} (hj : j < J) (hu : u < ℓ) :
    rowEntry (shiftZJet J ℓ A) j u = if j = 0 then 0 else rowEntry A (j - 1) u :=
  rowEntry_tabulateTable_of_lt _ hj hu

theorem rowEntry_shiftVJet {J ℓ : ℕ} (A : List (List ℤ)) {j u : ℕ} (hj : j < J) (hu : u < ℓ) :
    rowEntry (shiftVJet J ℓ A) j u = if u = 0 then 0 else rowEntry A j (u - 1) :=
  rowEntry_tabulateTable_of_lt _ hj hu

theorem rowEntry_convJet {J ℓ : ℕ} (A B : List (List ℤ)) {j u : ℕ} (hj : j < J) (hu : u < ℓ) :
    rowEntry (convJet J ℓ A B) j u =
      ∑ j₁ ∈ Finset.range (j + 1), ∑ u₁ ∈ Finset.range (u + 1),
        rowEntry A j₁ u₁ * rowEntry B (j - j₁) (u - u₁) := by
  rw [convJet, rowEntry_tabulateTable_of_lt _ hj hu, convEntry_eq_sum]

/-! ### Algebraic identities on `(J, ℓ)`-shaped jet arrays -/

theorem addJet_comm (J ℓ : ℕ) (A B : List (List ℤ)) :
    addJet J ℓ A B = addJet J ℓ B A :=
  eq_of_isTableShape_of_rowEntry_eq (isTableShape_addJet J ℓ A B) (isTableShape_addJet J ℓ B A)
    fun j hj u hu => by rw [rowEntry_addJet A B hj hu, rowEntry_addJet B A hj hu, Int.add_comm]

theorem addJet_assoc (J ℓ : ℕ) (A B C : List (List ℤ)) :
    addJet J ℓ (addJet J ℓ A B) C = addJet J ℓ A (addJet J ℓ B C) :=
  eq_of_isTableShape_of_rowEntry_eq (isTableShape_addJet J ℓ _ _) (isTableShape_addJet J ℓ _ _)
    fun j hj u hu => by
      rw [rowEntry_addJet _ _ hj hu, rowEntry_addJet _ _ hj hu,
        rowEntry_addJet _ _ hj hu, rowEntry_addJet _ _ hj hu, Int.add_assoc]

theorem zeroJet_addJet {J ℓ : ℕ} {A : List (List ℤ)} (hA : IsTableShape J ℓ A) :
    addJet J ℓ (zeroJet J ℓ) A = A :=
  eq_of_isTableShape_of_rowEntry_eq (isTableShape_addJet J ℓ _ _) hA fun j hj u hu => by
    rw [rowEntry_addJet _ _ hj hu, rowEntry_zeroJet, zero_add]

theorem addJet_zeroJet {J ℓ : ℕ} {A : List (List ℤ)} (hA : IsTableShape J ℓ A) :
    addJet J ℓ A (zeroJet J ℓ) = A := by
  rw [addJet_comm, zeroJet_addJet hA]

theorem negJet_addJet (J ℓ : ℕ) (A : List (List ℤ)) :
    addJet J ℓ (negJet J ℓ A) A = zeroJet J ℓ :=
  eq_of_isTableShape_of_rowEntry_eq (isTableShape_addJet J ℓ _ _) (isTableShape_zeroJet J ℓ)
    fun j hj u hu => by
      rw [rowEntry_addJet _ _ hj hu, rowEntry_negJet A hj hu, rowEntry_zeroJet, neg_add_cancel]

theorem addJet_negJet (J ℓ : ℕ) (A : List (List ℤ)) :
    addJet J ℓ A (negJet J ℓ A) = zeroJet J ℓ := by
  rw [addJet_comm, negJet_addJet]

theorem subJet_eq_addJet_negJet (J ℓ : ℕ) (A B : List (List ℤ)) :
    subJet J ℓ A B = addJet J ℓ A (negJet J ℓ B) :=
  eq_of_isTableShape_of_rowEntry_eq (isTableShape_subJet J ℓ A B) (isTableShape_addJet J ℓ _ _)
    fun j hj u hu => by
      rw [rowEntry_subJet A B hj hu, rowEntry_addJet _ _ hj hu, rowEntry_negJet B hj hu,
        sub_eq_add_neg]

theorem smulJet_addJet (J ℓ : ℕ) (c : ℤ) (A B : List (List ℤ)) :
    smulJet J ℓ c (addJet J ℓ A B) = addJet J ℓ (smulJet J ℓ c A) (smulJet J ℓ c B) :=
  eq_of_isTableShape_of_rowEntry_eq (isTableShape_smulJet J ℓ c _) (isTableShape_addJet J ℓ _ _)
    fun j hj u hu => by
      rw [rowEntry_smulJet c _ hj hu, rowEntry_addJet A B hj hu, rowEntry_addJet _ _ hj hu,
        rowEntry_smulJet c A hj hu, rowEntry_smulJet c B hj hu, mul_add]

theorem one_smulJet {J ℓ : ℕ} {A : List (List ℤ)} (hA : IsTableShape J ℓ A) :
    smulJet J ℓ 1 A = A :=
  eq_of_isTableShape_of_rowEntry_eq (isTableShape_smulJet J ℓ 1 A) hA fun j hj u hu => by
    rw [rowEntry_smulJet 1 A hj hu, one_mul]

/-- Commutativity of truncated 2D convolution. -/
theorem convJet_comm (J ℓ : ℕ) (A B : List (List ℤ)) :
    convJet J ℓ A B = convJet J ℓ B A := by
  refine eq_of_isTableShape_of_rowEntry_eq (isTableShape_convJet J ℓ A B)
    (isTableShape_convJet J ℓ B A) fun j hj u hu => ?_
  rw [rowEntry_convJet A B hj hu, rowEntry_convJet B A hj hu, ← Finset.sum_range_reflect _ (j + 1)]
  refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
  simp only [Finset.mem_range] at hj₁
  rw [← Finset.sum_range_reflect _ (u + 1)]
  refine Finset.sum_congr rfl fun u₁ hu₁ => ?_
  simp only [Finset.mem_range] at hu₁
  simp only [Nat.add_sub_cancel]
  have hj' : j - (j - j₁) = j₁ := by omega
  have hu' : u - (u - u₁) = u₁ := by omega
  rw [hj', hu', Int.mul_comm]

private lemma sum_range_triangle (n : ℕ) (g : ℕ → ℕ → ℕ → ℤ) :
    (∑ ab ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (ab + 1), g a (ab - a) (n - ab)) =
      ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n - a + 1), g a b (n - a - b) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => ⟨p.2, p.1 - p.2⟩) (fun q => ⟨q.1 + q.2, q.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro ⟨ab, a⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
    omega
  · intro ⟨a, b⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_range] at hq ⊢
    omega
  · intro ⟨ab, a⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    exact Sigma.ext (by dsimp only; omega) (heq_of_eq rfl)
  · intro ⟨a, b⟩ _
    exact Sigma.ext rfl (heq_of_eq (by dsimp only; omega))
  · intro ⟨ab, a⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    dsimp only
    exact congrArg (g a (ab - a)) (by omega)

/-- Associativity of truncated 2D convolution. -/
theorem convJet_assoc (J ℓ : ℕ) (A B C : List (List ℤ)) :
    convJet J ℓ (convJet J ℓ A B) C = convJet J ℓ A (convJet J ℓ B C) := by
  refine eq_of_isTableShape_of_rowEntry_eq (isTableShape_convJet J ℓ _ C)
    (isTableShape_convJet J ℓ A _) fun j hj u hu => ?_
  rw [rowEntry_convJet _ C hj hu, rowEntry_convJet A _ hj hu]
  have hL :
      (∑ j₁₂ ∈ Finset.range (j + 1), ∑ u₁₂ ∈ Finset.range (u + 1),
          rowEntry (convJet J ℓ A B) j₁₂ u₁₂ * rowEntry C (j - j₁₂) (u - u₁₂)) =
        ∑ j₁₂ ∈ Finset.range (j + 1), ∑ j₁ ∈ Finset.range (j₁₂ + 1),
          ∑ u₁₂ ∈ Finset.range (u + 1), ∑ u₁ ∈ Finset.range (u₁₂ + 1),
            rowEntry A j₁ u₁ * rowEntry B (j₁₂ - j₁) (u₁₂ - u₁) *
              rowEntry C (j - j₁₂) (u - u₁₂) := by
    refine Finset.sum_congr rfl fun j₁₂ hj₁₂ => ?_
    simp only [Finset.mem_range] at hj₁₂
    have hj₁₂_lt : j₁₂ < J := by omega
    calc
      (∑ u₁₂ ∈ Finset.range (u + 1),
          rowEntry (convJet J ℓ A B) j₁₂ u₁₂ * rowEntry C (j - j₁₂) (u - u₁₂))
          = ∑ u₁₂ ∈ Finset.range (u + 1), ∑ j₁ ∈ Finset.range (j₁₂ + 1),
              ∑ u₁ ∈ Finset.range (u₁₂ + 1),
                rowEntry A j₁ u₁ * rowEntry B (j₁₂ - j₁) (u₁₂ - u₁) *
                  rowEntry C (j - j₁₂) (u - u₁₂) := by
            refine Finset.sum_congr rfl fun u₁₂ hu₁₂ => ?_
            simp only [Finset.mem_range] at hu₁₂
            rw [rowEntry_convJet A B hj₁₂_lt (by omega), Finset.sum_mul]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_mul ..
      _ = _ := Finset.sum_comm
  have hR :
      (∑ j₁ ∈ Finset.range (j + 1), ∑ u₁ ∈ Finset.range (u + 1),
          rowEntry A j₁ u₁ * rowEntry (convJet J ℓ B C) (j - j₁) (u - u₁)) =
        ∑ j₁ ∈ Finset.range (j + 1), ∑ j₂ ∈ Finset.range (j - j₁ + 1),
          ∑ u₁ ∈ Finset.range (u + 1), ∑ u₂ ∈ Finset.range (u - u₁ + 1),
            rowEntry A j₁ u₁ * rowEntry B j₂ u₂ * rowEntry C (j - j₁ - j₂) (u - u₁ - u₂) := by
    refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
    simp only [Finset.mem_range] at hj₁
    have hj_sub : j - j₁ < J := by omega
    calc
      (∑ u₁ ∈ Finset.range (u + 1),
          rowEntry A j₁ u₁ * rowEntry (convJet J ℓ B C) (j - j₁) (u - u₁))
          = ∑ u₁ ∈ Finset.range (u + 1), ∑ j₂ ∈ Finset.range (j - j₁ + 1),
              ∑ u₂ ∈ Finset.range (u - u₁ + 1),
                rowEntry A j₁ u₁ * rowEntry B j₂ u₂ * rowEntry C (j - j₁ - j₂) (u - u₁ - u₂) := by
            refine Finset.sum_congr rfl fun u₁ hu₁ => ?_
            simp only [Finset.mem_range] at hu₁
            rw [rowEntry_convJet B C hj_sub (by omega), Finset.mul_sum]
            refine Finset.sum_congr rfl fun j₂ _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun u₂ _ => (mul_assoc _ _ _).symm
      _ = _ := Finset.sum_comm
  rw [hL, hR, sum_range_triangle j fun j₁ j₂ j₃ =>
    ∑ u₁₂ ∈ Finset.range (u + 1), ∑ u₁ ∈ Finset.range (u₁₂ + 1),
      rowEntry A j₁ u₁ * rowEntry B j₂ (u₁₂ - u₁) * rowEntry C j₃ (u - u₁₂)]
  refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => ?_
  exact sum_range_triangle u fun u₁ u₂ u₃ =>
    rowEntry A j₁ u₁ * rowEntry B j₂ u₂ * rowEntry C (j - j₁ - j₂) u₃

/-- Left distributivity of truncated 2D convolution over addition. -/
theorem convJet_addJet (J ℓ : ℕ) (A B C : List (List ℤ)) :
    convJet J ℓ A (addJet J ℓ B C) = addJet J ℓ (convJet J ℓ A B) (convJet J ℓ A C) := by
  refine eq_of_isTableShape_of_rowEntry_eq (isTableShape_convJet J ℓ A _)
    (isTableShape_addJet J ℓ _ _) fun j hj u hu => ?_
  rw [rowEntry_convJet A _ hj hu, rowEntry_addJet _ _ hj hu, rowEntry_convJet A B hj hu,
    rowEntry_convJet A C hj hu, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
  simp only [Finset.mem_range] at hj₁
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u₁ hu₁ => ?_
  simp only [Finset.mem_range] at hu₁
  rw [rowEntry_addJet B C (by omega) (by omega), mul_add]

/-- Right distributivity of truncated 2D convolution over addition. -/
theorem addJet_convJet (J ℓ : ℕ) (A B C : List (List ℤ)) :
    convJet J ℓ (addJet J ℓ A B) C = addJet J ℓ (convJet J ℓ A C) (convJet J ℓ B C) := by
  rw [convJet_comm, convJet_addJet, convJet_comm J ℓ C A, convJet_comm J ℓ C B]

theorem zeroJet_convJet (J ℓ : ℕ) (A : List (List ℤ)) :
    convJet J ℓ (zeroJet J ℓ) A = zeroJet J ℓ :=
  eq_of_isTableShape_of_rowEntry_eq (isTableShape_convJet J ℓ _ A) (isTableShape_zeroJet J ℓ)
    fun j hj u hu => by simp [rowEntry_convJet _ A hj hu]

theorem convJet_zeroJet (J ℓ : ℕ) (A : List (List ℤ)) :
    convJet J ℓ A (zeroJet J ℓ) = zeroJet J ℓ := by
  rw [convJet_comm, zeroJet_convJet]

theorem constJet_convJet (J ℓ : ℕ) (c : ℤ) (A : List (List ℤ)) :
    convJet J ℓ (constJet J ℓ c) A = smulJet J ℓ c A := by
  refine eq_of_isTableShape_of_rowEntry_eq (isTableShape_convJet J ℓ _ A)
    (isTableShape_smulJet J ℓ c A) fun j hj u hu => ?_
  rw [rowEntry_convJet _ A hj hu, rowEntry_smulJet c A hj hu]
  trans ∑ j₁ ∈ Finset.range (j + 1), if j₁ = 0 then c * rowEntry A j u else 0
  · refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
    simp only [Finset.mem_range] at hj₁
    trans ∑ u₁ ∈ Finset.range (u + 1),
      if u₁ = 0 then (if j₁ = 0 then c * rowEntry A j u else 0) else 0
    · refine Finset.sum_congr rfl fun u₁ hu₁ => ?_
      simp only [Finset.mem_range] at hu₁
      rw [rowEntry_constJet c (by omega) (by omega)]
      by_cases hj0 : j₁ = 0 <;> by_cases hu0 : u₁ = 0 <;> simp [hj0, hu0]
    · rw [Finset.sum_ite_eq' (Finset.range (u + 1)) 0,
        ite_eq_left (Finset.mem_range.mpr (Nat.zero_lt_succ u))]
  · rw [Finset.sum_ite_eq' (Finset.range (j + 1)) 0,
      ite_eq_left (Finset.mem_range.mpr (Nat.zero_lt_succ j))]

theorem convJet_constJet (J ℓ : ℕ) (A : List (List ℤ)) (c : ℤ) :
    convJet J ℓ A (constJet J ℓ c) = smulJet J ℓ c A := by
  rw [convJet_comm, constJet_convJet]

theorem constJet_one_convJet {J ℓ : ℕ} {A : List (List ℤ)} (hA : IsTableShape J ℓ A) :
    convJet J ℓ (constJet J ℓ 1) A = A := by
  rw [constJet_convJet, one_smulJet hA]

theorem convJet_constJet_one {J ℓ : ℕ} {A : List (List ℤ)} (hA : IsTableShape J ℓ A) :
    convJet J ℓ A (constJet J ℓ 1) = A := by
  rw [convJet_constJet, one_smulJet hA]

theorem smulJet_convJet (J ℓ : ℕ) (c : ℤ) (A B : List (List ℤ)) :
    convJet J ℓ (smulJet J ℓ c A) B = smulJet J ℓ c (convJet J ℓ A B) := by
  rw [← constJet_convJet, convJet_assoc, constJet_convJet]

theorem convJet_smulJet (J ℓ : ℕ) (c : ℤ) (A B : List (List ℤ)) :
    convJet J ℓ A (smulJet J ℓ c B) = smulJet J ℓ c (convJet J ℓ A B) := by
  rw [convJet_comm, smulJet_convJet, convJet_comm]

/-- `shiftZJet` agrees with multiplying by the generator `zJet` under `convJet`. -/
theorem shiftZJet_eq_convJet (J ℓ : ℕ) (A : List (List ℤ)) :
    shiftZJet J ℓ A = convJet J ℓ (zJet J ℓ) A := by
  refine eq_of_isTableShape_of_rowEntry_eq (isTableShape_shiftZJet J ℓ A)
    (isTableShape_convJet J ℓ _ A) fun j hj u hu => ?_
  rw [rowEntry_shiftZJet A hj hu, rowEntry_convJet _ A hj hu]
  symm
  trans ∑ j₁ ∈ Finset.range (j + 1), if j₁ = 1 then rowEntry A (j - 1) u else 0
  · refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
    simp only [Finset.mem_range] at hj₁
    trans ∑ u₁ ∈ Finset.range (u + 1),
      if u₁ = 0 then (if j₁ = 1 then rowEntry A (j - 1) u else 0) else 0
    · refine Finset.sum_congr rfl fun u₁ hu₁ => ?_
      simp only [Finset.mem_range] at hu₁
      rw [rowEntry_zJet (by omega) (by omega)]
      by_cases hj1 : j₁ = 1 <;> by_cases hu0 : u₁ = 0 <;> simp [hj1, hu0]
    · rw [Finset.sum_ite_eq' (Finset.range (u + 1)) 0,
        ite_eq_left (Finset.mem_range.mpr (Nat.zero_lt_succ u))]
  · rw [Finset.sum_ite_eq' (Finset.range (j + 1)) 1]
    by_cases hj0 : j = 0
    · subst hj0; simp
    · rw [ite_eq_right hj0, ite_eq_left (by simp only [Finset.mem_range]; omega)]

/-- `shiftVJet` agrees with multiplying by the generator `vJet` under `convJet`. -/
theorem shiftVJet_eq_convJet (J ℓ : ℕ) (A : List (List ℤ)) :
    shiftVJet J ℓ A = convJet J ℓ (vJet J ℓ) A := by
  refine eq_of_isTableShape_of_rowEntry_eq (isTableShape_shiftVJet J ℓ A)
    (isTableShape_convJet J ℓ _ A) fun j hj u hu => ?_
  rw [rowEntry_shiftVJet A hj hu, rowEntry_convJet _ A hj hu]
  symm
  trans ∑ j₁ ∈ Finset.range (j + 1),
    if j₁ = 0 then (if u = 0 then 0 else rowEntry A j (u - 1)) else 0
  · refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
    simp only [Finset.mem_range] at hj₁
    trans ∑ u₁ ∈ Finset.range (u + 1),
      if u₁ = 1 then (if j₁ = 0 then rowEntry A j (u - 1) else 0) else 0
    · refine Finset.sum_congr rfl fun u₁ hu₁ => ?_
      simp only [Finset.mem_range] at hu₁
      rw [rowEntry_vJet (by omega) (by omega)]
      by_cases hj0 : j₁ = 0 <;> by_cases hu1 : u₁ = 1 <;> simp [hj0, hu1]
    · rw [Finset.sum_ite_eq' (Finset.range (u + 1)) 1]
      by_cases hu0 : u = 0
      · subst hu0; simp
      · rw [ite_eq_left (by simp only [Finset.mem_range]; omega)]
        by_cases hj0 : j₁ = 0 <;> simp [hj0, hu0]
  · rw [Finset.sum_ite_eq' (Finset.range (j + 1)) 0,
      ite_eq_left (Finset.mem_range.mpr (Nat.zero_lt_succ j))]

/-! ### `ℓ₁` coefficient norm and binary bit-length bounds -/

/-- The `ℓ₁` coefficient norm `∑ |c|` of a list of integer rows. -/
def jetL1Norm (A : List (List ℤ)) : ℕ :=
  (A.map fun row => (row.map Int.natAbs).sum).sum

lemma jetL1Norm_tabulateTable (J ℓ : ℕ) (g : ℕ → ℕ → ℤ) :
    jetL1Norm (tabulateTable J ℓ g) =
      ∑ j ∈ Finset.range J, ∑ u ∈ Finset.range ℓ, (g j u).natAbs := by
  simp only [jetL1Norm, tabulateTable, List.map_map, Function.comp_def, List.sum_map_range,
    Finset.sum_range]

private lemma sum_getD_natAbs_le (ℓ : ℕ) (row : List ℤ) :
    (∑ u ∈ Finset.range ℓ, (row.getD u 0).natAbs) ≤ (row.map Int.natAbs).sum := by
  induction row generalizing ℓ with
  | nil => simp
  | cons x xs ih =>
    cases ℓ with
    | zero => simp
    | succ ℓ' =>
      rw [Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.sum_cons]
      have h := ih ℓ'
      omega

/-- Truncating any list of rows to `(J, ℓ)` cannot increase its `ℓ₁` coefficient norm. -/
lemma sum_rowEntry_natAbs_le_jetL1Norm (J ℓ : ℕ) (A : List (List ℤ)) :
    (∑ j ∈ Finset.range J, ∑ u ∈ Finset.range ℓ, (rowEntry A j u).natAbs) ≤ jetL1Norm A := by
  induction A generalizing J with
  | nil => simp [rowEntry, jetL1Norm]
  | cons row rows ih =>
    cases J with
    | zero => simp
    | succ J' =>
      rw [Finset.sum_range_succ']
      simp only [rowEntry, List.getD_cons_zero, List.getD_cons_succ, jetL1Norm, List.map_cons,
        List.sum_cons]
      have hrow := sum_getD_natAbs_le ℓ row
      have hrows := ih J'
      simp only [rowEntry, jetL1Norm] at hrows
      omega

/-- On a `(J, ℓ)`-shaped jet array, `jetL1Norm` equals the sum of in-bounds `|rowEntry A j u|`. -/
lemma jetL1Norm_eq_sum_rowEntry {J ℓ : ℕ} {A : List (List ℤ)} (hA : IsTableShape J ℓ A) :
    jetL1Norm A = ∑ j ∈ Finset.range J, ∑ u ∈ Finset.range ℓ, (rowEntry A j u).natAbs := by
  conv_lhs => rw [← tabulateTable_rowEntry hA]
  exact jetL1Norm_tabulateTable J ℓ (rowEntry A)

@[simp]
theorem jetL1Norm_zeroJet (J ℓ : ℕ) : jetL1Norm (zeroJet J ℓ) = 0 := by
  simp [zeroJet, jetL1Norm_tabulateTable]

theorem jetL1Norm_constJet_le (J ℓ : ℕ) (c : ℤ) :
    jetL1Norm (constJet J ℓ c) ≤ c.natAbs := by
  rw [constJet, jetL1Norm_tabulateTable]
  cases J with
  | zero => simp
  | succ J' =>
    cases ℓ with
    | zero => simp
    | succ ℓ' =>
      rw [Finset.sum_range_succ']
      have htail :
          (∑ k ∈ Finset.range J', ∑ u ∈ Finset.range (ℓ' + 1),
              (if k + 1 = 0 ∧ u = 0 then c else 0).natAbs) = 0 := by simp
      rw [htail, zero_add, Finset.sum_range_succ']
      simp

theorem jetL1Norm_negJet_le (J ℓ : ℕ) (A : List (List ℤ)) :
    jetL1Norm (negJet J ℓ A) ≤ jetL1Norm A := by
  rw [negJet, jetL1Norm_tabulateTable]
  simp only [Int.natAbs_neg]
  exact sum_rowEntry_natAbs_le_jetL1Norm J ℓ A

/-- Triangle inequality for the `ℓ₁` coefficient norm under `addJet`. -/
theorem jetL1Norm_addJet_le (J ℓ : ℕ) (A B : List (List ℤ)) :
    jetL1Norm (addJet J ℓ A B) ≤ jetL1Norm A + jetL1Norm B := by
  rw [addJet, jetL1Norm_tabulateTable]
  calc
    (∑ j ∈ Finset.range J, ∑ u ∈ Finset.range ℓ, (rowEntry A j u + rowEntry B j u).natAbs)
        ≤ ∑ j ∈ Finset.range J, ∑ u ∈ Finset.range ℓ,
            ((rowEntry A j u).natAbs + (rowEntry B j u).natAbs) :=
          Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => Int.natAbs_add_le _ _
    _ = (∑ j ∈ Finset.range J, ∑ u ∈ Finset.range ℓ, (rowEntry A j u).natAbs) +
          (∑ j ∈ Finset.range J, ∑ u ∈ Finset.range ℓ, (rowEntry B j u).natAbs) := by
          simp only [Finset.sum_add_distrib]
    _ ≤ jetL1Norm A + jetL1Norm B :=
          Nat.add_le_add (sum_rowEntry_natAbs_le_jetL1Norm J ℓ A)
            (sum_rowEntry_natAbs_le_jetL1Norm J ℓ B)

theorem jetL1Norm_subJet_le (J ℓ : ℕ) (A B : List (List ℤ)) :
    jetL1Norm (subJet J ℓ A B) ≤ jetL1Norm A + jetL1Norm B := by
  rw [subJet_eq_addJet_negJet]
  exact (jetL1Norm_addJet_le J ℓ A _).trans
    (Nat.add_le_add_left (jetL1Norm_negJet_le J ℓ B) _)

theorem jetL1Norm_smulJet_le (J ℓ : ℕ) (c : ℤ) (A : List (List ℤ)) :
    jetL1Norm (smulJet J ℓ c A) ≤ c.natAbs * jetL1Norm A := by
  rw [smulJet, jetL1Norm_tabulateTable]
  simp only [Int.natAbs_mul, ← Finset.mul_sum]
  exact Nat.mul_le_mul_left c.natAbs (sum_rowEntry_natAbs_le_jetL1Norm J ℓ A)

theorem jetL1Norm_shiftZJet_le (J ℓ : ℕ) (A : List (List ℤ)) :
    jetL1Norm (shiftZJet J ℓ A) ≤ jetL1Norm A := by
  rw [shiftZJet, jetL1Norm_tabulateTable]
  cases J with
  | zero => simp
  | succ J' =>
    rw [Finset.sum_range_succ']
    simp only [↓reduceIte, Int.natAbs_zero, Finset.sum_const_zero, add_zero, Nat.succ_ne_zero,
      Nat.add_sub_cancel]
    exact sum_rowEntry_natAbs_le_jetL1Norm J' ℓ A

theorem jetL1Norm_shiftVJet_le (J ℓ : ℕ) (A : List (List ℤ)) :
    jetL1Norm (shiftVJet J ℓ A) ≤ jetL1Norm A := by
  rw [shiftVJet, jetL1Norm_tabulateTable]
  cases ℓ with
  | zero => simp
  | succ ℓ' =>
    have hrow (j : ℕ) :
        (∑ u ∈ Finset.range (ℓ' + 1), (if u = 0 then 0 else rowEntry A j (u - 1)).natAbs) =
          ∑ u ∈ Finset.range ℓ', (rowEntry A j u).natAbs := by
      rw [Finset.sum_range_succ']
      simp
    simp only [hrow]
    exact sum_rowEntry_natAbs_le_jetL1Norm J ℓ' A

private lemma sum_conv_nat_le_mul (N : ℕ) (a b : ℕ → ℕ) :
    (∑ j ∈ Finset.range N, ∑ j₁ ∈ Finset.range (j + 1), a j₁ * b (j - j₁)) ≤
      (∑ j₁ ∈ Finset.range N, a j₁) * (∑ j₂ ∈ Finset.range N, b j₂) := by
  rw [Finset.sum_sigma', Finset.sum_mul_sum, ← Finset.sum_product']
  let S := (Finset.range N).sigma fun j => Finset.range (j + 1)
  let φ : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun p => (p.2, p.1 - p.2)
  have hinj : Set.InjOn φ S := by
    intro ⟨j, j₁⟩ hp ⟨j', j₁'⟩ hq hφ
    simp only [S, Finset.mem_coe, Finset.mem_sigma, Finset.mem_range] at hp hq
    simp only [φ, Prod.mk.injEq] at hφ
    simp only [Sigma.mk.injEq, heq_eq_eq]
    omega
  have hsub : S.image φ ⊆ Finset.range N ×ˢ Finset.range N := by
    intro q hq
    obtain ⟨⟨j, j₁⟩, hp, rfl⟩ := Finset.mem_image.mp hq
    simp only [S, Finset.mem_sigma, Finset.mem_range] at hp
    simp only [φ, Finset.mem_product, Finset.mem_range]
    omega
  calc
    (∑ p ∈ S, a p.2 * b (p.1 - p.2))
        = ∑ q ∈ S.image φ, a q.1 * b q.2 :=
          (Finset.sum_image (f := fun q : ℕ × ℕ => a q.1 * b q.2) hinj).symm
    _ ≤ ∑ q ∈ Finset.range N ×ˢ Finset.range N, a q.1 * b q.2 :=
          Finset.sum_le_sum_of_subset hsub

/-- Submultiplicativity of the `ℓ₁` coefficient norm under truncated 2D convolution
([OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix B.2):
`‖A * B mod (z^J, V^ℓ)‖₁ ≤ ‖A‖₁ · ‖B‖₁`. -/
theorem jetL1Norm_convJet_le (J ℓ : ℕ) (A B : List (List ℤ)) :
    jetL1Norm (convJet J ℓ A B) ≤ jetL1Norm A * jetL1Norm B := by
  rw [convJet, jetL1Norm_tabulateTable]
  let rowNorm (M : List (List ℤ)) (j : ℕ) : ℕ :=
    ∑ u ∈ Finset.range ℓ, (rowEntry M j u).natAbs
  have hentry (j u : ℕ) :
      (convEntry A B j u).natAbs ≤
        ∑ j₁ ∈ Finset.range (j + 1), ∑ u₁ ∈ Finset.range (u + 1),
          (rowEntry A j₁ u₁).natAbs * (rowEntry B (j - j₁) (u - u₁)).natAbs := by
    rw [convEntry_eq_sum]
    refine (Int.natAbs_sum_le _ _).trans (Finset.sum_le_sum fun j₁ _ => ?_)
    refine (Int.natAbs_sum_le _ _).trans (Finset.sum_le_sum fun u₁ _ => ?_)
    rw [Int.natAbs_mul]
  calc
    (∑ j ∈ Finset.range J, ∑ u ∈ Finset.range ℓ, (convEntry A B j u).natAbs)
        ≤ ∑ j ∈ Finset.range J, ∑ u ∈ Finset.range ℓ,
            ∑ j₁ ∈ Finset.range (j + 1), ∑ u₁ ∈ Finset.range (u + 1),
              (rowEntry A j₁ u₁).natAbs * (rowEntry B (j - j₁) (u - u₁)).natAbs :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun u _ => hentry j u
    _ = ∑ j ∈ Finset.range J, ∑ j₁ ∈ Finset.range (j + 1),
          ∑ u ∈ Finset.range ℓ, ∑ u₁ ∈ Finset.range (u + 1),
            (rowEntry A j₁ u₁).natAbs * (rowEntry B (j - j₁) (u - u₁)).natAbs :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.range J, ∑ j₁ ∈ Finset.range (j + 1),
          rowNorm A j₁ * rowNorm B (j - j₁) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun j₁ _ =>
            sum_conv_nat_le_mul ℓ (fun u₁ => (rowEntry A j₁ u₁).natAbs)
              (fun u₂ => (rowEntry B (j - j₁) u₂).natAbs)
    _ ≤ (∑ j₁ ∈ Finset.range J, rowNorm A j₁) * (∑ j₂ ∈ Finset.range J, rowNorm B j₂) :=
          sum_conv_nat_le_mul J (rowNorm A) (rowNorm B)
    _ ≤ jetL1Norm A * jetL1Norm B :=
          Nat.mul_le_mul (sum_rowEntry_natAbs_le_jetL1Norm J ℓ A)
            (sum_rowEntry_natAbs_le_jetL1Norm J ℓ B)

/-- Every stored entry of `A` has magnitude bounded by `jetL1Norm A`. -/
lemma natAbs_le_jetL1Norm_of_mem {A : List (List ℤ)} {row : List ℤ} (hrow : row ∈ A)
    {z : ℤ} (hz : z ∈ row) : z.natAbs ≤ jetL1Norm A := by
  have hz' : z.natAbs ∈ row.map Int.natAbs := List.mem_map_of_mem hz
  have hrow' : (row.map Int.natAbs).sum ∈ A.map fun r => (r.map Int.natAbs).sum :=
    List.mem_map_of_mem hrow
  exact (List.single_le_sum (fun _ _ => Nat.zero_le _) _ hz').trans
    (List.single_le_sum (fun _ _ => Nat.zero_le _) _ hrow')

/-- Every coefficient `rowEntry A j u` has magnitude bounded by `jetL1Norm A`. -/
lemma natAbs_rowEntry_le_jetL1Norm (A : List (List ℤ)) (j u : ℕ) :
    (rowEntry A j u).natAbs ≤ jetL1Norm A :=
  rowEntry_rel_of_mem (Nat.zero_le _) (fun _ hrow _ hz => natAbs_le_jetL1Norm_of_mem hrow hz) j u

/-- Magnitude bound on every entry of `convJet` in terms of input `ℓ₁` norms. -/
theorem natAbs_rowEntry_convJet_le_norm (J ℓ : ℕ) (A B : List (List ℤ)) (j u : ℕ) :
    (rowEntry (convJet J ℓ A B) j u).natAbs ≤ jetL1Norm A * jetL1Norm B :=
  (natAbs_rowEntry_le_jetL1Norm _ j u).trans (jetL1Norm_convJet_le J ℓ A B)

/-- Encoded bit-length bound on every stored entry of `convJet` via input `ℓ₁` norms. -/
theorem length_encIntBin_mem_convJet_le_norm {J ℓ : ℕ} {A B : List (List ℤ)}
    {row : List ℤ} (hrow : row ∈ convJet J ℓ A B) {z : ℤ} (hz : z ∈ row) :
    (Turing.MultiTapeTM.encIntBin z).length ≤ (jetL1Norm A * jetL1Norm B).size + 1 := by
  rw [Turing.MultiTapeTM.length_encIntBin]
  exact Nat.add_le_add_right
    (Nat.size_le_size ((natAbs_le_jetL1Norm_of_mem hrow hz).trans (jetL1Norm_convJet_le J ℓ A B)))
    1

/-- Entrywise max-magnitude bound for `convJet`: if entries of `A` and `B` have magnitudes at most
`MA` and `MB`, then every coefficient of `convJet J ℓ A B` has magnitude at most
`J * ℓ * (MA * MB)`. -/
theorem natAbs_rowEntry_convJet_le {J ℓ MA MB : ℕ} {A B : List (List ℤ)}
    (hA : ∀ row ∈ A, ∀ z ∈ row, z.natAbs ≤ MA)
    (hB : ∀ row ∈ B, ∀ z ∈ row, z.natAbs ≤ MB) (j u : ℕ) :
    (rowEntry (convJet J ℓ A B) j u).natAbs ≤ J * ℓ * (MA * MB) := by
  have hA' := rowEntry_rel_of_mem (Nat.zero_le MA) hA
  have hB' := rowEntry_rel_of_mem (Nat.zero_le MB) hB
  rw [convJet, rowEntry_tabulateTable]
  split_ifs with hju
  · obtain ⟨hj, hu⟩ := hju
    rw [convEntry_eq_sum]
    calc
      (∑ j₁ ∈ Finset.range (j + 1), ∑ u₁ ∈ Finset.range (u + 1),
          rowEntry A j₁ u₁ * rowEntry B (j - j₁) (u - u₁)).natAbs
          ≤ ∑ j₁ ∈ Finset.range (j + 1), ∑ u₁ ∈ Finset.range (u + 1),
              (rowEntry A j₁ u₁ * rowEntry B (j - j₁) (u - u₁)).natAbs := by
            refine (Int.natAbs_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => ?_)
            exact Int.natAbs_sum_le _ _
      _ ≤ ∑ _j₁ ∈ Finset.range (j + 1), ∑ _u₁ ∈ Finset.range (u + 1), MA * MB := by
            refine Finset.sum_le_sum fun j₁ _ => Finset.sum_le_sum fun u₁ _ => ?_
            rw [Int.natAbs_mul]
            exact Nat.mul_le_mul (hA' j₁ u₁) (hB' (j - j₁) (u - u₁))
      _ = (j + 1) * (u + 1) * (MA * MB) := by
            simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_assoc]
      _ ≤ J * ℓ * (MA * MB) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul hj hu)
  · exact Nat.zero_le _

/-- Binary magnitude-size bound for `convJet`: if stored entries of `A` and `B` have binary
magnitude size at most `bA` and `bB`, then every coefficient of `convJet J ℓ A B` has binary
magnitude size at most `bA + bB + (J * ℓ).size`. -/
theorem size_natAbs_rowEntry_convJet_le {J ℓ bA bB : ℕ} {A B : List (List ℤ)}
    (hA : ∀ row ∈ A, ∀ z ∈ row, z.natAbs.size ≤ bA)
    (hB : ∀ row ∈ B, ∀ z ∈ row, z.natAbs.size ≤ bB) (j u : ℕ) :
    (rowEntry (convJet J ℓ A B) j u).natAbs.size ≤ bA + bB + (J * ℓ).size := by
  have hA' := rowEntry_rel_of_mem (by simp) hA
  have hB' := rowEntry_rel_of_mem (by simp) hB
  rw [convJet, rowEntry_tabulateTable]
  split_ifs with hju
  · obtain ⟨hj, hu⟩ := hju
    unfold convEntry
    rw [← Function.comp_def List.sum, ← List.map_map, ← List.sum_flatten,
      ← List.flatMap_def]
    let terms := (List.range (j + 1)).flatMap fun j₁ =>
      (List.range (u + 1)).map fun u₁ => rowEntry A j₁ u₁ * rowEntry B (j - j₁) (u - u₁)
    have hmem : ∀ z ∈ terms, z.natAbs.size ≤ bA + bB := by
      intro z hz
      obtain ⟨j₁, -, hz⟩ := List.mem_flatMap.mp hz
      obtain ⟨u₁, -, rfl⟩ := List.mem_map.mp hz
      exact (Int.size_natAbs_mul_le _ _).trans (Nat.add_le_add (hA' j₁ u₁) (hB' _ _))
    have hlen : terms.length = (j + 1) * (u + 1) := by
      simp [terms, List.length_flatMap]
    refine (Int.size_natAbs_sum_le hmem).trans ?_
    rw [hlen]
    exact Nat.add_le_add_left (Nat.size_le_size (Nat.mul_le_mul hj hu)) (bA + bB)
  · simp

/-- Encoded bit-length bound for every stored entry of `convJet`: if stored entries of `A` and `B`
have `encIntBin` length at most `bA + 1` and `bB + 1`, then every stored entry of
`convJet J ℓ A B` has `encIntBin` length at most `bA + bB + (J * ℓ).size + 1`. -/
theorem length_encIntBin_mem_convJet_le {J ℓ bA bB : ℕ} {A B : List (List ℤ)}
    (hA : ∀ row ∈ A, ∀ z ∈ row, (Turing.MultiTapeTM.encIntBin z).length ≤ bA + 1)
    (hB : ∀ row ∈ B, ∀ z ∈ row, (Turing.MultiTapeTM.encIntBin z).length ≤ bB + 1)
    {row : List ℤ} (hrow : row ∈ convJet J ℓ A B) {z : ℤ} (hz : z ∈ row) :
    (Turing.MultiTapeTM.encIntBin z).length ≤ bA + bB + (J * ℓ).size + 1 := by
  obtain ⟨j, u, rfl⟩ := exists_rowEntry_eq hrow hz
  rw [Turing.MultiTapeTM.length_encIntBin]
  refine Nat.add_le_add_right (size_natAbs_rowEntry_convJet_le ?_ ?_ j u) 1
  · intro r hr x hx
    have h := hA r hr x hx
    rw [Turing.MultiTapeTM.length_encIntBin] at h
    omega
  · intro r hr x hx
    have h := hB r hr x hx
    rw [Turing.MultiTapeTM.length_encIntBin] at h
    omega

/-! ### Plain polynomial-time certificates -/

section PolyTime

open Turing MultiTapeTM

variable {α : Type} {encIn : α ↪ List Bool}

/-- `zeroJet` is computable in polynomial time for unary `(J, ℓ)`. -/
@[fun_prop]
theorem computableInPolyTime_zeroJet {J ℓ : α → ℕ}
    (hJ : ComputableInPolyTime J encIn encUnary)
    (hℓ : ComputableInPolyTime ℓ encIn encUnary) :
    ComputableInPolyTime (fun x => zeroJet (J x) (ℓ x))
      encIn (encList (encList encIntBin)) :=
  computableInPolyTime_tabulateTable hJ hℓ (.const 0)

/-- `constJet` is computable in polynomial time for unary `(J, ℓ)` and binary `c`. -/
@[fun_prop]
theorem computableInPolyTime_constJet {J ℓ : α → ℕ} {c : α → ℤ}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hc : ComputableInPolyTime c encIn encIntBin) :
    ComputableInPolyTime (fun x => constJet (J x) (ℓ x) (c x))
      encIn (encList (encList encIntBin)) := by
  refine computableInPolyTime_tabulateTable hJ hℓ ?_
  rw [show (fun p : (α × ℕ) × ℕ => if p.1.2 = 0 ∧ p.2 = 0 then c p.1.1 else 0) =
      fun p => if (p.1.2 == 0 && p.2 == 0) then c p.1.1 else 0 by funext; simp]
  fun_prop

/-- `zJet` is computable in polynomial time for unary `(J, ℓ)`. -/
@[fun_prop]
theorem computableInPolyTime_zJet {J ℓ : α → ℕ}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary) :
    ComputableInPolyTime (fun x => zJet (J x) (ℓ x)) encIn (encList (encList encIntBin)) := by
  refine computableInPolyTime_tabulateTable hJ hℓ ?_
  rw [show (fun p : (α × ℕ) × ℕ => if p.1.2 = 1 ∧ p.2 = 0 then (1 : ℤ) else 0) =
      fun p => if (p.1.2 == 1 && p.2 == 0) then 1 else 0 by funext; simp]
  fun_prop

/-- `vJet` is computable in polynomial time for unary `(J, ℓ)`. -/
@[fun_prop]
theorem computableInPolyTime_vJet {J ℓ : α → ℕ}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary) :
    ComputableInPolyTime (fun x => vJet (J x) (ℓ x)) encIn (encList (encList encIntBin)) := by
  refine computableInPolyTime_tabulateTable hJ hℓ ?_
  rw [show (fun p : (α × ℕ) × ℕ => if p.1.2 = 0 ∧ p.2 = 1 then (1 : ℤ) else 0) =
      fun p => if (p.1.2 == 0 && p.2 == 1) then 1 else 0 by funext; simp]
  fun_prop

/-- `addJet` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_addJet {J ℓ : α → ℕ} {A B : α → List (List ℤ)}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hA : ComputableInPolyTime A encIn (encList (encList encIntBin)))
    (hB : ComputableInPolyTime B encIn (encList (encList encIntBin))) :
    ComputableInPolyTime (fun x => addJet (J x) (ℓ x) (A x) (B x))
      encIn (encList (encList encIntBin)) :=
  computableInPolyTime_tabulateTable hJ hℓ (by fun_prop)

/-- `negJet` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_negJet {J ℓ : α → ℕ} {A : α → List (List ℤ)}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hA : ComputableInPolyTime A encIn (encList (encList encIntBin))) :
    ComputableInPolyTime (fun x => negJet (J x) (ℓ x) (A x)) encIn (encList (encList encIntBin)) :=
  computableInPolyTime_tabulateTable hJ hℓ (by fun_prop)

/-- `subJet` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_subJet {J ℓ : α → ℕ} {A B : α → List (List ℤ)}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hA : ComputableInPolyTime A encIn (encList (encList encIntBin)))
    (hB : ComputableInPolyTime B encIn (encList (encList encIntBin))) :
    ComputableInPolyTime (fun x => subJet (J x) (ℓ x) (A x) (B x))
      encIn (encList (encList encIntBin)) :=
  computableInPolyTime_tabulateTable hJ hℓ (by fun_prop)

/-- `smulJet` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_smulJet {J ℓ : α → ℕ} {c : α → ℤ} {A : α → List (List ℤ)}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hc : ComputableInPolyTime c encIn encIntBin)
    (hA : ComputableInPolyTime A encIn (encList (encList encIntBin))) :
    ComputableInPolyTime (fun x => smulJet (J x) (ℓ x) (c x) (A x))
      encIn (encList (encList encIntBin)) :=
  computableInPolyTime_tabulateTable hJ hℓ (by fun_prop)

/-- `shiftZJet` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_shiftZJet {J ℓ : α → ℕ} {A : α → List (List ℤ)}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hA : ComputableInPolyTime A encIn (encList (encList encIntBin))) :
    ComputableInPolyTime (fun x => shiftZJet (J x) (ℓ x) (A x))
      encIn (encList (encList encIntBin)) := by
  refine computableInPolyTime_tabulateTable hJ hℓ ?_
  rw [show (fun p : (α × ℕ) × ℕ =>
        if p.1.2 = 0 then (0 : ℤ) else rowEntry (A p.1.1) (p.1.2 - 1) p.2) =
      fun p => if p.1.2 == 0 then 0 else rowEntry (A p.1.1) (p.1.2 - 1) p.2 by funext; simp]
  fun_prop

/-- `shiftVJet` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_shiftVJet {J ℓ : α → ℕ} {A : α → List (List ℤ)}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hA : ComputableInPolyTime A encIn (encList (encList encIntBin))) :
    ComputableInPolyTime (fun x => shiftVJet (J x) (ℓ x) (A x))
      encIn (encList (encList encIntBin)) := by
  refine computableInPolyTime_tabulateTable hJ hℓ ?_
  rw [show (fun p : (α × ℕ) × ℕ =>
        if p.2 = 0 then (0 : ℤ) else rowEntry (A p.1.1) p.1.2 (p.2 - 1)) =
      fun p => if p.2 == 0 then 0 else rowEntry (A p.1.1) p.1.2 (p.2 - 1) by funext; simp]
  fun_prop

/-- Computing a single truncated 2D convolution coefficient `convEntry` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_convEntry {A B : α → List (List ℤ)} {j u : α → ℕ}
    (hA : ComputableInPolyTime A encIn (encList (encList encIntBin)))
    (hB : ComputableInPolyTime B encIn (encList (encList encIntBin)))
    (hj : ComputableInPolyTime j encIn encUnary) (hu : ComputableInPolyTime u encIn encUnary) :
    ComputableInPolyTime (fun x => convEntry (A x) (B x) (j x) (u x)) encIn encIntBin := by
  unfold convEntry
  fun_prop

/-- Truncated 2D convolution `convJet` is computable in polynomial time for unary `(J, ℓ)` and
dense `List (List ℤ)` arrays over `encIntBin`. -/
@[fun_prop]
theorem computableInPolyTime_convJet {J ℓ : α → ℕ} {A B : α → List (List ℤ)}
    (hJ : ComputableInPolyTime J encIn encUnary) (hℓ : ComputableInPolyTime ℓ encIn encUnary)
    (hA : ComputableInPolyTime A encIn (encList (encList encIntBin)))
    (hB : ComputableInPolyTime B encIn (encList (encList encIntBin))) :
    ComputableInPolyTime (fun x => convJet (J x) (ℓ x) (A x) (B x))
      encIn (encList (encList encIntBin)) :=
  computableInPolyTime_tabulateTable hJ hℓ (by fun_prop)

/-- Direct polynomial-time certificate for `zeroJet`. -/
theorem zeroJet_polytime :
    ComputableInPolyTime (fun p : ℕ × ℕ => zeroJet p.1 p.2)
      (encPair encUnary encUnary) (encList (encList encIntBin)) := by fun_prop

/-- Direct polynomial-time certificate for `constJet`. -/
theorem constJet_polytime :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℤ => constJet p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encIntBin) (encList (encList encIntBin)) := by fun_prop

/-- Direct polynomial-time certificate for `addJet`. -/
theorem addJet_polytime :
    ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List (List ℤ)) × List (List ℤ) => addJet p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encUnary encUnary) (encList (encList encIntBin)))
        (encList (encList encIntBin))) (encList (encList encIntBin)) := by fun_prop

/-- Direct polynomial-time certificate for `negJet`. -/
theorem negJet_polytime :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × List (List ℤ) => negJet p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) (encList (encList encIntBin)))
      (encList (encList encIntBin)) := by fun_prop

/-- Direct polynomial-time certificate for `subJet`. -/
theorem subJet_polytime :
    ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List (List ℤ)) × List (List ℤ) => subJet p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encUnary encUnary) (encList (encList encIntBin)))
        (encList (encList encIntBin))) (encList (encList encIntBin)) := by fun_prop

/-- Direct polynomial-time certificate for `smulJet`. -/
theorem smulJet_polytime :
    ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℤ) × List (List ℤ) => smulJet p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encUnary encUnary) encIntBin) (encList (encList encIntBin)))
      (encList (encList encIntBin)) := by fun_prop

/-- Direct polynomial-time certificate for `shiftZJet`. -/
theorem shiftZJet_polytime :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × List (List ℤ) => shiftZJet p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) (encList (encList encIntBin)))
      (encList (encList encIntBin)) := by fun_prop

/-- Direct polynomial-time certificate for `shiftVJet`. -/
theorem shiftVJet_polytime :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × List (List ℤ) => shiftVJet p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) (encList (encList encIntBin)))
      (encList (encList encIntBin)) := by fun_prop

/-- Direct polynomial-time certificate for `convJet`. -/
theorem convJet_polytime :
    ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List (List ℤ)) × List (List ℤ) => convJet p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encUnary encUnary) (encList (encList encIntBin)))
        (encList (encList encIntBin))) (encList (encList encIntBin)) := by fun_prop

end PolyTime

end Cslib

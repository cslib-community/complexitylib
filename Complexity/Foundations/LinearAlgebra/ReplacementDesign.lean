/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.UniformSchedules
public import Complexity.Foundations.LinearAlgebra.VariableCopyPlacement
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Binomial measurement row counts and algebraic replacement design assembly (Lemmas 4.1 and 4.7)

This module assembles the algebraic replacement design construction of Section 4 of the manuscript
*The Exponential Time Hypothesis is False* (`[OpenAI2026ETH]`, printed pp. 28, 32–34) by
proving the exact binomial fiber count of Lemma 4.1 (p. 28, equation 4.8), the total
measurement row bound of equation (4.16) (p. 32), and a generalized algebraic Lemma 4.7 existence
theorem (pp. 33–34) establishing conditions (1)–(4) of Definition 3.1 (pp. 21–22) together with
the explicit cleared-denominator and `ℓ₁`-coefficient norm bounds of Lemma 4.6 underlying
condition (5) (formal `O(Q log Q + log D)` bit-length and native runtime-cost integration remain
separate):

1. **Slot-level antisymmetric and symmetric pair counts (Lemma 4.1 proof, p. 28):**
   - For each evaluation slot `s : Fin Q`, the `r × r` pair basis splits into
     `antisymPairs r = {p : Fin r × Fin r | p.2 < p.1}` of cardinality `r * (r - 1) / 2`
     (`card_antisymPairs`, eigenvalue `-1`) and `symPairs r = {p : Fin r × Fin r | ¬ p.2 < p.1}`
     of cardinality `r * (r + 1) / 2` (`card_symPairs`, eigenvalue `+1`).

2. **Exact binomial fiber count and Lemma 4.1 tail bound (p. 28, eq. 4.8):**
   - For every subset `S : Finset (Fin Q)`, the set of auxiliary basis labels `β : AuxLabel Q r`
     whose antisymmetric slot set `antisymSlots β = {s | β.2 s < β.1 s}` equals `S` has
     cardinality `(r * (r - 1) / 2) ^ #S * (r * (r + 1) / 2) ^ (Q - #S)`
     (`card_filter_antisymSlots_eq`).
   - Summing over `S ∈ powersetCard j univ` gives the exact fiber count
     `#({β : AuxLabel Q r | antisymCount β = j}) =
       Q.choose j * (r * (r - 1) / 2) ^ j * (r * (r + 1) / 2) ^ (Q - j)`
     (`card_filter_antisymCount_eq`) and the exact measurement row count
     `#(measurementIndices Q r A₀ R)` (`card_measurementIndices_eq`).
   - Over `ℚ`, for `0 < r`,
     `(#(measurementIndices Q r A₀ R) : ℚ) = (r ^ (2 * Q) : ℚ) * binomTailProb Q r A₀ R`
     (`card_measurementIndices_cast_eq`), so `binomTailProb Q r A₀ R ≤ ε` (eq. 4.8) implies
     `(#(measurementIndices Q r A₀ R) : ℚ) ≤ ε * (r ^ (2 * Q) : ℚ)`
     (`card_measurementIndices_le_of_binomTailProb_le`).

3. **Total group measurement row bound (Section 4.5, eq. 4.16, p. 32):**
   - When `h * r ^ (2 * Q) ≤ 2 * M`, `M ≤ b * n`, and `binomTailProb Q r A₀ R ≤ τ / (r * b)`,
     the total number of measurement rows across all `r` variable groups satisfies
     `((r * (h * #(measurementIndices Q r A₀ R)) : ℕ) : ℚ) ≤ 2 * τ * (n : ℚ)`
     (`card_allGroupMeasurementRows_le_two_mul_tau_mul_n`).

4. **Algebraic replacement design assembly (Definition 3.1, pp. 21–22, and Lemma 4.7, pp. 33–34):**
   - `ReplacementDesign` bundles the variable partition `varAssign`, factor group schedule
     `factorAssign`, copy count `h`, and injective copy placement `place` together with the
     group-size, measurement-row count, measurement `ℓ₁`-norm, degree, evaluation-at-zero, and
     kernel-invariance properties of Definition 3.1 (1)–(4), plus the explicit cleared-denominator
     identity and `ℓ₁` coefficient norm bound of Lemma 4.6 (`commonDenom Q R = (R - 1)! * Q!`)
     underlying Definition 3.1 (5) (formal `O(Q log Q + log D)` bit-length and native runtime-cost
     endpoints remain separate follow-up).
   - `exists_replacementDesign` proves an algebraic generalization of **Lemma 4.7** (printed
     pp. 33–34) by combining Lemma 4.1, Lemma 4.3, Lemma 4.5
     (`exists_balanced_schedules_of_scopes`), Section 4.5 (`fiberRankCopy`, `varReplacementRow`,
     `varMeasurementMatrix`), and Lemma 4.6:
     it requires only `0 ≤ τ`, `M ≤ b * n` (omitting `n ≤ M` and `τ ≤ 1 / 2`), and the weaker
     node-range condition `hI : ∀ a < R - 1, A₀ + a ≤ Q` (vacuous at `R = 1`) rather than full
     interval containment `I ⊆ [0, Q]`.

## Main definitions

* `Cslib.LinearAlgebra.antisymPairs`, `Cslib.LinearAlgebra.symPairs`: antisymmetric (`p.2 < p.1`)
  and symmetric/diagonal (`¬ p.2 < p.1`) pairs in `Fin r × Fin r`.
* `Cslib.LinearAlgebra.antisymSlots`: the subset of evaluation slots where `β.2 s < β.1 s`.
* `Cslib.LinearAlgebra.binomTailProb`: the binomial tail probability
  `Pr[W ∉ {A₀, ..., A₀ + R - 1}]` for `W ∼ Bin(Q, (r - 1) / (2 * r))` (eq. 4.8).
* `Cslib.LinearAlgebra.ReplacementDesign`: bundled Section 4 replacement design satisfying
  Definition 3.1 (1)–(4) and the explicit denominator/coefficient-norm bounds of Lemma 4.6.

## Main results

* `Cslib.LinearAlgebra.card_antisymPairs`, `Cslib.LinearAlgebra.card_symPairs`:
  `#(antisymPairs r) = r * (r - 1) / 2` and `#(symPairs r) = r * (r + 1) / 2`.
* `Cslib.LinearAlgebra.card_filter_antisymCount_eq`,
  `Cslib.LinearAlgebra.card_measurementIndices_eq`,
  `Cslib.LinearAlgebra.card_measurementIndices_cast_eq`,
  `Cslib.LinearAlgebra.card_measurementIndices_le_of_binomTailProb_le`:
  Lemma 4.1 exact binomial fiber count and equation (4.8) tail bound.
* `Cslib.LinearAlgebra.card_allGroupMeasurementRows_le_two_mul_tau_mul_n`:
  equation (4.16) total measurement row bound `≤ 2 * τ * n`.
* `Cslib.LinearAlgebra.exists_replacementDesign`: **Lemma 4.7** algebraic existence of a
  Section 4 replacement design.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (Definition 3.1,
  Lemmas 4.1, 4.3, 4.5, 4.6, and 4.7, pp. 21–22, 28, 30–34)
-/

@[expose] public noncomputable section

namespace Cslib.LinearAlgebra

open Finset Matrix Polynomial
open scoped BigOperators
open Cslib.BalancedSchedules

variable {Q r A₀ R n : ℕ}

/-! ### Part 1: Slot-level antisymmetric and symmetric pair counts (Lemma 4.1, p. 28) -/

/-- Ordered pairs `(a, d) : Fin r × Fin r` with `d < a`, indexing the antisymmetric pair-basis
functions `e_{a,d} - e_{d,a}` of eigenvalue `-1` under coordinate swap. -/
def antisymPairs (r : ℕ) : Finset (Fin r × Fin r) :=
  univ.filter fun p => p.2 < p.1

/-- Ordered pairs `(a, d) : Fin r × Fin r` with `¬ (d < a)`, indexing the diagonal and symmetric
pair-basis functions of eigenvalue `+1` under coordinate swap. -/
def symPairs (r : ℕ) : Finset (Fin r × Fin r) :=
  univ.filter fun p => ¬ p.2 < p.1

/-- Diagonal ordered pairs `(a, d) : Fin r × Fin r` with `a = d`. -/
def diagPairs (r : ℕ) : Finset (Fin r × Fin r) :=
  univ.filter fun p => p.1 = p.2

@[simp]
theorem mem_antisymPairs {p : Fin r × Fin r} : p ∈ antisymPairs r ↔ p.2 < p.1 := by
  simp only [antisymPairs, mem_filter, mem_univ, true_and]

@[simp]
theorem mem_symPairs {p : Fin r × Fin r} : p ∈ symPairs r ↔ ¬ p.2 < p.1 := by
  simp only [symPairs, mem_filter, mem_univ, true_and]

@[simp]
theorem mem_diagPairs {p : Fin r × Fin r} : p ∈ diagPairs r ↔ p.1 = p.2 := by
  simp only [diagPairs, mem_filter, mem_univ, true_and]

/-- `antisymPairs r` and `symPairs r` partition `Fin r × Fin r`. -/
theorem card_antisymPairs_add_card_symPairs (r : ℕ) :
    #(antisymPairs r) + #(symPairs r) = r * r := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin r × Fin r)))
    (fun p : Fin r × Fin r => p.2 < p.1)
  simpa only [antisymPairs, symPairs, card_univ, Fintype.card_prod, Fintype.card_fin] using h

/-- There are `r` diagonal pairs `(a, a)` in `Fin r × Fin r`. -/
theorem card_diagPairs (r : ℕ) : #(diagPairs r) = r := by
  have hEq : diagPairs r = (univ : Finset (Fin r)).map
      ⟨fun a => (a, a), fun a b h => (Prod.ext_iff.mp h).1⟩ := by
    ext ⟨a, d⟩
    rw [mem_diagPairs, mem_map]
    constructor
    · intro (h : a = d)
      subst h
      exact ⟨a, mem_univ a, rfl⟩
    · rintro ⟨b, _, hb⟩
      have h1 := (Prod.ext_iff.mp hb).1
      have h2 := (Prod.ext_iff.mp hb).2
      exact h1.symm.trans h2
  rw [hEq, card_map, card_univ, Fintype.card_fin]

/-- Swapping coordinates maps `antisymPairs r` (`p.2 < p.1`) bijectively onto `{p | p.1 < p.2}`. -/
theorem map_swap_antisymPairs (r : ℕ) :
    (antisymPairs r).map (Equiv.prodComm (Fin r) (Fin r)).toEmbedding =
      univ.filter (fun p : Fin r × Fin r => p.1 < p.2) := by
  ext ⟨a, d⟩
  rw [mem_map, mem_filter]
  simp only [mem_univ, true_and]
  constructor
  · rintro ⟨⟨a', d'⟩, hlt, hEq⟩
    rw [mem_antisymPairs] at hlt
    have h1 : d' = a := (Prod.ext_iff.mp hEq).1
    have h2 : a' = d := (Prod.ext_iff.mp hEq).2
    rwa [← h1, ← h2]
  · intro hlt
    exact ⟨(d, a), mem_antisymPairs.mpr hlt, rfl⟩

/-- Partitioning `Fin r × Fin r` into `p.2 < p.1`, `p.1 < p.2`, and `p.1 = p.2` gives
`2 * #(antisymPairs r) + r = r * r`. -/
theorem two_mul_card_antisymPairs_add (r : ℕ) :
    2 * #(antisymPairs r) + r = r * r := by
  simpa only [antisymPairs, pow_two] using two_mul_card_antisymPair_add_eq_sq r

/-- Twice the number of antisymmetric pairs in `Fin r × Fin r` is `r * (r - 1)`. -/
theorem two_mul_card_antisymPairs (r : ℕ) :
    2 * #(antisymPairs r) = r * (r - 1) := by
  have h := two_mul_card_antisymPairs_add r
  rcases r with _ | r
  · omega
  · simp only [Nat.add_sub_cancel]
    nlinarith

/-- Twice the number of symmetric/diagonal pairs in `Fin r × Fin r` is `r * (r + 1)`. -/
theorem two_mul_card_symPairs (r : ℕ) :
    2 * #(symPairs r) = r * (r + 1) := by
  have h₁ := two_mul_card_antisymPairs_add r
  have h₂ := card_antisymPairs_add_card_symPairs r
  nlinarith

/-- There are `r * (r - 1) / 2` antisymmetric pairs in `Fin r × Fin r` (Lemma 4.1, p. 28). -/
theorem card_antisymPairs (r : ℕ) :
    #(antisymPairs r) = r * (r - 1) / 2 := by
  rw [← two_mul_card_antisymPairs r, Nat.mul_div_right _ (by decide)]

/-- There are `r * (r + 1) / 2` symmetric and diagonal pairs in `Fin r × Fin r`
(Lemma 4.1, p. 28). -/
theorem card_symPairs (r : ℕ) :
    #(symPairs r) = r * (r + 1) / 2 := by
  rw [← two_mul_card_symPairs r, Nat.mul_div_right _ (by decide)]

/-! ### Part 2: Exact binomial fiber count and Lemma 4.1 tail bound (p. 28, eq. 4.8) -/

/-- The subset of evaluation slots `s : Fin Q` at which `β.2 s < β.1 s`. -/
def antisymSlots (β : AuxLabel Q r) : Finset (Fin Q) :=
  univ.filter fun s : Fin Q => β.2 s < β.1 s

/-- `antisymCount β` is the cardinality of `antisymSlots β`. -/
theorem antisymCount_eq_card_antisymSlots (β : AuxLabel Q r) :
    antisymCount β = #(antisymSlots β) :=
  rfl

/-- `antisymCount β` is at most `Q`. -/
theorem antisymCount_le (β : AuxLabel Q r) : antisymCount β ≤ Q := by
  have h := card_filter_le (univ : Finset (Fin Q)) (fun s : Fin Q => β.2 s < β.1 s)
  simpa only [antisymCount, card_univ, Fintype.card_fin] using h

/-- Equivalence between `AuxLabel Q r = (Fin Q → Fin r) × (Fin Q → Fin r)` and slotwise pairs
`Fin Q → Fin r × Fin r`. -/
def auxLabelEquivSlotPairs (Q r : ℕ) : AuxLabel Q r ≃ (Fin Q → Fin r × Fin r) where
  toFun β s := (β.1 s, β.2 s)
  invFun f := (fun s => (f s).1, fun s => (f s).2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- For any fixed subset `S : Finset (Fin Q)` of evaluation slots, the auxiliary labels
`β : AuxLabel Q r` with `antisymSlots β = S` are in bijection with
`Fintype.piFinset (fun s => if s ∈ S then antisymPairs r else symPairs r)` and therefore have
cardinality `#(antisymPairs r) ^ #S * #(symPairs r) ^ (Q - #S)`. -/
theorem card_filter_antisymSlots_eq (Q r : ℕ) (S : Finset (Fin Q)) :
    #(univ.filter (fun β : AuxLabel Q r => antisymSlots β = S)) =
      #(antisymPairs r) ^ #S * #(symPairs r) ^ (Q - #S) := by
  let t : Fin Q → Finset (Fin r × Fin r) := fun s =>
    if s ∈ S then antisymPairs r else symPairs r
  have hbij : #(univ.filter (fun β : AuxLabel Q r => antisymSlots β = S)) =
      #(Fintype.piFinset t) := by
    refine card_bij (fun β _ => auxLabelEquivSlotPairs Q r β) ?_ ?_ ?_
    · intro β hβ
      rw [mem_filter] at hβ
      rw [Fintype.mem_piFinset]
      intro s
      have hs : s ∈ S ↔ β.2 s < β.1 s := by
        rw [← hβ.2, antisymSlots, mem_filter]
        simp only [mem_univ, true_and]
      dsimp only [t, auxLabelEquivSlotPairs, Equiv.coe_fn_mk]
      split_ifs with hmem
      · rw [mem_antisymPairs]
        exact hs.mp hmem
      · rw [mem_symPairs]
        exact hmem ∘ hs.mpr
    · intro β₁ _ β₂ _ hEq
      exact (auxLabelEquivSlotPairs Q r).injective hEq
    · intro f hf
      rw [Fintype.mem_piFinset] at hf
      refine ⟨(auxLabelEquivSlotPairs Q r).symm f, ?_,
        (auxLabelEquivSlotPairs Q r).apply_symm_apply f⟩
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      ext s
      rw [antisymSlots, mem_filter]
      simp only [mem_univ, true_and, auxLabelEquivSlotPairs, Equiv.coe_fn_symm_mk]
      have hfs := hf s
      dsimp only [t] at hfs
      split_ifs at hfs with hmem
      · rw [mem_antisymPairs] at hfs
        exact iff_of_true hfs hmem
      · rw [mem_symPairs] at hfs
        exact iff_of_false hfs hmem
  rw [hbij, Fintype.card_piFinset]
  have hprod : (∏ s : Fin Q, #(t s)) =
      (∏ s : Fin Q, if s ∈ S then #(antisymPairs r) else #(symPairs r)) := by
    refine prod_congr rfl fun s _ => ?_
    dsimp only [t]
    split_ifs <;> rfl
  rw [hprod, prod_ite, prod_const, prod_const]
  have hfilter₁ : univ.filter (fun s : Fin Q => s ∈ S) = S := by
    ext s
    simp only [mem_filter, mem_univ, true_and]
  have hfilter₂ : #(univ.filter (fun s : Fin Q => s ∉ S)) = Q - #S := by
    have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin Q))) (· ∈ S)
    rw [hfilter₁, card_univ, Fintype.card_fin] at hsum
    omega
  rw [hfilter₁, hfilter₂]

/-- **Lemma 4.1 exact binomial fiber count (p. 28)**:
The number of auxiliary basis labels `β : AuxLabel Q r` with `antisymCount β = j` is
`Q.choose j * (r * (r - 1) / 2) ^ j * (r * (r + 1) / 2) ^ (Q - j)`. -/
theorem card_filter_antisymCount_eq (Q r j : ℕ) :
    #(univ.filter (fun β : AuxLabel Q r => antisymCount β = j)) =
      Q.choose j * (r * (r - 1) / 2) ^ j * (r * (r + 1) / 2) ^ (Q - j) := by
  have hbiUnion :
      univ.filter (fun β : AuxLabel Q r => antisymCount β = j) =
        ((univ : Finset (Fin Q)).powersetCard j).biUnion
          (fun S => univ.filter (fun β : AuxLabel Q r => antisymSlots β = S)) := by
    ext β
    rw [mem_filter, mem_biUnion]
    simp only [mem_univ, true_and, mem_powersetCard, subset_univ, mem_filter,
      antisymCount_eq_card_antisymSlots]
    constructor
    · intro hj
      exact ⟨antisymSlots β, hj, rfl⟩
    · rintro ⟨S, hj, rfl⟩
      exact hj
  rw [hbiUnion, card_biUnion]
  · have hsum :
        (∑ S ∈ (univ : Finset (Fin Q)).powersetCard j,
          #(univ.filter (fun β : AuxLabel Q r => antisymSlots β = S))) =
        ∑ S ∈ (univ : Finset (Fin Q)).powersetCard j,
          (#(antisymPairs r) ^ j * #(symPairs r) ^ (Q - j)) := by
      refine sum_congr rfl fun S hS => ?_
      rw [mem_powersetCard] at hS
      rw [card_filter_antisymSlots_eq, hS.2]
    rw [hsum, sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul,
      card_antisymPairs, card_symPairs, mul_assoc]
  · intro S₁ _ S₂ _ hne
    change Disjoint _ _
    rw [disjoint_left]
    intro β hβ₁ hβ₂
    rw [mem_filter] at hβ₁ hβ₂
    exact hne (hβ₁.2.symm.trans hβ₂.2)

/-- **Lemma 4.1 exact measurement row count (p. 28)**:
The number of measurement indices in `measurementIndices Q r A₀ R` is the sum over
`j ∈ range (Q + 1)` outside `[A₀, A₀ + R)` of
`Q.choose j * (r * (r - 1) / 2) ^ j * (r * (r + 1) / 2) ^ (Q - j)`. -/
theorem card_measurementIndices_eq (Q r A₀ R : ℕ) :
    #(measurementIndices Q r A₀ R) =
      ∑ j ∈ (range (Q + 1)).filter (fun j => j < A₀ ∨ A₀ + R ≤ j),
        Q.choose j * (r * (r - 1) / 2) ^ j * (r * (r + 1) / 2) ^ (Q - j) := by
  let J := (range (Q + 1)).filter (fun j => j < A₀ ∨ A₀ + R ≤ j)
  have hbiUnion :
      measurementIndices Q r A₀ R =
        J.biUnion (fun j => univ.filter (fun β : AuxLabel Q r => antisymCount β = j)) := by
    ext β
    rw [measurementIndices, mem_filter, mem_biUnion]
    simp only [J, mem_univ, true_and, mem_filter, mem_range, mem_Ico]
    constructor
    · intro hβ
      refine ⟨antisymCount β, ⟨Nat.lt_succ_of_le (antisymCount_le β), by omega⟩, rfl⟩
    · rintro ⟨j, ⟨_, hj⟩, rfl⟩
      omega
  rw [hbiUnion, card_biUnion]
  · refine sum_congr rfl fun j _ => card_filter_antisymCount_eq Q r j
  · intro j₁ _ j₂ _ hne
    change Disjoint _ _
    rw [disjoint_left]
    intro β hβ₁ hβ₂
    rw [mem_filter] at hβ₁ hβ₂
    exact hne (hβ₁.2.symm.trans hβ₂.2)

/-- The binomial tail probability `Pr[W ∉ {A₀, ..., A₀ + R - 1}]` for
`W ∼ Bin(Q, (r - 1) / (2 * r))` from Lemma 4.1 and equation (4.8) (p. 28). -/
def binomTailProb (Q r A₀ R : ℕ) : ℚ :=
  ∑ j ∈ (range (Q + 1)).filter (fun j => j < A₀ ∨ A₀ + R ≤ j),
    (Q.choose j : ℚ) * (((r : ℚ) - 1) / (2 * (r : ℚ))) ^ j *
      (((r : ℚ) + 1) / (2 * (r : ℚ))) ^ (Q - j)

/-- Rational cast of `#(antisymPairs r) = r * (r - 1) / 2`. -/
theorem cast_antisymPairs_eq (r : ℕ) :
    ((r * (r - 1) / 2 : ℕ) : ℚ) = (r : ℚ) ^ 2 * (((r : ℚ) - 1) / (2 * (r : ℚ))) := by
  rcases r with _ | r
  · simp
  · have h2 : (2 : ℕ) * ((r + 1) * (r + 1 - 1) / 2) = (r + 1) * (r + 1 - 1) := by
      rw [← card_antisymPairs (r + 1), two_mul_card_antisymPairs (r + 1)]
    have hcast : (2 : ℚ) * (((r + 1) * r / 2 : ℕ) : ℚ) = ((r + 1 : ℕ) : ℚ) * (r : ℚ) := by
      simpa only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_ofNat] using
        congrArg (fun k : ℕ => (k : ℚ)) h2
    have hr0 : ((r + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero r)
    simp only [Nat.add_sub_cancel]
    have hsub : (((r + 1 : ℕ) : ℚ) - 1) = (r : ℚ) := by push_cast; ring
    rw [hsub]
    field_simp [hr0]
    linarith

/-- Rational cast of `#(symPairs r) = r * (r + 1) / 2`. -/
theorem cast_symPairs_eq (r : ℕ) (hr : 0 < r) :
    ((r * (r + 1) / 2 : ℕ) : ℚ) = (r : ℚ) ^ 2 * (((r : ℚ) + 1) / (2 * (r : ℚ))) := by
  have h2 : (2 : ℕ) * (r * (r + 1) / 2) = r * (r + 1) := by
    rw [← card_symPairs r, two_mul_card_symPairs r]
  have hcast : (2 : ℚ) * ((r * (r + 1) / 2 : ℕ) : ℚ) = (r : ℚ) * ((r : ℚ) + 1) := by
    exact_mod_cast h2
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  field_simp [hr0]
  linarith

/-- **Lemma 4.1 rational identity (p. 28)**:
For `0 < r`, the number of rows `#(measurementIndices Q r A₀ R)` of `measurementMatrix` equals
`D * Pr[W ∉ I] = r ^ (2 * Q) * binomTailProb Q r A₀ R`. -/
theorem card_measurementIndices_cast_eq (Q r A₀ R : ℕ) (hr : 0 < r) :
    (#(measurementIndices Q r A₀ R) : ℚ) =
      ((r ^ (2 * Q) : ℕ) : ℚ) * binomTailProb Q r A₀ R := by
  rw [card_measurementIndices_eq, Nat.cast_sum, binomTailProb, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_filter, mem_range] at hj
  have hjQ : j ≤ Q := Nat.le_of_lt_succ hj.1
  push_cast
  rw [cast_antisymPairs_eq r, cast_symPairs_eq r hr, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
  have hpow : (r : ℚ) ^ (2 * j) * (r : ℚ) ^ (2 * (Q - j)) = (r : ℚ) ^ (2 * Q) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    (Q.choose j : ℚ) * ((r : ℚ) ^ (2 * j) * (((r : ℚ) - 1) / (2 * (r : ℚ))) ^ j) *
        ((r : ℚ) ^ (2 * (Q - j)) * (((r : ℚ) + 1) / (2 * (r : ℚ))) ^ (Q - j))
      = ((r : ℚ) ^ (2 * j) * (r : ℚ) ^ (2 * (Q - j))) *
          ((Q.choose j : ℚ) * (((r : ℚ) - 1) / (2 * (r : ℚ))) ^ j *
            (((r : ℚ) + 1) / (2 * (r : ℚ))) ^ (Q - j)) := by ring
    _ = (r : ℚ) ^ (2 * Q) *
          ((Q.choose j : ℚ) * (((r : ℚ) - 1) / (2 * (r : ℚ))) ^ j *
            (((r : ℚ) + 1) / (2 * (r : ℚ))) ^ (Q - j)) := by rw [hpow]

/-- **Lemma 4.1 and equation (4.8) row bound (p. 28)**:
If `binomTailProb Q r A₀ R ≤ ε`, then `#(measurementIndices Q r A₀ R) ≤ ε * r ^ (2 * Q)`. -/
theorem card_measurementIndices_le_of_binomTailProb_le {Q r A₀ R : ℕ} {ε : ℚ}
    (hr : 0 < r) (hε : binomTailProb Q r A₀ R ≤ ε) :
    (#(measurementIndices Q r A₀ R) : ℚ) ≤ ε * ((r ^ (2 * Q) : ℕ) : ℚ) := by
  rw [card_measurementIndices_cast_eq Q r A₀ R hr, mul_comm]
  exact mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)

/-- For `0 < r`, `binomTailProb Q r A₀ R` equals the fraction
`#(measurementIndices Q r A₀ R) / r ^ (2 * Q)` of auxiliary basis labels outside `[A₀, A₀ + R)`. -/
theorem binomTailProb_eq_div (Q r A₀ R : ℕ) (hr : 0 < r) :
    binomTailProb Q r A₀ R =
      (#(measurementIndices Q r A₀ R) : ℚ) / ((r ^ (2 * Q) : ℕ) : ℚ) := by
  have hD0 : ((r ^ (2 * Q) : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_pos hr (2 * Q)).ne'
  rw [card_measurementIndices_cast_eq Q r A₀ R hr, mul_div_cancel_left₀ _ hD0]

/-- `binomTailProb Q r A₀ R` is nonnegative for `1 ≤ r`. -/
theorem binomTailProb_nonneg {Q r A₀ R : ℕ} (hr : 1 ≤ r) :
    0 ≤ binomTailProb Q r A₀ R := by
  unfold binomTailProb
  refine sum_nonneg fun j _ => ?_
  have hr1 : (0 : ℚ) ≤ (r : ℚ) - 1 := by
    have : (1 : ℚ) ≤ (r : ℚ) := by exact_mod_cast hr
    linarith
  positivity

/-- When `R = 0`, the interval `[A₀, A₀ + R)` is empty and `binomTailProb Q r A₀ 0 = 1`
(the full binomial distribution sums to `1`). -/
theorem binomTailProb_zero_right (Q r A₀ : ℕ) (hr : 0 < r) :
    binomTailProb Q r A₀ 0 = 1 := by
  have hcard : #(measurementIndices Q r A₀ 0) = r ^ (2 * Q) := by
    have huniv : measurementIndices Q r A₀ 0 = univ := by
      ext β
      simp only [measurementIndices, mem_filter, mem_univ, add_zero, Ico_self, notMem_empty,
        not_false_eq_true, and_self]
    rw [huniv, card_univ, card_auxLabel]
  have hcast := card_measurementIndices_cast_eq Q r A₀ 0 hr
  rw [hcard] at hcast
  have hD0 : ((r ^ (2 * Q) : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_pos hr (2 * Q)).ne'
  exact mul_left_cancel₀ hD0 (by linarith)

/-- `binomTailProb Q r A₀ R ≤ 1` for `0 < r`. -/
theorem binomTailProb_le_one (Q r A₀ R : ℕ) (hr : 0 < r) :
    binomTailProb Q r A₀ R ≤ 1 := by
  have hle : #(measurementIndices Q r A₀ R) ≤ r ^ (2 * Q) :=
    (card_le_univ _).trans (by rw [card_auxLabel])
  have hle_q : (#(measurementIndices Q r A₀ R) : ℚ) ≤ ((r ^ (2 * Q) : ℕ) : ℚ) := by
    exact_mod_cast hle
  rw [card_measurementIndices_cast_eq Q r A₀ R hr] at hle_q
  have hD_pos : (0 : ℚ) < ((r ^ (2 * Q) : ℕ) : ℚ) := by
    exact_mod_cast pow_pos hr (2 * Q)
  nlinarith

/-! ### Part 3: Total group measurement row bound (Section 4.5, eq. 4.16, p. 32) -/

/-- **Equation (4.16) total group measurement row bound (p. 32)**:
When `h * r ^ (2 * Q) ≤ 2 * M`, `M ≤ b * n`, `0 ≤ τ`, and
`binomTailProb Q r A₀ R ≤ τ / (r * b)`, the total number of measurement rows
`r * (h * #(measurementIndices Q r A₀ R))` across all `r` variable groups is at most
`2 * τ * n`. -/
theorem card_allGroupMeasurementRows_le_two_mul_tau_mul_n {Q r A₀ R h M b n : ℕ} {τ : ℚ}
    (hr : 0 < r) (hb : 0 < b) (hτ : 0 ≤ τ)
    (hhD : h * r ^ (2 * Q) ≤ 2 * M) (hM : M ≤ b * n)
    (htail : binomTailProb Q r A₀ R ≤ τ / ((r : ℚ) * (b : ℚ))) :
    ((r * (h * #(measurementIndices Q r A₀ R)) : ℕ) : ℚ) ≤ 2 * τ * (n : ℚ) := by
  have hcB := card_measurementIndices_le_of_binomTailProb_le hr htail
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hhD_q : ((h : ℚ) * ((r ^ (2 * Q) : ℕ) : ℚ)) ≤ 2 * (b : ℚ) * (n : ℚ) := by
    have hle : h * r ^ (2 * Q) ≤ 2 * (b * n) := hhD.trans (Nat.mul_le_mul_left 2 hM)
    have hcast : ((h * r ^ (2 * Q) : ℕ) : ℚ) ≤ ((2 * (b * n) : ℕ) : ℚ) := by
      exact_mod_cast hle
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hcast
  push_cast
  have h1 :
      (r : ℚ) * ((h : ℚ) * (#(measurementIndices Q r A₀ R) : ℚ)) ≤
        (r : ℚ) * ((h : ℚ) * (τ / ((r : ℚ) * (b : ℚ)) * ((r ^ (2 * Q) : ℕ) : ℚ))) := by
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg r)
    exact mul_le_mul_of_nonneg_left hcB (Nat.cast_nonneg h)
  have h2 :
      (r : ℚ) * ((h : ℚ) * (τ / ((r : ℚ) * (b : ℚ)) * ((r ^ (2 * Q) : ℕ) : ℚ))) =
        (τ / (b : ℚ)) * ((h : ℚ) * ((r ^ (2 * Q) : ℕ) : ℚ)) := by
    field_simp [hr0, hb0]
  have h3 :
      (τ / (b : ℚ)) * ((h : ℚ) * ((r ^ (2 * Q) : ℕ) : ℚ)) ≤
        (τ / (b : ℚ)) * (2 * (b : ℚ) * (n : ℚ)) := by
    refine mul_le_mul_of_nonneg_left hhD_q ?_
    exact div_nonneg hτ (Nat.cast_nonneg b)
  have h4 : (τ / (b : ℚ)) * (2 * (b : ℚ) * (n : ℚ)) = 2 * τ * (n : ℚ) := by
    field_simp [hb0]
  linarith

/-! ### Part 4: Algebraic Section 4 replacement design (Definition 3.1 & Lemma 4.7, pp. 32–34) -/

/-- A bundled Section 4 replacement design for a factor scope family `scope : F → Finset (Fin n)`,
recording Definition 3.1 (1)–(4) (pp. 21–22) together with the explicit cleared-denominator
identity and `ℓ₁` coefficient norm bound of Lemma 4.6 (p. 33) that underlie Definition 3.1 (5)
(formal `O(Q log Q + log D)` bit-length and native runtime endpoints are separate follow-up). -/
structure ReplacementDesign {F : Type*} [Fintype F]
    (scope : F → Finset (Fin n)) (Q r A₀ R : ℕ) (τ : ℚ) where
  /-- Variable group schedule `a_v : Fin Q → Fin r` for each `v : Fin n`
  (determining `varGroup varAssign t g = {v | varAssign v t = g}`). -/
  varAssign : Fin n → Fin Q → Fin r
  /-- Factor group schedule `σ_f = d_f : Fin Q → Fin r` for each `f : F`. -/
  factorAssign : F → Fin Q → Fin r
  /-- Number of auxiliary array copies `h`. -/
  h : ℕ
  /-- Placement of each factor–variable incidence into `Fin h × AuxLabel Q r`. -/
  place : ScopeIncidence scope → Fin h × AuxLabel Q r
  /-- Definition 3.1 (1): every variable group `S_{t,g}` has size at most `2 * n / r`. -/
  card_varGroup_le : ∀ (t : Fin Q) (g : Fin r), #(varGroup varAssign t g) ≤ 2 * n / r
  /-- Section 4.1 / Lemma 4.5: factors with empty scope are assigned to group `0` at every
  point. -/
  factorAssign_of_empty : ∀ (f : F), scope f = ∅ → ∀ t : Fin Q, (factorAssign f t).1 = 0
  /-- Section 4.5: all occupied positions `(c(f,v), u_{f,v})` in `[h] × B` are distinct. -/
  injective_place : Function.Injective place
  /-- Section 4.4–4.5: the auxiliary label of incidence `e = (f, v)` is `(a_v, d_f)`. -/
  place_snd : ∀ e : ScopeIncidence scope,
    (place e).2 = (varAssign (scopeVarOf scope e), factorAssign (scopeFactorOf scope e))
  /-- Section 4.5: the copy count satisfies `h * D ≤ 2 * M`. -/
  h_mul_D_le : h * r ^ (2 * Q) ≤ 2 * ∑ f : F, #(scope f)
  /-- Definition 3.1 (3) and equation (4.16): the total number of measurement rows across all
  `r` groups at each evaluation point `t` is at most `2 * τ * n`. -/
  total_measurement_rows_le :
    ((r * (h * #(measurementIndices Q r A₀ R)) : ℕ) : ℚ) ≤ 2 * τ * (n : ℚ)
  /-- Definition 3.1 (3): every row of the integer measurement matrix has `ℓ₁`-norm at most
  `D = r ^ (2 * Q)`. -/
  sum_abs_measurement_row_le :
    ∀ p : Fin h × measurementIndices Q r A₀ R,
      (∑ v : Fin n, |varMeasurementMatrix Q r A₀ R ℤ place (scopeVarOf scope) p v|) ≤
        (r ^ (2 * Q) : ℤ)
  /-- Definition 3.1 (4): every replacement polynomial entry has degree at most `R - 1` (`≤ R`). -/
  natDegree_replacementRow_le :
    ∀ (e : ScopeIncidence scope) (v : Fin n),
      (varReplacementRow Q r A₀ R place (scopeVarOf scope) e v).natDegree ≤ R - 1
  /-- Definition 3.1 (4): at `T = 0`, the replacement row for incidence `e` evaluates to
  `δ_{scopeVarOf scope e}`. -/
  eval_replacementRow_zero :
    ∀ (e : ScopeIncidence scope) (v : Fin n),
      (varReplacementRow Q r A₀ R place (scopeVarOf scope) e v).eval 0 =
        if scopeVarOf scope e = v then 1 else 0
  /-- Definition 3.1 (4): for every `t : Fin Q`, off-group `g ≠ factorAssign f t`, and vector
  `ξ : Fin n → ℚ` supported on `varGroup varAssign t g` in the kernel of the measurement matrix,
  the replacement form at `nodePoint t` annihilates `ξ`. -/
  evalReplacementRow_nodePoint_eq_zero_of_kernel :
    ∀ (e : ScopeIncidence scope) (t : Fin Q) (g : Fin r),
      g ≠ factorAssign (scopeFactorOf scope e) t →
      ∀ ξ : Fin n → ℚ,
        (∀ v ∉ varGroup varAssign t g, ξ v = 0) →
        (varMeasurementMatrix Q r A₀ R ℚ place (scopeVarOf scope)).mulVec ξ = 0 →
        evalVarReplacementRow Q r A₀ R place (scopeVarOf scope) e (nodePoint t) ξ = 0
  /-- Definition 3.1 (5) and Lemma 4.6: multiplying by `commonDenom Q R = (R - 1)! * Q!` clears
  all denominators to the integer polynomial row `varReplacementRowScaledInt`. -/
  map_replacementRowScaledInt :
    ∀ (e : ScopeIncidence scope) (v : Fin n),
      (varReplacementRowScaledInt Q r A₀ R place (scopeVarOf scope) e v).map (Int.castRingHom ℚ) =
        (commonDenom Q R : ℚ) •
          varReplacementRow Q r A₀ R place (scopeVarOf scope) e v
  /-- Definition 3.1 (5) and Lemma 4.6: the sum of the `ℓ₁` coefficient norms across all `n`
  entries of each cleared row `varReplacementRowScaledInt` is bounded by
  `commonDenom Q R * (1 + (1 + 2 ^ Q) * R * (4 * Q) ^ (R - 1))`. -/
  sum_coeffNorm1_replacementRowScaledInt_le :
    ∀ e : ScopeIncidence scope,
      (∑ v : Fin n,
        ((varReplacementRowScaledInt Q r A₀ R place (scopeVarOf scope) e v).coeffNorm1 : ℤ)) ≤
        (commonDenom Q R : ℤ) * (1 + (1 + 2 ^ Q) * (R : ℤ) * (4 * (Q : ℤ)) ^ (R - 1))

/-- Evaluating the replacement form at `T = 0` on any vector `x : Fin n → ℚ` extracts
`x (scopeVarOf scope e)`. -/
theorem ReplacementDesign.evalReplacementRow_zero {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} {Q r A₀ R : ℕ} {τ : ℚ}
    (D : ReplacementDesign scope Q r A₀ R τ) (e : ScopeIncidence scope) (x : Fin n → ℚ) :
    evalVarReplacementRow Q r A₀ R D.place (scopeVarOf scope) e 0 x = x (scopeVarOf scope e) :=
  evalVarReplacementRow_zero Q r A₀ R D.injective_place (scopeVarOf scope) e x

/-- In any `ReplacementDesign`, the value of `evalVarReplacementRow` at `nodePoint t` for
incidence `e = (f, v)` depends only on `x` restricted to the assigned variable group
`varGroup D.varAssign t (D.factorAssign f t)` and the measurements
`(varMeasurementMatrix Q r A₀ R ℚ D.place (scopeVarOf scope)).mulVec x`. -/
theorem ReplacementDesign.evalReplacementRow_nodePoint_eq_of_eq_on_varGroup {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} {Q r A₀ R : ℕ} {τ : ℚ}
    (D : ReplacementDesign scope Q r A₀ R τ) (e : ScopeIncidence scope) (t : Fin Q)
    (x x' : Fin n → ℚ)
    (hgrp : ∀ v ∈ varGroup D.varAssign t (D.factorAssign (scopeFactorOf scope e) t), x v = x' v)
    (hmeas :
      (varMeasurementMatrix Q r A₀ R ℚ D.place (scopeVarOf scope)).mulVec x =
        (varMeasurementMatrix Q r A₀ R ℚ D.place (scopeVarOf scope)).mulVec x') :
    evalVarReplacementRow Q r A₀ R D.place (scopeVarOf scope) e (nodePoint t) x =
      evalVarReplacementRow Q r A₀ R D.place (scopeVarOf scope) e (nodePoint t) x' := by
  have hplace_fst_snd : ∀ e' : ScopeIncidence scope,
      (D.place e').2.1 = D.varAssign (scopeVarOf scope e') :=
    fun e' => congrArg Prod.fst (D.place_snd e')
  have hplace_snd_snd : (D.place e).2.2 = D.factorAssign (scopeFactorOf scope e) :=
    congrArg Prod.snd (D.place_snd e)
  refine evalVarReplacementRow_nodePoint_eq_of_eq_on_varGroup Q r A₀ R D.place
    (scopeVarOf scope) D.varAssign hplace_fst_snd e t x x' ?_ hmeas
  rwa [hplace_snd_snd]

/-- **Lemma 4.7 (Algebraic existence of a Section 4 replacement design, pp. 33–34)**:
Suppose `1 ≤ n`, `1 ≤ b`, `1 ≤ w`, `2 ≤ r`, `1 ≤ R`, `R < Q`, `0 ≤ τ`, every factor scope
`scope f` has size at most `w`, every variable belongs to at most `b` scopes,
`M = ∑ f, #(scope f) ≤ b * n`, the balance inequalities `2 * (b + w) * (r ^ (2 * Q)) ^ 2 ≤ M`
and `2 * Q * r ^ 2 ≤ n` hold (eq. 4.13), the mismatch-annihilator node-range condition
`hI : ∀ a < R - 1, A₀ + a ≤ Q` holds (vacuous at `R = 1` and implied by `[A₀, A₀ + R) ⊆ [0, Q]`),
and the binomial tail bound `binomTailProb Q r A₀ R ≤ τ / (r * b)` holds (eq. 4.8). Then there
exists a `ReplacementDesign` satisfying Definition 3.1 (1)–(4) and the explicit cleared-denominator
and `ℓ₁`-coefficient norm bounds of Lemma 4.6 (omitting the paper's `n ≤ M` and `0 < τ ≤ 1 / 2`
regime assumptions and leaving the `O(Q log Q + log D)` bit-length / native runtime endpoint as
separate follow-up). -/
theorem exists_replacementDesign {F : Type*} [Fintype F]
    (scope : F → Finset (Fin n)) {Q r A₀ R b w : ℕ} {τ : ℚ}
    (hn : 1 ≤ n) (hb_pos : 1 ≤ b) (hw_pos : 1 ≤ w)
    (hr : 2 ≤ r) (hR : 1 ≤ R) (hRQ : R < Q) (hτ : 0 ≤ τ)
    (hI : ∀ a < R - 1, A₀ + a ≤ Q)
    (hb : ∀ v : Fin n, #{f : F | v ∈ scope f} ≤ b)
    (hw : ∀ f : F, #(scope f) ≤ w)
    (hM_le : (∑ f : F, #(scope f)) ≤ b * n)
    (hincidenceSize : 2 * (b + w) * (r ^ (2 * Q)) ^ 2 ≤ ∑ f : F, #(scope f))
    (hgroupSize : 2 * Q * r ^ 2 ≤ n)
    (htail : binomTailProb Q r A₀ R ≤ τ / ((r : ℚ) * (b : ℚ))) :
    Nonempty (ReplacementDesign scope Q r A₀ R τ) := by
  classical
  have hQ_pos : 0 < Q := lt_of_lt_of_le (Nat.zero_lt_of_lt hR) hRQ.le
  have hr_pos : 0 < r := lt_of_lt_of_le (by decide : 0 < 2) hr
  have : Nonempty (Fin Q) := ⟨⟨0, hQ_pos⟩⟩
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Nonempty (Fin r) := ⟨⟨0, hr_pos⟩⟩
  have hcardA : Fintype.card (ScopeIncidence scope) = ∑ f : F, #(scope f) :=
    card_scopeIncidence scope
  have hcardB : Fintype.card (AuxLabel Q r) = r ^ (2 * Q) := card_auxLabel Q r
  have hbw : 0 < b + w := by omega
  have hinc_card :
      2 * (b + w) * Fintype.card (AuxLabel Q r) ^ 2 ≤ Fintype.card (ScopeIncidence scope) := by
    simpa only [hcardA, hcardB] using hincidenceSize
  have hgrp_card :
      2 * Fintype.card (Fin Q) * Fintype.card (Fin r) ^ 2 ≤ Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using hgroupSize
  obtain ⟨a, d, hempty, hocc_inc, hocc_grp⟩ :=
    exists_balanced_schedules_of_scopes scope hb hw hbw hinc_card hgrp_card ⟨0, hr_pos⟩
  let u : ScopeIncidence scope → AuxLabel Q r :=
    incidenceLabel (scopeVarOf scope) (scopeFactorOf scope) a d
  let h : ℕ := 2 * Fintype.card (ScopeIncidence scope) / r ^ (2 * Q)
  have hD_pos : 0 < r ^ (2 * Q) := pow_pos hr_pos (2 * Q)
  have hu_bound : ∀ y : AuxLabel Q r, #{e : ScopeIncidence scope | u e = y} ≤ h := by
    intro y
    have hocc := hocc_inc y
    rw [hcardB] at hocc
    rw [← Fintype.card_subtype]
    exact (Nat.le_div_iff_mul_le hD_pos).mpr hocc
  let : LinearOrder (ScopeIncidence scope) :=
    LinearOrder.lift' (Fintype.equivFin (ScopeIncidence scope))
      (Fintype.equivFin (ScopeIncidence scope)).injective
  let place : ScopeIncidence scope → Fin h × AuxLabel Q r :=
    fun e => (fiberRankCopy u hu_bound e, u e)
  have hinj_place : Function.Injective place :=
    injective_fiberRankCopy_prod u hu_bound
  have hplace_fst_snd : ∀ e : ScopeIncidence scope, (place e).2.1 = a (scopeVarOf scope e) :=
    fun _ => rfl
  have hhD : h * r ^ (2 * Q) ≤ 2 * ∑ f : F, #(scope f) := by
    rw [← hcardA]
    exact Nat.div_mul_le_self (2 * Fintype.card (ScopeIncidence scope)) (r ^ (2 * Q))
  refine ⟨{
    varAssign := a
    factorAssign := d
    h := h
    place := place
    card_varGroup_le := fun t g => by
      have hocc := hocc_grp t g
      rw [Fintype.card_fin, Fintype.card_fin] at hocc
      rw [varGroup, ← Fintype.card_subtype]
      exact (Nat.le_div_iff_mul_le hr_pos).mpr hocc
    factorAssign_of_empty := fun f hf t => by
      rw [hempty f hf]
    injective_place := hinj_place
    place_snd := fun _ => rfl
    h_mul_D_le := hhD
    total_measurement_rows_le :=
      card_allGroupMeasurementRows_le_two_mul_tau_mul_n hr_pos hb_pos hτ hhD hM_le htail
    sum_abs_measurement_row_le :=
      sum_abs_varMeasurementMatrix_le Q r A₀ R hinj_place (scopeVarOf scope)
    natDegree_replacementRow_le :=
      natDegree_varReplacementRow_le Q r A₀ R place (scopeVarOf scope)
    eval_replacementRow_zero :=
      eval_varReplacementRow_zero Q r A₀ R hinj_place (scopeVarOf scope)
    evalReplacementRow_nodePoint_eq_zero_of_kernel := fun e t g hg ξ hsupp hker =>
      evalVarReplacementRow_nodePoint_eq_zero_of_kernel Q r A₀ R place (scopeVarOf scope) a
        hplace_fst_snd e t g hg ξ hsupp hker
    map_replacementRowScaledInt :=
      map_varReplacementRowScaledInt Q r A₀ R place (scopeVarOf scope)
    sum_coeffNorm1_replacementRowScaledInt_le :=
      sum_coeffNorm1_varReplacementRowScaledInt_le hQ_pos hinj_place (scopeVarOf scope) hI
  }⟩

end Cslib.LinearAlgebra

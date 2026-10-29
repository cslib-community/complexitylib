/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Alphabets
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Pi
import Mathlib.Tactic.Ring

/-!
# Full tensor recursion and shared encodings

The recursion works on mathematical arrays indexed by finite strings. Its multiplication
record identifies the two encoded integers at each leaf. The returned array equals the
bilinear tensor expansion. These recursive values and combinatorial counts carry no native
instruction-cost interpretation.

## Main definitions

* `Full.run`, `Full.result`, `Full.multipliedAt`: full evaluation and leaf operands.
* `encodeLeft`, `encodeRight`, `encodingL`, `encodingR`: shared leaf encodings.
* `bilinearProduct`, `coefficient`, `leaves`: the tensor expansion and contributing leaves.

## Main results

* `full_spec`: full evaluation returns the bilinear product and uses the stated encodings.
* `tensor_expansion`: expansion into products of the one-level tensor coefficients.
* `abs_phi_le_one`, `abs_psi_le_one`: bounded encoding coefficients.

## References

Part of [AlmanWilliams2026, Section 2]. Direct mathematical adaptation of
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Definitions are selectively extracted from that pin's `PaperStatements.lean`; no machine
semantics or running-time statement is imported. The docstrings below explain the local
declarations in our own words.
-/

@[expose] public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Fix the first coordinate of a tuple-indexed array and retain the shorter tuple as its
argument. The construction works for any coordinate alphabet and value type.
-/
def sliceAt {α β : Type} {L : ℕ} (a : (Fin (L + 1) → α) → β) (s : α) : (Fin L → α) → β :=
  fun u' => a (Fin.cons s u')

/-- Apply the left coefficient form for `lam` to all first-coordinate slices of the input array. -/
def encodeStepL {L : ℕ} (lam : Term) (a : LeftStr (L + 1) → ℤ) : LeftStr L → ℤ :=
  fun u' => ∑ s, phi lam s * sliceAt a s u'

/-- Apply the right coefficient form for `lam` to all first-coordinate slices of the input array. -/
def encodeStepR {L : ℕ} (lam : Term) (b : RightStr (L + 1) → ℤ) : RightStr L → ℤ :=
  fun v' => ∑ t, psi lam t * sliceAt b t v'

/-- Evaluate the two arrays and retain the operands used at each leaf. At depth zero, multiply
their unique entries. At positive depth, apply each term’s left and right coefficient forms,
recurse, and decode the child results into an output array. The second component maps each term
string to its pair of encoded input values. This is a finite integer recursion, with no
instruction counter.
-/
def Full.run : (L : ℕ) → (LeftStr L → ℤ) → (RightStr L → ℤ) → (OutStr L → ℤ) × (Leaf L → ℤ × ℤ)
  | 0, a, b => (fun _ => a Fin.elim0 * b Fin.elim0, fun _ => (a Fin.elim0, b Fin.elim0))
  | L + 1, a, b =>
    let R : Term → (OutStr L → ℤ) × (Leaf L → ℤ × ℤ) := fun lam =>
      Full.run L (encodeStepL lam a) (encodeStepR lam b)
    (fun w =>
        match w 0 with
        | .z i j => (R (.P i j)).1 (Fin.tail w)
        | .z0 => ∑ lam, (R lam).1 (Fin.tail w),
      fun τ => (R (τ 0)).2 (Fin.tail τ))

/-- Project the output array from full evaluation, discarding its record of leaf operands. -/
def Full.result (L : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ) : OutStr L → ℤ :=
  (Full.run L a b).1

/-- Read the ordered pair of leaf operands recorded by `Full.run`. -/
def Full.multipliedAt (L : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (τ : Leaf L) : ℤ × ℤ :=
  (Full.run L a b).2 τ

/-! ### 2.3.2 Unraveling the recursion computation -/

/-- Evaluate the left encoding at one leaf by weighting each input entry with the product of its
coordinate coefficients.
-/
def encodeLeft {L : ℕ} (τ : Leaf L) (a : LeftStr L → ℤ) : ℤ := ∑ u, a u * ∏ ℓ, phi (τ ℓ) (u ℓ)

/-- Evaluate the right encoding at one leaf using the corresponding products of right
coefficients.
-/
def encodeRight {L : ℕ} (τ : Leaf L) (b : RightStr L → ℤ) : ℤ := ∑ v, b v * ∏ ℓ, psi (τ ℓ) (v ℓ)

/-- A leaf is relevant to an output tuple when its labels are relevant at every coordinate. -/
def Leaf.Contributes {L : ℕ} (τ : Leaf L) (w : OutStr L) : Prop :=
  ∀ ℓ, (τ ℓ).Contributes (w ℓ)

instance Leaf.instDecidableContributes {L : ℕ} (τ : Leaf L) (w : OutStr L) :
    Decidable (Leaf.Contributes τ w) :=
  inferInstanceAs (Decidable (∀ ℓ, (τ ℓ).Contributes (w ℓ)))

/-- For each output tuple, sum the products of left and right encodings over its relevant leaves. -/
def bilinearProduct {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) : OutStr L → ℤ :=
  fun w => ∑ τ : Leaf L with Leaf.Contributes τ w, encodeLeft τ a * encodeRight τ b

/-- The coefficient linking one left, right and output coordinate, obtained by summing products of
the relevant label coefficients.
-/
def coefficient (s : LeftVar) (t : RightVar) (z : OutVar) : ℤ :=
  ∑ lam : Term with lam.Contributes z, phi lam s * psi lam t

/-- Package all left-encoding values into an array indexed by leaves. -/
def encodingL {L : ℕ} (a : LeftStr L → ℤ) : Leaf L → ℤ := fun τ => encodeLeft τ a

/-- Package all right-encoding values into an array indexed by leaves. -/
def encodingR {L : ℕ} (b : RightStr L → ℤ) : Leaf L → ℤ := fun τ => encodeRight τ b

/-- Take the union of the relevant-leaf sets of all requested output tuples. -/
def leaves {L : ℕ} (U : Finset (OutStr L)) : Finset (Leaf L) :=
  univ.filter fun τ => ∃ w ∈ U, Leaf.Contributes τ w

/-- Counting length-`L` left tuples gives `7^L`. -/
theorem card_leftStr (L : ℕ) : Fintype.card (LeftStr L) = 7 ^ L := by
  rw [Fintype.card_fun, card_leftVar, Fintype.card_fin]

/-- Counting length-`L` right tuples gives `7^L`. -/
theorem card_rightStr (L : ℕ) : Fintype.card (RightStr L) = 7 ^ L := by
  rw [Fintype.card_fun, card_rightVar, Fintype.card_fin]

/-- A depth-`k` label sequence has ten independent choices at each position. -/
theorem card_vertex (k : ℕ) : Fintype.card (Vertex k) = 10 ^ k := by
  rw [Fintype.card_fun, card_term, Fintype.card_fin]

/-- Every left coefficient has absolute value at most one. -/
theorem abs_phi_le_one (lam : Term) (s : LeftVar) : |phi lam s| ≤ 1 := by
  decide +revert

/-- Every right coefficient has absolute value at most one. -/
theorem abs_psi_le_one (lam : Term) (t : RightVar) : |psi lam t| ≤ 1 := by
  decide +revert

/-- The support of any left coefficient form has cardinality at most three. -/
theorem card_support_phi_le (lam : Term) : (univ.filter fun s => phi lam s ≠ 0).card ≤ 3 := by
  decide +revert

/-- The support of any right coefficient form has cardinality at most three. -/
theorem card_support_psi_le (lam : Term) : (univ.filter fun t => psi lam t ≠ 0).card ≤ 3 := by
  decide +revert

/-! ### Which leaves contribute to an output string -/

/-- Split coordinatewise leaf relevance into the first label and the remaining label tuple. -/
theorem Leaf.contributes_succ {L : ℕ} {τ : Leaf (L + 1)} {w : OutStr (L + 1)} :
    Leaf.Contributes τ w
      ↔ (τ 0).Contributes (w 0) ∧ Leaf.Contributes (Fin.tail τ) (Fin.tail w) := by
  simp only [Leaf.Contributes, Fin.forall_fin_succ, Fin.tail]

/-- A sum over the strings of length `L + 1` is a sum over the first variable `s` and the rest
`u'` of the string `s u'`.
-/
private theorem sum_strings_succ {α : Type*} [Fintype α] {L : ℕ} (f : (Fin (L + 1) → α) → ℤ) :
    ∑ u, f u = ∑ s, ∑ u', f (Fin.cons s u') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => α) _ _ fun _ => rfl).symm

/-- A sum over the leaves contributing to `w`, split by the first term of the leaf.
-/
theorem Leaf.sum_contributes_succ {L : ℕ} (w : OutStr (L + 1)) (f : Leaf (L + 1) → ℤ) :
    ∑ τ : Leaf (L + 1) with Leaf.Contributes τ w, f τ
      = ∑ lam : Term with lam.Contributes (w 0),
          ∑ τ' : Leaf L with Leaf.Contributes τ' (Fin.tail w), f (Fin.cons lam τ') := by
  simp only [sum_filter, sum_strings_succ, Leaf.contributes_succ, Fin.cons_zero,
    Fin.tail_cons]
  refine sum_congr rfl fun lam _ => ?_
  by_cases h : lam.Contributes (w 0) <;> simp [h]

/-- The relevant-leaf filter is a product of the allowed label sets at individual coordinates. -/
theorem Leaf.filter_contributes_eq_piFinset {L : ℕ} (w : OutStr L) :
    (univ.filter fun τ : Leaf L => Leaf.Contributes τ w)
      = Fintype.piFinset fun ℓ => univ.filter fun lam : Term => lam.Contributes (w ℓ) := by
  ext τ
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  rfl

/-- Membership in `leaves(U)`.
-/
@[simp]
theorem mem_leaves {L : ℕ} {U : Finset (OutStr L)} {τ : Leaf L} :
    τ ∈ leaves U ↔ ∃ w ∈ U, Leaf.Contributes τ w := by
  simp [leaves]

/-! ### The two encodings at once -/

section encodeWith

variable {α : Type} [Fintype α] (c : Term → α → ℤ) {L : ℕ}

/-- Encoding for an arbitrary coefficient family: weight each array entry by the product of
coefficients selected by the leaf. This specializes to both input encodings.
-/
def encodeWith (τ : Leaf L) (a : (Fin L → α) → ℤ) : ℤ := ∑ u, a u * ∏ ℓ, c (τ ℓ) (u ℓ)

/-- With no coordinates, the encoding evaluates the array at its unique empty argument. -/
theorem encodeWith_zero (τ : Leaf 0) (a : (Fin 0 → α) → ℤ) : encodeWith c τ a = a Fin.elim0 := by
  simp [encodeWith, Subsingleton.elim (default : Fin 0 → α) Fin.elim0]

/-- Process the first label of an encoding by combining the first-coordinate slices, then encode
the resulting shorter array.
-/
theorem encodeWith_cons (lam : Term) (τ' : Leaf L) (a : (Fin (L + 1) → α) → ℤ) :
    encodeWith c (Fin.cons lam τ' : Leaf (L + 1)) a
      = encodeWith c τ' fun u' => ∑ s, c lam s * sliceAt a s u' := by
  simp only [encodeWith, sum_strings_succ, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    sliceAt, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun u' _ => sum_congr rfl fun s _ => by ring

end encodeWith

/-! ### Lemma 7 -/

/-- The left encoding at a cons leaf is the tail encoding of the array produced by `encodeStepL`. -/
theorem encodeLeft_cons {L : ℕ} (lam : Term) (τ' : Leaf L) (a : LeftStr (L + 1) → ℤ) :
    encodeLeft (Fin.cons lam τ' : Leaf (L + 1)) a = encodeLeft τ' (encodeStepL lam a) :=
  encodeWith_cons phi lam τ' a

/-- The right encoding at a cons leaf is the tail encoding of the array produced by
`encodeStepR`.
-/
theorem encodeRight_cons {L : ℕ} (lam : Term) (τ' : Leaf L) (b : RightStr (L + 1) → ℤ) :
    encodeRight (Fin.cons lam τ' : Leaf (L + 1)) b = encodeRight τ' (encodeStepR lam b) :=
  encodeWith_cons psi lam τ' b

/-- The zero-depth left encoding reads the array at the empty tuple. -/
private theorem encodeLeft_zero (τ : Leaf 0) (a : LeftStr 0 → ℤ) : encodeLeft τ a = a Fin.elim0 :=
  encodeWith_zero phi τ a

/-- At depth zero, the right encoding equals the input entry at the unique empty string.
-/
private theorem encodeRight_zero (τ : Leaf 0) (b : RightStr 0 → ℤ) :
    encodeRight τ b = b Fin.elim0 :=
  encodeWith_zero psi τ b

/-- The operand record of full evaluation agrees with `encodeLeft` and `encodeRight` at every
leaf.
-/
theorem Full.multipliedAt_eq_encoding {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ)
    (τ : Leaf L) :
    Full.multipliedAt L a b τ = (encodeLeft τ a, encodeRight τ b) := by
  induction L with
  | zero =>
    rw [encodeLeft_zero, encodeRight_zero]
    rfl
  | succ L ih =>
    -- The leaf `τ` is `λ τ'` with `λ = τ 0` and `τ' = Fin.tail τ`. By steps (2) and (3) it is the
    -- leaf `τ'` of `Full.result(A_λ, B_λ)`.
    have hstep : Full.multipliedAt (L + 1) a b τ
        = Full.multipliedAt L (encodeStepL (τ 0) a) (encodeStepR (τ 0) b) (Fin.tail τ) := rfl
    rw [hstep, ih, ← encodeLeft_cons, ← encodeRight_cons, Fin.cons_self_tail]

/-- Unfold full evaluation once and express decoding as a sum over labels relevant to the leading
output coordinate.
-/
theorem Full.result_succ {L : ℕ} (a : LeftStr (L + 1) → ℤ) (b : RightStr (L + 1) → ℤ)
    (w : OutStr (L + 1)) :
    Full.result (L + 1) a b w = ∑ lam : Term with lam.Contributes (w 0),
      Full.result L (encodeStepL lam a) (encodeStepR lam b) (Fin.tail w) := by
  rw [Term.sum_contributes]
  rfl

/-- The bilinear product obeys the same first-coordinate decoding recurrence as full evaluation. -/
theorem bilinearProduct_succ {L : ℕ} (a : LeftStr (L + 1) → ℤ) (b : RightStr (L + 1) → ℤ)
    (w : OutStr (L + 1)) :
    bilinearProduct a b w = ∑ lam : Term with lam.Contributes (w 0),
      bilinearProduct (encodeStepL lam a) (encodeStepR lam b) (Fin.tail w) := by
  simp only [bilinearProduct, Leaf.sum_contributes_succ, encodeLeft_cons, encodeRight_cons]

/-- Full evaluation computes the bilinear tensor expansion `bilinearProduct`.
-/
theorem Full.result_eq_bilinearProduct {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) :
    Full.result L a b = bilinearProduct a b := by
  induction L with
  | zero =>
    funext w
    simp [Full.result, Full.run, bilinearProduct, Leaf.Contributes, encodeLeft_zero,
      encodeRight_zero]
  | succ L ih =>
    funext w
    simp only [Full.result_succ, bilinearProduct_succ, ih]

/-- The complete value specification of full evaluation: its result is `bilinearProduct`, and each
leaf’s operands are the corresponding left and right encodings.
-/
theorem full_spec {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) :
    (∀ τ : Leaf L, Full.multipliedAt L a b τ = (encodeLeft τ a, encodeRight τ b)) ∧
      Full.result L a b = bilinearProduct a b :=
  ⟨Full.multipliedAt_eq_encoding a b, Full.result_eq_bilinearProduct a b⟩

/-! ### Lemma 8 -/

/-- Expand the product of one-coordinate coefficients as a sum of coefficient products indexed by
relevant leaves.
-/
theorem prod_gamma_eq_sum_contributes {L : ℕ} (u : LeftStr L) (v : RightStr L) (w : OutStr L) :
    ∏ ℓ, coefficient (u ℓ) (v ℓ) (w ℓ)
      = ∑ τ : Leaf L with Leaf.Contributes τ w, (∏ ℓ, phi (τ ℓ) (u ℓ)) * ∏ ℓ, psi (τ ℓ) (v ℓ) := by
  simp only [coefficient]
  rw [prod_univ_sum, Leaf.filter_contributes_eq_piFinset]
  exact sum_congr rfl fun τ _ => prod_mul_distrib

/-- Expand `bilinearProduct` as a double sum of input-entry products. The coefficient of each pair
is the product, over string positions, of the one-level coefficients.
-/
theorem tensor_expansion {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (w : OutStr L) :
    bilinearProduct a b w = ∑ u, ∑ v, (∏ ℓ, coefficient (u ℓ) (v ℓ) (w ℓ)) * a u * b v := by
  -- Expand the encoded factors and reorder the finite sums. The coefficient of each input
  -- product is the product of its one-level coefficients.
  simp only [bilinearProduct, encodeLeft, encodeRight, sum_mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [prod_gamma_eq_sum_contributes, sum_mul, sum_mul]
  exact sum_congr rfl fun τ _ => by ring

end Cslib.Algorithms.MatrixMultiplication.Schonhage

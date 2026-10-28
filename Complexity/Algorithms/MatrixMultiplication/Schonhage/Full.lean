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
semantics or running-time statement is imported. Source-derived prose is paraphrased below.
-/

@[expose] public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Section 2.3.1: An array a on the left strings of length L assigns an integer a[u] to each u
that is a left string of length L.  So such an array is a function `LeftStr L → ℤ`, and likewise
for right strings, output strings and leaves.

the slice of a at a left variable s is the array a_s on the strings of length L - 1 given by
a_s[u'] := a[s u']; the same definition is used for every alphabet.
-/
def sliceAt {α β : Type} {L : ℕ} (a : (Fin (L + 1) → α) → β) (s : α) : (Fin L → α) → β :=
  fun u' => a (Fin.cons s u')

/-- Section 2.3.1, step (2) of `Full.result`: A_λ := ∑_s φ_λ(s) a_s.
-/
def encodeStepL {L : ℕ} (lam : Term) (a : LeftStr (L + 1) → ℤ) : LeftStr L → ℤ :=
  fun u' => ∑ s, phi lam s * sliceAt a s u'

/-- Section 2.3.1, step (2) of `Full.result`: B_λ := ∑_t ψ_λ(t) b_t.
-/
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

/-- The array that `Full.result(a, b)` returns.
-/
def Full.result (L : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ) : OutStr L → ℤ :=
  (Full.run L a b).1

/-- The two numbers that `Full.result(a, b)` multiplies at the leaf `τ`, the left one first.
-/
def Full.multipliedAt (L : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (τ : Leaf L) : ℤ × ℤ :=
  (Full.run L a b).2 τ

/-! ### 2.3.2 Unraveling the recursion computation -/

/-- Section 2.3.2: Φ_τ(a) := ∑_u a[u] ∏_{ℓ=1}^{L} φ_{τ_ℓ}(u_ℓ), the sum over all left strings `u`.
-/
def encodeLeft {L : ℕ} (τ : Leaf L) (a : LeftStr L → ℤ) : ℤ := ∑ u, a u * ∏ ℓ, phi (τ ℓ) (u ℓ)

/-- Section 2.3.2: Ψ_τ(b) := ∑_v b[v] ∏_{ℓ=1}^{L} ψ_{τ_ℓ}(v_ℓ), the sum over all right strings
`v`.
-/
def encodeRight {L : ℕ} (τ : Leaf L) (b : RightStr L → ℤ) : ℤ := ∑ v, b v * ∏ ℓ, psi (τ ℓ) (v ℓ)

/-- Section 2.3.2: a vertex τ₁ ⋯ τ_k contributes to an output string w if τ_ℓ contributes to w_ℓ
at every level ℓ ≤ k, for a leaf, that is, for `k = L`: the leaf `τ` contributes to `w` if `τ_ℓ`
contributes to `w_ℓ` at every level `ℓ`.
-/
def Leaf.Contributes {L : ℕ} (τ : Leaf L) (w : OutStr L) : Prop :=
  ∀ ℓ, (τ ℓ).Contributes (w ℓ)

instance Leaf.instDecidableContributes {L : ℕ} (τ : Leaf L) (w : OutStr L) :
    Decidable (Leaf.Contributes τ w) :=
  inferInstanceAs (Decidable (∀ ℓ, (τ ℓ).Contributes (w ℓ)))

/-- Equation (2): bilinearProduct(a, b)[w] := ∑_{τ contributing to w} Φ_τ(a) Ψ_τ(b).
-/
def bilinearProduct {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) : OutStr L → ℤ :=
  fun w => ∑ τ : Leaf L with Leaf.Contributes τ w, encodeLeft τ a * encodeRight τ b

/-- Equation (3): γ(s, t, z) := ∑_{λ contributing to z} φ_λ(s) ψ_λ(t).
-/
def coefficient (s : LeftVar) (t : RightVar) (z : OutVar) : ℤ :=
  ∑ lam : Term with lam.Contributes z, phi lam s * psi lam t

/-- Section 2.4.1: The encoding of a is the array of the 10^L numbers Φ_τ(a), indexed by the
leaves τ.
-/
def encodingL {L : ℕ} (a : LeftStr L → ℤ) : Leaf L → ℤ := fun τ => encodeLeft τ a

/-- Section 2.4.1: The encoding of b, the array of the numbers Ψ_τ(b).
-/
def encodingR {L : ℕ} (b : RightStr L → ℤ) : Leaf L → ℤ := fun τ => encodeRight τ b

/-- Section 2.4.2: For a set U of output strings of length L, we write leaves(U) for the set of
leaves that contribute to some output string of U.
-/
def leaves {L : ℕ} (U : Finset (OutStr L)) : Finset (Leaf L) :=
  univ.filter fun τ => ∃ w ∈ U, Leaf.Contributes τ w

/-- Section 2.3.1: an array on the left strings of length `L` has 7^L entries in total.
-/
theorem card_leftStr (L : ℕ) : Fintype.card (LeftStr L) = 7 ^ L := by
  rw [Fintype.card_fun, card_leftVar, Fintype.card_fin]

/-- Section 2.3.1: an array on the right strings of length `L` has `7^L` entries.
-/
theorem card_rightStr (L : ℕ) : Fintype.card (RightStr L) = 7 ^ L := by
  rw [Fintype.card_fun, card_rightVar, Fintype.card_fin]

/-- Section 2.3.1: At depth k there are 10^k vertices; in particular there are `10^L` leaves.
-/
theorem card_vertex (k : ℕ) : Fintype.card (Vertex k) = 10 ^ k := by
  rw [Fintype.card_fun, card_term, Fintype.card_fin]

/-- Section 2.3.1: φ_λ(s) ∈ {0, ±1}.
-/
theorem abs_phi_le_one (lam : Term) (s : LeftVar) : |phi lam s| ≤ 1 := by
  decide +revert

/-- Section 2.3.1: `ψ_λ(t) ∈ {0, ±1}`.
-/
theorem abs_psi_le_one (lam : Term) (t : RightVar) : |psi lam t| ≤ 1 := by
  decide +revert

/-- Section 2.3.1: for each term λ, at most three of the seven values φ_λ(s) are nonzero.
-/
theorem card_support_phi_le (lam : Term) : (univ.filter fun s => phi lam s ≠ 0).card ≤ 3 := by
  decide +revert

/-- Section 2.3.1: and similarly for the seven values ψ_λ(t).
-/
theorem card_support_psi_le (lam : Term) : (univ.filter fun t => psi lam t ≠ 0).card ≤ 3 := by
  decide +revert

/-! ### Which leaves contribute to an output string -/

/-- In the proof of Lemma 7: the leaves contributing to zw' are the λτ' with λ contributing to z
and τ' contributing to w'.  Here `λ = τ 0`, `τ' = Fin.tail τ`, `z = w 0` and `w' = Fin.tail w`.
-/
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

/-- In the proof of Lemma 8: the leaves contributing to `w` are the leaves whose term at level ℓ
contributes to w_ℓ, independently for each ℓ.
-/
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

/-- The number `∑_u a[u] ∏_ℓ c_{τ_ℓ}(u_ℓ)`, for an array `a` on the strings over a finite alphabet
and the coefficients `c` of a family of linear forms, one for each term. By definition it is
`Φ_τ(a)` for `c = φ` and `Ψ_τ(b)` for `c = ψ`.
-/
def encodeWith (τ : Leaf L) (a : (Fin L → α) → ℤ) : ℤ := ∑ u, a u * ∏ ℓ, c (τ ℓ) (u ℓ)

/-- For `L = 0` the only string is empty, and so are the products over the levels.
-/
theorem encodeWith_zero (τ : Leaf 0) (a : (Fin 0 → α) → ℤ) : encodeWith c τ a = a Fin.elim0 := by
  simp [encodeWith, Subsingleton.elim (default : Fin 0 → α) Fin.elim0]

/-- The number at the leaf `λτ'` for `a` is the number at the leaf `τ'` for `∑_s c_λ(s) a_s`.
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

/-- In the proof of Lemma 7: for every leaf λτ' we have Φ_{λτ'}(a) = ∑_s φ_λ(s) Φ_{τ'}(a_s) =
Φ_{τ'}(A_λ).
-/
theorem encodeLeft_cons {L : ℕ} (lam : Term) (τ' : Leaf L) (a : LeftStr (L + 1) → ℤ) :
    encodeLeft (Fin.cons lam τ' : Leaf (L + 1)) a = encodeLeft τ' (encodeStepL lam a) :=
  encodeWith_cons phi lam τ' a

/-- In the proof of Lemma 7: and similarly Ψ_{λτ'}(b) = Ψ_{τ'}(B_λ).
-/
theorem encodeRight_cons {L : ℕ} (lam : Term) (τ' : Leaf L) (b : RightStr (L + 1) → ℤ) :
    encodeRight (Fin.cons lam τ' : Leaf (L + 1)) b = encodeRight τ' (encodeStepR lam b) :=
  encodeWith_cons psi lam τ' b

/-- For L = 0, the only leaf is the empty string τ, and Φ_τ(a) = a […], as the products over the
levels are empty (proof of Lemma 7).
-/
private theorem encodeLeft_zero (τ : Leaf 0) (a : LeftStr 0 → ℤ) : encodeLeft τ a = a Fin.elim0 :=
  encodeWith_zero phi τ a

/-- At depth zero, the right encoding equals the input entry at the unique empty string.
-/
private theorem encodeRight_zero (τ : Leaf 0) (b : RightStr 0 → ℤ) :
    encodeRight τ b = b Fin.elim0 :=
  encodeWith_zero psi τ b

/-- **Lemma 7**, first half.  At the leaf τ, Full.result(a, b) multiplies Φ_τ(a) by Ψ_τ(b).
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

/-- Step (4) of `Full.result`, as it is read in the proof of Lemma 7: `c[z w'] = ∑_{λ contributing
to z} C_λ[w']`.
-/
theorem Full.result_succ {L : ℕ} (a : LeftStr (L + 1) → ℤ) (b : RightStr (L + 1) → ℤ)
    (w : OutStr (L + 1)) :
    Full.result (L + 1) a b w = ∑ lam : Term with lam.Contributes (w 0),
      Full.result L (encodeStepL lam a) (encodeStepR lam b) (Fin.tail w) := by
  rw [Term.sum_contributes]
  rfl

/-- In the proof of Lemma 7: `bilinearProduct(a, b)[z w'] = ∑_{λ contributing to z}
bilinearProduct(A_λ, B_λ)[w']`.
-/
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

/-- The display in the proof of Lemma 8: the sum, over the leaves `τ` contributing to `w`, of `∏_ℓ
φ_{τ_ℓ}(u_ℓ) ψ_{τ_ℓ}(v_ℓ)` is the product of sums ∏_ℓ ∑_{τ_ℓ contributing to w_ℓ} φ_{τ_ℓ}(u_ℓ)
ψ_{τ_ℓ}(v_ℓ) = ∏_ℓ γ(u_ℓ, v_ℓ, w_ℓ) by (3).
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

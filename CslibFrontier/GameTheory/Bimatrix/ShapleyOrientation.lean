/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.VertexOrientation
public import CslibFrontier.GameTheory.Bimatrix.LemkeHowson
public import Mathlib.Data.Finset.Sort
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Basic.Sign.Defs
import Mathlib.Tactic.Ring

/-!
# Shapley's orientation of Lemke–Howson paths

This module formalizes the determinant-based orientation (index) of the Lemke–Howson graph due to
Shapley [Shapley1974] (see also [vonStengel2007, Section 3.12]).

For two nondegenerate bounded polyhedra `A₁ *ᵥ x ≤ b₁` (`ι₁`-dimensional) and `A₂ *ᵥ y ≤ b₂`
(`ι₂`-dimensional) whose constraint rows share a label set `κ` of cardinality `m + n` with missing
label `k₀`, each active half-edge `(p, side)` out of a `LemkeHowson.Node` carries an orientation
sign `halfEdgeIndex ∈ {-1, 1}` defined by the product of the permutation sign matching the
combined tight bases (replacing the leaving label by `k₀` on the active side) and the signs of the
two basis determinants.

## Main definitions

* `Cslib.GameTheory.LemkeHowson.signOfK`: `{-1, 0, 1}` sign of an element of an ordered field.
* `Cslib.GameTheory.LemkeHowson.leaveLabel`: the label dropped on an active half-edge (`k₀` at a
  completely labelled node, otherwise the unique duplicate tight label).
* `Cslib.GameTheory.LemkeHowson.halfEdgeFun`: the label assignment `Fin m ⊕ Fin n → κ` for side
  `false` (`A₁`) or `true` (`A₂`).
* `Cslib.GameTheory.LemkeHowson.halfEdgeIndex`: Shapley's determinant orientation sign
  `∈ {-1, 0, 1}` on `(T₁, T₂, side)`.

## Main results

* `Cslib.GameTheory.LemkeHowson.halfEdgeFun_bijective_of_acl`: active half-edges induce bijections.
* `Cslib.GameTheory.LemkeHowson.halfEdgeIndex_ne_zero`: every active half-edge has sign `±1`.
* `Cslib.GameTheory.LemkeHowson.halfEdgeIndex_true_eq_neg_false`: at every degree-2 node (not
  completely labelled), the two incident half-edges carry opposite signs.
* `Cslib.GameTheory.LemkeHowson.halfEdgeIndex_pivot_left_eq_neg` and
  `Cslib.GameTheory.LemkeHowson.halfEdgeIndex_pivot_right_eq_neg`: moving across any edge of
  `LemkeHowson.graph` flips the half-edge sign, so path endpoints have opposite index.
* `Cslib.GameTheory.LemkeHowson.halfEdgeIndex_zero_zero`: on canonical nonnegativity bases
  (`-I_m`, `-I_n`), the origin `(0, 0)` has orientation `(-1) ^ (m + n)`.

## References

* [L. S. Shapley, *A note on the Lemke–Howson algorithm*][Shapley1974]
* [B. von Stengel, *Equilibrium computation for two-player games in strategic and extensive form*,
  Section 3.12][vonStengel2007]
-/

public section

namespace Cslib.GameTheory.LemkeHowson

open Matrix

section Signs

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Ordered-field sign in `{-1, 0, 1}`. -/
@[expose] def signOfK (c : K) : ℤ :=
  SignType.sign c

theorem signOfK_mul (a b : K) : signOfK (a * b) = signOfK a * signOfK b := by
  dsimp [signOfK]
  rw [sign_mul, SignType.coe_mul]

omit [IsStrictOrderedRing K] in
theorem signOfK_ne_zero {a : K} (ha : a ≠ 0) : signOfK a ≠ 0 := by
  dsimp [signOfK]
  rcases lt_or_gt_of_ne ha with h | h <;> simp [h]

omit [IsStrictOrderedRing K] in
theorem signOfK_sq {a : K} (ha : a ≠ 0) : signOfK a * signOfK a = 1 := by
  dsimp [signOfK]
  rcases lt_or_gt_of_ne ha with h | h <;> simp [h]

theorem signOfK_eq_neg_of_mul_lt_zero {a b : K} (h : a * b < 0) :
    signOfK b = -signOfK a := by
  have ha : a ≠ 0 := fun ha0 => by simp [ha0] at h
  have hmul : signOfK (a * b) = -1 := by
    dsimp [signOfK]
    simp [h]
  rw [signOfK_mul] at hmul
  calc signOfK b = 1 * signOfK b := (one_mul _).symm
    _ = (signOfK a * signOfK a) * signOfK b := by rw [signOfK_sq ha]
    _ = signOfK a * (signOfK a * signOfK b) := mul_assoc _ _ _
    _ = signOfK a * (-1) := by rw [hmul]
    _ = -signOfK a := mul_neg_one _

theorem signOfK_intCast (z : ℤ) : signOfK (z : K) = z.sign := by
  dsimp [signOfK]
  rw [sign_intCast, ← Int.sign_eq_sign]

theorem signOfK_neg_one_pow (k : ℕ) : signOfK ((-1 : K) ^ k) = (-1 : ℤ) ^ k := by
  dsimp [signOfK]
  rw [sign_pow, SignType.coe_pow]
  have : (SignType.sign (-1 : K) : ℤ) = -1 := by
    rw [show (-1 : K) = ((-1 : ℤ) : K) by simp, sign_intCast, ← Int.sign_eq_sign]
    rfl
  rw [this]
end Signs

section HalfEdge

variable {κ : Type*} [Fintype κ] [DecidableEq κ] [LinearOrder κ]

/-- The label dropped when leaving `(T₁, T₂)`: `k₀` when `k₀ ∈ T₁ ∪ T₂` (the completely labelled
case), and otherwise the minimum element of `T₁ ∩ T₂` (the unique duplicate label when `k₀`-almost
completely labelled). -/
@[expose] def leaveLabel (T₁ T₂ : Finset κ) (k₀ : κ) : κ :=
  if k₀ ∈ T₁ ∪ T₂ then k₀
  else if hne : (T₁ ∩ T₂).Nonempty then (T₁ ∩ T₂).min' hne else k₀

/-- The label assignment `Fin m ⊕ Fin n → κ` attached to half-edge `(T₁, T₂, side)`: it enumerates
`T₁` and `T₂` in increasing order, substituting `k₀` for `leaveLabel T₁ T₂ k₀` on the chosen
side. -/
@[expose] def halfEdgeFun {m n : ℕ} (T₁ T₂ : Finset κ) (hT₁ : T₁.card = m) (hT₂ : T₂.card = n)
    (k₀ : κ) (side : Bool) : Fin m ⊕ Fin n → κ :=
  let ord₁ := (T₁.orderIsoOfFin hT₁).toEquiv
  let ord₂ := (T₂.orderIsoOfFin hT₂).toEquiv
  let l := leaveLabel T₁ T₂ k₀
  match side with
  | false => Sum.elim (fun i => if (ord₁ i : κ) = l then k₀ else (ord₁ i : κ))
      (fun j => (ord₂ j : κ))
  | true => Sum.elim (fun i => (ord₁ i : κ))
      (fun j => if (ord₂ j : κ) = l then k₀ else (ord₂ j : κ))

omit [LinearOrder κ] in
private lemma card_inter_eq_one_of_acl {m n : ℕ} (hcard : Fintype.card κ = m + n)
    {T₁ T₂ : Finset κ} (hT₁ : T₁.card = m) (hT₂ : T₂.card = n) {k₀ : κ}
    (hacl : ∀ k, k ≠ k₀ → k ∈ T₁ ∨ k ∈ T₂) (hk₀ : k₀ ∉ T₁ ∪ T₂) :
    (T₁ ∩ T₂).card = 1 := by
  have hunion : T₁ ∪ T₂ = Finset.univ.erase k₀ := by
    ext k
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro (hk | hk) hkeq
      · exact hk₀ (Finset.mem_union.2 (.inl (hkeq ▸ hk)))
      · exact hk₀ (Finset.mem_union.2 (.inr (hkeq ▸ hk)))
    · exact hacl k
  have hucard : (T₁ ∪ T₂).card = m + n - 1 := by
    rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ k₀), Finset.card_univ, hcard]
  have hadd := Finset.card_union_add_card_inter T₁ T₂
  rw [hT₁, hT₂, hucard] at hadd
  have hpos : 1 ≤ m + n := by
    have : 0 < Fintype.card κ := Fintype.card_pos_iff.2 ⟨k₀⟩
    omega
  omega

omit [LinearOrder κ] in
lemma inter_eq_empty_of_mem_union {m n : ℕ} (hcard : Fintype.card κ = m + n)
    {T₁ T₂ : Finset κ} (hT₁ : T₁.card = m) (hT₂ : T₂.card = n) {k₀ : κ}
    (hacl : ∀ k, k ≠ k₀ → k ∈ T₁ ∨ k ∈ T₂) (hk₀ : k₀ ∈ T₁ ∪ T₂) :
    T₁ ∩ T₂ = ∅ := by
  have hunion : T₁ ∪ T₂ = Finset.univ := by
    ext k
    simp only [Finset.mem_univ, iff_true, Finset.mem_union]
    by_cases hk : k = k₀
    · exact hk ▸ Finset.mem_union.1 hk₀
    · exact hacl k hk
  have hadd := Finset.card_union_add_card_inter T₁ T₂
  rw [hT₁, hT₂, hunion, Finset.card_univ, hcard] at hadd
  exact Finset.card_eq_zero.1 (by omega)

lemma mem_inter_of_acl_not_mem {m n : ℕ} (hcard : Fintype.card κ = m + n)
    {T₁ T₂ : Finset κ} (hT₁ : T₁.card = m) (hT₂ : T₂.card = n) {k₀ : κ}
    (hacl : ∀ k, k ≠ k₀ → k ∈ T₁ ∨ k ∈ T₂) (hk₀ : k₀ ∉ T₁ ∪ T₂) :
    leaveLabel T₁ T₂ k₀ ∈ T₁ ∩ T₂ ∧ T₁ ∩ T₂ = {leaveLabel T₁ T₂ k₀} := by
  have h1 := card_inter_eq_one_of_acl hcard hT₁ hT₂ hacl hk₀
  obtain ⟨l, hl⟩ := Finset.card_eq_one.1 h1
  have hne : (T₁ ∩ T₂).Nonempty := ⟨l, by simp [hl]⟩
  have hleave : leaveLabel T₁ T₂ k₀ = l := by
    rw [leaveLabel, ite_eq_right hk₀, dite_eq_left hne]
    simp only [hl, Finset.min'_singleton]
  rw [hleave]
  exact ⟨by simp [hl], hl⟩

private lemma halfEdgeFun_bijective_left {m n : ℕ} (hcard : Fintype.card κ = m + n)
    {T₁ T₂ : Finset κ} (hT₁ : T₁.card = m) (hT₂ : T₂.card = n) {k₀ : κ}
    (hacl : ∀ k, k ≠ k₀ → k ∈ T₁ ∨ k ∈ T₂) (hact : k₀ ∉ T₂) :
    Function.Bijective (halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ false) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp [hcard]⟩
  intro a b hab
  let ord₁ := (T₁.orderIsoOfFin hT₁).toEquiv
  let ord₂ := (T₂.orderIsoOfFin hT₂).toEquiv
  by_cases hk₀ : k₀ ∈ T₁ ∪ T₂
  · have hdisj := inter_eq_empty_of_mem_union hcard hT₁ hT₂ hacl hk₀
    have hleave : leaveLabel T₁ T₂ k₀ = k₀ := by simp [leaveLabel, hk₀]
    have hval : ∀ x, halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ false x =
        Sum.elim (fun i => (ord₁ i : κ)) (fun j => (ord₂ j : κ)) x := by
      intro x
      cases x with
      | inl i =>
        dsimp only [halfEdgeFun]
        rw [hleave]
        dsimp only [Sum.elim_inl]
        split_ifs with h
        · exact h.symm
        · rfl
      | inr j => rfl
    rw [hval a, hval b] at hab
    rcases a with i₁ | j₁ <;> rcases b with i₂ | j₂
    · exact congrArg Sum.inl (ord₁.injective (Subtype.ext hab))
    · exfalso
      simp only [Sum.elim_inl, Sum.elim_inr] at hab
      exact Finset.eq_empty_iff_forall_notMem.1 hdisj (ord₁ i₁ : κ)
        (Finset.mem_inter.2 ⟨(ord₁ i₁).2, hab ▸ (ord₂ j₂).2⟩)
    · exfalso
      simp only [Sum.elim_inr, Sum.elim_inl] at hab
      exact Finset.eq_empty_iff_forall_notMem.1 hdisj (ord₂ j₁ : κ)
        (Finset.mem_inter.2 ⟨hab ▸ (ord₁ i₂).2, (ord₂ j₁).2⟩)
    · exact congrArg Sum.inr (ord₂.injective (Subtype.ext hab))
  · obtain ⟨_, hinter⟩ := mem_inter_of_acl_not_mem hcard hT₁ hT₂ hacl hk₀
    set l := leaveLabel T₁ T₂ k₀
    have hk₀1 : k₀ ∉ T₁ := fun h => hk₀ (Finset.mem_union.2 (.inl h))
    have hnot2 : ∀ i : Fin m, (ord₁ i : κ) ≠ l → (ord₁ i : κ) ∉ T₂ := fun i hi h2 => by
      have hm : (ord₁ i : κ) ∈ T₁ ∩ T₂ := Finset.mem_inter.2 ⟨(ord₁ i).2, h2⟩
      rw [hinter, Finset.mem_singleton] at hm
      exact hi hm
    rcases a with i₁ | j₁ <;> rcases b with i₂ | j₂
    · simp only [halfEdgeFun, Sum.elim_inl] at hab
      split_ifs at hab with h1 h2
      · exact congrArg Sum.inl (ord₁.injective (Subtype.ext (h1.trans h2.symm)))
      · exact absurd (hab.symm ▸ (ord₁ i₂).2) hk₀1
      · exact absurd (hab ▸ (ord₁ i₁).2) hk₀1
      · exact congrArg Sum.inl (ord₁.injective (Subtype.ext hab))
    · simp only [halfEdgeFun, Sum.elim_inl, Sum.elim_inr] at hab
      split_ifs at hab with h1
      · exact absurd (hab ▸ (ord₂ j₂).2) hact
      · exact absurd (hab ▸ (ord₂ j₂).2) (hnot2 i₁ h1)
    · simp only [halfEdgeFun, Sum.elim_inr, Sum.elim_inl] at hab
      split_ifs at hab with h2
      · exact absurd (hab ▸ (ord₂ j₁).2) hact
      · exact absurd (hab ▸ (ord₂ j₁).2) (hnot2 i₂ h2)
    · exact congrArg Sum.inr (ord₂.injective (Subtype.ext hab))

omit [Fintype κ] in
/-- Helper for swapping left and right tight bases along `Equiv.sumComm`. -/
private lemma halfEdgeFun_swap {m n : ℕ} (T₁ T₂ : Finset κ) (hT₁ : T₁.card = m)
    (hT₂ : T₂.card = n) (k₀ : κ) (side : Bool) :
    halfEdgeFun T₂ T₁ hT₂ hT₁ k₀ (!side) =
      halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ side ∘ Equiv.sumComm (Fin n) (Fin m) := by
  funext x
  have hun : T₂ ∪ T₁ = T₁ ∪ T₂ := Finset.union_comm T₂ T₁
  have hin : T₂ ∩ T₁ = T₁ ∩ T₂ := Finset.inter_comm T₂ T₁
  have hleave : leaveLabel T₂ T₁ k₀ = leaveLabel T₁ T₂ k₀ := by
    simp only [leaveLabel, hun, hin]
  cases side <;> rcases x with i | j <;>
    simp only [halfEdgeFun, Bool.not_false, Bool.not_true, Function.comp_apply,
      Equiv.sumComm_apply, Sum.swap_inl, Sum.swap_inr, Sum.elim_inl, Sum.elim_inr]
  · rw [hleave]
  · rw [hleave]

theorem halfEdgeFun_bijective_of_acl {m n : ℕ} (hcard : Fintype.card κ = m + n)
    {T₁ T₂ : Finset κ} (hT₁ : T₁.card = m) (hT₂ : T₂.card = n) {k₀ : κ}
    (hacl : ∀ k, k ≠ k₀ → k ∈ T₁ ∨ k ∈ T₂) {side : Bool}
    (hact : if side then k₀ ∉ T₁ else k₀ ∉ T₂) :
    Function.Bijective (halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ side) := by
  cases side
  · exact halfEdgeFun_bijective_left hcard hT₁ hT₂ hacl hact
  · have hswap := halfEdgeFun_bijective_left (by omega : Fintype.card κ = n + m) hT₂ hT₁
      (fun k hk => (hacl k hk).symm) hact
    have hcomp : halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ true =
        halfEdgeFun T₂ T₁ hT₂ hT₁ k₀ false ∘ (Equiv.sumComm (Fin n) (Fin m)).symm := by
      funext x
      have hs := congrFun (halfEdgeFun_swap T₁ T₂ hT₁ hT₂ k₀ true)
        ((Equiv.sumComm (Fin n) (Fin m)).symm x)
      simpa only [Bool.not_true, Function.comp_apply, Equiv.apply_symm_apply] using hs.symm
    rw [hcomp]
    exact hswap.comp (Equiv.sumComm (Fin n) (Fin m)).symm.bijective

end HalfEdge

section Orientation

variable {ι₁ ι₂ κ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Fintype ι₁] [Fintype ι₂] [Fintype κ] [DecidableEq κ] [LinearOrder κ]

/-- Shapley's orientation sign (`-1` or `1`, or `0` on invalid/inactive inputs) for a half-edge
`(T₁, T₂, side)` of two polyhedra `A₁`, `A₂`. -/
@[expose] noncomputable def halfEdgeIndex {m n : ℕ} (A₁ : Matrix κ ι₁ K) (A₂ : Matrix κ ι₂ K)
    (e₁ : Fin m ≃ ι₁) (e₂ : Fin n ≃ ι₂) (ref : Fin m ⊕ Fin n ≃ κ)
    (T₁ T₂ : Finset κ) (hT₁ : T₁.card = m) (hT₂ : T₂.card = n)
    (k₀ : κ) (side : Bool) : ℤ :=
  open Classical in
  if hbij : Function.Bijective (halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ side) then
    let π : Equiv.Perm (Fin m ⊕ Fin n) := (Equiv.ofBijective _ hbij).trans ref.symm
    let M₁ := A₁.submatrix (fun i => (T₁.orderIsoOfFin hT₁ i : κ)) e₁
    let M₂ := A₂.submatrix (fun j => (T₂.orderIsoOfFin hT₂ j : κ)) e₂
    (Equiv.Perm.sign π : ℤ) * signOfK M₁.det * signOfK M₂.det
  else 0

omit [IsStrictOrderedRing K] [Fintype ι₁] [Fintype ι₂] in
private lemma halfEdgeIndex_swap {m n : ℕ} (A₁ : Matrix κ ι₁ K) (A₂ : Matrix κ ι₂ K)
    (e₁ : Fin m ≃ ι₁) (e₂ : Fin n ≃ ι₂) (ref : Fin m ⊕ Fin n ≃ κ)
    (T₁ T₂ : Finset κ) (hT₁ : T₁.card = m) (hT₂ : T₂.card = n)
    (k₀ : κ) (side : Bool) :
    halfEdgeIndex A₂ A₁ e₂ e₁ ((Equiv.sumComm (Fin n) (Fin m)).trans ref) T₂ T₁ hT₂ hT₁ k₀
        (!side) =
      halfEdgeIndex A₁ A₂ e₁ e₂ ref T₁ T₂ hT₁ hT₂ k₀ side := by
  classical
  have hcomp : halfEdgeFun T₂ T₁ hT₂ hT₁ k₀ (!side) =
      halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ side ∘ Equiv.sumComm (Fin n) (Fin m) :=
    halfEdgeFun_swap T₁ T₂ hT₁ hT₂ k₀ side
  by_cases hbij : Function.Bijective (halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ side)
  · have hbij' : Function.Bijective (halfEdgeFun T₂ T₁ hT₂ hT₁ k₀ (!side)) := by
      rw [hcomp]
      exact hbij.comp (Equiv.sumComm (Fin n) (Fin m)).bijective
    rw [halfEdgeIndex, dite_eq_left hbij', halfEdgeIndex, dite_eq_left hbij]
    dsimp only
    set π : Equiv.Perm (Fin m ⊕ Fin n) := (Equiv.ofBijective _ hbij).trans ref.symm
    set π' : Equiv.Perm (Fin n ⊕ Fin m) :=
      (Equiv.ofBijective _ hbij').trans ((Equiv.sumComm (Fin n) (Fin m)).trans ref).symm
    have hπ : π' = Equiv.permCongr (Equiv.sumComm (Fin m) (Fin n)) π := by
      ext x
      simp only [π', π, Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.ofBijective_apply,
        hcomp, Function.comp_apply, Equiv.permCongr_apply, Equiv.sumComm_symm,
        Equiv.sumComm_apply]
    rw [hπ, Equiv.Perm.sign_permCongr]
    ring
  · have hbij' : ¬ Function.Bijective (halfEdgeFun T₂ T₁ hT₂ hT₁ k₀ (!side)) := by
      intro h
      have hcomp' : halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ side =
          halfEdgeFun T₂ T₁ hT₂ hT₁ k₀ (!side) ∘ (Equiv.sumComm (Fin n) (Fin m)).symm := by
        funext x
        have hs := congrFun hcomp ((Equiv.sumComm (Fin n) (Fin m)).symm x)
        simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hs.symm
      exact hbij (hcomp' ▸ h.comp (Equiv.sumComm (Fin n) (Fin m)).symm.bijective)
    rw [halfEdgeIndex, dite_eq_right hbij', halfEdgeIndex, dite_eq_right hbij]

omit [IsStrictOrderedRing K] in
/-- Every active half-edge of a `LemkeHowson.Node` has nonzero (`±1`) orientation index. -/
theorem halfEdgeIndex_ne_zero {m n : ℕ}
    {A₁ : Matrix κ ι₁ K} {b₁ : κ → K} {A₂ : Matrix κ ι₂ K} {b₂ : κ → K}
    (e₁ : Fin m ≃ ι₁) (e₂ : Fin n ≃ ι₂) (ref : Fin m ⊕ Fin n ≃ κ)
    (hcard : Fintype.card κ = m + n) {k₀ : κ} (p : Node A₁ b₁ A₂ b₂ k₀)
    {hT₁ : (tightRows A₁ b₁ p.x).card = m} {hT₂ : (tightRows A₂ b₂ p.y).card = n}
    {side : Bool} (hact : if side then k₀ ∉ tightRows A₁ b₁ p.x else k₀ ∉ tightRows A₂ b₂ p.y) :
    halfEdgeIndex A₁ A₂ e₁ e₂ ref (tightRows A₁ b₁ p.x) (tightRows A₂ b₂ p.y) hT₁ hT₂ k₀ side ≠
      0 := by
  classical
  have hbij := halfEdgeFun_bijective_of_acl hcard hT₁ hT₂ p.almostCompletelyLabeled hact
  rw [halfEdgeIndex, dite_eq_left hbij]
  dsimp only
  have hdet₁ : (A₁.submatrix (fun i => (tightRows A₁ b₁ p.x |>.orderIsoOfFin hT₁ i : κ)) e₁).det
      ≠ 0 := by
    have hsub : A₁.submatrix (fun i => (tightRows A₁ b₁ p.x |>.orderIsoOfFin hT₁ i : κ)) e₁ =
        (A₁.submatrix
          (fun i => (tightRows A₁ b₁ p.x |>.orderIsoOfFin hT₁ (e₁.symm i) : κ)) id).submatrix
          e₁ e₁ := by
      ext i j; simp
    rw [hsub, Matrix.det_submatrix_equiv_self]
    exact p.isVertex_x.det_submatrix_ne_zero
      (e₁.symm.trans (tightRows A₁ b₁ p.x |>.orderIsoOfFin hT₁).toEquiv)
  have hdet₂ : (A₂.submatrix (fun j => (tightRows A₂ b₂ p.y |>.orderIsoOfFin hT₂ j : κ)) e₂).det
      ≠ 0 := by
    have hsub : A₂.submatrix (fun j => (tightRows A₂ b₂ p.y |>.orderIsoOfFin hT₂ j : κ)) e₂ =
        (A₂.submatrix
          (fun j => (tightRows A₂ b₂ p.y |>.orderIsoOfFin hT₂ (e₂.symm j) : κ)) id).submatrix
          e₂ e₂ := by
      ext i j; simp
    rw [hsub, Matrix.det_submatrix_equiv_self]
    exact p.isVertex_y.det_submatrix_ne_zero
      (e₂.symm.trans (tightRows A₂ b₂ p.y |>.orderIsoOfFin hT₂).toEquiv)
  exact mul_ne_zero (mul_ne_zero (by simp [Units.ne_zero]) (signOfK_ne_zero hdet₁))
    (signOfK_ne_zero hdet₂)

omit [IsStrictOrderedRing K] in
/-- At a non-completely-labelled node (degree `2`), the two incident half-edges carry opposite
orientation indices. -/
theorem halfEdgeIndex_true_eq_neg_false {m n : ℕ}
    {A₁ : Matrix κ ι₁ K} {b₁ : κ → K} {A₂ : Matrix κ ι₂ K} {b₂ : κ → K}
    (e₁ : Fin m ≃ ι₁) (e₂ : Fin n ≃ ι₂) (ref : Fin m ⊕ Fin n ≃ κ)
    (hcard : Fintype.card κ = m + n) {k₀ : κ} (p : Node A₁ b₁ A₂ b₂ k₀)
    {hT₁ : (tightRows A₁ b₁ p.x).card = m} {hT₂ : (tightRows A₂ b₂ p.y).card = n}
    (hncl : ¬ CompletelyLabeled A₁ b₁ A₂ b₂ p.x p.y) :
    halfEdgeIndex A₁ A₂ e₁ e₂ ref (tightRows A₁ b₁ p.x) (tightRows A₂ b₂ p.y) hT₁ hT₂ k₀ true =
      -halfEdgeIndex A₁ A₂ e₁ e₂ ref (tightRows A₁ b₁ p.x) (tightRows A₂ b₂ p.y) hT₁ hT₂ k₀
        false := by
  classical
  set T₁ := tightRows A₁ b₁ p.x
  set T₂ := tightRows A₂ b₂ p.y
  have hk₀ : k₀ ∉ T₁ ∪ T₂ := by
    intro hmem
    apply hncl
    rw [completelyLabeled_iff]
    intro k
    by_cases hk : k = k₀
    · exact Finset.mem_union.1 (hk ▸ hmem)
    · exact p.almostCompletelyLabeled k hk
  have hk₀1 : k₀ ∉ T₁ := fun h => hk₀ (Finset.mem_union.2 (.inl h))
  have hk₀2 : k₀ ∉ T₂ := fun h => hk₀ (Finset.mem_union.2 (.inr h))
  have hbij_f :=
    halfEdgeFun_bijective_of_acl hcard hT₁ hT₂ p.almostCompletelyLabeled (side := false) hk₀2
  have hbij_t :=
    halfEdgeFun_bijective_of_acl hcard hT₁ hT₂ p.almostCompletelyLabeled (side := true) hk₀1
  obtain ⟨hmem, hinter⟩ := mem_inter_of_acl_not_mem hcard hT₁ hT₂ p.almostCompletelyLabeled hk₀
  set l := leaveLabel T₁ T₂ k₀
  have hl₁ : l ∈ T₁ := (Finset.mem_inter.1 hmem).1
  have hl₂ : l ∈ T₂ := (Finset.mem_inter.1 hmem).2
  let ord₁ := (T₁.orderIsoOfFin hT₁).toEquiv
  let ord₂ := (T₂.orderIsoOfFin hT₂).toEquiv
  set a : Fin m := ord₁.symm ⟨l, hl₁⟩
  set b : Fin n := ord₂.symm ⟨l, hl₂⟩
  have ha : (ord₁ a : κ) = l := congrArg Subtype.val (ord₁.apply_symm_apply ⟨l, hl₁⟩)
  have hb : (ord₂ b : κ) = l := congrArg Subtype.val (ord₂.apply_symm_apply ⟨l, hl₂⟩)
  have hswap_fun : halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ true =
      halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ false ∘ Equiv.swap (Sum.inl a) (Sum.inr b) := by
    funext x
    rcases x with i | j
    · by_cases hi : i = a
      · subst hi
        simp only [halfEdgeFun, Function.comp_apply, Equiv.swap_apply_left, Sum.elim_inl,
          Sum.elim_inr]
        exact ha.trans hb.symm
      · have hne_l : (ord₁ i : κ) ≠ l := fun h =>
          hi (ord₁.injective (Subtype.ext (h.trans ha.symm)))
        have hne_swap : (Sum.inl i : Fin m ⊕ Fin n) ≠ Sum.inl a := fun h => hi (Sum.inl.inj h)
        have hne_swap' : (Sum.inl i : Fin m ⊕ Fin n) ≠ Sum.inr b := by simp
        simp only [halfEdgeFun, Function.comp_apply,
          Equiv.swap_apply_of_ne_of_ne hne_swap hne_swap', Sum.elim_inl]
        rw [ite_eq_right hne_l]
    · by_cases hj : j = b
      · subst hj
        dsimp only [halfEdgeFun, Function.comp_apply]
        rw [Equiv.swap_apply_right, Sum.elim_inr, Sum.elim_inl]
        change (if (ord₂ b : κ) = l then k₀ else (ord₂ b : κ)) =
          if (ord₁ a : κ) = l then k₀ else (ord₁ a : κ)
        rw [hb, ha]
      · have hne_l : (ord₂ j : κ) ≠ l := fun h =>
          hj (ord₂.injective (Subtype.ext (h.trans hb.symm)))
        have hne_swap : (Sum.inr j : Fin m ⊕ Fin n) ≠ Sum.inl a := by simp
        have hne_swap' : (Sum.inr j : Fin m ⊕ Fin n) ≠ Sum.inr b := fun h => hj (Sum.inr.inj h)
        simp only [halfEdgeFun, Function.comp_apply,
          Equiv.swap_apply_of_ne_of_ne hne_swap hne_swap', Sum.elim_inr]
        rw [ite_eq_right hne_l]
  rw [halfEdgeIndex, dite_eq_left hbij_t, halfEdgeIndex, dite_eq_left hbij_f]
  dsimp only
  set π_f := (Equiv.ofBijective _ hbij_f).trans ref.symm
  set π_t := (Equiv.ofBijective _ hbij_t).trans ref.symm
  have hπ : π_t = (Equiv.swap (Sum.inl a) (Sum.inr b)).trans π_f := by
    ext x
    simp only [π_t, π_f, Equiv.trans_apply, Equiv.ofBijective_apply, hswap_fun, Function.comp_apply]
  have hsign : (Equiv.Perm.sign π_t : ℤ) = -(Equiv.Perm.sign π_f : ℤ) := by
    have hmul : ((Equiv.swap (Sum.inl a) (Sum.inr b)).trans π_f :
        Equiv.Perm (Fin m ⊕ Fin n)) = π_f * Equiv.swap (Sum.inl a) (Sum.inr b) := rfl
    rw [hπ, hmul, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by simp)]
    simp [Units.val_neg]
  change (Equiv.Perm.sign π_t : ℤ) * _ * _ = -((Equiv.Perm.sign π_f : ℤ) * _ * _)
  rw [hsign]
  ring

omit [Fintype κ] [LinearOrder κ] in
private lemma exists_unique_entering_of_pivot {m : ℕ} {T₁ T₁' : Finset κ} {l : κ}
    (hT₁ : T₁.card = m) (hT₁' : T₁'.card = m) (hl : l ∈ T₁) (_hl' : l ∉ T₁')
    (hsub : T₁.erase l ⊆ T₁') :
    ∃ (l' : κ) (_hl'mem : l' ∈ T₁'), T₁.erase l = T₁'.erase l' := by
  have hcard_erase : (T₁.erase l).card = m - 1 := by
    rw [Finset.card_erase_of_mem hl, hT₁]
  have hcard_sdiff : (T₁' \ T₁.erase l).card = 1 := by
    have hadd := Finset.card_sdiff_add_card_inter T₁' (T₁.erase l)
    have hinter : T₁' ∩ T₁.erase l = T₁.erase l := Finset.inter_eq_right.2 hsub
    rw [hinter, hT₁', hcard_erase] at hadd
    have hmpos : 1 ≤ m := by
      rw [← hT₁]
      exact Finset.card_pos.2 ⟨l, hl⟩
    omega
  obtain ⟨l', hl'sdiff⟩ := Finset.card_eq_one.1 hcard_sdiff
  have hl'mem : l' ∈ T₁' \ T₁.erase l := by simp [hl'sdiff]
  refine ⟨l', (Finset.mem_sdiff.1 hl'mem).1, ?_⟩
  ext k
  simp only [Finset.mem_erase]
  constructor
  · intro hk
    refine ⟨?_, hsub (Finset.mem_erase.2 hk)⟩
    rintro rfl
    exact (Finset.mem_sdiff.1 hl'mem).2 (Finset.mem_erase.2 hk)
  · rintro ⟨hkne, hkT'⟩
    by_contra hnot
    have hk_sdiff : k ∈ T₁' \ T₁.erase l := by
      refine Finset.mem_sdiff.2 ⟨hkT', fun hm => hnot (Finset.mem_erase.1 hm)⟩
    rw [hl'sdiff, Finset.mem_singleton] at hk_sdiff
    exact hkne hk_sdiff

private lemma leaveLabel_eq_dropped {m n : ℕ} (hcard : Fintype.card κ = m + n)
    {T₁ T₁' T₂ : Finset κ} (hT₁ : T₁.card = m) (hT₂ : T₂.card = n) {k₀ l : κ}
    (hacl : ∀ k, k ≠ k₀ → k ∈ T₁ ∨ k ∈ T₂) (hacl' : ∀ k, k ≠ k₀ → k ∈ T₁' ∨ k ∈ T₂)
    (hk₀2 : k₀ ∉ T₂) (hl : l ∈ T₁) (hl' : l ∉ T₁') :
    leaveLabel T₁ T₂ k₀ = l := by
  have hl_or : l ≠ k₀ → l ∈ T₂ := fun hne => (hacl' l hne).resolve_left hl'
  by_cases hk₀1 : k₀ ∈ T₁
  · have hmem_u : k₀ ∈ T₁ ∪ T₂ := Finset.mem_union.2 (.inl hk₀1)
    have hdisj := inter_eq_empty_of_mem_union hcard hT₁ hT₂ hacl hmem_u
    have hl_not2 : l ∉ T₂ := fun hl2 =>
      Finset.eq_empty_iff_forall_notMem.1 hdisj l (Finset.mem_inter.2 ⟨hl, hl2⟩)
    have hl_eq : l = k₀ := by
      by_contra hne
      exact hl_not2 (hl_or hne)
    simp [leaveLabel, hmem_u, hl_eq]
  · have hk₀ : k₀ ∉ T₁ ∪ T₂ := fun h => (Finset.mem_union.1 h).elim hk₀1 hk₀2
    have hne_k₀ : l ≠ k₀ := fun h => hk₀1 (h ▸ hl)
    obtain ⟨_, hinter⟩ := mem_inter_of_acl_not_mem hcard hT₁ hT₂ hacl hk₀
    have hl_inter : l ∈ T₁ ∩ T₂ := Finset.mem_inter.2 ⟨hl, hl_or hne_k₀⟩
    rw [hinter, Finset.mem_singleton] at hl_inter
    exact hl_inter.symm

/-- Moving across a left (`A₁`) pivot edge of `LemkeHowson.graph` reverses
`halfEdgeIndex · false`. -/
theorem halfEdgeIndex_pivot_left_eq_neg {m n : ℕ}
    {A₁ : Matrix κ ι₁ K} {b₁ : κ → K} {A₂ : Matrix κ ι₂ K} {b₂ : κ → K}
    (hnd₁ : IsNondegenerateSystem A₁ b₁)
    (e₁ : Fin m ≃ ι₁) (e₂ : Fin n ≃ ι₂) (ref : Fin m ⊕ Fin n ≃ κ)
    (hcard : Fintype.card κ = m + n) {k₀ : κ} {p q : Node A₁ b₁ A₂ b₂ k₀}
    {hT₁p : (tightRows A₁ b₁ p.x).card = m} {hT₁q : (tightRows A₁ b₁ q.x).card = m}
    {hT₂p : (tightRows A₂ b₂ p.y).card = n} {hT₂q : (tightRows A₂ b₂ q.y).card = n}
    (hqy : p.y = q.y) (hne : p.x ≠ q.x) (hadj : (graph A₁ b₁ A₂ b₂ k₀).Adj p q) :
    halfEdgeIndex A₁ A₂ e₁ e₂ ref (tightRows A₁ b₁ q.x) (tightRows A₂ b₂ q.y) hT₁q hT₂q k₀
        false =
      -halfEdgeIndex A₁ A₂ e₁ e₂ ref (tightRows A₁ b₁ p.x) (tightRows A₂ b₂ p.y) hT₁p hT₂p k₀
        false := by
  classical
  have hvertexAdj : VertexAdj A₁ b₁ p.x q.x := by
    rcases (graph_adj.1 hadj) with ⟨hx, _⟩ | ⟨_, ha⟩
    · exact absurd hx hne
    · exact ha
  set T₁p := tightRows A₁ b₁ p.x
  set T₁q := tightRows A₁ b₁ q.x
  set T₂p := tightRows A₂ b₂ p.y
  have hacl_q : ∀ k, k ≠ k₀ → k ∈ T₁q ∨ k ∈ T₂p := by
    intro k hk
    simpa only [T₂p, hqy] using q.almostCompletelyLabeled k hk
  have hnot_sub : ¬ T₁p ⊆ T₁q :=
    fun h => hne (p.isVertex_x.eq_of_tightRows_subset h).symm
  obtain ⟨l, hlp, hlq⟩ := Finset.not_subset.1 hnot_sub
  have hsub : T₁p.erase l ⊆ T₁q := by
    have hinter_sub : T₁p ∩ T₁q ⊆ T₁p.erase l := fun k hk =>
      Finset.mem_erase.2 ⟨fun h => hlq (h ▸ (Finset.mem_inter.1 hk).2), (Finset.mem_inter.1 hk).1⟩
    rw [vertexAdj_iff] at hvertexAdj
    rcases hvertexAdj with ⟨-, -, -, hcard_inter⟩
    have hcard_inter' : Fintype.card ι₁ ≤ (T₁p ∩ T₁q).card + 1 := hcard_inter
    have hcard_i : Fintype.card ι₁ = m := by
      have := p.isVertex_x.card_tightRows hnd₁
      omega
    have heq : T₁p ∩ T₁q = T₁p.erase l := Finset.eq_of_subset_of_card_le hinter_sub (by
      rw [Finset.card_erase_of_mem hlp, hT₁p]; omega)
    exact heq ▸ Finset.inter_subset_right
  obtain ⟨l', hl'q, herase⟩ := exists_unique_entering_of_pivot hT₁p hT₁q hlp hlq hsub
  have hl'p : l' ∉ T₁p := by
    intro hmem
    have hne_ll' : l' ≠ l := fun h => hlq (h ▸ hl'q)
    have hmem_e : l' ∈ T₁p.erase l := Finset.mem_erase.2 ⟨hne_ll', hmem⟩
    rw [herase] at hmem_e
    exact (Finset.notMem_erase l' T₁q) hmem_e
  have hk₀2 : k₀ ∉ T₂p := by
    intro hk2
    have hmem_u : k₀ ∈ T₁p ∪ T₂p := Finset.mem_union.2 (.inr hk2)
    have hdisj := inter_eq_empty_of_mem_union hcard hT₁p hT₂p p.almostCompletelyLabeled hmem_u
    have hl_not2 : l ∉ T₂p := fun hl2 =>
      Finset.eq_empty_iff_forall_notMem.1 hdisj l (Finset.mem_inter.2 ⟨hlp, hl2⟩)
    have hne_k₀ : l ≠ k₀ := fun h => hl_not2 (h ▸ hk2)
    rcases hacl_q l hne_k₀ with h | h
    · exact hlq h
    · exact hl_not2 h
  have hleave_p : leaveLabel T₁p T₂p k₀ = l :=
    leaveLabel_eq_dropped hcard hT₁p hT₂p p.almostCompletelyLabeled hacl_q hk₀2 hlp hlq
  have hleave_q : leaveLabel T₁q T₂p k₀ = l' :=
    leaveLabel_eq_dropped hcard hT₁q hT₂p hacl_q p.almostCompletelyLabeled hk₀2 hl'q hl'p
  suffices h : ∀ (T₂q : Finset κ) (hT₂q' : T₂q.card = n), T₂q = T₂p →
      halfEdgeIndex A₁ A₂ e₁ e₂ ref T₁q T₂q hT₁q hT₂q' k₀ false =
        -halfEdgeIndex A₁ A₂ e₁ e₂ ref T₁p T₂p hT₁p hT₂p k₀ false from
    h (tightRows A₂ b₂ q.y) hT₂q (by rw [← hqy])
  rintro _ hT₂q' rfl
  have hbij_p :=
    halfEdgeFun_bijective_of_acl hcard hT₁p hT₂p p.almostCompletelyLabeled (side := false) hk₀2
  have hbij_q :=
    halfEdgeFun_bijective_of_acl hcard hT₁q hT₂p hacl_q (side := false) hk₀2
  rw [halfEdgeIndex, dite_eq_left hbij_q, halfEdgeIndex, dite_eq_left hbij_p]
  dsimp only
  let ord₁p := (T₁p.orderIsoOfFin hT₁p).toEquiv
  let ord₁q := (T₁q.orderIsoOfFin hT₁q).toEquiv
  let e_piv : Fin m ≃ T₁q := pivotBasisEquiv ord₁p hlp hl'q herase
  set σ₁ : Equiv.Perm (Fin m) := e_piv.trans ord₁q.symm
  have hfun_comp : ∀ x : Fin m ⊕ Fin n,
      halfEdgeFun T₁q T₂p hT₁q hT₂q' k₀ false (Equiv.sumCongr σ₁ (Equiv.refl (Fin n)) x) =
        halfEdgeFun T₁p T₂p hT₁p hT₂p k₀ false x := by
    intro x
    rcases x with i | j
    · dsimp only [Equiv.sumCongr_apply, Sum.map_inl, halfEdgeFun, Sum.elim_inl]
      rw [hleave_p, hleave_q]
      change (if (ord₁q (σ₁ i) : κ) = l' then k₀ else (ord₁q (σ₁ i) : κ)) =
        if (ord₁p i : κ) = l then k₀ else (ord₁p i : κ)
      have he_eq : (ord₁q (σ₁ i) : κ) = (e_piv i : κ) :=
        congrArg Subtype.val (ord₁q.apply_symm_apply (e_piv i))
      rw [he_eq, show (e_piv i : κ) = if i = ord₁p.symm ⟨l, hlp⟩ then l' else (ord₁p i : κ) from
        coe_pivotBasisEquiv_apply ord₁p hlp hl'q herase i]
      by_cases hi : i = ord₁p.symm ⟨l, hlp⟩
      · have hor : (ord₁p i : κ) = l := by
          subst hi; exact congrArg Subtype.val (ord₁p.apply_symm_apply ⟨l, hlp⟩)
        rw [ite_eq_left hi, ite_eq_left hor]
        simp only [↓reduceIte]
      · have hor_ne_l : (ord₁p i : κ) ≠ l := fun h => by
          apply hi; apply ord₁p.injective; apply Subtype.ext
          simpa only [Equiv.apply_symm_apply] using h
        have hor_ne_l' : (ord₁p i : κ) ≠ l' := by
          have hm : (ord₁p i : κ) ∈ T₁p.erase l := Finset.mem_erase.2 ⟨hor_ne_l, (ord₁p i).2⟩
          rw [herase] at hm
          exact (Finset.mem_erase.1 hm).1
        simp [hi, hor_ne_l, hor_ne_l']
    · rfl
  set π_p := (Equiv.ofBijective _ hbij_p).trans ref.symm
  set π_q := (Equiv.ofBijective _ hbij_q).trans ref.symm
  have hπ : π_p = (Equiv.sumCongr σ₁ (Equiv.refl (Fin n))).trans π_q := by
    ext x
    simp only [π_p, π_q, Equiv.trans_apply, Equiv.ofBijective_apply, hfun_comp]
  have hsign_pi : (Equiv.Perm.sign π_p : ℤ) =
      (Equiv.Perm.sign π_q : ℤ) * (Equiv.Perm.sign σ₁ : ℤ) := by
    rw [hπ]
    change (Equiv.Perm.sign (π_q * Equiv.sumCongr σ₁ (Equiv.refl (Fin n))) : ℤ) = _
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_refl, mul_one]
    simp [Units.val_mul]
  let M₁p := A₁.submatrix (fun i => (T₁p.orderIsoOfFin hT₁p i : κ)) e₁
  let M₁q := A₁.submatrix (fun i => (T₁q.orderIsoOfFin hT₁q i : κ)) e₁
  let M₂ := A₂.submatrix (fun j => (T₂p.orderIsoOfFin hT₂p j : κ)) e₂
  let e₁' : ι₁ ≃ T₁p := e₁.symm.trans ord₁p
  let e₂' : ι₁ ≃ T₁q := e₁.symm.trans ord₁q
  have hdet_lt := p.isVertex_x.det_submatrix_pivot_mul_lt_zero q.isVertex_x hne hlp hl'q herase
    e₁' e₂'
  dsimp only at hdet_lt
  have hM₁p_det : (A₁.submatrix (fun i => (e₁' i : κ)) id).det = M₁p.det := by
    have hsub : M₁p = (A₁.submatrix (fun i => (e₁' i : κ)) id).submatrix e₁ e₁ := by
      ext i j; simp [M₁p, e₁', ord₁p]
    rw [hsub, Matrix.det_submatrix_equiv_self]
  have hM₁q_det : (A₁.submatrix (fun i => (e₂' i : κ)) id).det = M₁q.det := by
    have hsub : M₁q = (A₁.submatrix (fun i => (e₂' i : κ)) id).submatrix e₁ e₁ := by
      ext i j; simp [M₁q, e₂', ord₁q]
    rw [hsub, Matrix.det_submatrix_equiv_self]
  have hperm_eq : (pivotBasisEquiv e₁' hlp hl'q herase).trans e₂'.symm =
      e₁.permCongr σ₁ := by
    ext i
    rw [Equiv.trans_apply, Equiv.permCongr_apply]
    change e₁ (ord₁q.symm (pivotBasisEquiv e₁' hlp hl'q herase i)) =
      e₁ (ord₁q.symm (e_piv (e₁.symm i)))
    apply congrArg (fun z => e₁ (ord₁q.symm z))
    apply Subtype.ext
    rw [coe_pivotBasisEquiv_apply, coe_pivotBasisEquiv_apply]
    have hsym : e₁'.symm ⟨l, hlp⟩ = e₁ (ord₁p.symm ⟨l, hlp⟩) := rfl
    rw [hsym]
    by_cases hi : e₁.symm i = ord₁p.symm ⟨l, hlp⟩
    · have hi' : i = e₁ (ord₁p.symm ⟨l, hlp⟩) := (Equiv.symm_apply_eq e₁).1 hi
      rw [ite_eq_left hi', ite_eq_left hi]
    · have hi' : i ≠ e₁ (ord₁p.symm ⟨l, hlp⟩) := fun h => hi ((Equiv.symm_apply_eq e₁).2 h)
      rw [ite_eq_right hi', ite_eq_right hi]
      rfl
  rw [hM₁p_det, hM₁q_det, hperm_eq, Equiv.Perm.sign_permCongr] at hdet_lt
  have hsign_det : (Equiv.Perm.sign σ₁ : ℤ) * (signOfK M₁p.det * signOfK M₁q.det) = -1 := by
    have hneg1 : signOfK (((Equiv.Perm.sign σ₁ : ℤ) : K) * (M₁p.det * M₁q.det)) = -1 := by
      dsimp [signOfK]
      rw [sign_neg hdet_lt]
      rfl
    rw [signOfK_mul, signOfK_mul, signOfK_intCast] at hneg1
    have hσ_sign : (Equiv.Perm.sign σ₁ : ℤ).sign = (Equiv.Perm.sign σ₁ : ℤ) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ₁) with h | h <;> simp [h]
    simpa only [hσ_sign] using hneg1
  have hM₂_ne : M₂.det ≠ 0 := by
    have hsub : M₂ = (A₂.submatrix
        (fun j => (T₂p.orderIsoOfFin hT₂p (e₂.symm j) : κ)) id).submatrix e₂ e₂ := by
      ext i j; simp [M₂]
    rw [hsub, Matrix.det_submatrix_equiv_self]
    exact p.isVertex_y.det_submatrix_ne_zero (e₂.symm.trans (T₂p.orderIsoOfFin hT₂p).toEquiv)
  have hM₁q_ne : M₁q.det ≠ 0 := by
    rw [← hM₁q_det]
    exact q.isVertex_x.det_submatrix_ne_zero e₂'
  set idx_p : ℤ := (Equiv.Perm.sign π_p : ℤ) * signOfK M₁p.det * signOfK M₂.det
  set idx_q : ℤ := (Equiv.Perm.sign π_q : ℤ) * signOfK M₁q.det * signOfK M₂.det
  have hidx_q_sq : idx_q * idx_q = 1 := by
    have hπ_sq : (Equiv.Perm.sign π_q : ℤ) * (Equiv.Perm.sign π_q : ℤ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign π_q) with h | h <;> simp [h]
    calc idx_q * idx_q
        = ((Equiv.Perm.sign π_q : ℤ) * (Equiv.Perm.sign π_q : ℤ)) *
            (signOfK M₁q.det * signOfK M₁q.det) * (signOfK M₂.det * signOfK M₂.det) := by ring
      _ = 1 * 1 * 1 := by rw [hπ_sq, signOfK_sq hM₁q_ne, signOfK_sq hM₂_ne]
      _ = 1 := by ring
  have hprod : idx_p * idx_q = -1 := by
    have hπ_sq : (Equiv.Perm.sign π_q : ℤ) * (Equiv.Perm.sign π_q : ℤ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign π_q) with h | h <;> simp [h]
    calc idx_p * idx_q
        = ((Equiv.Perm.sign π_q : ℤ) * (Equiv.Perm.sign π_q : ℤ)) *
            ((Equiv.Perm.sign σ₁ : ℤ) * (signOfK M₁p.det * signOfK M₁q.det)) *
            (signOfK M₂.det * signOfK M₂.det) := by
          dsimp only [idx_p, idx_q]
          rw [hsign_pi]
          ring
      _ = 1 * (-1) * 1 := by rw [hπ_sq, hsign_det, signOfK_sq hM₂_ne]
      _ = -1 := by ring
  change idx_q = -idx_p
  calc idx_q = -(idx_p * idx_q) * idx_q := by rw [hprod]; ring
    _ = -idx_p * (idx_q * idx_q) := by ring
    _ = -idx_p := by rw [hidx_q_sq, mul_one]

/-- Moving across a right (`A₂`) pivot edge of `LemkeHowson.graph` reverses
`halfEdgeIndex · true`. -/
theorem halfEdgeIndex_pivot_right_eq_neg {m n : ℕ}
    {A₁ : Matrix κ ι₁ K} {b₁ : κ → K} {A₂ : Matrix κ ι₂ K} {b₂ : κ → K}
    (hnd₂ : IsNondegenerateSystem A₂ b₂)
    (e₁ : Fin m ≃ ι₁) (e₂ : Fin n ≃ ι₂) (ref : Fin m ⊕ Fin n ≃ κ)
    (hcard : Fintype.card κ = m + n) {k₀ : κ} {p q : Node A₁ b₁ A₂ b₂ k₀}
    {hT₁p : (tightRows A₁ b₁ p.x).card = m} {hT₁q : (tightRows A₁ b₁ q.x).card = m}
    {hT₂p : (tightRows A₂ b₂ p.y).card = n} {hT₂q : (tightRows A₂ b₂ q.y).card = n}
    (hpx : p.x = q.x) (hne : p.y ≠ q.y) (hadj : (graph A₁ b₁ A₂ b₂ k₀).Adj p q) :
    halfEdgeIndex A₁ A₂ e₁ e₂ ref (tightRows A₁ b₁ q.x) (tightRows A₂ b₂ q.y) hT₁q hT₂q k₀
        true =
      -halfEdgeIndex A₁ A₂ e₁ e₂ ref (tightRows A₁ b₁ p.x) (tightRows A₂ b₂ p.y) hT₁p hT₂p k₀
        true := by
  let p' : Node A₂ b₂ A₁ b₁ k₀ :=
    ⟨p.y, p.x, p.isVertex_y, p.isVertex_x, fun j hj => (p.almostCompletelyLabeled j hj).symm⟩
  let q' : Node A₂ b₂ A₁ b₁ k₀ :=
    ⟨q.y, q.x, q.isVertex_y, q.isVertex_x, fun j hj => (q.almostCompletelyLabeled j hj).symm⟩
  have hadj' : (graph A₂ b₂ A₁ b₁ k₀).Adj p' q' := by
    rcases (graph_adj.1 hadj) with ⟨hx, ha⟩ | ⟨hy, _⟩
    · exact graph_adj.2 (.inr ⟨hx, ha⟩)
    · exact absurd hy.symm (fun h => hne h.symm)
  have hsw_p := halfEdgeIndex_swap A₁ A₂ e₁ e₂ ref (tightRows A₁ b₁ p.x) (tightRows A₂ b₂ p.y)
    hT₁p hT₂p k₀ true
  have hsw_q := halfEdgeIndex_swap A₁ A₂ e₁ e₂ ref (tightRows A₁ b₁ q.x) (tightRows A₂ b₂ q.y)
    hT₁q hT₂q k₀ true
  simp only [Bool.not_true] at hsw_p hsw_q
  rw [← hsw_p, ← hsw_q]
  exact halfEdgeIndex_pivot_left_eq_neg hnd₂ e₂ e₁ ((Equiv.sumComm (Fin n) (Fin m)).trans ref)
    (by omega) (p := p') (q := q') (hT₁p := hT₂p) (hT₁q := hT₂q) (hT₂p := hT₁p) (hT₂q := hT₁q)
    hpx hne hadj'

omit [Fintype ι₁] [Fintype ι₂] in
/-- When `T₁` and `T₂` select the `Sum.inl` and `Sum.inr` blocks of `ref`, and the corresponding
basis submatrices are `-1`, the orientation index equals `(-1) ^ (m + n)` for every `k₀` and
`side`. -/
theorem halfEdgeIndex_zero_zero {m n : ℕ}
    (A₁ : Matrix κ ι₁ K) (A₂ : Matrix κ ι₂ K)
    (e₁ : Fin m ≃ ι₁) (e₂ : Fin n ≃ ι₂) (ref : Fin m ⊕ Fin n ≃ κ)
    {T₁ T₂ : Finset κ} (hT₁ : T₁.card = m) (hT₂ : T₂.card = n)
    (hT₁_eq : T₁ = Finset.univ.image (ref ∘ Sum.inl))
    (hT₂_eq : T₂ = Finset.univ.image (ref ∘ Sum.inr))
    (hA₁ : A₁.submatrix (ref ∘ Sum.inl) e₁ = -1)
    (hA₂ : A₂.submatrix (ref ∘ Sum.inr) e₂ = -1)
    (k₀ : κ) (side : Bool) :
    halfEdgeIndex A₁ A₂ e₁ e₂ ref T₁ T₂ hT₁ hT₂ k₀ side = (-1 : ℤ) ^ (m + n) := by
  classical
  have huniv : T₁ ∪ T₂ = Finset.univ := by
    ext k
    simp only [Finset.mem_union, Finset.mem_univ, iff_true, hT₁_eq, hT₂_eq, Finset.mem_image,
      Function.comp_apply, true_and]
    rcases hx : ref.symm k with i | j
    · exact .inl ⟨i, by rw [← hx, Equiv.apply_symm_apply]⟩
    · exact .inr ⟨j, by rw [← hx, Equiv.apply_symm_apply]⟩
  have hleave : leaveLabel T₁ T₂ k₀ = k₀ := by simp [leaveLabel, huniv]
  let ord₁ := (T₁.orderIsoOfFin hT₁).toEquiv
  let ord₂ := (T₂.orderIsoOfFin hT₂).toEquiv
  let eL : Fin m ≃ T₁ := Equiv.ofBijective
    (fun i => ⟨ref (.inl i), hT₁_eq ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun _ _ h => Sum.inl.inj (ref.injective (congrArg Subtype.val h)),
        by simp [Fintype.card_coe, hT₁]⟩)
  let eR : Fin n ≃ T₂ := Equiv.ofBijective
    (fun j => ⟨ref (.inr j), hT₂_eq ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun _ _ h => Sum.inr.inj (ref.injective (congrArg Subtype.val h)),
        by simp [Fintype.card_coe, hT₂]⟩)
  set σ₁ : Equiv.Perm (Fin m) := ord₁.trans eL.symm
  set σ₂ : Equiv.Perm (Fin n) := ord₂.trans eR.symm
  have hσ₁_val : ∀ i : Fin m, (ord₁ i : κ) = ref (.inl (σ₁ i)) := fun i =>
    (congrArg Subtype.val (eL.apply_symm_apply (ord₁ i))).symm
  have hσ₂_val : ∀ j : Fin n, (ord₂ j : κ) = ref (.inr (σ₂ j)) := fun j =>
    (congrArg Subtype.val (eR.apply_symm_apply (ord₂ j))).symm
  have hcomp : halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ side = ref ∘ Equiv.sumCongr σ₁ σ₂ := by
    funext x
    cases side <;> rcases x with i | j
    · dsimp only [halfEdgeFun, Function.comp_apply, Equiv.sumCongr_apply, Sum.map_inl]
      rw [hleave]
      dsimp only [Sum.elim_inl]
      by_cases h : (ord₁ i : κ) = k₀
      · rw [ite_eq_left h]; exact h.symm.trans (hσ₁_val i)
      · rw [ite_eq_right h]; exact hσ₁_val i
    · exact hσ₂_val j
    · exact hσ₁_val i
    · dsimp only [halfEdgeFun, Function.comp_apply, Equiv.sumCongr_apply, Sum.map_inr]
      rw [hleave]
      dsimp only [Sum.elim_inr]
      by_cases h : (ord₂ j : κ) = k₀
      · rw [ite_eq_left h]; exact h.symm.trans (hσ₂_val j)
      · rw [ite_eq_right h]; exact hσ₂_val j
  have hbij : Function.Bijective (halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ side) := by
    rw [hcomp]
    exact ref.bijective.comp (Equiv.sumCongr σ₁ σ₂).bijective
  rw [halfEdgeIndex, dite_eq_left hbij]
  dsimp only
  set π := (Equiv.ofBijective _ hbij).trans ref.symm
  have hπ : π = Equiv.sumCongr σ₁ σ₂ := by
    ext x
    simp only [π, Equiv.trans_apply, Equiv.ofBijective_apply, hcomp, Function.comp_apply,
      Equiv.symm_apply_apply]
  have hsign_pi : (Equiv.Perm.sign π : ℤ) =
      (Equiv.Perm.sign σ₁ : ℤ) * (Equiv.Perm.sign σ₂ : ℤ) := by
    rw [hπ, Equiv.Perm.sign_sumCongr, Units.val_mul]
  have hM₁ : A₁.submatrix (fun i => (T₁.orderIsoOfFin hT₁ i : κ)) e₁ =
      (-1 : Matrix (Fin m) (Fin m) K).submatrix σ₁ id := by
    ext i j
    have hi : (T₁.orderIsoOfFin hT₁ i : κ) = ref (.inl (σ₁ i)) := hσ₁_val i
    change A₁ (T₁.orderIsoOfFin hT₁ i : κ) (e₁ j) = (-1 : Matrix (Fin m) (Fin m) K) (σ₁ i) j
    rw [hi, ← hA₁]
    rfl
  have hM₂ : A₂.submatrix (fun j => (T₂.orderIsoOfFin hT₂ j : κ)) e₂ =
      (-1 : Matrix (Fin n) (Fin n) K).submatrix σ₂ id := by
    ext i j
    have hi : (T₂.orderIsoOfFin hT₂ i : κ) = ref (.inr (σ₂ i)) := hσ₂_val i
    change A₂ (T₂.orderIsoOfFin hT₂ i : κ) (e₂ j) = (-1 : Matrix (Fin n) (Fin n) K) (σ₂ i) j
    rw [hi, ← hA₂]
    rfl
  have hdet₁ : (A₁.submatrix (fun i => (T₁.orderIsoOfFin hT₁ i : κ)) e₁).det =
      ((Equiv.Perm.sign σ₁ : ℤ) : K) * (-1 : K) ^ m := by
    rw [hM₁, Matrix.det_permute, Matrix.det_neg, Matrix.det_one, Fintype.card_fin, mul_one]
  have hdet₂ : (A₂.submatrix (fun j => (T₂.orderIsoOfFin hT₂ j : κ)) e₂).det =
      ((Equiv.Perm.sign σ₂ : ℤ) : K) * (-1 : K) ^ n := by
    rw [hM₂, Matrix.det_permute, Matrix.det_neg, Matrix.det_one, Fintype.card_fin, mul_one]
  have hsign_int : ∀ (k : ℕ) (τ : Equiv.Perm (Fin k)),
      (Equiv.Perm.sign τ : ℤ).sign = (Equiv.Perm.sign τ : ℤ) := fun k τ => by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
  have hs₁ : signOfK (A₁.submatrix (fun i => (T₁.orderIsoOfFin hT₁ i : κ)) e₁).det =
      (Equiv.Perm.sign σ₁ : ℤ) * (-1 : ℤ) ^ m := by
    rw [hdet₁, signOfK_mul, signOfK_intCast, hsign_int m σ₁, signOfK_neg_one_pow]
  have hs₂ : signOfK (A₂.submatrix (fun j => (T₂.orderIsoOfFin hT₂ j : κ)) e₂).det =
      (Equiv.Perm.sign σ₂ : ℤ) * (-1 : ℤ) ^ n := by
    rw [hdet₂, signOfK_mul, signOfK_intCast, hsign_int n σ₂, signOfK_neg_one_pow]
  have hsq : ∀ (k : ℕ) (τ : Equiv.Perm (Fin k)),
      (Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign τ : ℤ) = 1 := fun k τ => by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
  rw [hsign_pi, hs₁, hs₂]
  calc ((Equiv.Perm.sign σ₁ : ℤ) * (Equiv.Perm.sign σ₂ : ℤ)) *
        ((Equiv.Perm.sign σ₁ : ℤ) * (-1 : ℤ) ^ m) *
        ((Equiv.Perm.sign σ₂ : ℤ) * (-1 : ℤ) ^ n)
      = ((Equiv.Perm.sign σ₁ : ℤ) * (Equiv.Perm.sign σ₁ : ℤ)) *
          ((Equiv.Perm.sign σ₂ : ℤ) * (Equiv.Perm.sign σ₂ : ℤ)) *
          ((-1 : ℤ) ^ m * (-1 : ℤ) ^ n) := by ring
    _ = 1 * 1 * (-1 : ℤ) ^ (m + n) := by rw [hsq m σ₁, hsq n σ₂, pow_add]
    _ = (-1 : ℤ) ^ (m + n) := by ring

end Orientation

end Cslib.GameTheory.LemkeHowson

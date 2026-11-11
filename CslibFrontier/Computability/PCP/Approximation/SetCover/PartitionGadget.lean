/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.FiniteCover
public import Mathlib.Data.Nat.Log
import Batteries.Data.Nat.Lemmas
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Powerset

/-!
# Partition gadgets for Set Cover hardness

A *partition gadget* ([LundYannakakis1994]; [Feige1998]) over a finite alphabet `γ` is a finite
universe of points `0, …, size - 1` together with subsets `S_b = {x | mem x b = true}` indexed by
`b : γ`. The gadget *separates* up to `t` labels (`PartitionGadget.Separates`) when every pair of
disjoint subsets `P, Q : Finset γ` with `P.card + Q.card ≤ t` admits an element `x < size` inside
every `S_b` (`b ∈ P`) and outside every `S_b` (`b ∈ Q`).

Consequently, if small subcollections `A' : Finset β` of complements `{x | mem x (π a) = false}` and
`B' : Finset γ` of `{x | mem x b = true}` with `A'.card + B'.card ≤ t` cover the entire gadget
universe, then `A'.image π` and `B'` must intersect (`PartitionGadget.exists_eq_of_covers`).

We provide two gadgets:
* `Cslib.PCP.boolCubeGadget`: the explicit `2 ^ |γ|`-element Boolean cube (`Nat.testBit`),
  separating for every `t`, which suffices for constant-factor `c`-approximation hardness;
* `Cslib.PCP.exists_small_partitionGadget`: via `Cslib.exists_cover_of_density`, a gadget of size
  `2 ^ t * (t * Nat.clog 2 (2 * |γ| + 1) + 1)` separates up to `t` labels.

## Main definitions

* `Cslib.PCP.PartitionGadget`: set-cover partition gadget structure and `Separates` predicate.
* `Cslib.PCP.boolCubeGadget`: explicit `2 ^ |γ|`-element Boolean-cube partition gadget.

## Main results

* `Cslib.PCP.PartitionGadget.exists_eq_of_covers`: any small cover of the gadget yields matching
  projected labels `π a = b`.
* `Cslib.PCP.boolCubeGadget_separates`: `boolCubeGadget γ` separates for every `t`.
* `Cslib.PCP.exists_small_partitionGadget`: existence of an `O(t * 2 ^ t * log |γ|)`-size
  `t`-separating gadget.

## References

Primary texts uninspected (bibliographic metadata checked via search records only; locators
unverified and no numbered paper theorems are claimed). The explicit `PartitionGadget`
structure, `boolCubeGadget`, and the `exists_cover_of_density`-derived size bound in
`exists_small_partitionGadget` are this library's formulation.

* [C. Lund, M. Yannakakis, *On the hardness of approximating minimization
  problems*][LundYannakakis1994]
* [U. Feige, *A threshold of ln n for approximating set cover*][Feige1998]
-/

public section

namespace Cslib.PCP

/-- A partition gadget over label alphabet `γ`: a ground range `[0, size)` and membership bit
`mem x b` deciding whether element `x` lies in the right-hand set of `b`. -/
structure PartitionGadget (γ : Type) where
  /-- Number of elements in the gadget universe `[0, size)`. -/
  size : ℕ
  /-- Membership predicate: `mem x b = true` puts `x` in `S_b` (and `false` puts `x` in its
  complement). -/
  mem : ℕ → γ → Bool

namespace PartitionGadget

/-- `G` separates up to `t` labels when every disjoint pair `(P, Q)` of total size at most `t`
is separated by some element `x < G.size`. -/
@[expose] def Separates {γ : Type} (G : PartitionGadget γ) (t : ℕ) : Prop :=
  ∀ P Q : Finset γ, Disjoint P Q → P.card + Q.card ≤ t →
    ∃ x < G.size, (∀ b ∈ P, G.mem x b = true) ∧ (∀ b ∈ Q, G.mem x b = false)

/-- **Anti-cover property**: if `A' ⊆ β` (whose sets are the complements of `π a`) and `B' ⊆ γ`
together cover `[0, G.size)` and have `A'.card + B'.card ≤ t`, then `π(A')` meets `B'`. -/
theorem exists_eq_of_covers {β γ : Type} {G : PartitionGadget γ} {t : ℕ}
    (hsep : G.Separates t) (π : β → γ) (A' : Finset β) (B' : Finset γ)
    (hcard : A'.card + B'.card ≤ t)
    (hcov : ∀ x < G.size, (∃ a ∈ A', G.mem x (π a) = false) ∨ (∃ b ∈ B', G.mem x b = true)) :
    ∃ a ∈ A', ∃ b ∈ B', π a = b := by
  classical
  by_contra hdisj
  have hDisj : Disjoint (A'.image π) B' := by
    rw [Finset.disjoint_left]
    intro b hbA hbB
    obtain ⟨a, haA, hab⟩ := Finset.mem_image.1 hbA
    exact hdisj ⟨a, haA, b, hbB, hab⟩
  have hle : (A'.image π).card + B'.card ≤ t :=
    (Nat.add_le_add_right Finset.card_image_le _).trans hcard
  obtain ⟨x, hx, hP, hQ⟩ := hsep (A'.image π) B' hDisj hle
  rcases hcov x hx with ⟨a, ha, hfalse⟩ | ⟨b, hb, htrue⟩
  · have hmem := hP (π a) (Finset.mem_image_of_mem π ha)
    rw [hfalse] at hmem
    exact Bool.false_ne_true hmem
  · have hmem := hQ b hb
    rw [htrue] at hmem
    exact Bool.false_ne_true hmem.symm

end PartitionGadget

/-! ### Explicit Boolean-cube gadget -/

/-- The explicit Boolean-cube partition gadget on `γ`: universe size `2 ^ Fintype.card γ`, where
element `x` lies in `S_b` when bit `(Fintype.equivFin γ b)` of `x` is set. -/
@[expose] noncomputable def boolCubeGadget (γ : Type) [Fintype γ] : PartitionGadget γ where
  size := 2 ^ Fintype.card γ
  mem x b := x.testBit (Fintype.equivFin γ b)

/-- The Boolean-cube partition gadget separates disjoint label sets of arbitrary finite size. -/
theorem boolCubeGadget_separates (γ : Type) [Fintype γ] (t : ℕ) :
    (boolCubeGadget γ).Separates t := by
  intro P Q hDisj _
  classical
  let e := Fintype.equivFin γ
  let f : Fin (Fintype.card γ) → Bool := fun k => decide (e.symm k ∈ P)
  refine ⟨Nat.ofBits f, Nat.ofBits_lt_two_pow f, fun b hbP => ?_, fun b hbQ => ?_⟩
  · change (Nat.ofBits f).testBit (e b : ℕ) = true
    rw [Nat.testBit_ofBits_lt f _ (e b).isLt]
    simp only [f, Fin.eta, Equiv.symm_apply_apply, decide_eq_true_eq]
    exact hbP
  · change (Nat.ofBits f).testBit (e b : ℕ) = false
    rw [Nat.testBit_ofBits_lt f _ (e b).isLt]
    simp only [f, Fin.eta, Equiv.symm_apply_apply, decide_eq_false_iff_not]
    exact Finset.disjoint_right.1 hDisj hbQ

/-! ### Small logarithmic-alphabet partition gadget via `FiniteCover` -/

/-- Existence of a `t`-separating partition gadget of size `2 ^ t * (t * ⌈log₂(2|γ| + 1)⌉ + 1)`
via `Cslib.exists_cover_of_density`. -/
theorem exists_small_partitionGadget (γ : Type) [Fintype γ] (t : ℕ) :
    ∃ G : PartitionGadget γ, G.Separates t ∧
      G.size = 2 ^ t * (t * Nat.clog 2 (2 * Fintype.card γ + 1) + 1) := by
  classical
  let W := {p : Finset γ × Finset γ // Disjoint p.1 p.2 ∧ p.1.card + p.2.card ≤ t}
  let hit : (γ → Bool) → W → Prop := fun f w =>
    (∀ b ∈ w.1.1, f b = true) ∧ (∀ b ∈ w.1.2, f b = false)
  let enc : W → (Fin t → Option (γ × Bool)) := fun w i =>
    ((w.1.1.image (fun b => (b, true)) ∪ w.1.2.image (fun b => (b, false))).toList)[(i : ℕ)]?
  have henc_inj : Function.Injective enc := by
    intro w₁ w₂ h
    let S₁ : Finset (γ × Bool) :=
      w₁.1.1.image (fun b => (b, true)) ∪ w₁.1.2.image (fun b => (b, false))
    let S₂ : Finset (γ × Bool) :=
      w₂.1.1.image (fun b => (b, true)) ∪ w₂.1.2.image (fun b => (b, false))
    have hcard₁ : S₁.card ≤ t := by
      calc S₁.card ≤ (w₁.1.1.image (fun b => (b, true))).card +
              (w₁.1.2.image (fun b => (b, false))).card := Finset.card_union_le _ _
        _ ≤ w₁.1.1.card + w₁.1.2.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
        _ ≤ t := w₁.2.2
    have hcard₂ : S₂.card ≤ t := by
      calc S₂.card ≤ (w₂.1.1.image (fun b => (b, true))).card +
              (w₂.1.2.image (fun b => (b, false))).card := Finset.card_union_le _ _
        _ ≤ w₂.1.1.card + w₂.1.2.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
        _ ≤ t := w₂.2.2
    have hS : S₁ = S₂ := by
      ext ⟨b, flag⟩
      simp only [← Finset.mem_toList]
      constructor
      · intro hb
        obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.1 hb
        have hit : i < t := lt_of_lt_of_le (by simpa using hi) hcard₁
        have hcon := congrFun h ⟨i, hit⟩
        simp only [enc, List.getElem?_eq_getElem hi, S₁] at hcon
        rw [heq] at hcon
        have hi2 : i < S₂.toList.length := by
          by_contra hn
          rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at hcon
          exact absurd hcon (Option.some_ne_none _)
        rw [List.getElem?_eq_getElem hi2, Option.some.injEq] at hcon
        rw [hcon]
        exact List.getElem_mem hi2
      · intro hb
        obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.1 hb
        have hit : i < t := lt_of_lt_of_le (by simpa using hi) hcard₂
        have hcon := congrFun h ⟨i, hit⟩
        simp only [enc, List.getElem?_eq_getElem hi, S₂] at hcon
        rw [heq] at hcon
        have hi1 : i < S₁.toList.length := by
          by_contra hn
          rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at hcon
          exact absurd hcon.symm (Option.some_ne_none _)
        rw [List.getElem?_eq_getElem hi1, Option.some.injEq] at hcon
        rw [← hcon]
        exact List.getElem_mem hi1
    apply Subtype.ext
    ext1
    · ext b
      have := congrArg (fun S : Finset (γ × Bool) => (b, true) ∈ S) hS
      simpa [S₁, S₂] using this
    · ext b
      have := congrArg (fun S : Finset (γ × Bool) => (b, false) ∈ S) hS
      simpa [S₁, S₂] using this
  have hW : Fintype.card W ≤ 2 ^ (t * Nat.clog 2 (2 * Fintype.card γ + 1)) := by
    calc Fintype.card W
        ≤ Fintype.card (Fin t → Option (γ × Bool)) := Fintype.card_le_of_injective enc henc_inj
      _ = (Fintype.card (Option (γ × Bool))) ^ t := by
          rw [Fintype.card_fun, Fintype.card_fin]
      _ = (2 * Fintype.card γ + 1) ^ t := by
          simp [Fintype.card_option, Fintype.card_prod, Nat.mul_comm, Nat.add_comm]
      _ ≤ (2 ^ Nat.clog 2 (2 * Fintype.card γ + 1)) ^ t :=
          Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _
      _ = 2 ^ (t * Nat.clog 2 (2 * Fintype.card γ + 1)) := by
          rw [← Nat.pow_mul, Nat.mul_comm]
  have hdens : ∀ w : W,
      Fintype.card (γ → Bool) ≤ 2 ^ t * Fintype.card {f : γ → Bool // hit f w} := by
    intro ⟨⟨P, Q⟩, hDisj, hsum⟩
    dsimp only at hDisj hsum
    let R : Finset γ := Finset.univ \ (P ∪ Q)
    let φ : {f : γ → Bool // hit f ⟨(P, Q), hDisj, hsum⟩} ≃ (R → Bool) :=
      { toFun := fun f b => f.1 b.1
        invFun := fun g => ⟨fun b =>
          if hb : b ∈ R then g ⟨b, hb⟩ else decide (b ∈ P), by
            refine ⟨fun b hbP => ?_, fun b hbQ => ?_⟩
            · have hnR : b ∉ R := fun h => (Finset.mem_sdiff.1 h).2 (Finset.mem_union_left _ hbP)
              simp [hnR, hbP]
            · have hnR : b ∉ R := fun h => (Finset.mem_sdiff.1 h).2 (Finset.mem_union_right _ hbQ)
              simp [hnR, Finset.disjoint_right.1 hDisj hbQ]⟩
        left_inv := fun ⟨f, hfP, hfQ⟩ => by
          apply Subtype.ext
          funext b
          by_cases hbR : b ∈ R
          · simp [hbR]
          · simp only [hbR, ↓reduceDIte]
            have hPQ : b ∈ P ∪ Q := by
              by_contra h
              exact hbR (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h⟩)
            rcases Finset.mem_union.1 hPQ with hbP | hbQ
            · simp [hfP b hbP, hbP]
            · simp [hfQ b hbQ, Finset.disjoint_right.1 hDisj hbQ]
        right_inv := fun g => by
          funext b
          simp [b.2] }
    have hcard_eq : Fintype.card {f : γ → Bool // hit f ⟨(P, Q), hDisj, hsum⟩} = 2 ^ R.card := by
      rw [Fintype.card_congr φ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    have hcard_R : P.card + Q.card + R.card = Fintype.card γ := by
      have hPQ : (P ∪ Q).card = P.card + Q.card := Finset.card_union_of_disjoint hDisj
      have hsub : P ∪ Q ⊆ Finset.univ := Finset.subset_univ _
      rw [← hPQ, add_comm]
      have hsdiff := Finset.card_sdiff_add_card_eq_card hsub
      simpa [R, Finset.card_univ] using hsdiff
    rw [hcard_eq, Fintype.card_fun, Fintype.card_bool, ← Nat.pow_add]
    refine Nat.pow_le_pow_right (by decide) ?_
    omega
  obtain ⟨tests, htests⟩ := Cslib.exists_cover_of_density hit (2 ^ t)
    (t * Nat.clog 2 (2 * Fintype.card γ + 1)) (Nat.two_pow_pos t) hW hdens
  let m := 2 ^ t * (t * Nat.clog 2 (2 * Fintype.card γ + 1) + 1)
  refine ⟨⟨m, fun x b => if hx : x < m then tests ⟨x, hx⟩ b else false⟩, ?_, rfl⟩
  intro P Q hDisj hsum
  obtain ⟨i, hi⟩ := htests ⟨(P, Q), hDisj, hsum⟩
  refine ⟨i.1, i.isLt, ⟨fun b hbP => ?_, fun b hbQ => ?_⟩⟩
  · dsimp only
    split_ifs with h
    · exact hi.1 b hbP
    · exact absurd i.isLt h
  · dsimp only
    split_ifs with h
    · exact hi.2 b hbQ
    · exact absurd i.isLt h

end Cslib.PCP

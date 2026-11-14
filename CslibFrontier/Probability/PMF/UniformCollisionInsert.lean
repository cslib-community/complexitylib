/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Finset.CollisionInsert
public import CslibFrontier.Probability.PMF.Uniform
public import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Sigma.Basic

/-!
# Uniform subset insertion with collision replacement

Choose a uniform `k`-subset of `S` and an independent uniform element of `insert p S`, where
`p ∉ S`. Inserting that element, or `p` when it collides, gives a uniform `(k + 1)`-subset of
`insert p S`. The proof keeps the candidate as a marked element of the resulting set: this is
a bijection, and every result has exactly `k + 1` possible marks.

## Main results

* `Cslib.Probability.PMF.uniformOfFinset_collisionInsert`: collision replacement preserves
  uniform fixed-cardinality subsets while increasing their size by one.
-/

public section

namespace Cslib.Probability.PMF

open Finset

variable {α : Type*} [DecidableEq α]

private theorem predecessor_mem {S T : Finset α} {p r : α} {k : ℕ}
    (hT : T ∈ (insert p S).powersetCard (k + 1)) (hr : r ∈ T) :
    (if p ∈ T then T.erase p else T.erase r) ∈ S.powersetCard k := by
  obtain ⟨hTS, hcard⟩ := mem_powersetCard.mp hT
  apply mem_powersetCard.mpr
  constructor
  · intro x hx
    by_cases hp : p ∈ T
    · rw [ite_eq_left hp] at hx
      have hxT := (mem_erase.mp hx).2
      exact (mem_insert.mp (hTS hxT)).resolve_left (mem_erase.mp hx).1
    · rw [ite_eq_right hp] at hx
      have hxT := (mem_erase.mp hx).2
      exact (mem_insert.mp (hTS hxT)).resolve_left (fun h => hp (h ▸ hxT))
  · split_ifs with hp
    · rw [card_erase_of_mem hp, hcard]
      omega
    · rw [card_erase_of_mem hr, hcard]
      omega

private def collisionInsertMarkedEquiv (S : Finset α) (p : α) (k : ℕ) (hp : p ∉ S) :
    (↥(S.powersetCard k) × ↥(insert p S)) ≃
      (Σ T : ↥((insert p S).powersetCard (k + 1)), ↥T.val) where
  toFun := fun ⟨U, r⟩ =>
    ⟨⟨U.val.collisionInsert p r.val, mem_powersetCard.mpr
      ⟨collisionInsert_subset (mem_powersetCard.mp U.property).1 p r.property,
        (card_collisionInsert (fun h => hp ((mem_powersetCard.mp U.property).1 h)) r.val).trans
          (congrArg (· + 1) (mem_powersetCard.mp U.property).2)⟩⟩,
      ⟨r.val, mem_collisionInsert U.val p r.val⟩⟩
  invFun := fun ⟨T, r⟩ =>
    (⟨if p ∈ T.val then T.val.erase p else T.val.erase r.val,
      predecessor_mem T.property r.property⟩,
      ⟨r.val, (mem_powersetCard.mp T.property).1 r.property⟩)
  left_inv := by
    rintro ⟨U, r⟩
    apply Prod.ext
    · apply Subtype.ext
      exact erase_collisionInsert (fun h => hp ((mem_powersetCard.mp U.property).1 h)) r.val
    · rfl
  right_inv := by
    rintro ⟨T, r⟩
    apply Sigma.subtype_ext
    · apply Subtype.ext
      exact collisionInsert_erase r.property p
    · rfl

private noncomputable def collisionInsertProductEquiv (S : Finset α) (p : α) (k : ℕ)
    (hp : p ∉ S) :
    (↥(S.powersetCard k) × ↥(insert p S)) ≃
      (↥((insert p S).powersetCard (k + 1)) × Fin (k + 1)) :=
  (collisionInsertMarkedEquiv S p k hp).trans
    (Equiv.sigmaEquivProdOfEquiv fun T =>
      T.val.equivFinOfCardEq (mem_powersetCard.mp T.property).2)

/-- Inserting an independent uniform candidate into a uniform `k`-subset of `S`, with a
reserved replacement `p ∉ S` for collisions, gives a uniform `(k + 1)`-subset of `insert p S`. -/
theorem uniformOfFinset_collisionInsert {S : Finset α} {p : α} {k : ℕ}
    (hp : p ∉ S) (hk : k ≤ S.card) :
    ((uniformOfFinset (S.powersetCard k) (powersetCard_nonempty.mpr hk)).bind fun U =>
      (uniformOfFinset (insert p S) (insert_nonempty p S)).map fun r => U.collisionInsert p r) =
      uniformOfFinset ((insert p S).powersetCard (k + 1))
        (powersetCard_nonempty.mpr (by rw [card_insert_of_notMem hp]; omega)) := by
  let : Nonempty (S.powersetCard k) := (powersetCard_nonempty.mpr hk).to_subtype
  let : Nonempty ↥(insert p S) := (insert_nonempty p S).to_subtype
  let : Nonempty ((insert p S).powersetCard (k + 1)) :=
    (powersetCard_nonempty.mpr (by rw [card_insert_of_notMem hp]; omega)).to_subtype
  have h := congrArg (fun μ => μ.map Subtype.val)
    (uniformOfFintype_bind_map_fst_equiv (collisionInsertProductEquiv S p k hp))
  rw [uniformOfFintype_finset_map_val] at h
  rw [← uniformOfFintype_finset_map_val (S.powersetCard k),
    ← uniformOfFintype_finset_map_val (insert p S)]
  simpa only [PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
    collisionInsertProductEquiv, collisionInsertMarkedEquiv, Equiv.trans_apply,
    Equiv.sigmaEquivProdOfEquiv, Equiv.sigmaEquivProd, Equiv.sigmaCongrRight,
    Equiv.coe_fn_mk] using h

end Cslib.Probability.PMF

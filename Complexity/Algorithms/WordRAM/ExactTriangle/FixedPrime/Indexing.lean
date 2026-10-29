/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Readback
public import Complexity.Algorithms.WordRAM.ExactTriangle.PreparationLocality

/-!
# The actual occupied ordinals name the existing finite instances

The producer's real counter supplies the range, and its existing dependent-sum readback
supplies the unique residue/chunk/piece for each ordinal. These are consequences of output,
not a second enumeration or a list supplied to the native controller.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle

/-- Every occupied runtime ordinal has exactly one existing finite meaning. -/
theorem occupied_index_unique {n D g p i : ℕ} (values : ℕ → ℤ)
    {initial a : Data 64} (h : Instances.Output n D g p values initial a)
    (hD : 16 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : p ≠ 0)
    (hi : i < a.regs Instances.produced) :
    ∃! idx : InstanceIndex p,
      idx ∈ instanceIndices (fun u v : Fin n => values (pairIndex (u, v))) D g p ∧
        RecordProduct.recordOrdinal n D g p values idx = i := by
  have hc := h.2.2.2.2.1
  rw [hc] at hi
  obtain ⟨idx, hidx, huniq⟩ := PreparationSpec.index_unique values
    (fun u v : Fin n => values (pairIndex (u, v))) hp (by intro u v; rfl)
    hD hDn hg i hi
  refine ⟨idx, ⟨hidx.1, hidx.2.symm⟩, fun other hother => ?_⟩
  exact huniq other ⟨hother.1, hother.2.symm⟩

/-- The actual occupied range enumerates every existing instance exactly once. This is a
proof-side interpretation of the native ordinal, not a table consumed by the program. -/
theorem exists_occupied_order {n D g p : ℕ} (values : ℕ → ℤ)
    {initial a : Data 64} (h : Instances.Output n D g p values initial a)
    (hD : 16 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : p ≠ 0) :
    ∃ f : Fin (a.regs Instances.produced) → InstanceIndex p,
      Function.Injective f ∧
      (∀ i, f i ∈ instanceIndices
        (fun u v : Fin n => values (pairIndex (u, v))) D g p ∧
        RecordProduct.recordOrdinal n D g p values (f i) = i.val) ∧
      ∀ idx ∈ instanceIndices (fun u v : Fin n => values (pairIndex (u, v))) D g p,
        ∃ i, f i = idx := by
  classical
  let I := instanceIndices (fun u v : Fin n => values (pairIndex (u, v))) D g p
  have he (i : Fin (a.regs Instances.produced)) : ∃ idx, idx ∈ I ∧
      RecordProduct.recordOrdinal n D g p values idx = i.val :=
    (occupied_index_unique values h hD hDn hg hp i.isLt).exists
  choose f hf using he
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact (hf i).2.symm.trans ((congrArg
      (RecordProduct.recordOrdinal n D g p values) hij).trans (hf j).2)
  let f' : Fin (a.regs Instances.produced) → I := fun i => ⟨f i, (hf i).1⟩
  have hinj' : Function.Injective f' := fun _ _ hij =>
    hinj (congrArg Subtype.val hij)
  have hcard : Fintype.card (Fin (a.regs Instances.produced)) = Fintype.card I := by
    simpa only [Fintype.card_fin, Fintype.card_coe, I] using
      PreparationSpec.count_eq_card values _ hp (by intro u v; rfl) h
  have hsurj := ((Fintype.bijective_iff_injective_and_card f').mpr ⟨hinj', hcard⟩).2
  refine ⟨f, hinj, hf, ?_⟩
  intro idx hidx
  obtain ⟨i, hi⟩ := hsurj ⟨idx, hidx⟩
  exact ⟨i, congrArg Subtype.val hi⟩

/-- Original interleaved query readback survives changes outside its protected span. -/
theorem decodedQueries_eq_of_eqOn {n q Q heap : ℕ} (hn : 0 < n)
    (x y : ℕ → ℕ) (h : Set.EqOn x y (Set.Iio heap)) (hspan : q + 2 * Q ≤ heap) :
    RecordProduct.decodedQueries hn x q Q = RecordProduct.decodedQueries hn y q Q := by
  unfold RecordProduct.decodedQueries
  apply congrArg List.ofFn
  funext i
  apply Prod.ext <;> apply Fin.ext
  · change x (q + 2 * i.val) % n = y (q + 2 * i.val) % n
    rw [h (by have := i.isLt; change q + 2 * i.val < heap; omega)]
  · change x (q + 2 * i.val + 1) % n = y (q + 2 * i.val + 1) % n
    rw [h (by have := i.isLt; change q + 2 * i.val + 1 < heap; omega)]

end Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime

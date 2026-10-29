/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalCall

/-!
# Charged native output delivery for one traversal node

The three actual heavy counts are read from the node allocation. The packed pointer is appended
to the reserved output table and the fresh heap advances past all node output and scratch cells.
Address computation is repeated explicitly instead of assuming scratch-register outputs that
the node builder's public contract does not export.

## Main definitions

* `deliveryState`: exact state after all 24 native delivery instructions.

## Main results

* `deliver_exec`: charged output delivery with derived address and counter fits.

The layout and native composition proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- All arithmetic results of the native delivery block, including its sole memory store. -/
def deliveryState (x : Data 128) : Data 128 :=
  let b := x.regs heap
  let n₀ := x.regs (slot 2)
  let n₁ := x.regs (slot 4)
  let n₂ := x.regs (slot 6)
  let N := x.regs groups
  let M := x.regs selected
  let p := b + 3 + n₀ + n₁ + n₂
  let o := x.regs outputs + x.regs outputCount
  let d₁ := b + 1 + n₀
  let d₂ := d₁ + 1 + n₁
  let a := ((((x.set packed 3).set packed (b + 3)).set packed (b + 3 + n₀)).set
    packed (b + 3 + n₀ + n₁)).set packed p
  let a := (((a.set temporary o).write o p).set outputCount (x.regs outputCount + 1)).set
    (heavyLength 0) (x.mem b)
  let a := (((a.set (heavyBase 0) (b + 1)).set temporary d₁).set
    (heavyLength 1) (x.mem d₁)).set (heavyBase 1) (d₁ + 1)
  let a := (((a.set temporary d₂).set (heavyLength 2) (x.mem d₂)).set
    (heavyBase 2) (d₂ + 1)).set endpoint (N + N)
  let a := ((((((a.set endpoint (N + N + (N + N))).set endpoint (p + 4 * N)).set
    endpoint (p + 4 * N + n₀)).set endpoint (p + 4 * N + n₀ + n₁)).set
    endpoint (p + 4 * N + n₀ + n₁ + n₂)).set endpoint (p + 4 * N + n₀ + n₁ + n₂ + M)).set
    heap (p + 4 * N + n₀ + n₁ + n₂ + M)
  a

/-- Delivery writes exactly one output-pointer cell; all other memory retains the node output. -/
theorem deliveryState_mem (x : Data 128) : (deliveryState x).mem =
    Function.update x.mem (x.regs outputs + x.regs outputCount)
      (x.regs heap + 3 + x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6)) := rfl

/-- The appended pointer is the existing node layout's packed base. -/
theorem deliveryState_packed (x : Data 128) : (deliveryState x).regs packed =
    (NodePacking.layout ((nodeState x).comap kernel)).packed := by
  change x.regs heap + 3 + x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6) =
    x.regs heap + 3 + (x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6))
  omega

/-- All allocated node output, residues and histogram lie below the new fresh heap. -/
theorem deliveryState_heap (x : Data 128) : (deliveryState x).regs heap =
    (NodePacking.layout ((nodeState x).comap kernel)).endpoint := by
  change x.regs heap + 3 + x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6) +
      4 * x.regs groups + x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6) + x.regs selected =
    x.regs heap + 3 + (x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6)) +
      4 * x.regs groups + (x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6)) + x.regs selected
  omega

/-- Exactly one node is appended to the output table. -/
theorem deliveryState_count (x : Data 128) :
    (deliveryState x).regs outputCount = x.regs outputCount + 1 := rfl

/-- Each delivered count was read from its actual count-prefixed heavy array. -/
theorem deliveryState_heavy_length (x : Data 128) (j : Fin 3) :
    (deliveryState x).regs (heavyLength j) =
      x.mem ((NodePacking.layout ((nodeState x).comap kernel)).descriptor j) := by
  fin_cases j
  · rfl
  · rfl
  · change x.mem (x.regs heap + 1 + x.regs (slot 2) + 1 + x.regs (slot 4)) =
      x.mem (x.regs heap + 2 + (x.regs (slot 2) + x.regs (slot 4)))
    congr 1
    omega

/-- Each delivered data pointer is the existing heavy-array base. -/
theorem deliveryState_heavy_base (x : Data 128) (j : Fin 3) :
    (deliveryState x).regs (heavyBase j) =
      (NodePacking.layout ((nodeState x).comap kernel)).heavy j := by
  fin_cases j
  · rfl
  · rfl
  · change x.regs heap + 1 + x.regs (slot 2) + 1 + x.regs (slot 4) + 1 =
      x.regs heap + 2 + (x.regs (slot 2) + x.regs (slot 4)) + 1
    omega

/-- Output delivery preserves the node builder's exact heavy/packed readback and allocation
frame. The sole external output-pointer store is recorded explicitly in the before-memory. -/
theorem delivery_output (x : Data 128) (values : Fin 3 → ℕ → ℤ) (before : ℕ → ℕ)
    (h : NodePacking.Output (NodePacking.layout ((nodeState x).comap kernel)) values
      before x.mem)
    (htable : x.regs outputs + x.regs outputCount < x.regs heap) :
    let L := NodePacking.layout ((nodeState x).comap kernel)
    NodePacking.Output L values
      (Function.update before (x.regs outputs + x.regs outputCount) L.packed)
      (deliveryState x).mem := by
  let L := NodePacking.layout ((nodeState x).comap kernel)
  let o := x.regs outputs + x.regs outputCount
  change NodePacking.Output L values before x.mem at h
  change NodePacking.Output L values (Function.update before o L.packed) (deliveryState x).mem
  have hm := deliveryState_mem x
  change (deliveryState x).mem = Function.update x.mem o ((deliveryState x).regs packed) at hm
  rw [deliveryState_packed] at hm
  have ho : o < L.base := htable
  have hkeep (a : ℕ) (ha : L.base ≤ a) : (deliveryState x).mem a = x.mem a := by
    rw [hm, Function.update_of_ne (show a ≠ o by omega)]
  refine ⟨?_, ?_, ?_⟩
  · intro j
    obtain ⟨zs, hnd, hs, hc, hd⟩ := h.heavy j
    refine ⟨zs, hnd, hs, (hkeep _ (L.base_le_descriptor j)).trans hc, ?_⟩
    intro k hk
    have hb := L.base_le_descriptor j
    have hbase : L.base ≤ L.heavy j + k := by
      dsimp only [NodePacking.Layout.heavy]
      omega
    exact (hkeep _ hbase).trans (hd k hk)
  · intro a ha
    have hbase : L.base ≤ L.packed + a := by
      dsimp only [NodePacking.Layout.packed]
      omega
    exact (hkeep _ hbase).trans (h.packed a ha)
  · intro a ha
    rw [hm]
    by_cases he : a = o
    · subst a
      simp only [Function.update_self]
      rfl
    · simp only [Function.update_of_ne he]
      exact h.frame a ha

/-- The delivered register is the existing heavy-set cardinality, not a capacity or pair count. -/
theorem delivery_heavy_card (x : Data 128) (values : Fin 3 → ℕ → ℤ) (before : ℕ → ℕ)
    (h : NodePacking.Output (NodePacking.layout ((nodeState x).comap kernel)) values
      before x.mem) (j : Fin 3) :
    (deliveryState x).regs (heavyLength j) =
      (Cslib.Algorithms.ThreeSum.ChanHe.heavy
        ((Finset.range ((NodePacking.layout ((nodeState x).comap kernel)).n j)).image (values j))
        (NodePacking.layout ((nodeState x).comap kernel)).M).card := by
  rw [deliveryState_heavy_length]
  exact h.heavy_card j

/-- All non-output controller parameters and the entire stack workspace survive delivery. -/
theorem deliver_preserves : ∀ i : Fin 128, i ≠ heap → i ≠ outputCount → i ≠ temporary →
    (i.val < 88 ∨ 96 ≤ i.val) → deliver.Preserves i := by decide

/-- The explicit delivered state retains every non-output controller and stack register. -/
theorem deliveryState_preserves (x : Data 128) (i : Fin 128)
    (hh : i ≠ heap) (hc : i ≠ outputCount) (ht : i ≠ temporary)
    (hi : i.val < 88 ∨ 96 ≤ i.val) : (deliveryState x).regs i = x.regs i := by
  have hp : i ≠ packed := by intro he; subst i; norm_num [packed] at hi
  have he : i ≠ endpoint := by intro he; subst i; norm_num [endpoint] at hi
  have hl (j : Fin 3) : i ≠ heavyLength j := by
    intro hj
    have hv := congrArg Fin.val hj
    dsimp only [heavyLength] at hv
    have := j.isLt
    omega
  have hb (j : Fin 3) : i ≠ heavyBase j := by
    intro hj
    have hv := congrArg Fin.val hj
    dsimp only [heavyBase] at hv
    have := j.isLt
    omega
  simp only [deliveryState, Data.set_regs, Data.write_regs, Function.update_of_ne hh,
    Function.update_of_ne hc, Function.update_of_ne ht, Function.update_of_ne hp,
    Function.update_of_ne he, Function.update_of_ne (hl 0), Function.update_of_ne (hl 1),
    Function.update_of_ne (hl 2), Function.update_of_ne (hb 0), Function.update_of_ne (hb 1),
    Function.update_of_ne (hb 2)]

/-- Every intermediate address and the output-count increment fit once the final endpoint fits.
The output table precedes the fresh allocation, so its store cannot change a heavy-count load. -/
theorem deliver_exec {w : ℕ} (x : Data 128)
    (hone : x.regs one = 1)
    (htable : x.regs outputs + x.regs outputCount < x.regs heap)
    (hfit : Fits w (x.regs heap + 3 + 2 *
      (x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6)) +
      4 * x.regs groups + x.regs selected)) :
    Exec w deliver x (deliveryState x) 24 := by
  have hbound (v : ℕ) (hv : v ≤ x.regs heap + 3 + 2 *
      (x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6)) +
      4 * x.regs groups + x.regs selected) : Fits w v := hfit.of_le hv
  have h3 : Fits w 3 := hbound _ (by omega)
  have hp₀ := hbound (x.regs heap + 3) (by omega)
  have hp₁ := hbound (x.regs heap + 3 + x.regs (slot 2)) (by omega)
  have hp₂ := hbound (x.regs heap + 3 + x.regs (slot 2) + x.regs (slot 4)) (by omega)
  have hp := hbound (x.regs heap + 3 + x.regs (slot 2) + x.regs (slot 4) +
    x.regs (slot 6)) (by omega)
  have ho := hbound (x.regs outputs + x.regs outputCount) (by omega)
  have hc := hbound (x.regs outputCount + 1) (by omega)
  have hd₀ := hbound (x.regs heap + 1) (by omega)
  have hd₁ := hbound (x.regs heap + 1 + x.regs (slot 2)) (by omega)
  have hd₁' := hbound (x.regs heap + 1 + x.regs (slot 2) + 1) (by omega)
  have hd₂ := hbound (x.regs heap + 1 + x.regs (slot 2) + 1 + x.regs (slot 4)) (by omega)
  have hd₂' := hbound (x.regs heap + 1 + x.regs (slot 2) + 1 + x.regs (slot 4) + 1) (by omega)
  have he₀ := hbound (x.regs groups + x.regs groups) (by omega)
  have he₁ := hbound (4 * x.regs groups) (by omega)
  have he₂ := hbound (x.regs heap + 3 + x.regs (slot 2) + x.regs (slot 4) +
    x.regs (slot 6) + 4 * x.regs groups) (by omega)
  have he₃ := hbound (x.regs heap + 3 + x.regs (slot 2) + x.regs (slot 4) +
    x.regs (slot 6) + 4 * x.regs groups + x.regs (slot 2)) (by omega)
  have he₄ := hbound (x.regs heap + 3 + x.regs (slot 2) + x.regs (slot 4) +
    x.regs (slot 6) + 4 * x.regs groups + x.regs (slot 2) + x.regs (slot 4)) (by omega)
  have he₅ := hbound (x.regs heap + 3 + x.regs (slot 2) + x.regs (slot 4) +
    x.regs (slot 6) + 4 * x.regs groups + x.regs (slot 2) + x.regs (slot 4) +
    x.regs (slot 6)) (by omega)
  have he := hbound (x.regs heap + 3 + x.regs (slot 2) + x.regs (slot 4) +
    x.regs (slot 6) + 4 * x.regs groups + x.regs (slot 2) + x.regs (slot 4) +
    x.regs (slot 6) + x.regs selected) (by omega)
  have hne₀ : x.regs heap ≠ x.regs outputs + x.regs outputCount := by omega
  have hne₁ : x.regs heap + 1 + x.regs (slot 2) ≠
      x.regs outputs + x.regs outputCount := by omega
  have hne₂ : x.regs heap + 1 + x.regs (slot 2) + 1 + x.regs (slot 4) ≠
      x.regs outputs + x.regs outputCount := by omega
  dsimp only [heap, slot, groups, selected, outputs, outputCount, one] at *
  ram_eval [deliver, deliveryState, heavyBase, heavyLength, heap, slot, groups, selected,
    outputs, outputCount, packed, temporary, endpoint, one, hone, h3, hp₀, hp₁, hp₂, hp, ho,
    hc, hd₀, hd₁, hd₁', hd₂, hd₂', he₀, he₁, he₂, he₃, he₄, he₅, he,
    hne₀, hne₁, hne₂, Function.update_of_ne, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
    show ∀ n : ℕ, n + n + (n + n) = 4 * n by omega]

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

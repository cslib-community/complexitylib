/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalConstruct

/-!
# Local Chan–He node delivery without catalogue publication

This block reads the three actual heavy-list counts and exposes the packed pointer and allocation
endpoint to an in-place consumer. It performs no memory store and does not use a pointer table
or output counter. All 21 instructions, including endpoint arithmetic, are charged.

## Main definitions

* `deliverLocal`, `localDeliveryState`: executable block and its exact resulting state.

## Main results

* `deliverLocal_exec`: actual execution with address fits derived from the endpoint.
* `localDeliveryState_mem`: the entire memory is preserved.

These native calling-convention proofs are original. Complete traversal and solver execution
are separate obligations.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- Read actual node metadata and advance the frontier without publishing a table entry. -/
def deliverLocal : Code .standard 128 :=
  let n₀ := slot 2
  let n₁ := slot 4
  let n₂ := slot 6
  let h₀ := heavyBase 0
  let h₁ := heavyBase 1
  let h₂ := heavyBase 2
  let c₀ := heavyLength 0
  let c₁ := heavyLength 1
  let c₂ := heavyLength 2
  ram[ packed ← #3; packed ← heap + packed; packed ← packed + n₀;
    packed ← packed + n₁; packed ← packed + n₂;
    c₀ ← *heap; h₀ ← heap + one;
    temporary ← h₀ + n₀; c₁ ← *temporary; h₁ ← temporary + one;
    temporary ← h₁ + n₁; c₂ ← *temporary; h₂ ← temporary + one;
    endpoint ← groups + groups; endpoint ← endpoint + endpoint;
    endpoint ← packed + endpoint; endpoint ← endpoint + n₀; endpoint ← endpoint + n₁;
    endpoint ← endpoint + n₂; endpoint ← endpoint + selected; heap ← endpoint ]

/-- Both complete native kernels followed by local metadata delivery, with no table store. -/
def localVisit : Code .standard 128 := .seq construct deliverLocal

/-- Exact state after the 21 local-delivery instructions. -/
def localDeliveryState (x : Data 128) : Data 128 :=
  let b := x.regs heap
  let n₀ := x.regs (slot 2)
  let n₁ := x.regs (slot 4)
  let n₂ := x.regs (slot 6)
  let N := x.regs groups
  let M := x.regs selected
  let p := b + 3 + n₀ + n₁ + n₂
  let d₁ := b + 1 + n₀
  let d₂ := d₁ + 1 + n₁
  let a := ((((x.set packed 3).set packed (b + 3)).set packed (b + 3 + n₀)).set
    packed (b + 3 + n₀ + n₁)).set packed p
  let a := a.set (heavyLength 0) (x.mem b)
  let a := (((a.set (heavyBase 0) (b + 1)).set temporary d₁).set
    (heavyLength 1) (x.mem d₁)).set (heavyBase 1) (d₁ + 1)
  let a := (((a.set temporary d₂).set (heavyLength 2) (x.mem d₂)).set
    (heavyBase 2) (d₂ + 1)).set endpoint (N + N)
  let a := ((((((a.set endpoint (N + N + (N + N))).set endpoint (p + 4 * N)).set
    endpoint (p + 4 * N + n₀)).set endpoint (p + 4 * N + n₀ + n₁)).set
    endpoint (p + 4 * N + n₀ + n₁ + n₂)).set endpoint (p + 4 * N + n₀ + n₁ + n₂ + M)).set
    heap (p + 4 * N + n₀ + n₁ + n₂ + M)
  a

/-- Local delivery performs no memory store. -/
theorem localDeliveryState_mem (x : Data 128) : (localDeliveryState x).mem = x.mem := rfl

/-- The delivered pointer is the existing node layout's packed base. -/
theorem localDeliveryState_packed (x : Data 128) : (localDeliveryState x).regs packed =
    (NodePacking.layout ((nodeState x).comap kernel)).packed := by
  change x.regs heap + 3 + x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6) =
    x.regs heap + 3 + (x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6))
  omega

/-- All allocated node output, residues and histogram lie below the new fresh heap. -/
theorem localDeliveryState_heap (x : Data 128) : (localDeliveryState x).regs heap =
    (NodePacking.layout ((nodeState x).comap kernel)).endpoint := by
  change x.regs heap + 3 + x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6) +
      4 * x.regs groups + x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6) + x.regs selected =
    x.regs heap + 3 + (x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6)) +
      4 * x.regs groups + (x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6)) + x.regs selected
  omega

/-- The unused catalogue output counter is preserved. -/
theorem localDeliveryState_count (x : Data 128) :
    (localDeliveryState x).regs outputCount = x.regs outputCount := rfl

/-- Each delivered count was read from its actual count-prefixed heavy array. -/
theorem localDeliveryState_heavy_length (x : Data 128) (j : Fin 3) :
    (localDeliveryState x).regs (heavyLength j) =
      x.mem ((NodePacking.layout ((nodeState x).comap kernel)).descriptor j) := by
  fin_cases j
  · rfl
  · rfl
  · change x.mem (x.regs heap + 1 + x.regs (slot 2) + 1 + x.regs (slot 4)) =
      x.mem (x.regs heap + 2 + (x.regs (slot 2) + x.regs (slot 4)))
    congr 1
    omega

/-- Each delivered data pointer is the existing heavy-array base. -/
theorem localDeliveryState_heavy_base (x : Data 128) (j : Fin 3) :
    (localDeliveryState x).regs (heavyBase j) =
      (NodePacking.layout ((nodeState x).comap kernel)).heavy j := by
  fin_cases j
  · rfl
  · rfl
  · change x.regs heap + 1 + x.regs (slot 2) + 1 + x.regs (slot 4) + 1 =
      x.regs heap + 2 + (x.regs (slot 2) + x.regs (slot 4)) + 1
    omega

/-- The explicit delivered state retains every non-output controller and stack register. -/
theorem localDeliveryState_preserves (x : Data 128) (i : Fin 128)
    (hh : i ≠ heap) (ht : i ≠ temporary)
    (hi : i.val < 88 ∨ 96 ≤ i.val) : (localDeliveryState x).regs i = x.regs i := by
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
  simp only [localDeliveryState, Data.set_regs, Function.update_of_ne hh,
    Function.update_of_ne ht, Function.update_of_ne hp,
    Function.update_of_ne he, Function.update_of_ne (hl 0), Function.update_of_ne (hl 1),
    Function.update_of_ne (hl 2), Function.update_of_ne (hb 0), Function.update_of_ne (hb 1),
    Function.update_of_ne (hb 2)]

/-- Every arithmetic result fits below the actual allocation endpoint. -/
theorem deliverLocal_exec {w : ℕ} (x : Data 128)
    (hone : x.regs one = 1)
    (hfit : Fits w (x.regs heap + 3 + 2 *
      (x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6)) +
      4 * x.regs groups + x.regs selected)) :
    Exec w deliverLocal x (localDeliveryState x) 21 := by
  have hbound (v : ℕ) (hv : v ≤ x.regs heap + 3 + 2 *
      (x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6)) +
      4 * x.regs groups + x.regs selected) : Fits w v := hfit.of_le hv
  have h3 : Fits w 3 := hbound _ (by omega)
  have hp₀ := hbound (x.regs heap + 3) (by omega)
  have hp₁ := hbound (x.regs heap + 3 + x.regs (slot 2)) (by omega)
  have hp₂ := hbound (x.regs heap + 3 + x.regs (slot 2) + x.regs (slot 4)) (by omega)
  have hp := hbound (x.regs heap + 3 + x.regs (slot 2) + x.regs (slot 4) +
    x.regs (slot 6)) (by omega)
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
  dsimp only [heap, slot, groups, selected, outputs, outputCount, one] at *
  ram_eval [deliverLocal, localDeliveryState, heavyBase, heavyLength, heap, slot, groups, selected,
    outputs, outputCount, packed, temporary, endpoint, one, hone, h3, hp₀, hp₁, hp₂, hp,
    hd₀, hd₁, hd₁', hd₂, hd₂', he₀, he₁, he₂, he₃, he₄, he₅, he,
    Function.update_of_ne, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
    show ∀ n : ℕ, n + n + (n + n) = 4 * n by omega]


end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

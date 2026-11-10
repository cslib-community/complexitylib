/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalFrames
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalTime
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalLocalDelivery

/-!
# Exact emissions from the complete native traversal visit

This packages the executed modulus and node calls into the worklist's semantic entry format.
The heavy lists are witnesses to actual native memory, not program inputs or advice. The old
prefix survives before the single output-pointer store, and every new packed cell equals the
existing finite node array.

## Main definitions

* `Emission`: exact metadata, old-prefix frame and heavy/packed readback of an actual live visit.

## Main results

* `emit_entry`: the complete native visit produces an exact emission with its charged bound.

These native composition proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- Semantic readback of one completed actual native visit. -/
structure Emission (Q : Finset ℕ) (Λ : ℕ) (e : Entry) (x y : Data 128)
    (published : Bool := true) where
  /-- The actual selected unsigned modulus. -/
  M : ℕ
  /-- Selection agrees with the existing finite node. -/
  exactModulus : M = (e.task.node Q Λ).M
  /-- The native fallback is positive. -/
  positive : 1 ≤ M
  /-- Both selected candidates lie within the supplied bound. -/
  upper : M ≤ x.regs limit ^ 2
  /-- Actual native compact heavy enumerations. -/
  lists : Fin 3 → List ℤ
  /-- Each enumeration is duplicate-free. -/
  nodup : ∀ j, (lists j).Nodup
  /-- The enumerated sets are exactly the existing heavy subsets. -/
  sets : ∀ j, (lists j).toFinset = Cslib.Algorithms.ThreeSum.ChanHe.heavy (e.task.sets j) M
  /-- A heavy enumeration never exceeds its parent column. -/
  length_le : ∀ j, (lists j).length ≤ (e.data j).length
  /-- The delivered unsigned lengths describe these actual lists. -/
  lengths : ∀ j, y.regs (heavyLength j) = (lists j).length
  /-- The delivered unsigned bases are the concrete heavy-array bases. -/
  bases : ∀ j, y.regs (heavyBase j) = (recordLayout x M).heavy j
  /-- Exact signed-encoded heavy-array readback. -/
  heavy : ∀ j, (Block.mk ((recordLayout x M).heavy j) (lists j).length).Realizes y.mem
    (fun i => Signed.encode (lists j)[i.val])
  /-- Exact signed-encoded packed-node readback. -/
  packed : (Block.mk (recordLayout x M).packed (4 * x.regs groups)).Realizes y.mem
    (fun i => Signed.encode ((e.task.node Q Λ).oneArray (x.regs magnitude) i.val))
  /-- The actual delivered register points to the represented packed block. -/
  packedPointer : y.regs Traversal.packed = (recordLayout x M).packed
  /-- Publication increments the count; local consumption preserves it. -/
  count : y.regs outputCount = x.regs outputCount + published.toNat
  /-- The actual advanced allocation frontier. -/
  heap_eq : y.regs heap = (recordLayout x M).endpoint
  /-- The complete node output before its single external pointer-table store. -/
  before : ℕ → ℕ
  /-- The two actual modulus searches and the node call preserve every old prefix cell. -/
  prefixMemory : ∀ p < x.regs heap, before p = x.mem p
  /-- Publication performs the single table store; local delivery leaves this memory intact. -/
  memory : y.mem = if published then
    Function.update before (x.regs outputs + x.regs outputCount) (recordLayout x M).packed
    else before
  /-- The current record, persistent controller parameters and stack dispatcher survive. -/
  registers : ∀ i : Fin 128, 64 ≤ i.val → i ≠ selected → i ≠ heap →
    i ≠ outputCount → i ≠ temporary → (i.val < 88 ∨ 96 ≤ i.val) → y.regs i = x.regs i

/-- A register fact that holds after both delivery blocks holds after the selected one. -/
private theorem delivered_regs (published : Bool) (b : Data 128) {i : Fin 128} {v : ℕ}
    (hg : (deliveryState b).regs i = v) (hl : (localDeliveryState b).regs i = v) :
    (if published then deliveryState b else localDeliveryState b).regs i = v := by
  cases published
  exacts [hl, hg]

/-- Shared semantic readback after either actual delivery block. The publication flag selects
fixed code; it is not runtime advice. The private-table fit is required only for publication. -/
theorem emission_readback {n : ℕ} (published : Bool) (x : Data 128) (e : Entry)
    (hl : e.Loaded x) (hv : e.Valid n (x.regs magnitude)) (M : ℕ) (u b : Data 128)
    (hu : ∀ i, 64 ≤ i.val → i ≠ selected → u.regs i = x.regs i)
    (hus : u.regs selected = M)
    (hprefix : ∀ p < x.regs heap, u.mem p = x.mem p)
    (hout : NodePacking.Output (recordLayout x M) e.read u.mem b.mem)
    (hb : ∀ i, 64 ≤ i.val → b.regs i = u.regs i)
    (hMpos : 1 ≤ M) (hMle : M ≤ x.regs limit ^ 2)
    (hM : M = Cslib.Algorithms.ThreeSum.ChanHe.modulus
      (Nat.primesLE (x.regs limit)) (x.regs digits)
      ((Finset.range (x.regs (arrayLength 0))).image (e.read 0))
      ((Finset.range (x.regs (arrayLength 1))).image (e.read 1))
      ((Finset.range (x.regs (arrayLength 2))).image (e.read 2)))
    (htable : published = true → x.regs outputs + x.regs outputCount < x.regs heap) :
    Nonempty (Emission (Nat.primesLE (x.regs limit)) (x.regs digits) e x
      (if published then deliveryState b else localDeliveryState b) published) := by
  have hbp (i : Fin 128) (hi : 64 ≤ i.val) (hne : i ≠ selected) :
      b.regs i = x.regs i := (hb i hi).trans (hu i hi hne)
  have hL : NodePacking.layout ((nodeState b).comap kernel) = recordLayout x M := by
    rw [nodeState_layout, hb selected (by decide), hus]
    exact recordLayout_congr x b M hbp
  have htableb (hp : published = true) :
      b.regs outputs + b.regs outputCount < b.regs heap := by
    rw [hbp outputs (by decide) (by decide), hbp outputCount (by decide) (by decide),
      hbp heap (by decide) (by decide)]
    exact htable hp
  have houtb : NodePacking.Output (NodePacking.layout ((nodeState b).comap kernel))
      e.read u.mem b.mem := by simpa only [hL] using hout
  have hd : NodePacking.Output (recordLayout x M) e.read
      (if published then Function.update u.mem (b.regs outputs + b.regs outputCount)
        (recordLayout x M).packed else u.mem)
      (if published then deliveryState b else localDeliveryState b).mem := by
    cases published with
    | false =>
      change NodePacking.Output (recordLayout x M) e.read u.mem (localDeliveryState b).mem
      rw [localDeliveryState_mem]
      exact hout
    | true =>
      change NodePacking.Output (recordLayout x M) e.read
        (Function.update u.mem (b.regs outputs + b.regs outputCount) (recordLayout x M).packed)
        (deliveryState b).mem
      have h := delivery_output b e.read u.mem houtb (htableb rfl)
      simpa only [hL] using h
  have hMexact : M = (e.task.node (Nat.primesLE (x.regs limit)) (x.regs digits)).M := by
    simpa only [hl.2.2, e.image_read, Math.Task.node, Entry.task] using hM
  have hnodeExact : NodePacking.node (recordLayout x M) e.read =
      e.task.node (Nat.primesLE (x.regs limit)) (x.regs digits) := by
    simp only [NodePacking.node, recordLayout, hl.2.2, e.image_read, Math.Task.node,
      Entry.task]
    exact congrArg (fun q => Cslib.Algorithms.ThreeSum.ChanHe.Node.mk
      (e.data 0).toFinset (e.data 1).toFinset (e.data 2).toFinset q) hMexact
  choose zs hnd hsets hcounts hdata using hd.heavy
  have hsets' (j : Fin 3) : (zs j).toFinset =
      Cslib.Algorithms.ThreeSum.ChanHe.heavy (e.task.sets j) M := by
    simpa only [recordLayout, hl.2.2, e.image_read, Entry.task] using hsets j
  have hlen (j : Fin 3) : (zs j).length ≤ (e.data j).length := by
    have hh := Cslib.Algorithms.ThreeSum.ChanHe.heavy_subset (e.task.sets j) M
    rw [← hsets' j] at hh
    have hc := Finset.card_le_card hh
    simpa only [Entry.task, List.toFinset_card_of_nodup (hnd j),
      List.toFinset_card_of_nodup (hv.1 j)] using hc
  refine ⟨⟨M, hMexact, hMpos, hMle, zs, hnd, hsets', hlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, b.mem,
    ?_, ?_, ?_⟩⟩
  · intro j
    rw [delivered_regs published b (deliveryState_heavy_length b j)
      (localDeliveryState_heavy_length b j), hL, hout.heavy_card j, ← hsets j]
    exact List.toFinset_card_of_nodup (hnd j)
  · intro j
    rw [delivered_regs published b (deliveryState_heavy_base b j)
      (localDeliveryState_heavy_base b j), hL]
  · intro j i
    exact hdata j i.val i.isLt
  · intro i
    have hp := hd.packed i.val i.isLt
    rw [hnodeExact] at hp
    simpa only [Block.read, recordLayout] using hp
  · rw [delivered_regs published b (deliveryState_packed b) (localDeliveryState_packed b), hL]
  · cases published with
    | false =>
      change (localDeliveryState b).regs outputCount = x.regs outputCount + 0
      rw [localDeliveryState_count, hbp outputCount (by decide) (by decide), Nat.add_zero]
    | true =>
      change (deliveryState b).regs outputCount = x.regs outputCount + 1
      rw [deliveryState_count, hbp outputCount (by decide) (by decide)]
  · rw [delivered_regs published b (deliveryState_heap b) (localDeliveryState_heap b), hL]
  · intro p hp
    exact (hout.frame p (Or.inl hp)).trans (hprefix p hp)
  · cases published with
    | false => exact localDeliveryState_mem b
    | true =>
      change (deliveryState b).mem =
        Function.update b.mem (x.regs outputs + x.regs outputCount) (recordLayout x M).packed
      rw [deliveryState_mem, hbp outputs (by decide) (by decide),
        hbp outputCount (by decide) (by decide)]
      congr 1
      exact (deliveryState_packed b).trans (congrArg NodePacking.Layout.packed hL)
  · intro i hi hsel hh hc ht hw
    cases published with
    | false =>
      exact (localDeliveryState_preserves b i hh ht hw).trans (hbp i hi hsel)
    | true => exact (deliveryState_preserves b i hh hc ht hw).trans (hbp i hi hsel)

/-- Execute both complete searches and the complete node construction for an actual loaded
entry. All heavy witnesses come from the executed memory and all control work is charged. -/
theorem emit_entry {w n : ℕ} (x : Data 128) (e : Entry) (hl : e.Loaded x)
    (hv : e.Valid n (x.regs magnitude)) (hs : e.Stored x.mem)
    (hm : 2 ≤ x.regs limit)
    (hmod : GenericRAM.Signed.Fits w ((x.regs limit ^ 2 : ℕ) : ℤ))
    (hbudget : Fits (w + 2) (Modulus.budget ((modulusState x).comap kernel)))
    (hnode : ∀ M, 1 ≤ M → M ≤ x.regs limit ^ 2 →
      GenericRAM.Signed.Fits w ((recordLayout x M).budget : ℤ))
    (hN : 2 * x.regs limit ^ 2 ≤ x.regs groups)
    (hcard : x.regs primeCount = (Nat.primesLE (x.regs limit)).card)
    (hbefore : x.regs bitmap + x.regs limit < x.regs heap)
    (hbitmap : ∀ q ≤ x.regs limit,
      x.mem (x.regs bitmap + q) = if q.Prime then 1 else 0)
    (hvalues : ∀ j i, i < (e.data j).length → GenericRAM.Signed.Fits w (e.read j i))
    (hsrc : ∀ j, e.source j + (e.data j).length ≤ x.regs heap)
    (hone : x.regs one = 1)
    (htable : x.regs outputs + x.regs outputCount < x.regs heap) :
    ∃ y, ExecWithin (w + 2) visit x y
      (visitTime n (x.regs limit) (x.regs groups)) ∧
      Nonempty (Emission (Nat.primesLE (x.regs limit)) (x.regs digits) e x y) := by
  classical
  obtain ⟨M, u, b, he, hu, hus, hprefix, hout, hb, hMpos, hMle, hM⟩ :=
    visit_exec x e.read hm hmod hbudget hnode hN hcard hbefore hbitmap
      (by simpa only [hl.2.2] using hvalues)
      (by intro j i hi; exact hv.natAbs_le j i ((hl.2.2 j) ▸ hi))
      (by simpa only [hl.2.1, hl.2.2] using hsrc)
      (by simpa only [hl.2.1, hl.2.2] using hs.input)
      (by intro j; simpa only [hl.2.2] using e.read_injOn j (hv.1 j)) hone htable
  refine ⟨deliveryState b, he.mono (visit_cost_le x n (x.regs limit) (x.regs groups) M
    (by intro j; rw [hl.2.2]; exact hv.length_le j) le_rfl le_rfl hMle), ?_⟩
  exact emission_readback true x e hl hv M u b hu hus hprefix hout hb hMpos hMle hM
    (fun _ => htable)

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

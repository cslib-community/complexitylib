/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalProgram
import Complexity.Algorithms.ThreeSum.ChanHe.SelectorBounds

/-!
# Actual native argument delivery in the Chan–He traversal

The current record and persistent parameters are delivered to the existing complete modulus
and node programs in registers 0–63. Every copy and histogram-base addition is a native
instruction. The record, controller parameters and native word-stack registers survive setup.

## Main definitions

* `modulusState`, `nodeState`: exact states after the two native argument blocks.

## Main results

* `prepareModulus_exec`: fourteen charged instructions, including all histogram-base additions.
* `prepareNode_exec`: ten charged native register copies.
* `modulusState_preserves`, `nodeState_preserves`: all registers above the kernel survive.

These calling-convention proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- The exact state after the fourteen-instruction modulus argument block. -/
def modulusState (x : Data 128) : Data 128 :=
  (((((((((((((x.set (kernel (CountCall.source 0)) (x.regs (slot 1))).set
    (kernel (CountCall.length 0)) (x.regs (slot 2))).set
    (kernel (CountCall.source 1)) (x.regs (slot 3))).set
    (kernel (CountCall.length 1)) (x.regs (slot 4))).set
    (kernel (CountCall.source 2)) (x.regs (slot 5))).set
    (kernel (CountCall.length 2)) (x.regs (slot 6))).set
    (kernel CountCall.scratch) (x.regs heap)).set
    (kernel CountCall.histogram) (x.regs heap + x.regs (slot 2))).set
    (kernel CountCall.histogram) (x.regs heap + x.regs (slot 2) + x.regs (slot 4))).set
    (kernel CountCall.histogram)
      (x.regs heap + x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6))).set
    (kernel Search.limit) (x.regs limit)).set (kernel Search.primes) (x.regs bitmap)).set
    (kernel CollisionTest.card) (x.regs primeCount)).set (kernel Modulus.digits) (x.regs digits)

/-- The exact state after the ten-instruction node argument block. -/
def nodeState (x : Data 128) : Data 128 :=
  (((((((((x.set (kernel (NodePacking.source 0)) (x.regs (slot 1))).set
    (kernel (NodePacking.length 0)) (x.regs (slot 2))).set
    (kernel (NodePacking.source 1)) (x.regs (slot 3))).set
    (kernel (NodePacking.length 1)) (x.regs (slot 4))).set
    (kernel (NodePacking.source 2)) (x.regs (slot 5))).set
    (kernel (NodePacking.length 2)) (x.regs (slot 6))).set
    (kernel NodePacking.base) (x.regs heap)).set
    (kernel NodePacking.groups) (x.regs groups)).set
    (kernel NodePacking.magnitude) (x.regs magnitude)).set
    (kernel NodePacking.modulus) (x.regs selected)

/-- The existing node layout instantiated by the traversal record and one computed modulus. -/
def recordLayout (x : Data 128) (M : ℕ) : NodePacking.Layout :=
  ⟨x.regs heap, fun j => x.regs (arrayLength j), x.regs groups, M, x.regs magnitude⟩

/-- The delivered node ABI has exactly the current record's layout. -/
theorem nodeState_layout (x : Data 128) :
    NodePacking.layout ((nodeState x).comap kernel) = recordLayout x (x.regs selected) := by
  unfold NodePacking.layout recordLayout
  congr 1
  funext j
  fin_cases j <;> rfl

/-- The layout reads only persistent record/controller fields outside the selected-modulus word. -/
theorem recordLayout_congr (x y : Data 128) (M : ℕ)
    (h : ∀ i, 64 ≤ i.val → i ≠ selected → y.regs i = x.regs i) :
    recordLayout y M = recordLayout x M := by
  unfold recordLayout
  congr 1
  · exact h heap (by decide) (by decide)
  · funext j
    fin_cases j <;> exact h _ (by decide) (by decide)
  · exact h groups (by decide) (by decide)
  · exact h magnitude (by decide) (by decide)

/-- The final endpoint formula expressed entirely in the persistent traversal ABI. -/
theorem recordLayout_endpoint (x : Data 128) (M : ℕ) :
    (recordLayout x M).endpoint = x.regs heap + 3 + 2 *
      (x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6)) + 4 * x.regs groups + M := by
  rw [NodePacking.Layout.endpoint_eq]
  rfl

private theorem kernel_ne {i : Fin 128} (hi : 64 ≤ i.val) (j : Fin 64) : i ≠ kernel j := by
  intro h
  have := congrArg Fin.val h
  dsimp [kernel] at this
  omega

private theorem set_kernel_regs (i : Fin 128) (hi : 64 ≤ i.val)
    (x : Data 128) (j : Fin 64) (v : ℕ) :
    (x.set (kernel j) v).regs i = x.regs i := Function.update_of_ne (kernel_ne hi j) ..

/-- Modulus argument delivery preserves every traversal and stack register. -/
theorem modulusState_preserves (x : Data 128) (i : Fin 128) (hi : 64 ≤ i.val) :
    (modulusState x).regs i = x.regs i := by
  simp only [modulusState, set_kernel_regs i hi]

/-- Node argument delivery preserves every traversal and stack register. -/
theorem nodeState_preserves (x : Data 128) (i : Fin 128) (hi : 64 ≤ i.val) :
    (nodeState x).regs i = x.regs i := by
  simp only [nodeState, set_kernel_regs i hi]

/-- Native modulus argument delivery charges the three histogram-base additions too.
A fit for their largest value derives all intermediate address fits. -/
theorem prepareModulus_exec {w : ℕ} (x : Data 128)
    (h : Fits w (x.regs heap + x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6))) :
    Exec w prepareModulus x (modulusState x) 14 := by
  have h₀ : Fits w (x.regs heap + x.regs (slot 2)) := h.of_le (by omega)
  have h₁ : Fits w (x.regs heap + x.regs (slot 2) + x.regs (slot 4)) := h.of_le (by omega)
  dsimp only [heap, slot] at h₀ h₁ h
  ram_eval [prepareModulus, modulusState, kernel, slot, CountCall.source, CountCall.length,
    CountCall.scratch, CountCall.histogram, Search.limit, Search.primes, CollisionTest.card,
    Modulus.digits, heap, limit, bitmap, primeCount, digits, h₀, h₁, h]

/-- Complete node argument delivery is ten native copies; no address arithmetic is hidden. -/
theorem prepareNode_exec {w : ℕ} (x : Data 128) :
    Exec w prepareNode x (nodeState x) 10 := by
  ram_eval [prepareNode, nodeState, kernel, slot, NodePacking.source, NodePacking.length,
    NodePacking.base, NodePacking.groups, NodePacking.magnitude, NodePacking.modulus,
    heap, groups, magnitude, selected]

private theorem kernel_injective : Function.Injective kernel := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 128 => i.val) h)

private theorem extend_kernel_regs (y : Data 64) (x : Data 128) (i : Fin 128)
    (hi : 64 ≤ i.val) : (y.extend kernel x).regs i = x.regs i := by
  change Function.extend kernel y.regs x.regs i = x.regs i
  apply Function.extend_apply'
  rintro ⟨j, hj⟩
  exact kernel_ne hi j hj.symm

/-- Actual argument delivery and complete two-prime computation inside the traversal's fixed
register file. The mathematical filters may fail; their default-one selections are still bounded.
The bitmap/count are the outputs of the separate native prime-table routine. -/
theorem callModulus_exec {w : ℕ} (x : Data 128) (values : Fin 3 → ℕ → ℤ)
    (hm : 2 ≤ x.regs limit)
    (hmod : GenericRAM.Signed.Fits w ((x.regs limit ^ 2 : ℕ) : ℤ))
    (hbudget : Fits (w + 2) (Modulus.budget ((modulusState x).comap kernel)))
    (hcard : x.regs primeCount = (Nat.primesLE (x.regs limit)).card)
    (hbefore : x.regs bitmap + x.regs limit < x.regs heap)
    (hbitmap : ∀ q ≤ x.regs limit,
      x.mem (x.regs bitmap + q) = if q.Prime then 1 else 0)
    (hvalues : ∀ j i, i < x.regs (arrayLength j) → GenericRAM.Signed.Fits w (values j i))
    (hsrc : ∀ j, x.regs (arraySource j) + x.regs (arrayLength j) ≤ x.regs heap)
    (hinput : ∀ j i, i < x.regs (arrayLength j) →
      x.mem (x.regs (arraySource j) + i) = Signed.encode (values j i))
    (hinj : ∀ j, Set.InjOn (values j)
      (↑(Finset.range (x.regs (arrayLength j))) : Set ℕ)) :
    ∃ y, ExecWithin (w + 2) (.seq prepareModulus (Modulus.program.rename kernel)) x y
        (14 + Modulus.cost ((modulusState x).comap kernel)) ∧
      (∀ i, 64 ≤ i.val → y.regs i = x.regs i) ∧
      (∀ a < x.regs heap, y.mem a = x.mem a) ∧
      y.regs (kernel Modulus.output) = Cslib.Algorithms.ThreeSum.ChanHe.modulus
        (Nat.primesLE (x.regs limit)) (x.regs digits)
        ((Finset.range (x.regs (arrayLength 0))).image (values 0))
        ((Finset.range (x.regs (arrayLength 1))).image (values 1))
        ((Finset.range (x.regs (arrayLength 2))).image (values 2)) ∧
      1 ≤ y.regs (kernel Modulus.output) ∧ y.regs (kernel Modulus.output) ≤ x.regs limit ^ 2 := by
  let a := modulusState x
  let z := a.comap kernel
  have hn (j : Fin 3) : z.regs (CountCall.length j) = x.regs (arrayLength j) := by
    fin_cases j <;> rfl
  have hs (j : Fin 3) : z.regs (CountCall.source j) = x.regs (arraySource j) := by
    fin_cases j <;> rfl
  have hzm : z.regs Search.limit = x.regs limit := rfl
  have hzd : z.regs Modulus.digits = x.regs digits := rfl
  have hhist : Fits (w + 2)
      (x.regs heap + x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6)) := by
    change Fits (w + 2) (z.regs CountCall.histogram)
    have hbz : Fits (w + 2) (Modulus.budget z) := hbudget
    apply hbz.of_le
    dsimp only [Modulus.budget]
    omega
  have ha := prepareModulus_exec x hhist
  obtain ⟨b, hb, _, hprefix, _, hout⟩ := Modulus.exec z values hm hmod hbudget hcard hbefore
    hbitmap
    (by intro j i hi; exact hvalues j i ((hn j) ▸ hi))
    (by intro j; change z.regs (CountCall.source j) + z.regs (CountCall.length j) ≤ x.regs heap
        rw [hs j, hn j]; exact hsrc j)
    (by
      intro j
      change x.regs heap + z.regs (CountCall.length j) ≤
        x.regs heap + x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6)
      rw [hn j]
      fin_cases j
      · change x.regs heap + x.regs (slot 2) ≤ _
        omega
      · change x.regs heap + x.regs (slot 4) ≤ _
        omega
      · change x.regs heap + x.regs (slot 6) ≤ _
        omega)
    (by intro j i hi; change x.mem (z.regs (CountCall.source j) + i) = _
        rw [hs j]; exact hinput j i ((hn j) ▸ hi))
    (by intro j; simpa only [hn j] using hinj j)
  let y := b.extend kernel a
  have hout' : y.regs (kernel Modulus.output) = Cslib.Algorithms.ThreeSum.ChanHe.modulus
      (Nat.primesLE (x.regs limit)) (x.regs digits)
      ((Finset.range (x.regs (arrayLength 0))).image (values 0))
      ((Finset.range (x.regs (arrayLength 1))).image (values 1))
      ((Finset.range (x.regs (arrayLength 2))).image (values 2)) := by
    change Function.extend kernel b.regs a.regs (kernel Modulus.output) = _
    rw [kernel_injective.extend_apply]
    simpa only [hn, hzm, hzd] using hout
  refine ⟨y, ha.within.seq (hb.rename kernel_injective), ?_, ?_, hout', ?_⟩
  · intro i hi
    exact (extend_kernel_regs b a i hi).trans (modulusState_preserves x i hi)
  · intro p hp
    exact hprefix p hp
  · rw [hout']
    exact Cslib.Algorithms.ThreeSum.ChanHe.modulus_bounds_of_candidates (by omega)
      (fun q hq => (Nat.prime_of_mem_primesLE hq).two_le.trans' (by decide))
      (fun _ hq => Nat.le_of_mem_primesLE hq) _ _ _ _

/-- Ten actual argument copies followed by the complete native heavy/packed-node program.
The existing exact semantic output and the full allocation frame survive register renaming. -/
theorem callNode_exec {w : ℕ} (x : Data 128) (values : Fin 3 → ℕ → ℤ)
    (hM : 0 < x.regs selected) (hN : 2 * x.regs selected ≤ x.regs groups)
    (hwidth : GenericRAM.Signed.Fits w
      ((NodePacking.layout ((nodeState x).comap kernel)).budget : ℤ))
    (hsrc : ∀ j, x.regs (arraySource j) + x.regs (arrayLength j) ≤ x.regs heap)
    (hbdd : ∀ j i, i < x.regs (arrayLength j) → (values j i).natAbs ≤ x.regs magnitude)
    (hinput : ∀ j i, i < x.regs (arrayLength j) →
      x.mem (x.regs (arraySource j) + i) = Signed.encode (values j i))
    (hinj : ∀ j, Set.InjOn (values j)
      (↑(Finset.range (x.regs (arrayLength j))) : Set ℕ)) :
    let L := NodePacking.layout ((nodeState x).comap kernel)
    ∃ y, ExecWithin (w + 2) (.seq prepareNode (NodePacking.program.rename kernel)) x y
        (10 + 66 * L.total + 15 * L.M + 12 * L.N + 228) ∧
      NodePacking.Output L values x.mem y.mem ∧
      ∀ i, 64 ≤ i.val → y.regs i = x.regs i := by
  let a := nodeState x
  let z := a.comap kernel
  let L := NodePacking.layout z
  have hn (j : Fin 3) : L.n j = x.regs (arrayLength j) := by fin_cases j <;> rfl
  have hs (j : Fin 3) : z.regs (NodePacking.source j) = x.regs (arraySource j) := by
    fin_cases j <;> rfl
  have hinj' (j : Fin 3) : Set.InjOn (values j) (↑(Finset.range (L.n j)) : Set ℕ) := by
    simpa only [hn] using hinj j
  obtain ⟨b, hb, hmem, _⟩ := NodePacking.exec z values hM hN hwidth
    (by intro j; rw [hs j]; change x.regs (arraySource j) + L.n j ≤ x.regs heap
        rw [hn j]; exact hsrc j)
    (by intro j i hi; exact hbdd j i ((hn j) ▸ hi))
    (by intro j i hi; change x.mem (z.regs (NodePacking.source j) + i) = _
        rw [hs j]; exact hinput j i ((hn j) ▸ hi)) hinj'
  refine ⟨b.extend kernel a, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using
      (prepareNode_exec (w := w + 2) x).within.seq (hb.rename kernel_injective)
  · change NodePacking.Output L values z.mem b.mem
    rw [hmem]
    exact NodePacking.memory_output L values z.mem hM hN hinj'
  · intro i hi
    exact (extend_kernel_regs b a i hi).trans (nodeState_preserves x i hi)

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

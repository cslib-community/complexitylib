/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalCall

/-!
# Charged Chan–He node construction before publication

The two complete native kernels construct the actual modulus, heavy lists and packed node.
This boundary exposes their readback and prefix frame before any output-pointer table store,
so catalogue delivery and an in-place solver visitor share the same kernel execution proof.

## Main results

* `construct_exec`: actual complete construction, charging argument preparation and modulus copy.

This is an original composition of the existing native kernels. It supplies no runtime advice
and makes no claim about a complete traversal, initialized input or solver callback.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- Both complete native kernels and every argument instruction, before output publication.
The final state retains actual heavy/packed readback and can instead enter a solver callback. -/
def construct : Code .standard 128 :=
  .seq (.seq prepareModulus (Modulus.program.rename kernel))
    (.seq (.op (.copy selected (kernel Modulus.output)))
      (.seq prepareNode (NodePacking.program.rename kernel)))

/-- Execute the complete modulus and node builders without publishing a catalogue pointer.
Both intermediate states are reached by charged native instructions. -/
theorem construct_exec {w : ℕ} (x : Data 128) (values : Fin 3 → ℕ → ℤ)
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
    (hvalues : ∀ j i, i < x.regs (arrayLength j) → GenericRAM.Signed.Fits w (values j i))
    (hbdd : ∀ j i, i < x.regs (arrayLength j) → (values j i).natAbs ≤ x.regs magnitude)
    (hsrc : ∀ j, x.regs (arraySource j) + x.regs (arrayLength j) ≤ x.regs heap)
    (hinput : ∀ j i, i < x.regs (arrayLength j) →
      x.mem (x.regs (arraySource j) + i) = Signed.encode (values j i))
    (hinj : ∀ j, Set.InjOn (values j)
      (↑(Finset.range (x.regs (arrayLength j))) : Set ℕ)) :
    ∃ (M : ℕ) (u b : Data 128),
      ExecWithin (w + 2) construct x b
        (Modulus.cost ((modulusState x).comap kernel) +
          66 * (recordLayout x M).total + 15 * M + 12 * x.regs groups + 253) ∧
      (∀ i, 64 ≤ i.val → i ≠ selected → u.regs i = x.regs i) ∧ u.regs selected = M ∧
      (∀ p < x.regs heap, u.mem p = x.mem p) ∧
      NodePacking.Output (recordLayout x M) values u.mem b.mem ∧
      (∀ i, 64 ≤ i.val → b.regs i = u.regs i) ∧
      1 ≤ M ∧ M ≤ x.regs limit ^ 2 ∧
      M = Cslib.Algorithms.ThreeSum.ChanHe.modulus
        (Nat.primesLE (x.regs limit)) (x.regs digits)
        ((Finset.range (x.regs (arrayLength 0))).image (values 0))
        ((Finset.range (x.regs (arrayLength 1))).image (values 1))
        ((Finset.range (x.regs (arrayLength 2))).image (values 2)) := by
  obtain ⟨a, ha, hpa, hprefix, hM, hMpos, hMle⟩ :=
    callModulus_exec x values hm hmod hbudget hcard hbefore hbitmap hvalues hsrc hinput hinj
  let M := a.regs (kernel Modulus.output)
  let u := a.set selected M
  have hcopy : Exec (B := .standard) (w + 2)
      (.op (.copy selected (kernel Modulus.output))) a u 1 := Exec.copy
  have hu (i : Fin 128) (hi : 64 ≤ i.val) (hne : i ≠ selected) :
      u.regs i = x.regs i := by
    simp only [u, Data.set_regs, Function.update_of_ne hne, hpa i hi]
  have hus : u.regs selected = M := rfl
  have huSource (j : Fin 3) : u.regs (arraySource j) = x.regs (arraySource j) := by
    fin_cases j <;> exact hu _ (by decide) (by decide)
  have huLength (j : Fin 3) : u.regs (arrayLength j) = x.regs (arrayLength j) := by
    fin_cases j <;> exact hu _ (by decide) (by decide)
  have huHeap : u.regs heap = x.regs heap := hu _ (by decide) (by decide)
  have huGroups : u.regs groups = x.regs groups := hu _ (by decide) (by decide)
  have huMagnitude : u.regs magnitude = x.regs magnitude := hu _ (by decide) (by decide)
  have hL : NodePacking.layout ((nodeState u).comap kernel) = recordLayout x M := by
    rw [nodeState_layout, hus]
    exact recordLayout_congr x u M hu
  have hwidth : GenericRAM.Signed.Fits w
      ((NodePacking.layout ((nodeState u).comap kernel)).budget : ℤ) := by
    rw [hL]
    exact hnode M hMpos hMle
  obtain ⟨b, hb, hout, hpb⟩ := callNode_exec u values (by omega)
    (by rw [hus, huGroups]; omega) hwidth
    (by intro j; rw [huSource j, huLength j, huHeap]; exact hsrc j)
    (by intro j i hi; rw [huMagnitude]; exact hbdd j i ((huLength j) ▸ hi))
    (by
      intro j i hi
      rw [huSource j]
      have hi' : i < x.regs (arrayLength j) := (huLength j) ▸ hi
      have hs := hsrc j
      rw [show u.mem (x.regs (arraySource j) + i) = x.mem (x.regs (arraySource j) + i)
        from hprefix _ (by omega)]
      exact hinput j i hi')
    (by intro j; simpa only [huLength] using hinj j)
  rw [hL] at hb hout
  refine ⟨M, u, b, ?_, hu, hus, hprefix, hout, hpb, hMpos, hMle, hM⟩
  have he := ha.seq (hcopy.within.seq hb)
  exact he.mono (by dsimp only [recordLayout] at he ⊢; omega)

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

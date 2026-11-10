/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalConstruct
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalDeliver

/-!
# Complete charged native work at one live traversal entry

Both native modulus searches, every counting call, the complete node builder and output delivery
are composed here. The intermediate states are exposed as proof witnesses so the worklist proof
can reuse the node builder's existing exact heavy/packed readback and allocation frame.

## Main results

* `visit_exec`: execution of the complete native visit, charging both kernel calls, every argument
  instruction, the modulus copy and all output-delivery instructions.

These are original native composition proofs. The global traversal and initialized-input width
and asymptotic bounds remain separate from this local calling-convention theorem.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- The full native live-node visit, including all setup and output delivery. The returned
intermediate states are reached by actual instructions, not supplied node or preprocessing oracles.
The node's signed envelope derives the delivery address/counter fits. -/
theorem visit_exec {w : ℕ} (x : Data 128) (values : Fin 3 → ℕ → ℤ)
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
      (↑(Finset.range (x.regs (arrayLength j))) : Set ℕ))
    (hone : x.regs one = 1)
    (htable : x.regs outputs + x.regs outputCount < x.regs heap) :
    ∃ (M : ℕ) (u b : Data 128),
      ExecWithin (w + 2) visit x (deliveryState b)
        (Modulus.cost ((modulusState x).comap kernel) +
          66 * (recordLayout x M).total + 15 * M + 12 * x.regs groups + 277) ∧
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
  obtain ⟨M, u, b, he, hu, hus, hprefix, hout, hpb, hMpos, hMle, hM⟩ :=
    construct_exec x values hm hmod hbudget hnode hN hcard hbefore hbitmap
      hvalues hbdd hsrc hinput hinj
  have hbp (i : Fin 128) (hi : 64 ≤ i.val) (hne : i ≠ selected) :
      b.regs i = x.regs i := (hpb i hi).trans (hu i hi hne)
  have hbL : NodePacking.layout ((nodeState b).comap kernel) = recordLayout x M := by
    rw [nodeState_layout, hpb selected (by decide), hus]
    exact recordLayout_congr x b M hbp
  have hbOne : b.regs one = 1 := (hbp _ (by decide) (by decide)).trans hone
  have hbTable : b.regs outputs + b.regs outputCount < b.regs heap := by
    rw [hbp outputs (by decide) (by decide), hbp outputCount (by decide) (by decide),
      hbp heap (by decide) (by decide)]
    exact htable
  have hEnd : Fits (w + 2) ((recordLayout x M).endpoint) :=
    (Signed.unsigned_fits_of_signed (hnode M hMpos hMle)).of_le
      (recordLayout x M).bounds.1
  have hEndEq : (recordLayout x M).endpoint = b.regs heap + 3 + 2 *
      (b.regs (slot 2) + b.regs (slot 4) + b.regs (slot 6)) +
      4 * b.regs groups + b.regs selected := by
    rw [← hbL, nodeState_layout, recordLayout_endpoint]
  rw [hEndEq] at hEnd
  have hd := deliver_exec b hbOne hbTable hEnd
  refine ⟨M, u, b, ?_, hu, hus, hprefix, hout, hpb, hMpos, hMle, hM⟩
  obtain ⟨tk, htk, hek⟩ := he
  cases hek with
  | seq hm hn =>
    cases hm with
    | seq hpM hkM =>
      cases hn with
      | seq hcopy hn =>
        cases hn with
        | seq hpN hkN =>
          have he := hpM.seq (hkM.seq (hcopy.seq (hpN.seq (hkN.seq hd))))
          exact he.within.mono (by omega)

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

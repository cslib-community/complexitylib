/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Control

/-!
# Actual native leaf multiplication

## Main results

* `PrunedQuery.exec_leafProduct`: load the two encoded leaf words and store their exact signed
  product, within nineteen native instructions.
* `PrunedQuery.exec_leaf`: take the actual empty/nonempty branch and return to the parent.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The existing signed workspace and the indexed-load address register. -/
def LeafLocal (i : Fin registers) : Prop := i.val < 9 ∨ i = address

instance (i : Fin registers) : Decidable (LeafLocal i) :=
  inferInstanceAs (Decidable (i.val < 9 ∨ i = address))

private theorem leafProduct_preserves (i : Fin registers) :
    ¬LeafLocal i → leafProduct.Preserves i := by decide +kernel +revert

/-- Both loads, the existing fourteen-instruction signed multiplication kernel and the store
are charged. The ordinary mathematical product must fit the source signed width. -/
theorem exec_leafProduct {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (hab : GenericRAM.Signed.Fits w (a * b))
    (x : Data registers)
    (hleft : x.mem (x.regs arrayA + x.regs leafPrefix) = encode a)
    (hright : x.mem (x.regs arrayB + x.regs leafPrefix) = encode b)
    (hp : Fits (w + 2) (x.regs arrayA + x.regs leafPrefix))
    (hq : Fits (w + 2) (x.regs arrayB + x.regs leafPrefix)) :
    ∃ y, ExecWithin (w + 2) leafProduct x y 19 ∧
      y.mem = Function.update x.mem (x.regs valueBase) (encode (a * b)) ∧
      (∀ i, ¬LeafLocal i → y.regs i = x.regs i) := by
  let z := ((((x.set address (x.regs arrayA + x.regs leafPrefix)).set left (encode a)).set
    address (x.regs arrayB + x.regs leafPrefix)).set right (encode b))
  have hload : ExecWithin (w + 2) leafLoad x z 4 := by
    ram_eval [leafLoad, z, hleft, hright, hp, hq, address, arrayA, arrayB, leafPrefix,
      left, right, Fin.mk.injEq]
  obtain ⟨u, hu, hproduct, hframe⟩ := Signed.exec_multiply (r := 87) ha hb hab z
    (by simp +decide [z, left, right, address]) (by simp [z])
  have hv : u.regs valueBase = x.regs valueBase := by
    rw [hframe.2 valueBase (Or.inr (by decide))]
    simp +decide [z, valueBase, address, left, right]
  have hproduct' : u.regs result = encode (a * b) := hproduct
  let y := u.write (x.regs valueBase) (encode (a * b))
  have hstore : ExecWithin (w + 2)
      (ram[ *valueBase ← result ] : Code .standard registers) u y 1 := by
    ram_eval [y, hv, hproduct']
  have he : ExecWithin (w + 2) leafProduct x y 19 := hload.seq (hu.seq hstore)
  refine ⟨y, he, ?_, fun i hi => he.regs_eq (leafProduct_preserves i hi)⟩
  simpa only [y, Data.write_mem, z, Data.set_mem] using
    congrArg (fun mem => Function.update mem (x.regs valueBase) (encode (a * b))) hframe.1

/-- Registers used by the full leaf phase, including its actual parent-return decision. -/
def LeafReturnLocal (i : Fin registers) : Prop :=
  LeafLocal i ∨ PopLocal i ∨ i = temporary

instance (i : Fin registers) : Decidable (LeafReturnLocal i) :=
  inferInstanceAs (Decidable (LeafLocal i ∨ PopLocal i ∨ i = temporary))

private theorem leaf_preserves (i : Fin registers) :
    ¬LeafReturnLocal i → leaf.Preserves i := by decide +kernel +revert

/-- The empty leaf performs no operand loads or multiplication. A requested leaf computes
its signed product. Both execute the real return branch; root termination and parent
accumulation are decided by the stored depth register, not by an external call rule. -/
theorem exec_leaf {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (hab : GenericRAM.Signed.Fits w (a * b))
    (x : Data registers) (h0 : x.regs nil = 0) (h1 : x.regs one = 1)
    (hleft : x.mem (x.regs arrayA + x.regs leafPrefix) = encode a)
    (hright : x.mem (x.regs arrayB + x.regs leafPrefix) = encode b)
    (hp : Fits (w + 2) (x.regs arrayA + x.regs leafPrefix))
    (hq : Fits (w + 2) (x.regs arrayB + x.regs leafPrefix))
    (hd : Fits (w + 2) (x.regs level + 2)) :
    ∃ y, ExecWithin (w + 2) leaf x y 24 ∧
      y.mem = (if x.regs count = 0 then x.mem else
        Function.update x.mem (x.regs valueBase) (encode (a * b))) ∧
      y.regs level = (if x.regs level = 0 then 0 else x.regs level - 1) ∧
      y.regs mode = (if x.regs level = 0 then x.regs mode else 2) ∧
      y.regs active = (if x.regs level = 0 then 0 else x.regs active) ∧
      (∀ i, ¬LeafReturnLocal i → y.regs i = x.regs i) := by
  have hpre : ∃ v, ExecWithin (w + 2)
      (ram[ if nil < count then [ ⟪leafProduct⟫ ] else [ temporary ← temporary ] ])
      x v 20 ∧
      v.mem = (if x.regs count = 0 then x.mem else
        Function.update x.mem (x.regs valueBase) (encode (a * b))) ∧
      (∀ i, ¬LeafLocal i → v.regs i = x.regs i) := by
    by_cases hc : x.regs count = 0
    · have hcopy : ExecWithin (w + 2)
          (ram[ temporary ← temporary ] : Code .standard registers) x x 1 := by
        simpa only [Data.set, Function.update_eq_self] using
          (Exec.copy (w := w + 2) (B := .standard) (x := x)
            (d := temporary) (s := temporary)).within
      have he : ExecWithin (w + 2)
          (ram[ if nil < count then [ ⟪leafProduct⟫ ] else [ temporary ← temporary ] ])
          x x 3 := by
        exact hcopy.branch_neg (by simp only [Cond.holds_lt, h0, hc, lt_self_iff_false,
          not_false_eq_true])
      exact ⟨x, he.mono (by decide), by simp only [hc, ↓reduceIte], fun _ _ => rfl⟩
    · obtain ⟨v, hv, hmem, hreg⟩ := exec_leafProduct ha hb hab x hleft hright hp hq
      have hcond : (Cond.lt nil count).Holds x := by
        simpa only [Cond.holds_lt, h0] using Nat.pos_of_ne_zero hc
      exact ⟨v, hv.branch_pos hcond, by simpa only [hc, ↓reduceIte] using hmem, hreg⟩
  obtain ⟨v, hv, hmem, hreg⟩ := hpre
  have hv0 := (hreg nil (by decide)).trans h0
  have hv1 := (hreg one (by decide)).trans h1
  have hvd := hreg level (by decide)
  have hvm := hreg mode (by decide)
  have hva := hreg active (by decide)
  obtain ⟨y, hy, hymem, hyl, hym, hya, _⟩ := exec_pop v hv0 hv1
    (by simpa only [hvd] using hd)
  have he : ExecWithin (w + 2) leaf x y 24 := hv.seq hy
  exact ⟨y, he, hymem.trans hmem, by simpa only [hvd] using hyl,
    by simpa only [hvd, hvm] using hym, by simpa only [hvd, hva] using hya,
    fun i hi => he.regs_eq (leaf_preserves i hi)⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

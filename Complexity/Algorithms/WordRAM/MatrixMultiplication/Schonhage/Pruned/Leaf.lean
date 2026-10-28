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

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

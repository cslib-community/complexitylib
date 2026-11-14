/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UOV.Field

/-!
# UOV concrete-field encoding clients

These clients check nontrivial nibble and byte round trips, both UOV quotient relations, and the
source's low-nibble-first packing.  The root and pair checks are convention-sensitive: reversing
the coefficient order maps `X` to a different bit, while reversing the element order maps `0x12`
to `0x21`.
-/

public section

namespace CslibFrontierTests.Crypto.UOVField

open Cslib Cslib.Crypto.UOV

/-! ### Positive round trips -/

example : f16EquivNibble (f16EquivNibble.symm ⟨0xb, by decide⟩) = ⟨0xb, by decide⟩ :=
  f16EquivNibble.apply_symm_apply _

example : f256EquivByte (f256EquivByte.symm ⟨0xa5, by decide⟩) = ⟨0xa5, by decide⟩ :=
  f256EquivByte.apply_symm_apply _

example : f16PairEquivByte (f16PairEquivByte.symm ⟨0xa5, by decide⟩) = ⟨0xa5, by decide⟩ :=
  f16PairEquivByte.apply_symm_apply _

/-! ### Source polynomial evaluations and ordering conventions -/

example :
    (f16EquivNibble (AdjoinRoot.root (leastIrreducible 4))).val = 2 :=
  val_f16EquivNibble_root

example :
    (f16EquivNibble (AdjoinRoot.root (leastIrreducible 4) ^ 4)).val = 0x03 :=
  val_f16EquivNibble_root_pow_four

example :
    (f256EquivByte (AdjoinRoot.root (leastIrreducible 8) ^ 8)).val = 0x1b :=
  val_f256EquivByte_root_pow_eight

-- The first element is `X` in the low nibble; the second is `1` in the high nibble.
example :
    (f16PairEquivByte (AdjoinRoot.root (leastIrreducible 4), 1)).val = 0x12 := by
  rw [val_f16PairEquivByte, val_f16EquivNibble_root, val_f16EquivNibble_one] <;> norm_num

end CslibFrontierTests.Crypto.UOVField

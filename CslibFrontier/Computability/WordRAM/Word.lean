/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Defs

/-!
# Truncation of Natural Numbers to `w`-Bit Words

Computable truncation `Cslib.WordRAM.wordOfNat w v : Fin (2 ^ w)` mapping a natural number `v` below
`2 ^ w` (`Fits w v`) to `⟨v, _⟩` and defaulting out-of-range values to `0`, shared between Word-RAM
table-extraction and cell-probe simulation layers.

## Main definitions

* `Cslib.WordRAM.wordOfNat`: truncate `v : ℕ` into `Fin (2 ^ w)`, returning `0` when `2 ^ w ≤ v`.

## Main results

* `Cslib.WordRAM.wordOfNat_val_of_lt`: `(wordOfNat w v).val = v` whenever `v < 2 ^ w` (`Fits w v`).
* `Cslib.WordRAM.wordOfNat_unifFin`: `wordOfNat w k.val` transports `Fin (2 ^ w - 1 + 1)` samples
  from `ProbComp.unifFin (2 ^ w - 1)` to `Fin (2 ^ w)`.
-/

public section

namespace Cslib.WordRAM

/-- Truncate a natural number `v` into a `w`-bit word `Fin (2 ^ w)`, defaulting to `0` out of
range. -/
@[expose] def wordOfNat (w v : ℕ) : Fin (2 ^ w) :=
  if h : v < 2 ^ w then ⟨v, h⟩ else ⟨0, Nat.two_pow_pos w⟩

@[simp]
theorem wordOfNat_val_of_lt {w v : ℕ} (hv : v < 2 ^ w) :
    (wordOfNat w v).val = v := by
  simp [wordOfNat, hv]

@[simp]
theorem wordOfNat_unifFin (w : ℕ) (k : Fin (2 ^ w - 1 + 1)) :
    wordOfNat w k.val = finCongr (Nat.sub_add_cancel Nat.one_le_two_pow) k := by
  have hlt : k.val < 2 ^ w := by
    have hpos : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    have hk := k.isLt
    omega
  apply Fin.ext
  simp [wordOfNat, hlt]

end Cslib.WordRAM

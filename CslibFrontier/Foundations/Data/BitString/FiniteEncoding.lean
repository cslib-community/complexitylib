/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.Data.Fintype.EquivFin

/-!
# Fixed-width encodings of finite types

`fintypeEncoding F` enumerates `F` by `Fintype.equivFin`, then uses `indexBits` to represent
the resulting index in `Nat.clog 2 (Fintype.card F)` bits, least significant bit first. The
chosen enumeration is noncomputable; no efficient encoding or decoding algorithm is claimed.
The embedding is independent of any circuit or function to be computed.

## Main definitions

* `Cslib.BitString.fintypeEncoding`: an embedding of a finite type into logarithmic-width words.
-/

public section

namespace Cslib.BitString

/-- A finite type embedded in logarithmic-width binary words through a chosen enumeration.
The enumeration is `Fintype.equivFin`; the index uses the least-significant-bit-first layout
of `indexBits`. This definition supplies no computational complexity certificate. -/
noncomputable def fintypeEncoding (F : Type*) [Fintype F] :
    F ↪ BitString (Nat.clog 2 (Fintype.card F)) :=
  ⟨indexBits ∘ Fintype.equivFin F, indexBits_injective.comp (Fintype.equivFin F).injective⟩

end Cslib.BitString

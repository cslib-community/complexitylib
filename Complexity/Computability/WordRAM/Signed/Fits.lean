/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Signed.Fits
public import Complexity.Computability.WordRAM.Signed.Encoding

/-!
# Unsigned envelopes at the signed compiler's execution width

Native callers use the same nonnegative envelope for encoded signed payloads and unsigned
addresses, counts and loop temporaries. The existing compiler executes at signed width plus two.

## Main results

* `unsigned_fits_of_signed`: a representable natural signed envelope fits that physical width.

This representation bound is original and reuses the existing sign-and-magnitude encoding.
-/

@[expose] public section

namespace Cslib.WordRAM.Signed

/-- One signed envelope suffices for every unsigned intermediate at the execution width. -/
theorem unsigned_fits_of_signed {w B : ℕ} (hfit : GenericRAM.Signed.Fits w (B : ℤ)) :
    Fits (w + 2) B :=
  ((encode_fits hfit).mono (by omega)).of_le (by simp [encode]; omega)

end Cslib.WordRAM.Signed

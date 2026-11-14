/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Circuit.Boolean.CarrySave.Local

/-! Local compressor queries preserve the existing circuit's word order and padding. -/

namespace CslibFrontierTests.CarrySaveLocal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean CarrySaveLocal

/-- Either output word agrees with the existing compressor, for arbitrary input words. -/
example {w : ℕ} (a b c d : BitString w) (i : Fin w) (carry : Bool) :
    (formula carry).eval interpretation (inputs ![a,b,c,d] i carry) =
      (csa4to2 w).eval interpretation (Fin.append (Fin.append a b) (Fin.append c d))
        (if carry then Fin.natAdd w i else Fin.castAdd w i) :=
  eval_formula_compressor a b c d i carry

/-- The low carry bit is zero even when every input bit is one. -/
example : (formula true).eval interpretation
    (inputs (fun _ : Fin 4 => fun _ : Fin 3 => true) 0 true) = false := by decide

/-- Four one-valued words give a carry word with bit one set. -/
example : (formula true).eval interpretation
    (inputs (fun _ : Fin 4 => ![true, false, false]) 1 true) = true := by decide

/-- The first sum port is the fourth word; a high carry port shifts twice. -/
example : source false 0 = ⟨3, 0⟩ ∧ source true 6 = ⟨2, 2⟩ := by decide

end CslibFrontierTests.CarrySaveLocal

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Affine
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Encoding affine parity equations

An affine equation is encoded as the framed pair of its framed variable list and its right-hand
side bit, the layout of `encPair (encList encV) encBool` (`encAffineEquation_apply`).
`Cslib.Complexity.XORSAT.encoding` and the affine template compiler of
`Cslib.Complexity.CSP.computableInPolyTime_instantiateAffine` both use it with binary labels.

## Main definitions

* `Cslib.Complexity.encAffineEquation`: the encoding of an equation, with `fun_prop` rules for
  reading its fields and building it.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

variable {V : Type}

/-- Encoding of an affine equation: its framed variable list, then its right-hand side bit. -/
enc_structure encAffineEquation (encV : V ↪ List Bool) : AffineEquation V where
  vars : (encList encV), rhs : encBool

end Cslib.Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/ModelTheory/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.ModelTheory.Basic

/-!
# Extensionality for structures of relational languages

A structure for a relational language has no function symbols to interpret, so two structures on
the same type are equal when they interpret every relation symbol alike.

## Main results

* `FirstOrder.Language.Structure.ext_of_isRelational`: structures for a relational language are
  determined by their relations.
-/

public section

namespace FirstOrder.Language.Structure

variable {L : Language} [L.IsRelational] {M : Type*}

/-- Two structures for a relational language on the same type are equal when they interpret every
relation symbol alike. -/
theorem ext_of_isRelational {S T : L.Structure M}
    (h : ∀ {l} (R : L.Relations l) (x : Fin l → M), @RelMap L M S l R x ↔ @RelMap L M T l R x) :
    S = T :=
  Structure.ext (funext fun _ => funext fun f => isEmptyElim f)
    (funext fun _ => funext fun R => funext fun x => propext (h R x))

end FirstOrder.Language.Structure

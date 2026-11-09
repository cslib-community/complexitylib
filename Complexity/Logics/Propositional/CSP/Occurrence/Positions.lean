/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Occurrence

/-!
# Extensionality in actual occurrence positions

The two original constraint and argument indices identify an occurrence; its variable is
read from the original scope. No variable-label equality or injectivity premise is needed.
-/

public section

namespace Cslib.Logic.PL.CSP.Occurrence

/-- Constraint and argument position values determine an actual dependent occurrence. -/
theorem eq_of_positions {Rel V : Type} {F : CSP Rel V} {o p : F.Occurrence}
    (hc : o.1.val = p.1.val) (ha : o.2.val = p.2.val) : o = p := by
  rcases o with ⟨i, j⟩
  rcases p with ⟨k, l⟩
  have hi : i = k := Fin.ext hc
  subst k
  exact congrArg (Sigma.mk i) (Fin.ext ha)

end Cslib.Logic.PL.CSP.Occurrence

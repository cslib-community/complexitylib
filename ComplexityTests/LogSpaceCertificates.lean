/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (imported logspace certificate fixtures)

public import Complexity.Tactic.LogSpace

/-! # Opaque named logspace certificates

These certificates are imported by `LogSpaceTactic`. Their eager computation premises exercise
family-directed search, and their implementations remain opaque to compositional search.
-/

public section

namespace ComplexityTests.LogSpaceCertificates

open Turing.MultiTapeTM

/-- An opaque named routine with an explicitly certified callback. -/
@[irreducible] def runNamed (f : List Bool → List Bool) (w : List Bool) : List Bool := f w

/-- The routine's behavior is available explicitly without a simplifier unfolding rule. -/
theorem runNamed_apply (f : List Bool → List Bool) (w : List Bool) : runNamed f w = f w := by
  unfold runNamed
  rfl

/-- An unavailable alternative must not prevent a later certificate from succeeding. -/
@[program_certificate impossible]
theorem runNamed_unavailable (f : List Bool → List Bool) (impossible : False) :
    ComputableInLogSpace (runNamed f) encBits encBits := impossible.elim

/-- The eager callback needs the logspace rule set, rather than polynomial-time search. -/
@[program_certificate hf]
theorem runNamed_logspace (f : List Bool → List Bool)
    (hf : ComputableInLogSpace f encBits encBits) :
    ComputableInLogSpace (runNamed f) encBits encBits := by
  unfold runNamed
  exact hf

/-- An unregistered routine used to check local attribute lifetime. -/
@[irreducible] def localNamed (f : List Bool → List Bool) (w : List Bool) : List Bool := f w

/-- This theorem is registered only inside a client's section. -/
theorem localNamed_logspace (f : List Bool → List Bool)
    (hf : ComputableInLogSpace f encBits encBits) :
    ComputableInLogSpace (localNamed f) encBits encBits := by
  unfold localNamed
  exact hf

namespace Scoped

/-- An opaque routine whose certificate requires opening its namespace's scope. -/
@[irreducible] def scopedNamed (f : List Bool → List Bool) (w : List Bool) : List Bool := f w

/-- Scoped certificates use the same scope for named lookup and compositional search. -/
@[scoped program_certificate hf]
theorem scopedNamed_logspace (f : List Bool → List Bool)
    (hf : ComputableInLogSpace f encBits encBits) :
    ComputableInLogSpace (scopedNamed f) encBits encBits := by
  unfold scopedNamed
  exact hf

end Scoped
end ComplexityTests.LogSpaceCertificates

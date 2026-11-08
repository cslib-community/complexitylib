/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Reduction.ManyOne

/-! The admissible-map API works without importing machines or complexity classes. -/

namespace ComplexityTests.ManyOneKernel

open Cslib.Complexity

private theorem flip : ManyOneReducibleBy (fun _ => True)
    {b : Bool | b = false} {b : Bool | b = true} :=
  ⟨Bool.not, trivial, fun b => by cases b <;> simp⟩

-- Complementing and then composing the flip gives a reduction of a proper, inhabited set to
-- itself. This uses only the lower import, retaining the existing public names.
example : ManyOneReducibleBy (fun _ => True) {b : Bool | b = false} {b : Bool | b = false} := by
  have back : ManyOneReducibleBy (fun _ => True)
      {b : Bool | b = true} {b : Bool | b = false} := by
    have hfalse : ({b : Bool | b = false}ᶜ : Set Bool) = {b : Bool | b = true} := by
      ext b; cases b <;> simp
    have htrue : ({b : Bool | b = true}ᶜ : Set Bool) = {b : Bool | b = false} := by
      ext b; cases b <;> simp
    simpa only [hfalse, htrue] using flip.compl
  exact flip.trans (fun _ _ _ _ => trivial) back

end ComplexityTests.ManyOneKernel

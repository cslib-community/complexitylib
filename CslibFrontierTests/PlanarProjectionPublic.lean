/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Projection

/-! The existing projection injection is available through an ordinary direct import. -/

open Cslib.Logic.PL.CSP Cslib.Complexity.CSP.OrderedBoundary

example (n a : ℕ) (j : Fin (n + 1)) :
    Function.Injective (PPGadget.substitutePort a (PPGadget.hidePort j)) :=
  projectPort_injective n a j

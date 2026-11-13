/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import CslibFrontier.Logics.Propositional.CSP.Occurrence.Enumeration
import CslibFrontier.Computability.PolyTime.CSP.Occurrence
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! # Shared typed and native occurrence scans -/

set_option linter.privateModule false

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity Cslib.Complexity.CSP
  Turing.MultiTapeTM

-- Identical constraints and repeated arguments keep distinct records; nullaries add none.
example : (incidenceList ([⟨true, [7, 7]⟩, ⟨true, []⟩, ⟨true, [7, 7]⟩] : CSP Bool ℕ)).map
    Occurrence.record = [(0, 0, 7), (0, 1, 7), (2, 0, 7), (2, 1, 7)] := by decide

example : (incidenceList ([] : CSP Bool ℕ)).isEmpty = true := by decide

-- Native certificate composition needs no graph or augmenting-walk import.
example : ComputableInPolyTime (fun F : CSP Bool ℕ => F.occurrences.length)
    (encCSP encBool encNat) encUnary := by fun_prop

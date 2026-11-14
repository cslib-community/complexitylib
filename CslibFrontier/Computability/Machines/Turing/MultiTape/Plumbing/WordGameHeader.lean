/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# The control word of a native word game

A blank control word transfers control to the terminal machine. A nonterminal word contains
the player followed by the cell in which that player writes a move. Both the controller and
the native metadata updater use this same layout.
-/

public section

namespace Turing

/-- A terminal position has no header; a live position stores its player and an empty move. -/
@[expose] def wordGameHeader : Option Bool → List Bool
  | none => []
  | some player => [player, false]

end Turing

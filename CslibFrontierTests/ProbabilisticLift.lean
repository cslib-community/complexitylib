/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Game
import CslibFrontier.Languages.Probabilistic.Lift
import CslibFrontier.Languages.Probabilistic.Notation

/-! Checked examples for `Cslib.ProbComp.instMonadLiftPMF`: a distribution written with `do`
binds programs directly, and the lift is the law. -/

namespace CslibFrontierTests.ProbabilisticLift

open Cslib Cslib.Crypto Probability

/-- A chooser/guesser game in the shape of a PMF security game: the adversary's programs are bound
directly, next to a distribution `conv`. -/
noncomputable def game {X S C : Type} (choose : ProbComp (X × S)) (conv : X → PMF C)
    (guess : S → C → ProbComp Bool) (valid : X → Bool) : PMF Bool := do
  let (x, s) ← choose
  if valid x then do
    let c ← conv x
    guess s c
  else pure false

/-- The same game written with explicit laws, as PMF games are written without the lift. -/
noncomputable def explicitGame {X S C : Type} (choose : ProbComp (X × S)) (conv : X → PMF C)
    (guess : S → C → ProbComp Bool) (valid : X → Bool) : PMF Bool :=
  (ProbComp.eval choose).bind fun (x, s) =>
    if valid x then (conv x).bind fun c => ProbComp.eval (guess s c) else pure false

-- The lifted game is the explicit one by definition, so lifting changes no meaning.
example {X S C : Type} (choose : ProbComp (X × S)) (conv : X → PMF C)
    (guess : S → C → ProbComp Bool) (valid : X → Bool) :
    game choose conv guess valid = explicitGame choose conv guess valid :=
  rfl

-- `pmf_norm` reads every lift back as the law, after which `ProbComp.eval` lemmas apply.
example {X S C : Type} (choose : ProbComp (X × S)) (conv : X → PMF C)
    (guess : S → C → ProbComp Bool) (valid : X → Bool) :
    game choose conv guess valid = (ProbComp.eval choose).bind fun (x, s) =>
      if valid x then (conv x).bind fun c => ProbComp.eval (guess s c) else pure false := by
  simp only [game, pmf_norm]

-- `rw` matches the `liftM` form that Lean inserts.
example (program : ProbComp Bool) : (liftM program : PMF Bool) = ProbComp.eval program := by
  rw [ProbComp.liftM_eq_eval]

-- The lift preserves `pure` and `bind` (`LawfulMonadLift`), so core's `liftM` lemmas apply.
example (program : ProbComp Bool) (f : Bool → ProbComp Bool) :
    (liftM (program >>= f) : PMF Bool) = liftM program >>= fun b => liftM (f b) :=
  liftM_bind program f

-- A program where a distribution is expected is lifted silently: `Game.advantage` takes
-- distributions, and here receives a program. `simp` reads the lift back.
example (program : ProbComp Bool) : Game.advantage program (ProbComp.eval program) = 0 := by
  simp only [ProbComp.monadLift_eq_eval, Game.advantage_self]

-- `Pr[·]` still reads a program as a program, not as a lifted distribution.
set_option linter.hashCommand false in
#guard_expr Pr[ProbComp.uniform Bool] =ₛ
  ENNReal.toReal (ProbComp.eval (ProbComp.uniform Bool) true)

end CslibFrontierTests.ProbabilisticLift

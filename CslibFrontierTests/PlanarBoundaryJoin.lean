/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryAppend
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryIdentify

/-! Actual boundary appends and adjacent joins retain unused ports and a degree-six cutvertex. -/

namespace CslibFrontierTests.PlanarBoundaryJoin

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity Cslib.Complexity.CSP
  Cslib.Complexity.CSP.OrderedBoundary

private abbrev F : CSP Unit ℕ :=
  [⟨(), [0]⟩, ⟨(), [0]⟩, ⟨(), [0]⟩, ⟨(), [0]⟩, ⟨(), [0]⟩, ⟨(), [0]⟩, ⟨(), []⟩]

private def w : Witness F (List.ofFn ![0, 1]) :=
  Witness.ofProbe (by decide) ⟨[2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 14, 11, 12, 15, 0, 13]⟩ (by decide)

private def v : Witness ([] : CSP Unit ℕ) (List.ofFn ![2]) :=
  Witness.ofProbe (by decide) ⟨[0, 1]⟩ (by decide)

private noncomputable def joined : Witness F (List.ofFn ![0, 1] ++ List.ofFn ![2]) :=
  w.appendOfFn v (by simp [F, CSP.vars, List.ofFn_succ]) (by decide)

example : verify F [0, 1, 2] joined.certificate = true := joined.accepted

example : F.length = 7 ∧ F.vars.count 0 = 6 := by decide

example : 1 ∉ F.vars ∧ 2 ∉ F.vars := by decide

private noncomputable def folded : Witness (F.relabel (Function.update id 1 0))
    (List.ofFn (fun i : Fin 2 => Function.update id 1 0 (![0, 1, 2] i.succ))) :=
  (show Witness F (List.ofFn ![0, 1, 2]) from joined).identifyFirstTwoOfFn
    (Function.update id 1 0) (by decide) (by intros; rfl) (by decide)

example : verify (F.relabel (Function.update id 1 0)) [0, 2] folded.certificate = true :=
  folded.accepted

example : F.relabel (Function.update id 1 0) = F := rfl

private noncomputable def closed : Witness (F.relabel (Function.update id 1 0)) [] :=
  (show Witness _ [0, 2] from folded).forgetHead (by decide) |>.forgetHead (by decide)

example : verify (F.relabel (Function.update id 1 0)) [] closed.certificate = true :=
  closed.accepted

end CslibFrontierTests.PlanarBoundaryJoin

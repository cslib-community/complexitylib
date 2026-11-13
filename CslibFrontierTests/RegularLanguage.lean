/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Languages.RegularLanguage

/-!
# Tests: regular languages given by conditions on words

* The connectives on conditions `{w | P w}` use the existing CSLib closures directly:
  `IsRegular.inf` for `∧`, `IsRegular.add` for `∨`, `IsRegular.compl` for `¬`, and
  `IsRegular.top`/`IsRegular.zero` for `True`/`False`.
* The positional languages are stated over positions `w[i]` (`setOf_forall_getElem`,
  `setOf_exists_getElem`), and a finite conjunction uses `setOf_forall`.
* All of these combine to give the regularity of a concrete language over `Bool`.
-/

namespace CslibFrontierTests.RegularLanguage

open Cslib.Language

variable {α : Type*} {P Q : List α → Prop}

example (hP : Language.IsRegular {w | P w}) (hQ : Language.IsRegular {w | Q w}) :
    Language.IsRegular {w | P w ∧ Q w} := hP.inf hQ

example (hP : Language.IsRegular {w | P w}) (hQ : Language.IsRegular {w | Q w}) :
    Language.IsRegular {w | P w ∨ Q w} := hP.add hQ

example (hP : Language.IsRegular {w | P w}) : Language.IsRegular {w | ¬ P w} := hP.compl

example : Language.IsRegular {_w : List α | True} := IsRegular.top

example : Language.IsRegular {_w : List α | False} := IsRegular.zero

/-- Words over `Bool` that are all `true`, or have a `false` strictly before a `true`. -/
example : Language.IsRegular {w : List Bool |
    (∀ i : Fin w.length, w[i] = true) ∨
      ∃ i j : Fin w.length, i < j ∧ w[i] = false ∧ w[j] = true} :=
  (IsRegular.setOf_forall_getElem (· = true)).add
    (IsRegular.setOf_exists_lt (· = false) (· = true))

/-- Words over `Fin 3` in which each of the three letters occurs. -/
example : Language.IsRegular {w : List (Fin 3) | ∀ a : Fin 3, ∃ i : Fin w.length, w[i] = a} :=
  IsRegular.setOf_forall fun a => IsRegular.setOf_exists_getElem (· = a)

end CslibFrontierTests.RegularLanguage

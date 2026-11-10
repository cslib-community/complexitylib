/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Basic
public import CslibFrontier.Foundations.Control.Monad.Memoize
import CslibFrontier.Languages.Probabilistic.Semantics

/-!
# Evaluating memoized probabilistic programs

Evaluating a memoized program preserves the joint answer and cache distribution. This is the
probabilistic specialization of the generic monad-morphism rule for `memoize`.

## Main results

* `Cslib.ProbComp.eval_memoize`: evaluation commutes with a cached call.

## References

Specializes `IsMonadHom.map_memoize`, adapted from Foundations/Control/Monad/Memoize.lean on
the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.ProbComp

/-- Evaluate the underlying sampler, retaining the same answer and entire list cache. -/
@[simp] theorem eval_memoize {Key Value : Type} [BEq Key]
    (compute : Key → ProbComp Value) (key : Key) (cache : List (Key × Value)) :
    eval (memoize compute key cache) = memoize (fun q => eval (compute q)) key cache :=
  isMonadHom_eval.map_memoize compute key cache

end Cslib.ProbComp

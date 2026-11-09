/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Basic
public import Complexity.Languages.Probabilistic.Norm.Init

/-!
# Normalizing laws of probabilistic programs

Tags the lemmas of the simp set `pmf_norm`. `simp only [pmf_norm]` turns the law
`ProbComp.eval` of a program written with `do` notation into a normal form of `PMF.bind`, `PMF.pure`
and `PMF.map`, the shape that the support and probability lemmas of `PMF` expect:

* the law of a program: `ProbComp.eval_bind`, `ProbComp.eval_pure`, `ProbComp.eval_map`;
* monad notation on `PMF`: `Cslib.Probability.PMF.monad_bind_eq_bind`,
  `Cslib.Probability.PMF.monad_pure_eq_pure`, `PMF.monad_map_eq_map`;
* the monad laws, oriented to reassociate binds to the right and substitute returned values:
  `PMF.bind_bind`, `PMF.pure_bind`, `PMF.bind_pure`;
* maps pushed into continuations and composed: `PMF.map_bind`, `PMF.bind_map`, `PMF.pure_map`,
  `PMF.map_comp`, with `Function.comp_def` unfolding the compositions these produce.

It is a curated set for non-terminal `simp only` calls: later steps can rely on the normal form,
which changes only when this list does.
-/

public section

attribute [pmf_norm] Cslib.ProbComp.eval_bind Cslib.ProbComp.eval_pure Cslib.ProbComp.eval_map
  Cslib.Probability.PMF.monad_bind_eq_bind Cslib.Probability.PMF.monad_pure_eq_pure
  PMF.monad_map_eq_map PMF.bind_bind PMF.pure_bind PMF.bind_pure PMF.map_bind PMF.bind_map
  PMF.pure_map PMF.map_comp Function.comp_def

end

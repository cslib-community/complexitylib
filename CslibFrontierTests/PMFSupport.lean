/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Probability.PMF.Support

/-! # Deterministic pushforwards and two-stage experiments

A pushforward that is constant on the support is a point mass, and a point-mass pushforward
determines the map on the support. Two distributions with different point-mass pushforwards are
different, and a two-stage experiment whose possible continuations all return the same point mass
is that point mass.
-/

namespace CslibFrontierTests.PMFSupport

open Cslib.Probability

-- Forgetting a fair coin is the point mass at the constant answer.
example : (PMF.uniformOfFintype Bool).map (fun b => b || true) = PMF.pure true :=
  PMF.map_eq_pure_iff.2 fun b _ => Bool.or_true b

-- A point-mass pushforward pins the map on every possible outcome.
example (p : PMF ℕ) (h : p.map (· % 2) = PMF.pure 0) (n : ℕ) (hn : n ∈ p.support) :
    n % 2 = 0 :=
  PMF.map_eq_pure_iff.1 h n hn

-- Distributions whose parities are different point masses are different.
example (p q : PMF ℕ) (hp : p.map (· % 2) = PMF.pure 0) (hq : q.map (· % 2) = PMF.pure 1) :
    p ≠ q :=
  PMF.ne_of_map_eq_pure hp hq zero_ne_one

-- A coin flip followed by a continuation that ignores it on the support is deterministic.
example (p : PMF Bool) : p.bind (fun b => PMF.pure (b && false)) = PMF.pure false :=
  PMF.bind_eq_pure_of_forall_mem_support fun b _ => by rw [Bool.and_false]

end CslibFrontierTests.PMFSupport

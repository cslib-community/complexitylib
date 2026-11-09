/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Languages.Probabilistic.Norm

/-! # The simp set `pmf_norm` -/

namespace ComplexityTests.PMFNorm

open Cslib

-- The law of a `do` block becomes right-nested binds, with the returned value substituted.
example (p : ProbComp Bool) (f : Bool → ProbComp ℕ) (g : ℕ → ℕ) :
    ProbComp.eval (do
      let b ← p
      let n ← f b
      return g n) =
      (ProbComp.eval p).bind fun b => (ProbComp.eval (f b)).bind fun n => PMF.pure (g n) := by
  simp only [pmf_norm]

-- Postprocessing is pushed into the continuation, and composed maps become one map.
example (p : ProbComp Bool) (q : Bool → PMF ℕ) (g h : ℕ → ℕ) :
    (((ProbComp.eval p).bind q).map g).map h =
      (ProbComp.eval p).bind fun b => (q b).map fun n => h (g n) := by
  simp only [pmf_norm]

-- A map before a bind is absorbed into the continuation.
example (p : ProbComp Bool) (f : Bool → ℕ) (q : ℕ → PMF Bool) :
    (ProbComp.eval (f <$> p)).bind q = (ProbComp.eval p).bind fun b => q (f b) := by
  simp only [pmf_norm]

-- Monad notation on `PMF` itself is normalized too, and returning a value already bound is dropped.
example (μ : PMF ℕ) (ν : ℕ → PMF ℕ) :
    (do
      let a ← μ
      let b ← ν a
      pure b : PMF ℕ) = μ.bind ν := by
  simp only [pmf_norm]

-- The set leaves unrelated structure alone: a sum over the support is not unfolded.
example (μ : PMF Bool) (q : Bool → PMF Bool) :
    (do
      let a ← μ
      q a : PMF Bool) true = ∑' a, μ a * q a true := by
  simp only [pmf_norm]
  rw [PMF.bind_apply]

end ComplexityTests.PMFNorm

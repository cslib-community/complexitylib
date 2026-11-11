/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.WeightedCut.RealCut
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.LinearProgramming
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Field.Defs

/-!
# Real-capacity Maximum Flow

This module defines maximum flows with real capacities.
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

open Cslib.WeightedCut

variable {V : Type*} [Fintype V] [DecidableEq V] {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def IsFeasibleRealFlow (W : V → V → K) (s t : V) (f : V × V → K) : Prop :=
  (∀ u v, 0 ≤ f (u, v)) ∧
  (∀ u v, f (u, v) ≤ W u v) ∧
  (∀ v, v ≠ s → v ≠ t → ∑ u, f (u, v) = ∑ w, f (v, w))

def realNetOut (f : V × V → K) (s : V) : K :=
  (∑ w, f (s, w)) - (∑ u, f (u, s))

def IsMaxRealFlow (W : V → V → K) (s t : V) (val : K) : Prop :=
  IsGreatest ((fun f => realNetOut f s) '' {f | IsFeasibleRealFlow W s t f}) val

end Cslib.Algorithms.Lean.MaxFlow

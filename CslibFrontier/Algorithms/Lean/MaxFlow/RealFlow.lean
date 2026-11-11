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

variable {V : Type*} [Fintype V] [DecidableEq V] {K : Type*} [Field K]
  [LinearOrder K] [IsStrictOrderedRing K]

def IsFeasibleRealFlow (W : V → V → K) (s t : V) (f : V × V → K) : Prop :=
  (∀ u v, 0 ≤ f (u, v)) ∧
  (∀ u v, f (u, v) ≤ W u v) ∧
  (∀ v, v ≠ s → v ≠ t → ∑ u, f (u, v) = ∑ w, f (v, w))

def realNetOut (f : V × V → K) (s : V) : K :=
  (∑ w, f (s, w)) - (∑ u, f (u, s))

def IsMaxRealFlow (W : V → V → K) (s t : V) (val : K) : Prop :=
  IsGreatest ((fun f => realNetOut f s) '' {f | IsFeasibleRealFlow W s t f}) val


/-- The equality constraints for flow conservation and capacity bounds, encoded as `A * x ≤ b`.
    To be formulated by `@verifier-math` as per handoff in #3422. -/
def flowLP_A (_W : V → V → K) (s t : V) : Matrix (Sum (V × V) (Sum V V)) (V × V) K :=
  fun i j => match i with
  | Sum.inl e => if e = j then 1 else 0
  | Sum.inr (Sum.inl v) => if v = s ∨ v = t then 0
                           else if j.2 = v then 1 else if j.1 = v then -1 else 0
  | Sum.inr (Sum.inr v) => if v = s ∨ v = t then 0
                           else if j.1 = v then 1 else if j.2 = v then -1 else 0

def flowLP_b (W : V → V → K) (_s _t : V) : (Sum (V × V) (Sum V V)) → K :=
  fun i => match i with
  | Sum.inl e => W e.1 e.2
  | Sum.inr _ => 0

def flowLP_c (s _t : V) : (V × V) → K :=
  fun e => if e.1 = s then 1 else if e.2 = s then -1 else 0

end Cslib.Algorithms.Lean.MaxFlow

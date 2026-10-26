/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedCompile
import Complexity.Computability.Complexity.Problems.Graph.OrthogonalDrawing
import Complexity.Computability.Complexity.Problems.SAT.Incidence.Degree
import Complexity.Logics.Propositional.CNF.ImplicationChain

namespace ComplexityTests.PlanarCompile

open Cslib.Logic.PL Cslib.Orthogonal Cslib.Complexity
open SAT.ParsimoniousPlanar

-- The compiler preserves the two degenerate SAT instances, including the empty clause.
example : formula [] = [] := by decide +kernel
example : formula [[]] = [[]] := by decide +kernel

-- A unit clause produces a nonempty wire, without inserting any crossing gadgets.
example : crossingSites [[(7, true)]] = [] := by decide +kernel
example : (rawFormula [[(7, true)]]).length = 319 := by decide +kernel
example : (rawFormula [[(7, true)]]).vars.length = 637 := by decide +kernel
example : (rawFormula [[(7, true)]]).eval (fun _ => true) = true := by decide +kernel

-- Crossing ports retain the side order and keep both lanes separate.
example : signal [(0, 0)] (0, 0) (-1, 0) 0 =
    ((0, 0), Sum.inr (CNF.PairedCrossover.terminal 0 0)) := by decide
example : access [] (0, 0) (1, 0) 0 = [(240, 110), (220, 110)] := by decide

-- Separate forward and backward lanes close the slack between adjacent cells.
example : (link [] (0, 0) (1, 0) 0).1 =
    [(((0, 0), Sum.inl (1, 0)), false), (((1, 0), Sum.inl (0, 0)), true)] := by decide
example : (link [] (0, 0) (1, 0) 1).1 =
    [(((1, 0), Sum.inl (0, 1)), false), (((0, 0), Sum.inl (1, 1)), true)] := by decide

-- Repeated literal incidences contribute separately to the actual graph degree.
example : (SAT.incidenceGraph [[(5, true), (5, false)]]).incidenceVertices.count 0 = 2 :=
  by decide
example : (SAT.incidenceGraph [[(5, true), (5, false)]]).incidenceVertices.count 1 = 2 :=
  by decide

example : (CNF.implicationChain ([0, 1, 2] : List ℕ)).eval (fun _ => true) = true := by decide
example : (CNF.implicationChain ([0, 1, 2] : List ℕ)).eval (fun i => i == 0) = false := by decide

-- A nonempty instance of the actual continuous drawing predicate.
example : Graph.IsPlanarOrthogonalDrawing ([0, 1], [(0, 1)])
    ([(0, 0), (1, 0)], [[(0, 0), (1, 0)]]) := by
  refine ⟨rfl, rfl, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain rfl := List.mem_singleton.mp he
    decide
  · intro e he
    obtain rfl := List.mem_singleton.mp he
    decide
  · intro i hi
    have : i = 0 := by simpa using hi
    subst i
    exact Or.inl ⟨rfl, rfl⟩
  · intro i hi
    have : i = 0 := by simpa using hi
    subst i
    simp [IsOrthogonal, List.consecutivePairs, AxisAligned]
  · intro i hi
    have : i = 0 := by simpa using hi
    subst i
    simp [IsSimple, List.consecutivePairs]
  · intro i hi v hv _
    have : i = 0 := by simpa using hi
    subst i
    simpa using hv
  · intro i hi j hj hij
    have : i = 0 := by simpa using hi
    have : j = 0 := by simpa using hj
    exact (hij (by omega)).elim

end ComplexityTests.PlanarCompile

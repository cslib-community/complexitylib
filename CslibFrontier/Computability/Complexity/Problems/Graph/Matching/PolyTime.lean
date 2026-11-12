/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.Matching.Algorithm
import CslibFrontier.Computability.Complexity.Problems.Graph.PerfectMatchingPolyTime
import CslibFrontier.Computability.PolyTime.CSP.Vars
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Mathlib.Data.List.GetD

/-!
# Native bit complexity of unweighted matching

The certificates use the complete framed `encGraph` input and `encMatching` output. Retained
vertex/name bits, explicit one-hot table rows, scope positions, every intermediate solver
state and the output edge list enter ordinary native multitape polynomial composition.
No graph validity, degree bound, finite relation language or runtime provider is an input.

For framed input length `L`, there are at most `L` distinct vertices and normalized edges.
Writing these counts as `n` and `m`, each choice table has at most `m + 1` rows of width
`m + 1`, and each pin has one unary row. Thus choice-row storage is bounded by
`n * (m + 1) ^ 2` Boolean entries, before the explicitly charged framing and binary scope
names. Tagging a retained vertex name by `2 * v + 1` adds at most one binary digit;
original edge names are tagged list positions. Solver storage growth is charged by the
all-raw explicit-table optimizer certificate used in the composition.
-/

public section

namespace Cslib.Complexity.Graph

open Cslib.Logic.PL Turing.MultiTapeTM

attribute [local fun_prop] computableInPolyTime_edgeList
attribute [local fun_prop] CSP.EdgeAugmenting.poly_records CSP.EdgeAugmenting.poly_readWith
attribute [local fun_prop] CSP.computableInPolyTime_tableExactlyOne

/-- The nonempty choice scope is built in polynomial time, retaining binary names. -/
theorem computableInPolyTime_matchingScope :
    ComputableInPolyTime (fun p : Graph × ℕ => p.1.matchingScope p.2)
      (encPair encGraph encNat) (encList encNat) := by
  unfold matchingScope incident
  fun_prop

attribute [local fun_prop] computableInPolyTime_matchingScope

/-- The complete generated explicit-table instance is native polynomial-time on every graph. -/
theorem computableInPolyTime_matchingInstance :
    ComputableInPolyTime matchingInstance encGraph (encCSP CSP.encTable encNat) := by
  unfold matchingInstance
  fun_prop

attribute [local fun_prop] computableInPolyTime_matchingInstance

/-- Reading mutual selection scans only actual occurrence records and their bit buffer. -/
theorem computableInPolyTime_selectedBit :
    ComputableInPolyTime (fun p : (CSP CSP.Table ℕ × List Bool) × ℕ =>
      selectedBit p.1.1 p.1.2 p.2)
      (encPair CSP.EdgeAugmenting.encBuffer encNat) encBool := by
  unfold selectedBit
  fun_prop

attribute [local fun_prop] computableInPolyTime_selectedBit

/-- The selected original position list is native polynomial-time. -/
theorem computableInPolyTime_matchingPositions :
    ComputableInPolyTime (fun p : Graph × List Bool => p.1.matchingPositions p.2)
      encMatchingBuffer (encList encNat) := by
  unfold matchingPositions encMatchingBuffer
  have hr : ComputableInPolyTime (fun p : Graph × List Bool => List.range p.1.edgeList.length)
      (encPair encGraph (encList encBool)) (encList encUnary) := by fun_prop
  have hc : ComputableInPolyTime (fun l : List ℕ => l.map fun i => i)
      (encList encUnary) (encList encNat) := by fun_prop
  have hb : ComputableInPolyTime (fun p : Graph × List Bool => List.range p.1.edgeList.length)
      encMatchingBuffer (encList encNat) := by
    simpa only [Function.comp_def, List.map_id'] using hc.comp hr
  apply ComputableInPolyTime.filterWithInput hb
  have hbody : ComputableInPolyTime
      (fun p : (Graph × List Bool) × ℕ => ((p.1.1.matchingInstance, p.1.2), 2 * p.2))
      (encPair encMatchingBuffer encNat) (encPair CSP.EdgeAugmenting.encBuffer encNat) := by
    fun_prop
  exact computableInPolyTime_selectedBit.comp hbody

attribute [local fun_prop] computableInPolyTime_matchingPositions

/-- Converting positions to actual original endpoint pairs is native polynomial-time. -/
theorem computableInPolyTime_edgesAtPositions :
    ComputableInPolyTime (fun p : Graph × List ℕ => p.1.edgesAtPositions p.2)
      (encPair encGraph (encList encNat)) encMatching := by
  unfold edgesAtPositions encMatching
  apply ComputableInPolyTime.mapWithInput (ComputableInPolyTime.snd _ _)
  apply ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.listGetD_binary (encL := encMatching) (0, 0)
  · exact (computableInPolyTime_edgeList.comp (by fun_prop)).tidy
  · fun_prop

/-- The graph-only maximum matching endpoint has an ordinary native polynomial certificate. -/
theorem computableInPolyTime_maximumMatching :
    ComputableInPolyTime maximumMatching encGraph encMatching := by
  have ho := CSP.EdgeSolver.computableInPolyTime_optimize.comp
    computableInPolyTime_matchingInstance
  have hb : ComputableInPolyTime
      (fun G : Graph => (CSP.EdgeSolver.optimize G.matchingInstance).getD [])
      encGraph (encList encBool) :=
    .of_tidy (ho.tidy.optionGetDWithInput (ComputableTidilyInPolyTime.const []))
  exact computableInPolyTime_edgesAtPositions.comp
    (ComputableInPolyTime.id'.prod
      (computableInPolyTime_matchingPositions.comp (ComputableInPolyTime.id'.prod hb)))

/-- Checking full vertex coverage scans the actual lists of vertices and selected edges. -/
theorem computableInPolyTime_coversVertices :
    ComputableInPolyTime (fun p : Graph × List (ℕ × ℕ) => p.1.coversVertices p.2)
      (encPair encGraph encMatching) encBool := by
  unfold coversVertices incident encMatching
  fun_prop

/-- Constructive perfect-matching search is native polynomial-time on complete raw graphs. -/
theorem computableInPolyTime_perfectMatching :
    ComputableInPolyTime perfectMatching encGraph (encOption encMatching) := by
  have hm := computableInPolyTime_maximumMatching
  have hc := computableInPolyTime_coversVertices.comp (ComputableInPolyTime.id'.prod hm)
  unfold perfectMatching
  dsimp only
  exact .of_tidy (hc.tidy.cond
    ((ComputableTidilyInPolyTime.optionSome encMatching).comp hm.tidy)
    (ComputableTidilyInPolyTime.const none))

/-- Full perfect-matching decision is native polynomial-time on complete raw graphs. -/
theorem computableInPolyTime_decidePerfectMatching :
    ComputableInPolyTime decidePerfectMatching encGraph encBool := by
  unfold decidePerfectMatching
  exact computableInPolyTime_perfectMatching.optionIsSome

end Cslib.Complexity.Graph

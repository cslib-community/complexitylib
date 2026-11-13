/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Permanent.ThreeSAT.Construction
public import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# The 3CNF matrix is computable in polynomial time

The entries of the matrix of a formula (`matrixEntry`) are computed in polynomial time from the
formula, under `encCNF`, and the two vertex indices, in unary; the entry is an integer in binary
sign-magnitude form. Vertex indices are at most the number of vertices, which is linear in the
encoded formula, so unary indices cost no more than the formula. Every step is an explicit list
or arithmetic operation of the multi-tape machine library: list lookups for the padded literals,
`List.find?` over the occurrence indices for first and next occurrences, `List.idxOf` for the
auxiliary vertex of a variable, and unary arithmetic for the vertex numbering.

## Main results

* `Cslib.Complexity.PermanentThreeSAT.computableInPolyTime_matrixEntry`.

## Main definitions

* `Cslib.Complexity.PermanentThreeSAT.encCNFVertexPair`: a formula with two unary vertex
  indices.
-/

@[expose] public section

namespace Cslib.Complexity.PermanentThreeSAT

open Cslib.Logic.PL Turing.MultiTapeTM PermanentGadget

/-- A formula with two vertex indices: the formula under `encCNF`, then the two indices in unary;
the formula and the first index are framed. -/
abbrev encCNFVertexPair : CNF ℕ × ℕ × ℕ ↪ List Bool :=
  encPair encCNF (encPair encUnary encUnary)

/-- `auxSucc` through option combinators. -/
theorem auxSucc_eq_getD (φ : CNF ℕ) (i : ℕ) (b : Bool) :
    auxSucc φ i b = ((firstOcc φ ((varList φ).getD i 0, b)).map (entryIdx φ)).getD i := by
  unfold auxSucc
  cases firstOcc φ ((varList φ).getD i 0, b) <;> rfl

/-- `exitSucc` through option combinators. -/
theorem exitSucc_eq_getD (φ : CNF ℕ) (o : ℕ) :
    exitSucc φ o = ((nextOcc φ o).map (entryIdx φ)).getD ((varList φ).idxOf (litAt φ o).1) := by
  unfold exitSucc
  cases nextOcc φ o <;> rfl

@[fun_prop]
theorem computableInPolyTime_varList :
    ComputableInPolyTime varList encCNF (encList encNat) := by
  unfold varList
  fun_prop

@[fun_prop]
theorem computableInPolyTime_numAux : ComputableInPolyTime numAux encCNF encUnary := by
  unfold numAux
  fun_prop

theorem computableInPolyTime_litAt :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => litAt p.1 p.2) (encPair encCNF encUnary)
      (encPair encNat encBool) := by
  unfold litAt encCNF
  fun_prop

@[fun_prop]
theorem computableInPolyTime_numOcc : ComputableInPolyTime numOcc encCNF encUnary := by
  unfold numOcc encCNF
  fun_prop

theorem computableInPolyTime_firstOcc :
    ComputableInPolyTime (fun p : CNF ℕ × Literal ℕ => firstOcc p.1 p.2)
      (encPair encCNF (encPair encNat encBool)) (encOption encUnary) := by
  have := computableInPolyTime_litAt
  have := computableInPolyTime_numOcc
  unfold firstOcc
  fun_prop

theorem computableInPolyTime_nextOcc :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => nextOcc p.1 p.2)
      (encPair encCNF encUnary) (encOption encUnary) := by
  have := computableInPolyTime_litAt
  have := computableInPolyTime_numOcc
  unfold nextOcc
  fun_prop

theorem computableInPolyTime_entryIdx :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => entryIdx p.1 p.2)
      (encPair encCNF encUnary) encUnary := by
  unfold entryIdx
  fun_prop

theorem computableInPolyTime_auxSucc :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ × Bool => auxSucc p.1 p.2.1 p.2.2)
      (encPair encCNF (encPair encUnary encBool)) encUnary := by
  have := computableInPolyTime_firstOcc
  have := computableInPolyTime_entryIdx
  simp only [auxSucc_eq_getD]
  fun_prop

theorem computableInPolyTime_exitSucc :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => exitSucc p.1 p.2)
      (encPair encCNF encUnary) encUnary := by
  have := computableInPolyTime_nextOcc
  have := computableInPolyTime_entryIdx
  have := computableInPolyTime_litAt
  simp only [exitSucc_eq_getD]
  fun_prop

theorem computableInPolyTime_gadgetEntry :
    ComputableInPolyTime (fun p : ℕ × ℕ => gadgetEntry p.1 p.2) (encPair encUnary encUnary)
      encIntBin := by
  unfold gadgetEntry
  fun_prop

theorem computableInPolyTime_trackEntry :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ × ℕ => trackEntry p.1 p.2.1 p.2.2)
      encCNFVertexPair encIntBin := by
  have := computableInPolyTime_auxSucc
  have := computableInPolyTime_exitSucc
  unfold trackEntry exitOcc
  fun_prop

theorem computableInPolyTime_gadgetPart :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ × ℕ => gadgetPart p.1 p.2.1 p.2.2)
      encCNFVertexPair encIntBin := by
  have := computableInPolyTime_gadgetEntry
  unfold gadgetPart
  fun_prop

/-- **The entries of the 3CNF matrix are computable in polynomial time.** -/
theorem computableInPolyTime_matrixEntry :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ × ℕ => matrixEntry p.1 p.2.1 p.2.2)
      encCNFVertexPair encIntBin := by
  have := computableInPolyTime_trackEntry
  have := computableInPolyTime_gadgetPart
  unfold matrixEntry
  fun_prop

end Cslib.Complexity.PermanentThreeSAT

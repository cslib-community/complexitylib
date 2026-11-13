/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Permanent.ThreeSAT.Gadget
public import CslibFrontier.Logics.Propositional.CNF.ModelCount

/-!
# The matrix of a 3CNF formula

The construction of Goldreich's proof of Proposition 6.21 [Goldreich, Section 6.2.1]
[Goldreich2007Draft], on natural-number vertex indices. For a formula `φ` with `m` clauses and
`n` distinct variables (`varList φ`, the distinct variables in order of first occurrence), the
vertices are `0, …, n - 1`, one auxiliary vertex per variable, followed by eight vertices
`n + 8 j, …, n + 8 j + 7` for clause `j`, carrying the clause gadget. Clause `j` is padded to
three literals by repeating its last literal, and its literal occurrences are numbered
`o = 3 j + p`; occurrence `o` enters its gadget at `entryIdx φ o` and leaves at `exitIdx φ o`.

The track of a literal `(x, b)` is a cycle of weight-`1` edges through the auxiliary vertex of `x`
and the occurrences of the literal in increasing order: from the auxiliary vertex to the entry of
the first occurrence, from the exit of each occurrence to the entry of the next one, and from the
exit of the last one back to the auxiliary vertex; it is a self-loop when the literal does not
occur. `auxSucc φ i b` and `exitSucc φ o` are the heads of these edges, and `matrixEntry φ k l` is
the gadget entry plus the number of track edges from `k` to `l`.

## Main definitions

* `Cslib.Complexity.PermanentThreeSAT.litAt`: the padded literal of an occurrence.
* `Cslib.Complexity.PermanentThreeSAT.auxSucc`, `Cslib.Complexity.PermanentThreeSAT.exitSucc`:
  the track edges.
* `Cslib.Complexity.PermanentThreeSAT.matrixEntry`: the entries of the matrix.
* `Cslib.Complexity.PermanentThreeSAT.WellFormed`: every clause has one to three literals.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, 2007 draft]
  [Goldreich2007Draft]
-/

@[expose] public section

namespace Cslib.Complexity.PermanentThreeSAT

open Cslib.Logic.PL PermanentGadget

variable (φ : CNF ℕ)

/-- The distinct variables of `φ`, in order of first occurrence. -/
def varList : List ℕ := φ.distinctVars

/-- The number of distinct variables: the auxiliary vertices. -/
def numAux : ℕ := (varList φ).length

/-- The number of literal occurrences, three per clause. -/
def numOcc : ℕ := 3 * φ.length

/-- The number of vertices. -/
def size : ℕ := numAux φ + 8 * φ.length

/-- The literal at occurrence `o`: position `o % 3` of clause `o / 3`, where a clause is padded
to three literals by repeating its last literal. -/
def litAt (o : ℕ) : Literal ℕ :=
  (φ.getD (o / 3) []).getD (min (o % 3) ((φ.getD (o / 3) []).length - 1)) (0, false)

/-- The first occurrence of a literal, if any. -/
def firstOcc (ℓ : Literal ℕ) : Option ℕ :=
  (List.range (numOcc φ)).find? fun o => litAt φ o == ℓ

/-- The next occurrence of the literal of occurrence `o`, if any. -/
def nextOcc (o : ℕ) : Option ℕ :=
  (List.range (numOcc φ)).find? fun o' => decide (o < o') && litAt φ o' == litAt φ o

/-- The entry vertex of occurrence `o`. -/
def entryIdx (o : ℕ) : ℕ := numAux φ + 8 * (o / 3) + o % 3

/-- The exit vertex of occurrence `o`. -/
def exitIdx (o : ℕ) : ℕ := numAux φ + 8 * (o / 3) + (o % 3 + 3)

/-- The head of the track edge of the literal `(varList φ)[i], b` leaving the auxiliary vertex
`i`: the entry of its first occurrence, or `i` itself. -/
def auxSucc (i : ℕ) (b : Bool) : ℕ :=
  match firstOcc φ ((varList φ).getD i 0, b) with
  | some o => entryIdx φ o
  | none => i

/-- The head of the track edge leaving the exit of occurrence `o`: the entry of the next
occurrence of the same literal, or the auxiliary vertex of its variable. -/
def exitSucc (o : ℕ) : ℕ :=
  match nextOcc φ o with
  | some o' => entryIdx φ o'
  | none => (varList φ).idxOf (litAt φ o).1

/-- The occurrence whose exit is the vertex `k`. -/
def exitOcc (k : ℕ) : ℕ := 3 * ((k - numAux φ) / 8) + ((k - numAux φ) % 8 - 3)

/-- The number of track edges from `k` to `l`. -/
def trackEntry (k l : ℕ) : ℤ :=
  if k < numAux φ then
    (if auxSucc φ k true = l then 1 else 0) + (if auxSucc φ k false = l then 1 else 0)
  else if 3 ≤ (k - numAux φ) % 8 ∧ (k - numAux φ) % 8 < 6 then
    if exitSucc φ (exitOcc φ k) = l then 1 else 0
  else 0

/-- The gadget entry between `k` and `l`, if both lie in the same clause gadget. -/
def gadgetPart (k l : ℕ) : ℤ :=
  if numAux φ ≤ k ∧ numAux φ ≤ l ∧ (k - numAux φ) / 8 = (l - numAux φ) / 8 then
    gadgetEntry ((k - numAux φ) % 8) ((l - numAux φ) % 8)
  else 0

/-- The entries of the matrix: gadget entries plus track edges. -/
def matrixEntry (k l : ℕ) : ℤ := gadgetPart φ k l + trackEntry φ k l

/-- Every clause has one, two or three literals. -/
def WellFormed : Prop := ∀ c ∈ φ, 1 ≤ c.length ∧ c.length ≤ 3

instance : DecidablePred WellFormed := fun φ =>
  inferInstanceAs (Decidable (∀ c ∈ φ, 1 ≤ c.length ∧ c.length ≤ 3))

end Cslib.Complexity.PermanentThreeSAT

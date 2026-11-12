/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Operations

/-!
# Choosing one of distinct communication instances

[ChukhinKulikovMihajlinSmal2026], Definition 3.4 (printed p. 7; PDF p. 8) and the upper-bound
proof of Theorem 1.1 (printed p. 9; PDF p. 10), give each player an
injective tuple and asks for a coordinate and a valid answer there. `Relation` uses
embeddings to enforce distinctness separately on the two sides. `atCoordinate` implements
the source's upper bound by running a given protocol on one fixed coordinate.
The reverse lower bound of Theorems 1.1 and 1.2 remains open.

## Main definitions

* `Answer`: an index together with the answer for that instance.
* `Relation`: the indexed-output relation on two injective tuples.

## Main results

* `solves_atCoordinate`: the constructed protocol solves the actual relation.
* `ecomplexity_le`: choosing among distinct instances costs no more than solving one.
-/

public section
namespace Cslib.Communication.OneOut
open Protocol
variable {X Y Z : Type*} {k : ℕ}

/-- An output specifies which instance was solved and a valid answer for it. -/
structure Answer (k : ℕ) (Z : Type*) where
  /-- Coordinate selected by the protocol. -/
  index : Fin k
  /-- Answer for the selected coordinate. -/
  value : Z

/-- Distinctness is enforced by the embedding input types, not promised by the caller. -/
@[expose] def Relation (R : X → Y → Z → Prop)
    (x : Fin k ↪ X) (y : Fin k ↪ Y) (z : Answer k Z) : Prop :=
  R (x z.index) (y z.index) z.value

/-- Execute a single-instance protocol on coordinate `i` and announce that index. -/
@[expose] def atCoordinate (p : Protocol X Y Z) (i : Fin k) :
    Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z) :=
  (p.comap (fun x => x i) (fun y => y i)).map (fun z => ⟨i, z⟩)

/-- Selecting a fixed coordinate sends exactly the bits of the original protocol. -/
@[simp] theorem depth_atCoordinate (p : Protocol X Y Z) (i : Fin k) :
    (atCoordinate p i).depth = p.depth := by
  simp [atCoordinate]

/-- The fixed-coordinate protocol outputs a correct index/answer pair. -/
theorem solves_atCoordinate {R : X → Y → Z → Prop} {p : Protocol X Y Z}
    (hp : p.Solves R Set.univ Set.univ) (i : Fin k) :
    (atCoordinate p i).Solves (Relation R) Set.univ Set.univ := by
  intro x _ y _
  simpa [atCoordinate, Relation] using hp (x i) trivial (y i) trivial

/-- The upper half of the one-out bound, for total search relations as well as functions.
An explicit coordinate excludes the empty-tuple case. No finiteness or totality is needed. -/
theorem ecomplexity_le (R : X → Y → Z → Prop) (i : Fin k) :
    ecomplexity (Relation (k := k) R) Set.univ Set.univ ≤
      ecomplexity R Set.univ Set.univ := by
  unfold ecomplexity
  apply le_iInf
  intro p
  exact (ecomplexity_le_depth (solves_atCoordinate p.2 i)).trans_eq
    (by simp)

end Cslib.Communication.OneOut

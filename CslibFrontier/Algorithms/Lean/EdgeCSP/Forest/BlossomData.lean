/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Search

/-!
# Executable ancestral-path and cycle data at a forest meeting

The two cases at the start of Section 5.3 of [KazdaKolmogorovRolinek2018],
arXiv:1602.03124v6, printed pp. 11–12, distinguish a variable lowest common ancestor
from a copied-constraint lowest common ancestor. In the latter case the child on the left
path becomes the new base after flipping its root path. The final cycle step uses the
two actual child ports at the common copied constraint.

`Meeting.blossomData` computes this information from actual paths; it does not replace
the two cases by an arbitrary constraint name or a flag. Timestamps identify copied nodes,
so repeated appearances of an original constraint are not conflated. Its `Option` records
the absence of a common root on augmentation events and permits total evaluation of externally
constructed malformed meeting records. The blossom validity theorem is a separate obligation.

## Main definitions

* `Meeting.blossomData`: actual cycle, preparatory root path, meeting pivot and LCA child ports.
-/

public section

namespace Cslib.Logic.PL.CSP.Forest

open DAG

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]

namespace Ancestry

/-- The actual variable and copied-constraint nodes of a timestamped ancestral walk.
Valid search ancestries have exactly one timestamp per step. -/
@[expose] def nodes (p : Ancestry F) : List (Node F) :=
  .inl p.walk.start :: (p.walk.steps.zip p.times).flatMap fun ((input, output), t) =>
    [.inr (input.1, t), .inl output.var]

end Ancestry

/-- Actual cycle, base and root-path preparation for the contraction layer.
These are raw executable data; the record itself asserts no blossom-correctness premise. -/
structure BlossomData (F : CSP Rel V) where
  /-- Copied or variable node that is the lowest common ancestor of the meeting endpoints. -/
  ancestor : Node F
  /-- Root-to-base prefix to flip before contraction; empty in the source's variable-LCA case. -/
  prepare : Walk F
  /-- Actual closed cycle of positional incidence pairs, oriented from the new base. -/
  cycle : Walk F
  /-- One timestamp per cycle step; orientation is reversed after the meeting copy. -/
  times : List ℕ
  /-- Number of steps from the new base through the meeting copied constraint. -/
  pivot : ℕ
  /-- Actual left child port at a constraint LCA, absent for a variable LCA. -/
  leftPort : Option (Occurrence F)
  /-- Actual right child port at a constraint LCA, absent for a variable LCA. -/
  rightPort : Option (Occurrence F)

namespace Meeting

/-- Shared ancestral nodes, with both the original constraint position and its timestamp
participating in copied-node equality. -/
@[expose] def commonNodes (m : Meeting F) : List (Node F) :=
  ((m.left.nodes.zip m.right.nodes).takeWhile fun (a, b) => a == b).map Prod.fst

/-- Last common ancestral node, absent when the endpoints lie in different trees. -/
@[expose] def ancestor? (m : Meeting F) : Option (Node F) := m.commonNodes.getLast?

/-- The cycle and preparatory prefix specified at the start of source Section 5.3.
In the constraint-LCA case the final step crosses the two actual child ports at that copy;
the preparatory path ends at the left child and includes the LCA step. -/
@[expose] def blossomData (m : Meeting F) : Option (BlossomData F) :=
  match m.ancestor? with
  | none => none
  | some ancestor =>
    let k := (m.commonNodes.length - 1) / 2
    match ancestor with
    | .inl base =>
      let left : Walk F := ⟨base, m.left.walk.steps.drop k⟩
      let right : Walk F := ⟨base, m.right.walk.steps.drop k⟩
      some ⟨ancestor, m.left.walk.take k,
        (left.snoc m.current.input m.output).append right.reverse,
        m.left.times.drop k ++ [m.older.length] ++ (m.right.times.drop k).reverse,
        left.steps.length + 1, none, none⟩
    | .inr c =>
      match m.left.walk.steps[k]?, m.right.walk.steps[k]? with
      | some (_, leftPort), some (_, rightPort) =>
        let left : Walk F := ⟨leftPort.var, m.left.walk.steps.drop (k + 1)⟩
        let right : Walk F := ⟨rightPort.var, m.right.walk.steps.drop (k + 1)⟩
        some ⟨ancestor, m.left.walk.take (k + 1),
          (((left.snoc m.current.input m.output).append right.reverse).snoc rightPort leftPort),
          m.left.times.drop (k + 1) ++ [m.older.length] ++
            (m.right.times.drop (k + 1)).reverse ++ [c.2],
          left.steps.length + 1, some leftPort, some rightPort⟩
      | _, _ => none

end Meeting

end Cslib.Logic.PL.CSP.Forest

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.MCSP.Magnification.MergeTree

/-!
# Tests: the oracle of the McKay–Murray–Williams merge tree

A single root leaf query on a whole truth table decides `MCSP[s]`, a node query is its header
followed by its payload, the header length does not depend on the requested bit, and the header
carries the arity.
-/

namespace CslibFrontierTests.MagnificationMergeTree

open Cslib Cslib.MCSP Cslib.MCSP.MergeTree

/-- The one-node tree: a root leaf query on the whole truth table decides `MCSP[s]`. -/
theorem root_leaf_mem_oracle_iff (s : ℕ → ℕ) (n : ℕ) (T : BitString (2 ^ n)) :
    encQuery (Query.ofNode n (s n) [] n true 0 (List.ofFn T)) ∈ oracle ↔
      (GapMCSP.yesSet s).slice (2 ^ n) T = true :=
  encQuery_ofNode_nil_mem_oracle_iff_leaf s T fun e => by simp

/-- The header of a node query has the same length for every requested bit, so all the queries of
one node have one length. -/
example (n s : ℕ) (p : List Bool) (k : ℕ) (leaf : Bool) (j j' : Fin (stateWidth n s))
    (v : List Bool) :
    (encQuery (Query.ofNode n s p k leaf j v)).length =
      (encQuery (Query.ofNode n s p k leaf j' v)).length := by
  rw [encQuery_ofNode, encQuery_ofNode _ _ _ _ _ j', List.length_append, List.length_append,
    length_encQuery_ofNode _ _ _ _ _ j.isLt.le, length_encQuery_ofNode _ _ _ _ _ j'.isLt.le]

/-- The header carries the arity: queries for different arities are different words, so one oracle
serves every arity. -/
example : encQuery (Query.ofNode 1 0 [] 0 true 0 []) ≠ encQuery (Query.ofNode 2 0 [] 0 true 0 []) :=
  fun h => by simpa [Query.ofNode] using congrArg Query.arity (encQuery.injective h)

/-- `mergeLanguage` satisfies the hypothesis of the binary merge step. -/
example {n s : ℕ} (f : BooleanFunction n) {p : List Bool} (hp : p.length < n) :
    mergeVec mergeLanguage n s p
        (Fin.append (subcubeState n s f (p ++ [false])) (subcubeState n s f (p ++ [true]))) =
      subcubeState n s f p :=
  mergeVec_eq_subcubeState (fun a => (encMerge_mem_mergeLanguage_iff a).symm) f hp

end CslibFrontierTests.MagnificationMergeTree

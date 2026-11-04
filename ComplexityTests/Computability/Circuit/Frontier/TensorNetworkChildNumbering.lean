/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ChildNumbering
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ModeExpansion

public section

open Cslib.Circuits.Frontier.ChildNumbering

namespace Cslib.Tests.TensorNetworkChildNumbering

/-! ### A four-cycle split into two groups

Rows `0, 1` and columns `2, 3` with groups `0, 1, 0, 1`, and the four edges `(0, 2)`, `(0, 3)`,
`(1, 2)`, `(1, 3)` in packets `0, 0, 1, 1`. The child of group `0` has the vertices `0` and `2`,
numbered `0` and `1`, and the packets, numbered `2` and `3`. Its edges are the row ports of edges
`0` and `1` at row `0`, then the column ports of edges `0` and `2` at column `2`. -/

def groupOf (v : Fin 4) : Fin 2 := ⟨v.val % 2, Nat.mod_lt _ (by omega)⟩
def src (e : Fin 4) : Fin 4 := ⟨e.val / 2, by omega⟩
def tgt (e : Fin 4) : Fin 4 := ⟨2 + e.val % 2, by omega⟩
def packet (e : Fin 4) : Fin 2 := ⟨e.val / 2, by omega⟩

example : childEdgeList [0, 1, 0, 1] 0 [(0, 2), (0, 3), (1, 2), (1, 3)] [0, 0, 1, 1] =
    [(0, 2), (0, 2), (1, 2), (1, 3)] := by
  decide +kernel

/-- The ports of the four child vertices. -/
example : (List.range 4).map (childPorts [(0, 2), (0, 2), (1, 2), (1, 3)]) =
    [[0, 1], [2, 3], [0, 1, 2], [3]] := by
  decide +kernel

/-- The native child edges are the numbered ends of the child edges. -/
example : childEdgeList (List.ofFn fun v => (groupOf v : ℕ)) 0
      (List.ofFn fun e => ((src e : ℕ), (tgt e : ℕ))) (List.ofFn fun e => (packet e : ℕ)) =
    List.ofFn fun j => (((childVertexEquiv (P := 2) groupOf 0)
        (childSrc src tgt groupOf 0 ((childEdgeEquiv src tgt groupOf 0).symm j)) : ℕ),
      ((childVertexEquiv groupOf 0)
        (childTgt src tgt groupOf packet 0 ((childEdgeEquiv src tgt groupOf 0).symm j)) : ℕ)) :=
  childEdgeList_eq src tgt groupOf packet 0

example : List.ofFn (fun e => ((src e : ℕ), (tgt e : ℕ))) = [(0, 2), (0, 3), (1, 2), (1, 3)] := by
  decide +kernel

/-! ### The children of a mode splitting

The ends of the edges of `TensorNetwork.ModeSplitting.child` are `childSrc` and `childTgt` for the
groups and packets of the splitting, by definition. -/

open Cslib.Circuits.Frontier in
example {R : Type} [CommRing R] {n m P : ℕ} {M : Type} [Fintype M] [DecidableEq M]
    {N : TensorNetwork R Bool (Fin n) (Fin m)} {W : Matrix (Fin m) (Fin m) R}
    (S : N.ModeSplitting W (Fin 2) (Fin P) M) (β : M → ℕ) (g : Fin 2) :
    (S.child β g).src = childSrc N.src N.tgt S.group g ∧
      (S.child β g).tgt = childTgt N.src N.tgt S.group S.packet g :=
  ⟨rfl, rfl⟩

end Cslib.Tests.TensorNetworkChildNumbering

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Network
public import Complexity.Computability.Circuit.Frontier.TensorNetwork
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Constraint networks as `0`–`1` tensor networks

A constraint network (`Cslib.Circuits.Frontier.Network`) on a fixed input is a tensor network
whose tensors take only the values zero and one: the tensor at `v` is the indicator of the
constraint at `v` (`Network.toTensorNetwork`). The two share the multigraph, and the locality of
the constraints is the locality of the tensors. The contraction of this tensor network is the
number of satisfying assignments (`Network.contraction_toTensorNetwork`), so over `ℕ` it is
nonzero exactly at the accepted inputs (`Network.mem_accepted_iff_contraction_ne_zero`).

A general tensor network is thus the weighted form of a constraint network, and the frontier
constraint networks of circuits (`Cslib.Circuits.Frontier.Compiler.network`) are special cases.

## Main definitions

* `Cslib.Circuits.Frontier.Network.toTensorNetwork`: the indicator tensor network of a constraint
  network on an input.

## Main results

* `Cslib.Circuits.Frontier.Network.contraction_toTensorNetwork`: its contraction counts the
  satisfying assignments.
* `Cslib.Circuits.Frontier.Network.mem_accepted_iff_contraction_ne_zero`: an input is accepted iff
  the contraction over `ℕ` is nonzero.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.Network

variable {U ι V E : Type*} (R : Type*) (N : Network U ι V E)

open Classical in
/-- The `0`–`1` tensor network of a constraint network on the input `x`: the same multigraph, with
the tensor at `v` equal to one where the constraint at `v` holds and to zero elsewhere. -/
noncomputable def toTensorNetwork [Zero R] [One R] (x : ι → U) : TensorNetwork R U V E where
  toMultigraph := N.toMultigraph
  tensor v α := if N.Constraint v x α then 1 else 0
  tensor_congr v α β h := by
    have hiff : N.Constraint v x α ↔ N.Constraint v x β :=
      ⟨N.constraint_congr v x x α β (fun _ _ => rfl) h,
        N.constraint_congr v x x β α (fun _ _ => rfl) fun e he => (h e he).symm⟩
    simp only [hiff]

/-- The tensor network of a constraint network has the same multigraph. -/
@[simp] theorem toMultigraph_toTensorNetwork [Zero R] [One R] (x : ι → U) :
    (N.toTensorNetwork R x).toMultigraph = N.toMultigraph :=
  rfl

/-- **The contraction counts satisfying assignments.** The contraction of the `0`–`1` tensor
network of a constraint network on the input `x` is the number of assignments of values to the
edges that satisfy every constraint on `x`. -/
theorem contraction_toTensorNetwork [CommSemiring R] [Fintype U] [Fintype V] [Fintype E]
    [DecidableEq E] (x : ι → U) :
    (N.toTensorNetwork R x).contraction = ({α | N.Satisfies x α} : Set (E → U)).ncard := by
  classical
  simp only [TensorNetwork.contraction, toTensorNetwork, Fintype.prod_boole, Finset.sum_boole,
    Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Satisfies]

/-- Over `ℕ`, the contraction is nonzero exactly at the accepted inputs. -/
theorem mem_accepted_iff_contraction_ne_zero [Fintype U] [Fintype V] [Fintype E] [DecidableEq E]
    (x : ι → U) : x ∈ N.accepted ↔ (N.toTensorNetwork ℕ x).contraction ≠ 0 := by
  rw [contraction_toTensorNetwork, Nat.cast_id, Ne, Set.ncard_eq_zero (Set.toFinite _),
    ← Ne, ← Set.nonempty_iff_ne_empty]
  rfl

end Cslib.Circuits.Frontier.Network

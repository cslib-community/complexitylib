/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Constraint
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Explicit
public import Mathlib.Data.ZMod.Defs

/-!
# Tests for tensor networks

Hand-checked contractions of small explicit Boolean tensor networks (two parallel edges, and
four-cycles of equality and negation tensors over `ZMod 8`), a tensor network on finite types
written out and subdivided, and a constraint network counted by its indicator tensor network.
-/

@[expose] public section

namespace ComplexityTests.Computability.Circuit.Frontier.TensorNetwork

open Cslib.Circuits.Frontier

/-! ### Explicit networks -/

/-- Two vertices joined by two parallel edges `0` and `1`, with the tables `A = (1, 2, 3, 4)` and
`B = (5, 6, 7, 8)`, read at positions `x₀ + 2 x₁`. -/
def parallel : ExplicitTensorNetwork ℤ :=
  ⟨2, [([0, 1], [1, 2, 3, 4]), ([0, 1], [5, 6, 7, 8])]⟩

/-- By hand: `Z = ∑ᵢ Aᵢ Bᵢ = 1·5 + 2·6 + 3·7 + 4·8 = 70`. -/
example : parallel.contraction = 70 := by decide

example : parallel.maxDegree = 2 ∧ parallel.tableLength = 8 := by decide

/-- The equality tensor on two ports. -/
def eqTable : List (ZMod 8) := [1, 0, 0, 1]

/-- The negation tensor on two ports: its two bits differ. -/
def neTable : List (ZMod 8) := [0, 1, 1, 0]

/-- A bipartite four-cycle `r₀ - c₀ - r₁ - c₁ - r₀` on the edges `0, 1, 2, 3`, with the table `t`
at `c₁` and equality tensors elsewhere. -/
def cycle (t : List (ZMod 8)) : ExplicitTensorNetwork (ZMod 8) :=
  ⟨4, [([3, 0], eqTable), ([0, 1], eqTable), ([1, 2], eqTable), ([2, 3], t)]⟩

/-- With equality tensors all around, an assignment contributes exactly when all four bits are
equal: `Z = 2`. -/
example : (cycle eqTable).contraction = 2 := by decide

/-- One negation on a cycle forces an odd number of bit changes around it, which is impossible:
`Z = 0`. -/
example : (cycle neTable).contraction = 0 := by decide

/-! ### A network on finite types, written out and subdivided -/

/-- The table `A` or `B` of `parallel` as a tensor on assignments to `Fin 2`. -/
def table (v : Fin 2) (x : Fin 2 → Bool) : ℤ :=
  [[1, 2, 3, 4], [5, 6, 7, 8]][v]!.getD (Cslib.BitString.lsbValue [x 0, x 1]) 0

/-- The network `parallel` on `Fin 2` vertices and `Fin 2` edges, both edges from `0` to `1`.
Every edge is at both vertices, so the tensors are trivially local. -/
def parallelNetwork : TensorNetwork ℤ Bool (Fin 2) (Fin 2) where
  src _ := 0
  tgt _ := 1
  tensor := table
  tensor_congr v x y h := by
    have hxy : x = y := funext fun e => h e (by fin_cases v <;> simp)
    rw [hxy]

/-- Writing the network out gives `parallel` up to the order of its data, and the same
contraction. -/
example : parallelNetwork.contraction = 70 := by
  rw [← parallelNetwork.contraction_toExplicit (Equiv.refl _) (Equiv.refl _)]
  decide

/-- Subdividing both edges by equality tensors gives a bipartite network with the same
contraction and degree bound. -/
example : parallelNetwork.subdivide.contraction = 70 ∧ parallelNetwork.subdivide.IsBipartite ∧
    parallelNetwork.subdivide.MaxDegreeLE 2 := by
  refine ⟨?_, parallelNetwork.isBipartite_subdivide,
    parallelNetwork.maxDegreeLE_subdivide (fun e => by simp [parallelNetwork]) (fun v => ?_)
      le_rfl⟩
  · rw [TensorNetwork.contraction_subdivide,
      ← parallelNetwork.contraction_toExplicit (Equiv.refl _) (Equiv.refl _)]
    decide
  · exact (Set.ncard_le_card _).trans (by simp)

/-! ### Constraint networks -/

/-- Two vertices joined by two parallel edges, each requiring its two edges to agree. -/
def agree : Network Bool Empty (Fin 2) (Fin 2) where
  src _ := 0
  tgt _ := 1
  site := Empty.elim
  Constraint _ _ α := α 0 = α 1
  constraint_congr v _ _ α β _ h hα := by
    have h' : ∀ e, α e = β e := fun e => h e (by fin_cases v <;> simp)
    rw [← h' 0, ← h' 1]
    exact hα

/-- The indicator tensor network of `agree` counts its two satisfying assignments. -/
example : (agree.toTensorNetwork ℕ Empty.elim).contraction = 2 := by
  rw [Network.contraction_toTensorNetwork, Nat.cast_id]
  have hsat : {α | agree.Satisfies Empty.elim α} = {fun _ => false, fun _ => true} := by
    ext α
    simp only [Network.Satisfies, agree, Set.mem_ofPred_eq, forall_const, Set.mem_insert_iff,
      Set.mem_singleton_iff, funext_iff, Fin.forall_fin_two]
    cases α 0 <;> cases α 1 <;> simp
  rw [hsat, Set.ncard_pair (fun h => Bool.false_ne_true (congrFun h 0))]

end ComplexityTests.Computability.Circuit.Frontier.TensorNetwork

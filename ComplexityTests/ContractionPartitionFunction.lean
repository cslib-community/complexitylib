/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.FineGrained.ContractionPartitionFunction

/-! # Weighted `#CSP` by tensor contraction: checked instances

The hard-core instance of the path `0 - 1 - 2` (a vertex constraint per vertex, of weight `λ` at
`true`, and an edge constraint per edge, forbidding two `true` ends): its partition function counts
the independent sets weighted by `λ ^ size`, its constraint network and admissibility, the guard,
and the counter on bounded-degree instances. -/

namespace ComplexityTests.ContractionPartitionFunction

open Cslib.Logic.PL Cslib.Circuits.Frontier Cslib.Circuits.Frontier.ClauseNetwork
  Cslib.Complexity Cslib.Complexity.ContractionPartitionFunction Cslib.Complexity.CountingSimulation

/-- The hard-core weights with fugacity `t`: a vertex constraint (`false`) weighs `t` when its
variable is `true`; an edge constraint (`true`) weighs zero when both its variables are `true`. -/
def hardCore (t : ℕ) (R : Bool) (w : List Bool) : ℕ :=
  if R then (if w = [true, true] then 0 else 1) else (if w = [true] then t else 1)

/-- The hard-core instance of the path `0 - 1 - 2`. -/
def path₃ : CSP Bool ℕ :=
  [(false, [0]), (false, [1]), (false, [2]), (true, [0, 1]), (true, [1, 2])]

-- The path has five independent sets: `∅, {0}, {1}, {2}, {0, 2}`.
example : path₃.partitionFunction (hardCore 1) = 5 := by decide

-- With fugacity two: `1 + 2 + 2 + 2 + 4`.
example : path₃.partitionFunction (hardCore 2) = 11 := by decide

-- The `0/1` weights of the edge constraints alone count the same five sets.
example : path₃.partitionFunction (hardCore 1) =
    path₃.modelCount (fun R w => decide (hardCore 1 R w = 1)) := by decide

-- The ports of the edge constraint `1 - 2` carry its scope in order.
example : (clausePorts (occurrences path₃.varCNF) 4).map
    (fun j => var (occurrences path₃.varCNF) (j / 3)) = [1, 2] := by decide

-- Seven occurrences: 21 edges, 5 + 14 vertices, degree at most `max 2 4`.
example : (cspNetwork 2 (hardCore 1) path₃).2.numEdges = 21 ∧
    (cspNetwork 2 (hardCore 1) path₃).2.vertices.length = 19 ∧
    (cspNetwork 2 (hardCore 1) path₃).2.maxDegree = 4 := by decide

-- The row table of the edge constraint `0 - 1`, at the words `ff, tf, ft, tt`.
example : (rowVertex (occurrences path₃.varCNF) 4 (cspRow 2 (hardCore 1) path₃) 3).2 =
    [1, 1, 1, 0] := by decide

-- The contraction of the network is the partition function, that is, five.
example : (cspNetwork 2 (hardCore 1) path₃).2.contraction = 5 := by
  rw [contraction_cspNetwork (by decide)]
  decide

example : ExplicitAdmissible (2 + 4) 21 (cspNetwork 2 (hardCore 1) path₃) :=
  explicitAdmissible_cspNetwork (F := path₃) (by decide)

-- The guard rejects the empty instance, an empty scope and a scope too wide.
example : guard 2 ([] : CSP Bool ℕ) = false ∧ guard 2 [(false, [0]), (true, [])] = false ∧
    guard 1 path₃ = false := by decide

-- The machine's value is the partition function on `path₃` and on the empty instance.
example : count 2 1 (hardCore 1) path₃ = 5 := by
  rw [count_eq (by intro R w _; unfold hardCore; split_ifs <;> omega) (by decide)]
  decide

example : count 2 1 (hardCore 1) ([] : CSP Bool ℕ) = 1 := by decide

-- Every variable of `path₃` occurs at most three times.
example : ∀ v, path₃.vars.count v ≤ 3 := by
  intro v
  by_cases hv : v < 3
  · interval_cases v <;> decide
  · rw [List.count_eq_zero_of_not_mem fun h => hv ?_]
    · omega
    · simp only [path₃, CSP.vars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
      omega

-- The counter for the hard-core language on bounded-degree instances.
example : ∃ (count : CSP Bool ℕ → ℕ) (T S : CSP Bool ℕ → ℕ) (e b : ℕ),
    (∀ F : CSP Bool ℕ, (∀ c ∈ F, 1 ≤ c.2.length ∧ c.2.length ≤ 2) →
      count F = F.partitionFunction (hardCore 1)) ∧
    Turing.MultiTapeTM.ComputableInO count (encCSP Turing.MultiTapeTM.encBool
      Turing.MultiTapeTM.encNat) Turing.MultiTapeTM.encNat T S ∧
    (∀ F, S F = ((encCSP Turing.MultiTapeTM.encBool Turing.MultiTapeTM.encNat F).length + 1) ^ b) ∧
    ∀ Δ : ℕ, ∃ A : ℕ, ∀ F : CSP Bool ℕ, (∀ v, F.vars.count v ≤ Δ) →
      T F ≤ 2 ^ (A * (F.numVars + 1) / Nat.sqrt (Nat.log 2 (F.numVars + 2))) *
        ((encCSP Turing.MultiTapeTM.encBool Turing.MultiTapeTM.encNat F).length + 1) ^ e :=
  exists_partitionFunctionCounter_of_finite _ 2 (hardCore 1)

end ComplexityTests.ContractionPartitionFunction

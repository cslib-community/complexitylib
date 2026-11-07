/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.FineGrained.ContractionPartitionFunction

/-! # Weighted `#CSP` by tensor contraction: checked instances

The hard-core instance of the path `0 - 1 - 2` (a vertex constraint per vertex, of weight `t` at
`true`, and an edge constraint per edge, forbidding two `true` ends): its partition function counts
the independent sets weighted by `t ^ size`, its constraint network and admissibility, the guard,
and the counters. Perfect matchings of the 4-cycle as a Holant instance with one variable per edge
and an exactly-one constraint per vertex. -/

namespace ComplexityTests.ContractionPartitionFunction

open Cslib.Logic.PL Cslib.Circuits.Frontier Cslib.Circuits.Frontier.ClauseNetwork
  Cslib.Complexity Cslib.Complexity.ContractionPartitionFunction Cslib.Complexity.CountingSimulation

/-- The edges of the path `0 - 1 - 2`. -/
def edges₃ : List (ℕ × ℕ) := [(0, 1), (1, 2)]

/-- The hard-core instance of the path `0 - 1 - 2`. -/
def path₃ : CSP Bool ℕ := CSP.hardCore 3 edges₃

example : path₃ = [(false, [0]), (false, [1]), (false, [2]), (true, [0, 1]), (true, [1, 2])] := by
  decide

-- The path has five independent sets: `∅, {0}, {1}, {2}, {0, 2}`.
example : path₃.partitionFunction (CSP.hardCoreWeight 1) = 5 := by decide

example : (∑ I ∈ (Finset.range 3).powerset with
    ∀ x ∈ edges₃, ¬(x.1 ∈ I ∧ x.2 ∈ I), 1 ^ I.card) = 5 := by decide

example : path₃.partitionFunction (CSP.hardCoreWeight 1) = ∑ I ∈ (Finset.range 3).powerset with
    ∀ x ∈ edges₃, ¬(x.1 ∈ I ∧ x.2 ∈ I), 1 ^ I.card :=
  CSP.partitionFunction_hardCore 1 (by decide)

-- With fugacity two: `1 + 2 + 2 + 2 + 4`.
example : path₃.partitionFunction (CSP.hardCoreWeight 2) = 11 := by decide

-- With fugacity one every weight is `0` or `1`, so the partition function is a model count.
example : path₃.partitionFunction (CSP.hardCoreWeight 1) =
    path₃.modelCount (fun R w => decide (CSP.hardCoreWeight 1 R w = 1)) := by decide

-- The ports of the edge constraint `1 - 2` carry its scope in order.
example : (clausePorts (occurrences path₃.varCNF) 4).map
    (fun j => var (occurrences path₃.varCNF) (j / 3)) = [1, 2] := by decide

-- Seven occurrences: 21 edges, 5 + 14 vertices, degree at most `max 2 4`.
example : (cspNetwork 2 (CSP.hardCoreWeight 1) path₃).2.numEdges = 21 ∧
    (cspNetwork 2 (CSP.hardCoreWeight 1) path₃).2.vertices.length = 19 ∧
    (cspNetwork 2 (CSP.hardCoreWeight 1) path₃).2.maxDegree = 4 := by decide

-- The row table of the edge constraint `0 - 1`, at the words `ff, tf, ft, tt`.
example : (rowVertex (occurrences path₃.varCNF) 4 (cspRow 2 (CSP.hardCoreWeight 1) path₃) 3).2 =
    [1, 1, 1, 0] := by decide

-- The contraction of the network is the partition function, that is, five.
example : (cspNetwork 2 (CSP.hardCoreWeight 1) path₃).2.contraction = 5 := by
  rw [contraction_cspNetwork (by decide)]
  decide

example : ExplicitAdmissible (2 + 4) 21 (cspNetwork 2 (CSP.hardCoreWeight 1) path₃) :=
  explicitAdmissible_cspNetwork (F := path₃) (by decide)

-- The guard rejects the empty instance, an empty scope and a scope too wide.
example : guard 2 ([] : CSP Bool ℕ) = false ∧ guard 2 [(false, [0]), (true, [])] = false ∧
    guard 1 path₃ = false := by decide

-- The machine's value is the partition function on `path₃` and on the empty instance.
example : count 2 1 (CSP.hardCoreWeight 1) path₃ = 5 := by
  rw [count_eq (by intro R w _; unfold CSP.hardCoreWeight; split_ifs <;> omega) (by decide)]
  decide

example : count 2 1 (CSP.hardCoreWeight 1) ([] : CSP Bool ℕ) = 1 := by decide

-- The counter for the hard-core language on bounded-degree instances.
example : ∃ (count : CSP Bool ℕ → ℕ) (T S : CSP Bool ℕ → ℕ) (e b : ℕ),
    (∀ F : CSP Bool ℕ, (∀ c ∈ F, 1 ≤ c.2.length ∧ c.2.length ≤ 2) →
      count F = F.partitionFunction (CSP.hardCoreWeight 1)) ∧
    Turing.MultiTapeTM.ComputableInO count (encCSP Turing.MultiTapeTM.encBool
      Turing.MultiTapeTM.encNat) Turing.MultiTapeTM.encNat T S ∧
    (∀ F, S F = ((encCSP Turing.MultiTapeTM.encBool Turing.MultiTapeTM.encNat F).length + 1) ^ b) ∧
    ∀ Δ : ℕ, ∃ A : ℕ, ∀ F : CSP Bool ℕ, (∀ v, F.vars.count v ≤ Δ) →
      T F ≤ 2 ^ (A * (F.numVars + 1) / Nat.sqrt (Nat.log 2 (F.numVars + 2))) *
        ((encCSP Turing.MultiTapeTM.encBool Turing.MultiTapeTM.encNat F).length + 1) ^ e :=
  exists_partitionFunctionCounter_of_finite _ 2 (CSP.hardCoreWeight 1)

-- The path meets the hypotheses of the independent-set counter with `Δ = 2`, and every variable
-- of its hard-core instance occurs at most three times.
theorem count_edges₃ (v : ℕ) : (edges₃.flatMap fun x => [x.1, x.2]).count v ≤ 2 := by
  simp only [edges₃, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
    List.nil_append, List.count_cons, List.count_nil, beq_iff_eq]
  split_ifs <;> omega

example (v : ℕ) : path₃.vars.count v ≤ 3 :=
  (CSP.count_vars_hardCore 3 edges₃ v).trans (by have := count_edges₃ v; omega)

example : ∃ (count : CSP Bool ℕ → ℕ) (T S : CSP Bool ℕ → ℕ) (e b : ℕ),
    (∀ (n : ℕ) (E : List (ℕ × ℕ)), (∀ x ∈ E, x.1 < n ∧ x.2 < n) →
      count (CSP.hardCore n E) =
        ∑ I ∈ (Finset.range n).powerset with ∀ x ∈ E, ¬(x.1 ∈ I ∧ x.2 ∈ I), 1 ^ I.card) ∧
    Turing.MultiTapeTM.ComputableInO count (encCSP Turing.MultiTapeTM.encBool
      Turing.MultiTapeTM.encNat) Turing.MultiTapeTM.encNat T S ∧
    (∀ F, S F = ((encCSP Turing.MultiTapeTM.encBool Turing.MultiTapeTM.encNat F).length + 1) ^ b) ∧
    ∀ Δ : ℕ, ∃ A : ℕ, ∀ (n : ℕ) (E : List (ℕ × ℕ)), (∀ x ∈ E, x.1 < n ∧ x.2 < n) →
      (∀ v, (E.flatMap fun x => [x.1, x.2]).count v ≤ Δ) →
      T (CSP.hardCore n E) ≤ 2 ^ (A * (n + 1) / Nat.sqrt (Nat.log 2 (n + 2))) *
        ((encCSP Turing.MultiTapeTM.encBool Turing.MultiTapeTM.encNat
          (CSP.hardCore n E)).length + 1) ^ e :=
  exists_hardCoreCounter 1

/-- Exactly one `true` among the edges at a vertex. -/
def exactlyOne (_ : Unit) (w : List Bool) : ℕ := if w.count true = 1 then 1 else 0

/-- The 4-cycle `a - b - c - d - a` as a Holant instance: the variables are its edges `ab = 0`,
`bc = 1`, `cd = 2`, `da = 3`, and every vertex has an exactly-one constraint on its two edges. -/
def cycle₄ : CSP Unit ℕ := [((), [3, 0]), ((), [0, 1]), ((), [1, 2]), ((), [2, 3])]

-- The 4-cycle has two perfect matchings, `{ab, cd}` and `{bc, da}`.
example : cycle₄.partitionFunction exactlyOne = 2 := by decide

-- Every edge variable occurs twice, so the bounded-degree counter applies with `Δ = 2`.
example : ∀ v, cycle₄.vars.count v ≤ 2 := by
  intro v
  simp only [cycle₄, CSP.vars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append, List.count_cons, List.count_nil, beq_iff_eq]
  split_ifs <;> omega

end ComplexityTests.ContractionPartitionFunction

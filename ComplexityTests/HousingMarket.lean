/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Lean.HousingMarket.Incentives
import Mathlib.Data.Fin.VecNotation

/-!
# Housing markets and top trading cycles: checked instances

Kernel-checked (`decide`, no `native_decide`) examples for the Shapley–Scarf housing market and
Gale's top trading cycles algorithm (TTC):

1. Boundary cases `n = 0` and `n = 1`.
2. A three-agent market in which TTC closes a single three-cycle in its first round. The
   allocation is in the strict core, individually rational and Pareto efficient, the endowment is
   blocked, and TTC is the only strict-core allocation; no agent gains by any misreport (each
   already receives its favourite house).
3. A three-agent market in which TTC trades a two-cycle in the first round and leaves a fixed
   point (an agent keeping its own house) for the second round. Here the core is strictly larger
   than the strict core: the allocation `![2, 0, 1]` is in the core but some coalition weakly
   blocks it, and it is not competitive at any prices. The TTC prices are `![3, 3, 1]`. Agent `2`
   receives its last choice, and no agent gains by any misreport.
4. Mechanisms: keeping the endowment is strategy-proof but not Pareto efficient, and a two-agent
   mechanism that trades only when agent `0` ranks its own house first is not strategy-proof.
-/

namespace ComplexityTests.HousingMarket

open Cslib.Algorithms.Lean.HousingMarket
open Cslib.Algorithms.Lean.StableMatching (permOfInjective)

/-- A preference list over `Fin 3`, given as the vector of houses from most to least preferred. -/
abbrev pref (v : Fin 3 → Fin 3) (h : Function.Injective v := by decide) : Equiv.Perm (Fin 3) :=
  permOfInjective v h

/-! ### 1. Boundary cases -/

/-- The empty market. -/
def empty : Instance 0 := ⟨Fin.elim0⟩

example : empty.ttc = 1 ∧ empty.InStrictCore empty.ttc := by decide

/-- The market with a single agent. -/
def single : Instance 1 := ⟨fun _ => 1⟩

example : single.ttc = 1 ∧ single.InStrictCore 1 ∧ single.ttcPrice 0 = 1 := by decide

/-! ### 2. A three-cycle -/

/-- Agent `0` likes house `1` best, agent `1` likes house `2` best and agent `2` likes house `0`
best, so the first round closes the cycle `0 → 1 → 2 → 0`. -/
def ex3 : Instance 3 := ⟨![pref ![1, 0, 2], pref ![2, 1, 0], pref ![0, 1, 2]]⟩

example : ex3.cycleAgents Finset.univ = Finset.univ := by decide

example : ex3.ttc = pref ![1, 2, 0] := by decide

example : ex3.InStrictCore ex3.ttc ∧ ex3.InCore ex3.ttc ∧ ex3.IsIndividuallyRational ex3.ttc ∧
    ex3.IsParetoEfficient ex3.ttc := by decide

/-- The endowment is individually rational but the grand coalition blocks it. -/
example : ex3.IsIndividuallyRational 1 ∧ ex3.Blocks 1 Finset.univ ∧ ¬ ex3.InCore 1 := by decide

/-- TTC is the unique strict-core allocation, checked by enumerating all six allocations. -/
example : ∀ μ : Allocation 3, ex3.InStrictCore μ ↔ μ = ex3.ttc := by decide

/-- All houses leave in the first round, at price `3`. -/
example : ex3.ttcPrice = ![3, 3, 3] ∧ ex3.IsCompetitive ex3.ttc ex3.ttcPrice := by decide

/-- No agent obtains a house it prefers by any misreport. -/
example : ∀ (i : Fin 3) (π : Equiv.Perm (Fin 3)),
    ex3.rank i (ex3.ttc i) ≤ ex3.rank i ((ex3.updatePref i π).ttc i) := by decide

/-! ### 3. A fixed point in the second round; core versus strict core -/

/-- Agents `0` and `1` point to each other's houses in the first round. Agent `2`, whose favourite
house `1` is gone, keeps its own house in the second round. -/
def exCore : Instance 3 := ⟨![pref ![1, 2, 0], pref ![0, 1, 2], pref ![1, 0, 2]]⟩

example : exCore.cycleAgents Finset.univ = {0, 1} ∧ exCore.cycleAgents {2} = {2} := by decide

example : exCore.ttc = pref ![1, 0, 2] ∧ exCore.ttcPrice = ![3, 3, 1] := by decide

example : exCore.InStrictCore exCore.ttc ∧ exCore.IsCompetitive exCore.ttc exCore.ttcPrice := by
  decide

/-- `![2, 0, 1]` is in the core but not in the strict core: agents `0` and `1` weakly block it by
swapping houses, which helps agent `0` and leaves agent `1` with its favourite house. -/
example : exCore.InCore (pref ![2, 0, 1]) ∧ ¬ exCore.InStrictCore (pref ![2, 0, 1]) ∧
    exCore.WeaklyBlocks (pref ![2, 0, 1]) {0, 1} := by decide

/-- No agent obtains a house it prefers by any misreport. Agent `2` receives its last choice, so
this is not settled by agents already holding their favourite houses. -/
example : exCore.rank 2 (exCore.ttc 2) = 2 ∧ ∀ (i : Fin 3) (π : Equiv.Perm (Fin 3)),
    exCore.rank i (exCore.ttc i) ≤ exCore.rank i ((exCore.updatePref i π).ttc i) := by decide

/-- The core allocation `![2, 0, 1]` is not competitive at any prices. -/
example : ¬ ∃ p : Fin 3 → ℕ, exCore.IsCompetitive (pref ![2, 0, 1]) p := by
  rw [Instance.exists_isCompetitive_iff]
  decide

/-- The TTC prices are not unique: any prices separating the two rounds work. -/
example : exCore.IsCompetitive exCore.ttc ![5, 5, 2] ∧
    ¬ exCore.IsCompetitive exCore.ttc ![1, 1, 1] := by
  decide

/-! ### 4. Mechanisms -/

/-- The mechanism that always returns the endowment. -/
def keepEndowment : HousingMechanism 3 := fun _ => 1

/-- Keeping the endowment is strategy-proof, but it is not Pareto efficient on `ex3`. -/
example : keepEndowment.IsStrategyProof ∧ ¬ ex3.IsParetoEfficient (keepEndowment ex3) :=
  ⟨fun _ _ _ => le_rfl, by decide⟩

/-- A two-agent mechanism that swaps the two houses exactly when agent `0` ranks its own house
first. -/
def swapIfFirst : HousingMechanism 2 := fun I =>
  if I.rank 0 0 = 0 then Equiv.swap 0 1 else 1

/-- A two-agent market in which agent `0` prefers house `1` to its own house. -/
def exSwap : Instance 2 := ⟨fun _ => Equiv.swap 0 1⟩

/-- `swapIfFirst` is manipulable: in `exSwap`, truthful agent `0` keeps its own house, its last
choice, but by reporting that it prefers its own house (the list `1`, the identity) it obtains
house `1`, its first choice. -/
example : ¬ swapIfFirst.IsStrategyProof := fun h => absurd (h exSwap 0 1) (by decide)

end ComplexityTests.HousingMarket

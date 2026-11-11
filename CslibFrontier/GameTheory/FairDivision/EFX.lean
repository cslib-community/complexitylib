/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Basic
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# EFX and Pareto efficiency for additive goods

Allocations assign every good to exactly one agent. Utilities are sums of nonnegative integral
item values. The positive counterexample of [MahabadiRamakrishnanTarnawski2026], Theorem 1,
uses four agents and eight goods and rules out EFX and Pareto efficiency together.
The paper's parameterized approximate-EFX extension (Theorem 2) is outside this module.

`EFX` tests removal of every good in another agent's bundle; `ParetoOptimal` forbids
any allocation improving one agent without harming another.

## Main definitions

* `bundleValue`: an observer's additive value for a recipient's bundle.
* `EFX`: envy-freeness after removal of every single good, including zero-valued goods.
* `ParetoDominates`, `ParetoOptimal`: strict Pareto improvement and its absence.
* `PositiveCounterexample.values`: the strictly positive four-agent instance.

## Main results

* `PositiveCounterexample.efx_has_pareto_improvement`: every EFX allocation is dominated.
* `PositiveCounterexample.not_efx_and_paretoOptimal`: EFX and Pareto efficiency are incompatible.

## References

* [S. Mahabadi, P. Ramakrishnan and J. Tarnawski, *Pareto Inefficiency of EFX*]
  [MahabadiRamakrishnanTarnawski2026], Theorem 1 and Figure 2, submission PDF pp. 3 and 7.
-/

public section

namespace Cslib.FairDivision

open Finset

/-- The utility that observer `i` assigns to recipient `j`'s bundle. -/
@[expose] def bundleValue {Agent Good : Type*} [Fintype Good] [DecidableEq Agent]
    (v : Agent → Good → ℕ) (a : Good → Agent) (i j : Agent) : ℕ :=
  ∑ g, if a g = j then v i g else 0

/-- Envy-freeness after removing any single good from the envied bundle, including a good
valued zero by the observer. This is the stronger all-goods convention; it coincides with
positive-good-only EFX when all item values are positive, as in `PositiveCounterexample.values`.
See [MahabadiRamakrishnanTarnawski2026], footnote 1. -/
@[expose] def EFX {Agent Good : Type*} [Fintype Good] [DecidableEq Agent]
    (v : Agent → Good → ℕ) (a : Good → Agent) : Prop :=
  ∀ i j g, i ≠ j → a g = j → bundleValue v a i j - v i g ≤ bundleValue v a i i

/-- Every agent weakly improves, and some agent strictly improves. -/
@[expose] def ParetoDominates {Agent Good : Type*} [Fintype Good] [DecidableEq Agent]
    (v : Agent → Good → ℕ) (b a : Good → Agent) : Prop :=
  (∀ i, bundleValue v a i i ≤ bundleValue v b i i) ∧
    ∃ i, bundleValue v a i i < bundleValue v b i i

/-- No complete allocation Pareto dominates the given complete allocation. -/
@[expose] def ParetoOptimal {Agent Good : Type*} [Fintype Good] [DecidableEq Agent]
    (v : Agent → Good → ℕ) (a : Good → Agent) : Prop :=
  ¬ ∃ b, ParetoDominates v b a

/-- EFX is decidable for a finite instance. -/
instance {Agent Good : Type*} [Fintype Agent] [Fintype Good]
    [DecidableEq Agent] (v : Agent → Good → ℕ) (a : Good → Agent) :
    Decidable (EFX v a) := by
  unfold EFX
  infer_instance

/-- Pareto improvement between two allocations is decidable for a finite instance. -/
instance {Agent Good : Type*} [Fintype Agent] [Fintype Good]
    [DecidableEq Agent] (v : Agent → Good → ℕ) (a b : Good → Agent) :
    Decidable (ParetoDominates v b a) := by
  unfold ParetoDominates
  infer_instance

namespace PositiveCounterexample

/-- The four-agent, eight-good valuation table of Mahabadi, Ramakrishnan and Tarnawski,
Theorem 1, submission PDF p. 3. Goods are ordered `x,y,a,b,c,d,p,q`. -/
@[expose] def values : Fin 4 → Fin 8 → ℕ :=
  ![![7, 6, 3, 3, 1, 1, 2, 1], ![6, 7, 1, 3, 3, 1, 1, 2],
    ![7, 6, 1, 1, 3, 3, 2, 1], ![6, 7, 3, 1, 1, 3, 1, 2]]

/-- Every good has strictly positive value for every agent. -/
theorem values_pos (i : Fin 4) (g : Fin 8) : 0 < values i g := by
  fin_cases i <;> fin_cases g <;> decide

private abbrev Allocation := Fin 8 → Fin 4

private def allocation (n : ℕ) : Allocation :=
  fun g => ⟨n / 4 ^ (g : ℕ) % 4, Nat.mod_lt _ (by decide)⟩

private def witnesses : List Allocation :=
  [![0, 2, 3, 1, 1, 3, 2, 1],
    ![2, 0, 3, 1, 1, 3, 0, 3],
    ![1, 3, 0, 0, 2, 2, 0, 1],
    ![1, 3, 0, 0, 2, 2, 2, 1],
    ![0, 2, 3, 1, 1, 3, 2, 3],
    ![2, 0, 3, 1, 1, 3, 0, 1],
    ![3, 1, 0, 0, 2, 2, 0, 3],
    ![3, 1, 0, 0, 2, 2, 2, 3],
    ![0, 1, 3, 0, 2, 2, 2, 3],
    ![0, 1, 3, 0, 2, 2, 3, 3],
    ![0, 1, 3, 1, 2, 2, 3, 3],
    ![0, 1, 3, 1, 2, 3, 2, 3],
    ![0, 2, 3, 1, 1, 3, 0, 3],
    ![0, 3, 0, 1, 2, 2, 2, 1],
    ![0, 3, 3, 1, 1, 2, 2, 1],
    ![0, 3, 3, 1, 1, 2, 2, 2],
    ![1, 3, 0, 0, 2, 2, 2, 3],
    ![2, 0, 3, 1, 1, 3, 2, 1],
    ![2, 0, 3, 1, 1, 3, 2, 3],
    ![2, 1, 0, 0, 1, 3, 3, 3],
    ![2, 1, 0, 0, 2, 3, 0, 3],
    ![2, 1, 3, 0, 1, 3, 0, 3],
    ![2, 3, 0, 0, 1, 2, 0, 1],
    ![2, 3, 0, 1, 1, 3, 0, 1]]

private def verified (n : ℕ) : Prop :=
  EFX values (allocation n) →
    witnesses.any (fun b => decide (ParetoDominates values b (allocation n))) = true

private instance (n : ℕ) : Decidable (verified n) := by
  unfold verified
  infer_instance

section FiniteCertificate

-- The finite universal decider traverses 256 allocations in each block.
-- A local recursion allowance accommodates that traversal; evaluation stays in the kernel.
set_option maxRecDepth 2048

private theorem block0 : ∀ i : Fin 256, verified (0 * 256 + i.val) := by decide
private theorem block1 : ∀ i : Fin 256, verified (1 * 256 + i.val) := by decide
private theorem block2 : ∀ i : Fin 256, verified (2 * 256 + i.val) := by decide
private theorem block3 : ∀ i : Fin 256, verified (3 * 256 + i.val) := by decide
private theorem block4 : ∀ i : Fin 256, verified (4 * 256 + i.val) := by decide
private theorem block5 : ∀ i : Fin 256, verified (5 * 256 + i.val) := by decide
private theorem block6 : ∀ i : Fin 256, verified (6 * 256 + i.val) := by decide
private theorem block7 : ∀ i : Fin 256, verified (7 * 256 + i.val) := by decide
private theorem block8 : ∀ i : Fin 256, verified (8 * 256 + i.val) := by decide
private theorem block9 : ∀ i : Fin 256, verified (9 * 256 + i.val) := by decide
private theorem block10 : ∀ i : Fin 256, verified (10 * 256 + i.val) := by decide
private theorem block11 : ∀ i : Fin 256, verified (11 * 256 + i.val) := by decide
private theorem block12 : ∀ i : Fin 256, verified (12 * 256 + i.val) := by decide
private theorem block13 : ∀ i : Fin 256, verified (13 * 256 + i.val) := by decide
private theorem block14 : ∀ i : Fin 256, verified (14 * 256 + i.val) := by decide
private theorem block15 : ∀ i : Fin 256, verified (15 * 256 + i.val) := by decide
private theorem block16 : ∀ i : Fin 256, verified (16 * 256 + i.val) := by decide
private theorem block17 : ∀ i : Fin 256, verified (17 * 256 + i.val) := by decide
private theorem block18 : ∀ i : Fin 256, verified (18 * 256 + i.val) := by decide
private theorem block19 : ∀ i : Fin 256, verified (19 * 256 + i.val) := by decide
private theorem block20 : ∀ i : Fin 256, verified (20 * 256 + i.val) := by decide
private theorem block21 : ∀ i : Fin 256, verified (21 * 256 + i.val) := by decide
private theorem block22 : ∀ i : Fin 256, verified (22 * 256 + i.val) := by decide
private theorem block23 : ∀ i : Fin 256, verified (23 * 256 + i.val) := by decide
private theorem block24 : ∀ i : Fin 256, verified (24 * 256 + i.val) := by decide
private theorem block25 : ∀ i : Fin 256, verified (25 * 256 + i.val) := by decide
private theorem block26 : ∀ i : Fin 256, verified (26 * 256 + i.val) := by decide
private theorem block27 : ∀ i : Fin 256, verified (27 * 256 + i.val) := by decide
private theorem block28 : ∀ i : Fin 256, verified (28 * 256 + i.val) := by decide
private theorem block29 : ∀ i : Fin 256, verified (29 * 256 + i.val) := by decide
private theorem block30 : ∀ i : Fin 256, verified (30 * 256 + i.val) := by decide
private theorem block31 : ∀ i : Fin 256, verified (31 * 256 + i.val) := by decide
private theorem block32 : ∀ i : Fin 256, verified (32 * 256 + i.val) := by decide
private theorem block33 : ∀ i : Fin 256, verified (33 * 256 + i.val) := by decide
private theorem block34 : ∀ i : Fin 256, verified (34 * 256 + i.val) := by decide
private theorem block35 : ∀ i : Fin 256, verified (35 * 256 + i.val) := by decide
private theorem block36 : ∀ i : Fin 256, verified (36 * 256 + i.val) := by decide
private theorem block37 : ∀ i : Fin 256, verified (37 * 256 + i.val) := by decide
private theorem block38 : ∀ i : Fin 256, verified (38 * 256 + i.val) := by decide
private theorem block39 : ∀ i : Fin 256, verified (39 * 256 + i.val) := by decide
private theorem block40 : ∀ i : Fin 256, verified (40 * 256 + i.val) := by decide
private theorem block41 : ∀ i : Fin 256, verified (41 * 256 + i.val) := by decide
private theorem block42 : ∀ i : Fin 256, verified (42 * 256 + i.val) := by decide
private theorem block43 : ∀ i : Fin 256, verified (43 * 256 + i.val) := by decide
private theorem block44 : ∀ i : Fin 256, verified (44 * 256 + i.val) := by decide
private theorem block45 : ∀ i : Fin 256, verified (45 * 256 + i.val) := by decide
private theorem block46 : ∀ i : Fin 256, verified (46 * 256 + i.val) := by decide
private theorem block47 : ∀ i : Fin 256, verified (47 * 256 + i.val) := by decide
private theorem block48 : ∀ i : Fin 256, verified (48 * 256 + i.val) := by decide
private theorem block49 : ∀ i : Fin 256, verified (49 * 256 + i.val) := by decide
private theorem block50 : ∀ i : Fin 256, verified (50 * 256 + i.val) := by decide
private theorem block51 : ∀ i : Fin 256, verified (51 * 256 + i.val) := by decide
private theorem block52 : ∀ i : Fin 256, verified (52 * 256 + i.val) := by decide
private theorem block53 : ∀ i : Fin 256, verified (53 * 256 + i.val) := by decide
private theorem block54 : ∀ i : Fin 256, verified (54 * 256 + i.val) := by decide
private theorem block55 : ∀ i : Fin 256, verified (55 * 256 + i.val) := by decide
private theorem block56 : ∀ i : Fin 256, verified (56 * 256 + i.val) := by decide
private theorem block57 : ∀ i : Fin 256, verified (57 * 256 + i.val) := by decide
private theorem block58 : ∀ i : Fin 256, verified (58 * 256 + i.val) := by decide
private theorem block59 : ∀ i : Fin 256, verified (59 * 256 + i.val) := by decide
private theorem block60 : ∀ i : Fin 256, verified (60 * 256 + i.val) := by decide
private theorem block61 : ∀ i : Fin 256, verified (61 * 256 + i.val) := by decide
private theorem block62 : ∀ i : Fin 256, verified (62 * 256 + i.val) := by decide
private theorem block63 : ∀ i : Fin 256, verified (63 * 256 + i.val) := by decide
private theorem block64 : ∀ i : Fin 256, verified (64 * 256 + i.val) := by decide
private theorem block65 : ∀ i : Fin 256, verified (65 * 256 + i.val) := by decide
private theorem block66 : ∀ i : Fin 256, verified (66 * 256 + i.val) := by decide
private theorem block67 : ∀ i : Fin 256, verified (67 * 256 + i.val) := by decide
private theorem block68 : ∀ i : Fin 256, verified (68 * 256 + i.val) := by decide
private theorem block69 : ∀ i : Fin 256, verified (69 * 256 + i.val) := by decide
private theorem block70 : ∀ i : Fin 256, verified (70 * 256 + i.val) := by decide
private theorem block71 : ∀ i : Fin 256, verified (71 * 256 + i.val) := by decide
private theorem block72 : ∀ i : Fin 256, verified (72 * 256 + i.val) := by decide
private theorem block73 : ∀ i : Fin 256, verified (73 * 256 + i.val) := by decide
private theorem block74 : ∀ i : Fin 256, verified (74 * 256 + i.val) := by decide
private theorem block75 : ∀ i : Fin 256, verified (75 * 256 + i.val) := by decide
private theorem block76 : ∀ i : Fin 256, verified (76 * 256 + i.val) := by decide
private theorem block77 : ∀ i : Fin 256, verified (77 * 256 + i.val) := by decide
private theorem block78 : ∀ i : Fin 256, verified (78 * 256 + i.val) := by decide
private theorem block79 : ∀ i : Fin 256, verified (79 * 256 + i.val) := by decide
private theorem block80 : ∀ i : Fin 256, verified (80 * 256 + i.val) := by decide
private theorem block81 : ∀ i : Fin 256, verified (81 * 256 + i.val) := by decide
private theorem block82 : ∀ i : Fin 256, verified (82 * 256 + i.val) := by decide
private theorem block83 : ∀ i : Fin 256, verified (83 * 256 + i.val) := by decide
private theorem block84 : ∀ i : Fin 256, verified (84 * 256 + i.val) := by decide
private theorem block85 : ∀ i : Fin 256, verified (85 * 256 + i.val) := by decide
private theorem block86 : ∀ i : Fin 256, verified (86 * 256 + i.val) := by decide
private theorem block87 : ∀ i : Fin 256, verified (87 * 256 + i.val) := by decide
private theorem block88 : ∀ i : Fin 256, verified (88 * 256 + i.val) := by decide
private theorem block89 : ∀ i : Fin 256, verified (89 * 256 + i.val) := by decide
private theorem block90 : ∀ i : Fin 256, verified (90 * 256 + i.val) := by decide
private theorem block91 : ∀ i : Fin 256, verified (91 * 256 + i.val) := by decide
private theorem block92 : ∀ i : Fin 256, verified (92 * 256 + i.val) := by decide
private theorem block93 : ∀ i : Fin 256, verified (93 * 256 + i.val) := by decide
private theorem block94 : ∀ i : Fin 256, verified (94 * 256 + i.val) := by decide
private theorem block95 : ∀ i : Fin 256, verified (95 * 256 + i.val) := by decide
private theorem block96 : ∀ i : Fin 256, verified (96 * 256 + i.val) := by decide
private theorem block97 : ∀ i : Fin 256, verified (97 * 256 + i.val) := by decide
private theorem block98 : ∀ i : Fin 256, verified (98 * 256 + i.val) := by decide
private theorem block99 : ∀ i : Fin 256, verified (99 * 256 + i.val) := by decide
private theorem block100 : ∀ i : Fin 256, verified (100 * 256 + i.val) := by decide
private theorem block101 : ∀ i : Fin 256, verified (101 * 256 + i.val) := by decide
private theorem block102 : ∀ i : Fin 256, verified (102 * 256 + i.val) := by decide
private theorem block103 : ∀ i : Fin 256, verified (103 * 256 + i.val) := by decide
private theorem block104 : ∀ i : Fin 256, verified (104 * 256 + i.val) := by decide
private theorem block105 : ∀ i : Fin 256, verified (105 * 256 + i.val) := by decide
private theorem block106 : ∀ i : Fin 256, verified (106 * 256 + i.val) := by decide
private theorem block107 : ∀ i : Fin 256, verified (107 * 256 + i.val) := by decide
private theorem block108 : ∀ i : Fin 256, verified (108 * 256 + i.val) := by decide
private theorem block109 : ∀ i : Fin 256, verified (109 * 256 + i.val) := by decide
private theorem block110 : ∀ i : Fin 256, verified (110 * 256 + i.val) := by decide
private theorem block111 : ∀ i : Fin 256, verified (111 * 256 + i.val) := by decide
private theorem block112 : ∀ i : Fin 256, verified (112 * 256 + i.val) := by decide
private theorem block113 : ∀ i : Fin 256, verified (113 * 256 + i.val) := by decide
private theorem block114 : ∀ i : Fin 256, verified (114 * 256 + i.val) := by decide
private theorem block115 : ∀ i : Fin 256, verified (115 * 256 + i.val) := by decide
private theorem block116 : ∀ i : Fin 256, verified (116 * 256 + i.val) := by decide
private theorem block117 : ∀ i : Fin 256, verified (117 * 256 + i.val) := by decide
private theorem block118 : ∀ i : Fin 256, verified (118 * 256 + i.val) := by decide
private theorem block119 : ∀ i : Fin 256, verified (119 * 256 + i.val) := by decide
private theorem block120 : ∀ i : Fin 256, verified (120 * 256 + i.val) := by decide
private theorem block121 : ∀ i : Fin 256, verified (121 * 256 + i.val) := by decide
private theorem block122 : ∀ i : Fin 256, verified (122 * 256 + i.val) := by decide
private theorem block123 : ∀ i : Fin 256, verified (123 * 256 + i.val) := by decide
private theorem block124 : ∀ i : Fin 256, verified (124 * 256 + i.val) := by decide
private theorem block125 : ∀ i : Fin 256, verified (125 * 256 + i.val) := by decide
private theorem block126 : ∀ i : Fin 256, verified (126 * 256 + i.val) := by decide
private theorem block127 : ∀ i : Fin 256, verified (127 * 256 + i.val) := by decide
private theorem block128 : ∀ i : Fin 256, verified (128 * 256 + i.val) := by decide
private theorem block129 : ∀ i : Fin 256, verified (129 * 256 + i.val) := by decide
private theorem block130 : ∀ i : Fin 256, verified (130 * 256 + i.val) := by decide
private theorem block131 : ∀ i : Fin 256, verified (131 * 256 + i.val) := by decide
private theorem block132 : ∀ i : Fin 256, verified (132 * 256 + i.val) := by decide
private theorem block133 : ∀ i : Fin 256, verified (133 * 256 + i.val) := by decide
private theorem block134 : ∀ i : Fin 256, verified (134 * 256 + i.val) := by decide
private theorem block135 : ∀ i : Fin 256, verified (135 * 256 + i.val) := by decide
private theorem block136 : ∀ i : Fin 256, verified (136 * 256 + i.val) := by decide
private theorem block137 : ∀ i : Fin 256, verified (137 * 256 + i.val) := by decide
private theorem block138 : ∀ i : Fin 256, verified (138 * 256 + i.val) := by decide
private theorem block139 : ∀ i : Fin 256, verified (139 * 256 + i.val) := by decide
private theorem block140 : ∀ i : Fin 256, verified (140 * 256 + i.val) := by decide
private theorem block141 : ∀ i : Fin 256, verified (141 * 256 + i.val) := by decide
private theorem block142 : ∀ i : Fin 256, verified (142 * 256 + i.val) := by decide
private theorem block143 : ∀ i : Fin 256, verified (143 * 256 + i.val) := by decide
private theorem block144 : ∀ i : Fin 256, verified (144 * 256 + i.val) := by decide
private theorem block145 : ∀ i : Fin 256, verified (145 * 256 + i.val) := by decide
private theorem block146 : ∀ i : Fin 256, verified (146 * 256 + i.val) := by decide
private theorem block147 : ∀ i : Fin 256, verified (147 * 256 + i.val) := by decide
private theorem block148 : ∀ i : Fin 256, verified (148 * 256 + i.val) := by decide
private theorem block149 : ∀ i : Fin 256, verified (149 * 256 + i.val) := by decide
private theorem block150 : ∀ i : Fin 256, verified (150 * 256 + i.val) := by decide
private theorem block151 : ∀ i : Fin 256, verified (151 * 256 + i.val) := by decide
private theorem block152 : ∀ i : Fin 256, verified (152 * 256 + i.val) := by decide
private theorem block153 : ∀ i : Fin 256, verified (153 * 256 + i.val) := by decide
private theorem block154 : ∀ i : Fin 256, verified (154 * 256 + i.val) := by decide
private theorem block155 : ∀ i : Fin 256, verified (155 * 256 + i.val) := by decide
private theorem block156 : ∀ i : Fin 256, verified (156 * 256 + i.val) := by decide
private theorem block157 : ∀ i : Fin 256, verified (157 * 256 + i.val) := by decide
private theorem block158 : ∀ i : Fin 256, verified (158 * 256 + i.val) := by decide
private theorem block159 : ∀ i : Fin 256, verified (159 * 256 + i.val) := by decide
private theorem block160 : ∀ i : Fin 256, verified (160 * 256 + i.val) := by decide
private theorem block161 : ∀ i : Fin 256, verified (161 * 256 + i.val) := by decide
private theorem block162 : ∀ i : Fin 256, verified (162 * 256 + i.val) := by decide
private theorem block163 : ∀ i : Fin 256, verified (163 * 256 + i.val) := by decide
private theorem block164 : ∀ i : Fin 256, verified (164 * 256 + i.val) := by decide
private theorem block165 : ∀ i : Fin 256, verified (165 * 256 + i.val) := by decide
private theorem block166 : ∀ i : Fin 256, verified (166 * 256 + i.val) := by decide
private theorem block167 : ∀ i : Fin 256, verified (167 * 256 + i.val) := by decide
private theorem block168 : ∀ i : Fin 256, verified (168 * 256 + i.val) := by decide
private theorem block169 : ∀ i : Fin 256, verified (169 * 256 + i.val) := by decide
private theorem block170 : ∀ i : Fin 256, verified (170 * 256 + i.val) := by decide
private theorem block171 : ∀ i : Fin 256, verified (171 * 256 + i.val) := by decide
private theorem block172 : ∀ i : Fin 256, verified (172 * 256 + i.val) := by decide
private theorem block173 : ∀ i : Fin 256, verified (173 * 256 + i.val) := by decide
private theorem block174 : ∀ i : Fin 256, verified (174 * 256 + i.val) := by decide
private theorem block175 : ∀ i : Fin 256, verified (175 * 256 + i.val) := by decide
private theorem block176 : ∀ i : Fin 256, verified (176 * 256 + i.val) := by decide
private theorem block177 : ∀ i : Fin 256, verified (177 * 256 + i.val) := by decide
private theorem block178 : ∀ i : Fin 256, verified (178 * 256 + i.val) := by decide
private theorem block179 : ∀ i : Fin 256, verified (179 * 256 + i.val) := by decide
private theorem block180 : ∀ i : Fin 256, verified (180 * 256 + i.val) := by decide
private theorem block181 : ∀ i : Fin 256, verified (181 * 256 + i.val) := by decide
private theorem block182 : ∀ i : Fin 256, verified (182 * 256 + i.val) := by decide
private theorem block183 : ∀ i : Fin 256, verified (183 * 256 + i.val) := by decide
private theorem block184 : ∀ i : Fin 256, verified (184 * 256 + i.val) := by decide
private theorem block185 : ∀ i : Fin 256, verified (185 * 256 + i.val) := by decide
private theorem block186 : ∀ i : Fin 256, verified (186 * 256 + i.val) := by decide
private theorem block187 : ∀ i : Fin 256, verified (187 * 256 + i.val) := by decide
private theorem block188 : ∀ i : Fin 256, verified (188 * 256 + i.val) := by decide
private theorem block189 : ∀ i : Fin 256, verified (189 * 256 + i.val) := by decide
private theorem block190 : ∀ i : Fin 256, verified (190 * 256 + i.val) := by decide
private theorem block191 : ∀ i : Fin 256, verified (191 * 256 + i.val) := by decide
private theorem block192 : ∀ i : Fin 256, verified (192 * 256 + i.val) := by decide
private theorem block193 : ∀ i : Fin 256, verified (193 * 256 + i.val) := by decide
private theorem block194 : ∀ i : Fin 256, verified (194 * 256 + i.val) := by decide
private theorem block195 : ∀ i : Fin 256, verified (195 * 256 + i.val) := by decide
private theorem block196 : ∀ i : Fin 256, verified (196 * 256 + i.val) := by decide
private theorem block197 : ∀ i : Fin 256, verified (197 * 256 + i.val) := by decide
private theorem block198 : ∀ i : Fin 256, verified (198 * 256 + i.val) := by decide
private theorem block199 : ∀ i : Fin 256, verified (199 * 256 + i.val) := by decide
private theorem block200 : ∀ i : Fin 256, verified (200 * 256 + i.val) := by decide
private theorem block201 : ∀ i : Fin 256, verified (201 * 256 + i.val) := by decide
private theorem block202 : ∀ i : Fin 256, verified (202 * 256 + i.val) := by decide
private theorem block203 : ∀ i : Fin 256, verified (203 * 256 + i.val) := by decide
private theorem block204 : ∀ i : Fin 256, verified (204 * 256 + i.val) := by decide
private theorem block205 : ∀ i : Fin 256, verified (205 * 256 + i.val) := by decide
private theorem block206 : ∀ i : Fin 256, verified (206 * 256 + i.val) := by decide
private theorem block207 : ∀ i : Fin 256, verified (207 * 256 + i.val) := by decide
private theorem block208 : ∀ i : Fin 256, verified (208 * 256 + i.val) := by decide
private theorem block209 : ∀ i : Fin 256, verified (209 * 256 + i.val) := by decide
private theorem block210 : ∀ i : Fin 256, verified (210 * 256 + i.val) := by decide
private theorem block211 : ∀ i : Fin 256, verified (211 * 256 + i.val) := by decide
private theorem block212 : ∀ i : Fin 256, verified (212 * 256 + i.val) := by decide
private theorem block213 : ∀ i : Fin 256, verified (213 * 256 + i.val) := by decide
private theorem block214 : ∀ i : Fin 256, verified (214 * 256 + i.val) := by decide
private theorem block215 : ∀ i : Fin 256, verified (215 * 256 + i.val) := by decide
private theorem block216 : ∀ i : Fin 256, verified (216 * 256 + i.val) := by decide
private theorem block217 : ∀ i : Fin 256, verified (217 * 256 + i.val) := by decide
private theorem block218 : ∀ i : Fin 256, verified (218 * 256 + i.val) := by decide
private theorem block219 : ∀ i : Fin 256, verified (219 * 256 + i.val) := by decide
private theorem block220 : ∀ i : Fin 256, verified (220 * 256 + i.val) := by decide
private theorem block221 : ∀ i : Fin 256, verified (221 * 256 + i.val) := by decide
private theorem block222 : ∀ i : Fin 256, verified (222 * 256 + i.val) := by decide
private theorem block223 : ∀ i : Fin 256, verified (223 * 256 + i.val) := by decide
private theorem block224 : ∀ i : Fin 256, verified (224 * 256 + i.val) := by decide
private theorem block225 : ∀ i : Fin 256, verified (225 * 256 + i.val) := by decide
private theorem block226 : ∀ i : Fin 256, verified (226 * 256 + i.val) := by decide
private theorem block227 : ∀ i : Fin 256, verified (227 * 256 + i.val) := by decide
private theorem block228 : ∀ i : Fin 256, verified (228 * 256 + i.val) := by decide
private theorem block229 : ∀ i : Fin 256, verified (229 * 256 + i.val) := by decide
private theorem block230 : ∀ i : Fin 256, verified (230 * 256 + i.val) := by decide
private theorem block231 : ∀ i : Fin 256, verified (231 * 256 + i.val) := by decide
private theorem block232 : ∀ i : Fin 256, verified (232 * 256 + i.val) := by decide
private theorem block233 : ∀ i : Fin 256, verified (233 * 256 + i.val) := by decide
private theorem block234 : ∀ i : Fin 256, verified (234 * 256 + i.val) := by decide
private theorem block235 : ∀ i : Fin 256, verified (235 * 256 + i.val) := by decide
private theorem block236 : ∀ i : Fin 256, verified (236 * 256 + i.val) := by decide
private theorem block237 : ∀ i : Fin 256, verified (237 * 256 + i.val) := by decide
private theorem block238 : ∀ i : Fin 256, verified (238 * 256 + i.val) := by decide
private theorem block239 : ∀ i : Fin 256, verified (239 * 256 + i.val) := by decide
private theorem block240 : ∀ i : Fin 256, verified (240 * 256 + i.val) := by decide
private theorem block241 : ∀ i : Fin 256, verified (241 * 256 + i.val) := by decide
private theorem block242 : ∀ i : Fin 256, verified (242 * 256 + i.val) := by decide
private theorem block243 : ∀ i : Fin 256, verified (243 * 256 + i.val) := by decide
private theorem block244 : ∀ i : Fin 256, verified (244 * 256 + i.val) := by decide
private theorem block245 : ∀ i : Fin 256, verified (245 * 256 + i.val) := by decide
private theorem block246 : ∀ i : Fin 256, verified (246 * 256 + i.val) := by decide
private theorem block247 : ∀ i : Fin 256, verified (247 * 256 + i.val) := by decide
private theorem block248 : ∀ i : Fin 256, verified (248 * 256 + i.val) := by decide
private theorem block249 : ∀ i : Fin 256, verified (249 * 256 + i.val) := by decide
private theorem block250 : ∀ i : Fin 256, verified (250 * 256 + i.val) := by decide
private theorem block251 : ∀ i : Fin 256, verified (251 * 256 + i.val) := by decide
private theorem block252 : ∀ i : Fin 256, verified (252 * 256 + i.val) := by decide
private theorem block253 : ∀ i : Fin 256, verified (253 * 256 + i.val) := by decide
private theorem block254 : ∀ i : Fin 256, verified (254 * 256 + i.val) := by decide
private theorem block255 : ∀ i : Fin 256, verified (255 * 256 + i.val) := by decide

end FiniteCertificate

private theorem verified_all (n : Fin 65536) : verified n.val := by
  have h : ∀ b : Fin 256, ∀ i : Fin 256, verified (b.val * 256 + i.val) := by
    intro b
    fin_cases b
    · exact block0
    · exact block1
    · exact block2
    · exact block3
    · exact block4
    · exact block5
    · exact block6
    · exact block7
    · exact block8
    · exact block9
    · exact block10
    · exact block11
    · exact block12
    · exact block13
    · exact block14
    · exact block15
    · exact block16
    · exact block17
    · exact block18
    · exact block19
    · exact block20
    · exact block21
    · exact block22
    · exact block23
    · exact block24
    · exact block25
    · exact block26
    · exact block27
    · exact block28
    · exact block29
    · exact block30
    · exact block31
    · exact block32
    · exact block33
    · exact block34
    · exact block35
    · exact block36
    · exact block37
    · exact block38
    · exact block39
    · exact block40
    · exact block41
    · exact block42
    · exact block43
    · exact block44
    · exact block45
    · exact block46
    · exact block47
    · exact block48
    · exact block49
    · exact block50
    · exact block51
    · exact block52
    · exact block53
    · exact block54
    · exact block55
    · exact block56
    · exact block57
    · exact block58
    · exact block59
    · exact block60
    · exact block61
    · exact block62
    · exact block63
    · exact block64
    · exact block65
    · exact block66
    · exact block67
    · exact block68
    · exact block69
    · exact block70
    · exact block71
    · exact block72
    · exact block73
    · exact block74
    · exact block75
    · exact block76
    · exact block77
    · exact block78
    · exact block79
    · exact block80
    · exact block81
    · exact block82
    · exact block83
    · exact block84
    · exact block85
    · exact block86
    · exact block87
    · exact block88
    · exact block89
    · exact block90
    · exact block91
    · exact block92
    · exact block93
    · exact block94
    · exact block95
    · exact block96
    · exact block97
    · exact block98
    · exact block99
    · exact block100
    · exact block101
    · exact block102
    · exact block103
    · exact block104
    · exact block105
    · exact block106
    · exact block107
    · exact block108
    · exact block109
    · exact block110
    · exact block111
    · exact block112
    · exact block113
    · exact block114
    · exact block115
    · exact block116
    · exact block117
    · exact block118
    · exact block119
    · exact block120
    · exact block121
    · exact block122
    · exact block123
    · exact block124
    · exact block125
    · exact block126
    · exact block127
    · exact block128
    · exact block129
    · exact block130
    · exact block131
    · exact block132
    · exact block133
    · exact block134
    · exact block135
    · exact block136
    · exact block137
    · exact block138
    · exact block139
    · exact block140
    · exact block141
    · exact block142
    · exact block143
    · exact block144
    · exact block145
    · exact block146
    · exact block147
    · exact block148
    · exact block149
    · exact block150
    · exact block151
    · exact block152
    · exact block153
    · exact block154
    · exact block155
    · exact block156
    · exact block157
    · exact block158
    · exact block159
    · exact block160
    · exact block161
    · exact block162
    · exact block163
    · exact block164
    · exact block165
    · exact block166
    · exact block167
    · exact block168
    · exact block169
    · exact block170
    · exact block171
    · exact block172
    · exact block173
    · exact block174
    · exact block175
    · exact block176
    · exact block177
    · exact block178
    · exact block179
    · exact block180
    · exact block181
    · exact block182
    · exact block183
    · exact block184
    · exact block185
    · exact block186
    · exact block187
    · exact block188
    · exact block189
    · exact block190
    · exact block191
    · exact block192
    · exact block193
    · exact block194
    · exact block195
    · exact block196
    · exact block197
    · exact block198
    · exact block199
    · exact block200
    · exact block201
    · exact block202
    · exact block203
    · exact block204
    · exact block205
    · exact block206
    · exact block207
    · exact block208
    · exact block209
    · exact block210
    · exact block211
    · exact block212
    · exact block213
    · exact block214
    · exact block215
    · exact block216
    · exact block217
    · exact block218
    · exact block219
    · exact block220
    · exact block221
    · exact block222
    · exact block223
    · exact block224
    · exact block225
    · exact block226
    · exact block227
    · exact block228
    · exact block229
    · exact block230
    · exact block231
    · exact block232
    · exact block233
    · exact block234
    · exact block235
    · exact block236
    · exact block237
    · exact block238
    · exact block239
    · exact block240
    · exact block241
    · exact block242
    · exact block243
    · exact block244
    · exact block245
    · exact block246
    · exact block247
    · exact block248
    · exact block249
    · exact block250
    · exact block251
    · exact block252
    · exact block253
    · exact block254
    · exact block255
  have h' := h ⟨n.val / 256, by omega⟩ ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  change verified (n.val / 256 * 256 + n.val % 256) at h'
  have heq : n.val / 256 * 256 + n.val % 256 = n.val := by omega
  rwa [heq] at h'

/-- Every EFX allocation of the positive instance has a strict Pareto improvement.
This is Theorem 1 of [MahabadiRamakrishnanTarnawski2026], submission PDF p. 3;
all complete allocations are covered by a kernel-checked finite certificate. -/
theorem efx_has_pareto_improvement (a : Fin 8 → Fin 4) (ha : EFX values a) :
    ∃ b, ParetoDominates values b a := by
  have hid : allocation (finFunctionFinEquiv a).val = a := by
    exact finFunctionFinEquiv.symm_apply_apply a
  have hc := verified_all (finFunctionFinEquiv a)
  unfold verified at hc
  rw [hid] at hc
  obtain ⟨b, _, hb⟩ := List.any_eq_true.mp (hc ha)
  exact ⟨b, of_decide_eq_true hb⟩

/-- Positive additive valuations need not admit an allocation that is both EFX and Pareto
optimal. This theorem concerns EFX and efficiency together, not existence of EFX alone. -/
theorem not_efx_and_paretoOptimal (a : Fin 8 → Fin 4) :
    ¬ (EFX values a ∧ ParetoOptimal values a) := by
  rintro ⟨ha, hp⟩
  exact hp (efx_has_pareto_improvement a ha)

end PositiveCounterexample

end Cslib.FairDivision

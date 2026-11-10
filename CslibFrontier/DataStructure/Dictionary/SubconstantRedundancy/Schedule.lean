/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.Dynamic.Spec
public import CslibFrontier.DataStructure.Dictionary.FeistelPerm
public import CslibFrontier.DataStructure.Dictionary.Minimap
public import CslibFrontier.DataStructure.Dictionary.SuccinctBucket
public import CslibFrontier.Foundations.Data.Nat.IterLog
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import CslibFrontier.Foundations.Data.Nat.Choose
import CslibFrontier.Foundations.Data.Nat.Choose.Vandermonde
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.Power
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multi-Level Tree Parameter Schedule and Subconstant-Redundancy Bit Budget

This module formalizes the integer-exact multi-level hashing parameter schedule and pure bit-budget
conservation bound for the large-parameter-regime dynamic succinct dictionary of Tianxiao Li,
Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic Dictionary with Subconstant Wasted Bits per
Key* ([LiLiangYuZhou2024, Section 5, Sections 5.1–5.2 and 5.4–5.6];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 25–36 / printed pp. 24–35).

## Source statements, notation mapping, and formalization adaptations

In [LiLiangYuZhou2024] (`arXiv:2310.20536v1`):
* **Regime and sentinel padding (Section 5 opening, PDF pp. 25–26 / printed pp. 24–25; Section 1,
  Theorem 1.1, PDF p. 2 / printed p. 1)**:
  For capacity `n` (`N` in the paper), polynomial universe `n ^ (1 + α_min) ≤ U ≤ n ^ (1 + α_max)`
  (encoded integer-exactly via `n ^ (q_min + p_min) ≤ U ^ q_min` and
  `U ^ q_max ≤ n ^ (q_max + p_max)`), value bound `1 ≤ V`, and redundancy
  `n / (log₂ n) ^ 0.1 ≤ R ≤ n` (`n ^ 10 ≤ R ^ 10 * Nat.log 2 n` and `R ≤ n`), the internal tree
  operates over `U_base = U + n` (adjoining `n` sentinel keys so active key count stays in
  `{n - 1, n}`) rounded up to a multiple `paddedUniv` of `B_0 * 2 ^ I_1` (Section 5.1, PDF p. 27 /
  printed p. 26).
* **Clamping `R` (`effRedundancy`, Section 5 opening, PDF p. 26 / printed p. 25, formalization
  adaptation)**:
  The paper caps `R` at `N / 2 ^ (log* N)` since update time `O(log* N + log(N / R))` already
  reaches `O(log* N)` there. Here `effRedundancy n R := min R (max 1 (n / max 256 (2 ^ logStar n)))`
  clamps `R` so `redundancyRatio n R = n / effRedundancy n R` satisfies both `256 ≤ r` and
  `2 ^ logStar n ≤ r` across **all** `R ≤ n` (including `R = n`) without inflating `thresholdN`,
  while preserving `effRedundancy n R ≤ R` and `log₂ r = O(logStar n + log(n / R))`.
* **Tree depth, branching factors, and ID-quotient schedule (Section 5 `Tree Parameters` &
  Section 5.1, PDF p. 27 / printed p. 26)**:
  - `treeDepth U r` (`k ≥ 2` in the paper) is the least `ℓ ≥ 2` with `Nat.iterLog ℓ U ≤ 4 * r`
    (adapting the paper's `iterLog k U ≤ r < iterLog (k - 1) U` by a factor of `4` so the bottom
    branching factor `B_{k - 1}` is always at least `2 ^ 17` rather than `1` when
    `iterLog (k - 1) U` lies just above `r`, while keeping `I_{k - 1} = O(r)` and leaf
    waiting-list bits `O(n / r ^ 2)`).
  - Power-of-two node counts `numNodes ℓ = 2 ^ cumBranchBits ℓ` (`B_ℓ = 2 ^ branchBits ℓ`) place
    `nFloor ℓ = n / numNodes ℓ ∈ [targetSize ℓ, 2 * targetSize ℓ)` where
    `targetSize ℓ = (Nat.iterLog ℓ U) ^ 9` (`1 ≤ ℓ < k`) and `targetSize k = r ^ 9`.
  - Window radius `delta ℓ = ⌊(nFloor ℓ) ^ (2 / 3)⌋` (`Nat.nthRoot 3 ((nFloor ℓ) ^ 2)`), thresholds
    `nLow ℓ = nFloor ℓ - delta ℓ` and `nHigh ℓ = nFloor ℓ + delta ℓ` (`n - 1` and `n` at `ℓ = 0`),
    ID bit-widths `idBits ℓ = 4 * Nat.clog 2 (2 * nFloor ℓ)`, and quotient ranges `quotUniv ℓ`
    satisfy the exact conservation identity `numNodes ℓ * 2 ^ idBits ℓ * quotUniv ℓ = paddedUniv`
    at every level `1 ≤ ℓ ≤ k` (`numNodes_mul_two_pow_idBits_mul_quotUniv`).
* **Shared root value pool (Section 5.2 adaptation for arbitrary value bound `V`)**:
  Section 5.2 (PDF pp. 28–29 / printed pp. 27–28) analyzes key-only root tables where `O(Δ_1)`
  unused root slots per root cost `O((N / n_1) * Δ_1 * log U) = O(N / log ^ 2 N)` bits. For general
  values in `Fin V` (with no upper bound on `log₂ V`), storing `⌈log₂ V⌉` bits inside every unused
  root slot would waste `Θ((n / log ^ 3 n) * log₂ V)` bits. Instead, root tables store `(x_quot,
  valPtr)` (`O(log U)` bits) indexing a shared root value pool of exact capacity
  `rootValPoolCap = n - numNodes 2 * nLow 2`, so total value slots across the entire tree equal `n`
  (`n_leaves` in leaf minimaps plus `n - n_leaves` in inner/root value arrays) and total bit usage
  is bounded by `infoBits U V n + O(R)` unconditionally for **all** `1 ≤ V`.

## Scope and explicit out-of-scope gaps

This module covers only the pure parameter schedule and bit-budget accounting for the Section 5
large-parameter polynomial-`U` milestone (`n / log₂ ^ 0.1 n ≤ R ≤ n`, `n ^ (1 + α_min) ≤ U ≤
n ^ (1 + α_max)`). Node data structures (`StorageNode.lean`), pure tree operations and expected
rehashing (`TreeModel.lean`), Word-RAM `Memory.Prog` compilation, Section 4 small-parameter adapter
trees (`R < n / log₂ ^ 0.1 n`), strong history independence, dynamic resizing in `|S|`, and
super-polynomial key universes (`U > n ^ (1 + α_max)`) are out of scope here.

## Main definitions

* `Cslib.DataStructure.Dictionary.SubconstantRedundancy.infoBits`: exact information-theoretic
  benchmark `⌈log₂(C(U, n) * V ^ n)⌉`.
* `Cslib.DataStructure.Dictionary.SubconstantRedundancy.effRedundancy`, `redundancyRatio`,
  `treeDepth`, `targetSize`, `cumBranchBits`, `branchBits`, `branchFactor`, `numNodes`, `nFloor`,
  `delta`, `nLow`, `nHigh`, `idBits`, `quotUnivOne`: integer-exact tree parameter schedule helpers.
* `Cslib.DataStructure.Dictionary.SubconstantRedundancy.TreeSchedule`,
  `TreeSchedule.ConcentrationReady`: reusable abstract tree parameter bundle and concentration
  hypotheses.

## Main results

* `minRedundancyRatio_le_redundancyRatio`, `two_pow_logStar_le_redundancyRatio`,
  `iterLog_treeDepth_le`, `lt_iterLog_of_lt_treeDepth`: clamped redundancy and tree-depth bounds.
* `TreeSchedule.numNodes_mul_idUniv_mul_quotUniv`: exact `paddedUniv` factorization across all tree
  levels.
* `TreeSchedule.leaf_add_inner_slots_eq`, `TreeSchedule.total_value_slots_eq_cap`: telescoping
  value-slot conservation across leaves, inner storage tables, and the shared root value pool.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
* [M. Pătrașcu, *Succincter*][Patrascu2008]
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation, and High
  Independence*][Thorup2013]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure.Dictionary
open Finset

/-! ## Section 1: Information benchmark, clamped redundancy, and integer schedule -/

/-- Exact integer ceiling `⌈log₂(C(U, n) * V ^ n)⌉` of the information-theoretic dictionary bit
lower bound, avoiding per-key ceiling loss when `V` is not a power of two. -/
@[expose]
def infoBits (U V n : ℕ) : ℕ :=
  Nat.clog 2 (U.choose n * V ^ n)

/-- Minimum clamped redundancy ratio `r₀ = 256` (`2 ^ 8`), chosen so leaf target sizes `r ^ 9`
dominate `(150 * m) ^ 3` in the child-router moment concentration inequality across all `R ≤ n`. -/
@[expose]
def minRedundancyRatio : ℕ :=
  256

/-- Clamped internal redundancy `R_eff = min R (max 1 (n / max 256 (2 ^ log* n)))`, ensuring
`R_eff ≤ R`, `256 ≤ n / R_eff`, and `2 ^ log* n ≤ n / R_eff` ([LiLiangYuZhou2024, Section 5],
PDF p. 26 / printed p. 25). -/
@[expose]
def effRedundancy (n R : ℕ) : ℕ :=
  min R (max 1 (n / max minRedundancyRatio (2 ^ Nat.logStar n)))

/-- Internal per-key inverse-redundancy scale `r = n / max (effRedundancy n R) 1`. -/
@[expose]
def redundancyRatio (n R : ℕ) : ℕ :=
  n / max (effRedundancy n R) 1

/-- Bounded fuel helper scanning levels `ℓ = cur, cur + 1, …` for the first `ℓ` with
`Nat.iterLog ℓ U ≤ 4 * r`. -/
def treeDepthAux (U r cur : ℕ) : ℕ → ℕ
  | 0 => cur
  | fuel + 1 =>
    if Nat.iterLog cur U ≤ 4 * r then cur
    else treeDepthAux U r (cur + 1) fuel

/-- Tree depth `k ≥ 2`: the least `ℓ ≥ 2` (within `Nat.floorLogStar U + 2`) such that
`Nat.iterLog ℓ U ≤ 4 * r`. -/
def treeDepth (U r : ℕ) : ℕ :=
  treeDepthAux U r 2 (Nat.floorLogStar U)

/-- Target expected node size lower bound at level `ℓ`: `n` at `ℓ = 0`, `(Nat.iterLog ℓ U) ^ 9` at
internal levels `1 ≤ ℓ < k`, and `r ^ 9` at leaf level `ℓ ≥ k`. -/
@[expose]
def targetSize (n U r k ℓ : ℕ) : ℕ :=
  if ℓ = 0 then n
  else if ℓ < k then (Nat.iterLog ℓ U) ^ 9
  else r ^ 9

/-- Cumulative base-2 branching exponent `S_ℓ` (`numNodes ℓ = 2 ^ S_ℓ`): `0` at `ℓ = 0` and
`⌊log₂(n / targetSize n U r k ℓ)⌋` for `1 ≤ ℓ`. -/
@[expose]
def cumBranchBits (n U r k ℓ : ℕ) : ℕ :=
  if ℓ = 0 then 0
  else Nat.log 2 (n / max (targetSize n U r k ℓ) 1)

/-- Per-level branching bit-width `s_ℓ = S_{ℓ + 1} - S_ℓ` (`B_ℓ = 2 ^ s_ℓ`). -/
@[expose]
def branchBits (n U r k ℓ : ℕ) : ℕ :=
  cumBranchBits n U r k (ℓ + 1) - cumBranchBits n U r k ℓ

/-- Power-of-two branching factor `B_ℓ = 2 ^ branchBits ℓ`. -/
@[expose]
def branchFactor (n U r k ℓ : ℕ) : ℕ :=
  2 ^ branchBits n U r k ℓ

/-- Total number of level-`ℓ` nodes `N_ℓ = 2 ^ cumBranchBits ℓ` across the forest. -/
@[expose]
def numNodes (n U r k ℓ : ℕ) : ℕ :=
  2 ^ cumBranchBits n U r k ℓ

/-- Integer floor `⌊n / N_ℓ⌋` of the expected key load per level-`ℓ` node. -/
@[expose]
def nFloor (n U r k ℓ : ℕ) : ℕ :=
  n / numNodes n U r k ℓ

/-- Allowed load-deviation radius `Δ_ℓ = ⌊(nFloor ℓ) ^ (2 / 3)⌋` at level `ℓ`. -/
@[expose]
def delta (n U r k ℓ : ℕ) : ℕ :=
  Nat.nthRoot 3 ((nFloor n U r k ℓ) ^ 2)

/-- Lower key-load threshold `n_low_ℓ`: `n - 1` at `ℓ = 0`, and `nFloor ℓ - delta ℓ` for `ℓ ≥ 1`. -/
@[expose]
def nLow (n U r k ℓ : ℕ) : ℕ :=
  if ℓ = 0 then n - 1 else nFloor n U r k ℓ - delta n U r k ℓ

/-- Upper key-load threshold `n_high_ℓ`: `n` at `ℓ = 0`, and `nFloor ℓ + delta ℓ` for `ℓ ≥ 1`. -/
@[expose]
def nHigh (n U r k ℓ : ℕ) : ℕ :=
  if ℓ = 0 then n else nFloor n U r k ℓ + delta n U r k ℓ

/-- Key-ID bit width `I_ℓ = 4 * ⌈log₂(2 * nFloor ℓ)⌉` at level `1 ≤ ℓ ≤ k` (`≥ 4 log₂ n_ℓ + 4`). -/
@[expose]
def idBits (n U r k ℓ : ℕ) : ℕ :=
  4 * Nat.clog 2 (2 * max (nFloor n U r k ℓ) 1)

/-- Level-1 quotient range `Q_1 = ⌈(U + n) / (B_0 * 2 ^ I_1)⌉` covering `U` real keys plus `n`
sentinel keys. -/
@[expose]
def quotUnivOne (n U r k : ℕ) : ℕ :=
  let step := branchFactor n U r k 0 * 2 ^ idBits n U r k 1
  (U + n + step - 1) / step

/-! ## Section 2: Basic properties of `effRedundancy`, `redundancyRatio`, and `treeDepth` -/

theorem effRedundancy_le (n R : ℕ) : effRedundancy n R ≤ R :=
  min_le_left _ _

theorem effRedundancy_pos {R : ℕ} (hR : 1 ≤ R) (n : ℕ) : 1 ≤ effRedundancy n R :=
  le_min hR (le_max_left 1 _)

theorem minRedundancyRatio_le_redundancyRatio {n R : ℕ} (hn : minRedundancyRatio ≤ n) :
    minRedundancyRatio ≤ redundancyRatio n R := by
  dsimp only [redundancyRatio, effRedundancy]
  set M := max minRedundancyRatio (2 ^ Nat.logStar n)
  have hM : minRedundancyRatio ≤ M := le_max_left _ _
  by_cases hnM : M ≤ n
  · have hdiv_pos : 1 ≤ n / M :=
      (Nat.le_div_iff_mul_le (by positivity)).mpr (by linarith [one_mul M])
    have heff_le : max (min R (max 1 (n / M))) 1 ≤ n / minRedundancyRatio := by
      have h1 : n / M ≤ n / minRedundancyRatio := Nat.div_le_div_left hM (by decide)
      have h2 : min R (max 1 (n / M)) ≤ max 1 (n / M) := min_le_right _ _
      omega
    refine (Nat.le_div_iff_mul_le (by positivity)).mpr ?_
    calc minRedundancyRatio * max (min R (max 1 (n / M))) 1
        ≤ minRedundancyRatio * (n / minRedundancyRatio) := Nat.mul_le_mul_left _ heff_le
      _ ≤ n := Nat.mul_div_le n minRedundancyRatio
  · have hdiv0 : n / M = 0 := Nat.div_eq_of_lt (not_le.mp hnM)
    have heff1 : max (min R (max 1 (n / M))) 1 = 1 := by rw [hdiv0]; omega
    rw [heff1, Nat.div_one]
    exact hn

theorem two_pow_logStar_le_redundancyRatio {n R : ℕ} (hn : 2 ^ Nat.logStar n ≤ n) :
    2 ^ Nat.logStar n ≤ redundancyRatio n R := by
  dsimp only [redundancyRatio, effRedundancy]
  set M := max minRedundancyRatio (2 ^ Nat.logStar n)
  have hM : 2 ^ Nat.logStar n ≤ M := le_max_right _ _
  by_cases hnM : M ≤ n
  · have hdiv_pos : 1 ≤ n / M :=
      (Nat.le_div_iff_mul_le (by positivity)).mpr (by linarith [one_mul M])
    have heff_le : max (min R (max 1 (n / M))) 1 ≤ n / 2 ^ Nat.logStar n := by
      have h1 : n / M ≤ n / 2 ^ Nat.logStar n :=
        Nat.div_le_div_left hM (Nat.two_pow_pos _)
      have h2 : min R (max 1 (n / M)) ≤ max 1 (n / M) := min_le_right _ _
      omega
    refine (Nat.le_div_iff_mul_le (by positivity)).mpr ?_
    calc 2 ^ Nat.logStar n * max (min R (max 1 (n / M))) 1
        ≤ 2 ^ Nat.logStar n * (n / 2 ^ Nat.logStar n) := Nat.mul_le_mul_left _ heff_le
      _ ≤ n := Nat.mul_div_le n _
  · have hdiv0 : n / M = 0 := Nat.div_eq_of_lt (not_le.mp hnM)
    have heff1 : max (min R (max 1 (n / M))) 1 = 1 := by rw [hdiv0]; omega
    rw [heff1, Nat.div_one]
    exact hn

private theorem le_treeDepthAux (U r cur fuel : ℕ) : cur ≤ treeDepthAux U r cur fuel := by
  induction fuel generalizing cur with
  | zero => exact le_rfl
  | succ fuel ih =>
    dsimp only [treeDepthAux]
    split_ifs
    · exact le_rfl
    · exact (Nat.le_succ cur).trans (ih (cur + 1))

private theorem treeDepthAux_le (U r cur fuel : ℕ) :
    treeDepthAux U r cur fuel ≤ cur + fuel := by
  induction fuel generalizing cur with
  | zero => simp [treeDepthAux]
  | succ fuel ih =>
    dsimp only [treeDepthAux]
    split_ifs
    · omega
    · have := ih (cur + 1)
      omega

private theorem iterLog_treeDepthAux_le {U r cur fuel : ℕ}
    (hend : Nat.iterLog (cur + fuel) U ≤ max (4 * r) 1) :
    Nat.iterLog (treeDepthAux U r cur fuel) U ≤ max (4 * r) 1 := by
  induction fuel generalizing cur with
  | zero => simpa [treeDepthAux] using hend
  | succ fuel ih =>
    dsimp only [treeDepthAux]
    split_ifs with h
    · exact h.trans (le_max_left _ _)
    · exact ih (by rwa [Nat.add_right_comm, Nat.add_assoc])

private theorem lt_iterLog_of_lt_treeDepthAux {U r cur fuel ℓ : ℕ}
    (hlo : cur ≤ ℓ) (hlt : ℓ < treeDepthAux U r cur fuel) :
    4 * r < Nat.iterLog ℓ U := by
  induction fuel generalizing cur with
  | zero =>
    dsimp only [treeDepthAux] at hlt
    omega
  | succ fuel ih =>
    dsimp only [treeDepthAux] at hlt
    split_ifs at hlt with h
    · omega
    · rcases eq_or_lt_of_le hlo with rfl | hgt
      · exact not_le.mp h
      · exact ih (Nat.succ_le_of_lt hgt) hlt

theorem two_le_treeDepth (U r : ℕ) : 2 ≤ treeDepth U r :=
  le_treeDepthAux U r 2 _

theorem treeDepth_le (U r : ℕ) : treeDepth U r ≤ Nat.floorLogStar U + 2 := by
  have h := treeDepthAux_le U r 2 (Nat.floorLogStar U)
  dsimp only [treeDepth]
  omega

theorem iterLog_treeDepth_le {U r : ℕ} (hr : 1 ≤ r) :
    Nat.iterLog (treeDepth U r) U ≤ 4 * r := by
  have hend : Nat.iterLog (2 + Nat.floorLogStar U) U ≤ 1 :=
    (Nat.iterLog_anti_left U (Nat.le_add_left _ 2)).trans (Nat.iterLog_floorLogStar_le_one U)
  have hmax : max (4 * r) 1 = 4 * r := max_eq_left (by omega)
  exact hmax ▸ iterLog_treeDepthAux_le (hend.trans (le_max_right _ _))

theorem lt_iterLog_of_lt_treeDepth {U r ℓ : ℕ} (h2 : 2 ≤ ℓ) (hlt : ℓ < treeDepth U r) :
    4 * r < Nat.iterLog ℓ U :=
  lt_iterLog_of_lt_treeDepthAux h2 hlt

/-! ## Section 3: Abstract `TreeSchedule` bundle and exact level conservation laws -/

/-- Abstract structural parameter bundle for a Section 5 multi-level dictionary tree.
Both small concrete test schedules and `canonicalSchedule` (under `ValidRegime`) instantiate
`TreeSchedule`, decoupling pure node and tree operations from asymptotic threshold constants. -/
structure TreeSchedule where
  /-- External key universe size `U`. -/
  univ : ℕ
  /-- Value bound `V` (`1 ≤ V`). -/
  valBound : ℕ
  /-- Dictionary capacity `n` (`2 ≤ n`; internal tree holds `n - 1` or `n` active keys). -/
  cap : ℕ
  /-- Tree depth `k ≥ 2` (`0` = top router, `1` = roots, `2 .. k - 1` = inner, `k` = leaves). -/
  depth : ℕ
  /-- Per-level branching bit-widths `s_ℓ` (`0 ≤ ℓ < depth`, `B_ℓ = 2 ^ s_ℓ`). -/
  branchBits : ℕ → ℕ
  /-- Integer floor `nFloor ℓ` of expected load at level `0 ≤ ℓ ≤ depth` (`nFloor 0 = cap`). -/
  nFloor : ℕ → ℕ
  /-- Load-deviation radius `Δ_ℓ` (`1 ≤ ℓ ≤ depth`). -/
  delta : ℕ → ℕ
  /-- Key-ID bit-width `I_ℓ` (`1 ≤ ℓ ≤ depth`). -/
  idBits : ℕ → ℕ
  /-- Level-1 quotient universe `Q_1 ≥ 1`. -/
  quotOne : ℕ
  /-- Inverse space exponent `ε_inv` for `DoubleTabulation` child routers. -/
  epsInv : ℕ
  /-- Gap exponent `α_inv` for `DoubleTabulation` child routers. -/
  alphaInv : ℕ
  val_pos : 1 ≤ valBound
  two_le_cap : 2 ≤ cap
  two_le_depth : 2 ≤ depth
  quotOne_pos : 1 ≤ quotOne
  nFloor_zero : nFloor 0 = cap
  nFloor_pos : ∀ ℓ ≤ depth, 1 ≤ nFloor ℓ
  branchBits_pos : ∀ ℓ < depth, 1 ≤ branchBits ℓ
  delta_lt_nFloor : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ depth → delta ℓ < nFloor ℓ
  nFloor_step_le : ∀ ℓ < depth, 2 ^ branchBits ℓ * nFloor (ℓ + 1) ≤ nFloor ℓ
  inner_cap_le : ∀ ℓ, 2 ≤ ℓ → ℓ < depth →
    2 ^ branchBits ℓ * (nFloor (ℓ + 1) - delta (ℓ + 1)) ≤ nFloor ℓ - delta ℓ
  root_cap_le :
    2 ^ branchBits 1 * (nFloor 2 - delta 2) ≤ nFloor 1 + delta 1
  idBits_step_le : ∀ ℓ, 1 ≤ ℓ → ℓ < depth →
    branchBits ℓ + idBits (ℓ + 1) ≤ idBits ℓ
  nHigh_le_two_pow_idBits : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ depth →
    nFloor ℓ + delta ℓ ≤ 2 ^ idBits ℓ
  univ_le_padded :
    univ + cap ≤ 2 ^ branchBits 0 * 2 ^ idBits 1 * quotOne

namespace TreeSchedule

variable (P : TreeSchedule)

/-- Branching factor `B_ℓ = 2 ^ s_ℓ` at level `ℓ`. -/
@[expose]
def branchFactor (ℓ : ℕ) : ℕ :=
  2 ^ P.branchBits ℓ

/-- Cumulative branching bit-depth `S_ℓ = s_0 + ⋯ + s_{ℓ - 1}`. -/
@[expose]
def cumBranchBits (P : TreeSchedule) : ℕ → ℕ
  | 0 => 0
  | ℓ + 1 => cumBranchBits P ℓ + P.branchBits ℓ

/-- Total number of level-`ℓ` nodes `N_ℓ = 2 ^ S_ℓ` across the forest. -/
@[expose]
def numNodes (ℓ : ℕ) : ℕ :=
  2 ^ P.cumBranchBits ℓ

@[simp]
theorem numNodes_zero : P.numNodes 0 = 1 := rfl

theorem numNodes_succ (ℓ : ℕ) : P.numNodes (ℓ + 1) = P.numNodes ℓ * P.branchFactor ℓ := by
  dsimp only [numNodes, cumBranchBits, branchFactor]
  exact Nat.pow_add 2 (cumBranchBits P ℓ) (P.branchBits ℓ)

theorem numNodes_pos (ℓ : ℕ) : 0 < P.numNodes ℓ :=
  Nat.two_pow_pos _

theorem branchFactor_pos (ℓ : ℕ) : 0 < P.branchFactor ℓ :=
  Nat.two_pow_pos _

/-- Lower load threshold `nLow ℓ` (`cap - 1` at `0`, `nFloor ℓ - delta ℓ` for `ℓ ≥ 1`). -/
@[expose]
def nLow (ℓ : ℕ) : ℕ :=
  if ℓ = 0 then P.cap - 1 else P.nFloor ℓ - P.delta ℓ

/-- Upper load threshold `nHigh ℓ` (`cap` at `0`, `nFloor ℓ + delta ℓ` for `ℓ ≥ 1`). -/
@[expose]
def nHigh (ℓ : ℕ) : ℕ :=
  if ℓ = 0 then P.cap else P.nFloor ℓ + P.delta ℓ

/-- Waiting-list capacity `2 * delta ℓ` at level `ℓ ≥ 2` (`nHigh ℓ - nLow ℓ = 2 * delta ℓ`). -/
@[expose]
def waitCap (ℓ : ℕ) : ℕ :=
  2 * P.delta ℓ

theorem nLow_pos {ℓ : ℕ} (hℓ : ℓ ≤ P.depth) : 1 ≤ P.nLow ℓ := by
  dsimp only [nLow]
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · simp only [↓reduceIte]
    have := P.two_le_cap
    omega
  · rw [ite_eq_right hpos.ne']
    have := P.delta_lt_nFloor ℓ hpos hℓ
    omega

theorem nLow_le_nHigh (ℓ : ℕ) : P.nLow ℓ ≤ P.nHigh ℓ := by
  dsimp only [nLow, nHigh]
  split_ifs <;> omega

theorem nHigh_sub_nLow {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) :
    P.nHigh ℓ - P.nLow ℓ = P.waitCap ℓ := by
  have hd := P.delta_lt_nFloor ℓ h1 hℓ
  have h0 : ℓ ≠ 0 := by omega
  simp only [nHigh, nLow, waitCap, h0, ↓reduceIte]
  omega

/-- Quotient remainder bit-shift `I_ℓ - s_ℓ - I_{ℓ + 1}` on edge `ℓ → ℓ + 1`. -/
@[expose]
def remBits (ℓ : ℕ) : ℕ :=
  P.idBits ℓ - P.branchBits ℓ - P.idBits (ℓ + 1)

/-- Quotient universe `Q_ℓ` at level `ℓ ≥ 1`. -/
@[expose]
def quotUniv (P : TreeSchedule) : ℕ → ℕ
  | 0 => P.quotOne
  | 1 => P.quotOne
  | ℓ + 2 => quotUniv P (ℓ + 1) * 2 ^ P.remBits (ℓ + 1)

/-- Padded top-level key universe `U_pad = B_0 * 2 ^ I_1 * Q_1`. -/
@[expose]
def paddedUniv : ℕ :=
  P.branchFactor 0 * 2 ^ P.idBits 1 * P.quotOne

theorem quotUniv_pos (ℓ : ℕ) : 1 ≤ P.quotUniv ℓ := by
  induction ℓ with
  | zero => exact P.quotOne_pos
  | succ m ih =>
    cases m with
    | zero => exact P.quotOne_pos
    | succ m' =>
      dsimp only [quotUniv]
      exact Nat.mul_pos ih (Nat.two_pow_pos _)

theorem quotUniv_succ_of_pos {ℓ : ℕ} (h1 : 1 ≤ ℓ) :
    P.quotUniv (ℓ + 1) = P.quotUniv ℓ * 2 ^ P.remBits ℓ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h1
  rw [Nat.add_comm 1 d]
  rfl

/-- **Exact ID-quotient universe conservation**: `N_ℓ * 2 ^ I_ℓ * Q_ℓ = U_pad` across all
`1 ≤ ℓ ≤ depth`. -/
theorem numNodes_mul_idUniv_mul_quotUniv {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) :
    P.numNodes ℓ * 2 ^ P.idBits ℓ * P.quotUniv ℓ = P.paddedUniv := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h1
  clear h1
  induction d with
  | zero =>
    simp [numNodes_succ, numNodes_zero, quotUniv, paddedUniv]
  | succ d ih =>
    have hd_lt : 1 + d < P.depth := by omega
    have hstep := P.idBits_step_le (1 + d) (by omega) hd_lt
    have hexp : P.idBits (1 + d + 1) + P.branchBits (1 + d) + P.remBits (1 + d) =
        P.idBits (1 + d) := by
      dsimp only [remBits]; omega
    calc P.numNodes (1 + (d + 1)) * 2 ^ P.idBits (1 + (d + 1)) * P.quotUniv (1 + (d + 1))
        = (P.numNodes (1 + d) * 2 ^ P.branchBits (1 + d)) *
            2 ^ P.idBits (1 + d + 1) *
            (P.quotUniv (1 + d) * 2 ^ P.remBits (1 + d)) := by
          rw [show 1 + (d + 1) = (1 + d) + 1 by omega, numNodes_succ, branchFactor,
            quotUniv_succ_of_pos P (by omega : 1 ≤ 1 + d)]
      _ = P.numNodes (1 + d) *
            (2 ^ P.idBits (1 + d + 1) * 2 ^ P.branchBits (1 + d) * 2 ^ P.remBits (1 + d)) *
            P.quotUniv (1 + d) := by ring
      _ = P.numNodes (1 + d) * 2 ^ P.idBits (1 + d) * P.quotUniv (1 + d) := by
          rw [← Nat.pow_add, ← Nat.pow_add, hexp]
      _ = P.paddedUniv := ih (by omega)

/-- Right-coordinate universe `T_ℓ` of the level-`ℓ` Feistel child router (`2 ^ I_1 * Q_1` at
`ℓ = 0`, `2 ^ (I_ℓ - s_ℓ)` for `1 ≤ ℓ < depth`). -/
@[expose]
def routerRightUniv (ℓ : ℕ) : ℕ :=
  if ℓ = 0 then 2 ^ P.idBits 1 * P.quotOne
  else 2 ^ (P.idBits ℓ - P.branchBits ℓ)

/-- Right-coordinate universe `T'_ℓ` of the level-`ℓ` Feistel ID compressor (`Q_1` at `ℓ = 1`,
`2 ^ (I_{ℓ - 1} - s_{ℓ - 1} - I_ℓ) = 2 ^ remBits (ℓ - 1)` for `2 ≤ ℓ ≤ depth`). -/
@[expose]
def idCompRightUniv (ℓ : ℕ) : ℕ :=
  if ℓ ≤ 1 then P.quotOne else 2 ^ P.remBits (ℓ - 1)

/-- Node storage capacity `m_ℓ` (`nHigh 1 - B_1 * nLow 2` at `ℓ = 1`,
`nLow ℓ - B_ℓ * nLow (ℓ + 1)` for `2 ≤ ℓ < depth`, and `nLow depth` at `ℓ = depth`). -/
@[expose]
def tableCap (ℓ : ℕ) : ℕ :=
  if ℓ = 1 then P.nHigh 1 - P.branchFactor 1 * P.nLow 2
  else if ℓ < P.depth then P.nLow ℓ - P.branchFactor ℓ * P.nLow (ℓ + 1)
  else P.nLow P.depth

/-- Capacity `cap - N_2 * nLow 2` of the shared root value pool. -/
@[expose]
def rootValPoolCap : ℕ :=
  P.cap - P.numNodes 2 * P.nLow 2

theorem numNodes_two_mul_nLow_two_le_cap : P.numNodes 2 * P.nLow 2 ≤ P.cap := by
  calc P.numNodes 2 * P.nLow 2
      = P.branchFactor 0 * (P.branchFactor 1 * P.nLow 2) := by
        simp [numNodes_succ, numNodes_zero, Nat.mul_assoc]
    _ ≤ P.branchFactor 0 * (P.branchFactor 1 * P.nFloor 2) := by
        gcongr; exact Nat.sub_le _ _
    _ ≤ P.branchFactor 0 * P.nFloor 1 :=
        Nat.mul_le_mul_left _ (P.nFloor_step_le 1 (by have := P.two_le_depth; omega))
    _ ≤ P.nFloor 0 := P.nFloor_step_le 0 (by have := P.two_le_depth; omega)
    _ = P.cap := P.nFloor_zero

/-- Telescoping slot identity across inner levels `2 .. depth - 1` and leaf level `depth`:
`N_depth * nLow depth + ∑_{ℓ ∈ Ico 2 depth} N_ℓ * tableCap ℓ = N_2 * nLow 2`. -/
theorem leaf_add_inner_slots_eq :
    P.numNodes P.depth * P.nLow P.depth +
      ∑ ℓ ∈ Finset.Ico 2 P.depth, P.numNodes ℓ * P.tableCap ℓ =
      P.numNodes 2 * P.nLow 2 := by
  have hgen : ∀ m, 2 ≤ m → m ≤ P.depth →
      P.numNodes m * P.nLow m + ∑ ℓ ∈ Finset.Ico 2 m, P.numNodes ℓ * P.tableCap ℓ =
        P.numNodes 2 * P.nLow 2 := by
    intro m hm2 hm_le
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm2
    clear hm2
    induction d with
    | zero => simp
    | succ d ih =>
      have hlt : 2 + d < P.depth := by omega
      have hcap_eq : P.tableCap (2 + d) =
          P.nLow (2 + d) - P.branchFactor (2 + d) * P.nLow (2 + d + 1) := by
        dsimp only [tableCap]
        rw [ite_eq_right (by omega), ite_eq_left hlt]
      have hle_sub : P.branchFactor (2 + d) * P.nLow (2 + d + 1) ≤ P.nLow (2 + d) := by
        dsimp only [nLow, branchFactor]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        exact P.inner_cap_le (2 + d) (by omega) hlt
      have hcomb : P.numNodes (2 + d + 1) * P.nLow (2 + d + 1) +
          P.numNodes (2 + d) * P.tableCap (2 + d) = P.numNodes (2 + d) * P.nLow (2 + d) := by
        rw [hcap_eq, numNodes_succ, Nat.mul_assoc, ← Nat.mul_add]
        congr 1
        omega
      rw [show 2 + (d + 1) = (2 + d) + 1 by omega, Finset.sum_Ico_succ_top (by omega)]
      linarith [ih (by omega), hcomb]
  exact hgen P.depth P.two_le_depth le_rfl

/-- Total value-slot conservation across leaf minimaps, inner tables, and the shared root value
pool: `leafSlots + innerSlots + rootValPoolCap = cap` (`= n`). -/
theorem total_value_slots_eq_cap :
    P.numNodes P.depth * P.nLow P.depth +
      (∑ ℓ ∈ Finset.Ico 2 P.depth, P.numNodes ℓ * P.tableCap ℓ) +
      P.rootValPoolCap = P.cap := by
  rw [P.leaf_add_inner_slots_eq]
  exact Nat.add_sub_of_le P.numNodes_two_mul_nLow_two_le_cap

/-- Probabilistic concentration readiness for `Claim 5.4` and `Lemma 5.3` across all levels of
`P`. -/
structure ConcentrationReady : Prop where
  six_le_nFloor : ∀ ℓ ≤ P.depth, 6 ≤ P.nFloor ℓ
  two_mul_delta_le_nFloor : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.depth → 2 * P.delta ℓ ≤ P.nFloor ℓ
  gap_bound : ∀ ℓ < P.depth,
    2 ^ P.branchBits ℓ * P.routerRightUniv ℓ ≤ (P.routerRightUniv ℓ) ^ max P.alphaInv 1
  conc_bound : ∀ ℓ < P.depth,
    2 ^ P.branchBits ℓ * (150 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ)) ^ 3 ≤ P.nLow ℓ
  window_contained : ∀ ℓ < P.depth, ∀ m b_load : ℕ,
    P.nLow ℓ ≤ m → m ≤ P.nHigh ℓ →
    (m : ℝ) / (2 ^ P.branchBits ℓ : ℝ) -
        ((1 : ℝ) / 5) * ((m : ℝ) / (2 ^ P.branchBits ℓ : ℝ)) ^ ((2 : ℝ) / 3) ≤ (b_load : ℝ) →
    (b_load : ℝ) ≤ (m : ℝ) / (2 ^ P.branchBits ℓ : ℝ) +
        ((1 : ℝ) / 5) * ((m : ℝ) / (2 ^ P.branchBits ℓ : ℝ)) ^ ((2 : ℝ) / 3) →
    P.nLow (ℓ + 1) ≤ b_load ∧ b_load ≤ P.nHigh (ℓ + 1)
  id_collision_bound : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.depth →
    (P.nHigh ℓ) ^ 2 * (P.nFloor ℓ) ^ 2 ≤ 4 * 2 ^ P.idBits ℓ

end TreeSchedule

/-! ## Section 4: Quantitative bounds for the canonical integer schedule -/

/-- Level scale `s_ℓ`: `Nat.iterLog ℓ U` for `ℓ < k`, and `r` for `ℓ ≥ k`. -/
@[expose]
def levelScale (U r k ℓ : ℕ) : ℕ :=
  if ℓ < k then Nat.iterLog ℓ U else r

theorem targetSize_eq_levelScale_pow {n U r k ℓ : ℕ} (h1 : 1 ≤ ℓ) :
    targetSize n U r k ℓ = (levelScale U r k ℓ) ^ 9 := by
  dsimp only [targetSize, levelScale]
  rw [ite_eq_right (by omega)]
  split_ifs <;> rfl

theorem r_le_levelScale {U r ℓ : ℕ} (h1 : 1 ≤ ℓ) (hU : 4 * r ≤ Nat.log 2 U) :
    r ≤ levelScale U r (treeDepth U r) ℓ := by
  dsimp only [levelScale]
  split_ifs with hlt
  · rcases eq_or_lt_of_le h1 with rfl | hgt
    · simpa only [Nat.iterLog_succ, Nat.iterLog_zero] using (by omega : r ≤ Nat.log 2 U)
    · have h4 := lt_iterLog_of_lt_treeDepth (Nat.succ_le_of_lt hgt) hlt
      omega
  · exact le_rfl

/-- Across all `0 ≤ ℓ < treeDepth U r`, consecutive target sizes shrink by at least `2 ^ 18`
(`= 4 ^ 9`). -/
theorem two_pow_eighteen_mul_targetSize_succ_le {n U r ℓ : ℕ}
    (hr : minRedundancyRatio ≤ r)
    (hU : 4 * r ≤ Nat.log 2 U)
    (hn : 2 ^ 18 * (Nat.log 2 U) ^ 9 ≤ n)
    (hlt : ℓ < treeDepth U r) :
    let k := treeDepth U r
    2 ^ 18 * targetSize n U r k (ℓ + 1) ≤ targetSize n U r k ℓ := by
  intro k
  have hk2 : 2 ≤ k := two_le_treeDepth U r
  have hr256 : 256 ≤ r := hr
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · dsimp only [targetSize]
    rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left rfl]
    simpa only [Nat.iterLog_succ, Nat.iterLog_zero] using hn
  · rw [targetSize_eq_levelScale_pow (by omega), targetSize_eq_levelScale_pow hpos]
    have h4pow : (2 : ℕ) ^ 18 = 4 ^ 9 := by decide
    rw [h4pow, ← Nat.mul_pow]
    refine Nat.pow_le_pow_left ?_ 9
    dsimp only [levelScale]
    rw [ite_eq_left hlt]
    by_cases hlt1 : ℓ + 1 < k
    · rw [ite_eq_left hlt1]
      set s := Nat.iterLog (ℓ + 1) U
      have hs_gt : 4 * r < s := lt_iterLog_of_lt_treeDepth (by omega) hlt1
      have hs_ge : 4 ≤ s := by omega
      have hsq : s ^ 2 ≤ 2 ^ s := Nat.sq_le_two_pow hs_ge
      have h4s : 4 * s ≤ 2 ^ s := by nlinarith
      have hX_pos : 0 < Nat.iterLog ℓ U := by
        by_contra h0
        have : s = 0 := by
          dsimp only [s]
          rw [Nat.iterLog_succ, Nat.eq_zero_of_le_zero (not_lt.mp h0)]
          decide
        omega
      have hpow_le : 2 ^ s ≤ Nat.iterLog ℓ U := by
        dsimp only [s]
        rw [Nat.iterLog_succ]
        exact Nat.pow_log_le_self 2 hX_pos.ne'
      exact h4s.trans hpow_le
    · rw [ite_eq_right hlt1]
      have hℓ_eq : ℓ = k - 1 := by omega
      rcases eq_or_lt_of_le hk2 with hk_eq | hk_gt
      · have hℓ1 : ℓ = 1 := by omega
        subst hℓ1
        simpa only [Nat.iterLog_succ, Nat.iterLog_zero] using hU
      · have hgt := lt_iterLog_of_lt_treeDepth (by omega : 2 ≤ ℓ) hlt
        omega

theorem targetSize_le_of_step {n U r k : ℕ}
    (hstep : ∀ j < k, 2 ^ 18 * targetSize n U r k (j + 1) ≤ targetSize n U r k j) :
    ∀ ℓ ≤ k, targetSize n U r k ℓ ≤ n := by
  intro ℓ hℓ
  induction ℓ with
  | zero => simp [targetSize]
  | succ j ih =>
    have hj : j < k := Nat.lt_of_succ_le hℓ
    have h1 := hstep j hj
    have h2 := ih hj.le
    omega

theorem targetSize_pos {n U r k ℓ : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hU : 4 * r ≤ Nat.log 2 U) (hℓ : ℓ ≤ treeDepth U r)
    (hk : k = treeDepth U r) :
    1 ≤ targetSize n U r k ℓ := by
  subst hk
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · simpa only [targetSize, ↓reduceIte] using hn
  · rw [targetSize_eq_levelScale_pow hpos]
    exact Nat.one_le_pow 9 _ (hr.trans (r_le_levelScale hpos hU))

theorem numNodes_mul_targetSize_bounds {n U r k ℓ : ℕ}
    (hpos : 1 ≤ targetSize n U r k ℓ) (hle : targetSize n U r k ℓ ≤ n) :
    numNodes n U r k ℓ * targetSize n U r k ℓ ≤ n ∧
      n < 2 * numNodes n U r k ℓ * targetSize n U r k ℓ := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ_pos
  · dsimp only [numNodes, cumBranchBits, targetSize]
    simp only [↓reduceIte, pow_zero, one_mul]
    omega
  · set T := targetSize n U r k ℓ
    have hmax : max T 1 = T := max_eq_left hpos
    have hS : cumBranchBits n U r k ℓ = Nat.log 2 (n / T) := by
      dsimp only [cumBranchBits]
      rw [ite_eq_right hℓ_pos.ne', hmax]
    set q := n / T
    have hq1 : 1 ≤ q := (Nat.le_div_iff_mul_le hpos).mpr (by linarith [one_mul T])
    have hlo : numNodes n U r k ℓ ≤ q := by
      dsimp only [numNodes]
      rw [hS]
      exact Nat.pow_log_le_self 2 (by omega : q ≠ 0)
    have hhi : q < 2 * numNodes n U r k ℓ := by
      dsimp only [numNodes]
      rw [hS, mul_comm 2, ← pow_succ]
      exact Nat.lt_pow_succ_log_self Nat.one_lt_two q
    refine ⟨(Nat.mul_le_mul_right T hlo).trans (Nat.div_mul_le_self n T), ?_⟩
    have hdiv := Nat.div_add_mod n T
    have hmod := Nat.mod_lt n hpos
    have hq1_le : q + 1 ≤ 2 * numNodes n U r k ℓ := by omega
    calc n = T * q + n % T := hdiv.symm
      _ < T * q + T := Nat.add_lt_add_left hmod _
      _ = (q + 1) * T := by ring
      _ ≤ (2 * numNodes n U r k ℓ) * T := Nat.mul_le_mul_right T hq1_le

theorem targetSize_le_nFloor_and_lt {n U r k ℓ : ℕ}
    (hpos : 1 ≤ targetSize n U r k ℓ) (hle : targetSize n U r k ℓ ≤ n) :
    targetSize n U r k ℓ ≤ nFloor n U r k ℓ ∧
      nFloor n U r k ℓ < 2 * targetSize n U r k ℓ := by
  obtain ⟨hlo, hhi⟩ := numNodes_mul_targetSize_bounds hpos hle
  have hN_pos : 0 < numNodes n U r k ℓ := Nat.two_pow_pos _
  refine ⟨(Nat.le_div_iff_mul_le hN_pos).mpr (by rwa [Nat.mul_comm]), ?_⟩
  refine (Nat.div_lt_iff_lt_mul hN_pos).mpr ?_
  linarith

theorem cumBranchBits_add_seventeen_le {n U r k ℓ : ℕ}
    (hpos_cur : 1 ≤ targetSize n U r k ℓ)
    (hpos_next : 1 ≤ targetSize n U r k (ℓ + 1))
    (hle_cur : targetSize n U r k ℓ ≤ n)
    (hstep : 2 ^ 18 * targetSize n U r k (ℓ + 1) ≤ targetSize n U r k ℓ) :
    cumBranchBits n U r k ℓ + 17 ≤ cumBranchBits n U r k (ℓ + 1) := by
  have hle_next : targetSize n U r k (ℓ + 1) ≤ n := by omega
  obtain ⟨hlo, _⟩ := numNodes_mul_targetSize_bounds hpos_cur hle_cur
  obtain ⟨_, hhi⟩ := numNodes_mul_targetSize_bounds hpos_next hle_next
  set T_next := targetSize n U r k (ℓ + 1)
  have hmul : (2 ^ 17 * numNodes n U r k ℓ) * (2 * T_next) <
      numNodes n U r k (ℓ + 1) * (2 * T_next) := by
    calc (2 ^ 17 * numNodes n U r k ℓ) * (2 * T_next)
        = numNodes n U r k ℓ * (2 ^ 18 * T_next) := by ring
      _ ≤ numNodes n U r k ℓ * targetSize n U r k ℓ := Nat.mul_le_mul_left _ hstep
      _ ≤ n := hlo
      _ < 2 * numNodes n U r k (ℓ + 1) * T_next := hhi
      _ = numNodes n U r k (ℓ + 1) * (2 * T_next) := by ring
  have hlt_N : 2 ^ (cumBranchBits n U r k ℓ + 17) < 2 ^ cumBranchBits n U r k (ℓ + 1) := by
    rw [Nat.pow_add, Nat.mul_comm _ (2 ^ 17)]
    exact Nat.lt_of_mul_lt_mul_right hmul
  have hlt_exp := (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hlt_N
  omega

theorem nFloor_succ_eq_div {n U r k ℓ : ℕ}
    (hle : cumBranchBits n U r k ℓ ≤ cumBranchBits n U r k (ℓ + 1)) :
    nFloor n U r k (ℓ + 1) = nFloor n U r k ℓ / branchFactor n U r k ℓ := by
  dsimp only [nFloor, numNodes, branchFactor, branchBits]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_sub_of_le hle]

theorem two_mul_delta_le_nFloor_of_eight_le {n U r k ℓ : ℕ}
    (h8 : 8 ≤ nFloor n U r k ℓ) :
    2 * delta n U r k ℓ ≤ nFloor n U r k ℓ := by
  set y := nFloor n U r k ℓ
  set d := delta n U r k ℓ
  have hd3 : d ^ 3 ≤ y ^ 2 := Nat.pow_nthRoot_le (.inl (by decide))
  have hcube : (2 * d) ^ 3 ≤ y ^ 3 := by
    calc (2 * d) ^ 3 = 8 * d ^ 3 := by ring
      _ ≤ 8 * y ^ 2 := Nat.mul_le_mul_left 8 hd3
      _ ≤ y * y ^ 2 := Nat.mul_le_mul_right _ h8
      _ = y ^ 3 := (pow_succ' y 2).symm
  exact (Nat.pow_le_pow_iff_left (by decide : 3 ≠ 0)).mp hcube

theorem ten_mul_delta_le_branchFactor_mul_delta_succ {n U r k ℓ : ℕ}
    (hS : cumBranchBits n U r k ℓ + 17 ≤ cumBranchBits n U r k (ℓ + 1))
    (hx8 : 8 ≤ nFloor n U r k (ℓ + 1)) :
    10 * delta n U r k ℓ ≤ branchFactor n U r k ℓ * delta n U r k (ℓ + 1) := by
  set B := branchFactor n U r k ℓ
  set y := nFloor n U r k ℓ
  set x := nFloor n U r k (ℓ + 1)
  set d_cur := delta n U r k ℓ
  set d_next := delta n U r k (ℓ + 1)
  have hB : 2 ^ 17 ≤ B := by
    dsimp only [B, branchFactor, branchBits]
    exact Nat.pow_le_pow_right Nat.two_pos (by omega)
  have hx_eq : x = y / B := nFloor_succ_eq_div (by omega)
  have hy_lt : y < B * (x + 1) := by
    have hB_pos : 0 < B := by positivity
    have hdiv := Nat.div_add_mod y B
    have hmod := Nat.mod_lt y hB_pos
    rw [← hx_eq] at hdiv
    linarith
  have hy_le : y ≤ 2 * B * x := by nlinarith
  have hd_next_pos : 1 ≤ d_next := by
    dsimp only [d_next, delta]
    rw [Nat.le_nthRoot_iff (by decide)]
    nlinarith
  have hx2_le : x ^ 2 ≤ 8 * d_next ^ 3 := by
    have hlt : x ^ 2 < (d_next + 1) ^ 3 := Nat.lt_pow_nthRoot_add_one (by decide) (x ^ 2)
    have hle2 : d_next + 1 ≤ 2 * d_next := by omega
    calc x ^ 2 ≤ (d_next + 1) ^ 3 := hlt.le
      _ ≤ (2 * d_next) ^ 3 := Nat.pow_le_pow_left hle2 3
      _ = 8 * d_next ^ 3 := by ring
  have hd_cur3 : d_cur ^ 3 ≤ y ^ 2 := Nat.pow_nthRoot_le (.inl (by decide))
  have hcube : (10 * d_cur) ^ 3 ≤ (B * d_next) ^ 3 := by
    have hB_num : 32000 ≤ B := by
      have : (2 : ℕ) ^ 17 = 131072 := by decide
      omega
    calc (10 * d_cur) ^ 3 = 1000 * d_cur ^ 3 := by ring
      _ ≤ 1000 * y ^ 2 := Nat.mul_le_mul_left 1000 hd_cur3
      _ ≤ 1000 * (2 * B * x) ^ 2 := Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left hy_le 2)
      _ = 4000 * B ^ 2 * x ^ 2 := by ring
      _ ≤ 4000 * B ^ 2 * (8 * d_next ^ 3) := Nat.mul_le_mul_left _ hx2_le
      _ = 32000 * (B ^ 2 * d_next ^ 3) := by ring
      _ ≤ B * (B ^ 2 * d_next ^ 3) := Nat.mul_le_mul_right _ hB_num
      _ = (B * d_next) ^ 3 := by ring
  exact (Nat.pow_le_pow_iff_left (by decide : 3 ≠ 0)).mp hcube

theorem four_mul_branchBits_add_idBits_succ_le {n U r k ℓ : ℕ}
    (hle : cumBranchBits n U r k ℓ ≤ cumBranchBits n U r k (ℓ + 1))
    (hx1 : 1 ≤ nFloor n U r k (ℓ + 1)) :
    4 * branchBits n U r k ℓ + idBits n U r k (ℓ + 1) ≤ idBits n U r k ℓ := by
  set s := branchBits n U r k ℓ
  set x := nFloor n U r k (ℓ + 1)
  set y := nFloor n U r k ℓ
  have hstep : 2 ^ s * x ≤ y := by
    dsimp only [s, x, y, branchFactor]
    rw [nFloor_succ_eq_div hle]
    exact Nat.mul_div_le _ _
  have hy1 : 1 ≤ y := by
    calc 1 ≤ 1 * 1 := by decide
      _ ≤ 2 ^ s * x := Nat.mul_le_mul (Nat.two_pow_pos s) hx1
      _ ≤ y := hstep
  set a := Nat.clog 2 (2 * max x 1)
  set b := Nat.clog 2 (2 * max y 1)
  have hmx : max x 1 = x := max_eq_left hx1
  have hmy : max y 1 = y := max_eq_left hy1
  have ha1 : 1 ≤ a := by
    dsimp only [a]
    rw [hmx]
    exact (show 1 = Nat.clog 2 2 by decide) ▸ Nat.clog_mono_right 2 (by omega)
  have hpow_lt : 2 ^ (a - 1) < 2 * x := by
    by_contra hge
    have hcl := Nat.clog_le_of_le_pow (hmx.symm ▸ not_lt.mp hge)
    omega
  have hlt_pow : 2 ^ (s + (a - 1)) < 2 ^ b := by
    calc 2 ^ (s + (a - 1)) = 2 ^ s * 2 ^ (a - 1) := Nat.pow_add 2 s (a - 1)
      _ < 2 ^ s * (2 * x) := Nat.mul_lt_mul_of_pos_left hpow_lt (Nat.two_pow_pos s)
      _ = 2 * (2 ^ s * x) := by ring
      _ ≤ 2 * y := Nat.mul_le_mul_left 2 hstep
      _ = 2 * max y 1 := by rw [hmy]
      _ ≤ 2 ^ b := Nat.le_pow_clog Nat.one_lt_two _
  have hlt_exp := (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hlt_pow
  change 4 * s + 4 * a ≤ 4 * b
  omega

theorem nHigh_sq_mul_nFloor_sq_le_four_mul_two_pow_idBits {n U r k ℓ : ℕ}
    (h1 : 1 ≤ ℓ) (h8 : 8 ≤ nFloor n U r k ℓ) :
    (nHigh n U r k ℓ) ^ 2 * (nFloor n U r k ℓ) ^ 2 ≤ 4 * 2 ^ idBits n U r k ℓ := by
  set y := nFloor n U r k ℓ
  have hd : 2 * delta n U r k ℓ ≤ y := two_mul_delta_le_nFloor_of_eight_le h8
  have hnh : nHigh n U r k ℓ ≤ 2 * y := by
    dsimp only [nHigh]
    rw [ite_eq_right (by omega)]
    omega
  have hmy : max y 1 = y := max_eq_left (by omega)
  have h2y_pow : 2 * y ≤ 2 ^ Nat.clog 2 (2 * max y 1) := by
    rw [hmy]
    exact Nat.le_pow_clog Nat.one_lt_two (2 * y)
  calc (nHigh n U r k ℓ) ^ 2 * y ^ 2
      ≤ (2 * y) ^ 2 * y ^ 2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hnh 2)
    _ ≤ (2 * y) ^ 4 := by nlinarith [sq_nonneg y]
    _ ≤ (2 ^ Nat.clog 2 (2 * max y 1)) ^ 4 := Nat.pow_le_pow_left h2y_pow 4
    _ = 2 ^ idBits n U r k ℓ := by
        dsimp only [idBits]
        rw [← Nat.pow_mul, Nat.mul_comm 4]
    _ ≤ 4 * 2 ^ idBits n U r k ℓ := by omega

theorem numNodes_mul_delta_mul_levelScale_cubed_le {n U r k ℓ : ℕ}
    (h1 : 1 ≤ ℓ)
    (hpos : 1 ≤ targetSize n U r k ℓ)
    (hle : targetSize n U r k ℓ ≤ n) :
    numNodes n U r k ℓ * delta n U r k ℓ * (levelScale U r k ℓ) ^ 3 ≤ n := by
  set N := numNodes n U r k ℓ
  set d := delta n U r k ℓ
  set s := levelScale U r k ℓ
  obtain ⟨hNT, _⟩ := numNodes_mul_targetSize_bounds hpos hle
  rw [targetSize_eq_levelScale_pow h1] at hNT
  have hNy : N * nFloor n U r k ℓ ≤ n := Nat.mul_div_le n N
  have hd3 : d ^ 3 ≤ (nFloor n U r k ℓ) ^ 2 := Nat.pow_nthRoot_le (.inl (by decide))
  have hcube : (N * d * s ^ 3) ^ 3 ≤ n ^ 3 := by
    calc (N * d * s ^ 3) ^ 3
        = N ^ 3 * d ^ 3 * s ^ 9 := by ring
      _ ≤ N ^ 3 * (nFloor n U r k ℓ) ^ 2 * s ^ 9 := by gcongr
      _ = (N * nFloor n U r k ℓ) ^ 2 * (N * s ^ 9) := by ring
      _ ≤ n ^ 2 * n := Nat.mul_le_mul (Nat.pow_le_pow_left hNy 2) hNT
      _ = n ^ 3 := (pow_succ n 2).symm
  exact (Nat.pow_le_pow_iff_left (by decide : 3 ≠ 0)).mp hcube

theorem idBits_pred_le_mul_levelScale {n U r ℓ : ℕ}
    (hr : minRedundancyRatio ≤ r)
    (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ treeDepth U r)
    (hpos_pred : 1 ≤ targetSize n U r (treeDepth U r) (ℓ - 1))
    (hle_pred : targetSize n U r (treeDepth U r) (ℓ - 1) ≤ n) :
    let k := treeDepth U r
    idBits n U r k (ℓ - 1) ≤ 148 * levelScale U r k ℓ := by
  intro k
  have hr256 : 256 ≤ r := hr
  obtain ⟨hlo, hhi⟩ := targetSize_le_nFloor_and_lt hpos_pred hle_pred
  have hpred1 : 1 ≤ ℓ - 1 := by omega
  have hpred_lt : ℓ - 1 < k := by omega
  have hT_eq : targetSize n U r k (ℓ - 1) = (Nat.iterLog (ℓ - 1) U) ^ 9 := by
    rw [targetSize_eq_levelScale_pow hpred1]
    dsimp only [levelScale]
    rw [ite_eq_left hpred_lt]
  set X := Nat.iterLog (ℓ - 1) U
  set s := levelScale U r k ℓ
  have hs_ge : 256 ≤ s := by
    dsimp only [s, levelScale]
    split_ifs with hlt
    · have := lt_iterLog_of_lt_treeDepth h2 hlt
      omega
    · exact hr256
  have hlogX_le : Nat.log 2 X ≤ 4 * s := by
    dsimp only [s, levelScale]
    split_ifs with hlt
    · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h2
      have heq : Nat.iterLog ℓ U = Nat.log 2 X := by
        dsimp only [X]
        rw [hm, show 2 + m - 1 = 1 + m by omega, show 2 + m = (1 + m) + 1 by omega,
          Nat.iterLog_succ]
      omega
    · have hℓ_eq : ℓ = k := by omega
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h2
      have heq : Nat.iterLog k U = Nat.log 2 X := by
        dsimp only [X]
        rw [← hℓ_eq, hm, show 2 + m - 1 = 1 + m by omega, show 2 + m = (1 + m) + 1 by omega,
          Nat.iterLog_succ]
      rw [← heq]
      exact iterLog_treeDepth_le (by omega)
  have hX_lt : X < 2 ^ (4 * s + 1) :=
    (Nat.lt_pow_succ_log_self Nat.one_lt_two X).trans_le
      (Nat.pow_le_pow_right Nat.two_pos (by omega))
  have hy_pos : 1 ≤ nFloor n U r k (ℓ - 1) := hpos_pred.trans hlo
  have h2y_le : 2 * max (nFloor n U r k (ℓ - 1)) 1 ≤ 2 ^ (36 * s + 11) := by
    rw [max_eq_left hy_pos]
    have h1 : 2 * nFloor n U r k (ℓ - 1) ≤ 4 * X ^ 9 := by
      dsimp only [k] at hT_eq ⊢
      rw [hT_eq] at hhi
      omega
    calc 2 * nFloor n U r k (ℓ - 1)
        ≤ 4 * X ^ 9 := h1
      _ ≤ 4 * (2 ^ (4 * s + 1)) ^ 9 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hX_lt.le 9)
      _ = 2 ^ (36 * s + 11) := by
          have h4 : (4 : ℕ) = 2 ^ 2 := by decide
          rw [h4, ← Nat.pow_mul, ← Nat.pow_add]
          congr 1; ring
  have hcl : Nat.clog 2 (2 * max (nFloor n U r k (ℓ - 1)) 1) ≤ 36 * s + 11 :=
    Nat.clog_le_of_le_pow h2y_le
  dsimp only [idBits]
  omega

end Cslib.DataStructure.Dictionary.SubconstantRedundancy

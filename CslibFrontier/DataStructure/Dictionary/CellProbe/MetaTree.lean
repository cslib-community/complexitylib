/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.CellProbe.Defs
public import CslibFrontier.Foundations.Data.Nat.IterLog
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Zify

/-!
# Divisibility-Free Meta-Operation Tree, LCA Probe Attribution, and Mixed-State Replay

This module formalizes the hierarchical meta-operation tree, lowest-common-ancestor (LCA) probe
accounting, bad-cell intersection inequality, and mixed-memory interval replay used in the dynamic
succinct dictionary cell-probe lower bounds of Li, Liang, Yu, and Zhou ([LiLiangYuZhou2023];
locators below follow `arXiv:2306.02253v3`, where printed page `p` is PDF page `p + 1`).

1. **Divisibility-free bottom-up `MetaTree` and forest-top height adaptation:**
   In [LiLiangYuZhou2023], Section 3 (p. 11 / PDF p. 12), the authors assume `m_{ℓ-1} ∣ m_ℓ` for
   simplicity and terminate at a single root with `m_h = n` covering all `n` meta-operations (and in
   Section 6, p. 25 / PDF p. 26, Footnote 6, assume all parameters are integers for simplicity). Our
   local formalization adaptation `MetaTree` specifies positive even integer fanouts `fanout ℓ`
   (`λ_ℓ`) from the leaves up, setting `blockSize 0 = 1` and
   `blockSize (ℓ + 1) = blockSize ℓ * fanout (ℓ + 1)` (`m_ℓ`), so `blockSize ℓ ∣ blockSize (ℓ + 1)`
   holds definitionally and `2 ∣ blockSize ℓ` holds for every `ℓ ≥ 1`. Because exact bottom-up
   products need not equal `horizon`, `MetaTree.ofFanout` chooses `height` as the largest level with
   `blockSize height ≤ horizon / 2` (so there is no single root covering all `horizon`
   meta-operations as in `m_h = n`, and each `blockSize ℓ` for `ℓ ≤ height` also fits Lemma 5.1's
   `m < n / 2` regime up to equality). At each level `ℓ`, `nodeCount ℓ := horizon / blockSize ℓ`
   disjoint full intervals `[b * blockSize ℓ, (b + 1) * blockSize ℓ)` are packed into
   `[0, horizon)`, retaining at least half of `[0, horizon)` (`horizon ≤ 2 * (nodeCount ℓ *
   blockSize ℓ)`) whenever `blockSize ℓ ≤ horizon` (any `< blockSize ℓ` trailing meta-operations
   are simply omitted from that level's full-block sum).
2. **Iterated-log and geometric schedules (`iterLogMetaTree` and `geomMetaTree`):**
   * `iterLogMetaTree n k c` ([LiLiangYuZhou2023], Section 3, p. 11 / PDF p. 12, for Theorems 1.1
     and 1.3(1)): uses `Nat.iterLog` with even `m_1` and
     `λ_ℓ = 2 * max (2 ^ 63) (Nat.iterLog (ℓ - 1) n / (2 * Nat.iterLog ℓ n))` for `ℓ ≥ 2`,
     preserving `blockSize ℓ * Nat.iterLog ℓ n = Θ(c * n * Nat.iterLog k n)` across levels with
     `71 ≤ Nat.iterLog ℓ n` without exponential rounding loss and achieving `height ≥ k - O_c(1)`.
   * `geomMetaTree n m₁_half` ([LiLiangYuZhou2023], Section 6, pp. 25–26 / PDF pp. 26–27, for
     Theorems 1.2 and 1.3(2)): uses constant even fanout `λ = 2 ^ 64` above
     `m_1 = 2 * max 1 m₁_half` with `n < 4 * max 1 m₁_half * (2 ^ 64) ^ height`.
3. **LCA probe accounting, Eq. (5) bad-cell bound, and memory qualification:**
   Over any step-indexed `D_det : IndexedScheme Op Result cells w` where meta-operation `t` runs
   `stride` elementary steps starting at `initLen + stride * t`:
   * `nodeCost` (`cost_u`, [LiLiangYuZhou2023], Section 3, p. 11 / PDF p. 12) assigns `s - 1`
     units to internal node `(ℓ + 1, b)` for each cell probed in `s` distinct child segments,
     telescoping across all levels to `≤ D_det.seqProbes ops` (`sum_nodeCost_le_seqProbes`).
   * `badCells` (`S_bad`, [LiLiangYuZhou2023], Section 4.2, p. 14 / PDF p. 15) collects cells
     probed in at least two distinct child segments, satisfying Eq. (5)
     ([LiLiangYuZhou2023], Section 4.3, Claim 4.1, p. 17 / PDF p. 18:
     `∑ i, (segProbedCells ... i ∩ badCells ...).card ≤ 2 * nodeCost ...`), post-memory
     qualification soundness (`mem_badCells_of_seg_postMem_ne_node_postMem`, Section 4.2, pp. 14–15
     / PDF pp. 15–16 and Section 4.3, Claim 4.2, p. 17 / PDF p. 18), and its local symmetric
     pre-memory counterpart (`mem_badCells_of_seg_preMem_ne_node_preMem`).
   * `mixMem` wraps `IndexedScheme.runInterval_eq_of_eq_on_probedCellsInterval` for mixed-state
     segment replay `C_mix` ([LiLiangYuZhou2023], Section 5.1, p. 22 / PDF p. 23 and Section 8,
     p. 29 / PDF p. 30).

## Main definitions

* `Cslib.DataStructure.Dictionary.CellProbe.MetaTree`,
  `Cslib.DataStructure.Dictionary.CellProbe.MetaTree.blockSize`,
  `Cslib.DataStructure.Dictionary.CellProbe.MetaTree.nodeCount`,
  `Cslib.DataStructure.Dictionary.CellProbe.MetaTree.ofFanout`: divisibility-free meta-operation
  tree.
* `Cslib.DataStructure.Dictionary.CellProbe.iterLogMetaTree`,
  `Cslib.DataStructure.Dictionary.CellProbe.geomMetaTree`: iterated-logarithm and geometric tree
  schedules.
* `Cslib.DataStructure.Dictionary.CellProbe.memAt`,
  `Cslib.DataStructure.Dictionary.CellProbe.metaProbedCells`,
  `Cslib.DataStructure.Dictionary.CellProbe.MetaTree.nodeProbes`,
  `Cslib.DataStructure.Dictionary.CellProbe.MetaTree.segProbedCells`,
  `Cslib.DataStructure.Dictionary.CellProbe.MetaTree.badCells`,
  `Cslib.DataStructure.Dictionary.CellProbe.MetaTree.nodeCost`: step-indexed execution snapshots,
  probed-cell sets, bad cells, and LCA probe cost.
* `Cslib.DataStructure.Dictionary.CellProbe.mixMem`: mixed memory `C_mix` for segment replay.

## Main results

* `Cslib.DataStructure.Dictionary.CellProbe.MetaTree.blockSize_dvd_of_le`,
  `Cslib.DataStructure.Dictionary.CellProbe.MetaTree.even_blockSize`,
  `Cslib.DataStructure.Dictionary.CellProbe.MetaTree.horizon_le_two_mul_nodeCount_mul_blockSize`:
  divisibility, evenness, and packing bounds.
* `Cslib.DataStructure.Dictionary.CellProbe.blockSize_mul_iterLog_le_iterLogMetaTree`,
  `Cslib.DataStructure.Dictionary.CellProbe.blockSize_one_mul_iterLog_le_two_mul_iterLogMetaTree`,
  `Cslib.DataStructure.Dictionary.CellProbe.le_height_iterLogMetaTree_add`,
  `Cslib.DataStructure.Dictionary.CellProbe.lt_mul_pow_height_geomMetaTree`: ratio and height
  bounds for `iterLogMetaTree` and `geomMetaTree`.
* `MetaTree.sum_nodeCost_le_seqProbes`, `MetaTree.sum_nodeProbes_le_seqProbes`,
  `MetaTree.sum_card_segProbedCells_inter_badCells_le_two_mul_nodeCost`,
  `MetaTree.mem_badCells_of_seg_preMem_ne_node_preMem`, and
  `MetaTree.mem_badCells_of_seg_postMem_ne_node_postMem`:
  global probe conservation, Eq. (5) bad-cell intersection bound, and pre- and post-memory
  qualification.
* `Cslib.DataStructure.Dictionary.CellProbe.runInterval_mixMem_eq_of_probedCellsInterval_subset`,
  `Cslib.DataStructure.Dictionary.CellProbe.mixMem_eq_postMem_of_notMem_inter`:
  mixed-memory replay equivalence and non-intersection cell recovery.

## References

* [T. Li, J. Liang, H. Yu and R. Zhou, *Tight Cell-Probe Lower Bounds for Dynamic Succinct
  Dictionaries*][LiLiangYuZhou2023], Sections 3, 4.2, 4.3, 5.1, 6, and 8 (`arXiv:2306.02253v3`).
* [P. B. Miltersen, *Cell Probe Complexity — a Survey*][Miltersen1999]
* [A. C.-C. Yao, *Probabilistic Computations: Toward a Unified Measure of Complexity*][Yao1977]
-/

public section

namespace Cslib.DataStructure.Dictionary.CellProbe

open Cslib.CellProbe

/-! ### Divisibility-free bottom-up meta-operation tree -/

/-- Divisibility-free bottom-up meta-operation tree over `horizon` meta-operations
([LiLiangYuZhou2023], Section 3, p. 11 / PDF p. 12 and Section 6, p. 25 / PDF p. 26). -/
structure MetaTree where
  /-- Total number of meta-operations `[0, horizon)`. -/
  horizon : ℕ
  /-- Active internal tree height (levels `1, …, height`). -/
  height : ℕ
  /-- Child fanout `λ_ℓ` at level `ℓ` (`ℓ ≥ 1`; `fanout 0` is unused). -/
  fanout : ℕ → ℕ
  /-- Every internal level `ℓ ≥ 1` has positive fanout. -/
  fanout_pos : ∀ ℓ, 1 ≤ ℓ → 0 < fanout ℓ
  /-- Every internal level `ℓ ≥ 1` has even fanout (`2 ∣ fanout ℓ`). -/
  even_fanout : ∀ ℓ, 1 ≤ ℓ → 2 ∣ fanout ℓ

/-- Bottom-up block size `m_ℓ` from `fanout`: `m_0 = 1` and `m_{ℓ+1} = m_ℓ * fanout (ℓ+1)`. -/
private def rawBlockSize (fanout : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | ℓ + 1 => rawBlockSize fanout ℓ * fanout (ℓ + 1)

namespace MetaTree

/-- Number of consecutive meta-operations `m_ℓ` represented by each level-`ℓ` node. -/
def blockSize (T : MetaTree) (ℓ : ℕ) : ℕ :=
  rawBlockSize T.fanout ℓ

/-- Number of disjoint full level-`ℓ` nodes `q_ℓ = horizon / blockSize ℓ` packed into
`[0, horizon)`. -/
@[expose] def nodeCount (T : MetaTree) (ℓ : ℕ) : ℕ :=
  T.horizon / T.blockSize ℓ

/-- Starting meta-operation index `b * blockSize ℓ` of node `(ℓ, b)`. -/
@[expose] def nodeStart (T : MetaTree) (ℓ b : ℕ) : ℕ :=
  b * T.blockSize ℓ

/-- Exclusive ending meta-operation index `(b + 1) * blockSize ℓ` of node `(ℓ, b)`. -/
@[expose] def nodeStop (T : MetaTree) (ℓ b : ℕ) : ℕ :=
  (b + 1) * T.blockSize ℓ

@[simp]
theorem blockSize_zero (T : MetaTree) : T.blockSize 0 = 1 := by rfl

@[simp]
theorem blockSize_succ (T : MetaTree) (ℓ : ℕ) :
    T.blockSize (ℓ + 1) = T.blockSize ℓ * T.fanout (ℓ + 1) := by rfl

theorem two_le_fanout (T : MetaTree) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 2 ≤ T.fanout ℓ := by
  have hpos := T.fanout_pos ℓ hℓ
  obtain ⟨k, hk⟩ := T.even_fanout ℓ hℓ
  omega

theorem blockSize_pos (T : MetaTree) (ℓ : ℕ) : 0 < T.blockSize ℓ := by
  induction ℓ with
  | zero => exact Nat.zero_lt_one
  | succ ℓ ih => exact Nat.mul_pos ih (T.fanout_pos (ℓ + 1) (Nat.le_add_left 1 ℓ))

theorem blockSize_dvd_succ (T : MetaTree) (ℓ : ℕ) : T.blockSize ℓ ∣ T.blockSize (ℓ + 1) :=
  ⟨T.fanout (ℓ + 1), by rfl⟩

theorem blockSize_dvd_of_le (T : MetaTree) {ℓ₁ ℓ₂ : ℕ} (h : ℓ₁ ≤ ℓ₂) :
    T.blockSize ℓ₁ ∣ T.blockSize ℓ₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => exact dvd_rfl
  | succ d ih => exact dvd_trans ih (T.blockSize_dvd_succ (ℓ₁ + d))

theorem even_blockSize (T : MetaTree) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 2 ∣ T.blockSize ℓ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hℓ
  rw [Nat.add_comm 1 k, blockSize_succ]
  exact dvd_mul_of_dvd_right (T.even_fanout (k + 1) (Nat.le_add_left 1 k)) _

theorem two_pow_le_blockSize (T : MetaTree) (ℓ : ℕ) : 2 ^ ℓ ≤ T.blockSize ℓ := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    rw [Nat.pow_succ, blockSize_succ]
    exact Nat.mul_le_mul ih (T.two_le_fanout (Nat.le_add_left 1 ℓ))

theorem blockSize_strictMono (T : MetaTree) : StrictMono T.blockSize := by
  refine strictMono_nat_of_lt_succ fun ℓ => ?_
  have hpos := T.blockSize_pos ℓ
  have h2 := T.two_le_fanout (Nat.le_add_left 1 ℓ)
  calc
    T.blockSize ℓ = T.blockSize ℓ * 1 := (Nat.mul_one _).symm
    _ < T.blockSize ℓ * T.fanout (ℓ + 1) := Nat.mul_lt_mul_of_pos_left (by omega) hpos

@[simp]
theorem nodeCount_zero (T : MetaTree) : T.nodeCount 0 = T.horizon := by
  simp [nodeCount]

theorem nodeCount_mul_fanout_le (T : MetaTree) (ℓ : ℕ) :
    T.nodeCount (ℓ + 1) * T.fanout (ℓ + 1) ≤ T.nodeCount ℓ := by
  simp only [nodeCount, blockSize_succ]
  rw [← Nat.div_div_eq_div_mul]
  exact Nat.div_mul_le_self (T.horizon / T.blockSize ℓ) (T.fanout (ℓ + 1))

theorem child_lt_nodeCount (T : MetaTree) {ℓ b : ℕ} (hb : b < T.nodeCount (ℓ + 1))
    (i : Fin (T.fanout (ℓ + 1))) :
    b * T.fanout (ℓ + 1) + i.1 < T.nodeCount ℓ := by
  have h1 : (b + 1) * T.fanout (ℓ + 1) ≤ T.nodeCount (ℓ + 1) * T.fanout (ℓ + 1) :=
    Nat.mul_le_mul_right _ hb
  have h2 := T.nodeCount_mul_fanout_le ℓ
  have hi := i.2
  calc
    b * T.fanout (ℓ + 1) + i.1 < b * T.fanout (ℓ + 1) + T.fanout (ℓ + 1) := by omega
    _ = (b + 1) * T.fanout (ℓ + 1) := by ring
    _ ≤ T.nodeCount ℓ := h1.trans h2

theorem nodeStop_le_horizon (T : MetaTree) {ℓ b : ℕ} (hb : b < T.nodeCount ℓ) :
    T.nodeStop ℓ b ≤ T.horizon := by
  simp only [nodeStop]
  exact (Nat.mul_le_mul_right (T.blockSize ℓ) hb).trans (Nat.div_mul_le_self _ _)

theorem nodeStart_child (T : MetaTree) (ℓ b i : ℕ) :
    T.nodeStart ℓ (b * T.fanout (ℓ + 1) + i) = T.nodeStart (ℓ + 1) b + i * T.blockSize ℓ := by
  simp only [nodeStart, blockSize_succ]
  ring

theorem nodeStop_child (T : MetaTree) (ℓ b i : ℕ) :
    T.nodeStop ℓ (b * T.fanout (ℓ + 1) + i) = T.nodeStart (ℓ + 1) b + (i + 1) * T.blockSize ℓ := by
  simp only [nodeStart, nodeStop, blockSize_succ]
  ring

/-- Divisibility-free packing lower bound: whenever `blockSize ℓ ≤ horizon`, full level-`ℓ` nodes
cover at least half of `[0, horizon)` (`horizon ≤ 2 * (nodeCount ℓ * blockSize ℓ)`). -/
theorem horizon_le_two_mul_nodeCount_mul_blockSize (T : MetaTree) {ℓ : ℕ}
    (h : T.blockSize ℓ ≤ T.horizon) :
    T.horizon ≤ 2 * (T.nodeCount ℓ * T.blockSize ℓ) := by
  have hpos := T.blockSize_pos ℓ
  have hdiv_pos : 1 ≤ T.horizon / T.blockSize ℓ := (Nat.le_div_iff_mul_le hpos).mpr (by omega)
  have hrem : T.horizon % T.blockSize ℓ < T.blockSize ℓ := Nat.mod_lt _ hpos
  have hmul_ge : T.blockSize ℓ ≤ (T.horizon / T.blockSize ℓ) * T.blockSize ℓ := by
    simpa using Nat.mul_le_mul_right (T.blockSize ℓ) hdiv_pos
  have hmod := Nat.div_add_mod T.horizon (T.blockSize ℓ)
  rw [mul_comm] at hmod
  simp only [nodeCount]
  omega

theorem horizon_div_two_mul_blockSize_le_nodeCount (T : MetaTree) {ℓ : ℕ}
    (h : T.blockSize ℓ ≤ T.horizon) :
    T.horizon / (2 * T.blockSize ℓ) ≤ T.nodeCount ℓ := by
  have hpos : 0 < 2 * T.blockSize ℓ := Nat.mul_pos Nat.two_pos (T.blockSize_pos ℓ)
  have hle : T.horizon ≤ T.nodeCount ℓ * (2 * T.blockSize ℓ) := by
    have h2 := T.horizon_le_two_mul_nodeCount_mul_blockSize h
    linarith
  calc
    T.horizon / (2 * T.blockSize ℓ)
      ≤ (T.nodeCount ℓ * (2 * T.blockSize ℓ)) / (2 * T.blockSize ℓ) :=
          Nat.div_le_div_right hle
    _ = T.nodeCount ℓ := Nat.mul_div_cancel _ hpos

end MetaTree

/-! ### Canonical `ofFanout` constructor, `geomMetaTree`, and `iterLogMetaTree` -/

/-- Recursive step counter finding the largest offset `d ≤ fuel` above `ℓ` with
`rawBlockSize fanout (ℓ + d) ≤ bound`. -/
private def countLevels (bound : ℕ) (fanout : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, ℓ =>
      if rawBlockSize fanout (ℓ + 1) ≤ bound then
        1 + countLevels bound fanout fuel (ℓ + 1)
      else
        0

private theorem rawBlockSize_countLevels_le {bound : ℕ} {fanout : ℕ → ℕ} :
    ∀ (fuel ℓ : ℕ), rawBlockSize fanout ℓ ≤ bound →
      rawBlockSize fanout (ℓ + countLevels bound fanout fuel ℓ) ≤ bound
  | 0, _, hle => by simpa [countLevels] using hle
  | fuel + 1, ℓ, _ => by
    simp only [countLevels]
    split_ifs with hnext
    · have h := rawBlockSize_countLevels_le fuel (ℓ + 1) hnext
      have hidx : ℓ + (1 + countLevels bound fanout fuel (ℓ + 1)) =
          ℓ + 1 + countLevels bound fanout fuel (ℓ + 1) := by omega
      rwa [hidx]
    · rwa [Nat.add_zero]

private theorem lt_rawBlockSize_countLevels_succ {bound : ℕ} {fanout : ℕ → ℕ} :
    ∀ (fuel ℓ : ℕ), bound < rawBlockSize fanout (ℓ + fuel + 1) →
      bound < rawBlockSize fanout (ℓ + countLevels bound fanout fuel ℓ + 1)
  | 0, ℓ, hgt => by simpa [countLevels] using hgt
  | fuel + 1, ℓ, hgt => by
    simp only [countLevels]
    split_ifs with hnext
    · have hgt' : bound < rawBlockSize fanout ((ℓ + 1) + fuel + 1) := by
        have hidx : (ℓ + 1) + fuel + 1 = ℓ + (fuel + 1) + 1 := by omega
        rwa [hidx]
      have h := lt_rawBlockSize_countLevels_succ fuel (ℓ + 1) hgt'
      have hidx : ℓ + (1 + countLevels bound fanout fuel (ℓ + 1)) + 1 =
          (ℓ + 1) + countLevels bound fanout fuel (ℓ + 1) + 1 := by omega
      rwa [hidx]
    · simp only [Nat.add_zero]
      omega

namespace MetaTree

/-- Build a `MetaTree` over `horizon` meta-operations from any positive even `fanout`, choosing
`height` as the largest level `h` with `blockSize h ≤ horizon / 2` (or `0` when `horizon < 2`).
Unlike the paper's single-root convention `m_h = n`, stopping at `horizon / 2` avoids assuming that
bottom-up integer products divide `horizon` while ensuring at least two full blocks at level
`height` when `2 ≤ horizon`. -/
def ofFanout (horizon : ℕ) (fanout : ℕ → ℕ)
    (hpos : ∀ ℓ, 1 ≤ ℓ → 0 < fanout ℓ)
    (heven : ∀ ℓ, 1 ≤ ℓ → 2 ∣ fanout ℓ) : MetaTree where
  horizon := horizon
  height := countLevels (horizon / 2) fanout horizon 0
  fanout := fanout
  fanout_pos := hpos
  even_fanout := heven

@[simp]
theorem ofFanout_horizon (horizon : ℕ) (fanout : ℕ → ℕ) (hpos) (heven) :
    (ofFanout horizon fanout hpos heven).horizon = horizon := by rfl

@[simp]
theorem ofFanout_fanout (horizon : ℕ) (fanout : ℕ → ℕ) (hpos) (heven) :
    (ofFanout horizon fanout hpos heven).fanout = fanout := by rfl

theorem lt_blockSize_height_ofFanout_succ (horizon : ℕ) (fanout : ℕ → ℕ) (hpos) (heven) :
    let T := ofFanout horizon fanout hpos heven
    horizon / 2 < T.blockSize (T.height + 1) := by
  set T := ofFanout horizon fanout hpos heven
  have h2pow : horizon / 2 < T.blockSize (0 + horizon + 1) := by
    have hpow := T.two_pow_le_blockSize (horizon + 1)
    have hlt : horizon < 2 ^ (horizon + 1) :=
      (Nat.lt_two_pow_self (n := horizon)).trans
        (Nat.pow_lt_pow_right Nat.one_lt_two (Nat.lt_succ_self horizon))
    rw [Nat.zero_add]
    omega
  simpa only [T, ofFanout, blockSize, Nat.zero_add] using
    lt_rawBlockSize_countLevels_succ horizon 0 h2pow

theorem le_height_ofFanout_iff {horizon : ℕ} (hn : 2 ≤ horizon) (fanout : ℕ → ℕ)
    (hpos) (heven) (ℓ : ℕ) :
    let T := ofFanout horizon fanout hpos heven
    ℓ ≤ T.height ↔ T.blockSize ℓ ≤ horizon / 2 := by
  set T := ofFanout horizon fanout hpos heven
  have hle_height : T.blockSize T.height ≤ horizon / 2 := by
    have h0 : rawBlockSize fanout 0 ≤ horizon / 2 := by
      change 1 ≤ horizon / 2; omega
    simpa only [T, ofFanout, blockSize, Nat.zero_add] using
      rawBlockSize_countLevels_le horizon 0 h0
  have hgt_succ : horizon / 2 < T.blockSize (T.height + 1) :=
    lt_blockSize_height_ofFanout_succ horizon fanout hpos heven
  constructor
  · intro hℓ
    exact (T.blockSize_strictMono.monotone hℓ).trans hle_height
  · intro hle
    by_contra hnot
    have hge : T.height + 1 ≤ ℓ := by omega
    have := T.blockSize_strictMono.monotone hge
    omega

end MetaTree

/-- Fanout schedule for `geomMetaTree`: `fanout 1 = 2 * max 1 m₁_half` and `fanout ℓ = 2 ^ 64` for
`ℓ ≥ 2`. -/
@[expose] def geomFanout (m₁_half : ℕ) : ℕ → ℕ
  | 0 => 2
  | 1 => 2 * max 1 m₁_half
  | _ + 2 => 2 ^ 64

/-- Geometric meta-operation tree ([LiLiangYuZhou2023], Section 6, pp. 25–26 / PDF pp. 26–27, for
Theorems 1.2 and 1.3(2)): `blockSize 1 = 2 * max 1 m₁_half` (even) and constant even fanout
`2 ^ 64` at all levels `ℓ ≥ 2`. -/
def geomMetaTree (n m₁_half : ℕ) : MetaTree :=
  MetaTree.ofFanout n (geomFanout m₁_half)
    (fun ℓ hℓ => by
      match ℓ with
      | 0 => omega
      | 1 => simp [geomFanout]
      | _ + 2 => norm_num [geomFanout])
    (fun ℓ hℓ => by
      match ℓ with
      | 0 => omega
      | 1 => exact ⟨max 1 m₁_half, rfl⟩
      | _ + 2 => exact ⟨2 ^ 63, by norm_num [geomFanout]⟩)

@[simp]
theorem geomMetaTree_horizon (n m₁_half : ℕ) :
    (geomMetaTree n m₁_half).horizon = n := by
  rfl

@[simp]
theorem geomMetaTree_fanout (n m₁_half : ℕ) :
    (geomMetaTree n m₁_half).fanout = geomFanout m₁_half := by
  rfl

theorem le_height_geomMetaTree_iff {n : ℕ} (hn : 2 ≤ n) (m₁_half ℓ : ℕ) :
    ℓ ≤ (geomMetaTree n m₁_half).height ↔
      (geomMetaTree n m₁_half).blockSize ℓ ≤ n / 2 :=
  MetaTree.le_height_ofFanout_iff hn (geomFanout m₁_half)
    (geomMetaTree n m₁_half).fanout_pos (geomMetaTree n m₁_half).even_fanout ℓ

theorem blockSize_le_horizon_of_le_height_geomMetaTree {n m₁_half ℓ : ℕ} (hn : 2 ≤ n)
    (hℓ : ℓ ≤ (geomMetaTree n m₁_half).height) :
    (geomMetaTree n m₁_half).blockSize ℓ ≤ n :=
  ((le_height_geomMetaTree_iff hn m₁_half ℓ).mp hℓ).trans (Nat.div_le_self n 2)

theorem blockSize_geomMetaTree (n m₁_half : ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (geomMetaTree n m₁_half).blockSize ℓ = (2 * max 1 m₁_half) * (2 ^ 64) ^ (ℓ - 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hℓ
  clear hℓ
  rw [Nat.add_comm 1 d]
  induction d with
  | zero =>
    change 1 * geomFanout m₁_half 1 = _
    simp [geomFanout]
  | succ d ih =>
    rw [(geomMetaTree n m₁_half).blockSize_succ (d + 1), ih]
    change (2 * max 1 m₁_half * (2 ^ 64) ^ d) * geomFanout m₁_half (d + 2) =
      (2 * max 1 m₁_half) * (2 ^ 64) ^ (d + 1)
    simp only [geomFanout, Nat.pow_succ]
    ring

/-- Multiplicative height lower bound for `geomMetaTree`:
`n < 4 * max 1 m₁_half * (2 ^ 64) ^ (geomMetaTree n m₁_half).height`. -/
theorem lt_mul_pow_height_geomMetaTree (n m₁_half : ℕ) :
    n < 4 * max 1 m₁_half * (2 ^ 64) ^ (geomMetaTree n m₁_half).height := by
  have hgt := MetaTree.lt_blockSize_height_ofFanout_succ n (geomFanout m₁_half)
    (geomMetaTree n m₁_half).fanout_pos (geomMetaTree n m₁_half).even_fanout
  change n / 2 < (geomMetaTree n m₁_half).blockSize ((geomMetaTree n m₁_half).height + 1) at hgt
  rw [blockSize_geomMetaTree n m₁_half (Nat.le_add_left 1 _), Nat.add_sub_cancel] at hgt
  have h2 : 4 * max 1 m₁_half * (2 ^ 64) ^ (geomMetaTree n m₁_half).height =
      2 * ((2 * max 1 m₁_half) * (2 ^ 64) ^ (geomMetaTree n m₁_half).height) := by ring
  omega

/-- Logarithmic level-count lower bound for `geomMetaTree`. -/
theorem log_div_le_mul_height_geomMetaTree (n m₁_half : ℕ) :
    Nat.log 2 (n / (4 * max 1 m₁_half)) ≤ 64 * (geomMetaTree n m₁_half).height := by
  set M := 4 * max 1 m₁_half
  have hM : 0 < M := by positivity
  have hlt := lt_mul_pow_height_geomMetaTree n m₁_half
  have hdiv_lt : n / M < 2 ^ (64 * (geomMetaTree n m₁_half).height) := by
    rw [Nat.div_lt_iff_lt_mul hM, mul_comm _ M, Nat.pow_mul]
    exact hlt
  rcases Nat.eq_zero_or_pos (n / M) with h0 | hpos
  · simp [h0]
  · have hdiv_lt_succ : n / M < 2 ^ (64 * (geomMetaTree n m₁_half).height + 1) :=
      hdiv_lt.trans (Nat.pow_lt_pow_right Nat.one_lt_two (Nat.lt_succ_self _))
    exact Nat.lt_succ_iff.mp
      ((Nat.log_lt_iff_lt_pow Nat.one_lt_two hpos.ne').mpr hdiv_lt_succ)

/-- Fanout schedule for `iterLogMetaTree`:
`fanout 1 = 2 * max 1 ((c * n * iterLog k n) / (2 * iterLog 1 n))` and
`fanout ℓ = 2 * max (2 ^ 63) (iterLog (ℓ - 1) n / (2 * iterLog ℓ n))` for `ℓ ≥ 2`. -/
@[expose] def iterLogFanout (n k c : ℕ) : ℕ → ℕ
  | 0 => 2
  | 1 => 2 * max 1 ((c * n * Nat.iterLog k n) / (2 * Nat.iterLog 1 n))
  | d + 2 => 2 * max (2 ^ 63) (Nat.iterLog (d + 1) n / (2 * Nat.iterLog (d + 2) n))

/-- Iterated-logarithm meta-operation tree ([LiLiangYuZhou2023], Section 3, p. 11 / PDF p. 12, for
Theorems 1.1 and 1.3(1)). -/
def iterLogMetaTree (n k c : ℕ) : MetaTree :=
  MetaTree.ofFanout n (iterLogFanout n k c)
    (fun ℓ hℓ => by
      match ℓ with
      | 0 => omega
      | 1 => simp [iterLogFanout]
      | d + 2 =>
        have hpos : 0 < max (2 ^ 63) (Nat.iterLog (d + 1) n / (2 * Nat.iterLog (d + 2) n)) :=
          lt_of_lt_of_le (by positivity) (_root_.le_max_left _ _)
        exact Nat.mul_pos Nat.two_pos hpos)
    (fun ℓ hℓ => by
      match ℓ with
      | 0 => omega
      | 1 => exact ⟨_, rfl⟩
      | _ + 2 => exact ⟨_, rfl⟩)

@[simp]
theorem iterLogMetaTree_horizon (n k c : ℕ) :
    (iterLogMetaTree n k c).horizon = n := by
  rfl

@[simp]
theorem iterLogMetaTree_fanout (n k c : ℕ) :
    (iterLogMetaTree n k c).fanout = iterLogFanout n k c := by
  rfl

theorem le_height_iterLogMetaTree_iff {n : ℕ} (hn : 2 ≤ n) (k c ℓ : ℕ) :
    ℓ ≤ (iterLogMetaTree n k c).height ↔
      (iterLogMetaTree n k c).blockSize ℓ ≤ n / 2 :=
  MetaTree.le_height_ofFanout_iff hn (iterLogFanout n k c)
    (iterLogMetaTree n k c).fanout_pos (iterLogMetaTree n k c).even_fanout ℓ

theorem blockSize_le_horizon_of_le_height_iterLogMetaTree {n k c ℓ : ℕ} (hn : 2 ≤ n)
    (hℓ : ℓ ≤ (iterLogMetaTree n k c).height) :
    (iterLogMetaTree n k c).blockSize ℓ ≤ n :=
  ((le_height_iterLogMetaTree_iff hn k c ℓ).mp hℓ).trans (Nat.div_le_self n 2)

theorem two_pow_le_fanout_iterLogMetaTree (n k c : ℕ) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    2 ^ 64 ≤ (iterLogMetaTree n k c).fanout ℓ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hℓ
  rw [Nat.add_comm 2 d]
  change 2 ^ 64 ≤ 2 * max (2 ^ 63) (Nat.iterLog (d + 1) n / (2 * Nat.iterLog (d + 2) n))
  have hle : 2 ^ 63 ≤ max (2 ^ 63) (Nat.iterLog (d + 1) n / (2 * Nat.iterLog (d + 2) n)) :=
    _root_.le_max_left _ _
  omega

private theorem two_pow_sixty_four_mul_le_two_pow {x : ℕ} (hx : 71 ≤ x) :
    2 ^ 64 * x ≤ 2 ^ x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hx
  induction d with
  | zero => decide
  | succ d ih =>
    have hpow : 71 + (d + 1) = (71 + d) + 1 := by omega
    rw [hpow, Nat.pow_succ]
    omega

private theorem eight_mul_add_four_le_two_pow {y : ℕ} (hy : 35 ≤ y) :
    8 * y + 4 ≤ 2 ^ y := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hy
  induction d with
  | zero => decide
  | succ d ih =>
    have hpow : 35 + (d + 1) = (35 + d) + 1 := by omega
    rw [hpow, Nat.pow_succ]
    omega

private theorem four_mul_mul_two_pow_div_two_le_two_pow {x : ℕ} (hx : 71 ≤ x) :
    4 * x * 2 ^ (x / 2) ≤ 2 ^ x := by
  have hy : 35 ≤ x / 2 := by omega
  have h8 := eight_mul_add_four_le_two_pow hy
  have h4x : 4 * x ≤ 2 ^ (x / 2) := by omega
  have hle_sub : x / 2 ≤ x - x / 2 := by omega
  have hpow_le : 2 ^ (x / 2) ≤ 2 ^ (x - x / 2) :=
    Nat.pow_le_pow_right Nat.two_pos hle_sub
  calc
    4 * x * 2 ^ (x / 2) ≤ 2 ^ (x - x / 2) * 2 ^ (x / 2) :=
      Nat.mul_le_mul_right _ (h4x.trans hpow_le)
    _ = 2 ^ x := by
      rw [← Nat.pow_add]
      exact congrArg (2 ^ ·) (by omega)

private theorem two_pow_le_prev_iterLog {n j : ℕ} (hx : 1 ≤ Nat.iterLog (j + 1) n) :
    2 ^ Nat.iterLog (j + 1) n ≤ Nat.iterLog j n := by
  have hprev_ne : Nat.iterLog j n ≠ 0 := by
    intro h0
    have : Nat.iterLog (j + 1) n = 0 := by simp [Nat.iterLog_succ, h0]
    omega
  exact Nat.pow_log_le_self 2 hprev_ne

/-- At any level `ℓ ≥ 2` with `71 ≤ Nat.iterLog ℓ n`, the level-`ℓ` fanout of `iterLogMetaTree`
satisfies `fanout ℓ * iterLog ℓ n ≤ iterLog (ℓ - 1) n`. -/
theorem fanout_mul_iterLog_le_iterLogMetaTree (n k c : ℕ) {ℓ : ℕ}
    (hℓ : 2 ≤ ℓ) (hx : 71 ≤ Nat.iterLog ℓ n) :
    (iterLogMetaTree n k c).fanout ℓ * Nat.iterLog ℓ n ≤ Nat.iterLog (ℓ - 1) n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hℓ
  clear hℓ
  rw [Nat.add_comm 2 d] at hx ⊢
  have hx1 : 1 ≤ Nat.iterLog ((d + 1) + 1) n := by
    simpa only [Nat.add_assoc] using (show 1 ≤ Nat.iterLog (d + 2) n by omega)
  have hpow : 2 ^ 64 * Nat.iterLog (d + 2) n ≤ Nat.iterLog (d + 1) n :=
    (two_pow_sixty_four_mul_le_two_pow hx).trans (two_pow_le_prev_iterLog hx1)
  have h2pos : 0 < 2 * Nat.iterLog (d + 2) n := by omega
  have hdiv_ge : 2 ^ 63 ≤ Nat.iterLog (d + 1) n / (2 * Nat.iterLog (d + 2) n) := by
    rw [Nat.le_div_iff_mul_le h2pos]
    omega
  change 2 * max (2 ^ 63) (Nat.iterLog (d + 1) n / (2 * Nat.iterLog (d + 2) n)) *
      Nat.iterLog (d + 2) n ≤ Nat.iterLog ((d + 2) - 1) n
  rw [max_eq_right hdiv_ge]
  have hsub : (d + 2) - 1 = d + 1 := by omega
  rw [hsub]
  calc
    2 * (Nat.iterLog (d + 1) n / (2 * Nat.iterLog (d + 2) n)) * Nat.iterLog (d + 2) n
      = (Nat.iterLog (d + 1) n / (2 * Nat.iterLog (d + 2) n)) * (2 * Nat.iterLog (d + 2) n) := by
          ring
    _ ≤ Nat.iterLog (d + 1) n := Nat.div_mul_le_self _ _

/-- Upper bound on `blockSize ℓ * iterLog ℓ n` for `iterLogMetaTree`: for all `1 ≤ ℓ` with
`71 ≤ iterLog ℓ n`, `blockSize ℓ * iterLog ℓ n ≤ max (2 * iterLog 1 n) (c * n * iterLog k n)`. -/
theorem blockSize_mul_iterLog_le_iterLogMetaTree (n k c : ℕ) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (hx : 71 ≤ Nat.iterLog ℓ n) :
    (iterLogMetaTree n k c).blockSize ℓ * Nat.iterLog ℓ n ≤
      max (2 * Nat.iterLog 1 n) (c * n * Nat.iterLog k n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hℓ
  clear hℓ
  rw [Nat.add_comm 1 d] at hx ⊢
  induction d with
  | zero =>
    change (1 * iterLogFanout n k c 1) * Nat.iterLog 1 n ≤ _
    simp only [Nat.one_mul, iterLogFanout]
    rcases le_total 1 ((c * n * Nat.iterLog k n) / (2 * Nat.iterLog 1 n)) with hmax | hmax
    · rw [max_eq_right hmax]
      have hmul : 2 * ((c * n * Nat.iterLog k n) / (2 * Nat.iterLog 1 n)) * Nat.iterLog 1 n =
          ((c * n * Nat.iterLog k n) / (2 * Nat.iterLog 1 n)) * (2 * Nat.iterLog 1 n) := by ring
      rw [hmul]
      exact (Nat.div_mul_le_self _ _).trans (_root_.le_max_right _ _)
    · rw [max_eq_left hmax, Nat.mul_one]
      exact _root_.le_max_left _ _
  | succ d ih =>
    have hx_prev : 71 ≤ Nat.iterLog (d + 1) n :=
      hx.trans (Nat.iterLog_anti_left n (Nat.le_succ (d + 1)))
    have hfan := fanout_mul_iterLog_le_iterLogMetaTree n k c
      (show 2 ≤ d + 2 by omega) hx
    have hsub : (d + 2) - 1 = d + 1 := by omega
    rw [hsub] at hfan
    calc
      (iterLogMetaTree n k c).blockSize (d + 2) * Nat.iterLog (d + 2) n
        = (iterLogMetaTree n k c).blockSize (d + 1) *
            ((iterLogMetaTree n k c).fanout (d + 2) * Nat.iterLog (d + 2) n) := by
              rw [(iterLogMetaTree n k c).blockSize_succ (d + 1), mul_assoc]
      _ ≤ (iterLogMetaTree n k c).blockSize (d + 1) * Nat.iterLog (d + 1) n :=
          Nat.mul_le_mul_left _ hfan
      _ ≤ max (2 * Nat.iterLog 1 n) (c * n * Nat.iterLog k n) := ih hx_prev

/-- Lower bound on `blockSize 1 * iterLog 1 n` for `iterLogMetaTree` when `2 ≤ n`:
`c * n * iterLog k n ≤ blockSize 1 * iterLog 1 n + 2 * iterLog 1 n`. -/
theorem mul_iterLog_le_blockSize_one_add_iterLogMetaTree {n : ℕ} (hn : 2 ≤ n) (k c : ℕ) :
    c * n * Nat.iterLog k n ≤
      (iterLogMetaTree n k c).blockSize 1 * Nat.iterLog 1 n + 2 * Nat.iterLog 1 n := by
  have hpos : 0 < Nat.iterLog 1 n := Nat.log_pos Nat.one_lt_two hn
  change c * n * Nat.iterLog k n ≤
      (1 * iterLogFanout n k c 1) * Nat.iterLog 1 n + 2 * Nat.iterLog 1 n
  simp only [Nat.one_mul, iterLogFanout]
  let q := (c * n * Nat.iterLog k n) / (2 * Nat.iterLog 1 n)
  have hq_le : q ≤ max 1 q := _root_.le_max_right 1 q
  have hrem : c * n * Nat.iterLog k n ≤ q * (2 * Nat.iterLog 1 n) + 2 * Nat.iterLog 1 n := by
    dsimp only [q]
    have hmod := Nat.div_add_mod (c * n * Nat.iterLog k n) (2 * Nat.iterLog 1 n)
    rw [mul_comm] at hmod
    have hlt : (c * n * Nat.iterLog k n) % (2 * Nat.iterLog 1 n) < 2 * Nat.iterLog 1 n :=
      Nat.mod_lt _ (by omega)
    omega
  have hmul : q * (2 * Nat.iterLog 1 n) ≤ 2 * max 1 q * Nat.iterLog 1 n := by
    calc
      q * (2 * Nat.iterLog 1 n) = (2 * q) * Nat.iterLog 1 n := by ring
      _ ≤ (2 * max 1 q) * Nat.iterLog 1 n :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hq_le)
  exact hrem.trans (Nat.add_le_add_right hmul _)

private theorem pow_pred_mul_blockSize_one_le (n k c : ℕ) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (hx : 71 ≤ Nat.iterLog ℓ n) :
    let T := iterLogMetaTree n k c
    (2 ^ (Nat.iterLog ℓ n / 2) - 1) * (T.blockSize 1 * Nat.iterLog 1 n) ≤
      2 ^ (Nat.iterLog ℓ n / 2) * (T.blockSize ℓ * Nat.iterLog ℓ n) := by
  set T := iterLogMetaTree n k c
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hℓ
  clear hℓ
  rw [Nat.add_comm 1 d] at hx ⊢
  induction d with
  | zero =>
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ 1)
  | succ d ih =>
    set x := Nat.iterLog (d + 2) n
    set y := Nat.iterLog (d + 1) n
    set P := 2 ^ (x / 2)
    set Q := 2 ^ (y / 2)
    set F := T.fanout (d + 2)
    have hx1 : 1 ≤ Nat.iterLog ((d + 1) + 1) n := by
      simpa only [Nat.add_assoc] using (show 1 ≤ x by omega)
    have hpow_xy : 4 * x * P ≤ y :=
      (four_mul_mul_two_pow_div_two_le_two_pow hx).trans (two_pow_le_prev_iterLog hx1)
    have hy71 : 71 ≤ y := by
      have : 1 ≤ P := Nat.one_le_pow _ _ Nat.two_pos
      nlinarith
    have ih' := ih hy71
    have hP_ge : 2 ≤ P := by
      have : 1 ≤ x / 2 := by omega
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (x / 2) := Nat.pow_le_pow_right Nat.two_pos this
    have h2P_le_Q : 2 * P ≤ Q := by
      have hdiv_lt : x / 2 + 1 ≤ y / 2 := by
        have : 1 ≤ P := by omega
        have h4x_le_y : 4 * x ≤ y := by nlinarith
        omega
      calc
        2 * P = 2 ^ (x / 2 + 1) := by rw [Nat.pow_succ]; ring
        _ ≤ 2 ^ (y / 2) := Nat.pow_le_pow_right Nat.two_pos hdiv_lt
    have hy_le_Fx : y ≤ F * x + 2 * x := by
      have hF_ge : 2 * (y / (2 * x)) ≤ F := by
        change 2 * (y / (2 * x)) ≤ 2 * max (2 ^ 63) (y / (2 * x))
        exact Nat.mul_le_mul_left 2 (_root_.le_max_right _ _)
      have hmod := Nat.div_add_mod y (2 * x)
      have hlt : y % (2 * x) < 2 * x := Nat.mod_lt y (by omega)
      have hmul : (2 * (y / (2 * x))) * x ≤ F * x := Nat.mul_le_mul_right x hF_ge
      have heq : (2 * x) * (y / (2 * x)) = (2 * (y / (2 * x))) * x := by ring
      omega
    have hstep_xy : Q * (P - 1) * y ≤ (Q - 1) * P * (F * x) := by
      have hQP : (Q - 1) * P * (2 * x) ≤ (Q - P) * y := by
        calc
          (Q - 1) * P * (2 * x) ≤ Q * P * (2 * x) :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.sub_le Q 1))
          _ = Q * (2 * x * P) := by ring
          _ ≤ (2 * (Q - P)) * (2 * x * P) := by
              refine Nat.mul_le_mul_right _ ?_
              omega
          _ = (Q - P) * (4 * x * P) := by ring
          _ ≤ (Q - P) * y := Nat.mul_le_mul_left _ hpow_xy
      have hident : Q * (P - 1) + (Q - P) = (Q - 1) * P := by
        zify [show 1 ≤ P by omega, show P ≤ Q by omega, show 1 ≤ Q by omega]
        ring
      have hadd : Q * (P - 1) * y + (Q - 1) * P * (2 * x) ≤
          (Q - 1) * P * (F * x) + (Q - 1) * P * (2 * x) := by
        calc
          Q * (P - 1) * y + (Q - 1) * P * (2 * x)
            ≤ Q * (P - 1) * y + (Q - P) * y := Nat.add_le_add_left hQP _
          _ = (Q * (P - 1) + (Q - P)) * y := by ring
          _ = (Q - 1) * P * y := by rw [hident]
          _ ≤ (Q - 1) * P * (F * x + 2 * x) := Nat.mul_le_mul_left _ hy_le_Fx
          _ = (Q - 1) * P * (F * x) + (Q - 1) * P * (2 * x) := by ring
      exact Nat.le_of_add_le_add_right hadd
    have hQ1_pos : 0 < Q - 1 := by omega
    refine Nat.le_of_mul_le_mul_left ?_ hQ1_pos
    calc
      (Q - 1) * ((P - 1) * (T.blockSize 1 * Nat.iterLog 1 n))
        = (P - 1) * ((Q - 1) * (T.blockSize 1 * Nat.iterLog 1 n)) := by ring
      _ ≤ (P - 1) * (Q * (T.blockSize (d + 1) * y)) := Nat.mul_le_mul_left _ ih'
      _ = (Q * (P - 1) * y) * T.blockSize (d + 1) := by ring
      _ ≤ ((Q - 1) * P * (F * x)) * T.blockSize (d + 1) := Nat.mul_le_mul_right _ hstep_xy
      _ = (Q - 1) * (P * (T.blockSize (d + 2) * x)) := by
          rw [T.blockSize_succ (d + 1)]
          ring

/-- Telescoping ratio preservation for `iterLogMetaTree`: at every level `1 ≤ ℓ` with
`71 ≤ iterLog ℓ n`, floor truncation across intermediate fanouts loses in total at most a factor
of `2` (`blockSize 1 * iterLog 1 n ≤ 2 * (blockSize ℓ * iterLog ℓ n)`). -/
theorem blockSize_one_mul_iterLog_le_two_mul_iterLogMetaTree (n k c : ℕ) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (hx : 71 ≤ Nat.iterLog ℓ n) :
    (iterLogMetaTree n k c).blockSize 1 * Nat.iterLog 1 n ≤
      2 * ((iterLogMetaTree n k c).blockSize ℓ * Nat.iterLog ℓ n) := by
  set T := iterLogMetaTree n k c
  set P := 2 ^ (Nat.iterLog ℓ n / 2)
  have hP_ge : 2 ≤ P := by
    have : 1 ≤ Nat.iterLog ℓ n / 2 := by omega
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (Nat.iterLog ℓ n / 2) := Nat.pow_le_pow_right Nat.two_pos this
  have htel := pow_pred_mul_blockSize_one_le n k c hℓ hx
  have hP_pos : 0 < P := by omega
  refine Nat.le_of_mul_le_mul_left ?_ hP_pos
  calc
    P * (T.blockSize 1 * Nat.iterLog 1 n)
      ≤ (2 * (P - 1)) * (T.blockSize 1 * Nat.iterLog 1 n) :=
          Nat.mul_le_mul_right _ (by omega)
    _ = 2 * ((P - 1) * (T.blockSize 1 * Nat.iterLog 1 n)) := by ring
    _ ≤ 2 * (P * (T.blockSize ℓ * Nat.iterLog ℓ n)) := Nat.mul_le_mul_left 2 htel
    _ = P * (2 * (T.blockSize ℓ * Nat.iterLog ℓ n)) := by ring

/-- Height lower bound for `iterLogMetaTree`: whenever `2 ≤ n`, `1 ≤ iterLog k n`, and
`2 * iterLog 1 n ≤ c * n * iterLog k n`, the tree height is within an `O(log* c)` additive
constant of `k`. -/
theorem le_height_iterLogMetaTree_add {n k c : ℕ}
    (hn : 2 ≤ n) (hk : 1 ≤ Nat.iterLog k n)
    (hc : 2 * Nat.iterLog 1 n ≤ c * n * Nat.iterLog k n) :
    k ≤ (iterLogMetaTree n k c).height +
      (Nat.logStar (max 71 (4 * c * (4 * c + 71))) + 2) := by
  set M := max 71 (4 * c * (4 * c + 71))
  set s := Nat.logStar M
  by_cases hsmall : k < s + 2
  · omega
  · push Not at hsmall
    set ℓ := k - (s + 1)
    have hℓ_ge : 1 ≤ ℓ := by omega
    have hk_eq : k = (s + 1) + ℓ := by omega
    have hM_le_tower : M ≤ Nat.twoTower (s + 1) := by
      have hs_le : Nat.logStar M ≤ s := le_rfl
      exact (Nat.logStar_le_iff.mp hs_le).trans (Nat.twoTower_lt_twoTower_succ s).le
    have htower_le_xℓ : Nat.twoTower (s + 1) ≤ Nat.iterLog ℓ n := by
      by_contra hlt
      push Not at hlt
      have hle1 : Nat.iterLog s (Nat.iterLog ℓ n) ≤ 1 :=
        Nat.iterLog_le_one_iff_lt_twoTower.mpr hlt
      have hk_zero : Nat.iterLog k n = 0 := by
        rw [hk_eq, Nat.iterLog_add, Nat.iterLog_succ]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h0 | h1
        · simp [h0]
        · simp [h1]
      omega
    have hxℓ_71 : 71 ≤ Nat.iterLog ℓ n :=
      (_root_.le_max_left 71 _).trans (hM_le_tower.trans htower_le_xℓ)
    have h4c_le : 4 * c * Nat.iterLog k n ≤ Nat.iterLog ℓ n := by
      by_cases hy_big : 4 * c + 71 ≤ Nat.iterLog k n
      · have hℓ_le_pred : ℓ ≤ k - 1 := by omega
        have hk_pos : 1 ≤ k := by omega
        have hprev_eq : (k - 1) + 1 = k := by omega
        have hpow_y : 2 ^ Nat.iterLog k n ≤ Nat.iterLog ℓ n := by
          have hp := two_pow_le_prev_iterLog (j := k - 1) (n := n) (by rwa [hprev_eq])
          rw [hprev_eq] at hp
          exact hp.trans (Nat.iterLog_anti_left n hℓ_le_pred)
        have hy71 : 71 ≤ Nat.iterLog k n := by omega
        have h8 := eight_mul_add_four_le_two_pow (y := Nat.iterLog k n / 2) (by omega)
        have hy_le_pow : Nat.iterLog k n ≤ 2 ^ (Nat.iterLog k n / 2) := by omega
        calc
          4 * c * Nat.iterLog k n ≤ Nat.iterLog k n * Nat.iterLog k n :=
            Nat.mul_le_mul_right _ (by omega)
          _ ≤ 4 * Nat.iterLog k n * 2 ^ (Nat.iterLog k n / 2) := by nlinarith
          _ ≤ 2 ^ Nat.iterLog k n := four_mul_mul_two_pow_div_two_le_two_pow hy71
          _ ≤ Nat.iterLog ℓ n := hpow_y
      · push Not at hy_big
        calc
          4 * c * Nat.iterLog k n ≤ 4 * c * (4 * c + 71) :=
            Nat.mul_le_mul_left _ hy_big.le
          _ ≤ M := _root_.le_max_right 71 _
          _ ≤ Nat.iterLog ℓ n := hM_le_tower.trans htower_le_xℓ
    have hB_mul := blockSize_mul_iterLog_le_iterLogMetaTree n k c hℓ_ge hxℓ_71
    rw [max_eq_right hc] at hB_mul
    have hcn_le : c * n * Nat.iterLog k n ≤ (n / 2) * Nat.iterLog ℓ n := by
      have hn_le_3 : n ≤ 3 * (n / 2) := by omega
      calc
        c * n * Nat.iterLog k n ≤ c * (3 * (n / 2)) * Nat.iterLog k n := by nlinarith
        _ ≤ (n / 2) * (4 * c * Nat.iterLog k n) := by nlinarith
        _ ≤ (n / 2) * Nat.iterLog ℓ n := Nat.mul_le_mul_left _ h4c_le
    have hB_le : (iterLogMetaTree n k c).blockSize ℓ ≤ n / 2 :=
      Nat.le_of_mul_le_mul_right (hB_mul.trans hcn_le) (by omega)
    have hℓ_le_h : ℓ ≤ (iterLogMetaTree n k c).height :=
      (MetaTree.le_height_ofFanout_iff hn (iterLogFanout n k c)
        (iterLogMetaTree n k c).fanout_pos (iterLogMetaTree n k c).even_fanout ℓ).mpr hB_le
    omega


/-! ### Step-indexed meta-operation execution and LCA probe accounting -/

section Execution

variable {Op : Type*} {Result : Op → Type} {cells w : ℕ}

/-- Cell memory snapshot right after executing the first `stepIdx` elementary operations of `ops`
from `(0, D.init)`. -/
@[expose] def memAt (D : IndexedScheme Op Result cells w) (ops : List Op) (stepIdx : ℕ) :
    Mem cells w :=
  (D.runSeq (ops.take stepIdx)).2

/-- Elementary operation slice corresponding to meta-operation range `[t₁, t₂)` when `initLen`
initial operations precede the meta-operations and each meta-operation spans `stride` elementary
operations (`stride = 3` for `insertQueryDeleteDist`, `stride = 2` for `insertDeleteDist`). -/
@[expose] def elemSlice (initLen stride : ℕ) (ops : List Op) (t₁ t₂ : ℕ) : List Op :=
  (ops.drop (initLen + stride * t₁)).take (stride * (t₂ - t₁))

/-- Set of distinct cells probed during meta-operation range `[t₁, t₂)`. -/
@[expose] def rangeProbedCells (D : IndexedScheme Op Result cells w) (initLen stride : ℕ)
    (ops : List Op) (t₁ t₂ : ℕ) : Finset (Fin cells) :=
  D.probedCellsInterval (initLen + stride * t₁) (memAt D ops (initLen + stride * t₁))
    (elemSlice initLen stride ops t₁ t₂)

/-- Number of cell probes executed during meta-operation range `[t₁, t₂)`. -/
@[expose] def rangeProbes (D : IndexedScheme Op Result cells w) (initLen stride : ℕ)
    (ops : List Op) (t₁ t₂ : ℕ) : ℕ :=
  D.probesInterval (initLen + stride * t₁) (memAt D ops (initLen + stride * t₁))
    (elemSlice initLen stride ops t₁ t₂)

/-- Set of distinct cells probed during single meta-operation `t`. -/
@[expose] def metaProbedCells (D : IndexedScheme Op Result cells w) (initLen stride : ℕ)
    (ops : List Op) (t : ℕ) : Finset (Fin cells) :=
  rangeProbedCells D initLen stride ops t (t + 1)

/-- Number of cell probes executed during single meta-operation `t`. -/
@[expose] def metaProbes (D : IndexedScheme Op Result cells w) (initLen stride : ℕ)
    (ops : List Op) (t : ℕ) : ℕ :=
  rangeProbes D initLen stride ops t (t + 1)

@[simp]
theorem rangeProbes_self (D : IndexedScheme Op Result cells w) (initLen stride : ℕ)
    (ops : List Op) (t : ℕ) :
    rangeProbes D initLen stride ops t t = 0 := by
  simp [rangeProbes, elemSlice]

@[simp]
theorem rangeProbedCells_self (D : IndexedScheme Op Result cells w) (initLen stride : ℕ)
    (ops : List Op) (t : ℕ) :
    rangeProbedCells D initLen stride ops t t = ∅ := by
  simp [rangeProbedCells, elemSlice]

theorem card_rangeProbedCells_le_rangeProbes (D : IndexedScheme Op Result cells w)
    (initLen stride : ℕ) (ops : List Op) (t₁ t₂ : ℕ) :
    (rangeProbedCells D initLen stride ops t₁ t₂).card ≤
      rangeProbes D initLen stride ops t₁ t₂ :=
  D.card_probedCellsInterval_le_probesInterval _ _ _

/-- Running `elemSlice initLen stride ops t₁ t₂` from `(initLen + stride * t₁, memAt ...)` reaches
exact post-memory `memAt D ops (initLen + stride * t₂)` whenever `t₁ ≤ t₂`. -/
theorem memAt_eq_runInterval_elemSlice (D : IndexedScheme Op Result cells w)
    (initLen stride : ℕ) (ops : List Op) {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    memAt D ops (initLen + stride * t₂) =
      (D.runInterval (initLen + stride * t₁) (memAt D ops (initLen + stride * t₁))
        (elemSlice initLen stride ops t₁ t₂)).2 := by
  let a := initLen + stride * t₁
  let b := initLen + stride * t₂
  have hab : b = a + stride * (t₂ - t₁) := by
    dsimp only [a, b]
    rw [Nat.mul_sub_left_distrib]
    have hle : stride * t₁ ≤ stride * t₂ := Nat.mul_le_mul_left _ h
    omega
  by_cases halen : a ≤ ops.length
  · have hsplit : ops.take b = ops.take a ++ elemSlice initLen stride ops t₁ t₂ := by
      rw [hab, List.take_add]
      rfl
    have hlen : (ops.take a).length = a := List.length_take_of_le halen
    change (D.runInterval 0 D.init (ops.take b)).2 =
      (D.runInterval a (memAt D ops a) (elemSlice initLen stride ops t₁ t₂)).2
    rw [hsplit, D.runInterval_append, Nat.zero_add, hlen]
    rfl
  · push Not at halen
    have htake_a : ops.take a = ops := List.take_of_length_le halen.le
    have htake_b : ops.take b = ops := List.take_of_length_le (by omega)
    have hdrop_a : ops.drop a = [] := List.drop_of_length_le halen.le
    change (D.runSeq (ops.take b)).2 =
      (D.runInterval a (D.runSeq (ops.take a)).2
        ((ops.drop a).take (stride * (t₂ - t₁)))).2
    rw [htake_a, htake_b, hdrop_a]
    simp

private theorem elemSlice_append {initLen stride : ℕ} (ops : List Op) {t₁ t₂ t₃ : ℕ}
    (h₁₂ : t₁ ≤ t₂) (h₂₃ : t₂ ≤ t₃) :
    elemSlice initLen stride ops t₁ t₃ =
      elemSlice initLen stride ops t₁ t₂ ++ elemSlice initLen stride ops t₂ t₃ := by
  have hlen : stride * (t₃ - t₁) = stride * (t₂ - t₁) + stride * (t₃ - t₂) := by
    repeat rw [Nat.mul_sub_left_distrib]
    have hle1 : stride * t₁ ≤ stride * t₂ := Nat.mul_le_mul_left _ h₁₂
    have hle2 : stride * t₂ ≤ stride * t₃ := Nat.mul_le_mul_left _ h₂₃
    omega
  have hbase : (initLen + stride * t₁) + stride * (t₂ - t₁) = initLen + stride * t₂ := by
    rw [Nat.mul_sub_left_distrib]
    have hle1 : stride * t₁ ≤ stride * t₂ := Nat.mul_le_mul_left _ h₁₂
    omega
  simp only [elemSlice, hlen, List.take_add, List.drop_drop, hbase]

private theorem elemSlice_step_or_nil {initLen stride : ℕ} (ops : List Op) {t₁ t₂ : ℕ}
    (h₁₂ : t₁ ≤ t₂) (t₃ : ℕ) :
    initLen + stride * t₁ + (elemSlice initLen stride ops t₁ t₂).length = initLen + stride * t₂ ∨
      elemSlice initLen stride ops t₂ t₃ = [] := by
  by_cases hblen : initLen + stride * t₂ ≤ ops.length
  · left
    have hlen : (elemSlice initLen stride ops t₁ t₂).length = stride * (t₂ - t₁) := by
      simp only [elemSlice, List.length_take, List.length_drop]
      have hle1 : stride * t₁ ≤ stride * t₂ := Nat.mul_le_mul_left _ h₁₂
      have hsub : stride * (t₂ - t₁) = (initLen + stride * t₂) - (initLen + stride * t₁) := by
        rw [Nat.mul_sub_left_distrib]; omega
      omega
    rw [hlen, Nat.mul_sub_left_distrib]
    have hle1 : stride * t₁ ≤ stride * t₂ := Nat.mul_le_mul_left _ h₁₂
    omega
  · right
    push Not at hblen
    simp [elemSlice, List.drop_of_length_le hblen.le]

/-- Additivity of `rangeProbes` across contiguous meta-operation intervals `[t₁, t₂)` and
`[t₂, t₃)`. -/
theorem rangeProbes_append (D : IndexedScheme Op Result cells w) (initLen stride : ℕ)
    (ops : List Op) {t₁ t₂ t₃ : ℕ} (h₁₂ : t₁ ≤ t₂) (h₂₃ : t₂ ≤ t₃) :
    rangeProbes D initLen stride ops t₁ t₃ =
      rangeProbes D initLen stride ops t₁ t₂ + rangeProbes D initLen stride ops t₂ t₃ := by
  simp only [rangeProbes]
  rw [elemSlice_append ops h₁₂ h₂₃, D.probesInterval_append,
    ← memAt_eq_runInterval_elemSlice D initLen stride ops h₁₂]
  congr 1
  rcases elemSlice_step_or_nil ops h₁₂ t₃ with hidx | hnil
  · rw [hidx]
  · simp [hnil]

/-- Union law for `rangeProbedCells` across contiguous meta-operation intervals `[t₁, t₂)` and
`[t₂, t₃)`. -/
theorem rangeProbedCells_append (D : IndexedScheme Op Result cells w) (initLen stride : ℕ)
    (ops : List Op) {t₁ t₂ t₃ : ℕ} (h₁₂ : t₁ ≤ t₂) (h₂₃ : t₂ ≤ t₃) :
    rangeProbedCells D initLen stride ops t₁ t₃ =
      rangeProbedCells D initLen stride ops t₁ t₂ ∪
        rangeProbedCells D initLen stride ops t₂ t₃ := by
  simp only [rangeProbedCells]
  rw [elemSlice_append ops h₁₂ h₂₃, D.probedCellsInterval_append,
    ← memAt_eq_runInterval_elemSlice D initLen stride ops h₁₂]
  congr 1
  rcases elemSlice_step_or_nil ops h₁₂ t₃ with hidx | hnil
  · rw [hidx]
  · simp [hnil]

theorem rangeProbes_le_seqProbes (D : IndexedScheme Op Result cells w) (initLen stride : ℕ)
    (ops : List Op) (t₁ t₂ : ℕ) :
    rangeProbes D initLen stride ops t₁ t₂ ≤ D.seqProbes ops := by
  let a := initLen + stride * t₁
  by_cases halen : a ≤ ops.length
  · have hlen_a : (ops.take a).length = a := List.length_take_of_le halen
    have hsplit : ops = ops.take a ++
        (elemSlice initLen stride ops t₁ t₂ ++ (ops.drop a).drop (stride * (t₂ - t₁))) := by
      dsimp only [elemSlice, a]
      rw [List.take_append_drop, List.take_append_drop]
    have hseq := D.probesInterval_append 0 D.init (ops.take a)
      (elemSlice initLen stride ops t₁ t₂ ++ (ops.drop a).drop (stride * (t₂ - t₁)))
    rw [← hsplit, Nat.zero_add, hlen_a] at hseq
    have hmem : (D.runInterval 0 D.init (ops.take a)).2 = memAt D ops a := rfl
    rw [hmem] at hseq
    have htail := D.probesInterval_append a (memAt D ops a)
      (elemSlice initLen stride ops t₁ t₂) ((ops.drop a).drop (stride * (t₂ - t₁)))
    change D.probesInterval a (memAt D ops a) (elemSlice initLen stride ops t₁ t₂) ≤
      D.probesInterval 0 D.init ops
    omega
  · push Not at halen
    have hdrop : ops.drop a = [] := List.drop_of_length_le halen.le
    change D.probesInterval a (memAt D ops a) ((ops.drop a).take (stride * (t₂ - t₁))) ≤
      D.seqProbes ops
    rw [hdrop]
    simp

private theorem rangeProbes_add_mul (D : IndexedScheme Op Result cells w) (initLen stride : ℕ)
    (ops : List Op) (t₀ m q : ℕ) :
    rangeProbes D initLen stride ops t₀ (t₀ + q * m) =
      ∑ i ∈ Finset.range q, rangeProbes D initLen stride ops (t₀ + i * m) (t₀ + (i + 1) * m) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h₁₂ : t₀ ≤ t₀ + q * m := Nat.le_add_right _ _
    have h₂₃ : t₀ + q * m ≤ t₀ + (q + 1) * m := by
      rw [Nat.succ_mul]
      omega
    rw [rangeProbes_append D initLen stride ops h₁₂ h₂₃, Finset.sum_range_succ, ih]

private theorem rangeProbedCells_add_mul (D : IndexedScheme Op Result cells w)
    (initLen stride : ℕ) (ops : List Op) (t₀ m q : ℕ) :
    rangeProbedCells D initLen stride ops t₀ (t₀ + q * m) =
      (Finset.range q).biUnion fun i =>
        rangeProbedCells D initLen stride ops (t₀ + i * m) (t₀ + (i + 1) * m) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h₁₂ : t₀ ≤ t₀ + q * m := Nat.le_add_right _ _
    have h₂₃ : t₀ + q * m ≤ t₀ + (q + 1) * m := by
      rw [Nat.succ_mul]
      omega
    rw [rangeProbedCells_append D initLen stride ops h₁₂ h₂₃, Finset.range_add_one,
      Finset.biUnion_insert, ih, Finset.union_comm]

namespace MetaTree

/-- Distinct cells probed during the `b`-th level-`ℓ` node `[nodeStart ℓ b, nodeStop ℓ b)`. -/
@[expose] def nodeProbedCells (T : MetaTree) (D : IndexedScheme Op Result cells w)
    (initLen stride : ℕ) (ops : List Op) (ℓ b : ℕ) : Finset (Fin cells) :=
  rangeProbedCells D initLen stride ops (T.nodeStart ℓ b) (T.nodeStop ℓ b)

/-- Total cell probes incurred during the `b`-th level-`ℓ` node (`probe_u` in
[LiLiangYuZhou2023], Section 3, p. 11 / PDF p. 12). -/
@[expose] def nodeProbes (T : MetaTree) (D : IndexedScheme Op Result cells w)
    (initLen stride : ℕ) (ops : List Op) (ℓ b : ℕ) : ℕ :=
  rangeProbes D initLen stride ops (T.nodeStart ℓ b) (T.nodeStop ℓ b)

/-- Distinct cells probed during the `i`-th child segment of internal node `(ℓ + 1, b)`, i.e.,
level-`ℓ` node `b * T.fanout (ℓ + 1) + i.1` (`S_A^{[i]}` in [LiLiangYuZhou2023], Section 4.2,
p. 14 / PDF p. 15). -/
@[expose] def segProbedCells (T : MetaTree) (D : IndexedScheme Op Result cells w)
    (initLen stride : ℕ) (ops : List Op) (ℓ b : ℕ) (i : Fin (T.fanout (ℓ + 1))) :
    Finset (Fin cells) :=
  T.nodeProbedCells D initLen stride ops ℓ (b * T.fanout (ℓ + 1) + i.1)

/-- Cell probes incurred during the `i`-th child segment of internal node `(ℓ + 1, b)`. -/
@[expose] def segProbes (T : MetaTree) (D : IndexedScheme Op Result cells w)
    (initLen stride : ℕ) (ops : List Op) (ℓ b : ℕ) (i : Fin (T.fanout (ℓ + 1))) : ℕ :=
  T.nodeProbes D initLen stride ops ℓ (b * T.fanout (ℓ + 1) + i.1)

/-- Number of distinct child segments of internal node `(ℓ + 1, b)` in which cell `j` is probed. -/
@[expose] def segHitCount (T : MetaTree) (D : IndexedScheme Op Result cells w)
    (initLen stride : ℕ) (ops : List Op) (ℓ b : ℕ) (j : Fin cells) : ℕ :=
  (Finset.univ.filter fun i : Fin (T.fanout (ℓ + 1)) =>
    j ∈ T.segProbedCells D initLen stride ops ℓ b i).card

/-- Bad cells of internal node `(ℓ + 1, b)` (`S_bad` in [LiLiangYuZhou2023], Section 4.2, p. 14 /
PDF p. 15): cells probed in at least two distinct child segments of `(ℓ + 1, b)`. -/
@[expose] def badCells (T : MetaTree) (D : IndexedScheme Op Result cells w)
    (initLen stride : ℕ) (ops : List Op) (ℓ b : ℕ) : Finset (Fin cells) :=
  Finset.univ.filter fun j => 2 ≤ T.segHitCount D initLen stride ops ℓ b j

/-- LCA probe cost `cost_u` assigned to internal node `(ℓ + 1, b)` ([LiLiangYuZhou2023], Section 3,
p. 11 / PDF p. 12): a cell probed in `s` distinct child segments has `s - 1` consecutive
cross-segment re-visits whose LCA is `(ℓ + 1, b)`. -/
@[expose] def nodeCost (T : MetaTree) (D : IndexedScheme Op Result cells w)
    (initLen stride : ℕ) (ops : List Op) (ℓ b : ℕ) : ℕ :=
  ∑ j : Fin cells, (T.segHitCount D initLen stride ops ℓ b j - 1)

theorem mem_badCells_iff (T : MetaTree) (D : IndexedScheme Op Result cells w)
    (initLen stride : ℕ) (ops : List Op) (ℓ b : ℕ) (j : Fin cells) :
    j ∈ T.badCells D initLen stride ops ℓ b ↔
      2 ≤ T.segHitCount D initLen stride ops ℓ b j := by
  simp [badCells]

/-- A cell belongs to `badCells` if and only if it is probed in two distinct child segments of
`(ℓ + 1, b)`. -/
theorem mem_badCells_iff_exists_ne (T : MetaTree) (D : IndexedScheme Op Result cells w)
    (initLen stride : ℕ) (ops : List Op) (ℓ b : ℕ) (j : Fin cells) :
    j ∈ T.badCells D initLen stride ops ℓ b ↔
      ∃ i₁ i₂ : Fin (T.fanout (ℓ + 1)), i₁ ≠ i₂ ∧
        j ∈ T.segProbedCells D initLen stride ops ℓ b i₁ ∧
        j ∈ T.segProbedCells D initLen stride ops ℓ b i₂ := by
  have htwo : 2 ≤ T.segHitCount D initLen stride ops ℓ b j ↔
      1 < T.segHitCount D initLen stride ops ℓ b j := by omega
  rw [T.mem_badCells_iff, htwo, segHitCount, Finset.one_lt_card_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨i₁, i₂, h₁, h₂, hne⟩ => ⟨i₁, i₂, hne, h₁, h₂⟩,
    fun ⟨i₁, i₂, hne, h₁, h₂⟩ => ⟨i₁, i₂, h₁, h₂, hne⟩⟩

theorem mem_badCells_of_mem_segProbedCells_ne (T : MetaTree)
    (D : IndexedScheme Op Result cells w) (initLen stride : ℕ) (ops : List Op)
    (ℓ b : ℕ) {i₁ i₂ : Fin (T.fanout (ℓ + 1))} (hne : i₁ ≠ i₂) {j : Fin cells}
    (hj₁ : j ∈ T.segProbedCells D initLen stride ops ℓ b i₁)
    (hj₂ : j ∈ T.segProbedCells D initLen stride ops ℓ b i₂) :
    j ∈ T.badCells D initLen stride ops ℓ b :=
  (T.mem_badCells_iff_exists_ne D initLen stride ops ℓ b j).mpr ⟨i₁, i₂, hne, hj₁, hj₂⟩

/-- Level-wise probe bound: the sum of `nodeProbes` across all packed nodes at any single level `ℓ`
never exceeds `D.seqProbes ops`. -/
theorem sum_nodeProbes_le_seqProbes (T : MetaTree) (D : IndexedScheme Op Result cells w)
    (initLen stride : ℕ) (ops : List Op) (ℓ : ℕ) :
    ∑ b ∈ Finset.range (T.nodeCount ℓ), T.nodeProbes D initLen stride ops ℓ b ≤
      D.seqProbes ops := by
  have heq := rangeProbes_add_mul D initLen stride ops 0 (T.blockSize ℓ) (T.nodeCount ℓ)
  simp only [Nat.zero_add] at heq
  change ∑ b ∈ Finset.range (T.nodeCount ℓ),
      rangeProbes D initLen stride ops (b * T.blockSize ℓ) ((b + 1) * T.blockSize ℓ) ≤
    D.seqProbes ops
  rw [← heq]
  exact rangeProbes_le_seqProbes D initLen stride ops 0 _

/-- Probes at internal node `(ℓ + 1, b)` decompose into the sum over its `T.fanout (ℓ + 1)` child
segments. -/
theorem nodeProbes_succ_eq_sum_segProbes (T : MetaTree) (D : IndexedScheme Op Result cells w)
    (initLen stride : ℕ) (ops : List Op) (ℓ b : ℕ) :
    T.nodeProbes D initLen stride ops (ℓ + 1) b =
      ∑ i : Fin (T.fanout (ℓ + 1)), T.segProbes D initLen stride ops ℓ b i := by
  have hstop : T.nodeStop (ℓ + 1) b =
      T.nodeStart (ℓ + 1) b + T.fanout (ℓ + 1) * T.blockSize ℓ := by
    simp only [nodeStart, nodeStop, T.blockSize_succ ℓ]; ring
  simp only [nodeProbes, segProbes]
  rw [hstop, rangeProbes_add_mul, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← T.nodeStart_child ℓ b i.1, ← T.nodeStop_child ℓ b i.1]

/-- Probed cells at internal node `(ℓ + 1, b)` equal the union over its `T.fanout (ℓ + 1)` child
segments. -/
theorem nodeProbedCells_succ_eq_biUnion_segProbedCells (T : MetaTree)
    (D : IndexedScheme Op Result cells w) (initLen stride : ℕ) (ops : List Op) (ℓ b : ℕ) :
    T.nodeProbedCells D initLen stride ops (ℓ + 1) b =
      Finset.univ.biUnion fun i : Fin (T.fanout (ℓ + 1)) =>
        T.segProbedCells D initLen stride ops ℓ b i := by
  have hstop : T.nodeStop (ℓ + 1) b =
      T.nodeStart (ℓ + 1) b + T.fanout (ℓ + 1) * T.blockSize ℓ := by
    simp only [nodeStart, nodeStop, T.blockSize_succ ℓ]; ring
  simp only [nodeProbedCells]
  rw [hstop, rangeProbedCells_add_mul]
  ext j
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_univ, true_and, segProbedCells,
    nodeProbedCells]
  constructor
  · rintro ⟨i, hi, hj⟩
    refine ⟨⟨i, hi⟩, ?_⟩
    rwa [T.nodeStart_child ℓ b i, T.nodeStop_child ℓ b i]
  · rintro ⟨⟨i, hi⟩, hj⟩
    refine ⟨i, hi, ?_⟩
    rwa [← T.nodeStart_child ℓ b i, ← T.nodeStop_child ℓ b i]

theorem sum_card_segProbedCells_le_nodeProbes (T : MetaTree)
    (D : IndexedScheme Op Result cells w) (initLen stride : ℕ) (ops : List Op) (ℓ b : ℕ) :
    ∑ i : Fin (T.fanout (ℓ + 1)), (T.segProbedCells D initLen stride ops ℓ b i).card ≤
      T.nodeProbes D initLen stride ops (ℓ + 1) b := by
  rw [T.nodeProbes_succ_eq_sum_segProbes]
  exact Finset.sum_le_sum fun i _ => card_rangeProbedCells_le_rangeProbes D initLen stride ops _ _

theorem card_badCells_le_nodeCost (T : MetaTree) (D : IndexedScheme Op Result cells w)
    (initLen stride : ℕ) (ops : List Op) (ℓ b : ℕ) :
    (T.badCells D initLen stride ops ℓ b).card ≤
      T.nodeCost D initLen stride ops ℓ b := by
  rw [Finset.card_eq_sum_ones, nodeCost]
  calc
    ∑ j ∈ T.badCells D initLen stride ops ℓ b, 1
      ≤ ∑ j ∈ T.badCells D initLen stride ops ℓ b,
          (T.segHitCount D initLen stride ops ℓ b j - 1) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have := (T.mem_badCells_iff D initLen stride ops ℓ b j).mp hj
            omega
    _ ≤ ∑ j : Fin cells, (T.segHitCount D initLen stride ops ℓ b j - 1) :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _

private theorem sum_card_segProbedCells_inter_eq_sum_segHitCount (T : MetaTree)
    (D : IndexedScheme Op Result cells w) (initLen stride : ℕ) (ops : List Op) (ℓ b : ℕ)
    (S : Finset (Fin cells)) :
    ∑ i : Fin (T.fanout (ℓ + 1)),
        (T.segProbedCells D initLen stride ops ℓ b i ∩ S).card =
      ∑ j ∈ S, T.segHitCount D initLen stride ops ℓ b j := by
  calc
    ∑ i : Fin (T.fanout (ℓ + 1)),
        (T.segProbedCells D initLen stride ops ℓ b i ∩ S).card
      = ∑ i : Fin (T.fanout (ℓ + 1)), ∑ j ∈ S,
          if j ∈ T.segProbedCells D initLen stride ops ℓ b i then 1 else 0 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    _ = ∑ j ∈ S, ∑ i : Fin (T.fanout (ℓ + 1)),
          if j ∈ T.segProbedCells D initLen stride ops ℓ b i then 1 else 0 :=
            Finset.sum_comm
    _ = ∑ j ∈ S, T.segHitCount D initLen stride ops ℓ b j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [segHitCount, Finset.card_filter]

/-- **Bad-cell intersection bound** ([LiLiangYuZhou2023], Section 4.3, Claim 4.1, Eq. (5), p. 17 /
PDF p. 18): across all `λ_{ℓ+1}` child segments of internal node `(ℓ + 1, b)`, the sum of
`|S_A^{[i]} ∩ S_bad|` is at most `2 * nodeCost`, since every cell probed in `s ≥ 2` segments
contributes `s` to the left-hand side and `s - 1 ≥ s / 2` to `nodeCost`. -/
theorem sum_card_segProbedCells_inter_badCells_le_two_mul_nodeCost (T : MetaTree)
    (D : IndexedScheme Op Result cells w) (initLen stride : ℕ) (ops : List Op) (ℓ b : ℕ) :
    ∑ i : Fin (T.fanout (ℓ + 1)),
      (T.segProbedCells D initLen stride ops ℓ b i ∩
        T.badCells D initLen stride ops ℓ b).card ≤
      2 * T.nodeCost D initLen stride ops ℓ b := by
  set bad := T.badCells D initLen stride ops ℓ b
  rw [T.sum_card_segProbedCells_inter_eq_sum_segHitCount D initLen stride ops ℓ b bad,
    nodeCost, Finset.mul_sum]
  calc
    ∑ j ∈ bad, T.segHitCount D initLen stride ops ℓ b j
      ≤ ∑ j ∈ bad, 2 * (T.segHitCount D initLen stride ops ℓ b j - 1) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have h2 := (T.mem_badCells_iff D initLen stride ops ℓ b j).mp hj
          omega
    _ ≤ ∑ j : Fin cells, 2 * (T.segHitCount D initLen stride ops ℓ b j - 1) :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _

/-- Exact per-node telescoping identity: `nodeCost` plus the number of distinct cells probed in
`(ℓ + 1, b)` equals the sum of distinct cells probed across its `T.fanout (ℓ + 1)` children. -/
theorem nodeCost_add_card_nodeProbedCells (T : MetaTree)
    (D : IndexedScheme Op Result cells w) (initLen stride : ℕ) (ops : List Op) (ℓ b : ℕ) :
    T.nodeCost D initLen stride ops ℓ b +
      (T.nodeProbedCells D initLen stride ops (ℓ + 1) b).card =
      ∑ i : Fin (T.fanout (ℓ + 1)), (T.segProbedCells D initLen stride ops ℓ b i).card := by
  have hmem_iff : ∀ j : Fin cells,
      j ∈ T.nodeProbedCells D initLen stride ops (ℓ + 1) b ↔
        0 < T.segHitCount D initLen stride ops ℓ b j := by
    intro j
    rw [T.nodeProbedCells_succ_eq_biUnion_segProbedCells, segHitCount, Finset.card_pos,
      Finset.filter_nonempty_iff]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  have hcard_parent : (T.nodeProbedCells D initLen stride ops (ℓ + 1) b).card =
      ∑ j : Fin cells, if 0 < T.segHitCount D initLen stride ops ℓ b j then 1 else 0 := by
    have hfilt : T.nodeProbedCells D initLen stride ops (ℓ + 1) b =
        Finset.univ.filter fun j => 0 < T.segHitCount D initLen stride ops ℓ b j := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem_iff]
    rw [hfilt, Finset.card_filter]
  have hsum_children : ∑ i : Fin (T.fanout (ℓ + 1)),
        (T.segProbedCells D initLen stride ops ℓ b i).card =
      ∑ j : Fin cells, T.segHitCount D initLen stride ops ℓ b j := by
    simpa only [Finset.inter_univ] using
      T.sum_card_segProbedCells_inter_eq_sum_segHitCount D initLen stride ops ℓ b Finset.univ
  rw [nodeCost, hcard_parent, hsum_children, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hpos <;> omega

private theorem sum_nodeCost_level_add_le (T : MetaTree)
    (D : IndexedScheme Op Result cells w) (initLen stride : ℕ) (ops : List Op) (ℓ : ℕ) :
    (∑ b ∈ Finset.range (T.nodeCount (ℓ + 1)), T.nodeCost D initLen stride ops ℓ b) +
      (∑ b ∈ Finset.range (T.nodeCount (ℓ + 1)),
        (T.nodeProbedCells D initLen stride ops (ℓ + 1) b).card) ≤
      ∑ c ∈ Finset.range (T.nodeCount ℓ),
        (T.nodeProbedCells D initLen stride ops ℓ c).card := by
  rw [← Finset.sum_add_distrib]
  have hrow : ∑ b ∈ Finset.range (T.nodeCount (ℓ + 1)),
        (T.nodeCost D initLen stride ops ℓ b +
          (T.nodeProbedCells D initLen stride ops (ℓ + 1) b).card) =
      ∑ b ∈ Finset.range (T.nodeCount (ℓ + 1)),
        ∑ i ∈ Finset.range (T.fanout (ℓ + 1)),
          (T.nodeProbedCells D initLen stride ops ℓ (b * T.fanout (ℓ + 1) + i)).card := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [T.nodeCost_add_card_nodeProbedCells, ← Fin.sum_univ_eq_sum_range]
    rfl
  rw [hrow]
  set q := T.nodeCount (ℓ + 1)
  set F := T.fanout (ℓ + 1)
  have hqF_le : q * F ≤ T.nodeCount ℓ := by
    have hdiv : q = T.nodeCount ℓ / F := by
      simp only [q, F, nodeCount, T.blockSize_succ ℓ, Nat.div_div_eq_div_mul]
    rw [hdiv]
    exact Nat.div_mul_le_self _ _
  have hflat : ∀ m : ℕ,
      ∑ b ∈ Finset.range m, ∑ i ∈ Finset.range F,
        (T.nodeProbedCells D initLen stride ops ℓ (b * F + i)).card =
      ∑ c ∈ Finset.range (m * F),
        (T.nodeProbedCells D initLen stride ops ℓ c).card := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]
  rw [hflat q]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hqF_le)

/-- **Global LCA probe conservation** ([LiLiangYuZhou2023], Section 3, p. 11 / PDF p. 12):
summing `nodeCost` across all packed internal nodes in the first `H` internal levels never exceeds
`D.seqProbes ops` (instantiating `H = T.height` covers the entire `MetaTree`). -/
theorem sum_nodeCost_le_seqProbes_of_height (T : MetaTree)
    (D : IndexedScheme Op Result cells w) (initLen stride : ℕ) (ops : List Op) (H : ℕ) :
    ∑ ℓ ∈ Finset.range H, ∑ b ∈ Finset.range (T.nodeCount (ℓ + 1)),
      T.nodeCost D initLen stride ops ℓ b ≤ D.seqProbes ops := by
  have htel : ∀ m : ℕ,
      (∑ ℓ ∈ Finset.range m, ∑ b ∈ Finset.range (T.nodeCount (ℓ + 1)),
        T.nodeCost D initLen stride ops ℓ b) +
      (∑ b ∈ Finset.range (T.nodeCount m),
        (T.nodeProbedCells D initLen stride ops m b).card) ≤
      ∑ c ∈ Finset.range (T.nodeCount 0),
        (T.nodeProbedCells D initLen stride ops 0 c).card := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, add_assoc]
      exact (Nat.add_le_add_left (T.sum_nodeCost_level_add_le D initLen stride ops m) _).trans ih
  have h0 : ∑ c ∈ Finset.range (T.nodeCount 0),
      (T.nodeProbedCells D initLen stride ops 0 c).card ≤ D.seqProbes ops := by
    calc
      ∑ c ∈ Finset.range (T.nodeCount 0),
          (T.nodeProbedCells D initLen stride ops 0 c).card
        ≤ ∑ c ∈ Finset.range (T.nodeCount 0), T.nodeProbes D initLen stride ops 0 c :=
            Finset.sum_le_sum fun _ _ =>
              card_rangeProbedCells_le_rangeProbes D initLen stride ops _ _
      _ ≤ D.seqProbes ops := T.sum_nodeProbes_le_seqProbes D initLen stride ops 0
  exact (Nat.le_add_right _ _).trans ((htel H).trans h0)

/-- **Global LCA probe conservation** across all active internal levels `1, …, T.height` of `T`. -/
theorem sum_nodeCost_le_seqProbes (T : MetaTree)
    (D : IndexedScheme Op Result cells w) (initLen stride : ℕ) (ops : List Op) :
    ∑ ℓ ∈ Finset.range T.height, ∑ b ∈ Finset.range (T.nodeCount (ℓ + 1)),
      T.nodeCost D initLen stride ops ℓ b ≤ D.seqProbes ops :=
  T.sum_nodeCost_le_seqProbes_of_height D initLen stride ops T.height

/-- **Pre-memory qualification soundness** (local symmetric counterpart to post-memory qualification
in [LiLiangYuZhou2023], Section 4.2, pp. 14–15 / PDF pp. 15–16 and Section 4.3, Claim 4.2, p. 17 /
PDF p. 18, which argues the post-memory direction): if cell `j` is probed during child segment `i`
of internal node `(ℓ + 1, b)` and segment `i`'s pre-memory disagrees with the node's start-of-block
memory at `j`, then `j` must also have been probed in an earlier child segment `i' < i`, so
`j ∈ T.badCells D initLen stride ops ℓ b`. -/
theorem mem_badCells_of_seg_preMem_ne_node_preMem (T : MetaTree)
    (D : IndexedScheme Op Result cells w) (initLen stride : ℕ) (ops : List Op)
    (ℓ b : ℕ) (i : Fin (T.fanout (ℓ + 1))) {j : Fin cells}
    (hj : j ∈ T.segProbedCells D initLen stride ops ℓ b i)
    (hne : memAt D ops (initLen + stride * T.nodeStart ℓ (b * T.fanout (ℓ + 1) + i.1)) j ≠
      memAt D ops (initLen + stride * T.nodeStart (ℓ + 1) b) j) :
    j ∈ T.badCells D initLen stride ops ℓ b := by
  let m := T.blockSize ℓ
  let nodeBeg := T.nodeStart (ℓ + 1) b
  let segBeg := T.nodeStart ℓ (b * T.fanout (ℓ + 1) + i.1)
  have hbeg_eq : segBeg = nodeBeg + i.1 * m := T.nodeStart_child ℓ b i.1
  have hle_beg : nodeBeg ≤ segBeg := by omega
  have hj_prev : j ∈ rangeProbedCells D initLen stride ops nodeBeg segBeg := by
    by_contra hnot
    have heq := D.nextMem_runInterval_eq_of_notMem_probedCellsInterval
      (initLen + stride * nodeBeg) (memAt D ops (initLen + stride * nodeBeg))
      (elemSlice initLen stride ops nodeBeg segBeg) hnot
    rw [← memAt_eq_runInterval_elemSlice D initLen stride ops hle_beg] at heq
    exact hne heq
  rw [hbeg_eq, rangeProbedCells_add_mul] at hj_prev
  rcases Finset.mem_biUnion.mp hj_prev with ⟨r, hr, hj_r⟩
  rw [Finset.mem_range] at hr
  let i' : Fin (T.fanout (ℓ + 1)) := ⟨r, hr.trans i.isLt⟩
  have hj_i' : j ∈ T.segProbedCells D initLen stride ops ℓ b i' := by
    have h1 : nodeBeg + r * m = T.nodeStart ℓ (b * T.fanout (ℓ + 1) + i'.1) :=
      (T.nodeStart_child ℓ b r).symm
    have h2 : nodeBeg + (r + 1) * m = T.nodeStop ℓ (b * T.fanout (ℓ + 1) + i'.1) :=
      (T.nodeStop_child ℓ b r).symm
    rwa [h1, h2] at hj_r
  have hne_idx : i' ≠ i := by
    intro heq
    have : r = i.1 := congrArg Fin.val heq
    omega
  exact T.mem_badCells_of_mem_segProbedCells_ne D initLen stride ops ℓ b hne_idx hj_i' hj

/-- Corollary of `mem_badCells_of_seg_preMem_ne_node_preMem` (local symmetric counterpart to
post-memory qualification): on child segment `i`, the number of probed cells whose pre-segment
value differs from the start-of-node memory is at most `|S_A^{[i]} ∩ S_bad|`. -/
theorem card_filter_seg_preMem_ne_node_preMem_le (T : MetaTree)
    (D : IndexedScheme Op Result cells w) (initLen stride : ℕ) (ops : List Op)
    (ℓ b : ℕ) (i : Fin (T.fanout (ℓ + 1))) :
    ((T.segProbedCells D initLen stride ops ℓ b i).filter fun j =>
        memAt D ops (initLen + stride * T.nodeStart ℓ (b * T.fanout (ℓ + 1) + i.1)) j ≠
          memAt D ops (initLen + stride * T.nodeStart (ℓ + 1) b) j).card ≤
      (T.segProbedCells D initLen stride ops ℓ b i ∩
        T.badCells D initLen stride ops ℓ b).card := by
  refine Finset.card_le_card fun j hj => ?_
  rw [Finset.mem_filter] at hj
  exact Finset.mem_inter.mpr
    ⟨hj.1, T.mem_badCells_of_seg_preMem_ne_node_preMem D initLen stride ops ℓ b i hj.1 hj.2⟩

/-- **Post-memory qualification soundness** ([LiLiangYuZhou2023], Section 4.2, pp. 14–15 /
PDF pp. 15–16 and Section 4.3, Claim 4.2, p. 17 / PDF p. 18): if cell `j` is probed during child
segment `i` of internal node `(ℓ + 1, b)` and segment `i`'s post-memory disagrees with the node's
end-of-block memory at `j`, then `j` must also be probed in a later child segment `i' > i`, so
`j ∈ T.badCells D initLen stride ops ℓ b`. -/
theorem mem_badCells_of_seg_postMem_ne_node_postMem (T : MetaTree)
    (D : IndexedScheme Op Result cells w) (initLen stride : ℕ) (ops : List Op)
    (ℓ b : ℕ) (i : Fin (T.fanout (ℓ + 1))) {j : Fin cells}
    (hj : j ∈ T.segProbedCells D initLen stride ops ℓ b i)
    (hne : memAt D ops (initLen + stride * T.nodeStop ℓ (b * T.fanout (ℓ + 1) + i.1)) j ≠
      memAt D ops (initLen + stride * T.nodeStop (ℓ + 1) b) j) :
    j ∈ T.badCells D initLen stride ops ℓ b := by
  let F := T.fanout (ℓ + 1)
  let m := T.blockSize ℓ
  let segStop := T.nodeStop ℓ (b * F + i.1)
  let nodeEnd := T.nodeStop (ℓ + 1) b
  have hsegStop_eq : segStop = T.nodeStart (ℓ + 1) b + (i.1 + 1) * m := T.nodeStop_child ℓ b i.1
  have hnodeEnd_eq : nodeEnd = T.nodeStart (ℓ + 1) b + F * m := by
    simp only [nodeEnd, nodeStart, nodeStop, F, m, T.blockSize_succ ℓ]; ring
  have hstop_eq : nodeEnd = segStop + (F - (i.1 + 1)) * m := by
    have hi : i.1 + 1 ≤ F := i.isLt
    have hmul_le : (i.1 + 1) * m ≤ F * m := Nat.mul_le_mul_right _ hi
    rw [hnodeEnd_eq, hsegStop_eq, Nat.sub_mul]
    omega
  have hle_end : segStop ≤ nodeEnd := by omega
  have hj_rest : j ∈ rangeProbedCells D initLen stride ops segStop nodeEnd := by
    by_contra hnot
    have heq := D.nextMem_runInterval_eq_of_notMem_probedCellsInterval
      (initLen + stride * segStop) (memAt D ops (initLen + stride * segStop))
      (elemSlice initLen stride ops segStop nodeEnd) hnot
    rw [← memAt_eq_runInterval_elemSlice D initLen stride ops hle_end] at heq
    exact hne heq.symm
  rw [hstop_eq, rangeProbedCells_add_mul] at hj_rest
  rcases Finset.mem_biUnion.mp hj_rest with ⟨r, hr, hj_r⟩
  rw [Finset.mem_range] at hr
  let i' : Fin (T.fanout (ℓ + 1)) := ⟨i.1 + 1 + r, by omega⟩
  have hj_i' : j ∈ T.segProbedCells D initLen stride ops ℓ b i' := by
    have h1 : segStop + r * m = T.nodeStart ℓ (b * T.fanout (ℓ + 1) + i'.1) := by
      rw [T.nodeStart_child ℓ b i'.1, hsegStop_eq]
      dsimp only [i', m]; ring
    have h2 : segStop + (r + 1) * m = T.nodeStop ℓ (b * T.fanout (ℓ + 1) + i'.1) := by
      rw [T.nodeStop_child ℓ b i'.1, hsegStop_eq]
      dsimp only [i', m]; ring
    rwa [h1, h2] at hj_r
  have hne_idx : i ≠ i' := by
    intro heq
    have : i.1 = i.1 + 1 + r := congrArg Fin.val heq
    omega
  exact T.mem_badCells_of_mem_segProbedCells_ne D initLen stride ops ℓ b hne_idx hj hj_i'

/-- Corollary of `mem_badCells_of_seg_postMem_ne_node_postMem`: on child segment `i`, the number of
probed cells whose post-segment value differs from the end-of-node memory is at most
`|S_A^{[i]} ∩ S_bad|`. -/
theorem card_filter_seg_postMem_ne_node_postMem_le (T : MetaTree)
    (D : IndexedScheme Op Result cells w) (initLen stride : ℕ) (ops : List Op)
    (ℓ b : ℕ) (i : Fin (T.fanout (ℓ + 1))) :
    ((T.segProbedCells D initLen stride ops ℓ b i).filter fun j =>
        memAt D ops (initLen + stride * T.nodeStop ℓ (b * T.fanout (ℓ + 1) + i.1)) j ≠
          memAt D ops (initLen + stride * T.nodeStop (ℓ + 1) b) j).card ≤
      (T.segProbedCells D initLen stride ops ℓ b i ∩
        T.badCells D initLen stride ops ℓ b).card := by
  refine Finset.card_le_card fun j hj => ?_
  rw [Finset.mem_filter] at hj
  exact Finset.mem_inter.mpr
    ⟨hj.1, T.mem_badCells_of_seg_postMem_ne_node_postMem D initLen stride ops ℓ b i hj.1 hj.2⟩

end MetaTree

/-! ### Mixed memory `mixMem` and segment replay -/

/-- Artificial mixed memory state `C_mix` ([LiLiangYuZhou2023], Section 5.1, p. 22 / PDF p. 23 and
Section 8, p. 29 / PDF p. 30): takes pre-segment memory `m_bef` on `mask` (`S_B ⊆ mask`) and
post-segment memory `m_after` outside `mask`. -/
@[expose] def mixMem (m_bef m_after : Mem cells w) (mask : Finset (Fin cells)) : Mem cells w :=
  fun j => if j ∈ mask then m_bef j else m_after j

@[simp]
theorem mixMem_of_mem {m_bef m_after : Mem cells w} {mask : Finset (Fin cells)} {j : Fin cells}
    (hj : j ∈ mask) :
    mixMem m_bef m_after mask j = m_bef j := by
  simp [mixMem, hj]

@[simp]
theorem mixMem_of_notMem {m_bef m_after : Mem cells w} {mask : Finset (Fin cells)} {j : Fin cells}
    (hj : j ∉ mask) :
    mixMem m_bef m_after mask j = m_after j := by
  simp [mixMem, hj]

/-- **Mixed-memory interval replay:** whenever `D.probedCellsInterval t₀ m_bef ops_B ⊆ mask`,
simulating `ops_B` from `(t₀, mixMem m_bef m_after mask)` produces the exact same transcript,
probe count, probed-cell set `S_B`, and post-memory values on `S_B` as simulating `ops_B` from
`(t₀, m_bef)`. -/
theorem runInterval_mixMem_eq_of_probedCellsInterval_subset (D : IndexedScheme Op Result cells w)
    (t₀ : ℕ) (m_bef m_after : Mem cells w) (mask : Finset (Fin cells)) (ops_B : List Op)
    (hsub : D.probedCellsInterval t₀ m_bef ops_B ⊆ mask) :
    (D.runInterval t₀ (mixMem m_bef m_after mask) ops_B).1 =
        (D.runInterval t₀ m_bef ops_B).1 ∧
      D.probesInterval t₀ (mixMem m_bef m_after mask) ops_B =
        D.probesInterval t₀ m_bef ops_B ∧
      D.probedCellsInterval t₀ (mixMem m_bef m_after mask) ops_B =
        D.probedCellsInterval t₀ m_bef ops_B ∧
      (∀ j ∈ D.probedCellsInterval t₀ m_bef ops_B,
        (D.runInterval t₀ (mixMem m_bef m_after mask) ops_B).2 j =
          (D.runInterval t₀ m_bef ops_B).2 j) :=
  D.runInterval_eq_of_eq_on_probedCellsInterval t₀ ops_B fun _ hj => mixMem_of_mem (hsub hj)

/-- **Non-intersection cell recovery from `mixMem`** ([LiLiangYuZhou2023], Section 5.1, p. 23 /
PDF p. 24 and Section 8, p. 29 / PDF p. 30): if `m_A = (D.runInterval t₀ m_bef ops_A).2` with
probed-cell set `S_A := D.probedCellsInterval t₀ m_bef ops_A`, and `mask` avoids `S_A \ S_B`
(`mask ∩ S_A ⊆ S_B`), then `mixMem m_bef m_A mask` already equals `m_A` at every cell outside
`S_A ∩ S_B`. -/
theorem mixMem_eq_postMem_of_notMem_inter (D : IndexedScheme Op Result cells w)
    (t₀ : ℕ) (m_bef : Mem cells w) (ops_A : List Op)
    (mask S_B : Finset (Fin cells))
    (hsep : mask ∩ D.probedCellsInterval t₀ m_bef ops_A ⊆ S_B)
    {j : Fin cells}
    (hj : j ∉ D.probedCellsInterval t₀ m_bef ops_A ∩ S_B) :
    mixMem m_bef (D.runInterval t₀ m_bef ops_A).2 mask j =
      (D.runInterval t₀ m_bef ops_A).2 j := by
  by_cases hmask : j ∈ mask
  · rw [mixMem_of_mem hmask]
    have hnotA : j ∉ D.probedCellsInterval t₀ m_bef ops_A := by
      intro hjA
      exact hj (Finset.mem_inter.mpr ⟨hjA, hsep (Finset.mem_inter.mpr ⟨hmask, hjA⟩)⟩)
    exact (D.nextMem_runInterval_eq_of_notMem_probedCellsInterval t₀ m_bef ops_A hnotA).symm
  · exact mixMem_of_notMem hmask

end Execution

end Cslib.DataStructure.Dictionary.CellProbe

end

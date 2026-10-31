/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.Karger.Graph
public import Complexity.Computability.WordRAM.Heap
public import Complexity.Computability.WordRAM.Notation
public import Complexity.Computability.WordRAM.Randomized.Structured

/-!
# Workspace-relocatable randomized contraction on the word RAM

Implements Karger's edge-weight-proportional contraction loop (`contractDownTo`) and its companion
row-degree initializer (`computeDegreesAndTotal`) as structured `Cslib.WordRAM` programs over
`Basis.standard` with `16` registers.

All memory accesses are parameterized dynamically by register-held workspace pointers
(`wBase`, `dBase`, `stride`, `activeK`, `targetT`, `totS`), with zero hardcoded memory addresses and
a `Modifies` frame confined to
`Finset.Ico wBase (wBase + stride * k) ∪ Finset.Ico dBase (dBase + k)`.
This allows both repeated-trial amplification (`KargerMinCut`) and recursive stack-allocated calls
in Karger–Stein (`FastCut`) to invoke `contractDownTo` directly at arbitrary memory offsets.

Each contraction from `m + 1` down to `m` active supervertices runs in `O(m)` worst-case
instructions and issues at most `1` `rand` call (`0` calls when total active weight `totS = 0`),
yielding `36 * (k ^ 2 - t ^ 2) + 4` worst-case instructions and at most `k - t` `rand` calls from
`k` down to `t`, with survival probability at least `(t * (t - 1)) / (k * (k - 1))` for any fixed
minimum cut of a connected multigraph.

## Source statements and notation mapping

* **Matrix contraction and survival bound (paraphrase):**
  - `[KargerStein1996]`, Section 2, Lemma 2.1, Theorem 2.2, and Corollary 2.3, and Section 2.1,
    Corollary 2.4 (paraphrase): contracting an `n`-vertex weighted multigraph from `k` down to `t`
    supervertices via edge-weight-proportional selection preserves any fixed minimum cut with
    probability at least `C(t, 2) / C(k, 2) = t * (t - 1) / (k * (k - 1))` (`[Karger1993]`,
    Section 2, Theorem 2.1 and `[MitzenmacherUpfal2017]`, Section 1.5, Theorem 1.8 give the `t = 2`
    case `2 / (n * (n - 1))`).
  - `[KargerStein1996]`, Section 3 ("Implementing the Contraction Algorithm"), Section 3.1,
    Lemma 3.1 and Section 3.2, Corollary 3.2 (paraphrase): maintaining an `n × n` weighted
    adjacency matrix `W` and row-degree array `D[u] = ∑ v, W[u, v]` selects each edge `(u, v)` with
    probability `2 * W[u, v] / ∑ w, D[w]` and executes the Contraction Algorithm in `O(n ^ 2)`
    total time (`O(n)` per contraction step in `[KargerStein1996]`, Section 3.2).
* **Notation mapping and implementation variants:**
  - `C(t, 2) / C(k, 2)` ↔ `((t * (t - 1) : ℕ) : ℝ≥0∞) / (k * (k - 1))` in `contractDownTo_spec`
    and `contractDownToAt_spec`;
  - whereas `[KargerStein1996]`, Section 3.1 draws twice (`u` proportional to `D[u]` then `v`
    proportional to `W[u, v]` via two `Random-Select` calls), our `contractDownTo` uses an
    equivalent single-draw variant: one unit-cost word-RAM `rand` instruction drawing uniformly from
    `{0, …, totS - 1}` (`totS = totalDoubledWeight W`), resolved through linear prefix-sum scans
    `uScan` over `D[0..k)` and `vScan` over `W[u, 0..k)` to select each unordered pair `{u, v}` with
    the same probability `2 * W[u, v] / totS` of Lemma 3.1;
  - whereas `[KargerStein1996]`, Section 3.2 updates rows and columns in `O(n)` per contraction by
    zeroing the removed vertex in place, our `contractDownTo` swap-compacts active slot `k - 1` into
    `v` so each contraction step on `k` active supervertices runs in `O(k)` instructions.

## Main definitions

* `Cslib.Algorithms.WordRAM.Karger.HoldsMatrix`,
  `Cslib.Algorithms.WordRAM.Karger.HoldsWorkspace`,
  `Cslib.Algorithms.WordRAM.Karger.workspaceFootprint`,
  `Cslib.Algorithms.WordRAM.Karger.ContractState`: relocatable memory layout and word-bound
  invariants for an active `k × k` supervertex adjacency matrix with row stride `stride` and row
  degree array at `dBase`.
* `Cslib.Algorithms.WordRAM.Karger.computeDegreesAndTotal`,
  `Cslib.Algorithms.WordRAM.Karger.computeDegreesAndTotalAt`: deterministic `O(k ^ 2)` initializer
  populating `D[0..k)` and `totS`.
* `Cslib.Algorithms.WordRAM.Karger.contractDownTo`,
  `Cslib.Algorithms.WordRAM.Karger.contractDownToAt`: randomized contraction loop from `activeK`
  down to `targetT`.

## Main results

* `Cslib.Algorithms.WordRAM.Karger.computeDegreesAndTotal_exec`: `computeDegreesAndTotal` populates
  `HoldsWorkspace` and `totS = totalDoubledWeight W` within `6 * k ^ 2 + 12 * k + 6` instructions,
  modifying only `Finset.Ico dBase (dBase + k)`.
* `Cslib.Algorithms.WordRAM.Karger.contractDownTo_spec`: joint certificate of `ExecRand`,
  `IsQueryBounded (k - t)`, worst-case step bound `36 * (k ^ 2 - t ^ 2) + 4`, `Modifies` frame,
  contraction invariant `IsContractionOf`, and telescoping cut-survival probability lower bound
  `((t * (t - 1) : ℕ) : ℝ≥0∞) / (k * (k - 1))`.

## References

* [D. R. Karger, *Global Min-cuts in RNC, and Other Ramifications of a Simple Min-Cut
  Algorithm*][Karger1993]
* [D. R. Karger and C. Stein, *A New Approach to the Minimum Cut Problem*][KargerStein1996]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Karger

open scoped ENNReal
open Cslib.WeightedCut
open Cslib.Probability.PMF
open Cslib.WordRAM

/-! ### Register layout (`r = 16`) -/

namespace Reg

/-- Constant `0`. -/
abbrev zero : Fin 16 := 0
/-- Constant `1`. -/
abbrev one : Fin 16 := 1
/-- Base address of active adjacency matrix `W`. -/
abbrev wBase : Fin 16 := 2
/-- Base address of active row-degree array `D`. -/
abbrev dBase : Fin 16 := 3
/-- Row stride (`≥ activeK`) of the matrix buffer at `wBase`. -/
abbrev stride : Fin 16 := 4
/-- Current number `k` of active supervertices. -/
abbrev activeK : Fin 16 := 5
/-- Target number `t` of active supervertices (`2 ≤ t ≤ k`). -/
abbrev targetT : Fin 16 := 6
/-- Current doubled total weight `S = totalDoubledWeight W`. -/
abbrev totS : Fin 16 := 7
/-- Sampled / outer row index `u`. -/
abbrev uReg : Fin 16 := 8
/-- Sampled / inner column index `v`. -/
abbrev vReg : Fin 16 := 9
/-- Loop index for merge and compaction sweeps. -/
abbrev idx : Fin 16 := 10
/-- Sample remainder / scratch address register. -/
abbrev rem : Fin 16 := 11
/-- Scratch pointer 1. -/
abbrev addr1 : Fin 16 := 12
/-- Scratch pointer 2. -/
abbrev addr2 : Fin 16 := 13
/-- Scratch value 1. -/
abbrev val1 : Fin 16 := 14
/-- Scratch value 2. -/
abbrev val2 : Fin 16 := 15

end Reg

/-! ### Relocatable workspace representation and address geometry -/

/-- Memory `mem` stores `W : Fin k → Fin k → ℕ` at base address `wb` with row stride `str`. -/
def HoldsMatrix (mem : ℕ → ℕ) (wb str : ℕ) {k : ℕ} (W : Fin k → Fin k → ℕ) : Prop :=
  ∀ i j : Fin k, mem (wb + i.val * str + j.val) = W i j

/-- Memory `mem` stores `W : Fin k → Fin k → ℕ` at `(wb, str)` and its row degrees `rowDeg W` at
`db`. -/
def HoldsWorkspace (mem : ℕ → ℕ) (wb db str : ℕ) {k : ℕ} (W : Fin k → Fin k → ℕ) : Prop :=
  HoldsMatrix mem wb str W ∧ ∀ i : Fin k, mem (db + i.val) = rowDeg W i

/-- Permitted memory write footprint of an active `k`-supervertex workspace at `(wb, db, str)`. -/
def workspaceFootprint (wb db str k : ℕ) : Finset ℕ :=
  Finset.Ico wb (wb + str * k) ∪ Finset.Ico db (db + k)

/-- Machine-state precondition for `contractDownTo` on `k` active supervertices targeting `t`. -/
structure ContractState (w wb db str k t : ℕ) (W : Fin k → Fin k → ℕ) (x : Data 16) : Prop where
  regs_wBase : x.regs Reg.wBase = wb
  regs_dBase : x.regs Reg.dBase = db
  regs_stride : x.regs Reg.stride = str
  regs_activeK : x.regs Reg.activeK = k
  regs_targetT : x.regs Reg.targetT = t
  regs_totS : x.regs Reg.totS = totalDoubledWeight W
  le_stride : k ≤ str
  disjoint_blocks : wb + str * k ≤ db ∨ db + k ≤ wb
  fits_wEnd : Fits w (wb + str * k)
  fits_dEnd : Fits w (db + k)
  fits_totS : Fits w (totalDoubledWeight W)
  workspace : HoldsWorkspace x.mem wb db str W

theorem matAddr_lt_end {wb str k : ℕ} (hstr : k ≤ str) (i j : Fin k) :
    wb + i.val * str + j.val < wb + str * k := by
  have hi : i.val + 1 ≤ k := i.isLt
  have hj : j.val < str := lt_of_lt_of_le j.isLt hstr
  have hmul : (i.val + 1) * str ≤ k * str := Nat.mul_le_mul_right str hi
  nlinarith

theorem matAddr_mem_Ico {wb str k : ℕ} (hstr : k ≤ str) (i j : Fin k) :
    wb + i.val * str + j.val ∈ Finset.Ico wb (wb + str * k) :=
  Finset.mem_Ico.mpr ⟨by omega, matAddr_lt_end hstr i j⟩

theorem degAddr_mem_Ico {db k : ℕ} (i : Fin k) :
    db + i.val ∈ Finset.Ico db (db + k) :=
  Finset.mem_Ico.mpr ⟨by omega, by omega⟩

theorem matAddr_inj {wb str k : ℕ} (hstr : k ≤ str) {i₁ j₁ i₂ j₂ : Fin k}
    (h : wb + i₁.val * str + j₁.val = wb + i₂.val * str + j₂.val) :
    i₁ = i₂ ∧ j₁ = j₂ := by
  have hj₁ : j₁.val < str := lt_of_lt_of_le j₁.isLt hstr
  have hj₂ : j₂.val < str := lt_of_lt_of_le j₂.isLt hstr
  have hi_eq : i₁.val = i₂.val := by
    rcases lt_trichotomy i₁.val i₂.val with hlt | heq | hgt
    · have hle : (i₁.val + 1) * str ≤ i₂.val * str := Nat.mul_le_mul_right str hlt
      nlinarith
    · exact heq
    · have hle : (i₂.val + 1) * str ≤ i₁.val * str := Nat.mul_le_mul_right str hgt
      nlinarith
  exact ⟨Fin.ext hi_eq, Fin.ext (by nlinarith)⟩

theorem matAddr_ne_degAddr {wb db str k : ℕ} (hstr : k ≤ str)
    (hdisj : wb + str * k ≤ db ∨ db + k ≤ wb) (i j l : Fin k) :
    wb + i.val * str + j.val ≠ db + l.val := by
  have hm := matAddr_lt_end (wb := wb) hstr i j
  have hl := l.isLt
  omega

theorem workspaceFootprint_mono {wb db str k₁ k₂ : ℕ} (hle : k₁ ≤ k₂) :
    workspaceFootprint wb db str k₁ ⊆ workspaceFootprint wb db str k₂ := by
  intro a ha
  simp only [workspaceFootprint, Finset.mem_union, Finset.mem_Ico] at ha ⊢
  have hmul : str * k₁ ≤ str * k₂ := Nat.mul_le_mul_left str hle
  omega

theorem modifies_trans_subset {F F₁ F₂ : Finset ℕ} {m₀ m₁ m₂ : ℕ → ℕ}
    (h₁ : Modifies F₁ m₀ m₁) (h₂ : Modifies F₂ m₁ m₂) (hs₁ : F₁ ⊆ F) (hs₂ : F₂ ⊆ F) :
    Modifies F m₀ m₂ := fun a ha =>
  (h₂ a fun h => ha (hs₂ h)).trans (h₁ a fun h => ha (hs₁ h))

theorem modifies_update_of_mem {F : Finset ℕ} {a : ℕ} (ha : a ∈ F) (m : ℕ → ℕ) (v : ℕ) :
    Modifies F m (Function.update m a v) := by
  intro b hb
  have hne : b ≠ a := fun h => hb (h ▸ ha)
  exact Function.update_of_ne hne v m

private theorem modifies_step_update {F : Finset ℕ} {m₁ m₂ : ℕ → ℕ} {a : ℕ}
    (h : Modifies F m₁ m₂) (ha : a ∈ F) (v : ℕ) :
    Modifies F m₁ (Function.update m₂ a v) :=
  modifies_trans_subset h (modifies_update_of_mem ha m₂ v) Finset.Subset.rfl Finset.Subset.rfl

/-! ### Prefix-sum step identities for `degBefore` and `weightBefore` -/

private theorem degBefore_zero {k : ℕ} (hk : 0 < k) (W : Fin k → Fin k → ℕ) :
    degBefore W ⟨0, hk⟩ = 0 := by
  unfold degBefore
  have hempty : (Finset.univ.filter fun a : Fin k => a < ⟨0, hk⟩) = ∅ := by
    ext a
    simp [Fin.lt_def]
  rw [hempty, Finset.sum_empty]

private theorem degBefore_succ {k i : ℕ} (hi : i + 1 < k) (W : Fin k → Fin k → ℕ) :
    degBefore W ⟨i + 1, hi⟩ = degBefore W ⟨i, by omega⟩ + rowDeg W ⟨i, by omega⟩ := by
  unfold degBefore
  let u : Fin k := ⟨i, by omega⟩
  have hsplit : (Finset.univ.filter fun a : Fin k => a < ⟨i + 1, hi⟩) =
      insert u (Finset.univ.filter fun a : Fin k => a < u) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.lt_def, Fin.ext_iff, u]
    omega
  have hnotmem : u ∉ Finset.univ.filter fun a : Fin k => a < u := by simp [u]
  rw [hsplit, Finset.sum_insert hnotmem, add_comm]

private theorem degBefore_full {k : ℕ} (W : Fin k → Fin k → ℕ) :
    (∑ a ∈ Finset.univ.filter (fun a : Fin k => a.val < k), rowDeg W a) =
      totalDoubledWeight W := by
  unfold totalDoubledWeight
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext a
  simp

private theorem weightBefore_zero {k : ℕ} (hk : 0 < k) (W : Fin k → Fin k → ℕ) (u : Fin k) :
    weightBefore W u ⟨0, hk⟩ = 0 := by
  unfold weightBefore
  have hempty : (Finset.univ.filter fun b : Fin k => b < ⟨0, hk⟩) = ∅ := by
    ext b
    simp [Fin.lt_def]
  rw [hempty, Finset.sum_empty]

private theorem weightBefore_succ {k j : ℕ} (hj : j + 1 < k) (W : Fin k → Fin k → ℕ)
    (u : Fin k) :
    weightBefore W u ⟨j + 1, hj⟩ = weightBefore W u ⟨j, by omega⟩ + W u ⟨j, by omega⟩ := by
  unfold weightBefore
  let v : Fin k := ⟨j, by omega⟩
  have hsplit : (Finset.univ.filter fun b : Fin k => b < ⟨j + 1, hj⟩) =
      insert v (Finset.univ.filter fun b : Fin k => b < v) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.lt_def, Fin.ext_iff, v]
    omega
  have hnotmem : v ∉ Finset.univ.filter fun b : Fin k => b < v := by simp [v]
  rw [hsplit, Finset.sum_insert hnotmem, add_comm]

/-! ### Part 1: Deterministic `O(k ^ 2)` row-degree and total-weight initializer -/

section ComputeDegrees

open Reg

/-- Inner loop body accumulating `W[u, v]` into `val1`. -/
def degInnerBody : Code .standard 16 := ram[
  addr2 ← addr1 + vReg;
  val2 ← *addr2;
  val1 ← val1 + val2;
  vReg ← vReg + one
]

/-- Outer loop body computing `D[u] = rowDeg W u` and adding it to `totS`. -/
def degOuterBody : Code .standard 16 := ram[
  val2 ← uReg * stride;
  addr1 ← wBase + val2;
  val1 ← #0;
  vReg ← #0;
  while vReg < activeK do [ ⟪degInnerBody⟫ ];
  addr2 ← dBase + uReg;
  *addr2 ← val1;
  totS ← totS + val1;
  uReg ← uReg + one
]

/-- Compute all row degrees `D[0..k)` at `dBase` and `totS = totalDoubledWeight W` from `W` at
`(wBase, stride)` in `6 * k ^ 2 + 12 * k + 6` instructions. -/
def computeDegreesAndTotal : Code .standard 16 := ram[
  zero ← #0;
  one ← #1;
  totS ← #0;
  uReg ← #0;
  while uReg < activeK do [ ⟪degOuterBody⟫ ]
]

private def partialRowSum {k : ℕ} (W : Fin k → Fin k → ℕ) (u : Fin k) (j : ℕ) : ℕ :=
  ∑ b ∈ Finset.univ.filter (fun b : Fin k => b.val < j), W u b

private theorem partialRowSum_zero {k : ℕ} (W : Fin k → Fin k → ℕ) (u : Fin k) :
    partialRowSum W u 0 = 0 := by
  unfold partialRowSum
  have hempty : (Finset.univ.filter fun b : Fin k => b.val < 0) = ∅ := by ext b; simp
  rw [hempty, Finset.sum_empty]

private theorem partialRowSum_succ {k : ℕ} (W : Fin k → Fin k → ℕ) (u : Fin k)
    {j : ℕ} (hj : j < k) :
    partialRowSum W u (j + 1) = partialRowSum W u j + W u ⟨j, hj⟩ := by
  unfold partialRowSum
  let v : Fin k := ⟨j, hj⟩
  have hsplit : (Finset.univ.filter fun b : Fin k => b.val < j + 1) =
      insert v (Finset.univ.filter fun b : Fin k => b.val < j) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, v]
    omega
  have hnotmem : v ∉ Finset.univ.filter fun b : Fin k => b.val < j := by simp [v]
  rw [hsplit, Finset.sum_insert hnotmem, add_comm]

private theorem partialRowSum_full {k : ℕ} (W : Fin k → Fin k → ℕ) (u : Fin k) :
    partialRowSum W u k = rowDeg W u := by
  unfold partialRowSum rowDeg
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext b
  simp

private theorem partialRowSum_le_rowDeg {k : ℕ} (W : Fin k → Fin k → ℕ) (u : Fin k) (j : ℕ) :
    partialRowSum W u j ≤ rowDeg W u :=
  Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _

private def partialDegSum {k : ℕ} (W : Fin k → Fin k → ℕ) (i : ℕ) : ℕ :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin k => a.val < i), rowDeg W a

private theorem partialDegSum_zero {k : ℕ} (W : Fin k → Fin k → ℕ) :
    partialDegSum W 0 = 0 := by
  unfold partialDegSum
  have hempty : (Finset.univ.filter fun a : Fin k => a.val < 0) = ∅ := by ext a; simp
  rw [hempty, Finset.sum_empty]

private theorem partialDegSum_succ {k : ℕ} (W : Fin k → Fin k → ℕ) {i : ℕ} (hi : i < k) :
    partialDegSum W (i + 1) = partialDegSum W i + rowDeg W ⟨i, hi⟩ := by
  unfold partialDegSum
  let u : Fin k := ⟨i, hi⟩
  have hsplit : (Finset.univ.filter fun a : Fin k => a.val < i + 1) =
      insert u (Finset.univ.filter fun a : Fin k => a.val < i) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, u]
    omega
  have hnotmem : u ∉ Finset.univ.filter fun a : Fin k => a.val < i := by simp [u]
  rw [hsplit, Finset.sum_insert hnotmem, add_comm]

private theorem partialDegSum_full {k : ℕ} (W : Fin k → Fin k → ℕ) :
    partialDegSum W k = totalDoubledWeight W :=
  degBefore_full W

private theorem partialDegSum_le {k : ℕ} (W : Fin k → Fin k → ℕ) (i : ℕ) :
    partialDegSum W i ≤ totalDoubledWeight W :=
  Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _

/-- `computeDegreesAndTotal` initializes `D[0..k)` and `totS` in `6 * k ^ 2 + 12 * k + 6`
instructions while modifying only `Finset.Ico db (db + k)`. -/
theorem computeDegreesAndTotal_exec {w wb db str k : ℕ} {W : Fin k → Fin k → ℕ} {x : Data 16}
    (hwBase : x.regs wBase = wb) (hdBase : x.regs dBase = db)
    (hstride : x.regs stride = str) (hactiveK : x.regs activeK = k)
    (hstr : k ≤ str) (hdisj : wb + str * k ≤ db ∨ db + k ≤ wb)
    (h1 : Fits w 1) (hwEnd : Fits w (wb + str * k)) (hdEnd : Fits w (db + k))
    (htot : Fits w (totalDoubledWeight W)) (hmat : HoldsMatrix x.mem wb str W) :
    ∃ y, ExecWithin w computeDegreesAndTotal x y (6 * k ^ 2 + 12 * k + 6) ∧
      HoldsWorkspace y.mem wb db str W ∧
      Modifies (Finset.Ico db (db + k)) x.mem y.mem ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧
      y.regs wBase = wb ∧ y.regs dBase = db ∧ y.regs stride = str ∧
      y.regs activeK = k ∧ y.regs targetT = x.regs targetT ∧
      y.regs totS = totalDoubledWeight W := by
  let OuterInv (y : Data 16) : Prop :=
    y.regs zero = 0 ∧ y.regs one = 1 ∧
    y.regs wBase = wb ∧ y.regs dBase = db ∧ y.regs stride = str ∧
    y.regs activeK = k ∧ y.regs targetT = x.regs targetT ∧
    y.regs uReg ≤ k ∧
    y.regs totS = partialDegSum W (y.regs uReg) ∧
    HoldsMatrix y.mem wb str W ∧
    Modifies (Finset.Ico db (db + k)) x.mem y.mem ∧
    ∀ a : Fin k, a.val < y.regs uReg → y.mem (db + a.val) = rowDeg W a
  have houter_body : ∀ y, OuterInv y → (Cond.lt uReg activeK).Holds y →
      ∃ z, ExecWithin w degOuterBody y z (6 * k + 10) ∧ OuterInv z ∧
        k - z.regs uReg < k - y.regs uReg := by
    intro y hy hc
    rcases hy with ⟨hy0, hy1, hywb, hydb, hystr, hyk, hyt, hyu_le, hytot, hymat, hymod, hydeg⟩
    have hu_lt : y.regs uReg < k := by simpa [hyk] using hc
    let u : Fin k := ⟨y.regs uReg, hu_lt⟩
    have hmul_fit : Fits w (u.val * str) :=
      hwEnd.of_le (by
        have : u.val * str ≤ k * str := Nat.mul_le_mul_right str (Nat.le_of_lt u.isLt)
        nlinarith)
    have hrow_fit : Fits w (wb + u.val * str) :=
      hwEnd.of_le (by
        have : u.val * str ≤ k * str := Nat.mul_le_mul_right str (Nat.le_of_lt u.isLt)
        nlinarith)
    let y_pre := (((y.set val2 (u.val * str)).set addr1 (wb + u.val * str)).set val1 0).set vReg 0
    have hpre_exec : ExecWithin w
        ram[val2 ← uReg * stride; addr1 ← wBase + val2; val1 ← #0; vReg ← #0] y y_pre 4 := by
      have e1 : ExecWithin w ram[val2 ← uReg * stride] y (y.set val2 (u.val * str)) 1 := by
        simpa [BinOp.eval, hystr] using
          ExecWithin.bin (f := .mul) (d := val2) (i := uReg) (j := stride) (x := y)
            (by simpa [BinOp.eval, hystr] using hmul_fit)
      have e2 : ExecWithin w ram[addr1 ← wBase + val2] (y.set val2 (u.val * str))
          ((y.set val2 (u.val * str)).set addr1 (wb + u.val * str)) 1 := by
        have hwb' : (y.set val2 (u.val * str)).regs wBase = wb := by
          simpa +decide [Function.update_apply] using hywb
        simpa [BinOp.eval, hwb'] using
          ExecWithin.bin (f := .add) (d := addr1) (i := wBase) (j := val2)
            (x := y.set val2 (u.val * str))
            (by simpa [BinOp.eval, hwb'] using hrow_fit)
      have e3 := ExecWithin.const (B := .standard) (d := val1)
        (x := (y.set val2 (u.val * str)).set addr1 (wb + u.val * str)) (fits_zero w)
      have e4 := ExecWithin.const (B := .standard) (d := vReg)
        (x := ((y.set val2 (u.val * str)).set addr1 (wb + u.val * str)).set val1 0) (fits_zero w)
      exact (e1.seq (e2.seq (e3.seq e4))).mono (by omega)
    let InnerInv (q : Data 16) : Prop :=
      q.regs zero = 0 ∧ q.regs one = 1 ∧
      q.regs wBase = wb ∧ q.regs dBase = db ∧ q.regs stride = str ∧
      q.regs activeK = k ∧ q.regs targetT = x.regs targetT ∧
      q.regs uReg = u.val ∧ q.regs totS = y.regs totS ∧
      q.regs addr1 = wb + u.val * str ∧
      q.regs vReg ≤ k ∧
      q.regs val1 = partialRowSum W u (q.regs vReg) ∧
      q.mem = y.mem
    have hinner_init : InnerInv y_pre := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
      · simpa +decide [y_pre, Function.update_apply] using hy0
      · simpa +decide [y_pre, Function.update_apply] using hy1
      · simpa +decide [y_pre, Function.update_apply] using hywb
      · simpa +decide [y_pre, Function.update_apply] using hydb
      · simpa +decide [y_pre, Function.update_apply] using hystr
      · simpa +decide [y_pre, Function.update_apply] using hyk
      · simpa +decide [y_pre, Function.update_apply] using hyt
      · simp +decide [y_pre, u]
      · simp +decide [y_pre]
      · simp +decide [y_pre]
      · simp +decide [y_pre]
      · simp +decide [y_pre, partialRowSum_zero]
    have hinner_body : ∀ q, InnerInv q → (Cond.lt vReg activeK).Holds q →
        ∃ q', ExecWithin w degInnerBody q q' 4 ∧ InnerInv q' ∧
          k - q'.regs vReg < k - q.regs vReg := by
      intro q hq hvc
      rcases hq with ⟨hq0, hq1, hqwb, hqdb, hqstr, hqk, hqt, hqu, hqtot, hqa1, hqv_le, hqval1,
        hqmem⟩
      have hv_lt : q.regs vReg < k := by simpa [hqk] using hvc
      let v : Fin k := ⟨q.regs vReg, hv_lt⟩
      have hcell_fit : Fits w (wb + u.val * str + v.val) :=
        hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr u v))
      have hsum_eq : partialRowSum W u v.val + W u v = partialRowSum W u (v.val + 1) :=
        (partialRowSum_succ W u hv_lt).symm
      have hsum_fit : Fits w (partialRowSum W u (v.val + 1)) :=
        htot.of_le ((partialRowSum_le_rowDeg W u (v.val + 1)).trans
          (rowDeg_le_totalDoubledWeight W u))
      have hv_inc_fit : Fits w (v.val + 1) := hdEnd.of_le (by omega)
      have hread_cell : q.mem (wb + u.val * str + v.val) = W u v := by
        rw [hqmem]
        exact hymat u v
      let q₁ := q.set addr2 (wb + u.val * str + v.val)
      let q₂ := q₁.set val2 (W u v)
      let q₃ := q₂.set val1 (partialRowSum W u (v.val + 1))
      let q₄ := q₃.set vReg (v.val + 1)
      have s1 : ExecWithin w ram[addr2 ← addr1 + vReg] q q₁ 1 := by
        simpa [q₁, BinOp.eval, hqa1, v] using
          ExecWithin.bin (f := .add) (d := addr2) (i := addr1) (j := vReg) (x := q)
            (by simpa [BinOp.eval, hqa1, v] using hcell_fit)
      have s2 : ExecWithin (B := .standard) w ram[val2 ← *addr2] q₁ q₂ 1 := by
        have ha2 : q₁.regs addr2 = wb + u.val * str + v.val := by simp [q₁]
        have hm1 : q₁.mem (wb + u.val * str + v.val) = W u v := hread_cell
        simpa only [q₂, ha2, hm1] using
          ExecWithin.load (B := .standard) (w := w) (d := val2) (a := addr2) (x := q₁)
      have s3 : ExecWithin w ram[val1 ← val1 + val2] q₂ q₃ 1 := by
        have hv1 : q₂.regs val1 = partialRowSum W u v.val := by
          simpa +decide [q₂, q₁, Function.update_apply] using hqval1
        have hv2 : q₂.regs val2 = W u v := by simp [q₂]
        simpa [q₃, BinOp.eval, hv1, hv2, hsum_eq] using
          ExecWithin.bin (f := .add) (d := val1) (i := val1) (j := val2) (x := q₂)
            (by simpa [BinOp.eval, hv1, hv2, hsum_eq] using hsum_fit)
      have s4 : ExecWithin w ram[vReg ← vReg + one] q₃ q₄ 1 := by
        have hvr : q₃.regs vReg = v.val := by simp +decide [q₃, q₂, q₁, v]
        have ho : q₃.regs one = 1 := by
          simpa +decide [q₃, q₂, q₁, Function.update_apply] using hq1
        simpa [q₄, BinOp.eval, hvr, ho] using
          ExecWithin.bin (f := .add) (d := vReg) (i := vReg) (j := one) (x := q₃)
            (by simpa [BinOp.eval, hvr, ho] using hv_inc_fit)
      refine ⟨q₄, (s1.seq (s2.seq (s3.seq s4))).mono (by omega), ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hqmem⟩
        · simpa +decide [q₄, q₃, q₂, q₁, Function.update_apply] using hq0
        · simpa +decide [q₄, q₃, q₂, q₁, Function.update_apply] using hq1
        · simpa +decide [q₄, q₃, q₂, q₁, Function.update_apply] using hqwb
        · simpa +decide [q₄, q₃, q₂, q₁, Function.update_apply] using hqdb
        · simpa +decide [q₄, q₃, q₂, q₁, Function.update_apply] using hqstr
        · simpa +decide [q₄, q₃, q₂, q₁, Function.update_apply] using hqk
        · simpa +decide [q₄, q₃, q₂, q₁, Function.update_apply] using hqt
        · simpa +decide [q₄, q₃, q₂, q₁, Function.update_apply] using hqu
        · simpa +decide [q₄, q₃, q₂, q₁, Function.update_apply] using hqtot
        · simpa +decide [q₄, q₃, q₂, q₁, Function.update_apply] using hqa1
        · simp only [q₄, Data.set_regs, Function.update_self]
          exact Nat.succ_le_of_lt hv_lt
        · simp +decide [q₄, q₃]
      · simp only [q₄, Data.set_regs, Function.update_self]
        dsimp [v]; omega
    obtain ⟨q_end, hloop_in, hq_end, hvc_end⟩ :=
      ExecWithin.loop_invariant InnerInv (fun q => k - q.regs vReg) hinner_body hinner_init
    rcases hq_end with ⟨hq0, hq1, hqwb, hqdb, hqstr, hqk, hqt, hqu, hqtot, _, hqv_le, hqval1,
      hqmem⟩
    have hv_end : q_end.regs vReg = k := by
      simp only [Cond.holds_lt, hqk] at hvc_end
      omega
    have hval1_deg : q_end.regs val1 = rowDeg W u := by
      rw [hqval1, hv_end, partialRowSum_full]
    have hd_addr_fit : Fits w (db + u.val) := hdEnd.of_le (by omega)
    have htot_next_eq : y.regs totS + rowDeg W u = partialDegSum W (u.val + 1) := by
      rw [hytot, ← partialDegSum_succ W hu_lt]
    have htot_next_fit : Fits w (partialDegSum W (u.val + 1)) :=
      htot.of_le (partialDegSum_le W (u.val + 1))
    have hu_inc_fit : Fits w (u.val + 1) := hdEnd.of_le (by omega)
    let z₁ := q_end.set addr2 (db + u.val)
    let z₂ := z₁.write (db + u.val) (rowDeg W u)
    let z₃ := z₂.set totS (partialDegSum W (u.val + 1))
    let z₄ := z₃.set uReg (u.val + 1)
    have p1 : ExecWithin w ram[addr2 ← dBase + uReg] q_end z₁ 1 := by
      simpa [z₁, BinOp.eval, hqdb, hqu] using
        ExecWithin.bin (f := .add) (d := addr2) (i := dBase) (j := uReg) (x := q_end)
          (by simpa [BinOp.eval, hqdb, hqu] using hd_addr_fit)
    have p2 : ExecWithin (B := .standard) w ram[*addr2 ← val1] z₁ z₂ 1 := by
      have ha2 : z₁.regs addr2 = db + u.val := by simp [z₁]
      have hv1 : z₁.regs val1 = rowDeg W u := by
        simpa +decide [z₁, Function.update_apply] using hval1_deg
      simpa [z₂, ha2, hv1] using
        ExecWithin.store (B := .standard) (w := w) (a := addr2) (s := val1) (x := z₁)
    have p3 : ExecWithin w ram[totS ← totS + val1] z₂ z₃ 1 := by
      have hts : z₂.regs totS = y.regs totS := by
        simpa +decide [z₂, z₁, Function.update_apply] using hqtot
      have hv1 : z₂.regs val1 = rowDeg W u := by
        simpa +decide [z₂, z₁, Function.update_apply] using hval1_deg
      simpa [z₃, BinOp.eval, hts, hv1, htot_next_eq] using
        ExecWithin.bin (f := .add) (d := totS) (i := totS) (j := val1) (x := z₂)
          (by simpa [BinOp.eval, hts, hv1, htot_next_eq] using htot_next_fit)
    have p4 : ExecWithin w ram[uReg ← uReg + one] z₃ z₄ 1 := by
      have hur : z₃.regs uReg = u.val := by
        simpa +decide [z₃, z₂, z₁, Function.update_apply] using hqu
      have ho : z₃.regs one = 1 := by
        simpa +decide [z₃, z₂, z₁, Function.update_apply] using hq1
      simpa [z₄, BinOp.eval, hur, ho] using
        ExecWithin.bin (f := .add) (d := uReg) (i := uReg) (j := one) (x := z₃)
          (by simpa [BinOp.eval, hur, ho] using hu_inc_fit)
    have hbody_exec : ExecWithin w degOuterBody y z₄ (6 * k + 10) := by
      unfold degOuterBody
      have hpre_v : y_pre.regs vReg = 0 := by simp [y_pre]
      have hloop_bound : (k - y_pre.regs vReg) * (4 + 2) + 2 ≤ 6 * k + 2 := by
        rw [hpre_v]
        omega
      -- Reassociate `degOuterBody` with `hpre_exec`, `hloop_in`, and `p1..p4`.
      rcases hpre_exec with ⟨n1, hn1, e_pre⟩
      rcases e_pre with _ | @⟨_, _, _, y1, _, _, _, e1, e_rest1⟩
      rcases e_rest1 with _ | @⟨_, _, _, y2, _, _, _, e2, e_rest2⟩
      rcases e_rest2 with _ | @⟨_, _, _, y3, _, _, _, e3, e4⟩
      exact ((e1.within).seq ((e2.within).seq ((e3.within).seq ((e4.within).seq
        ((hloop_in.mono hloop_bound).seq (p1.seq (p2.seq (p3.seq p4)))))))).mono (by omega)
    refine ⟨z₄, hbody_exec, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa +decide [z₄, z₃, z₂, z₁, Function.update_apply] using hq0
      · simpa +decide [z₄, z₃, z₂, z₁, Function.update_apply] using hq1
      · simpa +decide [z₄, z₃, z₂, z₁, Function.update_apply] using hqwb
      · simpa +decide [z₄, z₃, z₂, z₁, Function.update_apply] using hqdb
      · simpa +decide [z₄, z₃, z₂, z₁, Function.update_apply] using hqstr
      · simpa +decide [z₄, z₃, z₂, z₁, Function.update_apply] using hqk
      · simpa +decide [z₄, z₃, z₂, z₁, Function.update_apply] using hqt
      · simp +decide [z₄]
      · simp +decide [z₄, z₃]
      · intro i j
        simp only [z₄, z₃, z₂, z₁, Data.set_mem, Data.write_mem, hqmem]
        rw [Function.update_of_ne (matAddr_ne_degAddr hstr hdisj i j u)]
        exact hymat i j
      · simp only [z₄, z₃, z₂, z₁, Data.set_mem, Data.write_mem, hqmem]
        exact modifies_trans_subset hymod
          (modifies_update_of_mem (degAddr_mem_Ico u) y.mem (rowDeg W u))
          Finset.Subset.rfl Finset.Subset.rfl
      · intro a ha
        simp only [z₄, z₃, z₂, z₁, Data.set_regs, Data.set_mem, Data.write_mem,
          Function.update_self, hqmem] at ha ⊢
        by_cases hau : a = u
        · subst hau
          simp
        · have hne : db + a.val ≠ db + u.val := fun h => hau (Fin.ext (by omega))
          rw [Function.update_of_ne hne]
          have hu_val : u.val = y.regs uReg := rfl
          exact hydeg a (by have := Fin.val_ne_of_ne hau; omega)
    · simp only [z₄, Data.set_regs, Function.update_self, u]
      omega
  let x₀ := (((x.set zero 0).set one 1).set totS 0).set uReg 0
  have hx₀ : OuterInv x₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmat, Modifies.refl _ _, ?_⟩
    · simp +decide [x₀]
    · simp +decide [x₀]
    · simpa +decide [x₀, Function.update_apply] using hwBase
    · simpa +decide [x₀, Function.update_apply] using hdBase
    · simpa +decide [x₀, Function.update_apply] using hstride
    · simpa +decide [x₀, Function.update_apply] using hactiveK
    · simp +decide [x₀]
    · simp +decide [x₀]
    · simp +decide [x₀, partialDegSum_zero]
    · intro a ha
      simp +decide [x₀] at ha
  obtain ⟨y_end, hloop_out, hy_end, huc_end⟩ :=
    ExecWithin.loop_invariant OuterInv (fun y => k - y.regs uReg) houter_body hx₀
  rcases hy_end with ⟨hy0, hy1, hywb, hydb, hystr, hyk, hyt, hyu_le, hytot, hymat, hymod, hydeg⟩
  have hu_end : y_end.regs uReg = k := by
    simp only [Cond.holds_lt, hyk] at huc_end
    omega
  refine ⟨y_end, ?_, ⟨hymat, fun a => hydeg a (hu_end ▸ a.isLt)⟩, hymod,
    hy0, hy1, hywb, hydb, hystr, hyk, hyt, ?_⟩
  · unfold computeDegreesAndTotal
    have s1 := ExecWithin.const (B := .standard) (d := zero) (x := x) (fits_zero w)
    have s2 := ExecWithin.const (B := .standard) (d := one) (x := x.set zero 0) h1
    have s3 := ExecWithin.const (B := .standard) (d := totS)
      (x := (x.set zero 0).set one 1) (fits_zero w)
    have s4 := ExecWithin.const (B := .standard) (d := uReg)
      (x := ((x.set zero 0).set one 1).set totS 0) (fits_zero w)
    have hx₀_u : x₀.regs uReg = 0 := by simp [x₀]
    refine (s1.seq (s2.seq (s3.seq (s4.seq hloop_out)))).mono ?_
    rw [hx₀_u, Nat.sub_zero]
    nlinarith
  · rw [hytot, hu_end, partialDegSum_full]

end ComputeDegrees

/-! ### Part 2: Single contraction step and `contractDownTo` -/

section Contract

open Reg

/-- Loop body for scanning row degrees `D[u]` until `rem ≤ D[u]`. -/
def uScanBody : Code .standard 16 := ram[
  rem ← rem - val1;
  uReg ← uReg + one;
  addr1 ← dBase + uReg;
  val1 ← *addr1
]

/-- Scan `u = 0, 1, …` from `rem = r + 1` to locate the sampled row `u` and row offset. -/
def uScan : Code .standard 16 := ram[
  rem ← rem + one;
  uReg ← #0;
  addr1 ← dBase + uReg;
  val1 ← *addr1;
  while val1 < rem do [ ⟪uScanBody⟫ ]
]

/-- Loop body for scanning row `W[u, v]` until `rem ≤ W[u, v]`. -/
def vScanBody : Code .standard 16 := ram[
  rem ← rem - val1;
  vReg ← vReg + one;
  addr2 ← addr1 + vReg;
  val1 ← *addr2
]

/-- Scan `v = 0, 1, …` along row `u` to locate the sampled column `v` (`u ≠ v`) with
`val1 = W u v`. -/
def vScan : Code .standard 16 := ram[
  val2 ← uReg * stride;
  addr1 ← wBase + val2;
  vReg ← #0;
  addr2 ← addr1 + vReg;
  val1 ← *addr2;
  while val1 < rem do [ ⟪vScanBody⟫ ]
]

/-- Update `totS`, zero `W[u, v]`, and update `D[u]` and `D[v]` for merging `v` into `u`. -/
def phaseADegrees : Code .standard 16 := ram[
  totS ← totS - val1;
  totS ← totS - val1;
  *addr2 ← zero;
  addr2 ← dBase + uReg;
  val2 ← *addr2;
  val2 ← val2 - val1;
  addr1 ← dBase + vReg;
  rem ← *addr1;
  rem ← rem - val1;
  val2 ← val2 + rem;
  *addr2 ← val2;
  *addr1 ← zero
]

/-- Set `addr1 = wBase + u * stride`, `addr2 = wBase + v * stride`, zero `W[v, u]`, and set
`idx = 0`. -/
def phaseAPtrs : Code .standard 16 := ram[
  val2 ← uReg * stride;
  addr1 ← wBase + val2;
  val2 ← vReg * stride;
  addr2 ← wBase + val2;
  rem ← addr2 + uReg;
  *rem ← zero;
  idx ← #0
]

/-- Redirect edges between `v` and `idx` (`idx ∉ {u, v}`) into `u` and zero `v`'s entries. -/
def mergeUpdate : Code .standard 16 := ram[
  rem ← addr2 + idx;
  val1 ← *rem;
  *rem ← zero;
  rem ← addr1 + idx;
  val2 ← *rem;
  val2 ← val2 + val1;
  *rem ← val2;
  val1 ← idx * stride;
  val1 ← wBase + val1;
  rem ← val1 + vReg;
  *rem ← zero;
  rem ← val1 + uReg;
  *rem ← val2
]

/-- Single iteration of the Phase A merge sweep over `idx < activeK`. -/
def mergeBody : Code .standard 16 := ram[
  if idx = uReg then [
    idx ← idx + one
  ] else [
    if idx = vReg then [
      idx ← idx + one
    ] else [
      ⟪mergeUpdate⟫;
      idx ← idx + one
    ]
  ]
]

/-- Copy `(activeK, idx)` and `(idx, activeK)` into `(vReg, idx)` and `(idx, vReg)` for
`idx ≠ v`. -/
def compactUpdate : Code .standard 16 := ram[
  rem ← addr1 + idx;
  val1 ← *rem;
  rem ← addr2 + idx;
  *rem ← val1;
  val2 ← idx * stride;
  val2 ← wBase + val2;
  rem ← val2 + vReg;
  *rem ← val1
]

/-- Single iteration of the Phase B swap-compaction sweep over `idx < m`. -/
def compactBody : Code .standard 16 := ram[
  if idx = vReg then [
    idx ← idx + one
  ] else [
    ⟪compactUpdate⟫;
    idx ← idx + one
  ]
]

/-- Setup for Phase B when `v < m`: copy `D[m]` to `D[v]` and compute row pointers for `m` and
`v`. -/
def compactSetup : Code .standard 16 := ram[
  addr1 ← dBase + activeK;
  val1 ← *addr1;
  addr2 ← dBase + vReg;
  *addr2 ← val1;
  val1 ← activeK * stride;
  addr1 ← wBase + val1;
  val1 ← vReg * stride;
  addr2 ← wBase + val1;
  idx ← #0
]

/-- Deterministic continuation of a positive-weight contraction step once `rem` holds `r < totS`. -/
def postRandStep : Code .standard 16 := ram[
  ⟪uScan⟫;
  ⟪vScan⟫;
  ⟪phaseADegrees⟫;
  ⟪phaseAPtrs⟫;
  while idx < activeK do [ ⟪mergeBody⟫ ];
  activeK ← activeK - one;
  if vReg < activeK then [
    ⟪compactSetup⟫;
    while idx < activeK do [ ⟪compactBody⟫ ]
  ] else [
    idx ← #0
  ]
]

/-- One supervertex contraction step: deterministic merge when `totS = 0`, and edge-proportional
random contraction otherwise. -/
def contractStep : Code .standard 16 := ram[
  if totS = zero then [
    activeK ← activeK - one
  ] else [
    val1 ← totS - one;
    rem ← rand val1;
    ⟪postRandStep⟫
  ]
]

/-- Workspace-relocatable randomized contraction loop from `activeK` down to `targetT`. -/
def contractDownTo : Code .standard 16 := ram[
  zero ← #0;
  one ← #1;
  while targetT < activeK do [ ⟪contractStep⟫ ]
]

/-! #### Intermediate matrix invariants for `mergeLoop` and `compactLoop` -/

private def mergeStepMatrix {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k) (idx : ℕ)
    (i j : Fin k) : ℕ :=
  if ((i = u ∨ i = v) ∧ j ≠ u ∧ j ≠ v ∧ idx ≤ j.val) ∨
     ((j = u ∨ j = v) ∧ i ≠ u ∧ i ≠ v ∧ idx ≤ i.val) then
    W i j
  else
    mergePair W u v i j

private theorem mergeStepMatrix_zero {k : ℕ} {W : Fin k → Fin k → ℕ} (hW : IsMultigraph W)
    {u v : Fin k} (i j : Fin k) :
    mergeStepMatrix W u v 0 i j =
      if (i = u ∧ j = v) ∨ (i = v ∧ j = u) then 0 else W i j := by
  unfold mergeStepMatrix
  simp only [Nat.zero_le, and_true]
  by_cases hiu : i = u <;> by_cases hiv : i = v <;>
    by_cases hju : j = u <;> by_cases hjv : j = v
  all_goals simp_all [mergePair, hW.2]

private theorem mergeStepMatrix_full {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k)
    (i j : Fin k) :
    mergeStepMatrix W u v k i j = mergePair W u v i j := by
  unfold mergeStepMatrix
  have hj : ¬ (k ≤ j.val) := Nat.not_le_of_lt j.isLt
  have hi : ¬ (k ≤ i.val) := Nat.not_le_of_lt i.isLt
  simp [hj, hi]

private theorem mergeStepMatrix_step_eq_of_mem {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k)
    {c : ℕ} (hc : c = u.val ∨ c = v.val) (i j : Fin k) :
    mergeStepMatrix W u v (c + 1) i j = mergeStepMatrix W u v c i j := by
  unfold mergeStepMatrix
  have h1 : ((i = u ∨ i = v) ∧ j ≠ u ∧ j ≠ v ∧ c + 1 ≤ j.val) ↔
      ((i = u ∨ i = v) ∧ j ≠ u ∧ j ≠ v ∧ c ≤ j.val) := by
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, h3, by omega⟩
    · rintro ⟨h1, h2, h3, h4⟩
      have hnej : j.val ≠ c := by
        rcases hc with rfl | rfl
        · exact Fin.val_ne_of_ne h2
        · exact Fin.val_ne_of_ne h3
      exact ⟨h1, h2, h3, by omega⟩
  have h2 : ((j = u ∨ j = v) ∧ i ≠ u ∧ i ≠ v ∧ c + 1 ≤ i.val) ↔
      ((j = u ∨ j = v) ∧ i ≠ u ∧ i ≠ v ∧ c ≤ i.val) := by
    constructor
    · rintro ⟨g1, g2, g3, g4⟩
      exact ⟨g1, g2, g3, by omega⟩
    · rintro ⟨g1, g2, g3, g4⟩
      have hnei : i.val ≠ c := by
        rcases hc with rfl | rfl
        · exact Fin.val_ne_of_ne g2
        · exact Fin.val_ne_of_ne g3
      exact ⟨g1, g2, g3, by omega⟩
  simp only [h1, h2]

private def compactStepMatrix {m : ℕ} (W₁ : Fin (m + 1) → Fin (m + 1) → ℕ)
    (v : Fin (m + 1)) (idx : ℕ) (i j : Fin m) : ℕ :=
  if (i.val = v.val ∧ j.val ≠ v.val ∧ idx ≤ j.val) ∨
     (j.val = v.val ∧ i.val ≠ v.val ∧ idx ≤ i.val) then
    W₁ i.castSucc j.castSucc
  else
    W₁ (embedCompact v i) (embedCompact v j)

private theorem compactStepMatrix_zero {m : ℕ} {W₁ : Fin (m + 1) → Fin (m + 1) → ℕ}
    (hW₁ : IsMultigraph W₁) {v : Fin (m + 1)} (i j : Fin m) :
    compactStepMatrix W₁ v 0 i j = W₁ i.castSucc j.castSucc := by
  unfold compactStepMatrix embedCompact
  simp only [Nat.zero_le, and_true]
  by_cases hi : i.val = v.val <;> by_cases hj : j.val = v.val
  · have hij : i = j := Fin.ext (hi.trans hj.symm)
    subst hij
    simp [hi, hW₁.2]
  · simp [hi, hj]
  · simp [hi, hj]
  · simp [hi, hj]

private theorem compactStepMatrix_full {m : ℕ} (W : Fin (m + 1) → Fin (m + 1) → ℕ)
    (u v : Fin (m + 1)) (i j : Fin m) :
    compactStepMatrix (mergePair W u v) v m i j = contractMatrix W u v i j := by
  unfold compactStepMatrix contractMatrix
  have hj : ¬ (m ≤ j.val) := Nat.not_le_of_lt j.isLt
  have hi : ¬ (m ≤ i.val) := Nat.not_le_of_lt i.isLt
  simp [hj, hi]

private theorem compactStepMatrix_step_eq_of_eq {m : ℕ} (W₁ : Fin (m + 1) → Fin (m + 1) → ℕ)
    (v : Fin (m + 1)) {c : ℕ} (hc : c = v.val) (i j : Fin m) :
    compactStepMatrix W₁ v (c + 1) i j = compactStepMatrix W₁ v c i j := by
  unfold compactStepMatrix
  subst hc
  have h1 : (i.val = v.val ∧ j.val ≠ v.val ∧ v.val + 1 ≤ j.val) ↔
      (i.val = v.val ∧ j.val ≠ v.val ∧ v.val ≤ j.val) := by
    exact ⟨fun ⟨a, b, d⟩ => ⟨a, b, by omega⟩, fun ⟨a, b, d⟩ => ⟨a, b, by omega⟩⟩
  have h2 : (j.val = v.val ∧ i.val ≠ v.val ∧ v.val + 1 ≤ i.val) ↔
      (j.val = v.val ∧ i.val ≠ v.val ∧ v.val ≤ i.val) := by
    exact ⟨fun ⟨a, b, d⟩ => ⟨a, b, by omega⟩, fun ⟨a, b, d⟩ => ⟨a, b, by omega⟩⟩
  simp only [h1, h2]

/-! #### Deterministic execution of `uScan`, `vScan`, and `postRandStep` -/

/-- Deterministic execution of `uScan` locating row `u` for a sampled offset `r_val`. -/
theorem uScan_exec {w wb db str k r_val : ℕ} {W : Fin k → Fin k → ℕ}
    {u v : Fin k} {x : Data 16}
    (hsamp : IsSampledPair W r_val u v)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hwBase : x.regs wBase = wb) (hdBase : x.regs dBase = db)
    (hstride : x.regs stride = str) (hactiveK : x.regs activeK = k)
    (htotS : x.regs totS = totalDoubledWeight W) (hrem : x.regs rem = r_val)
    (hdEnd : Fits w (db + k)) (htot : Fits w (totalDoubledWeight W))
    (hdeg : ∀ i : Fin k, x.mem (db + i.val) = rowDeg W i) :
    ∃ y, ExecWithin w uScan x y (6 * k) ∧
      y.mem = x.mem ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧
      y.regs wBase = wb ∧ y.regs dBase = db ∧ y.regs stride = str ∧
      y.regs activeK = k ∧ y.regs targetT = x.regs targetT ∧
      y.regs totS = totalDoubledWeight W ∧
      y.regs uReg = u.val ∧
      y.regs rem = r_val + 1 - degBefore W u := by
  have hk_pos : 0 < k := Nat.zero_lt_of_lt u.isLt
  rcases hsamp with ⟨hoff_le, hoff_lt⟩
  unfold edgeOffset at hoff_le hoff_lt
  have hwb_le := weightBefore_add_le_rowDeg W u v
  have hr_lt_tot : r_val < totalDoubledWeight W := by
    have := degBefore_add_le_totalDoubledWeight W u
    omega
  have hr1_fit : Fits w (r_val + 1) := htot.of_le (by omega)
  have h1_fit : Fits w 1 := hdEnd.of_le (by omega)
  let xs (i : ℕ) : Data 16 :=
    if hi : i ≤ u.val then
      let a : Fin k := ⟨i, lt_of_le_of_lt hi u.isLt⟩
      (((x.set rem (r_val + 1 - degBefore W a)).set uReg i).set addr1 (db + i)).set val1
        (rowDeg W a)
    else x
  have hpre : ExecWithin w ram[rem ← rem + one; uReg ← #0; addr1 ← dBase + uReg; val1 ← *addr1]
      x (xs 0) 4 := by
    have s1 : ExecWithin w ram[rem ← rem + one] x (x.set rem (r_val + 1)) 1 := by
      simpa [BinOp.eval, hrem, h1] using
        ExecWithin.bin (f := .add) (d := rem) (i := rem) (j := one) (x := x)
          (by simpa [BinOp.eval, hrem, h1] using hr1_fit)
    have s2 := ExecWithin.const (B := .standard) (d := uReg)
      (x := x.set rem (r_val + 1)) (fits_zero w)
    have s3 : ExecWithin w ram[addr1 ← dBase + uReg] ((x.set rem (r_val + 1)).set uReg 0)
        (((x.set rem (r_val + 1)).set uReg 0).set addr1 (db + 0)) 1 := by
      have hdb' : ((x.set rem (r_val + 1)).set uReg 0).regs dBase = db := by
        simpa +decide [Function.update_apply] using hdBase
      simpa [BinOp.eval, hdb'] using
        ExecWithin.bin (f := .add) (d := addr1) (i := dBase) (j := uReg)
          (x := (x.set rem (r_val + 1)).set uReg 0)
          (by simpa [BinOp.eval, hdb'] using hdEnd.of_le (by omega))
    have s4 : ExecWithin (B := .standard) w ram[val1 ← *addr1]
        (((x.set rem (r_val + 1)).set uReg 0).set addr1 (db + 0)) (xs 0) 1 := by
      have hmem0 : x.mem db = rowDeg W ⟨0, hk_pos⟩ := by simpa using hdeg ⟨0, hk_pos⟩
      have hd0 : degBefore W ⟨0, hk_pos⟩ = 0 := degBefore_zero hk_pos W
      simpa [xs, hd0, hmem0] using
        ExecWithin.load (B := .standard) (w := w) (d := val1) (a := addr1)
          (x := ((x.set rem (r_val + 1)).set uReg 0).set addr1 (db + 0))
    exact (s1.seq (s2.seq (s3.seq s4))).mono (by omega)
  have hc_hold : ∀ i < u.val, (Cond.lt val1 rem).Holds (xs i) := by
    intro i hi
    have hi_le : i ≤ u.val := Nat.le_of_lt hi
    let a : Fin k := ⟨i, lt_trans hi u.isLt⟩
    have hlt_u : a < u := hi
    have hdeg_le := degBefore_le_of_lt W hlt_u
    simp only [xs, hi_le, ↓reduceDIte, Cond.holds_lt]
    have hv1 : ((((x.set rem (r_val + 1 - degBefore W a)).set uReg i).set addr1 (db + i)).set val1
        (rowDeg W a)).regs val1 = rowDeg W a := by simp
    have hrm : ((((x.set rem (r_val + 1 - degBefore W a)).set uReg i).set addr1 (db + i)).set val1
        (rowDeg W a)).regs rem = r_val + 1 - degBefore W a := by
      simp +decide
    dsimp only [a] at hv1 hrm hdeg_le
    rw [hv1, hrm]
    omega
  have hc_exit : ¬ (Cond.lt val1 rem).Holds (xs u.val) := by
    simp only [xs, le_rfl, ↓reduceDIte, Cond.holds_lt]
    have hv1 : ((((x.set rem (r_val + 1 - degBefore W u)).set uReg u.val).set addr1
        (db + u.val)).set val1 (rowDeg W u)).regs val1 = rowDeg W u := by simp
    have hrm : ((((x.set rem (r_val + 1 - degBefore W u)).set uReg u.val).set addr1
        (db + u.val)).set val1 (rowDeg W u)).regs rem = r_val + 1 - degBefore W u := by
      simp +decide
    rw [hv1, hrm]
    omega
  have hbody : ∀ i < u.val, ExecWithin w uScanBody (xs i) (xs (i + 1)) 4 := by
    intro i hi
    have hi_le : i ≤ u.val := Nat.le_of_lt hi
    have hi1_le : i + 1 ≤ u.val := hi
    let a : Fin k := ⟨i, lt_trans hi u.isLt⟩
    let a' : Fin k := ⟨i + 1, lt_of_le_of_lt hi1_le u.isLt⟩
    have hdeg_le := degBefore_le_of_lt W (show a < u from hi)
    have hsub_eq : (r_val + 1 - degBefore W a) - rowDeg W a = r_val + 1 - degBefore W a' := by
      have hsucc := degBefore_succ (lt_of_le_of_lt hi1_le u.isLt) W
      dsimp only [a, a'] at hdeg_le ⊢
      rw [hsucc]
      omega
    have hsub_fit : Fits w (r_val + 1 - degBefore W a') := hr1_fit.of_le (by omega)
    have hi1_fit : Fits w (i + 1) := hdEnd.of_le (by have := u.isLt; omega)
    have hdb1_fit : Fits w (db + (i + 1)) := hdEnd.of_le (by have := u.isLt; omega)
    have hxi : xs i = (((x.set rem (r_val + 1 - degBefore W a)).set uReg i).set addr1
        (db + i)).set val1 (rowDeg W a) := by simp [xs, hi_le, a]
    have hxi1 : xs (i + 1) = (((x.set rem (r_val + 1 - degBefore W a')).set uReg (i + 1)).set addr1
        (db + (i + 1))).set val1 (rowDeg W a') := by simp [xs, hi1_le, a']
    rw [hxi, hxi1]
    set s0 := (((x.set rem (r_val + 1 - degBefore W a)).set uReg i).set addr1
      (db + i)).set val1 (rowDeg W a)
    have hs0_rem : s0.regs rem = r_val + 1 - degBefore W a := by
      simp +decide [s0]
    have hs0_v1 : s0.regs val1 = rowDeg W a := by simp [s0]
    have hs0_u : s0.regs uReg = i := by simp +decide [s0]
    have hs0_1 : s0.regs one = 1 := by simpa +decide [s0, Function.update_apply] using h1
    have hs0_db : s0.regs dBase = db := by simpa +decide [s0, Function.update_apply] using hdBase
    have b1 : ExecWithin w ram[rem ← rem - val1] s0
        (s0.set rem (r_val + 1 - degBefore W a')) 1 := by
      simpa [BinOp.eval, hs0_rem, hs0_v1, hsub_eq] using
        ExecWithin.bin (f := .sub) (d := rem) (i := rem) (j := val1) (x := s0)
          (by simpa [BinOp.eval, hs0_rem, hs0_v1, hsub_eq] using hsub_fit)
    have b2 : ExecWithin w ram[uReg ← uReg + one] (s0.set rem (r_val + 1 - degBefore W a'))
        ((s0.set rem (r_val + 1 - degBefore W a')).set uReg (i + 1)) 1 := by
      have hu' : (s0.set rem (r_val + 1 - degBefore W a')).regs uReg = i := by
        simpa +decide [Function.update_apply] using hs0_u
      have h1' : (s0.set rem (r_val + 1 - degBefore W a')).regs one = 1 := by
        simpa +decide [Function.update_apply] using hs0_1
      simpa [BinOp.eval, hu', h1'] using
        ExecWithin.bin (f := .add) (d := uReg) (i := uReg) (j := one)
          (x := s0.set rem (r_val + 1 - degBefore W a'))
          (by simpa [BinOp.eval, hu', h1'] using hi1_fit)
    set s2 := (s0.set rem (r_val + 1 - degBefore W a')).set uReg (i + 1)
    have b3 : ExecWithin w ram[addr1 ← dBase + uReg] s2 (s2.set addr1 (db + (i + 1))) 1 := by
      have hdb' : s2.regs dBase = db := by
        simpa +decide [s2, Function.update_apply] using hs0_db
      have hu' : s2.regs uReg = i + 1 := by simp [s2]
      simpa [BinOp.eval, hdb', hu'] using
        ExecWithin.bin (f := .add) (d := addr1) (i := dBase) (j := uReg) (x := s2)
          (by simpa [BinOp.eval, hdb', hu'] using hdb1_fit)
    set s3 := s2.set addr1 (db + (i + 1))
    have b4 : ExecWithin (B := .standard) w ram[val1 ← *addr1] s3
        (s3.set val1 (rowDeg W a')) 1 := by
      have ha1' : s3.regs addr1 = db + (i + 1) := by simp [s3]
      have hm' : s3.mem (db + (i + 1)) = rowDeg W a' := hdeg a'
      simpa [ha1', hm'] using
        ExecWithin.load (B := .standard) (w := w) (d := val1) (a := addr1) (x := s3)
    have hstate_eq : s3.set val1 (rowDeg W a') =
        (((x.set rem (r_val + 1 - degBefore W a')).set uReg (i + 1)).set addr1
          (db + (i + 1))).set val1 (rowDeg W a') := by
      ext r
      · by_cases hr1 : r = val1
        · subst hr1; simp [s3]
        · by_cases hr2 : r = addr1
          · subst hr2; simp +decide [s3]
          · by_cases hr3 : r = uReg
            · subst hr3; simp +decide [s3, s2]
            · by_cases hr4 : r = rem
              · subst hr4; simp +decide [s3, s2]
              · simp only [s3, s2, s0, Data.set_regs,
                  Function.update_of_ne hr1, Function.update_of_ne hr2,
                  Function.update_of_ne hr3, Function.update_of_ne hr4]
      · rfl
    rw [← hstate_eq]
    exact (b1.seq (b2.seq (b3.seq b4))).mono (by omega)
  have hloop := ExecWithin.loop xs u.val 4 hc_hold hc_exit hbody
  refine ⟨xs u.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold uScan
    rcases hpre with ⟨n1, hn1, e_pre⟩
    rcases e_pre with _ | @⟨_, _, _, y1, _, _, _, e1, r1⟩
    rcases r1 with _ | @⟨_, _, _, y2, _, _, _, e2, r2⟩
    rcases r2 with _ | @⟨_, _, _, y3, _, _, _, e3, e4⟩
    have hu_lt : u.val < k := u.isLt
    exact ((e1.within).seq ((e2.within).seq ((e3.within).seq ((e4.within).seq hloop)))).mono
      (by omega)
  · simp [xs]
  · simpa +decide [xs, Function.update_apply] using h0
  · simpa +decide [xs, Function.update_apply] using h1
  · simpa +decide [xs, Function.update_apply] using hwBase
  · simpa +decide [xs, Function.update_apply] using hdBase
  · simpa +decide [xs, Function.update_apply] using hstride
  · simpa +decide [xs, Function.update_apply] using hactiveK
  · simp +decide [xs]
  · simpa +decide [xs, Function.update_apply] using htotS
  · simp +decide [xs]
  · simp +decide [xs]

/-- Deterministic execution of `vScan` locating column `v` along row `u`. -/
theorem vScan_exec {w wb db str k r_val : ℕ} {W : Fin k → Fin k → ℕ}
    {u v : Fin k} {x : Data 16}
    (hsamp : IsSampledPair W r_val u v)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hwBase : x.regs wBase = wb) (hdBase : x.regs dBase = db)
    (hstride : x.regs stride = str) (hactiveK : x.regs activeK = k)
    (htotS : x.regs totS = totalDoubledWeight W)
    (huReg : x.regs uReg = u.val) (hrem : x.regs rem = r_val + 1 - degBefore W u)
    (hstr : k ≤ str) (hwEnd : Fits w (wb + str * k)) (hdEnd : Fits w (db + k))
    (htot : Fits w (totalDoubledWeight W))
    (hmat : HoldsMatrix x.mem wb str W) :
    ∃ y, ExecWithin w vScan x y (6 * k + 1) ∧
      y.mem = x.mem ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧
      y.regs wBase = wb ∧ y.regs dBase = db ∧ y.regs stride = str ∧
      y.regs activeK = k ∧ y.regs targetT = x.regs targetT ∧
      y.regs totS = totalDoubledWeight W ∧
      y.regs uReg = u.val ∧ y.regs vReg = v.val ∧
      y.regs addr2 = wb + u.val * str + v.val ∧
      y.regs val1 = W u v := by
  have hk_pos : 0 < k := Nat.zero_lt_of_lt v.isLt
  rcases hsamp with ⟨hoff_le, hoff_lt⟩
  unfold edgeOffset at hoff_le hoff_lt
  let rem_u := r_val - degBefore W u
  have hrem_eq : r_val + 1 - degBefore W u = rem_u + 1 := by omega
  have hrem1_le_tot : rem_u + 1 ≤ totalDoubledWeight W := by
    have h1 := weightBefore_add_le_rowDeg W u v
    have h2 := degBefore_add_le_totalDoubledWeight W u
    omega
  have hmul_fit : Fits w (u.val * str) :=
    hwEnd.of_le (by
      have : u.val * str ≤ k * str := Nat.mul_le_mul_right str (Nat.le_of_lt u.isLt)
      nlinarith)
  have hrow_fit : Fits w (wb + u.val * str) :=
    hwEnd.of_le (by
      have : u.val * str ≤ k * str := Nat.mul_le_mul_right str (Nat.le_of_lt u.isLt)
      nlinarith)
  let x_base := (x.set val2 (u.val * str)).set addr1 (wb + u.val * str)
  let ys (j : ℕ) : Data 16 :=
    if hj : j ≤ v.val then
      let b : Fin k := ⟨j, lt_of_le_of_lt hj v.isLt⟩
      (((x_base.set rem (rem_u + 1 - weightBefore W u b)).set vReg j).set addr2
        (wb + u.val * str + j)).set val1 (W u b)
    else x_base
  have hpre : ExecWithin w
      ram[val2 ← uReg * stride; addr1 ← wBase + val2; vReg ← #0; addr2 ← addr1 + vReg;
        val1 ← *addr2] x (ys 0) 5 := by
    have s1 : ExecWithin w ram[val2 ← uReg * stride] x (x.set val2 (u.val * str)) 1 := by
      simpa [BinOp.eval, huReg, hstride] using
        ExecWithin.bin (f := .mul) (d := val2) (i := uReg) (j := stride) (x := x)
          (by simpa [BinOp.eval, huReg, hstride] using hmul_fit)
    have s2 : ExecWithin w ram[addr1 ← wBase + val2] (x.set val2 (u.val * str)) x_base 1 := by
      have hwb' : (x.set val2 (u.val * str)).regs wBase = wb := by
        simpa +decide [Function.update_apply] using hwBase
      simpa [x_base, BinOp.eval, hwb'] using
        ExecWithin.bin (f := .add) (d := addr1) (i := wBase) (j := val2)
          (x := x.set val2 (u.val * str))
          (by simpa [BinOp.eval, hwb'] using hrow_fit)
    have s3 := ExecWithin.const (B := .standard) (d := vReg) (x := x_base) (fits_zero w)
    have s4 : ExecWithin w ram[addr2 ← addr1 + vReg] (x_base.set vReg 0)
        ((x_base.set vReg 0).set addr2 (wb + u.val * str + 0)) 1 := by
      have ha1' : (x_base.set vReg 0).regs addr1 = wb + u.val * str := by
        simp +decide [x_base]
      simpa [BinOp.eval, ha1'] using
        ExecWithin.bin (f := .add) (d := addr2) (i := addr1) (j := vReg)
          (x := x_base.set vReg 0)
          (by simpa [BinOp.eval, ha1'] using hrow_fit)
    have s5 : ExecWithin (B := .standard) w ram[val1 ← *addr2]
        ((x_base.set vReg 0).set addr2 (wb + u.val * str + 0)) (ys 0) 1 := by
      have hm0 : x.mem (wb + u.val * str) = W u ⟨0, hk_pos⟩ := by simpa using hmat u ⟨0, hk_pos⟩
      have hw0 : weightBefore W u ⟨0, hk_pos⟩ = 0 := weightBefore_zero hk_pos W u
      have hx_rem : x_base.set rem (rem_u + 1 - weightBefore W u ⟨0, hk_pos⟩) = x_base := by
        ext r
        · by_cases hr : r = rem
          · subst hr
            simp +decide [x_base, hw0, hrem, hrem_eq]
          · simp [Function.update_of_ne hr]
        · rfl
      have hstate : (((x_base.set vReg 0).set addr2 (wb + u.val * str + 0)).set val1
          (W u ⟨0, hk_pos⟩)) = ys 0 := by
        simp only [ys, Nat.zero_le, ↓reduceDIte, hx_rem]
      rw [← hstate]
      simpa [x_base, hm0] using
        ExecWithin.load (B := .standard) (w := w) (d := val1) (a := addr2)
          (x := (x_base.set vReg 0).set addr2 (wb + u.val * str + 0))
    exact (s1.seq (s2.seq (s3.seq (s4.seq s5)))).mono (by omega)
  have hc_hold : ∀ j < v.val, (Cond.lt val1 rem).Holds (ys j) := by
    intro j hj
    have hj_le : j ≤ v.val := Nat.le_of_lt hj
    let b : Fin k := ⟨j, lt_trans hj v.isLt⟩
    have hwb_le := weightBefore_le_of_lt W u (show b < v from hj)
    simp only [ys, hj_le, ↓reduceDIte, Cond.holds_lt]
    have hv1 : ((((x_base.set rem (rem_u + 1 - weightBefore W u b)).set vReg j).set addr2
        (wb + u.val * str + j)).set val1 (W u b)).regs val1 = W u b := by simp
    have hrm : ((((x_base.set rem (rem_u + 1 - weightBefore W u b)).set vReg j).set addr2
        (wb + u.val * str + j)).set val1 (W u b)).regs rem =
        rem_u + 1 - weightBefore W u b := by simp +decide
    dsimp only [b] at hv1 hrm hwb_le
    rw [hv1, hrm]
    omega
  have hc_exit : ¬ (Cond.lt val1 rem).Holds (ys v.val) := by
    simp only [ys, le_rfl, ↓reduceDIte, Cond.holds_lt]
    have hv1 : ((((x_base.set rem (rem_u + 1 - weightBefore W u v)).set vReg v.val).set addr2
        (wb + u.val * str + v.val)).set val1 (W u v)).regs val1 = W u v := by simp
    have hrm : ((((x_base.set rem (rem_u + 1 - weightBefore W u v)).set vReg v.val).set addr2
        (wb + u.val * str + v.val)).set val1 (W u v)).regs rem =
        rem_u + 1 - weightBefore W u v := by simp +decide
    rw [hv1, hrm]
    omega
  have hbody : ∀ j < v.val, ExecWithin w vScanBody (ys j) (ys (j + 1)) 4 := by
    intro j hj
    have hj_le : j ≤ v.val := Nat.le_of_lt hj
    have hj1_le : j + 1 ≤ v.val := hj
    let b : Fin k := ⟨j, lt_trans hj v.isLt⟩
    let b' : Fin k := ⟨j + 1, lt_of_le_of_lt hj1_le v.isLt⟩
    have hwb_le := weightBefore_le_of_lt W u (show b < v from hj)
    have hsub_eq : (rem_u + 1 - weightBefore W u b) - W u b = rem_u + 1 - weightBefore W u b' := by
      have hsucc := weightBefore_succ (lt_of_le_of_lt hj1_le v.isLt) W u
      dsimp only [b, b'] at hwb_le ⊢
      rw [hsucc]
      omega
    have hsub_fit : Fits w (rem_u + 1 - weightBefore W u b') := htot.of_le (by omega)
    have hj1_fit : Fits w (j + 1) := hdEnd.of_le (by have := v.isLt; omega)
    have hcell_fit : Fits w (wb + u.val * str + (j + 1)) :=
      hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr u b'))
    have hyj : ys j = (((x_base.set rem (rem_u + 1 - weightBefore W u b)).set vReg j).set addr2
        (wb + u.val * str + j)).set val1 (W u b) := by simp [ys, hj_le, b]
    have hyj1 : ys (j + 1) =
        (((x_base.set rem (rem_u + 1 - weightBefore W u b')).set vReg (j + 1)).set addr2
          (wb + u.val * str + (j + 1))).set val1 (W u b') := by simp [ys, hj1_le, b']
    rw [hyj, hyj1]
    set s0 := (((x_base.set rem (rem_u + 1 - weightBefore W u b)).set vReg j).set addr2
      (wb + u.val * str + j)).set val1 (W u b)
    have hs0_rem : s0.regs rem = rem_u + 1 - weightBefore W u b := by
      simp +decide [s0]
    have hs0_v1 : s0.regs val1 = W u b := by simp [s0]
    have hs0_v : s0.regs vReg = j := by simp +decide [s0]
    have hs0_1 : s0.regs one = 1 := by
      simpa +decide [s0, x_base, Function.update_apply] using h1
    have hs0_a1 : s0.regs addr1 = wb + u.val * str := by
      simp +decide [s0, x_base]
    have b1 : ExecWithin w ram[rem ← rem - val1] s0
        (s0.set rem (rem_u + 1 - weightBefore W u b')) 1 := by
      simpa [BinOp.eval, hs0_rem, hs0_v1, hsub_eq] using
        ExecWithin.bin (f := .sub) (d := rem) (i := rem) (j := val1) (x := s0)
          (by simpa [BinOp.eval, hs0_rem, hs0_v1, hsub_eq] using hsub_fit)
    have b2 : ExecWithin w ram[vReg ← vReg + one] (s0.set rem (rem_u + 1 - weightBefore W u b'))
        ((s0.set rem (rem_u + 1 - weightBefore W u b')).set vReg (j + 1)) 1 := by
      have hv' : (s0.set rem (rem_u + 1 - weightBefore W u b')).regs vReg = j := by
        simpa +decide [Function.update_apply] using hs0_v
      have h1' : (s0.set rem (rem_u + 1 - weightBefore W u b')).regs one = 1 := by
        simpa +decide [Function.update_apply] using hs0_1
      simpa [BinOp.eval, hv', h1'] using
        ExecWithin.bin (f := .add) (d := vReg) (i := vReg) (j := one)
          (x := s0.set rem (rem_u + 1 - weightBefore W u b'))
          (by simpa [BinOp.eval, hv', h1'] using hj1_fit)
    set s2 := (s0.set rem (rem_u + 1 - weightBefore W u b')).set vReg (j + 1)
    have b3 : ExecWithin w ram[addr2 ← addr1 + vReg] s2
        (s2.set addr2 (wb + u.val * str + (j + 1))) 1 := by
      have ha1' : s2.regs addr1 = wb + u.val * str := by
        simpa +decide [s2, Function.update_apply] using hs0_a1
      have hv' : s2.regs vReg = j + 1 := by simp [s2]
      simpa [BinOp.eval, ha1', hv'] using
        ExecWithin.bin (f := .add) (d := addr2) (i := addr1) (j := vReg) (x := s2)
          (by simpa [BinOp.eval, ha1', hv'] using hcell_fit)
    set s3 := s2.set addr2 (wb + u.val * str + (j + 1))
    have b4 : ExecWithin (B := .standard) w ram[val1 ← *addr2] s3 (s3.set val1 (W u b')) 1 := by
      have ha2' : s3.regs addr2 = wb + u.val * str + (j + 1) := by simp [s3]
      have hm' : s3.mem (wb + u.val * str + (j + 1)) = W u b' := hmat u b'
      simpa [ha2', hm'] using
        ExecWithin.load (B := .standard) (w := w) (d := val1) (a := addr2) (x := s3)
    have hstate_eq : s3.set val1 (W u b') =
        (((x_base.set rem (rem_u + 1 - weightBefore W u b')).set vReg (j + 1)).set addr2
          (wb + u.val * str + (j + 1))).set val1 (W u b') := by
      ext r
      · by_cases hr1 : r = val1
        · subst hr1; simp [s3]
        · by_cases hr2 : r = addr2
          · subst hr2; simp +decide [s3]
          · by_cases hr3 : r = vReg
            · subst hr3; simp +decide [s3, s2]
            · by_cases hr4 : r = rem
              · subst hr4; simp +decide [s3, s2]
              · simp only [s3, s2, s0, Data.set_regs,
                  Function.update_of_ne hr1, Function.update_of_ne hr2,
                  Function.update_of_ne hr3, Function.update_of_ne hr4]
      · rfl
    rw [← hstate_eq]
    exact (b1.seq (b2.seq (b3.seq b4))).mono (by omega)
  have hloop := ExecWithin.loop ys v.val 4 hc_hold hc_exit hbody
  refine ⟨ys v.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold vScan
    rcases hpre with ⟨n1, hn1, e_pre⟩
    rcases e_pre with _ | @⟨_, _, _, y1, _, _, _, e1, r1⟩
    rcases r1 with _ | @⟨_, _, _, y2, _, _, _, e2, r2⟩
    rcases r2 with _ | @⟨_, _, _, y3, _, _, _, e3, r3⟩
    rcases r3 with _ | @⟨_, _, _, y4, _, _, _, e4, e5⟩
    have hv_lt : v.val < k := v.isLt
    exact ((e1.within).seq ((e2.within).seq ((e3.within).seq ((e4.within).seq
      ((e5.within).seq hloop))))).mono (by omega)
  · simp [ys, x_base]
  · simpa +decide [ys, x_base, Function.update_apply] using h0
  · simpa +decide [ys, x_base, Function.update_apply] using h1
  · simpa +decide [ys, x_base, Function.update_apply] using hwBase
  · simpa +decide [ys, x_base, Function.update_apply] using hdBase
  · simpa +decide [ys, x_base, Function.update_apply] using hstride
  · simpa +decide [ys, x_base, Function.update_apply] using hactiveK
  · simp +decide [ys, x_base]
  · simpa +decide [ys, x_base, Function.update_apply] using htotS
  · simpa +decide [ys, x_base, Function.update_apply] using huReg
  · simp +decide [ys, x_base]
  · simp +decide [ys, x_base]
  · simp +decide [ys, x_base]

/-! #### Execution of `phaseADegrees`, `phaseAPtrs`, and `mergeLoop` -/

private theorem exec_bin {w : ℕ} {f : BinOp} {d i j : Fin 16} {x : Data 16} {v : ℕ}
    (heq : BinOp.eval f (x.regs i) (x.regs j) = v) (hfit : Fits w v) :
    ExecWithin (B := .standard) w (.op (.bin f d i j)) x (x.set d v) 1 := by
  simpa only [heq] using ExecWithin.bin (f := f) (d := d) (i := i) (j := j)
    (x := x) (heq.symm ▸ hfit)

private theorem exec_const {w : ℕ} {d : Fin 16} {c : ℕ} {x : Data 16} (hfit : Fits w c) :
    ExecWithin (B := .standard) w (.op (.const d c)) x (x.set d c) 1 :=
  ExecWithin.const (B := .standard) (d := d) (x := x) hfit

private theorem exec_load {w : ℕ} {d a : Fin 16} {x : Data 16} {addr val : ℕ}
    (ha : x.regs a = addr) (hm : x.mem addr = val) :
    ExecWithin (B := .standard) w (.op (.load d a)) x (x.set d val) 1 := by
  simpa only [ha, hm] using ExecWithin.load (B := .standard) (d := d) (a := a) (x := x)

private theorem exec_store {w : ℕ} {a s : Fin 16} {x : Data 16} (addr val : ℕ)
    (ha : x.regs a = addr) (hs : x.regs s = val) :
    ExecWithin (B := .standard) w (.op (.store a s)) x (x.write addr val) 1 := by
  simpa only [ha, hs] using ExecWithin.store (B := .standard) (a := a) (s := s) (x := x)

/-- Deterministic execution of `phaseADegrees` updating `totS`, `W[u, v]`, `D[u]`, and `D[v]`. -/
theorem phaseADegrees_exec {w wb db str m : ℕ}
    {W : Fin (m + 1) → Fin (m + 1) → ℕ} {u v : Fin (m + 1)} {x : Data 16}
    (hW : IsMultigraph W) (huv : u ≠ v)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hwBase : x.regs wBase = wb) (hdBase : x.regs dBase = db)
    (hstride : x.regs stride = str) (hactiveK : x.regs activeK = m + 1)
    (htotS : x.regs totS = totalDoubledWeight W)
    (huReg : x.regs uReg = u.val) (hvReg : x.regs vReg = v.val)
    (ha2 : x.regs addr2 = wb + u.val * str + v.val) (hv1 : x.regs val1 = W u v)
    (hstr : m + 1 ≤ str) (hdisj : wb + str * (m + 1) ≤ db ∨ db + (m + 1) ≤ wb)
    (hdEnd : Fits w (db + (m + 1))) (htot : Fits w (totalDoubledWeight W))
    (hws : HoldsWorkspace x.mem wb db str W) :
    ∃ y, ExecWithin w phaseADegrees x y 12 ∧
      Modifies (workspaceFootprint wb db str (m + 1)) x.mem y.mem ∧
      (∀ i : Fin (m + 1), y.mem (db + i.val) = rowDeg (mergePair W u v) i) ∧
      (∀ i j : Fin (m + 1),
        y.mem (wb + i.val * str + j.val) = if i = u ∧ j = v then 0 else W i j) ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧
      y.regs wBase = wb ∧ y.regs dBase = db ∧ y.regs stride = str ∧
      y.regs activeK = m + 1 ∧ y.regs targetT = x.regs targetT ∧
      y.regs totS = totalDoubledWeight (contractMatrix W u v) ∧
      y.regs uReg = u.val ∧ y.regs vReg = v.val := by
  have htot_contract := totalDoubledWeight_contractMatrix hW huv
  have hS1_fit : Fits w (totalDoubledWeight W - W u v) := htot.of_le (by omega)
  have hS2_eq : (totalDoubledWeight W - W u v) - W u v =
      totalDoubledWeight (contractMatrix W u v) := by omega
  have hS2_fit : Fits w (totalDoubledWeight (contractMatrix W u v)) := htot.of_le (by omega)
  have hdu_addr_fit : Fits w (db + u.val) := hdEnd.of_le (by have := u.isLt; omega)
  have hdv_addr_fit : Fits w (db + v.val) := hdEnd.of_le (by have := v.isLt; omega)
  have hdu_sub_fit : Fits w (rowDeg W u - W u v) :=
    htot.of_le ((Nat.sub_le _ _).trans (rowDeg_le_totalDoubledWeight W u))
  have hdv_sub_fit : Fits w (rowDeg W v - W u v) :=
    htot.of_le ((Nat.sub_le _ _).trans (rowDeg_le_totalDoubledWeight W v))
  have hdu_new_eq : (rowDeg W u - W u v) + (rowDeg W v - W u v) = rowDeg (mergePair W u v) u := by
    rw [rowDeg_mergePair_u hW huv, hW.1 v u]
  have hdu_new_le : rowDeg (mergePair W u v) u ≤ totalDoubledWeight (contractMatrix W u v) := by
    have hidx : rowDeg (mergePair W u v) u =
        rowDeg (contractMatrix W u v) (compactIdx v u huv) := by
      rw [rowDeg_contractMatrix, embedCompact_compactIdx]
    rw [hidx]
    exact rowDeg_le_totalDoubledWeight _ _
  have hdu_new_fit : Fits w (rowDeg (mergePair W u v) u) :=
    hS2_fit.of_le hdu_new_le
  have hread_du : (Function.update x.mem (wb + u.val * str + v.val) 0) (db + u.val) =
      rowDeg W u := by
    rw [Function.update_of_ne (matAddr_ne_degAddr hstr hdisj u v u).symm]
    exact hws.2 u
  have hread_dv : (Function.update x.mem (wb + u.val * str + v.val) 0) (db + v.val) =
      rowDeg W v := by
    rw [Function.update_of_ne (matAddr_ne_degAddr hstr hdisj u v v).symm]
    exact hws.2 v
  let s1 := x.set totS (totalDoubledWeight W - W u v)
  let s2 := s1.set totS (totalDoubledWeight (contractMatrix W u v))
  let s3 := s2.write (wb + u.val * str + v.val) 0
  let s4 := s3.set addr2 (db + u.val)
  let s5 := s4.set val2 (rowDeg W u)
  let s6 := s5.set val2 (rowDeg W u - W u v)
  let s7 := s6.set addr1 (db + v.val)
  let s8 := s7.set rem (rowDeg W v)
  let s9 := s8.set rem (rowDeg W v - W u v)
  let s10 := s9.set val2 (rowDeg (mergePair W u v) u)
  let s11 := s10.write (db + u.val) (rowDeg (mergePair W u v) u)
  let s12 := s11.write (db + v.val) 0
  have e1 := exec_bin (f := .sub) (d := totS) (i := totS) (j := val1) (x := x)
    (by simp [BinOp.eval, htotS, hv1]) hS1_fit
  have e2 := exec_bin (f := .sub) (d := totS) (i := totS) (j := val1) (x := s1)
    (by simp +decide [s1, BinOp.eval, hv1, hS2_eq]) hS2_fit
  have e3 := exec_store (w := w) (a := addr2) (s := zero) (x := s2)
    (wb + u.val * str + v.val) 0
    (by simpa +decide [s2, s1, Function.update_apply] using ha2)
    (by simpa +decide [s2, s1, Function.update_apply] using h0)
  have e4 := exec_bin (f := .add) (d := addr2) (i := dBase) (j := uReg) (x := s3)
    (by simp +decide [s3, s2, s1, BinOp.eval, hdBase, huReg]) hdu_addr_fit
  have e5 := exec_load (w := w) (d := val2) (a := addr2) (x := s4)
    (by simp [s4]) hread_du
  have e6 := exec_bin (f := .sub) (d := val2) (i := val2) (j := val1) (x := s5)
    (by simp +decide [s5, s4, s3, s2, s1, BinOp.eval, hv1]) hdu_sub_fit
  have e7 := exec_bin (f := .add) (d := addr1) (i := dBase) (j := vReg) (x := s6)
    (by simp +decide [s6, s5, s4, s3, s2, s1, BinOp.eval, hdBase, hvReg])
    hdv_addr_fit
  have e8 := exec_load (w := w) (d := rem) (a := addr1) (x := s7)
    (by simp [s7]) hread_dv
  have e9 := exec_bin (f := .sub) (d := rem) (i := rem) (j := val1) (x := s8)
    (by simp +decide [s8, s7, s6, s5, s4, s3, s2, s1, BinOp.eval, hv1])
    hdv_sub_fit
  have e10 := exec_bin (f := .add) (d := val2) (i := val2) (j := rem) (x := s9)
    (by simp +decide [s9, s8, s7, s6, BinOp.eval, hdu_new_eq]) hdu_new_fit
  have e11 := exec_store (w := w) (a := addr2) (s := val2) (x := s10)
    (db + u.val) (rowDeg (mergePair W u v) u)
    (by simp +decide [s10, s9, s8, s7, s6, s5, s4]) (by simp [s10])
  have e12 := exec_store (w := w) (a := addr1) (s := zero) (x := s11)
    (db + v.val) 0
    (by simp +decide [s11, s10, s9, s8, s7])
    (by simpa +decide [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_apply]
      using h0)
  have hrun : ExecWithin w phaseADegrees x s12 12 := by
    unfold phaseADegrees
    exact (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq
      (e7.seq (e8.seq (e9.seq (e10.seq (e11.seq e12))))))))))).mono (by omega)
  refine ⟨s12, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Data.set_mem, Data.write_mem]
    exact modifies_step_update
      (modifies_step_update
        (modifies_update_of_mem (Finset.mem_union_left _ (matAddr_mem_Ico hstr u v)) x.mem 0)
        (Finset.mem_union_right _ (degAddr_mem_Ico u)) (rowDeg (mergePair W u v) u))
      (Finset.mem_union_right _ (degAddr_mem_Ico v)) 0
  · intro i
    dsimp only [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Data.set_mem, Data.write_mem]
    by_cases hiv : i = v
    · subst hiv
      simp [rowDeg_mergePair_v]
    · have hne_iv : db + i.val ≠ db + v.val := fun h => hiv (Fin.ext (by omega))
      rw [Function.update_of_ne hne_iv]
      by_cases hiu : i = u
      · subst hiu
        simp
      · have hne_iu : db + i.val ≠ db + u.val := fun h => hiu (Fin.ext (by omega))
        rw [Function.update_of_ne hne_iu,
          Function.update_of_ne (matAddr_ne_degAddr hstr hdisj u v i).symm, hws.2 i,
          rowDeg_mergePair_other hW huv hiu hiv]
  · intro i j
    dsimp only [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Data.set_mem, Data.write_mem]
    rw [Function.update_of_ne (matAddr_ne_degAddr hstr hdisj i j v),
      Function.update_of_ne (matAddr_ne_degAddr hstr hdisj i j u)]
    by_cases hij_uv : i = u ∧ j = v
    · rcases hij_uv with ⟨rfl, rfl⟩
      simp
    · have hne_mat : wb + i.val * str + j.val ≠ wb + u.val * str + v.val :=
        fun h => hij_uv (matAddr_inj hstr h)
      simp [hij_uv, Function.update_of_ne hne_mat, hws.1 i j]
  · simpa +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_apply]
      using h0
  · simpa +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_apply]
      using h1
  · simpa +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_apply]
      using hwBase
  · simpa +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_apply]
      using hdBase
  · simpa +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_apply]
      using hstride
  · simpa +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_apply]
      using hactiveK
  · simp +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]
  · simp +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2]
  · simpa +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_apply]
      using huReg
  · simpa +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_apply]
      using hvReg

private theorem phaseAPtrs_exec {w wb db str m : ℕ}
    {W : Fin (m + 1) → Fin (m + 1) → ℕ} {u v : Fin (m + 1)} {x : Data 16}
    (hW : IsMultigraph W)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hwBase : x.regs wBase = wb) (hdBase : x.regs dBase = db)
    (hstride : x.regs stride = str) (hactiveK : x.regs activeK = m + 1)
    (huReg : x.regs uReg = u.val) (hvReg : x.regs vReg = v.val)
    (hstr : m + 1 ≤ str) (hdisj : wb + str * (m + 1) ≤ db ∨ db + (m + 1) ≤ wb)
    (hwEnd : Fits w (wb + str * (m + 1)))
    (hdeg : ∀ i : Fin (m + 1), x.mem (db + i.val) = rowDeg (mergePair W u v) i)
    (hmat : ∀ i j : Fin (m + 1),
      x.mem (wb + i.val * str + j.val) = if i = u ∧ j = v then 0 else W i j) :
    ∃ y, ExecWithin w phaseAPtrs x y 7 ∧
      Modifies (workspaceFootprint wb db str (m + 1)) x.mem y.mem ∧
      (∀ i : Fin (m + 1), y.mem (db + i.val) = rowDeg (mergePair W u v) i) ∧
      HoldsMatrix y.mem wb str (mergeStepMatrix W u v 0) ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧
      y.regs wBase = wb ∧ y.regs dBase = db ∧ y.regs stride = str ∧
      y.regs activeK = m + 1 ∧ y.regs targetT = x.regs targetT ∧
      y.regs totS = x.regs totS ∧
      y.regs uReg = u.val ∧ y.regs vReg = v.val ∧
      y.regs addr1 = wb + u.val * str ∧
      y.regs addr2 = wb + v.val * str ∧
      y.regs idx = 0 := by
  have hmul_u_fit : Fits w (u.val * str) :=
    hwEnd.of_le (by
      have hle : u.val * str ≤ str * (m + 1) :=
        Nat.mul_comm (m + 1) str ▸ Nat.mul_le_mul_right str (Nat.le_of_lt u.isLt)
      omega)
  have hrow_u_fit : Fits w (wb + u.val * str) :=
    hwEnd.of_le (by
      have hle : u.val * str ≤ str * (m + 1) :=
        Nat.mul_comm (m + 1) str ▸ Nat.mul_le_mul_right str (Nat.le_of_lt u.isLt)
      omega)
  have hmul_v_fit : Fits w (v.val * str) :=
    hwEnd.of_le (by
      have hle : v.val * str ≤ str * (m + 1) :=
        Nat.mul_comm (m + 1) str ▸ Nat.mul_le_mul_right str (Nat.le_of_lt v.isLt)
      omega)
  have hrow_v_fit : Fits w (wb + v.val * str) :=
    hwEnd.of_le (by
      have hle : v.val * str ≤ str * (m + 1) :=
        Nat.mul_comm (m + 1) str ▸ Nat.mul_le_mul_right str (Nat.le_of_lt v.isLt)
      omega)
  have hvu_fit : Fits w (wb + v.val * str + u.val) :=
    hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr v u))
  let p1 := x.set val2 (u.val * str)
  let p2 := p1.set addr1 (wb + u.val * str)
  let p3 := p2.set val2 (v.val * str)
  let p4 := p3.set addr2 (wb + v.val * str)
  let p5 := p4.set rem (wb + v.val * str + u.val)
  let p6 := p5.write (wb + v.val * str + u.val) 0
  let p7 := p6.set idx 0
  have e1 := exec_bin (f := .mul) (d := val2) (i := uReg) (j := stride) (x := x)
    (by simp [BinOp.eval, huReg, hstride]) hmul_u_fit
  have e2 := exec_bin (f := .add) (d := addr1) (i := wBase) (j := val2) (x := p1)
    (by simp +decide [p1, BinOp.eval, hwBase]) hrow_u_fit
  have e3 := exec_bin (f := .mul) (d := val2) (i := vReg) (j := stride) (x := p2)
    (by simp +decide [p2, p1, BinOp.eval, hvReg, hstride]) hmul_v_fit
  have e4 := exec_bin (f := .add) (d := addr2) (i := wBase) (j := val2) (x := p3)
    (by simp +decide [p3, p2, p1, BinOp.eval, hwBase]) hrow_v_fit
  have e5 := exec_bin (f := .add) (d := rem) (i := addr2) (j := uReg) (x := p4)
    (by simp +decide [p4, p3, p2, p1, BinOp.eval, huReg]) hvu_fit
  have e6 := exec_store (w := w) (a := rem) (s := zero) (x := p5)
    (wb + v.val * str + u.val) 0
    (by simp [p5])
    (by simpa +decide [p5, p4, p3, p2, p1, Function.update_apply] using h0)
  have e7 := exec_const (w := w) (d := idx) (c := 0) (x := p6) (fits_zero w)
  have hrun : ExecWithin w phaseAPtrs x p7 7 := by
    unfold phaseAPtrs
    exact (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))).mono (by omega)
  refine ⟨p7, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [p7, p6, p5, p4, p3, p2, p1, Data.set_mem, Data.write_mem]
    exact modifies_update_of_mem
      (Finset.mem_union_left _ (matAddr_mem_Ico hstr v u)) x.mem 0
  · intro i
    dsimp only [p7, p6, p5, p4, p3, p2, p1, Data.set_mem, Data.write_mem]
    rw [Function.update_of_ne (matAddr_ne_degAddr hstr hdisj v u i).symm]
    exact hdeg i
  · intro i j
    dsimp only [p7, p6, p5, p4, p3, p2, p1, Data.set_mem, Data.write_mem]
    rw [mergeStepMatrix_zero hW]
    by_cases hvu : i = v ∧ j = u
    · rcases hvu with ⟨rfl, rfl⟩
      simp
    · have hne : wb + i.val * str + j.val ≠ wb + v.val * str + u.val :=
        fun h => hvu (matAddr_inj hstr h)
      rw [Function.update_of_ne hne, hmat i j]
      by_cases huv_ij : i = u ∧ j = v <;> simp [huv_ij, hvu]
  · simpa +decide [p7, p6, p5, p4, p3, p2, p1, Function.update_apply] using h0
  · simpa +decide [p7, p6, p5, p4, p3, p2, p1, Function.update_apply] using h1
  · simpa +decide [p7, p6, p5, p4, p3, p2, p1, Function.update_apply] using hwBase
  · simpa +decide [p7, p6, p5, p4, p3, p2, p1, Function.update_apply] using hdBase
  · simpa +decide [p7, p6, p5, p4, p3, p2, p1, Function.update_apply] using hstride
  · simpa +decide [p7, p6, p5, p4, p3, p2, p1, Function.update_apply] using hactiveK
  · simp +decide [p7, p6, p5, p4, p3, p2, p1]
  · simp +decide [p7, p6, p5, p4, p3, p2, p1]
  · simpa +decide [p7, p6, p5, p4, p3, p2, p1, Function.update_apply] using huReg
  · simpa +decide [p7, p6, p5, p4, p3, p2, p1, Function.update_apply] using hvReg
  · simp +decide [p7, p6, p5, p4, p3, p2]
  · simp +decide [p7, p6, p5, p4]
  · simp +decide [p7]

private theorem mergeLoop_exec {w wb db str m : ℕ}
    {W : Fin (m + 1) → Fin (m + 1) → ℕ} {u v : Fin (m + 1)} {x : Data 16}
    (hW : IsMultigraph W) (huv : u ≠ v)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hwBase : x.regs wBase = wb) (hdBase : x.regs dBase = db)
    (hstride : x.regs stride = str) (hactiveK : x.regs activeK = m + 1)
    (huReg : x.regs uReg = u.val) (hvReg : x.regs vReg = v.val)
    (ha1 : x.regs addr1 = wb + u.val * str) (ha2 : x.regs addr2 = wb + v.val * str)
    (hidx0 : x.regs idx = 0)
    (hstr : m + 1 ≤ str) (hdisj : wb + str * (m + 1) ≤ db ∨ db + (m + 1) ≤ wb)
    (hwEnd : Fits w (wb + str * (m + 1))) (hdEnd : Fits w (db + (m + 1)))
    (htot : Fits w (totalDoubledWeight W))
    (hdeg : ∀ i : Fin (m + 1), x.mem (db + i.val) = rowDeg (mergePair W u v) i)
    (hmat0 : HoldsMatrix x.mem wb str (mergeStepMatrix W u v 0)) :
    ∃ y, ExecWithin w ram[while idx < activeK do [ ⟪mergeBody⟫ ]] x y (20 * (m + 1) + 2) ∧
      Modifies (workspaceFootprint wb db str (m + 1)) x.mem y.mem ∧
      HoldsWorkspace y.mem wb db str (mergePair W u v) ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧
      y.regs wBase = wb ∧ y.regs dBase = db ∧ y.regs stride = str ∧
      y.regs activeK = m + 1 ∧ y.regs targetT = x.regs targetT ∧
      y.regs totS = x.regs totS ∧
      y.regs uReg = u.val ∧ y.regs vReg = v.val := by
  let Inv (y : Data 16) : Prop :=
    y.regs zero = 0 ∧ y.regs one = 1 ∧
    y.regs wBase = wb ∧ y.regs dBase = db ∧ y.regs stride = str ∧
    y.regs activeK = m + 1 ∧ y.regs targetT = x.regs targetT ∧
    y.regs totS = x.regs totS ∧
    y.regs uReg = u.val ∧ y.regs vReg = v.val ∧
    y.regs addr1 = wb + u.val * str ∧ y.regs addr2 = wb + v.val * str ∧
    y.regs idx ≤ m + 1 ∧
    Modifies (workspaceFootprint wb db str (m + 1)) x.mem y.mem ∧
    (∀ i : Fin (m + 1), y.mem (db + i.val) = rowDeg (mergePair W u v) i) ∧
    HoldsMatrix y.mem wb str (mergeStepMatrix W u v (y.regs idx))
  have hbody : ∀ y, Inv y → (Cond.lt idx activeK).Holds y →
      ∃ z, ExecWithin w mergeBody y z 18 ∧ Inv z ∧
        (m + 1) - z.regs idx < (m + 1) - y.regs idx := by
    intro y hy hc
    rcases hy with ⟨hy0, hy1, hywb, hydb, hystr, hyk, hyt, hytot, hyu, hyv, hya1, hya2,
      hyidx_le, hymod, hydeg, hymat⟩
    have hc_lt : y.regs idx < m + 1 := by simpa [hyk] using hc
    let c : Fin (m + 1) := ⟨y.regs idx, hc_lt⟩
    have hc1_fit : Fits w (c.val + 1) := hdEnd.of_le (by omega)
    by_cases hcu : c.val = u.val
    · have hcond_u : (Cond.eq idx uReg).Holds y := by
        simp only [Cond.holds_eq, hyu]
        exact hcu
      have hinc : ExecWithin w ram[idx ← idx + one] y (y.set idx (c.val + 1)) 1 := by
        simpa [BinOp.eval, c, hy1] using
          ExecWithin.bin (f := .add) (d := idx) (i := idx) (j := one) (x := y)
            (by simpa [BinOp.eval, c, hy1] using hc1_fit)
      refine ⟨y.set idx (c.val + 1), (ExecWithin.branch_pos hcond_u hinc).mono (by omega), ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hymod, hydeg, ?_⟩
        · simpa +decide [Function.update_apply] using hy0
        · simpa +decide [Function.update_apply] using hy1
        · simpa +decide [Function.update_apply] using hywb
        · simpa +decide [Function.update_apply] using hydb
        · simpa +decide [Function.update_apply] using hystr
        · simpa +decide [Function.update_apply] using hyk
        · simpa +decide [Function.update_apply] using hyt
        · simpa +decide [Function.update_apply] using hytot
        · simpa +decide [Function.update_apply] using hyu
        · simpa +decide [Function.update_apply] using hyv
        · simpa +decide [Function.update_apply] using hya1
        · simpa +decide [Function.update_apply] using hya2
        · simp only [Data.set_regs, Function.update_self]
          exact Nat.succ_le_of_lt hc_lt
        · intro i j
          simp only [Data.set_mem, Data.set_regs, Function.update_self]
          rw [mergeStepMatrix_step_eq_of_mem W u v (Or.inl hcu)]
          exact hymat i j
      · simp only [Data.set_regs, Function.update_self]
        dsimp [c]; omega
    · have hcond_nu : ¬ (Cond.eq idx uReg).Holds y := by
        simp only [Cond.holds_eq, hyu]
        exact hcu
      by_cases hcv : c.val = v.val
      · have hcond_v : (Cond.eq idx vReg).Holds y := by
          simp only [Cond.holds_eq, hyv]
          exact hcv
        have hinc : ExecWithin w ram[idx ← idx + one] y (y.set idx (c.val + 1)) 1 := by
          simpa [BinOp.eval, c, hy1] using
            ExecWithin.bin (f := .add) (d := idx) (i := idx) (j := one) (x := y)
              (by simpa [BinOp.eval, c, hy1] using hc1_fit)
        have hbr := ExecWithin.branch_neg (pos := ram[idx ← idx + one]) hcond_nu
          (ExecWithin.branch_pos (neg := ram[⟪mergeUpdate⟫; idx ← idx + one]) hcond_v hinc)
        refine ⟨y.set idx (c.val + 1), hbr.mono (by omega), ?_, ?_⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hymod, hydeg, ?_⟩
          · simpa +decide [Function.update_apply] using hy0
          · simpa +decide [Function.update_apply] using hy1
          · simpa +decide [Function.update_apply] using hywb
          · simpa +decide [Function.update_apply] using hydb
          · simpa +decide [Function.update_apply] using hystr
          · simpa +decide [Function.update_apply] using hyk
          · simpa +decide [Function.update_apply] using hyt
          · simpa +decide [Function.update_apply] using hytot
          · simpa +decide [Function.update_apply] using hyu
          · simpa +decide [Function.update_apply] using hyv
          · simpa +decide [Function.update_apply] using hya1
          · simpa +decide [Function.update_apply] using hya2
          · simp only [Data.set_regs, Function.update_self]
            exact Nat.succ_le_of_lt hc_lt
          · intro i j
            simp only [Data.set_mem, Data.set_regs, Function.update_self]
            rw [mergeStepMatrix_step_eq_of_mem W u v (Or.inr hcv)]
            exact hymat i j
        · simp only [Data.set_regs, Function.update_self]
          dsimp [c]; omega
      · have hcond_nv : ¬ (Cond.eq idx vReg).Holds y := by
          simp only [Cond.holds_eq, hyv]
          exact hcv
        have hc_ne_u : c ≠ u := fun h => hcu (congrArg Fin.val h)
        have hc_ne_v : c ≠ v := fun h => hcv (congrArg Fin.val h)
        have hvc_fit : Fits w (wb + v.val * str + c.val) :=
          hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr v c))
        have huc_fit : Fits w (wb + u.val * str + c.val) :=
          hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr u c))
        have hcmul_fit : Fits w (c.val * str) :=
          hwEnd.of_le (by
            have hle : c.val * str ≤ str * (m + 1) :=
              Nat.mul_comm (m + 1) str ▸ Nat.mul_le_mul_right str (Nat.le_of_lt c.isLt)
            omega)
        have hcrow_fit : Fits w (wb + c.val * str) :=
          hwEnd.of_le (by
            have hle : c.val * str ≤ str * (m + 1) :=
              Nat.mul_comm (m + 1) str ▸ Nat.mul_le_mul_right str (Nat.le_of_lt c.isLt)
            omega)
        have hcv_fit : Fits w (wb + c.val * str + v.val) :=
          hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr c v))
        have hcu_fit : Fits w (wb + c.val * str + u.val) :=
          hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr c u))
        have hsum_fit : Fits w (W u c + W v c) := by
          have hmp : mergePair W u v u c = W u c + W v c := by
            unfold mergePair
            simp [hc_ne_u.symm, huv, hc_ne_v]
          have hle1 : mergePair W u v u c ≤ rowDeg (mergePair W u v) u :=
            entry_le_rowDeg (mergePair W u v) u c
          have hle2 : rowDeg (mergePair W u v) u ≤ totalDoubledWeight W := by
            have htot_c := totalDoubledWeight_contractMatrix hW huv
            have hidx : rowDeg (mergePair W u v) u =
                rowDeg (contractMatrix W u v) (compactIdx v u huv) := by
              rw [rowDeg_contractMatrix, embedCompact_compactIdx]
            have hle_c := rowDeg_le_totalDoubledWeight (contractMatrix W u v) (compactIdx v u huv)
            omega
          exact htot.of_le (hmp ▸ hle1.trans hle2)
        have hread_vc : y.mem (wb + v.val * str + c.val) = W v c := by
          rw [hymat v c]
          unfold mergeStepMatrix
          simp [hc_ne_u, hc_ne_v, show y.regs idx ≤ c.val from le_rfl]
        have hne_uc_vc : wb + u.val * str + c.val ≠ wb + v.val * str + c.val :=
          fun h => huv (matAddr_inj hstr h).1
        have hread_uc : (Function.update y.mem (wb + v.val * str + c.val) 0)
            (wb + u.val * str + c.val) = W u c := by
          rw [Function.update_of_ne hne_uc_vc, hymat u c]
          unfold mergeStepMatrix
          simp [hc_ne_u, hc_ne_v, show y.regs idx ≤ c.val from le_rfl]
        have hidx_eq : y.regs idx = c.val := rfl
        have hupd : ∃ z, ExecWithin w ram[⟪mergeUpdate⟫; idx ← idx + one] y z 14 ∧
            z.mem = Function.update
              (Function.update
                (Function.update
                  (Function.update y.mem (wb + v.val * str + c.val) 0)
                  (wb + u.val * str + c.val) (W u c + W v c))
                (wb + c.val * str + v.val) 0)
              (wb + c.val * str + u.val) (W u c + W v c) ∧
            z.regs zero = 0 ∧ z.regs one = 1 ∧
            z.regs wBase = wb ∧ z.regs dBase = db ∧ z.regs stride = str ∧
            z.regs activeK = m + 1 ∧ z.regs targetT = x.regs targetT ∧
            z.regs totS = x.regs totS ∧
            z.regs uReg = u.val ∧ z.regs vReg = v.val ∧
            z.regs addr1 = wb + u.val * str ∧ z.regs addr2 = wb + v.val * str ∧
            z.regs idx = c.val + 1 := by
          let u1 := y.set rem (wb + v.val * str + c.val)
          let u2 := u1.set val1 (W v c)
          let u3 := u2.write (wb + v.val * str + c.val) 0
          let u4 := u3.set rem (wb + u.val * str + c.val)
          let u5 := u4.set val2 (W u c)
          let u6 := u5.set val2 (W u c + W v c)
          let u7 := u6.write (wb + u.val * str + c.val) (W u c + W v c)
          let u8 := u7.set val1 (c.val * str)
          let u9 := u8.set val1 (wb + c.val * str)
          let u10 := u9.set rem (wb + c.val * str + v.val)
          let u11 := u10.write (wb + c.val * str + v.val) 0
          let u12 := u11.set rem (wb + c.val * str + u.val)
          let u13 := u12.write (wb + c.val * str + u.val) (W u c + W v c)
          let u14 := u13.set idx (c.val + 1)
          have e1 := exec_bin (f := .add) (d := rem) (i := addr2) (j := idx) (x := y)
            (by simp [BinOp.eval, hya2, hidx_eq]) hvc_fit
          have e2 := exec_load (w := w) (d := val1) (a := rem) (x := u1)
            (by simp [u1]) hread_vc
          have e3 := exec_store (w := w) (a := rem) (s := zero) (x := u2)
            (wb + v.val * str + c.val) 0
            (by simp +decide [u2, u1])
            (by simpa +decide [u2, u1, Function.update_apply] using hy0)
          have e4 := exec_bin (f := .add) (d := rem) (i := addr1) (j := idx) (x := u3)
            (by simp +decide [u3, u2, u1, BinOp.eval, hya1, hidx_eq]) huc_fit
          have e5 := exec_load (w := w) (d := val2) (a := rem) (x := u4)
            (by simp [u4]) hread_uc
          have e6 := exec_bin (f := .add) (d := val2) (i := val2) (j := val1) (x := u5)
            (by simp +decide [u5, u4, u3, u2, BinOp.eval]) hsum_fit
          have e7 := exec_store (w := w) (a := rem) (s := val2) (x := u6)
            (wb + u.val * str + c.val) (W u c + W v c)
            (by simp +decide [u6, u5, u4]) (by simp [u6])
          have e8 := exec_bin (f := .mul) (d := val1) (i := idx) (j := stride) (x := u7)
            (by simp +decide [u7, u6, u5, u4, u3, u2, u1, BinOp.eval, hidx_eq, hystr]) hcmul_fit
          have e9 := exec_bin (f := .add) (d := val1) (i := wBase) (j := val1) (x := u8)
            (by simp +decide [u8, u7, u6, u5, u4, u3, u2, u1, BinOp.eval, hywb]) hcrow_fit
          have e10 := exec_bin (f := .add) (d := rem) (i := val1) (j := vReg) (x := u9)
            (by simp +decide [u9, u8, u7, u6, u5, u4, u3, u2, u1, BinOp.eval, hyv]) hcv_fit
          have e11 := exec_store (w := w) (a := rem) (s := zero) (x := u10)
            (wb + c.val * str + v.val) 0
            (by simp [u10])
            (by simpa +decide [u10, u9, u8, u7, u6, u5, u4, u3, u2, u1, Function.update_apply]
              using hy0)
          have e12 := exec_bin (f := .add) (d := rem) (i := val1) (j := uReg) (x := u11)
            (by simp +decide [u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1, BinOp.eval, hyu])
            hcu_fit
          have e13 := exec_store (w := w) (a := rem) (s := val2) (x := u12)
            (wb + c.val * str + u.val) (W u c + W v c)
            (by simp [u12])
            (by simp +decide [u12, u11, u10, u9, u8, u7, u6])
          have e14 := exec_bin (f := .add) (d := idx) (i := idx) (j := one) (x := u13)
            (by simp +decide [u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1,
              BinOp.eval, hidx_eq, hy1]) hc1_fit
          have hmu : ExecWithin w mergeUpdate y u13 13 := by
            unfold mergeUpdate
            exact (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq
              (e8.seq (e9.seq (e10.seq (e11.seq (e12.seq e13)))))))))))).mono (by omega)
          refine ⟨u14, (hmu.seq e14).mono (by omega), rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ?_, ?_, ?_⟩
          · simpa +decide [u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1,
              Function.update_apply] using hy0
          · simpa +decide [u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1,
              Function.update_apply] using hy1
          · simpa +decide [u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1,
              Function.update_apply] using hywb
          · simpa +decide [u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1,
              Function.update_apply] using hydb
          · simpa +decide [u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1,
              Function.update_apply] using hystr
          · simpa +decide [u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1,
              Function.update_apply] using hyk
          · simpa +decide [u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1,
              Function.update_apply] using hyt
          · simpa +decide [u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1,
              Function.update_apply] using hytot
          · simpa +decide [u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1,
              Function.update_apply] using hyu
          · simpa +decide [u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1,
              Function.update_apply] using hyv
          · simpa +decide [u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1,
              Function.update_apply] using hya1
          · simpa +decide [u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1,
              Function.update_apply] using hya2
          · simp +decide [u14]
        rcases hupd with ⟨z, hz_exec, hz_mem, hz0, hz1, hzwb, hzdb, hzstr, hzk, hzt, hztot,
          hzu, hzv, hza1, hza2, hzidx⟩
        have hbr := ExecWithin.branch_neg (pos := ram[idx ← idx + one]) hcond_nu
          (ExecWithin.branch_neg (pos := ram[idx ← idx + one]) hcond_nv hz_exec)
        refine ⟨z, hbr.mono (by omega), ?_, ?_⟩
        · refine ⟨hz0, hz1, hzwb, hzdb, hzstr, hzk, hzt, hztot, hzu, hzv, hza1, hza2,
            by omega, ?_, ?_, ?_⟩
          · rw [hz_mem]
            exact modifies_step_update
              (modifies_step_update
                (modifies_step_update
                  (modifies_step_update hymod
                    (Finset.mem_union_left _ (matAddr_mem_Ico hstr v c)) 0)
                  (Finset.mem_union_left _ (matAddr_mem_Ico hstr u c)) (W u c + W v c))
                (Finset.mem_union_left _ (matAddr_mem_Ico hstr c v)) 0)
              (Finset.mem_union_left _ (matAddr_mem_Ico hstr c u)) (W u c + W v c)
          · intro i
            rw [hz_mem,
              Function.update_of_ne (matAddr_ne_degAddr hstr hdisj c u i).symm,
              Function.update_of_ne (matAddr_ne_degAddr hstr hdisj c v i).symm,
              Function.update_of_ne (matAddr_ne_degAddr hstr hdisj u c i).symm,
              Function.update_of_ne (matAddr_ne_degAddr hstr hdisj v c i).symm]
            exact hydeg i
          · intro i j
            rw [hz_mem, hzidx]
            by_cases h_cu : i = c ∧ j = u
            · rcases h_cu with ⟨hi, hj⟩
              rw [hi, hj]
              simp only [Function.update_self]
              unfold mergeStepMatrix mergePair
              have : ¬ (c.val + 1 ≤ c.val) := by omega
              simp [hc_ne_u, hc_ne_v, huv, this, hW.1 c u, hW.1 c v]
            · rw [Function.update_of_ne (fun h => h_cu (matAddr_inj hstr h))]
              by_cases h_cv : i = c ∧ j = v
              · rcases h_cv with ⟨hi, hj⟩
                rw [hi, hj]
                simp only [Function.update_self]
                unfold mergeStepMatrix mergePair
                have : ¬ (c.val + 1 ≤ c.val) := by omega
                simp [hc_ne_u, hc_ne_v, this]
              · rw [Function.update_of_ne (fun h => h_cv (matAddr_inj hstr h))]
                by_cases h_uc : i = u ∧ j = c
                · rcases h_uc with ⟨hi, hj⟩
                  rw [hi, hj]
                  simp only [Function.update_self]
                  unfold mergeStepMatrix mergePair
                  have : ¬ (c.val + 1 ≤ c.val) := by omega
                  simp [hc_ne_u, hc_ne_u.symm, hc_ne_v, huv, this]
                · rw [Function.update_of_ne (fun h => h_uc (matAddr_inj hstr h))]
                  by_cases h_vc : i = v ∧ j = c
                  · rcases h_vc with ⟨hi, hj⟩
                    rw [hi, hj]
                    simp only [Function.update_self]
                    unfold mergeStepMatrix mergePair
                    have : ¬ (c.val + 1 ≤ c.val) := by omega
                    simp [hc_ne_u, hc_ne_v, this]
                  · rw [Function.update_of_ne (fun h => h_vc (matAddr_inj hstr h)), hymat i j]
                    unfold mergeStepMatrix
                    have hiff1 : ((i = u ∨ i = v) ∧ j ≠ u ∧ j ≠ v ∧ y.regs idx ≤ j.val) ↔
                        ((i = u ∨ i = v) ∧ j ≠ u ∧ j ≠ v ∧ c.val + 1 ≤ j.val) := by
                      constructor
                      · rintro ⟨a1, a2, a3, a4⟩
                        have hjc : j ≠ c := by
                          rintro rfl
                          rcases a1 with rfl | rfl
                          · exact h_uc ⟨rfl, rfl⟩
                          · exact h_vc ⟨rfl, rfl⟩
                        have := Fin.val_ne_of_ne hjc
                        exact ⟨a1, a2, a3, by dsimp [c] at *; omega⟩
                      · rintro ⟨a1, a2, a3, a4⟩
                        exact ⟨a1, a2, a3, by dsimp [c] at *; omega⟩
                    have hiff2 : ((j = u ∨ j = v) ∧ i ≠ u ∧ i ≠ v ∧ y.regs idx ≤ i.val) ↔
                        ((j = u ∨ j = v) ∧ i ≠ u ∧ i ≠ v ∧ c.val + 1 ≤ i.val) := by
                      constructor
                      · rintro ⟨a1, a2, a3, a4⟩
                        have hic : i ≠ c := by
                          rintro rfl
                          rcases a1 with rfl | rfl
                          · exact h_cu ⟨rfl, rfl⟩
                          · exact h_cv ⟨rfl, rfl⟩
                        have := Fin.val_ne_of_ne hic
                        exact ⟨a1, a2, a3, by dsimp [c] at *; omega⟩
                      · rintro ⟨a1, a2, a3, a4⟩
                        exact ⟨a1, a2, a3, by dsimp [c] at *; omega⟩
                    simp only [hiff1, hiff2]
        · rw [hzidx]; dsimp [c]; omega
  have hx_inv : Inv x :=
    ⟨h0, h1, hwBase, hdBase, hstride, hactiveK, rfl, rfl, huReg, hvReg, ha1, ha2,
      by omega, Modifies.refl _ _, hdeg, hidx0 ▸ hmat0⟩
  obtain ⟨y_end, hloop, hy_end, hnc⟩ :=
    ExecWithin.loop_invariant Inv (fun y => (m + 1) - y.regs idx) hbody hx_inv
  rcases hy_end with ⟨hy0, hy1, hywb, hydb, hystr, hyk, hyt, hytot, hyu, hyv, _, _,
    hyidx_le, hymod, hydeg, hymat⟩
  have hidx_end : y_end.regs idx = m + 1 := by
    simp only [Cond.holds_lt, hyk] at hnc
    omega
  refine ⟨y_end, hloop.mono (by rw [hidx0]; omega), hymod,
    ⟨fun i j => by simpa [hidx_end, mergeStepMatrix_full] using hymat i j, hydeg⟩,
    hy0, hy1, hywb, hydb, hystr, hyk, hyt, hytot, hyu, hyv⟩

/-! #### Execution of Phase B (`compactSetup` + `compactLoop`) and `postRandStep` -/

private theorem compactPhase_exec {w wb db str m : ℕ}
    {W : Fin (m + 1) → Fin (m + 1) → ℕ} {u v : Fin (m + 1)} {x : Data 16}
    (hW : IsMultigraph W) (hv_lt : v.val < m)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hwBase : x.regs wBase = wb) (hdBase : x.regs dBase = db)
    (hstride : x.regs stride = str) (hactiveK : x.regs activeK = m)
    (hvReg : x.regs vReg = v.val)
    (hstr : m + 1 ≤ str) (hdisj : wb + str * (m + 1) ≤ db ∨ db + (m + 1) ≤ wb)
    (hwEnd : Fits w (wb + str * (m + 1))) (hdEnd : Fits w (db + (m + 1)))
    (hws1 : HoldsWorkspace x.mem wb db str (mergePair W u v)) :
    ∃ y, ExecWithin w ram[⟪compactSetup⟫; while idx < activeK do [ ⟪compactBody⟫ ]]
        x y (13 * m + 11) ∧
      Modifies (workspaceFootprint wb db str (m + 1)) x.mem y.mem ∧
      HoldsWorkspace y.mem wb db str (contractMatrix W u v) ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧
      y.regs wBase = wb ∧ y.regs dBase = db ∧ y.regs stride = str ∧
      y.regs activeK = m ∧ y.regs targetT = x.regs targetT ∧
      y.regs totS = x.regs totS := by
  let W₁ := mergePair W u v
  have hW₁ : IsMultigraph W₁ := isMultigraph_mergePair hW u v
  let v_m : Fin m := ⟨v.val, hv_lt⟩
  have hdm_fit : Fits w (db + m) := hdEnd.of_le (by omega)
  have hdv_fit : Fits w (db + v.val) := hdEnd.of_le (by omega)
  have hmmul_fit : Fits w (m * str) :=
    hwEnd.of_le (by
      have hle : m * str ≤ str * (m + 1) :=
        Nat.mul_comm (m + 1) str ▸ Nat.mul_le_mul_right str (Nat.le_succ m)
      omega)
  have hmrow_fit : Fits w (wb + m * str) :=
    hwEnd.of_le (by
      have hle : m * str ≤ str * (m + 1) :=
        Nat.mul_comm (m + 1) str ▸ Nat.mul_le_mul_right str (Nat.le_succ m)
      omega)
  have hvmul_fit : Fits w (v.val * str) :=
    hwEnd.of_le (by
      have hle : v.val * str ≤ str * (m + 1) :=
        Nat.mul_comm (m + 1) str ▸ Nat.mul_le_mul_right str (Nat.le_of_lt v.isLt)
      omega)
  have hvrow_fit : Fits w (wb + v.val * str) :=
    hwEnd.of_le (by
      have hle : v.val * str ≤ str * (m + 1) :=
        Nat.mul_comm (m + 1) str ▸ Nat.mul_le_mul_right str (Nat.le_of_lt v.isLt)
      omega)
  have hread_dm : x.mem (db + m) = rowDeg W₁ (Fin.last m) := hws1.2 (Fin.last m)
  have hsetup : ∃ x₁, ExecWithin w compactSetup x x₁ 9 ∧
      x₁.mem = Function.update x.mem (db + v.val) (rowDeg W₁ (Fin.last m)) ∧
      x₁.regs zero = 0 ∧ x₁.regs one = 1 ∧
      x₁.regs wBase = wb ∧ x₁.regs dBase = db ∧ x₁.regs stride = str ∧
      x₁.regs activeK = m ∧ x₁.regs targetT = x.regs targetT ∧
      x₁.regs totS = x.regs totS ∧
      x₁.regs vReg = v.val ∧
      x₁.regs addr1 = wb + m * str ∧ x₁.regs addr2 = wb + v.val * str ∧
      x₁.regs idx = 0 := by
    let s1 := x.set addr1 (db + m)
    let s2 := s1.set val1 (rowDeg W₁ (Fin.last m))
    let s3 := s2.set addr2 (db + v.val)
    let s4 := s3.write (db + v.val) (rowDeg W₁ (Fin.last m))
    let s5 := s4.set val1 (m * str)
    let s6 := s5.set addr1 (wb + m * str)
    let s7 := s6.set val1 (v.val * str)
    let s8 := s7.set addr2 (wb + v.val * str)
    let s9 := s8.set idx 0
    have e1 := exec_bin (f := .add) (d := addr1) (i := dBase) (j := activeK) (x := x)
      (by simp [BinOp.eval, hdBase, hactiveK]) hdm_fit
    have e2 := exec_load (w := w) (d := val1) (a := addr1) (x := s1) (by simp [s1]) hread_dm
    have e3 := exec_bin (f := .add) (d := addr2) (i := dBase) (j := vReg) (x := s2)
      (by simp +decide [s2, s1, BinOp.eval, hdBase, hvReg]) hdv_fit
    have e4 := exec_store (w := w) (a := addr2) (s := val1) (x := s3)
      (db + v.val) (rowDeg W₁ (Fin.last m))
      (by simp [s3]) (by simp +decide [s3, s2])
    have e5 := exec_bin (f := .mul) (d := val1) (i := activeK) (j := stride) (x := s4)
      (by simp +decide [s4, s3, s2, s1, BinOp.eval, hactiveK, hstride])
      hmmul_fit
    have e6 := exec_bin (f := .add) (d := addr1) (i := wBase) (j := val1) (x := s5)
      (by simp +decide [s5, s4, s3, s2, s1, BinOp.eval, hwBase]) hmrow_fit
    have e7 := exec_bin (f := .mul) (d := val1) (i := vReg) (j := stride) (x := s6)
      (by simp +decide [s6, s5, s4, s3, s2, s1, BinOp.eval, hvReg, hstride])
      hvmul_fit
    have e8 := exec_bin (f := .add) (d := addr2) (i := wBase) (j := val1) (x := s7)
      (by simp +decide [s7, s6, s5, s4, s3, s2, s1, BinOp.eval, hwBase])
      hvrow_fit
    have e9 := exec_const (d := idx) (c := 0) (x := s8) (fits_zero w)
    have hcs : ExecWithin w compactSetup x s9 9 := by
      unfold compactSetup
      exact (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq e9)))))))).mono
        (by omega)
    refine ⟨s9, hcs, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_apply] using h0
    · simpa +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_apply] using h1
    · simpa +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_apply] using hwBase
    · simpa +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_apply] using hdBase
    · simpa +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_apply] using hstride
    · simpa +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_apply] using hactiveK
    · simp +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1]
    · simp +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1]
    · simpa +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_apply] using hvReg
    · simp +decide [s9, s8, s7, s6]
    · simp +decide [s9, s8]
    · simp +decide [s9]
  rcases hsetup with ⟨x₁, hx₁_exec, hx₁_mem, hx₁_0, hx₁_1, hx₁_wb, hx₁_db, hx₁_str, hx₁_k,
    hx₁_t, hx₁_tot, hx₁_v, hx₁_a1, hx₁_a2, hx₁_idx⟩
  have hx₁_mod : Modifies (workspaceFootprint wb db str (m + 1)) x.mem x₁.mem := by
    rw [hx₁_mem]
    exact modifies_update_of_mem (Finset.mem_union_right _ (degAddr_mem_Ico v)) x.mem _
  have hx₁_deg : ∀ i : Fin m, x₁.mem (db + i.val) = rowDeg (contractMatrix W u v) i := by
    intro i
    rw [hx₁_mem, rowDeg_contractMatrix]
    unfold embedCompact
    by_cases hiv : i.val = v.val
    · rw [hiv]
      simp [W₁]
    · have hne : db + i.val ≠ db + v.val := by omega
      have hread : x.mem (db + i.val) = rowDeg W₁ i.castSucc := hws1.2 i.castSucc
      rw [Function.update_of_ne hne]
      simp only [hiv, ↓reduceIte, hread, W₁]
  have hx₁_rowm : ∀ c : Fin m, x₁.mem (wb + m * str + c.val) = W₁ (Fin.last m) c.castSucc := by
    intro c
    have hne : wb + m * str + c.val ≠ db + v.val := by
      simpa only [Fin.val_last, Fin.val_castSucc] using
        matAddr_ne_degAddr hstr hdisj (Fin.last m) c.castSucc v
    rw [hx₁_mem, Function.update_of_ne hne]
    exact hws1.1 (Fin.last m) c.castSucc
  have hx₁_mat0 : HoldsMatrix x₁.mem wb str (compactStepMatrix W₁ v 0) := by
    intro i j
    have hne : wb + i.val * str + j.val ≠ db + v.val := by
      simpa only [Fin.val_castSucc] using
        matAddr_ne_degAddr hstr hdisj i.castSucc j.castSucc v
    rw [hx₁_mem, Function.update_of_ne hne, compactStepMatrix_zero hW₁]
    exact hws1.1 i.castSucc j.castSucc
  let Inv (y : Data 16) : Prop :=
    y.regs zero = 0 ∧ y.regs one = 1 ∧
    y.regs wBase = wb ∧ y.regs dBase = db ∧ y.regs stride = str ∧
    y.regs activeK = m ∧ y.regs targetT = x.regs targetT ∧
    y.regs totS = x.regs totS ∧
    y.regs vReg = v.val ∧
    y.regs addr1 = wb + m * str ∧ y.regs addr2 = wb + v.val * str ∧
    y.regs idx ≤ m ∧
    Modifies (workspaceFootprint wb db str (m + 1)) x.mem y.mem ∧
    (∀ i : Fin m, y.mem (db + i.val) = rowDeg (contractMatrix W u v) i) ∧
    (∀ c : Fin m, y.mem (wb + m * str + c.val) = W₁ (Fin.last m) c.castSucc) ∧
    HoldsMatrix y.mem wb str (compactStepMatrix W₁ v (y.regs idx))
  have hbody : ∀ y, Inv y → (Cond.lt idx activeK).Holds y →
      ∃ z, ExecWithin w compactBody y z 11 ∧ Inv z ∧
        m - z.regs idx < m - y.regs idx := by
    intro y hy hc
    rcases hy with ⟨hy0, hy1, hywb, hydb, hystr, hyk, hyt, hytot, hyv, hya1, hya2,
      hyidx_le, hymod, hydeg, hyrowm, hymat⟩
    have hc_lt : y.regs idx < m := by simpa [hyk] using hc
    let c : Fin m := ⟨y.regs idx, hc_lt⟩
    have hc1_fit : Fits w (c.val + 1) := hdEnd.of_le (by omega)
    by_cases hcv : c.val = v.val
    · have hcond_v : (Cond.eq idx vReg).Holds y := by
        simp only [Cond.holds_eq, hyv]
        exact hcv
      have hinc : ExecWithin w ram[idx ← idx + one] y (y.set idx (c.val + 1)) 1 := by
        simpa [BinOp.eval, c, hy1] using
          ExecWithin.bin (f := .add) (d := idx) (i := idx) (j := one) (x := y)
            (by simpa [BinOp.eval, c, hy1] using hc1_fit)
      refine ⟨y.set idx (c.val + 1), (ExecWithin.branch_pos hcond_v hinc).mono (by omega), ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hymod, hydeg, hyrowm, ?_⟩
        · simpa +decide [Function.update_apply] using hy0
        · simpa +decide [Function.update_apply] using hy1
        · simpa +decide [Function.update_apply] using hywb
        · simpa +decide [Function.update_apply] using hydb
        · simpa +decide [Function.update_apply] using hystr
        · simpa +decide [Function.update_apply] using hyk
        · simpa +decide [Function.update_apply] using hyt
        · simpa +decide [Function.update_apply] using hytot
        · simpa +decide [Function.update_apply] using hyv
        · simpa +decide [Function.update_apply] using hya1
        · simpa +decide [Function.update_apply] using hya2
        · simp only [Data.set_regs, Function.update_self]
          exact Nat.succ_le_of_lt hc_lt
        · intro i j
          simp only [Data.set_mem, Data.set_regs, Function.update_self]
          rw [compactStepMatrix_step_eq_of_eq W₁ v hcv]
          exact hymat i j
      · simp only [Data.set_regs, Function.update_self]
        dsimp [c]; omega
    · have hcond_nv : ¬ (Cond.eq idx vReg).Holds y := by
        simp only [Cond.holds_eq, hyv]
        exact hcv
      have hmc_fit : Fits w (wb + m * str + c.val) :=
        hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr (Fin.last m) c.castSucc))
      have hvc_fit : Fits w (wb + v.val * str + c.val) :=
        hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr v c.castSucc))
      have hcmul_fit : Fits w (c.val * str) :=
        hwEnd.of_le (by
          have hle : c.val * str ≤ str * (m + 1) :=
            Nat.mul_comm (m + 1) str ▸
              (Fin.val_castSucc c ▸ Nat.mul_le_mul_right str (Nat.le_of_lt c.castSucc.isLt))
          omega)
      have hcrow_fit : Fits w (wb + c.val * str) :=
        hwEnd.of_le (by
          have hle : c.val * str ≤ str * (m + 1) :=
            Nat.mul_comm (m + 1) str ▸
              (Fin.val_castSucc c ▸ Nat.mul_le_mul_right str (Nat.le_of_lt c.castSucc.isLt))
          omega)
      have hcv_fit : Fits w (wb + c.val * str + v.val) :=
        hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr c.castSucc v))
      have hread_mc : y.mem (wb + m * str + c.val) = W₁ (Fin.last m) c.castSucc := hyrowm c
      have hidx_eq : y.regs idx = c.val := rfl
      have hupd : ∃ z, ExecWithin w ram[⟪compactUpdate⟫; idx ← idx + one] y z 9 ∧
          z.mem = Function.update
            (Function.update y.mem (wb + v.val * str + c.val) (W₁ (Fin.last m) c.castSucc))
            (wb + c.val * str + v.val) (W₁ (Fin.last m) c.castSucc) ∧
          z.regs zero = 0 ∧ z.regs one = 1 ∧
          z.regs wBase = wb ∧ z.regs dBase = db ∧ z.regs stride = str ∧
          z.regs activeK = m ∧ z.regs targetT = x.regs targetT ∧
          z.regs totS = x.regs totS ∧
          z.regs vReg = v.val ∧
          z.regs addr1 = wb + m * str ∧ z.regs addr2 = wb + v.val * str ∧
          z.regs idx = c.val + 1 := by
        let q1 := y.set rem (wb + m * str + c.val)
        let q2 := q1.set val1 (W₁ (Fin.last m) c.castSucc)
        let q3 := q2.set rem (wb + v.val * str + c.val)
        let q4 := q3.write (wb + v.val * str + c.val) (W₁ (Fin.last m) c.castSucc)
        let q5 := q4.set val2 (c.val * str)
        let q6 := q5.set val2 (wb + c.val * str)
        let q7 := q6.set rem (wb + c.val * str + v.val)
        let q8 := q7.write (wb + c.val * str + v.val) (W₁ (Fin.last m) c.castSucc)
        let q9 := q8.set idx (c.val + 1)
        have e1 := exec_bin (f := .add) (d := rem) (i := addr1) (j := idx) (x := y)
          (by simp [BinOp.eval, hya1, hidx_eq]) hmc_fit
        have e2 := exec_load (w := w) (d := val1) (a := rem) (x := q1)
          (by simp [q1]) hread_mc
        have e3 := exec_bin (f := .add) (d := rem) (i := addr2) (j := idx) (x := q2)
          (by simp +decide [q2, q1, BinOp.eval, hya2, hidx_eq]) hvc_fit
        have e4 := exec_store (w := w) (a := rem) (s := val1) (x := q3)
          (wb + v.val * str + c.val) (W₁ (Fin.last m) c.castSucc)
          (by simp [q3]) (by simp +decide [q3, q2])
        have e5 := exec_bin (f := .mul) (d := val2) (i := idx) (j := stride) (x := q4)
          (by simp +decide [q4, q3, q2, q1, BinOp.eval, hidx_eq, hystr])
          hcmul_fit
        have e6 := exec_bin (f := .add) (d := val2) (i := wBase) (j := val2) (x := q5)
          (by simp +decide [q5, q4, q3, q2, q1, BinOp.eval, hywb]) hcrow_fit
        have e7 := exec_bin (f := .add) (d := rem) (i := val2) (j := vReg) (x := q6)
          (by simp +decide [q6, q5, q4, q3, q2, q1, BinOp.eval, hyv]) hcv_fit
        have e8 := exec_store (w := w) (a := rem) (s := val1) (x := q7)
          (wb + c.val * str + v.val) (W₁ (Fin.last m) c.castSucc)
          (by simp [q7]) (by simp +decide [q7, q6, q5, q4, q3, q2])
        have e9 := exec_bin (f := .add) (d := idx) (i := idx) (j := one) (x := q8)
          (by simp +decide [q8, q7, q6, q5, q4, q3, q2, q1,
            BinOp.eval, hidx_eq, hy1]) hc1_fit
        have hcu : ExecWithin w compactUpdate y q8 8 := by
          unfold compactUpdate
          exact (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))).mono (by omega)
        refine ⟨q9, (hcu.seq e9).mono (by omega), rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_⟩
        · simpa +decide [q9, q8, q7, q6, q5, q4, q3, q2, q1, Function.update_apply] using hy0
        · simpa +decide [q9, q8, q7, q6, q5, q4, q3, q2, q1, Function.update_apply] using hy1
        · simpa +decide [q9, q8, q7, q6, q5, q4, q3, q2, q1, Function.update_apply] using hywb
        · simpa +decide [q9, q8, q7, q6, q5, q4, q3, q2, q1, Function.update_apply] using hydb
        · simpa +decide [q9, q8, q7, q6, q5, q4, q3, q2, q1, Function.update_apply] using hystr
        · simpa +decide [q9, q8, q7, q6, q5, q4, q3, q2, q1, Function.update_apply] using hyk
        · simpa +decide [q9, q8, q7, q6, q5, q4, q3, q2, q1, Function.update_apply] using hyt
        · simpa +decide [q9, q8, q7, q6, q5, q4, q3, q2, q1, Function.update_apply] using hytot
        · simpa +decide [q9, q8, q7, q6, q5, q4, q3, q2, q1, Function.update_apply] using hyv
        · simpa +decide [q9, q8, q7, q6, q5, q4, q3, q2, q1, Function.update_apply] using hya1
        · simpa +decide [q9, q8, q7, q6, q5, q4, q3, q2, q1, Function.update_apply] using hya2
        · simp +decide [q9]
      rcases hupd with ⟨z, hz_exec, hz_mem, hz0, hz1, hzwb, hzdb, hzstr, hzk, hzt, hztot,
        hzv, hza1, hza2, hzidx⟩
      refine ⟨z, (ExecWithin.branch_neg (pos := ram[idx ← idx + one]) hcond_nv hz_exec).mono
        (by omega), ?_, ?_⟩
      · refine ⟨hz0, hz1, hzwb, hzdb, hzstr, hzk, hzt, hztot, hzv, hza1, hza2,
          by omega, ?_, ?_, ?_, ?_⟩
        · rw [hz_mem]
          exact modifies_step_update
            (modifies_step_update hymod
              (Finset.mem_union_left _ (matAddr_mem_Ico hstr v c.castSucc))
              (W₁ (Fin.last m) c.castSucc))
            (Finset.mem_union_left _ (matAddr_mem_Ico hstr c.castSucc v))
            (W₁ (Fin.last m) c.castSucc)
        · intro i
          have hne_d1 : db + i.val ≠ wb + c.val * str + v.val := by
            simpa only [Fin.val_castSucc] using
              (matAddr_ne_degAddr hstr hdisj c.castSucc v i.castSucc).symm
          have hne_d2 : db + i.val ≠ wb + v.val * str + c.val := by
            simpa only [Fin.val_castSucc] using
              (matAddr_ne_degAddr hstr hdisj v c.castSucc i.castSucc).symm
          rw [hz_mem, Function.update_of_ne hne_d1, Function.update_of_ne hne_d2]
          exact hydeg i
        · intro c'
          rw [hz_mem]
          have hne1 : wb + m * str + c'.val ≠ wb + c.val * str + v.val := by
            intro h
            have h1 := (matAddr_inj hstr (i₁ := Fin.last m) (j₁ := c'.castSucc)
              (i₂ := c.castSucc) (j₂ := v) h).1
            exact absurd (congrArg Fin.val h1) (by simp; omega)
          have hne2 : wb + m * str + c'.val ≠ wb + v.val * str + c.val := by
            intro h
            have h1 := (matAddr_inj hstr (i₁ := Fin.last m) (j₁ := c'.castSucc)
              (i₂ := v) (j₂ := c.castSucc) h).1
            exact absurd (congrArg Fin.val h1) (by simp; omega)
          rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
          exact hyrowm c'
        · intro i j
          rw [hz_mem, hzidx]
          by_cases h_cv : i = c ∧ j = v_m
          · rcases h_cv with ⟨rfl, rfl⟩
            simp only [v_m, Function.update_self]
            unfold compactStepMatrix embedCompact
            have : ¬ (c.val + 1 ≤ c.val) := by omega
            simp [hcv, this, hW₁.1 c.castSucc (Fin.last m)]
          · have hne_cv : wb + i.val * str + j.val ≠ wb + c.val * str + v.val := by
              intro h
              have hinj := matAddr_inj (by omega : m ≤ str) (i₁ := i) (j₁ := j)
                (i₂ := c) (j₂ := v_m) h
              exact h_cv hinj
            rw [Function.update_of_ne hne_cv]
            by_cases h_vc : i = v_m ∧ j = c
            · rcases h_vc with ⟨rfl, rfl⟩
              simp only [v_m, Function.update_self]
              unfold compactStepMatrix embedCompact
              have : ¬ (c.val + 1 ≤ c.val) := by omega
              simp [hcv, this]
            · have hne_vc : wb + i.val * str + j.val ≠ wb + v.val * str + c.val := by
                intro h
                have hinj := matAddr_inj (by omega : m ≤ str) (i₁ := i) (j₁ := j)
                  (i₂ := v_m) (j₂ := c) h
                exact h_vc hinj
              rw [Function.update_of_ne hne_vc, hymat i j]
              unfold compactStepMatrix
              have hiff1 : (i.val = v.val ∧ j.val ≠ v.val ∧ y.regs idx ≤ j.val) ↔
                  (i.val = v.val ∧ j.val ≠ v.val ∧ c.val + 1 ≤ j.val) := by
                constructor
                · rintro ⟨a1, a2, a3⟩
                  have hjc : j ≠ c := fun h => h_vc ⟨Fin.ext a1, h⟩
                  have := Fin.val_ne_of_ne hjc
                  exact ⟨a1, a2, by dsimp [c] at *; omega⟩
                · rintro ⟨a1, a2, a3⟩
                  exact ⟨a1, a2, by dsimp [c] at *; omega⟩
              have hiff2 : (j.val = v.val ∧ i.val ≠ v.val ∧ y.regs idx ≤ i.val) ↔
                  (j.val = v.val ∧ i.val ≠ v.val ∧ c.val + 1 ≤ i.val) := by
                constructor
                · rintro ⟨a1, a2, a3⟩
                  have hic : i ≠ c := fun h => h_cv ⟨h, Fin.ext a1⟩
                  have := Fin.val_ne_of_ne hic
                  exact ⟨a1, a2, by dsimp [c] at *; omega⟩
                · rintro ⟨a1, a2, a3⟩
                  exact ⟨a1, a2, by dsimp [c] at *; omega⟩
              simp only [hiff1, hiff2]
      · rw [hzidx]; dsimp [c]; omega
  have hx₁_inv : Inv x₁ :=
    ⟨hx₁_0, hx₁_1, hx₁_wb, hx₁_db, hx₁_str, hx₁_k, hx₁_t, hx₁_tot, hx₁_v, hx₁_a1, hx₁_a2,
      by omega, hx₁_mod, hx₁_deg, hx₁_rowm, hx₁_idx ▸ hx₁_mat0⟩
  obtain ⟨y_end, hloop, hy_end, hnc⟩ :=
    ExecWithin.loop_invariant Inv (fun y => m - y.regs idx) hbody hx₁_inv
  rcases hy_end with ⟨hy0, hy1, hywb, hydb, hystr, hyk, hyt, hytot, _, _, _,
    hyidx_le, hymod, hydeg, _, hymat⟩
  have hidx_end : y_end.regs idx = m := by
    simp only [Cond.holds_lt, hyk] at hnc
    omega
  refine ⟨y_end, (hx₁_exec.seq hloop).mono (by rw [hx₁_idx]; omega), hymod,
    ⟨fun i j => by simpa [hidx_end, W₁, compactStepMatrix_full] using hymat i j, hydeg⟩,
    hy0, hy1, hywb, hydb, hystr, hyk, hyt, hytot⟩

/-- Deterministic post-sampling execution: given `x.regs rem = r_val` with
`IsSampledPair W r_val u v`, `postRandStep` contracts `(u, v)` and swap-compacts `Fin.last m` into
slot `v` within `45 * (m + 1) + 22` instructions. -/
theorem postRandStep_exec {w wb db str m t r_val : ℕ}
    {W : Fin (m + 1) → Fin (m + 1) → ℕ} {u v : Fin (m + 1)} {x : Data 16}
    (hm : 2 ≤ m) (hW : IsMultigraph W) (hsamp : IsSampledPair W r_val u v)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hwBase : x.regs wBase = wb) (hdBase : x.regs dBase = db)
    (hstride : x.regs stride = str) (hactiveK : x.regs activeK = m + 1)
    (htargetT : x.regs targetT = t) (htotS : x.regs totS = totalDoubledWeight W)
    (hrem : x.regs rem = r_val)
    (hstr : m + 1 ≤ str) (hdisj : wb + str * (m + 1) ≤ db ∨ db + (m + 1) ≤ wb)
    (hwEnd : Fits w (wb + str * (m + 1))) (hdEnd : Fits w (db + (m + 1)))
    (htot : Fits w (totalDoubledWeight W)) (hws : HoldsWorkspace x.mem wb db str W) :
    ∃ y, ExecWithin w postRandStep x y (45 * (m + 1) + 22) ∧
      Modifies (workspaceFootprint wb db str (m + 1)) x.mem y.mem ∧
      ContractState w wb db str m t (contractMatrix W u v) y ∧
      y.regs zero = 0 ∧ y.regs one = 1 := by
  have huv : u ≠ v := isSampledPair_ne hW hsamp
  obtain ⟨y1, e1, hm1, h1_0, h1_1, h1_wb, h1_db, h1_str, h1_k, h1_t, h1_tot, h1_u, h1_rem⟩ :=
    uScan_exec hsamp h0 h1 hwBase hdBase hstride hactiveK htotS hrem hdEnd htot hws.2
  obtain ⟨y2, e2, hm2, h2_0, h2_1, h2_wb, h2_db, h2_str, h2_k, h2_t, h2_tot, h2_u, h2_v,
      h2_a2, h2_v1⟩ :=
    vScan_exec hsamp h1_0 h1_1 h1_wb h1_db h1_str h1_k h1_tot h1_u h1_rem
      hstr hwEnd hdEnd htot (hm1 ▸ hws.1)
  obtain ⟨y3, e3, hmod3, h3_deg, h3_mat, h3_0, h3_1, h3_wb, h3_db, h3_str, h3_k, h3_t,
      h3_tot, h3_u, h3_v⟩ :=
    phaseADegrees_exec hW huv h2_0 h2_1 h2_wb h2_db h2_str h2_k h2_tot h2_u h2_v h2_a2 h2_v1
      hstr hdisj hdEnd htot (hm2.trans hm1 ▸ hws)
  obtain ⟨y4, e4, hmod4, h4_deg, h4_mat0, h4_0, h4_1, h4_wb, h4_db, h4_str, h4_k, h4_t,
      h4_tot, h4_u, h4_v, h4_a1, h4_a2, h4_idx⟩ :=
    phaseAPtrs_exec hW h3_0 h3_1 h3_wb h3_db h3_str h3_k h3_u h3_v hstr hdisj hwEnd h3_deg h3_mat
  obtain ⟨y5, e5, hmod5, h5_ws, h5_0, h5_1, h5_wb, h5_db, h5_str, h5_k, h5_t, h5_tot,
      h5_u, h5_v⟩ :=
    mergeLoop_exec hW huv h4_0 h4_1 h4_wb h4_db h4_str h4_k h4_u h4_v h4_a1 h4_a2 h4_idx
      hstr hdisj hwEnd hdEnd htot h4_deg h4_mat0
  have hm_fit : Fits w m := hdEnd.of_le (by omega)
  let y6 := y5.set activeK m
  have e6 : ExecWithin w ram[activeK ← activeK - one] y5 y6 1 := by
    simpa [y6, BinOp.eval, h5_k, h5_1] using
      ExecWithin.bin (f := .sub) (d := activeK) (i := activeK) (j := one) (x := y5)
        (by simpa [BinOp.eval, h5_k, h5_1] using hm_fit)
  have hmod15 : Modifies (workspaceFootprint wb db str (m + 1)) x.mem y6.mem := by
    have hmod_x_y3 : Modifies (workspaceFootprint wb db str (m + 1)) x.mem y3.mem := by
      simpa only [hm2, hm1] using hmod3
    exact modifies_trans_subset
      (modifies_trans_subset hmod_x_y3 hmod4 Finset.Subset.rfl Finset.Subset.rfl)
      hmod5 Finset.Subset.rfl Finset.Subset.rfl
  have htot_c_fit : Fits w (totalDoubledWeight (contractMatrix W u v)) := by
    have := totalDoubledWeight_contractMatrix hW huv
    exact htot.of_le (by omega)
  have hdisj_m : wb + str * m ≤ db ∨ db + m ≤ wb := by
    have : str * m ≤ str * (m + 1) := Nat.mul_le_mul_left str (Nat.le_succ m)
    omega
  by_cases hv_lt : v.val < m
  · have hcond : (Cond.lt vReg activeK).Holds y6 := by
      have hv6 : y6.regs vReg = v.val := by simpa +decide [y6, Function.update_apply] using h5_v
      simp only [Cond.holds_lt, hv6]
      exact hv_lt
    obtain ⟨y7, e7, hmod7, h7_ws, h7_0, h7_1, h7_wb, h7_db, h7_str, h7_k, h7_t, h7_tot⟩ :=
      compactPhase_exec (x := y6) (u := u) hW hv_lt
        (by simpa +decide [y6, Function.update_apply] using h5_0)
        (by simpa +decide [y6, Function.update_apply] using h5_1)
        (by simpa +decide [y6, Function.update_apply] using h5_wb)
        (by simpa +decide [y6, Function.update_apply] using h5_db)
        (by simpa +decide [y6, Function.update_apply] using h5_str)
        rfl
        (by simpa +decide [y6, Function.update_apply] using h5_v)
        hstr hdisj hwEnd hdEnd h5_ws
    have hbr := ExecWithin.branch_pos (neg := ram[idx ← #0]) hcond e7
    refine ⟨y7, ?_, modifies_trans_subset hmod15 hmod7 Finset.Subset.rfl Finset.Subset.rfl,
      ?_, h7_0, h7_1⟩
    · unfold postRandStep
      exact (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq hbr)))))).mono (by omega)
    · exact {
        regs_wBase := h7_wb
        regs_dBase := h7_db
        regs_stride := h7_str
        regs_activeK := h7_k
        regs_targetT := by
          rw [h7_t]
          have : y6.regs targetT = y5.regs targetT := by simp +decide [y6]
          rw [this, h5_t, h4_t, h3_t, h2_t, h1_t, htargetT]
        regs_totS := by
          rw [h7_tot]
          have : y6.regs totS = y5.regs totS := by simp +decide [y6]
          rw [this, h5_tot, h4_tot, h3_tot]
        le_stride := by omega
        disjoint_blocks := hdisj_m
        fits_wEnd := hwEnd.of_le (by
          have : str * m ≤ str * (m + 1) := Nat.mul_le_mul_left str (Nat.le_succ m)
          omega)
        fits_dEnd := hdEnd.of_le (by omega)
        fits_totS := htot_c_fit
        workspace := h7_ws
      }
  · have hv_eq_m : v.val = m := by have := v.isLt; omega
    have hcond : ¬ (Cond.lt vReg activeK).Holds y6 := by
      have hv6 : y6.regs vReg = v.val := by simpa +decide [y6, Function.update_apply] using h5_v
      simp only [Cond.holds_lt, hv6]
      exact hv_lt
    let y7 := y6.set idx 0
    have e7 := ExecWithin.branch_neg (pos := ram[⟪compactSetup⟫;
        while idx < activeK do [ ⟪compactBody⟫ ]]) hcond
      (ExecWithin.const (B := .standard) (d := idx) (x := y6) (fits_zero w))
    have hws_m : HoldsWorkspace y7.mem wb db str (contractMatrix W u v) := by
      constructor
      · intro i j
        have hi : embedCompact v i = i.castSucc := by
          unfold embedCompact
          have : i.val ≠ v.val := by have := i.isLt; omega
          simp [this]
        have hj : embedCompact v j = j.castSucc := by
          unfold embedCompact
          have : j.val ≠ v.val := by have := j.isLt; omega
          simp [this]
        have h1 : y5.mem (wb + i.val * str + j.val) = mergePair W u v i.castSucc j.castSucc :=
          h5_ws.1 i.castSucc j.castSucc
        change y5.mem (wb + i.val * str + j.val) = _
        rw [h1]
        unfold contractMatrix
        rw [hi, hj]
      · intro i
        have hi : embedCompact v i = i.castSucc := by
          unfold embedCompact
          have : i.val ≠ v.val := by have := i.isLt; omega
          simp [this]
        have h2 : y5.mem (db + i.val) = rowDeg (mergePair W u v) i.castSucc :=
          h5_ws.2 i.castSucc
        change y5.mem (db + i.val) = _
        rw [h2, rowDeg_contractMatrix, hi]
    refine ⟨y7, ?_, hmod15, ?_,
      by simpa +decide [y7, y6, Function.update_apply] using h5_0,
      by simpa +decide [y7, y6, Function.update_apply] using h5_1⟩
    · unfold postRandStep
      exact (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))).mono (by omega)
    · exact {
        regs_wBase := by simpa +decide [y7, y6, Function.update_apply] using h5_wb
        regs_dBase := by simpa +decide [y7, y6, Function.update_apply] using h5_db
        regs_stride := by simpa +decide [y7, y6, Function.update_apply] using h5_str
        regs_activeK := by simp +decide [y7, y6]
        regs_targetT := by
          have : y7.regs targetT = y5.regs targetT := by
            simp +decide [y7, y6]
          rw [this, h5_t, h4_t, h3_t, h2_t, h1_t, htargetT]
        regs_totS := by
          have : y7.regs totS = y5.regs totS := by simp +decide [y7, y6]
          rw [this, h5_tot, h4_tot, h3_tot]
        le_stride := by omega
        disjoint_blocks := hdisj_m
        fits_wEnd := hwEnd.of_le (by
          have : str * m ≤ str * (m + 1) := Nat.mul_le_mul_left str (Nat.le_succ m)
          omega)
        fits_dEnd := hdEnd.of_le (by omega)
        fits_totS := htot_c_fit
        workspace := hws_m
      }

/-! #### `PMF.toOuterMeasure` helpers for step-count maps and `contractDownTo_spec` -/

private theorem eval_map_snd_toOuterMeasure {α : Type} (m : ProbComp (α × ℕ))
    (g : α × ℕ → ℕ) (P : α → Prop) :
    (((fun z => (z.1, g z)) <$> m).eval).toOuterMeasure {z | P z.1} =
      m.eval.toOuterMeasure {z | P z.1} := by
  rw [ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
  rfl

private theorem step_budget_succ {t m n_post z₂ : ℕ} (ht : 2 ≤ t) (hm : t ≤ m)
    (hn : n_post ≤ 45 * (m + 1) + 22) (hz : z₂ ≤ 36 * (m ^ 2 - t ^ 2) + 2) :
    (1 + (1 + n_post) + 2) + z₂ + 2 ≤ 36 * ((m + 1) ^ 2 - t ^ 2) + 2 := by
  have ht2 : t ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hm 2
  have hm2 : t ^ 2 ≤ (m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hsq : (m ^ 2 - t ^ 2) + (2 * m + 1) = (m + 1) ^ 2 - t ^ 2 := by
    zify [ht2, hm2]
    ring
  have hlin : 36 * (m ^ 2 - t ^ 2) + 36 * (2 * m + 1) = 36 * ((m + 1) ^ 2 - t ^ 2) := by
    rw [← Nat.mul_add, hsq]
  omega

/-- Target survival predicate on final `Data 16`: memory holds a contracted `t`-supervertex
multigraph `W'` along `part'` where some active cut `B'` pulls back to `C_star`. -/
def SurvivalPost {n : ℕ} (W₀ : Fin n → Fin n → ℕ) (wb db str t : ℕ)
    (C_star : Finset (Fin n)) (y : Data 16) : Prop :=
  ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t) (B' : Finset (Fin t)),
    IsContractionOf W₀ part' W' ∧
    HoldsWorkspace y.mem wb db str W' ∧
    y.regs totS = totalDoubledWeight W' ∧
    pullbackCut part' B' = C_star

private theorem contractLoop_spec {n w wb db str t steps : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W : Fin (t + steps) → Fin (t + steps) → ℕ} {part : Fin n → Fin (t + steps)} {x : Data 16}
    (ht : 2 ≤ t) (hC : IsContractionOf W₀ part W)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hst : ContractState w wb db str (t + steps) t W x) :
    ∃ m : ProbComp (Data 16 × ℕ),
      ExecRand w ram[while targetT < activeK do [ ⟪contractStep⟫ ]] x m ∧
      m.IsQueryBounded steps ∧
      (∀ z ∈ m.support,
        z.2 ≤ 36 * ((t + steps) ^ 2 - t ^ 2) + 2 ∧
        Modifies (workspaceFootprint wb db str (t + steps)) x.mem z.1.mem ∧
        ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
          IsContractionOf W₀ part' W' ∧
          ContractState w wb db str t t W' z.1) ∧
      (∀ B : Finset (Fin (t + steps)),
        0 < minCut W₀ → IsNonTrivialCut B →
        cutWeight W₀ (pullbackCut part B) = minCut W₀ →
        (((t * (t - 1) : ℕ) : ℝ≥0∞) / (((t + steps) * (t + steps - 1) : ℕ) : ℝ≥0∞)) ≤
          m.eval.toOuterMeasure {z | SurvivalPost W₀ wb db str t (pullbackCut part B) z.1}) := by
  induction steps generalizing x with
  | zero =>
    have hk_eq : t + 0 = t := Nat.add_zero t
    have hnc : ¬ (Cond.lt targetT activeK).Holds x := by
      simp [hst.regs_targetT, hst.regs_activeK]
    refine ⟨pure (x, 2), ExecRand.loop_exit hnc, .pure _ 0, ?_, ?_⟩
    · intro z hz
      cases OracleComp.eq_of_mem_supportWith_pure hz
      refine ⟨by simp, Modifies.refl _ _, ?_⟩
      cases hk_eq
      exact ⟨W, part, hC, hst⟩
    · intro B _ _ _
      simp only [Nat.add_zero, ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply]
      have ht_pos : 0 < t * (t - 1) := Nat.mul_pos (by omega) (by omega)
      have hne0 : (((t * (t - 1) : ℕ) : ℝ≥0∞)) ≠ 0 := by exact_mod_cast ht_pos.ne'
      have htop : (((t * (t - 1) : ℕ) : ℝ≥0∞)) ≠ ⊤ := ENNReal.natCast_ne_top _
      rw [ENNReal.div_self hne0 htop]
      have hmem : (x, 2) ∈ {z : Data 16 × ℕ |
          SurvivalPost W₀ wb db str t (pullbackCut part B) z.1} := by
        cases hk_eq
        exact ⟨W, part, B, hC, hst.workspace, hst.regs_totS, rfl⟩
      simp [hmem]
  | succ s ih =>
    let m_cur := t + s
    have hm_def : m_cur = t + s := rfl
    have hm_ge : 2 ≤ m_cur := by omega
    have hc_loop : (Cond.lt targetT activeK).Holds x := by
      simp only [Cond.holds_lt, hst.regs_targetT, hst.regs_activeK]
      omega
    by_cases hS0 : totalDoubledWeight W = 0
    · -- Zero-weight branch: `totS = 0`, deterministic merge of `(0, Fin.last m_cur)` in `0` calls.
      have hcond_z : (Cond.eq totS zero).Holds x := by
        simp [hst.regs_totS, hS0, h0]
      have hm_fit : Fits w m_cur := hst.fits_dEnd.of_le (by omega)
      let x_next := x.set activeK m_cur
      have hsub1 : (t + (s + 1)) - 1 = m_cur := by omega
      have hop : (Op.bin .sub activeK activeK one).eval w x = some x_next := by
        simp only [Op.eval_bin, BinOp.eval, hst.regs_activeK, h1, hsub1]
        exact Data.put_of_fits hm_fit
      have hstep_det : ExecRand w contractStep x (pure (x_next, 2)) := by
        unfold contractStep
        simpa only [map_pure] using ExecRand.branch_pos hcond_z (ExecRand.op hop)
      let u₀ : Fin (m_cur + 1) := ⟨0, by omega⟩
      let v₀ : Fin (m_cur + 1) := Fin.last m_cur
      have huv₀ : u₀ ≠ v₀ := by
        intro h
        have := congrArg Fin.val h
        change 0 = m_cur at this
        omega
      have hW_zero : ∀ a b : Fin (m_cur + 1), W a b = 0 := fun a b => by
        have := entry_le_totalDoubledWeight W a b
        omega
      have hcm_zero : ∀ i j : Fin m_cur, contractMatrix W u₀ v₀ i j = 0 := fun i j => by
        unfold contractMatrix mergePair
        simp [hW_zero]
      have hdeg_cm_zero : ∀ i : Fin m_cur, rowDeg (contractMatrix W u₀ v₀) i = 0 := fun i => by
        unfold rowDeg
        simp [hcm_zero]
      have htot_cm_zero : totalDoubledWeight (contractMatrix W u₀ v₀) = 0 := by
        unfold totalDoubledWeight
        simp [hdeg_cm_zero]
      have hws_next : HoldsWorkspace x_next.mem wb db str (contractMatrix W u₀ v₀) := by
        refine ⟨fun i j => ?_, fun i => ?_⟩
        · have hw1 : x.mem (wb + i.val * str + j.val) = W i.castSucc j.castSucc :=
            hst.workspace.1 i.castSucc j.castSucc
          change x.mem (wb + i.val * str + j.val) = _
          rw [hw1, hW_zero, hcm_zero]
        · have hw2 : x.mem (db + i.val) = rowDeg W i.castSucc :=
            hst.workspace.2 i.castSucc
          change x.mem (db + i.val) = _
          rw [hw2, hdeg_cm_zero]
          unfold rowDeg
          simp [hW_zero]
      have hmul_le : str * m_cur ≤ str * (t + (s + 1)) := Nat.mul_le_mul_left str (by omega)
      have hst_next : ContractState w wb db str m_cur t (contractMatrix W u₀ v₀) x_next := {
        regs_wBase := by simpa +decide [x_next, Function.update_apply] using hst.regs_wBase
        regs_dBase := by simpa +decide [x_next, Function.update_apply] using hst.regs_dBase
        regs_stride := by simpa +decide [x_next, Function.update_apply] using hst.regs_stride
        regs_activeK := by simp +decide [x_next]
        regs_targetT := by simpa +decide [x_next, Function.update_apply] using hst.regs_targetT
        regs_totS := by
          have : x_next.regs totS = x.regs totS := by
            simp +decide [x_next]
          rw [this, hst.regs_totS, hS0, htot_cm_zero]
        le_stride := by have := hst.le_stride; omega
        disjoint_blocks := by have := hst.disjoint_blocks; omega
        fits_wEnd := hst.fits_wEnd.of_le (by omega)
        fits_dEnd := hst.fits_dEnd.of_le (by omega)
        fits_totS := by rw [htot_cm_zero]; exact fits_zero w
        workspace := hws_next
      }
      have hC_next : IsContractionOf W₀ (contractPart part u₀ v₀ huv₀)
          (contractMatrix W u₀ v₀) := isContractionOf_contract hC huv₀
      obtain ⟨m_tail, hm_tail, hq_tail, hsup_tail, _⟩ := ih hC_next
        (by simpa +decide [x_next, Function.update_apply] using h0)
        (by simpa +decide [x_next, Function.update_apply] using h1)
        hst_next
      have hiter := ExecRand.loop_iter hc_loop hstep_det (ml := fun _ => m_tail) fun z hz => by
        cases OracleComp.eq_of_mem_supportWith_pure hz
        exact hm_tail
      refine ⟨_, hiter, ?_, ?_, ?_⟩
      · rw [pure_bind]
        exact (hq_tail.bind fun _ => .pure _ 0).mono (by omega)
      · intro z hz
        obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
        cases OracleComp.eq_of_mem_supportWith_pure hz₁
        obtain ⟨z₂, hz₂, hfinal⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
        cases OracleComp.eq_of_mem_supportWith_pure hfinal
        rcases hsup_tail z₂ hz₂ with ⟨htime₂, hmod₂, W', part', hC', hst'⟩
        refine ⟨?_, ?_, W', part', hC', hst'⟩
        · have hbud := step_budget_succ ht (by omega : t ≤ m_cur) (Nat.zero_le _) htime₂
          change 2 + z₂.2 + 2 ≤ 36 * ((m_cur + 1) ^ 2 - t ^ 2) + 2
          omega
        · exact modifies_trans_subset (Modifies.refl _ x.mem) hmod₂
            Finset.Subset.rfl (workspaceFootprint_mono (Nat.le_succ m_cur))
      · -- Vacuous when `0 < minCut W₀` since `0 < minCut W₀ ≤ minCut W` forces `0 < totS`.
        intro B hmin_pos _ _
        have hminW : 0 < minCut W :=
          lt_of_lt_of_le hmin_pos
            (minCut_le_of_isContractionOf (by rw [Fintype.card_fin]; omega) hC)
        have hS_pos := totalDoubledWeight_pos_of_minCut_pos (by rw [Fintype.card_fin]; omega)
          hC.multigraph hminW
        omega
    · -- Positive-weight branch: `0 < totalDoubledWeight W`.
      have hS_pos : 0 < totalDoubledWeight W := Nat.pos_of_ne_zero hS0
      let S := totalDoubledWeight W
      have hS_def : S = totalDoubledWeight W := rfl
      have hcond_nz : ¬ (Cond.eq totS zero).Holds x := by
        simp [hst.regs_totS, h0, hS0]
      have hSm1_fit : Fits w (S - 1) := hst.fits_totS.of_le (by omega)
      let x_sub := x.set val1 (S - 1)
      have hop_sub : (Op.bin .sub val1 totS one).eval w x = some x_sub := by
        simp only [Op.eval_bin, BinOp.eval, hst.regs_totS, h1]
        exact Data.put_of_fits hSm1_fit
      have hfit_rand : Fits w (x_sub.regs val1) := by simpa [x_sub] using hSm1_fit
      have hper_sample : ∀ k : Fin (x_sub.regs val1 + 1),
          ∃ (u v : Fin (m_cur + 1)) (huv : u ≠ v) (y_post : Data 16) (n_post : ℕ)
            (m_rec : ProbComp (Data 16 × ℕ)),
            IsSampledPair W k.val u v ∧
            n_post ≤ 45 * (m_cur + 1) + 22 ∧
            Exec w postRandStep (x_sub.set rem k.val) y_post n_post ∧
            Modifies (workspaceFootprint wb db str (m_cur + 1)) x.mem y_post.mem ∧
            ContractState w wb db str m_cur t (contractMatrix W u v) y_post ∧
            ExecRand w ram[while targetT < activeK do [ ⟪contractStep⟫ ]] y_post m_rec ∧
            m_rec.IsQueryBounded s ∧
            (∀ z ∈ m_rec.support,
              z.2 ≤ 36 * (m_cur ^ 2 - t ^ 2) + 2 ∧
              Modifies (workspaceFootprint wb db str m_cur) y_post.mem z.1.mem ∧
              ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
                IsContractionOf W₀ part' W' ∧
                ContractState w wb db str t t W' z.1) ∧
            (∀ B' : Finset (Fin m_cur),
              0 < minCut W₀ → IsNonTrivialCut B' →
              cutWeight W₀ (pullbackCut (contractPart part u v huv) B') = minCut W₀ →
              (((t * (t - 1) : ℕ) : ℝ≥0∞) / ((m_cur * (m_cur - 1) : ℕ) : ℝ≥0∞)) ≤
                m_rec.eval.toOuterMeasure
                  {z | SurvivalPost W₀ wb db str t
                    (pullbackCut (contractPart part u v huv) B') z.1}) := by
        intro k
        have hk_lt : k.val < S := by
          have hk_bound := k.isLt
          simp only [x_sub, Data.set_regs, Function.update_self] at hk_bound
          omega
        obtain ⟨u, v, hsamp⟩ := exists_isSampledPair W hk_lt
        have huv : u ≠ v := isSampledPair_ne hC.multigraph hsamp
        obtain ⟨y_post, ⟨n_post, hn_post, he_post⟩, hmod_post, hst_post, hy0, hy1⟩ :=
          postRandStep_exec (x := x_sub.set rem k.val) (t := t) hm_ge hC.multigraph hsamp
            (by simpa +decide [x_sub, Function.update_apply] using h0)
            (by simpa +decide [x_sub, Function.update_apply] using h1)
            (by simpa +decide [x_sub, Function.update_apply] using hst.regs_wBase)
            (by simpa +decide [x_sub, Function.update_apply] using hst.regs_dBase)
            (by simpa +decide [x_sub, Function.update_apply] using hst.regs_stride)
            (by
              have hk_sub : (x_sub.set rem k.val).regs activeK = t + (s + 1) := by
                simpa +decide [x_sub, Function.update_apply] using hst.regs_activeK
              omega)
            (by simpa +decide [x_sub, Function.update_apply] using hst.regs_targetT)
            (by simpa +decide [x_sub, Function.update_apply] using hst.regs_totS)
            (by simp +decide)
            hst.le_stride hst.disjoint_blocks hst.fits_wEnd hst.fits_dEnd hst.fits_totS
            hst.workspace
        obtain ⟨m_rec, hm_rec, hq_rec, hsup_rec, hsurv_rec⟩ :=
          ih (isContractionOf_contract hC huv) hy0 hy1 hst_post
        exact ⟨u, v, huv, y_post, n_post, m_rec, hsamp, hn_post, he_post, hmod_post, hst_post,
          hm_rec, hq_rec, hsup_rec, hsurv_rec⟩
      -- Assemble `ExecRand` for `contractStep` via `codeComp`.
      let m_post (d : Data 16) := codeComp w postRandStep d
      have hrand_post : ExecRand w ram[rem ← rand val1; ⟪postRandStep⟫] x_sub
          (do
            let z₁ ← (do
              let k ← ProbComp.unifFin (x_sub.regs val1)
              pure (x_sub.set rem k.val, 1))
            let z₂ ← m_post z₁.1
            pure (z₂.1, z₁.2 + z₂.2)) := by
        refine ExecRand.seq (ExecRand.rand hfit_rand) fun z₁ hz₁ => ?_
        obtain ⟨k, -, hk_eq'⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₁
        cases OracleComp.eq_of_mem_supportWith_pure hk_eq'
        obtain ⟨_, _, _, y_post, n_post, _, _, _, he_post, _, _, _, _, _, _⟩ := hper_sample k
        dsimp only [m_post]
        rw [he_post.execRand.codeComp_eq]
        exact he_post.execRand
      have hsub_rand_post := (Exec.op hop_sub).seqRand hrand_post
      have hstep_rand : ExecRand w contractStep x
          ((fun z => (z.1, z.2 + 2)) <$> ((fun z => (z.1, 1 + z.2)) <$> (do
            let z₁ ← (do
              let k ← ProbComp.unifFin (x_sub.regs val1)
              pure (x_sub.set rem k.val, 1))
            let z₂ ← m_post z₁.1
            pure (z₂.1, z₁.2 + z₂.2)))) :=
        ExecRand.branch_neg hcond_nz hsub_rand_post
      let m_loop_rec (d : Data 16) :=
        codeComp w ram[while targetT < activeK do [ ⟪contractStep⟫ ]] d
      let mb := (fun z : Data 16 × ℕ => (z.1, z.2 + 2)) <$> ((fun z => (z.1, 1 + z.2)) <$> (do
        let z₁ ← (do
          let k ← ProbComp.unifFin (x_sub.regs val1)
          pure (x_sub.set rem k.val, 1))
        let z₂ ← m_post z₁.1
        pure (z₂.1, z₁.2 + z₂.2)))
      have hmb_support : ∀ z ∈ mb.support, ∃ k : Fin (x_sub.regs val1 + 1),
          ∃ (u v : Fin (m_cur + 1)) (huv : u ≠ v) (y_post : Data 16) (n_post : ℕ)
            (m_rec : ProbComp (Data 16 × ℕ)),
            z = (y_post, (1 + (1 + n_post)) + 2) ∧
            IsSampledPair W k.val u v ∧
            n_post ≤ 45 * (m_cur + 1) + 22 ∧
            Modifies (workspaceFootprint wb db str (m_cur + 1)) x.mem y_post.mem ∧
            m_loop_rec y_post = m_rec ∧
            ExecRand w ram[while targetT < activeK do [ ⟪contractStep⟫ ]] y_post m_rec ∧
            m_rec.IsQueryBounded s ∧
            (∀ z' ∈ m_rec.support,
              z'.2 ≤ 36 * (m_cur ^ 2 - t ^ 2) + 2 ∧
              Modifies (workspaceFootprint wb db str m_cur) y_post.mem z'.1.mem ∧
              ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
                IsContractionOf W₀ part' W' ∧
                ContractState w wb db str t t W' z'.1) := by
        intro z hz
        obtain ⟨za, hza, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
        obtain ⟨zb, hzb, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hza
        obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hzb
        obtain ⟨k, -, hk_pure⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₁
        cases OracleComp.eq_of_mem_supportWith_pure hk_pure
        obtain ⟨u, v, huv, y_post, n_post, m_rec, hsamp, hn_post, he_post, hmod_post, _,
          hm_rec, hq_rec, hsup_rec, _⟩ := hper_sample k
        obtain ⟨z₂, hz₂, hzb_pure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
        cases OracleComp.eq_of_mem_supportWith_pure hzb_pure
        dsimp only [m_post] at hz₂
        rw [he_post.execRand.codeComp_eq] at hz₂
        cases OracleComp.eq_of_mem_supportWith_pure hz₂
        have hml_eq : m_loop_rec y_post = m_rec := hm_rec.codeComp_eq
        exact ⟨k, u, v, huv, y_post, n_post, m_rec, rfl, hsamp, hn_post, hmod_post,
          hml_eq, hm_rec, hq_rec, hsup_rec⟩
      have hiter : ExecRand w ram[while targetT < activeK do [ ⟪contractStep⟫ ]] x
          (do
            let z₁ ← mb
            let z₂ ← m_loop_rec z₁.1
            pure (z₂.1, z₁.2 + z₂.2 + 2)) := by
        refine ExecRand.loop_iter hc_loop hstep_rand fun z₁ hz₁ => ?_
        obtain ⟨_, _, _, _, _, _, m_rec, rfl, _, _, _, hml_eq, hm_rec, _, _⟩ := hmb_support z₁ hz₁
        rw [hml_eq]
        exact hm_rec
      have hmb_qb : mb.IsQueryBounded 1 := by
        dsimp only [mb]
        simp only [OracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
        have hrand_qb : (do
            let k ← ProbComp.unifFin (x_sub.regs val1)
            pure (x_sub.set rem k.val, 1)).IsQueryBounded 1 := by
          simpa only [Nat.add_zero] using
            (ProbComp.isQueryBounded_unifFin (x_sub.regs val1)).bind fun _ => .pure _ 0
        have hpost_qb : ∀ z₁ ∈ (do
            let k ← ProbComp.unifFin (x_sub.regs val1)
            pure (x_sub.set rem k.val, 1)).support,
            (m_post z₁.1 >>= fun z₂ => pure (z₂.1, z₁.2 + z₂.2)).IsQueryBounded 0 := by
          intro z₁ hz₁
          obtain ⟨k, -, hk_p⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₁
          cases OracleComp.eq_of_mem_supportWith_pure hk_p
          obtain ⟨_, _, _, _, _, _, _, _, he_post, _, _, _, _, _, _⟩ := hper_sample k
          dsimp only [m_post]
          rw [he_post.execRand.codeComp_eq, pure_bind]
          exact .pure _ 0
        simpa only [Nat.add_zero] using
          OracleComp.IsCostBounded.bind_on_support hrand_qb hpost_qb
      refine ⟨_, hiter, ?_, ?_, ?_⟩
      · have htot_qb : (1 : ℕ) + s = s + 1 := Nat.add_comm 1 s
        rw [← htot_qb]
        refine OracleComp.IsCostBounded.bind_on_support hmb_qb fun z₁ hz₁ => ?_
        obtain ⟨_, _, _, _, _, _, m_rec, rfl, _, _, _, hml_eq, _, hq_rec, _⟩ := hmb_support z₁ hz₁
        rw [hml_eq]
        simpa only [Nat.add_zero] using hq_rec.bind fun _ => .pure _ 0
      · intro z hz
        obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
        obtain ⟨k, u, v, huv, y_post, n_post, m_rec, rfl, _, hn_post, hmod_post,
          hml_eq, _, _, hsup_rec⟩ := hmb_support z₁ hz₁
        rw [hml_eq] at hrest
        obtain ⟨z₂, hz₂, hfinal⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
        cases OracleComp.eq_of_mem_supportWith_pure hfinal
        rcases hsup_rec z₂ hz₂ with ⟨htime₂, hmod₂, W', part', hC', hst'⟩
        refine ⟨?_, ?_, W', part', hC', hst'⟩
        · exact step_budget_succ ht (by omega : t ≤ m_cur) hn_post htime₂
        · exact modifies_trans_subset hmod_post hmod₂ Finset.Subset.rfl
            (workspaceFootprint_mono (Nat.le_succ m_cur))
      · -- Telescoping survival probability bound.
        intro B hmin_pos hB_nt hB_min
        let C_star := pullbackCut part B
        let E : Set (Data 16 × ℕ) := {z | SurvivalPost W₀ wb db str t C_star z.1}
        have hN_eq : x_sub.regs val1 + 1 = S := by
          simp only [x_sub, Data.set_regs, Function.update_self]
          omega
        have hm_simp : (do
            let z₁ ← mb
            let z₂ ← m_loop_rec z₁.1
            pure (z₂.1, z₁.2 + z₂.2 + 2)) = (do
            let k ← ProbComp.unifFin (x_sub.regs val1)
            let zp ← m_post (x_sub.set rem k.val)
            let z₂ ← m_loop_rec zp.1
            pure (z₂.1, ((1 + (1 + zp.2)) + 2) + z₂.2 + 2)) := by
          dsimp only [mb]
          simp only [← bind_pure_comp, bind_assoc, pure_bind]
        rw [hm_simp, ProbComp.eval_bind]
        let castFin : Fin (x_sub.regs val1 + 1) ≃ Fin (totalDoubledWeight W) := finCongr hN_eq
        let survSet : Set (Fin (x_sub.regs val1 + 1)) :=
          {k | SampleSurvives W B (castFin k)}
        have hdeg_bound : (m_cur + 1) * cutWeight W B ≤ totalDoubledWeight W := by
          have hcw_eq : cutWeight W B = minCut W₀ := by
            rw [← cutWeight_pullbackCut hC B, hB_min]
          rw [hcw_eq]
          have hmul := mul_minCut_le_totalDoubledWeight (by rw [Fintype.card_fin]; omega)
            hC.multigraph
          rw [Fintype.card_fin] at hmul
          exact (Nat.mul_le_mul_left (m_cur + 1)
            (minCut_le_of_isContractionOf (by rw [Fintype.card_fin]; omega) hC)).trans hmul
        have hstep_prob : (((m_cur - 1 : ℕ) : ℝ≥0∞) / (m_cur + 1 : ℕ)) ≤
            (ProbComp.unifFin (x_sub.regs val1)).eval.toOuterMeasure survSet := by
          rw [ProbComp.eval_unifFin]
          let _ : Nonempty (Fin (x_sub.regs val1 + 1)) := ⟨⟨0, by omega⟩⟩
          let _ : Nonempty (Fin (totalDoubledWeight W)) := ⟨⟨0, hS_pos⟩⟩
          have hmap_u : Cslib.Probability.PMF.uniformOfFintype (Fin (totalDoubledWeight W)) =
              (Cslib.Probability.PMF.uniformOfFintype
                (Fin (x_sub.regs val1 + 1))).map castFin :=
            (Cslib.Probability.PMF.uniformOfFintype_map_equiv castFin).symm
          have h1_step := step_survival_prob_ge (by omega : 2 ≤ m_cur + 1) hC.multigraph
            hS_pos hdeg_bound
          have hsub_m : m_cur + 1 - 2 = m_cur - 1 := by omega
          rw [hsub_m, hmap_u, PMF.toOuterMeasure_map_apply] at h1_step
          exact h1_step
        have hsub_ms : t + (s + 1) - 1 = m_cur := by omega
        have hm_add : t + (s + 1) = m_cur + 1 := rfl
        have htele : (((m_cur - 1 : ℕ) : ℝ≥0∞) / (m_cur + 1 : ℕ)) *
            (((t * (t - 1) : ℕ) : ℝ≥0∞) / ((m_cur * (m_cur - 1) : ℕ) : ℝ≥0∞)) =
            (((t * (t - 1) : ℕ) : ℝ≥0∞) / (((t + (s + 1)) * (t + (s + 1) - 1) : ℕ) : ℝ≥0∞)) := by
          rw [hsub_ms, hm_add]
          exact telescope_survival_step ht (by omega : t ≤ m_cur)
        rw [← htele]
        refine toOuterMeasure_bind_ge_mul_ennreal _ _ survSet E hstep_prob ?_
        intro k _ hk_surv
        obtain ⟨u, v, huv, y_post, n_post, m_rec, hsamp, _, he_post, _, _,
          hm_rec, _, _, hsurv_rec⟩ := hper_sample k
        have hmp_eq : m_post (x_sub.set rem k.val) = pure (y_post, n_post) :=
          he_post.execRand.codeComp_eq
        have hml_eq : m_loop_rec y_post = m_rec := hm_rec.codeComp_eq
        have hcont_eq : (do
            let zp ← m_post (x_sub.set rem k.val)
            let z₂ ← m_loop_rec zp.1
            pure (z₂.1, ((1 + (1 + zp.2)) + 2) + z₂.2 + 2)) =
              ((fun z₂ => (z₂.1, ((1 + (1 + n_post)) + 2) + z₂.2 + 2)) <$> m_rec) := by
          rw [hmp_eq, pure_bind, hml_eq, ← bind_pure_comp]
        rw [hcont_eq, eval_map_snd_toOuterMeasure]
        rcases hk_surv with ⟨u', v', hsamp', hsame'⟩
        have hcast_val : (castFin k).val = k.val := rfl
        rw [hcast_val] at hsamp'
        rcases isSampledPair_unique W hsamp hsamp' with ⟨rfl, rfl⟩
        let B' := contractCut v B
        have hpb_eq : pullbackCut (contractPart part u v huv) B' = C_star :=
          pullbackCut_contractCut part huv hsame'
        have hC_star_nt : IsNonTrivialCut C_star :=
          isNonTrivialCut_pullbackCut hC.surj hB_nt
        have hB'_nt : IsNonTrivialCut B' :=
          isNonTrivialCut_of_pullbackCut (contractPart part u v huv) (hpb_eq ▸ hC_star_nt)
        have hB'_min : cutWeight W₀ (pullbackCut (contractPart part u v huv) B') = minCut W₀ := by
          rw [hpb_eq]
          exact hB_min
        simpa only [hpb_eq] using hsurv_rec B' hmin_pos hB'_nt hB'_min

/-- **Master specification for `contractDownTo` (`Code .standard 16`).**
Starting from any `ContractState w wb db str k t W x` (`2 ≤ t ≤ k`) where `W` is a contraction of
`W₀` along `part`, `contractDownTo`:
1. terminates fault-free on every path (`ExecRand`),
2. issues at most `k - t` `rand` calls (`IsQueryBounded (k - t)`),
3. executes at most `36 * (k ^ 2 - t ^ 2) + 4` instructions on every path, modifying only
   `workspaceFootprint wb db str k` and leaving a valid `t`-supervertex `ContractState` that is a
   contraction of `W₀`, and
4. preserves any fixed minimum cut `pullbackCut part B` of a connected multigraph (`0 < minCut W₀`)
   with probability at least `(t * (t - 1)) / (k * (k - 1))`. -/
theorem contractDownTo_spec {n w wb db str k t : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 16}
    (ht : 2 ≤ t) (htk : t ≤ k) (hC : IsContractionOf W₀ part W)
    (hst : ContractState w wb db str k t W x) :
    ∃ m : ProbComp (Data 16 × ℕ),
      ExecRand w contractDownTo x m ∧
      m.IsQueryBounded (k - t) ∧
      (∀ z ∈ m.support,
        z.2 ≤ 36 * (k ^ 2 - t ^ 2) + 4 ∧
        Modifies (workspaceFootprint wb db str k) x.mem z.1.mem ∧
        ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
          IsContractionOf W₀ part' W' ∧
          ContractState w wb db str t t W' z.1) ∧
      (∀ B : Finset (Fin k),
        0 < minCut W₀ → IsNonTrivialCut B →
        cutWeight W₀ (pullbackCut part B) = minCut W₀ →
        (((t * (t - 1) : ℕ) : ℝ≥0∞) / ((k * (k - 1) : ℕ) : ℝ≥0∞)) ≤
          m.eval.toOuterMeasure {z | SurvivalPost W₀ wb db str t (pullbackCut part B) z.1}) := by
  have hk_split : t + (k - t) = k := Nat.add_sub_of_le htk
  revert W part hst
  rw [← hk_split]
  intro W part hC hst
  have h1_fit : Fits w 1 := hst.fits_dEnd.of_le (by omega)
  let x₁ := (x.set zero 0).set one 1
  have e0 : Exec w (Code.op (.const zero 0)) x (x.set zero 0) 1 :=
    Exec.const (B := .standard) (d := zero) (x := x) (fits_zero w)
  have e1 : Exec w (Code.op (.const one 1)) (x.set zero 0) x₁ 1 :=
    Exec.const (B := .standard) (d := one) (x := x.set zero 0) h1_fit
  have hst₁ : ContractState w wb db str (t + (k - t)) t W x₁ := {
    regs_wBase := by simpa +decide [x₁, Function.update_apply] using hst.regs_wBase
    regs_dBase := by simpa +decide [x₁, Function.update_apply] using hst.regs_dBase
    regs_stride := by simpa +decide [x₁, Function.update_apply] using hst.regs_stride
    regs_activeK := by simpa +decide [x₁, Function.update_apply] using hst.regs_activeK
    regs_targetT := by simpa +decide [x₁, Function.update_apply] using hst.regs_targetT
    regs_totS := by simpa +decide [x₁, Function.update_apply] using hst.regs_totS
    le_stride := hst.le_stride
    disjoint_blocks := hst.disjoint_blocks
    fits_wEnd := hst.fits_wEnd
    fits_dEnd := hst.fits_dEnd
    fits_totS := hst.fits_totS
    workspace := hst.workspace
  }
  obtain ⟨m_loop, hm_loop, hq_loop, hsup_loop, hsurv_loop⟩ :=
    contractLoop_spec ht hC (by simp +decide [x₁])
      (by simp +decide [x₁]) hst₁
  have hfull : ExecRand w contractDownTo x ((fun z => (z.1, 2 + z.2)) <$> m_loop) := by
    unfold contractDownTo
    have he12 := e1.seqRand hm_loop
    have he012 := e0.seqRand he12
    have hmap_assoc : ((fun z : Data 16 × ℕ => (z.1, 1 + z.2)) <$>
        ((fun z : Data 16 × ℕ => (z.1, 1 + z.2)) <$> m_loop)) =
        ((fun z : Data 16 × ℕ => (z.1, 2 + z.2)) <$> m_loop) := by
      rw [Functor.map_map]
      refine congrArg (· <$> m_loop) (funext fun z => Prod.ext rfl (by omega))
    rwa [hmap_assoc] at he012
  have hsub_cancel : t + (k - t) - t = k - t := by omega
  refine ⟨(fun z => (z.1, 2 + z.2)) <$> m_loop, hfull, ?_, ?_, ?_⟩
  · rw [hsub_cancel]
    simp only [OracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
    exact hq_loop
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    rcases hsup_loop z₀ hz₀ with ⟨ht0, hmod0, W', part', hC', hst'⟩
    exact ⟨by omega, hmod0, W', part', hC', hst'⟩
  · intro B hmin_pos hB_nt hB_min
    rw [eval_map_snd_toOuterMeasure]
    exact hsurv_loop B hmin_pos hB_nt hB_min

/-- At `t = 2`, any state satisfying `SurvivalPost W₀ wb db str 2 C_star y` where `C_star` is a
non-trivial cut attaining `minCut W₀` stores `minCut W₀` in `y.mem (wb + 1)`. -/
theorem survivalPost_two_mem_eq {n : ℕ} {W₀ : Fin n → Fin n → ℕ} {wb db str : ℕ}
    {C_star : Finset (Fin n)} {y : Data 16}
    (hnt : IsNonTrivialCut C_star) (hmin : cutWeight W₀ C_star = minCut W₀)
    (hsurv : SurvivalPost W₀ wb db str 2 C_star y) :
    y.mem (wb + 1) = minCut W₀ := by
  rcases hsurv with ⟨W', part', B', hC', hws', _, hpb'⟩
  have hB'_nt : IsNonTrivialCut B' :=
    isNonTrivialCut_of_pullbackCut part' (hpb' ▸ hnt)
  rw [isNonTrivialCut_iff_card, Fintype.card_fin] at hB'_nt
  have hcard1 : B'.card = 1 := by omega
  rcases Finset.card_eq_one.mp hcard1 with ⟨b, rfl⟩
  have hcell : y.mem (wb + 1) = W' 0 1 := by
    simpa using hws'.1 0 1
  rw [hcell, ← hmin, ← hpb', cutWeight_pullbackCut hC']
  have hb : b = 0 ∨ b = 1 := by omega
  rcases hb with rfl | rfl
  · exact (cutWeight_two_singleton_zero hC'.multigraph).symm
  · have hcompl : ({(1 : Fin 2)} : Finset (Fin 2)) = Finset.univ \ {0} := by decide
    rw [hcompl, cutWeight_compl hC'.multigraph, cutWeight_two_singleton_zero hC'.multigraph]

/-! ### Register-embedding (`Code.rename`) wrappers for callers with `r ≥ 16` -/

/-- `computeDegreesAndTotal` embedded on registers `0..15` of any `r`-register file (`16 ≤ r`). -/
def computeDegreesAndTotalAt {r : ℕ} (hr : 16 ≤ r) : Code .standard r :=
  computeDegreesAndTotal.rename (Fin.castLE hr)

/-- `contractDownTo` embedded on registers `0..15` of any `r`-register file (`16 ≤ r`). -/
def contractDownToAt {r : ℕ} (hr : 16 ≤ r) : Code .standard r :=
  contractDownTo.rename (Fin.castLE hr)

private theorem extend_castLE_regs_lt {r : ℕ} (hr : 16 ≤ r) (y : Data 16) (x : Data r)
    (i : Fin 16) :
    (y.extend (Fin.castLE hr) x).regs (Fin.castLE hr i) = y.regs i :=
  (Fin.castLE_injective hr).extend_apply y.regs x.regs i

private theorem extend_castLE_regs_ge {r : ℕ} (hr : 16 ≤ r) (y : Data 16) (x : Data r)
    (j : Fin r) (hj : 16 ≤ j.val) :
    (y.extend (Fin.castLE hr) x).regs j = x.regs j :=
  Function.extend_apply' y.regs x.regs j
    (by rintro ⟨i, rfl⟩; exact absurd i.isLt (by simp [Fin.castLE] at hj; omega))

/-- Specification of `computeDegreesAndTotalAt hr` on any `r`-register file (`16 ≤ r`), preserving
all caller registers with index `≥ 16`. -/
theorem computeDegreesAndTotalAt_exec {r w wb db str k : ℕ} (hr : 16 ≤ r)
    {W : Fin k → Fin k → ℕ} {x : Data r}
    (hwBase : x.regs (Fin.castLE hr wBase) = wb)
    (hdBase : x.regs (Fin.castLE hr dBase) = db)
    (hstride : x.regs (Fin.castLE hr stride) = str)
    (hactiveK : x.regs (Fin.castLE hr activeK) = k)
    (hstr : k ≤ str) (hdisj : wb + str * k ≤ db ∨ db + k ≤ wb)
    (h1 : Fits w 1) (hwEnd : Fits w (wb + str * k)) (hdEnd : Fits w (db + k))
    (htot : Fits w (totalDoubledWeight W)) (hmat : HoldsMatrix x.mem wb str W) :
    ∃ y : Data r, ExecWithin w (computeDegreesAndTotalAt hr) x y (6 * k ^ 2 + 12 * k + 6) ∧
      HoldsWorkspace y.mem wb db str W ∧
      Modifies (Finset.Ico db (db + k)) x.mem y.mem ∧
      y.regs (Fin.castLE hr wBase) = wb ∧
      y.regs (Fin.castLE hr dBase) = db ∧
      y.regs (Fin.castLE hr stride) = str ∧
      y.regs (Fin.castLE hr activeK) = k ∧
      y.regs (Fin.castLE hr targetT) = x.regs (Fin.castLE hr targetT) ∧
      y.regs (Fin.castLE hr totS) = totalDoubledWeight W ∧
      ∀ j : Fin r, 16 ≤ j.val → y.regs j = x.regs j := by
  obtain ⟨y₀, hy₀_exec, hy₀_ws, hy₀_mod, _, _, hy₀_wb, hy₀_db, hy₀_str, hy₀_k, hy₀_t, hy₀_tot⟩ :=
    computeDegreesAndTotal_exec (x := x.comap (Fin.castLE hr))
      hwBase hdBase hstride hactiveK hstr hdisj h1 hwEnd hdEnd htot hmat
  refine ⟨y₀.extend (Fin.castLE hr) x, hy₀_exec.rename (Fin.castLE_injective hr),
    hy₀_ws, hy₀_mod, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => extend_castLE_regs_ge hr y₀ x j hj⟩
  · rw [extend_castLE_regs_lt, hy₀_wb]
  · rw [extend_castLE_regs_lt, hy₀_db]
  · rw [extend_castLE_regs_lt, hy₀_str]
  · rw [extend_castLE_regs_lt, hy₀_k]
  · rw [extend_castLE_regs_lt, hy₀_t]; rfl
  · rw [extend_castLE_regs_lt, hy₀_tot]

/-- Specification of `contractDownToAt hr` on any `r`-register file (`16 ≤ r`), preserving all
caller registers with index `≥ 16`. -/
theorem contractDownToAt_spec {r n w wb db str k t : ℕ} (hr : 16 ≤ r)
    {W₀ : Fin n → Fin n → ℕ} {W : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data r}
    (ht : 2 ≤ t) (htk : t ≤ k) (hC : IsContractionOf W₀ part W)
    (hst : ContractState w wb db str k t W (x.comap (Fin.castLE hr))) :
    ∃ m : ProbComp (Data r × ℕ),
      ExecRand w (contractDownToAt hr) x m ∧
      m.IsQueryBounded (k - t) ∧
      (∀ z ∈ m.support,
        z.2 ≤ 36 * (k ^ 2 - t ^ 2) + 4 ∧
        Modifies (workspaceFootprint wb db str k) x.mem z.1.mem ∧
        (∀ j : Fin r, 16 ≤ j.val → z.1.regs j = x.regs j) ∧
        ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
          IsContractionOf W₀ part' W' ∧
          ContractState w wb db str t t W' (z.1.comap (Fin.castLE hr))) ∧
      (∀ B : Finset (Fin k),
        0 < minCut W₀ → IsNonTrivialCut B →
        cutWeight W₀ (pullbackCut part B) = minCut W₀ →
        (((t * (t - 1) : ℕ) : ℝ≥0∞) / ((k * (k - 1) : ℕ) : ℝ≥0∞)) ≤
          m.eval.toOuterMeasure
            {z | SurvivalPost W₀ wb db str t (pullbackCut part B)
              (z.1.comap (Fin.castLE hr))}) := by
  obtain ⟨m₀, hm₀, hq₀, hsup₀, hsurv₀⟩ := contractDownTo_spec ht htk hC hst
  let f := Fin.castLE hr
  have hf : f.Injective := Fin.castLE_injective hr
  unfold contractDownToAt
  refine ⟨(fun z : Data 16 × ℕ => (z.1.extend f x, z.2)) <$> m₀, hm₀.rename hf, ?_, ?_, ?_⟩
  · simp only [OracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
    exact hq₀
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    rcases hsup₀ z₀ hz₀ with ⟨ht0, hmod0, W', part', hC', hst'⟩
    refine ⟨ht0, hmod0, fun j hj => extend_castLE_regs_ge hr z₀.1 x j hj, W', part', hC', ?_⟩
    rwa [Data.comap_extend hf]
  · intro B hmin_pos hB_nt hB_min
    rw [ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    have hpre : ((fun z : Data 16 × ℕ => (z.1.extend f x, z.2)) ⁻¹'
        {z : Data r × ℕ | SurvivalPost W₀ wb db str t (pullbackCut part B) (z.1.comap f)}) =
        {z : Data 16 × ℕ | SurvivalPost W₀ wb db str t (pullbackCut part B) z.1} := by
      ext z
      change SurvivalPost W₀ wb db str t (pullbackCut part B) ((z.1.extend f x).comap f) ↔
        SurvivalPost W₀ wb db str t (pullbackCut part B) z.1
      rw [Data.comap_extend hf]
    rw [hpre]
    exact hsurv₀ B hmin_pos hB_nt hB_min

end Contract

end Cslib.Algorithms.WordRAM.Karger

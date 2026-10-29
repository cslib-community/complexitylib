/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.Karger.Graph
public import Complexity.Algorithms.WordRAM.Karger.Contract
public import Complexity.Computability.WordRAM.Copy
public import Complexity.Computability.WordRAM.Time

/-!
# Karger's randomized global minimum cut algorithm on the word RAM

Implements Karger's randomized contraction algorithm `[Karger1993]` on `n`-vertex weighted
undirected multigraphs (`n ≥ 2`, `IsMultigraph W`) over `Cslib.WordRAM.Basis.standard`, providing
three complete machine-level endpoints built on the workspace-relocatable subroutine
`contractDownTo`:

1. **Single-trial contraction (`singleProgram`, `r = 16`):** runs on `n :: flattenMatrix W`,
   computes row degrees at `2 + n ^ 2`, contracts in place down to `2` supervertices in at most
   `42 * n ^ 2 + 12 * n + 21` steps and `n - 2` `rand` calls, outputs a genuine non-trivial cut
   weight `cutWeight W C ≥ minCut W` on every supported branch, and achieves `minCut W` with
   probability at least `2 / (n * (n - 1))` whenever `0 < minCut W`.
2. **Repeated-trial amplification (`amplifiedProgram`, `r = 22`):** runs on
   `R :: n :: flattenMatrix W` (`1 ≤ R`), copies the immutable input matrix from `[3, 3 + n ^ 2)`
   into `[3 + n ^ 2, 3 + 2 * n ^ 2)` via `Cslib.WordRAM.ArrayCopy` before each of `R` independent
   contractions, halts within `R * (50 * n ^ 2 + 12 * n + 30) + 16` steps and `R * (n - 2)` `rand`
   calls with a genuine non-trivial cut weight `≥ minCut W`, and misses `minCut W` with probability
   at most `(1 - 2 / (n * (n - 1))) ^ R` whenever `0 < minCut W`.
3. **Explicit `O(n ^ 4 log n)` high-probability global minimum cut (`highProbProgram`, `r = 22`):**
   runs on `n :: flattenMatrix W`, computes `highProbTrials n = (n * (n - 1) / 2) * (⌊log₂ n⌋ + 2)`
   in registers using shifts and multiplication (without `.div` or `.mod`), halts within
   `33 * n ^ 4 * (Nat.log 2 n + 2)` steps with a genuine non-trivial cut weight `≥ minCut W`, and
   misses `minCut W` with probability at most `1 / (2 * n)` (hence at most `1 / n`) whenever
   `0 < minCut W`, via an elementary Bernoulli power bound without `Real.exp`.

## Source statements and notation mapping

* **Source locators (paraphrase):**
  - `[Karger1993]`, Section 2, Theorem 2.1 and Corollary 2.1 (paraphrase): contracting uniformly
    chosen edges in an `n`-vertex multigraph down to `2` meta-vertices returns any fixed global
    minimum cut with probability at least `C(n, 2)⁻¹ = 2 / (n * (n - 1))`, and repeating
    `O(n ^ 2 log n)` independent trials amplifies the success probability to `1 - 1 / poly(n)`.
  - `[KargerStein1996]`, Section 2, Lemma 2.1, Theorem 2.2, and Corollary 2.3, Section 2.1,
    Corollary 2.4, and Section 3 ("Implementing the Contraction Algorithm", Section 3.1, Lemma 3.1
    and Section 3.2, Corollary 3.2) (paraphrase): contracting an `n`-vertex weighted multigraph
    from `k` down to `t` supervertices via edge-weight-proportional selection preserves any fixed
    minimum cut with probability at least `C(t, 2) / C(k, 2) = t * (t - 1) / (k * (k - 1))`
    (`2 / (n * (n - 1))` at `t = 2, k = n`), and an `n × n` weighted adjacency matrix with a
    maintained row-degree array executes each trial in `O(n ^ 2)` total time (`O(n)` per step in
    Section 3.2).
  - `[MitzenmacherUpfal2017]`, Section 1.5, Theorem 1.8 (paraphrase): multiplying single-step
    survival bounds `1 - 2 / i` from `i = n` down to `3` yields `2 / (n * (n - 1))`.
* **Notation mapping, implementation variants, and parameter choices:**
  - `C(n, 2)⁻¹` ↔ `2 / (n * (n - 1))` (`singleProgram_spec`, `amplifiedProgram_spec`);
  - whereas `[KargerStein1996]`, Section 3.1 draws twice (`u` proportional to `D[u]` then `v`
    proportional to `W[u, v]` via two `Random-Select` calls), `contractDownTo` uses an equivalent
    single-draw variant: one unit-cost `rand` draw in `{0, …, S - 1}` (`S = totalDoubledWeight W`)
    resolved through linear prefix-sum scans `uScan` (`rowDeg`) and `vScan` (`W[u, v]`), achieving
    the same `2 * W[u, v] / S` distribution of Lemma 3.1; and whereas Section 3.2 states `O(n)` per
    contraction step, our swap-compaction of active slot `k - 1` into `v` gives `O(k)` instructions
    on `k` active supervertices;
  - the concrete trial count `highProbTrials n = (n * (n - 1) / 2) * (Nat.log 2 n + 2)` and the
    `1 / (2 * n)` failure bound in `highProbProgram_spec` are our own parameter choice instantiating
    the `O(n ^ 2 log n)` amplification of `[Karger1993]`, Section 2, Corollary 2.1;
  - the hypothesis `0 < minCut W` in the probability clauses is included only for proof convenience
    (when `minCut W = 0`, deterministic `S = 0` contraction still halts without faulting and outputs
    a valid non-trivial cut weight).

## Main definitions

* `Cslib.Algorithms.WordRAM.Karger.singleCode`,
  `Cslib.Algorithms.WordRAM.Karger.singleProgram`,
  `Cslib.Algorithms.WordRAM.Karger.singleTime`: single-trial Basic Karger (`r = 16`).
* `Cslib.Algorithms.WordRAM.Karger.ampCore`,
  `Cslib.Algorithms.WordRAM.Karger.amplifiedCode`,
  `Cslib.Algorithms.WordRAM.Karger.amplifiedProgram`,
  `Cslib.Algorithms.WordRAM.Karger.amplifiedTime`: `R`-trial amplified Karger (`r = 22`).
* `Cslib.Algorithms.WordRAM.Karger.highProbCode`,
  `Cslib.Algorithms.WordRAM.Karger.highProbProgram`,
  `Cslib.Algorithms.WordRAM.Karger.highProbTime`: `O(n ^ 4 log n)` high-probability global min-cut
  (`r = 22`).

## Main results

* `Cslib.Algorithms.WordRAM.Karger.singleProgram_spec`: worst-case `O(n ^ 2)` step bound, `n - 2`
  `rand`-call bound, pathwise non-trivial cut realization, `Modifies` frame, and
  `2 / (n * (n - 1))` success probability lower bound for `singleProgram`.
* `Cslib.Algorithms.WordRAM.Karger.amplifiedProgram_spec`: worst-case `O(R * n ^ 2)` step bound,
  `R * (n - 2)` `rand`-call bound, pathwise non-trivial cut realization, `Modifies` frame, and
  `(1 - 2 / (n * (n - 1))) ^ R` failure probability upper bound for `amplifiedProgram`.
* `Cslib.Algorithms.WordRAM.Karger.highProbProgram_spec`,
  `Cslib.Algorithms.WordRAM.Karger.highProbProgram_failure_le_inv_n`: worst-case
  `33 * n ^ 4 * (Nat.log 2 n + 2)` step bound, pathwise non-trivial cut realization, `Modifies`
  frame, and `1 / (2 * n)` (`1 / n`) failure probability upper bound for `highProbProgram`.

## References

* [D. R. Karger, *Global Min-cuts in RNC, and Other Ramifications of a Simple Min-Cut
  Algorithm*][Karger1993]
* [D. R. Karger and C. Stein, *A New Approach to the Minimum Cut Problem*][KargerStein1996]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Karger

open scoped ENNReal
open Cslib.WordRAM

/-! ### Word-size sufficiency and `Data.init` matrix layout -/

/-- Under `2 ≤ n` and `logWidth 3 n ≤ w`, workspace end-addresses up to `3 + 2 * (n * n) + n` fit in
`w`-bit words. -/
theorem fits_workspace_of_logWidth_three {n w : ℕ} (hn : 2 ≤ n) (hw : logWidth 3 n ≤ w) :
    Fits w (3 + 2 * (n * n) + n) := by
  refine (fits_of_lt_pow (k := 3) (n := n) ?_).mono hw
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by omega⟩
  nlinarith

/-- Under `2 ≤ n` and `logWidth 3 n ≤ w`, `highProbTrials n` and intermediate `n * (n - 1)` and
`Nat.log 2 n + 2` values fit in `w`-bit words. -/
theorem fits_highProbTrials_of_logWidth_three {n w : ℕ} (hn : 2 ≤ n) (hw : logWidth 3 n ≤ w) :
    Fits w (highProbTrials n) := by
  refine (fits_of_lt_pow (k := 3) (n := n) ?_).mono hw
  unfold highProbTrials
  have hlog : Nat.log 2 n < n := Nat.log_lt_self 2 (by omega)
  have hlg2 : Nat.log 2 n + 2 ≤ n + 1 := by omega
  have hhalf : n * (n - 1) / 2 < n * n := by
    have hlt : n * (n - 1) < n * n := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hlt
  have hmul : (n * (n - 1) / 2) * (Nat.log 2 n + 2) < (n * n) * (n + 1) := by
    have hpos : 0 < Nat.log 2 n + 2 := by omega
    calc
      (n * (n - 1) / 2) * (Nat.log 2 n + 2) < (n * n) * (Nat.log 2 n + 2) :=
        Nat.mul_lt_mul_of_pos_right hhalf hpos
      _ ≤ (n * n) * (n + 1) := Nat.mul_le_mul_left (n * n) hlg2
  have hcube : (n * n) * (n + 1) ≤ (n + 1) ^ 3 := by nlinarith
  exact lt_of_lt_of_le hmul hcube

/-- `logWidth 3 n ≤ w` and `Fits w (totalDoubledWeight W)` suffice for
`InputFits w (n :: flattenMatrix W)`. -/
theorem inputFits_single {n w : ℕ} {W : Fin n → Fin n → ℕ} (hn : 2 ≤ n)
    (hw : logWidth 3 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    InputFits w (n :: flattenMatrix W) := by
  have hws := fits_workspace_of_logWidth_three hn hw
  refine ⟨?_, ?_⟩
  · simp only [List.length_cons, length_flattenMatrix]
    exact hws.of_le (by omega)
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hmem
    · exact hws.of_le (by omega)
    · exact htot.of_le (mem_flattenMatrix_le_totalDoubledWeight W hmem)

/-- `logWidth 3 n ≤ w`, `Fits w R`, and `Fits w (totalDoubledWeight W)` suffice for
`InputFits w (R :: n :: flattenMatrix W)`. -/
theorem inputFits_amplified {R n w : ℕ} {W : Fin n → Fin n → ℕ} (hn : 2 ≤ n)
    (hw : logWidth 3 n ≤ w) (hR : Fits w R) (htot : Fits w (totalDoubledWeight W)) :
    InputFits w (R :: n :: flattenMatrix W) := by
  have hws := fits_workspace_of_logWidth_three hn hw
  refine ⟨?_, ?_⟩
  · simp only [List.length_cons, length_flattenMatrix]
    exact hws.of_le (by omega)
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact hR
    · rcases List.mem_cons.mp hv' with rfl | hmem
      · exact hws.of_le (by omega)
      · exact htot.of_le (mem_flattenMatrix_le_totalDoubledWeight W hmem)

/-- In `Data.init (pfx ++ flattenMatrix W)`, the flattened matrix occupies memory starting at
`1 + pfx.length` with stride `n`. -/
theorem holdsMatrix_init_append {r n : ℕ} (pfx : List ℕ) (W : Fin n → Fin n → ℕ) :
    HoldsMatrix (Data.init (r := r) (pfx ++ flattenMatrix W)).mem (1 + pfx.length) n W := by
  intro i j
  have haddr : (1 + pfx.length) + i.val * n + j.val =
      (pfx.length + (i.val * n + j.val)) + 1 := by omega
  rw [haddr, Data.init_mem_succ]
  have hlt : i.val * n + j.val < (flattenMatrix W).length := by
    rw [length_flattenMatrix]
    nlinarith [i.isLt, j.isLt]
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right pfx.length _)]
  simp only [Nat.add_sub_cancel_left, List.getElem?_eq_getElem hlt, Option.getD_some]
  exact getElem_flattenMatrix W i j

/-- In `Data.init (n :: flattenMatrix W)`, memory holds `W` at base `2` with stride `n`. -/
theorem holdsMatrix_init_single {r n : ℕ} (W : Fin n → Fin n → ℕ) :
    HoldsMatrix (Data.init (r := r) (n :: flattenMatrix W)).mem 2 n W :=
  holdsMatrix_init_append [n] W

/-- In `Data.init (R :: n :: flattenMatrix W)`, memory holds `W` at base `3` with stride `n`. -/
theorem holdsMatrix_init_amplified {r R n : ℕ} (W : Fin n → Fin n → ℕ) :
    HoldsMatrix (Data.init (r := r) (R :: n :: flattenMatrix W)).mem 3 n W :=
  holdsMatrix_init_append [R, n] W

/-! ### Endpoint 1: Single-trial Basic Karger (`r = 16`) -/

section SingleTrial

open Reg

/-- Setup for `singleCode`: read `n` from `mem[1]` and configure `(wBase, dBase, stride, activeK,
targetT) = (2, 2 + n * n, n, n, 2)`. -/
def singleSetup : Code .standard 16 := ram[
  one ← #1;
  activeK ← *one;
  stride ← activeK;
  wBase ← #2;
  val1 ← activeK * activeK;
  dBase ← wBase + val1;
  targetT ← #2
]

/-- Postprocessing for `singleCode`: load the contracted superedge weight `mem[wBase + 1]` into
`val1`. -/
def singlePost : Code .standard 16 := ram[
  one ← #1;
  addr1 ← wBase + one;
  val1 ← *addr1
]

/-- Structured 16-register single-trial Karger contraction program on `n :: flattenMatrix W`. -/
def singleCode : Code .standard 16 := ram[
  ⟪singleSetup⟫;
  ⟪computeDegreesAndTotal⟫;
  ⟪contractDownTo⟫;
  ⟪singlePost⟫
]

/-- Compiled 16-register single-trial Karger contraction program. -/
def singleProgram : Program .standard 16 :=
  singleCode.program val1

/-- Worst-case instruction bound `42 * n ^ 2 + 12 * n + 21` for `singleProgram`. -/
def singleTime (n : ℕ) : ℕ :=
  42 * n ^ 2 + 12 * n + 21

theorem singleSetup_exec {w n : ℕ} {W : Fin n → Fin n → ℕ} (hn : 2 ≤ n)
    (hw : logWidth 3 n ≤ w) :
    ∃ y : Data 16, Exec w singleSetup (Data.init (n :: flattenMatrix W)) y 7 ∧
      y.mem = (Data.init (r := 16) (n :: flattenMatrix W)).mem ∧
      y.regs wBase = 2 ∧ y.regs dBase = 2 + n * n ∧ y.regs stride = n ∧
      y.regs activeK = n ∧ y.regs targetT = 2 := by
  have hws := fits_workspace_of_logWidth_three hn hw
  have h1 : Fits w 1 := hws.of_le (by omega)
  have h2 : Fits w 2 := hws.of_le (by omega)
  have hnn : Fits w (n * n) := hws.of_le (by omega)
  have hdb : Fits w (2 + n * n) := hws.of_le (by omega)
  let x₀ : Data 16 := Data.init (n :: flattenMatrix W)
  have hmem1 : x₀.mem 1 = n := rfl
  let s₁ := x₀.set one 1
  let s₂ := s₁.set activeK n
  let s₃ := s₂.set stride n
  let s₄ := s₃.set wBase 2
  let s₅ := s₄.set val1 (n * n)
  let s₆ := s₅.set dBase (2 + n * n)
  let s₇ := s₆.set targetT 2
  have e1 : Exec (B := .standard) w ram[one ← #1] x₀ s₁ 1 := Exec.const h1
  have e2 : Exec (B := .standard) w ram[activeK ← *one] s₁ s₂ 1 := by
    have hr : s₁.regs one = 1 := by simp [s₁]
    simpa [s₂, s₁, hr, hmem1] using Exec.load (B := .standard) (w := w) (d := activeK) (a := one)
      (x := s₁)
  have e3 : Exec (B := .standard) w ram[stride ← activeK] s₂ s₃ 1 := by
    have hr : s₂.regs activeK = n := by simp [s₂]
    simpa [s₃, hr] using Exec.copy (B := .standard) (w := w) (d := stride) (s := activeK) (x := s₂)
  have e4 : Exec (B := .standard) w ram[wBase ← #2] s₃ s₄ 1 := Exec.const h2
  have e5 : Exec w ram[val1 ← activeK * activeK] s₄ s₅ 1 := by
    have hr : s₄.regs activeK = n := by simp +decide [s₄, s₃, s₂]
    simpa [s₅, BinOp.eval, hr] using
      Exec.bin (w := w) (f := .mul) (d := val1) (i := activeK) (j := activeK) (x := s₄)
        (by simpa [BinOp.eval, hr] using hnn)
  have e6 : Exec w ram[dBase ← wBase + val1] s₅ s₆ 1 := by
    have hwb : s₅.regs wBase = 2 := by simp +decide [s₅, s₄]
    have hv1 : s₅.regs val1 = n * n := by simp [s₅]
    simpa [s₆, BinOp.eval, hwb, hv1] using
      Exec.bin (w := w) (f := .add) (d := dBase) (i := wBase) (j := val1) (x := s₅)
        (by simpa [BinOp.eval, hwb, hv1] using hdb)
  have e7 : Exec (B := .standard) w ram[targetT ← #2] s₆ s₇ 1 := Exec.const h2
  refine ⟨s₇, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · unfold singleSetup
    exact e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))
  · simp +decide [s₇, s₆, s₅, s₄]
  · simp +decide [s₇, s₆]
  · simp +decide [s₇, s₆, s₅, s₄, s₃]
  · simp +decide [s₇, s₆, s₅, s₄, s₃, s₂]
  · simp [s₇]

theorem singlePost_exec {w wb : ℕ} {x : Data 16} (hwBase : x.regs wBase = wb)
    (h1 : Fits w 1) (hwb1 : Fits w (wb + 1)) :
    ∃ y : Data 16, Exec w singlePost x y 3 ∧
      y.mem = x.mem ∧ y.regs val1 = x.mem (wb + 1) := by
  let s₁ := x.set one 1
  let s₂ := s₁.set addr1 (wb + 1)
  let s₃ := s₂.set val1 (x.mem (wb + 1))
  have e1 : Exec (B := .standard) w ram[one ← #1] x s₁ 1 := Exec.const h1
  have e2 : Exec w ram[addr1 ← wBase + one] s₁ s₂ 1 := by
    have hwb : s₁.regs wBase = wb := by simpa +decide [s₁, Function.update_apply] using hwBase
    have ho : s₁.regs one = 1 := by simp [s₁]
    simpa [s₂, BinOp.eval, hwb, ho] using
      Exec.bin (w := w) (f := .add) (d := addr1) (i := wBase) (j := one) (x := s₁)
        (by simpa [BinOp.eval, hwb, ho] using hwb1)
  have e3 : Exec (B := .standard) w ram[val1 ← *addr1] s₂ s₃ 1 := by
    have ha : s₂.regs addr1 = wb + 1 := by simp [s₂]
    simpa [s₃, s₂, s₁, ha] using
      Exec.load (B := .standard) (w := w) (d := val1) (a := addr1) (x := s₂)
  exact ⟨s₃, e1.seq (e2.seq e3), rfl, by simp [s₃]⟩

/-- Structured `ProbComp` specification of `singleCode`. -/
theorem singleCode_spec {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    ∃ m : ProbComp (Data 16 × ℕ),
      ExecRand w singleCode (Data.init (n :: flattenMatrix W)) m ∧
      m.IsQueryBounded (n - 2) ∧
      (∀ z ∈ m.support,
        z.2 + 1 ≤ singleTime n ∧
        Modifies (Finset.Ico 2 (2 + n * n + n))
          (Data.init (r := 16) (n :: flattenMatrix W)).mem z.1.mem ∧
        ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ z.1.regs val1 = cutWeight W C) ∧
      (0 < minCut W →
        (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) ≤
          m.eval.toOuterMeasure {z | z.1.regs val1 = minCut W}) := by
  have hws_fit := fits_workspace_of_logWidth_three hn hw
  have h1 : Fits w 1 := hws_fit.of_le (by omega)
  have hwEnd : Fits w (2 + n * n) := hws_fit.of_le (by omega)
  have hdEnd : Fits w (2 + n * n + n) := hws_fit.of_le (by omega)
  have hwb1 : Fits w (2 + 1) := hws_fit.of_le (by omega)
  obtain ⟨y_setup, e_setup, hmem_setup, hwb_s, hdb_s, hstr_s, hk_s, ht_s⟩ :=
    singleSetup_exec (W := W) hn hw
  obtain ⟨y_deg, ⟨n_deg, hn_deg, e_deg⟩, hws_deg, hmod_deg, _, _,
      hwb_d, hdb_d, hstr_d, hk_d, ht_d, htot_d⟩ :=
    computeDegreesAndTotal_exec (w := w) (W := W) (x := y_setup)
      hwb_s hdb_s hstr_s hk_s (le_refl n) (Or.inl (le_refl _)) h1 hwEnd hdEnd htot
      (hmem_setup ▸ holdsMatrix_init_single W)
  rw [ht_s] at ht_d
  have hst_deg : ContractState w 2 (2 + n * n) n n 2 W y_deg :=
    ⟨hwb_d, hdb_d, hstr_d, hk_d, ht_d, htot_d, le_refl n, Or.inl (le_refl _),
      hwEnd, hdEnd, htot, hws_deg⟩
  obtain ⟨m_c, hm_c, hq_c, hsup_c, hsurv_c⟩ :=
    contractDownTo_spec (le_refl 2) hn (isContractionOf_id hW) hst_deg
  have hpost_all : ∀ z ∈ m_c.support,
      ∃ y_p : Data 16, Exec w singlePost z.1 y_p 3 ∧
        y_p.mem = z.1.mem ∧ y_p.regs val1 = z.1.mem 3 := by
    intro z hz
    rcases hsup_c z hz with ⟨_, _, W', part', _, hst'⟩
    exact singlePost_exec hst'.regs_wBase h1 hwb1
  obtain ⟨m_post, hm_post_def⟩ :
      ∃ m_post : Data 16 → ProbComp (Data 16 × ℕ),
        ∀ d, m_post d = codeComp w singlePost d := ⟨_, fun _ => rfl⟩
  have hm_post : ∀ z ∈ m_c.support, ExecRand w singlePost z.1 (m_post z.1) := by
    intro z hz
    obtain ⟨y_p, e_p, _, _⟩ := hpost_all z hz
    have hr := e_p.execRand
    rw [hm_post_def]
    simpa only [hr.codeComp_eq] using hr
  have hm_c_post : ExecRand w (ram[⟪contractDownTo⟫; ⟪singlePost⟫]) y_deg
      (do let z₁ ← m_c; let z₂ ← m_post z₁.1; pure (z₂.1, z₁.2 + z₂.2)) :=
    ExecRand.seq hm_c hm_post
  have hm_deg_rest := e_deg.seqRand hm_c_post
  have hm_full := e_setup.seqRand hm_deg_rest
  let m_total := (fun z => (z.1, 7 + z.2)) <$>
    ((fun z => (z.1, n_deg + z.2)) <$>
      (do let z₁ ← m_c; let z₂ ← m_post z₁.1; pure (z₂.1, z₁.2 + z₂.2)))
  have hcode_eq : singleCode =
      .seq singleSetup (.seq computeDegreesAndTotal (.seq contractDownTo singlePost)) := rfl
  rw [hcode_eq]
  refine ⟨m_total, hm_full, ?_, ?_, ?_⟩
  · simp only [m_total, OracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
    have hq_post : ∀ z₁ ∈ m_c.support,
        (m_post z₁.1 >>= fun z₂ => pure (z₂.1, z₁.2 + z₂.2)).IsQueryBounded 0 := by
      intro z₁ hz₁
      obtain ⟨y_p, e_p, _, _⟩ := hpost_all z₁ hz₁
      rw [hm_post_def, e_p.execRand.codeComp_eq, pure_bind]
      exact .pure _ 0
    simpa only [Nat.add_zero] using OracleComp.IsCostBounded.bind_on_support hq_c hq_post
  · intro z hz
    simp only [m_total, Functor.map_map] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₀
    obtain ⟨y_p, e_p, hmem_p, hv1_p⟩ := hpost_all z₁ hz₁
    rw [hm_post_def, e_p.execRand.codeComp_eq] at hrest
    obtain ⟨z₂, hz₂, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hz₂
    cases OracleComp.eq_of_mem_supportWith_pure hpure
    rcases hsup_c z₁ hz₁ with ⟨ht_c, hmod_c, W', part', hC', hst'⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [singleTime]
      omega
    · rw [hmem_p]
      have hsub1 : Finset.Ico (2 + n * n) (2 + n * n + n) ⊆ Finset.Ico 2 (2 + n * n + n) :=
        Finset.Ico_subset_Ico (by omega) (le_refl _)
      have hsub2 : workspaceFootprint 2 (2 + n * n) n n ⊆ Finset.Ico 2 (2 + n * n + n) := by
        intro a ha
        simp only [workspaceFootprint, Finset.mem_union, Finset.mem_Ico] at ha ⊢
        omega
      exact modifies_trans_subset (hmem_setup ▸ hmod_deg) hmod_c hsub1 hsub2
    · refine ⟨pullbackCut part' {0},
        isNonTrivialCut_pullbackCut hC'.surj (isNonTrivialCut_singleton (le_refl 2) 0), ?_⟩
      rw [hv1_p, cutWeight_pullbackCut hC', cutWeight_two_singleton_zero hC'.multigraph]
      simpa using hst'.workspace.1 0 1
  · intro hmin_pos
    obtain ⟨C_star, hC_nt, hC_min⟩ := exists_minCut_achiever hn W
    have hpb_id : pullbackCut (id : Fin n → Fin n) C_star = C_star := by
      ext u
      simp [pullbackCut]
    have hsurv := hsurv_c C_star hmin_pos hC_nt (by rw [hpb_id, hC_min])
    rw [hpb_id] at hsurv
    have h2 : (((2 * (2 - 1) : ℕ) : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) =
        (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) := by norm_num
    rw [h2] at hsurv
    refine hsurv.trans ?_
    have hm_eval : m_total.eval =
        m_c.eval.bind fun z₁ =>
          ((m_post z₁.1).eval.map fun z₂ => (z₂.1, 7 + (n_deg + (z₁.2 + z₂.2)))) := by
      have hm_eq : m_total = (do
          let z₁ ← m_c
          let z₂ ← m_post z₁.1
          pure (z₂.1, 7 + (n_deg + (z₁.2 + z₂.2)))) := by
        simp only [m_total, ← bind_pure_comp, bind_assoc, pure_bind]
      rw [hm_eq, ProbComp.eval_bind]
      refine congrArg (m_c.eval.bind ·) (funext fun z₁ => ?_)
      rw [bind_pure_comp, ProbComp.eval_map]
    rw [hm_eval]
    have hstep := toOuterMeasure_bind_ge_mul_ennreal m_c.eval
      (fun z₁ => (m_post z₁.1).eval.map fun z₂ => (z₂.1, 7 + (n_deg + (z₁.2 + z₂.2))))
      {z | SurvivalPost W 2 (2 + n * n) n 2 C_star z.1}
      {z | z.1.regs val1 = minCut W}
      (s₁ := m_c.eval.toOuterMeasure {z | SurvivalPost W 2 (2 + n * n) n 2 C_star z.1})
      (s₂ := 1) le_rfl ?_
    · simpa using hstep
    · intro z₁ hz₁_eval hsurv₁
      have hz₁ : z₁ ∈ m_c.support := (ProbComp.support_eval m_c) ▸ hz₁_eval
      obtain ⟨y_p, e_p, _, hv1_p⟩ := hpost_all z₁ hz₁
      rw [hm_post_def, e_p.execRand.codeComp_eq, ProbComp.eval_pure,
        PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_pure_apply]
      have hmem3 : z₁.1.mem 3 = minCut W := survivalPost_two_mem_eq hC_nt hC_min hsurv₁
      have hhit : y_p.regs val1 = minCut W := hv1_p.trans hmem3
      simp [hhit]

/-- **Single-trial Basic Karger specification (`singleProgram`).**
At word size `w ≥ logWidth 3 n` when `totalDoubledWeight W < 2 ^ w`:
1. `singleProgram` halts within `singleTime n = 42 * n ^ 2 + 12 * n + 21` steps;
2. executes at most `n - 2` `rand` calls;
3. on every supported branch, outputs `cutWeight W C ≥ minCut W` for a genuine non-trivial cut `C`
   of `W` while modifying memory only in `[2, 2 + n * n + n)`;
4. when `0 < minCut W` (excluded only for proof convenience; `S = 0` contraction still halts
   fault-free with a valid cut weight), outputs `minCut W` with probability at least
   `2 / (n * (n - 1))`. -/
theorem singleProgram_spec {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    let input := n :: flattenMatrix W
    RandHaltsWithin w singleProgram (.init input) (singleTime n) ∧
    RandCallsBounded w singleProgram (.init input) (singleTime n) (n - 2) ∧
    (∀ cfg ∈ (runRand w singleProgram (singleTime n) (.running (.init input))).support,
      ∃ (y : Data 16) (C : Finset (Fin n)),
        cfg = .halted (cutWeight W C) y ∧
        y.Bounded w ∧
        IsNonTrivialCut C ∧
        minCut W ≤ cutWeight W C ∧
        Modifies (Finset.Ico 2 (2 + n * n + n)) (Data.init (r := 16) input).mem y.mem) ∧
    (0 < minCut W →
      (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) ≤
        (evalRand w singleProgram (singleTime n) (.init input)).toOuterMeasure
          {cfg | ∃ y, cfg = .halted (minCut W) y}) := by
  intro input
  have hfit_in : InputFits w input := inputFits_single hn hw htot
  obtain ⟨m, hm, hq, hsup, hsurv⟩ := singleCode_spec hn hW hw htot
  have hrun : runRand w singleProgram (singleTime n) (.running (.init input)) =
      (fun z : Data 16 × ℕ => RandCfg.halted (z.1.regs val1) z.1) <$> m :=
    hm.runRand_program val1 fun z hz => (hsup z hz).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cfg hcfg
    rw [hrun] at hcfg
    obtain ⟨z, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hcfg
    exact ⟨z.1.regs val1, z.1, rfl⟩
  · rw [RandCallsBounded, hrun]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr hq
  · intro cfg hcfg
    have hbnd := (runRand_bounded_init hfit_in hcfg)
    rw [hrun] at hcfg
    obtain ⟨z, hz, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hcfg
    rcases hsup z hz with ⟨_, hmod, C, hC_nt, hv1⟩
    exact ⟨z.1, C, by rw [hv1], hbnd.2, hC_nt, minCut_le_cutWeight W hC_nt, hmod⟩
  · intro hmin_pos
    rw [evalRand, hrun, ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    refine (hsurv hmin_pos).trans (PMF.toOuterMeasure_mono _ ?_)
    intro z hz
    exact ⟨z.1, congrArg (fun v => RandCfg.halted v z.1) hz.1⟩

end SingleTrial

/-! ### Shared `R`-trial amplification engine (`r = 22`) -/

/-- `16 ≤ 22`, used to embed `computeDegreesAndTotal` and `contractDownTo` into `Data 22`. -/
private theorem hr22 : 16 ≤ 22 := by decide

-- Register layout (`r = 22`) for repeated-trial Karger amplification: registers `0..15` match
-- `Reg` (`Contract.lean`), while `16..21` hold caller state preserved across contractions.
namespace AmpReg

/-- Constant register `0` (`Reg.zero` embedded into `Fin 22`). -/
abbrev zero : Fin 22 := 0
/-- Constant register `1` (`Reg.one` embedded into `Fin 22`). -/
abbrev one : Fin 22 := 1
/-- Working matrix base address (`Reg.wBase` embedded into `Fin 22`). -/
abbrev wBase : Fin 22 := 2
/-- Working degree-array base address (`Reg.dBase` embedded into `Fin 22`). -/
abbrev dBase : Fin 22 := 3
/-- Working matrix row stride (`Reg.stride` embedded into `Fin 22`). -/
abbrev stride : Fin 22 := 4
/-- Active supervertex count `k` (`Reg.activeK` embedded into `Fin 22`). -/
abbrev activeK : Fin 22 := 5
/-- Target supervertex count `t` (`Reg.targetT` embedded into `Fin 22`). -/
abbrev targetT : Fin 22 := 6
/-- Active doubled edge weight `S` (`Reg.totS` embedded into `Fin 22`). -/
abbrev totS : Fin 22 := 7
/-- Loop index scratch register (`Reg.idx` embedded into `Fin 22`). -/
abbrev idx : Fin 22 := 10
/-- Loop counter / remainder scratch register (`Reg.rem` embedded into `Fin 22`). -/
abbrev rem : Fin 22 := 11
/-- Primary scratch address register (`Reg.addr1` embedded into `Fin 22`). -/
abbrev addr1 : Fin 22 := 12
/-- Primary scratch value register (`Reg.val1` embedded into `Fin 22`). -/
abbrev val1 : Fin 22 := 14
/-- Secondary scratch value register (`Reg.val2` embedded into `Fin 22`). -/
abbrev val2 : Fin 22 := 15
/-- Base address of the immutable input matrix `W`. -/
abbrev srcBase : Fin 22 := 16
/-- Original vertex count `n`, preserved across all trials. -/
abbrev nOrig : Fin 22 := 17
/-- Word count `n * n` of the flattened matrix. -/
abbrev matLen : Fin 22 := 18
/-- Total number `R` of independent trials to execute. -/
abbrev numTrials : Fin 22 := 19
/-- Number of trials completed so far (`0 .. R`). -/
abbrev trialIdx : Fin 22 := 20
/-- Minimum cut weight seen across completed trials. -/
abbrev bestVal : Fin 22 := 21

end AmpReg

section AmplificationEngine

open AmpReg

/-- Injective register map embedding `Cslib.WordRAM.ArrayCopy` (`r = 7`) into `Fin 22` with
`(src, dst, len, idx, addr, value, one) = (srcBase, wBase, matLen, idx, addr1, val1, one)`. -/
def copyRegMap : Fin 7 → Fin 22 :=
  ![srcBase, wBase, matLen, idx, addr1, val1, one]

theorem copyRegMap_injective : Function.Injective copyRegMap := by
  decide

/-- Copy `matLen` words from `srcBase` to `wBase` via `Cslib.WordRAM.ArrayCopy.program`. -/
def copyMatrixCode : Code .standard 22 :=
  ArrayCopy.program.rename copyRegMap

theorem copyMatrixCode_exec {w sb wb n : ℕ} {W : Fin n → Fin n → ℕ} {x : Data 22}
    (hsb : x.regs srcBase = sb) (hwb : x.regs wBase = wb) (hlen : x.regs matLen = n * n)
    (hdisj : sb + n * n ≤ wb)
    (h1 : Fits w 1) (hwEnd : Fits w (wb + n * n))
    (hsrc_mat : HoldsMatrix x.mem sb n W) :
    ∃ y : Data 22, ExecWithin w copyMatrixCode x y (7 * (n * n) + 4) ∧
      HoldsMatrix y.mem wb n W ∧
      Modifies (Finset.Ico wb (wb + n * n)) x.mem y.mem ∧
      y.regs wBase = wb ∧ y.regs dBase = x.regs dBase ∧
      y.regs srcBase = sb ∧ y.regs nOrig = x.regs nOrig ∧
      y.regs matLen = n * n ∧ y.regs numTrials = x.regs numTrials ∧
      y.regs trialIdx = x.regs trialIdx ∧ y.regs bestVal = x.regs bestVal := by
  have hs_fit : Fits w ((x.comap copyRegMap).regs ArrayCopy.src +
      (x.comap copyRegMap).regs ArrayCopy.len) := by
    change Fits w (x.regs srcBase + x.regs matLen)
    rw [hsb, hlen]
    exact hwEnd.of_le (by omega)
  have hd_fit : Fits w ((x.comap copyRegMap).regs ArrayCopy.dst +
      (x.comap copyRegMap).regs ArrayCopy.len) := by
    change Fits w (x.regs wBase + x.regs matLen)
    rw [hwb, hlen]
    exact hwEnd
  have hdisj' : (x.comap copyRegMap).regs ArrayCopy.src +
      (x.comap copyRegMap).regs ArrayCopy.len ≤ (x.comap copyRegMap).regs ArrayCopy.dst := by
    change x.regs srcBase + x.regs matLen ≤ x.regs wBase
    rw [hsb, hlen, hwb]
    exact hdisj
  obtain ⟨y₀, hy₀_exec, hy₀_mem, hy₀_src, hy₀_dst, hy₀_len⟩ :=
    ArrayCopy.exec (x.comap copyRegMap) h1 hs_fit hd_fit hdisj'
  have ht_eq : 7 * (x.comap copyRegMap).regs ArrayCopy.len + 4 = 7 * (n * n) + 4 := by
    change 7 * x.regs matLen + 4 = 7 * (n * n) + 4
    rw [hlen]
  rw [ht_eq] at hy₀_exec
  let y := y₀.extend copyRegMap x
  have hymem : y.mem = ArrayCopy.copyPrefix x.mem sb wb (n * n) := by
    have h₀ : y₀.mem = ArrayCopy.copyPrefix x.mem (x.regs srcBase) (x.regs wBase)
        (x.regs matLen) := hy₀_mem
    rwa [hsb, hwb, hlen] at h₀
  have hnot_in : ∀ (r : Fin 22), (∀ i : Fin 7, copyRegMap i ≠ r) → y.regs r = x.regs r :=
    fun r hne => Function.extend_apply' y₀.regs x.regs r (by rintro ⟨i, rfl⟩; exact hne i rfl)
  refine ⟨y, hy₀_exec.rename copyRegMap_injective, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [hymem]
    have hj_lt : i.val * n + j.val < n * n := by nlinarith [i.isLt, j.isLt]
    have haddr : wb + i.val * n + j.val = wb + (i.val * n + j.val) := by omega
    rw [haddr, ArrayCopy.copyPrefix_read hj_lt]
    have hsrc_addr : sb + (i.val * n + j.val) = sb + i.val * n + j.val := by omega
    rw [hsrc_addr]
    exact hsrc_mat i j
  · intro a ha
    rw [hymem, ArrayCopy.copyPrefix_outside]
    rwa [Finset.mem_Ico] at ha
  · change Function.extend copyRegMap y₀.regs x.regs (copyRegMap ArrayCopy.dst) = wb
    rw [copyRegMap_injective.extend_apply]
    exact hy₀_dst.trans hwb
  · exact hnot_in dBase (by decide)
  · change Function.extend copyRegMap y₀.regs x.regs (copyRegMap ArrayCopy.src) = sb
    rw [copyRegMap_injective.extend_apply]
    exact hy₀_src.trans hsb
  · exact hnot_in nOrig (by decide)
  · change Function.extend copyRegMap y₀.regs x.regs (copyRegMap ArrayCopy.len) = n * n
    rw [copyRegMap_injective.extend_apply]
    exact hy₀_len.trans hlen
  · exact hnot_in numTrials (by decide)
  · exact hnot_in trialIdx (by decide)
  · exact hnot_in bestVal (by decide)

/-- Postprocessing at the end of each trial: extract `mem[wBase + 1]`, update `bestVal` (replacing
it unconditionally on trial `0` and taking the minimum thereafter), and increment `trialIdx`. -/
def ampTrialPost : Code .standard 22 := ram[
  zero ← #0;
  one ← #1;
  addr1 ← wBase + one;
  val1 ← *addr1;
  if trialIdx = zero then [
    bestVal ← val1
  ] else [
    if val1 < bestVal then [
      bestVal ← val1
    ] else [
      zero ← #0
    ]
  ];
  trialIdx ← trialIdx + one
]

/-- Single amplification trial: copy `[srcBase, srcBase + n * n)` into `wBase`, initialize row
degrees at `dBase`, contract down to `2` supervertices, and update `bestVal`. -/
def ampTrialBody : Code .standard 22 := ram[
  ⟪copyMatrixCode⟫;
  activeK ← nOrig;
  stride ← nOrig;
  targetT ← #2;
  ⟪computeDegreesAndTotalAt (by decide)⟫;
  ⟪contractDownToAt (by decide)⟫;
  ⟪ampTrialPost⟫
]

/-- Loop running `numTrials` independent contractions. -/
def ampLoop : Code .standard 22 := ram[
  while trialIdx < numTrials do [ ⟪ampTrialBody⟫ ]
]

/-- Shared amplification core assuming `srcBase`, `nOrig`, and `numTrials` are initialized in
registers. -/
def ampCore : Code .standard 22 := ram[
  val1 ← nOrig * nOrig;
  matLen ← val1;
  wBase ← srcBase + matLen;
  dBase ← wBase + matLen;
  trialIdx ← #0;
  bestVal ← #0;
  ⟪ampLoop⟫
]

/-- Loop invariant for `ampLoop` at `trialIdx = i ≤ R`. -/
structure AmpInv (w sb n R i : ℕ) (W : Fin n → Fin n → ℕ) (mem₀ : ℕ → ℕ)
    (x : Data 22) : Prop where
  regs_srcBase : x.regs srcBase = sb
  regs_wBase : x.regs wBase = sb + n * n
  regs_dBase : x.regs dBase = sb + 2 * (n * n)
  regs_nOrig : x.regs nOrig = n
  regs_matLen : x.regs matLen = n * n
  regs_numTrials : x.regs numTrials = R
  regs_trialIdx : x.regs trialIdx = i
  src_matrix : HoldsMatrix x.mem sb n W
  modifies_ws : Modifies (Finset.Ico (sb + n * n) (sb + 2 * (n * n) + n)) mem₀ x.mem
  best_cut : 0 < i → ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ x.regs bestVal = cutWeight W C

theorem ampTrialPost_exec {w wb i R : ℕ} {x : Data 22}
    (hwb : x.regs wBase = wb) (hti : x.regs trialIdx = i) (hiR : i < R)
    (h1 : Fits w 1) (hwb1 : Fits w (wb + 1)) (hR_fit : Fits w R) :
    ∃ y : Data 22, ExecWithin w ampTrialPost x y 10 ∧
      y.mem = x.mem ∧
      y.regs srcBase = x.regs srcBase ∧
      y.regs wBase = wb ∧
      y.regs dBase = x.regs dBase ∧
      y.regs nOrig = x.regs nOrig ∧
      y.regs matLen = x.regs matLen ∧
      y.regs numTrials = x.regs numTrials ∧
      y.regs trialIdx = i + 1 ∧
      y.regs bestVal =
        (if i = 0 then x.mem (wb + 1) else min (x.mem (wb + 1)) (x.regs bestVal)) := by
  have hi1_fit : Fits w (i + 1) := hR_fit.of_le (by omega)
  let v_new := x.mem (wb + 1)
  let s₁ := (((x.set zero 0).set one 1).set addr1 (wb + 1)).set val1 v_new
  have e1 : Exec (B := .standard) w ram[zero ← #0] x (x.set zero 0) 1 :=
    Exec.const (fits_zero w)
  have e2 : Exec (B := .standard) w ram[one ← #1] (x.set zero 0)
      ((x.set zero 0).set one 1) 1 := Exec.const h1
  have e3 : Exec w ram[addr1 ← wBase + one] ((x.set zero 0).set one 1)
      (((x.set zero 0).set one 1).set addr1 (wb + 1)) 1 := by
    have hw' : ((x.set zero 0).set one 1).regs wBase = wb := by
      simpa +decide [Function.update_apply] using hwb
    have ho' : ((x.set zero 0).set one 1).regs one = 1 := by simp
    simpa [BinOp.eval, hw', ho'] using
      Exec.bin (w := w) (f := .add) (d := addr1) (i := wBase) (j := one)
        (x := (x.set zero 0).set one 1) (by simpa [BinOp.eval, hw', ho'] using hwb1)
  have e4 : Exec (B := .standard) w ram[val1 ← *addr1]
      (((x.set zero 0).set one 1).set addr1 (wb + 1)) s₁ 1 := by
    have ha' : (((x.set zero 0).set one 1).set addr1 (wb + 1)).regs addr1 = wb + 1 := by simp
    simpa [s₁, v_new, ha'] using
      Exec.load (B := .standard) (w := w) (d := val1) (a := addr1)
        (x := ((x.set zero 0).set one 1).set addr1 (wb + 1))
  let best_next := if i = 0 then v_new else min v_new (x.regs bestVal)
  have hbr : ∃ s₂ : Data 22,
      ExecWithin (B := .standard) w (ram[
        if trialIdx = zero then [ bestVal ← val1 ] else [
          if val1 < bestVal then [ bestVal ← val1 ] else [ zero ← #0 ]
        ]]) s₁ s₂ 5 ∧
      s₂.mem = x.mem ∧
      s₂.regs one = 1 ∧
      s₂.regs srcBase = x.regs srcBase ∧
      s₂.regs wBase = wb ∧
      s₂.regs dBase = x.regs dBase ∧
      s₂.regs nOrig = x.regs nOrig ∧
      s₂.regs matLen = x.regs matLen ∧
      s₂.regs numTrials = x.regs numTrials ∧
      s₂.regs trialIdx = i ∧
      s₂.regs bestVal = best_next := by
    have hs1_ti : s₁.regs trialIdx = i := by
      simpa +decide [s₁, Function.update_apply] using hti
    have hs1_z : s₁.regs zero = 0 := by simp +decide [s₁]
    have hs1_v1 : s₁.regs val1 = v_new := by simp [s₁]
    have hs1_bv : s₁.regs bestVal = x.regs bestVal := by simp +decide [s₁]
    by_cases hi0 : i = 0
    · have hc : (Cond.eq trialIdx zero).Holds s₁ := by simp [Cond.holds_eq, hs1_ti, hs1_z, hi0]
      have e_pos : ExecWithin (B := .standard) w ram[bestVal ← val1] s₁
          (s₁.set bestVal v_new) 1 := by
        simpa [hs1_v1] using
          (Exec.copy (B := .standard) (w := w) (d := bestVal) (s := val1) (x := s₁)).within
      refine ⟨s₁.set bestVal v_new,
        (ExecWithin.branch_pos hc e_pos).mono (by omega), rfl,
        by simp +decide [s₁],
        by simp +decide [s₁],
        by simpa +decide [s₁, Function.update_apply] using hwb,
        by simp +decide [s₁],
        by simp +decide [s₁],
        by simp +decide [s₁],
        by simp +decide [s₁],
        by simp +decide [hs1_ti],
        by simp [best_next, hi0]⟩
    · have hc : ¬(Cond.eq trialIdx zero).Holds s₁ := by simp [Cond.holds_eq, hs1_ti, hs1_z, hi0]
      by_cases hlt : v_new < x.regs bestVal
      · have hc2 : (Cond.lt val1 bestVal).Holds s₁ := by
          simp [Cond.holds_lt, hs1_v1, hs1_bv, hlt]
        have e_pos2 : ExecWithin (B := .standard) w ram[bestVal ← val1] s₁
            (s₁.set bestVal v_new) 1 := by
          simpa [hs1_v1] using
            (Exec.copy (B := .standard) (w := w) (d := bestVal) (s := val1) (x := s₁)).within
        have e_in := ExecWithin.branch_pos (neg := ram[zero ← #0]) hc2 e_pos2
        refine ⟨s₁.set bestVal v_new,
          (ExecWithin.branch_neg (pos := ram[bestVal ← val1]) hc e_in).mono (by omega), rfl,
          by simp +decide [s₁],
          by simp +decide [s₁],
          by simpa +decide [s₁, Function.update_apply] using hwb,
          by simp +decide [s₁],
          by simp +decide [s₁],
          by simp +decide [s₁],
          by simp +decide [s₁],
          by simp +decide [hs1_ti],
          by simp [best_next, hi0, Nat.min_eq_left (Nat.le_of_lt hlt)]⟩
      · have hc2 : ¬(Cond.lt val1 bestVal).Holds s₁ := by
          simp [Cond.holds_lt, hs1_v1, hs1_bv, hlt]
        have e_neg2 : ExecWithin (B := .standard) w ram[zero ← #0] s₁ (s₁.set zero 0) 1 :=
          ExecWithin.const (fits_zero w)
        have e_in := ExecWithin.branch_neg (pos := ram[bestVal ← val1]) hc2 e_neg2
        refine ⟨s₁.set zero 0,
          (ExecWithin.branch_neg (pos := ram[bestVal ← val1]) hc e_in).mono (by omega), rfl,
          by simp +decide [s₁],
          by simp +decide [s₁],
          by simpa +decide [s₁, Function.update_apply] using hwb,
          by simp +decide [s₁],
          by simp +decide [s₁],
          by simp +decide [s₁],
          by simp +decide [s₁],
          by simp +decide [hs1_ti],
          by simp +decide [s₁, best_next, hi0, Nat.min_eq_right (Nat.le_of_not_lt hlt)]⟩
  obtain ⟨s₂, e_br, hm2, ho2, hsb2, hwb2, hdb2, hn2, hml2, hnt2, hti2, hbv2⟩ := hbr
  have e_inc : ExecWithin w ram[trialIdx ← trialIdx + one] s₂ (s₂.set trialIdx (i + 1)) 1 := by
    simpa [BinOp.eval, hti2, ho2] using
      ExecWithin.bin (f := .add) (d := trialIdx) (i := trialIdx) (j := one) (x := s₂)
        (by simpa [BinOp.eval, hti2, ho2] using hi1_fit)
  refine ⟨s₂.set trialIdx (i + 1), ?_, hm2,
    by simpa +decide [Function.update_apply] using hsb2,
    by simpa +decide [Function.update_apply] using hwb2,
    by simpa +decide [Function.update_apply] using hdb2,
    by simpa +decide [Function.update_apply] using hn2,
    by simpa +decide [Function.update_apply] using hml2,
    by simpa +decide [Function.update_apply] using hnt2,
    by simp,
    by simpa +decide [Function.update_apply] using hbv2⟩
  unfold ampTrialPost
  exact ((e1.within).seq ((e2.within).seq ((e3.within).seq
    ((e4.within).seq (e_br.seq e_inc))))).mono (by omega)

private theorem ampTrial_step_bound {n n_cp n_deg t_c n_p : ℕ}
    (hcp : n_cp ≤ 7 * (n * n) + 4)
    (hdeg : n_deg ≤ 6 * n ^ 2 + 12 * n + 6)
    (hc : t_c ≤ 36 * (n ^ 2 - 2 ^ 2) + 4)
    (hp : n_p ≤ 10) :
    (n_cp + (3 + n_deg)) + (t_c + n_p) ≤ 49 * n ^ 2 + 12 * n + 27 := by
  have hnn : n * n = n ^ 2 := (sq n).symm
  omega

/-- Specification of a single trial `ampTrialBody` from `AmpInv`. -/
theorem ampTrialBody_spec {w sb n R i : ℕ} {W : Fin n → Fin n → ℕ} {mem₀ : ℕ → ℕ} {x : Data 22}
    (hn : 2 ≤ n) (hW : IsMultigraph W) (hiR : i < R)
    (h1 : Fits w 1) (hdEnd : Fits w (sb + 2 * (n * n) + n))
    (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W))
    (hinv : AmpInv w sb n R i W mem₀ x) :
    ∃ m : ProbComp (Data 22 × ℕ),
      ExecRand w ampTrialBody x m ∧
      m.IsQueryBounded (n - 2) ∧
      (∀ z ∈ m.support,
        z.2 ≤ 49 * n ^ 2 + 12 * n + 27 ∧
        AmpInv w sb n R (i + 1) W mem₀ z.1 ∧
        (0 < i → x.regs bestVal = minCut W → z.1.regs bestVal = minCut W)) ∧
      (0 < minCut W →
        m.eval.toOuterMeasure {z | z.1.regs bestVal ≠ minCut W} ≤
          (1 : ℝ≥0∞) - (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) := by
  let wb := sb + n * n
  let db := sb + 2 * (n * n)
  have hwEnd : Fits w (wb + n * n) := hdEnd.of_le (by omega)
  have h2_fit : Fits w 2 := hdEnd.of_le (by omega)
  have hwb1_fit : Fits w (wb + 1) := hdEnd.of_le (by omega)
  obtain ⟨y_cp, ⟨n_cp, hn_cp, e_cp⟩, hmat_cp, hmod_cp,
      hwb_cp, hdb_cp, hsb_cp, hn_cp_reg, hml_cp, hnt_cp, hti_cp, hbv_cp⟩ :=
    copyMatrixCode_exec hinv.regs_srcBase hinv.regs_wBase hinv.regs_matLen
      (le_refl _) h1 hwEnd hinv.src_matrix
  rw [hinv.regs_dBase] at hdb_cp
  rw [hinv.regs_nOrig] at hn_cp_reg
  rw [hinv.regs_numTrials] at hnt_cp
  rw [hinv.regs_trialIdx] at hti_cp
  let y_cfg := ((y_cp.set activeK n).set stride n).set targetT 2
  have ec1 : Exec (B := .standard) w ram[activeK ← nOrig] y_cp (y_cp.set activeK n) 1 := by
    simpa [hn_cp_reg] using
      Exec.copy (B := .standard) (w := w) (d := activeK) (s := nOrig) (x := y_cp)
  have ec2 : Exec (B := .standard) w ram[stride ← nOrig] (y_cp.set activeK n)
      ((y_cp.set activeK n).set stride n) 1 := by
    have hr : (y_cp.set activeK n).regs nOrig = n := by
      simpa +decide [Function.update_apply] using hn_cp_reg
    simpa [hr] using
      Exec.copy (B := .standard) (w := w) (d := stride) (s := nOrig) (x := y_cp.set activeK n)
  have ec3 : Exec (B := .standard) w ram[targetT ← #2]
      ((y_cp.set activeK n).set stride n) y_cfg 1 :=
    Exec.const h2_fit
  obtain ⟨y_deg, ⟨n_deg, hn_deg, e_deg⟩, hws_deg, hmod_deg,
      hwb_d, hdb_d, hstr_d, hk_d, ht_d, htot_d, hhi_d⟩ :=
    computeDegreesAndTotalAt_exec (w := w) (W := W) (x := y_cfg) hr22
      (by change y_cfg.regs wBase = wb; simpa +decide [y_cfg, Function.update_apply] using hwb_cp)
      (by change y_cfg.regs dBase = db; simpa +decide [y_cfg, Function.update_apply] using hdb_cp)
      (by change y_cfg.regs stride = n; simp +decide [y_cfg])
      (by change y_cfg.regs activeK = n; simp +decide [y_cfg])
      (le_refl n) (Or.inl (by omega)) h1 hwEnd hdEnd htot hmat_cp
  have ht_d' : y_deg.regs (Fin.castLE hr22 Reg.targetT) = 2 := by
    rw [ht_d]
    change y_cfg.regs targetT = 2
    simp [y_cfg]
  have hst_deg : ContractState w wb db n n 2 W (y_deg.comap (Fin.castLE hr22)) :=
    ⟨hwb_d, hdb_d, hstr_d, hk_d, ht_d', htot_d, le_refl n, Or.inl (by omega),
      hwEnd, hdEnd, htot, hws_deg⟩
  obtain ⟨m_c, hm_c, hq_c, hsup_c, hsurv_c⟩ :=
    contractDownToAt_spec hr22 (le_refl 2) hn (isContractionOf_id hW) hst_deg
  have hy_deg_hi : y_deg.regs srcBase = sb ∧ y_deg.regs nOrig = n ∧
      y_deg.regs matLen = n * n ∧ y_deg.regs numTrials = R ∧
      y_deg.regs trialIdx = i ∧ y_deg.regs bestVal = x.regs bestVal := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hhi_d srcBase (by decide)]; simpa +decide [y_cfg, Function.update_apply] using hsb_cp
    · rw [hhi_d nOrig (by decide)]; simpa +decide [y_cfg, Function.update_apply] using hn_cp_reg
    · rw [hhi_d matLen (by decide)]; simpa +decide [y_cfg, Function.update_apply] using hml_cp
    · rw [hhi_d numTrials (by decide)]; simpa +decide [y_cfg, Function.update_apply] using hnt_cp
    · rw [hhi_d trialIdx (by decide)]; simpa +decide [y_cfg, Function.update_apply] using hti_cp
    · rw [hhi_d bestVal (by decide)]; simpa +decide [y_cfg, Function.update_apply] using hbv_cp
  have hpost_all : ∀ z ∈ m_c.support,
      ∃ (y_p : Data 22) (n_p : ℕ), n_p ≤ 10 ∧ Exec w ampTrialPost z.1 y_p n_p ∧
        y_p.mem = z.1.mem ∧
        y_p.regs srcBase = sb ∧ y_p.regs wBase = wb ∧ y_p.regs dBase = db ∧
        y_p.regs nOrig = n ∧ y_p.regs matLen = n * n ∧ y_p.regs numTrials = R ∧
        y_p.regs trialIdx = i + 1 ∧
        y_p.regs bestVal =
          (if i = 0 then z.1.mem (wb + 1) else min (z.1.mem (wb + 1)) (x.regs bestVal)) := by
    intro z hz
    rcases hsup_c z hz with ⟨_, _, hz_hi, W', part', _, hst'⟩
    have hz_wb : z.1.regs wBase = wb := hst'.regs_wBase
    have hz_db : z.1.regs dBase = db := hst'.regs_dBase
    have hz_sb : z.1.regs srcBase = sb := (hz_hi srcBase (by decide)).trans hy_deg_hi.1
    have hz_n : z.1.regs nOrig = n := (hz_hi nOrig (by decide)).trans hy_deg_hi.2.1
    have hz_ml : z.1.regs matLen = n * n := (hz_hi matLen (by decide)).trans hy_deg_hi.2.2.1
    have hz_nt : z.1.regs numTrials = R := (hz_hi numTrials (by decide)).trans hy_deg_hi.2.2.2.1
    have hz_ti : z.1.regs trialIdx = i := (hz_hi trialIdx (by decide)).trans hy_deg_hi.2.2.2.2.1
    have hz_bv : z.1.regs bestVal = x.regs bestVal :=
      (hz_hi bestVal (by decide)).trans hy_deg_hi.2.2.2.2.2
    obtain ⟨y_p, ⟨n_p, hn_p, e_p⟩, hm_p, hsb_p, hwb_p, hdb_p, hn_p_r, hml_p, hnt_p, hti_p, hbv_p⟩ :=
      ampTrialPost_exec hz_wb hz_ti hiR h1 hwb1_fit hR_fit
    exact ⟨y_p, n_p, hn_p, e_p, hm_p, hsb_p.trans hz_sb, hwb_p, hdb_p.trans hz_db,
      hn_p_r.trans hz_n, hml_p.trans hz_ml, hnt_p.trans hz_nt, hti_p,
      by simpa only [hz_bv] using hbv_p⟩
  obtain ⟨m_post, hm_post_def⟩ :
      ∃ m_post : Data 22 → ProbComp (Data 22 × ℕ),
        ∀ d, m_post d = codeComp w ampTrialPost d := ⟨_, fun _ => rfl⟩
  have hm_post : ∀ z ∈ m_c.support, ExecRand w ampTrialPost z.1 (m_post z.1) := by
    intro z hz
    obtain ⟨y_p, n_p, _, e_p, _⟩ := hpost_all z hz
    have hr := e_p.execRand
    rw [hm_post_def]
    simpa only [hr.codeComp_eq] using hr
  have hm_c_post := ExecRand.seq hm_c hm_post
  have hm_body : ExecRand w ampTrialBody x
      ((fun z => (z.1, (n_cp + (3 + n_deg)) + z.2)) <$>
        (do let z₁ ← m_c; let z₂ ← m_post z₁.1; pure (z₂.1, z₁.2 + z₂.2))) := by
    have hbody_eq : ampTrialBody = .seq copyMatrixCode
        (.seq ram[activeK ← nOrig] (.seq ram[stride ← nOrig]
          (.seq ram[targetT ← #2] (.seq (computeDegreesAndTotalAt hr22)
            (.seq (contractDownToAt hr22) ampTrialPost))))) := rfl
    rw [hbody_eq]
    have r4 := e_deg.seqRand hm_c_post
    have r3 := ec3.seqRand r4
    have r2 := ec2.seqRand r3
    have r1 := ec1.seqRand r2
    have r0 := e_cp.seqRand r1
    have h111 : ∀ k, 1 + (1 + (1 + k)) = 3 + k := fun _ => by omega
    simpa only [Functor.map_map, Nat.add_assoc, h111] using r0
  let m_total := (fun z => (z.1, (n_cp + (3 + n_deg)) + z.2)) <$>
    (do let z₁ ← m_c; let z₂ ← m_post z₁.1; pure (z₂.1, z₁.2 + z₂.2))
  refine ⟨m_total, hm_body, ?_, ?_, ?_⟩
  · simp only [m_total, OracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
    have hq_post : ∀ z₁ ∈ m_c.support,
        (m_post z₁.1 >>= fun z₂ => pure (z₂.1, z₁.2 + z₂.2)).IsQueryBounded 0 := by
      intro z₁ hz₁
      obtain ⟨y_p, n_p, _, e_p, _⟩ := hpost_all z₁ hz₁
      rw [hm_post_def, e_p.execRand.codeComp_eq, pure_bind]
      exact .pure _ 0
    simpa only [Nat.add_zero] using OracleComp.IsCostBounded.bind_on_support hq_c hq_post
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₀
    obtain ⟨y_p, n_p, hn_p, e_p, hm_p, hsb_p, hwb_p, hdb_p, hn_p_r, hml_p, hnt_p, hti_p, hbv_p⟩ :=
      hpost_all z₁ hz₁
    rw [hm_post_def, e_p.execRand.codeComp_eq] at hrest
    obtain ⟨z₂, hz₂, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hz₂
    cases OracleComp.eq_of_mem_supportWith_pure hpure
    rcases hsup_c z₁ hz₁ with ⟨ht_c, hmod_c, _, W', part', hC', hst'⟩
    have hmod_ws_all : Modifies (Finset.Ico wb (db + n)) x.mem y_p.mem := by
      rw [hm_p]
      have hs_cp : Finset.Ico wb (wb + n * n) ⊆ Finset.Ico wb (db + n) :=
        Finset.Ico_subset_Ico (le_refl _) (by omega)
      have hs_deg : Finset.Ico db (db + n) ⊆ Finset.Ico wb (db + n) :=
        Finset.Ico_subset_Ico (by omega) (le_refl _)
      have hs_c : workspaceFootprint wb db n n ⊆ Finset.Ico wb (db + n) := by
        intro a ha
        simp only [workspaceFootprint, Finset.mem_union, Finset.mem_Ico] at ha ⊢
        omega
      have hm12 := modifies_trans_subset hmod_cp hmod_deg hs_cp hs_deg
      exact modifies_trans_subset hm12 hmod_c Finset.Subset.rfl hs_c
    have hsrc_preserved : HoldsMatrix y_p.mem sb n W := by
      intro a b
      have hlt : sb + a.val * n + b.val < wb := by
        have := matAddr_lt_end (wb := sb) (le_refl n) a b
        omega
      rw [hmod_ws_all _ (by rw [Finset.mem_Ico]; omega)]
      exact hinv.src_matrix a b
    have hnew_cut : z₁.1.mem (wb + 1) = cutWeight W (pullbackCut part' {0}) := by
      rw [cutWeight_pullbackCut hC', cutWeight_two_singleton_zero hC'.multigraph]
      simpa using hst'.workspace.1 0 1
    have hnew_nt : IsNonTrivialCut (pullbackCut part' {0}) :=
      isNonTrivialCut_pullbackCut hC'.surj (isNonTrivialCut_singleton (le_refl 2) 0)
    refine ⟨ampTrial_step_bound hn_cp hn_deg ht_c hn_p, ?_, ?_⟩
    · refine ⟨hsb_p, hwb_p, hdb_p, hn_p_r, hml_p, hnt_p, hti_p, hsrc_preserved,
        modifies_trans_subset hinv.modifies_ws hmod_ws_all Finset.Subset.rfl Finset.Subset.rfl,
        fun _ => ?_⟩
      by_cases hi0 : i = 0
      · exact ⟨pullbackCut part' {0}, hnew_nt, by simp [hbv_p, hi0, hnew_cut]⟩
      · obtain ⟨C_old, hC_old_nt, hbv_old⟩ := hinv.best_cut (Nat.pos_of_ne_zero hi0)
        simp only [hbv_p, hi0, ↓reduceIte]
        by_cases hle : z₁.1.mem (wb + 1) ≤ x.regs bestVal
        · exact ⟨pullbackCut part' {0}, hnew_nt, by rw [Nat.min_eq_left hle, hnew_cut]⟩
        · exact ⟨C_old, hC_old_nt, by rw [Nat.min_eq_right (Nat.le_of_not_le hle), hbv_old]⟩
    · intro hi_pos hbv_min
      have hi0 : i ≠ 0 := Nat.ne_of_gt hi_pos
      have hge : minCut W ≤ z₁.1.mem (wb + 1) := by
        rw [hnew_cut]
        exact minCut_le_cutWeight W hnew_nt
      simp only [hbv_p, hi0, ↓reduceIte, hbv_min]
      exact Nat.min_eq_right hge
  · intro hmin_pos
    obtain ⟨C_star, hC_nt, hC_min⟩ := exists_minCut_achiever hn W
    have hpb_id : pullbackCut (id : Fin n → Fin n) C_star = C_star := by
      ext u
      simp [pullbackCut]
    have hsurv := hsurv_c C_star hmin_pos hC_nt (by rw [hpb_id, hC_min])
    rw [hpb_id] at hsurv
    have h2 : (((2 * (2 - 1) : ℕ) : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) =
        (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) := by norm_num
    rw [h2] at hsurv
    have hhit_ge : (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) ≤
        m_total.eval.toOuterMeasure {z | z.1.regs bestVal = minCut W} := by
      refine hsurv.trans ?_
      have hm_eval : m_total.eval =
          m_c.eval.bind fun z₁ =>
            ((m_post z₁.1).eval.map fun z₂ =>
              (z₂.1, (n_cp + (3 + n_deg)) + (z₁.2 + z₂.2))) := by
        have hm_eq : m_total = (do
            let z₁ ← m_c
            let z₂ ← m_post z₁.1
            pure (z₂.1, (n_cp + (3 + n_deg)) + (z₁.2 + z₂.2))) := by
          simp only [m_total, ← bind_pure_comp, bind_assoc, pure_bind]
        rw [hm_eq, ProbComp.eval_bind]
        refine congrArg (m_c.eval.bind ·) (funext fun z₁ => ?_)
        rw [bind_pure_comp, ProbComp.eval_map]
      rw [hm_eval]
      have hstep := toOuterMeasure_bind_ge_mul_ennreal m_c.eval
        (fun z₁ => (m_post z₁.1).eval.map fun z₂ =>
          (z₂.1, (n_cp + (3 + n_deg)) + (z₁.2 + z₂.2)))
        {z | SurvivalPost W wb db n 2 C_star (z.1.comap (Fin.castLE hr22))}
        {z | z.1.regs bestVal = minCut W}
        (s₁ := m_c.eval.toOuterMeasure
          {z | SurvivalPost W wb db n 2 C_star (z.1.comap (Fin.castLE hr22))})
        (s₂ := 1) le_rfl ?_
      · simpa using hstep
      · intro z₁ hz₁_eval hsurv₁
        have hz₁ : z₁ ∈ m_c.support := (ProbComp.support_eval m_c) ▸ hz₁_eval
        obtain ⟨y_p, n_p, _, e_p, _, _, _, _, _, _, _, _, hbv_p⟩ := hpost_all z₁ hz₁
        rw [hm_post_def, e_p.execRand.codeComp_eq, ProbComp.eval_pure,
          PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_pure_apply]
        have hmem_wb1 : z₁.1.mem (wb + 1) = minCut W :=
          survivalPost_two_mem_eq hC_nt hC_min hsurv₁
        have hbv_hit : y_p.regs bestVal = minCut W := by
          rw [hbv_p, hmem_wb1]
          by_cases hi0 : i = 0
          · simp [hi0]
          · obtain ⟨C_old, hC_old_nt, hbv_old⟩ := hinv.best_cut (Nat.pos_of_ne_zero hi0)
            simp only [hi0, ↓reduceIte, hbv_old]
            exact Nat.min_eq_left (minCut_le_cutWeight W hC_old_nt)
        simp [hbv_hit]
    have hcompl : {z : Data 22 × ℕ | z.1.regs bestVal ≠ minCut W} =
        {z : Data 22 × ℕ | z.1.regs bestVal = minCut W}ᶜ := by
      ext z
      simp
    rw [hcompl]
    exact toOuterMeasure_compl_le_one_sub m_total.eval _ hhit_ge

/-- Specification of `ampLoop` over `rem = R - i` remaining trials. -/
theorem ampLoop_spec {w sb n R : ℕ} {W : Fin n → Fin n → ℕ} {mem₀ : ℕ → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (h1 : Fits w 1) (hdEnd : Fits w (sb + 2 * (n * n) + n))
    (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W)) :
    ∀ (rem i : ℕ) (x : Data 22),
      i + rem = R →
      AmpInv w sb n R i W mem₀ x →
      ∃ m : ProbComp (Data 22 × ℕ),
        ExecRand w ampLoop x m ∧
        m.IsQueryBounded (rem * (n - 2)) ∧
        (∀ z ∈ m.support,
          z.2 ≤ rem * (50 * n ^ 2 + 12 * n + 30) + 2 ∧
          AmpInv w sb n R R W mem₀ z.1 ∧
          (0 < i → x.regs bestVal = minCut W → z.1.regs bestVal = minCut W)) ∧
        (0 < minCut W →
          m.eval.toOuterMeasure {z | z.1.regs bestVal ≠ minCut W} ≤
            ((1 : ℝ≥0∞) - (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) ^ rem) := by
  intro rem
  induction rem with
  | zero =>
    intro i x hiR hinv
    have hi_eq : i = R := by omega
    subst hi_eq
    have hc : ¬(Cond.lt trialIdx numTrials).Holds x := by
      simp [Cond.holds_lt, hinv.regs_trialIdx, hinv.regs_numTrials]
    refine ⟨pure (x, 2), .loop_exit hc, .pure _ _, ?_, ?_⟩
    · intro z hz
      cases OracleComp.eq_of_mem_supportWith_pure hz
      exact ⟨by simp, hinv, fun _ hbv => hbv⟩
    · intro _
      simp only [pow_zero]
      exact Cslib.Probability.PMF.toOuterMeasure_le_one _ _
  | succ rem ih =>
    intro i x hiR hinv
    have hi_lt : i < R := by omega
    have hc : (Cond.lt trialIdx numTrials).Holds x := by
      simp [Cond.holds_lt, hinv.regs_trialIdx, hinv.regs_numTrials, hi_lt]
    obtain ⟨m_b, hm_b, hq_b, hsup_b, hfail_b⟩ :=
      ampTrialBody_spec hn hW hi_lt h1 hdEnd hR_fit htot hinv
    have hnext : ∀ z₁ ∈ m_b.support,
        ∃ m_r : ProbComp (Data 22 × ℕ),
          ExecRand w ampLoop z₁.1 m_r ∧
          m_r.IsQueryBounded (rem * (n - 2)) ∧
          (∀ z₂ ∈ m_r.support,
            z₂.2 ≤ rem * (50 * n ^ 2 + 12 * n + 30) + 2 ∧
            AmpInv w sb n R R W mem₀ z₂.1 ∧
            (0 < i + 1 → z₁.1.regs bestVal = minCut W → z₂.1.regs bestVal = minCut W)) ∧
          (0 < minCut W →
            m_r.eval.toOuterMeasure {z | z.1.regs bestVal ≠ minCut W} ≤
              ((1 : ℝ≥0∞) - (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) ^ rem) := by
      intro z₁ hz₁
      exact ih (i + 1) z₁.1 (by omega) (hsup_b z₁ hz₁).2.1
    obtain ⟨ml, hml_def⟩ :
        ∃ ml : Data 22 → ProbComp (Data 22 × ℕ),
          ∀ d, ml d = codeComp w ampLoop d := ⟨_, fun _ => rfl⟩
    have hml_exec : ∀ z₁ ∈ m_b.support, ExecRand w ampLoop z₁.1 (ml z₁.1) := by
      intro z₁ hz₁
      obtain ⟨m_r, hm_r, _⟩ := hnext z₁ hz₁
      rw [hml_def]
      simpa only [hm_r.codeComp_eq] using hm_r
    have hm_iter : ExecRand w ampLoop x
        (do let z₁ ← m_b; let z₂ ← ml z₁.1; pure (z₂.1, z₁.2 + z₂.2 + 2)) :=
      ExecRand.loop_iter hc hm_b hml_exec
    let m_total := (do let z₁ ← m_b; let z₂ ← ml z₁.1; pure (z₂.1, z₁.2 + z₂.2 + 2))
    refine ⟨m_total, hm_iter, ?_, ?_, ?_⟩
    · have hq_each : ∀ z₁ ∈ m_b.support,
          (ml z₁.1 >>= fun z₂ => pure (z₂.1, z₁.2 + z₂.2 + 2)).IsQueryBounded
            (rem * (n - 2)) := by
        intro z₁ hz₁
        obtain ⟨m_r, hm_r, hq_r, _⟩ := hnext z₁ hz₁
        rw [hml_def, hm_r.codeComp_eq]
        simpa only [Nat.add_zero] using hq_r.bind fun _ => .pure _ 0
      have hq_tot := OracleComp.IsCostBounded.bind_on_support hq_b hq_each
      exact hq_tot.mono (by rw [Nat.succ_mul, Nat.add_comm])
    · intro z hz
      obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
      obtain ⟨m_r, hm_r, _, hsup_r, _⟩ := hnext z₁ hz₁
      rw [hml_def, hm_r.codeComp_eq] at hrest
      obtain ⟨z₂, hz₂, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
      cases OracleComp.eq_of_mem_supportWith_pure hpure
      rcases hsup_b z₁ hz₁ with ⟨ht₁, _, hstick₁⟩
      rcases hsup_r z₂ hz₂ with ⟨ht₂, hinv₂, hstick₂⟩
      refine ⟨?_, hinv₂, ?_⟩
      · rw [Nat.succ_mul]
        omega
      · intro hi_pos hbv_x
        exact hstick₂ (Nat.succ_pos i) (hstick₁ hi_pos hbv_x)
    · intro hmin_pos
      have hm_eval : m_total.eval =
          m_b.eval.bind fun z₁ =>
            ((ml z₁.1).eval.map fun z₂ => (z₂.1, z₁.2 + z₂.2 + 2)) := by
        dsimp only [m_total]
        rw [ProbComp.eval_bind]
        refine congrArg (m_b.eval.bind ·) (funext fun z₁ => ?_)
        rw [bind_pure_comp, ProbComp.eval_map]
      rw [hm_eval, pow_succ']
      refine toOuterMeasure_bind_le_mul_ennreal m_b.eval
        (fun z₁ => (ml z₁.1).eval.map fun z₂ => (z₂.1, z₁.2 + z₂.2 + 2))
        {z₁ | z₁.1.regs bestVal ≠ minCut W}
        {z | z.1.regs bestVal ≠ minCut W}
        (q₁ := (1 : ℝ≥0∞) - (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞))
        (q₂ := ((1 : ℝ≥0∞) - (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) ^ rem)
        (hfail_b hmin_pos) ?_ ?_
      · intro z₁ hz₁_eval _
        have hz₁ : z₁ ∈ m_b.support := (ProbComp.support_eval m_b) ▸ hz₁_eval
        obtain ⟨m_r, hm_r, _, _, hfail_r⟩ := hnext z₁ hz₁
        rw [hml_def, hm_r.codeComp_eq, PMF.toOuterMeasure_map_apply]
        exact hfail_r hmin_pos
      · intro z₁ hz₁_eval hhit
        have hz₁ : z₁ ∈ m_b.support := (ProbComp.support_eval m_b) ▸ hz₁_eval
        have hbv₁ : z₁.1.regs bestVal = minCut W := not_not.mp hhit
        obtain ⟨m_r, hm_r, _, hsup_r, _⟩ := hnext z₁ hz₁
        rw [hml_def, hm_r.codeComp_eq, PMF.toOuterMeasure_map_apply,
          PMF.toOuterMeasure_apply]
        refine tsum_eq_zero_iff.mpr ?_
        intro z₂
        by_cases hz₂_eval : z₂ ∈ m_r.eval.support
        · have hz₂ : z₂ ∈ m_r.support := (ProbComp.support_eval m_r) ▸ hz₂_eval
          have hbv₂ : z₂.1.regs bestVal = minCut W :=
            (hsup_r z₂ hz₂).2.2 (Nat.succ_pos i) hbv₁
          have hnot : z₂ ∉ ((fun z : Data 22 × ℕ => (z.1, z₁.2 + z.2 + 2)) ⁻¹'
              {z : Data 22 × ℕ | z.1.regs bestVal ≠ minCut W}) := by
            simp [hbv₂]
          exact Set.indicator_of_notMem hnot _
        · have hp0 : m_r.eval z₂ = 0 := by simpa only [PMF.mem_support_iff, not_not] using hz₂_eval
          simp [hp0]

/-- Specification of `ampCore` for `1 ≤ R` trials from any state with `srcBase = sb`,
`nOrig = n`, `numTrials = R`, and `HoldsMatrix x.mem sb n W`. -/
theorem ampCore_spec {w sb n R : ℕ} {W : Fin n → Fin n → ℕ} {x : Data 22}
    (hR : 1 ≤ R) (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hsb : x.regs srcBase = sb) (hnOrig : x.regs nOrig = n) (hnumT : x.regs numTrials = R)
    (h1 : Fits w 1) (hdEnd : Fits w (sb + 2 * (n * n) + n))
    (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W))
    (hsrc_mat : HoldsMatrix x.mem sb n W) :
    ∃ m : ProbComp (Data 22 × ℕ),
      ExecRand w ampCore x m ∧
      m.IsQueryBounded (R * (n - 2)) ∧
      (∀ z ∈ m.support,
        z.2 ≤ R * (50 * n ^ 2 + 12 * n + 30) + 8 ∧
        Modifies (Finset.Ico (sb + n * n) (sb + 2 * (n * n) + n)) x.mem z.1.mem ∧
        ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ z.1.regs bestVal = cutWeight W C) ∧
      (0 < minCut W →
        m.eval.toOuterMeasure {z | z.1.regs bestVal ≠ minCut W} ≤
          ((1 : ℝ≥0∞) - (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) ^ R) := by
  have hnn_fit : Fits w (n * n) := hdEnd.of_le (by omega)
  have hwb_fit : Fits w (sb + n * n) := hdEnd.of_le (by omega)
  have hdb_fit : Fits w (sb + 2 * (n * n)) := hdEnd.of_le (by omega)
  let s₁ := x.set val1 (n * n)
  let s₂ := s₁.set matLen (n * n)
  let s₃ := s₂.set wBase (sb + n * n)
  let s₄ := s₃.set dBase (sb + 2 * (n * n))
  let s₅ := s₄.set trialIdx 0
  let s₆ := s₅.set bestVal 0
  have e1 : Exec w ram[val1 ← nOrig * nOrig] x s₁ 1 := by
    simpa [s₁, BinOp.eval, hnOrig] using
      Exec.bin (w := w) (f := .mul) (d := val1) (i := nOrig) (j := nOrig) (x := x)
        (by simpa [BinOp.eval, hnOrig] using hnn_fit)
  have e2 : Exec (B := .standard) w ram[matLen ← val1] s₁ s₂ 1 := by
    have hv1 : s₁.regs val1 = n * n := by simp [s₁]
    simpa [s₂, hv1] using Exec.copy (B := .standard) (w := w) (d := matLen) (s := val1) (x := s₁)
  have e3 : Exec w ram[wBase ← srcBase + matLen] s₂ s₃ 1 := by
    have hs : s₂.regs srcBase = sb := by simpa +decide [s₂, s₁, Function.update_apply] using hsb
    have hm : s₂.regs matLen = n * n := by simp [s₂]
    simpa [s₃, BinOp.eval, hs, hm] using
      Exec.bin (w := w) (f := .add) (d := wBase) (i := srcBase) (j := matLen) (x := s₂)
        (by simpa [BinOp.eval, hs, hm] using hwb_fit)
  have e4 : Exec w ram[dBase ← wBase + matLen] s₃ s₄ 1 := by
    have hw' : s₃.regs wBase = sb + n * n := by simp [s₃]
    have hm : s₃.regs matLen = n * n := by simp +decide [s₃, s₂]
    have hadd : sb + n * n + n * n = sb + 2 * (n * n) := by omega
    simpa [s₄, BinOp.eval, hw', hm, hadd] using
      Exec.bin (w := w) (f := .add) (d := dBase) (i := wBase) (j := matLen) (x := s₃)
        (by simpa [BinOp.eval, hw', hm, hadd] using hdb_fit)
  have e5 : Exec (B := .standard) w ram[trialIdx ← #0] s₄ s₅ 1 := Exec.const (fits_zero w)
  have e6 : Exec (B := .standard) w ram[bestVal ← #0] s₅ s₆ 1 := Exec.const (fits_zero w)
  have hinv₀ : AmpInv w sb n R 0 W x.mem s₆ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hsrc_mat, Modifies.refl _ _, fun h0 => absurd h0 (by omega)⟩
    · simpa +decide [s₆, s₅, s₄, s₃, s₂, s₁, Function.update_apply] using hsb
    · simp +decide [s₆, s₅, s₄, s₃]
    · simp +decide [s₆, s₅, s₄]
    · simpa +decide [s₆, s₅, s₄, s₃, s₂, s₁, Function.update_apply] using hnOrig
    · simp +decide [s₆, s₅, s₄, s₃, s₂]
    · simpa +decide [s₆, s₅, s₄, s₃, s₂, s₁, Function.update_apply] using hnumT
    · simp +decide [s₆, s₅]
  obtain ⟨m_l, hm_l, hq_l, hsup_l, hfail_l⟩ :=
    ampLoop_spec (mem₀ := x.mem) hn hW h1 hdEnd hR_fit htot R 0 s₆ (Nat.zero_add R) hinv₀
  have hcore_eq : ampCore = .seq ram[val1 ← nOrig * nOrig]
      (.seq ram[matLen ← val1] (.seq ram[wBase ← srcBase + matLen]
        (.seq ram[dBase ← wBase + matLen] (.seq ram[trialIdx ← #0]
          (.seq ram[bestVal ← #0] ampLoop))))) := rfl
  rw [hcore_eq]
  have hm_full := e1.seqRand (e2.seqRand (e3.seqRand (e4.seqRand (e5.seqRand (e6.seqRand hm_l)))))
  refine ⟨_, hm_full, ?_, ?_, ?_⟩
  · simp only [Functor.map_map, OracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
    exact hq_l
  · intro z hz
    simp only [Functor.map_map] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    rcases hsup_l z₀ hz₀ with ⟨ht₀, hinv_f, _⟩
    exact ⟨by omega, hinv_f.modifies_ws, hinv_f.best_cut hR⟩
  · intro hmin_pos
    simp only [Functor.map_map, ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    exact hfail_l hmin_pos

end AmplificationEngine

/-! ### Endpoint 2: Amplified `R`-trial Karger (`r = 22`) -/

section Amplified

open AmpReg

/-- Setup for `amplifiedCode` on `R :: n :: flattenMatrix W`: load `R = mem[1]`, `n = mem[2]`, and
set `srcBase = 3`. -/
def amplifiedSetup : Code .standard 22 := ram[
  one ← #1;
  numTrials ← *one;
  srcBase ← #2;
  nOrig ← *srcBase;
  srcBase ← #3
]

/-- Structured 22-register `R`-trial Karger program on `R :: n :: flattenMatrix W`. -/
def amplifiedCode : Code .standard 22 := ram[
  ⟪amplifiedSetup⟫;
  ⟪ampCore⟫
]

/-- Compiled 22-register `R`-trial Karger program. -/
def amplifiedProgram : Program .standard 22 :=
  amplifiedCode.program bestVal

/-- Worst-case instruction bound `R * (50 * n ^ 2 + 12 * n + 30) + 16` for `amplifiedProgram`. -/
def amplifiedTime (R n : ℕ) : ℕ :=
  R * (50 * n ^ 2 + 12 * n + 30) + 16

theorem amplifiedSetup_exec {w R n : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hw : logWidth 3 n ≤ w) :
    ∃ y : Data 22, Exec w amplifiedSetup (Data.init (R :: n :: flattenMatrix W)) y 5 ∧
      y.mem = (Data.init (r := 22) (R :: n :: flattenMatrix W)).mem ∧
      y.regs srcBase = 3 ∧ y.regs nOrig = n ∧ y.regs numTrials = R := by
  have hws := fits_workspace_of_logWidth_three hn hw
  have h1 : Fits w 1 := hws.of_le (by omega)
  have h2 : Fits w 2 := hws.of_le (by omega)
  have h3 : Fits w 3 := hws.of_le (by omega)
  let x₀ : Data 22 := Data.init (R :: n :: flattenMatrix W)
  have hm1 : x₀.mem 1 = R := rfl
  have hm2 : x₀.mem 2 = n := rfl
  let s₁ := x₀.set one 1
  let s₂ := s₁.set numTrials R
  let s₃ := s₂.set srcBase 2
  let s₄ := s₃.set nOrig n
  let s₅ := s₄.set srcBase 3
  have e1 : Exec (B := .standard) w ram[one ← #1] x₀ s₁ 1 := Exec.const h1
  have e2 : Exec (B := .standard) w ram[numTrials ← *one] s₁ s₂ 1 := by
    have hr : s₁.regs one = 1 := by simp [s₁]
    simpa [s₂, s₁, hr, hm1] using
      Exec.load (B := .standard) (w := w) (d := numTrials) (a := one) (x := s₁)
  have e3 : Exec (B := .standard) w ram[srcBase ← #2] s₂ s₃ 1 := Exec.const h2
  have e4 : Exec (B := .standard) w ram[nOrig ← *srcBase] s₃ s₄ 1 := by
    have hr : s₃.regs srcBase = 2 := by simp [s₃]
    simpa [s₄, s₃, s₂, s₁, hr, hm2] using
      Exec.load (B := .standard) (w := w) (d := nOrig) (a := srcBase) (x := s₃)
  have e5 : Exec (B := .standard) w ram[srcBase ← #3] s₄ s₅ 1 := Exec.const h3
  exact ⟨s₅, e1.seq (e2.seq (e3.seq (e4.seq e5))), rfl,
    by simp [s₅], by simp +decide [s₅, s₄], by simp +decide [s₅, s₄, s₃, s₂]⟩

/-- Structured `ProbComp` specification of `amplifiedCode`. -/
theorem amplifiedCode_spec {R n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hR : 1 ≤ R) (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W)) :
    ∃ m : ProbComp (Data 22 × ℕ),
      ExecRand w amplifiedCode (Data.init (R :: n :: flattenMatrix W)) m ∧
      m.IsQueryBounded (R * (n - 2)) ∧
      (∀ z ∈ m.support,
        z.2 + 1 ≤ amplifiedTime R n ∧
        Modifies (Finset.Ico (3 + n * n) (3 + 2 * (n * n) + n))
          (Data.init (r := 22) (R :: n :: flattenMatrix W)).mem z.1.mem ∧
        ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ z.1.regs bestVal = cutWeight W C) ∧
      (0 < minCut W →
        m.eval.toOuterMeasure {z | z.1.regs bestVal ≠ minCut W} ≤
          ((1 : ℝ≥0∞) - (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) ^ R) := by
  have hws := fits_workspace_of_logWidth_three hn hw
  have h1 : Fits w 1 := hws.of_le (by omega)
  obtain ⟨y_s, e_s, hm_s, hsb_s, hn_s, hnt_s⟩ := amplifiedSetup_exec (R := R) (W := W) hn hw
  obtain ⟨m_c, hm_c, hq_c, hsup_c, hfail_c⟩ :=
    ampCore_spec hR hn hW hsb_s hn_s hnt_s h1 hws hR_fit htot
      (hm_s ▸ holdsMatrix_init_amplified W)
  refine ⟨_, e_s.seqRand hm_c, ?_, ?_, ?_⟩
  · simp only [OracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
    exact hq_c
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    rcases hsup_c z₀ hz₀ with ⟨ht₀, hmod₀, hcut₀⟩
    exact ⟨by simp only [amplifiedTime]; omega, hm_s ▸ hmod₀, hcut₀⟩
  · intro hmin_pos
    rw [ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    exact hfail_c hmin_pos

/-- **`R`-trial amplified Karger specification (`amplifiedProgram`).**
At word size `w ≥ logWidth 3 n` when `1 ≤ R`, `R < 2 ^ w`, and `totalDoubledWeight W < 2 ^ w`:
1. `amplifiedProgram` halts within `amplifiedTime R n = R * (50 * n ^ 2 + 12 * n + 30) + 16` steps;
2. executes at most `R * (n - 2)` `rand` calls;
3. on every supported branch, outputs `cutWeight W C ≥ minCut W` for a genuine non-trivial cut `C`
   of `W` while modifying memory only in `[3 + n * n, 3 + 2 * (n * n) + n)`;
4. when `0 < minCut W` (excluded only for proof convenience; `S = 0` contraction still halts
   fault-free with a valid cut weight), misses `minCut W` with probability at most
   `(1 - 2 / (n * (n - 1))) ^ R`. -/
theorem amplifiedProgram_spec {R n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hR : 1 ≤ R) (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W)) :
    let input := R :: n :: flattenMatrix W
    RandHaltsWithin w amplifiedProgram (.init input) (amplifiedTime R n) ∧
    RandCallsBounded w amplifiedProgram (.init input) (amplifiedTime R n) (R * (n - 2)) ∧
    (∀ cfg ∈ (runRand w amplifiedProgram (amplifiedTime R n) (.running (.init input))).support,
      ∃ (y : Data 22) (C : Finset (Fin n)),
        cfg = .halted (cutWeight W C) y ∧
        y.Bounded w ∧
        IsNonTrivialCut C ∧
        minCut W ≤ cutWeight W C ∧
        Modifies (Finset.Ico (3 + n * n) (3 + 2 * (n * n) + n))
          (Data.init (r := 22) input).mem y.mem) ∧
    (0 < minCut W →
      (evalRand w amplifiedProgram (amplifiedTime R n) (.init input)).toOuterMeasure
          {cfg | ∀ y, cfg ≠ .halted (minCut W) y} ≤
        ((1 : ℝ≥0∞) - (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) ^ R) := by
  intro input
  have hfit_in : InputFits w input := inputFits_amplified hn hw hR_fit htot
  obtain ⟨m, hm, hq, hsup, hfail⟩ := amplifiedCode_spec hR hn hW hw hR_fit htot
  have hrun : runRand w amplifiedProgram (amplifiedTime R n) (.running (.init input)) =
      (fun z : Data 22 × ℕ => RandCfg.halted (z.1.regs bestVal) z.1) <$> m :=
    hm.runRand_program bestVal fun z hz => (hsup z hz).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cfg hcfg
    rw [hrun] at hcfg
    obtain ⟨z, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hcfg
    exact ⟨z.1.regs bestVal, z.1, rfl⟩
  · rw [RandCallsBounded, hrun]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr hq
  · intro cfg hcfg
    have hbnd := runRand_bounded_init hfit_in hcfg
    rw [hrun] at hcfg
    obtain ⟨z, hz, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hcfg
    rcases hsup z hz with ⟨_, hmod, C, hC_nt, hbv⟩
    exact ⟨z.1, C, by rw [hbv], hbnd.2, hC_nt, minCut_le_cutWeight W hC_nt, hmod⟩
  · intro hmin_pos
    rw [evalRand, hrun, ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    refine (PMF.toOuterMeasure_mono _ ?_).trans (hfail hmin_pos)
    intro z hz heq
    exact hz.1 z.1 (congrArg (fun v => RandCfg.halted v z.1) heq)

end Amplified

/-! ### Endpoint 3: Explicit `O(n ^ 4 log n)` high-probability global minimum cut (`r = 22`) -/

section HighProb

open AmpReg

/-- Body of `logLoop`: halve `rem` via right-shift by `1` and increment `idx`. -/
def logStep : Code .standard 22 := ram[
  rem ← rem >>> one;
  idx ← idx + one
]

/-- Loop computing `idx = Nat.log 2 n` from `rem = n` (`n ≥ 1`), `idx = 0`, `one = 1`. -/
def logLoop : Code .standard 22 := ram[
  while one < rem do [ ⟪logStep⟫ ]
]

/-- Setup for `highProbCode` on `n :: flattenMatrix W`: load `n = mem[1]`, compute
`numTrials = highProbTrials n = (n * (n - 1) / 2) * (Nat.log 2 n + 2)` using shifts and
multiplications, and set `srcBase = 2`. -/
def highProbSetup : Code .standard 22 := ram[
  one ← #1;
  nOrig ← *one;
  rem ← nOrig;
  idx ← #0;
  ⟪logLoop⟫;
  val2 ← #2;
  idx ← idx + val2;
  val1 ← nOrig - one;
  val1 ← nOrig * val1;
  val1 ← val1 >>> one;
  numTrials ← val1 * idx;
  srcBase ← #2
]

/-- Structured 22-register `O(n ^ 4 log n)` high-probability Karger program on
`n :: flattenMatrix W`. -/
def highProbCode : Code .standard 22 := ram[
  ⟪highProbSetup⟫;
  ⟪ampCore⟫
]

/-- Compiled 22-register `O(n ^ 4 log n)` high-probability Karger program. -/
def highProbProgram : Program .standard 22 :=
  highProbCode.program bestVal

/-- Worst-case instruction bound `33 * n ^ 4 * (Nat.log 2 n + 2)` for `highProbProgram`. -/
def highProbTime (n : ℕ) : ℕ :=
  33 * n ^ 4 * (Nat.log 2 n + 2)

theorem logLoop_exec {w n : ℕ} {x : Data 22} (hn : 1 ≤ n)
    (hone : x.regs one = 1) (hrem : x.regs rem = n) (hidx : x.regs idx = 0)
    (hnOrig : x.regs nOrig = n)
    (hn_fit : Fits w n) (hlg_fit : Fits w (Nat.log 2 n)) :
    ∃ y : Data 22, ExecWithin w logLoop x y (4 * Nat.log 2 n + 2) ∧
      y.mem = x.mem ∧
      y.regs one = 1 ∧
      y.regs nOrig = n ∧
      y.regs idx = Nat.log 2 n := by
  let I (y : Data 22) : Prop :=
    y.mem = x.mem ∧ y.regs one = 1 ∧ y.regs nOrig = n ∧
    1 ≤ y.regs rem ∧ y.regs rem ≤ n ∧
    y.regs idx + Nat.log 2 (y.regs rem) = Nat.log 2 n
  have hbody : ∀ y, I y → (Cond.lt one rem).Holds y →
      ∃ z, ExecWithin w logStep y z 2 ∧ I z ∧
        Nat.log 2 (z.regs rem) < Nat.log 2 (y.regs rem) := by
    intro y ⟨hym, hy1, hyn, hyr_ge, hyr_le, hy_sum⟩ hc
    have hgt1 : 1 < y.regs rem := by simpa [Cond.holds_lt, hy1] using hc
    have hshr_eq : y.regs rem >>> 1 = y.regs rem / 2 := by
      rw [Nat.shiftRight_eq_div_pow, pow_one]
    have hlog_step : Nat.log 2 (y.regs rem) = Nat.log 2 (y.regs rem / 2) + 1 :=
      Nat.log_of_one_lt_of_le (by decide) (by omega)
    have hdiv_fit : Fits w (y.regs rem / 2) := hn_fit.of_le (by omega)
    have hidx1_fit : Fits w (y.regs idx + 1) := hlg_fit.of_le (by omega)
    let z₁ := y.set rem (y.regs rem / 2)
    let z₂ := z₁.set idx (y.regs idx + 1)
    have e1 : ExecWithin w ram[rem ← rem >>> one] y z₁ 1 := by
      simpa [z₁, BinOp.eval, hy1, hshr_eq] using
        ExecWithin.bin (f := .shiftRight) (d := rem) (i := rem) (j := one) (x := y)
          (by simpa [BinOp.eval, hy1, hshr_eq] using hdiv_fit)
    have e2 : ExecWithin w ram[idx ← idx + one] z₁ z₂ 1 := by
      have hi' : z₁.regs idx = y.regs idx := by simp +decide [z₁]
      have ho' : z₁.regs one = 1 := by simpa +decide [z₁, Function.update_apply] using hy1
      simpa [z₂, BinOp.eval, hi', ho'] using
        ExecWithin.bin (f := .add) (d := idx) (i := idx) (j := one) (x := z₁)
          (by simpa [BinOp.eval, hi', ho'] using hidx1_fit)
    refine ⟨z₂, e1.seq e2, ?_, ?_⟩
    · refine ⟨hym,
        by simpa +decide [z₂, z₁, Function.update_apply] using hy1,
        by simpa +decide [z₂, z₁, Function.update_apply] using hyn,
        by simp +decide [z₂, z₁]; omega,
        by simp +decide [z₂, z₁]; omega,
        ?_⟩
      simp +decide only [z₂, z₁, Data.set_regs, Function.update_apply, ↓reduceIte]
      omega
    · simp +decide only [z₂, z₁, Data.set_regs, Function.update_apply, ↓reduceIte]
      omega
  have hx : I x := ⟨rfl, hone, hnOrig, by omega, hrem.le, by rw [hidx, hrem, zero_add]⟩
  obtain ⟨y, he, ⟨hym, hy1, hyn, hyr_ge, _, hy_sum⟩, hnc⟩ :=
    ExecWithin.loop_invariant I (fun y => Nat.log 2 (y.regs rem)) hbody hx
  have hyr_eq1 : y.regs rem = 1 := by
    have : ¬(1 < y.regs rem) := by simpa [Cond.holds_lt, hy1] using hnc
    omega
  have hy_idx : y.regs idx = Nat.log 2 n := by
    rw [hyr_eq1, Nat.log_one_right, add_zero] at hy_sum
    exact hy_sum
  refine ⟨y, ?_, hym, hy1, hyn, hy_idx⟩
  exact he.mono (by rw [hrem]; omega)

theorem highProbSetup_exec {w n : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hw : logWidth 3 n ≤ w) :
    ∃ y : Data 22,
      ExecWithin w highProbSetup (Data.init (n :: flattenMatrix W)) y (4 * Nat.log 2 n + 13) ∧
      y.mem = (Data.init (r := 22) (n :: flattenMatrix W)).mem ∧
      y.regs srcBase = 2 ∧
      y.regs nOrig = n ∧
      y.regs numTrials = highProbTrials n := by
  have hws := fits_workspace_of_logWidth_three hn hw
  have hhp_fit := fits_highProbTrials_of_logWidth_three hn hw
  have h1 : Fits w 1 := hws.of_le (by omega)
  have h2 : Fits w 2 := hws.of_le (by omega)
  have hn_fit : Fits w n := hws.of_le (by omega)
  have hn1_fit : Fits w (n - 1) := hws.of_le (by omega)
  have hmul_fit : Fits w (n * (n - 1)) :=
    hws.of_le (by have := Nat.mul_le_mul_left n (Nat.sub_le n 1); omega)
  have hhalf_fit : Fits w (n * (n - 1) / 2) := hmul_fit.of_le (Nat.div_le_self _ _)
  have hlog_lt : Nat.log 2 n < n := Nat.log_lt_self 2 (by omega)
  have hlg_fit : Fits w (Nat.log 2 n) := hws.of_le (by omega)
  have hlg2_fit : Fits w (Nat.log 2 n + 2) := hws.of_le (by omega)
  let x₀ : Data 22 := Data.init (n :: flattenMatrix W)
  have hm1 : x₀.mem 1 = n := rfl
  let s₁ := x₀.set one 1
  let s₂ := s₁.set nOrig n
  let s₃ := s₂.set rem n
  let s₄ := s₃.set idx 0
  have e1 : Exec (B := .standard) w ram[one ← #1] x₀ s₁ 1 := Exec.const h1
  have e2 : Exec (B := .standard) w ram[nOrig ← *one] s₁ s₂ 1 := by
    have hr : s₁.regs one = 1 := by simp [s₁]
    simpa [s₂, s₁, hr, hm1] using
      Exec.load (B := .standard) (w := w) (d := nOrig) (a := one) (x := s₁)
  have e3 : Exec (B := .standard) w ram[rem ← nOrig] s₂ s₃ 1 := by
    have hr : s₂.regs nOrig = n := by simp [s₂]
    simpa [s₃, hr] using Exec.copy (B := .standard) (w := w) (d := rem) (s := nOrig) (x := s₂)
  have e4 : Exec (B := .standard) w ram[idx ← #0] s₃ s₄ 1 := Exec.const (fits_zero w)
  obtain ⟨s₅, e_loop, hm5, ho5, hn5, hidx5⟩ :=
    logLoop_exec (x := s₄) (by omega)
      (by simp +decide [s₄, s₃, s₂, s₁])
      (by simp +decide [s₄, s₃])
      (by simp [s₄])
      (by simp +decide [s₄, s₃, s₂])
      hn_fit hlg_fit
  let t₁ := s₅.set val2 2
  let t₂ := t₁.set idx (Nat.log 2 n + 2)
  let t₃ := t₂.set val1 (n - 1)
  let t₄ := t₃.set val1 (n * (n - 1))
  let t₅ := t₄.set val1 (n * (n - 1) / 2)
  let t₆ := t₅.set numTrials (highProbTrials n)
  let t₇ := t₆.set srcBase 2
  have p1 : Exec (B := .standard) w ram[val2 ← #2] s₅ t₁ 1 := Exec.const h2
  have p2 : Exec w ram[idx ← idx + val2] t₁ t₂ 1 := by
    have hi : t₁.regs idx = Nat.log 2 n := by simpa +decide [t₁, Function.update_apply] using hidx5
    have hv2 : t₁.regs val2 = 2 := by simp [t₁]
    simpa [t₂, BinOp.eval, hi, hv2] using
      Exec.bin (w := w) (f := .add) (d := idx) (i := idx) (j := val2) (x := t₁)
        (by simpa [BinOp.eval, hi, hv2] using hlg2_fit)
  have p3 : Exec w ram[val1 ← nOrig - one] t₂ t₃ 1 := by
    have hno : t₂.regs nOrig = n := by simpa +decide [t₂, t₁, Function.update_apply] using hn5
    have ho : t₂.regs one = 1 := by simpa +decide [t₂, t₁, Function.update_apply] using ho5
    simpa [t₃, BinOp.eval, hno, ho] using
      Exec.bin (w := w) (f := .sub) (d := val1) (i := nOrig) (j := one) (x := t₂)
        (by simpa [BinOp.eval, hno, ho] using hn1_fit)
  have p4 : Exec w ram[val1 ← nOrig * val1] t₃ t₄ 1 := by
    have hno : t₃.regs nOrig = n := by simpa +decide [t₃, t₂, t₁, Function.update_apply] using hn5
    have hv1 : t₃.regs val1 = n - 1 := by simp [t₃]
    simpa [t₄, BinOp.eval, hno, hv1] using
      Exec.bin (w := w) (f := .mul) (d := val1) (i := nOrig) (j := val1) (x := t₃)
        (by simpa [BinOp.eval, hno, hv1] using hmul_fit)
  have p5 : Exec w ram[val1 ← val1 >>> one] t₄ t₅ 1 := by
    have hv1 : t₄.regs val1 = n * (n - 1) := by simp [t₄]
    have ho : t₄.regs one = 1 := by
      simpa +decide [t₄, t₃, t₂, t₁, Function.update_apply] using ho5
    have hshr : (n * (n - 1)) >>> 1 = n * (n - 1) / 2 := by
      rw [Nat.shiftRight_eq_div_pow, pow_one]
    simpa [t₅, BinOp.eval, hv1, ho, hshr] using
      Exec.bin (w := w) (f := .shiftRight) (d := val1) (i := val1) (j := one) (x := t₄)
        (by simpa [BinOp.eval, hv1, ho, hshr] using hhalf_fit)
  have p6 : Exec w ram[numTrials ← val1 * idx] t₅ t₆ 1 := by
    have hv1 : t₅.regs val1 = n * (n - 1) / 2 := by simp [t₅]
    have hi : t₅.regs idx = Nat.log 2 n + 2 := by simp +decide [t₅, t₄, t₃, t₂]
    simpa [t₆, BinOp.eval, hv1, hi, highProbTrials] using
      Exec.bin (w := w) (f := .mul) (d := numTrials) (i := val1) (j := idx) (x := t₅)
        (by simpa [BinOp.eval, hv1, hi, highProbTrials] using hhp_fit)
  have p7 : Exec (B := .standard) w ram[srcBase ← #2] t₆ t₇ 1 := Exec.const h2
  refine ⟨t₇, ?_, hm5, by simp [t₇],
    by simpa +decide [t₇, t₆, t₅, t₄, t₃, t₂, t₁, Function.update_apply] using hn5,
    by simp +decide [t₇, t₆]⟩
  unfold highProbSetup
  exact ((e1.within).seq ((e2.within).seq ((e3.within).seq ((e4.within).seq
    (e_loop.seq ((p1.within).seq ((p2.within).seq ((p3.within).seq
      ((p4.within).seq ((p5.within).seq ((p6.within).seq p7.within))))))))))).mono (by omega)

private theorem highProbTime_bound {n : ℕ} (hn : 2 ≤ n) :
    (4 * Nat.log 2 n + 13) + (highProbTrials n * (50 * n ^ 2 + 12 * n + 30) + 8) + 1 ≤
      highProbTime n := by
  unfold highProbTime highProbTrials
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by omega⟩
  have h1 : 50 * (d + 2) ^ 2 + 12 * (d + 2) + 30 ≤ 64 * (d + 2) ^ 2 := by nlinarith
  have h2 : ((d + 2) * (d + 2 - 1) / 2) * (64 * (d + 2) ^ 2) ≤ 32 * (d + 2) ^ 4 := by
    have hdiv : 2 * ((d + 2) * (d + 2 - 1) / 2) ≤ (d + 2) * (d + 1) := by
      have hsub : d + 2 - 1 = d + 1 := by omega
      rw [hsub]
      omega
    nlinarith
  have htrial : (((d + 2) * (d + 2 - 1) / 2) * (Nat.log 2 (d + 2) + 2)) *
      (50 * (d + 2) ^ 2 + 12 * (d + 2) + 30) ≤
      32 * (d + 2) ^ 4 * (Nat.log 2 (d + 2) + 2) := by
    calc
      (((d + 2) * (d + 2 - 1) / 2) * (Nat.log 2 (d + 2) + 2)) *
          (50 * (d + 2) ^ 2 + 12 * (d + 2) + 30)
        ≤ (((d + 2) * (d + 2 - 1) / 2) * (Nat.log 2 (d + 2) + 2)) * (64 * (d + 2) ^ 2) :=
          Nat.mul_le_mul_left _ h1
      _ = (((d + 2) * (d + 2 - 1) / 2) * (64 * (d + 2) ^ 2)) * (Nat.log 2 (d + 2) + 2) := by ring
      _ ≤ (32 * (d + 2) ^ 4) * (Nat.log 2 (d + 2) + 2) := Nat.mul_le_mul_right _ h2
  have hoverhead : 4 * Nat.log 2 (d + 2) + 22 ≤ 1 * (d + 2) ^ 4 * (Nat.log 2 (d + 2) + 2) := by
    have hpow4 : 16 ≤ (d + 2) ^ 4 := by nlinarith
    nlinarith
  calc
    (4 * Nat.log 2 (d + 2) + 13) +
        (((d + 2) * (d + 2 - 1) / 2 * (Nat.log 2 (d + 2) + 2)) *
          (50 * (d + 2) ^ 2 + 12 * (d + 2) + 30) + 8) + 1
      = (4 * Nat.log 2 (d + 2) + 22) +
          (((d + 2) * (d + 2 - 1) / 2 * (Nat.log 2 (d + 2) + 2)) *
            (50 * (d + 2) ^ 2 + 12 * (d + 2) + 30)) := by ring
    _ ≤ 1 * (d + 2) ^ 4 * (Nat.log 2 (d + 2) + 2) +
          32 * (d + 2) ^ 4 * (Nat.log 2 (d + 2) + 2) := Nat.add_le_add hoverhead htrial
    _ = 33 * (d + 2) ^ 4 * (Nat.log 2 (d + 2) + 2) := by ring

/-- Structured `ProbComp` specification of `highProbCode`. -/
theorem highProbCode_spec {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    ∃ m : ProbComp (Data 22 × ℕ),
      ExecRand w highProbCode (Data.init (n :: flattenMatrix W)) m ∧
      m.IsQueryBounded (highProbTrials n * (n - 2)) ∧
      (∀ z ∈ m.support,
        z.2 + 1 ≤ highProbTime n ∧
        Modifies (Finset.Ico (2 + n * n) (2 + 2 * (n * n) + n))
          (Data.init (r := 22) (n :: flattenMatrix W)).mem z.1.mem ∧
        ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ z.1.regs bestVal = cutWeight W C) ∧
      (0 < minCut W →
        m.eval.toOuterMeasure {z | z.1.regs bestVal ≠ minCut W} ≤
          (1 : ℝ≥0∞) / ((2 * n : ℕ) : ℝ≥0∞)) := by
  have hws := fits_workspace_of_logWidth_three hn hw
  have h1 : Fits w 1 := hws.of_le (by omega)
  have hdEnd : Fits w (2 + 2 * (n * n) + n) := hws.of_le (by omega)
  have hhp_fit := fits_highProbTrials_of_logWidth_three hn hw
  obtain ⟨y_s, ⟨n_s, hn_s, e_s⟩, hm_s, hsb_s, hn_s_r, hnt_s⟩ :=
    highProbSetup_exec (W := W) hn hw
  obtain ⟨m_c, hm_c, hq_c, hsup_c, hfail_c⟩ :=
    ampCore_spec (highProbTrials_pos hn) hn hW hsb_s hn_s_r hnt_s h1 hdEnd hhp_fit htot
      (hm_s ▸ holdsMatrix_init_single W)
  have hbound := highProbTime_bound hn
  refine ⟨_, e_s.seqRand hm_c, ?_, ?_, ?_⟩
  · simp only [OracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
    exact hq_c
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    rcases hsup_c z₀ hz₀ with ⟨ht₀, hmod₀, hcut₀⟩
    exact ⟨by omega, hm_s ▸ hmod₀, hcut₀⟩
  · intro hmin_pos
    rw [ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    exact (hfail_c hmin_pos).trans (highProb_failure_le hn)

/-- **Explicit `O(n ^ 4 log n)` high-probability global minimum cut (`highProbProgram`).**
At word size `w ≥ logWidth 3 n` when `2 ≤ n` and `totalDoubledWeight W < 2 ^ w`:
1. `highProbProgram` halts within `highProbTime n = 33 * n ^ 4 * (Nat.log 2 n + 2)` steps;
2. executes at most `highProbTrials n * (n - 2)` `rand` calls;
3. on every supported branch, outputs `cutWeight W C ≥ minCut W` for a genuine non-trivial cut `C`
   of `W` while modifying memory only in `[2 + n * n, 2 + 2 * (n * n) + n)`;
4. when `0 < minCut W` (excluded only for proof convenience; `S = 0` contraction still halts
   fault-free with a valid cut weight), misses `minCut W` with probability at most `1 / (2 * n)`. -/
theorem highProbProgram_spec {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    let input := n :: flattenMatrix W
    RandHaltsWithin w highProbProgram (.init input) (highProbTime n) ∧
    RandCallsBounded w highProbProgram (.init input) (highProbTime n)
      (highProbTrials n * (n - 2)) ∧
    (∀ cfg ∈ (runRand w highProbProgram (highProbTime n) (.running (.init input))).support,
      ∃ (y : Data 22) (C : Finset (Fin n)),
        cfg = .halted (cutWeight W C) y ∧
        y.Bounded w ∧
        IsNonTrivialCut C ∧
        minCut W ≤ cutWeight W C ∧
        Modifies (Finset.Ico (2 + n * n) (2 + 2 * (n * n) + n))
          (Data.init (r := 22) input).mem y.mem) ∧
    (0 < minCut W →
      (evalRand w highProbProgram (highProbTime n) (.init input)).toOuterMeasure
          {cfg | ∀ y, cfg ≠ .halted (minCut W) y} ≤
        (1 : ℝ≥0∞) / ((2 * n : ℕ) : ℝ≥0∞)) := by
  intro input
  have hfit_in : InputFits w input := inputFits_single hn hw htot
  obtain ⟨m, hm, hq, hsup, hfail⟩ := highProbCode_spec hn hW hw htot
  have hrun : runRand w highProbProgram (highProbTime n) (.running (.init input)) =
      (fun z : Data 22 × ℕ => RandCfg.halted (z.1.regs bestVal) z.1) <$> m :=
    hm.runRand_program bestVal fun z hz => (hsup z hz).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cfg hcfg
    rw [hrun] at hcfg
    obtain ⟨z, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hcfg
    exact ⟨z.1.regs bestVal, z.1, rfl⟩
  · rw [RandCallsBounded, hrun]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr hq
  · intro cfg hcfg
    have hbnd := runRand_bounded_init hfit_in hcfg
    rw [hrun] at hcfg
    obtain ⟨z, hz, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hcfg
    rcases hsup z hz with ⟨_, hmod, C, hC_nt, hbv⟩
    exact ⟨z.1, C, by rw [hbv], hbnd.2, hC_nt, minCut_le_cutWeight W hC_nt, hmod⟩
  · intro hmin_pos
    rw [evalRand, hrun, ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    refine (PMF.toOuterMeasure_mono _ ?_).trans (hfail hmin_pos)
    intro z hz heq
    exact hz.1 z.1 (congrArg (fun v => RandCfg.halted v z.1) heq)

/-- Corollary of `highProbProgram_spec`: when `0 < minCut W`, `highProbProgram` misses `minCut W`
with probability at most `1 / n`. -/
theorem highProbProgram_failure_le_inv_n {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (htot : Fits w (totalDoubledWeight W))
    (hpos : 0 < minCut W) :
    (evalRand w highProbProgram (highProbTime n) (.init (n :: flattenMatrix W))).toOuterMeasure
        {cfg | ∀ y, cfg ≠ .halted (minCut W) y} ≤
      (1 : ℝ≥0∞) / (n : ℝ≥0∞) := by
  refine ((highProbProgram_spec hn hW hw htot).2.2.2 hpos).trans ?_
  apply ENNReal.div_le_div_left
  exact_mod_cast (by omega : n ≤ 2 * n)

end HighProb

end Cslib.Algorithms.WordRAM.Karger

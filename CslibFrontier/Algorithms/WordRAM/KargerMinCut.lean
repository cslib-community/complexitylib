/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.Call
public import CslibFrontier.Init
public import CslibFrontier.Algorithms.WordRAM.Karger.Graph
public import CslibFrontier.Algorithms.WordRAM.Karger.Contract
public import CslibFrontier.Algorithms.WordRAM.Karger.OutputLaw
public import CslibFrontier.Computability.WordRAM.Copy
public import CslibFrontier.Computability.WordRAM.Time

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

No probability is proved on machine states. Each program simulates a client of
`Cslib.Algorithms.Lean.Karger`: the word it outputs has the law of the answer of
`Cslib.Algorithms.Lean.Karger.karger` (`singleCode_law`), or of the amplification client
`Cslib.Algorithms.Lean.Karger.minRuns` run against independent runs of `karger`
(`amplifiedCode_law`, `highProbCode_law`). Each trial contracts as the client does
(`contractDownTo_law`) and reads half the total weight of the two supervertices left
(`ContractState.mem_add_one`), and the loop of trials keeps the least answer as `minRuns` does
(`ampTrialBody_law`, `ampLoop_law`). The success and failure bounds and the cut realization are the
specification's (`Cslib.Algorithms.Lean.Karger.two_div_le_toOuterMeasure_karger`,
`Cslib.Algorithms.Lean.Karger.minRuns_ne_minCut_le`,
`Cslib.Algorithms.Lean.Karger.exists_cut_of_mem_support_answerLaw`,
`Cslib.Algorithms.Lean.Karger.mem_support_minRuns`), carried through those laws.

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

* `Cslib.Algorithms.WordRAM.Karger.singleCode_law`,
  `Cslib.Algorithms.WordRAM.Karger.amplifiedCode_law`,
  `Cslib.Algorithms.WordRAM.Karger.highProbCode_law`: each program's output has the law of the
  output of `karger` or of amplified `karger`, within its instruction and `rand`-call bounds.
* `Cslib.Algorithms.WordRAM.Karger.ampTrialBody_law`, `Cslib.Algorithms.WordRAM.Karger.ampLoop_law`,
  `Cslib.Algorithms.WordRAM.Karger.ampCore_law`: one trial, the loop of trials and the
  amplification core.
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
open Cslib.WeightedCut
open Cslib.Probability.PMF
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
    InputFits w (n :: flattenMatrix W) :=
  inputFits_cons_flattenMatrix (fits_workspace_of_logWidth_three hn hw) (by omega) (by omega) htot

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

/-- **A single trial runs `karger`.** At word size `w ≥ logWidth 3 n` with
`totalDoubledWeight W < 2 ^ w`, `singleCode` on `n :: flattenMatrix W` runs within
`singleTime n - 1` instructions and `n - 2` `rand` calls and writes only `[2, 2 + n * n + n)`. The
weight it leaves in `val1` has the law of the answer of `Lean.Karger.karger` on `⟨n, W⟩`:
`contractDownTo` contracts as the client does (`contractDownTo_law`), and `singlePost` reads the
weight between the last two supervertices, half their total weight. -/
theorem singleCode_law {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    ExecRandLaw w singleCode (Data.init (n :: flattenMatrix W))
      (fun y => Modifies (Finset.Ico 2 (2 + n * n + n))
        (Data.init (r := 16) (n :: flattenMatrix W)).mem y.mem)
      (42 * n ^ 2 + 12 * n + 20) (n - 2) (fun y => y.regs val1)
      (Lean.Karger.answerLaw ⟨n, W⟩) := by
  have hws_fit := fits_workspace_of_logWidth_three hn hw
  have h1 : Fits w 1 := hws_fit.of_le (by omega)
  have hwEnd : Fits w (2 + n * n) := hws_fit.of_le (by omega)
  have hdEnd : Fits w (2 + n * n + n) := hws_fit.of_le (by omega)
  have hwb1 : Fits w (2 + 1) := hws_fit.of_le (by omega)
  obtain ⟨y_setup, e_setup, hmem_setup, hwb_s, hdb_s, hstr_s, hk_s, ht_s⟩ :=
    singleSetup_exec (W := W) hn hw
  obtain ⟨y_deg, e_deg, hws_deg, hmod_deg, _, _, hwb_d, hdb_d, hstr_d, hk_d, ht_d, htot_d⟩ :=
    computeDegreesAndTotal_exec (w := w) (W := W) (x := y_setup)
      hwb_s hdb_s hstr_s hk_s (le_refl n) (Or.inl (le_refl _)) h1 hwEnd hdEnd htot
      (hmem_setup ▸ holdsMatrix_init_single W)
  rw [ht_s] at ht_d
  have hst_deg : ContractState w 2 (2 + n * n) n n 2 W y_deg :=
    ⟨hwb_d, hdb_d, hstr_d, hk_d, ht_d, htot_d, le_refl n, Or.inl (le_refl _),
      hwEnd, hdEnd, htot, hws_deg⟩
  have hsub : workspaceFootprint 2 (2 + n * n) n n ⊆ Finset.Ico 2 (2 + n * n + n) := by
    intro a ha
    simp only [workspaceFootprint, Finset.mem_union, Finset.mem_Ico] at ha ⊢
    omega
  have hrun := ExecRandLaw.seq (contractDownTo_law (le_refl 2) hn hW hst_deg)
    (κ := fun G => PMF.pure (totalDoubledWeight G.weight / 2)) fun y ⟨hmod_c, W', hW', hst'⟩ => by
      obtain ⟨y_p, e_p, hmem_p, hv_p⟩ := singlePost_exec hst'.regs_wBase h1 hwb1
      have hmod : Modifies (Finset.Ico 2 (2 + n * n + n))
          (Data.init (r := 16) (n :: flattenMatrix W)).mem y_p.mem := by
        rw [hmem_p]
        exact modifies_trans_subset (hmem_setup ▸ hmod_deg) hmod_c
          (Finset.Ico_subset_Ico (by omega) le_rfl) hsub
      exact (ExecRandLaw.of_execWithin (f := fun y => y.regs val1) e_p.within hmod).congr_law
        (by rw [hv_p, hst'.mem_add_one hW'])
  have hcode_eq : singleCode =
      .seq singleSetup (.seq computeDegreesAndTotal (.seq contractDownTo singlePost)) := rfl
  rw [hcode_eq]
  refine ((ExecRandLaw.seq_det e_setup.within (ExecRandLaw.seq_det e_deg hrun)).congr_law ?_).mono
    (fun _ h => h) (by omega) (by omega)
  rw [Lean.Karger.answerLaw_eq]
  exact PMF.bind_pure_comp _ _

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
  obtain ⟨hhalt, hcalls, hpost, hhit, -⟩ := program_of_law (T' := singleTime n)
    (singleCode_law hn hW hw htot) (by unfold singleTime; omega) (inputFits_single hn hw htot)
    fun _ hv => Lean.Karger.exists_cut_of_mem_support_answerLaw hn hW hv
  refine ⟨hhalt, hcalls, hpost, fun hmin => le_trans ?_ hhit⟩
  rw [Lean.Karger.answerLaw, PMF.toOuterMeasure_map_apply]
  exact Lean.Karger.two_div_le_toOuterMeasure_karger hn hW hmin

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
  obtain ⟨y, hy_exec, ⟨hy_mem, hy_src, hy_dst, hy_len⟩, hnot_in⟩ :=
    ExecWithin.rename_post copyRegMap_injective
      (ArrayCopy.exec (x.comap copyRegMap) h1 hs_fit hd_fit hdisj')
  have ht_eq : 7 * (x.comap copyRegMap).regs ArrayCopy.len + 4 = 7 * (n * n) + 4 := by
    change 7 * x.regs matLen + 4 = 7 * (n * n) + 4
    rw [hlen]
  rw [ht_eq] at hy_exec
  have hymem : y.mem = ArrayCopy.copyPrefix x.mem sb wb (n * n) := by
    have h₀ : y.mem = ArrayCopy.copyPrefix x.mem (x.regs srcBase) (x.regs wBase)
        (x.regs matLen) := hy_mem
    rwa [hsb, hwb, hlen] at h₀
  refine ⟨y, hy_exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · exact hy_dst.trans hwb
  · exact hnot_in dBase (by decide)
  · exact hy_src.trans hsb
  · exact hnot_in nOrig (by decide)
  · exact hy_len.trans hlen
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

/-- **One trial runs `karger`.** From `AmpInv` at trial `i < R`, `ampTrialBody` runs within
`49 n² + 12 n + 27` instructions and `n - 2` `rand` calls and keeps the invariant at trial `i + 1`.
Its new `bestVal` has the law of the answer `v` of `Lean.Karger.karger` on `⟨n, W⟩`, taken as is on
the first trial and as `min v bestVal` after: `contractDownToAt` contracts the fresh copy of `W` as
the client does (`contractDownToAt_law`), and `ampTrialPost` reads the weight between the last two
supervertices, half their total weight. -/
theorem ampTrialBody_law {w sb n R i : ℕ} {W : Fin n → Fin n → ℕ} {mem₀ : ℕ → ℕ} {x : Data 22}
    (hn : 2 ≤ n) (hW : IsMultigraph W) (hiR : i < R)
    (h1 : Fits w 1) (hdEnd : Fits w (sb + 2 * (n * n) + n))
    (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W))
    (hinv : AmpInv w sb n R i W mem₀ x) :
    ExecRandLaw w ampTrialBody x (AmpInv w sb n R (i + 1) W mem₀) (49 * n ^ 2 + 12 * n + 27)
      (n - 2) (fun y => y.regs bestVal)
      ((Lean.Karger.answerLaw ⟨n, W⟩).map fun v =>
        if i = 0 then v else min v (x.regs bestVal)) := by
  let wb := sb + n * n
  let db := sb + 2 * (n * n)
  have hwEnd : Fits w (wb + n * n) := hdEnd.of_le (by omega)
  have h2_fit : Fits w 2 := hdEnd.of_le (by omega)
  have hwb1_fit : Fits w (wb + 1) := hdEnd.of_le (by omega)
  obtain ⟨y_cp, e_cp, hmat_cp, hmod_cp,
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
  obtain ⟨y_deg, e_deg, hws_deg, hmod_deg,
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
  have hmod_deg' : Modifies (Finset.Ico wb (db + n)) x.mem y_deg.mem :=
    modifies_trans_subset hmod_cp hmod_deg (Finset.Ico_subset_Ico (le_refl _) (by omega))
      (Finset.Ico_subset_Ico (by omega) (le_refl _))
  have hs_c : workspaceFootprint wb db n n ⊆ Finset.Ico wb (db + n) := by
    intro a ha
    simp only [workspaceFootprint, Finset.mem_union, Finset.mem_Ico] at ha ⊢
    omega
  -- The contraction runs `karger` on the copy, then `ampTrialPost` updates `bestVal`.
  have hrun := ExecRandLaw.seq (contractDownToAt_law hr22 (le_refl 2) hn hW hst_deg)
    (κ := fun G => PMF.pure (if i = 0 then totalDoubledWeight G.weight / 2
      else min (totalDoubledWeight G.weight / 2) (x.regs bestVal)))
    fun y ⟨hmod_c, hy_hi, W', hW', hst'⟩ => by
      have hz_db : y.regs dBase = db := hst'.regs_dBase
      have hz_ti : y.regs trialIdx = i := (hy_hi trialIdx (by decide)).trans hy_deg_hi.2.2.2.2.1
      have hv : y.mem (wb + 1) = _ := hst'.mem_add_one hW'
      obtain ⟨y_p, e_p, hm_p, hsb_p, hwb_p, hdb_p, hn_p, hml_p, hnt_p, hti_p, hbv_p⟩ :=
        ampTrialPost_exec hst'.regs_wBase hz_ti hiR h1 hwb1_fit hR_fit
      have hmod : Modifies (Finset.Ico wb (db + n)) x.mem y_p.mem := by
        rw [hm_p]
        exact modifies_trans_subset hmod_deg' hmod_c Finset.Subset.rfl hs_c
      refine (ExecRandLaw.of_execWithin (P := AmpInv w sb n R (i + 1) W mem₀)
        (f := fun y => y.regs bestVal) e_p ⟨?_, hwb_p, hdb_p.trans hz_db, ?_, ?_, ?_, hti_p,
        fun a b => ?_, modifies_trans_subset hinv.modifies_ws hmod Finset.Subset.rfl
          Finset.Subset.rfl⟩).congr_law ?_
      · exact hsb_p.trans ((hy_hi srcBase (by decide)).trans hy_deg_hi.1)
      · exact hn_p.trans ((hy_hi nOrig (by decide)).trans hy_deg_hi.2.1)
      · exact hml_p.trans ((hy_hi matLen (by decide)).trans hy_deg_hi.2.2.1)
      · exact hnt_p.trans ((hy_hi numTrials (by decide)).trans hy_deg_hi.2.2.2.1)
      · have hlt := matAddr_lt_end (wb := sb) (le_refl n) a b
        rw [hmod _ (by rw [Finset.mem_Ico]; omega)]
        exact hinv.src_matrix a b
      · rw [hbv_p, (hy_hi bestVal (by decide)).trans hy_deg_hi.2.2.2.2.2, hv]
  have hbody_eq : ampTrialBody = .seq copyMatrixCode
      (.seq ram[activeK ← nOrig] (.seq ram[stride ← nOrig]
        (.seq ram[targetT ← #2] (.seq (computeDegreesAndTotalAt hr22)
          (.seq (contractDownToAt hr22) ampTrialPost))))) := rfl
  rw [hbody_eq]
  refine ((ExecRandLaw.seq_det e_cp (ExecRandLaw.seq_det ec1.within
    (ExecRandLaw.seq_det ec2.within (ExecRandLaw.seq_det ec3.within
      (ExecRandLaw.seq_det e_deg hrun))))).congr_law ?_).mono (fun _ h => h) ?_ (by omega)
  · rw [Lean.Karger.answerLaw_eq, PMF.map_comp]
    exact PMF.bind_pure_comp _ _
  · have hnn : n * n = n ^ 2 := (sq n).symm
    omega

/-- **The loop of trials runs amplified Karger.** From `AmpInv` at trial `i`, with `rem = R - i`
trials left, `ampLoop` runs within `rem (50 n² + 12 n + 30) + 2` instructions and `rem (n - 2)`
`rand` calls and ends at trial `R`. Its `bestVal` has the law of the amplification client run
against independent runs of `Lean.Karger.karger` on `⟨n, W⟩`: of `Lean.Karger.minRuns rem` on the
first trial, and of `rem` more `Lean.Karger.minStep`s from `bestVal` after. -/
theorem ampLoop_law {w sb n R : ℕ} {W : Fin n → Fin n → ℕ} {mem₀ : ℕ → ℕ}
    (hR : 1 ≤ R) (hn : 2 ≤ n) (hW : IsMultigraph W)
    (h1 : Fits w 1) (hdEnd : Fits w (sb + 2 * (n * n) + n))
    (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W)) :
    ∀ (rem i : ℕ) (x : Data 22), i + rem = R → AmpInv w sb n R i W mem₀ x →
      ExecRandLaw w ampLoop x (AmpInv w sb n R R W mem₀)
        (rem * (50 * n ^ 2 + 12 * n + 30) + 2) (rem * (n - 2)) (fun y => y.regs bestVal)
        (OracleComp.evalWith (fun _ => Lean.Karger.answerLaw ⟨n, W⟩)
          (if i = 0 then Lean.Karger.minRuns rem
            else OracleComp.iterate rem Lean.Karger.minStep (x.regs bestVal))) := by
  intro rem
  induction rem with
  | zero =>
    intro i x hiR hinv
    obtain rfl : i = R := by omega
    have hc : ¬(Cond.lt trialIdx numTrials).Holds x := by
      simp [Cond.holds_lt, hinv.regs_trialIdx, hinv.regs_numTrials]
    rw [ite_eq_right (by omega)]
    exact (ExecRandLaw.loop_exit hc hinv).mono (fun _ h => h) (by omega) (Nat.zero_le _)
  | succ rem ih =>
    intro i x hiR hinv
    have hc : (Cond.lt trialIdx numTrials).Holds x := by
      simp [Cond.holds_lt, hinv.regs_trialIdx, hinv.regs_numTrials]
      omega
    refine ((ExecRandLaw.loop_iter hc (ampTrialBody_law hn hW (by omega) h1 hdEnd hR_fit htot hinv)
      (κ := fun b => OracleComp.evalWith (fun _ => Lean.Karger.answerLaw ⟨n, W⟩)
        (OracleComp.iterate rem Lean.Karger.minStep b)) fun y hy => by
          have h := ih (i + 1) y (by omega) hy
          rw [ite_eq_right (Nat.succ_ne_zero i)] at h
          exact h).congr_law ?_).mono (fun _ h => h) (by rw [add_one_mul]; omega)
      (by rw [add_one_mul]; omega)
    by_cases hi : i = 0
    · simp [hi, Lean.Karger.minRuns, Function.comp_def]
    · simp [hi, OracleComp.iterate_succ_bind, Lean.Karger.minStep, Function.comp_def]

/-- **The amplification core runs amplified Karger.** For `1 ≤ R` trials, from a state with
`srcBase = sb`, `nOrig = n`, `numTrials = R` and `HoldsMatrix x.mem sb n W`, `ampCore` runs within
`R (50 n² + 12 n + 30) + 8` instructions and `R (n - 2)` `rand` calls and writes only the
workspace. Its `bestVal` has the law of `Lean.Karger.minRuns R` against independent runs of
`Lean.Karger.karger` on `⟨n, W⟩`. -/
theorem ampCore_law {w sb n R : ℕ} {W : Fin n → Fin n → ℕ} {x : Data 22}
    (hR : 1 ≤ R) (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hsb : x.regs srcBase = sb) (hnOrig : x.regs nOrig = n) (hnumT : x.regs numTrials = R)
    (h1 : Fits w 1) (hdEnd : Fits w (sb + 2 * (n * n) + n))
    (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W))
    (hsrc_mat : HoldsMatrix x.mem sb n W) :
    ExecRandLaw w ampCore x
      (fun y => Modifies (Finset.Ico (sb + n * n) (sb + 2 * (n * n) + n)) x.mem y.mem)
      (R * (50 * n ^ 2 + 12 * n + 30) + 8) (R * (n - 2)) (fun y => y.regs bestVal)
      (OracleComp.evalWith (fun _ => Lean.Karger.answerLaw ⟨n, W⟩) (Lean.Karger.minRuns R)) := by
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
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hsrc_mat, Modifies.refl _ _⟩
    · simpa +decide [s₆, s₅, s₄, s₃, s₂, s₁, Function.update_apply] using hsb
    · simp +decide [s₆, s₅, s₄, s₃]
    · simp +decide [s₆, s₅, s₄]
    · simpa +decide [s₆, s₅, s₄, s₃, s₂, s₁, Function.update_apply] using hnOrig
    · simp +decide [s₆, s₅, s₄, s₃, s₂]
    · simpa +decide [s₆, s₅, s₄, s₃, s₂, s₁, Function.update_apply] using hnumT
    · simp +decide [s₆, s₅]
  have hloop := ampLoop_law (mem₀ := x.mem) hR hn hW h1 hdEnd hR_fit htot R 0 s₆
    (Nat.zero_add R) hinv₀
  rw [ite_eq_left rfl] at hloop
  have hcore_eq : ampCore = .seq ram[val1 ← nOrig * nOrig]
      (.seq ram[matLen ← val1] (.seq ram[wBase ← srcBase + matLen]
        (.seq ram[dBase ← wBase + matLen] (.seq ram[trialIdx ← #0]
          (.seq ram[bestVal ← #0] ampLoop))))) := rfl
  rw [hcore_eq]
  exact (ExecRandLaw.seq_det e1.within (ExecRandLaw.seq_det e2.within
    (ExecRandLaw.seq_det e3.within (ExecRandLaw.seq_det e4.within (ExecRandLaw.seq_det e5.within
      (ExecRandLaw.seq_det e6.within hloop)))))).mono (fun _ h => h.modifies_ws) (by omega) le_rfl

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

/-- **`amplifiedCode` runs amplified Karger.** At word size `w ≥ logWidth 3 n` with `1 ≤ R`,
`R < 2 ^ w` and `totalDoubledWeight W < 2 ^ w`, `amplifiedCode` on `R :: n :: flattenMatrix W` runs
within `amplifiedTime R n - 1` instructions and `R (n - 2)` `rand` calls and writes only
`[3 + n * n, 3 + 2 * (n * n) + n)`. Its `bestVal` has the law of `Lean.Karger.minRuns R` against
independent runs of `Lean.Karger.karger` on `⟨n, W⟩`. -/
theorem amplifiedCode_law {R n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hR : 1 ≤ R) (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W)) :
    ExecRandLaw w amplifiedCode (Data.init (R :: n :: flattenMatrix W))
      (fun y => Modifies (Finset.Ico (3 + n * n) (3 + 2 * (n * n) + n))
        (Data.init (r := 22) (R :: n :: flattenMatrix W)).mem y.mem)
      (R * (50 * n ^ 2 + 12 * n + 30) + 15) (R * (n - 2)) (fun y => y.regs bestVal)
      (OracleComp.evalWith (fun _ => Lean.Karger.answerLaw ⟨n, W⟩) (Lean.Karger.minRuns R)) := by
  have hws := fits_workspace_of_logWidth_three hn hw
  obtain ⟨y_s, e_s, hm_s, hsb_s, hn_s, hnt_s⟩ := amplifiedSetup_exec (R := R) (W := W) hn hw
  exact (ExecRandLaw.seq_det e_s.within (ampCore_law hR hn hW hsb_s hn_s hnt_s
    (hws.of_le (by omega)) hws hR_fit htot (hm_s ▸ holdsMatrix_init_amplified W))).mono
    (fun _ h => hm_s ▸ h) (by omega) le_rfl

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
  obtain ⟨hhalt, hcalls, hpost, -, hmiss⟩ :=
    program_of_law (T' := amplifiedTime R n) (amplifiedCode_law hR hn hW hw hR_fit htot)
      (by unfold amplifiedTime; omega)
      (inputFits_amplified hn hw hR_fit htot)
      fun _ hv => Lean.Karger.exists_cut_of_mem_support_answerLaw hn hW
        (Lean.Karger.mem_support_minRuns (by omega) hv)
  exact ⟨hhalt, hcalls, hpost, fun hmin =>
    hmiss.trans (Lean.Karger.minRuns_ne_minCut_le hn hW hmin R)⟩

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

/-- The setup's `4 log₂ n + 13` instructions, the `highProbTrials n` trials'
`highProbTrials n (50 n² + 12 n + 30) + 8` and the final halt fit in `highProbTime n`. -/
theorem highProbTime_bound {n : ℕ} (hn : 2 ≤ n) :
    4 * Nat.log 2 n + highProbTrials n * (50 * n ^ 2 + 12 * n + 30) + 22 ≤ highProbTime n := by
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
    4 * Nat.log 2 (d + 2) +
        ((d + 2) * (d + 2 - 1) / 2 * (Nat.log 2 (d + 2) + 2)) *
          (50 * (d + 2) ^ 2 + 12 * (d + 2) + 30) + 22
      = (4 * Nat.log 2 (d + 2) + 22) +
          (((d + 2) * (d + 2 - 1) / 2 * (Nat.log 2 (d + 2) + 2)) *
            (50 * (d + 2) ^ 2 + 12 * (d + 2) + 30)) := by ring
    _ ≤ 1 * (d + 2) ^ 4 * (Nat.log 2 (d + 2) + 2) +
          32 * (d + 2) ^ 4 * (Nat.log 2 (d + 2) + 2) := Nat.add_le_add hoverhead htrial
    _ = 33 * (d + 2) ^ 4 * (Nat.log 2 (d + 2) + 2) := by ring

/-- **`highProbCode` runs amplified Karger.** At word size `w ≥ logWidth 3 n` with
`totalDoubledWeight W < 2 ^ w`, `highProbCode` on `n :: flattenMatrix W` runs within
`4 log₂ n + highProbTrials n (50 n² + 12 n + 30) + 21` instructions and
`highProbTrials n (n - 2)` `rand` calls and writes only `[2 + n * n, 2 + 2 * (n * n) + n)`. Its
`bestVal` has the law of `Lean.Karger.minRuns (highProbTrials n)` against independent runs of
`Lean.Karger.karger` on `⟨n, W⟩`. -/
theorem highProbCode_law {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    ExecRandLaw w highProbCode (Data.init (n :: flattenMatrix W))
      (fun y => Modifies (Finset.Ico (2 + n * n) (2 + 2 * (n * n) + n))
        (Data.init (r := 22) (n :: flattenMatrix W)).mem y.mem)
      (4 * Nat.log 2 n + highProbTrials n * (50 * n ^ 2 + 12 * n + 30) + 21)
      (highProbTrials n * (n - 2)) (fun y => y.regs bestVal)
      (OracleComp.evalWith (fun _ => Lean.Karger.answerLaw ⟨n, W⟩)
        (Lean.Karger.minRuns (highProbTrials n))) := by
  have hws := fits_workspace_of_logWidth_three hn hw
  obtain ⟨y_s, e_s, hm_s, hsb_s, hn_s, hnt_s⟩ := highProbSetup_exec (W := W) hn hw
  exact (ExecRandLaw.seq_det e_s (ampCore_law (highProbTrials_pos hn) hn hW hsb_s hn_s hnt_s
    (hws.of_le (by omega)) (hws.of_le (by omega)) (fits_highProbTrials_of_logWidth_three hn hw)
    htot (hm_s ▸ holdsMatrix_init_single W))).mono (fun _ h => hm_s ▸ h) (by omega) le_rfl

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
  obtain ⟨hhalt, hcalls, hpost, -, hmiss⟩ :=
    program_of_law (highProbCode_law hn hW hw htot) (highProbTime_bound hn)
      (inputFits_single hn hw htot) fun _ hv =>
        Lean.Karger.exists_cut_of_mem_support_answerLaw hn hW
          (Lean.Karger.mem_support_minRuns (Nat.one_le_iff_ne_zero.mp (highProbTrials_pos hn)) hv)
  exact ⟨hhalt, hcalls, hpost, fun hmin =>
    (hmiss.trans (Lean.Karger.minRuns_ne_minCut_le hn hW hmin _)).trans (highProb_failure_le hn)⟩

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

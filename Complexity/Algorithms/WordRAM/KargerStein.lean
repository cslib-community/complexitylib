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
public import Complexity.Algorithms.WordRAM.Karger.FastCut
public import Complexity.Computability.WordRAM.Copy
public import Complexity.Computability.WordRAM.Randomized.LoopSegment
public import Complexity.Computability.WordRAM.Time
import Complexity.Languages.Probabilistic.Event

/-!
# Karger–Stein's recursive `FastCut` algorithm on the word RAM

Implements the Karger–Stein recursive randomized global minimum cut algorithm (`[KargerStein1996]`,
Section 4, Figure 6, Lemmas 4.1–4.3, and the minimum-cut-value part of Theorem 4.4; paraphrase) on
`n`-vertex weighted undirected
multigraphs (`n ≥ 2`, `IsMultigraph W`) over `Cslib.WordRAM.Basis.standard` using `r = 24`
registers and an explicit iterative frame stack in `O(n ^ 2)` scratch words (`≤ 26 * n ^ 2` stack
words plus `n ^ 2` input words, matching Section 4, Lemma 4.2), providing two machine-level
endpoints on `n :: flattenMatrix W`:

1. **Single-tree recursive contraction (`fastCutProgram`, `r = 24`, `[KargerStein1996]`, Section 4,
   Figure 6 and Lemmas 4.1–4.3; paraphrase):** contracts recursively from `k ≥ 7` down to the
   pure-integer threshold `t = fastCutThreshold k` (smallest `t ≥ 2` with `k * (k - 1) ≤ 2 * t *
   (t - 1)`, an integer deviation from Figure 6's `⌈k / √2 + 1⌉` that is never larger and is
   strictly smaller at e.g. `k = 8`, where `t = 6` vs `7`) along two independent branches, switches
   at `k ≤ 6` to a single contraction down to `2` supervertices (the source's base case: Figure 6's
   `Contract(G, 2)` with the size-7 cutoff of equation (2); a leaf keeps a fixed minimum cut with
   probability `≥ 2 / (k * (k - 1)) ≥ 1 / 15`, equation (2)'s base-case bound, which is where the
   `15` comes from), halts within `fastCutTime n = 2500 * n ^ 2 * (Nat.log 2 n + 2)`
   (`O(n ^ 2 log n)`) steps and `fastCutNodeQueries n ≤ 6 * n ^ 2` (`O(n ^ 2)`) `rand` calls with a
   genuine non-trivial cut weight `cutWeight W C ≥ minCut W` on every supported path, modifies only
   `[2 + n ^ 2, 2 + 27 * n ^ 2)`, and achieves `minCut W` with probability at least
   `1 / (Nat.log 2 n + 15)` whenever `0 < minCut W` (excluded only for proof convenience; when
   `minCut W = 0`, any non-trivial zero-weight cut is already optimal).
2. **Amplified high-probability global minimum cut (`fastCutHighProbProgram`, `r = 24`,
   `[KargerStein1996]`, Section 4, Theorem 4.4; paraphrase, the value part only: the source finds
   all minimum cuts in `O(m log(n ^ 2 / m))` space; we prove the returned value is `minCut W` except
   with probability `≤ 1 / (2 * n)`):** executes our concrete `O(log ^ 2 n)`
   trial schedule `fastCutTrials n = (Nat.log 2 n + 15) * (Nat.log 2 n + 2)` of independent
   `FastCut` trees reusing the same `[2 + n ^ 2, 2 + 27 * n ^ 2)` scratch arena, halts within
   `fastCutHighProbTime n = 2600 * n ^ 2 * (Nat.log 2 n + 15) * (Nat.log 2 n + 2) ^ 2`
   (`O(n ^ 2 log ^ 3 n)`) steps and `fastCutTrials n * (6 * n ^ 2)` `rand` calls with a genuine
   non-trivial cut weight `≥ minCut W`, and misses `minCut W` with probability at most
   `1 / (2 * n)` (hence at most `1 / n`) whenever `0 < minCut W` (excluded only for proof
   convenience).

## Main definitions

* `Cslib.Algorithms.WordRAM.Karger.fastCutCode`,
  `Cslib.Algorithms.WordRAM.Karger.fastCutProgram`,
  `Cslib.Algorithms.WordRAM.Karger.fastCutTime`: single-tree `O(n ^ 2 log n)` Karger–Stein
  `FastCut` (`r = 24`).
* `Cslib.Algorithms.WordRAM.Karger.fastCutHighProbCode`,
  `Cslib.Algorithms.WordRAM.Karger.fastCutHighProbProgram`,
  `Cslib.Algorithms.WordRAM.Karger.fastCutHighProbTime`: amplified `O(n ^ 2 log ^ 3 n)`
  high-probability Karger–Stein (`r = 24`).

## Main results

* `Cslib.Algorithms.WordRAM.Karger.fastCutProgram_spec`: worst-case `O(n ^ 2 log n)` step bound,
  `O(n ^ 2)` `rand`-call bound, pathwise non-trivial cut realization, `Modifies` frame, and
  `1 / (Nat.log 2 n + 15)` success probability lower bound for `fastCutProgram`
  (`[KargerStein1996]`, Section 4, Figure 6 and Lemmas 4.1–4.3; paraphrase).
* `Cslib.Algorithms.WordRAM.Karger.fastCutHighProbProgram_spec`,
  `Cslib.Algorithms.WordRAM.Karger.fastCutHighProbProgram_failure_le_inv_n`: worst-case
  `O(n ^ 2 log ^ 3 n)` step bound, pathwise non-trivial cut realization, `Modifies` frame, and
  `1 / (2 * n)` (`1 / n`) failure probability upper bound for `fastCutHighProbProgram`
  (the minimum-cut-value part of `[KargerStein1996]`, Section 4, Theorem 4.4; paraphrase).

## References

* [D. R. Karger and C. Stein, *A New Approach to the Minimum Cut Problem*][KargerStein1996]
* [D. R. Karger, *Global Min-cuts in RNC, and Other Ramifications of a Simple Min-Cut
  Algorithm*][Karger1993]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Karger

open scoped ENNReal
open Cslib.WeightedCut
open Cslib.Probability.PMF
open Cslib.WordRAM

/-! ### Word-size sufficiency (`logWidth 4 n ≤ w`) and input layout -/

/-- `16 ≤ 24`, used to embed `computeDegreesAndTotal` and `contractDownTo` into `Data 24`. -/
private theorem hr24 : 16 ≤ 24 := by decide

/-- Under `2 ≤ n` and `logWidth 4 n ≤ w`, stack workspace end-addresses up to `2 + 27 * (n * n)` fit
in `w`-bit words. -/
theorem fits_fastCutWorkspace_of_logWidth_four {n w : ℕ} (hn : 2 ≤ n) (hw : logWidth 4 n ≤ w) :
    Fits w (2 + 27 * (n * n)) := by
  by_cases hn5 : 5 ≤ n
  · refine (fits_of_lt_pow (k := 4) (n := n) ?_).mono hw
    obtain ⟨d, rfl⟩ : ∃ d, n = d + 5 := ⟨n - 5, by omega⟩
    have hpow : (d + 5 + 1) ^ 4 = (d + 6) ^ 2 * (d + 6) ^ 2 := by ring
    have h36 : 36 ≤ (d + 6) ^ 2 := by nlinarith
    rw [hpow]
    nlinarith
  · have hfit_lw : Fits (logWidth 4 n) (2 + 27 * (n * n)) := by
      interval_cases n <;> decide
    exact hfit_lw.mono hw

/-- Under `2 ≤ n` and `logWidth 4 n ≤ w`, `fastCutTrials n = (Nat.log 2 n + 15) * (Nat.log 2 n + 2)`
fits in `w`-bit words. -/
theorem fits_fastCutTrials_of_logWidth_four {n w : ℕ} (hn : 2 ≤ n) (hw : logWidth 4 n ≤ w) :
    Fits w (fastCutTrials n) := by
  by_cases hn4 : 4 ≤ n
  · refine (fits_of_lt_pow (k := 4) (n := n) ?_).mono hw
    unfold fastCutTrials
    have hlog : Nat.log 2 n < n := Nat.log_lt_self 2 (by omega)
    have h15 : Nat.log 2 n + 15 ≤ n + 14 := by omega
    have h2 : Nat.log 2 n + 2 ≤ n + 1 := by omega
    have hmul : (Nat.log 2 n + 15) * (Nat.log 2 n + 2) ≤ (n + 14) * (n + 1) :=
      Nat.mul_le_mul h15 h2
    have hpow : (n + 14) * (n + 1) < (n + 1) ^ 4 := by
      obtain ⟨d, rfl⟩ : ∃ d, n = d + 4 := ⟨n - 4, by omega⟩
      have hp4 : (d + 4 + 1) ^ 4 = (d + 5) ^ 2 * (d + 5) ^ 2 := by ring
      have h25 : 25 ≤ (d + 5) ^ 2 := by nlinarith
      rw [hp4]
      nlinarith
    exact lt_of_le_of_lt hmul hpow
  · have hfit_lw : Fits (logWidth 4 n) (fastCutTrials n) := by
      interval_cases n <;> decide
    exact hfit_lw.mono hw

/-- `logWidth 4 n ≤ w` and `Fits w (totalDoubledWeight W)` suffice for
`InputFits w (n :: flattenMatrix W)`. -/
theorem inputFits_fastCut {n w : ℕ} {W : Fin n → Fin n → ℕ} (hn : 2 ≤ n)
    (hw : logWidth 4 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    InputFits w (n :: flattenMatrix W) := by
  have hws := fits_fastCutWorkspace_of_logWidth_four hn hw
  refine ⟨?_, ?_⟩
  · simp only [List.length_cons, length_flattenMatrix]
    exact hws.of_le (by omega)
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hmem
    · exact hws.of_le (by nlinarith)
    · exact htot.of_le (mem_flattenMatrix_le_totalDoubledWeight W hmem)

/-- In `Data.init (n :: flattenMatrix W)`, memory holds `W` at base `2` with stride `n`. -/
theorem holdsMatrix_init_fastCut {r n : ℕ} (W : Fin n → Fin n → ℕ) :
    HoldsMatrix (Data.init (r := r) (n :: flattenMatrix W)).mem 2 n W := by
  intro i j
  have haddr : 2 + i.val * n + j.val = (1 + (i.val * n + j.val)) + 1 := by omega
  rw [haddr, Data.init_mem_succ]
  have hlt : i.val * n + j.val < (flattenMatrix W).length := by
    rw [length_flattenMatrix]
    nlinarith [i.isLt, j.isLt]
  change (n :: flattenMatrix W).getD (1 + (i.val * n + j.val)) 0 = W i j
  have hcons : (n :: flattenMatrix W).getD (1 + (i.val * n + j.val)) 0 =
      (flattenMatrix W).getD (i.val * n + j.val) 0 := by
    rw [Nat.add_comm 1, List.getD_cons_succ]
  rw [hcons, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  exact getElem_flattenMatrix W i j

private theorem toOuterMeasure_mono_support {α : Type} (m : ProbComp α) {S T : Set α}
    (h : ∀ a ∈ m.support, a ∈ S → a ∈ T) :
    m.eval.toOuterMeasure S ≤ m.eval.toOuterMeasure T := by
  classical
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  refine tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ S
  · simp only [Set.indicator_of_mem ha]
    by_cases hs : a ∈ m.support
    · simp only [Set.indicator_of_mem (h a hs ha), le_rfl]
    · have hs' : a ∉ m.eval.support := by rwa [ProbComp.support_eval]
      have hz : m.eval a = 0 := (PMF.apply_eq_zero_iff m.eval a).mpr hs'
      simp [hz]
  · simp [Set.indicator_of_notMem ha]

/-! ### Register layout (`r = 24`) -/

-- Registers `0..15` match `Reg` (`Contract.lean`) via `Fin.castLE hr24`, while `16..23` hold the
-- immutable input descriptor, explicit iterative frame stack, and outer amplification state.
namespace KSReg

/-- Constant register `0` (`Reg.zero` embedded into `Fin 24`). -/
abbrev zero : Fin 24 := 0
/-- Constant register `1` (`Reg.one` embedded into `Fin 24`). -/
abbrev one : Fin 24 := 1
/-- Working matrix base address (`Reg.wBase` embedded into `Fin 24`). -/
abbrev wBase : Fin 24 := 2
/-- Working degree-array base address (`Reg.dBase` embedded into `Fin 24`). -/
abbrev dBase : Fin 24 := 3
/-- Working matrix row stride (`Reg.stride` embedded into `Fin 24`). -/
abbrev stride : Fin 24 := 4
/-- Active supervertex count `k` (`Reg.activeK` embedded into `Fin 24`). -/
abbrev activeK : Fin 24 := 5
/-- Target supervertex count `t` (`Reg.targetT` embedded into `Fin 24`). -/
abbrev targetT : Fin 24 := 6
/-- Active doubled edge weight `S` (`Reg.totS` embedded into `Fin 24`). -/
abbrev totS : Fin 24 := 7
/-- Row / auxiliary scratch register (`Reg.uReg` embedded into `Fin 24`). -/
abbrev uReg : Fin 24 := 8
/-- Column / auxiliary scratch register (`Reg.vReg` embedded into `Fin 24`). -/
abbrev vReg : Fin 24 := 9
/-- Loop index scratch register (`Reg.idx` embedded into `Fin 24`). -/
abbrev idx : Fin 24 := 10
/-- Loop length / remainder scratch register (`Reg.rem` embedded into `Fin 24`). -/
abbrev rem : Fin 24 := 11
/-- Primary scratch address register (`Reg.addr1` embedded into `Fin 24`). -/
abbrev addr1 : Fin 24 := 12
/-- Secondary scratch address register (`Reg.addr2` embedded into `Fin 24`). -/
abbrev addr2 : Fin 24 := 13
/-- Primary scratch value register (`Reg.val1` embedded into `Fin 24`). -/
abbrev val1 : Fin 24 := 14
/-- Secondary scratch value register (`Reg.val2` embedded into `Fin 24`). -/
abbrev val2 : Fin 24 := 15
/-- Base address (`2`) of the immutable input matrix `W`. -/
abbrev srcBase : Fin 24 := 16
/-- Root vertex count `n`, preserved across all trees. -/
abbrev nOrig : Fin 24 := 17
/-- Current stack frame base address `fp`. -/
abbrev fpReg : Fin 24 := 18
/-- Current active stack depth `sp` (`0` = empty). -/
abbrev spReg : Fin 24 := 19
/-- Cut weight returned by the most recently popped frame. -/
abbrev retVal : Fin 24 := 20
/-- Total number of `FastCut` trees to run in `fastCutHighProbCode`. -/
abbrev numTrials : Fin 24 := 21
/-- Number of `FastCut` trees completed so far. -/
abbrev trialIdx : Fin 24 := 22
/-- Minimum cut weight seen across completed `FastCut` trees. -/
abbrev bestVal : Fin 24 := 23

end KSReg

section Subroutines

open KSReg

/-! ### Deterministic subroutines: block copy, integer threshold, and submatrix compaction -/

/-- Injective register map embedding `Cslib.WordRAM.ArrayCopy` (`r = 7`) into `Fin 24` with
`(src, dst, len, idx, addr, value, one) = (uReg, wBase, rem, idx, addr1, val1, one)`. -/
def ksCopyRegMap : Fin 7 → Fin 24 :=
  ![uReg, wBase, rem, idx, addr1, val1, one]

theorem ksCopyRegMap_injective : Function.Injective ksCopyRegMap := by
  decide

/-- Copy `rem` words from `uReg` to `wBase` via `Cslib.WordRAM.ArrayCopy.program`. -/
def ksCopyCode : Code .standard 24 :=
  ArrayCopy.program.rename ksCopyRegMap

theorem holdsMatrix_of_copyPrefix {mem : ℕ → ℕ} {sb db k : ℕ} {W : Fin k → Fin k → ℕ}
    (hsrc : HoldsMatrix mem sb k W) :
    HoldsMatrix (ArrayCopy.copyPrefix mem sb db (k * k)) db k W := by
  intro i j
  have hlt : i.val * k + j.val < k * k := by nlinarith [i.isLt, j.isLt]
  have haddr_d : db + i.val * k + j.val = db + (i.val * k + j.val) := by omega
  have haddr_s : sb + (i.val * k + j.val) = sb + i.val * k + j.val := by omega
  rw [haddr_d, ArrayCopy.copyPrefix_read hlt, haddr_s]
  exact hsrc i j

theorem ksCopyCode_exec {w sb db k : ℕ} {W : Fin k → Fin k → ℕ} {x : Data 24}
    (hsb : x.regs uReg = sb) (hdb : x.regs wBase = db) (hlen : x.regs rem = k * k)
    (hdisj : sb + k * k ≤ db) (h1 : Fits w 1) (hdEnd : Fits w (db + k * k))
    (hsrc : HoldsMatrix x.mem sb k W) :
    ∃ y : Data 24, ExecWithin w ksCopyCode x y (7 * (k * k) + 4) ∧
      HoldsMatrix y.mem db k W ∧
      Modifies (Finset.Ico db (db + k * k)) x.mem y.mem ∧
      y.regs zero = x.regs zero ∧
      y.regs wBase = db ∧
      y.regs dBase = x.regs dBase ∧
      y.regs stride = x.regs stride ∧
      y.regs activeK = x.regs activeK ∧
      y.regs targetT = x.regs targetT ∧
      (∀ j : Fin 24, 16 ≤ j.val → y.regs j = x.regs j) := by
  have hs_fit : Fits w ((x.comap ksCopyRegMap).regs ArrayCopy.src +
      (x.comap ksCopyRegMap).regs ArrayCopy.len) := by
    change Fits w (x.regs uReg + x.regs rem)
    rw [hsb, hlen]
    exact hdEnd.of_le (by omega)
  have hd_fit : Fits w ((x.comap ksCopyRegMap).regs ArrayCopy.dst +
      (x.comap ksCopyRegMap).regs ArrayCopy.len) := by
    change Fits w (x.regs wBase + x.regs rem)
    rw [hdb, hlen]
    exact hdEnd
  have hdisj' : (x.comap ksCopyRegMap).regs ArrayCopy.src +
      (x.comap ksCopyRegMap).regs ArrayCopy.len ≤ (x.comap ksCopyRegMap).regs ArrayCopy.dst := by
    change x.regs uReg + x.regs rem ≤ x.regs wBase
    rw [hsb, hlen, hdb]
    exact hdisj
  obtain ⟨y₀, hy₀_exec, hy₀_mem, _, _, _⟩ :=
    ArrayCopy.exec (x.comap ksCopyRegMap) h1 hs_fit hd_fit hdisj'
  have hsrc_c : (x.comap ksCopyRegMap).regs ArrayCopy.src = sb := hsb
  have hdst_c : (x.comap ksCopyRegMap).regs ArrayCopy.dst = db := hdb
  have hlen_c : (x.comap ksCopyRegMap).regs ArrayCopy.len = k * k := hlen
  rw [hlen_c] at hy₀_exec
  rw [hsrc_c, hdst_c, hlen_c] at hy₀_mem
  let y := y₀.extend ksCopyRegMap x
  have hex : ExecWithin w ksCopyCode x y (7 * (k * k) + 4) :=
    hy₀_exec.rename ksCopyRegMap_injective
  have hym : y.mem = ArrayCopy.copyPrefix x.mem sb db (k * k) := hy₀_mem
  have ⟨_, _, he⟩ := hex
  have hpres : ∀ j : Fin 24, ksCopyCode.Preserves j → y.regs j = x.regs j :=
    fun j hj => he.regs_eq hj
  refine ⟨y, hex, hym ▸ holdsMatrix_of_copyPrefix hsrc, ?_,
    hpres zero (by decide), hpres wBase (by decide) ▸ hdb,
    hpres dBase (by decide), hpres stride (by decide),
    hpres activeK (by decide), hpres targetT (by decide),
    fun j hj => ?_⟩
  · intro a ha
    rw [hym]
    apply ArrayCopy.copyPrefix_outside
    rw [Finset.mem_Ico] at ha
    exact ha
  · have : j = srcBase ∨ j = nOrig ∨ j = fpReg ∨ j = spReg ∨
        j = retVal ∨ j = numTrials ∨ j = trialIdx ∨ j = bestVal := by
      fin_cases j <;> simp_all
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hpres _ (by decide)

/-- Loop body of `thresholdCode`: advance `t` to `t + 1` while maintaining `uReg = t`
(`= (t + 1) - 1`) and `val1 = 2 * (t + 1) * t` without subtraction. -/
def thresholdLoopBody : Code .standard 24 := ram[
  uReg ← targetT;
  targetT ← targetT + one;
  val1 ← val2 * targetT;
  val1 ← val1 * uReg
]

/-- Preamble of `thresholdCode`: initialize `rem = k * (k - 1)` and `(targetT, uReg, val2, val1) =
(2, 1, 2, 4)`. -/
def thresholdPre : Code .standard 24 := ram[
  one ← #1;
  rem ← activeK - one;
  rem ← activeK * rem;
  targetT ← #2;
  uReg ← #1;
  val2 ← #2;
  val1 ← #4
]

/-- Compute `targetT = fastCutThreshold k` in `O(k)` instructions for `k = x.regs activeK ≥ 7`. -/
def thresholdCode : Code .standard 24 := ram[
  ⟪thresholdPre⟫;
  while val1 < rem do [ ⟪thresholdLoopBody⟫ ]
]

theorem thresholdCode_exec {w k : ℕ} {x : Data 24} (hk : 7 ≤ k)
    (hactiveK : x.regs activeK = k) (hfit : Fits w (2 * k * (k - 1))) :
    ∃ y : Data 24, ExecWithin w thresholdCode x y (6 * k + 9) ∧
      y.mem = x.mem ∧
      y.regs one = 1 ∧
      y.regs activeK = k ∧
      y.regs targetT = fastCutThreshold k ∧
      y.regs wBase = x.regs wBase ∧
      y.regs dBase = x.regs dBase ∧
      y.regs stride = x.regs stride ∧
      (∀ j : Fin 24, 16 ≤ j.val → y.regs j = x.regs j) := by
  have hk42 : 42 ≤ k * (k - 1) := by
    obtain ⟨c, rfl⟩ : ∃ c, k = c + 7 := ⟨k - 7, by omega⟩
    have : c + 7 - 1 = c + 6 := by omega
    rw [this]; nlinarith
  have h2k : 2 * (k * (k - 1)) = 2 * k * (k - 1) := by ring
  have h1 : Fits w 1 := hfit.of_le (by omega)
  have h2 : Fits w 2 := hfit.of_le (by omega)
  have h4 : Fits w 4 := hfit.of_le (by omega)
  have hkm1_fit : Fits w (k - 1) := hfit.of_le (by nlinarith)
  have hkkm1_fit : Fits w (k * (k - 1)) := hfit.of_le (by omega)
  let t_star := fastCutThreshold k
  have ht_ge2 : 2 ≤ t_star := fastCutThreshold_ge_two (by omega)
  have ht_le_pred : t_star ≤ k - 1 := fastCutThreshold_le_pred (by omega)
  have ht_spec : k * (k - 1) ≤ 2 * t_star * (t_star - 1) := fastCutThreshold_spec (by omega)
  let I (y : Data 24) : Prop :=
    y.mem = x.mem ∧
    y.regs one = 1 ∧
    y.regs activeK = k ∧
    y.regs rem = k * (k - 1) ∧
    y.regs val2 = 2 ∧
    2 ≤ y.regs targetT ∧
    y.regs targetT ≤ t_star ∧
    y.regs uReg = y.regs targetT - 1 ∧
    y.regs val1 = 2 * y.regs targetT * (y.regs targetT - 1)
  have hbody : ∀ y, I y → (Cond.lt val1 rem).Holds y →
      ∃ z, ExecWithin w thresholdLoopBody y z 4 ∧ I z ∧
        t_star - z.regs targetT < t_star - y.regs targetT := by
    intro y ⟨hym, hy1, hyk, hyrem, hyv2, hyt_ge, hyt_le, _, hyv1⟩ hc
    let t := y.regs targetT
    have hlt_prod : 2 * t * (t - 1) < k * (k - 1) := by
      simpa [Cond.holds_lt, hyv1, hyrem] using hc
    have ht_lt_star : t < t_star := by
      by_contra hge
      have heq : t = t_star := by omega
      rw [heq] at hlt_prod
      exact absurd ht_spec (not_le_of_gt hlt_prod)
    have ht1_le : t + 1 ≤ k - 1 := by omega
    have hfit_tp1 : Fits w (t + 1) := hfit.of_le (by nlinarith)
    have hfit_2tp1 : Fits w (2 * (t + 1)) := hfit.of_le (by nlinarith)
    have hfit_prod : Fits w (2 * (t + 1) * t) := hfit.of_le (by
      have hmul : (t + 1) * t ≤ k * (k - 1) := Nat.mul_le_mul (by omega) (by omega)
      nlinarith)
    let b₁ := y.set uReg t
    let b₂ := b₁.set targetT (t + 1)
    let b₃ := b₂.set val1 (2 * (t + 1))
    let b₄ := b₃.set val1 (2 * (t + 1) * t)
    have e1 : ExecWithin (B := .standard) w ram[uReg ← targetT] y b₁ 1 :=
      (Exec.copy (B := .standard) (w := w) (d := uReg) (s := targetT) (x := y)).within
    have e2 : ExecWithin w ram[targetT ← targetT + one] b₁ b₂ 1 := by
      have ht' : b₁.regs targetT = t := by simp +decide [b₁, t]
      have h1' : b₁.regs one = 1 := by simpa +decide [b₁, Function.update_apply] using hy1
      simpa [b₂, BinOp.eval, ht', h1'] using
        ExecWithin.bin (f := .add) (d := targetT) (i := targetT) (j := one) (x := b₁)
          (by simpa [BinOp.eval, ht', h1'] using hfit_tp1)
    have e3 : ExecWithin w ram[val1 ← val2 * targetT] b₂ b₃ 1 := by
      have hv2' : b₂.regs val2 = 2 := by simpa +decide [b₂, b₁, Function.update_apply] using hyv2
      have ht' : b₂.regs targetT = t + 1 := by simp [b₂]
      simpa [b₃, BinOp.eval, hv2', ht'] using
        ExecWithin.bin (f := .mul) (d := val1) (i := val2) (j := targetT) (x := b₂)
          (by simpa [BinOp.eval, hv2', ht'] using hfit_2tp1)
    have e4 : ExecWithin w ram[val1 ← val1 * uReg] b₃ b₄ 1 := by
      have hv1' : b₃.regs val1 = 2 * (t + 1) := by simp [b₃]
      have hu' : b₃.regs uReg = t := by simp +decide [b₃, b₂, b₁]
      simpa [b₄, BinOp.eval, hv1', hu'] using
        ExecWithin.bin (f := .mul) (d := val1) (i := val1) (j := uReg) (x := b₃)
          (by simpa [BinOp.eval, hv1', hu'] using hfit_prod)
    have hrun : ExecWithin w thresholdLoopBody y b₄ 4 := by
      unfold thresholdLoopBody
      exact (e1.seq (e2.seq (e3.seq e4))).mono (by omega)
    have hb4_t : b₄.regs targetT = t + 1 := by simp +decide [b₄, b₃, b₂]
    refine ⟨b₄, hrun, ?_, ?_⟩
    · refine ⟨hym, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa +decide [b₄, b₃, b₂, b₁, Function.update_apply] using hy1
      · simpa +decide [b₄, b₃, b₂, b₁, Function.update_apply] using hyk
      · simpa +decide [b₄, b₃, b₂, b₁, Function.update_apply] using hyrem
      · simpa +decide [b₄, b₃, b₂, b₁, Function.update_apply] using hyv2
      · rw [hb4_t]; omega
      · rw [hb4_t]; exact ht_lt_star
      · rw [hb4_t]; simp +decide [b₄, b₃, b₂, b₁]
      · rw [hb4_t]; simp +decide [b₄, b₃]
    · rw [hb4_t]; omega
  let p₁ := x.set one 1
  let p₂ := p₁.set rem (k - 1)
  let p₃ := p₂.set rem (k * (k - 1))
  let p₄ := p₃.set targetT 2
  let p₅ := p₄.set uReg 1
  let p₆ := p₅.set val2 2
  let x₀ := p₆.set val1 4
  have hex_pre : ExecWithin w thresholdPre x x₀ 7 := by
    have s1 : ExecWithin (B := .standard) w ram[one ← #1] x p₁ 1 := ExecWithin.const h1
    have s2 : ExecWithin w ram[rem ← activeK - one] p₁ p₂ 1 := by
      have hk' : p₁.regs activeK = k := by simpa +decide [p₁, Function.update_apply] using hactiveK
      have h1' : p₁.regs one = 1 := by simp [p₁]
      simpa [p₂, BinOp.eval, hk', h1'] using
        ExecWithin.bin (f := .sub) (d := rem) (i := activeK) (j := one) (x := p₁)
          (by simpa [BinOp.eval, hk', h1'] using hkm1_fit)
    have s3 : ExecWithin w ram[rem ← activeK * rem] p₂ p₃ 1 := by
      have hk' : p₂.regs activeK = k := by
        simpa +decide [p₂, p₁, Function.update_apply] using hactiveK
      have hr' : p₂.regs rem = k - 1 := by simp [p₂]
      simpa [p₃, BinOp.eval, hk', hr'] using
        ExecWithin.bin (f := .mul) (d := rem) (i := activeK) (j := rem) (x := p₂)
          (by simpa [BinOp.eval, hk', hr'] using hkkm1_fit)
    have s4 : ExecWithin (B := .standard) w ram[targetT ← #2] p₃ p₄ 1 := ExecWithin.const h2
    have s5 : ExecWithin (B := .standard) w ram[uReg ← #1] p₄ p₅ 1 := ExecWithin.const h1
    have s6 : ExecWithin (B := .standard) w ram[val2 ← #2] p₅ p₆ 1 := ExecWithin.const h2
    have s7 : ExecWithin (B := .standard) w ram[val1 ← #4] p₆ x₀ 1 := ExecWithin.const h4
    unfold thresholdPre
    exact (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq s7)))))).mono (by omega)
  have hx₀_t : x₀.regs targetT = 2 := by simp +decide [x₀, p₆, p₅, p₄]
  have hx₀ : I x₀ := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp +decide [x₀, p₆, p₅, p₄, p₃, p₂, p₁]
    · simpa +decide [x₀, p₆, p₅, p₄, p₃, p₂, p₁, Function.update_apply] using hactiveK
    · simp +decide [x₀, p₆, p₅, p₄, p₃]
    · simp +decide [x₀, p₆]
    · rw [hx₀_t]
    · rw [hx₀_t]; exact ht_ge2
    · rw [hx₀_t]; simp +decide [x₀, p₆, p₅]
    · rw [hx₀_t]; simp +decide [x₀]
  obtain ⟨y, hex_loop, hy, hc_exit⟩ :=
    ExecWithin.loop_invariant I (fun z => t_star - z.regs targetT) hbody hx₀
  rcases hy with ⟨hym, hy1, hyk, hyrem, _, hyt_ge, hyt_le, _, hyv1⟩
  have hyt_eq : y.regs targetT = t_star := by
    apply le_antisymm hyt_le
    by_contra hlt'
    have hlt : y.regs targetT < t_star := Nat.lt_of_not_ge hlt'
    have hmin := fastCutThreshold_lt_of_lt (by omega : 4 ≤ k) hyt_ge hlt
    have hge_exit : k * (k - 1) ≤ 2 * y.regs targetT * (y.regs targetT - 1) := by
      simp only [Cond.holds_lt, hyv1, hyrem, not_lt] at hc_exit
      exact hc_exit
    omega
  have htot_exec : ExecWithin w thresholdCode x y (6 * k + 9) := by
    have hseq : ExecWithin w thresholdCode x y
        (7 + ((t_star - x₀.regs targetT) * (4 + 2) + 2)) := hex_pre.seq hex_loop
    refine hseq.mono ?_
    rw [hx₀_t]
    omega
  have ⟨_, _, he⟩ := htot_exec
  have hpres : ∀ j : Fin 24, thresholdCode.Preserves j → y.regs j = x.regs j :=
    fun j hj => he.regs_eq hj
  refine ⟨y, htot_exec, hym, hy1, hyk, hyt_eq,
    hpres wBase (by decide), hpres dBase (by decide), hpres stride (by decide),
    fun j hj => ?_⟩
  have : j = srcBase ∨ j = nOrig ∨ j = fpReg ∨ j = spReg ∨
      j = retVal ∨ j = numTrials ∨ j = trialIdx ∨ j = bestVal := by
    fin_cases j <;> simp_all
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact hpres _ (by decide)

/-- Inner column loop body of `copySubmatrixCode`: copy `mem[idx + vReg]` to `mem[rem + vReg]`. -/
def copySubColBody : Code .standard 24 := ram[
  addr1 ← idx + vReg;
  val1 ← *addr1;
  addr1 ← rem + vReg;
  *addr1 ← val1;
  vReg ← vReg + one
]

/-- Row-pointer advance at the end of `copySubRowBody`. -/
def copySubRowPost : Code .standard 24 := ram[
  idx ← idx + stride;
  rem ← rem + targetT;
  uReg ← uReg + one
]

/-- Outer row loop body of `copySubmatrixCode`: copy row `uReg` of length `targetT` and advance row
pointers `idx` by `stride` and `rem` by `targetT`. -/
def copySubRowBody : Code .standard 24 := ram[
  vReg ← #0;
  while vReg < targetT do [ ⟪copySubColBody⟫ ];
  ⟪copySubRowPost⟫
]

/-- Preamble of `copySubmatrixCode`. -/
def copySubPre : Code .standard 24 := ram[
  idx ← wBase;
  rem ← addr2;
  uReg ← #0
]

/-- Copy the active `t × t` submatrix at `wBase` (stride `stride`) densely into `addr2` (stride `t`)
without `.sub`, `.div`, or `.mod`. -/
def copySubmatrixCode : Code .standard 24 := ram[
  ⟪copySubPre⟫;
  while uReg < targetT do [ ⟪copySubRowBody⟫ ]
]

theorem copySubmatrixCode_exec {w wb str dstBase t : ℕ} {W : Fin t → Fin t → ℕ} {x : Data 24}
    (hwBase : x.regs wBase = wb) (hstride : x.regs stride = str)
    (htargetT : x.regs targetT = t) (hdst : x.regs addr2 = dstBase) (hone : x.regs one = 1)
    (hstr : t ≤ str) (hdisj : wb + str * t ≤ dstBase)
    (hwEnd : Fits w (wb + str * t)) (hdstEnd : Fits w (dstBase + t * t))
    (hmat : HoldsMatrix x.mem wb str W) :
    ∃ y : Data 24, ExecWithin w copySubmatrixCode x y (7 * t ^ 2 + 8 * t + 5) ∧
      HoldsMatrix y.mem dstBase t W ∧
      Modifies (Finset.Ico dstBase (dstBase + t * t)) x.mem y.mem ∧
      y.regs one = 1 ∧
      y.regs wBase = wb ∧
      y.regs dBase = x.regs dBase ∧
      y.regs stride = str ∧
      y.regs activeK = x.regs activeK ∧
      y.regs targetT = t ∧
      y.regs addr2 = dstBase ∧
      (∀ j : Fin 24, 16 ≤ j.val → y.regs j = x.regs j) := by
  let OuterI (y : Data 24) : Prop :=
    y.regs one = 1 ∧
    y.regs wBase = wb ∧
    y.regs stride = str ∧
    y.regs targetT = t ∧
    y.regs addr2 = dstBase ∧
    y.regs uReg ≤ t ∧
    y.regs idx = wb + y.regs uReg * str ∧
    y.regs rem = dstBase + y.regs uReg * t ∧
    Modifies (Finset.Ico dstBase (dstBase + t * t)) x.mem y.mem ∧
    ∀ i j : Fin t, i.val < y.regs uReg → y.mem (dstBase + i.val * t + j.val) = W i j
  have houter_body : ∀ y, OuterI y → (Cond.lt uReg targetT).Holds y →
      ∃ z, ExecWithin w copySubRowBody y z (7 * t + 6) ∧ OuterI z ∧
        t - z.regs uReg < t - y.regs uReg := by
    intro y ⟨hy1, hywb, hystr, hyt, hydst, hyu_le, hyidx, hyrem, hymod, hydone⟩ hc
    have hu_lt : y.regs uReg < t := by simpa [Cond.holds_lt, hyt] using hc
    let u : Fin t := ⟨y.regs uReg, hu_lt⟩
    let InnerI (q : Data 24) : Prop :=
      q.regs one = 1 ∧
      q.regs wBase = wb ∧
      q.regs stride = str ∧
      q.regs targetT = t ∧
      q.regs addr2 = dstBase ∧
      q.regs uReg = u.val ∧
      q.regs idx = wb + u.val * str ∧
      q.regs rem = dstBase + u.val * t ∧
      q.regs vReg ≤ t ∧
      Modifies (Finset.Ico dstBase (dstBase + t * t)) x.mem q.mem ∧
      ∀ i j : Fin t, (i.val < u.val ∨ (i = u ∧ j.val < q.regs vReg)) →
        q.mem (dstBase + i.val * t + j.val) = W i j
    have hcol_body : ∀ q, InnerI q → (Cond.lt vReg targetT).Holds q →
        ∃ q', ExecWithin w copySubColBody q q' 5 ∧ InnerI q' ∧
          t - q'.regs vReg < t - q.regs vReg := by
      intro q ⟨hq1, hqwb, hqstr, hqt, hqdst, hqu, hqidx, hqrem, hqv_le, hqmod, hqdone⟩ hcv
      have hv_lt : q.regs vReg < t := by simpa [Cond.holds_lt, hqt] using hcv
      let v : Fin t := ⟨q.regs vReg, hv_lt⟩
      have hsrc_lt : wb + u.val * str + v.val < wb + str * t := matAddr_lt_end hstr u v
      have hdst_lt : dstBase + u.val * t + v.val < dstBase + t * t :=
        matAddr_lt_end (le_refl t) u v
      have hv_eq : q.regs vReg = v.val := rfl
      have hfit_src : Fits w (wb + u.val * str + v.val) := hwEnd.of_le (by omega)
      have hfit_dst : Fits w (dstBase + u.val * t + v.val) := hdstEnd.of_le (by omega)
      have hfit_vp1 : Fits w (v.val + 1) := hdstEnd.of_le (by
        have : t ≤ t * t := Nat.le_mul_self t
        omega)
      have hread_src : q.mem (wb + u.val * str + v.val) = W u v := by
        rw [hqmod _ (by rw [Finset.mem_Ico]; omega)]
        exact hmat u v
      let c₁ := q.set addr1 (wb + u.val * str + v.val)
      let c₂ := c₁.set val1 (W u v)
      let c₃ := c₂.set addr1 (dstBase + u.val * t + v.val)
      let c₄ := c₃.write (dstBase + u.val * t + v.val) (W u v)
      let q' := c₄.set vReg (v.val + 1)
      have e1 : ExecWithin w ram[addr1 ← idx + vReg] q c₁ 1 := by
        simpa [c₁, BinOp.eval, hqidx, hv_eq] using
          ExecWithin.bin (f := .add) (d := addr1) (i := idx) (j := vReg) (x := q)
            (by simpa [BinOp.eval, hqidx, hv_eq] using hfit_src)
      have e2 : ExecWithin (B := .standard) w ram[val1 ← *addr1] c₁ c₂ 1 := by
        have ha1 : c₁.regs addr1 = wb + u.val * str + v.val := by simp [c₁]
        have hm1 : c₁.mem (wb + u.val * str + v.val) = W u v := hread_src
        simpa [c₂, ha1, hm1] using
          ExecWithin.load (B := .standard) (w := w) (d := val1) (a := addr1) (x := c₁)
      have e3 : ExecWithin w ram[addr1 ← rem + vReg] c₂ c₃ 1 := by
        have hrem' : c₂.regs rem = dstBase + u.val * t := by
          simpa +decide [c₂, c₁, Function.update_apply] using hqrem
        have hv' : c₂.regs vReg = v.val := by simp +decide [c₂, c₁, hv_eq]
        simpa [c₃, BinOp.eval, hrem', hv'] using
          ExecWithin.bin (f := .add) (d := addr1) (i := rem) (j := vReg) (x := c₂)
            (by simpa [BinOp.eval, hrem', hv'] using hfit_dst)
      have e4 : ExecWithin (B := .standard) w ram[*addr1 ← val1] c₃ c₄ 1 := by
        have ha1 : c₃.regs addr1 = dstBase + u.val * t + v.val := by simp [c₃]
        have hv1 : c₃.regs val1 = W u v := by simp +decide [c₃, c₂]
        simpa [c₄, ha1, hv1] using
          ExecWithin.store (B := .standard) (w := w) (a := addr1) (s := val1) (x := c₃)
      have e5 : ExecWithin w ram[vReg ← vReg + one] c₄ q' 1 := by
        have hv' : c₄.regs vReg = v.val := by simp +decide [c₄, c₃, c₂, c₁, hv_eq]
        have h1' : c₄.regs one = 1 := by
          simpa +decide [c₄, c₃, c₂, c₁, Function.update_apply] using hq1
        simpa [q', BinOp.eval, hv', h1'] using
          ExecWithin.bin (f := .add) (d := vReg) (i := vReg) (j := one) (x := c₄)
            (by simpa [BinOp.eval, hv', h1'] using hfit_vp1)
      have hrun : ExecWithin w copySubColBody q q' 5 := by
        unfold copySubColBody
        exact (e1.seq (e2.seq (e3.seq (e4.seq e5)))).mono (by omega)
      have hq'_v : q'.regs vReg = v.val + 1 := by simp [q']
      have hq'_mem : q'.mem = Function.update q.mem (dstBase + u.val * t + v.val) (W u v) := rfl
      refine ⟨q', hrun, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa +decide [q', c₄, c₃, c₂, c₁, Function.update_apply] using hq1
        · simpa +decide [q', c₄, c₃, c₂, c₁, Function.update_apply] using hqwb
        · simpa +decide [q', c₄, c₃, c₂, c₁, Function.update_apply] using hqstr
        · simpa +decide [q', c₄, c₃, c₂, c₁, Function.update_apply] using hqt
        · simpa +decide [q', c₄, c₃, c₂, c₁, Function.update_apply] using hqdst
        · simpa +decide [q', c₄, c₃, c₂, c₁, Function.update_apply] using hqu
        · simpa +decide [q', c₄, c₃, c₂, c₁, Function.update_apply] using hqidx
        · simpa +decide [q', c₄, c₃, c₂, c₁, Function.update_apply] using hqrem
        · rw [hq'_v]; exact hv_lt
        · rw [hq'_mem]
          exact modifies_trans_subset hqmod
            (modifies_update_of_mem (matAddr_mem_Ico (le_refl t) u v) q.mem _)
            Finset.Subset.rfl Finset.Subset.rfl
        · intro i j hij
          rw [hq'_v] at hij
          rw [hq'_mem]
          by_cases huv : i = u ∧ j = v
          · rcases huv with ⟨rfl, rfl⟩
            exact Function.update_self _ _ _
          · have hne : dstBase + i.val * t + j.val ≠ dstBase + u.val * t + v.val := by
              intro heq
              exact huv (matAddr_inj (le_refl t) heq)
            rw [Function.update_of_ne hne]
            apply hqdone i j
            rcases hij with hlt_u | ⟨rfl, hlt_vp1⟩
            · exact Or.inl hlt_u
            · refine Or.inr ⟨rfl, ?_⟩
              have hjv : j.val ≠ v.val := fun h => huv ⟨rfl, Fin.ext h⟩
              omega
      · rw [hq'_v, hv_eq]
        omega
    let q₀ := y.set vReg 0
    have hq₀_exec : ExecWithin (B := .standard) w ram[vReg ← #0] y q₀ 1 :=
      ExecWithin.const (fits_zero w)
    have hq₀_inv : InnerI q₀ := by
      refine ⟨by simpa +decide [q₀, Function.update_apply] using hy1,
        by simpa +decide [q₀, Function.update_apply] using hywb,
        by simpa +decide [q₀, Function.update_apply] using hystr,
        by simpa +decide [q₀, Function.update_apply] using hyt,
        by simpa +decide [q₀, Function.update_apply] using hydst,
        by simp +decide [q₀, u],
        by simpa +decide [q₀, Function.update_apply, u] using hyidx,
        by simpa +decide [q₀, Function.update_apply, u] using hyrem,
        by simp +decide [q₀],
        hymod,
        fun i j hij => ?_⟩
      have hqv0 : q₀.regs vReg = 0 := by simp [q₀]
      rw [hqv0] at hij
      rcases hij with hlt_u | ⟨_, hlt0⟩
      · exact hydone i j hlt_u
      · omega
    obtain ⟨q₁, hex_inner, hq₁, hc_inner_exit⟩ :=
      ExecWithin.loop_invariant InnerI (fun q => t - q.regs vReg) hcol_body hq₀_inv
    rcases hq₁ with ⟨hq1, hqwb, hqstr, hqt, hqdst, hqu, hqidx, hqrem, hqv_le, hqmod, hqdone⟩
    have hqv_eq : q₁.regs vReg = t := by
      simp only [Cond.holds_lt, hqt, not_lt] at hc_inner_exit
      omega
    have hfit_idx_next : Fits w (wb + u.val * str + str) :=
      hwEnd.of_le (by
        have hle : u.val * str + str ≤ str * t := by
          calc
            u.val * str + str = (u.val + 1) * str := by ring
            _ ≤ t * str := Nat.mul_le_mul_right str u.isLt
            _ = str * t := Nat.mul_comm t str
        omega)
    have hfit_rem_next : Fits w (dstBase + u.val * t + t) :=
      hdstEnd.of_le (by
        have hle : u.val * t + t ≤ t * t := by
          calc
            u.val * t + t = (u.val + 1) * t := by ring
            _ ≤ t * t := Nat.mul_le_mul_right t u.isLt
        omega)
    have hfit_up1 : Fits w (u.val + 1) := hdstEnd.of_le (by
      have : t ≤ t * t := Nat.le_mul_self t
      have := u.isLt
      omega)
    let r₁ := q₁.set idx (wb + u.val * str + str)
    let r₂ := r₁.set rem (dstBase + u.val * t + t)
    let z := r₂.set uReg (u.val + 1)
    have hex_post : ExecWithin w copySubRowPost q₁ z 3 := by
      have s1 : ExecWithin w ram[idx ← idx + stride] q₁ r₁ 1 := by
        simpa [r₁, BinOp.eval, hqidx, hqstr] using
          ExecWithin.bin (f := .add) (d := idx) (i := idx) (j := stride) (x := q₁)
            (by simpa [BinOp.eval, hqidx, hqstr] using hfit_idx_next)
      have s2 : ExecWithin w ram[rem ← rem + targetT] r₁ r₂ 1 := by
        have hrem' : r₁.regs rem = dstBase + u.val * t := by
          simpa +decide [r₁, Function.update_apply] using hqrem
        have hqt' : r₁.regs targetT = t := by
          simpa +decide [r₁, Function.update_apply] using hqt
        simpa [r₂, BinOp.eval, hrem', hqt'] using
          ExecWithin.bin (f := .add) (d := rem) (i := rem) (j := targetT) (x := r₁)
            (by simpa [BinOp.eval, hrem', hqt'] using hfit_rem_next)
      have s3 : ExecWithin w ram[uReg ← uReg + one] r₂ z 1 := by
        have hu' : r₂.regs uReg = u.val := by
          simpa +decide [r₂, r₁, Function.update_apply] using hqu
        have h1' : r₂.regs one = 1 := by
          simpa +decide [r₂, r₁, Function.update_apply] using hq1
        simpa [z, BinOp.eval, hu', h1'] using
          ExecWithin.bin (f := .add) (d := uReg) (i := uReg) (j := one) (x := r₂)
            (by simpa [BinOp.eval, hu', h1'] using hfit_up1)
      unfold copySubRowPost
      exact (s1.seq (s2.seq s3)).mono (by omega)
    have hz_u : z.regs uReg = u.val + 1 := by simp [z]
    have hz_inv : OuterI z := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hqmod, ?_⟩
      · simpa +decide [z, r₂, r₁, Function.update_apply] using hq1
      · simpa +decide [z, r₂, r₁, Function.update_apply] using hqwb
      · simpa +decide [z, r₂, r₁, Function.update_apply] using hqstr
      · simpa +decide [z, r₂, r₁, Function.update_apply] using hqt
      · simpa +decide [z, r₂, r₁, Function.update_apply] using hqdst
      · rw [hz_u]; exact u.isLt
      · rw [hz_u]
        simp +decide only [z, r₂, r₁, Data.set_regs, Function.update_apply, ↓reduceIte]
        ring
      · rw [hz_u]
        simp +decide only [z, r₂, r₁, Data.set_regs, Function.update_apply, ↓reduceIte]
        ring
      · intro i j hij
        rw [hz_u] at hij
        apply hqdone i j
        rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt_u | heq_u
        · exact Or.inl hlt_u
        · exact Or.inr ⟨Fin.ext heq_u, hqv_eq ▸ j.isLt⟩
    have hz_dec : t - z.regs uReg < t - y.regs uReg := by
      rw [hz_u]
      exact Nat.sub_lt_sub_left hu_lt (Nat.lt_succ_self _)
    refine ⟨z, ?_, hz_inv, hz_dec⟩
    have hqv0 : q₀.regs vReg = 0 := by simp [q₀]
    have hrow_seq : ExecWithin w copySubRowBody y z
        (1 + (((t - q₀.regs vReg) * (5 + 2) + 2) + 3)) :=
      hq₀_exec.seq (hex_inner.seq hex_post)
    refine hrow_seq.mono ?_
    rw [hqv0]
    omega
  let x₀ := ((x.set idx wb).set rem dstBase).set uReg 0
  have hx₀_exec : ExecWithin w copySubPre x x₀ 3 := by
    have hzero := fits_zero w
    have e1 : ExecWithin (B := .standard) w ram[idx ← wBase] x (x.set idx wb) 1 := by
      simpa [hwBase] using
        (Exec.copy (B := .standard) (w := w) (d := idx) (s := wBase) (x := x)).within
    have e2 : ExecWithin (B := .standard) w ram[rem ← addr2] (x.set idx wb)
        ((x.set idx wb).set rem dstBase) 1 := by
      have ha2 : (x.set idx wb).regs addr2 = dstBase := by
        simpa +decide [Function.update_apply] using hdst
      simpa [ha2] using
        (Exec.copy (B := .standard) (w := w) (d := rem) (s := addr2) (x := x.set idx wb)).within
    have e3 : ExecWithin (B := .standard) w ram[uReg ← #0] ((x.set idx wb).set rem dstBase) x₀ 1 :=
      ExecWithin.const hzero
    unfold copySubPre
    exact (e1.seq (e2.seq e3)).mono (by omega)
  have hx₀_inv : OuterI x₀ := by
    refine ⟨by simpa +decide [x₀, Function.update_apply] using hone,
      by simpa +decide [x₀, Function.update_apply] using hwBase,
      by simpa +decide [x₀, Function.update_apply] using hstride,
      by simpa +decide [x₀, Function.update_apply] using htargetT,
      by simpa +decide [x₀, Function.update_apply] using hdst,
      by simp +decide [x₀],
      by simp +decide [x₀],
      by simp +decide [x₀],
      Modifies.refl _ _,
      fun i j hij => ?_⟩
    have hu0 : x₀.regs uReg = 0 := by simp [x₀]
    rw [hu0] at hij
    omega
  obtain ⟨y, hex_outer, hy, hc_outer_exit⟩ :=
    ExecWithin.loop_invariant OuterI (fun z => t - z.regs uReg) houter_body hx₀_inv
  rcases hy with ⟨hy1, hywb, hystr, hyt, hydst, hyu_le, _, _, hymod, hydone⟩
  have hyu_eq : y.regs uReg = t := by
    simp only [Cond.holds_lt, hyt, not_lt] at hc_outer_exit
    omega
  have htot_exec : ExecWithin w copySubmatrixCode x y (7 * t ^ 2 + 8 * t + 5) := by
    have hu0 : x₀.regs uReg = 0 := by simp [x₀]
    have hseq : ExecWithin w copySubmatrixCode x y
        (3 + ((t - x₀.regs uReg) * (7 * t + 6 + 2) + 2)) :=
      hx₀_exec.seq hex_outer
    refine hseq.mono ?_
    rw [hu0, Nat.sub_zero]
    exact le_of_eq (by ring)
  have ⟨_, _, he⟩ := htot_exec
  have hpres : ∀ j : Fin 24, copySubmatrixCode.Preserves j → y.regs j = x.regs j :=
    fun j hj => he.regs_eq hj
  refine ⟨y, htot_exec, fun i j => hydone i j (hyu_eq ▸ i.isLt), hymod,
    hy1, hywb, hpres dBase (by decide), hystr,
    hpres activeK (by decide), hyt, hydst,
    fun j hj => ?_⟩
  have : j = srcBase ∨ j = nOrig ∨ j = fpReg ∨ j = spReg ∨
      j = retVal ∨ j = numTrials ∨ j = trialIdx ∨ j = bestVal := by
    fin_cases j <;> simp_all
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact hpres _ (by decide)

/-- Contracting a multigraph never increases `totalDoubledWeight`. -/
theorem totalDoubledWeight_le_of_isContractionOf {n k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {part : Fin n → Fin k} {W : Fin k → Fin k → ℕ} (hC : IsContractionOf W₀ part W) :
    totalDoubledWeight W ≤ totalDoubledWeight W₀ := by
  unfold totalDoubledWeight
  calc
    ∑ a : Fin k, rowDeg W a
      = ∑ a : Fin k, cutWeight W₀ (pullbackCut part {a}) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← cutWeight_singleton hC.multigraph a, cutWeight_pullbackCut hC]
    _ ≤ ∑ a : Fin k, ∑ x ∈ pullbackCut part {a}, rowDeg W₀ x :=
          Finset.sum_le_sum fun a _ => cutWeight_le_sum_rowDeg W₀ _
    _ = ∑ x : Fin n, rowDeg W₀ x := by
          rw [← Finset.sum_biUnion]
          · refine Finset.sum_congr ?_ fun _ _ => rfl
            ext x
            simp [pullbackCut]
          · intro a _ b _ hab
            simp only [Finset.disjoint_left, mem_pullbackCut, Finset.mem_singleton]
            rintro x rfl hxb
            exact hab hxb

end Subroutines

/-! ### Explicit iterative call-stack machine for `FastCut` (`r = 24`)

Each active frame at base address `fp` for a `k`-supervertex subproblem (`frameSize k =
4 + 2 * (k * k) + k`) lays out its immutable data first and its mutable workspace second:
* `mem[fp + 0] = parentFp` (immutable during this frame),
* `mem[fp + 1] = k` (immutable during this frame),
* `[fp + 2, fp + 2 + k * k)`: immutable `k × k` matrix `W_k` (stride `k`),
* `mem[fp + 2 + k * k] = stage` (`0`, `1`, or `2`),
* `mem[fp + 3 + k * k] = savedVal1` (Branch 1's returned cut weight),
* `[fp + 4 + k * k, fp + 4 + 2 * (k * k))`: working `k × k` contraction matrix (`wBase`),
* `[fp + 4 + 2 * (k * k), fp + frameSize k)`: working `k`-word degree buffer (`dBase`),
* `childFp = fp + frameSize k`: child frame pushed by Stages `0` and `1`.

Consequently, executing a frame at `fp` (including all of its recursive descendants) modifies only
`Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)`, leaving `parentFp`, `k`, `W_k`, and every
ancestor frame below `fp` untouched. -/

section FrameMachine

open KSReg

/-- Frame-dispatch header: load `activeK = k = mem[fp + 1]`, compute `rem = k * k`,
`addr1 = fp + 2`, and `addr2 = fp + 2 + k * k`, load `val2 = stage = mem[addr2]`, and set
`val1 = 7`. -/
def stepHeader : Code .standard 24 := ram[
  zero ← #0;
  one ← #1;
  addr1 ← fpReg + one;
  activeK ← *addr1;
  rem ← activeK * activeK;
  addr1 ← addr1 + one;
  addr2 ← addr1 + rem;
  val2 ← *addr2;
  val1 ← #7
]

/-- Base-case workspace pointer setup (`2 ≤ k ≤ 6`): set `uReg = fp + 2`, `wBase = fp + 4 + k * k`,
`dBase = wBase + k * k`, `stride = k`, and `targetT = 2`. -/
def basePre : Code .standard 24 := ram[
  uReg ← addr1;
  val1 ← #2;
  wBase ← addr2 + val1;
  dBase ← wBase + rem;
  stride ← activeK;
  targetT ← #2
]

/-- Base-case epilogue: read `retVal = mem[wBase + 1]` and pop the frame (`fpReg ← mem[fpReg]`,
`spReg ← spReg - 1`). -/
def basePost : Code .standard 24 := ram[
  zero ← #0;
  one ← #1;
  addr1 ← wBase + one;
  retVal ← *addr1;
  fpReg ← *fpReg;
  spReg ← spReg - one
]

/-- Base-case execution (`2 ≤ k ≤ 6`): copy `W_k` to `wBase`, compute degrees, contract once down to
`2` supervertices, read `W'[0, 1]`, and pop the frame. -/
def baseCaseAndPop : Code .standard 24 := ram[
  ⟪basePre⟫;
  ⟪ksCopyCode⟫;
  ⟪computeDegreesAndTotalAt (by decide)⟫;
  ⟪contractDownToAt (by decide)⟫;
  ⟪basePost⟫
]

/-- Stage `0` update (`7 ≤ k`): set `mem[fp + 2 + k * k] ← 1` before contracting Branch 1. -/
def stageZeroSet : Code .standard 24 := ram[
  *addr2 ← one
]

/-- Stage `1` update (`7 ≤ k`): set `mem[fp + 2 + k * k] ← 2` and save `retVal` into
`mem[fp + 3 + k * k]` before contracting Branch 2. -/
def stageOneSaveAndSet : Code .standard 24 := ram[
  val1 ← #2;
  *addr2 ← val1;
  addr1 ← addr2 + one;
  *addr1 ← retVal
]

/-- Workspace setup for `branchContractAndPush` (`7 ≤ k`). -/
def branchSetup : Code .standard 24 := ram[
  val1 ← #2;
  uReg ← fpReg + val1;
  rem ← activeK * activeK;
  val1 ← #4;
  wBase ← fpReg + val1;
  wBase ← wBase + rem;
  dBase ← wBase + rem;
  stride ← activeK
]

/-- Destination setup before compacting the contracted `t × t` submatrix into `childFp + 2`. -/
def branchCompactPre : Code .standard 24 := ram[
  one ← #1;
  val2 ← dBase + stride;
  val1 ← #2;
  addr2 ← val2 + val1
]

/-- Initialize the child frame header at `childFp = dBase + stride` (`parentFp = fp`, `k_child = t`,
`stage_child = 0`) and push `(fpReg, spReg) ← (childFp, spReg + 1)`. -/
def branchPushChild : Code .standard 24 := ram[
  zero ← #0;
  one ← #1;
  addr1 ← dBase + stride;
  *addr1 ← fpReg;
  addr2 ← addr1 + one;
  *addr2 ← targetT;
  rem ← targetT * targetT;
  addr2 ← addr2 + one;
  addr2 ← addr2 + rem;
  *addr2 ← zero;
  fpReg ← addr1;
  spReg ← spReg + one
]

/-- Deterministic tail of `branchContractAndPush`: compact the `t × t` contracted submatrix into
`childFp + 2` and push the child frame header at `childFp`. -/
def branchTail : Code .standard 24 := ram[
  ⟪branchCompactPre⟫;
  ⟪copySubmatrixCode⟫;
  ⟪branchPushChild⟫
]

/-- Shared Branch 1 / Branch 2 contraction-and-push body (`7 ≤ k`): compute
`t = fastCutThreshold k`, copy `W_k` to `wBase`, compute degrees, contract down to `t`, compact the
`t × t` submatrix into `childFp + 2`, and push the child frame at `childFp = fp + frameSize k`. -/
def branchContractAndPush : Code .standard 24 := ram[
  ⟪thresholdCode⟫;
  ⟪branchSetup⟫;
  ⟪ksCopyCode⟫;
  ⟪computeDegreesAndTotalAt (by decide)⟫;
  ⟪contractDownToAt (by decide)⟫;
  ⟪branchTail⟫
]

/-- Stage `2` epilogue (`7 ≤ k`): set `retVal ← min savedVal1 retVal` and pop the frame. -/
def combineAndPop : Code .standard 24 := ram[
  addr1 ← addr2 + one;
  val1 ← *addr1;
  if val1 < retVal then [
    retVal ← val1
  ] else [
    zero ← #0
  ];
  fpReg ← *fpReg;
  spReg ← spReg - one
]

/-- Single iteration body of the explicit-stack `FastCut` loop. -/
def fastCutStep : Code .standard 24 := ram[
  ⟪stepHeader⟫;
  if activeK < val1 then [
    ⟪baseCaseAndPop⟫
  ] else [
    if val2 = zero then [
      ⟪stageZeroSet⟫;
      ⟪branchContractAndPush⟫
    ] else [
      if val2 = one then [
        ⟪stageOneSaveAndSet⟫;
        ⟪branchContractAndPush⟫
      ] else [
        ⟪combineAndPop⟫
      ]
    ]
  ]
]

/-- Outer explicit-stack `while` loop executing all active frames down to `spReg = 0`. -/
def fastCutLoop : Code .standard 24 := ram[
  while zero < spReg do [ ⟪fastCutStep⟫ ]
]

theorem stepHeader_exec {w fp k stg : ℕ} {x : Data 24} (hk2 : 2 ≤ k)
    (hfp : x.regs fpReg = fp) (hmem_k : x.mem (fp + 1) = k)
    (hmem_stg : x.mem (fp + 2 + k * k) = stg)
    (hfit : Fits w (fp + frameSize k)) :
    ∃ y : Data 24, Exec w stepHeader x y 9 ∧
      y.mem = x.mem ∧
      y.regs zero = 0 ∧
      y.regs one = 1 ∧
      y.regs activeK = k ∧
      y.regs rem = k * k ∧
      y.regs addr1 = fp + 2 ∧
      y.regs addr2 = fp + 2 + k * k ∧
      y.regs val2 = stg ∧
      y.regs val1 = 7 ∧
      (∀ j : Fin 24, 16 ≤ j.val → y.regs j = x.regs j) := by
  have hfs : 14 ≤ frameSize k := by
    unfold frameSize
    have : 4 ≤ k * k := Nat.mul_le_mul hk2 hk2
    omega
  have h0 : Fits w 0 := fits_zero w
  have h1 : Fits w 1 := hfit.of_le (by omega)
  have h7 : Fits w 7 := hfit.of_le (by omega)
  have hfp1 : Fits w (fp + 1) := hfit.of_le (by unfold frameSize; omega)
  have hfp2 : Fits w (fp + 2) := hfit.of_le (by unfold frameSize; omega)
  have hkk : Fits w (k * k) := hfit.of_le (by unfold frameSize; omega)
  have hstg_addr : Fits w (fp + 2 + k * k) := hfit.of_le (by unfold frameSize; omega)
  let s₁ := x.set zero 0
  let s₂ := s₁.set one 1
  let s₃ := s₂.set addr1 (fp + 1)
  let s₄ := s₃.set activeK k
  let s₅ := s₄.set rem (k * k)
  let s₆ := s₅.set addr1 (fp + 2)
  let s₇ := s₆.set addr2 (fp + 2 + k * k)
  let s₈ := s₇.set val2 stg
  let y := s₈.set val1 7
  have e1 : Exec (B := .standard) w ram[zero ← #0] x s₁ 1 := Exec.const h0
  have e2 : Exec (B := .standard) w ram[one ← #1] s₁ s₂ 1 := Exec.const h1
  have e3 : Exec w ram[addr1 ← fpReg + one] s₂ s₃ 1 := by
    have hfp' : s₂.regs fpReg = fp := by simpa +decide [s₂, s₁, Function.update_apply] using hfp
    have h1' : s₂.regs one = 1 := by simp [s₂]
    simpa [s₃, BinOp.eval, hfp', h1'] using
      Exec.bin (f := .add) (d := addr1) (i := fpReg) (j := one) (x := s₂)
        (by simpa [BinOp.eval, hfp', h1'] using hfp1)
  have e4 : Exec (B := .standard) w ram[activeK ← *addr1] s₃ s₄ 1 := by
    have ha1 : s₃.regs addr1 = fp + 1 := by simp [s₃]
    have hm1 : s₃.mem (fp + 1) = k := hmem_k
    simpa [s₄, ha1, hm1] using Exec.load (B := .standard) (w := w) (d := activeK) (a := addr1)
      (x := s₃)
  have e5 : Exec w ram[rem ← activeK * activeK] s₄ s₅ 1 := by
    have hk' : s₄.regs activeK = k := by simp [s₄]
    simpa [s₅, BinOp.eval, hk'] using
      Exec.bin (f := .mul) (d := rem) (i := activeK) (j := activeK) (x := s₄)
        (by simpa [BinOp.eval, hk'] using hkk)
  have e6 : Exec w ram[addr1 ← addr1 + one] s₅ s₆ 1 := by
    have ha1 : s₅.regs addr1 = fp + 1 := by simp +decide [s₅, s₄, s₃]
    have h1' : s₅.regs one = 1 := by simp +decide [s₅, s₄, s₃, s₂]
    have heq : (fp + 1) + 1 = fp + 2 := by omega
    simpa [s₆, BinOp.eval, ha1, h1', heq] using
      Exec.bin (f := .add) (d := addr1) (i := addr1) (j := one) (x := s₅)
        (by simpa [BinOp.eval, ha1, h1', heq] using hfp2)
  have e7 : Exec w ram[addr2 ← addr1 + rem] s₆ s₇ 1 := by
    have ha1 : s₆.regs addr1 = fp + 2 := by simp [s₆]
    have hr' : s₆.regs rem = k * k := by simp +decide [s₆, s₅]
    simpa [s₇, BinOp.eval, ha1, hr'] using
      Exec.bin (f := .add) (d := addr2) (i := addr1) (j := rem) (x := s₆)
        (by simpa [BinOp.eval, ha1, hr'] using hstg_addr)
  have e8 : Exec (B := .standard) w ram[val2 ← *addr2] s₇ s₈ 1 := by
    have ha2 : s₇.regs addr2 = fp + 2 + k * k := by simp [s₇]
    have hm2 : s₇.mem (fp + 2 + k * k) = stg := hmem_stg
    simpa [s₈, ha2, hm2] using Exec.load (B := .standard) (w := w) (d := val2) (a := addr2)
      (x := s₇)
  have e9 : Exec (B := .standard) w ram[val1 ← #7] s₈ y 1 := Exec.const h7
  have hex : Exec w stepHeader x y 9 := by
    unfold stepHeader
    exact e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq e9)))))))
  have hpres : ∀ j : Fin 24, stepHeader.Preserves j → y.regs j = x.regs j :=
    fun j hj => hex.regs_eq hj
  refine ⟨y, hex, rfl,
    by simp +decide [y, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁],
    by simp +decide [y, s₈, s₇, s₆, s₅, s₄, s₃, s₂],
    by simp +decide [y, s₈, s₇, s₆, s₅, s₄],
    by simp +decide [y, s₈, s₇, s₆, s₅],
    by simp +decide [y, s₈, s₇, s₆],
    by simp +decide [y, s₈, s₇],
    by simp +decide [y, s₈],
    by simp [y],
    fun j hj => ?_⟩
  have : j = srcBase ∨ j = nOrig ∨ j = fpReg ∨ j = spReg ∨
      j = retVal ∨ j = numTrials ∨ j = trialIdx ∨ j = bestVal := by
    fin_cases j <;> simp_all
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact hpres _ (by decide)

theorem combineAndPop_exec {w fp parentFp b k v1 r2 : ℕ} {x : Data 24}
    (hk2 : 2 ≤ k) (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (ha2 : x.regs addr2 = fp + 2 + k * k)
    (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1) (hr2 : x.regs retVal = r2)
    (hmem_p : x.mem fp = parentFp) (hmem_v1 : x.mem (fp + 3 + k * k) = v1)
    (hfit : Fits w (fp + frameSize k)) (hsp_fit : Fits w b) :
    ∃ y : Data 24, ExecWithin w combineAndPop x y 7 ∧
      y.mem = x.mem ∧
      y.regs zero = 0 ∧
      y.regs fpReg = parentFp ∧
      y.regs spReg = b ∧
      y.regs retVal = min v1 r2 := by
  have ha1_fit : Fits w (fp + 3 + k * k) := hfit.of_le (by
    unfold frameSize
    have : 4 ≤ k * k := Nat.mul_le_mul hk2 hk2
    omega)
  let s₁ := x.set addr1 (fp + 3 + k * k)
  let s₂ := s₁.set val1 v1
  have e1 : ExecWithin w ram[addr1 ← addr2 + one] x s₁ 1 := by
    have heq : (fp + 2 + k * k) + 1 = fp + 3 + k * k := by omega
    simpa [s₁, BinOp.eval, ha2, h1, heq] using
      ExecWithin.bin (f := .add) (d := addr1) (i := addr2) (j := one) (x := x)
        (by simpa [BinOp.eval, ha2, h1, heq] using ha1_fit)
  have e2 : ExecWithin (B := .standard) w ram[val1 ← *addr1] s₁ s₂ 1 := by
    have ha1' : s₁.regs addr1 = fp + 3 + k * k := by simp [s₁]
    have hm1 : s₁.mem (fp + 3 + k * k) = v1 := hmem_v1
    simpa [s₂, ha1', hm1] using ExecWithin.load (B := .standard) (w := w) (d := val1) (a := addr1)
      (x := s₁)
  have hbr : ∃ s₃ : Data 24,
      ExecWithin (B := .standard) w
        ram[if val1 < retVal then [ retVal ← val1 ] else [ zero ← #0 ]] s₂ s₃ 3 ∧
      s₃.mem = x.mem ∧
      s₃.regs zero = 0 ∧
      s₃.regs one = 1 ∧
      s₃.regs fpReg = fp ∧
      s₃.regs spReg = b + 1 ∧
      s₃.regs retVal = min v1 r2 := by
    have hs2_v1 : s₂.regs val1 = v1 := by simp [s₂]
    have hs2_r2 : s₂.regs retVal = r2 := by
      simpa +decide [s₂, s₁, Function.update_apply] using hr2
    by_cases hlt : v1 < r2
    · have hc : (Cond.lt val1 retVal).Holds s₂ := by
        simpa [Cond.holds_lt, hs2_v1, hs2_r2] using hlt
      let s₃ := s₂.set retVal v1
      have e_pos : ExecWithin (B := .standard) w ram[retVal ← val1] s₂ s₃ 1 := by
        simpa [s₃, hs2_v1] using
          (Exec.copy (B := .standard) (w := w) (d := retVal) (s := val1) (x := s₂)).within
      refine ⟨s₃, (ExecWithin.branch_pos hc e_pos).mono (by omega), rfl,
        by simpa +decide [s₃, s₂, s₁, Function.update_apply] using h0,
        by simpa +decide [s₃, s₂, s₁, Function.update_apply] using h1,
        by simpa +decide [s₃, s₂, s₁, Function.update_apply] using hfp,
        by simpa +decide [s₃, s₂, s₁, Function.update_apply] using hsp, ?_⟩
      simp only [s₃, Data.set_regs, Function.update_self]
      omega
    · have hnc : ¬(Cond.lt val1 retVal).Holds s₂ := by
        simpa [Cond.holds_lt, hs2_v1, hs2_r2] using hlt
      let s₃ := s₂.set zero 0
      have e_neg : ExecWithin (B := .standard) w ram[zero ← #0] s₂ s₃ 1 :=
        ExecWithin.const (fits_zero w)
      refine ⟨s₃, (ExecWithin.branch_neg hnc e_neg).mono (by omega), rfl,
        by simp [s₃],
        by simpa +decide [s₃, s₂, s₁, Function.update_apply] using h1,
        by simpa +decide [s₃, s₂, s₁, Function.update_apply] using hfp,
        by simpa +decide [s₃, s₂, s₁, Function.update_apply] using hsp, ?_⟩
      have hr3 : s₃.regs retVal = r2 := by
        simpa +decide [s₃, Function.update_apply] using hs2_r2
      rw [hr3]
      omega
  obtain ⟨s₃, e3, hs3_mem, hs3_0, hs3_1, hs3_fp, hs3_sp, hs3_ret⟩ := hbr
  let s₄ := s₃.set fpReg parentFp
  let s₅ := s₄.set spReg b
  have e4 : ExecWithin (B := .standard) w ram[fpReg ← *fpReg] s₃ s₄ 1 := by
    have hm : s₃.mem fp = parentFp := hs3_mem ▸ hmem_p
    simpa [s₄, hs3_fp, hm] using
      ExecWithin.load (B := .standard) (w := w) (d := fpReg) (a := fpReg) (x := s₃)
  have e5 : ExecWithin w ram[spReg ← spReg - one] s₄ s₅ 1 := by
    have hsp' : s₄.regs spReg = b + 1 := by
      simpa +decide [s₄, Function.update_apply] using hs3_sp
    have h1' : s₄.regs one = 1 := by
      simpa +decide [s₄, Function.update_apply] using hs3_1
    have hsub : (b + 1) - 1 = b := by omega
    simpa [s₅, BinOp.eval, hsp', h1', hsub] using
      ExecWithin.bin (f := .sub) (d := spReg) (i := spReg) (j := one) (x := s₄)
        (by simpa [BinOp.eval, hsp', h1', hsub] using hsp_fit)
  refine ⟨s₅, ?_, hs3_mem,
    by simpa +decide [s₅, s₄, Function.update_apply] using hs3_0,
    by simp +decide [s₅, s₄],
    by simp [s₅],
    by simpa +decide [s₅, s₄, Function.update_apply] using hs3_ret⟩
  unfold combineAndPop
  exact (e1.seq (e2.seq (e3.seq (e4.seq e5)))).mono (by omega)

theorem baseCaseAndPop_spec {n w fp parentFp b k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    (hk2 : 2 ≤ k) (hk6 : k ≤ 6)
    (hk_reg : x.regs activeK = k) (hrem_reg : x.regs rem = k * k)
    (ha1_reg : x.regs addr1 = fp + 2) (ha2_reg : x.regs addr2 = fp + 2 + k * k)
    (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1)
    (hmem_p : x.mem fp = parentFp) (hmat : HoldsMatrix x.mem (fp + 2) k W_k)
    (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + frameSize k)) (hsp_fit : Fits w b)
    (htot : Fits w (totalDoubledWeight W₀)) :
    ∃ m : ProbComp (Data 24 × ℕ),
      ExecRand w baseCaseAndPop x m ∧
      m.IsQueryBounded (k - 2) ∧
      (∀ z ∈ m.support,
        z.2 ≤ 2000 ∧
        Modifies (Finset.Ico (fp + 2 + k * k) (fp + frameSize k)) x.mem z.1.mem ∧
        z.1.regs zero = 0 ∧
        z.1.regs fpReg = parentFp ∧
        z.1.regs spReg = b ∧
        ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ z.1.regs retVal = cutWeight W₀ C) ∧
      (∀ B : Finset (Fin k),
        0 < minCut W₀ → IsNonTrivialCut B →
        cutWeight W₀ (pullbackCut part B) = minCut W₀ →
        (2 : ℝ≥0∞) / (30 : ℝ≥0∞) ≤
          m.eval.toOuterMeasure {z | z.1.regs retVal = minCut W₀}) := by
  let wb := fp + 4 + k * k
  let db := fp + 4 + 2 * (k * k)
  have hfs_eq : fp + frameSize k = db + k := by
    dsimp only [db]
    unfold frameSize
    omega
  have hkk_ge : 4 ≤ k * k := Nat.mul_le_mul hk2 hk2
  have hkk_le : k * k ≤ 36 := Nat.mul_le_mul hk6 hk6
  have h1 : Fits w 1 := hfit.of_le (by rw [hfs_eq]; dsimp only [db]; omega)
  have h2 : Fits w 2 := hfit.of_le (by rw [hfs_eq]; dsimp only [db]; omega)
  have hwb_fit : Fits w wb := hfit.of_le (by rw [hfs_eq]; dsimp only [wb, db]; omega)
  have hdb_fit : Fits w db := hfit.of_le (by rw [hfs_eq]; omega)
  have hdEnd_fit : Fits w (db + k) := hfs_eq ▸ hfit
  have htot_k : Fits w (totalDoubledWeight W_k) :=
    htot.of_le (totalDoubledWeight_le_of_isContractionOf hC)
  -- Step 1: `basePre`
  let p₁ := x.set uReg (fp + 2)
  let p₂ := p₁.set val1 2
  let p₃ := p₂.set wBase wb
  let p₄ := p₃.set dBase db
  let p₅ := p₄.set stride k
  let x_pre := p₅.set targetT 2
  have hex_pre : Exec w basePre x x_pre 6 := by
    have s1 : Exec (B := .standard) w ram[uReg ← addr1] x p₁ 1 := by
      simpa [p₁, ha1_reg] using
        Exec.copy (B := .standard) (w := w) (d := uReg) (s := addr1) (x := x)
    have s2 : Exec (B := .standard) w ram[val1 ← #2] p₁ p₂ 1 := Exec.const h2
    have s3 : Exec w ram[wBase ← addr2 + val1] p₂ p₃ 1 := by
      have ha2' : p₂.regs addr2 = fp + 2 + k * k := by
        simpa +decide [p₂, p₁, Function.update_apply] using ha2_reg
      have hv1' : p₂.regs val1 = 2 := by simp [p₂]
      have heq : (fp + 2 + k * k) + 2 = wb := by dsimp only [wb]; omega
      simpa [p₃, BinOp.eval, ha2', hv1', heq] using
        Exec.bin (f := .add) (d := wBase) (i := addr2) (j := val1) (x := p₂)
          (by simpa [BinOp.eval, ha2', hv1', heq] using hwb_fit)
    have s4 : Exec w ram[dBase ← wBase + rem] p₃ p₄ 1 := by
      have hwb' : p₃.regs wBase = wb := by simp [p₃]
      have hr' : p₃.regs rem = k * k := by
        simpa +decide [p₃, p₂, p₁, Function.update_apply] using hrem_reg
      have heq : wb + k * k = db := by dsimp only [wb, db]; omega
      simpa [p₄, BinOp.eval, hwb', hr', heq] using
        Exec.bin (f := .add) (d := dBase) (i := wBase) (j := rem) (x := p₃)
          (by simpa [BinOp.eval, hwb', hr', heq] using hdb_fit)
    have s5 : Exec (B := .standard) w ram[stride ← activeK] p₄ p₅ 1 := by
      have hk' : p₄.regs activeK = k := by
        simpa +decide [p₄, p₃, p₂, p₁, Function.update_apply] using hk_reg
      simpa [p₅, hk'] using Exec.copy (B := .standard) (w := w) (d := stride) (s := activeK)
        (x := p₄)
    have s6 : Exec (B := .standard) w ram[targetT ← #2] p₅ x_pre 1 := Exec.const h2
    unfold basePre
    exact s1.seq (s2.seq (s3.seq (s4.seq (s5.seq s6))))
  -- Step 2: `ksCopyCode`
  have hd_eq : wb + k * k = db := by dsimp only [wb, db]; omega
  obtain ⟨x_cp, ⟨n_cp, hn_cp, hex_cp⟩, hmat_cp, hmod_cp, _, hwb_cp, hdb_cp, hstr_cp, hk_cp,
      ht_cp, hhi_cp⟩ :=
    ksCopyCode_exec (x := x_pre) (sb := fp + 2) (db := wb) (k := k) (W := W_k)
      (by simp +decide [x_pre, p₅, p₄, p₃, p₂, p₁])
      (by simp +decide [x_pre, p₅, p₄, p₃])
      (by simpa +decide [x_pre, p₅, p₄, p₃, p₂, p₁, Function.update_apply] using hrem_reg)
      (by dsimp only [wb]; omega) h1 (hd_eq ▸ hdb_fit) hmat
  have hdb_cp' : x_cp.regs dBase = db := by
    rw [hdb_cp]; simp +decide [x_pre, p₅, p₄]
  have hstr_cp' : x_cp.regs stride = k := by
    rw [hstr_cp]; simp +decide [x_pre, p₅]
  have hk_cp' : x_cp.regs activeK = k := by
    rw [hk_cp]; simpa +decide [x_pre, p₅, p₄, p₃, p₂, p₁, Function.update_apply] using hk_reg
  have ht_cp' : x_cp.regs targetT = 2 := by
    rw [ht_cp]; simp [x_pre]
  -- Step 3: `computeDegreesAndTotalAt hr24`
  obtain ⟨x_deg, ⟨n_deg, hn_deg, hex_deg⟩, hws_deg, hmod_deg, hwb_deg, hdb_deg, hstr_deg, hk_deg,
      ht_deg, htot_deg, hhi_deg⟩ :=
    computeDegreesAndTotalAt_exec hr24 (x := x_cp) (wb := wb) (db := db) (str := k) (k := k)
      (W := W_k) hwb_cp hdb_cp' hstr_cp' hk_cp' (le_refl k) (Or.inl (by dsimp only [wb, db]; omega))
      h1 (hd_eq ▸ hdb_fit) hdEnd_fit htot_k hmat_cp
  have hfp_deg : x_deg.regs fpReg = fp := by
    rw [hhi_deg fpReg (by decide), hhi_cp fpReg (by decide)]
    simpa +decide [x_pre, p₅, p₄, p₃, p₂, p₁, Function.update_apply] using hfp
  have hsp_deg : x_deg.regs spReg = b + 1 := by
    rw [hhi_deg spReg (by decide), hhi_cp spReg (by decide)]
    simpa +decide [x_pre, p₅, p₄, p₃, p₂, p₁, Function.update_apply] using hsp
  have hst_deg : ContractState w wb db k k 2 W_k (x_deg.comap (Fin.castLE hr24)) := {
    regs_wBase := hwb_deg
    regs_dBase := hdb_deg
    regs_stride := hstr_deg
    regs_activeK := hk_deg
    regs_targetT := ht_deg.trans ht_cp'
    regs_totS := htot_deg
    le_stride := le_refl k
    disjoint_blocks := Or.inl (by dsimp only [wb, db]; omega)
    fits_wEnd := hd_eq ▸ hdb_fit
    fits_dEnd := hdEnd_fit
    fits_totS := htot_k
    workspace := hws_deg
  }
  -- Step 4: `contractDownToAt hr24`
  obtain ⟨m_c, hm_c, hq_c, hsup_c, hsurv_c⟩ :=
    contractDownToAt_spec hr24 (by decide : 2 ≤ 2) hk2 hC hst_deg
  -- Step 5: `basePost` on every supported output of `m_c`
  have hpost : ∀ z ∈ m_c.support, ∃ y : Data 24,
      ExecWithin w basePost z.1 y 6 ∧
      y.mem = z.1.mem ∧
      y.regs zero = 0 ∧
      y.regs fpReg = parentFp ∧
      y.regs spReg = b ∧
      y.regs retVal = z.1.mem (wb + 1) := by
    intro z hz
    rcases hsup_c z hz with ⟨_, hmod_c, hhi_c, _, _, _, hst_c⟩
    have hz_wb : z.1.regs wBase = wb := hst_c.regs_wBase
    have hz_fp : z.1.regs fpReg = fp := (hhi_c fpReg (by decide)).trans hfp_deg
    have hz_sp : z.1.regs spReg = b + 1 := (hhi_c spReg (by decide)).trans hsp_deg
    have hz_mem_p : z.1.mem fp = parentFp := by
      have h1_out : z.1.mem fp = x_deg.mem fp :=
        hmod_c fp (by
          simp only [workspaceFootprint, Finset.mem_union, Finset.mem_Ico, not_or]
          exact ⟨by dsimp only [wb]; omega, by dsimp only [db]; omega⟩)
      have h2_out : x_deg.mem fp = x_cp.mem fp :=
        hmod_deg fp (by rw [Finset.mem_Ico]; dsimp only [db]; omega)
      have h3_out : x_cp.mem fp = x.mem fp :=
        hmod_cp fp (by rw [Finset.mem_Ico]; dsimp only [wb]; omega)
      rw [h1_out, h2_out, h3_out, hmem_p]
    have hwb1_fit : Fits w (wb + 1) := hdEnd_fit.of_le (by dsimp only [wb, db]; omega)
    let q₁ := z.1.set zero 0
    let q₂ := q₁.set one 1
    let q₃ := q₂.set addr1 (wb + 1)
    let q₄ := q₃.set retVal (z.1.mem (wb + 1))
    let q₅ := q₄.set fpReg parentFp
    let y := q₅.set spReg b
    have b1 : ExecWithin (B := .standard) w ram[zero ← #0] z.1 q₁ 1 :=
      ExecWithin.const (fits_zero w)
    have b2 : ExecWithin (B := .standard) w ram[one ← #1] q₁ q₂ 1 := ExecWithin.const h1
    have b3 : ExecWithin w ram[addr1 ← wBase + one] q₂ q₃ 1 := by
      have hwb' : q₂.regs wBase = wb := by
        simpa +decide [q₂, q₁, Function.update_apply] using hz_wb
      have h1' : q₂.regs one = 1 := by simp [q₂]
      simpa [q₃, BinOp.eval, hwb', h1'] using
        ExecWithin.bin (f := .add) (d := addr1) (i := wBase) (j := one) (x := q₂)
          (by simpa [BinOp.eval, hwb', h1'] using hwb1_fit)
    have b4 : ExecWithin (B := .standard) w ram[retVal ← *addr1] q₃ q₄ 1 := by
      have ha1' : q₃.regs addr1 = wb + 1 := by simp [q₃]
      have hm_q3 : q₃.mem (wb + 1) = z.1.mem (wb + 1) := rfl
      simpa [q₄, ha1', hm_q3] using
        ExecWithin.load (B := .standard) (w := w) (d := retVal) (a := addr1) (x := q₃)
    have b5 : ExecWithin (B := .standard) w ram[fpReg ← *fpReg] q₄ q₅ 1 := by
      have hfp' : q₄.regs fpReg = fp := by
        simpa +decide [q₄, q₃, q₂, q₁, Function.update_apply] using hz_fp
      have hm_q4 : q₄.mem fp = parentFp := hz_mem_p
      simpa [q₅, hfp', hm_q4] using
        ExecWithin.load (B := .standard) (w := w) (d := fpReg) (a := fpReg) (x := q₄)
    have b6 : ExecWithin w ram[spReg ← spReg - one] q₅ y 1 := by
      have hsp' : q₅.regs spReg = b + 1 := by
        simpa +decide [q₅, q₄, q₃, q₂, q₁, Function.update_apply] using hz_sp
      have h1' : q₅.regs one = 1 := by simp +decide [q₅, q₄, q₃, q₂]
      have hsub : (b + 1) - 1 = b := by omega
      simpa [y, BinOp.eval, hsp', h1', hsub] using
        ExecWithin.bin (f := .sub) (d := spReg) (i := spReg) (j := one) (x := q₅)
          (by simpa [BinOp.eval, hsp', h1', hsub] using hsp_fit)
    refine ⟨y, ?_, rfl,
      by simp +decide [y, q₅, q₄, q₃, q₂, q₁],
      by simp +decide [y, q₅],
      by simp [y],
      by simp +decide [y, q₅, q₄]⟩
    unfold basePost
    exact (b1.seq (b2.seq (b3.seq (b4.seq (b5.seq b6))))).mono (by omega)
  obtain ⟨g, hseq_post, hg⟩ := execRand_seq_det
    (Q := fun d y => y.mem = d.mem ∧ y.regs zero = 0 ∧ y.regs fpReg = parentFp ∧
      y.regs spReg = b ∧ y.regs retVal = d.mem (wb + 1))
    hm_c hpost
  have hfull_raw := hex_pre.seqRand (hex_cp.seqRand (hex_deg.seqRand hseq_post))
  let m_out : ProbComp (Data 24 × ℕ) :=
    (fun z => ((g z.1).1, 6 + (n_cp + (n_deg + (z.2 + (g z.1).2))))) <$> m_c
  have hfull : ExecRand w baseCaseAndPop x m_out := by
    unfold baseCaseAndPop
    convert hfull_raw using 1
    simp only [m_out, Functor.map_map]
  refine ⟨m_out, hfull, ?_, ?_, ?_⟩
  · simp only [m_out, OracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
    exact hq_c
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    rcases hsup_c z₀ hz₀ with ⟨ht_c, hmod_c, _, W', part', hC', hst_c⟩
    rcases hg z₀ hz₀ with ⟨ht_post, _, hmem_post, hz0, hzfp, hzsp, hzret⟩
    refine ⟨?_, ?_, hz0, hzfp, hzsp, ?_⟩
    · have hk2_le : k ^ 2 ≤ 36 := by simpa [sq] using hkk_le
      omega
    · rw [hmem_post]
      have hsub1 : Finset.Ico wb (wb + k * k) ⊆ Finset.Ico (fp + 2 + k * k) (fp + frameSize k) := by
        intro a ha; rw [Finset.mem_Ico] at ha ⊢; rw [hfs_eq]; dsimp only [wb, db] at ha ⊢; omega
      have hsub2 : Finset.Ico db (db + k) ⊆ Finset.Ico (fp + 2 + k * k) (fp + frameSize k) := by
        intro a ha; rw [Finset.mem_Ico] at ha ⊢; rw [hfs_eq]; dsimp only [db] at ha ⊢; omega
      have hsub3 : workspaceFootprint wb db k k ⊆
          Finset.Ico (fp + 2 + k * k) (fp + frameSize k) :=
        Finset.union_subset hsub1 hsub2
      exact modifies_trans_subset
        (modifies_trans_subset hmod_cp hmod_deg hsub1 hsub2) hmod_c Finset.Subset.rfl hsub3
    · rcases two_vertex_contraction_output hC' with ⟨hnt_out, hcw_out, _⟩
      refine ⟨pullbackCut part' ({0} : Finset (Fin 2)), hnt_out, ?_⟩
      have hcell : z₀.1.mem (wb + 1) = W' 0 1 := by simpa using hst_c.workspace.1 0 1
      rw [hzret, hcell, hcw_out]
  · intro B hmin_pos hB_nt hB_min
    have hprob := hsurv_c B hmin_pos hB_nt hB_min
    have h2_eq : (((2 * (2 - 1) : ℕ) : ℝ≥0∞) / ((k * (k - 1) : ℕ) : ℝ≥0∞)) =
        (2 : ℝ≥0∞) / ((k * (k - 1) : ℕ) : ℝ≥0∞) := by norm_num
    rw [h2_eq] at hprob
    have hbase := base_survival_ge hk2 hk6
    have hC_nt : IsNonTrivialCut (pullbackCut part B) :=
      isNonTrivialCut_pullbackCut hC.surj hB_nt
    rw [ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    refine (hbase.trans hprob).trans (toOuterMeasure_mono_support m_c fun z₀ hsup hz₀ => ?_)
    rcases hg z₀ hsup with ⟨_, _, _, _, _, _, hzret⟩
    change (g z₀.1).1.regs retVal = minCut W₀
    rw [hzret]
    exact survivalPost_two_mem_eq hC_nt hB_min hz₀

theorem frameSize_le_fastCutScratch (m : ℕ) :
    frameSize m ≤ fastCutScratch m := by
  by_cases hm : 7 ≤ m
  · rw [fastCutScratch_of_ge_seven hm]
    exact Nat.le_add_right _ _
  · rw [fastCutScratch_of_lt_seven (by omega)]

private theorem two_mul_pred_le_frameSize (k : ℕ) :
    2 * k * (k - 1) ≤ frameSize k := by
  unfold frameSize
  have hle : k * (k - 1) ≤ k * k := Nat.mul_le_mul_left k (Nat.sub_le k 1)
  have h2 : 2 * k * (k - 1) = 2 * (k * (k - 1)) := by ring
  omega

private theorem branch_step_bound {k t n_th n_cp n_deg n_c n_tail : ℕ}
    (hk7 : 7 ≤ k) (htk : t ≤ k)
    (hth : n_th ≤ 6 * k + 9)
    (hcp : n_cp ≤ 7 * (k * k) + 4)
    (hdeg : n_deg ≤ 6 * k ^ 2 + 12 * k + 6)
    (hc : n_c ≤ 36 * (k ^ 2 - t ^ 2) + 4)
    (htail : n_tail ≤ 7 * t ^ 2 + 8 * t + 21) :
    n_th + (8 + (n_cp + (n_deg + (n_c + n_tail)))) ≤ 80 * (k * k) := by
  have ht2_le : t ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left htk 2
  have hkk : k ^ 2 = k * k := sq k
  have hc' : n_c + 7 * t ^ 2 ≤ 36 * (k * k) + 4 := by
    have : 36 * (k ^ 2 - t ^ 2) + 7 * t ^ 2 ≤ 36 * k ^ 2 := by omega
    omega
  obtain ⟨c, rfl⟩ : ∃ c, k = c + 7 := ⟨k - 7, by omega⟩
  nlinarith

/-- Event on a child-frame entry state `d` at `childFp` asserting that `d.mem` holds a valid
`t`-supervertex contraction `(W₁, part₁)` of `W₀` together with a non-trivial cut `B₁` pulling back
to a minimum cut of `W₀`. -/
def ChildMinCutSurvives {n : ℕ} (W₀ : Fin n → Fin n → ℕ) (childFp t : ℕ) (d : Data 24) : Prop :=
  ∃ (W₁ : Fin t → Fin t → ℕ) (part₁ : Fin n → Fin t) (B₁ : Finset (Fin t)),
    IsContractionOf W₀ part₁ W₁ ∧
    HoldsMatrix d.mem (childFp + 2) t W₁ ∧
    IsNonTrivialCut B₁ ∧
    cutWeight W₀ (pullbackCut part₁ B₁) = minCut W₀

theorem branchTail_exec {w fp b k t : ℕ} {x : Data 24}
    (ht6 : 6 ≤ t) (htk : t ≤ k)
    (hwBase : x.regs wBase = fp + 4 + k * k)
    (hdBase : x.regs dBase = fp + 4 + 2 * (k * k))
    (hstride : x.regs stride = k)
    (htargetT : x.regs targetT = t)
    (hfp : x.regs fpReg = fp)
    (hsp : x.regs spReg = b + 1)
    (hfit : Fits w (fp + frameSize k + frameSize t))
    (hsp_fit : Fits w (b + 2)) :
    ∃ y : Data 24,
      ExecWithin w branchTail x y (7 * t ^ 2 + 8 * t + 21) ∧
      Modifies (Finset.Ico (fp + frameSize k) (fp + frameSize k + frameSize t)) x.mem y.mem ∧
      y.regs zero = 0 ∧
      y.regs fpReg = fp + frameSize k ∧
      y.regs spReg = b + 2 ∧
      y.mem (fp + frameSize k) = fp ∧
      y.mem (fp + frameSize k + 1) = t ∧
      y.mem (fp + frameSize k + 2 + t * t) = 0 ∧
      ∀ i j : Fin t,
        y.mem (fp + frameSize k + 2 + i.val * t + j.val) =
          x.mem (fp + 4 + k * k + i.val * k + j.val) := by
  let wb := fp + 4 + k * k
  let db := fp + 4 + 2 * (k * k)
  let childFp := fp + frameSize k
  have hcfp_eq : db + k = childFp := by
    dsimp only [db, childFp]
    unfold frameSize
    omega
  have htt_ge : 36 ≤ t * t := Nat.mul_le_mul ht6 ht6
  have hfs_t : frameSize t = 4 + 2 * (t * t) + t := rfl
  have h1 : Fits w 1 := hfit.of_le (by rw [hfs_t]; omega)
  have h2 : Fits w 2 := hfit.of_le (by rw [hfs_t]; omega)
  have hcfp_fit : Fits w childFp := hfit.of_le (by omega)
  have hcfp1_fit : Fits w (childFp + 1) := hfit.of_le (by rw [hfs_t]; omega)
  have hcfp2_fit : Fits w (childFp + 2) := hfit.of_le (by rw [hfs_t]; omega)
  have htt_fit : Fits w (t * t) := hfit.of_le (by rw [hfs_t]; omega)
  have hdstEnd : Fits w (childFp + 2 + t * t) := hfit.of_le (by rw [hfs_t]; omega)
  have hkt_le : k * t ≤ k * k := Nat.mul_le_mul_left k htk
  have hwEnd : Fits w (wb + k * t) := hfit.of_le (by
    dsimp only [wb]
    unfold frameSize
    omega)
  -- Substep 1: `branchCompactPre`
  let c₁ := x.set one 1
  let c₂ := c₁.set val2 childFp
  let c₃ := c₂.set val1 2
  let x₁ := c₃.set addr2 (childFp + 2)
  have hex_pre : ExecWithin w branchCompactPre x x₁ 4 := by
    have s1 : ExecWithin (B := .standard) w ram[one ← #1] x c₁ 1 := ExecWithin.const h1
    have s2 : ExecWithin w ram[val2 ← dBase + stride] c₁ c₂ 1 := by
      have hdb' : c₁.regs dBase = db := by simpa +decide [c₁, Function.update_apply] using hdBase
      have hstr' : c₁.regs stride = k := by simpa +decide [c₁, Function.update_apply] using hstride
      simpa [c₂, BinOp.eval, hdb', hstr', hcfp_eq] using
        ExecWithin.bin (f := .add) (d := val2) (i := dBase) (j := stride) (x := c₁)
          (by simpa [BinOp.eval, hdb', hstr', hcfp_eq] using hcfp_fit)
    have s3 : ExecWithin (B := .standard) w ram[val1 ← #2] c₂ c₃ 1 := ExecWithin.const h2
    have s4 : ExecWithin w ram[addr2 ← val2 + val1] c₃ x₁ 1 := by
      have hv2' : c₃.regs val2 = childFp := by simp +decide [c₃, c₂]
      have hv1' : c₃.regs val1 = 2 := by simp [c₃]
      simpa [x₁, BinOp.eval, hv2', hv1'] using
        ExecWithin.bin (f := .add) (d := addr2) (i := val2) (j := val1) (x := c₃)
          (by simpa [BinOp.eval, hv2', hv1'] using hcfp2_fit)
    unfold branchCompactPre
    exact (s1.seq (s2.seq (s3.seq s4))).mono (by omega)
  -- Substep 2: `copySubmatrixCode`
  let W_src : Fin t → Fin t → ℕ := fun i j => x.mem (wb + i.val * k + j.val)
  obtain ⟨x₂, hex_sub, hmat_sub, hmod_sub, _, _, hdb₂, hstr₂, _, ht₂, _, hhi₂⟩ :=
    copySubmatrixCode_exec (W := W_src) (x := x₁) (wb := wb) (str := k) (dstBase := childFp + 2)
      (t := t)
      (by simpa +decide [x₁, c₃, c₂, c₁, Function.update_apply] using hwBase)
      (by simpa +decide [x₁, c₃, c₂, c₁, Function.update_apply] using hstride)
      (by simpa +decide [x₁, c₃, c₂, c₁, Function.update_apply] using htargetT)
      (by simp [x₁])
      (by simp +decide [x₁, c₃, c₂, c₁])
      htk
      (by dsimp only [wb]; rw [← hcfp_eq]; dsimp only [db]; omega)
      hwEnd hdstEnd (fun _ _ => rfl)
  have hdb₂' : x₂.regs dBase = db := by
    rw [hdb₂]; simpa +decide [x₁, c₃, c₂, c₁, Function.update_apply] using hdBase
  have hstr₂' : x₂.regs stride = k := hstr₂
  have ht₂' : x₂.regs targetT = t := ht₂
  have hfp₂ : x₂.regs fpReg = fp := by
    rw [hhi₂ fpReg (by decide)]
    simpa +decide [x₁, c₃, c₂, c₁, Function.update_apply] using hfp
  have hsp₂ : x₂.regs spReg = b + 1 := by
    rw [hhi₂ spReg (by decide)]
    simpa +decide [x₁, c₃, c₂, c₁, Function.update_apply] using hsp
  -- Substep 3: `branchPushChild`
  let p₁ := x₂.set zero 0
  let p₂ := p₁.set one 1
  let p₃ := p₂.set addr1 childFp
  let p₄ := p₃.write childFp fp
  let p₅ := p₄.set addr2 (childFp + 1)
  let p₆ := p₅.write (childFp + 1) t
  let p₇ := p₆.set rem (t * t)
  let p₈ := p₇.set addr2 (childFp + 2)
  let p₉ := p₈.set addr2 (childFp + 2 + t * t)
  let p₁₀ := p₉.write (childFp + 2 + t * t) 0
  let p₁₁ := p₁₀.set fpReg childFp
  let y := p₁₁.set spReg (b + 2)
  have hex_push : ExecWithin w branchPushChild x₂ y 12 := by
    have q1 : ExecWithin (B := .standard) w ram[zero ← #0] x₂ p₁ 1 :=
      ExecWithin.const (fits_zero w)
    have q2 : ExecWithin (B := .standard) w ram[one ← #1] p₁ p₂ 1 := ExecWithin.const h1
    have q3 : ExecWithin w ram[addr1 ← dBase + stride] p₂ p₃ 1 := by
      have hdb' : p₂.regs dBase = db := by
        simpa +decide [p₂, p₁, Function.update_apply] using hdb₂'
      have hstr' : p₂.regs stride = k := by
        simpa +decide [p₂, p₁, Function.update_apply] using hstr₂'
      simpa [p₃, BinOp.eval, hdb', hstr', hcfp_eq] using
        ExecWithin.bin (f := .add) (d := addr1) (i := dBase) (j := stride) (x := p₂)
          (by simpa [BinOp.eval, hdb', hstr', hcfp_eq] using hcfp_fit)
    have q4 : ExecWithin (B := .standard) w ram[*addr1 ← fpReg] p₃ p₄ 1 := by
      have ha1 : p₃.regs addr1 = childFp := by simp [p₃]
      have hfp' : p₃.regs fpReg = fp := by
        simpa +decide [p₃, p₂, p₁, Function.update_apply] using hfp₂
      simpa [p₄, ha1, hfp'] using
        ExecWithin.store (B := .standard) (w := w) (a := addr1) (s := fpReg) (x := p₃)
    have q5 : ExecWithin w ram[addr2 ← addr1 + one] p₄ p₅ 1 := by
      have ha1 : p₄.regs addr1 = childFp := by simp +decide [p₄, p₃]
      have h1' : p₄.regs one = 1 := by simp +decide [p₄, p₃, p₂]
      simpa [p₅, BinOp.eval, ha1, h1'] using
        ExecWithin.bin (f := .add) (d := addr2) (i := addr1) (j := one) (x := p₄)
          (by simpa [BinOp.eval, ha1, h1'] using hcfp1_fit)
    have q6 : ExecWithin (B := .standard) w ram[*addr2 ← targetT] p₅ p₆ 1 := by
      have ha2 : p₅.regs addr2 = childFp + 1 := by simp [p₅]
      have ht' : p₅.regs targetT = t := by
        simpa +decide [p₅, p₄, p₃, p₂, p₁, Function.update_apply] using ht₂'
      simpa [p₆, ha2, ht'] using
        ExecWithin.store (B := .standard) (w := w) (a := addr2) (s := targetT) (x := p₅)
    have q7 : ExecWithin w ram[rem ← targetT * targetT] p₆ p₇ 1 := by
      have ht' : p₆.regs targetT = t := by
        simpa +decide [p₆, p₅, p₄, p₃, p₂, p₁, Function.update_apply] using ht₂'
      simpa [p₇, BinOp.eval, ht'] using
        ExecWithin.bin (f := .mul) (d := rem) (i := targetT) (j := targetT) (x := p₆)
          (by simpa [BinOp.eval, ht'] using htt_fit)
    have q8 : ExecWithin w ram[addr2 ← addr2 + one] p₇ p₈ 1 := by
      have ha2 : p₇.regs addr2 = childFp + 1 := by simp +decide [p₇, p₆, p₅]
      have h1' : p₇.regs one = 1 := by simp +decide [p₇, p₆, p₅, p₄, p₃, p₂]
      have heq : (childFp + 1) + 1 = childFp + 2 := by omega
      simpa [p₈, BinOp.eval, ha2, h1', heq] using
        ExecWithin.bin (f := .add) (d := addr2) (i := addr2) (j := one) (x := p₇)
          (by simpa [BinOp.eval, ha2, h1', heq] using hcfp2_fit)
    have q9 : ExecWithin w ram[addr2 ← addr2 + rem] p₈ p₉ 1 := by
      have ha2 : p₈.regs addr2 = childFp + 2 := by simp [p₈]
      have hr' : p₈.regs rem = t * t := by simp +decide [p₈, p₇]
      simpa [p₉, BinOp.eval, ha2, hr'] using
        ExecWithin.bin (f := .add) (d := addr2) (i := addr2) (j := rem) (x := p₈)
          (by simpa [BinOp.eval, ha2, hr'] using hdstEnd)
    have q10 : ExecWithin (B := .standard) w ram[*addr2 ← zero] p₉ p₁₀ 1 := by
      have ha2 : p₉.regs addr2 = childFp + 2 + t * t := by simp [p₉]
      have hz' : p₉.regs zero = 0 := by simp +decide [p₉, p₈, p₇, p₆, p₅, p₄, p₃, p₂, p₁]
      simpa [p₁₀, ha2, hz'] using
        ExecWithin.store (B := .standard) (w := w) (a := addr2) (s := zero) (x := p₉)
    have q11 : ExecWithin (B := .standard) w ram[fpReg ← addr1] p₁₀ p₁₁ 1 := by
      have ha1 : p₁₀.regs addr1 = childFp := by simp +decide [p₁₀, p₉, p₈, p₇, p₆, p₅, p₄, p₃]
      simpa [p₁₁, ha1] using
        (Exec.copy (B := .standard) (w := w) (d := fpReg) (s := addr1) (x := p₁₀)).within
    have q12 : ExecWithin w ram[spReg ← spReg + one] p₁₁ y 1 := by
      have hsp' : p₁₁.regs spReg = b + 1 := by
        simpa +decide [p₁₁, p₁₀, p₉, p₈, p₇, p₆, p₅, p₄, p₃, p₂, p₁, Function.update_apply]
          using hsp₂
      have h1' : p₁₁.regs one = 1 := by
        simp +decide [p₁₁, p₁₀, p₉, p₈, p₇, p₆, p₅, p₄, p₃, p₂]
      have heq : (b + 1) + 1 = b + 2 := by omega
      simpa [y, BinOp.eval, hsp', h1', heq] using
        ExecWithin.bin (f := .add) (d := spReg) (i := spReg) (j := one) (x := p₁₁)
          (by simpa [BinOp.eval, hsp', h1', heq] using hsp_fit)
    unfold branchPushChild
    exact (q1.seq (q2.seq (q3.seq (q4.seq (q5.seq (q6.seq (q7.seq (q8.seq
      (q9.seq (q10.seq (q11.seq q12))))))))))).mono (by omega)
  have hym : y.mem = Function.update
      (Function.update (Function.update x₂.mem childFp fp) (childFp + 1) t)
      (childFp + 2 + t * t) 0 := rfl
  refine ⟨y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold branchTail
    exact (hex_pre.seq (hex_sub.seq hex_push)).mono (by omega)
  · intro a ha
    rw [Finset.mem_Ico, hfs_t] at ha
    rw [hym, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hmod_sub a (by rw [Finset.mem_Ico]; omega)
  · simp +decide [y, p₁₁, p₁₀, p₉, p₈, p₇, p₆, p₅, p₄, p₃, p₂, p₁]
  · simp +decide [y, p₁₁, childFp]
  · simp [y]
  · rw [hym, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_self]
  · rw [hym, Function.update_of_ne (by omega), Function.update_self]
  · rw [hym, Function.update_self]
  · intro i j
    have hlt : childFp + 2 + i.val * t + j.val < childFp + 2 + t * t :=
      matAddr_lt_end (le_refl t) i j
    rw [hym, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hmat_sub i j

theorem branchContractAndPush_spec {n w fp b k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    (hk7 : 7 ≤ k)
    (hk_reg : x.regs activeK = k)
    (hfp : x.regs fpReg = fp)
    (hsp : x.regs spReg = b + 1)
    (hmat : HoldsMatrix x.mem (fp + 2) k W_k)
    (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + fastCutScratch k))
    (hsp_fit : Fits w (b + 2))
    (htot : Fits w (totalDoubledWeight W₀)) :
    let t := fastCutThreshold k
    let childFp := fp + frameSize k
    ∃ m : ProbComp (Data 24 × ℕ),
      ExecRand w branchContractAndPush x m ∧
      m.IsQueryBounded (k - t) ∧
      (∀ z ∈ m.support,
        z.2 ≤ 80 * (k * k) ∧
        Modifies (Finset.Ico (fp + 4 + k * k) (fp + fastCutScratch k)) x.mem z.1.mem ∧
        z.1.regs zero = 0 ∧
        z.1.regs fpReg = childFp ∧
        z.1.regs spReg = b + 2 ∧
        z.1.mem childFp = fp ∧
        z.1.mem (childFp + 1) = t ∧
        z.1.mem (childFp + 2 + t * t) = 0 ∧
        ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
          IsContractionOf W₀ part' W' ∧
          HoldsMatrix z.1.mem (childFp + 2) t W') ∧
      (∀ B : Finset (Fin k),
        0 < minCut W₀ → IsNonTrivialCut B →
        cutWeight W₀ (pullbackCut part B) = minCut W₀ →
        (1 : ℝ≥0∞) / 2 ≤
          m.eval.toOuterMeasure {z | ChildMinCutSurvives W₀ childFp t z.1}) := by
  intro t childFp
  let wb := fp + 4 + k * k
  let db := fp + 4 + 2 * (k * k)
  have ht6 : 6 ≤ t := fastCutThreshold_ge_six hk7
  have htk : t < k := fastCutThreshold_lt (by omega)
  have hscr_eq : fp + fastCutScratch k = childFp + fastCutScratch t := by
    dsimp only [childFp, t]
    rw [fastCutScratch_of_ge_seven hk7]
    omega
  have hfs_t_le : frameSize t ≤ fastCutScratch t := frameSize_le_fastCutScratch t
  have hcfp_eq : fp + frameSize k = db + k := by
    dsimp only [db]
    unfold frameSize
    omega
  have hfit_child : Fits w (childFp + frameSize t) := hfit.of_le (by omega)
  have hfit_th : Fits w (2 * k * (k - 1)) := by
    have := two_mul_pred_le_frameSize k
    exact hfit.of_le (by dsimp only [childFp] at hfit_child; omega)
  have hkk_ge : 49 ≤ k * k := Nat.mul_le_mul hk7 hk7
  have h1 : Fits w 1 := hfit_child.of_le (by dsimp only [childFp]; rw [hcfp_eq]; omega)
  have h2 : Fits w 2 := hfit_child.of_le (by dsimp only [childFp]; rw [hcfp_eq]; omega)
  have h4 : Fits w 4 := hfit_child.of_le (by dsimp only [childFp]; rw [hcfp_eq]; omega)
  have hfp2_fit : Fits w (fp + 2) := hfit_child.of_le (by dsimp only [childFp]; rw [hcfp_eq]; omega)
  have hfp4_fit : Fits w (fp + 4) := hfit_child.of_le (by dsimp only [childFp]; rw [hcfp_eq]; omega)
  have hkk_fit : Fits w (k * k) := hfit_child.of_le (by
    dsimp only [childFp]; rw [hcfp_eq]; dsimp only [db]; omega)
  have hwb_fit : Fits w wb := hfit_child.of_le (by
    dsimp only [childFp]; rw [hcfp_eq]; dsimp only [wb, db]; omega)
  have hdb_fit : Fits w db := hfit_child.of_le (by dsimp only [childFp]; rw [hcfp_eq]; omega)
  have hdEnd_fit : Fits w (db + k) := hfit_child.of_le (by
    dsimp only [childFp]; rw [hcfp_eq]; omega)
  have hd_eq : wb + k * k = db := by dsimp only [wb, db]; omega
  have htot_k : Fits w (totalDoubledWeight W_k) :=
    htot.of_le (totalDoubledWeight_le_of_isContractionOf hC)
  -- Step 1: `thresholdCode`
  obtain ⟨x_th, ⟨n_th, hn_th, hex_th⟩, hmem_th, _, hk_th, ht_th, _, _, _, hhi_th⟩ :=
    thresholdCode_exec hk7 hk_reg hfit_th
  have hfp_th : x_th.regs fpReg = fp := (hhi_th fpReg (by decide)).trans hfp
  have hsp_th : x_th.regs spReg = b + 1 := (hhi_th spReg (by decide)).trans hsp
  -- Step 2: `branchSetup`
  let s₁ := x_th.set val1 2
  let s₂ := s₁.set uReg (fp + 2)
  let s₃ := s₂.set rem (k * k)
  let s₄ := s₃.set val1 4
  let s₅ := s₄.set wBase (fp + 4)
  let s₆ := s₅.set wBase wb
  let s₇ := s₆.set dBase db
  let x_set := s₇.set stride k
  have hex_setup : Exec w branchSetup x_th x_set 8 := by
    have e1 : Exec (B := .standard) w ram[val1 ← #2] x_th s₁ 1 := Exec.const h2
    have e2 : Exec w ram[uReg ← fpReg + val1] s₁ s₂ 1 := by
      have hfp' : s₁.regs fpReg = fp := by simpa +decide [s₁, Function.update_apply] using hfp_th
      have hv1' : s₁.regs val1 = 2 := by simp [s₁]
      simpa [s₂, BinOp.eval, hfp', hv1'] using
        Exec.bin (f := .add) (d := uReg) (i := fpReg) (j := val1) (x := s₁)
          (by simpa [BinOp.eval, hfp', hv1'] using hfp2_fit)
    have e3 : Exec w ram[rem ← activeK * activeK] s₂ s₃ 1 := by
      have hk' : s₂.regs activeK = k := by
        simpa +decide [s₂, s₁, Function.update_apply] using hk_th
      simpa [s₃, BinOp.eval, hk'] using
        Exec.bin (f := .mul) (d := rem) (i := activeK) (j := activeK) (x := s₂)
          (by simpa [BinOp.eval, hk'] using hkk_fit)
    have e4 : Exec (B := .standard) w ram[val1 ← #4] s₃ s₄ 1 := Exec.const h4
    have e5 : Exec w ram[wBase ← fpReg + val1] s₄ s₅ 1 := by
      have hfp' : s₄.regs fpReg = fp := by
        simpa +decide [s₄, s₃, s₂, s₁, Function.update_apply] using hfp_th
      have hv1' : s₄.regs val1 = 4 := by simp [s₄]
      simpa [s₅, BinOp.eval, hfp', hv1'] using
        Exec.bin (f := .add) (d := wBase) (i := fpReg) (j := val1) (x := s₄)
          (by simpa [BinOp.eval, hfp', hv1'] using hfp4_fit)
    have e6 : Exec w ram[wBase ← wBase + rem] s₅ s₆ 1 := by
      have hwb' : s₅.regs wBase = fp + 4 := by simp [s₅]
      have hr' : s₅.regs rem = k * k := by simp +decide [s₅, s₄, s₃]
      have heq : (fp + 4) + k * k = wb := rfl
      simpa [s₆, BinOp.eval, hwb', hr', heq] using
        Exec.bin (f := .add) (d := wBase) (i := wBase) (j := rem) (x := s₅)
          (by simpa [BinOp.eval, hwb', hr', heq] using hwb_fit)
    have e7 : Exec w ram[dBase ← wBase + rem] s₆ s₇ 1 := by
      have hwb' : s₆.regs wBase = wb := by simp [s₆]
      have hr' : s₆.regs rem = k * k := by simp +decide [s₆, s₅, s₄, s₃]
      simpa [s₇, BinOp.eval, hwb', hr', hd_eq] using
        Exec.bin (f := .add) (d := dBase) (i := wBase) (j := rem) (x := s₆)
          (by simpa [BinOp.eval, hwb', hr', hd_eq] using hdb_fit)
    have e8 : Exec (B := .standard) w ram[stride ← activeK] s₇ x_set 1 := by
      have hk' : s₇.regs activeK = k := by
        simpa +decide [s₇, s₆, s₅, s₄, s₃, s₂, s₁, Function.update_apply] using hk_th
      simpa [x_set, hk'] using
        Exec.copy (B := .standard) (w := w) (d := stride) (s := activeK) (x := s₇)
    unfold branchSetup
    exact e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))
  -- Step 3: `ksCopyCode`
  obtain ⟨x_cp, ⟨n_cp, hn_cp, hex_cp⟩, hmat_cp, hmod_cp, _, hwb_cp, hdb_cp, hstr_cp, hk_cp,
      ht_cp, hhi_cp⟩ :=
    ksCopyCode_exec (x := x_set) (sb := fp + 2) (db := wb) (k := k) (W := W_k)
      (by simp +decide [x_set, s₇, s₆, s₅, s₄, s₃, s₂])
      (by simp +decide [x_set, s₇, s₆])
      (by simp +decide [x_set, s₇, s₆, s₅, s₄, s₃])
      (by dsimp only [wb]; omega) h1 (hd_eq ▸ hdb_fit) (hmem_th ▸ hmat)
  have hdb_cp' : x_cp.regs dBase = db := by
    rw [hdb_cp]; simp +decide [x_set, s₇]
  have hstr_cp' : x_cp.regs stride = k := by
    rw [hstr_cp]; simp [x_set]
  have hk_cp' : x_cp.regs activeK = k := by
    rw [hk_cp]
    simpa +decide [x_set, s₇, s₆, s₅, s₄, s₃, s₂, s₁, Function.update_apply] using hk_th
  have ht_cp' : x_cp.regs targetT = t := by
    rw [ht_cp]
    simpa +decide [x_set, s₇, s₆, s₅, s₄, s₃, s₂, s₁, Function.update_apply] using ht_th
  -- Step 4: `computeDegreesAndTotalAt hr24`
  obtain ⟨x_deg, ⟨n_deg, hn_deg, hex_deg⟩, hws_deg, hmod_deg, hwb_deg, hdb_deg, hstr_deg, hk_deg,
      ht_deg, htot_deg, hhi_deg⟩ :=
    computeDegreesAndTotalAt_exec hr24 (x := x_cp) (wb := wb) (db := db) (str := k) (k := k)
      (W := W_k) hwb_cp hdb_cp' hstr_cp' hk_cp' (le_refl k) (Or.inl (by dsimp only [wb, db]; omega))
      h1 (hd_eq ▸ hdb_fit) hdEnd_fit htot_k hmat_cp
  have hfp_deg : x_deg.regs fpReg = fp := by
    rw [hhi_deg fpReg (by decide), hhi_cp fpReg (by decide)]
    simpa +decide [x_set, s₇, s₆, s₅, s₄, s₃, s₂, s₁, Function.update_apply] using hfp_th
  have hsp_deg : x_deg.regs spReg = b + 1 := by
    rw [hhi_deg spReg (by decide), hhi_cp spReg (by decide)]
    simpa +decide [x_set, s₇, s₆, s₅, s₄, s₃, s₂, s₁, Function.update_apply] using hsp_th
  have hst_deg : ContractState w wb db k k t W_k (x_deg.comap (Fin.castLE hr24)) := {
    regs_wBase := hwb_deg
    regs_dBase := hdb_deg
    regs_stride := hstr_deg
    regs_activeK := hk_deg
    regs_targetT := ht_deg.trans ht_cp'
    regs_totS := htot_deg
    le_stride := le_refl k
    disjoint_blocks := Or.inl (by dsimp only [wb, db]; omega)
    fits_wEnd := hd_eq ▸ hdb_fit
    fits_dEnd := hdEnd_fit
    fits_totS := htot_k
    workspace := hws_deg
  }
  -- Step 5: `contractDownToAt hr24`
  obtain ⟨m_c, hm_c, hq_c, hsup_c, hsurv_c⟩ :=
    contractDownToAt_spec hr24 (by omega : 2 ≤ t) htk.le hC hst_deg
  -- Step 6: `branchTail` on every supported output of `m_c`
  have htail : ∀ z ∈ m_c.support, ∃ y : Data 24,
      ExecWithin w branchTail z.1 y (7 * t ^ 2 + 8 * t + 21) ∧
      Modifies (Finset.Ico childFp (childFp + frameSize t)) z.1.mem y.mem ∧
      y.regs zero = 0 ∧
      y.regs fpReg = childFp ∧
      y.regs spReg = b + 2 ∧
      y.mem childFp = fp ∧
      y.mem (childFp + 1) = t ∧
      y.mem (childFp + 2 + t * t) = 0 ∧
      ∀ i j : Fin t,
        y.mem (childFp + 2 + i.val * t + j.val) = z.1.mem (wb + i.val * k + j.val) := by
    intro z hz
    rcases hsup_c z hz with ⟨_, _, hhi_c, _, _, _, hst_c⟩
    exact branchTail_exec ht6 htk.le hst_c.regs_wBase hst_c.regs_dBase hst_c.regs_stride
      hst_c.regs_targetT ((hhi_c fpReg (by decide)).trans hfp_deg)
      ((hhi_c spReg (by decide)).trans hsp_deg) hfit_child hsp_fit
  obtain ⟨g, hseq_tail, hg⟩ := execRand_seq_det
    (Q := fun d y => Modifies (Finset.Ico childFp (childFp + frameSize t)) d.mem y.mem ∧
      y.regs zero = 0 ∧ y.regs fpReg = childFp ∧ y.regs spReg = b + 2 ∧
      y.mem childFp = fp ∧ y.mem (childFp + 1) = t ∧ y.mem (childFp + 2 + t * t) = 0 ∧
      ∀ i j : Fin t,
        y.mem (childFp + 2 + i.val * t + j.val) = d.mem (wb + i.val * k + j.val))
    hm_c htail
  have hfull_raw := hex_th.seqRand (hex_setup.seqRand (hex_cp.seqRand (hex_deg.seqRand hseq_tail)))
  let m_out : ProbComp (Data 24 × ℕ) :=
    (fun z => ((g z.1).1, n_th + (8 + (n_cp + (n_deg + (z.2 + (g z.1).2)))))) <$> m_c
  have hfull : ExecRand w branchContractAndPush x m_out := by
    unfold branchContractAndPush
    convert hfull_raw using 1
    simp only [m_out, Functor.map_map]
  refine ⟨m_out, hfull, ?_, ?_, ?_⟩
  · simp only [m_out, OracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
    exact hq_c
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    rcases hsup_c z₀ hz₀ with ⟨ht_c, hmod_c, _, W', part', hC', hst_c⟩
    rcases hg z₀ hz₀ with
      ⟨ht_tail, _, hmod_tail, hz0, hzfp, hzsp, hm_cfp, hm_cfp1, hm_cfp_stg, hm_sub⟩
    refine ⟨branch_step_bound hk7 htk.le hn_th hn_cp hn_deg ht_c ht_tail,
      ?_, hz0, hzfp, hzsp, hm_cfp, hm_cfp1, hm_cfp_stg, W', part', hC', ?_⟩
    · let S_mod := Finset.Ico wb (fp + fastCutScratch k)
      have hsub_cp : Finset.Ico wb (wb + k * k) ⊆ S_mod := by
        intro a ha
        rw [Finset.mem_Ico] at ha ⊢
        rw [hscr_eq]; dsimp only [childFp] at *; rw [hcfp_eq]; omega
      have hsub_deg : Finset.Ico db (db + k) ⊆ S_mod := by
        intro a ha
        rw [Finset.mem_Ico] at ha ⊢
        rw [hscr_eq]; dsimp only [wb, childFp] at *; rw [hcfp_eq]; omega
      have hsub_c : workspaceFootprint wb db k k ⊆ S_mod :=
        Finset.union_subset hsub_cp hsub_deg
      have hsub_tail : Finset.Ico childFp (childFp + frameSize t) ⊆ S_mod := by
        intro a ha
        rw [Finset.mem_Ico] at ha ⊢
        rw [hscr_eq]; dsimp only [wb, childFp] at *; rw [hcfp_eq]; dsimp only [db]; omega
      have hmod_xcp : Modifies S_mod x.mem x_cp.mem := by
        have hmem_set : x_set.mem = x.mem := hmem_th
        exact hmem_set ▸ (modifies_trans_subset (Modifies.refl S_mod x_set.mem) hmod_cp
          Finset.Subset.rfl hsub_cp)
      exact modifies_trans_subset
        (modifies_trans_subset
          (modifies_trans_subset hmod_xcp hmod_deg Finset.Subset.rfl hsub_deg)
          hmod_c Finset.Subset.rfl hsub_c)
        hmod_tail Finset.Subset.rfl hsub_tail
    · intro i j
      rw [hm_sub i j]
      exact hst_c.workspace.1 i j
  · intro B hmin_pos hB_nt hB_min
    have hprob := hsurv_c B hmin_pos hB_nt hB_min
    have hhalf := half_le_threshold_survival hk7
    have hC_nt : IsNonTrivialCut (pullbackCut part B) :=
      isNonTrivialCut_pullbackCut hC.surj hB_nt
    rw [ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    refine (hhalf.trans hprob).trans (toOuterMeasure_mono_support m_c fun z₀ hsup hz₀ => ?_)
    rcases hg z₀ hsup with ⟨_, _, _, _, _, _, _, _, _, hm_sub⟩
    rcases hz₀ with ⟨W₁, part₁, B₁, hC₁, hws₁, _, hpb₁⟩
    refine ⟨W₁, part₁, B₁, hC₁, fun i j => (hm_sub i j).trans (hws₁.1 i j),
      isNonTrivialCut_of_pullbackCut part₁ (hpb₁ ▸ hC_nt), hpb₁ ▸ hB_min⟩

private theorem probComp_seq_hit_ge {r : ℕ} (m₁ : ProbComp (Data r × ℕ))
    (m₂ : Data r → ProbComp (Data r × ℕ)) (pre : Data r → Prop) (post : Data r → Prop)
    {s₁ s₂ : ℝ≥0∞}
    (hp : s₁ ≤ m₁.eval.toOuterMeasure {z | pre z.1})
    (hstep : ∀ z ∈ m₁.support, pre z.1 →
      s₂ ≤ (m₂ z.1).eval.toOuterMeasure {z' | post z'.1}) :
    s₁ * s₂ ≤ (do
      let z₁ ← m₁
      let z₂ ← m₂ z₁.1
      pure (z₂.1, z₁.2 + z₂.2)).eval.toOuterMeasure {z | post z.1} := by
  have heval : (do
      let z₁ ← m₁
      let z₂ ← m₂ z₁.1
      pure (z₂.1, z₁.2 + z₂.2)).eval =
      m₁.eval.bind (fun z₁ => (m₂ z₁.1).eval.map (fun z₂ => (z₂.1, z₁.2 + z₂.2))) := by
    rw [ProbComp.eval_bind]
    refine congrArg (m₁.eval.bind ·) (funext fun z₁ => ?_)
    rw [bind_pure_comp, ProbComp.eval_map]
  rw [heval]
  refine toOuterMeasure_bind_ge_mul_ennreal _ _
    {z : Data r × ℕ | pre z.1} {z : Data r × ℕ | post z.1} hp fun z₁ hz₁ hpre => ?_
  rw [PMF.toOuterMeasure_map_apply]
  exact hstep z₁ ((ProbComp.support_eval m₁) ▸ hz₁) hpre

private theorem isQueryBounded_seq {r q₁ q₂ : ℕ} {m₁ : ProbComp (Data r × ℕ)}
    {m₂ : Data r → ProbComp (Data r × ℕ)}
    (hq₁ : m₁.IsQueryBounded q₁)
    (hq₂ : ∀ z ∈ m₁.support, (m₂ z.1).IsQueryBounded q₂) :
    (do
      let z₁ ← m₁
      let z₂ ← m₂ z₁.1
      pure (z₂.1, z₁.2 + z₂.2)).IsQueryBounded (q₁ + q₂) := by
  refine OracleComp.IsCostBounded.bind_on_support hq₁ fun z₁ hz₁ => ?_
  simpa only [Nat.add_zero] using (hq₂ z₁ hz₁).bind fun _ => .pure _ 0

theorem fastCutStep_base_seg {n w fp parentFp b k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    (hk2 : 2 ≤ k) (hk6 : k ≤ 6)
    (h0 : x.regs zero = 0) (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1)
    (hmem_p : x.mem fp = parentFp) (hmem_k : x.mem (fp + 1) = k)
    (hmat : HoldsMatrix x.mem (fp + 2) k W_k) (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + frameSize k)) (hsp_fit : Fits w b)
    (htot : Fits w (totalDoubledWeight W₀)) :
    ∃ m : ProbComp (Data 24 × ℕ),
      LoopSegment w (Cond.lt zero spReg) fastCutStep x m ∧
      m.IsQueryBounded (k - 2) ∧
      (∀ z ∈ m.support,
        z.2 ≤ 2400 ∧
        Modifies (Finset.Ico (fp + 2 + k * k) (fp + frameSize k)) x.mem z.1.mem ∧
        z.1.regs zero = 0 ∧
        z.1.regs fpReg = parentFp ∧
        z.1.regs spReg = b ∧
        ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ z.1.regs retVal = cutWeight W₀ C) ∧
      (∀ B : Finset (Fin k),
        0 < minCut W₀ → IsNonTrivialCut B →
        cutWeight W₀ (pullbackCut part B) = minCut W₀ →
        (2 : ℝ≥0∞) / (30 : ℝ≥0∞) ≤
          m.eval.toOuterMeasure {z | z.1.regs retVal = minCut W₀}) := by
  have hc_loop : (Cond.lt zero spReg).Holds x := by simp [Cond.holds_lt, h0, hsp]
  obtain ⟨y_h, hex_hdr, hm_h, _, _, hk_h, hrem_h, ha1_h, ha2_h, _, hv1_h, hhi_h⟩ :=
    stepHeader_exec hk2 hfp hmem_k rfl hfit
  have hfp_h : y_h.regs fpReg = fp := (hhi_h fpReg (by decide)).trans hfp
  have hsp_h : y_h.regs spReg = b + 1 := (hhi_h spReg (by decide)).trans hsp
  have hc_lt : (Cond.lt activeK val1).Holds y_h := by
    simp only [Cond.holds_lt, hk_h, hv1_h]
    omega
  obtain ⟨m_b, hm_b, hq_b, hsup_b, hsurv_b⟩ :=
    baseCaseAndPop_spec hk2 hk6 hk_h hrem_h ha1_h ha2_h hfp_h hsp_h
      (hm_h ▸ hmem_p) (hm_h ▸ hmat) hC hfit hsp_fit htot
  have hstep : ExecRand w fastCutStep x
      ((fun z => (z.1, 9 + (z.2 + 1))) <$> m_b) := by
    unfold fastCutStep
    convert hex_hdr.seqRand (ExecRand.branch_pos hc_lt hm_b) using 1
    simp only [Functor.map_map]
  have hseg_raw := LoopSegment.single hc_loop hstep
  let m_out : ProbComp (Data 24 × ℕ) := (fun z => (z.1, 9 + (z.2 + 1) + 2)) <$> m_b
  have hseg : LoopSegment w (Cond.lt zero spReg) fastCutStep x m_out := by
    convert hseg_raw using 1
    simp only [m_out, Functor.map_map]
  refine ⟨m_out, hseg, ?_, ?_, ?_⟩
  · simp only [m_out, OracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
    exact hq_b
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    rcases hsup_b z₀ hz₀ with ⟨ht₀, hmod₀, hz0, hzfp, hzsp, hcut⟩
    exact ⟨by omega, hm_h ▸ hmod₀, hz0, hzfp, hzsp, hcut⟩
  · intro B hmin_pos hB_nt hB_min
    rw [ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    exact hsurv_b B hmin_pos hB_nt hB_min

theorem fastCutNode_base {n w d fp parentFp b k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    (hk2 : 2 ≤ k) (hk6 : k ≤ 6)
    (h0 : x.regs zero = 0) (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1)
    (hmem_p : x.mem fp = parentFp) (hmem_k : x.mem (fp + 1) = k)
    (hmat : HoldsMatrix x.mem (fp + 2) k W_k) (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + fastCutScratch k)) (hsp_fit : Fits w (b + 1 + d))
    (htot : Fits w (totalDoubledWeight W₀)) :
    ∃ m : ProbComp (Data 24 × ℕ),
      LoopSegment w (Cond.lt zero spReg) fastCutStep x m ∧
      m.IsQueryBounded (fastCutNodeQueries k) ∧
      (∀ z ∈ m.support,
        z.2 ≤ fastCutNodeTime k ∧
        Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) x.mem z.1.mem ∧
        z.1.regs zero = 0 ∧
        z.1.regs fpReg = parentFp ∧
        z.1.regs spReg = b ∧
        ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ z.1.regs retVal = cutWeight W₀ C) ∧
      (∀ B : Finset (Fin k),
        0 < minCut W₀ → IsNonTrivialCut B →
        cutWeight W₀ (pullbackCut part B) = minCut W₀ →
        (2 : ℝ≥0∞) / ((d + 30 : ℕ) : ℝ≥0∞) ≤
          m.eval.toOuterMeasure {z | z.1.regs retVal = minCut W₀}) := by
  have hlt7 : k < 7 := by omega
  have hscr : fastCutScratch k = frameSize k := fastCutScratch_of_lt_seven hlt7
  have hq_eq : fastCutNodeQueries k = k - 2 := fastCutNodeQueries_of_lt_seven hlt7
  have ht_eq : fastCutNodeTime k = 2400 := fastCutNodeTime_of_lt_seven hlt7
  obtain ⟨m, hm, hq, hsup, hsurv⟩ :=
    fastCutStep_base_seg hk2 hk6 h0 hfp hsp hmem_p hmem_k hmat hC
      (hscr ▸ hfit) (hsp_fit.of_le (by omega)) htot
  refine ⟨m, hm, hq_eq ▸ hq, ?_, ?_⟩
  · intro z hz
    rcases hsup z hz with ⟨ht, hmod, rest⟩
    exact ⟨ht_eq ▸ ht, hscr.symm ▸ hmod, rest⟩
  · intro B hmin_pos hB_nt hB_min
    refine (ENNReal.div_le_div_left ?_ (2 : ℝ≥0∞)).trans (hsurv B hmin_pos hB_nt hB_min)
    exact_mod_cast (by omega : 30 ≤ d + 30)

theorem fastCutStep_stage0_seg {n w fp b k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    (hk7 : 7 ≤ k)
    (h0 : x.regs zero = 0) (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1)
    (hmem_k : x.mem (fp + 1) = k) (hmem_stg : x.mem (fp + 2 + k * k) = 0)
    (hmat : HoldsMatrix x.mem (fp + 2) k W_k) (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + fastCutScratch k)) (hsp_fit : Fits w (b + 2))
    (htot : Fits w (totalDoubledWeight W₀)) :
    let t := fastCutThreshold k
    let childFp := fp + frameSize k
    ∃ m : ProbComp (Data 24 × ℕ),
      LoopSegment w (Cond.lt zero spReg) fastCutStep x m ∧
      m.IsQueryBounded (k - t) ∧
      (∀ z ∈ m.support,
        z.2 ≤ 80 * (k * k) + 15 ∧
        Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) x.mem z.1.mem ∧
        z.1.mem (fp + 2 + k * k) = 1 ∧
        z.1.regs zero = 0 ∧
        z.1.regs fpReg = childFp ∧
        z.1.regs spReg = b + 2 ∧
        z.1.mem childFp = fp ∧
        z.1.mem (childFp + 1) = t ∧
        z.1.mem (childFp + 2 + t * t) = 0 ∧
        ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
          IsContractionOf W₀ part' W' ∧
          HoldsMatrix z.1.mem (childFp + 2) t W') ∧
      (∀ B : Finset (Fin k),
        0 < minCut W₀ → IsNonTrivialCut B →
        cutWeight W₀ (pullbackCut part B) = minCut W₀ →
        (1 : ℝ≥0∞) / 2 ≤
          m.eval.toOuterMeasure {z | ChildMinCutSurvives W₀ childFp t z.1}) := by
  intro t childFp
  have hc_loop : (Cond.lt zero spReg).Holds x := by simp [Cond.holds_lt, h0, hsp]
  have hfs_le : frameSize k ≤ fastCutScratch k := frameSize_le_fastCutScratch k
  obtain ⟨y_h, hex_hdr, hm_h, h0_h, h1_h, hk_h, _, _, ha2_h, hv2_h, hv1_h, hhi_h⟩ :=
    stepHeader_exec (by omega : 2 ≤ k) hfp hmem_k hmem_stg (hfit.of_le (by omega))
  have hfp_h : y_h.regs fpReg = fp := (hhi_h fpReg (by decide)).trans hfp
  have hsp_h : y_h.regs spReg = b + 1 := (hhi_h spReg (by decide)).trans hsp
  have hnc_lt : ¬(Cond.lt activeK val1).Holds y_h := by
    simp only [Cond.holds_lt, hk_h, hv1_h]
    omega
  have hc_eq0 : (Cond.eq val2 zero).Holds y_h := by
    simp [Cond.holds_eq, hv2_h, h0_h]
  let y_s := y_h.write (fp + 2 + k * k) 1
  have hex_s0 : Exec (B := .standard) w stageZeroSet y_h y_s 1 := by
    unfold stageZeroSet
    simpa [y_s, ha2_h, h1_h] using
      Exec.store (B := .standard) (w := w) (a := addr2) (s := one) (x := y_h)
  have hmat_s : HoldsMatrix y_s.mem (fp + 2) k W_k := by
    intro i j
    have hlt : fp + 2 + i.val * k + j.val < fp + 2 + k * k := matAddr_lt_end (le_refl k) i j
    change Function.update y_h.mem (fp + 2 + k * k) 1 (fp + 2 + i.val * k + j.val) = W_k i j
    rw [Function.update_of_ne (by omega), hm_h]
    exact hmat i j
  obtain ⟨m_c, hm_c, hq_c, hsup_c, hsurv_c⟩ :=
    branchContractAndPush_spec (x := y_s) hk7 hk_h hfp_h hsp_h hmat_s hC hfit hsp_fit htot
  have hbr0 : ExecRand w
      ram[if val2 = zero then [ ⟪stageZeroSet⟫; ⟪branchContractAndPush⟫ ] else [
        if val2 = one then [ ⟪stageOneSaveAndSet⟫; ⟪branchContractAndPush⟫ ] else [
          ⟪combineAndPop⟫ ] ]]
      y_h ((fun z => (z.1, (1 + z.2) + 1)) <$> m_c) := by
    convert ExecRand.branch_pos hc_eq0 (hex_s0.seqRand hm_c) using 1
    simp only [Functor.map_map]
  have hstep : ExecRand w fastCutStep x
      ((fun z => (z.1, 9 + (((1 + z.2) + 1) + 2))) <$> m_c) := by
    unfold fastCutStep
    convert hex_hdr.seqRand (ExecRand.branch_neg hnc_lt hbr0) using 1
    simp only [Functor.map_map]
  have hseg_raw := LoopSegment.single hc_loop hstep
  let m_out : ProbComp (Data 24 × ℕ) :=
    (fun z => (z.1, 9 + (((1 + z.2) + 1) + 2) + 2)) <$> m_c
  have hseg : LoopSegment w (Cond.lt zero spReg) fastCutStep x m_out := by
    convert hseg_raw using 1
    simp only [m_out, Functor.map_map]
  refine ⟨m_out, hseg, ?_, ?_, ?_⟩
  · simp only [m_out, OracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
    exact hq_c
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    rcases hsup_c z₀ hz₀ with ⟨ht₀, hmod₀, rest⟩
    have hstg_in : fp + 2 + k * k ∈ Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k) := by
      rw [Finset.mem_Ico]
      unfold frameSize at hfs_le
      omega
    have hmod_s : Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k))
        x.mem y_s.mem := by
      change Modifies _ x.mem (Function.update y_h.mem (fp + 2 + k * k) 1)
      rw [hm_h]
      exact modifies_update_of_mem hstg_in x.mem 1
    have hsub : Finset.Ico (fp + 4 + k * k) (fp + fastCutScratch k) ⊆
        Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k) := by
      intro a ha; rw [Finset.mem_Ico] at ha ⊢; omega
    have hstg_val : z₀.1.mem (fp + 2 + k * k) = 1 := by
      rw [hmod₀ _ (by rw [Finset.mem_Ico]; omega)]
      exact Function.update_self _ _ _
    exact ⟨by omega, modifies_trans_subset hmod_s hmod₀ Finset.Subset.rfl hsub, hstg_val, rest⟩
  · intro B hmin_pos hB_nt hB_min
    rw [ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    exact hsurv_c B hmin_pos hB_nt hB_min

theorem fastCutStep_stage1_seg {n w fp b k v1 : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    (hk7 : 7 ≤ k)
    (h0 : x.regs zero = 0) (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1)
    (hret : x.regs retVal = v1)
    (hmem_k : x.mem (fp + 1) = k) (hmem_stg : x.mem (fp + 2 + k * k) = 1)
    (hmat : HoldsMatrix x.mem (fp + 2) k W_k) (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + fastCutScratch k)) (hsp_fit : Fits w (b + 2))
    (htot : Fits w (totalDoubledWeight W₀)) :
    let t := fastCutThreshold k
    let childFp := fp + frameSize k
    ∃ m : ProbComp (Data 24 × ℕ),
      LoopSegment w (Cond.lt zero spReg) fastCutStep x m ∧
      m.IsQueryBounded (k - t) ∧
      (∀ z ∈ m.support,
        z.2 ≤ 80 * (k * k) + 20 ∧
        Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) x.mem z.1.mem ∧
        z.1.mem (fp + 2 + k * k) = 2 ∧
        z.1.mem (fp + 3 + k * k) = v1 ∧
        z.1.regs zero = 0 ∧
        z.1.regs fpReg = childFp ∧
        z.1.regs spReg = b + 2 ∧
        z.1.mem childFp = fp ∧
        z.1.mem (childFp + 1) = t ∧
        z.1.mem (childFp + 2 + t * t) = 0 ∧
        ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
          IsContractionOf W₀ part' W' ∧
          HoldsMatrix z.1.mem (childFp + 2) t W') ∧
      (∀ B : Finset (Fin k),
        0 < minCut W₀ → IsNonTrivialCut B →
        cutWeight W₀ (pullbackCut part B) = minCut W₀ →
        (1 : ℝ≥0∞) / 2 ≤
          m.eval.toOuterMeasure {z | ChildMinCutSurvives W₀ childFp t z.1}) := by
  intro t childFp
  have hc_loop : (Cond.lt zero spReg).Holds x := by simp [Cond.holds_lt, h0, hsp]
  have hfs_le : frameSize k ≤ fastCutScratch k := frameSize_le_fastCutScratch k
  have hfit_fs : Fits w (fp + frameSize k) := hfit.of_le (by omega)
  have h2_fit : Fits w 2 := hfit_fs.of_le (by unfold frameSize; omega)
  have ha1_fit : Fits w (fp + 3 + k * k) := hfit_fs.of_le (by unfold frameSize; omega)
  obtain ⟨y_h, hex_hdr, hm_h, h0_h, h1_h, hk_h, _, _, ha2_h, hv2_h, hv1_h, hhi_h⟩ :=
    stepHeader_exec (by omega : 2 ≤ k) hfp hmem_k hmem_stg hfit_fs
  have hfp_h : y_h.regs fpReg = fp := (hhi_h fpReg (by decide)).trans hfp
  have hsp_h : y_h.regs spReg = b + 1 := (hhi_h spReg (by decide)).trans hsp
  have hret_h : y_h.regs retVal = v1 := (hhi_h retVal (by decide)).trans hret
  have hnc_lt : ¬(Cond.lt activeK val1).Holds y_h := by
    simp only [Cond.holds_lt, hk_h, hv1_h]
    omega
  have hnc_eq0 : ¬(Cond.eq val2 zero).Holds y_h := by
    simp [Cond.holds_eq, hv2_h, h0_h]
  have hc_eq1 : (Cond.eq val2 one).Holds y_h := by
    simp [Cond.holds_eq, hv2_h, h1_h]
  let q₁ := y_h.set val1 2
  let q₂ := q₁.write (fp + 2 + k * k) 2
  let q₃ := q₂.set addr1 (fp + 3 + k * k)
  let y_s := q₃.write (fp + 3 + k * k) v1
  have hex_s1 : Exec w stageOneSaveAndSet y_h y_s 4 := by
    have s1 : Exec (B := .standard) w ram[val1 ← #2] y_h q₁ 1 := Exec.const h2_fit
    have s2 : Exec (B := .standard) w ram[*addr2 ← val1] q₁ q₂ 1 := by
      have ha2' : q₁.regs addr2 = fp + 2 + k * k := by
        simpa +decide [q₁, Function.update_apply] using ha2_h
      have hv1' : q₁.regs val1 = 2 := by simp [q₁]
      simpa [q₂, ha2', hv1'] using
        Exec.store (B := .standard) (w := w) (a := addr2) (s := val1) (x := q₁)
    have s3 : Exec w ram[addr1 ← addr2 + one] q₂ q₃ 1 := by
      have ha2' : q₂.regs addr2 = fp + 2 + k * k := by
        simpa +decide [q₂, q₁, Function.update_apply] using ha2_h
      have h1' : q₂.regs one = 1 := by simpa +decide [q₂, q₁, Function.update_apply] using h1_h
      have heq : (fp + 2 + k * k) + 1 = fp + 3 + k * k := by omega
      simpa [q₃, BinOp.eval, ha2', h1', heq] using
        Exec.bin (f := .add) (d := addr1) (i := addr2) (j := one) (x := q₂)
          (by simpa [BinOp.eval, ha2', h1', heq] using ha1_fit)
    have s4 : Exec (B := .standard) w ram[*addr1 ← retVal] q₃ y_s 1 := by
      have ha1' : q₃.regs addr1 = fp + 3 + k * k := by simp [q₃]
      have hr' : q₃.regs retVal = v1 := by
        simpa +decide [q₃, q₂, q₁, Function.update_apply] using hret_h
      simpa [y_s, ha1', hr'] using
        Exec.store (B := .standard) (w := w) (a := addr1) (s := retVal) (x := q₃)
    unfold stageOneSaveAndSet
    exact s1.seq (s2.seq (s3.seq s4))
  have hys_mem : y_s.mem =
      Function.update (Function.update x.mem (fp + 2 + k * k) 2) (fp + 3 + k * k) v1 := by
    change Function.update (Function.update y_h.mem _ _) _ _ = _
    rw [hm_h]
  have hmat_s : HoldsMatrix y_s.mem (fp + 2) k W_k := by
    intro i j
    have hlt : fp + 2 + i.val * k + j.val < fp + 2 + k * k := matAddr_lt_end (le_refl k) i j
    rw [hys_mem, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hmat i j
  have hk_s : y_s.regs activeK = k := by
    simpa +decide [y_s, q₃, q₂, q₁, Function.update_apply] using hk_h
  have hfp_s : y_s.regs fpReg = fp := by
    simpa +decide [y_s, q₃, q₂, q₁, Function.update_apply] using hfp_h
  have hsp_s : y_s.regs spReg = b + 1 := by
    simpa +decide [y_s, q₃, q₂, q₁, Function.update_apply] using hsp_h
  obtain ⟨m_c, hm_c, hq_c, hsup_c, hsurv_c⟩ :=
    branchContractAndPush_spec (x := y_s) hk7 hk_s hfp_s hsp_s hmat_s hC hfit hsp_fit htot
  have hbr1 : ExecRand w
      ram[if val2 = one then [ ⟪stageOneSaveAndSet⟫; ⟪branchContractAndPush⟫ ] else [
        ⟪combineAndPop⟫ ]]
      y_h ((fun z => (z.1, (4 + z.2) + 1)) <$> m_c) := by
    convert ExecRand.branch_pos hc_eq1 (hex_s1.seqRand hm_c) using 1
    simp only [Functor.map_map]
  have hbr0 : ExecRand w
      ram[if val2 = zero then [ ⟪stageZeroSet⟫; ⟪branchContractAndPush⟫ ] else [
        if val2 = one then [ ⟪stageOneSaveAndSet⟫; ⟪branchContractAndPush⟫ ] else [
          ⟪combineAndPop⟫ ] ]]
      y_h ((fun z => (z.1, ((4 + z.2) + 1) + 2)) <$> m_c) := by
    convert ExecRand.branch_neg hnc_eq0 hbr1 using 1
    simp only [Functor.map_map]
  have hstep : ExecRand w fastCutStep x
      ((fun z => (z.1, 9 + ((((4 + z.2) + 1) + 2) + 2))) <$> m_c) := by
    unfold fastCutStep
    convert hex_hdr.seqRand (ExecRand.branch_neg hnc_lt hbr0) using 1
    simp only [Functor.map_map]
  have hseg_raw := LoopSegment.single hc_loop hstep
  let m_out : ProbComp (Data 24 × ℕ) :=
    (fun z => (z.1, 9 + ((((4 + z.2) + 1) + 2) + 2) + 2)) <$> m_c
  have hseg : LoopSegment w (Cond.lt zero spReg) fastCutStep x m_out := by
    convert hseg_raw using 1
    simp only [m_out, Functor.map_map]
  refine ⟨m_out, hseg, ?_, ?_, ?_⟩
  · simp only [m_out, OracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
    exact hq_c
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    rcases hsup_c z₀ hz₀ with ⟨ht₀, hmod₀, rest⟩
    have hstg_in : fp + 2 + k * k ∈ Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k) := by
      rw [Finset.mem_Ico]; unfold frameSize at hfs_le; omega
    have hv1_in : fp + 3 + k * k ∈ Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k) := by
      rw [Finset.mem_Ico]; unfold frameSize at hfs_le; omega
    have hmod_s : Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k))
        x.mem y_s.mem := by
      rw [hys_mem]
      exact modifies_trans_subset
        (modifies_update_of_mem hstg_in x.mem 2)
        (modifies_update_of_mem hv1_in _ v1)
        Finset.Subset.rfl Finset.Subset.rfl
    have hsub : Finset.Ico (fp + 4 + k * k) (fp + fastCutScratch k) ⊆
        Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k) := by
      intro a ha; rw [Finset.mem_Ico] at ha ⊢; omega
    have hstg_val : z₀.1.mem (fp + 2 + k * k) = 2 := by
      rw [hmod₀ _ (by rw [Finset.mem_Ico]; omega), hys_mem,
        Function.update_of_ne (by omega), Function.update_self]
    have hv1_val : z₀.1.mem (fp + 3 + k * k) = v1 := by
      rw [hmod₀ _ (by rw [Finset.mem_Ico]; omega), hys_mem, Function.update_self]
    exact ⟨by omega, modifies_trans_subset hmod_s hmod₀ Finset.Subset.rfl hsub,
      hstg_val, hv1_val, rest⟩
  · intro B hmin_pos hB_nt hB_min
    rw [ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    exact hsurv_c B hmin_pos hB_nt hB_min

theorem fastCutStep_stage2_seg {w fp parentFp b k v1 r2 : ℕ} {x : Data 24}
    (hk7 : 7 ≤ k)
    (h0 : x.regs zero = 0) (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1)
    (hr2 : x.regs retVal = r2)
    (hmem_p : x.mem fp = parentFp) (hmem_k : x.mem (fp + 1) = k)
    (hmem_stg : x.mem (fp + 2 + k * k) = 2) (hmem_v1 : x.mem (fp + 3 + k * k) = v1)
    (hfit : Fits w (fp + frameSize k)) (hsp_fit : Fits w b) :
    ∃ (y : Data 24) (n_s2 : ℕ),
      n_s2 ≤ 24 ∧
      LoopSegment w (Cond.lt zero spReg) fastCutStep x (pure (y, n_s2)) ∧
      y.mem = x.mem ∧
      y.regs zero = 0 ∧
      y.regs fpReg = parentFp ∧
      y.regs spReg = b ∧
      y.regs retVal = min v1 r2 := by
  have hc_loop : (Cond.lt zero spReg).Holds x := by simp [Cond.holds_lt, h0, hsp]
  obtain ⟨y_h, hex_hdr, hm_h, h0_h, h1_h, hk_h, _, _, ha2_h, hv2_h, hv1_h, hhi_h⟩ :=
    stepHeader_exec (by omega : 2 ≤ k) hfp hmem_k hmem_stg hfit
  have hfp_h : y_h.regs fpReg = fp := (hhi_h fpReg (by decide)).trans hfp
  have hsp_h : y_h.regs spReg = b + 1 := (hhi_h spReg (by decide)).trans hsp
  have hr2_h : y_h.regs retVal = r2 := (hhi_h retVal (by decide)).trans hr2
  have hnc_lt : ¬(Cond.lt activeK val1).Holds y_h := by
    simp only [Cond.holds_lt, hk_h, hv1_h]; omega
  have hnc_eq0 : ¬(Cond.eq val2 zero).Holds y_h := by
    simp [Cond.holds_eq, hv2_h, h0_h]
  have hnc_eq1 : ¬(Cond.eq val2 one).Holds y_h := by
    simp [Cond.holds_eq, hv2_h, h1_h]
  obtain ⟨y_f, ⟨n_c, hn_c, hex_c⟩, hm_f, h0_f, hfp_f, hsp_f, hret_f⟩ :=
    combineAndPop_exec (by omega : 2 ≤ k) h0_h h1_h ha2_h hfp_h hsp_h hr2_h
      (hm_h ▸ hmem_p) (hm_h ▸ hmem_v1) hfit hsp_fit
  have hstep : Exec w fastCutStep x y_f (9 + (((n_c + 2) + 2) + 2)) := by
    unfold fastCutStep
    exact hex_hdr.seq (.branch_neg hnc_lt (.branch_neg hnc_eq0 (.branch_neg hnc_eq1 hex_c)))
  exact ⟨y_f, 9 + (((n_c + 2) + 2) + 2) + 2, by omega,
    LoopSegment.detSingle hc_loop hstep, hm_f.trans hm_h, h0_f, hfp_f, hsp_f, hret_f⟩

private theorem composeBranchWithChild {n w d' fp b k T_s : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {part : Fin n → Fin k} {P_frame : (ℕ → ℕ) → Prop} {d₀ : Data 24}
    {m_s : ProbComp (Data 24 × ℕ)}
    (hk7 : 7 ≤ k) (hd' : fastCutDepth (fastCutThreshold k) ≤ d')
    (hfit : Fits w (fp + fastCutScratch k)) (hsp_fit : Fits w (b + 1 + (d' + 1)))
    (hm_s : LoopSegment w (Cond.lt zero spReg) fastCutStep d₀ m_s)
    (hq_s : m_s.IsQueryBounded (k - fastCutThreshold k))
    (hsup_s : ∀ z ∈ m_s.support,
      let t := fastCutThreshold k
      let childFp := fp + frameSize k
      z.2 ≤ T_s ∧
      Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) d₀.mem z.1.mem ∧
      P_frame z.1.mem ∧
      z.1.regs zero = 0 ∧
      z.1.regs fpReg = childFp ∧
      z.1.regs spReg = b + 2 ∧
      z.1.mem childFp = fp ∧
      z.1.mem (childFp + 1) = t ∧
      z.1.mem (childFp + 2 + t * t) = 0 ∧
      ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
        IsContractionOf W₀ part' W' ∧
        HoldsMatrix z.1.mem (childFp + 2) t W')
    (hsurv_s : ∀ B : Finset (Fin k),
      0 < minCut W₀ → IsNonTrivialCut B →
      cutWeight W₀ (pullbackCut part B) = minCut W₀ →
      (1 : ℝ≥0∞) / 2 ≤
        m_s.eval.toOuterMeasure
          {z | ChildMinCutSurvives W₀ (fp + frameSize k) (fastCutThreshold k) z.1})
    (hP_pres : ∀ m₁ m₂ : ℕ → ℕ,
      let t := fastCutThreshold k
      let childFp := fp + frameSize k
      Modifies (Finset.Ico (childFp + 2 + t * t) (childFp + fastCutScratch t)) m₁ m₂ →
      P_frame m₁ → P_frame m₂)
    (hih : ∀ {W_t : Fin (fastCutThreshold k) → Fin (fastCutThreshold k) → ℕ}
      {part_t : Fin n → Fin (fastCutThreshold k)} {x_c : Data 24},
      let t := fastCutThreshold k
      let childFp := fp + frameSize k
      2 ≤ t → fastCutDepth t ≤ d' →
      x_c.regs zero = 0 → x_c.regs fpReg = childFp → x_c.regs spReg = (b + 1) + 1 →
      x_c.mem childFp = fp → x_c.mem (childFp + 1) = t → x_c.mem (childFp + 2 + t * t) = 0 →
      HoldsMatrix x_c.mem (childFp + 2) t W_t → IsContractionOf W₀ part_t W_t →
      Fits w (childFp + fastCutScratch t) → Fits w ((b + 1) + 1 + d') →
      ∃ mc : ProbComp (Data 24 × ℕ),
        LoopSegment w (Cond.lt zero spReg) fastCutStep x_c mc ∧
        mc.IsQueryBounded (fastCutNodeQueries t) ∧
        (∀ zc ∈ mc.support,
          zc.2 ≤ fastCutNodeTime t ∧
          Modifies (Finset.Ico (childFp + 2 + t * t) (childFp + fastCutScratch t))
            x_c.mem zc.1.mem ∧
          zc.1.regs zero = 0 ∧
          zc.1.regs fpReg = fp ∧
          zc.1.regs spReg = b + 1 ∧
          ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ zc.1.regs retVal = cutWeight W₀ C) ∧
        (∀ B : Finset (Fin t),
          0 < minCut W₀ → IsNonTrivialCut B →
          cutWeight W₀ (pullbackCut part_t B) = minCut W₀ →
          (2 : ℝ≥0∞) / ((d' + 30 : ℕ) : ℝ≥0∞) ≤
            mc.eval.toOuterMeasure {zc | zc.1.regs retVal = minCut W₀})) :
    let t := fastCutThreshold k
    ∃ m_br : ProbComp (Data 24 × ℕ),
      LoopSegment w (Cond.lt zero spReg) fastCutStep d₀ m_br ∧
      m_br.IsQueryBounded ((k - t) + fastCutNodeQueries t) ∧
      (∀ z ∈ m_br.support,
        z.2 ≤ T_s + fastCutNodeTime t ∧
        Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) d₀.mem z.1.mem ∧
        P_frame z.1.mem ∧
        z.1.regs zero = 0 ∧
        z.1.regs fpReg = fp ∧
        z.1.regs spReg = b + 1 ∧
        ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ z.1.regs retVal = cutWeight W₀ C) ∧
      (∀ B : Finset (Fin k),
        0 < minCut W₀ → IsNonTrivialCut B →
        cutWeight W₀ (pullbackCut part B) = minCut W₀ →
        (1 : ℝ≥0∞) / ((d' + 30 : ℕ) : ℝ≥0∞) ≤
          m_br.eval.toOuterMeasure {z | z.1.regs retVal = minCut W₀}) := by
  intro t
  let childFp := fp + frameSize k
  have ht2 : 2 ≤ t := fastCutThreshold_ge_two (by omega)
  have hscr_eq : fp + fastCutScratch k = childFp + fastCutScratch t := by
    dsimp only [childFp, t]
    rw [fastCutScratch_of_ge_seven hk7]
    omega
  have hfit_c : Fits w (childFp + fastCutScratch t) := hscr_eq ▸ hfit
  have hsp_c : Fits w ((b + 1) + 1 + d') := hsp_fit.of_le (by omega)
  let Q_c (dc : Data 24) (mc : ProbComp (Data 24 × ℕ)) : Prop :=
    mc.IsQueryBounded (fastCutNodeQueries t) ∧
    (∀ zc ∈ mc.support,
      zc.2 ≤ fastCutNodeTime t ∧
      Modifies (Finset.Ico (childFp + 2 + t * t) (childFp + fastCutScratch t))
        dc.mem zc.1.mem ∧
      zc.1.regs zero = 0 ∧
      zc.1.regs fpReg = fp ∧
      zc.1.regs spReg = b + 1 ∧
      ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ zc.1.regs retVal = cutWeight W₀ C) ∧
    (0 < minCut W₀ → ChildMinCutSurvives W₀ childFp t dc →
      (2 : ℝ≥0∞) / ((d' + 30 : ℕ) : ℝ≥0∞) ≤
        mc.eval.toOuterMeasure {zc | zc.1.regs retVal = minCut W₀})
  have hchild_ex : ∀ z₀ ∈ m_s.support,
      ∃ mc, LoopSegment w (Cond.lt zero spReg) fastCutStep z₀.1 mc ∧ Q_c z₀.1 mc := by
    intro z₀ hz₀
    rcases hsup_s z₀ hz₀ with
      ⟨_, _, _, hz0, hzfp, hzsp, hm_cfp, hm_cfp1, hm_stg, W', part', hC', hmat'⟩
    by_cases hgood : 0 < minCut W₀ ∧ ChildMinCutSurvives W₀ childFp t z₀.1
    · rcases hgood with ⟨hmin_pos, W₁, part₁, B₁, hC₁, hmat₁, hB₁_nt, hB₁_min⟩
      obtain ⟨mc, hseg_c, hq_c, hsup_c, hsurv_c⟩ :=
        hih ht2 hd' hz0 hzfp hzsp hm_cfp hm_cfp1 hm_stg hmat₁ hC₁ hfit_c hsp_c
      exact ⟨mc, hseg_c, hq_c, hsup_c, fun _ _ => hsurv_c B₁ hmin_pos hB₁_nt hB₁_min⟩
    · obtain ⟨mc, hseg_c, hq_c, hsup_c, _⟩ :=
        hih ht2 hd' hz0 hzfp hzsp hm_cfp hm_cfp1 hm_stg hmat' hC' hfit_c hsp_c
      exact ⟨mc, hseg_c, hq_c, hsup_c, fun hp hs => absurd ⟨hp, hs⟩ hgood⟩
  obtain ⟨mc_fn, hseg_br, hmc_fn⟩ := hm_s.trans_exists hchild_ex
  let m_br := do let z₀ ← m_s; let zc ← mc_fn z₀.1; pure (zc.1, z₀.2 + zc.2)
  refine ⟨m_br, hseg_br,
    isQueryBounded_seq hq_s (fun z₀ hz₀ => (hmc_fn z₀ hz₀).2.1), ?_, ?_⟩
  · intro z hz
    obtain ⟨z₀, hz₀, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨zc, hzc, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hpure
    rcases hsup_s z₀ hz₀ with ⟨ht₀, hmod₀, hP₀, _⟩
    rcases (hmc_fn z₀ hz₀).2.2.1 zc hzc with ⟨ht_c, hmod_c, hz0, hzfp, hzsp, hcut⟩
    have hsub_c : Finset.Ico (childFp + 2 + t * t) (childFp + fastCutScratch t) ⊆
        Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k) := by
      intro a ha
      rw [Finset.mem_Ico] at ha ⊢
      rw [hscr_eq]; dsimp only [childFp] at *; unfold frameSize at *; omega
    exact ⟨by omega, modifies_trans_subset hmod₀ hmod_c Finset.Subset.rfl hsub_c,
      hP_pres z₀.1.mem zc.1.mem hmod_c hP₀, hz0, hzfp, hzsp, hcut⟩
  · intro B hmin_pos hB_nt hB_min
    have h1 := hsurv_s B hmin_pos hB_nt hB_min
    have hprod := probComp_seq_hit_ge m_s mc_fn
      (ChildMinCutSurvives W₀ childFp t)
      (fun d => d.regs retVal = minCut W₀) h1
      fun z₀ hz₀ hs => (hmc_fn z₀ hz₀).2.2.2 hmin_pos hs
    rwa [half_mul_two_div_eq (by omega : 1 ≤ d' + 30)] at hprod

/-- **Structural `LoopSegment` specification of recursive `FastCut` over depth budget `d`.** -/
theorem fastCutNode_spec {n w : ℕ} {W₀ : Fin n → Fin n → ℕ}
    (htot : Fits w (totalDoubledWeight W₀)) :
    ∀ (d : ℕ) {fp parentFp b k : ℕ} {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k}
      {x : Data 24},
      2 ≤ k →
      fastCutDepth k ≤ d →
      x.regs zero = 0 →
      x.regs fpReg = fp →
      x.regs spReg = b + 1 →
      x.mem fp = parentFp →
      x.mem (fp + 1) = k →
      x.mem (fp + 2 + k * k) = 0 →
      HoldsMatrix x.mem (fp + 2) k W_k →
      IsContractionOf W₀ part W_k →
      Fits w (fp + fastCutScratch k) →
      Fits w (b + 1 + d) →
      ∃ m : ProbComp (Data 24 × ℕ),
        LoopSegment w (Cond.lt zero spReg) fastCutStep x m ∧
        m.IsQueryBounded (fastCutNodeQueries k) ∧
        (∀ z ∈ m.support,
          z.2 ≤ fastCutNodeTime k ∧
          Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) x.mem z.1.mem ∧
          z.1.regs zero = 0 ∧
          z.1.regs fpReg = parentFp ∧
          z.1.regs spReg = b ∧
          ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ z.1.regs retVal = cutWeight W₀ C) ∧
        (∀ B : Finset (Fin k),
          0 < minCut W₀ → IsNonTrivialCut B →
          cutWeight W₀ (pullbackCut part B) = minCut W₀ →
          (2 : ℝ≥0∞) / ((d + 30 : ℕ) : ℝ≥0∞) ≤
            m.eval.toOuterMeasure {z | z.1.regs retVal = minCut W₀}) := by
  intro d
  induction d with
  | zero =>
    intro fp parentFp b k W_k part x hk2 hd0 h0 hfp hsp hmem_p hmem_k _ hmat hC hfit hsp_fit
    have hk6 : k ≤ 6 := by
      by_contra hlt
      have hk7 : 7 ≤ k := by omega
      rw [fastCutDepth_of_ge_seven hk7] at hd0
      omega
    exact fastCutNode_base hk2 hk6 h0 hfp hsp hmem_p hmem_k hmat hC hfit hsp_fit htot
  | succ d' ih =>
    intro fp parentFp b k W_k part x hk2 hd h0 hfp hsp hmem_p hmem_k hmem_stg hmat hC hfit hsp_fit
    by_cases hk7 : 7 ≤ k
    · let t := fastCutThreshold k
      let childFp := fp + frameSize k
      have hd' : fastCutDepth t ≤ d' := by
        dsimp only [t]
        rw [fastCutDepth_of_ge_seven hk7] at hd
        omega
      have hkk49 : 49 ≤ k * k := Nat.mul_le_mul hk7 hk7
      have hfs_le : frameSize k ≤ fastCutScratch k := frameSize_le_fastCutScratch k
      have hsp_b2 : Fits w (b + 2) := hsp_fit.of_le (by omega)
      -- Branch 1: Stage 0 + Child 1
      obtain ⟨m_s0, hm_s0, hq_s0, hsup_s0, hsurv_s0⟩ :=
        fastCutStep_stage0_seg hk7 h0 hfp hsp hmem_k hmem_stg hmat hC hfit hsp_b2 htot
      obtain ⟨m_b1, hseg_b1, hq_b1, hsup_b1, hsurv_b1⟩ :=
        composeBranchWithChild (P_frame := fun mem => mem (fp + 2 + k * k) = 1)
          hk7 hd' hfit hsp_fit hm_s0 hq_s0 hsup_s0 hsurv_s0
          (fun m₁ m₂ hmod h1 => by
            rw [hmod _ (by rw [Finset.mem_Ico]; unfold frameSize; omega)]
            exact h1)
          (fun ht2 hd_c hz0 hzfp hzsp hm_cfp hm_cfp1 hm_stg hmat_c hC_c hfit_c hsp_c =>
            ih ht2 hd_c hz0 hzfp hzsp hm_cfp hm_cfp1 hm_stg hmat_c hC_c hfit_c hsp_c)
      -- Branch 2 + Stage 2 from every supported state `z₁ ∈ m_b1.support`
      let Q_b2 (d₁ : Data 24) (m₂ : ProbComp (Data 24 × ℕ)) : Prop :=
        m₂.IsQueryBounded ((k - t) + fastCutNodeQueries t) ∧
        (∀ zf ∈ m₂.support,
          zf.2 ≤ 80 * (k * k) + 44 + fastCutNodeTime t ∧
          Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) d₁.mem zf.1.mem ∧
          zf.1.regs zero = 0 ∧
          zf.1.regs fpReg = parentFp ∧
          zf.1.regs spReg = b ∧
          (∃ C : Finset (Fin n), IsNonTrivialCut C ∧ zf.1.regs retVal = cutWeight W₀ C) ∧
          (d₁.regs retVal = minCut W₀ → zf.1.regs retVal = minCut W₀)) ∧
        (∀ B : Finset (Fin k),
          0 < minCut W₀ → IsNonTrivialCut B →
          cutWeight W₀ (pullbackCut part B) = minCut W₀ →
          (1 : ℝ≥0∞) / ((d' + 30 : ℕ) : ℝ≥0∞) ≤
            m₂.eval.toOuterMeasure {zf | zf.1.regs retVal = minCut W₀})
      have hb2_ex : ∀ z₁ ∈ m_b1.support,
          ∃ m₂, LoopSegment w (Cond.lt zero spReg) fastCutStep z₁.1 m₂ ∧ Q_b2 z₁.1 m₂ := by
        intro z₁ hz₁
        rcases hsup_b1 z₁ hz₁ with ⟨_, hmod₁, hstg₁, hz1_0, hz1_fp, hz1_sp, C₁, hC₁_nt, hret₁⟩
        let v₁ := z₁.1.regs retVal
        have hm1_p : z₁.1.mem fp = parentFp := by
          rw [hmod₁ _ (by rw [Finset.mem_Ico]; omega)]; exact hmem_p
        have hm1_k : z₁.1.mem (fp + 1) = k := by
          rw [hmod₁ _ (by rw [Finset.mem_Ico]; omega)]; exact hmem_k
        have hm1_mat : HoldsMatrix z₁.1.mem (fp + 2) k W_k := by
          intro i j
          have hlt : fp + 2 + i.val * k + j.val < fp + 2 + k * k :=
            matAddr_lt_end (le_refl k) i j
          rw [hmod₁ _ (by rw [Finset.mem_Ico]; omega)]
          exact hmat i j
        obtain ⟨m_s1, hm_s1, hq_s1, hsup_s1, hsurv_s1⟩ :=
          fastCutStep_stage1_seg (v1 := v₁) hk7 hz1_0 hz1_fp hz1_sp rfl hm1_k hstg₁ hm1_mat
            hC hfit hsp_b2 htot
        obtain ⟨m_b2_pre, hseg_pre, hq_pre, hsup_pre, hsurv_pre⟩ :=
          composeBranchWithChild
            (P_frame := fun mem => mem (fp + 2 + k * k) = 2 ∧ mem (fp + 3 + k * k) = v₁)
            hk7 hd' hfit hsp_fit hm_s1 hq_s1
            (fun z hz => by
              rcases hsup_s1 z hz with ⟨ht, hmod, hs2, hv, rest⟩
              exact ⟨ht, hmod, ⟨hs2, hv⟩, rest⟩)
            hsurv_s1
            (fun m₁ m₂ hmod ⟨hs2, hv⟩ => ⟨by
              rw [hmod _ (by rw [Finset.mem_Ico]; unfold frameSize; omega)]; exact hs2, by
              rw [hmod _ (by rw [Finset.mem_Ico]; unfold frameSize; omega)]; exact hv⟩)
            (fun ht2 hd_c hz0 hzfp hzsp hm_cfp hm_cfp1 hm_stg hmat_c hC_c hfit_c hsp_c =>
              ih ht2 hd_c hz0 hzfp hzsp hm_cfp hm_cfp1 hm_stg hmat_c hC_c hfit_c hsp_c)
        -- Append deterministic Stage 2 (`combineAndPop`)
        let Q_s2 (d₂ : Data 24) (ms2 : ProbComp (Data 24 × ℕ)) : Prop :=
          ms2.IsQueryBounded 0 ∧
          ∀ zf ∈ ms2.support,
            zf.2 ≤ 24 ∧
            zf.1.mem = d₂.mem ∧
            zf.1.regs zero = 0 ∧
            zf.1.regs fpReg = parentFp ∧
            zf.1.regs spReg = b ∧
            zf.1.regs retVal = min v₁ (d₂.regs retVal)
        have hs2_ex : ∀ z₂ ∈ m_b2_pre.support,
            ∃ ms2, LoopSegment w (Cond.lt zero spReg) fastCutStep z₂.1 ms2 ∧ Q_s2 z₂.1 ms2 := by
          intro z₂ hz₂
          rcases hsup_pre z₂ hz₂ with ⟨_, hmod₂, ⟨hstg₂, hv1_₂⟩, hz2_0, hz2_fp, hz2_sp, _⟩
          have hm2_p : z₂.1.mem fp = parentFp := by
            rw [hmod₂ _ (by rw [Finset.mem_Ico]; omega)]; exact hm1_p
          have hm2_k : z₂.1.mem (fp + 1) = k := by
            rw [hmod₂ _ (by rw [Finset.mem_Ico]; omega)]; exact hm1_k
          obtain ⟨y_f, n_s2, hn_s2, hseg_f, hm_f, h0_f, hfp_f, hsp_f, hret_f⟩ :=
            fastCutStep_stage2_seg hk7 hz2_0 hz2_fp hz2_sp rfl hm2_p hm2_k hstg₂ hv1_₂
              (hfit.of_le (by omega)) (hsp_fit.of_le (by omega))
          refine ⟨pure (y_f, n_s2), hseg_f, .pure _ 0, fun zf hzf => ?_⟩
          cases OracleComp.eq_of_mem_supportWith_pure hzf
          exact ⟨hn_s2, hm_f, h0_f, hfp_f, hsp_f, hret_f⟩
        obtain ⟨ms2_fn, hseg_b2, hms2_fn⟩ := hseg_pre.trans_exists hs2_ex
        let m₂ := do let z₂ ← m_b2_pre; let zf ← ms2_fn z₂.1; pure (zf.1, z₂.2 + zf.2)
        have hq_m₂ : m₂.IsQueryBounded ((k - t) + fastCutNodeQueries t) := by
          simpa only [Nat.add_zero] using
            isQueryBounded_seq hq_pre (fun z₂ hz₂ => (hms2_fn z₂ hz₂).2.1)
        refine ⟨m₂, hseg_b2, hq_m₂, ?_, ?_⟩
        · intro zf hzf
          obtain ⟨z₂, hz₂, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hzf
          obtain ⟨zs, hzs, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
          cases OracleComp.eq_of_mem_supportWith_pure hpure
          rcases hsup_pre z₂ hz₂ with ⟨ht₂, hmod₂, _, _, _, _, C₂, hC₂_nt, hret₂⟩
          rcases (hms2_fn z₂ hz₂).2.2 zs hzs with ⟨ht_s, hm_s, h0_s, hfp_s, hsp_s, hret_s⟩
          have hv1_ge : minCut W₀ ≤ v₁ := by
            dsimp only [v₁]
            rw [hret₁]
            exact minCut_le_cutWeight W₀ hC₁_nt
          have hv2_ge : minCut W₀ ≤ z₂.1.regs retVal := by
            rw [hret₂]
            exact minCut_le_cutWeight W₀ hC₂_nt
          refine ⟨by dsimp only [t] at ht₂ ⊢; omega, hm_s ▸ hmod₂, h0_s, hfp_s, hsp_s, ?_, ?_⟩
          · rw [hret_s]
            by_cases hle : v₁ ≤ z₂.1.regs retVal
            · exact ⟨C₁, hC₁_nt, by rw [min_eq_left hle]; exact hret₁⟩
            · exact ⟨C₂, hC₂_nt, by rw [min_eq_right (by omega)]; exact hret₂⟩
          · intro hv1_eq
            rw [hret_s]
            have hv1_eq' : v₁ = minCut W₀ := hv1_eq
            rw [hv1_eq']
            exact min_eq_left hv2_ge
        · intro B hmin_pos hB_nt hB_min
          have hp_pre := hsurv_pre B hmin_pos hB_nt hB_min
          have hprod := probComp_seq_hit_ge m_b2_pre ms2_fn
            (fun d₂ => d₂.regs retVal = minCut W₀)
            (fun df => df.regs retVal = minCut W₀) hp_pre
            fun z₂ hz₂ hr₂_min => by
              have hv1_ge : minCut W₀ ≤ v₁ := by
                dsimp only [v₁]; rw [hret₁]; exact minCut_le_cutWeight W₀ hC₁_nt
              suffices h1 : (1 : ℝ≥0∞) ≤
                  (ms2_fn z₂.1).eval.toOuterMeasure
                    {zs | zs.1.regs retVal = minCut W₀} from h1
              have hcompl0 : (ms2_fn z₂.1).eval.toOuterMeasure
                  {zs | zs.1.regs retVal = minCut W₀}ᶜ = 0 := by
                rw [PMF.toOuterMeasure_apply]
                refine tsum_eq_zero_iff.mpr fun zs => ?_
                by_cases hzs_ev : zs ∈ (ms2_fn z₂.1).eval.support
                · have hzs : zs ∈ (ms2_fn z₂.1).support :=
                    (ProbComp.support_eval (ms2_fn z₂.1)) ▸ hzs_ev
                  rcases (hms2_fn z₂ hz₂).2.2 zs hzs with ⟨_, _, _, _, _, hret_s⟩
                  have hhit_zs : zs.1.regs retVal = minCut W₀ := by
                    rw [hret_s, hr₂_min]
                    exact min_eq_right hv1_ge
                  have hnot : zs ∉ ({zs : Data 24 × ℕ | zs.1.regs retVal = minCut W₀}ᶜ) := by
                    simp [hhit_zs]
                  exact Set.indicator_of_notMem hnot _
                · have hp0 : (ms2_fn z₂.1).eval zs = 0 := by
                    simpa only [PMF.mem_support_iff, not_not] using hzs_ev
                  simp [hp0]
              have hsum := toOuterMeasure_add_compl_ennreal (ms2_fn z₂.1).eval
                {zs | zs.1.regs retVal = minCut W₀}
              rw [hcompl0, add_zero] at hsum
              exact hsum.ge
          simpa only [mul_one] using hprod
      obtain ⟨m₂_fn, hseg_tot, hm₂_fn⟩ := hseg_b1.trans_exists hb2_ex
      let m_tot := do let z₁ ← m_b1; let z₂ ← m₂_fn z₁.1; pure (z₂.1, z₁.2 + z₂.2)
      refine ⟨m_tot, hseg_tot, ?_, ?_, ?_⟩
      · have hq_tot := isQueryBounded_seq hq_b1 (fun z₁ hz₁ => (hm₂_fn z₁ hz₁).2.1)
        refine hq_tot.mono ?_
        rw [fastCutNodeQueries_of_ge_seven hk7]
        dsimp only [t]
        omega
      · intro z hz
        obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
        obtain ⟨z₂, hz₂, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
        cases OracleComp.eq_of_mem_supportWith_pure hpure
        rcases hsup_b1 z₁ hz₁ with ⟨ht₁, hmod₁, _⟩
        rcases (hm₂_fn z₁ hz₁).2.2.1 z₂ hz₂ with
          ⟨ht₂, hmod₂, hz0, hzfp, hzsp, hcut, _⟩
        refine ⟨?_, modifies_trans_subset hmod₁ hmod₂ Finset.Subset.rfl Finset.Subset.rfl,
          hz0, hzfp, hzsp, hcut⟩
        rw [fastCutNodeTime_of_ge_seven hk7]
        dsimp only [t] at ht₁ ht₂
        omega
      · intro B hmin_pos hB_nt hB_min
        have hrec := ProbComp.two_branch_hit_prob_ge m_b1 (fun z₁ => m₂_fn z₁.1)
          (fun z₁ z₂ => (z₂.1, z₁.2 + z₂.2))
          {z₁ | z₁.1.regs retVal = minCut W₀}
          {z | z.1.regs retVal = minCut W₀}
          (s := d' + 30) (by omega)
          (hsurv_b1 B hmin_pos hB_nt hB_min)
          (fun z₁ hz₁ hhit₁ z₂ hz₂ => ((hm₂_fn z₁ hz₁).2.2.1 z₂ hz₂).2.2.2.2.2.2 hhit₁)
          (fun z₁ hz₁ _ => by
            rw [PMF.toOuterMeasure_map_apply]
            exact (hm₂_fn z₁ hz₁).2.2.2 B hmin_pos hB_nt hB_min)
        have heq_s : (d' + 30) + 1 = d' + 1 + 30 := by omega
        rwa [heq_s] at hrec
    · exact fastCutNode_base hk2 (by omega) h0 hfp hsp hmem_p hmem_k hmat hC hfit hsp_fit htot

/-- Root-frame setup before copying the input matrix `W` from `srcBase` into `fp₀ + 2`. -/
def fastCutRootSetup : Code .standard 24 := ram[
  zero ← #0;
  one ← #1;
  rem ← nOrig * nOrig;
  fpReg ← srcBase + rem;
  *fpReg ← zero;
  addr1 ← fpReg + one;
  *addr1 ← nOrig;
  uReg ← srcBase;
  wBase ← addr1 + one
]

/-- Root-frame stage/stack-pointer initialization after copying `W` into `fp₀ + 2`. -/
def fastCutRootFinish : Code .standard 24 := ram[
  zero ← #0;
  one ← #1;
  rem ← nOrig * nOrig;
  addr2 ← wBase + rem;
  *addr2 ← zero;
  spReg ← #1
]

/-- Single `FastCut` tree execution from `srcBase` and `nOrig`, writing `retVal` and preserving
`srcBase`, `nOrig`, `numTrials`, `trialIdx`, and `bestVal`. -/
def fastCutTree : Code .standard 24 := ram[
  ⟪fastCutRootSetup⟫;
  ⟪ksCopyCode⟫;
  ⟪fastCutRootFinish⟫;
  ⟪fastCutLoop⟫
]

theorem fastCutTree_spec {n w sb : ℕ} {W : Fin n → Fin n → ℕ} {x : Data 24}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hsb : x.regs srcBase = sb) (hnOrig : x.regs nOrig = n)
    (hmat : HoldsMatrix x.mem sb n W)
    (hws_fit : Fits w (sb + 27 * (n * n)))
    (hsp_fit : Fits w (2 * Nat.log 2 n + 1))
    (htot : Fits w (totalDoubledWeight W)) :
    ∃ m : ProbComp (Data 24 × ℕ),
      ExecRand w fastCutTree x m ∧
      m.IsQueryBounded (fastCutNodeQueries n) ∧
      (∀ z ∈ m.support,
        z.2 ≤ fastCutNodeTime n + 7 * (n * n) + 21 ∧
        Modifies (Finset.Ico (sb + n * n) (sb + 27 * (n * n))) x.mem z.1.mem ∧
        z.1.regs srcBase = sb ∧
        z.1.regs nOrig = n ∧
        z.1.regs numTrials = x.regs numTrials ∧
        z.1.regs trialIdx = x.regs trialIdx ∧
        z.1.regs bestVal = x.regs bestVal ∧
        ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ z.1.regs retVal = cutWeight W C) ∧
      (0 < minCut W →
        (1 : ℝ≥0∞) / ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞) ≤
          m.eval.toOuterMeasure {z | z.1.regs retVal = minCut W}) := by
  let fp₀ := sb + n * n
  have hscr_le : fastCutScratch n ≤ 26 * (n * n) := fastCutScratch_le hn
  have hfs_le : frameSize n ≤ fastCutScratch n := frameSize_le_fastCutScratch n
  have hnn_ge : 4 ≤ n * n := Nat.mul_le_mul hn hn
  have hfit_scr : Fits w (fp₀ + fastCutScratch n) := hws_fit.of_le (by dsimp only [fp₀]; omega)
  have hfit_fs : Fits w (fp₀ + frameSize n) := hfit_scr.of_le (by omega)
  have h0_fit : Fits w 0 := fits_zero w
  have h1_fit : Fits w 1 := hfit_fs.of_le (by unfold frameSize; omega)
  have hnn_fit : Fits w (n * n) := hfit_fs.of_le (by unfold frameSize; omega)
  have hfp_fit : Fits w fp₀ := hfit_fs.of_le (by omega)
  have hfp1_fit : Fits w (fp₀ + 1) := hfit_fs.of_le (by unfold frameSize; omega)
  have hfp2_fit : Fits w (fp₀ + 2) := hfit_fs.of_le (by unfold frameSize; omega)
  have hstg_fit : Fits w (fp₀ + 2 + n * n) := hfit_fs.of_le (by unfold frameSize; omega)
  -- Step 1: `fastCutRootSetup`
  let r₁ := x.set zero 0
  let r₂ := r₁.set one 1
  let r₃ := r₂.set rem (n * n)
  let r₄ := r₃.set fpReg fp₀
  let r₅ := r₄.write fp₀ 0
  let r₆ := r₅.set addr1 (fp₀ + 1)
  let r₇ := r₆.write (fp₀ + 1) n
  let r₈ := r₇.set uReg sb
  let x₁ := r₈.set wBase (fp₀ + 2)
  have hex_rset : Exec w fastCutRootSetup x x₁ 9 := by
    have s1 : Exec (B := .standard) w ram[zero ← #0] x r₁ 1 := Exec.const h0_fit
    have s2 : Exec (B := .standard) w ram[one ← #1] r₁ r₂ 1 := Exec.const h1_fit
    have s3 : Exec w ram[rem ← nOrig * nOrig] r₂ r₃ 1 := by
      have hn' : r₂.regs nOrig = n := by simpa +decide [r₂, r₁, Function.update_apply] using hnOrig
      simpa [r₃, BinOp.eval, hn'] using
        Exec.bin (f := .mul) (d := rem) (i := nOrig) (j := nOrig) (x := r₂)
          (by simpa [BinOp.eval, hn'] using hnn_fit)
    have s4 : Exec w ram[fpReg ← srcBase + rem] r₃ r₄ 1 := by
      have hsb' : r₃.regs srcBase = sb := by
        simpa +decide [r₃, r₂, r₁, Function.update_apply] using hsb
      have hr' : r₃.regs rem = n * n := by simp [r₃]
      simpa [r₄, BinOp.eval, hsb', hr', fp₀] using
        Exec.bin (f := .add) (d := fpReg) (i := srcBase) (j := rem) (x := r₃)
          (by simpa [BinOp.eval, hsb', hr', fp₀] using hfp_fit)
    have s5 : Exec (B := .standard) w ram[*fpReg ← zero] r₄ r₅ 1 := by
      have hfp' : r₄.regs fpReg = fp₀ := by simp [r₄]
      have hz' : r₄.regs zero = 0 := by simp +decide [r₄, r₃, r₂, r₁]
      simpa [r₅, hfp', hz'] using
        Exec.store (B := .standard) (w := w) (a := fpReg) (s := zero) (x := r₄)
    have s6 : Exec w ram[addr1 ← fpReg + one] r₅ r₆ 1 := by
      have hfp' : r₅.regs fpReg = fp₀ := by simp +decide [r₅, r₄]
      have h1' : r₅.regs one = 1 := by simp +decide [r₅, r₄, r₃, r₂]
      simpa [r₆, BinOp.eval, hfp', h1'] using
        Exec.bin (f := .add) (d := addr1) (i := fpReg) (j := one) (x := r₅)
          (by simpa [BinOp.eval, hfp', h1'] using hfp1_fit)
    have s7 : Exec (B := .standard) w ram[*addr1 ← nOrig] r₆ r₇ 1 := by
      have ha1 : r₆.regs addr1 = fp₀ + 1 := by simp [r₆]
      have hn' : r₆.regs nOrig = n := by
        simpa +decide [r₆, r₅, r₄, r₃, r₂, r₁, Function.update_apply] using hnOrig
      simpa [r₇, ha1, hn'] using
        Exec.store (B := .standard) (w := w) (a := addr1) (s := nOrig) (x := r₆)
    have s8 : Exec (B := .standard) w ram[uReg ← srcBase] r₇ r₈ 1 := by
      have hsb' : r₇.regs srcBase = sb := by
        simpa +decide [r₇, r₆, r₅, r₄, r₃, r₂, r₁, Function.update_apply] using hsb
      simpa [r₈, hsb'] using
        Exec.copy (B := .standard) (w := w) (d := uReg) (s := srcBase) (x := r₇)
    have s9 : Exec w ram[wBase ← addr1 + one] r₈ x₁ 1 := by
      have ha1 : r₈.regs addr1 = fp₀ + 1 := by simp +decide [r₈, r₇, r₆]
      have h1' : r₈.regs one = 1 := by simp +decide [r₈, r₇, r₆, r₅, r₄, r₃, r₂]
      have heq : (fp₀ + 1) + 1 = fp₀ + 2 := by omega
      simpa [x₁, BinOp.eval, ha1, h1', heq] using
        Exec.bin (f := .add) (d := wBase) (i := addr1) (j := one) (x := r₈)
          (by simpa [BinOp.eval, ha1, h1', heq] using hfp2_fit)
    unfold fastCutRootSetup
    exact s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq s9)))))))
  have hx₁_mem : x₁.mem = Function.update (Function.update x.mem fp₀ 0) (fp₀ + 1) n := rfl
  have hx₁_src : HoldsMatrix x₁.mem sb n W := by
    intro i j
    have hlt : sb + i.val * n + j.val < fp₀ := matAddr_lt_end (wb := sb) (le_refl n) i j
    rw [hx₁_mem, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hmat i j
  -- Step 2: `ksCopyCode`
  obtain ⟨x₂, ⟨n_cp, hn_cp, hex_cp⟩, hmat_cp, hmod_cp, _, hwb₂, _, _, _, _, _⟩ :=
    ksCopyCode_exec (x := x₁) (sb := sb) (db := fp₀ + 2) (k := n) (W := W)
      (by simp +decide [x₁, r₈])
      (by simp [x₁])
      (by simp +decide [x₁, r₈, r₇, r₆, r₅, r₄, r₃])
      (by dsimp only [fp₀]; omega) h1_fit hstg_fit hx₁_src
  -- Step 3: `fastCutRootFinish`
  have hn_x₂ : x₂.regs nOrig = n :=
    (hex_cp.regs_eq (by decide)).trans (hex_rset.regs_eq (by decide) |>.trans hnOrig)
  have hfp_x₂ : x₂.regs fpReg = fp₀ := by
    rw [hex_cp.regs_eq (by decide)]
    simp +decide [x₁, r₈, r₇, r₆, r₅, r₄]
  let q₁ := x₂.set zero 0
  let q₂ := q₁.set one 1
  let q₃ := q₂.set rem (n * n)
  let q₄ := q₃.set addr2 (fp₀ + 2 + n * n)
  let q₅ := q₄.write (fp₀ + 2 + n * n) 0
  let x₃ := q₅.set spReg 1
  have hex_rfin : Exec w fastCutRootFinish x₂ x₃ 6 := by
    have s1 : Exec (B := .standard) w ram[zero ← #0] x₂ q₁ 1 := Exec.const h0_fit
    have s2 : Exec (B := .standard) w ram[one ← #1] q₁ q₂ 1 := Exec.const h1_fit
    have s3 : Exec w ram[rem ← nOrig * nOrig] q₂ q₃ 1 := by
      have hn' : q₂.regs nOrig = n := by
        simpa +decide [q₂, q₁, Function.update_apply] using hn_x₂
      simpa [q₃, BinOp.eval, hn'] using
        Exec.bin (f := .mul) (d := rem) (i := nOrig) (j := nOrig) (x := q₂)
          (by simpa [BinOp.eval, hn'] using hnn_fit)
    have s4 : Exec w ram[addr2 ← wBase + rem] q₃ q₄ 1 := by
      have hwb' : q₃.regs wBase = fp₀ + 2 := by
        simpa +decide [q₃, q₂, q₁, Function.update_apply] using hwb₂
      have hr' : q₃.regs rem = n * n := by simp [q₃]
      simpa [q₄, BinOp.eval, hwb', hr'] using
        Exec.bin (f := .add) (d := addr2) (i := wBase) (j := rem) (x := q₃)
          (by simpa [BinOp.eval, hwb', hr'] using hstg_fit)
    have s5 : Exec (B := .standard) w ram[*addr2 ← zero] q₄ q₅ 1 := by
      have ha2 : q₄.regs addr2 = fp₀ + 2 + n * n := by simp [q₄]
      have hz' : q₄.regs zero = 0 := by simp +decide [q₄, q₃, q₂, q₁]
      simpa [q₅, ha2, hz'] using
        Exec.store (B := .standard) (w := w) (a := addr2) (s := zero) (x := q₄)
    have s6 : Exec (B := .standard) w ram[spReg ← #1] q₅ x₃ 1 := Exec.const h1_fit
    unfold fastCutRootFinish
    exact s1.seq (s2.seq (s3.seq (s4.seq (s5.seq s6))))
  have hx₃_mem : x₃.mem = Function.update x₂.mem (fp₀ + 2 + n * n) 0 := rfl
  have hx₃_p : x₃.mem fp₀ = 0 := by
    rw [hx₃_mem, Function.update_of_ne (by omega), hmod_cp _ (by rw [Finset.mem_Ico]; omega),
      hx₁_mem, Function.update_of_ne (by omega), Function.update_self]
  have hx₃_k : x₃.mem (fp₀ + 1) = n := by
    rw [hx₃_mem, Function.update_of_ne (by omega), hmod_cp _ (by rw [Finset.mem_Ico]; omega),
      hx₁_mem, Function.update_self]
  have hx₃_stg : x₃.mem (fp₀ + 2 + n * n) = 0 := by
    rw [hx₃_mem, Function.update_self]
  have hx₃_mat : HoldsMatrix x₃.mem (fp₀ + 2) n W := by
    intro i j
    have hlt : fp₀ + 2 + i.val * n + j.val < fp₀ + 2 + n * n := matAddr_lt_end (le_refl n) i j
    rw [hx₃_mem, Function.update_of_ne (by omega)]
    exact hmat_cp i j
  -- Step 4: `fastCutLoop` via `fastCutNode_spec` + `LoopSegment.finish`
  obtain ⟨m_seg, hseg, hq_seg, hsup_seg, hsurv_seg⟩ :=
    fastCutNode_spec htot (2 * Nat.log 2 n) (b := 0) (parentFp := 0)
      hn (fastCutDepth_le_two_mul_log n)
      (by simp +decide [x₃, q₅, q₄, q₃, q₂, q₁])
      (by simpa +decide [x₃, q₅, q₄, q₃, q₂, q₁, Function.update_apply] using hfp_x₂)
      (by simp [x₃])
      hx₃_p hx₃_k hx₃_stg hx₃_mat (isContractionOf_id hW) hfit_scr
      (by simpa only [Nat.zero_add, Nat.add_comm 1] using hsp_fit)
  have hex_loop : ExecRand w fastCutLoop x₃ ((fun z => (z.1, z.2 + 2)) <$> m_seg) :=
    hseg.finish fun z hz => by
      rcases hsup_seg z hz with ⟨_, _, hz0, _, hzsp, _⟩
      simp [Cond.holds_lt, hz0, hzsp]
  have htree_raw := hex_rset.seqRand (hex_cp.seqRand (hex_rfin.seqRand hex_loop))
  let m_out : ProbComp (Data 24 × ℕ) :=
    (fun z => (z.1, 9 + (n_cp + (6 + (z.2 + 2))))) <$> m_seg
  have htree : ExecRand w fastCutTree x m_out := by
    unfold fastCutTree
    convert htree_raw using 1
    simp only [m_out, Functor.map_map]
  refine ⟨m_out, htree, ?_, ?_, ?_⟩
  · simp only [m_out, OracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
    exact hq_seg
  · intro z hz
    have hsb_z : z.1.regs srcBase = sb := (htree.regs_eq (by decide) hz).trans hsb
    have hn_z : z.1.regs nOrig = n := (htree.regs_eq (by decide) hz).trans hnOrig
    have hnt_z : z.1.regs numTrials = x.regs numTrials := htree.regs_eq (by decide) hz
    have hti_z : z.1.regs trialIdx = x.regs trialIdx := htree.regs_eq (by decide) hz
    have hbv_z : z.1.regs bestVal = x.regs bestVal := htree.regs_eq (by decide) hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    rcases hsup_seg z₀ hz₀ with ⟨ht₀, hmod₀, _, _, _, hcut⟩
    refine ⟨by omega, ?_, hsb_z, hn_z, hnt_z, hti_z, hbv_z, hcut⟩
    let S_all := Finset.Ico fp₀ (sb + 27 * (n * n))
    have hfp_in : fp₀ ∈ S_all := by rw [Finset.mem_Ico]; dsimp only [fp₀]; omega
    have hfp1_in : fp₀ + 1 ∈ S_all := by rw [Finset.mem_Ico]; dsimp only [fp₀]; omega
    have hstg_in : fp₀ + 2 + n * n ∈ S_all := by rw [Finset.mem_Ico]; dsimp only [fp₀]; omega
    have hmod_x₁ : Modifies S_all x.mem x₁.mem := by
      rw [hx₁_mem]
      exact modifies_trans_subset
        (modifies_update_of_mem hfp_in x.mem 0)
        (modifies_update_of_mem hfp1_in _ n)
        Finset.Subset.rfl Finset.Subset.rfl
    have hsub_cp : Finset.Ico (fp₀ + 2) (fp₀ + 2 + n * n) ⊆ S_all := by
      intro a ha; rw [Finset.mem_Ico] at ha ⊢; dsimp only [fp₀] at ha ⊢; omega
    have hmod_x₃ : Modifies S_all x₂.mem x₃.mem := by
      rw [hx₃_mem]
      exact modifies_update_of_mem hstg_in x₂.mem 0
    have hsub_seg : Finset.Ico (fp₀ + 2 + n * n) (fp₀ + fastCutScratch n) ⊆ S_all := by
      intro a ha; rw [Finset.mem_Ico] at ha ⊢; dsimp only [fp₀] at ha ⊢; omega
    exact modifies_trans_subset
      (modifies_trans_subset
        (modifies_trans_subset hmod_x₁ hmod_cp Finset.Subset.rfl hsub_cp)
        hmod_x₃ Finset.Subset.rfl Finset.Subset.rfl)
      hmod₀ Finset.Subset.rfl hsub_seg
  · intro hmin_pos
    obtain ⟨C_star, hC_nt, hC_min⟩ := exists_minCut_achiever (by rwa [Fintype.card_fin]) W
    have hpb : pullbackCut (id : Fin n → Fin n) C_star = C_star := by
      ext u; simp [pullbackCut]
    have hprob := hsurv_seg C_star hmin_pos hC_nt (by rw [hpb, hC_min])
    rw [root_hit_prob_eq n] at hprob
    rw [ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    exact hprob

end FrameMachine

/-! ### Endpoint 1: Single-tree recursive `FastCut` (`r = 24`) -/

section FastCutSingle

open KSReg

/-- Setup for `fastCutCode` on `n :: flattenMatrix W`: load `n = mem[1]` and set `srcBase = 2`. -/
def fastCutSetup : Code .standard 24 := ram[
  one ← #1;
  nOrig ← *one;
  srcBase ← #2
]

/-- Structured 24-register single-tree Karger–Stein `FastCut` code on `n :: flattenMatrix W`. -/
def fastCutCode : Code .standard 24 := ram[
  ⟪fastCutSetup⟫;
  ⟪fastCutTree⟫
]

/-- Compiled 24-register single-tree Karger–Stein `FastCut` program. -/
def fastCutProgram : Program .standard 24 :=
  fastCutCode.program retVal

/-- Worst-case `O(n ^ 2 log n)` instruction bound `2500 * n ^ 2 * (Nat.log 2 n + 2)` for
`fastCutProgram`. -/
def fastCutTime (n : ℕ) : ℕ :=
  2500 * n ^ 2 * (Nat.log 2 n + 2)

private theorem fits_sp_of_ws {n w : ℕ} (hn : 2 ≤ n) (hws : Fits w (2 + 27 * (n * n))) :
    Fits w (2 * Nat.log 2 n + 1) := by
  have hlog : Nat.log 2 n < n := Nat.log_lt_self 2 (by omega)
  have hmul : n ≤ n * n := Nat.le_mul_self n
  exact hws.of_le (by omega)

private theorem fastCutTime_bound {n : ℕ} (hn : 2 ≤ n) :
    3 + (fastCutNodeTime n + 7 * (n * n) + 21) + 1 ≤ fastCutTime n := by
  unfold fastCutTime
  have hnt := fastCutNodeTime_le hn
  have hnn : n * n = n ^ 2 := (sq n).symm
  rw [hnn]
  have hn2 : 4 ≤ n ^ 2 := by nlinarith
  have hlg : 2 ≤ Nat.log 2 n + 2 := by omega
  have hov : 7 * n ^ 2 + 25 ≤ 100 * n ^ 2 * (Nat.log 2 n + 2) := by nlinarith
  linarith

theorem fastCutSetup_exec {w n : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hw : logWidth 4 n ≤ w) :
    ∃ y : Data 24, Exec w fastCutSetup (Data.init (n :: flattenMatrix W)) y 3 ∧
      y.mem = (Data.init (r := 24) (n :: flattenMatrix W)).mem ∧
      y.regs srcBase = 2 ∧
      y.regs nOrig = n := by
  have hws := fits_fastCutWorkspace_of_logWidth_four hn hw
  have h1 : Fits w 1 := hws.of_le (by omega)
  have h2 : Fits w 2 := hws.of_le (by omega)
  let x₀ : Data 24 := Data.init (n :: flattenMatrix W)
  have hm1 : x₀.mem 1 = n := rfl
  let s₁ := x₀.set one 1
  let s₂ := s₁.set nOrig n
  let s₃ := s₂.set srcBase 2
  have e1 : Exec (B := .standard) w ram[one ← #1] x₀ s₁ 1 := Exec.const h1
  have e2 : Exec (B := .standard) w ram[nOrig ← *one] s₁ s₂ 1 := by
    have hr : s₁.regs one = 1 := by simp [s₁]
    simpa [s₂, s₁, hr, hm1] using
      Exec.load (B := .standard) (w := w) (d := nOrig) (a := one) (x := s₁)
  have e3 : Exec (B := .standard) w ram[srcBase ← #2] s₂ s₃ 1 := Exec.const h2
  exact ⟨s₃, e1.seq (e2.seq e3), rfl, by simp [s₃], by simp +decide [s₃, s₂]⟩

/-- Structured `ProbComp` specification of `fastCutCode`. -/
theorem fastCutCode_spec {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 4 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    ∃ m : ProbComp (Data 24 × ℕ),
      ExecRand w fastCutCode (Data.init (n :: flattenMatrix W)) m ∧
      m.IsQueryBounded (fastCutNodeQueries n) ∧
      (∀ z ∈ m.support,
        z.2 + 1 ≤ fastCutTime n ∧
        Modifies (Finset.Ico (2 + n * n) (2 + 27 * (n * n)))
          (Data.init (r := 24) (n :: flattenMatrix W)).mem z.1.mem ∧
        ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ z.1.regs retVal = cutWeight W C) ∧
      (0 < minCut W →
        (1 : ℝ≥0∞) / ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞) ≤
          m.eval.toOuterMeasure {z | z.1.regs retVal = minCut W}) := by
  have hws := fits_fastCutWorkspace_of_logWidth_four hn hw
  have hsp := fits_sp_of_ws hn hws
  obtain ⟨y_s, e_s, hm_s, hsb_s, hn_s⟩ := fastCutSetup_exec (W := W) hn hw
  obtain ⟨m_t, hm_t, hq_t, hsup_t, hsurv_t⟩ :=
    fastCutTree_spec hn hW hsb_s hn_s (hm_s ▸ holdsMatrix_init_fastCut W) hws hsp htot
  have hbound := fastCutTime_bound hn
  refine ⟨_, e_s.seqRand hm_t, ?_, ?_, ?_⟩
  · simp only [OracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
    exact hq_t
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    rcases hsup_t z₀ hz₀ with ⟨ht₀, hmod₀, _, _, _, _, _, hcut₀⟩
    exact ⟨by omega, hm_s ▸ hmod₀, hcut₀⟩
  · intro hmin_pos
    rw [ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    exact hsurv_t hmin_pos

/-- **Single-tree Karger–Stein `FastCut` specification (`fastCutProgram`, `[KargerStein1996]`,
Section 4, Figure 6 and Lemmas 4.1–4.3; paraphrase).**
At word size `w ≥ logWidth 4 n` when `2 ≤ n` and `totalDoubledWeight W < 2 ^ w`:
1. `fastCutProgram` halts within `fastCutTime n = 2500 * n ^ 2 * (Nat.log 2 n + 2)` steps;
2. executes at most `fastCutNodeQueries n` (`≤ 6 * (n * n)`) `rand` calls;
3. on every supported branch, outputs `cutWeight W C ≥ minCut W` for a genuine non-trivial cut `C`
   of `W` while modifying memory only in `[2 + n * n, 2 + 27 * (n * n))`;
4. when `0 < minCut W` (excluded only for proof convenience), outputs `minCut W` with probability at
   least `1 / (Nat.log 2 n + 15)`. -/
theorem fastCutProgram_spec {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 4 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    let input := n :: flattenMatrix W
    RandHaltsWithin w fastCutProgram (.init input) (fastCutTime n) ∧
    RandCallsBounded w fastCutProgram (.init input) (fastCutTime n) (fastCutNodeQueries n) ∧
    (∀ cfg ∈ (runRand w fastCutProgram (fastCutTime n) (.running (.init input))).support,
      ∃ (y : Data 24) (C : Finset (Fin n)),
        cfg = .halted (cutWeight W C) y ∧
        y.Bounded w ∧
        IsNonTrivialCut C ∧
        minCut W ≤ cutWeight W C ∧
        Modifies (Finset.Ico (2 + n * n) (2 + 27 * (n * n)))
          (Data.init (r := 24) input).mem y.mem) ∧
    (0 < minCut W →
      (1 : ℝ≥0∞) / ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞) ≤
        (evalRand w fastCutProgram (fastCutTime n) (.init input)).toOuterMeasure
          {cfg | ∃ y, cfg = .halted (minCut W) y}) := by
  intro input
  have hfit_in : InputFits w input := inputFits_fastCut hn hw htot
  obtain ⟨m, hm, hq, hsup, hsurv⟩ := fastCutCode_spec hn hW hw htot
  have hrun : runRand w fastCutProgram (fastCutTime n) (.running (.init input)) =
      (fun z : Data 24 × ℕ => RandCfg.halted (z.1.regs retVal) z.1) <$> m :=
    hm.runRand_program retVal fun z hz => (hsup z hz).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cfg hcfg
    rw [hrun] at hcfg
    obtain ⟨z, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hcfg
    exact ⟨z.1.regs retVal, z.1, rfl⟩
  · rw [RandCallsBounded, hrun]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr hq
  · intro cfg hcfg
    have hbnd := runRand_bounded_init hfit_in hcfg
    rw [hrun] at hcfg
    obtain ⟨z, hz, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hcfg
    rcases hsup z hz with ⟨_, hmod, C, hC_nt, hrv⟩
    exact ⟨z.1, C, by rw [hrv], hbnd.2, hC_nt, minCut_le_cutWeight W hC_nt, hmod⟩
  · intro hmin_pos
    rw [evalRand, hrun, ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    refine (hsurv hmin_pos).trans (PMF.toOuterMeasure_mono _ ?_)
    intro z hz
    exact ⟨z.1, congrArg (fun v => RandCfg.halted v z.1) hz.1⟩

end FastCutSingle

/-! ### Endpoint 2: Amplified `O(n ^ 2 log ^ 3 n)` high-probability `FastCut` (`r = 24`) -/

section FastCutHighProb

open KSReg

/-- Body of `ksLogLoop`: halve `rem` via right-shift by `1` and increment `idx`. -/
def ksLogStep : Code .standard 24 := ram[
  rem ← rem >>> one;
  idx ← idx + one
]

/-- Loop computing `idx = Nat.log 2 n` from `rem = n` (`n ≥ 1`), `idx = 0`, `one = 1`. -/
def ksLogLoop : Code .standard 24 := ram[
  while one < rem do [ ⟪ksLogStep⟫ ]
]

/-- Setup for `fastCutHighProbCode` on `n :: flattenMatrix W`: load `n = mem[1]`, compute
`numTrials = fastCutTrials n = (Nat.log 2 n + 15) * (Nat.log 2 n + 2)` without subtraction or
division, and initialize `srcBase = 2`, `trialIdx = 0`, `bestVal = 0`. -/
def fastCutHighProbSetup : Code .standard 24 := ram[
  one ← #1;
  nOrig ← *one;
  rem ← nOrig;
  idx ← #0;
  ⟪ksLogLoop⟫;
  val1 ← #15;
  val1 ← idx + val1;
  val2 ← #2;
  val2 ← idx + val2;
  numTrials ← val1 * val2;
  srcBase ← #2;
  trialIdx ← #0;
  bestVal ← #0
]

/-- Postprocessing after each `fastCutTree` trial: update `bestVal` with `retVal` (unconditionally
on trial `0` and via minimum thereafter) and increment `trialIdx`. -/
def fastCutAmpPost : Code .standard 24 := ram[
  zero ← #0;
  one ← #1;
  if trialIdx = zero then [
    bestVal ← retVal
  ] else [
    if retVal < bestVal then [
      bestVal ← retVal
    ] else [
      zero ← #0
    ]
  ];
  trialIdx ← trialIdx + one
]

/-- Body of one outer `FastCut` amplification trial. -/
def fastCutAmpBody : Code .standard 24 := ram[
  ⟪fastCutTree⟫;
  ⟪fastCutAmpPost⟫
]

/-- Outer amplification loop running `numTrials` independent `FastCut` trees. -/
def fastCutAmpLoop : Code .standard 24 := ram[
  while trialIdx < numTrials do [ ⟪fastCutAmpBody⟫ ]
]

/-- Structured 24-register `O(n ^ 2 log ^ 3 n)` high-probability Karger–Stein program on
`n :: flattenMatrix W`. -/
def fastCutHighProbCode : Code .standard 24 := ram[
  ⟪fastCutHighProbSetup⟫;
  ⟪fastCutAmpLoop⟫
]

/-- Compiled 24-register `O(n ^ 2 log ^ 3 n)` high-probability Karger–Stein program. -/
def fastCutHighProbProgram : Program .standard 24 :=
  fastCutHighProbCode.program bestVal

/-- Worst-case instruction bound `2600 * n ^ 2 * (Nat.log 2 n + 15) * (Nat.log 2 n + 2) ^ 2`
(`O(n ^ 2 log ^ 3 n)`) for `fastCutHighProbProgram`. -/
def fastCutHighProbTime (n : ℕ) : ℕ :=
  2600 * n ^ 2 * (Nat.log 2 n + 15) * (Nat.log 2 n + 2) ^ 2

/-- Loop invariant for `fastCutAmpLoop` at `trialIdx = i ≤ R`. -/
structure KSAmpInv (sb n R i : ℕ) (W : Fin n → Fin n → ℕ) (mem₀ : ℕ → ℕ)
    (x : Data 24) : Prop where
  regs_srcBase : x.regs srcBase = sb
  regs_nOrig : x.regs nOrig = n
  regs_numTrials : x.regs numTrials = R
  regs_trialIdx : x.regs trialIdx = i
  src_matrix : HoldsMatrix x.mem sb n W
  modifies_ws : Modifies (Finset.Ico (sb + n * n) (sb + 27 * (n * n))) mem₀ x.mem
  best_cut : 0 < i → ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ x.regs bestVal = cutWeight W C

theorem ksLogLoop_exec {w n : ℕ} {x : Data 24} (hn : 1 ≤ n)
    (hone : x.regs one = 1) (hrem : x.regs rem = n) (hidx : x.regs idx = 0)
    (hnOrig : x.regs nOrig = n)
    (hn_fit : Fits w n) (hlg_fit : Fits w (Nat.log 2 n)) :
    ∃ y : Data 24, ExecWithin w ksLogLoop x y (4 * Nat.log 2 n + 2) ∧
      y.mem = x.mem ∧
      y.regs one = 1 ∧
      y.regs nOrig = n ∧
      y.regs idx = Nat.log 2 n := by
  let I (y : Data 24) : Prop :=
    y.mem = x.mem ∧ y.regs one = 1 ∧ y.regs nOrig = n ∧
    1 ≤ y.regs rem ∧ y.regs rem ≤ n ∧
    y.regs idx + Nat.log 2 (y.regs rem) = Nat.log 2 n
  have hbody : ∀ y, I y → (Cond.lt one rem).Holds y →
      ∃ z, ExecWithin w ksLogStep y z 2 ∧ I z ∧
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
  obtain ⟨y, he, ⟨hym, hy1, hyn, _, _, hy_sum⟩, hnc⟩ :=
    ExecWithin.loop_invariant I (fun y => Nat.log 2 (y.regs rem)) hbody hx
  have hyr_eq1 : y.regs rem = 1 := by
    have : ¬(1 < y.regs rem) := by simpa [Cond.holds_lt, hy1] using hnc
    omega
  have hy_idx : y.regs idx = Nat.log 2 n := by
    rw [hyr_eq1, Nat.log_one_right, add_zero] at hy_sum
    exact hy_sum
  exact ⟨y, he.mono (by rw [hrem]; omega), hym, hy1, hyn, hy_idx⟩

theorem fastCutHighProbSetup_exec {w n : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hw : logWidth 4 n ≤ w) :
    ∃ y : Data 24,
      ExecWithin w fastCutHighProbSetup (Data.init (n :: flattenMatrix W)) y
        (4 * Nat.log 2 n + 14) ∧
      y.mem = (Data.init (r := 24) (n :: flattenMatrix W)).mem ∧
      y.regs srcBase = 2 ∧
      y.regs nOrig = n ∧
      y.regs numTrials = fastCutTrials n ∧
      y.regs trialIdx = 0 ∧
      y.regs bestVal = 0 := by
  have hws := fits_fastCutWorkspace_of_logWidth_four hn hw
  have hhp_fit := fits_fastCutTrials_of_logWidth_four hn hw
  have h1 : Fits w 1 := hws.of_le (by omega)
  have h2 : Fits w 2 := hws.of_le (by omega)
  have h15 : Fits w 15 := hws.of_le (by have := Nat.mul_le_mul hn hn; omega)
  have hn_fit : Fits w n := hws.of_le (by have := Nat.le_mul_self n; omega)
  have hlg_fit : Fits w (Nat.log 2 n) := hhp_fit.of_le (by unfold fastCutTrials; nlinarith)
  have hlg15_fit : Fits w (Nat.log 2 n + 15) := hhp_fit.of_le (by unfold fastCutTrials; nlinarith)
  have hlg2_fit : Fits w (Nat.log 2 n + 2) := hhp_fit.of_le (by unfold fastCutTrials; nlinarith)
  let x₀ : Data 24 := Data.init (n :: flattenMatrix W)
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
  obtain ⟨s₅, e_loop, hm5, _, hn5, hidx5⟩ :=
    ksLogLoop_exec (x := s₄) (by omega)
      (by simp +decide [s₄, s₃, s₂, s₁])
      (by simp +decide [s₄, s₃])
      (by simp [s₄])
      (by simp +decide [s₄, s₃, s₂])
      hn_fit hlg_fit
  let t₁ := s₅.set val1 15
  let t₂ := t₁.set val1 (Nat.log 2 n + 15)
  let t₃ := t₂.set val2 2
  let t₄ := t₃.set val2 (Nat.log 2 n + 2)
  let t₅ := t₄.set numTrials (fastCutTrials n)
  let t₆ := t₅.set srcBase 2
  let t₇ := t₆.set trialIdx 0
  let t₈ := t₇.set bestVal 0
  have p1 : Exec (B := .standard) w ram[val1 ← #15] s₅ t₁ 1 := Exec.const h15
  have p2 : Exec w ram[val1 ← idx + val1] t₁ t₂ 1 := by
    have hi : t₁.regs idx = Nat.log 2 n := by simpa +decide [t₁, Function.update_apply] using hidx5
    have hv1 : t₁.regs val1 = 15 := by simp [t₁]
    simpa [t₂, BinOp.eval, hi, hv1] using
      Exec.bin (w := w) (f := .add) (d := val1) (i := idx) (j := val1) (x := t₁)
        (by simpa [BinOp.eval, hi, hv1] using hlg15_fit)
  have p3 : Exec (B := .standard) w ram[val2 ← #2] t₂ t₃ 1 := Exec.const h2
  have p4 : Exec w ram[val2 ← idx + val2] t₃ t₄ 1 := by
    have hi : t₃.regs idx = Nat.log 2 n := by
      simpa +decide [t₃, t₂, t₁, Function.update_apply] using hidx5
    have hv2 : t₃.regs val2 = 2 := by simp [t₃]
    simpa [t₄, BinOp.eval, hi, hv2] using
      Exec.bin (w := w) (f := .add) (d := val2) (i := idx) (j := val2) (x := t₃)
        (by simpa [BinOp.eval, hi, hv2] using hlg2_fit)
  have p5 : Exec w ram[numTrials ← val1 * val2] t₄ t₅ 1 := by
    have hv1 : t₄.regs val1 = Nat.log 2 n + 15 := by simp +decide [t₄, t₃, t₂]
    have hv2 : t₄.regs val2 = Nat.log 2 n + 2 := by simp [t₄]
    simpa [t₅, BinOp.eval, hv1, hv2, fastCutTrials] using
      Exec.bin (w := w) (f := .mul) (d := numTrials) (i := val1) (j := val2) (x := t₄)
        (by simpa [BinOp.eval, hv1, hv2, fastCutTrials] using hhp_fit)
  have p6 : Exec (B := .standard) w ram[srcBase ← #2] t₅ t₆ 1 := Exec.const h2
  have p7 : Exec (B := .standard) w ram[trialIdx ← #0] t₆ t₇ 1 := Exec.const (fits_zero w)
  have p8 : Exec (B := .standard) w ram[bestVal ← #0] t₇ t₈ 1 := Exec.const (fits_zero w)
  refine ⟨t₈, ?_, hm5, by simp +decide [t₈, t₇, t₆],
    by simpa +decide [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, Function.update_apply] using hn5,
    by simp +decide [t₈, t₇, t₆, t₅],
    by simp +decide [t₈, t₇],
    by simp [t₈]⟩
  unfold fastCutHighProbSetup
  exact ((e1.within).seq ((e2.within).seq ((e3.within).seq ((e4.within).seq
    (e_loop.seq ((p1.within).seq ((p2.within).seq ((p3.within).seq
      ((p4.within).seq ((p5.within).seq ((p6.within).seq
        ((p7.within).seq p8.within)))))))))))).mono (by omega)

theorem fastCutAmpPost_exec {w i R : ℕ} {x : Data 24}
    (hti : x.regs trialIdx = i) (hiR : i < R)
    (h1 : Fits w 1) (hR_fit : Fits w R) :
    ∃ y : Data 24, ExecWithin w fastCutAmpPost x y 8 ∧
      y.mem = x.mem ∧
      y.regs srcBase = x.regs srcBase ∧
      y.regs nOrig = x.regs nOrig ∧
      y.regs numTrials = x.regs numTrials ∧
      y.regs trialIdx = i + 1 ∧
      y.regs bestVal =
        (if i = 0 then x.regs retVal else min (x.regs retVal) (x.regs bestVal)) := by
  have hi1_fit : Fits w (i + 1) := hR_fit.of_le (by omega)
  let v_new := x.regs retVal
  let s₁ := (x.set zero 0).set one 1
  have e1 : Exec (B := .standard) w ram[zero ← #0] x (x.set zero 0) 1 :=
    Exec.const (fits_zero w)
  have e2 : Exec (B := .standard) w ram[one ← #1] (x.set zero 0) s₁ 1 :=
    Exec.const h1
  have hs1_z : s₁.regs zero = 0 := by simp +decide [s₁]
  have hs1_1 : s₁.regs one = 1 := by simp [s₁]
  have hs1_rv : s₁.regs retVal = v_new := by
    simp +decide [s₁, v_new]
  have hs1_ti : s₁.regs trialIdx = i := by
    simpa +decide [s₁, Function.update_apply] using hti
  have hs1_bv : s₁.regs bestVal = x.regs bestVal := by
    simp +decide [s₁]
  let best_next := if i = 0 then v_new else min v_new (x.regs bestVal)
  have hbr : ∃ s₂ : Data 24,
      ExecWithin (B := .standard) w ram[
        if trialIdx = zero then [ bestVal ← retVal ]
        else [ if retVal < bestVal then [ bestVal ← retVal ] else [ zero ← #0 ] ]
      ] s₁ s₂ 5 ∧
      s₂.mem = x.mem ∧
      s₂.regs one = 1 ∧
      s₂.regs srcBase = x.regs srcBase ∧
      s₂.regs nOrig = x.regs nOrig ∧
      s₂.regs numTrials = x.regs numTrials ∧
      s₂.regs trialIdx = i ∧
      s₂.regs bestVal = best_next := by
    by_cases hi0 : i = 0
    · have hc : (Cond.eq trialIdx zero).Holds s₁ := by simp [Cond.holds_eq, hs1_ti, hs1_z, hi0]
      have e_pos : ExecWithin (B := .standard) w ram[bestVal ← retVal] s₁
          (s₁.set bestVal v_new) 1 := by
        simpa [hs1_rv] using
          (Exec.copy (B := .standard) (w := w) (d := bestVal) (s := retVal) (x := s₁)).within
      refine ⟨s₁.set bestVal v_new, (ExecWithin.branch_pos hc e_pos).mono (by omega), rfl,
        by simp +decide [s₁],
        by simp +decide [s₁],
        by simp +decide [s₁],
        by simp +decide [s₁],
        by simp +decide [hs1_ti],
        by simp [best_next, hi0]⟩
    · have hc : ¬(Cond.eq trialIdx zero).Holds s₁ := by simp [Cond.holds_eq, hs1_ti, hs1_z, hi0]
      by_cases hlt : v_new < x.regs bestVal
      · have hc2 : (Cond.lt retVal bestVal).Holds s₁ := by
          simp [Cond.holds_lt, hs1_rv, hs1_bv, hlt]
        have e_pos2 : ExecWithin (B := .standard) w ram[bestVal ← retVal] s₁
            (s₁.set bestVal v_new) 1 := by
          simpa [hs1_rv] using
            (Exec.copy (B := .standard) (w := w) (d := bestVal) (s := retVal) (x := s₁)).within
        have e_in := ExecWithin.branch_pos (neg := ram[zero ← #0]) hc2 e_pos2
        refine ⟨s₁.set bestVal v_new,
          (ExecWithin.branch_neg (pos := ram[bestVal ← retVal]) hc e_in).mono (by omega), rfl,
          by simp +decide [s₁],
          by simp +decide [s₁],
          by simp +decide [s₁],
          by simp +decide [s₁],
          by simp +decide [hs1_ti],
          by simp [best_next, hi0, min_eq_left (Nat.le_of_lt hlt)]⟩
      · have hc2 : ¬(Cond.lt retVal bestVal).Holds s₁ := by
          simp [Cond.holds_lt, hs1_rv, hs1_bv, hlt]
        have e_neg2 : ExecWithin (B := .standard) w ram[zero ← #0] s₁ (s₁.set zero 0) 1 :=
          ExecWithin.const (fits_zero w)
        have e_in := ExecWithin.branch_neg (pos := ram[bestVal ← retVal]) hc2 e_neg2
        refine ⟨s₁.set zero 0,
          (ExecWithin.branch_neg (pos := ram[bestVal ← retVal]) hc e_in).mono (by omega), rfl,
          by simp +decide [s₁],
          by simp +decide [s₁],
          by simp +decide [s₁],
          by simp +decide [s₁],
          by simp +decide [hs1_ti],
          by simp +decide [s₁, best_next, hi0, min_eq_right (Nat.le_of_not_lt hlt)]⟩
  obtain ⟨s₂, e_br, hm2, ho2, hsb2, hn2, hnt2, hti2, hbv2⟩ := hbr
  have e_inc : ExecWithin w ram[trialIdx ← trialIdx + one] s₂ (s₂.set trialIdx (i + 1)) 1 := by
    simpa [BinOp.eval, hti2, ho2] using
      ExecWithin.bin (f := .add) (d := trialIdx) (i := trialIdx) (j := one) (x := s₂)
        (by simpa [BinOp.eval, hti2, ho2] using hi1_fit)
  refine ⟨s₂.set trialIdx (i + 1), ?_, hm2,
    by simpa +decide [Function.update_apply] using hsb2,
    by simpa +decide [Function.update_apply] using hn2,
    by simpa +decide [Function.update_apply] using hnt2,
    by simp,
    by simpa +decide [Function.update_apply] using hbv2⟩
  unfold fastCutAmpPost
  exact ((e1.within).seq ((e2.within).seq (e_br.seq e_inc))).mono (by omega)

private theorem ksAmpTrial_step_bound {n t_tree n_p : ℕ} (hn : 2 ≤ n)
    (htree : t_tree ≤ fastCutNodeTime n + 7 * (n * n) + 21) (hp : n_p ≤ 8) :
    t_tree + n_p + 2 ≤ 2500 * n ^ 2 * (Nat.log 2 n + 2) := by
  have hnt := fastCutNodeTime_le hn
  have hnn : n * n = n ^ 2 := (sq n).symm
  rw [hnn] at htree
  have hn2 : 4 ≤ n ^ 2 := by nlinarith
  have hlg : 2 ≤ Nat.log 2 n + 2 := by omega
  have hov : 7 * n ^ 2 + 31 ≤ 100 * n ^ 2 * (Nat.log 2 n + 2) := by nlinarith
  linarith

theorem fastCutAmpBody_spec {w sb n R i : ℕ} {W : Fin n → Fin n → ℕ} {mem₀ : ℕ → ℕ} {x : Data 24}
    (hn : 2 ≤ n) (hW : IsMultigraph W) (hiR : i < R)
    (h1 : Fits w 1) (hws_fit : Fits w (sb + 27 * (n * n)))
    (hsp_fit : Fits w (2 * Nat.log 2 n + 1))
    (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W))
    (hinv : KSAmpInv sb n R i W mem₀ x) :
    ∃ m : ProbComp (Data 24 × ℕ),
      ExecRand w fastCutAmpBody x m ∧
      m.IsQueryBounded (6 * (n * n)) ∧
      (∀ z ∈ m.support,
        z.2 + 2 ≤ 2500 * n ^ 2 * (Nat.log 2 n + 2) ∧
        KSAmpInv sb n R (i + 1) W mem₀ z.1 ∧
        (0 < i → x.regs bestVal = minCut W → z.1.regs bestVal = minCut W)) ∧
      (0 < minCut W →
        m.eval.toOuterMeasure {z | z.1.regs bestVal ≠ minCut W} ≤
          (1 : ℝ≥0∞) - (1 : ℝ≥0∞) / ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞)) := by
  obtain ⟨m_t, hm_t, hq_t, hsup_t, hsurv_t⟩ :=
    fastCutTree_spec hn hW hinv.regs_srcBase hinv.regs_nOrig hinv.src_matrix hws_fit hsp_fit htot
  let Qpost (d y : Data 24) : Prop :=
    y.mem = d.mem ∧
    y.regs srcBase = d.regs srcBase ∧
    y.regs nOrig = d.regs nOrig ∧
    y.regs numTrials = d.regs numTrials ∧
    y.regs trialIdx = i + 1 ∧
    y.regs bestVal = (if i = 0 then d.regs retVal else min (d.regs retVal) (d.regs bestVal))
  have hpost : ∀ z₀ ∈ m_t.support, ∃ y, ExecWithin w fastCutAmpPost z₀.1 y 8 ∧ Qpost z₀.1 y := by
    intro z₀ hz₀
    have hti : z₀.1.regs trialIdx = i := (hsup_t z₀ hz₀).2.2.2.2.2.1.trans hinv.regs_trialIdx
    exact fastCutAmpPost_exec hti hiR h1 hR_fit
  obtain ⟨g, hm_body, hg⟩ := execRand_seq_det (Q := Qpost) hm_t hpost
  let m_out := (fun z : Data 24 × ℕ => ((g z.1).1, z.2 + (g z.1).2)) <$> m_t
  have hex_body : ExecRand w fastCutAmpBody x m_out := hm_body
  refine ⟨m_out, hex_body, ?_, ?_, ?_⟩
  · simp only [m_out, OracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
    exact hq_t.mono (fastCutNodeQueries_le hn)
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    rcases hsup_t z₀ hz₀ with ⟨ht₀, hmod₀, hsb₀, hn₀, hnt₀, _, hbv₀, C_new, hC_nt, hrv₀⟩
    rcases hg z₀ hz₀ with ⟨ht_g, _, hym_g, hsb_g, hn_g, hnt_g, hti_g, hbv_g⟩
    refine ⟨ksAmpTrial_step_bound hn ht₀ ht_g, ?_, ?_⟩
    · refine ⟨hsb_g.trans hsb₀, hn_g.trans hn₀,
        hnt_g.trans (hnt₀.trans hinv.regs_numTrials), hti_g, ?_, ?_, ?_⟩
      · intro u v
        have hlt : sb + u.val * n + v.val < sb + n * n := matAddr_lt_end (le_refl n) u v
        rw [hym_g, hmod₀ _ (by rw [Finset.mem_Ico]; omega)]
        exact hinv.src_matrix u v
      · rw [hym_g]
        exact modifies_trans_subset hinv.modifies_ws hmod₀ Finset.Subset.rfl Finset.Subset.rfl
      · intro _
        by_cases hi0 : i = 0
        · exact ⟨C_new, hC_nt, by simp [hbv_g, hi0, hrv₀]⟩
        · obtain ⟨C_old, hC_old_nt, hbv_old⟩ := hinv.best_cut (Nat.pos_of_ne_zero hi0)
          simp only [hbv_g, hi0, ↓reduceIte, hrv₀, hbv₀, hbv_old]
          rcases min_cases (cutWeight W C_new) (cutWeight W C_old) with ⟨hmin, _⟩ | ⟨hmin, _⟩
          · exact ⟨C_new, hC_nt, hmin⟩
          · exact ⟨C_old, hC_old_nt, hmin⟩
    · intro hi_pos hbv_min
      have hge : minCut W ≤ cutWeight W C_new := minCut_le_cutWeight W hC_nt
      have hne0 : i ≠ 0 := by omega
      simp only [hbv_g, hne0, ↓reduceIte, hrv₀, hbv₀, hbv_min, min_eq_right hge]
  · intro hmin_pos
    have hhit_ge : (1 : ℝ≥0∞) / ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞) ≤
        m_out.eval.toOuterMeasure {z | z.1.regs bestVal = minCut W} := by
      dsimp only [m_out]
      rw [ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
      refine (hsurv_t hmin_pos).trans (toOuterMeasure_mono_support m_t fun z₀ hz₀ hrv_eq => ?_)
      rcases hsup_t z₀ hz₀ with ⟨_, _, _, _, _, _, hbv₀, _⟩
      rcases hg z₀ hz₀ with ⟨_, _, _, _, _, _, _, hbv_g⟩
      change (g z₀.1).1.regs bestVal = minCut W
      change z₀.1.regs retVal = minCut W at hrv_eq
      by_cases hi0 : i = 0
      · simp [hbv_g, hi0, hrv_eq]
      · obtain ⟨C_old, hC_old_nt, hbv_old⟩ := hinv.best_cut (Nat.pos_of_ne_zero hi0)
        have hge : minCut W ≤ cutWeight W C_old := minCut_le_cutWeight W hC_old_nt
        simp [hbv_g, hi0, hrv_eq, hbv₀, hbv_old, min_eq_left hge]
    have hcompl : {z : Data 24 × ℕ | z.1.regs bestVal ≠ minCut W} =
        {z : Data 24 × ℕ | z.1.regs bestVal = minCut W}ᶜ := by
      ext z
      simp
    rw [hcompl]
    exact toOuterMeasure_compl_le_one_sub m_out.eval _ hhit_ge

theorem fastCutAmpLoop_spec {w sb n R : ℕ} {W : Fin n → Fin n → ℕ} {mem₀ : ℕ → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (h1 : Fits w 1) (hws_fit : Fits w (sb + 27 * (n * n)))
    (hsp_fit : Fits w (2 * Nat.log 2 n + 1))
    (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W)) :
    ∀ (rem i : ℕ) (x : Data 24),
      i + rem = R →
      KSAmpInv sb n R i W mem₀ x →
      ∃ m : ProbComp (Data 24 × ℕ),
        ExecRand w fastCutAmpLoop x m ∧
        m.IsQueryBounded (rem * (6 * (n * n))) ∧
        (∀ z ∈ m.support,
          z.2 ≤ rem * (2500 * n ^ 2 * (Nat.log 2 n + 2)) + 2 ∧
          KSAmpInv sb n R R W mem₀ z.1 ∧
          (0 < i → x.regs bestVal = minCut W → z.1.regs bestVal = minCut W)) ∧
        (0 < minCut W →
          m.eval.toOuterMeasure {z | z.1.regs bestVal ≠ minCut W} ≤
            ((1 : ℝ≥0∞) - (1 : ℝ≥0∞) / ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞)) ^ rem) := by
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
      fastCutAmpBody_spec hn hW hi_lt h1 hws_fit hsp_fit hR_fit htot hinv
    have hnext : ∀ z₁ ∈ m_b.support,
        ∃ m_r : ProbComp (Data 24 × ℕ),
          ExecRand w fastCutAmpLoop z₁.1 m_r ∧
          m_r.IsQueryBounded (rem * (6 * (n * n))) ∧
          (∀ z₂ ∈ m_r.support,
            z₂.2 ≤ rem * (2500 * n ^ 2 * (Nat.log 2 n + 2)) + 2 ∧
            KSAmpInv sb n R R W mem₀ z₂.1 ∧
            (0 < i + 1 → z₁.1.regs bestVal = minCut W → z₂.1.regs bestVal = minCut W)) ∧
          (0 < minCut W →
            m_r.eval.toOuterMeasure {z | z.1.regs bestVal ≠ minCut W} ≤
              ((1 : ℝ≥0∞) - (1 : ℝ≥0∞) / ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞)) ^ rem) := by
      intro z₁ hz₁
      exact ih (i + 1) z₁.1 (by omega) (hsup_b z₁ hz₁).2.1
    obtain ⟨ml, hml_def⟩ :
        ∃ ml : Data 24 → ProbComp (Data 24 × ℕ),
          ∀ d, ml d = codeComp w fastCutAmpLoop d := ⟨_, fun _ => rfl⟩
    have hml_exec : ∀ z₁ ∈ m_b.support, ExecRand w fastCutAmpLoop z₁.1 (ml z₁.1) := by
      intro z₁ hz₁
      obtain ⟨m_r, hm_r, _⟩ := hnext z₁ hz₁
      rw [hml_def]
      simpa only [hm_r.codeComp_eq] using hm_r
    have hm_iter : ExecRand w fastCutAmpLoop x
        (do let z₁ ← m_b; let z₂ ← ml z₁.1; pure (z₂.1, z₁.2 + z₂.2 + 2)) :=
      ExecRand.loop_iter hc hm_b hml_exec
    let m_total := (do let z₁ ← m_b; let z₂ ← ml z₁.1; pure (z₂.1, z₁.2 + z₂.2 + 2))
    refine ⟨m_total, hm_iter, ?_, ?_, ?_⟩
    · have hq_each : ∀ z₁ ∈ m_b.support,
          (ml z₁.1 >>= fun z₂ => pure (z₂.1, z₁.2 + z₂.2 + 2)).IsQueryBounded
            (rem * (6 * (n * n))) := by
        intro z₁ hz₁
        obtain ⟨m_r, hm_r, hq_r, _⟩ := hnext z₁ hz₁
        rw [hml_def, hm_r.codeComp_eq]
        simpa only [Nat.add_zero] using hq_r.bind fun _ => .pure _ 0
      have hq_tot := OracleComp.IsCostBounded.bind_on_support hq_b hq_each
      exact hq_tot.mono (le_of_eq (by ring))
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
      refine toOuterMeasure_bind_le_mul_ennreal (α := Data 24 × ℕ) (β := Data 24 × ℕ) m_b.eval
        (fun z₁ => (ml z₁.1).eval.map fun z₂ => (z₂.1, z₁.2 + z₂.2 + 2))
        {z₁ | z₁.1.regs bestVal ≠ minCut W}
        {z | z.1.regs bestVal ≠ minCut W}
        (q₁ := (1 : ℝ≥0∞) - (1 : ℝ≥0∞) / ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞))
        (q₂ := ((1 : ℝ≥0∞) - (1 : ℝ≥0∞) / ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞)) ^ rem)
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
        rw [hml_def, hm_r.codeComp_eq, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
        refine tsum_eq_zero_iff.mpr fun z₂ => ?_
        by_cases hz₂_eval : z₂ ∈ m_r.eval.support
        · have hz₂ : z₂ ∈ m_r.support := (ProbComp.support_eval m_r) ▸ hz₂_eval
          have hbv₂ : z₂.1.regs bestVal = minCut W :=
            (hsup_r z₂ hz₂).2.2 (Nat.succ_pos i) hbv₁
          have hnot : z₂ ∉ ((fun z : Data 24 × ℕ => (z.1, z₁.2 + z.2 + 2)) ⁻¹'
              {z : Data 24 × ℕ | z.1.regs bestVal ≠ minCut W}) := by
            simp [hbv₂]
          exact Set.indicator_of_notMem hnot _
        · have hp0 : m_r.eval z₂ = 0 := by simpa only [PMF.mem_support_iff, not_not] using hz₂_eval
          simp [hp0]

private theorem fastCutHighProbTime_bound {n : ℕ} (hn : 2 ≤ n) :
    (4 * Nat.log 2 n + 14) +
        (fastCutTrials n * (2500 * n ^ 2 * (Nat.log 2 n + 2)) + 2) + 1 ≤
      fastCutHighProbTime n := by
  unfold fastCutHighProbTime fastCutTrials
  let L := Nat.log 2 n
  change (4 * L + 14) + (((L + 15) * (L + 2)) * (2500 * n ^ 2 * (L + 2)) + 2) + 1 ≤
    2600 * n ^ 2 * (L + 15) * (L + 2) ^ 2
  let P := n ^ 2 * (L + 2) ^ 2
  have hn2 : 4 ≤ n ^ 2 := by nlinarith
  have hL2 : 4 ≤ (L + 2) ^ 2 := by rw [sq]; nlinarith
  have hP : 16 ≤ P := by dsimp only [P]; nlinarith
  have hL : 4 * L + 17 ≤ 100 * P * (L + 15) := by nlinarith
  have hp_eq : 100 * P * (L + 15) = 100 * n ^ 2 * (L + 15) * (L + 2) ^ 2 := by
    dsimp only [P]; ring
  have hmul : ((L + 15) * (L + 2)) * (2500 * n ^ 2 * (L + 2)) =
      2500 * n ^ 2 * (L + 15) * (L + 2) ^ 2 := by ring
  linarith

/-- Structured `ProbComp` specification of `fastCutHighProbCode`. -/
theorem fastCutHighProbCode_spec {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 4 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    ∃ m : ProbComp (Data 24 × ℕ),
      ExecRand w fastCutHighProbCode (Data.init (n :: flattenMatrix W)) m ∧
      m.IsQueryBounded (fastCutTrials n * (6 * (n * n))) ∧
      (∀ z ∈ m.support,
        z.2 + 1 ≤ fastCutHighProbTime n ∧
        Modifies (Finset.Ico (2 + n * n) (2 + 27 * (n * n)))
          (Data.init (r := 24) (n :: flattenMatrix W)).mem z.1.mem ∧
        ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ z.1.regs bestVal = cutWeight W C) ∧
      (0 < minCut W →
        m.eval.toOuterMeasure {z | z.1.regs bestVal ≠ minCut W} ≤
          (1 : ℝ≥0∞) / ((2 * n : ℕ) : ℝ≥0∞)) := by
  have hws := fits_fastCutWorkspace_of_logWidth_four hn hw
  have hsp := fits_sp_of_ws hn hws
  have h1 : Fits w 1 := hws.of_le (by omega)
  have hhp_fit := fits_fastCutTrials_of_logWidth_four hn hw
  obtain ⟨y_s, ⟨n_s, hn_s, e_s⟩, hm_s, hsb_s, hn_s_r, hnt_s, hti_s, _⟩ :=
    fastCutHighProbSetup_exec (W := W) hn hw
  have hinv₀ : KSAmpInv 2 n (fastCutTrials n) 0 W
      (Data.init (r := 24) (n :: flattenMatrix W)).mem y_s :=
    ⟨hsb_s, hn_s_r, hnt_s, hti_s, hm_s ▸ holdsMatrix_init_fastCut W,
      hm_s ▸ Modifies.refl _ _, fun h0 => absurd h0 (by omega)⟩
  obtain ⟨m_l, hm_l, hq_l, hsup_l, hfail_l⟩ :=
    fastCutAmpLoop_spec hn hW h1 hws hsp hhp_fit htot (fastCutTrials n) 0 y_s
      (Nat.zero_add _) hinv₀
  have hbound := fastCutHighProbTime_bound hn
  refine ⟨_, e_s.seqRand hm_l, ?_, ?_, ?_⟩
  · simp only [OracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
    exact hq_l
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    rcases hsup_l z₀ hz₀ with ⟨ht₀, hinv_f, _⟩
    exact ⟨by omega, hinv_f.modifies_ws, hinv_f.best_cut (fastCutTrials_pos n)⟩
  · intro hmin_pos
    rw [ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    exact (hfail_l hmin_pos).trans (fastCutHighProb_failure_le n)

/-- **Amplified `O(n ^ 2 log ^ 3 n)` high-probability Karger–Stein (`fastCutHighProbProgram`,
the minimum-cut-value part of `[KargerStein1996]`, Section 4, Theorem 4.4; paraphrase).**
At word size `w ≥ logWidth 4 n` when `2 ≤ n` and `totalDoubledWeight W < 2 ^ w`:
1. `fastCutHighProbProgram` halts within
   `fastCutHighProbTime n = 2600 * n ^ 2 * (Nat.log 2 n + 15) * (Nat.log 2 n + 2) ^ 2` steps;
2. executes at most `fastCutTrials n * (6 * (n * n))` `rand` calls;
3. on every supported branch, outputs `cutWeight W C ≥ minCut W` for a genuine non-trivial cut `C`
   of `W` while modifying memory only in `[2 + n * n, 2 + 27 * (n * n))`;
4. when `0 < minCut W` (excluded only for proof convenience), misses `minCut W` with probability at
   most `1 / (2 * n)`. -/
theorem fastCutHighProbProgram_spec {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 4 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    let input := n :: flattenMatrix W
    RandHaltsWithin w fastCutHighProbProgram (.init input) (fastCutHighProbTime n) ∧
    RandCallsBounded w fastCutHighProbProgram (.init input) (fastCutHighProbTime n)
      (fastCutTrials n * (6 * (n * n))) ∧
    (∀ cfg ∈ (runRand w fastCutHighProbProgram (fastCutHighProbTime n)
        (.running (.init input))).support,
      ∃ (y : Data 24) (C : Finset (Fin n)),
        cfg = .halted (cutWeight W C) y ∧
        y.Bounded w ∧
        IsNonTrivialCut C ∧
        minCut W ≤ cutWeight W C ∧
        Modifies (Finset.Ico (2 + n * n) (2 + 27 * (n * n)))
          (Data.init (r := 24) input).mem y.mem) ∧
    (0 < minCut W →
      (evalRand w fastCutHighProbProgram (fastCutHighProbTime n) (.init input)).toOuterMeasure
          {cfg | ∀ y, cfg ≠ .halted (minCut W) y} ≤
        (1 : ℝ≥0∞) / ((2 * n : ℕ) : ℝ≥0∞)) := by
  intro input
  have hfit_in : InputFits w input := inputFits_fastCut hn hw htot
  obtain ⟨m, hm, hq, hsup, hfail⟩ := fastCutHighProbCode_spec hn hW hw htot
  have hrun : runRand w fastCutHighProbProgram (fastCutHighProbTime n) (.running (.init input)) =
      (fun z : Data 24 × ℕ => RandCfg.halted (z.1.regs bestVal) z.1) <$> m :=
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

/-- Corollary of `fastCutHighProbProgram_spec`: when `0 < minCut W`, `fastCutHighProbProgram`
misses `minCut W` with probability at most `1 / n`. -/
theorem fastCutHighProbProgram_failure_le_inv_n {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 4 n ≤ w) (htot : Fits w (totalDoubledWeight W))
    (hpos : 0 < minCut W) :
    (evalRand w fastCutHighProbProgram (fastCutHighProbTime n)
        (.init (n :: flattenMatrix W))).toOuterMeasure
        {cfg | ∀ y, cfg ≠ .halted (minCut W) y} ≤
      (1 : ℝ≥0∞) / (n : ℝ≥0∞) := by
  refine ((fastCutHighProbProgram_spec hn hW hw htot).2.2.2 hpos).trans ?_
  apply ENNReal.div_le_div_left
  exact_mod_cast (by omega : n ≤ 2 * n)

end FastCutHighProb

end Cslib.Algorithms.WordRAM.Karger

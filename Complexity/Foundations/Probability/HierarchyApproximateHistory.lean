/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyCompressedBin
public import Complexity.Foundations.Probability.HierarchyChildRootMoment
public import Complexity.Foundations.Probability.RootMetric.WalkPerturbation
public import Complexity.Foundations.Probability.RootMetric.WeightedError

/-!
# Perturbations of executed budget histories

The history interface below executes the existing compressed bin at each dense request's
own budget. It is an alternative input to the literal RAW assembly, not a replacement of
production semantic leaves. Successful direct, left and reset-right calls are connected to
the existing signed-residual child-error payment on the unchanged environment. Child accuracy
and availability remain lower-budget obligations; no parent accuracy is assumed.
-/
public section
noncomputable section
open Finset Cslib Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- Computed approximate dense inputs, using the actual compressed-bin program. Other
constructors retain the existing evaluator. The supplied terminal exponent and decoder
parameters are checked by `compressedBin`, rather than treated as accuracy certificates. -/
@[expose] def compressedHistory (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (m : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Option (BudgetValue P) :=
  match r.task with
  | .baseNormalized 0 bin =>
    (B.compressedBin m bin (exponent r) ζ floor r).map BudgetValue.row
  | _ => B.evaluate m r

/-- The alternative dense call is literally the compressed computation on the original
request, including its source, terminal and usage channels. -/
theorem compressedHistory_dense (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (m bin : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (ht : r.task = .baseNormalized 0 bin) :
    row (B.compressedHistory exponent ζ floor) m r =
      B.compressedBin m bin (exponent r) ζ floor r := by
  simp only [row, compressedHistory, ht]
  cases B.compressedBin m bin (exponent r) ζ floor r <;> rfl

/-- Availability at the three literal requests identifies an executed positive sample
with the shared signed-residual API. In particular, the right source is not rewritten to
the parent's source. This accepts a genuine strict lower-budget IH through `hc`. -/
theorem positiveSample_of_rows
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (m bin : ℕ) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (child : HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hc : ∀ q ∈ ({(HierarchyTask.rawRequests 0 bin t r.source (midpoint r)
        r.terminal (B.binRate bin)).direct,
      (HierarchyTask.rawRequests 0 bin t r.source (midpoint r)
        r.terminal (B.binRate bin)).left,
      (HierarchyTask.rawRequests 0 bin t r.source (midpoint r)
        r.terminal (B.binRate bin)).right} : Finset _),
      row history m q = some (child q)) :
    B.positiveSample history m bin t r = some (fun σ x y =>
      HierarchyTask.rawPositiveSample (channels B.padding) 0 bin t r.source (midpoint r)
        r.terminal (B.binRate bin) (fun q => child q σ) x y) := by
  unfold positiveSample
  dsimp only
  rw [hc _ (by simp), hc _ (by simp), hc _ (by simp)]
  rfl

/-- Actual successful sample error is paid by the existing support-restricted direct,
left and reset-right error. The ranges are child facts, never a desired parent bound. -/
theorem positiveSample_error
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (m bin : ℕ) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (child canonical : HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hc : ∀ q ∈ ({(HierarchyTask.rawRequests 0 bin t r.source (midpoint r)
        r.terminal (B.binRate bin)).direct,
      (HierarchyTask.rawRequests 0 bin t r.source (midpoint r)
        r.terminal (B.binRate bin)).left,
      (HierarchyTask.rawRequests 0 bin t r.source (midpoint r)
        r.terminal (B.binRate bin)).right} : Finset _),
      row history m q = some (child q))
    (CA CB : ℝ) (σ : Environment P 3) (x y : ZMod P)
    (hleft : ∀ z, |child (HierarchyTask.rawRequests 0 bin t r.source (midpoint r)
      r.terminal (B.binRate bin)).left σ x z| ≤ CA)
    (hright : ∀ z, |canonical (HierarchyTask.rawRequests 0 bin t r.source (midpoint r)
      r.terminal (B.binRate bin)).right σ z y| ≤ CB) :
    ∃ A, B.positiveSample history m bin t r = some A ∧
      |A σ x y - HierarchyTask.rawPositiveSample (channels B.padding) 0 bin t
        r.source (midpoint r) r.terminal (B.binRate bin) (fun q => canonical q σ) x y| ≤
      HierarchyTask.positiveChildError (channels B.padding) 0 bin t r.source (midpoint r)
        r.terminal (B.binRate bin) CA CB (fun q => child q σ) (fun q => canonical q σ) x y := by
  refine ⟨_, B.positiveSample_of_rows history m bin t r child hc, ?_⟩
  exact HierarchyTask.rawPositiveSample_sub_le (channels B.padding) 0 bin t
    r.source (midpoint r) r.terminal (B.binRate bin) CA CB
    (fun q => child q σ) (fun q => canonical q σ) x y hleft hright

/-- Paired perturbations retain both changing budgets. Only the two actually executed
samples need availability; equal-budget groups execute no children. -/
theorem pairedSample_of_errors
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (bin : Option ℕ)
    (A C A₀ C₀ : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hf : B.sample history (LogSpaceEstimation.lastBudget M d B.slack
      (B.sampleScale r bin)) t r bin = some A)
    (hc : B.sample history (LogSpaceEstimation.lastBudget M (2 * d) B.slack
      (B.sampleScale r bin)) t r bin = some C)
    (hne : LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) ≠
      LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)) :
    B.pairedSample history M d t r bin = some (A - C) ∧
    ∀ σ x y, |(A - C) σ x y - (A₀ - C₀) σ x y| ≤
      |A σ x y - A₀ σ x y| + |C σ x y - C₀ σ x y| := by
  constructor
  · simp only [pairedSample, hne, ↓reduceIte, hf, hc, bind, Option.bind_some, pure]
  · intro σ x y
    change |(A σ x y - C σ x y) - (A₀ σ x y - C₀ σ x y)| ≤ _
    rw [show (A σ x y - C σ x y) - (A₀ σ x y - C₀ σ x y) =
      (A σ x y - A₀ σ x y) - (C σ x y - C₀ σ x y) by ring]
    exact abs_sub _ _

/-- Initial parent assembly executes two computed approximate dense calls and its own
literal zero correction. Approximation need not have zero error: the parent's perturbation
is exactly the weighted direct-child perturbation. The right child is still executed with
its reset source, even though the zero left correction annihilates its contribution. -/
theorem positiveSample_initial_compressed
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M m bin : ℕ) (hm : m < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (D R : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hd : B.compressedBin m bin
      (exponent (HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)).direct) ζ floor
      (HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)).direct = some D)
    (hr : B.compressedBin m bin
      (exponent (HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)).right) ζ floor
      (HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)).right = some R) :
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    let A := fun σ x y => B.binRate bin *
      HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y * D σ x y
    B.positiveSample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
      else none) m bin (.pilotInput ⟨0, HP.k_pos⟩) r = some A ∧
    ∀ σ x y, |A σ x y - B.initialSample r bin σ x y| =
      |B.binRate bin * HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y| *
      |D σ x y - denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
        HP.ρ HP.K B.base σ x y| := by
  dsimp only
  constructor
  · unfold positiveSample
    dsimp only
    simp only [row, hm, ↓reduceIte, compressedHistory, HierarchyTask.rawRequests,
      HierarchyTask.correctionAtomTask] at hd hr ⊢
    simp only [show (⟨0, HP.k_pos⟩ : Fin HP.k).castSucc = 0 from rfl, Fin.cases_zero]
    rw [hd]
    simp only [Option.map_some, bind, Option.bind_some, BudgetValue.row?]
    rw [B.evaluate_pilotCorrection_zero m _ rfl]
    rw [hr]
    simp only [Option.map_some, Option.bind_some, pure]
    congr 1
    funext σ x y
    simp
  · intro σ x y
    unfold initialSample
    rw [← mul_sub, abs_mul]

/-- The executed initial positive sample is paid by the computed direct child's rooted
moment on its own source and usage. Successful compression certifies its range and usage
vanishing. The reset-right child needs availability only; zero left correction removes its
error payment altogether. Importance is integrated, without extracting environment atoms. -/
theorem positiveSample_initial_compressed_root
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M m bin : ℕ) (hm : m < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hs : 0 ≤ r.source.rate)
    (D R : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hd :
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some D)
    (hr :
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R) :
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    let C := denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
      HP.ρ HP.K B.base
    ∃ A, B.positiveSample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
      else none) m bin (.pilotInput ⟨0, HP.k_pos⟩) r = some A ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y)
        (fun σ x y => A σ x y - B.initialSample r bin σ x y) ≤
      ‖fun y => B.binRate bin * HierarchyTask.usageRatio (channels B.padding)
        r.terminal Q.direct y‖ ^ 4 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) ^ 4 *
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) D C := by
  dsimp only
  let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)
  have hru := B.compressedBin_range_usage m bin (exponent Q.direct) ζ floor Q.direct D hd
  refine ⟨_, (B.positiveSample_initial_compressed exponent ζ floor M m bin hm r D R hd hr).1,
    ?_⟩
  change rowNormPow 4 P r.source.rate _ _ (fun σ x y =>
    B.binRate bin * HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y *
      D σ x y - B.initialSample r bin σ x y) ≤ _
  have he : (fun σ x y =>
      B.binRate bin * HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y *
        D σ x y - B.initialSample r bin σ x y) =
      (fun σ x y =>
        (B.binRate bin * HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y) *
        (D σ x y - denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base σ x y)) := by
    funext σ x y
    unfold initialSample
    ring
  rw [he]
  exact rowNormPow_weighted_sub_le_rootDistPow (mul_nonneg (Nat.cast_nonneg _) hs)
    _ _ _ D _ _ hru.1
    (fun σ x y => normalizedRequest_mem_Icc HP B.padding Q.direct (B.cutoff bin)
      B.binCap_nonneg (B.cutoff_bounds bin) _ _ σ x y)
    (fun σ x y hy => by
      rw [hru.2 σ x y hy]
      exact (normalizedRequest_zero_off_usage B.padding id Q.direct _ _ _ _ _ σ x y hy).symm)

/-- A legitimate lower-budget availability IH constructs the actual approximate initial
paired sample, including its zero coarse boundary and unequal fine/coarse budgets. The
computed direct children may have nonzero errors; their difference is retained literally. -/
theorem pairedSample_initial_compressed
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M d bin : ℕ) (hM : 0 < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (D : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (hzero : D 0 = 0)
    (ih : ∀ n < M, 0 < n →
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin n bin (exponent Q.direct) ζ floor Q.direct = some (D n) ∧
      ∃ R, B.compressedBin n bin (exponent Q.right) ζ floor Q.right = some R) :
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
    let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
    B.pairedSample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
      else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) =
      some (fun σ x y => B.binRate bin *
        HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y *
        (D fine σ x y - D coarse σ x y)) := by
  dsimp only
  let H := fun n q => if n < M then B.compressedHistory exponent ζ floor n q else none
  let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)
  have hs (n : ℕ) (hn : n < M) :
      B.sample H n (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) =
        some (fun σ x y => B.binRate bin *
          HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y * D n σ x y) := by
    by_cases hz : n = 0
    · subst n
      simp only [sample, ↓reduceIte, hzero, Pi.zero_apply, Matrix.zero_apply, mul_zero]
      rfl
    · obtain ⟨hd, R, hr⟩ := ih n hn (Nat.pos_of_ne_zero hz)
      rw [sample, ite_eq_right hz]
      exact (B.positiveSample_initial_compressed exponent ζ floor M n bin hn r
        (D n) R hd hr).1
  have hbud := B.pairedSample_budgets_lt M d hM r (some bin)
  unfold pairedSample
  dsimp only
  split_ifs with he
  · rw [he]
    congr 1
    funext σ x y
    simp
  · rw [hs _ hbud.1, hs _ hbud.2]
    simp only [bind, Option.bind_some, pure]
    congr 1
    funext σ x y
    simp only [Pi.sub_apply]
    dsimp only [Q]
    ring

/-- Strict own-request lower-budget rooted accuracy pays both actual paired endpoints.
At budget zero both executions are literally zero, so no compressed call or accuracy
premise is required there. Reset-right availability is retained at every positive endpoint.
The reference is the actual semantic paired history, not a substituted parent target. -/
theorem pairedSample_initial_compressed_root
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M d bin : ℕ) (hM : 0 < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hs : 0 ≤ r.source.rate)
    (D : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (hzero : D 0 = 0)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n)
    (ih : ∀ n < M, 0 < n →
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin n bin (exponent Q.direct) ζ floor Q.direct = some (D n) ∧
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) (D n)
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤ ε n ∧
      ∃ R, B.compressedBin n bin (exponent Q.right) ζ floor Q.right = some R) :
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
    let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
    ∃ A C,
      B.pairedSample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) = some A ∧
      B.pairedSample (fun n q => if n < M then B.evaluate n q else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) = some C ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y) (A - C) ≤
        8 * (‖fun y => B.binRate bin * HierarchyTask.usageRatio (channels B.padding)
          r.terminal Q.direct y‖ ^ 4 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) ^ 4) *
          (ε fine + ε coarse) := by
  dsimp only
  let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)
  let w := fun y => B.binRate bin *
    HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y
  let K := ‖w‖ ^ 4 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) ^ 4
  let E : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun n σ x y => w y * D n σ x y
  let C := fun n => if n = 0 then 0 else B.initialSample r bin
  let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
  let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := mul_nonneg (Nat.cast_nonneg _) hs
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hend (n : ℕ) (hn : n < M) :
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y) (E n - C n) ≤ K * ε n := by
    by_cases hz : n = 0
    · subst n
      have he : E 0 - C 0 = 0 := by ext; simp [E, C, hzero]
      rw [he]
      simpa [rowNormPow] using mul_nonneg hK (hε 0)
    · obtain ⟨hd, he, R, hr⟩ := ih n hn (Nat.pos_of_ne_zero hz)
      obtain ⟨A, hA, hb⟩ := B.positiveSample_initial_compressed_root exponent ζ floor
        M n bin hn r hs (D n) R hd hr
      have ha : A = E n := Option.some.inj (hA.symm.trans
        (B.positiveSample_initial_compressed exponent ζ floor M n bin hn r (D n) R hd hr).1)
      rw [ha] at hb
      dsimp only [C]
      rw [ite_eq_right hz]
      exact hb.trans (mul_le_mul_of_nonneg_left he hK)
  have hp := B.pairedSample_initial_compressed exponent ζ floor M d bin hM r D hzero
    (fun n hn hp => ⟨(ih n hn hp).1, (ih n hn hp).2.2⟩)
  have hp' : B.pairedSample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
      else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) = some (E fine - E coarse) := by
    rw [hp]
    congr 1
    funext σ x y
    simp only [Pi.sub_apply, Matrix.sub_apply]
    dsimp only [E, w, fine, coarse, Q]
    ring
  refine ⟨E fine - E coarse, C fine - C coarse, hp',
    B.pairedSample_initial M d hM bin r, ?_⟩
  have he : (E fine - E coarse) - (C fine - C coarse) =
      (fun σ x y => (E fine - C fine) σ x y + (-(E coarse - C coarse)) σ x y) := by
    funext σ x y
    simp only [Pi.sub_apply, Matrix.sub_apply, Pi.neg_apply, Matrix.neg_apply]
    ring
  rw [he]
  have hb := rowNormPow_add_le (X := fun σ x => r.source.retains (channels B.padding) σ x)
    (Y := fun σ y => r.usage.retains (channels B.padding) σ y) hNu
    (E fine - C fine) (-(E coarse - C coarse))
  simp only [rowNormPow, Pi.neg_apply, Matrix.neg_apply, abs_neg] at hb
  change rowNormPow 4 P r.source.rate _ _ _ ≤ _ at hb
  apply hb.trans
  have hf := hend fine (B.pairedSample_budgets_lt M d hM r (some bin)).1
  have hc := hend coarse (B.pairedSample_budgets_lt M d hM r (some bin)).2
  change 8 * (_ + _) ≤ 8 * K * (ε fine + ε coarse)
  unfold rowNormPow at hf hc
  linarith

/-- A zero endpoint executes no child, so its perturbation charge is exactly zero.
Positive endpoints retain the direct child's actual request precision. -/
@[expose] def initialEndpointCharge (m : ℕ)
    (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (coefficient : ℝ) : ℝ :=
  if m = 0 then 0 else coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision m q)) ^ 4

omit [Fact P.Prime] in
/-- The exact zero-boundary payment is nonnegative at every actual budget. -/
lemma initialEndpointCharge_nonneg (m : ℕ)
    (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (coefficient : ℝ) :
    0 ≤ B.initialEndpointCharge m q coefficient := by
  unfold initialEndpointCharge
  split_ifs <;> positivity

/-- Actual scheduled endpoints consume strict lower-budget rooted hypotheses at their
own request precision. The coefficient is fixed across these calls; neither a parent
accuracy certificate nor an independently chosen endpoint error budget is accepted. -/
theorem pairedSample_initial_compressed_precision
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M d bin : ℕ) (hM : 0 < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hs : 0 ≤ r.source.rate)
    (D : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (hzero : D 0 = 0)
    (coefficient : ℝ)
    (ih : ∀ n < M, 0 < n →
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin n bin (exponent Q.direct) ζ floor Q.direct = some (D n) ∧
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) (D n)
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤ (coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision n
        (HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)).direct)) ^ 4) ∧
      ∃ R, B.compressedBin n bin (exponent Q.right) ζ floor Q.right = some R) :
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
    let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
    ∃ A C,
      B.pairedSample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) = some A ∧
      B.pairedSample (fun n q => if n < M then B.evaluate n q else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) = some C ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y) (A - C) ≤
        if fine = coarse then 0 else
        8 * (‖fun y => B.binRate bin * HierarchyTask.usageRatio (channels B.padding)
          r.terminal Q.direct y‖ ^ 4 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) ^ 4) *
          (B.initialEndpointCharge fine Q.direct coefficient +
            B.initialEndpointCharge coarse Q.direct coefficient) := by
  dsimp only
  by_cases he : LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) =
      LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
  · refine ⟨0, 0, ?_, ?_, ?_⟩
    · simp only [pairedSample, he, ↓reduceIte]
    · simp only [pairedSample, he, ↓reduceIte]
    · simp [rowNormPow, he]
  rw [ite_eq_right he]
  apply B.pairedSample_initial_compressed_root exponent ζ floor M d bin hM r hs D hzero
    (fun n => B.initialEndpointCharge n
      (HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)).direct coefficient)
    (fun n => B.initialEndpointCharge_nonneg n _ coefficient)
  intro n hn hp
  simpa only [initialEndpointCharge, ite_eq_right (Nat.ne_of_gt hp)] using ih n hn hp

/-- Own-precision payment requiring success only at this unequal pair's actual positive
endpoints. Equal pairs execute no child. This avoids imposing availability at unrelated
small budgets or at an unused bin's endpoints. Reset-right success remains separate. -/
theorem pairedSample_initial_compressed_precision_at
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M d bin : ℕ) (hM : 0 < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hs : 0 ≤ r.source.rate)
    (D : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (hzero : D 0 = 0)
    (coefficient : ℝ)
    (ih :
      let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
      let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
      fine ≠ coarse → ∀ n ∈ ({fine, coarse} : Finset ℕ), n < M → 0 < n →
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin n bin (exponent Q.direct) ζ floor Q.direct = some (D n) ∧
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) (D n)
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤
        coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision n Q.direct)) ^ 4 ∧
      ∃ R, B.compressedBin n bin (exponent Q.right) ζ floor Q.right = some R) :
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
    let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
    ∃ A C,
      B.pairedSample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) = some A ∧
      B.pairedSample (fun n q => if n < M then B.evaluate n q else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) = some C ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y) (A - C) ≤
        if fine = coarse then 0 else
        8 * (‖fun y => B.binRate bin * HierarchyTask.usageRatio (channels B.padding)
          r.terminal Q.direct y‖ ^ 4 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) ^ 4) *
          (B.initialEndpointCharge fine Q.direct coefficient +
            B.initialEndpointCharge coarse Q.direct coefficient) := by
  dsimp only at ih ⊢
  let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)
  let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
  let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
  by_cases heq : fine = coarse
  · dsimp only [fine, coarse] at heq
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · simp only [pairedSample, heq, ↓reduceIte]
    · simp only [pairedSample, heq, ↓reduceIte]
    · simp [rowNormPow, heq]
  dsimp only [fine, coarse] at heq
  let K := ‖fun y => B.binRate bin * HierarchyTask.usageRatio (channels B.padding)
    r.terminal Q.direct y‖ ^ 4 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) ^ 4
  let E : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ := fun n σ x y =>
    B.binRate bin * HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y * D n σ x y
  let C := fun n => if n = 0 then 0 else B.initialSample r bin
  have hend (n : ℕ) (hn : n ∈ ({fine, coarse} : Finset ℕ)) (hlt : n < M) :
      B.sample (fun m q => if m < M then B.compressedHistory exponent ζ floor m q else none)
          n (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) = some (E n) ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y) (E n - C n) ≤
          K * B.initialEndpointCharge n Q.direct coefficient := by
    by_cases hz : n = 0
    · subst n
      have hE : E 0 = 0 := by ext; simp [E, hzero]
      rw [hE]
      simp [sample, C, initialEndpointCharge, rowNormPow]
    obtain ⟨hd, herr, R, hr⟩ := ih heq n hn hlt (Nat.pos_of_ne_zero hz)
    obtain ⟨A, hA, hb⟩ := B.positiveSample_initial_compressed_root exponent ζ floor
      M n bin hlt r hs (D n) R hd hr
    have ha : A = E n := Option.some.inj (hA.symm.trans
      (B.positiveSample_initial_compressed exponent ζ floor M n bin hlt r (D n) R hd hr).1)
    rw [ha] at hA hb
    refine ⟨?_, ?_⟩
    · simpa only [sample, ite_eq_right hz] using hA
    · have he : E n - C n = (fun σ x y => E n σ x y - B.initialSample r bin σ x y) := by
        funext σ x y
        simp only [Pi.sub_apply, Matrix.sub_apply, C, ite_eq_right hz]
      rw [he]
      simpa only [initialEndpointCharge, ite_eq_right hz, K, Q] using
        hb.trans (mul_le_mul_of_nonneg_left herr (show 0 ≤ K by positivity))
  have hlt := B.pairedSample_budgets_lt M d hM r (some bin)
  have hf := hend fine (by simp only [mem_insert, mem_singleton, true_or]) hlt.1
  have hc := hend coarse (by simp only [mem_insert, mem_singleton, or_true]) hlt.2
  dsimp only [fine, coarse] at hf hc
  refine ⟨E fine - E coarse, C fine - C coarse, ?_,
    B.pairedSample_initial M d hM bin r, ?_⟩
  · rw [pairedSample, ite_eq_right heq, hf.1, hc.1]
    rfl
  · have he : (E fine - E coarse) - (C fine - C coarse) =
        (fun σ x y => (E fine - C fine) σ x y + (-(E coarse - C coarse)) σ x y) := by
      funext σ x y
      simp only [Pi.sub_apply, Matrix.sub_apply, Pi.neg_apply, Matrix.neg_apply]
      ring
    rw [he, ite_eq_right heq]
    have hb := rowNormPow_add_le
      (X := fun σ x => r.source.retains (channels B.padding) σ x)
      (Y := fun σ y => r.usage.retains (channels B.padding) σ y)
      (mul_nonneg (Nat.cast_nonneg P) hs) (E fine - C fine) (-(E coarse - C coarse))
    simp only [rowNormPow, Pi.neg_apply, Matrix.neg_apply, abs_neg] at hb
    change rowNormPow 4 P r.source.rate _ _ _ ≤ _ at hb
    apply hb.trans
    change 8 * (_ + _) ≤ 8 * K *
      (B.initialEndpointCharge fine Q.direct coefficient +
        B.initialEndpointCharge coarse Q.direct coefficient)
    have hf' := hf.2
    have hc' := hc.2
    unfold rowNormPow at hf' hc'
    dsimp only [fine, coarse, Q, K] at hf' hc' ⊢
    linarith

/-- Completion transports the literal paired-history difference through the same graph,
length, source and usage suffixes. It introduces no canonical-equality assumption. -/
theorem complete_grid_sub (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su)
    (A C : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :
    B.complete M r (A - C) d = some (conditionalWalk
      (X s (side P ks) (CopyPadding.identifier B.padding ss))
      (Y t (side P ku) (CopyPadding.identifier B.padding su))
      (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
        (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su))
      (fun _ _ => B.steps M r d) A - conditionalWalk
      (X s (side P ks) (CopyPadding.identifier B.padding ss))
      (Y t (side P ku) (CopyPadding.identifier B.padding su))
      (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
        (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su))
      (fun _ _ => B.steps M r d) C) := by
  rw [B.complete_grid M r s t hst ks ku ss su hs hu (A - C) d,
    conditionalWalk_sub]

/-- The actual completion of a paired approximate history has a fourth-moment payment
from the two endpoint perturbations. Source and usage are the parent's literal grid
channels; different endpoint budgets and correlated errors require no extra assumption. -/
theorem complete_paired_error (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su)
    (A C A₀ C₀ : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Yu := Y t (side P ku) (CopyPadding.identifier B.padding su)
    let G := graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
      (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su)
    ∃ F : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ,
      B.complete M r (A - C) d = some F ∧
      rowNormPow 4 P r.source.rate Xs Yu
        (fun σ x y => F σ x y -
          conditionalWalk Xs Yu G (fun _ _ => B.steps M r d) (A₀ - C₀) σ x y) ≤
      8 * (rowNormPow 4 P r.source.rate Xs Yu (A - A₀) +
        rowNormPow 4 P r.source.rate Xs Yu (C - C₀)) := by
  dsimp only
  refine ⟨_, B.complete_grid M r s t hst ks ku ss su hs hu (A - C) d, ?_⟩
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]
    exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  exact rowNormPow_conditionalWalk_paired_fourth_le _ _ hNu _ _ A C A₀ C₀

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData

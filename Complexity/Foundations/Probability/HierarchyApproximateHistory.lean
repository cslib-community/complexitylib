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

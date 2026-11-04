/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyBudgetEvaluator
public import Complexity.Foundations.Probability.NormalizedAtomRows.ActualMoment
public import Complexity.Foundations.Probability.NormalizedAtomRows.SecondSignal
public import Complexity.Foundations.Probability.UnroutedBinDecoder

/-!
# Compressed normalized bins from actual budget history

The first signal sums the actual completed initial groups on full terminal rank. The second
signal completes the selected bin preparation of each first prefix on source × usage. Both
use the original environment. Compression decodes with the selected bin numerator, not the
hierarchy's atom cutoff. The result has dense normalized-bin scope; it is not RAW or an
incoming/max-decorated correction.

The integrated conditional comparison consumes the successful executed histories against the
genuine dense polynomial-preparation target, using support after compression and raw-prefix
false-overflow charges. It does not establish the lower-budget canonical-error invariant or
its weighted mean/noise and heavy-tail payments. Later RAW constructors remain unavailable
in the underlying evaluator.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.RowCompression Cslib.Probability
open NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- Prefixes of the actual completed groups, with zero at prefix length zero.
The history and all paired budgets are those of the public budget evaluator. -/
@[expose] def initialPrefixes (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Option (ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) := do
  let groups ← (List.range (Nat.log2 M + 1)).mapM fun j =>
    B.completedGroup (fun m q => if m < M then B.evaluate m q else none) M
      (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
      { r with usage := r.terminal }
  pure fun j σ x y => ((groups.take j).map (fun A => A σ x y)).sum

/-- Selected dense preparation of a stochastic first prefix, before its actual usage walk.
The numerator's corresponding bin preparation is retained, including the full terminal rank. -/
@[expose] def binPreparation (bin : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :
    Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
  fun σ => densePreparation B.padding id r (B.auxiliary bin) HP.ρ HP.K (A σ) σ

/-- Shared pure compression/decoding of executed first prefixes and preparation walks.
Both semantic and transported histories use this same two-signal iterate. Execution and
accuracy certificates belong to its callers; this function supplies neither. -/
@[expose] def decodePrefixes (M bin k : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (walks : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)) :
    Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
  let m := Nat.log2 M + 1
  let W := fun j σ x y => (walks[j - 1]?.getD 0) σ x y
  let Δ := firstSignalIncrement F k (secondSignalIncrement W ζ)
  fun σ x y =>
    let S : Finset (ZMod P) := {z | r.terminal.retains (channels B.padding) σ z}
    let a := iterate S (compatibleCapacity HP.K m) (fun _ => HP.K)
      (dyadicFloor floor m) (Δ σ x) ⟨0, 0⟩ m
    if r.usage.retains (channels B.padding) σ y then
      FourthRootHierarchyParams.NormalizedRow.output (B.cutoff bin) HP.ρ ζ
        (a.row y 0) (a.row y 1) (firstRank S HP.K a.defaultValue a.row)
    else 0

/-- Actual paired-group first prefixes, computed preparatory second prefixes and compression.
The positive-budget guard preserves the unavailable coarse boundary. The return scope is the
selected dense normalized bin; no incoming or maximum gate is added. -/
@[expose] def compressedBin (M bin k : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Option (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) := do
  if M = 0 ∨ ¬ 0 < B.requestPrecision M r ∨ r.terminal.rate ≠ rate k then none else do
    let F ← B.initialPrefixes M r
    let m := Nat.log2 M + 1
    let walks ← (List.range m).mapM fun j =>
      B.complete M r (B.binPreparation bin r (F (j + 1))) (dyadicSlack m j)
    pure (B.decodePrefixes M bin k ζ floor r F walks)

/-- Every successful compressed bin has the bounded normalized range and literal usage
support, independently of the additional cutoff hypotheses needed for rank sparsity. -/
theorem compressedBin_range_usage (M bin k : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : B.compressedBin M bin k ζ floor r = some A) :
    (∀ σ x y, A σ x y ∈ Set.Icc 0 (2 * B.binCap)) ∧
    (∀ σ x y, ¬ r.usage.retains (channels B.padding) σ y → A σ x y = 0) := by
  unfold compressedBin at hA
  simp only [decodePrefixes] at hA
  split at hA
  · contradiction
  · cases hF : B.initialPrefixes M r with
    | none => simp [hF] at hA
    | some F =>
      simp only [hF, bind, Option.bind_some] at hA
      cases hW : (List.range (Nat.log2 M + 1)).mapM (fun j =>
          B.complete M r (B.binPreparation bin r (F (j + 1)))
            (dyadicSlack (Nat.log2 M + 1) j)) with
      | none => simp [hW] at hA
      | some W =>
        simp only [hW, Option.bind_some, pure] at hA
        have ha := Option.some.inj hA
        subst A
        dsimp only
        constructor
        · intro σ x y
          split_ifs
          · exact FourthRootHierarchyParams.NormalizedRow.output_mem_Icc _ _ B.binCap_nonneg
              (B.cutoff_bounds bin) (fun q => ⟨HP.ρ_nonneg q, HP.ρ_le_one q⟩) _ _ _ _
          · exact ⟨le_rfl, mul_nonneg (by norm_num) B.binCap_nonneg⟩
        · intro σ x y hy
          exact ite_eq_right hy

/-- Successful compression retains the actual bin's range and usage mask. The separate
threshold premise proves terminal-row support after compression, without propagating support
through either of its walks. No child-error or final-accuracy premise is used. -/
theorem compressedBin_bounds (M bin k : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : B.compressedBin M bin k ζ floor r = some A)
    {e g : ℝ} (he : 0 ≤ e) (hge : g ≤ e)
    (hc : ∀ d, d ≤ e → B.cutoff bin d = 0) (hg : ∀ q, g ≤ q → HP.ρ q = 0) :
    (∀ σ x y, A σ x y ∈ Set.Icc 0 (2 * B.binCap)) ∧
    (∀ σ x y, ¬ r.usage.retains (channels B.padding) σ y → A σ x y = 0) ∧
    ∀ σ x, #{y ∈ ({y | r.terminal.retains (channels B.padding) σ y} : Finset _) |
      A σ x y ≠ 0} < HP.K := by
  have hru := B.compressedBin_range_usage M bin k ζ floor r A hA
  unfold compressedBin at hA
  simp only [decodePrefixes] at hA
  split at hA
  · contradiction
  · cases hF : B.initialPrefixes M r with
    | none => simp [hF] at hA
    | some F =>
      simp only [hF, bind, Option.bind_some] at hA
      cases hW : (List.range (Nat.log2 M + 1)).mapM (fun j =>
          B.complete M r (B.binPreparation bin r (F (j + 1)))
            (dyadicSlack (Nat.log2 M + 1) j)) with
      | none => simp [hW] at hA
      | some W =>
        simp only [hW, Option.bind_some, pure] at hA
        have ha := Option.some.inj hA
        subst A
        dsimp only
        refine ⟨?_, ?_, ?_⟩
        · exact hru.1
        · exact hru.2
        · intro σ x
          let a := iterate {z | r.terminal.retains (channels B.padding) σ z}
            (compatibleCapacity HP.K (Nat.log2 M + 1)) (fun _ => HP.K)
            (dyadicFloor floor (Nat.log2 M + 1))
            (firstSignalIncrement F k
              (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ) σ x)
            ⟨0, 0⟩ (Nat.log2 M + 1)
          apply lt_of_le_of_lt (card_le_card ?_)
            (FourthRootHierarchyParams.NormalizedRow.support_of_cutoff _ _
              (FourthRootHierarchyParams.NormalizedRow.rank_pos HP) he hge hc hg
              {z | r.terminal.retains (channels B.padding) σ z} a ζ)
          intro y hy
          simp only [mem_filter] at hy ⊢
          refine ⟨hy.1, ?_⟩
          split_ifs at hy with hu
          · exact hy.2
          · exact (hy.2 rfl).elim

/-- Preparation retains its scalar range on the original full environment. -/
theorem binPreparation_mem_Icc (bin : ℕ)
    (haux : ∀ d, B.auxiliary bin d ∈ Set.Icc 0 1)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (G : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (σ : Environment P 3) (x y : ZMod P) :
    B.binPreparation bin r G σ x y ∈ Set.Icc 0 1 := by
  change B.auxiliary bin _ * HP.ρ _ ∈ Set.Icc 0 1
  exact ⟨mul_nonneg (haux _).1 (HP.ρ_nonneg _),
    (mul_le_of_le_one_right (haux _).1 (HP.ρ_le_one _)).trans (haux _).2⟩

/-- Conditional accuracy of the executed compressed bin against the genuine dense normalized
recipe on the deterministic canonical matrix G. Both signals are the actual history prefixes
and computed preparation walks. The remaining hypothesis is a raw-prefix clipped-error
bound on those executions, including prefix zero; it is not a parent output certificate.
Deriving and paying this bound from ALL lower-budget canonical errors remains separate. -/
theorem exists_compressedBin_root_bound (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {cap ζ : ℝ} (hcap : 0 ≤ cap) (hζ : 0 < ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P)
      (b : ℕ → ℝ), (∀ i, 0 < b i) → (∀ i, b i = 16 * b (i + 1)) →
      ∀ (M bin k : ℕ) (floor scale : ℝ)
        (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)), Admissible r →
      r.terminal.rate = rate k →
      B.cutoff bin = boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap bin
        (fun _ => 1) → B.auxiliary bin = polynomialPrepCutoff4 HP.θ →
      0 < scale → scale ≤ max cap 16 / 10000 → scale ≤ HP.η → ζ ≤ scale / 2 →
      0 ≤ floor → floor ≤ scale →
      ∀ (G : Matrix (ZMod P) (ZMod P) ℝ), (∀ x y, 0 ≤ G x y) →
      ∀ (ε : ℕ → ℝ), (∀ i ≤ Nat.log2 M + 1, 0 ≤ ε i) →
      (∀ F, B.initialPrefixes M r = some F → ∀ W,
        (List.range (Nat.log2 M + 1)).mapM (fun j =>
          B.complete M r (B.binPreparation bin r (F (j + 1)))
            (dyadicSlack (Nat.log2 M + 1) j)) = some W →
        ∀ i ≤ Nat.log2 M + 1, ∀ σ x y,
          r.terminal.retains (channels B.padding) σ y →
          clippedError
            (requestSignals ζ B.padding id r (fun _ => G)
              (B.binPreparation bin r (fun _ => G)) σ x y 0)
            (requestSignals ζ B.padding id r (fun _ => G)
              (B.binPreparation bin r (fun _ => G)) σ x y 1)
            (uncompressedRow
              (firstSignalIncrement F k
                (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ) σ x)
              0 i y) ≤ ε i) →
      ∀ A, B.compressedBin M bin k ζ floor r = some A → ∀ σ x y,
        r.terminal.retains (channels B.padding) σ y →
        |A σ x y ^ (4⁻¹ : ℝ) -
          denseChild B.padding id r (B.cutoff bin) (polynomialPrepCutoff4 HP.θ)
            HP.ρ HP.K G σ x y ^ (4⁻¹ : ℝ)| ≤
          C * prefixErrorBudget ε (Nat.log2 M + 1) := by
  obtain ⟨C, hC, hc⟩ := DenseBinRecipe.exists_polynomialUnrouted_iterate_bound HP hcap hζ
  refine ⟨C, hC, ?_⟩
  intro P _ B b hb hstep M bin k floor scale r hr hrate hcut haux hs hscale hmargin hsmall
    hfloor hfs G hG ε hε herr A hA σ x y hy
  let truth := requestSignals ζ B.padding id r (fun _ => G)
    (B.binPreparation bin r (fun _ => G)) σ x
  have htfirst (z : ZMod P) (_hz : r.terminal.retains (channels B.padding) σ z) :
      0 ≤ truth z 0 := by
    simp only [truth, requestSignals, Fin.isValue, ↓reduceIte, hrate]
    exact div_nonneg (hG x z) (rate_pos k).le
  have htsecond (z : ZMod P) (_hz : r.terminal.retains (channels B.padding) σ z) :
      |truth z 1| ≤ scale / 2 := by
    let T : Finset (Environment P 3) :=
      {τ | r.source.retains (channels B.padding) τ x ∧
        r.usage.retains (channels B.padding) τ z}
    have hp (τ : Environment P 3) := B.binPreparation_mem_Icc bin
      (fun d => by rw [haux]; exact ⟨polynomialPrepCutoff4_nonneg _ _,
        polynomialPrepCutoff4_le_one _ _⟩) r (fun _ => G) τ x z
    have hm : (𝔼 τ ∈ T, B.binPreparation bin r (fun _ => G) τ x z) ∈ Set.Icc 0 1 := by
      constructor
      · exact expect_nonneg fun τ _ => (hp τ).1
      · rcases T.eq_empty_or_nonempty with h | h
        · rw [h]; norm_num
        · exact expect_le h fun τ _ => (hp τ).2
    simp only [truth, requestSignals, Fin.isValue, one_ne_zero, ↓reduceIte]
    split_ifs
    · rw [abs_mul, abs_of_pos hζ]
      change ζ * |𝔼 τ ∈ T, B.binPreparation bin r (fun _ => G) τ x z| ≤ scale / 2
      rw [abs_of_nonneg hm.1]
      exact (mul_le_of_le_one_right hζ.le hm.2).trans hsmall
    · simp only [mul_zero, abs_zero]; linarith
  unfold compressedBin at hA
  simp only [decodePrefixes] at hA
  split at hA
  · contradiction
  · cases hF : B.initialPrefixes M r with
    | none => simp [hF] at hA
    | some F =>
      simp only [hF, bind, Option.bind_some] at hA
      cases hW : (List.range (Nat.log2 M + 1)).mapM (fun j =>
          B.complete M r (B.binPreparation bin r (F (j + 1)))
            (dyadicSlack (Nat.log2 M + 1) j)) with
      | none => simp [hW] at hA
      | some W =>
        simp only [hW, Option.bind_some, pure] at hA
        have ha := Option.some.inj hA
        subst A
        dsimp only
        rw [denseChild, ← haux]
        rw [normalizedRequest_eq_output (B.cutoff bin) HP.ρ HP.K hζ B.padding id r hr]
        change |(if r.usage.retains (channels B.padding) σ y then _ else 0) ^ (4⁻¹ : ℝ) -
          (if r.usage.retains (channels B.padding) σ y then _ else 0) ^ (4⁻¹ : ℝ)| ≤ _
        split_ifs with hu
        · rw [hcut]
          exact hc b hb hstep bin {z | r.terminal.retains (channels B.padding) σ z}
            (compatibleCapacity HP.K (Nat.log2 M + 1)) (dyadicFloor floor (Nat.log2 M + 1))
            (firstSignalIncrement F k
              (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ) σ x)
            truth 0 scale (Nat.log2 M + 1) hs hscale hmargin (by omega)
            (fun i _ => (compatibleCapacity_bounds HP.K _ i).1)
            (fun i _ => (dyadicFloor_le_scale_div hfloor _ i).trans (by linarith))
            (fun z hz => htfirst z (mem_filter.mp hz).2)
            (fun z hz => htsecond z (mem_filter.mp hz).2) ε hε
            (fun i hi z hz => herr F hF W hW i hi σ x z (mem_filter.mp hz).2)
            y (mem_filter.mpr ⟨mem_univ _, hy⟩)
        · rw [sub_self, abs_zero]
          exact mul_nonneg hC (prefixErrorBudget_nonneg hε)

/-- Sharp conditional comparison for the constructed zero-start compressed consumer.
The truth is the deterministic dense polynomial-preparation bin, with the actual terminal
rank and source/usage slice mean. The no-overflow premise concerns the executed history.
Only post-increment clipped errors and the final error are assumed: no prefix-zero accuracy
or supplied initial truth is required. Weighted mean/noise and recursive IH payments remain open. -/
theorem exists_compressedBin_sharp_noOverflow (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {cap ζ : ℝ} (hcap : 0 ≤ cap) (hζ : 0 < ζ) :
    ∃ Cfinal : ℝ, 0 ≤ Cfinal ∧ ∀ floor : ℝ, 0 < floor → floor ≤ HP.η →
      floor ≤ max cap 16 → ∃ Cpre : ℝ, 0 ≤ Cpre ∧ ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P)
      (b : ℕ → ℝ), (∀ i, 0 < b i) → (∀ i, b i = 16 * b (i + 1)) →
      ∀ (M bin k : ℕ)
        (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)), Admissible r →
      r.terminal.rate = rate k →
      B.cutoff bin = boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap bin
        (fun _ => 1) → B.auxiliary bin = polynomialPrepCutoff4 HP.θ →
      ∀ (G : Matrix (ZMod P) (ZMod P) ℝ), (∀ x y, 0 ≤ G x y) →
      (∀ F, B.initialPrefixes M r = some F → ∀ W,
        (List.range (Nat.log2 M + 1)).mapM (fun j =>
          B.complete M r (B.binPreparation bin r (F (j + 1)))
            (dyadicSlack (Nat.log2 M + 1) j)) = some W →
        ∀ σ x i, i < Nat.log2 M + 1 →
          stepThreshold {z | r.terminal.retains (channels B.padding) σ z}
            (compatibleCapacity HP.K (Nat.log2 M + 1)) (fun _ => HP.K)
            (dyadicFloor floor (Nat.log2 M + 1))
            (firstSignalIncrement F k
              (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ) σ x)
            ⟨0, 0⟩ i ≤ dyadicFloor floor (Nat.log2 M + 1) i) →
      ∀ (ε : ℕ → ℝ), (∀ i < Nat.log2 M + 1, 0 ≤ ε (i + 1)) →
      (∀ F, B.initialPrefixes M r = some F → ∀ W,
        (List.range (Nat.log2 M + 1)).mapM (fun j =>
          B.complete M r (B.binPreparation bin r (F (j + 1)))
            (dyadicSlack (Nat.log2 M + 1) j)) = some W →
        ∀ i < Nat.log2 M + 1, ∀ σ x y,
          r.terminal.retains (channels B.padding) σ y →
          floor / 2 ≤ requestSignals ζ B.padding id r (fun _ => G)
            (B.binPreparation bin r (fun _ => G)) σ x y 0 →
          clippedError
            (requestSignals ζ B.padding id r (fun _ => G)
              (B.binPreparation bin r (fun _ => G)) σ x y 0)
            (requestSignals ζ B.padding id r (fun _ => G)
              (B.binPreparation bin r (fun _ => G)) σ x y 1)
            (uncompressedRow
              (firstSignalIncrement F k
                (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ) σ x)
              0 (i + 1) y) ≤ ε (i + 1)) →
      ∀ εfinal : ℝ, 0 ≤ εfinal →
      (∀ F, B.initialPrefixes M r = some F → ∀ W,
        (List.range (Nat.log2 M + 1)).mapM (fun j =>
          B.complete M r (B.binPreparation bin r (F (j + 1)))
            (dyadicSlack (Nat.log2 M + 1) j)) = some W →
        ∀ σ x y,
          r.terminal.retains (channels B.padding) σ y →
          clippedError
            (requestSignals ζ B.padding id r (fun _ => G)
              (B.binPreparation bin r (fun _ => G)) σ x y 0)
            (requestSignals ζ B.padding id r (fun _ => G)
              (B.binPreparation bin r (fun _ => G)) σ x y 1)
            (uncompressedRow
              (firstSignalIncrement F k
                (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ) σ x)
              0 (Nat.log2 M + 1) y) ≤ εfinal) →
      ∀ A, B.compressedBin M bin k ζ floor r = some A → ∀ σ x y,
        r.terminal.retains (channels B.padding) σ y →
        |A σ x y ^ (4⁻¹ : ℝ) -
          denseChild B.padding id r (B.cutoff bin) (polynomialPrepCutoff4 HP.θ)
            HP.ρ HP.K G σ x y ^ (4⁻¹ : ℝ)| ≤
          Cpre * ∑ i ∈ range (Nat.log2 M + 1), dyadicFloor floor (Nat.log2 M + 1) i * ε (i + 1) +
          Cfinal * εfinal := by
  obtain ⟨Cf, hCf, hf⟩ := DenseBinRecipe.exists_polynomialUnrouted_sharp_noOverflow HP hcap hζ
  refine ⟨Cf, hCf, ?_⟩
  intro floor hfloor hmargin hfloorT
  obtain ⟨Cp, hCp, hc⟩ := hf floor hfloor hmargin hfloorT
  refine ⟨Cp, hCp, ?_⟩
  intro P _ B b hb hstep M bin k r hr hrate hcut haux G hG hno ε hε herr
    εfinal hεfinal herrfinal A hA σ x y hy
  let truth := requestSignals ζ B.padding id r (fun _ => G)
    (B.binPreparation bin r (fun _ => G)) σ x
  have htfirst (z : ZMod P) (_hz : r.terminal.retains (channels B.padding) σ z) :
      0 ≤ truth z 0 := by
    simp only [truth, requestSignals, Fin.isValue, ↓reduceIte, hrate]
    exact div_nonneg (hG x z) (rate_pos k).le
  unfold compressedBin at hA
  simp only [decodePrefixes] at hA
  split at hA
  · contradiction
  · cases hF : B.initialPrefixes M r with
    | none => simp [hF] at hA
    | some F =>
      simp only [hF, bind, Option.bind_some] at hA
      cases hW : (List.range (Nat.log2 M + 1)).mapM (fun j =>
          B.complete M r (B.binPreparation bin r (F (j + 1)))
            (dyadicSlack (Nat.log2 M + 1) j)) with
      | none => simp [hW] at hA
      | some W =>
        simp only [hW, Option.bind_some, pure] at hA
        have ha := Option.some.inj hA
        subst A
        dsimp only
        rw [denseChild, ← haux]
        rw [normalizedRequest_eq_output (B.cutoff bin) HP.ρ HP.K hζ B.padding id r hr]
        change |(if r.usage.retains (channels B.padding) σ y then _ else 0) ^ (4⁻¹ : ℝ) -
          (if r.usage.retains (channels B.padding) σ y then _ else 0) ^ (4⁻¹ : ℝ)| ≤ _
        split_ifs with hu
        · rw [hcut]
          exact hc b hb hstep bin {z | r.terminal.retains (channels B.padding) σ z}
            (compatibleCapacity HP.K (Nat.log2 M + 1))
            (firstSignalIncrement F k
              (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ) σ x)
            truth 0 (Nat.log2 M + 1) (hno F hF W hW σ x)
            (fun z hz => htfirst z (mem_filter.mp hz).2) (fun i => ε (i + 1)) hε
            (fun i hi z hz hd => herr F hF W hW i hi σ x z (mem_filter.mp hz).2 hd)
            εfinal hεfinal
            (fun z hz => herrfinal F hF W hW σ x z (mem_filter.mp hz).2)
            y (mem_filter.mpr ⟨mem_univ _, hy⟩)
        · rw [sub_self, abs_zero]
          exact add_nonneg (mul_nonneg hCp (sum_nonneg fun i hi =>
            mul_nonneg (dyadicFloor_nonneg hfloor.le _ _) (hε i (mem_range.mp hi))))
            (mul_nonneg hCf hεfinal)

/-- The shared decoder's usage-masked error is bounded by its full-terminal error.
This algebraic bridge applies to either history; it supplies no execution certificate. -/
theorem decodePrefixes_rootDistPow_le (M bin k : ℕ) {ζ floor N u : ℝ}
    (hζ : 0 < ζ) (hNu : 0 ≤ N * u)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : Admissible r)
    (G : Matrix (ZMod P) (ZMod P) ℝ)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)) :
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
    let Δ := firstSignalIncrement F k
      (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ)
    let truth := requestSignals ζ B.padding id r (fun _ => G)
      (B.binPreparation bin r (fun _ => G))
    let S := fun σ => ({y | Y σ y} : Finset (ZMod P))
    let actual := fun σ x => iterate (S σ) (compatibleCapacity HP.K (Nat.log2 M + 1))
      (fun _ => HP.K) (dyadicFloor floor (Nat.log2 M + 1)) (Δ σ x) ⟨0, 0⟩ (Nat.log2 M + 1)
    rootDistPow 4 N u X Y (B.decodePrefixes M bin k ζ floor r F W)
      (denseChild B.padding id r (B.cutoff bin) (B.auxiliary bin) HP.ρ HP.K G) ≤
      rowNormPow 4 N u X Y (fun σ x y => stateRootError
        (FourthRootHierarchyParams.NormalizedRow.output (B.cutoff bin) HP.ρ ζ)
        (S σ) HP.K (actual σ x) ⟨0, truth σ x⟩ y) := by
  dsimp only [decodePrefixes]
  unfold rootDistPow rowNormPow
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNu)
  apply expect_le_expect
  intro σ _
  apply sum_le_sum
  intro x _
  apply sum_le_sum
  intro y _
  dsimp only
  rw [denseChild, normalizedRequest_eq_output (B.cutoff bin) HP.ρ HP.K hζ B.padding id r hr]
  change |(if r.usage.retains (channels B.padding) σ y then _ else 0) ^ (4⁻¹ : ℝ) -
    (if r.usage.retains (channels B.padding) σ y then _ else 0) ^ (4⁻¹ : ℝ)| ^ 4 ≤ _
  split_ifs
  · exact le_rfl
  · rw [sub_self, abs_zero, zero_pow (by decide : 4 ≠ 0)]
    positivity


/-- The executed compressed bin's usage-masked error is bounded by its full-terminal
prefix decoder error against the genuine dense preparation target on the same environment. -/
theorem compressedBin_rootDistPow_le (M bin k : ℕ) {ζ floor N u : ℝ}
    (hζ : 0 < ζ) (hNu : 0 ≤ N * u)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : Admissible r)
    (G : Matrix (ZMod P) (ZMod P) ℝ)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hF : B.initialPrefixes M r = some F)
    (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (hW : (List.range (Nat.log2 M + 1)).mapM (fun j =>
      B.complete M r (B.binPreparation bin r (F (j + 1)))
        (dyadicSlack (Nat.log2 M + 1) j)) = some W)
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : B.compressedBin M bin k ζ floor r = some A) :
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
    let Δ := firstSignalIncrement F k
      (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ)
    let truth := requestSignals ζ B.padding id r (fun _ => G)
      (B.binPreparation bin r (fun _ => G))
    let S := fun σ => ({y | Y σ y} : Finset (ZMod P))
    let actual := fun σ x => iterate (S σ) (compatibleCapacity HP.K (Nat.log2 M + 1))
      (fun _ => HP.K) (dyadicFloor floor (Nat.log2 M + 1)) (Δ σ x) ⟨0, 0⟩ (Nat.log2 M + 1)
    rootDistPow 4 N u X Y A
      (denseChild B.padding id r (B.cutoff bin) (B.auxiliary bin) HP.ρ HP.K G) ≤
      rowNormPow 4 N u X Y (fun σ x y => stateRootError
        (FourthRootHierarchyParams.NormalizedRow.output (B.cutoff bin) HP.ρ ζ)
        (S σ) HP.K (actual σ x) ⟨0, truth σ x⟩ y) := by
  unfold compressedBin at hA
  simp only [decodePrefixes] at hA
  split at hA
  · contradiction
  · simp only [hF, bind, Option.bind_some, hW, pure] at hA
    have heq := Option.some.inj hA
    subst A
    exact B.decodePrefixes_rootDistPow_le M bin k hζ hNu r hr G F W

/-- Integrated comparison for the shared decoder, independent of the origin of its inputs.
The masks, rank and canonical joint mean are literal request data. Polynomial preparation
proves the light-entry annihilation needed by false-overflow payment. Error envelopes
still require payment from the lower-budget invariant; this is a conditional analytic kernel. -/
theorem exists_decodePrefixes_integrated (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {cap ζ scale : ℝ} (hcap : 0 ≤ cap) (hζ : 0 < ζ) (hs : 0 < scale)
    (hmargin : scale ≤ HP.η) (hcapscale : scale ≤ max cap 16 / 10000)
    (hsmall : ζ ≤ scale / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ floor : ℝ, 0 < floor → floor ≤ scale → floor ≤ 1 →
      ∃ Cpre : ℝ, 0 ≤ Cpre ∧ ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P)
      (b : ℕ → ℝ), (∀ i, 0 < b i) → (∀ i, b i = 16 * b (i + 1)) →
      ∀ (M bin k : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
      Admissible r → r.terminal.rate = rate k →
      B.cutoff bin = boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap bin
        (fun _ => 1) → B.auxiliary bin = polynomialPrepCutoff4 HP.θ →
      ∀ (G : Matrix (ZMod P) (ZMod P) ℝ), (∀ x y, 0 ≤ G x y) →
      ∀ (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
        (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)),
      ∀ N u : ℝ, 0 ≤ N * u →
      let m := Nat.log2 M + 1
      let n := compatibleCapacity HP.K m
      let X := fun σ x => r.source.retains (channels B.padding) σ x
      let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
      let Δ := firstSignalIncrement F k
        (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ)
      let raw : Environment P 3 → ZMod P → ZMod P → Fin 2 → ℝ := 0
      let truth := requestSignals ζ B.padding id r (fun _ => G)
        (B.binPreparation bin r (fun _ => G))
      ∀ (ε : ℕ → Environment P 3 → ZMod P → ℝ) (εfinal : Environment P 3 → ZMod P → ℝ),
        (∀ i < m, ∀ σ x, X σ x → 0 ≤ ε i σ x) →
        (∀ σ x, X σ x → 0 ≤ εfinal σ x) →
        (∀ i < m, ∀ σ x y, X σ x → Y σ y →
          clippedError (truth σ x y 0) (truth σ x y 1)
            (uncompressedRow (Δ σ x) (raw σ x) (i + 1) y) ≤ ε i σ x) →
        (∀ σ x y, X σ x → Y σ y →
          clippedError (truth σ x y 0) (truth σ x y 1)
            (uncompressedRow (Δ σ x) (raw σ x) m y) ≤ εfinal σ x) →
        let S := fun σ => ({y | Y σ y} : Finset (ZMod P))
        let Pre := fun σ x => ∑ i ∈ range m, dyadicFloor floor m i * ε i σ x
        let No := fun σ x => if ∀ i < m,
          stepThreshold (S σ) n (fun _ => HP.K) (dyadicFloor floor m) (Δ σ x) ⟨0, raw σ x⟩ i ≤
            dyadicFloor floor m i then εfinal σ x else 0
        let Tail := fun σ x => ∑ j ∈ range m,
          if IsFirstOverflow (S σ) n (fun _ => HP.K) (dyadicFloor floor m) (Δ σ x) ⟨0, raw σ x⟩ j ∧
            heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor floor m j) (n j) σ then
              ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i σ x else 0
        rootDistPow 4 N u X Y (B.decodePrefixes M bin k ζ floor r F W)
          (denseChild B.padding id r (B.cutoff bin) (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K G) ≤
          128 * (HP.K : ℝ) * (Cpre ^ 4 * vertexNormPow 4 N u X Pre +
            C ^ 4 * vertexNormPow 4 N u X No + C ^ 4 * vertexNormPow 4 N u X Tail) +
          ∑ j ∈ range m, (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 / ((n j : ℝ) *
            dyadicFloor floor m j ^ 4)) *
            rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
              (uncompressedRow (Δ σ x) (raw σ x) (j + 1) y)) := by
  obtain ⟨C, hC, hscales⟩ := DenseBinRecipe.exists_polynomialUnrouted_rowNormPow_le
    HP hcap hζ hs hmargin hcapscale
  refine ⟨C, hC, ?_⟩
  intro floor hfloor hfs hf1
  obtain ⟨Cp, hCp, hbound⟩ := hscales floor hfloor hfs hf1
  refine ⟨Cp, hCp, ?_⟩
  intro P _ B b hb hstep M bin k r hr hrate hcut haux G hG F W N u hNu
  dsimp only
  intro ε εfinal hε hεfinal herr herrfinal
  rw [← haux]
  refine (B.decodePrefixes_rootDistPow_le M bin k hζ hNu r hr G F W).trans ?_
  rw [hcut]
  apply hbound b hb hstep bin N u hNu
    (fun σ x => r.source.retains (channels B.padding) σ x)
    (fun σ y => r.terminal.retains (channels B.padding) σ y)
    (compatibleCapacity HP.K (Nat.log2 M + 1)) (Nat.log2 M + 1)
    (fun i _ => (compatibleCapacity_bounds HP.K _ i).1)
    (firstSignalIncrement F k
      (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ)) 0
    (requestSignals ζ B.padding id r (fun _ => G)
      (B.binPreparation bin r (fun _ => G)))
  · intro σ x y _ _
    simp only [requestSignals, Fin.isValue, ↓reduceIte, hrate]
    exact div_nonneg (hG x y) (rate_pos k).le
  · intro σ x y _ _
    let T : Finset (Environment P 3) :=
      {τ | r.source.retains (channels B.padding) τ x ∧
        r.usage.retains (channels B.padding) τ y}
    have hp (τ : Environment P 3) := B.binPreparation_mem_Icc bin
      (fun d => by rw [haux]; exact ⟨polynomialPrepCutoff4_nonneg _ _,
        polynomialPrepCutoff4_le_one _ _⟩) r (fun _ => G) τ x y
    have hm : (𝔼 τ ∈ T, B.binPreparation bin r (fun _ => G) τ x y) ∈ Set.Icc 0 1 := by
      constructor
      · exact expect_nonneg fun τ _ => (hp τ).1
      · rcases T.eq_empty_or_nonempty with h | h
        · rw [h]; norm_num
        · exact expect_le h fun τ _ => (hp τ).2
    simp only [requestSignals, Fin.isValue, one_ne_zero, ↓reduceIte]
    split_ifs
    · rw [abs_mul, abs_of_pos hζ]
      change ζ * |𝔼 τ ∈ T, B.binPreparation bin r (fun _ => G) τ x y| ≤ scale / 2
      rw [abs_of_nonneg hm.1]
      exact (mul_le_of_le_one_right hζ.le hm.2).trans hsmall
    · simp only [mul_zero, abs_zero]; linarith
  · intro j _ σ x y _ _ hd
    have hd' : G x y / r.terminal.rate ≤ HP.θ / 2 := by
      simp only [requestSignals, Fin.isValue, ↓reduceIte] at hd
      have hf := dyadicFloor_le_scale_div hfloor.le (Nat.log2 M + 1) j
      have hm := FourthRootHierarchyParams.NormalizedRow.threshold_margin HP
      linarith [HP.η_lt_η₂, HP.η_pos]
    have hz (τ : Environment P 3) : B.binPreparation bin r (fun _ => G) τ x y = 0 := by
      change B.auxiliary bin (G x y / r.terminal.rate) * _ = 0
      rw [haux, polynomialPrepCutoff4_eq_zero HP.θ_pos hd', zero_mul]
    simp only [requestSignals, Fin.isValue, one_ne_zero, ↓reduceIte]
    split_ifs
    · simp only [rowSliceMean, hz, expect_const_zero, mul_zero]
    · exact mul_zero _
  · exact hε
  · exact hεfinal
  · exact herr
  · exact herrfinal

/-- Integrated truth comparison for the actual successful prefix/preparation history.
The masks, rank and canonical joint mean are literal request data. Polynomial preparation
proves the light-entry annihilation needed by false-overflow payment. Error envelopes
still require payment from the lower-budget invariant; this is a conditional analytic kernel. -/
theorem exists_compressedBin_integrated (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {cap ζ scale : ℝ} (hcap : 0 ≤ cap) (hζ : 0 < ζ) (hs : 0 < scale)
    (hmargin : scale ≤ HP.η) (hcapscale : scale ≤ max cap 16 / 10000)
    (hsmall : ζ ≤ scale / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ floor : ℝ, 0 < floor → floor ≤ scale → floor ≤ 1 →
      ∃ Cpre : ℝ, 0 ≤ Cpre ∧ ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P)
      (b : ℕ → ℝ), (∀ i, 0 < b i) → (∀ i, b i = 16 * b (i + 1)) →
      ∀ (M bin k : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
      Admissible r → r.terminal.rate = rate k →
      B.cutoff bin = boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap bin
        (fun _ => 1) → B.auxiliary bin = polynomialPrepCutoff4 HP.θ →
      ∀ (G : Matrix (ZMod P) (ZMod P) ℝ), (∀ x y, 0 ≤ G x y) →
      ∀ F, B.initialPrefixes M r = some F → ∀ W,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.complete M r (B.binPreparation bin r (F (j + 1)))
          (dyadicSlack (Nat.log2 M + 1) j)) = some W →
      ∀ A, B.compressedBin M bin k ζ floor r = some A →
      ∀ N u : ℝ, 0 ≤ N * u →
      let m := Nat.log2 M + 1
      let n := compatibleCapacity HP.K m
      let X := fun σ x => r.source.retains (channels B.padding) σ x
      let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
      let Δ := firstSignalIncrement F k
        (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ)
      let raw : Environment P 3 → ZMod P → ZMod P → Fin 2 → ℝ := 0
      let truth := requestSignals ζ B.padding id r (fun _ => G)
        (B.binPreparation bin r (fun _ => G))
      ∀ (ε : ℕ → Environment P 3 → ZMod P → ℝ) (εfinal : Environment P 3 → ZMod P → ℝ),
        (∀ i < m, ∀ σ x, X σ x → 0 ≤ ε i σ x) →
        (∀ σ x, X σ x → 0 ≤ εfinal σ x) →
        (∀ i < m, ∀ σ x y, X σ x → Y σ y →
          clippedError (truth σ x y 0) (truth σ x y 1)
            (uncompressedRow (Δ σ x) (raw σ x) (i + 1) y) ≤ ε i σ x) →
        (∀ σ x y, X σ x → Y σ y →
          clippedError (truth σ x y 0) (truth σ x y 1)
            (uncompressedRow (Δ σ x) (raw σ x) m y) ≤ εfinal σ x) →
        let S := fun σ => ({y | Y σ y} : Finset (ZMod P))
        let Pre := fun σ x => ∑ i ∈ range m, dyadicFloor floor m i * ε i σ x
        let No := fun σ x => if ∀ i < m,
          stepThreshold (S σ) n (fun _ => HP.K) (dyadicFloor floor m) (Δ σ x) ⟨0, raw σ x⟩ i ≤
            dyadicFloor floor m i then εfinal σ x else 0
        let Tail := fun σ x => ∑ j ∈ range m,
          if IsFirstOverflow (S σ) n (fun _ => HP.K) (dyadicFloor floor m) (Δ σ x) ⟨0, raw σ x⟩ j ∧
            heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor floor m j) (n j) σ then
              ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i σ x else 0
        rootDistPow 4 N u X Y A
          (denseChild B.padding id r (B.cutoff bin) (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K G) ≤
          128 * (HP.K : ℝ) * (Cpre ^ 4 * vertexNormPow 4 N u X Pre +
            C ^ 4 * vertexNormPow 4 N u X No + C ^ 4 * vertexNormPow 4 N u X Tail) +
          ∑ j ∈ range m, (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 / ((n j : ℝ) *
            dyadicFloor floor m j ^ 4)) *
            rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
              (uncompressedRow (Δ σ x) (raw σ x) (j + 1) y)) := by
  obtain ⟨C, hC, hscales⟩ := exists_decodePrefixes_integrated HP hcap hζ hs hmargin
    hcapscale hsmall
  refine ⟨C, hC, ?_⟩
  intro floor hf hfs hf1
  obtain ⟨Cp, hCp, hbound⟩ := hscales floor hf hfs hf1
  refine ⟨Cp, hCp, ?_⟩
  intro P _ B b hb hstep M bin k r hr hrate hcut haux G hG F hF W hW A hA N u hNu
  unfold compressedBin at hA
  split at hA
  · contradiction
  · simp only [hF, bind, Option.bind_some, hW, pure] at hA
    have he := Option.some.inj hA
    subst A
    exact hbound B b hb hstep M bin k r hr hrate hcut haux G hG F W N u hNu

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData

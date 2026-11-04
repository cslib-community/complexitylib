/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyInitialSecondNoise

/-!
# Concrete four-max inputs to the executed compressed-bin decoder

Successful actual histories and preparation walks supply the four literal row maxima.
The integrated decoder no longer asks its caller for clipped-error envelopes. The RHS
retains weighted preloss, final and heavy-tail moments and raw postincrement false-event
charges. These original finite assembly bounds do not prove a requested global budget or
parent induction.

## Main results

* `exists_compressedBin_fourMax`: successful actual output with concrete four-max inputs.
* `initialFourMax_moment`: both centered noises paid, deterministic mean norms explicit.
* `initialFourMaxReserve_le`: explicit finite numerical charge for all sharp reserve terms.
* `initialFourMax_preloss`: finite Minkowski stationary payment without a group-count loss.
* `initialFourMax_tail`: deterministic heavy-tail norm plus unconditional noise payment.
* `initialSignals_falseBudget`: raw j+1 false-event moments with both noises paid.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.RowCompression Cslib.Probability
open NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false

/-- Literal sharp reserve of the shared decoder: stationary preloss, no-overflow final,
heavy first-overflow tail and raw false-overflow charges. No smallness is asserted. -/
@[expose] def initialFourMaxReserve {P : ℕ} [Fact P.Prime]
    {HP : FourthRootHierarchyParams 16 1 16 32 8} (B : BudgetData HP P)
    (M bin k : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ku : ℕ) (ss st : List (ZMod P))
    (G : Matrix (ZMod P) (ZMod P) ℝ)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (cap C Cpre : ℝ) : ℝ :=
  let m := Nat.log2 M + 1
  let n := compatibleCapacity HP.K m
  let X := fun σ x => r.source.retains (channels B.padding) σ x
  let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
  let Δ := firstSignalIncrement F k
    (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ)
  let raw : Environment P 3 → ZMod P → ZMod P → Fin 2 → ℝ := 0
  let truth := requestSignals ζ B.padding id r (fun _ => G)
    (B.binPreparation bin r (fun _ => G))
  let ε := actualFourMax HP R.source R.terminal (side P ks) (side P k) (side P ku)
    B.padding ss st k G ζ Δ raw
  let εfinal := ε (Nat.log2 M)
  let S := fun σ => ({y | Y σ y} : Finset (ZMod P))
  let Pre := fun σ x => ∑ i ∈ range m, dyadicFloor floor m i * ε i σ x
  let No := fun σ x => if ∀ i < m,
      stepThreshold (S σ) n (fun _ => HP.K) (dyadicFloor floor m) (Δ σ x) ⟨0, raw σ x⟩ i ≤
        dyadicFloor floor m i then εfinal σ x else 0
  let Tail := fun σ x => ∑ j ∈ range m,
      if IsFirstOverflow (S σ) n (fun _ => HP.K) (dyadicFloor floor m) (Δ σ x) ⟨0, raw σ x⟩ j ∧
        heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor floor m j) (n j) σ then
          ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i σ x else 0
  128 * (HP.K : ℝ) * (Cpre ^ 4 * vertexNormPow 4 P r.source.rate X Pre +
    C ^ 4 * vertexNormPow 4 P r.source.rate X No +
    C ^ 4 * vertexNormPow 4 P r.source.rate X Tail) +
  ∑ j ∈ range m, (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 / ((n j : ℝ) *
    dyadicFloor floor m j ^ 4)) *
    rowNormPow 4 P r.source.rate X Y (fun σ x y =>
      clippedError (truth σ x y 0) (truth σ x y 1)
      (uncompressedRow (Δ σ x) (raw σ x) (j + 1) y))

/-- Numerical sufficient charge for the literal sharp initial reserve. This keeps
floor, capacity and prefix-weight costs explicit, with no stochastic hypotheses. -/
@[expose] def initialNumericalReserve (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (M : ℕ) (floor cap C Cpre : ℝ) (a : ℕ → ℝ) : ℝ :=
  let m := Nat.log2 M + 1
  let n := compatibleCapacity HP.K m
  128 * (HP.K : ℝ) *
    (Cpre ^ 4 * (∑ i ∈ range m, dyadicFloor floor m i * a i) ^ 4 +
      C ^ 4 * a (Nat.log2 M) ^ 4 +
      C ^ 4 * (∑ j ∈ range m, ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * a i) ^ 4) +
    ∑ j ∈ range m,
      (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
        ((n j : ℝ) * dyadicFloor floor m j ^ 4)) * a j ^ 4

/-- A finite numerical allocation for the sharp reserve. This conservative payment
keeps every stationary, final, heavy-selected and raw false-event coefficient. Dropping
heavy selection here gains no rarity factor and never discounts correlated noise. -/
theorem initialFourMaxReserve_le {P : ℕ} [Fact P.Prime]
    {HP : FourthRootHierarchyParams 16 1 16 32 8} (B : BudgetData HP P)
    (M bin k : ℕ) (ζ floor : ℝ) (hf : 0 ≤ floor)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 0 ≤ r.source.rate)
    (R : RoleProfile 3) (ks ku : ℕ) (ss st : List (ZMod P))
    (G : Matrix (ZMod P) (ZMod P) ℝ)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (cap C Cpre : ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hb : ∀ j < Nat.log2 M + 1,
      vertexNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (actualFourMax HP R.source R.terminal (side P ks) (side P k) (side P ku)
          B.padding ss st k G ζ
          (firstSignalIncrement F k
            (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ)) 0 j) ≤ a j ^ 4)
    (hraw : ∀ j < Nat.log2 M + 1,
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun σ x y =>
          let truth := requestSignals ζ B.padding id r (fun _ => G)
            (B.binPreparation bin r (fun _ => G)) σ x y
          clippedError (truth 0) (truth 1)
            (uncompressedRow ((firstSignalIncrement F k
              (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ)) σ x)
              0 (j + 1) y)) ≤ a j ^ 4) :
    B.initialFourMaxReserve M bin k ζ floor r R ks ku ss st G F W cap C Cpre ≤
      initialNumericalReserve HP M floor cap C Cpre a := by
  unfold initialFourMaxReserve initialNumericalReserve
  extract_lets m n X Y Δ raw truth ε εfinal S Pre No Tail
  change ∀ j < m, vertexNormPow 4 P r.source.rate X (ε j) ≤ a j ^ 4 at hb
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := mul_nonneg (Nat.cast_nonneg _) hr
  have hrestrict (Θ : Environment P 3 → ZMod P → Prop)
      (f : Environment P 3 → ZMod P → ℝ) :
      vertexNormPow 4 P r.source.rate X (fun σ x => if Θ σ x then f σ x else 0) ≤
        vertexNormPow 4 P r.source.rate X f := by
    unfold vertexNormPow
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNu)
    apply expect_le_expect
    intro σ _
    apply sum_le_sum
    intro x _
    dsimp only
    split_ifs
    · exact le_rfl
    · simp only [abs_zero, zero_pow (by decide : 4 ≠ 0)]
      positivity
  have hpre : vertexNormPow 4 P r.source.rate X Pre ≤
      (∑ i ∈ range m, dyadicFloor floor m i * a i) ^ 4 :=
    vertexNormPow_sum_le_pow_sum (by decide : 4 ≠ 0) hNu (range m) ε
      (dyadicFloor floor m) a (fun i _ => dyadicFloor_nonneg hf m i)
      (fun i _ => ha i) (fun i hi => hb i (mem_range.mp hi))
  have hno : vertexNormPow 4 P r.source.rate X No ≤ a (Nat.log2 M) ^ 4 := by
    dsimp only [No]
    convert (hrestrict (fun σ x => ∀ i < m,
      stepThreshold (S σ) n (fun _ => HP.K) (dyadicFloor floor m) (Δ σ x)
        ⟨0, raw σ x⟩ i ≤ dyadicFloor floor m i) εfinal).trans
      (hb (Nat.log2 M) (by omega)) using 1
    congr 1
    funext σ x
    split_ifs <;> rfl
  let tail := fun j σ x => if IsFirstOverflow (S σ) n (fun _ => HP.K)
      (dyadicFloor floor m) (Δ σ x) ⟨0, raw σ x⟩ j ∧
      heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor floor m j) (n j) σ then
        ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i σ x else 0
  let budget := fun j => ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * a i
  have ht (j : ℕ) : vertexNormPow 4 P r.source.rate X (tail j) ≤ budget j ^ 4 := by
    dsimp only [tail, budget]
    refine le_trans (b := vertexNormPow 4 P r.source.rate X
      (fun σ x => ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i σ x)) ?_ ?_
    · convert (hrestrict (fun σ x => IsFirstOverflow (S σ) n (fun _ => HP.K)
      (dyadicFloor floor m) (Δ σ x) ⟨0, raw σ x⟩ j ∧
      heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor floor m j) (n j) σ)
      (fun σ x => ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i σ x)) using 1
      congr 1
      funext σ x
      split_ifs <;> rfl
    · exact vertexNormPow_sum_le_pow_sum (by decide : 4 ≠ 0) hNu (Ico j m) ε
        (fun i => (28 : ℝ) ^ (m - i)) a (fun i _ => by positivity)
        (fun i _ => ha i) (fun i hi => hb i (mem_Ico.mp hi).2)
  have htail : vertexNormPow 4 P r.source.rate X Tail ≤
      (∑ j ∈ range m, ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * a i) ^ 4 := by
    have h := vertexNormPow_sum_le_pow_sum (by decide : 4 ≠ 0) hNu (range m) tail
      (fun _ => 1) budget (fun _ _ => by norm_num)
      (fun j _ => sum_nonneg fun i _ => mul_nonneg (by positivity) (ha i)) (fun j _ => ht j)
    simpa only [one_mul, Tail, tail, budget] using h
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hpre (by positivity))
      (mul_le_mul_of_nonneg_left hno (by positivity)))
      (mul_le_mul_of_nonneg_left htail (by positivity))
  · apply sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hraw j (mem_range.mp hj)) (by positivity)

/-- Shared decoding against the genuine dense bin using literal four-max statistics.
Actual preparation executions retain their usage noise and full-terminal first rank.
The remaining moments on the RHS are allocation obligations, not assumed budgets. -/
theorem exists_decodePrefixes_fourMax (HP : FourthRootHierarchyParams 16 1 16 32 8)
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
      ∀ (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) W,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.complete M r (B.binPreparation bin r (F (j + 1)))
          (dyadicSlack (Nat.log2 M + 1) j)) = some W →
      ∀ (R : RoleProfile 3) (ks ku : ℕ) (ss st : List (ZMod P)),
      r.source = gridChannel R.source ks ss →
      r.terminal = gridChannel R.terminal k st →
      r.usage = gridChannel R.terminal ku st →
      let m := Nat.log2 M + 1
      let n := compatibleCapacity HP.K m
      let X := fun σ x => r.source.retains (channels B.padding) σ x
      let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
      let Δ := firstSignalIncrement F k
        (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ)
      let raw : Environment P 3 → ZMod P → ZMod P → Fin 2 → ℝ := 0
      let truth := requestSignals ζ B.padding id r (fun _ => G)
        (B.binPreparation bin r (fun _ => G))
      let ε := actualFourMax HP R.source R.terminal (side P ks) (side P k) (side P ku)
        B.padding ss st k G ζ Δ raw
      let εfinal := ε (Nat.log2 M)
        let S := fun σ => ({y | Y σ y} : Finset (ZMod P))
        let Pre := fun σ x => ∑ i ∈ range m, dyadicFloor floor m i * ε i σ x
        let No := fun σ x => if ∀ i < m,
          stepThreshold (S σ) n (fun _ => HP.K) (dyadicFloor floor m) (Δ σ x) ⟨0, raw σ x⟩ i ≤
            dyadicFloor floor m i then εfinal σ x else 0
        let Tail := fun σ x => ∑ j ∈ range m,
          if IsFirstOverflow (S σ) n (fun _ => HP.K) (dyadicFloor floor m) (Δ σ x) ⟨0, raw σ x⟩ j ∧
            heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor floor m j) (n j) σ then
              ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i σ x else 0
        rootDistPow 4 P r.source.rate X Y (B.decodePrefixes M bin k ζ floor r F W)
          (denseChild B.padding id r (B.cutoff bin) (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K G) ≤
          128 * (HP.K : ℝ) * (Cpre ^ 4 * vertexNormPow 4 P r.source.rate X Pre +
            C ^ 4 * vertexNormPow 4 P r.source.rate X No +
            C ^ 4 * vertexNormPow 4 P r.source.rate X Tail) +
          ∑ j ∈ range m, (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 / ((n j : ℝ) *
            dyadicFloor floor m j ^ 4)) *
            rowNormPow 4 P r.source.rate X Y (fun σ x y =>
              clippedError (truth σ x y 0) (truth σ x y 1)
              (uncompressedRow (Δ σ x) (raw σ x) (j + 1) y)) := by
  obtain ⟨C, hC, hscales⟩ := exists_decodePrefixes_integrated HP hcap hζ hs hmargin hcapscale hsmall
  refine ⟨C, hC, ?_⟩
  intro floor hf hfs hf1
  obtain ⟨Cp, hCp, hbound⟩ := hscales floor hf hfs hf1
  refine ⟨Cp, hCp, ?_⟩
  intro P _ B b hb hstep M bin k r hr hrate hcut haux G hG F W hW R ks ku ss st
    hsource hterminal husage
  dsimp only
  let Δ := firstSignalIncrement F k
    (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ)
  let ε := actualFourMax HP R.source R.terminal (side P ks) (side P k) (side P ku)
    B.padding ss st k G ζ Δ 0
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hsource]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have he (i : ℕ) (σ : Environment P 3) (x : ZMod P) : 0 ≤ ε i σ x :=
    actualFourMax_nonneg HP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have htgt := B.requestSignals_eq_genuineTarget bin k ku r R ks ss st hsource hterminal
    husage haux G ζ
  have herr (i : ℕ) (hi : i < Nat.log2 M + 1) (σ : Environment P 3) (x y : ZMod P)
      (_hx : r.source.retains (channels B.padding) σ x)
      (hy : r.terminal.retains (channels B.padding) σ y) :
      clippedError
        (requestSignals ζ B.padding id r (fun _ => G)
          (B.binPreparation bin r (fun _ => G)) σ x y 0)
        (requestSignals ζ B.padding id r (fun _ => G)
          (B.binPreparation bin r (fun _ => G)) σ x y 1)
        (uncompressedRow (Δ σ x) 0 (i + 1) y) ≤ ε i σ x := by
    rw [htgt]
    have hy' : retainedMask R.terminal (side P k) B.padding st σ y := by
      simpa only [hterminal, gridChannel, CorrectionRowTask.Channel.retains, channels,
        semanticSide_grid, retainedMask] using hy
    exact actual_clipped_le_fourMax HP R.source R.terminal (side P ks) (side P k)
      (side P ku) B.padding ss st k G hG ζ Δ 0 i
      (B.preparationPrefix_zero_off M bin k ku r R ks ss st hsource husage F W hW ζ i hi)
      σ x y hy'
  exact hbound B b hb hstep M bin k r hr hrate hcut haux G hG F W
    P r.source.rate hNu ε (ε (Nat.log2 M))
    (fun i _ σ x _ => he i σ x) (fun σ x _ => he _ σ x) herr
    (fun σ x y hx hy => herr (Nat.log2 M) (by omega) σ x y hx hy)

/-- Actual successful compressed output against the genuine dense bin, using the four
executed row maxima. There is no supplied final accuracy or replacement signal family.
The remaining moments on the RHS are allocation obligations, not assumed budgets. -/
theorem exists_compressedBin_fourMax (HP : FourthRootHierarchyParams 16 1 16 32 8)
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
      ∀ (R : RoleProfile 3) (ks ku : ℕ) (ss st : List (ZMod P)),
      r.source = gridChannel R.source ks ss →
      r.terminal = gridChannel R.terminal k st →
      r.usage = gridChannel R.terminal ku st →
      let m := Nat.log2 M + 1
      let n := compatibleCapacity HP.K m
      let X := fun σ x => r.source.retains (channels B.padding) σ x
      let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
      let Δ := firstSignalIncrement F k
        (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ)
      let raw : Environment P 3 → ZMod P → ZMod P → Fin 2 → ℝ := 0
      let truth := requestSignals ζ B.padding id r (fun _ => G)
        (B.binPreparation bin r (fun _ => G))
      let ε := actualFourMax HP R.source R.terminal (side P ks) (side P k) (side P ku)
        B.padding ss st k G ζ Δ raw
      let εfinal := ε (Nat.log2 M)
        let S := fun σ => ({y | Y σ y} : Finset (ZMod P))
        let Pre := fun σ x => ∑ i ∈ range m, dyadicFloor floor m i * ε i σ x
        let No := fun σ x => if ∀ i < m,
          stepThreshold (S σ) n (fun _ => HP.K) (dyadicFloor floor m) (Δ σ x) ⟨0, raw σ x⟩ i ≤
            dyadicFloor floor m i then εfinal σ x else 0
        let Tail := fun σ x => ∑ j ∈ range m,
          if IsFirstOverflow (S σ) n (fun _ => HP.K) (dyadicFloor floor m) (Δ σ x) ⟨0, raw σ x⟩ j ∧
            heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor floor m j) (n j) σ then
              ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i σ x else 0
        rootDistPow 4 P r.source.rate X Y A
          (denseChild B.padding id r (B.cutoff bin) (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K G) ≤
          128 * (HP.K : ℝ) * (Cpre ^ 4 * vertexNormPow 4 P r.source.rate X Pre +
            C ^ 4 * vertexNormPow 4 P r.source.rate X No +
            C ^ 4 * vertexNormPow 4 P r.source.rate X Tail) +
          ∑ j ∈ range m, (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 / ((n j : ℝ) *
            dyadicFloor floor m j ^ 4)) *
            rowNormPow 4 P r.source.rate X Y (fun σ x y =>
              clippedError (truth σ x y 0) (truth σ x y 1)
              (uncompressedRow (Δ σ x) (raw σ x) (j + 1) y)) := by
  obtain ⟨C, hC, hscales⟩ := exists_decodePrefixes_fourMax HP hcap hζ hs hmargin hcapscale hsmall
  refine ⟨C, hC, ?_⟩
  intro floor hf hfs hf1
  obtain ⟨Cp, hCp, hbound⟩ := hscales floor hf hfs hf1
  refine ⟨Cp, hCp, ?_⟩
  intro P _ B b hb hstep M bin k r hr hrate hcut haux G hG F hF W hW A hA R ks ku ss st
    hsource hterminal husage
  unfold compressedBin at hA
  split at hA
  · contradiction
  · simp only [hF, bind, Option.bind_some, hW, pure] at hA
    have he := Option.some.inj hA
    subst A
    exact hbound B b hb hstep M bin k r hr hrate hcut haux G hG F W hW R ks ku ss st
      hsource hterminal husage

variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- The actual first and second completion payments combined by finite Minkowski.
Only the two literal deterministic mean norms remain unpaid; precision and rank-rate
costs are explicit, and the noise has no heavy-event rarity factor. -/
theorem initialFourMax_moment (B : BudgetData HP P) (M bin ka : ℕ) (hM : 0 < M)
    (hbins : B.bins.Nonempty) (haux : ∀ d, B.auxiliary bin d ∈ Set.Icc 0 1)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ku : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st)
    (hu : r.usage = gridChannel R.terminal ku st)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hF : B.initialPrefixes M r = some F)
    (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (hW : (List.range (Nat.log2 M + 1)).mapM (fun i =>
      B.complete M r (B.binPreparation bin r (F (i + 1)))
        (dyadicSlack (Nat.log2 M + 1) i)) = some W)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) (ζ : ℝ)
    (j : ℕ) (hj : j < Nat.log2 M + 1) :
    let X := retainedMask R.source (side P ks) B.padding ss
    let Δ := firstSignalIncrement F ka
      (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
    let a := fun ν => vertexNormPow 4 P r.source.rate X
      (actualMeanMax HP R.source R.terminal (side P ks) (side P ka) (side P ku)
        B.padding ss st ka G ζ Δ 0 ν j) ^ (4⁻¹ : ℝ)
    let e₀ := (2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) *
      (64 / 63) / rate ka
    let e₁ := |ζ| * (2 : ℝ) ^ (-B.requestPrecision M r)
    vertexNormPow 4 P r.source.rate X
      (actualFourMax HP R.source R.terminal (side P ks) (side P ka) (side P ku)
        B.padding ss st ka G ζ Δ 0 j) ≤
      ((a 0 + a 1) + (e₀ + e₁) *
        (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 := by
  extract_lets X Δ a e₀ e₁
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  let z := fun ν : Fin 2 => (if ν = 0 then e₀ else e₁) *
    (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j
  have hra := rate_pos ka
  have hz (ν : Fin 2) : 0 ≤ z ν := by
    dsimp only [z]; split_ifs <;> dsimp only [e₀, e₁] <;> positivity
  have hb (ν : Fin 2) : vertexNormPow 4 P r.source.rate X
      (actualNoiseMax R.source R.terminal (side P ks) (side P ka) (side P ku)
        B.padding ss st ka G Δ 0 ν j) ≤ (z ν) ^ 4 := by
    apply actualNoiseMax_budget _ _ _ _ _ _ _ _ _ G hG Δ 0 hNu ν j
    fin_cases ν
    · exact B.initial_actualNoiseEntry M hM hbins r R.source R.terminal R.source_terminal
        ks ka ss st hs ht F hF G hG (side P ku)
        (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ) j hj
    · exact B.initialSecondSignal_noise_moment M bin haux r R ks ku ss st hs hu
        F W hW ka G ζ j hj
  have hm (ν : Fin 2) : vertexNormPow 4 P r.source.rate X
      (actualMeanMax HP R.source R.terminal (side P ks) (side P ka) (side P ku)
        B.padding ss st ka G ζ Δ 0 ν j) ≤ (a ν) ^ 4 := by
    rw [show (a ν) ^ 4 = _ from
      Real.rpow_inv_natCast_pow (vertexNormPow_nonneg hNu _) (by decide : 4 ≠ 0)]
  have h := actualFourMax_budget HP R.source R.terminal (side P ks) (side P ka)
    (side P ku) B.padding ss st ka G ζ Δ 0 j hNu a z
    (fun ν => Real.rpow_nonneg (vertexNormPow_nonneg hNu _) _) hz hm hb
  dsimp only [z] at h
  simp only [Fin.isValue, one_ne_zero, ↓reduceIte] at h
  convert h using 1; ring

/-- The scheduled stationary payment of all four maxima. Finite Minkowski keeps
correlated prefixes together without a group-count loss. Deterministic mean norms stay
explicit, while both noises pay the existing geometric stationary schedule. -/
theorem initialFourMax_preloss (B : BudgetData HP P) (M bin ka : ℕ) (hM : 0 < M)
    (hbins : B.bins.Nonempty) (haux : ∀ d, B.auxiliary bin d ∈ Set.Icc 0 1)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ku : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st)
    (hu : r.usage = gridChannel R.terminal ku st)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hF : B.initialPrefixes M r = some F)
    (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (hW : (List.range (Nat.log2 M + 1)).mapM (fun i =>
      B.complete M r (B.binPreparation bin r (F (i + 1)))
        (dyadicSlack (Nat.log2 M + 1) i)) = some W)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) (ζ : ℝ)
    {floor : ℝ} (hf : 0 < floor) :
    let m := Nat.log2 M + 1
    let X := retainedMask R.source (side P ks) B.padding ss
    let Δ := firstSignalIncrement F ka
      (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
    let a := fun i ν => vertexNormPow 4 P r.source.rate X
      (actualMeanMax HP R.source R.terminal (side P ks) (side P ka) (side P ku)
        B.padding ss st ka G ζ Δ 0 ν i) ^ (4⁻¹ : ℝ)
    let e₀ := (2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) *
      (64 / 63) / rate ka
    let e₁ := |ζ| * (2 : ℝ) ^ (-B.requestPrecision M r)
    vertexNormPow 4 P r.source.rate X (fun σ x =>
      ∑ i ∈ range m, dyadicFloor floor m i *
        actualFourMax HP R.source R.terminal (side P ks) (side P ka) (side P ku)
          B.padding ss st ka G ζ Δ 0 i σ x) ≤
      ((∑ i ∈ range m, dyadicFloor floor m i * (a i 0 + a i 1)) +
        floor * (e₀ + e₁) / 511) ^ 4 := by
  extract_lets m X Δ a e₀ e₁
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have hra := rate_pos ka
  have he : 0 ≤ e₀ + e₁ := by dsimp only [e₀, e₁]; positivity
  let c := fun i => (a i 0 + a i 1) + (e₀ + e₁) * (1 / 64 : ℝ) ^ dyadicSlack m i
  have hc (i : ℕ) : 0 ≤ c i := by
    dsimp only [c, a]
    exact add_nonneg (add_nonneg (Real.rpow_nonneg (vertexNormPow_nonneg hNu _) _)
      (Real.rpow_nonneg (vertexNormPow_nonneg hNu _) _)) (by positivity)
  have hp := vertexNormPow_sum_le_pow_sum (X := X) (by decide : 4 ≠ 0) hNu
    (range m)
    (actualFourMax HP R.source R.terminal (side P ks) (side P ka) (side P ku)
      B.padding ss st ka G ζ Δ 0)
    (dyadicFloor floor m) c (fun i _ => dyadicFloor_nonneg hf.le m i)
    (fun i _ => hc i)
    (fun i hi => B.initialFourMax_moment M bin ka hM hbins haux r R ks ku ss st
      hs ht hu F hF W hW G hG ζ i (mem_range.mp hi))
  apply hp.trans
  apply pow_le_pow_left₀ (sum_nonneg fun i _ =>
    mul_nonneg (dyadicFloor_nonneg hf.le m i) (hc i)) _ 4
  simp only [c, mul_add, sum_add_distrib]
  rw [← mul_add floor e₀ e₁]
  apply add_le_add le_rfl
  refine (sum_le_sum fun i _ => ?_).trans (pre_schedule_sum hf.le he m)
  apply mul_le_mul_of_nonneg_left _ (dyadicFloor_nonneg hf.le m i)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 64 : ℝ) ≤ 2) _) he

/-- Raw postincrement false-event charges paid by Holder and the existing two-noise
payment. Only the actual deterministic mean moments remain in the charge sum. -/
theorem initialSignals_falseBudget (B : BudgetData HP P) (M bin ka : ℕ) (hM : 0 < M)
    (hbins : B.bins.Nonempty) (haux : ∀ d, B.auxiliary bin d ∈ Set.Icc 0 1)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ku : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st)
    (hu : r.usage = gridChannel R.terminal ku st)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hF : B.initialPrefixes M r = some F)
    (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (hW : (List.range (Nat.log2 M + 1)).mapM (fun i =>
      B.complete M r (B.binPreparation bin r (F (i + 1)))
        (dyadicSlack (Nat.log2 M + 1) i)) = some W)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) (ζ : ℝ)
    (husage : side P ku ≤ side P ka) {floor : ℝ} (hf : 0 < floor) (radius : ℝ) :
    let m := Nat.log2 M + 1
    let X := retainedMask R.source (side P ks) B.padding ss
    let Y := fun ν : Fin 2 => retainedMask R.terminal
      (if ν = 0 then side P ka else side P ku) B.padding st
    let Δ := firstSignalIncrement F ka
      (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
    let a := fun j ν => rowNormPow 4 P r.source.rate X (Y ν)
      (fun _ x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
        (side P ku) B.padding ss st ka G ζ Δ 0 ν j x y)
    let w := fun j => 64 * (HP.K : ℝ) * radius ^ 4 /
      ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor floor m j ^ 4)
    let e₀ := (2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) *
      (64 / 63) / rate ka
    let e₁ := |ζ| * (2 : ℝ) ^ (-B.requestPrecision M r)
    let c := 64 * (HP.K : ℝ) * radius ^ 4 / floor ^ 4
    ∑ j ∈ range m, w j * rowNormPow 4 P r.source.rate X (Y 0)
      (fun σ x y => clippedError (G x y / rate ka)
        (genuineTarget HP R.source R.terminal (side P ks) (side P ku)
          B.padding ss st ka G ζ σ x y 1) (actualPrefix Δ 0 j σ x y)) ≤
      64 * ((∑ j ∈ range m, w j * (a j 0 + a j 1)) +
        (c * e₀ ^ 4 / 63 + c * e₁ ^ 4 / 63)) := by
  extract_lets m X Y Δ a w e₀ e₁ c
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  let z := fun j ν => rowNormPow 4 P r.source.rate X (Y ν)
    (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
      B.padding ss st ka G Δ 0 ν j)
  have hb (j : ℕ) (hj : j ∈ range m) := raw_prefix_four_moments HP R.source R.terminal
    (side P ks) (side P ka) (side P ku) B.padding ss st ka G hG ζ Δ 0 j
    (B.preparationPrefix_zero_off M bin ka ku r R ks ss st hs hu F W hW ζ j (mem_range.mp hj))
    (fun σ y hy => mem_retentionBox.mpr (fun v =>
      (mem_retentionBox.mp hy v).trans_le husage)) hNu
  have hraw : (∑ j ∈ range m, w j * rowNormPow 4 P r.source.rate X (Y 0)
      (fun σ x y => clippedError (G x y / rate ka)
        (genuineTarget HP R.source R.terminal (side P ks) (side P ku)
          B.padding ss st ka G ζ σ x y 1) (actualPrefix Δ 0 j σ x y))) ≤
      64 * ((∑ j ∈ range m, w j * (a j 0 + a j 1)) +
        ∑ j ∈ range m, w j * (z j 0 + z j 1)) := by
    calc
      _ ≤ ∑ j ∈ range m, w j * (64 * ((a j 0 + a j 1) + (z j 0 + z j 1))) :=
        sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hb j hj) (by dsimp only [w]; positivity)
      _ = _ := by
        rw [← sum_add_distrib, mul_sum]
        apply sum_congr rfl
        intro j _
        ring
  apply hraw.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 64)
  apply add_le_add le_rfl
  exact B.initialSignals_falseNoise M bin haux r R ks ku ss st hs hu F W hW
    hM hbins ka ht hF G hG ζ hf radius

/-- Actual heavy-selected four-max tail with both noises paid unconditionally.
Only the deterministic mean tail norm remains. Rarity may subsequently reduce that
mean norm; it never discounts either centered noise term. -/
theorem initialFourMax_tail (B : BudgetData HP P) (M bin ka : ℕ) (hM : 0 < M)
    (hbins : B.bins.Nonempty) (haux : ∀ d, B.auxiliary bin d ∈ Set.Icc 0 1)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ku : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st)
    (hu : r.usage = gridChannel R.terminal ku st)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hF : B.initialPrefixes M r = some F)
    (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (hW : (List.range (Nat.log2 M + 1)).mapM (fun i =>
      B.complete M r (B.binPreparation bin r (F (i + 1)))
        (dyadicSlack (Nat.log2 M + 1) i)) = some W)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) (ζ : ℝ)
    (floor : ℝ) :
    let m := Nat.log2 M + 1
    let Δ := firstSignalIncrement F ka
      (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
    let raw : Environment P 3 → ZMod P → ZMod P → Fin 2 → ℝ := 0
    let N : ℝ := P
    let u := r.source.rate
    let e₀ := (2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) *
      (64 / 63) / rate ka
    let e₁ := |ζ| * (2 : ℝ) ^ (-B.requestPrecision M r)
    let X := retainedMask R.source (side P ks) B.padding ss
    let Mean := fun σ x => ∑ j ∈ range m,
      if meanFirstEvent R.terminal B.padding st ka m j floor G
          (compatibleCapacity HP.K m) (fun _ => HP.K) Δ raw σ x then
        meanRowTail R.terminal (side P ka) B.padding st m j
          (actualClippedMean HP R.source R.terminal (side P ks) (side P ka) (side P ku)
            B.padding ss st ka G ζ Δ raw 0) σ x +
        meanRowTail R.terminal (side P ku) B.padding st m j
          (actualClippedMean HP R.source R.terminal (side P ks) (side P ka) (side P ku)
            B.padding ss st ka G ζ Δ raw 1) σ x
      else 0
    vertexNormPow 4 N u X (fun σ x => ∑ j ∈ range m,
      if meanFirstEvent R.terminal B.padding st ka m j floor G
          (compatibleCapacity HP.K m) (fun _ => HP.K) Δ raw σ x then
        ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) *
          actualFourMax HP R.source R.terminal (side P ks) (side P ka) (side P ku)
            B.padding ss st ka G ζ Δ raw i σ x
      else 0) ≤
      (vertexNormPow 4 N u X Mean ^ (4⁻¹ : ℝ) + (e₀ + e₁) * (7 / 9)) ^ 4 := by
  extract_lets m Δ raw N u e₀ e₁ X Mean
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  let e := fun ν : Fin 2 => if ν = 0 then e₀ else e₁
  have hra := rate_pos ka
  have he (ν : Fin 2) : 0 ≤ e ν := by
    dsimp only [e]; split_ifs <;> dsimp only [e₀, e₁] <;> positivity
  have hz (ν : Fin 2) (i : ℕ) (hi : i < m) :
      vertexNormPow 4 P r.source.rate X
        (actualNoiseMax R.source R.terminal (side P ks) (side P ka) (side P ku)
          B.padding ss st ka G Δ 0 ν i) ≤
        (e ν * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4 := by
    apply actualNoiseMax_budget _ _ _ _ _ _ _ _ _ G hG Δ 0 hNu ν i
    fin_cases ν
    · exact B.initial_actualNoiseEntry M hM hbins r R.source R.terminal R.source_terminal
        ks ka ss st hs ht F hF G hG (side P ku)
        (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ) i hi
    · exact B.initialSecondSignal_noise_moment M bin haux r R ks ku ss st hs hu
        F W hW ka G ζ i hi
  exact fourMax_tail_budget HP R.source R.terminal (side P ks) (side P ku) B.padding ss st
    ka m floor G ζ (compatibleCapacity HP.K m) (fun _ => HP.K) Δ 0 hNu e he hz

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyInitialSecondNoise
import Complexity.Foundations.Probability.RootMetric.WeightedError

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
* `initialFourMaxReserve_le_tail`: actual reserve with four separate numerical payments.
* `initialFirstTransportPayment_exists_charge`: one charge for all first-mean transport.
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
floor, capacity and prefix-weight costs explicit. Mutually exclusive first overflows
pay a sum of fourth moments, without a cube in the number of possible overflows. -/
@[expose] def initialNumericalReserve (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (M : ℕ) (floor cap C Cpre : ℝ) (a : ℕ → ℝ) : ℝ :=
  let m := Nat.log2 M + 1
  let n := compatibleCapacity HP.K m
  128 * (HP.K : ℝ) *
    (Cpre ^ 4 * (∑ i ∈ range m, dyadicFloor floor m i * a i) ^ 4 +
      C ^ 4 * a (Nat.log2 M) ^ 4 +
      C ^ 4 * ∑ j ∈ range m, (∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * a i) ^ 4) +
    ∑ j ∈ range m,
      (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
        ((n j : ℝ) * dyadicFloor floor m j ^ 4)) * a j ^ 4

/-- The final statistic is an unavoidable summand of this numerical envelope.
This does not give a lower bound on the actual sharp reserve or actual output error. -/
theorem initialNumericalReserve_ge_final (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (M : ℕ) (floor cap C Cpre : ℝ) (a : ℕ → ℝ) :
    128 * (HP.K : ℝ) * C ^ 4 * a (Nat.log2 M) ^ 4 ≤
      initialNumericalReserve HP M floor cap C Cpre a := by
  unfold initialNumericalReserve
  dsimp only
  calc
    _ = 128 * (HP.K : ℝ) * (C ^ 4 * a (Nat.log2 M) ^ 4) := by ring
    _ ≤ 128 * (HP.K : ℝ) *
        (Cpre ^ 4 * (∑ i ∈ range (Nat.log2 M + 1),
          dyadicFloor floor (Nat.log2 M + 1) i * a i) ^ 4 +
          C ^ 4 * a (Nat.log2 M) ^ 4 +
          C ^ 4 * ∑ j ∈ range (Nat.log2 M + 1),
            (∑ i ∈ Ico j (Nat.log2 M + 1),
              (28 : ℝ) ^ (Nat.log2 M + 1 - i) * a i) ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (le_add_of_nonneg_left (by positivity)).trans (le_add_of_nonneg_right
        (by positivity))
    _ ≤ _ := le_add_of_nonneg_right (by positivity)

/-- Numerical reserve with separate stationary, final, heavy-tail and aggregate raw
payments. Callers keep deterministic transport, semantic deficit and centered noise
separate inside these payments; only deterministic tails may receive rarity. -/
@[expose] def initialSeparatedReserve (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (C Cpre preBudget finalBudget tailBudget rawBudget : ℝ) : ℝ :=
  128 * (HP.K : ℝ) *
    (Cpre ^ 4 * preBudget ^ 4 + C ^ 4 * finalBudget ^ 4 + C ^ 4 * tailBudget ^ 4) + rawBudget

/-- Monotonicity of the four literal nonnegative reserve payments. Decoder constants
need no sign hypotheses because they enter only through fourth powers. -/
theorem initialSeparatedReserve_mono (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (C Cpre : ℝ) {p f t r p' f' t' r' : ℝ}
    (hp : 0 ≤ p) (hf : 0 ≤ f) (ht : 0 ≤ t)
    (hpp : p ≤ p') (hff : f ≤ f') (htt : t ≤ t') (hrr : r ≤ r') :
    initialSeparatedReserve HP C Cpre p f t r ≤
      initialSeparatedReserve HP C Cpre p' f' t' r' := by
  unfold initialSeparatedReserve
  exact add_le_add (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hpp 4) (by positivity))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hf hff 4) (by positivity)))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht htt 4) (by positivity)))
    (by positivity)) hrr

/-- The four first-mean transport components after exact endpoint summation. This
excludes semantic deficits, the second mean and centered noise. `x` is the scalar
endpoint factor, including structural decay and parent precision. -/
@[expose] def initialFirstTransportPayment (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (floor cap C Cpre x : ℝ) : ℝ :=
  initialSeparatedReserve HP C Cpre
    ((8 : ℝ) ^ (4⁻¹ : ℝ) * x * floor / 511)
    ((8 : ℝ) ^ (4⁻¹ : ℝ) * x)
    ((8 : ℝ) ^ (4⁻¹ : ℝ) * x * (2 + 256 / floor) ^ (4⁻¹ : ℝ) / 63)
    (64 * 8 * x ^ 4 *
      (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
        ((HP.K + 1) * floor ^ 4)) / 63)

/-- The common first-mean scalar is monotone for nonnegative inputs. -/
theorem initialFirstTransportPayment_mono
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (floor cap C Cpre : ℝ) (hf : 0 ≤ floor) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    initialFirstTransportPayment HP floor cap C Cpre x ≤
      initialFirstTransportPayment HP floor cap C Cpre y := by
  unfold initialFirstTransportPayment
  apply initialSeparatedReserve_mono HP C Cpre
  all_goals first | positivity | gcongr

/-- One structural charge pays all four deterministic first-mean transport components.
The charge is chosen after the fixed decoder/floor/cap constants and endpoint factor,
but before any precision, budget, request exponents, width or field. This does not pay
semantic deficits or either noise. -/
theorem initialFirstTransportPayment_exists_charge
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (floor cap C Cpre L : ℝ) :
    ∃ A : ℕ, ∀ t : ℝ,
      initialFirstTransportPayment HP floor cap C Cpre
        (L * ((2 : ℝ) ^ (-(A : ℝ))) * t) ≤ t ^ 4 := by
  let F := initialFirstTransportPayment HP floor cap C Cpre
  have hhom (x y : ℝ) : F (x * y) = F x * y ^ 4 := by
    dsimp only [F, initialFirstTransportPayment, initialSeparatedReserve]
    ring
  obtain ⟨A, hA⟩ := exists_nat_gt (F L)
  have hpow : (A : ℝ) ≤ (2 : ℝ) ^ A := by
    exact_mod_cast (Nat.lt_two_pow_self (n := A)).le
  have hlarge : F L ≤ ((2 : ℝ) ^ A) ^ 4 :=
    hA.le.trans (hpow.trans (le_self_pow₀ (one_le_pow₀ (by norm_num)) (by decide : 4 ≠ 0)))
  refine ⟨A, fun t => ?_⟩
  change F (L * ((2 : ℝ) ^ (-(A : ℝ))) * t) ≤ t ^ 4
  rw [mul_assoc, hhom, mul_pow, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_natCast]
  have hp : (0 : ℝ) < 2 ^ A := by positivity
  have hh := mul_le_mul_of_nonneg_right hlarge (by positivity : 0 ≤ ((2 : ℝ) ^ A)⁻¹ ^ 4)
  rw [← mul_pow, mul_inv_cancel₀ hp.ne', one_pow] at hh
  calc
    F L * ((((2 : ℝ) ^ A)⁻¹) ^ 4 * t ^ 4) =
      (F L * (((2 : ℝ) ^ A)⁻¹) ^ 4) * t ^ 4 := by ring
    _ ≤ 1 * t ^ 4 := mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := one_mul _

/-- Assemble the literal reserve with a separately paid actual tail. Stationary and
raw terms retain their coefficients, including the postincrement raw prefix. -/
theorem initialFourMaxReserve_le_tail {P : ℕ} [Fact P.Prime]
    {HP : FourthRootHierarchyParams 16 1 16 32 8} (B : BudgetData HP P)
    (M bin k : ℕ) (ζ floor : ℝ) (hf : 0 ≤ floor)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 0 ≤ r.source.rate)
    (R : RoleProfile 3) (ks ku : ℕ) (ss st : List (ZMod P))
    (G : Matrix (ZMod P) (ZMod P) ℝ)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (cap C Cpre : ℝ) (a : ℕ → ℝ) (preBudget finalBudget tailBudget rawBudget : ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (hprealloc : (∑ i ∈ range (Nat.log2 M + 1),
      dyadicFloor floor (Nat.log2 M + 1) i * a i) ≤ preBudget)
    (hfinalalloc : a (Nat.log2 M) ≤ finalBudget)
    (hb : ∀ j < Nat.log2 M + 1,
      vertexNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (actualFourMax HP R.source R.terminal (side P ks) (side P k) (side P ku)
          B.padding ss st k G ζ
          (firstSignalIncrement F k
            (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ)) 0 j) ≤ a j ^ 4)
    (hraw : (∑ j ∈ range (Nat.log2 M + 1),
      (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
        ((compatibleCapacity HP.K (Nat.log2 M + 1) j : ℝ) *
          dyadicFloor floor (Nat.log2 M + 1) j ^ 4)) * rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun σ x y =>
          let truth := requestSignals ζ B.padding id r (fun _ => G)
            (B.binPreparation bin r (fun _ => G)) σ x y
          clippedError (truth 0) (truth 1)
            (uncompressedRow ((firstSignalIncrement F k
              (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ)) σ x)
              0 (j + 1) y))) ≤ rawBudget)
    (htail : vertexNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ x => ∑ j ∈ range (Nat.log2 M + 1),
        if IsFirstOverflow {y | r.terminal.retains (channels B.padding) σ y}
            (compatibleCapacity HP.K (Nat.log2 M + 1)) (fun _ => HP.K)
            (dyadicFloor floor (Nat.log2 M + 1))
            ((firstSignalIncrement F k
              (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ)) σ x)
            ⟨0, 0⟩ j ∧
          heavyCountEvent (fun σ y => r.terminal.retains (channels B.padding) σ y) univ
            (fun y => (requestSignals ζ B.padding id r (fun _ => G)
              (B.binPreparation bin r (fun _ => G))) σ x y 0)
            (dyadicFloor floor (Nat.log2 M + 1) j)
            (compatibleCapacity HP.K (Nat.log2 M + 1) j) σ then
          ∑ i ∈ Ico j (Nat.log2 M + 1), (28 : ℝ) ^ (Nat.log2 M + 1 - i) *
            actualFourMax HP R.source R.terminal (side P ks) (side P k) (side P ku)
              B.padding ss st k G ζ
              (firstSignalIncrement F k
                (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ)) 0 i σ x
        else 0) ≤ tailBudget ^ 4) :
    B.initialFourMaxReserve M bin k ζ floor r R ks ku ss st G F W cap C Cpre ≤
      initialSeparatedReserve HP C Cpre preBudget finalBudget tailBudget rawBudget := by
  unfold initialFourMaxReserve initialSeparatedReserve
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
  change vertexNormPow 4 P r.source.rate X Tail ≤ tailBudget ^ 4 at htail
  have hpre' := hpre.trans (pow_le_pow_left₀
    (sum_nonneg fun i _ => mul_nonneg (dyadicFloor_nonneg hf m i) (ha i)) hprealloc 4)
  have hno' := hno.trans (pow_le_pow_left₀ (ha _) hfinalalloc 4)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hpre' (by positivity))
      (mul_le_mul_of_nonneg_left hno' (by positivity)))
      (mul_le_mul_of_nonneg_left htail (by positivity))
  · exact hraw

/-- A finite numerical allocation for the sharp reserve. This conservative payment
keeps every stationary, final, heavy-selected and raw false-event coefficient. Dropping
heavy selection here gains no rarity factor and never discounts correlated noise.
First-overflow disjointness removes the outer Minkowski cardinality loss. -/
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
      ∑ j ∈ range m, (∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * a i) ^ 4 := by
    have he := vertexNormPow_sum_ite (range m) 4 (by decide : 4 ≠ 0)
      (P : ℝ) r.source.rate X
      (fun j σ x => IsFirstOverflow (S σ) n (fun _ => HP.K)
        (dyadicFloor floor m) (Δ σ x) ⟨0, raw σ x⟩ j ∧
        heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor floor m j) (n j) σ)
      (fun σ x i j hi hj => hi.1.unique hj.1)
      (fun j σ x => ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i σ x)
    change vertexNormPow 4 P r.source.rate X Tail =
      ∑ j ∈ range m, vertexNormPow 4 P r.source.rate X (tail j) at he
    rw [he]
    exact sum_le_sum (fun j _ => ht j)
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

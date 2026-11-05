/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyTerminalMean
public import Complexity.Foundations.Probability.HierarchyResidualDomination
public import Complexity.Foundations.Probability.RootMetric.ClippedMean
import Complexity.Foundations.Probability.GridRowMoment.Rate

/-!
# Clipped product means against the genuine signed residual

The canonical product mean is bounded by `C + E C`, then by the actual
`C + E C - E` residual using the ramp gap. The resulting clipped comparison
consumes the literal successful left/reset-right calls and scalar own-request
root moments. Importance and midpoint density are unchanged. No accuracy of
the parent or independence of the child tables is assumed.

The coefficient is linear in the physical product scale divided by the parent
rate; the ordinary comparison's fourth power is absent. This is a component
mean payment, not an allocation of the complete precision schedule or a bound
on centered sampling noise. Recursive availability remains a separate premise.
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

/-- The actual positive product is dominated before subtracting the once-negative
correction. Polynomial bins supply entrywise domination, including zero entries.
No finite coverage assumption or approximate canonical support is needed. -/
theorem residualProductMean_canonical_le_residual
    (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
    (hD : B.padding ≠ 0) (H : Horizon P)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (hks : ks ≤ H.maxExponent) (hka : ka ≤ ks)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, B.base x y ≤ rate ka)
    (i : ℕ) (hib : i ∈ B.bins) (hiH : i ≤ H.maxExponent) (x y : ZMod P) :
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)
    B.residualProductMean i r (B.residualCanonicalChild i Q.left)
      (B.residualCanonicalChild i Q.right) x y ≤
    max 1 (((HP.k : ℝ) + 1) / HP.θ) *
      HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
        (canonicalChannel id (rate ka)) (rate ka) B.base x y := by
  dsimp only
  let E := HP.toHierarchyParams.correctionIter (canonicalChannel id (rate ka))
    (canonicalChannel id (rate ka)) (rate ka) B.base HP.k
  let bin := fun j x y => B.binRate j * B.cutoff j (B.base x y / B.binRate j)
  have hb0 (j : ℕ) (x y : ZMod P) : 0 ≤ bin j x y :=
    mul_nonneg (by rw [hrate]; exact (rate_pos j).le) (B.cutoff_bounds j _).1
  have hbin (x y : ZMod P) : bin i x y ≤ B.base x y := by
    have hsum := B.initialBins_polynomial_sum n hbins hrate hcutoff hC hC1 x y
    exact (single_le_sum (fun j _ => hb0 j x y) hib).trans (hsum.trans_le
      (mul_le_of_le_one_right (hC x y) (polynomialSwitch4_le_one _ _ _)))
  let roles : RoleProfile 3 :=
    ⟨s, midpointRole s t, t, (midpointRole_distinct s t).1, hst,
      (midpointRole_distinct s t).2⟩
  have hm : midpoint r = gridChannel roles.midpoint ka [] := by
    simp only [midpoint, hs, ht, gridChannel, roles]
  have hp (v : ℝ) (hv : B.cutoff i v ≠ 0) : B.auxiliary i v = 1 := by
    rw [hcutoff] at hv
    rw [haux]
    exact HP.routedBin_prep_eq_one (by norm_num)
      (fun w hw => polynomialSwitch4_of_le (by norm_num) hw) rate_pos rate_antitone
      i (fun _ => 1) hv
  have hK : 2 * (1 + 32 / HP.η) ≤ HP.K := by
    have hk1 : (1 : ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
    have hdiv := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk1 (by norm_num : (0 : ℝ) ≤ 32)) HP.η_pos.le
    have hg := HP.gate
    norm_num only [mul_one] at hdiv
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 32) HP.η_pos.le]
  have hmean := canonical_rawPositiveSample_mean HP B.padding id hD Function.injective_id
    H roles 0 i ks ka ka i hks hka hiH ss [] st B.base hC hC1 hCf
    (B.cutoff i) (B.auxiliary i) HP.ρ HP.K hp HP.ρ_nonneg HP.ρ_le_one
    HP.η_pos HP.ρ_one hK x y
  have hpositive : rowSliceMean
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun σ x y => HierarchyTask.rawPositiveSample (channels B.padding) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
        (fun q => B.residualCanonicalChild i q σ) x y) x y =
      bin i x y + ∑ z, E x z * bin i z y := by
    simpa only [rowSliceMean, residualCanonicalChild, hs, ht, hm, hrate, roles, id_eq,
      bin, E] using hmean
  have hprod : B.residualProductMean i r
      (B.residualCanonicalChild i (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left)
      (B.residualCanonicalChild i (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right) x y ≤
      bin i x y + ∑ z, E x z * bin i z y := by
    rw [← hpositive]
    apply expect_le_expect
    intro σ _
    change _ ≤ _ + _
    apply le_add_of_nonneg_left
    apply mul_nonneg
    · exact mul_nonneg (by rw [hrate]; exact (rate_pos i).le)
        (by unfold HierarchyTask.usageRatio; positivity)
    · exact (canonicalRequestChild_mem_Icc HP B.padding id B.base (B.cutoff i)
        (B.auxiliary i) HP.ρ HP.K B.binCap_nonneg (B.cutoff_bounds i)
        (fun v => ⟨HP.ρ_nonneg v, HP.ρ_le_one v⟩) _ σ x y).1
  have he (z : ZMod P) : 0 ≤ E x z :=
    (HP.toHierarchyParams.isCorrectionSeq_correctionIter (rate_pos ka) hC).nonneg HP.k x z
  exact hprod.trans ((add_le_add (hbin x y) (sum_le_sum fun z _ =>
    mul_le_mul_of_nonneg_left (hbin z y) (he z))).trans
      (HP.toHierarchyParams.correctionInput_last_le_residual _ _ (rate_pos ka) hC hC1 hCf x y))

/-- Actual clipped conditional product mean from the scalar left/right root IH.
The target is the true signed residual, with no target-agreement premise. The
once-negative term is outside this component comparison. This preserves the
actual positive bin budget and separately reset right request. -/
theorem residualProduct_parent_clipped_le
    (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
    (hD : B.padding ≠ 0) (H : Horizon P)
    (M i k ks ka : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hi : B.binRate i = rate i)
    (hks : ks ≤ H.maxExponent) (hka : ka ≤ ks)
    (hib : i ∈ B.bins) (hiH : i ≤ H.maxExponent)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, B.base x y ≤ rate ka)
    (hlight : ∀ d, d ≤ HP.θ → B.cutoff i d = 0)
    (L R : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hL : let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).left
      B.evaluate (B.binBudget M i r) q = some (.row L))
    (hR : let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).right
      B.compressedBin (B.binBudget M i r) i k ζ floor q = some R)
    (εL εR : ℝ)
    (hEL : let Q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i))
      rootDistPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ z => (midpoint r).retains (channels B.padding) σ z)
        L (B.residualCanonicalChild i Q.left) ≤ εL ^ 4)
    (hER : let Q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i))
      rootDistPow 4 P r.terminal.rate
        (fun σ z => (midpoint r).retains (channels B.padding) σ z)
        (fun σ y => Q.right.usage.retains (channels B.padding) σ y)
        R (B.residualCanonicalChild i Q.right) ≤ εR ^ 4) :
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)
    let A := B.residualProductMean i r L R
    let C := B.residualProductMean i r
      (B.residualCanonicalChild i Q.left) (B.residualCanonicalChild i Q.right)
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    let K := max 1 (((HP.k : ℝ) + 1) / HP.θ)
    rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun _ x y => min 1 (|A x y - C x y| / (rate ka + G x y))) ≤
    (512 * (3 * K + 3) ^ 3 / rate ka) *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((2 * B.binCap) * HP.K * εL ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * εR ^ 4)) := by
  dsimp only
  let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
    r.terminal (B.binRate i)
  let C := B.residualCanonicalChild i
  let A := B.residualProductMean i r L R
  let T := B.residualProductMean i r (C Q.left) (C Q.right)
  let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
    (canonicalChannel id (rate ka)) (rate ka) B.base
  let K := max 1 (((HP.k : ℝ) + 1) / HP.θ)
  have hK : 0 ≤ K := le_trans (by norm_num) (le_max_left _ _)
  have hspos : 0 < r.source.rate := by rw [hs]; exact rate_pos ks
  have htpos : 0 < r.terminal.rate := by rw [ht]; exact rate_pos ka
  have hf : 0 < rate ka := rate_pos ka
  have hb : 0 ≤ B.binRate i := by rw [hi]; exact (rate_pos i).le
  have hπ : 0 < gridMass P ka := gridMass_pos ka
  have hπu : 0 < gridMass P (max ka i) := gridMass_pos _
  have hcap : 0 ≤ B.binCap := B.binCap_nonneg
  have hQ : 0 ≤ HP.Q HP.toHierarchyParams.atomCap := HP.Q_nonneg _
  have hleft := B.evaluate_normalized_bounds (B.binBudget M i r) false
    ⟨HP.k - 1, Nat.sub_lt HP.k_pos (by decide)⟩ Q.left
    (by simp only [Q, HierarchyTask.rawRequests,
      HierarchyTask.correctionAtomTask_last HP.k_pos, Bool.false_eq_true, ↓reduceIte]) L hL
  have hright := B.compressedBin_range_usage (B.binBudget M i r) i k ζ floor Q.right R hR
  have hn (U V : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
      (hU : ∀ σ x z, 0 ≤ U σ x z) (hV : ∀ σ z y, 0 ≤ V σ z y) (x y : ZMod P) :
      0 ≤ B.residualProductMean i r U V x y := by
    apply expect_nonneg
    intro σ _
    exact mul_nonneg (mul_nonneg (mul_nonneg (by rw [hi]; exact (rate_pos i).le)
      (by unfold HierarchyTask.usageRatio; positivity))
      (div_nonneg htpos.le (by positivity)))
      (sum_nonneg fun z _ => mul_nonneg (hU σ x z) (hV σ z y))
  have hcanon (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      (σ : Environment P 3) (x y : ZMod P) : 0 ≤ C q σ x y :=
    (canonicalRequestChild_mem_Icc HP B.padding id B.base (B.cutoff i)
      (B.auxiliary i) HP.ρ HP.K B.binCap_nonneg (B.cutoff_bounds i)
      (fun v => ⟨HP.ρ_nonneg v, HP.ρ_le_one v⟩) q σ x y).1
  have hA := hn L R (fun σ x z => (hleft.1 σ x z).1)
    (fun σ z y => (hright.1 σ z y).1)
  have hT := hn (C Q.left) (C Q.right) (hcanon Q.left) (hcanon Q.right)
  have hdom (x y : ZMod P) : T x y ≤ K * G x y :=
    B.residualProductMean_canonical_le_residual n hbins hrate hcutoff haux hD H r
      r.source.role r.terminal.role hst ks ka r.source.suffix r.terminal.suffix
      (by change r.source = {r.source with rate := rate ks}; rw [← hs])
      (by change r.terminal = {r.terminal with rate := rate ka}; rw [← ht])
      hks hka hC hC1 hCf i hib hiH x y
  have hconvert : rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun _ x y => min 1 (|A x y - T x y| / (rate ka + G x y))) ≤
      (512 * (3 * K + 3) ^ 3 / rate ka) * rootDistPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun _ => A) (fun _ => T) := by
    apply rowNormPow_le_mul (mul_nonneg (Nat.cast_nonneg _) hspos.le)
    intro σ x y _ _
    have hG : 0 ≤ G x y := HP.toHierarchyParams.residual_nonneg (rate_pos ka) hC x y
    have hc := mul_min_pow_le_homogeneousLoss (s := 4) (by decide) hK hG
      (rate_pos ka) (hT x y) (hdom x y) (hA x y)
    have hr := homogeneousLoss_le_rpow_inv_sub_pow (s := 4) (by decide) (hT x y) (hA x y)
    norm_num only [Nat.reduceSub, Nat.cast_ofNat] at hc hr
    rw [abs_of_nonneg (show 0 ≤ min 1 (|A x y - T x y| / (rate ka + G x y)) by positivity)]
    rw [abs_sub_comm] at hc
    have hh := hc.trans (mul_le_mul_of_nonneg_left hr (by positivity))
    have hh' : rate ka * min 1 (|A x y - T x y| / (rate ka + G x y)) ^ 4 ≤
        (512 * (3 * K + 3) ^ 3) * |A x y ^ (4⁻¹ : ℝ) - T x y ^ (4⁻¹ : ℝ)| ^ 4 := by
      change rate ka * min 1 (|A x y - T x y| / (rate ka + G x y)) ^ 4 ≤
        2 * (3 * K + 3) ^ 3 * (256 *
          |T x y ^ (1 / 4 : ℝ) - A x y ^ (1 / 4 : ℝ)| ^ 4) at hh
      rw [abs_sub_comm (T x y ^ (1 / 4 : ℝ)) (A x y ^ (1 / 4 : ℝ))] at hh
      norm_num only [show (4⁻¹ : ℝ) = 1 / 4 by norm_num]
      convert hh using 1; ring
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hf).mpr
    linarith only [hh']
  apply hconvert.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (B.residualProduct_parent_root_le M i k ks ka ζ floor r hst hs ht hi hlight
    L R hL hR).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add
    (mul_le_mul_of_nonneg_left hEL (by positivity))
    (mul_le_mul_of_nonneg_left hER (by positivity))

/-- Signed two-budget product means pay the two nonnegative comparisons separately.
Both endpoints retain their actual bin budgets; no root is taken of the signed pair.
This is the product component of a paired stream, not the direct or once-negative payment. -/
theorem residualProduct_parent_clipped_pair_le
    (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
    (hD : B.padding ≠ 0) (H : Horizon P)
    (M : Fin 2 → ℕ) (i k ks ka : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hi : B.binRate i = rate i)
    (hks : ks ≤ H.maxExponent) (hka : ka ≤ ks)
    (hib : i ∈ B.bins) (hiH : i ≤ H.maxExponent)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, B.base x y ≤ rate ka)
    (hlight : ∀ d, d ≤ HP.θ → B.cutoff i d = 0)
    (L R : Fin 2 → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hL : ∀ j, let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).left
      B.evaluate (B.binBudget (M j) i r) q = some (.row (L j)))
    (hR : ∀ j, let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).right
      B.compressedBin (B.binBudget (M j) i r) i k ζ floor q = some (R j))
    (εL εR : Fin 2 → ℝ)
    (hEL : ∀ j, let Q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i))
      rootDistPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ z => (midpoint r).retains (channels B.padding) σ z)
        (L j) (B.residualCanonicalChild i Q.left) ≤ εL j ^ 4)
    (hER : ∀ j, let Q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i))
      rootDistPow 4 P r.terminal.rate
        (fun σ z => (midpoint r).retains (channels B.padding) σ z)
        (fun σ y => Q.right.usage.retains (channels B.padding) σ y)
        (R j) (B.residualCanonicalChild i Q.right) ≤ εR j ^ 4) :
    let A := fun j => B.residualProductMean i r (L j) (R j)
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    let K := max 1 (((HP.k : ℝ) + 1) / HP.θ)
    let pay := fun j => (512 * (3 * K + 3) ^ 3 / rate ka) *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((2 * B.binCap) * HP.K * εL j ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * εR j ^ 4))
    rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun _ x y => min 1 (|A 0 x y - A 1 x y| / (rate ka + G x y))) ≤
      8 * (pay 0 + pay 1) := by
  dsimp only
  let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
    r.terminal (B.binRate i)
  let T := B.residualProductMean i r
    (B.residualCanonicalChild i Q.left) (B.residualCanonicalChild i Q.right)
  let A := fun j => B.residualProductMean i r (L j) (R j)
  let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
    (canonicalChannel id (rate ka)) (rate ka) B.base
  have hh (j : Fin 2) := B.residualProduct_parent_clipped_le n hbins hrate hcutoff haux
    hD H (M j) i k ks ka ζ floor r hst hs ht hi hks hka hib hiH hC hC1 hCf hlight
    (L j) (R j) (hL j) (hR j) (εL j) (εR j) (hEL j) (hER j)
  have htarg (x y : ZMod P) : 0 < rate ka + G x y :=
    add_pos_of_pos_of_nonneg (rate_pos ka)
      (HP.toHierarchyParams.residual_nonneg (rate_pos ka) hC x y)
  have hNu : 0 ≤ (P : ℝ) * r.source.rate :=
    mul_nonneg (Nat.cast_nonneg _) (by rw [hs]; exact (rate_pos ks).le)
  have hp := rowNormPow_clipped_add_le hNu
    (fun σ x => r.source.retains (channels B.padding) σ x)
    (fun σ y => r.terminal.retains (channels B.padding) σ y)
    (fun x y => A 0 x y - T x y) (fun x y => T x y - A 1 x y)
    (fun x y => rate ka + G x y) htarg
  simp only [sub_add_sub_cancel] at hp
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add (hh 0)
  simpa only [abs_sub_comm] using hh 1

/-- In the coarse regime the exact clipped scale has only one power of the
bin/parent rate ratio. Rounded masses are retained until the final inequality.
This coefficient estimate is not a joint precision/rank allocation. -/
theorem residualProduct_coarse_clipped_coefficient_le (H : Horizon P) (ka i : ℕ)
    (ha : ka ≤ H.maxExponent) (hia : i ≤ ka) (K : ℝ) (hK : 0 ≤ K) :
    (512 * (3 * K + 3) ^ 3 / rate ka) *
      ((rate i * (rate ka / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i))) ≤
      512 * (3 * K + 3) ^ 3 * (rate i / rate ka) := by
  rw [max_eq_left hia]
  have hf : 0 < rate ka := rate_pos ka
  have hb : 0 < rate i := rate_pos i
  have hπ : 0 < gridMass P ka := gridMass_pos ka
  have he : (512 * (3 * K + 3) ^ 3 / rate ka) *
      ((rate i * (rate ka / gridMass P ka)) * (gridMass P ka / gridMass P ka)) =
      512 * (3 * K + 3) ^ 3 * (rate i / gridMass P ka) := by field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_left hb.le hf (gridMass_bounds H ha).1) (by positivity)

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData

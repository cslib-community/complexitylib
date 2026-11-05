/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyFixedCharge
import Complexity.Foundations.Probability.GridRowMoment.Rate

/-!
# Active canonical bins in the signed product consumer

Strictly coarse bins have zero genuine dense-right tables, from the actual
polynomial cutoff and base cap. The coupled comparison therefore charges only
the reset-right error there. Approximate tables retain all their actual errors
and may be correlated on the unchanged environment.

`finiteInput_residual_clipped_active_le` executes the actual finite signed input
and retains the coarse/ordinary product minimum with this active coefficient.
It does not allocate the whole RHS with one fixed charge: the unchanged direct
endpoint coefficient has no fine-bin decay. The final identities quantify that
remaining comparison cost, rather than asserting an actual-error lower bound.
Recursive joint availability, general noise and the full induction remain open.
-/

public section
noncomputable section
open Finset Cslib Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} {HP : FourthRootHierarchyParams 16 1 16 32 8}

variable [Fact P.Prime] (B : BudgetData HP P)

/-- Adjacent grid rates differ by sixteen. -/
theorem rate_succ_sixteen (i : ℕ) : rate i = 16 * rate (i + 1) := by
  simp only [rate, pow_succ]
  ring

omit [Fact P.Prime] in
/-- The polynomial bin cutoff vanishes below half its matrix-unit scale. -/
theorem residual_cutoff_zero_of_le_half
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1)) (hrate : B.binRate = rate) (i : ℕ) (v : ℝ) (hv : v ≤ rate i / 2) :
    B.cutoff i (v / B.binRate i) = 0 := by
  rw [hcutoff, hrate]
  apply boundedRoutedBinCutoff_eq_zero (by norm_num)
    (fun t ht => polynomialSwitch4_of_le (by norm_num) ht) rate_pos rate_antitone
  apply (div_le_iff₀ (rate_pos i)).mpr
  linarith

/-- Strictly coarse canonical dense-right entries are exactly zero. This concerns
only the genuine table, and places no support constraint on approximate children. -/
theorem residualCanonicalRight_zero_of_lt
    (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (i ka : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hCf : ∀ x y, B.base x y ≤ rate ka) (hia : i < ka)
    (σ : Environment P 3) (z y : ZMod P) :
    B.residualCanonicalChild i
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i)).right σ z y = 0 := by
  let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
    r.terminal (B.binRate i)).right
  have hz : B.cutoff i (B.base z y / q.terminal.rate) = 0 := by
    apply B.residual_cutoff_zero_of_le_half hcutoff hrate
    have hh : rate ka ≤ rate (i + 1) := rate_antitone hia
    have hp := rate_pos (i + 1)
    have he := rate_succ_sixteen i
    linarith [hCf z y]
  change normalizedRequest B.padding id q (B.cutoff i) HP.ρ HP.K
    (fun _ => B.base) (densePreparation B.padding id q (B.auxiliary i) HP.ρ HP.K B.base)
    σ z y = 0
  by_cases ha : Admissible q
  · rw [normalizedRequest_formula B.padding id q ha]
    split_ifs <;> simp [hz]
  · simp [normalizedRequest, ha]

/-- Coupled comparison with the genuine right cap zero on strictly coarse bins. -/
theorem residualProduct_active_compressed_mean_root_le
    (M i k ka : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (hCf : ∀ x y, B.base x y ≤ rate ka)
    (hs : 0 < r.source.rate) (ht : 0 < r.terminal.rate) (hi : 0 ≤ B.binRate i)
    (hlight : ∀ d, d ≤ HP.θ → B.cutoff i d = 0)
    (L R : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hL : let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).left
      B.evaluate (B.binBudget M i r) q = some (.row L))
    (hR : let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).right
      B.compressedBin (B.binBudget M i r) i k ζ floor q = some R) :
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)
    let C := B.residualCanonicalChild i
    let Xs := fun σ x => r.source.retains (channels B.padding) σ x
    let Zs := fun σ z => (midpoint r).retains (channels B.padding) σ z
    let Yu := fun σ y => Q.right.usage.retains (channels B.padding) σ y
    let prod := fun A D σ x y => ∑ z : ZMod P, A σ x z * D σ z y
    rootDistPow 4 P r.source.rate Xs Yu
      (fun _ x y => conditionalTableMean Xs Yu (prod L R) x y)
      (fun _ x y => conditionalTableMean Xs Yu (prod (C Q.left) (C Q.right)) x y) ≤
      33554432 * ((if ka ≤ i then 2 * B.binCap else 0) * HP.K *
        rootDistPow 4 P r.source.rate Xs Zs L (C Q.left) +
        (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
          (r.terminal.rate / r.source.rate) *
            rootDistPow 4 P r.terminal.rate Zs Yu R (C Q.right)) := by
  have hcap0 := B.binCap_nonneg
  dsimp only
  let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
    r.terminal (B.binRate i)
  let C := B.residualCanonicalChild i
  let Xs := fun σ x => r.source.retains (channels B.padding) σ x
  let Zs := fun σ z => (midpoint r).retains (channels B.padding) σ z
  let Yu := fun σ y => Q.right.usage.retains (channels B.padding) σ y
  have hleft := B.evaluate_normalized_bounds (B.binBudget M i r) false
    ⟨HP.k - 1, Nat.sub_lt HP.k_pos (by decide)⟩ Q.left
    (by simp only [Q, HierarchyTask.rawRequests,
      HierarchyTask.correctionAtomTask_last HP.k_pos, Bool.false_eq_true, ↓reduceIte]) L hL
  have hright := B.compressedBin_range_usage (B.binBudget M i r) i k ζ floor Q.right R hR
  have heL : (fun σ x y => ∑ z : ZMod P, L σ x z * R σ z y) =
      (fun σ x y => ∑ z ∈ ({z | Zs σ z} : Finset _), L σ x z * R σ z y) := by
    funext σ x y
    rw [sum_filter]
    apply sum_congr rfl
    intro z _
    split_ifs with hz
    · rfl
    · rw [(hleft.2.1 σ x z hz), zero_mul]
  have heC : (fun σ x y => ∑ z : ZMod P, C Q.left σ x z * C Q.right σ z y) =
      (fun σ x y => ∑ z ∈ ({z | Zs σ z} : Finset _), C Q.left σ x z * C Q.right σ z y) := by
    funext σ x y
    rw [sum_filter]
    apply sum_congr rfl
    intro z _
    split_ifs with hz
    · rfl
    · have hc := canonicalRequestChild_zero_off_usage HP B.padding id B.base (B.cutoff i)
        (B.auxiliary i) HP.ρ HP.K Q.left σ x z hz
      change C Q.left σ x z = 0 at hc
      rw [hc, zero_mul]
  have htrue (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (σ : Environment P 3)
      (x y : ZMod P) := canonicalRequestChild_mem_Icc HP B.padding id B.base (B.cutoff i)
        (B.auxiliary i) HP.ρ HP.K B.binCap_nonneg (B.cutoff_bounds i)
        (fun v => ⟨HP.ρ_nonneg v, HP.ρ_le_one v⟩) q σ x y
  have hdense (σ : Environment P 3) (z y : ZMod P) :
      C Q.right σ z y ∈ Set.Icc 0 (2 * B.binCap) :=
    normalizedRequest_mem_Icc HP B.padding Q.right (B.cutoff i) B.binCap_nonneg
      (B.cutoff_bounds i) (fun _ => B.base)
      (densePreparation B.padding id Q.right (B.auxiliary i) HP.ρ HP.K B.base) σ z y
  have ha : Admissible Q.left := by
    refine ⟨?_, rfl, rfl⟩
    exact (midpointRole_distinct r.source.role r.terminal.role).1
  have hcol (σ : Environment P 3) (z : ZMod P) (_hz : Zs σ z) :
      #{x ∈ ({x | Xs σ x} : Finset _) | L σ x z ≠ 0} ≤ ⌈4 * (1 + 32 * HP.R)⌉₊ := by
    exact (B.evaluate_normalized_col_support (B.binBudget M i r) false
      ⟨HP.k - 1, Nat.sub_lt HP.k_pos (by decide)⟩ Q.left ha
      (by simp only [Q, HierarchyTask.rawRequests,
        HierarchyTask.correctionAtomTask_last HP.k_pos, Bool.false_eq_true, ↓reduceIte])
      L hL σ z).le
  have hrow (σ : Environment P 3) (z : ZMod P) (_hz : Zs σ z) :
      #{y ∈ ({y | Yu σ y} : Finset _) | C Q.right σ z y ≠ 0} ≤ HP.K :=
    le_trans (card_le_card (fun _ hy => mem_filter.mpr
      ⟨mem_univ _, (mem_filter.mp hy).2⟩))
      (B.residualCanonicalRight_row_support i r ht.le hi hlight σ z)
  have hactive : 0 ≤ (if ka ≤ i then 2 * B.binCap else 0 : ℝ) := by
    split_ifs <;> positivity
  have hbound (σ : Environment P 3) (z y : ZMod P) :
      C Q.right σ z y ≤ (if ka ≤ i then 2 * B.binCap else 0) := by
    split_ifs with hai
    · exact (hdense σ z y).2
    · have hz := B.residualCanonicalRight_zero_of_lt hrate hcutoff i ka r hCf
        (Nat.lt_of_not_ge hai) σ z y
      exact le_of_eq hz
  have hp := rootDistPow_mul_le (s := 4) (N := (P : ℝ)) (u := r.source.rate)
    (f := r.terminal.rate) (X := Xs) (Z := Zs) (Y := Yu)
    (F := C Q.left) (F' := L) (B := C Q.right) (B' := R)
    (CF := 2 * HP.Q HP.toHierarchyParams.atomCap) (CB := if ka ≤ i then 2 * B.binCap else 0)
    (by decide) (by exact_mod_cast (Fact.out : P.Prime).pos) hs ht
    (fun σ x z => (htrue Q.left σ x z).1) (fun σ x z => (hleft.1 σ x z).1)
    (fun σ z y => (hdense σ z y).1) (fun σ z y => (hright.1 σ z y).1)
    (mul_nonneg (by norm_num) (HP.Q_nonneg _)) hactive
    (fun σ x z => (hleft.1 σ x z).2) hbound hrow hcol
  rw [rootDistPow_comm] at hp
  have hm := rootDistPow_conditionalTableMean_mul_le (s := 4) (N := (P : ℝ))
    (u := r.source.rate) (X := Xs) (Y := Yu) (c := 1)
    (H := fun σ x y => ∑ z ∈ ({z | Zs σ z} : Finset _), L σ x z * R σ z y)
    (H' := fun σ x y => ∑ z ∈ ({z | Zs σ z} : Finset _), C Q.left σ x z * C Q.right σ z y)
    (by decide) (by exact_mod_cast (Fact.out : P.Prime).pos) hs (by norm_num)
    (fun σ x y => sum_nonneg fun z _ => mul_nonneg (hleft.1 σ x z).1 (hright.1 σ z y).1)
    (fun σ x y => sum_nonneg fun z _ => mul_nonneg (htrue Q.left σ x z).1 (hdense σ z y).1)
  simp only [one_mul] at hm
  rw [heL, heC]
  apply hm.trans
  have hp' := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2048)
  rw [rootDistPow_comm (C Q.left) L, rootDistPow_comm (C Q.right) R] at hp'
  norm_num only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.cast_ofNat] at hp' ⊢
  convert hp' using 1
  ring

/-- Active canonical support propagated through actual parent density and importance. -/
theorem residualProduct_active_parent_root_le
    (M i k ks ka : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (hCf : ∀ x y, B.base x y ≤ rate ka)
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hi : B.binRate i = rate i)
    (hlight : ∀ d, d ≤ HP.θ → B.cutoff i d = 0)
    (L R : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hL : let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).left
      B.evaluate (B.binBudget M i r) q = some (.row L))
    (hR : let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).right
      B.compressedBin (B.binBudget M i r) i k ζ floor q = some R) :
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)
    let C := B.residualCanonicalChild i
    let Xs := fun σ x => r.source.retains (channels B.padding) σ x
    let Zs := fun σ z => (midpoint r).retains (channels B.padding) σ z
    let Yu := fun σ y => Q.right.usage.retains (channels B.padding) σ y
    rootDistPow 4 P r.source.rate Xs
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun _ => B.residualProductMean i r L R)
      (fun _ => B.residualProductMean i r (C Q.left) (C Q.right)) ≤
    (B.binRate i * (r.terminal.rate / gridMass P ka)) *
      (gridMass P ka / gridMass P (max ka i)) * 33554432 *
      ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * rootDistPow 4 P r.source.rate Xs Zs L (C
      Q.left) +
        (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
          (r.terminal.rate / r.source.rate) *
            rootDistPow 4 P r.terminal.rate Zs Yu R (C Q.right)) := by
  dsimp only
  let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
    r.terminal (B.binRate i)
  let C := B.residualCanonicalChild i
  let prod := fun (A D : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (σ : Environment P 3) (x y : ZMod P) =>
    ∑ z : ZMod P, A σ x z * D σ z y
  have hleft := B.evaluate_normalized_bounds (B.binBudget M i r) false
    ⟨HP.k - 1, Nat.sub_lt HP.k_pos (by decide)⟩ Q.left
    (by simp only [Q, HierarchyTask.rawRequests,
      HierarchyTask.correctionAtomTask_last HP.k_pos, Bool.false_eq_true, ↓reduceIte]) L hL
  have hright := B.compressedBin_range_usage (B.binBudget M i r) i k ζ floor Q.right R hR
  have hoffC (σ : Environment P 3) (z y : ZMod P)
      (hy : ¬ Q.right.usage.retains (channels B.padding) σ y) : C Q.right σ z y = 0 :=
    canonicalRequestChild_zero_off_usage HP B.padding id B.base (B.cutoff i)
      (B.auxiliary i) HP.ρ HP.K Q.right σ z y hy
  have hmean (A D : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
      (hoff : ∀ σ z y, ¬ Q.right.usage.retains (channels B.padding) σ y → D σ z y = 0) :
      B.residualProductMean i r A D =
      (fun x y => (B.binRate i * (r.terminal.rate / gridMass P ka)) *
        conditionalTableMean (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => Q.right.usage.retains (channels B.padding) σ y) (prod A D) x y) := by
    funext x y
    exact B.residualProduct_parent_mean i ka r hst ht hi A D hoff x y
  rw [hmean L R hright.2, hmean (C Q.left) (C Q.right) hoffC]
  have hu : Q.right.usage.rate = rate (max ka i) := by
    dsimp only [Q, HierarchyTask.rawRequests]
    rw [ht, hi, rate_min]
  have hc : 0 ≤ B.binRate i * (r.terminal.rate / gridMass P ka) := by
    rw [hi, ht]
    exact mul_nonneg (rate_pos i).le (div_nonneg (rate_pos ka).le (gridMass_pos (P := P) ka).le)
  rw [channel_rootDist_const_change_terminal B.padding r.source r.terminal Q.right.usage
    hst rfl ks ka (max ka i) hs ht hu P r.source.rate _ hc]
  · have h := B.residualProduct_active_compressed_mean_root_le M i k ka ζ floor r hrate hcutoff hCf
      (by rw [hs]; exact rate_pos ks) (by rw [ht]; exact rate_pos ka)
      (by rw [hi]; exact (rate_pos i).le) hlight L R hL hR
    have hh := mul_le_mul_of_nonneg_left h
      (mul_nonneg hc (div_nonneg (gridMass_pos (P := P) ka).le
        (gridMass_pos (P := P) (max ka i)).le))
    simpa only [mul_assoc, prod, Q, C] using hh
  · intro x y
    exact expect_nonneg fun σ _ => sum_nonneg fun z _ =>
      mul_nonneg (hleft.1 σ x z).1 (hright.1 σ z y).1
  · intro x y
    apply expect_nonneg
    intro σ _
    apply sum_nonneg
    intro z _
    apply mul_nonneg
    all_goals exact (canonicalRequestChild_mem_Icc HP B.padding id B.base (B.cutoff i)
      (B.auxiliary i) HP.ρ HP.K B.binCap_nonneg (B.cutoff_bounds i)
      (fun v => ⟨HP.ρ_nonneg v, HP.ρ_le_one v⟩) _ σ _ _).1

/-- The ordinary cubic conversion retains the active left coefficient. -/
theorem residualProduct_active_parent_ordinary_le
    (M i k ks ka : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (hCf : ∀ x y, B.base x y ≤ rate ka)
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hi : B.binRate i = rate i)
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
    let cap := (B.binRate i * (r.terminal.rate / gridMass P ka)) *
      (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap))
    rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun _ x y => A x y - C x y) ≤
    (4 * cap ^ ((3 : ℝ) / 4)) ^ 4 *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * εL ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * εR ^ 4)) := by
  have hcap0 := B.binCap_nonneg
  dsimp only
  let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
    r.terminal (B.binRate i)
  let C := B.residualCanonicalChild i
  have hp := B.residualProduct_active_parent_root_le M i k ks ka ζ floor r hrate hcutoff hCf hst
      hs ht hi hlight
    L R hL hR
  have hspos : 0 < r.source.rate := by rw [hs]; exact rate_pos ks
  have htpos : 0 < r.terminal.rate := by rw [ht]; exact rate_pos ka
  have hleft := B.evaluate_normalized_bounds (B.binBudget M i r) false
    ⟨HP.k - 1, Nat.sub_lt HP.k_pos (by decide)⟩ Q.left
    (by simp only [Q, HierarchyTask.rawRequests,
      HierarchyTask.correctionAtomTask_last HP.k_pos, Bool.false_eq_true, ↓reduceIte]) L hL
  have hright := B.compressedBin_range_usage (B.binBudget M i r) i k ζ floor Q.right R hR
  have hn (A D : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
      (hA : ∀ σ x z, 0 ≤ A σ x z) (hD : ∀ σ z y, 0 ≤ D σ z y) (x y : ZMod P) :
      0 ≤ B.residualProductMean i r A D x y := by
    apply expect_nonneg
    intro σ _
    have hb : 0 ≤ B.binRate i := by rw [hi]; exact (rate_pos i).le
    exact mul_nonneg (mul_nonneg (mul_nonneg hb (by unfold HierarchyTask.usageRatio; positivity))
      (div_nonneg htpos.le (by positivity)))
      (sum_nonneg fun z _ => mul_nonneg (hA σ x z) (hD σ z y))
  have hcanon (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      (σ : Environment P 3) (x y : ZMod P) : 0 ≤ C q σ x y :=
    (canonicalRequestChild_mem_Icc HP B.padding id B.base (B.cutoff i)
      (B.auxiliary i) HP.ρ HP.K B.binCap_nonneg (B.cutoff_bounds i)
      (fun v => ⟨HP.ρ_nonneg v, HP.ρ_le_one v⟩) q σ x y).1
  have hnorm (A : Matrix (ZMod P) (ZMod P) ℝ) (x y : ZMod P) : A x y ≤ ‖fun x y => A x y‖ :=
    (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm (fun y => A x y) y).trans
          (norm_le_pi_norm (fun x y => A x y) x))
  have hcap := B.residualProductMean_cap M i k ka ζ floor r hst ht hi L R hL hR
  have hconvert := rowNormPow_sub_le_rootDistPow (s := 4)
    (N := (P : ℝ)) (u := r.source.rate)
    (X := fun σ x => r.source.retains (channels B.padding) σ x)
    (Y := fun σ y => r.terminal.retains (channels B.padding) σ y)
    (C := (B.binRate i * (r.terminal.rate / gridMass P ka)) *
      (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap)))
    (H := fun _ => B.residualProductMean i r L R)
    (H' := fun _ => B.residualProductMean i r (C Q.left) (C Q.right))
    (by decide) (mul_nonneg (Nat.cast_nonneg P) hspos.le)
    (fun _ x y _ _ => ⟨hn L R (fun σ x z => (hleft.1 σ x z).1)
      (fun σ z y => (hright.1 σ z y).1) x y, (hnorm _ x y).trans ((le_max_left _ _).trans hcap)⟩)
    (fun _ x y _ _ => ⟨hn _ _ (hcanon Q.left) (hcanon Q.right) x y,
      (hnorm _ x y).trans ((le_max_right _ _).trans hcap)⟩)
  norm_num only [Nat.cast_ofNat, show ((4 : ℝ) - 1) / 4 = 3 / 4 by norm_num] at hconvert
  apply hconvert.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply hp.trans
  apply mul_le_mul_of_nonneg_left
  · exact add_le_add
      (mul_le_mul_of_nonneg_left hEL
        (mul_nonneg (by split_ifs <;> positivity) (Nat.cast_nonneg _)))
      (mul_le_mul_of_nonneg_left hER (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (HP.Q_nonneg _)) (Nat.cast_nonneg _))
        (div_nonneg htpos.le hspos.le)))
  · exact mul_nonneg (mul_nonneg
      (mul_nonneg (by rw [hi]; exact (rate_pos i).le)
        (div_nonneg htpos.le (gridMass_pos (P := P) ka).le))
      (div_nonneg (gridMass_pos (P := P) ka).le
        (gridMass_pos (P := P) (max ka i)).le)) (by norm_num)

/-- Coarse clipped payment with zero left charge on strictly coarse bins. -/
theorem residualProduct_active_parent_clipped_le
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
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * εL ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * εR ^ 4)) := by
  have hcap0 := B.binCap_nonneg
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
  apply (B.residualProduct_active_parent_root_le M i k ks ka ζ floor r hrate hcutoff hCf hst hs ht
      hi hlight
    L R hL hR).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add
    (mul_le_mul_of_nonneg_left hEL (by split_ifs <;> positivity))
    (mul_le_mul_of_nonneg_left hER (by positivity))

/-- Actual signed finite input with active left coefficients in both product payments.
Successful recursive calls and scalar IH remain on their literal own masks and budgets. -/
theorem finiteInput_residual_clipped_active_le
    (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
    (hD : B.padding ≠ 0) (H : Horizon P) (hnH : n ≤ H.maxExponent)
    (M ks ka : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hks : ks ≤ H.maxExponent) (hka : ka ≤ ks)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, B.base x y ≤ rate ka)
    (hcover : ∀ z y, B.base z y = 0 ∨ rate n ≤ B.base z y)
    (hkh : ∀ i ∈ B.bins, ∀ v, B.cutoff i v ≠ 0 → B.auxiliary i v = 1)
    (hlight : ∀ i ∈ B.bins, ∀ d, d ≤ HP.θ → B.cutoff i d = 0)
    (hK : 2 * (1 + 32 / HP.η) ≤ HP.K)
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (child : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (depth : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℝ)
    (ε : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℝ)
    (hrows : ∀ i ∈ B.bins,
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        row history (B.binBudget M i r) q = some (child i q))
    (hnrow : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      row history (B.childBudget M) q = some (child 0 q))
    (hdirect : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      B.compressedBin (B.binBudget M i r) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hleft : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      B.evaluate (B.binBudget M i r) q = some (.row (child i q)))
    (hright : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      B.compressedBin (B.binBudget M i r) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hnegative : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      B.evaluate (B.childBudget M) q = some (.row (child 0 q)))
    (hID : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ε (B.binBudget M i r) q ^ 4)
    (hIL : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ε (B.binBudget M i r) q ^ 4)
    (hIR : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ε (B.binBudget M i r) q ^ 4)
    (hIN : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child 0 q) (B.residualCanonicalChild 0 q) ≤ ε (B.childBudget M) q ^ 4) :
    let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i))
    let neg := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
    let d := fun i => F *
      ((B.binRate i * (gridMass P ka / gridMass P (max ka i))) / rate ka) *
        ε (B.binBudget M i r) (Q i).direct ^ 4
    let pc := fun i => (F / rate ka) *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
    let po := fun i => (1 / rate ka) ^ 4 *
      (4 * ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap))) ^
          ((3 : ℝ) / 4)) ^ 4 *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
    let p := fun i => min (pc i) (po i)
    let ne := F * ε (B.childBudget M) neg ^ 4
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    ∃ executed, B.finiteInput history M .residual r = some executed ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun _ x y => min 1 (|rowSliceMean
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.terminal.retains (channels B.padding) σ y)
          executed x y - G x y| /
            (rate ka + G x y))) ≤
        (ne ^ (4⁻¹ : ℝ) + ∑ i ∈ B.bins, d i ^ (4⁻¹ : ℝ) +
          ∑ i ∈ B.bins, p i ^ (4⁻¹ : ℝ)) ^ 4 := by
  dsimp only
  let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i))
  let neg := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
  let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
  let d := fun i => F *
      ((B.binRate i * (gridMass P ka / gridMass P (max ka i))) / rate ka) *
        ε (B.binBudget M i r) (Q i).direct ^ 4
  let pc := fun i => (F / rate ka) *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
  let po := fun i => (1 / rate ka) ^ 4 *
      (4 * ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap))) ^
          ((3 : ℝ) / 4)) ^ 4 *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
  let p := fun i => min (pc i) (po i)
  let ne := F * ε (B.childBudget M) neg ^ 4
  let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
  let X := fun σ x => r.source.retains (channels B.padding) σ x
  let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
  let de := fun i x y =>
    (B.binRate i * (gridMass P ka / gridMass P (max ka i))) *
      rowSliceMean X Y (fun σ x y =>
        child i (Q i).direct σ x y - B.residualCanonicalChild i (Q i).direct σ x y) x y
  let pe := fun i x y => B.residualProductMean i r (child i (Q i).left)
    (child i (Q i).right) x y - B.residualProductMean i r
      (B.residualCanonicalChild i (Q i).left) (B.residualCanonicalChild i (Q i).right) x y
  let nege := fun x y => -rowSliceMean X Y (fun σ x y =>
    HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
      r.source (midpoint r) r.terminal (B.binRate 0) (fun q => child 0 q σ) x y -
    HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
      r.source (midpoint r) r.terminal (B.binRate 0)
      (fun q => B.residualCanonicalChild 0 q σ) x y) x y
  have hNu : 0 ≤ (P : ℝ) * r.source.rate :=
    mul_nonneg (Nat.cast_nonneg _) (by rw [hs]; exact (rate_pos ks).le)
  have hiH (i : ℕ) (hi : i ∈ B.bins) : i ≤ H.maxExponent := by
    rw [hbins, mem_range] at hi
    omega
  have hde (i : ℕ) (hi : i ∈ B.bins) : rowNormPow 4 P r.source.rate X Y
      (fun _ x y => min 1 (|de i x y| / (rate ka + G x y))) ≤ d i :=
    B.residualDirect_parent_clipped_le n hbins hrate hcutoff hD H M i (depth i (Q i).direct) ks ka
      (ζ i (Q i).direct) (floor i (Q i).direct) r hst hs ht hks hi
      (hiH i hi) hC hC1 hCf (hkh i hi) hK
      (child i (Q i).direct) (hdirect i hi) (ε (B.binBudget M i r) (Q i).direct) (hID i hi)
  have hpe (i : ℕ) (hi : i ∈ B.bins) : rowNormPow 4 P r.source.rate X Y
      (fun _ x y => min 1 (|pe i x y| / (rate ka + G x y))) ≤ p i := by
    apply le_min
    · exact B.residualProduct_active_parent_clipped_le n hbins hrate hcutoff haux hD H M i
        (depth i (Q i).right) ks ka (ζ i (Q i).right) (floor i (Q i).right)
        r hst hs ht (congrFun hrate i)
        hks hka hi (hiH i hi) hC hC1 hCf (hlight i hi)
        (child i (Q i).left) (child i (Q i).right) (hleft i hi) (hright i hi)
        (ε (B.binBudget M i r) (Q i).left) (ε (B.binBudget M i r) (Q i).right)
        (hIL i hi) (hIR i hi)
    · apply (rowNormPow_clipped_le_of_ordinary hNu (rate_pos ka) X Y (pe i) G
        (fun x y => HP.toHierarchyParams.residual_nonneg (rate_pos ka) hC x y)).trans
      dsimp only [po]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact B.residualProduct_active_parent_ordinary_le M i (depth i (Q i).right) ks ka
        (ζ i (Q i).right) (floor i (Q i).right) r hrate hcutoff hCf hst hs ht (congrFun hrate i)
        (hlight i hi)
        (child i (Q i).left) (child i (Q i).right) (hleft i hi) (hright i hi)
        (ε (B.binBudget M i r) (Q i).left) (ε (B.binBudget M i r) (Q i).right)
        (hIL i hi) (hIR i hi)
  have hne : rowNormPow 4 P r.source.rate X Y
      (fun _ x y => min 1 (|nege x y| / (rate ka + G x y))) ≤ ne := by
    simp only [nege, abs_neg]
    exact B.residualNegative_parent_clipped_le hD H M ks ka r hst hs ht hks hka
      hC hC1 hCf (child 0 neg) hnegative (ε (B.childBudget M) neg) hIN
  let S : Finset (Option (ℕ ⊕ ℕ)) := insert none
    ((B.bins.image (fun i => some (Sum.inl i))) ∪
      (B.bins.image (fun i => some (Sum.inr i))))
  let e : Option (ℕ ⊕ ℕ) → ZMod P → ZMod P → ℝ := fun o =>
    match o with
    | none => nege
    | some (.inl i) => de i
    | some (.inr i) => pe i
  let pay : Option (ℕ ⊕ ℕ) → ℝ := fun o =>
    match o with
    | none => ne
    | some (.inl i) => d i
    | some (.inr i) => p i
  have hsum (v : Option (ℕ ⊕ ℕ) → ℝ) : ∑ o ∈ S, v o =
      v none + ∑ i ∈ B.bins, v (some (.inl i)) + ∑ i ∈ B.bins, v (some (.inr i)) := by
    have hd : Disjoint (B.bins.image (fun i => some (Sum.inl i)))
        (B.bins.image (fun i => some (Sum.inr i))) := by
      simp only [disjoint_left, mem_image]
      rintro o ⟨i, hi, rfl⟩ ⟨j, hj, he⟩
      cases he
    rw [show S = _ from rfl, sum_insert (by simp), sum_union hd,
      sum_image (fun _ _ _ _ h => by simpa using h),
      sum_image (fun _ _ _ _ h => by simpa using h)]
    ring
  have h := rowNormPow_clipped_sum_le_pow_sum S hNu X Y e
    (fun x y => rate ka + G x y)
    (fun x y => add_pos_of_pos_of_nonneg (rate_pos ka)
      (HP.toHierarchyParams.residual_nonneg (rate_pos ka) hC x y)) pay (by
        intro o ho
        cases o with
        | none => exact hne
        | some a =>
          cases a with
          | inl i => exact hde i (by simpa [S] using ho)
          | inr i => exact hpe i (by simpa [S] using ho))
  rw [hsum (fun o => pay o ^ (4⁻¹ : ℝ))] at h
  simp only [pay] at h
  simp_rw [hsum (fun o => e o _ _)] at h
  refine ⟨_, B.finiteInput_residual_of_rows history M r child hrows hnrow, ?_⟩
  have htarget (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (x y : ZMod P) :
      rowSliceMean X Y A x y - G x y = rowSliceMean X Y
        (fun σ x y => A σ x y - B.residualCanonicalInput r σ x y) x y := by
    have href := B.residualCanonicalInput_mean n hbins hrate hcutoff haux hD H hnH
      r r.source.role r.terminal.role hst ks ka r.source.suffix r.terminal.suffix
      (by change r.source = {r.source with rate := rate ks}; rw [← hs])
      (by change r.terminal = { r.terminal with rate := rate ka}; rw [← ht])
      hks hka hC hC1 hCf x y (fun z => hcover z y)
    change rowSliceMean X Y (B.residualCanonicalInput r) x y = G x y at href
    rw [← href]
    exact (expect_sub_distrib _ _ _).symm
  change rowNormPow 4 P r.source.rate X Y (fun _ x y =>
    min 1 (|rowSliceMean X Y _ x y - G x y| / (rate ka + G x y))) ≤ _
  simp_rw [htarget]
  convert h using 1
  congr 1
  funext σ x y
  congr 2
  congr 1
  simp only [rowSliceMean, residualCanonicalInput, expect_sub_distrib,
    expect_sum_comm, HierarchyTask.rawPositiveSample, expect_add_distrib,
    e, de, pe, nege, residualProductMean, conditionalTableMean, X, Y]
  have hratio (i : ℕ) : HierarchyTask.usageRatio (channels B.padding)
      r.terminal (Q i).direct y = gridMass P ka / gridMass P (max ka i) := by
    apply usageRatio_grid B.padding r.terminal (Q i).direct ka (max ka i) ht
    dsimp only [Q, HierarchyTask.rawRequests]
    rw [ht, hrate, rate_min]
  dsimp only [Q] at hratio ⊢
  simp_rw [hratio, ← mul_expect]
  simp only [mul_sub, sum_sub_distrib, sum_add_distrib]
  ring

omit [Fact P.Prime] in
/-- General grid requests retain positive precision for all sufficiently large
budgets after fixing the charge, rates and task. This asserts no recursive availability. -/
theorem grid_precision_eventually_pos (ks ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, 0 < B.requestPrecision M r := by
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt
    (16 * (B.slack : ℝ) * (2 * ((ks : ℝ) + ka) + B.rankCharge * r.task.rank))
  refine ⟨M₀, fun M hM => ?_⟩
  rw [B.requestPrecision_grid M ks ka r hs ht]
  have hslack : (0 : ℝ) < B.slack := by exact_mod_cast B.slack_pos
  have hcast : (M₀ : ℝ) ≤ M := by exact_mod_cast hM
  have hd : 0 < (M : ℝ) / (16 * B.slack) -
      (2 * ((ks : ℝ) + ka) + B.rankCharge * r.task.rank) := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 16 * B.slack)).mpr
    nlinarith
  linarith

/-- The retained direct coefficient has no fine-bin decay. Rounded masses can
change it by a factor of sixteen, but cannot supply a geometric offset salary. -/
theorem residualDirect_fine_coefficient_lower (H : Horizon P) (ka i : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : i ≤ H.maxExponent) (hai : ka ≤ i) :
    (1 / 16 : ℝ) ≤
      (rate i * (gridMass P ka / gridMass P (max ka i))) / rate ka := by
  rw [max_eq_right hai]
  have ha0 := rate_pos ka
  have hi0 := rate_pos i
  have hm0 := gridMass_pos (P := P) i
  have hma := (gridMass_bounds H ha).1
  have hmi := (gridMass_bounds H hi).2
  apply (le_div_iff₀ ha0).mpr
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hm0).mpr
  nlinarith [mul_le_mul_of_nonneg_left hma hi0.le,
    mul_le_mul_of_nonneg_left hmi ha0.le]

omit [Fact P.Prime] in
/-- Exact direct fine-bin salary at its literal non-exhausted budget. It grows
like `2^(9*(i-ka)/4)` before rank payment. The coarse canonical-right repair
therefore cannot by itself pay the unchanged direct endpoint bound. This is a
comparison-cost identity, not an actual-error counterexample. -/
theorem requestPrecision_residual_fine_direct (M ks ka i : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hr : r.task = .residual 0) (hrate : B.binRate = rate)
    (hai : ka ≤ i) (hM : B.slack * (1 + 4 * (i - ka)) ≤ M) :
    let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).direct
    (2 : ℝ) ^ (-B.requestPrecision (B.binBudget M i r) q) =
      (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (1 / 16 + 9 * ((i : ℝ) - ka) / 4 -
          (80 * (HP.k : ℝ) + 94) * B.rankCharge) := by
  dsimp only
  let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
    r.terminal (B.binRate i)).direct
  have hscale : ⌊Real.logb 2 (B.binRate i / r.terminal.rate)⌋ =
      -(4 * ((i - ka : ℕ) : ℤ)) := by
    change B.sampleScale r (some i) = _
    rw [B.sampleScale_grid r ka i hrate ht, Int.ofNat_sub hai]
    ring
  have hcost : LogSpaceEstimation.scaleCutoff B.slack
      ⌊Real.logb 2 (B.binRate i / r.terminal.rate)⌋ =
      B.slack * (1 + 4 * (i - ka)) := by
    rw [hscale, LogSpaceEstimation.scaleCutoff, Int.natAbs_neg, Int.natAbs_mul]
    norm_num
  have hcost1 : 1 ≤ B.slack * (1 + 4 * (i - ka)) := by
    have hslack := B.slack_pos
    nlinarith
  have hbudget : B.binBudget M i r = M - B.slack * (1 + 4 * (i - ka)) := by
    rw [binBudget, LogSpaceEstimation.lastBudget, hcost, max_eq_right hcost1]
  have hloss : ((M : ℝ) - B.binBudget M i r) / (16 * B.slack) =
      1 / 16 + ((i : ℝ) - ka) / 4 := by
    rw [hbudget, Nat.cast_sub hM, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hai]
    have hp : (B.slack : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt B.slack_pos)
    field_simp
    ring
  have hq := B.requestPrecision_residual_direct M (B.binBudget M i r) ks ka i r hs ht
    (congrFun hrate i)
  have hg := residual_base_rank_gap (HP := HP) i
  have hc : (q.task.rank : ℝ) + (80 * (HP.k : ℝ) + 94) = r.task.rank := by
    rw [hr]
    exact_mod_cast hg
  have he : -B.requestPrecision (B.binBudget M i r) q = -B.requestPrecision M r +
      (1 / 16 + 9 * ((i : ℝ) - ka) / 4 - (80 * (HP.k : ℝ) + 94) * B.rankCharge) := by
    change B.requestPrecision (B.binBudget M i r) q - B.requestPrecision M r = _ at hq
    rw [show ((B.binBudget M i r : ℕ) : ℝ) - M =
      -((M : ℝ) - B.binBudget M i r) by ring, neg_div, hloss] at hq
    rw [← hc] at hq
    linarith
  rw [show -B.requestPrecision (B.binBudget M i r) _ = _ from he,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData

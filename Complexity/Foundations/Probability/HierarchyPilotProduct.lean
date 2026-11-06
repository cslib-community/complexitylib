/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyPilotMean
public import Complexity.Foundations.Probability.HierarchyApproximateHistory
public import Complexity.Foundations.Probability.RootMetric.RelativeError

/-!
# Executed later pilot product relative transport

The literal per-bin positive sample consumes three own-request rooted errors before
averaging. The reset-right error retains its midpoint source and measured density.
All factors share one environment. Range/support and joint denominator comparisons
are explicit payments, not a desired parent-error hypothesis. In particular one can
use the actual denominator `terminal.rate + base x y` without a free ordinary to
relative conversion. The proof adapts the direct/product split of
`positiveSample_residual_fourth_le`, originally by Christian Reitwiessner,
retaining Samuel Schlesinger’s adapted hierarchy construction.

This does not identify computed means with canonical means: finite coverage,
canonical alignment, omitted bins, spectral noise, precision allocation and incoming
PREP still need payment. Supplied successful lookups do not prove joint recursion.
-/

public section
noncomputable section
open Finset Cslib
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- Genuine reference table for a requested later pilot input. Direct and reset-right
entries use their own dense recipes; the left entry uses its own pilot RAW/PREP and
current maximum. This does not change `canonicalRequestChild` dispatch. -/
@[expose] def pilotInputReference (i : ℕ) (j : Fin HP.k) (a : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hl : Admissible (HierarchyTask.rawRequests 0 i (.pilotInput j)
      r.source (midpoint r) r.terminal (B.binRate i)).left)
    (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
  if q = (HierarchyTask.rawRequests 0 i (.pilotInput j)
      r.source (midpoint r) r.terminal (B.binRate i)).left then
    pilotChild HP B.padding id
      (HierarchyTask.rawRequests 0 i (.pilotInput j)
        r.source (midpoint r) r.terminal (B.binRate i)).left hl B.base a
  else denseChild B.padding id q (B.cutoff i) (B.auxiliary i) HP.ρ HP.K B.base

omit [Fact P.Prime] in
/-- Structural alignment identifies the literal requested pilot normalized index. -/
theorem pilotInput_left_task (i : ℕ) (j : Fin HP.k) (a : ℕ) (hja : j.val = a + 1)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    (HierarchyTask.rawRequests 0 i (.pilotInput j)
      r.source (midpoint r) r.terminal (B.binRate i)).left.task =
        .row 0 (.pilotNormalized ⟨a, by omega⟩) := by
  have he : j.castSucc = (⟨a, by omega⟩ : Fin HP.k).succ := by
    apply Fin.ext
    exact hja
  simp only [HierarchyTask.rawRequests, he, HierarchyTask.correctionAtomTask,
    Fin.cases_succ, ↓reduceIte]

/-- Literal later pilot positive samples consume genuine own-request rooted errors.
The structural alignment excludes the initial zero-product case. All denominator,
range, support and reset costs are explicit; no uniform precision payment is claimed. -/
theorem positiveSample_pilot_genuine_relative_le
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M i : ℕ) (j : Fin HP.k) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (child : HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (a : ℕ) (hja : j.val = a + 1)
    (href : Admissible (HierarchyTask.rawRequests 0 i (.pilotInput j)
      r.source (midpoint r) r.terminal (B.binRate i)).left)
    (Y : Environment P 3 → ZMod P → Prop) [∀ σ y, Decidable (Y σ y)]
    (den : ZMod P → ZMod P → ℝ) (KD KP : ℝ)
    (CD CL CR : ℝ) (hCL : 0 ≤ CL) (hCR : 0 ≤ CR)
    (KL KR Kc : ℕ) (hs : 0 < r.source.rate) (hm : 0 < (midpoint r).rate)
    (hrows :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i (.pilotInput j)
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _), row history (B.binBudget M i r) q = some
      (child q))
    (hD :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i (.pilotInput j)
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ x y, child Q.direct σ x y ∈ Set.Icc 0 CD ∧
        (B.pilotInputReference i j a r href) Q.direct σ x y ∈ Set.Icc 0 CD)
    (hL :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i (.pilotInput j)
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ x z, child Q.left σ x z ∈ Set.Icc 0 CL ∧
        (B.pilotInputReference i j a r href) Q.left σ x z ∈ Set.Icc 0 CL)
    (hR :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i (.pilotInput j)
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ z y, child Q.right σ z y ∈ Set.Icc 0 CR ∧
        (B.pilotInputReference i j a r href) Q.right σ z y ∈ Set.Icc 0 CR)
    (hDo :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i (.pilotInput j)
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ x y, ¬ Q.direct.usage.retains (channels B.padding) σ y →
        child Q.direct σ x y = (B.pilotInputReference i j a r href) Q.direct σ x y)
    (hRo :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i (.pilotInput j)
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ z y, ¬ Q.right.usage.retains (channels B.padding) σ y →
        child Q.right σ z y = 0 ∧ (B.pilotInputReference i j a r href) Q.right σ z y = 0)
    (hLo :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i (.pilotInput j)
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ x z, ¬ (midpoint r).retains (channels B.padding) σ z →
        child Q.left σ x z = 0 ∧ (B.pilotInputReference i j a r href) Q.left σ x z = 0)
    (hK :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i (.pilotInput j)
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ x, #{z ∈ ({z | (midpoint r).retains (channels B.padding) σ z} : Finset _) |
        child Q.left σ x z ≠ 0} ≤ KL ∧
        #{z ∈ ({z | (midpoint r).retains (channels B.padding) σ z} : Finset _) |
          (B.pilotInputReference i j a r href) Q.left σ x z ≠ 0} ≤ KL)
    (hKr :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i (.pilotInput j)
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ z, (midpoint r).retains (channels B.padding) σ z →
        #{y ∈ ({y | Q.right.usage.retains (channels B.padding) σ y} : Finset _) |
          child Q.right σ z y ≠ 0} ≤ KR)
    (hKc :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i (.pilotInput j)
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ z, (midpoint r).retains (channels B.padding) σ z →
        #{x ∈ ({x | r.source.retains (channels B.padding) σ x} : Finset _) |
          (B.pilotInputReference i j a r href) Q.left σ x z ≠ 0} ≤ Kc)
    (hdenD : ∀ x y,
      |(B.binRate i * HierarchyTask.usageRatio (channels B.padding) r.terminal
        (HierarchyTask.rawRequests 0 i (.pilotInput j) r.source (midpoint r)
          r.terminal (B.binRate i)).direct y) / den x y| *
        (4 * CD ^ ((3 : ℝ) / 4)) ≤ KD)
    (hdenP : ∀ x y,
      |(B.binRate i * HierarchyTask.usageRatio (channels B.padding) r.terminal
        (HierarchyTask.rawRequests 0 i (.pilotInput j) r.source (midpoint r)
          r.terminal (B.binRate i)).right y * ((midpoint r).rate /
          (dens {τ | (midpoint r).retains (channels B.padding) τ y} : ℝ))) / den x y| *
        (4 * ((KL : ℝ) * CL * CR) ^ ((3 : ℝ) / 4)) ≤ KP) :
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 i (.pilotInput j)
      r.source (midpoint r) r.terminal (B.binRate i)
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let Z := fun σ z => (midpoint r).retains (channels B.padding) σ z
    let U := fun σ y => Q.right.usage.retains (channels B.padding) σ y
    ∃ A, B.positiveSample history (B.binBudget M i r) i (.pilotInput j) r = some A ∧
      rowNormPow 4 P r.source.rate X Y (fun σ x y => (A σ x y -
        HierarchyTask.rawPositiveSample (channels B.padding) 0 i (.pilotInput j)
          r.source (midpoint r) r.terminal (B.binRate i) (fun q => (B.pilotInputReference i j a
      r href) q σ) x y) / den x y) ≤
      8 * (KD ^ 4 *
        rootDistPow 4 P r.source.rate X
          (fun σ y => Q.direct.usage.retains (channels B.padding) σ y)
          (child Q.direct) ((B.pilotInputReference i j a r href) Q.direct) +
        KP ^ 4 *
          (16384 * (CR * KR * rootDistPow 4 P r.source.rate X Z
            (child Q.left) ((B.pilotInputReference i j a r href) Q.left) +
            CL * Kc * ((midpoint r).rate / r.source.rate) *
              rootDistPow 4 P (midpoint r).rate Z U (child Q.right) ((B.pilotInputReference i j
      a r href) Q.right)))) := by
  dsimp only
  have _ := B.pilotInput_left_task i j a hja r
  let canonical := B.pilotInputReference i j a r href
  let Q := HierarchyTask.rawRequests (k := HP.k) 0 i (.pilotInput j)
    r.source (midpoint r) r.terminal (B.binRate i)
  let X := fun σ x => r.source.retains (channels B.padding) σ x
  let Z := fun σ z => (midpoint r).retains (channels B.padding) σ z
  let U := fun σ y => Q.right.usage.retains (channels B.padding) σ y
  let wd := fun y => B.binRate i * HierarchyTask.usageRatio (channels B.padding)
    r.terminal Q.direct y
  let wp := fun y => B.binRate i * HierarchyTask.usageRatio (channels B.padding)
    r.terminal Q.right y * ((midpoint r).rate /
      (dens {τ | (midpoint r).retains (channels B.padding) τ y} : ℝ))
  have hN : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hd := rowNormPow_relative_sub_le_rootDistPow (mul_pos hN hs).le X Y
    (fun σ y => Q.direct.usage.retains (channels B.padding) σ y)
    (child Q.direct) (canonical Q.direct) wd den (fun _ _ => CD)
    (fun σ x y => (hD σ x y).1) (fun σ x y => (hD σ x y).2) hDo hdenD
  have hprod (σ : Environment P 3) (x y : ZMod P) :
      (∑ z ∈ ({z | Z σ z} : Finset _), child Q.left σ x z * child Q.right σ z y) ∈
        Set.Icc 0 ((KL : ℝ) * CL * CR) ∧
      (∑ z ∈ ({z | Z σ z} : Finset _), canonical Q.left σ x z * canonical Q.right σ z y) ∈
        Set.Icc 0 ((KL : ℝ) * CL * CR) := by
    have bound (L R : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
        (hl : ∀ σ x z, L σ x z ∈ Set.Icc 0 CL)
        (hr : ∀ σ z y, R σ z y ∈ Set.Icc 0 CR)
        (hk : ∀ σ x, #{z ∈ ({z | Z σ z} : Finset _) | L σ x z ≠ 0} ≤ KL) :
        (∑ z ∈ ({z | Z σ z} : Finset _), L σ x z * R σ z y) ∈
          Set.Icc 0 ((KL : ℝ) * CL * CR) := by
      refine ⟨sum_nonneg (fun z _ => mul_nonneg (hl σ x z).1 (hr σ z y).1), ?_⟩
      rw [← sum_filter_of_ne (p := fun z => L σ x z ≠ 0)
        (fun z _ h hz => h (by rw [hz, zero_mul]))]
      calc
        _ ≤ ∑ z ∈ ({z | Z σ z} : Finset _) with L σ x z ≠ 0, CL * CR :=
          sum_le_sum fun z _ => mul_le_mul (hl σ x z).2 (hr σ z y).2 (hr σ z y).1 hCL
        _ ≤ (KL : ℝ) * CL * CR := by
          rw [sum_const, nsmul_eq_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk σ x) (mul_nonneg hCL hCR)
    exact ⟨bound _ _ (fun σ x z => (hL σ x z).1) (fun σ z y => (hR σ z y).1)
      (fun σ x => (hK σ x).1),
      bound _ _ (fun σ x z => (hL σ x z).2) (fun σ z y => (hR σ z y).2)
      (fun σ x => (hK σ x).2)⟩
  have hp := rowNormPow_relative_product_sub_le_root hN hs hm hCL hCR X Z Y U
    (child Q.left) (canonical Q.left) (child Q.right) (canonical Q.right) wp den
    (fun _ _ => (KL : ℝ) * CL * CR) KR Kc
    (fun σ x z => ((hL σ x z).1).1) (fun σ x z => (hL σ x z).2)
    (fun σ z y => (hR σ z y).1) (fun σ z y => ((hR σ z y).2).1)
    hprod hKr hKc hRo hdenP
  have hz (A : HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
      (ha : ∀ σ x z, ¬ Z σ z → A Q.left σ x z = 0) (σ x y) :
      (∑ z, A Q.left σ x z * A Q.right σ z y) =
        ∑ z ∈ ({z | Z σ z} : Finset _), A Q.left σ x z * A Q.right σ z y := by
    symm
    apply sum_subset (filter_subset _ _)
    intro z _ hz
    rw [ha σ x z (by simpa using hz), zero_mul]
  refine ⟨_, B.positiveSample_of_rows history (B.binBudget M i r) i (.pilotInput j) r child
      hrows, ?_⟩
  have he : (fun σ x y => (HierarchyTask.rawPositiveSample (channels B.padding) 0 i
      (.pilotInput j) r.source (midpoint r) r.terminal (B.binRate i) (fun q => child q σ) x y -
      HierarchyTask.rawPositiveSample (channels B.padding) 0 i (.pilotInput j) r.source
        (midpoint r) r.terminal (B.binRate i) (fun q => canonical q σ) x y) / den x y) =
      (fun σ x y => wd y * (child Q.direct σ x y - canonical Q.direct σ x y) / den x y +
        wp y * ((∑ z ∈ ({z | Z σ z} : Finset _), child Q.left σ x z * child Q.right σ z y) -
          ∑ z ∈ ({z | Z σ z} : Finset _), canonical Q.left σ x z * canonical Q.right σ z y) /
      den x y) := by
    funext σ x y
    unfold HierarchyTask.rawPositiveSample
    dsimp only
    rw [hz child (fun σ x z h => (hLo σ x z h).1),
      hz canonical (fun σ x z h => (hLo σ x z h).2)]
    dsimp only [wd, wp, Q]
    ring
  rw [he]
  exact (rowNormPow_add_le (mul_pos hN hs).le _ _).trans
    (mul_le_mul_of_nonneg_left (add_le_add hd hp) (by norm_num))



end Matrix.HierarchyParams.H4RankEnvironment.BudgetData

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.CorrectionRowRecipe
public import Complexity.Foundations.Probability.DenseRowRecipes.Stability
public import Complexity.Foundations.Probability.NormalizedAtomRows.Output

/-!
# Stability of incoming correction preparation

The raw tables may be signed and unbounded. Both ranks use the same finite source
and terminal sets, including empty sets. The incoming estimate explicitly retains
column errors and the maximum row error over the full source by terminal rectangle.
The normalized factorization reuses the bounded scalar decoder; preparatory estimates
enter its clipped denominator through the actual joint conditional mean.

## Main results

* `Matrix.auxScore_stability`: entry and same-terminal-rank errors.
* `Matrix.incomingGate_stability`: same-source incoming-rank errors.
* `Matrix.correctionPrep_stability`: actual incoming preparation on changing raw tables.
* `Matrix.CorrectionRowRecipe.normalizer_stability`: joint conditional mean error.
-/
public section
namespace Matrix
open Finset Cslib
open scoped BigOperators

variable {V : Type*}

/-- Auxiliary incoming scores propagate entry and row-rank errors at the actual rate. -/
theorem auxScore_stability {I : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hI : ∀ v q v' q', |I v q - I v' q'| ≤ L * (|v - v'| + |q - q'|))
    {K : ℕ} (hK : 0 < K) {f : ℝ} (hf : 0 < f)
    (A B : Matrix V V ℝ) (T : Finset V) (x y : V) :
    |auxScore I K f A T x y - auxScore I K f B T x y| ≤
      L * (|A x y - B x y| + kthLargest 1 T (fun w => |A x w - B x w|)) / f := by
  have hq := abs_kthLargest_div_sub_div_le hK hf T (A x) (B x)
  have hi := hI (A x y / f) (kthLargest K T (fun w => A x w / f))
    (B x y / f) (kthLargest K T (fun w => B x w / f))
  rw [← sub_div, abs_div, abs_of_pos hf] at hi
  calc
    _ ≤ L * (|A x y - B x y| / f +
        |kthLargest K T (fun w => A x w / f) -
          kthLargest K T (fun w => B x w / f)|) := hi
    _ ≤ L * (|A x y - B x y| / f +
        kthLargest 1 T (fun w => |A x w - B x w|) / f) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hq) hL
    _ = _ := by ring

/-- Incoming ranks see the column error and every source row's terminal-rank error.
No source or terminal resampling occurs in this estimate. -/
theorem incomingGate_stability {I : ℝ → ℝ → ℝ} {τ : ℝ → ℝ} {LI Lτ : ℝ}
    (hLI : 0 ≤ LI) (hLτ : 0 ≤ Lτ)
    (hI : ∀ v q v' q', |I v q - I v' q'| ≤ LI * (|v - v'| + |q - q'|))
    (hτ : ∀ a b, |τ a - τ b| ≤ Lτ * |a - b|)
    {K Kc : ℕ} (hK : 0 < K) (hKc : 0 < Kc) {f : ℝ} (hf : 0 < f)
    (A B : Matrix V V ℝ) (S T : Finset V) (y : V)
    {Ec Er : ℝ} (hEc : 0 ≤ Ec) (hEr : 0 ≤ Er)
    (hc : ∀ x ∈ S, |A x y - B x y| ≤ Ec)
    (hr : ∀ x ∈ S, kthLargest 1 T (fun w => |A x w - B x w|) ≤ Er) :
    |incomingGate I τ K Kc f A S T y - incomingGate I τ K Kc f B S T y| ≤
      Lτ * (LI * (Ec + Er) / f) := by
  apply (hτ _ _).trans
  apply mul_le_mul_of_nonneg_left _ hLτ
  apply abs_kthLargest_sub_kthLargest_le hKc (by positivity)
  intro x hx
  exact (auxScore_stability hLI hI hK hf A B T x y).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add (hc x hx) (hr x hx)) hLI) hf.le)

/-- Actual correction preparation, with a changing completed raw child. The incoming
term keeps the full source/terminal rectangle; the local term uses the selected row. -/
theorem correctionPrep_stability {I : ℝ → ℝ → ℝ} {τ h ρ : ℝ → ℝ}
    {LI Lτ Lh Lρ : ℝ} (hLI : 0 ≤ LI) (hLτ : 0 ≤ Lτ) (hLρ : 0 ≤ Lρ)
    (hh : ∀ z, h z ∈ Set.Icc 0 1) (hρ : ∀ z, ρ z ∈ Set.Icc 0 1)
    (hτrange : ∀ z, τ z ∈ Set.Icc 0 1)
    (hI : ∀ v q v' q', |I v q - I v' q'| ≤ LI * (|v - v'| + |q - q'|))
    (hτ : ∀ a b, |τ a - τ b| ≤ Lτ * |a - b|)
    (hlh : ∀ a b, |h a - h b| ≤ Lh * |a - b|)
    (hlρ : ∀ a b, |ρ a - ρ b| ≤ Lρ * |a - b|)
    {K Kc : ℕ} (hK : 0 < K) (hKc : 0 < Kc) {f : ℝ} (hf : 0 < f)
    (A B : Matrix V V ℝ) (S T : Finset V) (x y : V)
    {Ec Er : ℝ} (hEc : 0 ≤ Ec) (hEr : 0 ≤ Er)
    (hc : ∀ z ∈ S, |A z y - B z y| ≤ Ec)
    (hr : ∀ z ∈ S, kthLargest 1 T (fun w => |A z w - B z w|) ≤ Er) :
    |correctionPrep I τ K Kc f A h ρ S T x y -
      correctionPrep I τ K Kc f B h ρ S T x y| ≤
      (Lh * |A x y - B x y| + Lρ * kthLargest 1 T (fun w => |A x w - B x w|)) / f +
        Lτ * (LI * (Ec + Er) / f) := by
  have hd := DenseRowRecipe.atomPrep_stability hh hρ hlh hlρ hLρ hK hf A B T x y
  have hi := incomingGate_stability hLI hLτ hI hτ hK hKc hf A B S T y hEc hEr hc hr
  have hb0 : 0 ≤ atomPrep h ρ K f B T x y := mul_nonneg (hh _).1 (hρ _).1
  have hb1 : atomPrep h ρ K f B T x y ≤ 1 :=
    (mul_le_mul_of_nonneg_right (hh _).2 (hρ _).1).trans (by simpa using (hρ _).2)
  change |atomPrep h ρ K f A T x y * incomingGate I τ K Kc f A S T y -
    atomPrep h ρ K f B T x y * incomingGate I τ K Kc f B S T y| ≤ _
  calc
    _ = |(atomPrep h ρ K f A T x y - atomPrep h ρ K f B T x y) *
        incomingGate I τ K Kc f A S T y + atomPrep h ρ K f B T x y *
        (incomingGate I τ K Kc f A S T y - incomingGate I τ K Kc f B S T y)| := by
      congr 1; ring
    _ ≤ |atomPrep h ρ K f A T x y - atomPrep h ρ K f B T x y| +
        |incomingGate I τ K Kc f A S T y - incomingGate I τ K Kc f B S T y| := by
      apply (abs_add_le _ _).trans
      rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ incomingGate I τ K Kc f A S T y from
        (hτrange _).1), abs_of_nonneg hb0]
      exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (hτrange _).2)
        (mul_le_of_le_one_left (abs_nonneg _) hb1)
    _ ≤ _ := add_le_add hd hi

namespace CorrectionRowRecipe

variable [Fintype V] {Γ Ζ : Type*} [Fintype Γ] [Fintype Ζ]

omit [Fintype V] in
/-- Preparatory changes enter through the existing joint source/usage conditional mean,
including empty conditioning slices. This does not separate correlated children. -/
theorem normalizer_stability (Xs : Γ → V → Prop) (Zt : Ζ → V → Prop)
    [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Zt t v)]
    (prep prep' : Γ × Ζ → Matrix V V ℝ) (x y : V) :
    |normalizer Xs Zt prep x y - normalizer Xs Zt prep' x y| ≤
      𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ ({t | Zt t y} : Finset Ζ),
        |prep σ x y - prep' σ x y| := by
  rw [normalizer, normalizer, ← expect_sub_distrib]
  exact abs_expect_le _ _

/-- Factorization through the existing bounded scalar decoder. Only its scalar argument
is capped; the row and incoming ranks still inspect the original signed raw table. -/
lemma normalized_factorization (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (I : ℝ → ℝ → ℝ) (τ : ℝ → ℝ) (Kc : ℕ) (f : ℝ)
    (Xs : Γ → V → Prop) (Z Zt : Ζ → V → Prop)
    [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Z t v)] [∀ t v, Decidable (Zt t v)]
    (A : Matrix V V ℝ) (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ)
    (σ : Γ × Ζ) (x y : V) (hy : Zt σ.2 y) :
    normalized I τ HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc f Xs Z Zt
      A prep maximum σ x y =
    FourthRootHierarchyParams.NormalizedRow.output HP.toHierarchyParams.atomCutoff HP.ρ 1 (A x y
      / f)
      (normalizer Xs Zt prep x y) (kthLargest HP.K {w | Z σ.2 w} (fun w => A x w / f)) *
      incomingGate I τ HP.K Kc f A {w | Xs σ.1 w} {w | Z σ.2 w} y * HP.γ (maximum y) := by
  simp only [normalized, hy, ↓reduceIte, FourthRootHierarchyParams.NormalizedRow.output,
    FourthRootHierarchyParams.NormalizedRow.clip, div_one, rowGate]
  ring

end CorrectionRowRecipe

end Matrix

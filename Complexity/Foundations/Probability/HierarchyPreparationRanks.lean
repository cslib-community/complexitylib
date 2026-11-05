/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyIncomingPreparationBias

/-!
# Weighted ranks in actual incoming PREP bias

The original comparison below retains the source-column auxiliary-score rank and the
terminal-row RAW-error rank, with their multiplicative preparation weights. Conditional
Jensen is applied to this profile before any global rectangle maximum is taken.
There is no ambient field factor in the comparison, but its right side is a weighted
rank moment, NOT the ordinary child IH. Bounding that moment uniformly by the actual
completed child's own RAW error remains an additional, unproved invariant. No support
property of canonical inputs is transferred to approximate completed inputs.

Precisely, at full terminal rate a uniform payment still needs a constant D fixed at
HP (before structural charge, field and geometry) such that the weighted rank moment is at most
`D^4 * rowNormPow 4 P r.source.rate X U (A - canonicalInput)` for actual successful
completed children. This is stronger than their ordinary own-error IH. The checked
half-identity execution satisfies such a comparison, but general completed inputs and
the exhaustive polynomial-bin family have not been proved to satisfy it. At general
terminal rates the entry/row terms keep division by that rate and the auxiliary scores
inside the source-column rank keep their own rate normalization.

The execution consumer keeps the literal child budget, successful input/pilotInput,
source/terminal/usage masks, suffixes and default completion slack. Its own-mask version
requires usage equal to terminal. No independence or recursive availability is asserted.

## Main definitions

* `Matrix.preparationRankError`: weighted entry, terminal-row and source-column errors.

## Main results

* `Matrix.correctionPrep_rank_error_le`: weighted pointwise comparison.
* `Matrix.HierarchyParams.H4RankEnvironment.BudgetData.evaluate_preparation_rank_bias`:
  literal evaluated PREP bias paid by the weighted rank profile.
-/

public section
noncomputable section
namespace Matrix
open Finset Cslib

/-- A local perturbation profile. The last rank is over source columns of auxiliary
scores; each score still reads its original terminal-row rank. The weights are actual
factors in preparation, not support assumptions about the completed input. -/
@[expose] def preparationRankError {V : Type*}
    (I : ℝ → ℝ → ℝ) (τ h ρ : ℝ → ℝ) (K Kc : ℕ) (f Lh Lρ Lτ : ℝ)
    (A B : Matrix V V ℝ) (S T : Finset V) (x y : V) : ℝ :=
  (Lh / f) * |A x y - B x y| * rowGate ρ K f A T x *
      incomingGate I τ K Kc f A S T y +
    (Lρ / f) * h (B x y / f) * kthLargest 1 T (fun w => |A x w - B x w|) *
      incomingGate I τ K Kc f A S T y +
    Lτ * atomPrep h ρ K f B T x y * kthLargest 1 S (fun z =>
      |auxScore I K f A T z y - auxScore I K f B T z y|)

/-- Telescope the three actual factors before discarding their weights. Empty rank
sets are allowed. Signed, unbounded RAW values need no range or support premise. -/
theorem correctionPrep_rank_error_le {V : Type*}
    {I : ℝ → ℝ → ℝ} {τ h ρ : ℝ → ℝ} {Lh Lρ Lτ : ℝ}
    (hLρ : 0 ≤ Lρ) (hLτ : 0 ≤ Lτ)
    (hh : ∀ z, 0 ≤ h z) (hρ : ∀ z, 0 ≤ ρ z) (hτ : ∀ z, 0 ≤ τ z)
    (hlh : ∀ a b, |h a - h b| ≤ Lh * |a - b|)
    (hlρ : ∀ a b, |ρ a - ρ b| ≤ Lρ * |a - b|)
    (hlτ : ∀ a b, |τ a - τ b| ≤ Lτ * |a - b|)
    {K Kc : ℕ} (hK : 0 < K) (hKc : 0 < Kc) {f : ℝ} (hf : 0 < f)
    (A B : Matrix V V ℝ) (S T : Finset V) (x y : V) :
    |correctionPrep I τ K Kc f A h ρ S T x y -
      correctionPrep I τ K Kc f B h ρ S T x y| ≤
      preparationRankError I τ h ρ K Kc f Lh Lρ Lτ A B S T x y := by
  have he := hlh (A x y / f) (B x y / f)
  rw [← sub_div, abs_div, abs_of_pos hf] at he
  have hr := (hlρ (kthLargest K T (fun w => A x w / f))
    (kthLargest K T (fun w => B x w / f))).trans
    (mul_le_mul_of_nonneg_left (abs_kthLargest_div_sub_div_le hK hf T (A x) (B x)) hLρ)
  have hc := (hlτ (kthLargest Kc S (fun z => auxScore I K f A T z y))
    (kthLargest Kc S (fun z => auxScore I K f B T z y))).trans
    (mul_le_mul_of_nonneg_left (abs_kthLargest_sub_kthLargest_le hKc
      (kthLargest_nonneg (k := 1)) (fun z hz =>
        abs_le_kthLargest_one S (fun z => auxScore I K f A T z y -
          auxScore I K f B T z y) z hz)) hLτ)
  have ht : 0 ≤ incomingGate I τ K Kc f A S T y := hτ _
  have hb : 0 ≤ atomPrep h ρ K f B T x y := mul_nonneg (hh _) (hρ _)
  have hd :
      |correctionPrep I τ K Kc f A h ρ S T x y -
        correctionPrep I τ K Kc f B h ρ S T x y| ≤
      |h (A x y / f) - h (B x y / f)| * rowGate ρ K f A T x *
          incomingGate I τ K Kc f A S T y +
        h (B x y / f) * |rowGate ρ K f A T x - rowGate ρ K f B T x| *
          incomingGate I τ K Kc f A S T y +
        atomPrep h ρ K f B T x y *
          |incomingGate I τ K Kc f A S T y - incomingGate I τ K Kc f B S T y| := by
    have hid : correctionPrep I τ K Kc f A h ρ S T x y -
        correctionPrep I τ K Kc f B h ρ S T x y =
        (h (A x y / f) - h (B x y / f)) * rowGate ρ K f A T x *
          incomingGate I τ K Kc f A S T y +
        h (B x y / f) * (rowGate ρ K f A T x - rowGate ρ K f B T x) *
          incomingGate I τ K Kc f A S T y +
        atomPrep h ρ K f B T x y *
          (incomingGate I τ K Kc f A S T y - incomingGate I τ K Kc f B S T y) := by
      simp only [correctionPrep, atomPrep]
      ring
    rw [hid]
    let a := (h (A x y / f) - h (B x y / f)) * rowGate ρ K f A T x *
      incomingGate I τ K Kc f A S T y
    let b := h (B x y / f) * (rowGate ρ K f A T x - rowGate ρ K f B T x) *
      incomingGate I τ K Kc f A S T y
    let c := atomPrep h ρ K f B T x y *
      (incomingGate I τ K Kc f A S T y - incomingGate I τ K Kc f B S T y)
    have htri : |a + b + c| ≤ |a| + |b| + |c| :=
      (abs_add_le (a + b) c).trans (add_le_add (abs_add_le a b) (le_refl |c|))
    apply htri.trans
    dsimp only [a, b, c]
    simp only [abs_mul, abs_of_nonneg (show 0 ≤ rowGate ρ K f A T x from hρ _),
      abs_of_nonneg ht, abs_of_nonneg (hh _), abs_of_nonneg hb]
    exact le_rfl
  apply hd.trans
  have hrow : 0 ≤ rowGate ρ K f A T x := hρ _
  have hbentry : 0 ≤ h (B x y / f) := hh _
  have hbound := add_le_add
    (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hrow) ht)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hbentry) ht))
    (mul_le_mul_of_nonneg_left hc hb)
  exact hbound.trans_eq (by unfold preparationRankError; ring)

end Matrix

namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.Probability
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
variable {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- Weighted rank Jensen for the literal successful PREP. Constants depend only on HP,
selected before the field or requests. No global maximum or ambient-width estimate is
used. To obtain an own-IH salary, a further comparison of the displayed rank moment
with the ordinary RAW error is still needed; this theorem does not assume that comparison. -/
theorem evaluate_preparation_rank_bias :
    ∃ Lh Lρ Lτ : ℝ, 0 ≤ Lh ∧ 0 ≤ Lρ ∧ 0 ≤ Lτ ∧
    ∀ (P : ℕ) [Fact P.Prime] (B : BudgetData HP P) (M : ℕ) (pilot : Bool)
      (i : Fin HP.k) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
    r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i) →
    0 < B.requestPrecision M r → B.childBudget M < M →
    r.usage = r.terminal → 0 ≤ r.source.rate → 0 < r.terminal.rate →
    ∀ (A W : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ),
    let q := { r with task := .row 0 (if pilot then .pilotInput i else .input i) }
    0 < B.requestPrecision (B.childBudget M) q →
    B.evaluate (B.childBudget M) q = some (.row A) →
    B.evaluate M r = some (.row W) →
    ∀ (s u : Fin 3) (_hsu : s ≠ u) (ks ku : ℕ) (ss su : List (ZMod P)),
    r.source = gridChannel s ks ss → r.usage = gridChannel u ku su →
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    let C := B.canonicalPreparationInput pilot i r
    rowNormPow 4 P r.source.rate X U (fun _ x y => rowSliceMean X U W x y -
      rowSliceMean X U (B.incomingPreparation r (fun _ => C)) x y) ≤
    rowNormPow 4 P r.source.rate X U (fun σ x y =>
      preparationRankError (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
        (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
        r.terminal.rate Lh Lρ Lτ (A σ) C {z | X σ z} {w | U σ w} x y) := by
  obtain ⟨Lh, Lρ, hh, hρ, hlh, hlρ⟩ :=
    NormalizedMoments.preparation_stability_constants HP
  obtain ⟨Lτ, hlτ⟩ := HP.incomingCutoff_root
  have hLτ : 0 ≤ (4 : ℝ) * Lτ := by positivity
  refine ⟨Lh, Lρ, 4 * Lτ, hh, hρ, hLτ, ?_⟩
  intro P instP B M pilot i r hr hp hm hu hs hf A W q _hqp hA hW
    s u hsu ks ku ss su hsource husage X U C
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := mul_nonneg (Nat.cast_nonneg _) hs
  have hmean : (fun (_ : Environment P 3) x y => rowSliceMean X U W x y -
      rowSliceMean X U (B.incomingPreparation r (fun _ => C)) x y) =
      (fun _ => rowSliceMean X U (fun σ x y =>
        B.incomingPreparation r A σ x y -
          B.incomingPreparation r (fun _ => C) σ x y)) := by
    funext σ x y
    rw [B.evaluate_preparation_mean M pilot i r hr hp hm A W hA hW
      s u hsu ks ku ss su hsource husage]
    simp only [rowSliceMean, expect_sub_distrib, X, U]
  rw [hmean]
  apply (rowNormPow_sliceMean_fourth_le hNu X U _).trans
  apply (rowNormPow_le_mul hNu (c := 1) ?_).trans_eq (one_mul _)
  intro σ x y _hx _hy
  have hKc : 0 < ⌈4 * (1 + 32 * HP.R)⌉₊ :=
    Nat.ceil_pos.mpr (by linarith [HP.R_var])
  have h := correctionPrep_rank_error_le (I := polynomialAuxCutoff4 HP.θ) hρ hLτ
    (polynomialPrepCutoff4_nonneg HP.θ) HP.ρ_nonneg HP.incomingCutoff_nonneg
    hlh hlρ (abs_sub_le_four_mul_root_lipschitz
      (fun z => ⟨HP.incomingCutoff_nonneg z, HP.incomingCutoff_le_one z⟩) hlτ)
    (FourthRootHierarchyParams.NormalizedRow.rank_pos HP)
    hKc hf
    (A σ) C {z | X σ z} {w | U σ w} x y
  have hn := (abs_nonneg _).trans h
  have hpw := pow_le_pow_left₀ (abs_nonneg _) h 4
  rw [one_mul, abs_of_nonneg hn]
  simpa only [incomingPreparation, X, U, hu] using hpw

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData

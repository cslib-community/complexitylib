/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyIncomingPreparationBias
public import Mathlib.Data.Matrix.Basis
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# One-entry rate loss in the literal normalized correction recipe

This original algebraic regression checks the proposed cancellation at the PREP/normalized
seam. It supplies tables to the actual decoder, not successful recursive evaluator histories.
The true input has one entry equal to the terminal rate; the approximate input replaces it
by `5 * θ / 8` times that rate. Each table's own row and incoming ranks are computed.
Preparation is half only at the distinguished pair, and zero elsewhere: it is not a
constant matrix. Conditional averaging is over environments at a fixed pair.

`ratio` and `walked_ratio` compare the rooted normalized output with the ordinary fourth
moment of its own RAW input error. The same actual density divided by `P` occurs in both
moments and cancels. `ratio_unbounded` disproves a geometry-uniform constant for this
algebraic inference. There is no external rate in this normalized-task consumer.

No precision policy, bounded-rate payment, recursive IH, or estimator-failure claim changes.
This construction is original; its motivation is issue #1721, research comment 6673113515.
The comment's half-mean assertion is valid at the exceptional pair, not at all source vertices.

## Main results

* `Matrix.DecoderRateObstruction.ratio`: exact positive coefficient times inverse rate to four.
* `Matrix.DecoderRateObstruction.walked_ratio`: the same ratio after actual completion walks.
* `Matrix.DecoderRateObstruction.ratio_unbounded`: no uniform algebraic decoder constant.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Matrix.DecoderRateObstruction
open Finset Cslib
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
variable {V : Type*} [DecidableEq V]

/-- The tables used below are nonnegative and substochastic whenever their one entry is. -/
theorem entry_substochastic [Fintype V] (a b : V) {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    (∀ x y, 0 ≤ single a b v x y) ∧ (∀ x, ∑ y, single a b v x y ≤ 1) := by
  constructor
  · intro x y
    simp only [single_apply]
    split_ifs <;> positivity
  · intro x
    by_cases hx : x = a
    · simpa [single_apply, hx] using hv1
    · simp [Ne.symm hx]

omit [DecidableEq V] in
private theorem sparse_rank_zero {k : ℕ} (hk : 1 < k) (S : Finset V)
    (g : V → ℝ) (a : V) (hg : ∀ x, x ≠ a → g x = 0) : kthLargest k S g = 0 := by
  apply le_antisymm _ kthLargest_nonneg
  apply not_lt.mp
  intro ht
  have hc := (lt_kthLargest_iff (by omega : 0 < k) (le_refl (0 : ℝ))).mp ht
  have hs : {x ∈ S | 0 < g x} ⊆ {a} := by
    intro x hx
    by_contra hn
    have hxa : x ≠ a := by simpa using hn
    have hpos := (mem_filter.mp hx).2
    rw [hg x hxa] at hpos
    exact lt_irrefl _ hpos
  have hcard := card_le_card hs
  simp only [card_singleton] at hcard
  omega

/-- One-entry row and column supports are bounded separately on arbitrary retained sets. -/
theorem supports (a b x y : V) (v : ℝ) (S T : Finset V) :
    #{z ∈ T | single a b v x z ≠ 0} ≤ 1 ∧
    #{z ∈ S | single a b v z y ≠ 0} ≤ 1 := by
  constructor
  · apply (card_le_card (show {z ∈ T | single a b v x z ≠ 0} ⊆ {b} from ?_)).trans_eq
      (card_singleton b)
    intro z hz
    by_contra hn
    have hz' : z ≠ b := by simpa using hn
    exact (mem_filter.mp hz).2 (by simp [hz'.symm])
  · apply (card_le_card (show {z ∈ S | single a b v z y ≠ 0} ⊆ {a} from ?_)).trans_eq
      (card_singleton a)
    intro z hz
    by_contra hn
    have hz' : z ≠ a := by simpa using hn
    exact (mem_filter.mp hz).2 (by simp [hz'.symm])

/-- Each row rank vanishes on every retained set, independently for each table. -/
theorem row_rank (a b x : V) (v f : ℝ) {K : ℕ} (hK : 1 < K) (T : Finset V) :
    kthLargest K T (fun y => single a b v x y / f) = 0 := by
  apply sparse_rank_zero hK T _ b
  intro y hy
  simp [hy.symm]

/-- Incoming ranks also vanish; zero entries have zero auxiliary score. -/
theorem incoming_rank (a b y : V) (v f : ℝ) {K Kc : ℕ} (hc : 1 < Kc)
    (I : ℝ → ℝ → ℝ) (hI : ∀ r, I 0 r = 0) (S T : Finset V) :
    kthLargest Kc S (fun x => auxScore I K f (single a b v) T x y) = 0 := by
  apply sparse_rank_zero hc S _ a
  intro x hx
  simp [auxScore, hx.symm, hI]

/-- Exact evaluation of both production gates and preparation, on arbitrary retained sets. -/
theorem preparation (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (hK : 1 < HP.K) (a b x y : V) (v f : ℝ) (S T : Finset V) :
    correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K
      ⌈4 * (1 + 32 * HP.R)⌉₊ f (single a b v) (polynomialPrepCutoff4 HP.θ) HP.ρ S T x y =
      polynomialPrepCutoff4 HP.θ (single a b v x y / f) := by
  have hc : 1 < ⌈4 * (1 + 32 * HP.R)⌉₊ := by
    have h := Nat.le_ceil (4 * (1 + 32 * HP.R))
    have hr := HP.R_var
    by_contra hn
    have hn' : (⌈4 * (1 + 32 * HP.R)⌉₊ : ℝ) ≤ 1 := by
      exact_mod_cast (by omega : ⌈4 * (1 + 32 * HP.R)⌉₊ ≤ 1)
    linarith
  have hz : ∀ r, polynomialAuxCutoff4 HP.θ 0 r = 0 := fun r =>
    polynomialAuxCutoff4_eq_zero_of_entry_le HP.θ_pos (by linarith [HP.θ_pos])
  have ht : HP.incomingCutoff 0 = 1 := HP.incomingCutoff_one (by rw [HP.τ₀_eq]; norm_num)
  simp only [correctionPrep, rowGate, incomingGate,
    row_rank a b x v f hK T, incoming_rank a b y v f hc _ hz S T,
    HP.ρ_one 0 HP.η_pos.le, ht, mul_one]

/-- The midpoint value is computed from the actual degree-seven switch. -/
theorem prep_half {θ : ℝ} (hθ : 0 < θ) : polynomialPrepCutoff4 θ (5 * θ / 8) = 1 / 2 := by
  have he : (5 * θ / 8 - θ / 2) / (3 * θ / 4 - θ / 2) = 1 / 2 := by
    field_simp
    nlinarith [hθ.ne']
  norm_num [polynomialPrepCutoff4, polynomialSwitch4, he, polynomialTransition4,
    transitionPolynomial4]

open Matrix.HierarchyParams Cslib.Probability
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.HierarchyParams.H4RankEnvironment.BudgetData

variable {P : ℕ} [Fact P.Prime]

/-- Full source, narrower terminal and identical usage, with distinct roles and fixed suffixes. -/
@[expose] def request (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ) :
    HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
  ⟨.row 0 (.normalized ⟨0, HP.k_pos⟩), gridChannel 0 0 [1],
    gridChannel 2 ka [2, 3], gridChannel 2 ka [2, 3]⟩

/-- Concrete budget data fixes the true one-entry input. Its evaluator is not asserted to run. -/
@[expose] def data (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ) :
    BudgetData HP P where
  padding := 1
  base := single 0 0 (rate ka)
  bins := {0}
  binRate := fun _ => 1
  cutoff := fun _ => polynomialSwitch4 (1 / 2) 1
  auxiliary := fun _ _ => 1
  slack := 1
  slack_pos := by decide
  rankCharge := 0
  binCap := 1
  binCap_nonneg := zero_le_one
  cutoff_bounds := fun _ d =>
    ⟨polynomialSwitch4_nonneg _ _ d, polynomialSwitch4_le_one _ _ d⟩

/-- Exact production preparation on the whole table: a one-entry cutoff table. -/
theorem incoming (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ) (v : ℝ)
    (σ : Environment P 3) :
    (data HP ka).incomingPreparation (request (P := P) HP ka) (fun _ => single 0 0 v) σ =
      single 0 0 (polynomialPrepCutoff4 HP.θ (v / rate ka)) := by
  funext x y
  rw [incomingPreparation, preparation HP (FourthRootHierarchyParams.NormalizedRow.rank_gt_one HP)]
  change polynomialPrepCutoff4 HP.θ (single 0 0 v x y / rate ka) = _
  by_cases h : x = 0 ∧ y = 0
  · simp [h.1, h.2]
  · have hn : ¬(0 = x ∧ 0 = y) := by simpa only [eq_comm] using h
    simp [hn, polynomialPrepCutoff4_eq_zero HP.θ_pos
      (by linarith [HP.θ_pos] : (0 : ℝ) ≤ HP.θ / 2)]

/-- Approximate PREP is half at the exceptional pair, and zero elsewhere. -/
theorem incoming_half (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ)
    (σ : Environment P 3) :
    (data HP ka).incomingPreparation (request (P := P) HP ka)
      (fun _ => single 0 0 (5 * HP.θ * rate ka / 8)) σ = single 0 0 (1 / 2) := by
  rw [incoming]
  have he : 5 * HP.θ * rate ka / 8 / rate ka = 5 * HP.θ / 8 := by
    field_simp [(rate_pos ka).ne']
  rw [he, prep_half HP.θ_pos]

/-- True PREP is one at the exceptional pair. -/
theorem incoming_one (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ)
    (σ : Environment P 3) :
    (data HP ka).incomingPreparation (request (P := P) HP ka)
      (fun _ => single 0 0 (rate ka)) σ = single 0 0 1 := by
  rw [incoming, div_self (rate_pos ka).ne', polynomialPrepCutoff4_eq_one HP.θ_pos
    (by linarith [HP.θ_lt_θ₂, HP.θ₂_lt])]

private theorem source_full (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ)
    (σ : Environment P 3) (x : ZMod P) :
    (request (P := P) HP ka).source.retains (channels (1 : ZMod P)) σ x := by
  change frameRetains P 4 (semanticSide P (rate 0)) (σ 0) _
  rw [semanticSide_grid]
  simpa [side] using full_retains (σ 0) _

/-- Actual usage density; ceiling-rounded side lengths are retained. -/
@[expose] def densityFactor (ka : ℕ) : ℝ := (((side P ka : ℝ) / P) ^ 4) / P

/-- Every actual pair slice is nonempty, despite a possibly tiny nominal rate. -/
theorem slice_nonempty (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ)
    (x y : ZMod P) :
    ({σ : Environment P 3 | (request (P := P) HP ka).source.retains (channels (1 : ZMod P)) σ x ∧
      (request (P := P) HP ka).usage.retains (channels (1 : ZMod P)) σ y} : Finset _).Nonempty := by
  have hd := density (P := P) (2 : Fin 3) (side P ka) (side_le P ka)
    (CopyPadding.identifier (1 : ZMod P) [2, 3] y)
  apply dens_ne_zero.mp
  intro hz
  have he : ({σ : Environment P 3 |
      (request (P := P) HP ka).source.retains (channels (1 : ZMod P)) σ x ∧
      (request (P := P) HP ka).usage.retains (channels (1 : ZMod P)) σ y} : Finset _) =
      ({σ : Environment P 3 | frameRetains P 4 (side P ka) (σ 2)
        (CopyPadding.identifier (1 : ZMod P) [2, 3] y)} : Finset _) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, source_full, true_and]
    change frameRetains P 4 (semanticSide P (rate ka)) (σ 2) _ ↔ _
    rw [semanticSide_grid]
    rfl
  rw [he] at hz
  rw [hz] at hd
  have hp : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hs : (0 : ℝ) < side P ka := by
    exact_mod_cast side_pos P ka (Fact.out : P.Prime).pos
  have hh : (0 : ℝ) < ((side P ka : ℝ) / P) ^ 4 := by positivity
  exact hh.ne' (by simpa using hd.symm)

/-- A constant-in-environment one-entry preparation has its literal nonempty-slice mean. -/
theorem slice_entry (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ) (v : ℝ)
    (x y : ZMod P) :
    rowSliceMean
      (fun σ x => (request (P := P) HP ka).source.retains (channels (1 : ZMod P)) σ x)
      (fun σ y => (request (P := P) HP ka).usage.retains (channels (1 : ZMod P)) σ y)
      (fun _ => single 0 0 v) x y = single 0 0 v x y := by
  exact Finset.expect_const (slice_nonempty HP ka x y) _

/-- The actual correction request with fixed true RAW and maximum zero. No external rate. -/
@[expose] def output (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ)
    (W : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :
    Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
  correctionRequest 1 id (request (P := P) HP ka) (polynomialAuxCutoff4 HP.θ)
    HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K
    ⌈4 * (1 + 32 * HP.R)⌉₊ (fun _ => single 0 0 (rate ka)) W (fun _ _ => 0)

/-- Literal decoder evaluation, with the actual usage mask and dimensionless denominator. -/
theorem output_entry (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ) (c : ℝ)
    (σ : Environment P 3) (x y : ZMod P) :
    output HP ka (fun _ => single 0 0 c) σ x y =
      if (request (P := P) HP ka).usage.retains (channels (1 : ZMod P)) σ y then
        single 0 0 (HP.Q 1 / max (1 / 2) (min 1 c)) x y else 0 := by
  have hr : Admissible (request (P := P) HP ka) := by
    exact ⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩
  have hc : 1 < ⌈4 * (1 + 32 * HP.R)⌉₊ := by
    have h := Nat.le_ceil (4 * (1 + 32 * HP.R))
    have hn := HP.R_var
    by_contra hh
    have hh' : (⌈4 * (1 + 32 * HP.R)⌉₊ : ℝ) ≤ 1 := by
      exact_mod_cast (by omega : ⌈4 * (1 + 32 * HP.R)⌉₊ ≤ 1)
    linarith
  have hz : ∀ r, polynomialAuxCutoff4 HP.θ 0 r = 0 := fun r =>
    polynomialAuxCutoff4_eq_zero_of_entry_le HP.θ_pos (by linarith [HP.θ_pos])
  have ht : HP.incomingCutoff 0 = 1 :=
    HP.incomingCutoff_one (by rw [HP.τ₀_eq]; norm_num)
  unfold output correctionRequest
  rw [dite_eq_left hr]
  dsimp only
  unfold CorrectionRowRecipe.normalized
  rw [normalizer_full 1 id (request (P := P) HP ka) hr (fun _ => single 0 0 c) x y]
  simp only [id_eq]
  rw [slice_entry HP ka c x y]
  simp only [rowGate, incomingGate, show (request (P := P) HP ka).terminal.rate = rate ka
      from rfl, row_rank 0 0 x (rate ka) (rate ka)
      (FourthRootHierarchyParams.NormalizedRow.rank_gt_one HP),
    incoming_rank 0 0 y (rate ka) (rate ka) hc _ hz,
    HP.ρ_one 0 HP.η_pos.le, ht, mul_one, HP.γ_one 0 (by norm_num)]
  have hu : coordinate (1 : ZMod P) (request (P := P) HP ka).usage
      ((Equiv.piSplitAt (request (P := P) HP ka).terminal.role
        (fun _ : Fin 3 => FrameChannel P 4 1) σ).1) y =
      (request (P := P) HP ka).usage.retains (channels (1 : ZMod P)) σ y := by rfl
  simp only [hu]
  split_ifs
  · by_cases h : x = 0 ∧ y = 0
    · rcases h with ⟨rfl, rfl⟩
      simp only [single_apply, and_self, ↓reduceIte, div_self (rate_pos ka).ne']
      rw [HP.toHierarchyParams.atomCutoff_eq (by norm_num) (by
        have hk : (0 : ℝ) ≤ HP.k := Nat.cast_nonneg _
        linarith)]
    · have hn : ¬(0 = x ∧ 0 = y) := by simpa only [eq_comm] using h
      simp [hn, HP.toHierarchyParams.atomCutoff_eq_zero (le_refl (0 : ℝ))]
  · rfl

/-- The numerator at one is positive for the actual bounded cutoff. -/
theorem numerator_pos (HP : FourthRootHierarchyParams 16 1 16 32 8) : 0 < HP.Q 1 := by
  have h := HP.le_Q 1
  linarith [HP.θ₂_lt]

/-- Successful completion preserves each actual conditional preparation mean.
This is completion algebra, not successful evaluation of a RAW child. -/
theorem completed_mean (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka M : ℕ)
    (v : ℝ) (W : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hW : (data HP ka).complete M (request (P := P) HP ka)
      ((data HP ka).incomingPreparation (request (P := P) HP ka) (fun _ => single 0 0 v)) = some W)
    (x y : ZMod P) :
    rowSliceMean
      (fun σ x => (request (P := P) HP ka).source.retains (channels (1 : ZMod P)) σ x)
      (fun σ y => (request (P := P) HP ka).usage.retains (channels (1 : ZMod P)) σ y) W x y =
    single 0 0 (polynomialPrepCutoff4 HP.θ (v / rate ka)) x y := by
  have hm := BudgetData.preparationWalk_mean (data HP ka) M (request (P := P) HP ka)
    0 2 (by decide) 0 ka [1] [2, 3] rfl rfl _ W hW x y
  apply hm.trans
  have hi := fun σ : Environment P 3 => incoming (P := P) HP ka v σ
  have he : (data HP ka).incomingPreparation (request (P := P) HP ka) (fun _ => single 0 0 v) =
      fun _ => single 0 0 (polynomialPrepCutoff4 HP.θ (v / rate ka)) := funext hi
  rw [he]
  exact slice_entry HP ka _ x y

/-- Exact integrated ordinary moment, with actual retention density divided by `P`. -/
theorem entry_moment (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ) (v : ℝ) :
    rowNormPow 4 P (request (P := P) HP ka).source.rate
      (fun σ x => (request (P := P) HP ka).source.retains (channels (1 : ZMod P)) σ x)
      (fun σ y => (request (P := P) HP ka).usage.retains (channels (1 : ZMod P)) σ y)
      (fun _ => single 0 0 v) = densityFactor (P := P) ka * |v| ^ 4 := by
  unfold rowNormPow
  have hs : (request (P := P) HP ka).source.rate = 1 := by norm_num [request, gridChannel, rate]
  simp only [hs, mul_one]
  have he (σ : Environment P 3) :
      (∑ x ∈ {x | (request (P := P) HP ka).source.retains (channels (1 : ZMod P)) σ x},
        ∑ y ∈ {y | (request (P := P) HP ka).usage.retains (channels (1 : ZMod P)) σ y},
          |single 0 0 v x y| ^ 4) =
      (if (request (P := P) HP ka).usage.retains (channels (1 : ZMod P)) σ 0 then 1 else 0) *
        |v| ^ 4 := by
    simp [single_apply, source_full, ite_and, apply_ite abs, ite_pow]
  simp_rw [he]
  rw [← Finset.expect_mul, Fintype.expect_boole]
  have hd := density (P := P) (2 : Fin 3) (side P ka) (side_le P ka)
    (CopyPadding.identifier (1 : ZMod P) [2, 3] 0)
  have hu : (fun σ : Environment P 3 =>
      (request (P := P) HP ka).usage.retains (channels (1 : ZMod P)) σ 0) =
      (fun σ => frameRetains P 4 (side P ka) (σ 2)
        (CopyPadding.identifier (1 : ZMod P) [2, 3] 0)) := by
    funext σ
    change frameRetains P 4 (semanticSide P (rate ka)) (σ 2) _ = _
    rw [semanticSide_grid]
    rfl
  simp only [hu]
  rw [hd]
  unfold densityFactor
  ring

/-- The RAW error uses ordinary fourth powers in matrix units. -/
theorem input_moment (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ) :
    rowNormPow 4 P (request (P := P) HP ka).source.rate
      (fun σ x => (request (P := P) HP ka).source.retains (channels (1 : ZMod P)) σ x)
      (fun σ y => (request (P := P) HP ka).usage.retains (channels (1 : ZMod P)) σ y)
      (fun _ x y => single 0 0 (5 * HP.θ * rate ka / 8) x y -
        single 0 0 (rate ka) x y) =
      densityFactor (P := P) ka * rate ka ^ 4 * (1 - 5 * HP.θ / 8) ^ 4 := by
  have he : (fun (_ : Environment P 3) (x y : ZMod P) => single 0 0 (5 * HP.θ * rate ka / 8) x y -
      single 0 0 (rate ka) x y) = fun _ => single 0 0 (5 * HP.θ * rate ka / 8 - rate ka) := by
    funext σ x y
    simp only [single_apply]
    split_ifs <;> ring
  rw [he, entry_moment, show |5 * HP.θ * rate ka / 8 - rate ka| ^ 4 =
      (5 * HP.θ * rate ka / 8 - rate ka) ^ 4 by
    exact (by decide : Even 4).pow_abs _]
  ring

/-- Exact rooted output moment. The factor is actual density, not the nominal rate. -/
theorem output_moment (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ) :
    rootDistPow 4 P (request (P := P) HP ka).source.rate
      (fun σ x => (request (P := P) HP ka).source.retains (channels (1 : ZMod P)) σ x)
      (fun σ y => (request (P := P) HP ka).usage.retains (channels (1 : ZMod P)) σ y)
      (output HP ka (fun _ => single 0 0 (1 / 2)))
      (output HP ka (fun _ => single 0 0 1)) =
      densityFactor (P := P) ka * HP.Q 1 * ((2 : ℝ) ^ (4⁻¹ : ℝ) - 1) ^ 4 := by
  let d := (2 * HP.Q 1) ^ (4⁻¹ : ℝ) - HP.Q 1 ^ (4⁻¹ : ℝ)
  have he : rootDistPow 4 P (request (P := P) HP ka).source.rate
      (fun σ x => (request (P := P) HP ka).source.retains (channels (1 : ZMod P)) σ x)
      (fun σ y => (request (P := P) HP ka).usage.retains (channels (1 : ZMod P)) σ y)
      (output HP ka (fun _ => single 0 0 (1 / 2)))
      (output HP ka (fun _ => single 0 0 1)) =
      rowNormPow 4 P (request (P := P) HP ka).source.rate
        (fun σ x => (request (P := P) HP ka).source.retains (channels (1 : ZMod P)) σ x)
        (fun σ y => (request (P := P) HP ka).usage.retains (channels (1 : ZMod P)) σ y)
        (fun _ => single 0 0 d) := by
    unfold rootDistPow rowNormPow
    congr 1
    apply Finset.expect_congr rfl
    intro σ _
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro y hy
    have hu := (mem_filter.mp hy).2
    dsimp only
    rw [output_entry, output_entry, ite_eq_left hu, ite_eq_left hu]
    by_cases h : x = 0 ∧ y = 0
    · simp only [single_apply, h.1, h.2, and_self, ↓reduceIte]
      norm_num only [min_self, max_self, show max (1 / 2 : ℝ) 1 = 1 by norm_num,
        show min (1 : ℝ) (1 / 2) = 1 / 2 by norm_num, div_one, div_div, div_one]
      congr 2
      dsimp only [d]
      congr 2 <;> norm_num; ring
    · have hn : ¬(0 = x ∧ 0 = y) := by simpa only [eq_comm] using h
      simp [hn]
  rw [he, entry_moment]
  have hq := numerator_pos HP
  have hd : d = (HP.Q 1) ^ (4⁻¹ : ℝ) * ((2 : ℝ) ^ (4⁻¹ : ℝ) - 1) := by
    dsimp only [d]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hq.le]
    ring
  rw [hd, abs_mul, mul_pow, (by decide : Even 4).pow_abs,
    (by decide : Even 4).pow_abs]
  have hp : ((HP.Q 1) ^ (4⁻¹ : ℝ)) ^ (4 : ℕ) = HP.Q 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    norm_num
  rw [hp]
  ring

/-- Positive mask factor, even when ceiling rounding differs from the nominal rate. -/
theorem densityFactor_pos (ka : ℕ) : 0 < densityFactor (P := P) ka := by
  have hp : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hs : (0 : ℝ) < side P ka := by
    exact_mod_cast side_pos P ka (Fact.out : P.Prime).pos
  unfold densityFactor
  positivity

/-- Fixed, positive coefficient of the inverse-fourth-power rate loss. -/
@[expose] def coefficient (HP : FourthRootHierarchyParams 16 1 16 32 8) : ℝ :=
  HP.Q 1 * ((2 : ℝ) ^ (4⁻¹ : ℝ) - 1) ^ 4 / (1 - 5 * HP.θ / 8) ^ 4

/-- The coefficient is independent of field, masks, requests and rate. -/
theorem coefficient_pos (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    0 < coefficient HP := by
  have hq := numerator_pos HP
  have hθ : 0 < 1 - 5 * HP.θ / 8 := by linarith [HP.θ_lt_θ₂, HP.θ₂_lt]
  have hr : (1 : ℝ) < 2 ^ (4⁻¹ : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  unfold coefficient
  positivity

/-- The true table is the actual stage-zero canonical input, for either input task. -/
theorem canonical_input (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ)
    (pilot : Bool) :
    (data (P := P) HP ka).canonicalPreparationInput pilot ⟨0, HP.k_pos⟩
      (request HP ka) = single 0 0 (rate ka) := by
  cases pilot
  · simp [BudgetData.canonicalPreparationInput, HierarchyParams.correctionInput,
      HierarchyParams.correctionIter, cutoffCorrectionIter, data]
  · simp [BudgetData.canonicalPreparationInput, PilotTask.value, pilotInput,
      pilotCorrection_zero, data]

/-- Both tables separately satisfy nonnegativity and the ordinary row-mass bound. -/
theorem both_substochastic (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ) :
    (∀ x y : ZMod P, 0 ≤ single 0 0 (rate ka) x y) ∧
    (∀ x : ZMod P, ∑ y : ZMod P, single 0 0 (rate ka) x y ≤ 1) ∧
    (∀ x y : ZMod P, 0 ≤ single 0 0 (5 * HP.θ * rate ka / 8) x y) ∧
    (∀ x : ZMod P, ∑ y : ZMod P, single 0 0 (5 * HP.θ * rate ka / 8) x y ≤ 1) := by
  have hf : rate ka ≤ 1 := by
    simpa only [rate, pow_zero, inv_one, one_pow] using rate_antitone (Nat.zero_le ka)
  have hc : 5 * HP.θ / 8 ≤ 1 := by linarith [HP.θ_lt_θ₂, HP.θ₂_lt]
  have ha : 5 * HP.θ * rate ka / 8 ≤ 1 := by
    calc
      _ = (5 * HP.θ / 8) * rate ka := by ring
      _ ≤ 1 * 1 := mul_le_mul hc hf (rate_pos ka).le (by norm_num)
      _ = 1 := one_mul 1
  have ha0 : 0 ≤ 5 * HP.θ * rate ka / 8 := by
    have ht := HP.θ_pos
    have hf0 := rate_pos ka
    positivity
  exact ⟨(entry_substochastic 0 0 (rate_pos ka).le hf).1,
    (entry_substochastic 0 0 (rate_pos ka).le hf).2,
    (entry_substochastic 0 0 ha0 ha).1,
    (entry_substochastic 0 0 ha0 ha).2⟩

/-- Actual normalized-root/ordinary-input error ratio; the common actual mask cancels. -/
theorem ratio (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ) :
    let X := fun σ x => (request (P := P) HP ka).source.retains (channels 1) σ x
    let U := fun σ y => (request (P := P) HP ka).usage.retains (channels 1) σ y
    rootDistPow 4 P (request (P := P) HP ka).source.rate X U
        (output HP ka ((data HP ka).incomingPreparation (request HP ka)
          (fun _ => single 0 0 (5 * HP.θ * rate ka / 8))))
        (output HP ka ((data HP ka).incomingPreparation (request HP ka)
          (fun _ => single 0 0 (rate ka)))) /
      rowNormPow 4 P (request (P := P) HP ka).source.rate X U
        (fun _ x y => single 0 0 (5 * HP.θ * rate ka / 8) x y -
          single 0 0 (rate ka) x y) = coefficient HP * (rate ka)⁻¹ ^ 4 := by
  dsimp only
  have ha : (data (P := P) HP ka).incomingPreparation (request HP ka)
      (fun _ => single 0 0 (5 * HP.θ * rate ka / 8)) = fun _ => single 0 0 (1 / 2) :=
    funext (incoming_half HP ka)
  have hg : (data (P := P) HP ka).incomingPreparation (request HP ka)
      (fun _ => single 0 0 (rate ka)) = fun _ => single 0 0 1 := funext (incoming_one HP ka)
  rw [ha, hg, output_moment, input_moment]
  have hα := (densityFactor_pos (P := P) ka).ne'
  have hf := (rate_pos ka).ne'
  have hθ : 1 - 5 * HP.θ / 8 ≠ 0 := by
    have h : 0 < 1 - 5 * HP.θ / 8 := by linarith [HP.θ_lt_θ₂, HP.θ₂_lt]
    exact h.ne'
  unfold coefficient
  field_simp

/-- The inverse-rate factor grows geometrically. -/
theorem inverse_rate_fourth (ka : ℕ) : (rate ka)⁻¹ ^ 4 = (65536 : ℝ) ^ ka := by
  rw [show (65536 : ℝ) = 2 ^ (16 : ℕ) by norm_num]
  simp only [rate, inv_pow, inv_inv, ← pow_mul]
  congr 1
  omega

/-- No fixed coefficient bounds this algebraic seam uniformly in terminal geometry.
The chosen exponent works over every prime, so a prime above any required horizon can
be selected afterwards. This is a decoder ratio, not failure of an evaluated estimator. -/
theorem ratio_unbounded (HP : FourthRootHierarchyParams 16 1 16 32 8) (C : ℝ) :
    ∃ ka : ℕ, ∀ (P : ℕ) [Fact P.Prime],
      let X := fun σ x => (request (P := P) HP ka).source.retains (channels 1) σ x
      let U := fun σ y => (request (P := P) HP ka).usage.retains (channels 1) σ y
      C < rootDistPow 4 P (request (P := P) HP ka).source.rate X U
          (output HP ka ((data HP ka).incomingPreparation (request HP ka)
            (fun _ => single 0 0 (5 * HP.θ * rate ka / 8))))
          (output HP ka ((data HP ka).incomingPreparation (request HP ka)
            (fun _ => single 0 0 (rate ka)))) /
        rowNormPow 4 P (request (P := P) HP ka).source.rate X U
          (fun _ x y => single 0 0 (5 * HP.θ * rate ka / 8) x y -
            single 0 0 (rate ka) x y) := by
  obtain ⟨ka, hk⟩ := pow_unbounded_of_one_lt (C / coefficient HP)
    (by norm_num : (1 : ℝ) < 65536)
  refine ⟨ka, ?_⟩
  intro P instP
  dsimp only
  rw [ratio, inverse_rate_fourth]
  have hh := (div_lt_iff₀ (coefficient_pos HP)).mp hk
  simpa only [mul_comm] using hh

/-- The actual production completion walk, with its original source and usage slices. -/
@[expose] def walkedPreparation (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (ka M : ℕ) (v : ℝ) : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
  conditionalWalk
    (X 0 (side P 0) (CopyPadding.identifier (1 : ZMod P) [1]))
    (Y 2 (side P ka) (CopyPadding.identifier (1 : ZMod P) [2, 3]))
    (graph 0 2 (by decide) (side P 0) (side P ka) (side_le P 0) (side_le P ka)
      (CopyPadding.identifier (1 : ZMod P) [1]) (CopyPadding.identifier (1 : ZMod P) [2, 3]))
    (fun _ _ => (data (P := P) HP ka).steps M (request (P := P) HP ka) 0)
    ((data HP ka).incomingPreparation (request HP ka) (fun _ => single 0 0 v))

/-- Completion exists algebraically for every budget; this does not assert RAW execution. -/
theorem complete_walked (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka M : ℕ)
    (v : ℝ) :
    (data (P := P) HP ka).complete M (request HP ka)
      ((data HP ka).incomingPreparation (request HP ka) (fun _ => single 0 0 v)) =
      some (walkedPreparation HP ka M v) := by
  exact BudgetData.complete_grid (data HP ka) M (request HP ka)
    0 2 (by decide) 0 ka [1] [2, 3] rfl rfl _ 0

/-- The decoder sees the stationary mean of the actual walk, not a mean premise. -/
theorem output_walked (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka M : ℕ)
    (v : ℝ) :
    output (P := P) HP ka (walkedPreparation HP ka M v) =
    output HP ka ((data HP ka).incomingPreparation (request HP ka)
      (fun _ => single 0 0 v)) := by
  funext σ x y
  unfold output
  have hr : Admissible (request (P := P) HP ka) :=
    ⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩
  apply correctionRequest_congr_normalizer (1 : ZMod P) id (request (P := P) HP ka) hr
  have hm := completed_mean HP ka M v _ (complete_walked HP ka M v) x y
  have hi : (data (P := P) HP ka).incomingPreparation (request HP ka)
      (fun _ => single 0 0 v) =
      fun _ => single 0 0 (polynomialPrepCutoff4 HP.θ (v / rate ka)) :=
    funext (incoming HP ka v)
  simpa only [id_eq, hi, slice_entry] using hm

/-- The same exact ratio holds after the actual preparation walks, at any two budgets. -/
theorem walked_ratio (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka M N : ℕ) :
    let X := fun σ x => (request (P := P) HP ka).source.retains (channels 1) σ x
    let U := fun σ y => (request (P := P) HP ka).usage.retains (channels 1) σ y
    rootDistPow 4 P (request (P := P) HP ka).source.rate X U
        (output HP ka (walkedPreparation HP ka M (5 * HP.θ * rate ka / 8)))
        (output HP ka (walkedPreparation HP ka N (rate ka))) /
      rowNormPow 4 P (request (P := P) HP ka).source.rate X U
        (fun _ x y => single 0 0 (5 * HP.θ * rate ka / 8) x y -
          single 0 0 (rate ka) x y) = coefficient HP * (rate ka)⁻¹ ^ 4 := by
  dsimp only
  rw [output_walked, output_walked]
  exact ratio HP ka

end Matrix.DecoderRateObstruction

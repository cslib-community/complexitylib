/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.InitialPilotScore
public import Complexity.Foundations.Probability.HierarchyCanonicalTargets
public import Complexity.Foundations.Probability.PilotDetectorTransport

/-!
# Initial detectors consuming allocated source-dependent scores

The child environment is reconstructed from the actual terminal split. Its source frame
and all spectators remain arguments of the score inside the detector's literal means.
They are integration variables, not independent seeds for successive calls. The true
reference uses the original score and detector recipes on the same stage channels.
This original finite single-bin construction does not close later pilot iterations,
bin sums, recursive growth or workspace bounds.

## Main definitions

* `environmentDetector`: direct evaluation with the full integrated child environment.
* `initialPilotDetector`: the detector consuming the actual completed RAW/score call.

## Main results

* `environmentDetector_row_moment`: width, rate and terminal-density payment.
* `initialPilotDetector_allocated`: payment derived from the computed dense input budget.
* `initialPilotDetector_accuracy`: calibrated allocation against the canonical true detector.
-/
public section
noncomputable section
open Finset Cslib Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- Evaluate a score on precisely the environment described by the integration variables.
The source rank resets to the terminal rate; roles and copy suffixes are preserved. -/
@[expose] def environmentDetector
    {V : Type} [Fintype V] {k : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P)) (hr : Admissible r)
    (A : Environment P J → Matrix V V ℝ) : V → ℝ :=
  PilotRowRecipe.sourceDetector HP.toHierarchyParams (stageSource D ident r hr)
    (splitTerminal D ident r) (fun s t => A ((terminalSplit r.terminal.role).symm (s, t)))

/-- Full-coordinate finite Fubini transports the literal detector payment. No
full-environment atom is extracted, and no child coordinate is discarded. -/
theorem environmentDetector_row_moment
    {V : Type} [Fintype V] {k : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P)) (hr : Admissible r)
    {N u π : ℝ} (hN : 0 < N) (hu : 0 < u) (hf : 0 < r.terminal.rate) (hπ : 0 < π)
    (hY : ∀ y, π ≤ (dens {t | splitTerminal D ident r t y} : ℝ))
    (A B : Environment P J → Matrix V V ℝ) :
    rowNormPow 4 N u
      (fun σ x => r.source.retains (channels D) σ (ident x))
      (fun σ y => r.terminal.retains (channels D) σ (ident y))
      (fun _ _ y => environmentDetector HP D ident r hr A y -
        environmentDetector HP D ident r hr B y) ≤
    (Fintype.card V : ℝ) * r.terminal.rate / (u * π) *
      rowNormPow 4 N r.terminal.rate
        (fun σ x => ({r.source with rate := r.terminal.rate}).retains
          (channels D) σ (ident x))
        (fun σ y => r.terminal.retains (channels D) σ (ident y))
        (fun σ x y => A σ x y - B σ x y) := by
  have h := PilotRowRecipe.sourceDetector_row_moment_transport HP.toHierarchyParams
    (stageSource D ident r hr) (splitTerminal D ident r)
    (fun σ x => r.source.retains (channels D) σ (ident x))
    (fun σ y => r.terminal.retains (channels D) σ (ident y))
    hN hu hf hπ hY
    (fun (_ : Environment P J) s t => A ((terminalSplit r.terminal.role).symm (s, t)))
    (fun (_ : Environment P J) s t => B ((terminalSplit r.terminal.role).symm (s, t)))
  apply h.trans_eq
  congr 1
  unfold rowNormPow
  congr 1
  rw [← univ_product_univ, expect_product]
  simp only [Fintype.expect_const]
  apply Fintype.expect_equiv (terminalSplit r.terminal.role).symm
  intro p
  simp [hr.1, stageSource, splitTerminal, terminalSplit, coordinate,
    CorrectionRowTask.Channel.retains, channels]

/-- The actual stage-zero detector request, retaining parent source and terminal metadata. -/
@[expose] def initialDetectorRequest
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (R : RoleProfile J)
    (ks kt : ℕ) (ss st : List (ZMod P)) : HierarchyTask.Request HP.k (Fin J) (ZMod P) :=
  ⟨.row 0 (.detector ⟨0, HP.k_pos⟩), gridChannel R.source ks ss,
    gridChannel R.terminal kt st, gridChannel R.terminal kt st⟩

omit [Fact P.Prime] in
/-- Distinct actual stage roles give an admissible detector request. -/
theorem initialDetectorRequest_admissible
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (R : RoleProfile J)
    (ks kt : ℕ) (ss st : List (ZMod P)) :
    Admissible (initialDetectorRequest HP R ks kt ss st) := ⟨R.source_terminal, rfl, rfl⟩

/-- The actual score request resets the entire source rate before completing RAW.
The original role, suffix, terminal and usage tuple are retained. -/
@[expose] def initialDetectorScoreRequest
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (R : RoleProfile J)
    (ks kt : ℕ) (ss st : List (ZMod P)) : HierarchyTask.Request HP.k (Fin J) (ZMod P) :=
  let r := initialDetectorRequest HP R ks kt ss st
  { r with
    task := .row 0 (.score ⟨0, HP.k_pos⟩)
    source := {r.source with rate := r.terminal.rate} }

omit [Fact P.Prime] in
/-- Resetting the score source preserves the actual stage roles and inherited suffixes. -/
theorem initialDetectorScoreRequest_eq
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (R : RoleProfile J)
    (ks kt : ℕ) (ss st : List (ZMod P)) :
    initialDetectorScoreRequest HP R ks kt ss st =
      ⟨.row 0 (.score ⟨0, HP.k_pos⟩), gridChannel R.source kt ss,
        gridChannel R.terminal kt st, gridChannel R.terminal kt st⟩ := rfl

/-- The true terminal density is derived from the actual padded frame channel.
No environment-atom lower bound is introduced. -/
theorem initialDetector_terminal_density (D : ZMod P) (kt : ℕ) (st : List (ZMod P)) :
    0 < ((side P kt : ℝ) / P) ^ 4 ∧
    ∀ y : ZMod P, (dens {t : FrameChannel P 4 1 |
      frameRetains P 4 (side P kt) t (CopyPadding.identifier D st y)} : ℝ) =
        ((side P kt : ℝ) / P) ^ 4 := by
  constructor
  · exact pow_pos (div_pos (by exact_mod_cast side_pos P kt (Fact.out : P.Prime).pos)
      (by exact_mod_cast (Fact.out : P.Prime).pos)) 4
  · intro y
    unfold frameRetains
    have he := congrArg (fun q : ℚ≥0 => (q : ℝ))
      (dens_eval_mem_retentionBox (P := P) (H := 4) (r := 1)
        (by decide) (side_le P kt) (CopyPadding.identifier D st y))
    push_cast at he
    simpa only [nnratCast_dens] using he

/-- The initial detector consumes the completed score on the very same integrated
frame. The score's source rate is reset to the stage rate before the lower call. -/
@[expose] def initialPilotDetector
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ) (steps : ℕ) : ZMod P → ℝ :=
  environmentDetector HP D id (initialDetectorRequest HP R ks kt ss st)
    (initialDetectorRequest_admissible HP R ks kt ss st)
    (initialPilotScore HP D R bin kt kt kb ss st cutoff h C steps)

omit [Fact P.Prime] in
/-- The score child is genuinely earlier than its detector in the hierarchy task order. -/
theorem initialPilotDetector_rank_lt (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (R : RoleProfile J) (ks kt : ℕ) (ss st : List (ZMod P)) :
    (initialDetectorScoreRequest HP R ks kt ss st).task.rank <
      (initialDetectorRequest HP R ks kt ss st).task.rank := by
  change (HierarchyTask.row (k := HP.k) 0 (.score ⟨0, HP.k_pos⟩)).rank <
    (HierarchyTask.row 0 (.detector ⟨0, HP.k_pos⟩)).rank
  apply HierarchyTask.rank_lt_of_mem_children
  simp [HierarchyTask.children, BoundedRowTask.children]

/-- True initial detector of the base, using the original unmodified score recipe.
The source reset and suffixes are the same as those used by the approximate call. -/
@[expose] def initialTrueDetector
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (ks kt : ℕ) (ss st : List (ZMod P)) (C : Matrix (ZMod P) (ZMod P) ℝ) :=
  let r := initialDetectorRequest HP R ks kt ss st
  PilotRowRecipe.detector HP.toHierarchyParams
    (stageSource D id r (initialDetectorRequest_admissible HP R ks kt ss st))
    (splitTerminal D id r)
    (PilotRowRecipe.score HP.toHierarchyParams (splitTerminal D id r) (rate kt) C)

set_option backward.isDefEq.respectTransparency false in
/-- The reference is the canonical true initial column detector, with the original
algorithm's cutoffs and rank. No source invariance of the approximate score is used. -/
theorem initialTrueDetector_eq_canonical
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (hD : D ≠ 0)
    (R : RoleProfile J) (ks kt : ℕ) (ss st : List (ZMod P))
    (C : Matrix (ZMod P) (ZMod P) ℝ) :
    initialTrueDetector HP D R ks kt ss st C =
      columnDetector (canonicalChannel id (rate kt)) (canonicalChannel id (rate kt))
        HP.ϕ HP.ρ HP.J HP.K (rate kt) C := by
  let r := initialDetectorRequest HP R ks kt ss st
  have he := stage_columnDetector_eq_canonical HP D id r
    (initialDetectorRequest_admissible HP R ks kt ss st) hD C
  change columnDetector (stageSource D id r
      (initialDetectorRequest_admissible HP R ks kt ss st)) (splitTerminal D id r)
      HP.ϕ HP.ρ HP.J HP.K (rate kt) C =
    columnDetector (canonicalChannel id (rate kt)) (canonicalChannel id (rate kt))
      HP.ϕ HP.ρ HP.J HP.K (rate kt) C at he
  funext y
  change min 1 (max 0 (columnDetector
    (stageSource D id r (initialDetectorRequest_admissible HP R ks kt ss st))
    (splitTerminal D id r) HP.ϕ HP.ρ HP.J HP.K (rate kt) C y)) = _
  rw [he]
  have h0 := columnDetector_nonneg (X := canonicalChannel id (rate kt))
    (Y := canonicalChannel id (rate kt)) (ϕ := HP.ϕ) (ρ := HP.ρ)
    (J := HP.J) (K := HP.K) (f := rate kt) (G := C) (y := y)
  have h1 := columnDetector_le_one (X := canonicalChannel id (rate kt))
    (Y := canonicalChannel id (rate kt)) (ϕ := HP.ϕ) (ρ := HP.ρ)
    (J := HP.J) (K := HP.K) (f := rate kt) (G := C) (y := y)
    HP.ϕ_nonneg HP.ϕ_le_one HP.ρ_le_one
  rw [max_eq_right h0, min_eq_right h1]

/-- A true score ignores the source spectators. The direct environment evaluation
therefore recovers the original detector exactly, without an invariance assumption
on the approximate score. -/
theorem environmentDetector_true
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (ks kt : ℕ) (ss st : List (ZMod P)) (C : Matrix (ZMod P) (ZMod P) ℝ) :
    environmentDetector HP D id (initialDetectorRequest HP R ks kt ss st)
      (initialDetectorRequest_admissible HP R ks kt ss st)
      (fun σ => PilotRowRecipe.score HP.toHierarchyParams
        (Y R.terminal (side P kt) (CopyPadding.identifier D st)) (rate kt) C σ) =
      initialTrueDetector HP D R ks kt ss st C := by
  let r := initialDetectorRequest HP R ks kt ss st
  have hy (rest : Spectators P J R.terminal) (t : FrameChannel P 4 1) :
      (fun w => Y R.terminal (side P kt) (CopyPadding.identifier D st)
        ((terminalSplit R.terminal).symm (rest, t)) w) = splitTerminal D id r t := by
    funext w
    simp [r, initialDetectorRequest, splitTerminal, coordinate, gridChannel,
      semanticSide_grid, Y, terminalSplit]
  change PilotRowRecipe.sourceDetector HP.toHierarchyParams _ _ _ = _
  have he : (fun rest t => PilotRowRecipe.score HP.toHierarchyParams
      (Y R.terminal (side P kt) (CopyPadding.identifier D st)) (rate kt) C
      ((terminalSplit R.terminal).symm (rest, t))) =
      (fun (_ : Spectators P J R.terminal) t =>
        PilotRowRecipe.score HP.toHierarchyParams (splitTerminal D id r) (rate kt) C t) := by
    funext rest t
    change atomPrep HP.ϕ HP.ρ HP.K (rate kt) C _ = atomPrep HP.ϕ HP.ρ HP.K (rate kt) C _
    exact congrArg (fun f : ZMod P → Prop =>
      atomPrep HP.ϕ HP.ρ HP.K (rate kt) C {w | f w}) (hy rest t)
  exact congrArg (PilotRowRecipe.sourceDetector HP.toHierarchyParams
    (stageSource D id r (initialDetectorRequest_admissible HP R ks kt ss st))
    (splitTerminal D id r)) he

set_option backward.isDefEq.respectTransparency false in
/-- The dense input budget is allocated before either completed child is called.
Accuracy of the actual detector follows from RAW contraction and score stability,
not from a score/detector error premise. The visible payment is width times the
stage/parent source-rate ratio divided by actual terminal density. One covering
bin and equal bin/stage terminal rates are the explicit mathematical boundary. -/
theorem initialPilotDetector_allocated
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ L : ℝ, 0 ≤ L ∧
    ∀ (P J : ℕ) [Fact P.Prime] (D : ZMod P), D ≠ 0 →
    ∀ (R : RoleProfile J) (H : Horizon P) (bin ks kt : ℕ),
    kt ≤ H.maxExponent →
    ∀ (ss st : List (ZMod P)) (cutoff h : ℝ → ℝ)
      (C : Matrix (ZMod P) (ZMod P) ℝ),
    (∀ v, cutoff v ≠ 0 → h v = 1) →
    ∀ η : ℝ, 0 < η → (∀ v, v ≤ η → HP.ρ v = 1) →
    2 * (1 + 32 / η) ≤ HP.K →
    (∀ x y, 0 ≤ C x y) → C *ᵥ 1 ≤ 1 →
    (∀ x y, rate kt * cutoff (C x y / rate kt) = C x y) →
    ∀ π : ℝ, 0 < π →
    (∀ y, π ≤ (dens {t : FrameChannel P 4 1 | frameRetains P 4 (side P kt) t
      (CopyPadding.identifier D st y)} : ℝ)) →
    ∀ ε : ℝ, 0 < ε →
    let steps := initialPilotSteps HP L D R bin kt kt kt ss st cutoff h C ε
    0 < steps ∧
    rowNormPow 4 P (rate ks)
      (X R.source (side P ks) (CopyPadding.identifier D ss))
      (Y R.terminal (side P kt) (CopyPadding.identifier D st))
      (fun _ _ y => initialPilotDetector HP D R bin ks kt kt ss st cutoff h C steps y -
        initialTrueDetector HP D R ks kt ss st C y) ≤
      (P : ℝ) * rate kt / (rate ks * π) * ε ^ 4 := by
  obtain ⟨L, hL, ha⟩ := initialPilotScore_allocated_of_single_bin HP
  refine ⟨L, hL, ?_⟩
  intro P J inst D hD R H bin ks kt hkt ss st cutoff h C hkh η hη hρη hK hC hC1
    hcover π hπ hY ε hε steps
  refine ⟨initialPilotSteps_pos HP L D R bin kt kt kt ss st cutoff h C ε, ?_⟩
  let r := initialDetectorRequest HP R ks kt ss st
  let hr := initialDetectorRequest_admissible HP R ks kt ss st
  let Yt := Y R.terminal (side P kt) (CopyPadding.identifier D st)
  let A := initialPilotScore HP D R bin kt kt kt ss st cutoff h C steps
  let B := fun σ => PilotRowRecipe.score HP.toHierarchyParams Yt (rate kt) C σ
  have he := environmentDetector_row_moment HP D id r hr
    (N := P) (u := rate ks) (π := π)
    (by exact_mod_cast (Fact.out : Nat.Prime P).pos) (rate_pos ks) (rate_pos kt) hπ
    (by simpa only [r, initialDetectorRequest, splitTerminal, coordinate,
      gridChannel, semanticSide_grid, Y, id_eq] using hY) A B
  have hb := environmentDetector_true HP D R ks kt ss st C
  have hs := ha P J D hD R H bin kt kt hkt hkt ss st cutoff h C hkh η hη hρη hK hC hC1
    hcover ε hε
  dsimp only at hs
  change environmentDetector HP D id r hr B = _ at hb
  rw [hb] at he
  simp only [r, initialDetectorRequest, CorrectionRowTask.Channel.retains,
    channels, gridChannel, semanticSide_grid, id_eq, ZMod.card] at he
  change rowNormPow 4 P (rate ks)
      (X R.source (side P ks) (CopyPadding.identifier D ss)) Yt
      (fun _ _ y => initialPilotDetector HP D R bin ks kt kt ss st cutoff h C steps y -
        initialTrueDetector HP D R ks kt ss st C y) ≤ _
  have hs' : rowNormPow 4 P (rate kt)
      (fun σ x => frameRetains P 4 (side P kt) (σ R.source) (CopyPadding.identifier D ss x))
      (fun σ y => frameRetains P 4 (side P kt) (σ R.terminal) (CopyPadding.identifier D st y))
      (fun σ x y => A σ x y - B σ x y) ≤ ε ^ 4 := by
    convert hs using 1; dsimp only [rowNormPow, A, B, Yt, X, Y]; congr 3
    funext σ
    apply sum_congr (by ext x; simp only [mem_filter, mem_univ, true_and])
    intro x hx
    apply sum_congr (by ext y; simp only [mem_filter, mem_univ, true_and])
    intro y hy
    rfl
  convert he.trans (mul_le_mul_of_nonneg_left hs'
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (rate_pos kt).le)
      (mul_pos (rate_pos ks) hπ).le)) using 1;
      dsimp only [rowNormPow, initialPilotDetector, A, r, initialDetectorRequest, X, Y, Yt];
      congr 3
  funext σ
  apply sum_congr (by ext x; simp only [mem_filter, mem_univ, true_and])
  intro x hx
  apply sum_congr (by ext y; simp only [mem_filter, mem_univ, true_and])
  intro y hy
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- Calibrate the RAW tolerance by the explicit detector payment before making the
completed calls. The resulting detector has any requested positive fourth-root accuracy. -/
theorem initialPilotDetector_accuracy
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ L : ℝ, 0 ≤ L ∧
    ∀ (P J : ℕ) [Fact P.Prime] (D : ZMod P), D ≠ 0 →
    ∀ (R : RoleProfile J) (H : Horizon P) (bin ks kt : ℕ),
    kt ≤ H.maxExponent →
    ∀ (ss st : List (ZMod P)) (cutoff h : ℝ → ℝ)
      (C : Matrix (ZMod P) (ZMod P) ℝ),
    (∀ v, cutoff v ≠ 0 → h v = 1) →
    ∀ η : ℝ, 0 < η → (∀ v, v ≤ η → HP.ρ v = 1) →
    2 * (1 + 32 / η) ≤ HP.K →
    (∀ x y, 0 ≤ C x y) → C *ᵥ 1 ≤ 1 →
    (∀ x y, rate kt * cutoff (C x y / rate kt) = C x y) →
    ∀ π : ℝ, 0 < π →
    (∀ y, π ≤ (dens {t : FrameChannel P 4 1 | frameRetains P 4 (side P kt) t
      (CopyPadding.identifier D st y)} : ℝ)) →
    ∀ ε : ℝ, 0 < ε →
    let payment := (P : ℝ) * rate kt / (rate ks * π)
    let tolerance := ε / (1 + payment)
    let steps := initialPilotSteps HP L D R bin kt kt kt ss st cutoff h C tolerance
    0 < steps ∧
    rowNormPow 4 P (rate ks)
      (X R.source (side P ks) (CopyPadding.identifier D ss))
      (Y R.terminal (side P kt) (CopyPadding.identifier D st))
      (fun _ _ y => initialPilotDetector HP D R bin ks kt kt ss st cutoff h C steps y -
        initialTrueDetector HP D R ks kt ss st C y) ≤
      ε ^ 4 := by
  obtain ⟨L, hL, ha⟩ := initialPilotDetector_allocated HP
  refine ⟨L, hL, ?_⟩
  intro P J inst D hD R H bin ks kt hkt ss st cutoff h C hkh η hη hρη hK hC hC1
    hcover π hπ hY ε hε payment tolerance steps
  have hc : 0 ≤ payment := div_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (rate_pos kt).le) (mul_pos (rate_pos ks) hπ).le
  have hden : 0 < 1 + payment := by linarith
  have ht : 0 < tolerance := div_pos hε hden
  obtain ⟨hs, he⟩ := ha P J D hD R H bin ks kt hkt ss st cutoff h C hkh η hη hρη hK hC hC1
    hcover π hπ hY tolerance ht
  refine ⟨hs, he.trans ?_⟩
  exact calibrated_fourth_moment hc hε

end Matrix.HierarchyParams.H4RankEnvironment

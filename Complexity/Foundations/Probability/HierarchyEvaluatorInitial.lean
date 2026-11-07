/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyInitialUniform

/-!
# Actual initial constructors of the shared evaluator

The initial actual input and initial pilot input use the same zero-correction RAW recipe.
Their constructor ranks still determine their own precisions and walk lengths. The final
initial history is the actual returned row, rather than an independent family of estimates.
The deterministic deficit and unconditional noise payment therefore apply to these calls.

This is an initial RAW contract, not the simultaneous compressed lower-budget invariant.
The dense leaves are still exact semantic leaves; replacing them by the compressed consumer
requires a changing-request induction and explicit growth/reserve payments.

## Main results

* `evaluate_lower_dense_contract`: all positive lower-budget dense seeds on their own masks.
* `evaluate_initial_prefix`: the executed initial row is its actual final prefix.
* `evaluate_initial_absolute_moment`: canonical error paid by the actual deficit and noise.
* `evaluate_score_child`: actual lower-budget score assembly and its full-rank error payment.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.Probability Cslib.RowCompression NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- Simultaneous seed contract for every actual positive lower-budget dense call, with
changing requests and bins. The target is the constructor's genuine dense normalization;
range, usage support, terminal-rank sparsity and both rooted moments hold together. This
covers the exact dense leaves only, not later recursive normalized constructors. -/
theorem evaluate_lower_dense_contract (M : ℕ) :
    ∀ m < M, 0 < m → ∀ (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (bin : ℕ),
      r.task = .baseNormalized 0 bin → Admissible r →
      ∀ e g : ℝ, 0 ≤ e → g ≤ e →
      (∀ d, d ≤ e → B.cutoff bin d = 0) → (∀ q, g ≤ q → HP.ρ q = 0) →
      ∃ A, (if m < M then B.evaluate m r else none) = some (.row A) ∧
        A = denseChild B.padding id r (B.cutoff bin) (B.auxiliary bin) HP.ρ HP.K B.base ∧
        (∀ σ x y, A σ x y ∈ Set.Icc 0 (2 * B.binCap)) ∧
        (∀ σ x y, ¬ r.usage.retains (channels B.padding) σ y → A σ x y = 0) ∧
        (∀ σ x, #{y ∈ ({y | r.terminal.retains (channels B.padding) σ y} : Finset _) |
          A σ x y ≠ 0} < HP.K) ∧
        rootDistPow 4 P r.source.rate
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.usage.retains (channels B.padding) σ y) A
          (denseChild B.padding id r (B.cutoff bin) (B.auxiliary bin) HP.ρ HP.K B.base) = 0 ∧
        rootDistPow 4 P r.source.rate
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.terminal.retains (channels B.padding) σ y) A
          (denseChild B.padding id r (B.cutoff bin) (B.auxiliary bin) HP.ρ HP.K B.base) = 0 := by
  intro m hm hm0 r bin hr ha e g he hge hc hg
  let A := denseChild B.padding id r (B.cutoff bin) (B.auxiliary bin) HP.ρ HP.K B.base
  have hout := B.evaluate_dense_eq_output m bin hm0 r hr ha (by norm_num : (0 : ℝ) < 1)
  rw [B.evaluate_dense m bin hm0 r hr] at hout
  have heq := BudgetValue.row.inj (Option.some.inj hout)
  refine ⟨A, by rw [ite_eq_left hm]; exact B.evaluate_dense m bin hm0 r hr, rfl, ?_, ?_, ?_,
    rootDistPow_self (by decide) _, rootDistPow_self (by decide) _⟩
  · exact fun σ x y => normalizedRequest_mem_Icc HP B.padding r (B.cutoff bin)
      B.binCap_nonneg (B.cutoff_bounds bin) (fun _ => B.base)
      (densePreparation B.padding id r (B.auxiliary bin) HP.ρ HP.K B.base) σ x y
  · intro σ x y hy
    change denseChild _ _ _ _ _ _ _ _ _ _ _ = 0
    rw [heq]
    exact ite_eq_right hy
  · intro σ x
    change #{y ∈ ({y | r.terminal.retains (channels B.padding) σ y} : Finset _) |
      denseChild _ _ _ _ _ _ _ _ _ _ _ ≠ 0} < HP.K
    rw [heq]
    let a : State (ZMod P) := ⟨0, requestSignals 1 B.padding id r (fun _ => B.base)
      (densePreparation B.padding id r (B.auxiliary bin) HP.ρ HP.K B.base) σ x⟩
    apply lt_of_le_of_lt (card_le_card ?_)
      (FourthRootHierarchyParams.NormalizedRow.support_of_cutoff _ _
        (FourthRootHierarchyParams.NormalizedRow.rank_pos HP) he hge hc hg
        {y | r.terminal.retains (channels B.padding) σ y} a 1)
    intro y hy
    simp only [mem_filter] at hy ⊢
    refine ⟨hy.1, ?_⟩
    split_ifs at hy with hu
    · exact hy.2
    · exact (hy.2 rfl).elim

/-- Both initial inputs return the final prefix of their own actual history. Full terminal
usage is explicit: a usage-narrowed RAW walk cannot be identified with this history. -/
theorem evaluate_initial_prefix (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (pilot : Bool)
    (hr : r.task = .row 0 (if pilot then .pilotInput ⟨0, HP.k_pos⟩ else
      .input ⟨0, HP.k_pos⟩))
    (hu : r.usage = r.terminal) (hp : 0 < B.requestPrecision M r)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hF : B.initialPrefixes M r = some F) :
    B.evaluate M r = some (.row (F (Nat.log2 M + 1))) := by
  have hreq : { r with usage := r.terminal } = r := by cases r; simp_all
  unfold initialPrefixes at hF
  rw [hreq] at hF
  cases hg : (List.range (Nat.log2 M + 1)).mapM (fun j =>
      B.completedGroup (fun m q => if m < M then B.evaluate m q else none) M
        (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩) r) with
  | none => simp [hg] at hF
  | some groups =>
    simp only [hg, bind, Option.bind_some, pure] at hF
    have hlen : groups.length = Nat.log2 M + 1 := by
      have := (List.mapM_eq_some_iff_forall₂.mp hg).length_eq
      simpa only [List.length_range] using this.symm
    have htake : groups.take (Nat.log2 M + 1) = groups := by
      rw [← hlen, List.take_length]
    have he := Option.some.inj hF
    subst F
    rw [B.evaluate_eq, step, hr]
    cases pilot <;>
      simp only [Bool.false_eq_true, ↓reduceIte, hp, raw, hg, bind, Option.bind_some,
        pure, htake] <;> rfl

/-- Actual initial RAW error on its own source and full terminal rank. Availability and
the actual history are constructed. The target is the stage-zero matrix C = C + 0*C; the RHS
retains omitted/inactive/coarse deficits and correlated completion noise. No desired parent
error or lower-call oracle is supplied. -/
theorem evaluate_initial_absolute_moment (M : ℕ) (hM : 0 < M) (n : ℕ)
    (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
    (hD : B.padding ≠ 0) (H : Horizon P) (hn : n ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (pilot : Bool)
    (hr : r.task = .row 0 (if pilot then .pilotInput ⟨0, HP.k_pos⟩ else
      .input ⟨0, HP.k_pos⟩))
    (hu : r.usage = r.terminal) (hp : 0 < B.requestPrecision M r)
    (R : RoleProfile 3) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st) (hks : ks ≤ H.maxExponent)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1) :
    ∃ A, B.evaluate M r = some (.row A) ∧
      rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (side P ka) B.padding st)
        (fun σ x y => A σ x y - B.base x y) ≤
      8 * (((2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) *
        (64 / 63) * (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) (Nat.log2 M)) ^ 4 +
        rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ka) B.padding st)
          (fun _ => B.initialPolynomialLoss M n (Nat.log2 M) r)) := by
  have hne : B.bins.Nonempty := by rw [hbins]; exact ⟨0, mem_range.mpr (by omega)⟩
  obtain ⟨hF, _⟩ := B.initialPrefixes_grid M hM hne r R.source R.terminal
    R.source_terminal ks ka ss st hs ht
  refine ⟨_, B.evaluate_initial_prefix M r pilot hr hu hp _ hF, ?_⟩
  exact B.initialPrefix_absolute_moment M hM n hbins hrate hcutoff haux hD H hn r R ks ka
    ss st hs ht hks hC hC1 _ hF (Nat.log2 M) (by omega)

/-- A genuine successor consumes only an actual strictly lower-budget row call. The
score's reference target and full-rank payment use that child's same environment and masks;
no parent-error bound is an input. The width and inverse-rate costs remain explicit. -/
theorem evaluate_score_child (M : ℕ) (hM : 0 < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (i : Fin HP.k)
    (hr : r.task = .row 0 (.score i)) (hp : 0 < B.requestPrecision M r)
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : B.evaluate (B.childBudget M) { r with task := .row 0 (.pilotInput i) } =
      some (.row A)) :
    B.evaluate M r = some (.row (fun σ => PilotRowRecipe.score HP.toHierarchyParams
      (fun τ y => r.terminal.retains (channels B.padding) τ y) r.terminal.rate (A σ) σ)) ∧
    B.childBudget M < M ∧
    (HierarchyTask.row 0 (.pilotInput i)).rank < r.task.rank ∧
    ∀ (G : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (Lϕ Lρ : ℝ),
      0 ≤ Lϕ → 0 ≤ Lρ → 0 < r.terminal.rate → 0 ≤ (P : ℝ) * r.source.rate →
      (∀ a b, |HP.ϕ a - HP.ϕ b| ≤ Lϕ * |a - b|) →
      (∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|) →
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun σ x y => PilotRowRecipe.score HP.toHierarchyParams
            (fun τ y => r.terminal.retains (channels B.padding) τ y) r.terminal.rate (A σ) σ x y -
          PilotRowRecipe.score HP.toHierarchyParams
            (fun τ y => r.terminal.retains (channels B.padding) τ y) r.terminal.rate (G σ) σ x y) ≤
        P * ((Lϕ + Lρ) / r.terminal.rate) ^ 4 *
          rowNormPow 4 P r.source.rate
            (fun σ x => r.source.retains (channels B.padding) σ x)
            (fun σ y => r.terminal.retains (channels B.padding) σ y)
            (fun σ x y => A σ x y - G σ x y) := by
  constructor
  · rw [B.evaluate_eq, step, hr]
    simp only [hp, ↓reduceIte, row, B.childBudget_lt hM, hA, Option.bind_some,
      BudgetValue.row?]
    rfl
  · refine ⟨B.childBudget_lt hM, ?_, ?_⟩
    · rw [hr]
      exact HierarchyTask.rank_lt_of_mem_children (by
        simp [HierarchyTask.children, BoundedRowTask.children])
    intro G Lϕ Lρ hLϕ hLρ hf hNu hϕ hρ
    simpa only [ZMod.card] using PilotRowRecipe.score_row_moment HP.toHierarchyParams
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      HP.ρ_nonneg hLϕ hLρ hϕ hρ
      (FourthRootHierarchyParams.NormalizedRow.rank_pos HP) hf hNu A G

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData

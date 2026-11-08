/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.MoserTardos
import Cslib.Probability.PMF

/-! The Moser–Tardos algorithmic local lemma: a satisfiable instance of its hypothesis on one fair
coin, where the expectation bound of Theorem 1.2 is attained (the number of resamplings is
geometric with mean `1`). Also a degenerate instance with an impossible event and `x = 0`, an
instance where the hypothesis must fail because every assignment hits some event, and a concrete
valid log on a fixed table with its witness tree computed by `decide`. -/

namespace ComplexityTests.MoserTardos

open Cslib.Probability.MoserTardos MeasureTheory
open scoped ENNReal

/-- A fair coin. -/
noncomputable def coin : Unit → Measure Bool :=
  fun _ => (Cslib.Probability.PMF.uniformOfFintype Bool).toMeasure

instance (u : Unit) : IsProbabilityMeasure (coin u) := by
  unfold coin
  infer_instance

/-- The variable sets: the single event reads the single variable. -/
def vbl : Unit → Finset Unit := fun _ => {()}

/-- Selection rules for a table of coin samples. -/
abbrev Rule := (∀ p : Unit × ℕ, (fun _ : Unit => Bool) p.1) → List Unit → Option Unit

/-- The event "the coin shows `b`", on the single variable `()`. -/
def shows (b : Bool) : Set (Unit → Bool) := {σ | σ () = b}

theorem measurableSet_shows (b : Bool) : MeasurableSet (shows b) :=
  show MeasurableSet ((fun σ : Unit → Bool => σ ()) ⁻¹' {b}) from
    measurable_pi_apply () (measurableSet_singleton b)

theorem shows_dependsOn (b : Bool) :
    DependsOn (· ∈ shows b) (({()} : Finset Unit) : Set Unit) :=
  fun σ τ h => by
    simp only [shows, Set.mem_ofPred_eq]
    rw [h () (by simp)]

theorem measureReal_shows (b : Bool) : (Measure.pi coin).real (shows b) = 1 / 2 := by
  have hset : shows b = Set.univ.pi fun _ : Unit => ({b} : Set Bool) := by
    ext σ
    simp only [shows, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, Set.mem_singleton_iff,
      forall_const]
    exact ⟨fun h _ => h, fun h => h ()⟩
  rw [measureReal_def, hset, Measure.pi_pi, Fintype.prod_unique, coin,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b),
    Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_bool]
  norm_num

/-! ### One fair coin, one event: the bound `x / (1 - x) = 1` holds with equality -/

-- With `x = 1/2` and no neighbours, `Pr[A] = 1/2 ≤ x`: the hypothesis holds.
theorem hyp : ∀ _ : Unit, (Measure.pi coin).real (shows true) ≤
    (1 / 2 : ℝ) * ∏ j ∈ (∅ : Finset Unit), (1 - (fun _ => (1 / 2 : ℝ)) j) :=
  fun _ => by rw [measureReal_shows, Finset.prod_empty, mul_one]

example {sel : Rule}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ shows true) :
    ∫⁻ T, resamplings (α := fun _ : Unit => Bool) sel () T ∂table coin ≤ 1 := by
  refine (lintegral_resamplings_le coin vbl (fun _ => shows true)
    (fun _ => measurableSet_shows true) (fun _ => shows_dependsOn true) (fun _ => ∅)
    (fun i j h => absurd (Subsingleton.elim j i) h) (x := fun _ => 1 / 2)
    (fun _ => ⟨by norm_num, by norm_num⟩) hyp hsel ()).trans (le_of_eq ?_)
  norm_num

-- Almost surely the greedy run reaches tails.
example : ∀ᵐ T ∂table coin, ∃ n, ∀ _ : Unit,
    current vbl T (run (greedy vbl fun _ => shows true) T n) ∉
      shows true :=
  ae_exists_forall_notMem_run_greedy coin vbl (fun _ => shows true)
    (fun _ => measurableSet_shows true) (fun _ => shows_dependsOn true) (fun _ => ∅)
    (fun i j h => absurd (Subsingleton.elim j i) h) (x := fun _ => 1 / 2)
    (fun _ => ⟨by norm_num, by norm_num⟩) hyp

/-! ### An impossible event with `x = 0`: no resamplings in expectation -/

example {sel : Rule}
    (hsel : ∀ T w i, sel T w = some i →
      current (fun _ : Unit => (∅ : Finset Unit)) T w ∈ (∅ : Set (Unit → Bool))) :
    ∫⁻ T, resamplings (α := fun _ : Unit => Bool) sel () T ∂table coin ≤ 0 := by
  refine (lintegral_resamplings_le coin (fun _ : Unit => (∅ : Finset Unit))
    (fun _ => (∅ : Set (Unit → Bool))) (fun _ => MeasurableSet.empty)
    (fun _ _ _ _ => rfl) (fun _ => ∅) (fun i j h => absurd (Subsingleton.elim j i) h)
    (x := fun _ => 0) (fun _ => ⟨le_rfl, by norm_num⟩) (fun _ => by simp) hsel ()).trans
    (le_of_eq ?_)
  simp

/-! ### The hypothesis fails when the events cover every assignment -/

-- "Heads" and "tails" on the same coin: every assignment hits one of them, so no `x`, `Γ` can
-- satisfy the hypothesis (`Pr = 1/2` would need `x (1 - x) ≥ 1/2`, impossible).
example (Γ : Bool → Finset Bool) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (({()} : Finset Unit))
      ({()} : Finset Unit) → j ∈ Γ i) (x : Bool → ℝ) (hx : ∀ i, x i ∈ Set.Ico 0 1) :
    ¬∀ i, (Measure.pi coin).real (shows i) ≤ x i * ∏ j ∈ Γ i, (1 - x j) := fun hP => by
  obtain ⟨σ, hσ⟩ := exists_forall_notMem coin (fun _ : Bool => ({()} : Finset Unit)) shows
    measurableSet_shows
    (fun b => shows_dependsOn b) Γ hΓ hx hP
  exact hσ (σ ()) rfl

/-! ### A concrete log and its witness tree -/

/-- Three events on two variables: `0` reads `x₀`, `1` reads both, `2` reads `x₁`. -/
def vbl3 : Fin 3 → Finset (Fin 2)
  | 0 => {0}
  | 1 => {0, 1}
  | 2 => {1}

/-- Event `i`: every variable of `vbl3 i` is `true`. -/
def allTrue (i : Fin 3) : Set (Fin 2 → Bool) := {σ | ∀ v ∈ vbl3 i, σ v = true}

theorem allTrue_dependsOn (i : Fin 3) : DependsOn (· ∈ allTrue i) (vbl3 i : Set (Fin 2)) :=
  fun σ τ h => by
    simp only [allTrue, Set.mem_ofPred_eq]
    exact propext (forall₂_congr fun v hv => by rw [h v (Finset.mem_coe.2 hv)])

/-- The first two samples of each variable are `true`, the later ones `false`. -/
def tbl : ∀ p : Fin 2 × ℕ, (fun _ : Fin 2 => Bool) p.1 := fun p => decide (p.2 < 2)

-- The log "resample `2`, then `1`, then `0`" (latest first) is valid on `tbl`.
theorem isLog_tbl : IsLog vbl3 allTrue tbl [0, 1, 2] := by
  simp [isLog_cons, isLog_nil, allTrue, current_apply, uses, vbl3, tbl]

-- Afterwards no event occurs.
example : ∀ i, current vbl3 tbl [0, 1, 2] ∉ allTrue i := by
  intro i
  fin_cases i <;> simp [allTrue, current_apply, uses, vbl3, tbl]

-- The witness tree of the latest step is the path `0 — 1 — 2`, and it is proper.
theorem witness_tbl : witness vbl3 0 [1, 2] = {(0, 0), (1, 1), (2, 2)} := by decide

example : Proper vbl3 (witness vbl3 0 [1, 2]) := proper_witness vbl3 0 [1, 2]

-- A step that shares no variable with the root is not attached.
example : witness vbl3 0 [2] = {(0, 0)} := by decide

-- The coupling: the witness tree passes its check on `tbl`.
example : Check vbl3 allTrue {(0, 0), (1, 1), (2, 2)} tbl :=
  witness_tbl ▸ check_witness vbl3 allTrue allTrue_dependsOn 0 [1, 2] tbl isLog_tbl

end ComplexityTests.MoserTardos

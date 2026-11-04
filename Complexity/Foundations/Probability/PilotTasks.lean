/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyParams
public import Complexity.Foundations.Probability.StochasticAtom
public import Complexity.Foundations.Probability.EstimatorSchedule

/-!
# Concrete pilot tasks and their dependency order

The pilot family of [OpenAI2026LogSpace, Sections 7.1–7.2, printed pp. 33–35], revision
`7ef5c0cc`, is indexed here by its actual input, score row, detector vector, running maximum
and correction. `PilotTask.value` uses the existing `pilotInput`, `atomPrep`, `columnDetector`,
`pilotMax` and `pilotCorrection`; it introduces no alternative hierarchy. The score is the
unnormalized detector score of Section 5.4, not a dense atom with a clipped denominator.

`PilotTask.children` specifies the constructor recipes. Ranks are computed from the iteration
and constructor, never supplied by a caller. Their strict decrease supplies the rank premise
of the existing fourth-moment precision calculation. The stage-local iteration bound is explicit;
this is not yet the global stage order or a recursive estimator. The stochastic extension is in
`Complexity/Foundations/Probability/PilotRowTasks.lean`; routed bins, copy/reward multipliers
and full mean-prefix assembly remain open.

The exact finite detector mean is independent of the fourth/eighth moment choice. The precision
client specializes to fourth moments and uses the existing integer logarithmic-rate schedule.

## Main definitions

* `Matrix.HierarchyParams.PilotTask`: the pilot constructor family.
* `Matrix.HierarchyParams.PilotTask.value`: the existing pilot values indexed by constructor.
* `Matrix.HierarchyParams.PilotTask.inputRequests`: the direct and product child calls.

## Main results

* `Matrix.HierarchyParams.PilotTask.rank_lt_of_mem_children`: strict constructor decrease.
* `Matrix.HierarchyParams.PilotTask.value_detector`: the exact detector mean.
* `Matrix.HierarchyParams.PilotTask.input_request_cost_le`: scheduled precision for actual calls.
-/

public section

universe u

open Finset
open scoped BigOperators

namespace Matrix.HierarchyParams

/-- The complete deterministic pilot family at one stage. `input i` is the input of step `i+1`;
`detector i` measures that input; `maximum i` and `correction i` are the completed step `i`. -/
inductive PilotTask where
  | base
  | input (i : ℕ)
  | score (i : ℕ)
  | detector (i : ℕ)
  | maximum (i : ℕ)
  | correction (i : ℕ)
  deriving DecidableEq

namespace PilotTask

/-- Immediate inputs used by the actual constructor equations. Zero-step values are exact bases. -/
@[expose] def children : PilotTask → List PilotTask
  | .base => []
  | .input i => [.base, .correction i]
  | .score i => [.input i]
  | .detector i => [.score i]
  | .maximum 0 => []
  | .maximum (i + 1) => [.maximum i, .detector i]
  | .correction 0 => []
  | .correction (i + 1) => [.input i, .maximum (i + 1)]

/-- Positive constructor rank, with five slots per completed pilot step. -/
@[expose] def rank : PilotTask → ℕ
  | .base => 1
  | .input i => 5 * i + 3
  | .score i => 5 * i + 4
  | .detector i => 5 * i + 5
  | .maximum i => 5 * i + 1
  | .correction i => 5 * i + 2

/-- Every recursive input is strictly earlier, including the current maximum used by correction. -/
theorem rank_lt_of_mem_children {parent child : PilotTask} (h : child ∈ parent.children) :
    child.rank < parent.rank := by
  cases parent with
  | base => simp [children] at h
  | input i => simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
               rcases h with rfl | rfl <;> simp only [rank] <;> omega
  | score i => simp only [children, List.mem_singleton] at h; subst child; simp [rank]
  | detector i => simp only [children, List.mem_singleton] at h; subst child; simp [rank]
  | maximum i =>
    cases i with
    | zero => simp [children] at h
    | succ i =>
      simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> simp only [rank] <;> omega
  | correction i =>
    cases i with
    | zero => simp [children] at h
    | succ i =>
      simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> simp only [rank] <;> omega

/-- Iteration label, for bounding the number of ranks at a stage. -/
@[expose] def iteration : PilotTask → ℕ
  | .base => 0
  | .input i | .score i | .detector i | .maximum i | .correction i => i

/-- The finite pilot has at most a constant number of rank slots per iteration. -/
theorem rank_le {t : PilotTask} {k : ℕ} (h : t.iteration ≤ k) : t.rank ≤ 5 * k + 5 := by
  cases t <;> simp only [iteration, rank] at * <;> omega

/-- Row tasks, sampled score rows and vertex tasks have their actual distinct argument types. -/
abbrev Value (V κ : Type u) : PilotTask → Type _
  | .score _ => κ → Matrix V V ℝ
  | .detector _ | .maximum _ => V → ℝ
  | _ => Matrix V V ℝ

/-- Constructor decrease discharges the rank payment in the scheduled fourth-moment bound.
Rates may change, and the child may restart on a broader source domain. -/
theorem scheduled_child_cost_le {parent child : PilotTask} (hchild : child ∈ parent.children)
    {A a a' u u' : ℝ} (hA : 0 ≤ A) (M d c : ℕ) (hc : 0 < c) (h : ℤ)
    (ha : 0 < a) (ha' : 0 < a') (hu : 0 < u) (huu' : u ≤ u')
    (hscale : Real.logb 2 (a' / a) = (h : ℝ)) :
    Cslib.LogSpaceEstimation.binNormCost 4 (h : ℝ) *
        (2 : ℝ) ^ (Real.logb 2 (u' / u) / 4) *
        (2 : ℝ) ^ (-Cslib.LogSpaceEstimation.precision (16 * c) A
          (Cslib.LogSpaceEstimation.lastBudget M d c h) child.rank a' u') ≤
      (2 : ℝ) ^ (-Cslib.LogSpaceEstimation.precision (16 * c) A M parent.rank a u - A +
        (d : ℝ) / (16 * c) + 1 / 16) * Cslib.LogSpaceEstimation.scaleMajorant h :=
  Cslib.LogSpaceEstimation.scheduled_child_cost_le hA M d c parent.rank child.rank hc h
    (rank_lt_of_mem_children hchild) ha ha' hu huu' hscale

/-- A task call carries its rates, never a particular old source or right endpoint.
The arguments of the called row remain arguments of `value`. -/
structure Request where
  /-- Constructor being called. -/
  task : PilotTask
  /-- Endpoint scale of the child row. -/
  endRate : ℝ
  /-- Inherited source rate, or the midpoint rate after release. -/
  sourceRate : ℝ

/-- Child calls in `C + Êᵢ C`: direct stage row, left correction, and right stage row.
The right call restarts on the midpoint domain and does not retain the old source rate. -/
@[expose] def inputRequests (f u : ℝ) (i : ℕ) : List Request :=
  [⟨.base, f, u⟩, ⟨.correction i, f, u⟩, ⟨.base, f, f⟩]

/-- Every call in the input's actual direct/product recipe decreases constructor rank. -/
theorem rank_lt_of_mem_inputRequests {f u : ℝ} {i : ℕ} {r : Request}
    (hr : r ∈ inputRequests f u i) : r.task.rank < (input i).rank := by
  simp only [inputRequests, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    exact rank_lt_of_mem_children (by simp [children])

/-- Precision for an actual direct/product child of the pilot input. Its endpoint rate is the
stage rate; only the right product child resets its source to that stage rate. -/
theorem input_request_cost_le {f u a A : ℝ} {i : ℕ} {r : Request}
    (hr : r ∈ inputRequests f u i) (hA : 0 ≤ A) (M d c : ℕ) (hc : 0 < c) (h : ℤ)
    (ha : 0 < a) (hf : 0 < f) (hu : 0 < u) (huf : u ≤ f)
    (hscale : Real.logb 2 (f / a) = (h : ℝ)) :
    Cslib.LogSpaceEstimation.binNormCost 4 (h : ℝ) *
        (2 : ℝ) ^ (Real.logb 2 (r.sourceRate / u) / 4) *
        (2 : ℝ) ^ (-Cslib.LogSpaceEstimation.precision (16 * c) A
          (Cslib.LogSpaceEstimation.lastBudget M d c h) r.task.rank r.endRate r.sourceRate) ≤
      (2 : ℝ) ^ (-Cslib.LogSpaceEstimation.precision (16 * c) A M (input i).rank a u - A +
        (d : ℝ) / (16 * c) + 1 / 16) * Cslib.LogSpaceEstimation.scaleMajorant h := by
  have hrank := rank_lt_of_mem_inputRequests hr
  have hrates : r.endRate = f ∧ u ≤ r.sourceRate := by
    simp only [inputRequests, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨rfl, by first | exact le_rfl | exact huf⟩
  apply Cslib.LogSpaceEstimation.scheduled_child_cost_le hA M d c (input i).rank r.task.rank
    hc h hrank ha (hrates.1.symm ▸ hf) hu hrates.2
  rwa [hrates.1]

variable {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar)
  {V κ : Type u} {ι : Type*} [Fintype V] [Fintype ι] [Fintype κ]
  (X : ι → V → Prop) (Y : κ → V → Prop)
  [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)]
  (f : ℝ) (C : Matrix V V ℝ)

/-- Concrete values of the existing pilot, including its sampled detector score row. -/
@[expose] noncomputable def value : (t : PilotTask) → t.Value V κ
  | .base => C
  | .input i => pilotInput (P.cutoff f) P.γ (columnDetector X Y P.ϕ P.ρ P.J P.K f) C i
  | .score i => fun t => atomPrep P.ϕ P.ρ P.K f
      (pilotInput (P.cutoff f) P.γ (columnDetector X Y P.ϕ P.ρ P.J P.K f) C i)
      {w | Y t w}
  | .detector i => columnDetector X Y P.ϕ P.ρ P.J P.K f
      (pilotInput (P.cutoff f) P.γ (columnDetector X Y P.ϕ P.ρ P.J P.K f) C i)
  | .maximum i => pilotMax (P.cutoff f) P.γ (columnDetector X Y P.ϕ P.ρ P.J P.K f) C i
  | .correction i => pilotCorrection (P.cutoff f) P.γ
      (columnDetector X Y P.ϕ P.ρ P.J P.K f) C i

/-- The input recipe reads precisely the base matrix and the earlier pilot correction. -/
theorem value_input (i : ℕ) : value P X Y f C (.input i) =
    value P X Y f C .base + value P X Y f C (.correction i) * value P X Y f C .base := rfl

/-- The score recipe reads only its input and the terminal seed. -/
theorem value_score (i : ℕ) (t : κ) (x y : V) : value P X Y f C (.score i) t x y =
    P.ϕ (value P X Y f C (.input i) x y / f) *
      rowGate P.ρ P.K f (value P X Y f C (.input i)) {w | Y t w} x := rfl

/-- Taking the actual score rank and its conditional mean gives the detector value.
This is (7.4), with zero padding supplied by the existing `kthLargest` convention. -/
theorem value_detector (i : ℕ) (y : V) : value P X Y f C (.detector i) y =
    𝔼 s, 𝔼 t ∈ {t | Y t y},
      kthLargest P.J {x | X s x} (fun x => value P X Y f C (.score i) t x y) := rfl

/-- Zero padding makes every detector vanish when its rank exceeds the entire vertex domain. -/
theorem value_detector_eq_zero (hJ : Fintype.card V < P.J) (i : ℕ) :
    value P X Y f C (.detector i) = 0 := by
  have hrank (s : ι) (t : κ) (y : V) :
      kthLargest P.J {x | X s x} (fun x => value P X Y f C (.score i) t x y) = 0 := by
    apply le_antisymm _ kthLargest_nonneg
    apply le_of_not_gt
    intro hh
    have hc := (lt_kthLargest_iff P.J_pos (le_refl (0 : ℝ))).mp hh
    have hb := card_le_univ {x ∈ {x | X s x} | 0 < value P X Y f C (.score i) t x y}
    omega
  ext y
  simp [value_detector, hrank]

/-- The running maximum uses its previous value and the just-completed detector. -/
theorem value_maximum_succ (i : ℕ) : value P X Y f C (.maximum (i + 1)) =
    value P X Y f C (.maximum i) ⊔ value P X Y f C (.detector i) :=
  pilotMax_succ i

/-- A zero-padded detector family leaves every running maximum at its exact zero base. -/
theorem value_maximum_eq_zero (hJ : Fintype.card V < P.J) (i : ℕ) :
    value P X Y f C (.maximum i) = 0 := by
  induction i with
  | zero => exact pilotMax_zero
  | succ i ih => rw [value_maximum_succ, ih, value_detector_eq_zero P X Y f C hJ, sup_idem]

/-- The correction uses the current maximum, after the detector has completed. -/
theorem value_correction_succ (i : ℕ) (x y : V) :
    value P X Y f C (.correction (i + 1)) x y =
      f * P.Q (value P X Y f C (.input i) x y / f) *
        P.γ (value P X Y f C (.maximum (i + 1)) y) := by
  change pilotCorrection (P.cutoff f) P.γ
    (columnDetector X Y P.ϕ P.ρ P.J P.K f) C (i + 1) x y = _
  rw [pilotCorrection_succ_apply, P.cutoff_apply]
  rfl

/-- The final vector is exactly the hierarchy's pilot multiplier input. -/
theorem value_maximum_last : value P X Y f C (.maximum P.k) = P.pilot X Y f C := by
  rw [P.pilot_eq]
  rfl

/-- Input nonnegativity and row mass follow from the actual pilot, rather than task fields. -/
theorem value_input_bounds (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y)
    (hC1 : C *ᵥ 1 ≤ 1) (i : ℕ) :
    (∀ x y, 0 ≤ value P X Y f C (.input i) x y) ∧
      ∀ x, ∑ y, value P X Y f C (.input i) x y ≤ (i : ℝ) + 1 := by
  have hseq := isCorrectionSeq_pilotCorrection
    (U := columnDetector X Y P.ϕ P.ρ P.J P.K f) hC (P.cutoff_nonneg hf)
    (fun t ht => (P.cutoff_le hf t).trans (max_le (by
      have := mul_nonneg P.θ_pos.le hf.le
      linarith) ht)) P.γ_nonneg P.γ_le_one
  exact ⟨hseq.input_nonneg hC i, fun x => (hseq.sum_input_le hC1 i x).1⟩

end PilotTask
end Matrix.HierarchyParams

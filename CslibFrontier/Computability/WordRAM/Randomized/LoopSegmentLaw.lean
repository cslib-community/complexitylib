/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Randomized.LoopSegment
public import CslibFrontier.Computability.WordRAM.Randomized.Law
import CslibFrontier.Probability.PMF.Bind

/-!
# Observation laws for randomized loop segments

`LoopSegmentLaw` packages the existing `LoopSegment` execution relation with an exact observation
law, a supported-path instruction bound and a pathwise random-query bound. The witness still
contains the complete joint distribution of native data and instruction count. No additional
execution semantics or expected-time relaxation is introduced.

Segments may stop while the loop condition still holds. Closing a segment into a complete loop
requires the explicit exit postcondition and charges the final two instructions.

## Main definitions

* `Cslib.WordRAM.LoopSegmentLaw`: an observation law for an existing loop segment.

## Main results

* `LoopSegmentLaw.single`, `LoopSegmentLaw.trans`: compose exact observation laws and path budgets.
* `LoopSegmentLaw.finish`: obtain the existing `ExecRandLaw` for the completed loop.

## References

Original packaging of the existing `LoopSegment` and `ExecRandLaw` interfaces.
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B : Basis} {r : ℕ} {α β : Type}

/-- A finite loop segment with a strict supported-path time bound, a pathwise random-call bound
and the exact law of an observation of its final data. -/
def LoopSegmentLaw (w : ℕ) (cond : Cond r) (body : Code B r) (x : Data r)
    (P : Data r → Prop) (T R : ℕ) (f : Data r → α) (μ : PMF α) : Prop :=
  ∃ m, LoopSegment w cond body x m ∧ m.IsQueryBounded R ∧
    (∀ z ∈ m.support, P z.1 ∧ z.2 ≤ T) ∧ ((fun z => f z.1) <$> m).eval = μ

namespace LoopSegmentLaw

variable {w : ℕ} {cond : Cond r} {body : Code B r} {x : Data r}
  {P Q : Data r → Prop} {T T' T₁ T₂ R R' R₁ R₂ : ℕ} {f : Data r → α} {μ : PMF α}

/-- Zero iterations observe the starting data and use no instructions or random calls. -/
theorem nil (hx : P x) : LoopSegmentLaw w cond body x P 0 0 f (PMF.pure (f x)) := by
  refine ⟨pure (x, 0), .nil x, .pure _ 0, ?_, ?_⟩
  · intro z hz
    cases OracleComp.eq_of_mem_supportWith_pure hz
    exact ⟨hx, le_rfl⟩
  · rw [map_pure, ProbComp.eval_pure]

/-- Enlarge budgets and weaken the supported-path postcondition. -/
theorem mono (h : LoopSegmentLaw w cond body x P T R f μ)
    (hPQ : ∀ y, P y → Q y) (hT : T ≤ T') (hR : R ≤ R') :
    LoopSegmentLaw w cond body x Q T' R' f μ := by
  obtain ⟨m, hm, hq, hsup, hlaw⟩ := h
  exact ⟨m, hm, hq.mono hR, fun z hz => ⟨hPQ z.1 (hsup z hz).1, (hsup z hz).2.trans hT⟩,
    hlaw⟩

/-- Rewrite only the exact observation law. -/
theorem congr_law {μ' : PMF α} (h : LoopSegmentLaw w cond body x P T R f μ)
    (hμ : μ = μ') : LoopSegmentLaw w cond body x P T R f μ' := hμ ▸ h

/-- A single active body execution pays the existing two-instruction loop-header allowance. -/
theorem single (hc : cond.Holds x) (h : ExecRandLaw w body x P T R f μ) :
    LoopSegmentLaw w cond body x P (T + 2) R f μ := by
  obtain ⟨m, hm, hq, hsup, hlaw⟩ := h
  refine ⟨_, LoopSegment.single hc hm, (OracleComp.isCostBounded_map_iff _ _ _).mpr hq,
    ?_, ?_⟩
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    exact ⟨(hsup a ha).1, Nat.add_le_add_right (hsup a ha).2 2⟩
  · simpa only [Functor.map_map] using hlaw

/-- Segment laws compose through the observed intermediate state. The continuation witness is
chosen per state; no uniqueness of partial loop segments is assumed. -/
theorem trans {g : Data r → β} {ν : PMF β} {κ : β → PMF α}
    (h₁ : LoopSegmentLaw w cond body x P T₁ R₁ g ν)
    (h₂ : ∀ y, P y → LoopSegmentLaw w cond body y Q T₂ R₂ f (κ (g y))) :
    LoopSegmentLaw w cond body x Q (T₁ + T₂) (R₁ + R₂) f (ν.bind κ) := by
  classical
  obtain ⟨m₁, hm₁, hq₁, hsup₁, hlaw₁⟩ := h₁
  let m₂ : Data r → ProbComp (Data r × ℕ) := fun y =>
    if hy : P y then (h₂ y hy).choose else pure (y, 0)
  have hstep (y : Data r) (hy : P y) :
      LoopSegment w cond body y (m₂ y) ∧ (m₂ y).IsQueryBounded R₂ ∧
        (∀ z ∈ (m₂ y).support, Q z.1 ∧ z.2 ≤ T₂) ∧
        ((fun z => f z.1) <$> m₂ y).eval = κ (g y) := by
    simp only [m₂, hy, ↓reduceDIte]
    exact (h₂ y hy).choose_spec
  refine ⟨_, hm₁.trans (fun z hz => (hstep z.1 (hsup₁ z hz).1).1), ?_, ?_, ?_⟩
  · refine OracleComp.IsCostBounded.bind_on_support hq₁ fun z hz => ?_
    simpa only [Nat.add_zero] using
      (hstep z.1 (hsup₁ z hz).1).2.1.bind fun _ => .pure _ 0
  · intro z hz
    obtain ⟨a, ha, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨b, hb, hfinal⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hfinal
    exact ⟨((hstep a.1 (hsup₁ a ha).1).2.2.1 b hb).1,
      Nat.add_le_add (hsup₁ a ha).2 ((hstep a.1 (hsup₁ a ha).1).2.2.1 b hb).2⟩
  · rw [← hlaw₁]
    simp only [map_bind, map_pure, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_map,
      PMF.bind_map]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun z hz => ?_
    rw [ProbComp.support_eval] at hz
    rw [Function.comp_apply, ← (hstep z.1 (hsup₁ z hz).1).2.2.2, ProbComp.eval_map]
    rfl

/-- An explicit supported exit condition closes the loop and pays its final exit check. -/
theorem finish (h : LoopSegmentLaw w cond body x P T R f μ)
    (hexit : ∀ y, P y → ¬cond.Holds y) :
    ExecRandLaw w (.loop cond body) x P (T + 2) R f μ := by
  obtain ⟨m, hm, hq, hsup, hlaw⟩ := h
  refine ⟨_, hm.finish (fun z hz => hexit z.1 (hsup z hz).1),
    (OracleComp.isCostBounded_map_iff _ _ _).mpr hq, ?_, ?_⟩
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    exact ⟨(hsup a ha).1, Nat.add_le_add_right (hsup a ha).2 2⟩
  · simpa only [Functor.map_map] using hlaw

end LoopSegmentLaw

end Cslib.WordRAM

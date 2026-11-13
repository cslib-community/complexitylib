/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.RandomOracle
public import CslibFrontier.Languages.Probabilistic.Sum

/-!
# Random-oracle caches on a sum of interfaces

Several independent lazy random oracles are one lazy random oracle on the sum of their interfaces,
answered by `OracleComp.sumHandler`. `RandomOracle.Cache.sum` joins one cache per side into a cache
of the joined interface, and a lazy call on one side of a joined cache is a lazy call on that side's
cache (`answer_sum_inl`, `answer_sum_inr`). A game that keeps one cache per oracle can therefore be
read as one represented lazy oracle.

## Main definitions

* `Cslib.RandomOracle.Cache.sum`: the cache of `spec₁ ⊕ₒ spec₂` built from one cache for each side.

## Main results

* `Cslib.RandomOracle.answer_sum_inl`, `Cslib.RandomOracle.answer_sum_inr`: a lazy call on one side
  of a joined cache is a lazy call on that side's cache.
* `Cslib.RandomOracle.Cache.update_sum_inl`, `Cslib.RandomOracle.Cache.update_sum_inr`: recording
  an answer in a joined cache records it on its side.
-/

public section

namespace Cslib.RandomOracle

open scoped Cslib

universe u

variable {ι₁ ι₂ : Type u} {spec₁ : OracleSpec.{u, u} ι₁} {spec₂ : OracleSpec.{u, u} ι₂}

/-- The cache of the joined interface `spec₁ ⊕ₒ spec₂`: left queries read `c₁`, right queries read
`c₂`. -/
@[expose] def Cache.sum (c₁ : Cache spec₁) (c₂ : Cache spec₂) : Cache (spec₁ ⊕ₒ spec₂)
  | .inl q => c₁ q
  | .inr q => c₂ q

@[simp] theorem Cache.sum_inl (c₁ : Cache spec₁) (c₂ : Cache spec₂) (q : ι₁) :
    Cache.sum c₁ c₂ (.inl q) = c₁ q := rfl

@[simp] theorem Cache.sum_inr (c₁ : Cache spec₁) (c₂ : Cache spec₂) (q : ι₂) :
    Cache.sum c₁ c₂ (.inr q) = c₂ q := rfl

/-- The responses of a joined interface are finite when both sides' responses are. -/
instance [∀ q, Finite (spec₁ q)] [∀ q, Finite (spec₂ q)] : ∀ q, Finite ((spec₁ ⊕ₒ spec₂) q)
  | .inl q => inferInstanceAs (Finite (spec₁ q))
  | .inr q => inferInstanceAs (Finite (spec₂ q))

variable [DecidableEq ι₁] [DecidableEq ι₂]

/-- Recording a left answer in a joined cache records it in the left cache. -/
theorem Cache.update_sum_inl (c₁ : Cache spec₁) (c₂ : Cache spec₂) (q : ι₁) (v : spec₁ q) :
    Function.update (Cache.sum c₁ c₂) (.inl q) (some v) =
      Cache.sum (Function.update c₁ q (some v)) c₂ := by
  funext q'
  rcases q' with q' | q'
  · by_cases h : q' = q
    · subst h; simp
    · simp [Function.update_of_ne h, Function.update_of_ne (Sum.inl_injective.ne h)]
  · simp

/-- Recording a right answer in a joined cache records it in the right cache. -/
theorem Cache.update_sum_inr (c₁ : Cache spec₁) (c₂ : Cache spec₂) (q : ι₂) (v : spec₂ q) :
    Function.update (Cache.sum c₁ c₂) (.inr q) (some v) =
      Cache.sum c₁ (Function.update c₂ q (some v)) := by
  funext q'
  rcases q' with q' | q'
  · simp
  · by_cases h : q' = q
    · subst h; simp
    · simp [Function.update_of_ne h, Function.update_of_ne (Sum.inr_injective.ne h)]

/-- A lazy call on the left side of a joined cache is a lazy call on the left cache. -/
theorem answer_sum_inl (d₁ : (q : ι₁) → PMF (spec₁ q)) (d₂ : (q : ι₂) → PMF (spec₂ q))
    (c₁ : Cache spec₁) (c₂ : Cache spec₂) (q : ι₁) :
    answer (OracleComp.sumHandler d₁ d₂) (.inl q) (Cache.sum c₁ c₂) =
      (answer d₁ q c₁).map fun z => (z.1, Cache.sum z.2 c₂) := by
  cases h : c₁ q with
  | none =>
    rw [answer_of_none d₁ c₁ q h,
      answer_of_none (OracleComp.sumHandler d₁ d₂) (Cache.sum c₁ c₂) (.inl q) h, PMF.map_comp]
    exact congrArg (PMF.map · (d₁ q))
      (funext fun v => Prod.ext rfl (Cache.update_sum_inl c₁ c₂ q v))
  | some v =>
    rw [answer_of_some d₁ c₁ q v h,
      answer_of_some (OracleComp.sumHandler d₁ d₂) (Cache.sum c₁ c₂) (.inl q) v h, PMF.pure_map]

/-- A lazy call on the right side of a joined cache is a lazy call on the right cache. -/
theorem answer_sum_inr (d₁ : (q : ι₁) → PMF (spec₁ q)) (d₂ : (q : ι₂) → PMF (spec₂ q))
    (c₁ : Cache spec₁) (c₂ : Cache spec₂) (q : ι₂) :
    answer (OracleComp.sumHandler d₁ d₂) (.inr q) (Cache.sum c₁ c₂) =
      (answer d₂ q c₂).map fun z => (z.1, Cache.sum c₁ z.2) := by
  cases h : c₂ q with
  | none =>
    rw [answer_of_none d₂ c₂ q h,
      answer_of_none (OracleComp.sumHandler d₁ d₂) (Cache.sum c₁ c₂) (.inr q) h, PMF.map_comp]
    exact congrArg (PMF.map · (d₂ q))
      (funext fun v => Prod.ext rfl (Cache.update_sum_inr c₁ c₂ q v))
  | some v =>
    rw [answer_of_some d₂ c₂ q v h,
      answer_of_some (OracleComp.sumHandler d₁ d₂) (Cache.sum c₁ c₂) (.inr q) v h, PMF.pure_map]

end Cslib.RandomOracle

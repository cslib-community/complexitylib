/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.SingleParameter
public import CslibFrontier.GameTheory.Mechanism.VCG

/-!
# Single-parameter mechanisms as general mechanisms

A single-parameter environment is a general environment `Cslib.GameTheory.Mechanism ι Ω` in which
agent `i` values the outcome `ω` at `vᵢ · xᵢ(ω)`, for an allocation map `x : Ω → ι → ℝ` and a
private scalar `vᵢ ≥ 0` ([Roughgarden2013CS364A], Lecture 7, §1). `linearValuation x i v` is this
valuation, `linearDomain x i` the set of them, and `linearProfile x b` the profile of reported
valuations of the scalar bids `b`.

Running a general mechanism `M` on the reports `linearProfile x b` gives the single-parameter
mechanism `M.toSingleParameter x`, with allocation `x (M.outcome (linearProfile x b))`. It is DSIC
in the single-parameter sense (nonnegative bids and values) exactly when `M` is DSIC on the linear
domains (`isDSIC_toSingleParameter_iff`). In particular every DSIC general mechanism, such as VCG,
gives a DSIC single-parameter mechanism (`Mechanism.IsDSIC.toSingleParameter`). Conversely, a
single-parameter mechanism `M` is the general mechanism `M.toMechanism` on allocation vectors
`Ω = ι → ℝ`, which reads each scalar bid off the reported value of a unit allocation and gives
back `M` (`toSingleParameter_toMechanism`).

## Main definitions

* `Cslib.GameTheory.Mechanism.linearValuation`, `Cslib.GameTheory.Mechanism.linearDomain`,
  `Cslib.GameTheory.Mechanism.linearProfile`.
* `Cslib.GameTheory.Mechanism.toSingleParameter`: a general mechanism on linear valuations.
* `Cslib.GameTheory.SingleParameter.Mechanism.toMechanism`: a single-parameter mechanism as a
  general mechanism on allocation vectors.

## Main results

* `Cslib.GameTheory.Mechanism.isDSIC_toSingleParameter_iff`: single-parameter DSIC is DSIC on the
  linear domains.
* `Cslib.GameTheory.Mechanism.IsDSIC.toSingleParameter`,
  `Cslib.GameTheory.Mechanism.IsIR.toSingleParameter`.
* `Cslib.GameTheory.SingleParameter.Mechanism.isDSIC_iff_isDSICOn_toMechanism`.

## References

* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
-/

public section

namespace Cslib.GameTheory

namespace Mechanism

variable {ι Ω : Type*}

/-- The linear valuation `ω ↦ v · xᵢ(ω)` of agent `i` with scalar value `v` under the allocation
map `x`. -/
@[expose] def linearValuation (x : Ω → ι → ℝ) (i : ι) (v : ℝ) : Ω → ℝ := fun ω => v * x ω i

/-- The single-parameter valuation domain of agent `i`: linear valuations with a nonnegative
scalar value. -/
@[expose] def linearDomain (x : Ω → ι → ℝ) (i : ι) : Set (Ω → ℝ) :=
  linearValuation x i '' Set.Ici 0

/-- The profile of linear valuations reported by the scalar bids `b`. -/
@[expose] def linearProfile (x : Ω → ι → ℝ) (b : ι → ℝ) : ι → Ω → ℝ :=
  fun i => linearValuation x i (b i)

@[simp]
theorem linearValuation_apply (x : Ω → ι → ℝ) (i : ι) (v : ℝ) (ω : Ω) :
    linearValuation x i v ω = v * x ω i :=
  rfl

@[simp]
theorem linearProfile_apply (x : Ω → ι → ℝ) (b : ι → ℝ) (i : ι) :
    linearProfile x b i = linearValuation x i (b i) :=
  rfl

theorem linearValuation_mem_linearDomain (x : Ω → ι → ℝ) (i : ι) {v : ℝ} (hv : 0 ≤ v) :
    linearValuation x i v ∈ linearDomain x i :=
  ⟨v, hv, rfl⟩

/-- Changing agent `i`'s scalar bid changes only its reported valuation. -/
theorem linearProfile_update [DecidableEq ι] (x : Ω → ι → ℝ) (b : ι → ℝ) (i : ι) (z : ℝ) :
    linearProfile x (Function.update b i z) =
      Function.update (linearProfile x b) i (linearValuation x i z) :=
  funext (Function.apply_update (fun j => linearValuation x j) b i z)

/-- The general mechanism `M` run on linear valuations: the scalar bids `b` are reported as the
valuations `linearProfile x b`, and agent `i` is allocated `xᵢ` of the chosen outcome. -/
@[expose] def toSingleParameter (M : Mechanism ι Ω) (x : Ω → ι → ℝ) :
    SingleParameter.Mechanism ι where
  allocation b := x (M.outcome (linearProfile x b))
  payment b := M.payment (linearProfile x b)

/-- Single-parameter utility is general utility with the linear valuation. -/
theorem utility_toSingleParameter (M : Mechanism ι Ω) (x : Ω → ι → ℝ) (i : ι) (v : ℝ)
    (b : ι → ℝ) :
    (M.toSingleParameter x).utility i v b =
      M.utility i (linearValuation x i v) (linearProfile x b) :=
  rfl

/-- **Single-parameter DSIC is DSIC on linear valuations**: a general mechanism is DSIC on the
domains `linearDomain x` exactly when, run on linear valuations, it is DSIC for nonnegative bids
and values. -/
theorem isDSIC_toSingleParameter_iff [DecidableEq ι] {M : Mechanism ι Ω} {x : Ω → ι → ℝ} :
    (M.toSingleParameter x).IsDSIC ↔ M.IsDSICOn (linearDomain x) := by
  constructor
  · rintro h i B _ hB ⟨w, hw, rfl⟩
    simp only [linearDomain, Set.mem_image, Set.mem_Ici] at hB
    choose c hc hcB using hB
    obtain rfl : linearProfile x c = B := funext hcB
    have := h i c w hc hw
    rwa [utility_toSingleParameter, utility_toSingleParameter, linearProfile_update] at this
  · intro h i b v hb hv
    rw [utility_toSingleParameter, utility_toSingleParameter, linearProfile_update]
    exact h i _ _ (fun j => linearValuation_mem_linearDomain x j (hb j))
      (linearValuation_mem_linearDomain x i hv)

/-- A DSIC general mechanism, run on linear valuations, is DSIC as a single-parameter
mechanism. -/
theorem IsDSIC.toSingleParameter [DecidableEq ι] {M : Mechanism ι Ω} (hM : M.IsDSIC)
    (x : Ω → ι → ℝ) : (M.toSingleParameter x).IsDSIC :=
  isDSIC_toSingleParameter_iff.2 (hM.isDSICOn _)

/-- An individually rational general mechanism, run on nonnegative allocations, is individually
rational as a single-parameter mechanism. -/
theorem IsIR.toSingleParameter {M : Mechanism ι Ω} (hM : M.IsIR) {x : Ω → ι → ℝ} (hx : 0 ≤ x) :
    (M.toSingleParameter x).IsIR :=
  fun i b hb => hM i (linearProfile x b) fun ω => mul_nonneg (hb i) (hx ω i)

end Mechanism

namespace SingleParameter.Mechanism

variable {ι : Type*} [DecidableEq ι]

/-- A single-parameter mechanism as a general mechanism whose outcomes are allocation vectors:
agent `j`'s scalar bid is its reported value `B j (Pi.single j 1)` of a unit allocation. -/
@[expose] def toMechanism (M : Mechanism ι) : GameTheory.Mechanism ι (ι → ℝ) where
  outcome B := M.allocation fun j => B j (Pi.single j 1)
  payment B := M.payment fun j => B j (Pi.single j 1)

/-- On linear valuations `toMechanism` gives back the single-parameter mechanism. -/
@[simp]
theorem toSingleParameter_toMechanism (M : Mechanism ι) :
    M.toMechanism.toSingleParameter id = M := by
  cases M
  simp only [GameTheory.Mechanism.toSingleParameter, toMechanism,
    GameTheory.Mechanism.linearProfile_apply, GameTheory.Mechanism.linearValuation_apply, id_eq,
    Pi.single_eq_same, mul_one]

/-- A single-parameter mechanism is DSIC exactly when its general form is DSIC on linear
valuations of allocation vectors. -/
theorem isDSIC_iff_isDSICOn_toMechanism {M : Mechanism ι} :
    M.IsDSIC ↔ M.toMechanism.IsDSICOn (GameTheory.Mechanism.linearDomain id) := by
  conv_lhs => rw [← toSingleParameter_toMechanism M]
  exact GameTheory.Mechanism.isDSIC_toSingleParameter_iff

end SingleParameter.Mechanism

end Cslib.GameTheory

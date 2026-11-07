/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith

/-!
# The Vickrey–Clarke–Groves mechanism

A general (multi-parameter) mechanism design environment has agents `ι`, a set `Ω` of outcomes,
and a private valuation `vᵢ : Ω → ℝ` for each agent ([Roughgarden2013CS364A], Lecture 7, §1). A
direct-revelation mechanism collects reported valuations `b : ι → Ω → ℝ`, chooses an outcome and
charges payments; agent `i` with valuation `v` has quasilinear utility `v(ω) − pᵢ(b)`.

*Groves mechanisms* [Groves1973] choose an outcome maximizing reported welfare `∑ᵢ bᵢ(ω)` and
charge `pᵢ(b) = hᵢ(b₋ᵢ) − ∑ⱼ≠ᵢ bⱼ(ω*)`; every such mechanism is DSIC. The *Clarke pivot*
[Clarke1971] `hᵢ(b₋ᵢ) = max_ω ∑ⱼ≠ᵢ bⱼ(ω)` gives the VCG mechanism, which charges each agent its
externality ([Roughgarden2013CS364A], Lecture 7, (2)). Its payments are nonnegative and a
truthful agent with nonnegative valuation gets nonnegative utility (Lecture 7, (4) and the
exercise following it).

DSIC holds for arbitrary real valuations; nonnegativity is only assumed for individual
rationality. The finite outcome set is needed for the Clarke pivot and for the existence of a
welfare-maximizing outcome rule; DSIC of Groves mechanisms holds for any outcome type.

## Main definitions

* `Mechanism`: an outcome rule and a payment rule on reported valuation profiles.
* `Mechanism.utility`, `Mechanism.IsDSIC`, `Mechanism.IsIR`.
* `Mechanism.welfare`, `Mechanism.IsWelfareMaximizing`.
* `Mechanism.groves`, `Mechanism.clarkePivot`, `Mechanism.vcg`.

## Main results

* `Mechanism.groves_isDSIC`: Groves mechanisms with a welfare-maximizing outcome rule are DSIC.
* `Mechanism.vcg_isDSIC`, `Mechanism.vcg_payment_nonneg`, `Mechanism.vcg_isIR`.
* `Mechanism.exists_isDSIC_isWelfareMaximizing`: in every general mechanism design environment
  with finitely many outcomes there is a DSIC welfare-maximizing mechanism
  ([Roughgarden2013CS364A], Lecture 7, Theorem 2.1), which can moreover be taken individually
  rational with nonnegative payments.

## References

* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
* [T. Roughgarden, *Twenty Lectures on Algorithmic Game Theory*][Roughgarden2016]
* [E. H. Clarke, *Multipart pricing of public goods*][Clarke1971]
* [T. Groves, *Incentives in teams*][Groves1973]
* [W. Vickrey, *Counterspeculation, auctions, and competitive sealed tenders*][Vickrey1961]
-/

public section

namespace Cslib.GameTheory

/-- A direct-revelation mechanism with agents `ι` and outcomes `Ω`: on the reported valuations
`b : ι → Ω → ℝ` it chooses `outcome b` and charges agent `i` the amount `payment b i`. -/
structure Mechanism (ι Ω : Type*) where
  /-- The outcome rule. -/
  outcome : (ι → Ω → ℝ) → Ω
  /-- The payment rule. -/
  payment : (ι → Ω → ℝ) → ι → ℝ

namespace Mechanism

variable {ι Ω : Type*}

/-- The quasilinear utility `v(ω) − pᵢ(b)` of agent `i` with valuation `v` on the reports `b`,
where `ω` is the chosen outcome. -/
@[expose] def utility (M : Mechanism ι Ω) (i : ι) (v : Ω → ℝ) (b : ι → Ω → ℝ) : ℝ :=
  v (M.outcome b) - M.payment b i

/-- Dominant-strategy incentive compatibility: for every agent `i`, valuation `v` and reports `b`,
reporting `v` instead of `bᵢ` does not lower `i`'s utility ([Roughgarden2013CS364A], Lecture 7,
§2). Valuations are arbitrary real functions. -/
@[expose] def IsDSIC [DecidableEq ι] (M : Mechanism ι Ω) : Prop :=
  ∀ (i : ι) (b : ι → Ω → ℝ) (v : Ω → ℝ),
    M.utility i v b ≤ M.utility i v (Function.update b i v)

/-- Individual rationality: an agent whose valuation `bᵢ` is nonnegative and who reports it
truthfully gets nonnegative utility, whatever the others report. -/
@[expose] def IsIR (M : Mechanism ι Ω) : Prop :=
  ∀ (i : ι) (b : ι → Ω → ℝ), 0 ≤ b i → 0 ≤ M.utility i (b i) b

variable [Fintype ι]

/-- The reported welfare `∑ᵢ bᵢ(ω)` of the outcome `ω`. -/
@[expose] def welfare (b : ι → Ω → ℝ) (ω : Ω) : ℝ := ∑ i, b i ω

/-- An outcome rule is welfare-maximizing if it always chooses an outcome maximizing the reported
welfare ([Roughgarden2013CS364A], Lecture 7, (1)). -/
@[expose] def IsWelfareMaximizing (f : (ι → Ω → ℝ) → Ω) : Prop :=
  ∀ b ω, welfare b ω ≤ welfare b (f b)

theorem welfare_eq_add [DecidableEq ι] (b : ι → Ω → ℝ) (i : ι) (ω : Ω) :
    welfare b ω = b i ω + ∑ j ∈ Finset.univ.erase i, b j ω :=
  (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm

variable [DecidableEq ι]

/-- The Groves mechanism [Groves1973] with outcome rule `f` and pivot `h`: agent `i` pays
`hᵢ(b) − ∑ⱼ≠ᵢ bⱼ(f(b))`. -/
@[expose] def groves (f : (ι → Ω → ℝ) → Ω) (h : ι → (ι → Ω → ℝ) → ℝ) : Mechanism ι Ω where
  outcome := f
  payment b i := h i b - ∑ j ∈ Finset.univ.erase i, b j (f b)

theorem sum_erase_update (b : ι → Ω → ℝ) (i : ι) (v : Ω → ℝ) (ω : Ω) :
    ∑ j ∈ Finset.univ.erase i, Function.update b i v j ω = ∑ j ∈ Finset.univ.erase i, b j ω :=
  Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- **Groves mechanisms are DSIC** [Groves1973]: if the outcome rule maximizes reported welfare
and the pivot `hᵢ` does not depend on `i`'s report, then `i`'s utility under truthful reporting is
`∑ⱼ bⱼ(ω*) − hᵢ(b₋ᵢ)` with `bᵢ = vᵢ`, which the mechanism maximizes. -/
theorem groves_isDSIC {f : (ι → Ω → ℝ) → Ω} (hf : IsWelfareMaximizing f)
    {h : ι → (ι → Ω → ℝ) → ℝ} (hh : ∀ i b v, h i (Function.update b i v) = h i b) :
    (groves f h).IsDSIC := by
  intro i b v
  simp only [utility, groves, hh, sum_erase_update]
  have key := hf (Function.update b i v) (f b)
  rw [welfare_eq_add _ i, welfare_eq_add _ i, Function.update_self, sum_erase_update,
    sum_erase_update] at key
  linarith

variable [Fintype Ω] [Nonempty Ω]

/-- The Clarke pivot [Clarke1971]: the maximum welfare `max_ω ∑ⱼ≠ᵢ bⱼ(ω)` of the other agents. -/
@[expose] noncomputable def clarkePivot (i : ι) (b : ι → Ω → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun ω => ∑ j ∈ Finset.univ.erase i, b j ω

/-- The VCG mechanism with welfare-maximizing outcome rule `f`: agent `i` pays its externality
`max_ω ∑ⱼ≠ᵢ bⱼ(ω) − ∑ⱼ≠ᵢ bⱼ(f(b))` ([Roughgarden2013CS364A], Lecture 7, (2)). -/
@[expose] noncomputable def vcg (f : (ι → Ω → ℝ) → Ω) : Mechanism ι Ω := groves f clarkePivot

/-- The Clarke pivot of agent `i` does not depend on `i`'s report. -/
@[simp]
theorem clarkePivot_update (i : ι) (b : ι → Ω → ℝ) (v : Ω → ℝ) :
    clarkePivot i (Function.update b i v) = clarkePivot i b := by
  simp only [clarkePivot, sum_erase_update]

/-- **The VCG mechanism is DSIC** ([Roughgarden2013CS364A], Lecture 7, Theorem 2.1). -/
theorem vcg_isDSIC {f : (ι → Ω → ℝ) → Ω} (hf : IsWelfareMaximizing f) : (vcg f).IsDSIC :=
  groves_isDSIC hf clarkePivot_update

/-- VCG payments are nonnegative ([Roughgarden2013CS364A], Lecture 7, after (2)), for any
outcome rule. -/
theorem vcg_payment_nonneg (f : (ι → Ω → ℝ) → Ω) (b : ι → Ω → ℝ) (i : ι) :
    0 ≤ (vcg f).payment b i := by
  simp only [vcg, groves, clarkePivot, sub_nonneg]
  exact Finset.le_sup' (fun ω => ∑ j ∈ Finset.univ.erase i, b j ω) (Finset.mem_univ (f b))

/-- **VCG is individually rational** ([Roughgarden2013CS364A], Lecture 7, after (4)): the rebate
`∑ⱼ bⱼ(ω*) − max_ω ∑ⱼ≠ᵢ bⱼ(ω)` is nonnegative when `bᵢ ≥ 0`, so a truthful agent with
nonnegative valuation pays at most its value of the chosen outcome. -/
theorem vcg_isIR {f : (ι → Ω → ℝ) → Ω} (hf : IsWelfareMaximizing f) : (vcg f).IsIR := by
  intro i b hb
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Ω))
    fun ω => ∑ j ∈ Finset.univ.erase i, b j ω
  have key := hf b ω
  rw [welfare_eq_add _ i, welfare_eq_add _ i] at key
  have hbi : 0 ≤ b i ω := hb ω
  simp only [utility, vcg, groves, clarkePivot, hω]
  linarith

omit [DecidableEq ι] [Fintype Ω] in
/-- A welfare-maximizing outcome rule exists when there are finitely many outcomes. -/
theorem exists_isWelfareMaximizing [Finite Ω] :
    ∃ f : (ι → Ω → ℝ) → Ω, IsWelfareMaximizing f := by
  have := Fintype.ofFinite Ω
  have : ∀ b : ι → Ω → ℝ, ∃ ω, ∀ ω', welfare b ω' ≤ welfare b ω := fun b => by
    obtain ⟨ω, -, hω⟩ := Finset.exists_max_image Finset.univ (welfare b) Finset.univ_nonempty
    exact ⟨ω, fun ω' => hω ω' (Finset.mem_univ _)⟩
  choose f hf using this
  exact ⟨f, hf⟩

omit [Fintype Ω] in
/-- **Vickrey–Clarke–Groves** ([Roughgarden2013CS364A], Lecture 7, Theorem 2.1): in every general
mechanism design environment with finitely many outcomes there is a DSIC welfare-maximizing
mechanism. The VCG mechanism is moreover individually rational with nonnegative payments. -/
theorem exists_isDSIC_isWelfareMaximizing [Finite Ω] :
    ∃ M : Mechanism ι Ω, M.IsDSIC ∧ IsWelfareMaximizing M.outcome ∧ M.IsIR ∧
      ∀ b i, 0 ≤ M.payment b i := by
  have := Fintype.ofFinite Ω
  obtain ⟨f, hf⟩ := exists_isWelfareMaximizing (ι := ι) (Ω := Ω)
  exact ⟨vcg f, vcg_isDSIC hf, hf, vcg_isIR hf, vcg_payment_nonneg f⟩

end Mechanism

end Cslib.GameTheory

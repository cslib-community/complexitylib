/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Computability.Probabilistic.Oracle.Time
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Choose
import CslibFrontier.Tactic.PolyTime

/-!
# Resource-indexed concrete security of Boolean experiments

`Cslib.Crypto.Game.Indistinguishable` quantifies asymptotically over admissible adversaries.
Concrete security theorems instead bound distinguishing advantage or success probability as an
explicit function `ε n r` of the security parameter `n` and adversary resource budget `r` (such as
query count `q`, halting machine steps `t`, or the pair `(t, q)`), and compose reductions by
mapping target resource budgets `r` to source resource budgets `mapRes n r`.

This module provides:

* `Game.IndistinguishableWithin` and one-sided `Game.SuccWithin`, parameterized by a resource
  predicate `Within : ℕ → Resource → Adversary → Prop` and error surface `ε : ℕ → Resource → ℝ≥0`;
* algebra and game-hopping combinators (`.refl`, `.symm`, `.trans`, `.mono`, `.of_within`,
  `.hybrid`, `.hybrid_const`) and concrete reduction transfer
  (`IndistinguishableWithin.of_reduction`, `SuccWithin.of_reduction`);
* standard resource predicates `WithinQueries`, `WithinTime`, `WithinTimeUpTo`, `WithinOracleTime`,
  and `WithinTimeAndQueries` built on plain halting `ComputesInTime` and `ComputesOracleInTime`,
  together with exact equivalences against global step schedules;
* concrete-to-asymptotic bridges (`IndistinguishableWithin.indistinguishable`,
  `Game.Indistinguishable.of_queryBounded`, `of_queryBounded_real`, `of_queryBounded_reduction`,
  `of_timeBounded`, and `of_timeAndQueryBounded`) eliminating manual polynomial schedule unpacking.

## Main definitions

* `Cslib.Crypto.Game.IndistinguishableWithin`: resource-indexed concrete advantage bound.
* `Cslib.Crypto.Game.SuccWithin`: resource-indexed concrete success-probability bound.
* `Cslib.Crypto.Game.WithinQueries`, `Cslib.Crypto.Game.WithinTime`,
  `Cslib.Crypto.Game.WithinTimeUpTo`, `Cslib.Crypto.Game.WithinOracleTime`,
  `Cslib.Crypto.Game.WithinTimeAndQueries`: concrete query, halting-time, and `(t, q)` adversary
  predicates.

## Main results

* `Cslib.Probability.IsOraclePPT.exists_computable_queryBound`: extract a unary polynomial-time
  computable, polynomially bounded query schedule from `IsOraclePPT`.
* `Cslib.Crypto.Game.IndistinguishableWithin.of_reduction`,
  `Cslib.Crypto.Game.SuccWithin.of_reduction`: transfer concrete security across resource-mapping
  reductions.
* `Cslib.Crypto.Game.IndistinguishableWithin.hybrid`, `.hybrid_const`: concrete multi-hop triangle
  inequalities.
* `Cslib.Crypto.Game.IndistinguishableWithin.indistinguishable`: general concrete-to-asymptotic
  bridge along polynomial resource schedules.
* `Cslib.Crypto.Game.Indistinguishable.of_queryBounded`, `.of_queryBounded_real`,
  `.of_birthday_queryBounded_real`, `.of_queryBounded_reduction`,
  `.of_succProbability_queryBounded`, `.of_costBounded`: concrete query/cost-bounded security
  implies `IsOraclePPT` asymptotic security.
* `Cslib.Crypto.Game.Indistinguishable.of_timeBounded`, `.of_timeBounded_upTo`,
  `.of_timeAndQueryBounded`: concrete `(t, ε)` and `(t, q, ε)` security imply `IsPPT` and
  `IsOraclePPT` asymptotic security.

## References

* [M. Bellare, P. Rogaway, *The Security of Triple Encryption and a Framework for Code-Based
  Game-Playing Proofs*][BonehShoup2023] (see Boneh–Shoup Sections 3.1, 3.11, 4.1).
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Sections 3.1,
  3.11, 4.1.
-/

public section

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- Extract an explicit unary polynomial-time computable, polynomially bounded schedule `Q : ℕ → ℕ`
bounding both external query counts and request lengths of an `IsOraclePPT` program at
`n + aux.length`. -/
theorem IsOraclePPT.exists_computable_queryBound {Operation β : Type} [DecidableEq Operation]
    {output : β ↪ List Bool} {program : ℕ → List Bool → WordOracleComp Operation β}
    (h : IsOraclePPT output program) :
    ∃ Q : ℕ → ℕ, ComputableInPolyTime Q encUnary encUnary ∧ PolynomiallyBounded Q ∧
      ∀ n aux, (program n aux).IsQueryBounded (Q (n + aux.length)) ∧
        (program n aux).QueriesSatisfy fun request =>
          request.2.length ≤ Q (n + aux.length) := by
  obtain ⟨c, d, hbounds⟩ := h.query_bounds
  let Q : ℕ → ℕ := fun m => c * (m + 2) ^ d
  have hcomp : ComputableInPolyTime Q encUnary encUnary := .of_tidy (by unfold Q; polytime)
  have hpoly : PolynomiallyBounded Q :=
    (PolynomiallyBounded.const c).mul ((PolynomiallyBounded.id.add (.const 2)).pow d)
  exact ⟨Q, hcomp, hpoly, hbounds⟩

end Cslib.Probability

namespace Cslib.Crypto.Game

open Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### Concrete advantage and success predicates -/

/-- Two families of games are concretely `(Within, ε)`-indistinguishable when at every security
parameter `n` and resource budget `r`, every adversary satisfying `Within n r adversary` has
distinguishing advantage at most `ε n r`. -/
@[expose] def IndistinguishableWithin {Adversary Resource : Type*}
    (game1 game2 : Adversary → ℕ → Game)
    (Within : ℕ → Resource → Adversary → Prop)
    (ε : ℕ → Resource → ℝ≥0) : Prop :=
  ∀ n r adversary, Within n r adversary →
    advantage (game1 adversary n) (game2 adversary n) ≤ ε n r

/-- A family of one-sided search or forgery games is concretely `(Within, ε)`-secure when at every
security parameter `n` and resource budget `r`, every adversary satisfying `Within n r adversary`
succeeds with probability at most `ε n r`. -/
@[expose] def SuccWithin {Adversary Resource : Type*}
    (game : Adversary → ℕ → Game)
    (Within : ℕ → Resource → Adversary → Prop)
    (ε : ℕ → Resource → ℝ≥0) : Prop :=
  ∀ n r adversary, Within n r adversary →
    succProbability (game adversary n) ≤ ε n r

/-- Concrete indistinguishability from `PMF.pure false` is concrete one-sided `SuccWithin`
security. -/
theorem indistinguishableWithin_pure_false_iff {Adversary Resource : Type*}
    (game : Adversary → ℕ → Game) (Within : ℕ → Resource → Adversary → Prop)
    (ε : ℕ → Resource → ℝ≥0) :
    IndistinguishableWithin game (fun _ _ => PMF.pure false) Within ε ↔
      SuccWithin game Within ε := by
  simp [IndistinguishableWithin, SuccWithin]

/-- Concrete indistinguishability with `PMF.pure false` on the left is concrete `SuccWithin`
security. -/
theorem pure_false_indistinguishableWithin_iff {Adversary Resource : Type*}
    (game : Adversary → ℕ → Game) (Within : ℕ → Resource → Adversary → Prop)
    (ε : ℕ → Resource → ℝ≥0) :
    IndistinguishableWithin (fun _ _ => PMF.pure false) game Within ε ↔
      SuccWithin game Within ε := by
  simp [IndistinguishableWithin, SuccWithin]

/-! ### Algebra, hopping, and reductions for `IndistinguishableWithin` and `SuccWithin` -/

namespace IndistinguishableWithin

/-- Every family of games is within zero error of itself. -/
theorem refl {Adversary Resource : Type*} (game : Adversary → ℕ → Game)
    (Within : ℕ → Resource → Adversary → Prop) :
    IndistinguishableWithin game game Within (fun _ _ => 0) :=
  fun _ _ _ _ => by simp

/-- Swapping the two games preserves any concrete error bound. -/
theorem symm {Adversary Resource : Type*} {game1 game2 : Adversary → ℕ → Game}
    {Within : ℕ → Resource → Adversary → Prop} {ε : ℕ → Resource → ℝ≥0}
    (h : IndistinguishableWithin game1 game2 Within ε) :
    IndistinguishableWithin game2 game1 Within ε :=
  fun n r adversary hw => (advantage_comm _ _).trans_le (h n r adversary hw)

/-- Concrete error bounds add across an intermediate game hop. -/
theorem trans {Adversary Resource : Type*}
    {first middle last : Adversary → ℕ → Game}
    {Within : ℕ → Resource → Adversary → Prop}
    {ε₁ ε₂ : ℕ → Resource → ℝ≥0}
    (h₁ : IndistinguishableWithin first middle Within ε₁)
    (h₂ : IndistinguishableWithin middle last Within ε₂) :
    IndistinguishableWithin first last Within (fun n r => ε₁ n r + ε₂ n r) :=
  fun n r adversary hw =>
    (advantage_triangle _ _ _).trans (add_le_add (h₁ n r adversary hw) (h₂ n r adversary hw))

/-- Enlarging the concrete error surface preserves the bound. -/
theorem mono {Adversary Resource : Type*} {game1 game2 : Adversary → ℕ → Game}
    {Within : ℕ → Resource → Adversary → Prop} {ε₁ ε₂ : ℕ → Resource → ℝ≥0}
    (h : IndistinguishableWithin game1 game2 Within ε₁)
    (hle : ∀ n r, ε₁ n r ≤ ε₂ n r) :
    IndistinguishableWithin game1 game2 Within ε₂ :=
  fun n r adversary hw => (h n r adversary hw).trans (hle n r)

/-- Contravariantly refine the resource type and admissibility predicate through `mapRes`. -/
theorem of_within {Adversary SourceResource TargetResource : Type*}
    {game1 game2 : Adversary → ℕ → Game}
    {SourceWithin : ℕ → SourceResource → Adversary → Prop}
    {TargetWithin : ℕ → TargetResource → Adversary → Prop}
    {ε : ℕ → SourceResource → ℝ≥0}
    (h : IndistinguishableWithin game1 game2 SourceWithin ε)
    (mapRes : ℕ → TargetResource → SourceResource)
    (hsub : ∀ n r adversary, TargetWithin n r adversary → SourceWithin n (mapRes n r) adversary) :
    IndistinguishableWithin game1 game2 TargetWithin (fun n r => ε n (mapRes n r)) :=
  fun n r adversary hw => h n (mapRes n r) adversary (hsub n r adversary hw)

/-- Sum concrete errors across `hops n` adjacent hybrids `hyb 0, …, hyb (hops n)`. -/
theorem hybrid {Adversary Resource : Type*}
    (hyb : ℕ → Adversary → ℕ → Game)
    (hops : ℕ → ℕ)
    {Within : ℕ → Resource → Adversary → Prop}
    {stepErr : ℕ → Resource → ℕ → ℝ≥0}
    (hstep : ∀ n r i, i < hops n → ∀ adversary, Within n r adversary →
      advantage (hyb i adversary n) (hyb (i + 1) adversary n) ≤ stepErr n r i) :
    IndistinguishableWithin (hyb 0) (fun adversary n => hyb (hops n) adversary n) Within
      (fun n r => ∑ i ∈ Finset.range (hops n), stepErr n r i) := by
  intro n r adversary hw
  refine (advantage_hybrid_le_sum (fun i => hyb i adversary n) (hops n)).trans ?_
  exact Finset.sum_le_sum fun i hi => hstep n r i (Finset.mem_range.mp hi) adversary hw

/-- Concrete `hops n`-step hybrid argument with a uniform per-hop error `δ n r`. -/
theorem hybrid_const {Adversary Resource : Type*}
    (hyb : ℕ → Adversary → ℕ → Game)
    (hops : ℕ → ℕ)
    {Within : ℕ → Resource → Adversary → Prop}
    {δ : ℕ → Resource → ℝ≥0}
    (hstep : ∀ n r i, i < hops n → ∀ adversary, Within n r adversary →
      advantage (hyb i adversary n) (hyb (i + 1) adversary n) ≤ δ n r) :
    IndistinguishableWithin (hyb 0) (fun adversary n => hyb (hops n) adversary n) Within
      (fun n r => hops n * δ n r) := by
  simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
    hybrid hyb hops (stepErr := fun n r _ => δ n r) hstep

/-- **Concrete security reduction.** If `reduce` maps every target adversary within budget `r` at
parameter `n` to a source adversary within budget `mapRes n r`, and bounds target advantage by
`loss n r` times source advantage plus `err n r`, then source `(SourceWithin, ε)`-security implies
target `(TargetWithin, fun n r => loss n r * ε n (mapRes n r) + err n r)`-security. -/
theorem of_reduction {SourceAdversary TargetAdversary SourceResource TargetResource : Type*}
    {source1 source2 : SourceAdversary → ℕ → Game}
    {target1 target2 : TargetAdversary → ℕ → Game}
    {SourceWithin : ℕ → SourceResource → SourceAdversary → Prop}
    {TargetWithin : ℕ → TargetResource → TargetAdversary → Prop}
    {ε : ℕ → SourceResource → ℝ≥0}
    (hsource : IndistinguishableWithin source1 source2 SourceWithin ε)
    (reduce : TargetAdversary → SourceAdversary)
    (mapRes : ℕ → TargetResource → SourceResource)
    (loss err : ℕ → TargetResource → ℝ≥0)
    (hwithin : ∀ n r adversary, TargetWithin n r adversary →
      SourceWithin n (mapRes n r) (reduce adversary))
    (hbound : ∀ n r adversary, TargetWithin n r adversary →
      advantage (target1 adversary n) (target2 adversary n) ≤
        loss n r * advantage (source1 (reduce adversary) n) (source2 (reduce adversary) n) +
          err n r) :
    IndistinguishableWithin target1 target2 TargetWithin
      (fun n r => loss n r * ε n (mapRes n r) + err n r) := by
  intro n r adversary hw
  refine (hbound n r adversary hw).trans (add_le_add ?_ le_rfl)
  exact mul_le_mul_of_nonneg_left (hsource n (mapRes n r) (reduce adversary)
    (hwithin n r adversary hw)) zero_le

/-- **General concrete-to-asymptotic bridge.** If every `Admissible` adversary admits a resource
schedule `r : ℕ → Resource` in `PolyResource`, and `ε` is negligible along every schedule in
`PolyResource`, then `IndistinguishableWithin` implies asymptotic `Game.Indistinguishable`. -/
theorem indistinguishable {Adversary Resource : Type*}
    {game1 game2 : Adversary → ℕ → Game}
    {Within : ℕ → Resource → Adversary → Prop}
    {ε : ℕ → Resource → ℝ≥0}
    {Admissible : Adversary → Prop}
    (PolyResource : (ℕ → Resource) → Prop)
    (h : IndistinguishableWithin game1 game2 Within ε)
    (hsched : ∀ adversary, Admissible adversary →
      ∃ r : ℕ → Resource, PolyResource r ∧ ∀ n, Within n (r n) adversary)
    (hneg : ∀ r : ℕ → Resource, PolyResource r → Negligible (fun n => ε n (r n))) :
    Indistinguishable game1 game2 Admissible := by
  intro adversary hadm
  obtain ⟨r, hr, hwithin⟩ := hsched adversary hadm
  exact negligible_of_le (hneg r hr) fun n => h n (r n) adversary (hwithin n)

end IndistinguishableWithin

namespace SuccWithin

/-- Enlarging the concrete success bound preserves `SuccWithin`. -/
theorem mono {Adversary Resource : Type*} {game : Adversary → ℕ → Game}
    {Within : ℕ → Resource → Adversary → Prop} {ε₁ ε₂ : ℕ → Resource → ℝ≥0}
    (h : SuccWithin game Within ε₁) (hle : ∀ n r, ε₁ n r ≤ ε₂ n r) :
    SuccWithin game Within ε₂ :=
  fun n r adversary hw => (h n r adversary hw).trans (hle n r)

/-- Contravariantly refine the resource type and admissibility predicate of a `SuccWithin` bound. -/
theorem of_within {Adversary SourceResource TargetResource : Type*}
    {game : Adversary → ℕ → Game}
    {SourceWithin : ℕ → SourceResource → Adversary → Prop}
    {TargetWithin : ℕ → TargetResource → Adversary → Prop}
    {ε : ℕ → SourceResource → ℝ≥0}
    (h : SuccWithin game SourceWithin ε)
    (mapRes : ℕ → TargetResource → SourceResource)
    (hsub : ∀ n r adversary, TargetWithin n r adversary → SourceWithin n (mapRes n r) adversary) :
    SuccWithin game TargetWithin (fun n r => ε n (mapRes n r)) :=
  fun n r adversary hw => h n (mapRes n r) adversary (hsub n r adversary hw)

/-- **One-sided concrete security reduction.** Transfer `SuccWithin` across a resource-mapping
reduction with multiplicative `loss` and additive `err`. -/
theorem of_reduction {SourceAdversary TargetAdversary SourceResource TargetResource : Type*}
    {source : SourceAdversary → ℕ → Game}
    {target : TargetAdversary → ℕ → Game}
    {SourceWithin : ℕ → SourceResource → SourceAdversary → Prop}
    {TargetWithin : ℕ → TargetResource → TargetAdversary → Prop}
    {ε : ℕ → SourceResource → ℝ≥0}
    (hsource : SuccWithin source SourceWithin ε)
    (reduce : TargetAdversary → SourceAdversary)
    (mapRes : ℕ → TargetResource → SourceResource)
    (loss err : ℕ → TargetResource → ℝ≥0)
    (hwithin : ∀ n r adversary, TargetWithin n r adversary →
      SourceWithin n (mapRes n r) (reduce adversary))
    (hbound : ∀ n r adversary, TargetWithin n r adversary →
      succProbability (target adversary n) ≤
        loss n r * succProbability (source (reduce adversary) n) + err n r) :
    SuccWithin target TargetWithin (fun n r => loss n r * ε n (mapRes n r) + err n r) := by
  rw [← indistinguishableWithin_pure_false_iff] at hsource ⊢
  refine hsource.of_reduction reduce mapRes loss err hwithin fun n r adversary hw => ?_
  simpa using hbound n r adversary hw

/-- Bridge `SuccWithin` to asymptotic indistinguishability from `PMF.pure false` along polynomial
resource schedules. -/
theorem indistinguishable_pure_false {Adversary Resource : Type*}
    {game : Adversary → ℕ → Game}
    {Within : ℕ → Resource → Adversary → Prop}
    {ε : ℕ → Resource → ℝ≥0}
    {Admissible : Adversary → Prop}
    (PolyResource : (ℕ → Resource) → Prop)
    (h : SuccWithin game Within ε)
    (hsched : ∀ adversary, Admissible adversary →
      ∃ r : ℕ → Resource, PolyResource r ∧ ∀ n, Within n (r n) adversary)
    (hneg : ∀ r : ℕ → Resource, PolyResource r → Negligible (fun n => ε n (r n))) :
    Indistinguishable game (fun _ _ => PMF.pure false) Admissible :=
  ((indistinguishableWithin_pure_false_iff game Within ε).mpr h).indistinguishable
    PolyResource hsched hneg

end SuccWithin

/-! ### Standard query, time, and `(t, q)` concrete resource predicates -/

/-- At parameter `n`, the empty-auxiliary execution `adversary n []` makes at most `q` external
queries on every path. -/
@[expose] def WithinQueries {Query α : Type} {spec : Query → Type}
    (n q : ℕ) (adversary : ℕ → List Bool → ProbOracleComp spec α) : Prop :=
  (adversary n []).IsQueryBounded q

/-- At parameter `n`, `adversary` is realized by a uniform halting fair-coin machine taking at most
`t` steps on all auxiliary inputs of length at most `auxLen n`. -/
@[expose] def WithinTimeUpTo {β : Type} (output : β ↪ List Bool) (auxLen : ℕ → ℕ)
    (n t : ℕ) (adversary : ℕ → List Bool → ProbComp β) : Prop :=
  ∃ T : ℕ → ℕ → ℕ, (∀ m ≤ auxLen n, T n m ≤ t) ∧ ComputesInTime output T adversary

/-- At parameter `n` on empty auxiliary input `[]`, `adversary` is realized by a uniform halting
fair-coin machine taking at most `t` steps. -/
abbrev WithinTime {β : Type} (output : β ↪ List Bool) :
    ℕ → ℕ → (ℕ → List Bool → ProbComp β) → Prop :=
  WithinTimeUpTo output (fun _ => 0)

/-- `WithinTime` unpacks to `T n 0 ≤ t` for a uniform halting schedule `T`. -/
theorem withinTime_iff {β : Type} {output : β ↪ List Bool} {n t : ℕ}
    {adversary : ℕ → List Bool → ProbComp β} :
    WithinTime output n t adversary ↔
      ∃ T : ℕ → ℕ → ℕ, T n 0 ≤ t ∧ ComputesInTime output T adversary := by
  simp [WithinTime, WithinTimeUpTo]

/-- At parameter `n`, `adversary` is realized by a uniform halting oracle machine taking at most `t`
steps on all auxiliary inputs of length at most `auxLen n`. -/
@[expose] def WithinOracleTimeUpTo {Operation β : Type} [DecidableEq Operation]
    (output : β ↪ List Bool) (auxLen : ℕ → ℕ)
    (n t : ℕ) (adversary : ℕ → List Bool → WordOracleComp Operation β) : Prop :=
  ∃ T : ℕ → ℕ → ℕ, (∀ m ≤ auxLen n, T n m ≤ t) ∧ ComputesOracleInTime output T adversary

/-- At parameter `n` on empty auxiliary input `[]`, `adversary` is realized by a uniform halting
oracle machine taking at most `t` steps. -/
abbrev WithinOracleTime {Operation β : Type} [DecidableEq Operation]
    (output : β ↪ List Bool) :
    ℕ → ℕ → (ℕ → List Bool → WordOracleComp Operation β) → Prop :=
  WithinOracleTimeUpTo output (fun _ => 0)

/-- `WithinOracleTime` unpacks to `T n 0 ≤ t` for a uniform halting oracle schedule `T`. -/
theorem withinOracleTime_iff {Operation β : Type} [DecidableEq Operation]
    {output : β ↪ List Bool} {n t : ℕ}
    {adversary : ℕ → List Bool → WordOracleComp Operation β} :
    WithinOracleTime output n t adversary ↔
      ∃ T : ℕ → ℕ → ℕ, T n 0 ≤ t ∧ ComputesOracleInTime output T adversary := by
  simp [WithinOracleTime, WithinOracleTimeUpTo]

/-- Joint `(t, q)` concrete adversary predicate at parameter `n`: `adversary` is realized by a
uniform halting oracle machine within `t` steps on `(n, [])` and makes at most `q` external queries
on `(n, [])`. -/
@[expose] def WithinTimeAndQueries {Operation β : Type} [DecidableEq Operation]
    (output : β ↪ List Bool) (n : ℕ) (r : ℕ × ℕ)
    (adversary : ℕ → List Bool → WordOracleComp Operation β) : Prop :=
  WithinOracleTime output n r.1 adversary ∧ (adversary n []).IsQueryBounded r.2

/-- Because `ComputesInTime.mono` holds unconditionally without computability of the padded
schedule, concrete `(WithinTime, ε)`-security is equivalent to bounding advantage at `T n 0` for
every `ComputesInTime` schedule `T`. -/
theorem indistinguishableWithin_withinTime_iff {β : Type} (output : β ↪ List Bool)
    (game1 game2 : (ℕ → List Bool → ProbComp β) → ℕ → Game) (ε : ℕ → ℕ → ℝ≥0) :
    IndistinguishableWithin game1 game2 (WithinTime output) ε ↔
      ∀ T adversary, ComputesInTime output T adversary →
        ∀ n, advantage (game1 adversary n) (game2 adversary n) ≤ ε n (T n 0) := by
  constructor
  · intro h T adversary hT n
    exact h n (T n 0) adversary (withinTime_iff.mpr ⟨T, le_rfl, hT⟩)
  · intro h n t adversary hw
    obtain ⟨T, hle, hT⟩ := withinTime_iff.mp hw
    let T' : ℕ → ℕ → ℕ := fun n' m' => if n' = n ∧ m' = 0 then t else T n' m'
    have hT' : ComputesInTime output T' adversary := hT.mono fun n' m' => by
      dsimp only [T']
      split_ifs with hnm
      · rcases hnm with ⟨rfl, rfl⟩; exact hle
      · exact le_rfl
    simpa [T'] using h T' adversary hT' n

/-- Concrete `(WithinTimeAndQueries, ε)`-security is equivalent to bounding advantage at
`(T n 0, Q n)` for every `ComputesOracleInTime` schedule `T` and query schedule `Q`. -/
theorem indistinguishableWithin_withinTimeAndQueries_iff {Operation β : Type}
    [DecidableEq Operation] (output : β ↪ List Bool)
    (game1 game2 : (ℕ → List Bool → WordOracleComp Operation β) → ℕ → Game)
    (ε : ℕ → ℕ × ℕ → ℝ≥0) :
    IndistinguishableWithin game1 game2 (WithinTimeAndQueries output) ε ↔
      ∀ (T : ℕ → ℕ → ℕ) (Q : ℕ → ℕ) adversary, ComputesOracleInTime output T adversary →
        (∀ n, (adversary n []).IsQueryBounded (Q n)) →
        ∀ n, advantage (game1 adversary n) (game2 adversary n) ≤ ε n (T n 0, Q n) := by
  constructor
  · intro h T Q adversary hT hQ n
    exact h n (T n 0, Q n) adversary ⟨withinOracleTime_iff.mpr ⟨T, le_rfl, hT⟩, hQ n⟩
  · intro h n r adversary ⟨ht, hq⟩
    obtain ⟨T, hle, hT⟩ := withinOracleTime_iff.mp ht
    let T' : ℕ → ℕ → ℕ := fun n' m' => if n' = n ∧ m' = 0 then r.1 else T n' m'
    let Q' : ℕ → ℕ := fun n' => if n' = n then r.2 else T' n' 0
    have hT' : ComputesOracleInTime output T' adversary := hT.mono fun n' m' => by
      dsimp only [T']
      split_ifs with hnm
      · rcases hnm with ⟨rfl, rfl⟩; exact hle
      · exact le_rfl
    have hQ' : ∀ n', (adversary n' []).IsQueryBounded (Q' n') := fun n' => by
      dsimp only [Q']
      split_ifs with hn
      · subst hn; exact hq
      · exact hT'.isQueryBounded n' []
    simpa [T', Q'] using h T' Q' adversary hT' hQ' n

/-! ### Direct concrete-to-asymptotic bridges for `IsOraclePPT` and `IsPPT` -/

/-- **Query-bounded concrete-to-asymptotic bridge.** If every `Q`-query execution `adversary n []`
has advantage at most `ε n Q` and `n ↦ ε n (Q n)` is negligible along every polynomially bounded
schedule `Q`, then `game1` and `game2` are asymptotically indistinguishable against
`IsOraclePPT`. -/
theorem Indistinguishable.of_queryBounded {Operation β : Type} [DecidableEq Operation]
    {output : β ↪ List Bool}
    {game1 game2 : (ℕ → List Bool → WordOracleComp Operation β) → ℕ → Game}
    (ε : ℕ → ℕ → ℝ≥0)
    (hbound : ∀ n Q adversary, (adversary n []).IsQueryBounded Q →
      advantage (game1 adversary n) (game2 adversary n) ≤ ε n Q)
    (hneg : ∀ Q : ℕ → ℕ, PolynomiallyBounded Q → Negligible (fun n => ε n (Q n))) :
    Indistinguishable game1 game2 (IsOraclePPT output) := by
  refine IndistinguishableWithin.indistinguishable (Within := WithinQueries) PolynomiallyBounded
    hbound (fun adversary hadversary => ?_) hneg
  obtain ⟨Q, _, hpoly, hQ⟩ := hadversary.exists_computable_queryBound
  exact ⟨Q, hpoly, fun n => by simpa [WithinQueries] using (hQ n []).1⟩

/-- Real-valued variant of `Game.Indistinguishable.of_queryBounded`, directly accepting switching
and collision lemmas stated as `(Game.advantage … : ℝ) ≤ ε n Q`. -/
theorem Indistinguishable.of_queryBounded_real {Operation β : Type} [DecidableEq Operation]
    {output : β ↪ List Bool}
    {game1 game2 : (ℕ → List Bool → WordOracleComp Operation β) → ℕ → Game}
    (ε : ℕ → ℕ → ℝ≥0)
    (hbound : ∀ n Q adversary, (adversary n []).IsQueryBounded Q →
      (advantage (game1 adversary n) (game2 adversary n) : ℝ) ≤ ε n Q)
    (hneg : ∀ Q : ℕ → ℕ, PolynomiallyBounded Q → Negligible (fun n => ε n (Q n))) :
    Indistinguishable game1 game2 (IsOraclePPT output) :=
  Indistinguishable.of_queryBounded ε
    (fun n Q adversary hQ => NNReal.coe_le_coe.mp (hbound n Q adversary hQ)) hneg

/-- Birthday-collision specialization of `Game.Indistinguishable.of_queryBounded_real` for concrete
switching bounds of the form `k * (Q.choose 2 : ℝ≥0) * base n` with `Negligible base` (for
example PRP–PRF switching with `k = 1` and Luby–Rackoff with `k = 3` or `4`). -/
theorem Indistinguishable.of_birthday_queryBounded_real {Operation β : Type}
    [DecidableEq Operation] {output : β ↪ List Bool}
    {game1 game2 : (ℕ → List Bool → WordOracleComp Operation β) → ℕ → Game}
    (k : ℕ) {base : ℕ → ℝ≥0} (hbase : Negligible base)
    (hbound : ∀ n Q adversary, (adversary n []).IsQueryBounded Q →
      (advantage (game1 adversary n) (game2 adversary n) : ℝ) ≤
        ((k : ℝ≥0) * (Q.choose 2 : ℝ≥0) * base n : ℝ≥0)) :
    Indistinguishable game1 game2 (IsOraclePPT output) :=
  Indistinguishable.of_queryBounded_real
    (fun n Q => (k : ℝ≥0) * (Q.choose 2 : ℝ≥0) * base n) hbound
    fun Q hQ => by
      simpa only [Nat.cast_mul] using hbase.polynomiallyBounded_mul
        ((PolynomiallyBounded.const k).mul hQ.choose_two)

/-- General auxiliary-input variant of `Game.Indistinguishable.of_queryBounded` for games invoking
`adversary n (aux n)` along a polynomially bounded auxiliary word length. -/
theorem Indistinguishable.of_queryBounded_aux {Operation β : Type} [DecidableEq Operation]
    {output : β ↪ List Bool}
    {game1 game2 : (ℕ → List Bool → WordOracleComp Operation β) → ℕ → Game}
    (aux : ℕ → List Bool) (haux : PolynomiallyBounded (fun n => (aux n).length))
    (ε : ℕ → ℕ → ℝ≥0)
    (hbound : ∀ n Q adversary, (adversary n (aux n)).IsQueryBounded Q →
      advantage (game1 adversary n) (game2 adversary n) ≤ ε n Q)
    (hneg : ∀ Q : ℕ → ℕ, PolynomiallyBounded Q → Negligible (fun n => ε n (Q n))) :
    Indistinguishable game1 game2 (IsOraclePPT output) := by
  intro adversary hadversary
  obtain ⟨Q₀, _, hQ₀, hbounds⟩ := hadversary.exists_computable_queryBound
  let Q : ℕ → ℕ := fun n => Q₀ (n + (aux n).length)
  have hQ : PolynomiallyBounded Q := hQ₀.comp (PolynomiallyBounded.id.add haux)
  exact negligible_of_le (hneg Q hQ) fun n => hbound n (Q n) adversary (hbounds n (aux n)).1

/-- One-sided search/forgery variant of `Game.Indistinguishable.of_queryBounded` against
`PMF.pure false`. -/
theorem Indistinguishable.of_succProbability_queryBounded {Operation β : Type}
    [DecidableEq Operation] {output : β ↪ List Bool}
    {game : (ℕ → List Bool → WordOracleComp Operation β) → ℕ → Game}
    (ε : ℕ → ℕ → ℝ≥0)
    (hbound : ∀ n Q adversary, (adversary n []).IsQueryBounded Q →
      succProbability (game adversary n) ≤ ε n Q)
    (hneg : ∀ Q : ℕ → ℕ, PolynomiallyBounded Q → Negligible (fun n => ε n (Q n))) :
    Indistinguishable game (fun _ _ => PMF.pure false) (IsOraclePPT output) :=
  Indistinguishable.of_queryBounded ε (fun n Q adversary hQ => by
    simpa using hbound n Q adversary hQ) hneg

/-- Cost-bounded variant of `Game.Indistinguishable.of_queryBounded` for any per-request cost bound
`cost op ≤ B` (for instance charging `1` on signing calls and `0` on hash calls). -/
theorem Indistinguishable.of_costBounded {Operation β : Type} [DecidableEq Operation]
    {output : β ↪ List Bool}
    {game1 game2 : (ℕ → List Bool → WordOracleComp Operation β) → ℕ → Game}
    (cost : Operation × List Bool → ℕ) (B : ℕ) (hcost : ∀ req, cost req ≤ B)
    (ε : ℕ → ℕ → ℝ≥0)
    (hbound : ∀ n K adversary,
      OracleComp.IsCostBounded (Sum.elim (fun _ => 0) cost) (adversary n []) K →
      advantage (game1 adversary n) (game2 adversary n) ≤ ε n K)
    (hneg : ∀ K : ℕ → ℕ, PolynomiallyBounded K → Negligible (fun n => ε n (K n))) :
    Indistinguishable game1 game2 (IsOraclePPT output) := by
  refine Indistinguishable.of_queryBounded (fun n Q => ε n (B * Q)) (fun n Q adversary hQ => ?_)
    (fun Q hQ => hneg (fun n => B * Q n) ((PolynomiallyBounded.const B).mul hQ))
  refine hbound n (B * Q) adversary ?_
  have hmul : ∀ {p : WordOracleComp Operation β} {Q : ℕ},
      p.IsQueryBounded Q →
      OracleComp.IsCostBounded (Sum.elim (fun _ => 0) cost) p (B * Q) := by
    intro p Q h
    induction h with
    | pure a n => exact .pure a (B * n)
    | liftBind q cont n _ ih =>
      refine (OracleComp.IsCostBounded.liftBind q cont (B * n) ih).mono ?_
      cases q with
      | inl _ => simp
      | inr req =>
        simp only [Sum.elim_inr, mul_add, mul_one]
        exact Nat.add_le_add_left (hcost req) (B * n)
  exact hmul hQ

/-- **Query-schedule-parameterized reduction to asymptotic security.** Covers hybrid and tree
reductions (such as GGM) whose reduction algorithm `reduce adversary Q` takes an explicit unary
polynomial-time computable query bound `Q : ℕ → ℕ` for `adversary`. -/
theorem Indistinguishable.of_queryBounded_reduction {SourceAdversary Operation β : Type}
    [DecidableEq Operation] {output : β ↪ List Bool}
    {source1 source2 : SourceAdversary → ℕ → Game}
    {target1 target2 : (ℕ → List Bool → WordOracleComp Operation β) → ℕ → Game}
    {SourceAdmissible : SourceAdversary → Prop}
    (hsource : Indistinguishable source1 source2 SourceAdmissible)
    (reduce : (ℕ → List Bool → WordOracleComp Operation β) → (ℕ → ℕ) → SourceAdversary)
    (loss : ℕ → ℕ → ℕ) (err : ℕ → ℕ → ℝ≥0)
    (hadmissible : ∀ adversary Q, IsOraclePPT output adversary →
      ComputableInPolyTime Q encUnary encUnary → PolynomiallyBounded Q →
      SourceAdmissible (reduce adversary Q))
    (hloss : ∀ Q : ℕ → ℕ, PolynomiallyBounded Q → PolynomiallyBounded (fun n => loss n (Q n)))
    (herr : ∀ Q : ℕ → ℕ, PolynomiallyBounded Q → Negligible (fun n => err n (Q n)))
    (hbound : ∀ adversary Q n, (adversary n []).IsQueryBounded (Q n) →
      advantage (target1 adversary n) (target2 adversary n) ≤
        loss n (Q n) * advantage (source1 (reduce adversary Q) n)
          (source2 (reduce adversary Q) n) + err n (Q n)) :
    Indistinguishable target1 target2 (IsOraclePPT output) := by
  intro adversary hadversary
  obtain ⟨Q, hQcomp, hQpoly, hQbounds⟩ := hadversary.exists_computable_queryBound
  have hsrc := hsource (reduce adversary Q) (hadmissible adversary Q hadversary hQcomp hQpoly)
  have hl := hloss Q hQpoly
  have he := herr Q hQpoly
  refine negligible_of_le ((hsrc.polynomiallyBounded_mul hl).add he) fun n => ?_
  exact hbound adversary Q n (by simpa using (hQbounds n []).1)

/-- **Concrete `(t, ε)` security implies asymptotic `IsPPT` security** on bounded-length auxiliary
inputs (`auxLen : ℕ → ℕ` polynomially bounded). -/
theorem Indistinguishable.of_timeBounded_upTo {β : Type} {output : β ↪ List Bool}
    {game1 game2 : (ℕ → List Bool → ProbComp β) → ℕ → Game}
    (auxLen : ℕ → ℕ) (haux : PolynomiallyBounded auxLen)
    (ε : ℕ → ℕ → ℝ≥0)
    (h : IndistinguishableWithin game1 game2 (WithinTimeUpTo output auxLen) ε)
    (hneg : ∀ T : ℕ → ℕ, PolynomiallyBounded T → Negligible (fun n => ε n (T n))) :
    Indistinguishable game1 game2 (IsPPT output) := by
  refine h.indistinguishable PolynomiallyBounded (fun adversary hadversary => ?_) hneg
  obtain ⟨T₀, hT₀, hcomp⟩ := isPPT_iff_exists_polyBounded_computesInTime.mp hadversary
  obtain ⟨c, d, hle⟩ := hT₀.exists_le
  let B : ℕ → ℕ := fun n => c * (n + auxLen n + 1) ^ d
  have hB : PolynomiallyBounded B :=
    (PolynomiallyBounded.const c).mul
      (((PolynomiallyBounded.id.add haux).add (.const 1)).pow d)
  refine ⟨B, hB, fun n => ⟨T₀, fun m hm => ?_, hcomp⟩⟩
  exact (hle (n, m)).trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d))

/-- **Concrete `(t, ε)` security implies asymptotic `IsPPT` security** on empty auxiliary input. -/
theorem Indistinguishable.of_timeBounded {β : Type} {output : β ↪ List Bool}
    {game1 game2 : (ℕ → List Bool → ProbComp β) → ℕ → Game}
    (ε : ℕ → ℕ → ℝ≥0)
    (h : IndistinguishableWithin game1 game2 (WithinTime output) ε)
    (hneg : ∀ T : ℕ → ℕ, PolynomiallyBounded T → Negligible (fun n => ε n (T n))) :
    Indistinguishable game1 game2 (IsPPT output) :=
  Indistinguishable.of_timeBounded_upTo (fun _ => 0) (.const 0) ε h hneg

/-- **Concrete `(t, q, ε)` security implies asymptotic `IsOraclePPT` security.** -/
theorem Indistinguishable.of_timeAndQueryBounded {Operation β : Type} [DecidableEq Operation]
    {output : β ↪ List Bool}
    {game1 game2 : (ℕ → List Bool → WordOracleComp Operation β) → ℕ → Game}
    (ε : ℕ → ℕ × ℕ → ℝ≥0)
    (h : IndistinguishableWithin game1 game2 (WithinTimeAndQueries output) ε)
    (hneg : ∀ T Q : ℕ → ℕ, PolynomiallyBounded T → PolynomiallyBounded Q →
      Negligible (fun n => ε n (T n, Q n))) :
    Indistinguishable game1 game2 (IsOraclePPT output) := by
  refine h.indistinguishable
    (fun r : ℕ → ℕ × ℕ =>
      PolynomiallyBounded (fun n => (r n).1) ∧ PolynomiallyBounded (fun n => (r n).2))
    (fun adversary hadversary => ?_)
    (fun r ⟨hT, hQ⟩ => hneg (fun n => (r n).1) (fun n => (r n).2) hT hQ)
  obtain ⟨T₀, Q₀, hT₀, hQ₀, hcomp, hqueries⟩ :=
    isOraclePPT_iff_exists_polyBounded_computesOracleInTimeAndQueries.mp hadversary
  obtain ⟨ct, dt, hlet⟩ := hT₀.exists_le
  obtain ⟨cq, dq, hleq⟩ := hQ₀.exists_le
  let T : ℕ → ℕ := fun n => ct * (n + 1) ^ dt
  let Q : ℕ → ℕ := fun n => cq * (n + 1) ^ dq
  have hT : PolynomiallyBounded T :=
    (PolynomiallyBounded.const ct).mul ((PolynomiallyBounded.id.add (.const 1)).pow dt)
  have hQ : PolynomiallyBounded Q :=
    (PolynomiallyBounded.const cq).mul ((PolynomiallyBounded.id.add (.const 1)).pow dq)
  refine ⟨fun n => (T n, Q n), ⟨hT, hQ⟩, fun n => ?_⟩
  refine ⟨withinOracleTime_iff.mpr ⟨T₀, ?_, hcomp⟩, ?_⟩
  · simpa [T] using hlet (n, 0)
  · exact (hqueries n []).mono (by simpa [Q] using hleq (n, 0))

end Cslib.Crypto.Game

/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Game.CloseTo.RandomOracle
public import CslibFrontier.Crypto.Game.UntilBad
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.Event

/-!
# Stateful `ProbOracleComp` Until-Bad and Random-Oracle Programming/Birthday Tests

Exercises the reusable until-bad flag combinators, triangular `choose 2` union bounds, and
random-oracle min-entropy programming and birthday collision lemmas on concrete fixtures:

1. **Triangular `choose 2` union bound (`OracleComp.toOuterMeasure_bad_choose_two_le`) and concrete
   sharpness**: a 2-draw uniform `Bool` collision step wrapped with `withBadFlag` satisfies the
   upper bound `((2).choose 2 : ℝ≥0∞) / 2 = 1 / 2` and attains exact collision probability `1 / 2`.
2. **`ProbOracleComp.IdenticalUntilBad`, monotone `withBadFlag`, marginal projection, and
   `Game.advantage`**: two stateful external handlers on `Bool → StateT ℕ PMF Bool` differing only
   on a `1 / 4`-probability coin outcome `r = 0` are related via
   `ProbOracleComp.identicalUntilBad_withBadFlag` and `ProbOracleComp.runWith_withBadFlag_map_fst`,
   yielding a `1 / 2` distinguishing-advantage bound on a randomized 2-query `ProbOracleComp`
   adversary with private coin sampling.
3. **Min-entropy list-key collision (`RandomOracle.toOuterMeasure_exists_mem_fst_eq_le`)**: uniform
   draws on `Fin 4` match a key of the 2-entry cache `[(0, true), (2, false)]` with exact
   probability `1 / 2`, matching the `cache.length * (1 / 4)` bound.
4. **Adaptive RO programming (`lazyProgramHandler` vs. `overwriteProgramHandler`)**: for a
   randomized client making `q_S = 2` programming calls (`δ = 1 / 4` on `Fin 8`) and `q_H = 1`
   direct hash query from an empty cache, the sharpened `choose 2` bound gives nontrivial error
   `3 / 4` (`(2 * 1 + (2).choose 2) * (1 / 4)`), strictly improving the vacuous rectangular bound
   `3 / 2` (`2 * (2 + 1) * (1 / 4)`).
5. **Random-oracle birthday bound (`q.choose 2 / Fintype.card Digest`) and sharpness at `q = 2` on
   `Bool`**: `toOuterMeasure_collision_memoize_uniform_le`,
   `toOuterMeasure_hasOutputCollision_memoize_uniform_le`, and
   `toOuterMeasure_hasOutputCollision_runWith_memoize_uniform_le` yield `1 / 2` at `q = 2` on
   `Digest = Bool`, and querying `false` then `true` attains `HasOutputCollision` with exact
   probability `1 / 2`.
-/

public section

namespace CslibFrontierTests.Crypto.UntilBadROMFramework

open Cslib Cslib.OracleComp Cslib.ProbOracleComp Cslib.RandomOracle Cslib.Crypto Cslib.Probability
open scoped ENNReal NNReal

private theorem two_inv_mul_two_inv_add_eq :
    (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
  have h2 : (2 : ℝ≥0∞)⁻¹ = ((2⁻¹ : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_inv (by norm_num)).symm
  rw [h2]
  norm_cast
  norm_num

private theorem four_inv_add_four_inv_eq :
    (4 : ℝ≥0∞)⁻¹ + (4 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
  have h4 : (4 : ℝ≥0∞)⁻¹ = ((4⁻¹ : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_inv (by norm_num)).symm
  have h2 : (2 : ℝ≥0∞)⁻¹ = ((2⁻¹ : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_inv (by norm_num)).symm
  rw [h4, h2]
  norm_cast
  norm_num

/-! ### 1. Triangular `choose 2` Union Bound and Concrete Sharpness on `Bool` -/

/-- Step kernel drawing a uniform `Bool`, prepending it to `seen`, and flagging `b ∈ seen`. -/
noncomputable def boolDrawStep (_ : Unit) (seen : List Bool) : PMF (Bool × (List Bool × Bool)) :=
  (PMF.uniformOfFintype Bool).map fun b => (b, (b :: seen, decide (b ∈ seen)))

/-- Two-query deterministic client against `Unit → Bool`. -/
def twoUnitQueries : OracleComp (fun _ : Unit => Bool) (Bool × Bool) :=
  OracleComp.query () >>= fun b₀ =>
    OracleComp.query () >>= fun b₁ =>
      pure (b₀, b₁)

theorem twoUnitQueries_isQueryBounded : OracleComp.IsQueryBounded twoUnitQueries 2 :=
  ((OracleComp.IsCostBounded.query ()).bind fun b₀ =>
    (OracleComp.IsCostBounded.query ()).bind fun b₁ =>
      OracleComp.IsCostBounded.pure (b₀, b₁) 0).mono (by omega)

private theorem step_bad_boolDrawStep (q : Unit) (st : List Bool × Bool) (hst : ¬FlagBad st) :
    (withBadFlag boolDrawStep q st).toOuterMeasure {x | FlagBad x.2} ≤
      st.1.length * (2 : ℝ≥0∞)⁻¹ := by
  obtain ⟨seen, b⟩ := st
  have hb : b = false := Bool.eq_false_iff.mpr hst
  subst hb
  rw [withBadFlag_false, boolDrawStep, PMF.toOuterMeasure_map_apply]
  have hsub : (fun x : Bool => (x, (x :: seen, decide (x ∈ seen)))) ⁻¹' {y | FlagBad y.2} ⊆
      {x : Bool | ∃ e ∈ seen.map (·, ()), e.1 = id x} := by
    intro x hx
    change decide (x ∈ seen) = true at hx
    exact ⟨(x, ()), List.mem_map_of_mem (of_decide_eq_true hx), rfl⟩
  refine (MeasureTheory.measure_mono hsub).trans ?_
  have hunif : ∀ y : Bool, ((PMF.uniformOfFintype Bool).map id) y ≤ (2 : ℝ≥0∞)⁻¹ := by
    intro y
    simp [PMF.uniformOfFintype_apply]
  simpa only [List.length_map] using
    toOuterMeasure_exists_mem_fst_eq_le hunif (seen.map (·, ()))

private theorem grow_boolDrawStep (q : Unit) (st : List Bool × Bool) (_ : ¬FlagBad st)
    (x : Bool × (List Bool × Bool)) (hx : x ∈ (withBadFlag boolDrawStep q st).support)
    (_ : ¬FlagBad x.2) :
    x.2.1.length ≤ st.1.length + 1 := by
  obtain ⟨seen, b⟩ := st
  simp only [withBadFlag, boolDrawStep, PMF.mem_support_map_iff] at hx
  obtain ⟨_, ⟨d, -, rfl⟩, rfl⟩ := hx
  simp

/-- Applying `OracleComp.toOuterMeasure_bad_choose_two_le` bounds 2 uniform `Bool` draws by
`((2).choose 2) * 2⁻¹ = 2⁻¹`. -/
theorem toOuterMeasure_bad_twoUnitQueries_le :
    ((OracleComp.interpret (withBadFlag boolDrawStep) twoUnitQueries).run
      ([], false)).toOuterMeasure {x | FlagBad x.2} ≤ (2 : ℝ≥0∞)⁻¹ := by
  have h := OracleComp.toOuterMeasure_bad_choose_two_le (fun st : List Bool × Bool => st.1.length)
    (2 : ℝ≥0∞)⁻¹ step_bad_boolDrawStep grow_boolDrawStep twoUnitQueries_isQueryBounded
    (s := ([], false)) Bool.false_ne_true
  simpa using h

/-- Concrete sharpness: `twoUnitQueries` hits `FlagBad` with exact probability `2⁻¹`. -/
theorem toOuterMeasure_bad_twoUnitQueries_eq :
    ((OracleComp.interpret (withBadFlag boolDrawStep) twoUnitQueries).run
      ([], false)).toOuterMeasure {x | FlagBad x.2} = (2 : ℝ≥0∞)⁻¹ := by
  simp only [twoUnitQueries, run_interpret_bind, run_interpret_query, run_interpret_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, withBadFlag, boolDrawStep, PMF.map_comp,
    PMF.bind_map, PMF.toOuterMeasure_bind_apply, tsum_fintype, Fintype.sum_bool,
    PMF.uniformOfFintype_apply, Fintype.card_bool]
  simpa [FlagBad, Prod.map] using two_inv_mul_two_inv_add_eq

/-! ### 2. `ProbOracleComp.IdenticalUntilBad`, Monotone `withBadFlag`, and `Game.advantage` -/

/-- Unflagged external handler 1: draws `r ← unif (Fin 4)` and overrides reply to `true` on `r = 0`.
-/
noncomputable def trapTrueHandler (q : Bool) (s : ℕ) : PMF (Bool × ℕ) :=
  (PMF.uniformOfFintype (Fin 4)).map fun r => (if r = 0 then true else q, s + 1)

/-- Unflagged external handler 2: draws `r ← unif (Fin 4)` and overrides reply to `false` on
`r = 0`. -/
noncomputable def trapFalseHandler (q : Bool) (s : ℕ) : PMF (Bool × ℕ) :=
  (PMF.uniformOfFintype (Fin 4)).map fun r => (if r = 0 then false else q, s + 1)

/-- Flagged step kernel for `trapTrueHandler`, flagging `r = 0`. -/
noncomputable def trapTrueStep (q : Bool) (s : ℕ) : PMF (Bool × (ℕ × Bool)) :=
  (PMF.uniformOfFintype (Fin 4)).map fun r =>
    (if r = 0 then true else q, (s + 1, decide (r = 0)))

/-- Flagged step kernel for `trapFalseHandler`, flagging `r = 0`. -/
noncomputable def trapFalseStep (q : Bool) (s : ℕ) : PMF (Bool × (ℕ × Bool)) :=
  (PMF.uniformOfFintype (Fin 4)).map fun r =>
    (if r = 0 then false else q, (s + 1, decide (r = 0)))

private theorem trapStep_agree (q : Bool) (s : ℕ) (a : Bool) (s' : ℕ) :
    trapTrueStep q s (a, (s', false)) = trapFalseStep q s (a, (s', false)) := by
  simp only [trapTrueStep, trapFalseStep, PMF.map_apply]
  refine tsum_congr fun r => ?_
  by_cases hr : r = 0
  · subst hr; simp
  · simp [hr]

/-- `ProbOracleComp.identicalUntilBad_withBadFlag` relates the two `withBadFlag` handlers across
private randomness automatically. -/
theorem identicalUntilBad_trapSteps :
    ProbOracleComp.IdenticalUntilBad (withBadFlag trapTrueStep) (withBadFlag trapFalseStep)
      FlagBad :=
  ProbOracleComp.identicalUntilBad_withBadFlag trapTrueStep trapFalseStep trapStep_agree

/-- Randomized client drawing 1 private coin (`unifFin 1`) and making 2 adaptive external queries.
-/
def randomizedTwoQueryClient : ProbOracleComp (fun _ : Bool => Bool) Bool :=
  ProbOracleComp.sample (ProbComp.unifFin 1) >>= fun coin =>
    ProbOracleComp.query (coin == 1) >>= fun r₀ =>
      ProbOracleComp.query (!r₀) >>= fun r₁ =>
        pure (r₀ && r₁)

theorem randomizedTwoQueryClient_isQueryBounded :
    randomizedTwoQueryClient.IsQueryBounded 2 :=
  ((ProbOracleComp.isCostBounded_sample (spec := fun _ : Bool => Bool) (fun _ => 1)
      (ProbComp.unifFin 1)).bind fun coin =>
    (ProbOracleComp.isCostBounded_query (spec := fun _ : Bool => Bool) (fun _ => 1)
      (coin == 1)).bind fun r₀ =>
      (ProbOracleComp.isCostBounded_query (spec := fun _ : Bool => Bool) (fun _ => 1)
        (!r₀)).bind fun r₁ =>
        OracleComp.IsCostBounded.pure (r₀ && r₁) 0).mono (by omega)

/-- Dropping the Boolean bad flag recovers the unflagged `ProbOracleComp.runWith` distribution. -/
theorem runWith_trapTrueStep_map_fst :
    (ProbOracleComp.runWith (withBadFlag trapTrueStep) randomizedTwoQueryClient (0, false)).map
        (Prod.map id Prod.fst) =
      ProbOracleComp.runWith trapTrueHandler randomizedTwoQueryClient 0 :=
  ProbOracleComp.runWith_withBadFlag_map_fst trapTrueStep trapTrueHandler
    (fun q s => by rw [trapTrueStep, trapTrueHandler, PMF.map_comp]; rfl)
    randomizedTwoQueryClient 0 false

/-- Combining `ProbOracleComp.IdenticalUntilBad.advantage_le`, `runWith_withBadFlag_map_fst`, and
`ProbOracleComp.toOuterMeasure_bad_le` bounds distinguishing advantage on `randomizedTwoQueryClient`
by `2 * (1 / 4) = 1 / 2`. -/
theorem advantage_trapHandlers_randomizedTwoQueryClient_le :
    (Game.advantage
      ((ProbOracleComp.runWith trapTrueHandler randomizedTwoQueryClient 0).map Prod.fst)
      ((ProbOracleComp.runWith trapFalseHandler randomizedTwoQueryClient 0).map Prod.fst) : ℝ) ≤
      1 / 2 := by
  have hl := congrArg (PMF.map Prod.fst) runWith_trapTrueStep_map_fst
  have hr := congrArg (PMF.map Prod.fst)
    (ProbOracleComp.runWith_withBadFlag_map_fst trapFalseStep trapFalseHandler
      (fun q s => by rw [trapFalseStep, trapFalseHandler, PMF.map_comp]; rfl)
      randomizedTwoQueryClient 0 false)
  simp only [PMF.map_comp, Function.comp_def, Prod.map] at hl hr
  rw [← hl, ← hr, ← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  refine (identicalUntilBad_trapSteps.advantage_le randomizedTwoQueryClient (0, false)
    (fun out => PMF.pure out.1)).trans ?_
  have hbad := ProbOracleComp.toOuterMeasure_bad_le
    (handler := withBadFlag trapTrueStep) (bad := FlagBad) (fun _ : Bool => 1)
    (fun _ : ℕ × Bool => ((4⁻¹ : ℝ≥0) : ℝ≥0∞)) 0
    (fun q ⟨s, b⟩ hst => by
      have hb : b = false := Bool.eq_false_iff.mpr hst
      subst hb
      rw [withBadFlag_false, trapTrueStep, PMF.toOuterMeasure_map_apply]
      simp only [one_mul, Nat.cast_one, PMF.toOuterMeasure_apply, tsum_fintype,
        Fin.sum_univ_four]
      simp [PMF.uniformOfFintype_apply, FlagBad, Set.indicator])
    (fun _ _ _ _ _ _ => by simp)
    randomizedTwoQueryClient_isQueryBounded randomizedTwoQueryClient_isQueryBounded
    (s := (0, false)) Bool.false_ne_true
  have hbad' : (ProbOracleComp.runWith (withBadFlag trapTrueStep) randomizedTwoQueryClient
      (0, false)).toOuterMeasure {x | FlagBad x.2} ≤ ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
    refine hbad.trans ?_
    simp only [mul_zero, add_zero]
    change (((2 : ℕ) : ℝ≥0) : ℝ≥0∞) * ((4⁻¹ : ℝ≥0) : ℝ≥0∞) ≤ ((1 / 2 : ℝ≥0) : ℝ≥0∞)
    norm_cast
    norm_num
  exact (ENNReal.toReal_mono ENNReal.coe_ne_top hbad').trans_eq (by norm_num)

/-! ### 3. Min-Entropy List-Key Collision (`toOuterMeasure_exists_mem_fst_eq_le`) -/

/-- A 2-entry cache on `Fin 4` has a key hit by a uniform draw with probability at most
`2 * 4⁻¹ = 2⁻¹`, and in fact with exact probability `2⁻¹`. -/
theorem exists_mem_fst_fin4_two_entries :
    (PMF.uniformOfFintype (Fin 4)).toOuterMeasure
        {x : Fin 4 | ∃ e ∈ ([(0, true), (2, false)] : List (Fin 4 × Bool)), e.1 = id x} ≤
      (2 : ℝ≥0∞)⁻¹ ∧
    (PMF.uniformOfFintype (Fin 4)).toOuterMeasure
        {x : Fin 4 | ∃ e ∈ ([(0, true), (2, false)] : List (Fin 4 × Bool)), e.1 = id x} =
      (2 : ℝ≥0∞)⁻¹ := by
  have heq : (PMF.uniformOfFintype (Fin 4)).toOuterMeasure
      {x : Fin 4 | ∃ e ∈ ([(0, true), (2, false)] : List (Fin 4 × Bool)), e.1 = id x} =
      (2 : ℝ≥0∞)⁻¹ := by
    classical
    simp only [PMF.toOuterMeasure_apply, tsum_fintype, Fin.sum_univ_four]
    simpa [PMF.uniformOfFintype_apply, Set.indicator] using four_inv_add_four_inv_eq
  refine ⟨?_, heq⟩
  have h := RandomOracle.toOuterMeasure_exists_mem_fst_eq_le
    (μ := PMF.uniformOfFintype (Fin 4)) (f := id) (δ := ((4⁻¹ : ℝ≥0) : ℝ≥0∞))
    (fun q => by simp [PMF.uniformOfFintype_apply])
    ([(0, true), (2, false)] : List (Fin 4 × Bool))
  refine h.trans_eq ?_
  have h2 : (2 : ℝ≥0∞)⁻¹ = ((2⁻¹ : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_inv (by norm_num)).symm
  rw [List.length_cons, List.length_singleton, h2]
  change (((2 : ℕ) : ℝ≥0) : ℝ≥0∞) * ((4⁻¹ : ℝ≥0) : ℝ≥0∞) = ((2⁻¹ : ℝ≥0) : ℝ≥0∞)
  norm_cast
  norm_num

/-! ### 4. Adaptive RO Programming: Sharpened `choose 2` vs. Rectangular Bound -/

/-- Injection embedding `Fin 4` pre-challenge coins into `Fin 8` random-oracle keys. -/
def embedFin4ToFin8 (r : Fin 4) : Fin 8 := ⟨r.val, by omega⟩

theorem injective_embedFin4ToFin8 : Function.Injective embedFin4ToFin8 := by
  intro a b hab
  exact Fin.ext (Fin.mk.inj hab)

/-- Two-channel oracle specification for the programming test. -/
abbrev TestProgSpec : Unit ⊕ Fin 8 → Type :=
  (fun _ : Unit => Fin 4 × Bool) ⊕ₒ fun _ : Fin 8 => Bool

/-- Randomized client making 1 private coin draw, `q_S = 2` `.inl ()` programming calls, and
`q_H = 1` `.inr` random-oracle query. -/
def progTwoSignOneHash : ProbOracleComp TestProgSpec Bool :=
  ProbOracleComp.sample (ProbComp.unifFin 1) >>= fun coin =>
    ProbOracleComp.query (spec := TestProgSpec) (.inl ()) >>= fun s₀ =>
      ProbOracleComp.query (spec := TestProgSpec) (.inr ⟨coin.val, by omega⟩) >>= fun h =>
        ProbOracleComp.query (spec := TestProgSpec) (.inl ()) >>= fun s₁ =>
          pure (s₀.2 == h && s₁.2)

theorem progTwoSignOneHash_cost_inl :
    OracleComp.IsCostBounded
      (Sum.elim (fun _ => 0) (Sum.elim (fun _ : Unit => 1) (fun _ : Fin 8 => 0)))
      progTwoSignOneHash 2 := by
  have hinr (q : Fin 8) :
      OracleComp.IsCostBounded
        (Sum.elim (fun _ => 0) (Sum.elim (fun _ : Unit => 1) (fun _ : Fin 8 => 0)))
        (ProbOracleComp.query (spec := TestProgSpec) (.inr q)) 0 :=
    ProbOracleComp.isCostBounded_query (spec := TestProgSpec)
      (Sum.elim (fun _ : Unit => 1) (fun _ : Fin 8 => 0)) (.inr q)
  have hinl :
      OracleComp.IsCostBounded
        (Sum.elim (fun _ => 0) (Sum.elim (fun _ : Unit => 1) (fun _ : Fin 8 => 0)))
        (ProbOracleComp.query (spec := TestProgSpec) (.inl ())) 1 :=
    ProbOracleComp.isCostBounded_query (spec := TestProgSpec)
      (Sum.elim (fun _ : Unit => 1) (fun _ : Fin 8 => 0)) (.inl ())
  exact ((ProbOracleComp.isCostBounded_sample (spec := TestProgSpec)
      (Sum.elim (fun _ : Unit => 1) (fun _ : Fin 8 => 0)) (ProbComp.unifFin 1)).bind fun coin =>
    hinl.bind fun s₀ =>
      (hinr ⟨coin.val, by omega⟩).bind fun h =>
        hinl.bind fun s₁ =>
          OracleComp.IsCostBounded.pure (s₀.2 == h && s₁.2) 0).mono (by omega)

theorem progTwoSignOneHash_cost_inr :
    OracleComp.IsCostBounded
      (Sum.elim (fun _ => 0) (Sum.elim (fun _ : Unit => 0) (fun _ : Fin 8 => 1)))
      progTwoSignOneHash 1 := by
  have hinr (q : Fin 8) :
      OracleComp.IsCostBounded
        (Sum.elim (fun _ => 0) (Sum.elim (fun _ : Unit => 0) (fun _ : Fin 8 => 1)))
        (ProbOracleComp.query (spec := TestProgSpec) (.inr q)) 1 :=
    ProbOracleComp.isCostBounded_query (spec := TestProgSpec)
      (Sum.elim (fun _ : Unit => 0) (fun _ : Fin 8 => 1)) (.inr q)
  have hinl :
      OracleComp.IsCostBounded
        (Sum.elim (fun _ => 0) (Sum.elim (fun _ : Unit => 0) (fun _ : Fin 8 => 1)))
        (ProbOracleComp.query (spec := TestProgSpec) (.inl ())) 0 :=
    ProbOracleComp.isCostBounded_query (spec := TestProgSpec)
      (Sum.elim (fun _ : Unit => 0) (fun _ : Fin 8 => 1)) (.inl ())
  exact ((ProbOracleComp.isCostBounded_sample (spec := TestProgSpec)
      (Sum.elim (fun _ : Unit => 0) (fun _ : Fin 8 => 1)) (ProbComp.unifFin 1)).bind fun coin =>
    hinl.bind fun s₀ =>
      (hinr ⟨coin.val, by omega⟩).bind fun h =>
        hinl.bind fun s₁ =>
          OracleComp.IsCostBounded.pure (s₀.2 == h && s₁.2) 0).mono (by omega)

/-- For `q_S = 2`, `q_H = 1`, `δ = 1 / 4` from `([], ())`, the sharpened `choose 2` programming
`Game.advantage` bound gives nontrivial `3 / 4 < 1` (whereas rectangular `q_S * (q_S + q_H) * δ`
is `3 / 2`). -/
theorem advantage_progTwoSignOneHash_le_three_quarters :
    Game.advantage
      ((ProbOracleComp.runWith
        (RandomOracle.lazyProgramHandler (Reply := fun _ : Unit => Fin 4 × Bool)
          (PMF.uniformOfFintype Bool) (fun _ => true) (fun _ h _ => Bool.noConfusion h)
          (fun _ => PMF.uniformOfFintype (Fin 4)) (fun _ => embedFin4ToFin8)
          (fun _ r c _ => ((r, c), ()))) progTwoSignOneHash ([], ())).bind
        (fun out => PMF.pure out.1))
      ((ProbOracleComp.runWith
        (RandomOracle.overwriteProgramHandler (Reply := fun _ : Unit => Fin 4 × Bool)
          (PMF.uniformOfFintype Bool) (fun _ => true) (fun _ h _ => Bool.noConfusion h)
          (fun _ => PMF.uniformOfFintype (Fin 4)) (fun _ => embedFin4ToFin8)
          (fun _ r c _ => ((r, c), ()))) progTwoSignOneHash ([], ())).bind
        (fun out => PMF.pure out.1)) ≤ 3 / 4 := by
  have hminEnt : ∀ req : Unit, true = true → ∀ q : Fin 8,
      ((PMF.uniformOfFintype (Fin 4)).map embedFin4ToFin8) q ≤
        ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
    intro _ _
    exact RandomOracle.map_comp_apply_le_of_injective (g := id) injective_embedFin4ToFin8
      (fun b => by simp [PMF.uniformOfFintype_apply])
  have h := RandomOracle.advantage_runWith_lazyProgramHandler_overwriteProgramHandler_choose_two_le
    (Reply := fun _ : Unit => Fin 4 × Bool) (PMF.uniformOfFintype Bool) (fun _ => true)
    (fun _ h _ => Bool.noConfusion h) (fun _ => PMF.uniformOfFintype (Fin 4))
    (fun _ => embedFin4ToFin8) (fun _ r c _ => ((r, c), ())) hminEnt
    progTwoSignOneHash_cost_inl progTwoSignOneHash_cost_inr [] ()
    (fun out => PMF.pure out.1)
  exact h.trans_eq (by norm_num [Nat.choose])

/-! ### 5. Random-Oracle `q`-Query Birthday Bound and Sharpness at `q = 2` on `Bool` -/

/-- Deterministic 2-query client querying distinct keys `false` and `true` on `Digest = Bool`. -/
def twoDistinctBoolQueries : OracleComp (fun _ : Bool => Bool) (Bool × Bool) :=
  OracleComp.query false >>= fun d₀ =>
    OracleComp.query true >>= fun d₁ =>
      pure (d₀, d₁)

theorem twoDistinctBoolQueries_isQueryBounded :
    OracleComp.IsQueryBounded twoDistinctBoolQueries 2 :=
  ((OracleComp.IsCostBounded.query false).bind fun d₀ =>
    (OracleComp.IsCostBounded.query true).bind fun d₁ =>
      OracleComp.IsCostBounded.pure (d₀, d₁) 0).mono (by omega)

/-- Randomized 2-query `ProbOracleComp` client choosing query order from a private coin. -/
def randomizedTwoBoolQueries : ProbOracleComp (fun _ : Bool => Bool) (Bool × Bool) :=
  ProbOracleComp.sample (ProbComp.unifFin 1) >>= fun coin =>
    ProbOracleComp.query (coin == 1) >>= fun d₀ =>
      ProbOracleComp.query (!(coin == 1)) >>= fun d₁ =>
        pure (d₀, d₁)

theorem randomizedTwoBoolQueries_isQueryBounded :
    randomizedTwoBoolQueries.IsQueryBounded 2 :=
  ((ProbOracleComp.isCostBounded_sample (spec := fun _ : Bool => Bool) (fun _ => 1)
      (ProbComp.unifFin 1)).bind fun coin =>
    (ProbOracleComp.isCostBounded_query (spec := fun _ : Bool => Bool) (fun _ => 1)
      (coin == 1)).bind fun d₀ =>
      (ProbOracleComp.isCostBounded_query (spec := fun _ : Bool => Bool) (fun _ => 1)
        (!(coin == 1))).bind fun d₁ =>
        OracleComp.IsCostBounded.pure (d₀, d₁) 0).mono (by omega)

/-- Birthday bound (`OracleComp` and `ProbOracleComp.runWith`): 2 queries to a uniform `Bool`
random oracle produce an output collision (`HasOutputCollision`) with probability at most `1 / 2`.
-/
theorem birthday_bound_two_bool_queries_le :
    ((OracleComp.interpret (memoize (fun _ : Bool => PMF.uniformOfFintype Bool))
      twoDistinctBoolQueries).run []).toOuterMeasure {x | HasOutputCollision x.2} ≤
      (2 : ℝ≥0∞)⁻¹ ∧
    (ProbOracleComp.runWith (memoize (fun _ : Bool => PMF.uniformOfFintype Bool))
      randomizedTwoBoolQueries []).toOuterMeasure {x | HasOutputCollision x.2} ≤
      (2 : ℝ≥0∞)⁻¹ := by
  constructor
  · have h := RandomOracle.toOuterMeasure_hasOutputCollision_memoize_uniform_le
      twoDistinctBoolQueries_isQueryBounded
    simpa [Nat.choose, Fintype.card_bool] using h
  · have h := RandomOracle.toOuterMeasure_hasOutputCollision_runWith_memoize_uniform_le
      randomizedTwoBoolQueries_isQueryBounded
    simpa [Nat.choose, Fintype.card_bool] using h

/-- Concrete sharpness of the random-oracle birthday bound at `q = 2` on `Digest = Bool`: querying
`false` then `true` produces `HasOutputCollision` with exact probability `1 / 2`. -/
theorem birthday_bound_twoDistinctBoolQueries_sharp :
    ((OracleComp.interpret (memoize (fun _ : Bool => PMF.uniformOfFintype Bool))
      twoDistinctBoolQueries).run []).toOuterMeasure {x | HasOutputCollision x.2} =
      (2 : ℝ≥0∞)⁻¹ := by
  have hiff (d₀ d₁ : Bool) :
      HasOutputCollision [(true, d₁), (false, d₀)] ↔ d₁ = d₀ := by
    have hnd : (([(true, d₁), (false, d₀)] : List (Bool × Bool)).map Prod.fst).Nodup := by simp
    rw [RandomOracle.hasOutputCollision_iff_not_nodup_snd hnd]
    cases d₀ <;> cases d₁ <;> decide
  have hm₀ : memoize (fun _ : Bool => PMF.uniformOfFintype Bool) false [] =
      (PMF.uniformOfFintype Bool).bind (fun d₀ => PMF.pure (d₀, [(false, d₀)])) :=
    memoize_of_none _ false [] rfl
  have hm₁ (d₀ : Bool) :
      memoize (fun _ : Bool => PMF.uniformOfFintype Bool) true [(false, d₀)] =
        (PMF.uniformOfFintype Bool).bind
          (fun d₁ => PMF.pure (d₁, [(true, d₁), (false, d₀)])) :=
    memoize_of_none _ true [(false, d₀)] rfl
  simp only [twoDistinctBoolQueries, run_interpret_bind, run_interpret_query, run_interpret_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  change ((memoize (fun _ : Bool => PMF.uniformOfFintype Bool) false []).bind fun x₀ =>
    (memoize (fun _ : Bool => PMF.uniformOfFintype Bool) true x₀.2).bind fun x₁ =>
      PMF.pure ((x₀.1, x₁.1), x₁.2)).toOuterMeasure {x | HasOutputCollision x.2} = _
  rw [hm₀]
  simp only [PMF.bind_bind, PMF.pure_bind, hm₁, PMF.toOuterMeasure_bind_apply,
    PMF.toOuterMeasure_pure_apply, tsum_fintype, Fintype.sum_bool,
    PMF.uniformOfFintype_apply, Fintype.card_bool]
  simpa [hiff] using two_inv_mul_two_inv_add_eq

end CslibFrontierTests.Crypto.UntilBadROMFramework

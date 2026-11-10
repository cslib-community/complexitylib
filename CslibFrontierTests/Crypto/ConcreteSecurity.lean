/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

import CslibFrontier.Crypto.Game.Concrete
import CslibFrontier.Crypto.Game.CloseTo.UntilBad
import CslibFrontier.Computability.Interactive.Security.Oracle
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.Uniform
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import Mathlib.Data.Fintype.Pi

/-!
# Checked tests for explicit-time realizations and concrete `(t, q, ε)` game security

Exercises `ComputesInTimeOn`, `ComputesOracleInTimeOn`, `ComputesOracleInTimeAndQueriesOn`,
`Game.IndistinguishableWithin`, `Game.IndistinguishableWithin.of_reduction`, and
`Game.Indistinguishable.of_timeAndQueryBounded` on concrete randomized programs, stateful oracle
runs, and a non-vacuous `(t, q, q / 2 ^ n)` game pair with a tight `1`-query distinguisher.
-/

namespace Cslib.Tests.ConcreteSecurity

open Cslib Cslib.Probability Cslib.Crypto Cslib.Interactive Turing.MultiTapeTM
open scoped ENNReal NNReal

/-! ### 1. Closed halting `ComputesInTimeOn`, monotonicity, and `IsPPTOn` round-trip -/

/-- Sample two fair bits sequentially via `ProbComp` bind and return the second. -/
noncomputable def twoStageCoin (_ : List Bool) : ProbComp Bool := do
  let _ ← ProbComp.uniform Bool
  ProbComp.uniform Bool

/-- `twoStageCoin` is genuinely randomized: it outputs `true` with exact probability `1 / 2`. -/
theorem eval_twoStageCoin_true (w : List Bool) :
    ProbComp.eval (twoStageCoin w) true = (2 : ℝ≥0∞)⁻¹ := by
  simp only [twoStageCoin, ProbComp.eval_bind, ProbComp.eval_uniform,
    PMF.bind_apply, tsum_bool, PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat]
  rw [← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]

/-- Explicit halting realization of `twoStageCoin` in `7` steps (`2 * 1 + 1 + 4`) via
`ComputesInTimeOn.bind` on two `1`-step `uniform_bool` realizations. -/
theorem computesInTimeOn_twoStageCoin :
    ComputesInTimeOn encBits encBool (fun _ => 7) twoStageCoin :=
  ((ComputesInTimeOn.uniform_bool encBits).bind
    (ComputesInTimeOn.uniform_bool encBool) fun _ _ _ => le_rfl).mono fun _ => le_rfl

/-- Unconditional monotonicity to an input-dependent schedule and round-trip equivalence with
`IsPPTOn` on `twoStageCoin`. -/
theorem isPPTOn_twoStageCoin_roundTrip :
    IsPPTOn encBits encBool twoStageCoin ∧
      ∃ t, PolyBounded (fun w : List Bool => w.length) t ∧
        ComputesInTimeOn encBits encBool (fun w => t w + w.length + 7) twoStageCoin := by
  have hppt : IsPPTOn encBits encBool twoStageCoin :=
    isPPTOn_iff_exists_polyBounded_computesInTimeOn.mpr
      ⟨fun _ => 7, PolyBounded.const 7, computesInTimeOn_twoStageCoin⟩
  obtain ⟨t, ht, hrt⟩ := isPPTOn_iff_exists_polyBounded_computesInTimeOn.mp hppt
  exact ⟨hppt, t, ht, hrt.mono fun w => by omega⟩

/-! ### 2. Open halting `ComputesOracleInTimeOn` & `ComputesOracleInTimeAndQueriesOn` -/

/-- Submit `q` on channel `()` and read at most `limit` reply bits, given
`encPair encBits encUnary`. -/
def probePrefix (req : List Bool × ℕ) : WordOracleComp Unit (List Bool) :=
  List.take req.2 <$> ProbOracleComp.query ((), req.1)

/-- `probePrefix` runs in `4 * |q| + 2 * limit + 6` halting steps while making at most `1` query
(`1 < 4 * |q| + 2 * limit + 6` for every input). -/
theorem computesOracleInTimeAndQueriesOn_probePrefix :
    ComputesOracleInTimeAndQueriesOn (encPair encBits encUnary) encBits
      (fun req => 4 * req.1.length + 2 * req.2 + 6) (fun _ => 1) probePrefix := by
  refine ⟨ComputesOracleInTimeOn.query_take_pair (), fun req => ?_⟩
  exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (ProbOracleComp.IsQueryBounded.query _)

/-- Stateful execution check: against an oracle that echoes `req.reverse` and increments a call
counter, `probePrefix ([true, false, true], 2)` returns `[true, false]` with final counter `1`. -/
theorem runWith_probePrefix_stateful :
    ProbOracleComp.runWith
      (fun (_op, payload) (count : ℕ) => PMF.pure (payload.reverse, count + 1))
      (probePrefix ([true, false, true], 2)) 0 =
      PMF.pure ([true, false], 1) := by
  simp [probePrefix, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query]

/-- Round-trip `probePrefix` through
`isOraclePPTOn_iff_exists_polyBounded_computesOracleInTimeOn`. -/
theorem isOraclePPTOn_probePrefix_roundTrip :
    IsOraclePPTOn (encPair encBits encUnary) encBits probePrefix := by
  refine isOraclePPTOn_iff_exists_polyBounded_computesOracleInTimeOn.mpr
    ⟨fun req => 4 * req.1.length + 2 * req.2 + 6, ?_,
      computesOracleInTimeAndQueriesOn_probePrefix.1⟩
  refine PolyBounded.of_forall_le 6 1 fun req => ?_
  simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate, pow_one]
  omega

/-! ### 3. Concrete `(t, q, ε)` game security, reduction composition, and asymptotic bridge -/

/-- Oracle handler that outputs `[true]` with probability `2 ^ (-n)` (when `n` fresh fair bits are
all `true`) and `[false]` otherwise. -/
noncomputable def rareOracle (n : ℕ) : Unit × List Bool → StateT Unit PMF (List Bool) :=
  fun _ s => (PMF.uniformOfFintype (Fin n → Bool)).map fun coins =>
    ([decide (coins = fun _ => true)], s)

/-- Reference oracle handler that always outputs `[false]`. -/
noncomputable def nullOracle : Unit × List Bool → StateT Unit PMF (List Bool) :=
  fun _ s => PMF.pure ([false], s)

/-- Concrete experiment running `adversary n []` against `rareOracle n`. -/
noncomputable def rareGame (adversary : ℕ → List Bool → WordOracleComp Unit Bool) (n : ℕ) : Game :=
  (ProbOracleComp.runWith (rareOracle n) (adversary n []) ()).map Prod.fst

/-- Reference experiment running `adversary n []` against `nullOracle`. -/
noncomputable def nullGame (adversary : ℕ → List Bool → WordOracleComp Unit Bool) (n : ℕ) : Game :=
  (ProbOracleComp.runWith nullOracle (adversary n []) ()).map Prod.fst

private theorem closeTo_rareOracle_nullOracle (n : ℕ) (req : Unit × List Bool) (s : Unit) :
    CloseTo (rareOracle n req s) (nullOracle req s) (((2 : ℝ≥0) ^ n)⁻¹ : ℝ≥0∞) := by
  have h1 : rareOracle n req s = (PMF.uniformOfFintype (Fin n → Bool)).bind
      (fun coins => PMF.pure ([decide (coins = fun _ => true)], s)) := rfl
  have h2 : nullOracle req s = (PMF.uniformOfFintype (Fin n → Bool)).bind
      (fun _ => PMF.pure ([false], s)) := by
    simp [nullOracle]
  rw [h1, h2]
  refine (CloseTo.bind_of_eq_on (PMF.uniformOfFintype (Fin n → Bool)) _ _
      {fun _ => true} ?_).mono ?_
  · intro coins _ hne
    have hfalse : decide (coins = fun _ => true) = false := decide_eq_false hne
    rw [hfalse]
  · rw [PMF.toOuterMeasure_apply_singleton]
    simp [PMF.uniformOfFintype_apply]

/-- Concrete `(t, q, q / 2 ^ n)` security of `rareGame` vs `nullGame`. -/
theorem indistinguishableWithin_rareGame_nullGame :
    Game.IndistinguishableWithin rareGame nullGame (Game.WithinTimeAndQueries encBool)
      (fun n r => r.2 * ((2 : ℝ≥0) ^ n)⁻¹) := by
  intro n r adversary ⟨_, hq⟩
  have hstep : ∀ q (s : Unit),
      CloseTo (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
          (rareOracle n) q s)
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
          nullOracle q s)
        (((Sum.elim (fun _ => 0) (fun _ => 1) q : ℕ) : ℝ≥0∞) * (((2 : ℝ≥0) ^ n)⁻¹ : ℝ≥0∞)) := by
    rintro (m | req) s
    · simp only [OracleComp.sumHandler, Sum.elim_inl, Nat.cast_zero, zero_mul]
      exact CloseTo.refl _
    · simpa only [OracleComp.sumHandler, Sum.elim_inr, Nat.cast_one, one_mul] using
        closeTo_rareOracle_nullOracle n req s
  have hrun := hq.closeTo_runWith hstep ()
  have hcast : (r.2 : ℝ≥0∞) * (((2 : ℝ≥0) ^ n)⁻¹ : ℝ≥0∞) =
      ((r.2 * ((2 : ℝ≥0) ^ n)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    push_cast; rfl
  rw [hcast] at hrun
  exact Game.advantage_map_le_of_closeTo hrun Prod.fst

/-- Non-vacuity and sharpness: a concrete `1`-query distinguisher achieves exact advantage
`((2 : ℝ≥0) ^ n)⁻¹` between `rareGame` and `nullGame` at every parameter `n` (e.g. `1 / 4` at
`n = 2`). -/
def oneQueryDistinguisher : ℕ → List Bool → WordOracleComp Unit Bool :=
  fun _ _ => do
    let reply ← List.take 1 <$> ProbOracleComp.query ((), [])
    pure (reply.headD false)

theorem advantage_oneQueryDistinguisher (n : ℕ) :
    Game.advantage (rareGame oneQueryDistinguisher n) (nullGame oneQueryDistinguisher n) =
      ((2 : ℝ≥0) ^ n)⁻¹ := by
  have hnull : nullGame oneQueryDistinguisher n = PMF.pure false := by
    simp [nullGame, nullOracle, oneQueryDistinguisher, ProbOracleComp.runWith_map,
      ProbOracleComp.runWith_query]
  have hrare_true : rareGame oneQueryDistinguisher n true = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
    have hrare : rareGame oneQueryDistinguisher n =
        (PMF.uniformOfFintype (Fin n → Bool)).map
          (fun coins => decide (coins = fun _ => true)) := by
      simp [rareGame, rareOracle, oneQueryDistinguisher, ProbOracleComp.runWith_map,
        ProbOracleComp.runWith_query, PMF.map_comp, Function.comp_def]
    rw [hrare, PMF.map_apply]
    simp [PMF.uniformOfFintype_apply]
  rw [hnull, Game.advantage_pure_false, Game.succProbability, hrare_true]
  simp [ENNReal.toNNReal_inv, ENNReal.toNNReal_pow, ENNReal.toNNReal_ofNat]

/-- Target game pair whose output bit is complemented relative to `rareGame` / `nullGame`, used to
check concrete `(t, q) ↦ (t', q')` reduction composition. -/
noncomputable def compRareGame (adversary : ℕ → List Bool → WordOracleComp Unit Bool) (n : ℕ) :
    Game :=
  (rareGame adversary n).map Bool.not

noncomputable def compNullGame (adversary : ℕ → List Bool → WordOracleComp Unit Bool) (n : ℕ) :
    Game :=
  (nullGame adversary n).map Bool.not

/-- Concrete reduction negating the target adversary's Boolean output. -/
def negateAdversary (adversary : ℕ → List Bool → WordOracleComp Unit Bool) :
    ℕ → List Bool → WordOracleComp Unit Bool :=
  fun n aux => Bool.not <$> adversary n aux

/-- Using `ComputesOracleInTimeOn.map` and `Game.IndistinguishableWithin.of_reduction`, a concrete
`(t, q)` adversary for `(compRareGame, compNullGame)` reduces to a `(2 * t + cNot + 4, q)` adversary
for `(rareGame, nullGame)` with multiplicative loss `1` and additive error `0`. -/
theorem indistinguishableWithin_compRareGame_compNullGame :
    Game.IndistinguishableWithin compRareGame compNullGame (Game.WithinTimeAndQueries encBool)
      (fun n r => r.2 * ((2 : ℝ≥0) ^ n)⁻¹) := by
  obtain ⟨cNot, hNot⟩ :=
    computableInTimeAndSpace_of_finite (encIn := encBool) (encOut := encBool) Bool.not
  have hred := indistinguishableWithin_rareGame_nullGame.of_reduction
    (target1 := compRareGame) (target2 := compNullGame)
    (TargetWithin := Game.WithinTimeAndQueries encBool)
    negateAdversary (fun _ r => (2 * r.1 + cNot + 4, r.2)) (fun _ _ => 1) (fun _ _ => 0)
    (fun n r adversary ⟨ht, hq⟩ => by
      obtain ⟨T, hle, hT⟩ := Game.withinOracleTime_iff.mp ht
      have hmap : ComputesOracleInTime encBool (fun n' m' => 2 * T n' m' + cNot + 4)
          (negateAdversary adversary) :=
        hT.on.map hNot fun _ _ _ _ _ _ _ => le_rfl
      refine ⟨Game.withinOracleTime_iff.mpr ⟨_, by omega, hmap⟩, ?_⟩
      exact (OracleComp.isCostBounded_map_iff _ _ _).mpr hq)
    (fun n r adversary _ => by
      have heq1 : rareGame (negateAdversary adversary) n = compRareGame adversary n := by
        simp [rareGame, compRareGame, negateAdversary, ProbOracleComp.runWith_map, PMF.map_comp,
          Function.comp_def]
      have heq2 : nullGame (negateAdversary adversary) n = compNullGame adversary n := by
        simp [nullGame, compNullGame, negateAdversary, ProbOracleComp.runWith_map, PMF.map_comp,
          Function.comp_def]
      rw [heq1, heq2]
      simp)
  exact hred.mono fun n r => by simp

/-- Derive asymptotic `IsOraclePPT` indistinguishability of `(compRareGame, compNullGame)` directly
from its concrete `(t, q, ε)` bound via `Game.Indistinguishable.of_timeAndQueryBounded`. -/
theorem indistinguishable_compRareGame_compNullGame :
    Game.Indistinguishable compRareGame compNullGame (IsOraclePPT encBool) := by
  refine Game.Indistinguishable.of_timeAndQueryBounded
    (fun n r => r.2 * ((2 : ℝ≥0) ^ n)⁻¹)
    indistinguishableWithin_compRareGame_compNullGame
    fun _ Q _ hQ => ?_
  have hgeom : Negligible fun n => ((2 : ℝ≥0) ^ n)⁻¹ := by
    simpa only [inv_pow] using negligible_geometric (ratio := (2 : ℝ≥0)⁻¹) (by norm_num)
  exact hgeom.polynomiallyBounded_mul hQ

end Cslib.Tests.ConcreteSecurity

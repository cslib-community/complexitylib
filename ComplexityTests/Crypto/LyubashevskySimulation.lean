/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature.Simulation
public import ComplexityTests.Crypto.LyubashevskyRandomOracle
import Complexity.Probability.PMF.Bind

@[expose] public section

open Cslib Cslib.Probability Cslib.Probability.PMF Cslib.OracleComp Cslib.Interactive
open Cslib.Crypto.Protocols Cslib.Crypto.Protocols.SigmaProtocol ROMSignature
open LyubashevskyViewTests LyubashevskyRandomOracleTests
open scoped ENNReal _root_.Matrix

namespace LyubashevskySimulationTests

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

noncomputable def H_fixed : Matrix (Fin 1) (Fin 2) (ZMod 17) →
    PMF (Matrix (Fin 1) (Fin 2) (ZMod 17) × Matrix (Fin 1) (Fin 1) (ZMod 17)) :=
  fun _ => PMF.pure key

theorem zero_relation (A : Matrix (Fin 1) (Fin 2) (ZMod 17))
    (h : Matrix (Fin 1) (Fin 2) (ZMod 17) × Matrix (Fin 1) (Fin 1) (ZMod 17))
    (_hh : h ∈ (H_fixed A).support) :
    lyubashevskyRelation 1 0 (A, key.2) := by
  simp only [H_fixed, PMF.mem_support_pure_iff] at _hh
  subst _hh
  constructor
  · ext i j
    simp [key]
  · intro i j
    norm_num

/-- Test 1: Zero later reads continuation makes at most 0 queries. -/
theorem zero_reads_bounded (_A : Matrix (Fin 1) (Fin 2) (ZMod 17))
    (_h : Matrix (Fin 1) (Fin 2) (ZMod 17) × Matrix (Fin 1) (Fin 1) (ZMod 17))
    (_sig : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ))) :
    IsQueryBounded (pure () : OracleComp (fun _ : Query => Digest) Unit) 0 :=
  IsCostBounded.pure () 0

/-- Test 1: Application of `closeTo_lyubashevskySign_simulate` with zero later reads. -/
theorem zero_reads_closeTo :
    CloseTo
      (lyubashevskySignVisibleProg 1 2 1 17 3 1 H_fixed (fun _ => 0) (fun _ _ => key.2)
        (fun _ => ()) (fun _ => []) (fun _ _ _ => pure ()))
      (lyubashevskySignVisibleSim 1 2 1 17 3 1 H_fixed (fun _ _ => key.2)
        (fun _ => ()) (fun _ => []) (fun _ _ _ => pure ()))
      ((Nat.cast 0 : ℝ≥0∞) / (Nat.cast 17 : ℝ≥0∞) ^ 1 +
        ENNReal.ofReal (Real.sqrt ((Nat.cast 17 : ℝ) ^ 1 / ((2 * 3 + 1 : ℕ) : ℝ) ^ 2) / 2)) :=
  closeTo_lyubashevskySign_simulate 1 2 1 17 1 3 1 0 (by decide) (by decide) (by decide)
    H_fixed (fun _ => 0) (fun _ _ => key.2) zero_relation (fun _ => ()) (fun _ => [])
    (fun _ _ _ => pure ()) (fun _ _ _ _ => IsCostBounded.pure () 0)

/-- Test 1: When the continuation makes zero oracle queries, the visible programmed
and simulated experiments are identically distributed. -/
theorem zero_reads_visible_eq :
    lyubashevskySignVisibleProg 1 2 1 17 3 1 H_fixed (fun _ => 0) (fun _ _ => key.2)
      (fun _ => ()) (fun _ => []) (fun _ _ sig => pure sig) =
    lyubashevskySignVisibleSim 1 2 1 17 3 1 H_fixed (fun _ _ => key.2)
      (fun _ => ()) (fun _ => []) (fun _ _ sig => pure sig) :=
  lyubashevskySignVisibleProg_eq_sim_of_pure 1 2 1 17 1 3 1 (by decide) (by decide)
    H_fixed (fun _ => 0) (fun _ _ => key.2) zero_relation (fun _ => ()) (fun _ => [])
    (fun _ _ sig => sig)

abbrev BoolQuery := Bool × (Fin 1 → ZMod 17)

/-- Test 2 (avoid): Continuation querying `(true, 0)` with message type `Bool`. -/
def avoidCont (_ : Matrix (Fin 1) (Fin 2) (ZMod 17))
    (_ : Matrix (Fin 1) (Fin 2) (ZMod 17) × Matrix (Fin 1) (Fin 1) (ZMod 17))
    (_ : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ))) :
    OracleComp (fun _ : BoolQuery => Digest) Digest :=
  OracleComp.query (true, 0)

theorem avoid_bounded (A : Matrix (Fin 1) (Fin 2) (ZMod 17))
    (h : Matrix (Fin 1) (Fin 2) (ZMod 17) × Matrix (Fin 1) (Fin 1) (ZMod 17))
    (sig : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ))) :
    IsQueryBounded (avoidCont A h sig) 1 :=
  IsCostBounded.query (spec := fun _ : BoolQuery => Digest) (cost := fun _ => 1) (true, 0)

/-- The avoid query `(true, 0)` is provably disjoint from the programmed signing key
`(false, coin.1)` for all coin commits because `true ≠ false`. -/
theorem avoid_key_disjoint (coin : (Fin 1 → ZMod 17) × (Fin 2 → ℤ)) :
    (true, (0 : Fin 1 → ZMod 17)) ≠ (false, coin.1) := by
  intro h
  injection h with hmsg _
  contradiction

theorem avoid_closeTo :
    CloseTo
      (lyubashevskySignVisibleProg 1 2 1 17 3 1 H_fixed (fun _ => 0) (fun _ _ => key.2)
        (fun _ => false) (fun _ => []) avoidCont)
      (lyubashevskySignVisibleSim 1 2 1 17 3 1 H_fixed (fun _ _ => key.2)
        (fun _ => false) (fun _ => []) avoidCont)
      ((Nat.cast 1 : ℝ≥0∞) / (Nat.cast 17 : ℝ≥0∞) ^ 1 +
        ENNReal.ofReal (Real.sqrt ((Nat.cast 17 : ℝ) ^ 1 / ((2 * 3 + 1 : ℕ) : ℝ) ^ 2) / 2)) :=
  closeTo_lyubashevskySign_simulate 1 2 1 17 1 3 1 1 (by decide) (by decide) (by decide)
    H_fixed (fun _ => 0) (fun _ _ => key.2) zero_relation (fun _ => false) (fun _ => [])
    avoidCont (fun A h sig _ => avoid_bounded A h sig)

/-- Test 2 (hit): Continuation querying commitment point on acceptance makes at most 1 query. -/
def hitCont (_ : Matrix (Fin 1) (Fin 2) (ZMod 17))
    (_ : Matrix (Fin 1) (Fin 2) (ZMod 17) × Matrix (Fin 1) (Fin 1) (ZMod 17))
    (sig : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ))) :
    OracleComp (fun _ : Query => Digest) (Option Digest) :=
  match sig with
  | some (t, _) => (OracleComp.query ((), t)).map some
  | none => pure none

theorem hit_bounded (A : Matrix (Fin 1) (Fin 2) (ZMod 17))
    (h : Matrix (Fin 1) (Fin 2) (ZMod 17) × Matrix (Fin 1) (Fin 1) (ZMod 17))
    (sig : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ))) :
    IsQueryBounded (hitCont A h sig) 1 := by
  dsimp only [hitCont]
  cases sig with
  | none => exact IsCostBounded.pure none 1
  | some tz =>
    exact IsCostBounded.liftBind (spec := fun _ : Query => Digest) (cost := fun _ => 1)
      ((), tz.1) (fun a => pure (some a)) 0 (fun _ => .pure _ 0)

/-- A query hitting an existing cache entry returns the cached digest deterministically. -/
theorem hit_returns_c {Q D : Type} [DecidableEq Q] [Fintype D] [Nonempty D]
    (q : Q) (c : D) (cache : List (Q × D)) :
    (interpret (oracle D) (OracleComp.query q)).run ((q, c) :: cache) =
      PMF.pure (c, (q, c) :: cache) := by
  simp only [OracleComp.interpret_query, oracle, memoize, List.lookup_cons_self,
    StateT.run, PMF.monad_pure_eq_pure]

/-- A query missing an existing cache entry samples a fresh uniform digest and updates cache. -/
theorem avoid_miss_cache {Q D : Type} [DecidableEq Q] [Fintype D] [Nonempty D]
    (q q' : Q) (c : D) (cache : List (Q × D)) (hne : q' ≠ q)
    (hlookup : cache.lookup q' = none) :
    (interpret (oracle D) (OracleComp.query q')).run ((q, c) :: cache) =
      (PMF.uniformOfFintype D).map (fun d => (d, (q', d) :: (q, c) :: cache)) := by
  have hlook : (((q, c) :: cache).lookup q') = none := by
    simp [List.lookup_cons, beq_false_of_ne hne, hlookup]
  simp only [OracleComp.interpret_query, oracle, memoize, hlook, StateT.run,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map]
  rfl

/-- Test 3: Actual final-verifier consumer client checking signature validity. -/
noncomputable def verifierCont (A : Matrix (Fin 1) (Fin 2) (ZMod 17))
    (_ : Matrix (Fin 1) (Fin 2) (ZMod 17) × Matrix (Fin 1) (Fin 1) (ZMod 17))
    (sig : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ))) :
    OracleComp (fun _ : Query => Digest) Bool :=
  match sig with
  | none => pure false
  | some (t, z) => do
      let c ← OracleComp.query ((), t)
      pure (protocol.verify (A, key.2) t c (some z))

theorem verifier_bounded (A : Matrix (Fin 1) (Fin 2) (ZMod 17))
    (h : Matrix (Fin 1) (Fin 2) (ZMod 17) × Matrix (Fin 1) (Fin 1) (ZMod 17))
    (sig : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ))) :
    IsQueryBounded (verifierCont A h sig) 1 := by
  dsimp only [verifierCont]
  cases sig with
  | none => exact IsCostBounded.pure false 1
  | some tz =>
    exact IsCostBounded.liftBind (spec := fun _ : Query => Digest) (cost := fun _ => 1)
      ((), tz.1) (fun c => pure (protocol.verify (A, key.2) tz.1 c (some tz.2))) 0
      (fun _ => .pure _ 0)

/-- Test 3: The final-verifier continuation satisfies simulation closeness with `R = 1`. -/
theorem verifier_closeTo :
    CloseTo
      (lyubashevskySignVisibleProg 1 2 1 17 3 1 H_fixed (fun _ => 0) (fun _ _ => key.2)
        (fun _ => ()) (fun _ => []) verifierCont)
      (lyubashevskySignVisibleSim 1 2 1 17 3 1 H_fixed (fun _ _ => key.2)
        (fun _ => ()) (fun _ => []) verifierCont)
      ((Nat.cast 1 : ℝ≥0∞) / (Nat.cast 17 : ℝ≥0∞) ^ 1 +
        ENNReal.ofReal (Real.sqrt ((Nat.cast 17 : ℝ) ^ 1 / ((2 * 3 + 1 : ℕ) : ℝ) ^ 2) / 2)) :=
  closeTo_lyubashevskySign_simulate 1 2 1 17 1 3 1 1 (by decide) (by decide) (by decide)
    H_fixed (fun _ => 0) (fun _ _ => key.2) zero_relation (fun _ => ()) (fun _ => [])
    verifierCont (fun A h sig _ => verifier_bounded A h sig)

/-- Test 4: The mandatory counterexample for `q=17, n=1, m=2, γ=3, β=1, S=0`.
The honest prover abort mass is `1 - (5/7)^2 = 24/49`. -/
theorem counterexample_abort_mass (A : Matrix (Fin 1) (Fin 2) (ZMod 17)) (c : Digest) :
    (lyubashevsky 1 2 1 17 3 1).acceptedTranscript
        (0 : Matrix (Fin 2) (Fin 1) ℤ) (A, key.2) c none =
      1 - (5 / 7 : ℝ≥0∞) ^ 2 := by
  have habort := lyubashevsky_acceptedTranscript_none (n := 1) (m := 2) (k := 1) (q := 17)
    (γ := 3) (β := 1) (η := 1) (by decide) (by decide)
    (S := (0 : Matrix (Fin 2) (Fin 1) ℤ)) (by intro i j; simp) (A, key.2) c
  rw [habort]
  norm_num

/-- Test 4: In Prog, the final cache always has length 1 (never empty), even on abort. -/
theorem prog_cache_length_ne_zero (coin : (Fin 1 → ZMod 17) × (Fin 2 → ℤ)) (c : Digest) :
    (((((), coin.1), c) :: ([] : Cache))).length ≠ 0 := by
  simp

/-- Test 4: In Sim, on abort the final cache is empty (length 0). -/
theorem trans_cache_length_zero_on_abort (c : Digest) :
    (match (none : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ))) with
     | some (t, _) => [(((), t), c)]
     | none => ([] : Cache)).length = 0 := rfl

noncomputable def progExp :=
  lyubashevskySignFullProg 1 2 1 17 3 1 H_fixed (fun _ => 0) (fun _ _ => key.2)
    (fun _ => ()) (fun _ => [])

noncomputable def simExp :=
  lyubashevskySignFullSim 1 2 1 17 3 1 H_fixed (fun _ _ => key.2)
    (fun _ => ()) (fun _ => [])

/-- Exact full-run law: The probability that the programmed hybrid leaves an empty cache is 0. -/
theorem progExp_empty_cache_eq_zero :
    (progExp.map fun r => decide (r.2.2.2 = [])) true = 0 := by
  dsimp only [progExp, lyubashevskySignFullProg]
  simp only [H_fixed, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map, PMF.pure_bind]
  have hfalse (t : Fin 1 → ZMod 17) :
      (fun (c : BitString 1) => PMF.pure (decide ([(((), t), c)] = []))) =
        fun _ => PMF.pure false := by
    funext c; rfl
  simp only [hfalse, PMF.bind_const, PMF.pure_apply]
  split_ifs with _ h <;> first | contradiction | rfl

theorem simulate_abort_prob (A : Matrix (Fin 1) (Fin 2) (ZMod 17)) (c : BitString 1) :
    ((lyubashevskySimulate 1 2 1 17 3 1 (A, key.2) c).bind fun view =>
      PMF.pure (decide (lyubashevskySimCache () c [] view = []))) true =
    1 - (5 / 7 : ℝ≥0∞) ^ 2 := by
  have hdecide (view : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ))) :
      decide (lyubashevskySimCache () c [] view = []) = decide (view = none) := by
    rw [decide_eq_decide, lyubashevskySimCache_eq_nil_iff]
    simp
  simp only [hdecide]
  change ((lyubashevskySimulate 1 2 1 17 3 1 (A, key.2) c).map
    (fun a_2 => decide (a_2 = none))) true = _
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  have hset : (fun a_2 : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ)) =>
      decide (a_2 = none)) ⁻¹' {true} =
    {(none : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ)))} := by
    ext a_2; cases a_2 <;> simp
  rw [hset, PMF.toOuterMeasure_apply_singleton]
  have hhvzk := (lyubashevsky_nonAbortSpecialHVZK (n := 1) (m := 2) (k := 1) (q := 17)
    (γ := 3) (β := 1) (by decide) (by decide)).acceptedTranscript_eq
    (0 : Matrix (Fin 2) (Fin 1) ℤ) (A, key.2) (zero_relation A key (by simp [H_fixed])) c
  rw [hhvzk]
  exact counterexample_abort_mass A c

/-- Exact full-run law: The probability that the simulated experiment leaves an empty cache
is exactly the abort mass `1 - (5/7)^2 = 24/49`. -/
theorem simExp_empty_cache_eq_abort_mass :
    (simExp.map fun r => decide (r.2.2.2 = [])) true = 1 - (5 / 7 : ℝ≥0∞) ^ 2 := by
  dsimp only [simExp, lyubashevskySignFullSim]
  simp only [H_fixed, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map, PMF.pure_bind]
  refine bind_apply_of_forall _ fun A => ?_
  refine bind_apply_of_forall _ fun c => ?_
  exact simulate_abort_prob A c

/-- Projection link: The visible programmed experiment is the marginal projection of the
full execution. -/
theorem progExp_proj_visible :
    progExp.map (fun (A, h, sig, _) => (A, h, sig)) =
    lyubashevskySignVisibleProg 1 2 1 17 3 1 H_fixed (fun _ => 0) (fun _ _ => key.2)
      (fun _ => ()) (fun _ => []) (fun _ _ sig => pure sig) :=
  (lyubashevskySignVisibleProg_eq_map_full 1 2 1 17 3 1 H_fixed (fun _ => 0) (fun _ _ => key.2)
    (fun _ => ()) (fun _ => [])).symm

/-- Projection link: The visible simulated experiment is the marginal projection of the
full execution. -/
theorem simExp_proj_visible :
    simExp.map (fun (A, h, view, _) => (A, h, view)) =
    lyubashevskySignVisibleSim 1 2 1 17 3 1 H_fixed (fun _ _ => key.2)
      (fun _ => ()) (fun _ => []) (fun _ _ view => pure view) :=
  (lyubashevskySignVisibleSim_eq_map_full 1 2 1 17 3 1 H_fixed (fun _ _ => key.2)
    (fun _ => ()) (fun _ => [])).symm

/-- Counterexample separation: The visible marginal projections agree identically,
even though the full executions differ in empty-cache probability (0 vs 24/49). -/
theorem full_projections_agree :
    progExp.map (fun (A, h, sig, _) => (A, h, sig)) =
    simExp.map (fun (A, h, view, _) => (A, h, view)) := by
  rw [progExp_proj_visible, simExp_proj_visible]
  exact zero_reads_visible_eq

end LyubashevskySimulationTests

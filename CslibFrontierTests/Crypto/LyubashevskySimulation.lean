/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature.Simulation
public import CslibFrontierTests.Crypto.LyubashevskyRandomOracle
import CslibFrontier.Probability.PMF.Bind

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
  | some (t, _) => some <$> OracleComp.query ((), t)
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

/-- Test 2 (hit): Application of `closeTo_lyubashevskySign_simulate` to `hitCont`. -/
theorem hit_closeTo :
    CloseTo
      (lyubashevskySignVisibleProg 1 2 1 17 3 1 H_fixed (fun _ => 0) (fun _ _ => key.2)
        (fun _ => ()) (fun _ => []) hitCont)
      (lyubashevskySignVisibleSim 1 2 1 17 3 1 H_fixed (fun _ _ => key.2)
        (fun _ => ()) (fun _ => []) hitCont)
      ((Nat.cast 1 : ℝ≥0∞) / (Nat.cast 17 : ℝ≥0∞) ^ 1 +
        ENNReal.ofReal (Real.sqrt ((Nat.cast 17 : ℝ) ^ 1 / ((2 * 3 + 1 : ℕ) : ℝ) ^ 2) / 2)) :=
  closeTo_lyubashevskySign_simulate 1 2 1 17 1 3 1 1 (by decide) (by decide) (by decide)
    H_fixed (fun _ => 0) (fun _ _ => key.2) zero_relation (fun _ => ()) (fun _ => [])
    hitCont (fun A h sig _ => hit_bounded A h sig)

/-- A query hitting an existing cache entry returns the cached digest deterministically. -/
theorem hit_returns_c {Q D : Type} [DecidableEq Q] [Fintype D] [Nonempty D]
    (q : Q) (c : D) (cache : List (Q × D)) :
    (interpret (oracle D) (OracleComp.query q)).run ((q, c) :: cache) =
      PMF.pure (c, (q, c) :: cache) := by
  simp only [OracleComp.interpret_query, oracle, memoize, List.lookup_cons_self,
    StateT.run, PMF.monad_pure_eq_pure]

/-- Test 2 (hit): Because `hitCont` queries only accepted commitments, both visible experiments
return `some c` on acceptance via `hit_returns_c` and `none` on abort, agreeing identically. -/
theorem hit_visible_eq :
    lyubashevskySignVisibleProg 1 2 1 17 3 1 H_fixed (fun _ => 0) (fun _ _ => key.2)
      (fun _ => ()) (fun _ => []) hitCont =
    lyubashevskySignVisibleSim 1 2 1 17 3 1 H_fixed (fun _ _ => key.2)
      (fun _ => ()) (fun _ => []) hitCont := by
  have hprog_run (A : Matrix (Fin 1) (Fin 2) (ZMod 17))
      (h : Matrix (Fin 1) (Fin 2) (ZMod 17) × Matrix (Fin 1) (Fin 1) (ZMod 17))
      (t : Fin 1 → ZMod 17) (c : Digest) (resp : Option (Fin 2 → ℤ)) :
      ((interpret (oracle Digest) (hitCont A h (resp.map fun z => (t, z)))).run
        ((((), t), c) :: ([] : Cache))).map (fun out => (A, h, out.1)) =
      PMF.pure (A, h, resp.map fun _ => c) := by
    cases resp with
    | none =>
      simp only [Option.map_none, hitCont, interpret_pure, StateT.run_pure,
        PMF.monad_pure_eq_pure, PMF.pure_map]
    | some z =>
      rw [Option.map_some, hitCont, interpret_map, StateT.run_map, hit_returns_c]
      simp only [PMF.monad_map_eq_map, PMF.pure_map, Option.map_some]
  have hsim_run (A : Matrix (Fin 1) (Fin 2) (ZMod 17))
      (h : Matrix (Fin 1) (Fin 2) (ZMod 17) × Matrix (Fin 1) (Fin 1) (ZMod 17))
      (c : Digest) (view : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ))) :
      ((interpret (oracle Digest) (hitCont A h view)).run
        (lyubashevskySimCache () c ([] : Cache) view)).map (fun out => (A, h, out.1)) =
      PMF.pure (A, h, view.map fun _ => c) := by
    rcases view with _ | ⟨t, z⟩
    · simp only [Option.map_none, hitCont, lyubashevskySimCache_none, interpret_pure,
        StateT.run_pure, PMF.monad_pure_eq_pure, PMF.pure_map]
    · rw [Option.map_some, hitCont, lyubashevskySimCache_some, interpret_map,
        StateT.run_map, hit_returns_c]
      simp only [PMF.monad_map_eq_map, PMF.pure_map]
  rw [lyubashevskySignVisibleProg_eq_bind_full, lyubashevskySignVisibleSim_eq_bind_full]
  dsimp only [lyubashevskySignFullProg, lyubashevskySignFullSim]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  congr 1 with A : 1
  refine PMF.bind_congr_on_support (H_fixed A) _ _ fun h hh => ?_
  simp only [hprog_run, hsim_run]
  rw [PMF.bind_comm]
  congr 1 with c : 1
  have hhvzk := (lyubashevsky_nonAbortSpecialHVZK (n := 1) (m := 2) (k := 1) (q := 17)
    (γ := 3) (β := 1) (by decide) (by decide)).acceptedTranscript_eq
    (0 : Matrix (Fin 2) (Fin 1) ℤ) (A, key.2) (zero_relation A h hh) c
  have hmap := congrArg (PMF.map fun view : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ)) =>
    (A, h, view.map fun _ => c)) hhvzk.symm
  simpa only [acceptedTranscript, transcript, PMF.map, PMF.bind_bind, PMF.pure_bind,
    Option.map_map, Function.comp_def] using hmap

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

/-- Test 2 (avoid): Because `(true, 0) ≠ (false, t)` (`avoid_key_disjoint`), `avoid_miss_cache`
shows the disjoint query misses the signing cache entry even when observing `(sig, digest)`,
yielding exact equality between `lyubashevskySignVisibleProg` and `lyubashevskySignVisibleSim`. -/
theorem avoid_visible_eq :
    lyubashevskySignVisibleProg 1 2 1 17 3 1 H_fixed (fun _ => 0) (fun _ _ => key.2)
      (fun _ => false) (fun _ => []) (fun A h sig => (sig, ·) <$> avoidCont A h sig) =
    lyubashevskySignVisibleSim 1 2 1 17 3 1 H_fixed (fun _ _ => key.2)
      (fun _ => false) (fun _ => []) (fun A h sig => (sig, ·) <$> avoidCont A h sig) := by
  have hcons (A : Matrix (Fin 1) (Fin 2) (ZMod 17))
      (h : Matrix (Fin 1) (Fin 2) (ZMod 17) × Matrix (Fin 1) (Fin 1) (ZMod 17))
      (t : Fin 1 → ZMod 17) (c : Digest)
      (sig : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ))) :
      ((interpret (oracle Digest) ((sig, ·) <$> avoidCont A h sig)).run
        (((false, t), c) :: ([] : List (BoolQuery × Digest)))).map
          (fun out => (A, h, out.1)) =
      (PMF.uniformOfFintype Digest).map fun d => (A, h, (sig, d)) := by
    have hmiss := avoid_miss_cache (q := (false, t)) (q' := (true, (0 : Fin 1 → ZMod 17)))
      c ([] : List (BoolQuery × Digest)) (avoid_key_disjoint (t, 0)) rfl
    rw [avoidCont, interpret_map, StateT.run_map, hmiss]
    simp only [PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]
  have hsim_run (A : Matrix (Fin 1) (Fin 2) (ZMod 17))
      (h : Matrix (Fin 1) (Fin 2) (ZMod 17) × Matrix (Fin 1) (Fin 1) (ZMod 17))
      (c : Digest) (view : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ))) :
      ((interpret (oracle Digest) ((view, ·) <$> avoidCont A h view)).run
        (lyubashevskySimCache false c ([] : List (BoolQuery × Digest)) view)).map
          (fun out => (A, h, out.1)) =
      (PMF.uniformOfFintype Digest).map fun d => (A, h, (view, d)) := by
    rcases view with _ | ⟨t, z⟩
    · rw [lyubashevskySimCache_none, avoidCont, interpret_map, StateT.run_map,
        OracleComp.interpret_query, oracle, StateT.run, memoize_of_none _ _ _ rfl]
      simp [PMF.map, Function.comp_def]
    · rw [lyubashevskySimCache_some]
      exact hcons A h t c (some (t, z))
  rw [lyubashevskySignVisibleProg_eq_bind_full, lyubashevskySignVisibleSim_eq_bind_full]
  have hprog :
      (lyubashevskySignFullProg 1 2 1 17 3 1 H_fixed (fun _ => 0) (fun _ _ => key.2)
        (fun _ => false) (fun _ => [])).bind (fun (A, h, sig, curCache) =>
          ((interpret (oracle Digest) ((sig, ·) <$> avoidCont A h sig)).run curCache).map
            fun out => (A, h, out.1)) =
      ((lyubashevskySignFullProg 1 2 1 17 3 1 H_fixed (fun _ => 0) (fun _ _ => key.2)
        (fun _ => false) (fun _ => [])).map fun (A, h, sig, _) => (A, h, sig)).bind
          fun r => (PMF.uniformOfFintype Digest).map fun d => (r.1, r.2.1, (r.2.2, d)) := by
    dsimp only [lyubashevskySignFullProg]
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, hcons]
    simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
  have hsim :
      (lyubashevskySignFullSim 1 2 1 17 3 1 H_fixed (fun _ _ => key.2)
        (fun _ => false) (fun _ => [])).bind (fun (A, h, view, curCache) =>
          ((interpret (oracle Digest) ((view, ·) <$> avoidCont A h view)).run curCache).map
            fun out => (A, h, out.1)) =
      ((lyubashevskySignFullSim 1 2 1 17 3 1 H_fixed (fun _ _ => key.2)
        (fun _ => false) (fun _ => [])).map fun (A, h, view, _) => (A, h, view)).bind
          fun r => (PMF.uniformOfFintype Digest).map fun d => (r.1, r.2.1, (r.2.2, d)) := by
    dsimp only [lyubashevskySignFullSim]
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind,
      hsim_run]
    simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
  rw [hprog, hsim, ← lyubashevskySignVisibleProg_eq_map_full,
    ← lyubashevskySignVisibleSim_eq_map_full,
    lyubashevskySignVisibleProg_eq_sim_of_pure 1 2 1 17 1 3 1 (by decide) (by decide)
      H_fixed (fun _ => 0) (fun _ _ => key.2) zero_relation (fun _ => false) (fun _ => [])
      (fun _ _ sig => sig)]

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

noncomputable def progExp :=
  lyubashevskySignFullProg 1 2 1 17 3 1 H_fixed (fun _ => 0) (fun _ _ => key.2)
    (fun _ => ()) (fun _ => [])

noncomputable def simExp :=
  lyubashevskySignFullSim 1 2 1 17 3 1 H_fixed (fun _ _ => key.2)
    (fun _ => ()) (fun _ => [])

/-- Test 4: Every supported outcome of `progExp` (`lyubashevskySignFullProg`) has final cache
length 1, even on abort. -/
theorem progExp_cache_length_eq_one
    (r : Matrix (Fin 1) (Fin 2) (ZMod 17) ×
      (Matrix (Fin 1) (Fin 2) (ZMod 17) × Matrix (Fin 1) (Fin 1) (ZMod 17)) ×
      Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ)) × Cache)
    (hr : r ∈ progExp.support) :
    r.2.2.2.length = 1 := by
  simp only [progExp, lyubashevskySignFullProg, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hr
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hr
  rfl

/-- Test 4: `lyubashevskySimCache` leaves an initially empty cache at length 0 on abort. -/
theorem simCache_length_zero_on_abort (c : Digest) :
    (lyubashevskySimCache () c ([] : Cache)
      (none : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ)))).length = 0 := rfl

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

/-- `K = 0` visible simulation client: the programmed hybrid and simulation agree identically
on the `q = 17` test fixture. -/
theorem zero_attempts_prog_eq_sim_test :
    lyubashevskySignAttemptsVisibleProg 1 2 1 17 3 1 0 H_fixed (fun _ => 0) (fun _ _ => key.2)
      (fun _ => ()) (fun _ => []) (fun _ _ sig => pure sig) =
    lyubashevskySignAttemptsVisibleSim 1 2 1 17 3 1 0 H_fixed (fun _ _ => key.2)
      (fun _ => ()) (fun _ => []) (fun _ _ sig => pure sig) :=
  lyubashevskySignAttemptsVisibleProg_zero_eq_sim 1 2 1 17 3 1 H_fixed (fun _ => 0)
    (fun _ _ => key.2) (fun _ => ()) (fun _ => []) (fun _ _ sig => pure sig)

/-- `K = 1` visible simulation client: the programmed hybrid and simulation agree identically
for pure continuations on the `q = 17` test fixture. -/
theorem one_attempt_prog_eq_sim_pure_test :
    lyubashevskySignAttemptsVisibleProg 1 2 1 17 3 1 1 H_fixed (fun _ => 0) (fun _ _ => key.2)
      (fun _ => ()) (fun _ => []) (fun _ _ sig => pure sig) =
    lyubashevskySignAttemptsVisibleSim 1 2 1 17 3 1 1 H_fixed (fun _ _ => key.2)
      (fun _ => ()) (fun _ => []) (fun _ _ sig => pure sig) :=
  lyubashevskySignAttemptsVisibleProg_eq_sim_of_pure_one 1 2 1 17 1 3 1 (by decide) (by decide)
    H_fixed (fun _ => 0) (fun _ _ => key.2) zero_relation (fun _ => ()) (fun _ => [])
    (fun _ _ sig => sig)

/-- `K = 1` visible simulation client: `closeTo_lyubashevskySignAttempts_simulate_one` recovers
the single-attempt bound on the `q = 17` test fixture. -/
theorem one_attempt_prog_sim_closeTo_test :
    CloseTo
      (lyubashevskySignAttemptsVisibleProg 1 2 1 17 3 1 1 H_fixed (fun _ => 0) (fun _ _ => key.2)
        (fun _ => ()) (fun _ => []) (fun _ _ _ => pure ()))
      (lyubashevskySignAttemptsVisibleSim 1 2 1 17 3 1 1 H_fixed (fun _ _ => key.2)
        (fun _ => ()) (fun _ => []) (fun _ _ _ => pure ()))
      ((Nat.cast 0 : ℝ≥0∞) / (Nat.cast 17 : ℝ≥0∞) ^ 1 +
        ENNReal.ofReal (Real.sqrt ((Nat.cast 17 : ℝ) ^ 1 / ((2 * 3 + 1 : ℕ) : ℝ) ^ 2) / 2)) :=
  closeTo_lyubashevskySignAttempts_simulate_one 1 2 1 17 1 3 1 0 (by decide) (by decide) (by decide)
    H_fixed (fun _ => 0) (fun _ _ => key.2) zero_relation (fun _ => ()) (fun _ => [])
    (fun _ _ _ => pure ()) (fun _ _ _ _ => IsCostBounded.pure () 0)

/-- `K ≤ 1` visible simulation client: `closeTo_lyubashevskySignAttempts_simulate_le_one` reduces
`K = 0` and `K = 1` to the single-attempt bound on the `q = 17` test fixture. -/
theorem le_one_attempts_prog_sim_closeTo_test (K : ℕ) (hK : K ≤ 1) :
    CloseTo
      (lyubashevskySignAttemptsVisibleProg 1 2 1 17 3 1 K H_fixed (fun _ => 0) (fun _ _ => key.2)
        (fun _ => ()) (fun _ => []) (fun _ _ _ => pure ()))
      (lyubashevskySignAttemptsVisibleSim 1 2 1 17 3 1 K H_fixed (fun _ _ => key.2)
        (fun _ => ()) (fun _ => []) (fun _ _ _ => pure ()))
      (∑ j ∈ Finset.range K, (((Nat.cast 0 : ℝ≥0∞) + (K : ℝ≥0∞) - 1 - (j : ℝ≥0∞)) /
        (Nat.cast 17 : ℝ≥0∞) ^ 1 +
        ENNReal.ofReal (Real.sqrt ((Nat.cast 17 : ℝ) ^ 1 / ((2 * 3 + 1 : ℕ) : ℝ) ^ 2) / 2))) :=
  closeTo_lyubashevskySignAttempts_simulate_le_one 1 2 1 17 1 3 1 K 0 (by decide) (by decide)
    (by decide) hK H_fixed (fun _ => 0) (fun _ _ => key.2) zero_relation (fun _ => ())
    (fun _ => []) (fun _ _ _ => pure ()) (fun _ _ _ _ => IsCostBounded.pure () 0)

end LyubashevskySimulationTests

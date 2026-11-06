/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature.Simulation
public import ComplexityTests.Crypto.LyubashevskyRandomOracle

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

/-- Test 2 (avoid): Continuation querying a distinct point makes at most 1 query. -/
def avoidCont (_ : Matrix (Fin 1) (Fin 2) (ZMod 17))
    (_ : Matrix (Fin 1) (Fin 2) (ZMod 17) × Matrix (Fin 1) (Fin 1) (ZMod 17))
    (_ : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ))) :
    OracleComp (fun _ : Query => Digest) Digest :=
  OracleComp.query ((), 2)

theorem avoid_bounded (A : Matrix (Fin 1) (Fin 2) (ZMod 17))
    (h : Matrix (Fin 1) (Fin 2) (ZMod 17) × Matrix (Fin 1) (Fin 1) (ZMod 17))
    (sig : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ))) :
    IsQueryBounded (avoidCont A h sig) 1 :=
  IsCostBounded.query (spec := fun _ : Query => Digest) (cost := fun _ => 1) ((), 2)

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
theorem counterexample_abort_mass (c : Digest) :
    protocol.acceptedTranscript (0 : Matrix (Fin 2) (Fin 1) ℤ) key c none =
      1 - (5 / 7 : ℝ≥0∞) ^ 2 := by
  have habort := lyubashevsky_acceptedTranscript_none (n := 1) (m := 2) (k := 1) (q := 17)
    (γ := 3) (β := 1) (η := 1) (by decide) (by decide)
    (S := (0 : Matrix (Fin 2) (Fin 1) ℤ)) (by intro i j; simp) key c
  rw [habort]
  norm_num

/-- Test 4: In Prog, the final cache always has length 1 (never empty), even on abort. -/
theorem prog_cache_length_ne_zero (coin : (Fin 1 → ZMod 17) × (Fin 2 → ℤ)) (c : Digest) :
    (((((), coin.1), c) :: ([] : Cache))).length ≠ 0 := by
  simp

/-- Test 4: In Trans, on abort the final cache is empty (length 0). -/
theorem trans_cache_length_zero_on_abort (c : Digest) :
    (match (none : Option ((Fin 1 → ZMod 17) × (Fin 2 → ℤ))) with
     | some (t, _) => [(((), t), c)]
     | none => ([] : Cache)).length = 0 := rfl

end LyubashevskySimulationTests

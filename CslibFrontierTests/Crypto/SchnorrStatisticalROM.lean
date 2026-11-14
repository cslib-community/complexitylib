/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SchnorrSignature.StatisticalROM
import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import Mathlib.Tactic.NormNum.Prime

/-! Adaptive sampler replacement retains the complete output/cache/log, and an actual native
forger obtains its budget from the actual key generator rather than a supplied call cap. -/

noncomputable section

namespace CslibFrontierTests.Crypto.SchnorrStatisticalROM

open Cslib Cslib.Probability Cslib.Interactive Cslib.Crypto Cslib.Crypto.Protocols ROMSignature
open Turing Turing.MultiTapeTM OracleComp
open scoped ENNReal NNReal

private def d23 : schnorrGroups.Desc :=
  ⟨(23, 11, 2), ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

local instance : NeZero (schnorrGroups.order d23) := ⟨by decide⟩
private theorem width_bound : 2 ^ 3 ≤ schnorrGroups.order d23 := by decide

private def hashOnly :
    OracleComp (ForgerSpec (List Bool) (List Bool) (List Bool) (BitString 3)) (BitString 3) := do
  let _ ← query (.inr [])
  let _ ← query (.inr [true])
  query (spec := ForgerSpec (List Bool) (List Bool) (List Bool) (BitString 3)) (.inr [])

private theorem hashOnly_bound : IsCostBounded signingCost hashOnly 0 :=
  .liftBind _ _ 0 fun _ => .liftBind _ _ 0 fun _ => .query _

-- Even state-mutating hash requests and arbitrary raw secret keys cost no nonce error.
example (sk : List Bool) (n : ℕ)
    (state : List (List Bool × BitString 3) × List (List Bool)) :
    CloseTo
      (runWith (handler (schnorrGroups.schnorrEncodedROMScheme d23 3
        (PMF.pure ([], [])) ((ProbComp.eval (schnorrGroups.sampleExp n d23)).map Nat.cast)) sk)
        hashOnly state)
      (runWith (handler (schnorrGroups.schnorrEncodedROMScheme d23 3
        (PMF.pure ([], [])) (PMF.uniformOfFintype (ZMod (schnorrGroups.order d23)))) sk)
        hashOnly state) 0 := by
  simpa using schnorrGroups.closeTo_runWith_schnorrEncodedROMScheme d23 n 3
    (PMF.pure ([], [])) sk hashOnly hashOnly_bound state

private def forger : Forger (List Bool) (List Bool) (List Bool) (List Bool) (BitString 3) where
  Coins := Unit
  coins := PMF.pure ()
  forge _ _ := do
    let sig ← query (.inl [])
    let _ ← query (.inl [])
    let digest ← query (.inr sig)
    let _ ← query (.inr [])
    let _ ← query (.inr [true])
    return (List.ofFn digest, sig)

private theorem forger_bound : forger.CallBounded 2 3 := by
  intro _ _
  constructor
  · exact .liftBind _ _ 1 fun _ => .liftBind _ _ 0 fun _ =>
      .liftBind _ _ 0 fun _ => .liftBind _ _ 0 fun _ => .liftBind _ _ 0 fun _ => .pure _ 0
  · exact .liftBind _ _ 3 fun _ => .liftBind _ _ 3 fun _ =>
      .liftBind _ _ 2 fun _ => .liftBind _ _ 1 fun _ => .liftBind _ _ 0 fun _ => .pure _ 0

private def cache : List (List Bool × BitString 3) :=
  [([], ![true, false, true]), ([true], ![false, true, true])]

-- Nontrivial error 2/16, full candidate output, populated junk cache, and a repeated-signing log.
example (sk pk : List Bool) :
    CloseTo
      (runWith (handler (schnorrGroups.schnorrEncodedROMScheme d23 3
        (PMF.pure ([], [])) ((ProbComp.eval (schnorrGroups.sampleExp 4 d23)).map Nat.cast)) sk)
        (forger.forge pk ()) (cache, [[]]))
      (runWith (handler (schnorrGroups.schnorrEncodedROMScheme d23 3
        (PMF.pure ([], [])) (PMF.uniformOfFintype (ZMod (schnorrGroups.order d23)))) sk)
        (forger.forge pk ()) (cache, [[]])) (1 / 8 : ℝ≥0) := by
  convert schnorrGroups.closeTo_runWith_schnorrEncodedROMScheme d23 4 3
    (PMF.pure ([], [])) sk (forger.forge pk ()) (forger_bound pk ()).1 (cache, [[]]) using 1
  change (↑(1 / 8 : ℝ≥0) : ℝ≥0∞) = 2 * ↑(1 / 2 ^ 4 : ℝ≥0)
  rw [← ENNReal.coe_ofNat 2, ← ENNReal.coe_mul]
  norm_num

-- The actual key pair adds 1/16 to the two signing errors; the result is below one.
example : CloseTo
    (eufCmaGame (schnorrGroups.schnorrEncodedROMScheme d23 3
      (ProbComp.eval (schnorrGroups.schnorrSigKeyGen 4 d23))
      ((ProbComp.eval (schnorrGroups.sampleExp 4 d23)).map Nat.cast)) forger)
    (eufCmaGame (schnorrGroups.schnorrWordROMScheme d23 width_bound)
      (schnorrGroups.schnorrDecodedForger d23 forger)) (3 / 16 : ℝ≥0) := by
  convert schnorrGroups.closeTo_eufCmaGame_schnorrEncodedROMScheme d23 4 3 width_bound
    forger forger_bound using 1
  change (↑(3 / 16 : ℝ≥0) : ℝ≥0∞) = 3 * ↑(1 / 2 ^ 4 : ℝ≥0)
  rw [← ENNReal.coe_ofNat 3, ← ENNReal.coe_mul]
  norm_num

private def nativeForger (_ : ℕ) (_ : List Bool) :
    WordOracleComp Bool (List Bool × List Bool) := do
  let sig ← List.take 1 <$> ProbOracleComp.query (false, [])
  let _ ← List.take 1 <$> ProbOracleComp.query (false, [])
  let digest ← List.take 3 <$> ProbOracleComp.query (true, sig)
  return (digest, sig)

private theorem nativeForger_ppt : IsOraclePPT (encPair encBits encBits) nativeForger := by
  unfold IsOraclePPT nativeForger
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · fun_prop
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · fun_prop
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · fun_prop
  fun_prop

-- Instantiate the complete native endpoint, including the derived machine/clock and actual keys.
-- The constant description is a finite example, not an asymptotic security assumption.
example : ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : MultiTapePTM k Bool Control Bool) (c e keyC keyD : ℕ),
    IsOraclePPTOn (encPair encUnary (encPair encBits encBits)) (encPair encBits encBits)
      (savedWordReplay machine (fun op word => ProbOracleComp.query (op, word)) c e keyC keyD) ∧
    ∀ n,
      let encoding : BitString 3 ↪ List Bool := ⟨List.ofFn, List.ofFn_injective⟩
      let A := savedCoinForger machine encoding c e keyC keyD n
      let budget := savedCoinBudget c e keyC keyD n
      A.CallBounded budget budget ∧
      CloseTo
        (worldGame (schnorrGroups.schnorrEncodedROMScheme d23 3
          (ProbComp.eval (schnorrGroups.schnorrSigKeyGen n d23))
          ((ProbComp.eval (schnorrGroups.sampleExp n d23)).map Nat.cast))
          (fun pk => routeWordProgram encoding (nativeForger n pk))
          (fun verified ⟨msg, _⟩ pairs => verified && !(pairs.map Prod.fst).contains msg))
        (eufCmaGame (schnorrGroups.schnorrWordROMScheme d23 width_bound)
          (schnorrGroups.schnorrDecodedForger d23 A))
        ((budget + 1 : ℕ) * (1 / 2 ^ n : ℝ≥0)) :=
  schnorrGroups.exists_closeTo_worldGame_schnorrEncodedROMScheme (fun _ => d23)
    (by fun_prop) (fun _ => 3) (fun _ => width_bound) nativeForger_ppt

end CslibFrontierTests.Crypto.SchnorrStatisticalROM

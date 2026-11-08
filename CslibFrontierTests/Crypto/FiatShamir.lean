/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Crypto.Protocols.SigmaProtocol.FiatShamir
import CslibFrontier.Crypto.Protocols.SigmaProtocol.SchnorrIdentification
import CslibFrontier.Crypto.Protocols.SigmaProtocol.SchnorrSignature
import CslibFrontier.Probability.PMF
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for Fiat–Shamir signatures

Schnorr signatures in `ZMod 11`, with base `2`, are Fiat–Shamir signatures from Schnorr's
protocol, and honest signatures verify. Discrete logarithms are easy here: a forger that computes
the witness and signs a message honestly, with one hash call, always wins, so the security
theorem for Schnorr signatures makes the reduction compute discrete logarithms with probability
at least `81 / 242`.
-/

namespace ComplexityTests.Crypto.FiatShamir

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols SigmaProtocol ROMSignature
open scoped NNReal

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- Challenges are all of `ZMod 11`. -/
abbrev ι : ZMod 11 ↪ ZMod 11 := Function.Embedding.refl _

/-- Schnorr signatures on `Bool` messages in `ZMod 11` with base `2`. -/
noncomputable abbrev scheme :=
  fiatShamir (M := Bool) (Function.Embedding.refl _) (schnorr ι (2 : ZMod 11)) (schnorrKeyGen 2)

/-- Honest Schnorr signatures verify. -/
example : scheme.Correct :=
  fiatShamir_correct (Function.Embedding.refl _) schnorr_complete fun _ h =>
    mem_support_schnorrKeyGen h

/-- The forger that computes the witness `6 • u` of `u` and signs `true` honestly, with one hash
call. -/
noncomputable def knower : Forger (ZMod 11) Bool (ZMod 11 × ZMod 11) (Bool × ZMod 11) (ZMod 11)
    where
  Coins := ZMod 11
  coins := PMF.uniformOfFintype (ZMod 11)
  forge u r := do
    let c ← OracleComp.query (spec := ForgerSpec Bool (Bool × ZMod 11) (ZMod 11 × ZMod 11)
      (ZMod 11)) (.inr (true, r • 2))
    return (true, (r • 2, r + c • (6 • u)))

/-- The knowing forger always wins. -/
theorem succProbability_knower : Game.succProbability (eufCmaGame scheme knower) = 1 := by
  rw [Game.succProbability, ENNReal.toNNReal_eq_one_iff]
  refine le_antisymm (PMF.coe_le_one _ _) ?_
  simp only [eufCmaGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine PMF.le_bind_apply_on_support _ fun keys hkeys => ?_
  obtain ⟨key, hkey, rfl⟩ := (_root_.PMF.mem_support_map_iff _ _ _).mp hkeys
  have hrel := mem_support_schnorrKeyGen hkey
  refine PMF.le_bind_apply_on_support _ fun (r : ZMod 11) _ => ?_
  refine PMF.le_bind_apply_on_support _ fun forged hforged => ?_
  simp only [knower, OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
    OracleComp.interpret_pure, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff,
    StateT.run_pure, PMF.monad_pure_eq_pure, _root_.PMF.mem_support_pure_iff] at hforged
  obtain ⟨answer, hanswer, rfl⟩ := hforged
  change answer ∈ ((memoize (fun _ => PMF.uniformOfFintype (ZMod 11)) (true, r • (2 : ZMod 11))
    []).bind fun a => PMF.pure (a.1, a.2, ([] : List Bool))).support at hanswer
  rw [memoize_of_none _ _ _ rfl] at hanswer
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind,
    PMF.mem_support_bind_iff, _root_.PMF.mem_support_pure_iff] at hanswer
  obtain ⟨c, -, rfl⟩ := hanswer
  refine PMF.le_bind_apply_on_support _ fun verified hverified => ?_
  simp only [scheme, fiatShamir, OracleComp.interpret_map, OracleComp.interpret_query,
    StateT.run_map, PMF.monad_map_eq_map, _root_.PMF.mem_support_map_iff] at hverified
  obtain ⟨v, hv, rfl⟩ := hverified
  change v ∈ (memoize (fun _ => PMF.uniformOfFintype (ZMod 11)) (true, r • (2 : ZMod 11))
    [((true, r • 2), c)]).support at hv
  rw [memoize_of_some _ _ _ _ List.lookup_cons_self, PMF.monad_pure_eq_pure,
    _root_.PMF.mem_support_pure_iff] at hv
  subst hv
  have h11 : (11 : ZMod 11) = 0 := by decide
  have haccept : (schnorr ι (2 : ZMod 11)).Accepts key.2 (r • 2) c (r + c • (6 • key.2)) := by
    rw [schnorr_accepts_iff, ← hrel]
    simp only [smul_eq_mul, Function.Embedding.refl_apply]
    linear_combination (2 * c * key.1) * h11
  have hverify : (schnorr ι (2 : ZMod 11)).verify key.2 (r • 2) c (r + c • (6 • key.2)) = true :=
    haccept
  simp only [hverify]
  simp

/-- The knowing forger makes no signing call and one hash call. -/
theorem knower_callBounded : knower.CallBounded 0 1 :=
  fun _ _ => ⟨.liftBind _ _ 0 fun _ => .pure _ 0, .liftBind _ _ 0 fun _ => .pure _ 0⟩

/-- The reduction built from the knowing forger computes a discrete logarithm with probability at
least `81 / 242`: the security bound, with no signing call and one hash call, reads
`1 ≤ 0 + 2 / 11 + √(2 · ε')`. -/
example : (81 / 242 : ℝ) ≤ Game.succProbability (oneWayGame (schnorrKeyGen (2 : ZMod 11))
    (fun α u => α • (2 : ZMod 11) = u)
    (FiatShamir.reduction (Function.Embedding.refl _) (schnorr ι (2 : ZMod 11))
      (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod 11) (ZMod 11) 2) id ι)
      (linearExtract ι) 0 knower 0 1)) := by
  have h := schnorr_succProbability_eufCmaGame_le (ι := ι) (g := (2 : ZMod 11)) (by decide)
    knower knower_callBounded
  have hknower : Game.succProbability (eufCmaGame (fiatShamir (M := Bool)
    (Function.Embedding.refl _)
      (schnorr ι (2 : ZMod 11)) (schnorrKeyGen 2)) knower) = 1 := succProbability_knower
  rw [hknower, ZMod.card] at h
  set ε := (Game.succProbability (oneWayGame (schnorrKeyGen (2 : ZMod 11))
    (fun α u => α • (2 : ZMod 11) = u)
    (FiatShamir.reduction (Function.Embedding.refl _) (schnorr ι (2 : ZMod 11))
      (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod 11) (ZMod 11) 2) id ι)
      (linearExtract ι) 0 knower 0 1)) : ℝ) with hε
  have hε0 : 0 ≤ ε := NNReal.coe_nonneg _
  simp only [Nat.cast_zero, zero_mul, zero_div, zero_add, Nat.cast_one,
    show (1 : ℝ) + 1 = 2 by norm_num] at h
  have hsqrt : (9 / 11 : ℝ) ≤ √(2 * ε) := by
    simp only [NNReal.coe_one, Nat.cast_ofNat] at h
    linarith
  have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * ε)
  nlinarith [mul_le_mul hsqrt hsqrt (by norm_num) (Real.sqrt_nonneg _)]

/-- Two tagged junk queries lie outside the message/commitment image. -/
private def extendedHashPoint : (Bool × ZMod 11) ↪ ((Bool × ZMod 11) ⊕ Bool) :=
  Function.Embedding.inl

example (point : Bool × ZMod 11) (junk : Bool) : extendedHashPoint point ≠ .inr junk := by
  simp [extendedHashPoint]

/-- An out-of-image point remains cached while a canonical point is queried in between. -/
private def mixedHashQueries :
    OracleComp (ForgerSpec Bool (((Bool × ZMod 11) ⊕ Bool)) (ZMod 11 × ZMod 11) (ZMod 11))
      (ZMod 11 × ZMod 11 × ZMod 11 × ZMod 11) := do
  let first ← OracleComp.query (.inr (.inr false))
  let canonical ← OracleComp.query (.inr (.inl (true, 0)))
  let other ← OracleComp.query (.inr (.inr true))
  let repeated ← OracleComp.query (.inr (.inr false))
  return (first, canonical, other, repeated)

-- Four adversary hash calls induce three fresh queries; distinct junk keys are never collapsed.
example :
    OracleComp.runWithAnswers (0 : ZMod 11)
      ((OracleComp.interpret (FiatShamir.reductionHandler extendedHashPoint)
        mixedHashQueries).run ⟨[], [], 0, []⟩) [3, 7, 9] =
      (((3, 7, 9, 3),
        ⟨[(.inr true, 9, some 2), (.inl (true, 0), 7, some 1), (.inr false, 3, some 0)],
          [], 3, []⟩), [.inr false, .inl (true, 0), .inr true]) := by rfl

-- Programming a signature retains a previously cached junk key and records only its own message.
example :
    OracleComp.runWithAnswers (0 : ZMod 11)
      ((FiatShamir.reductionHandler extendedHashPoint (.inl false)).run
        ⟨[(.inr false, 3, some 0)], [], 1, [(0, 5, 9)]⟩) [] =
      (((0, 9), ⟨[(.inl (false, 0), 5, none), (.inr false, 3, some 0)], [false], 1, []⟩),
        []) := by rfl

example : (fiatShamir extendedHashPoint (schnorr ι (2 : ZMod 11))
    (schnorrKeyGen 2)).Correct :=
  fiatShamir_correct extendedHashPoint schnorr_complete fun _ h => mem_support_schnorrKeyGen h

private noncomputable def extendedForger :
    Forger (ZMod 11) Bool (ZMod 11 × ZMod 11) (((Bool × ZMod 11) ⊕ Bool)) (ZMod 11) where
  Coins := Unit
  coins := PMF.pure ()
  forge _ _ := do
    let answers ← mixedHashQueries
    return (answers.1 == answers.2.2.2, (0, answers.2.1))

private theorem extendedForger_bound : extendedForger.CallBounded 0 4 := by
  intro _ _
  constructor
  · exact .liftBind _ _ 0 fun _ => .liftBind _ _ 0 fun _ =>
      .liftBind _ _ 0 fun _ => .liftBind _ _ 0 fun _ => .pure _ 0
  · exact .liftBind _ _ 3 fun _ => .liftBind _ _ 2 fun _ =>
      .liftBind _ _ 1 fun _ => .liftBind _ _ 0 fun _ => .pure _ 0

-- The same quantitative theorem applies without restricting queries to the embedding image.
example :
    (Game.succProbability (eufCmaGame
      (fiatShamir extendedHashPoint (schnorr ι (2 : ZMod 11)) (schnorrKeyGen 2))
        extendedForger) : ℝ) ≤
      0 * (0 + 4) * (11 : ℝ≥0)⁻¹ + (4 + 1) / Fintype.card (ZMod 11) +
        √((4 + 1) * Game.succProbability
          (oneWayGame (schnorrKeyGen (2 : ZMod 11)) (fun α u => α • (2 : ZMod 11) = u)
            (FiatShamir.reduction extendedHashPoint (schnorr ι (2 : ZMod 11))
              (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod 11) (ZMod 11) 2)
                id ι) (linearExtract ι) 0 extendedForger 0 4))) := by
  have hcommit : ∀ key ∈ (schnorrKeyGen (2 : ZMod 11)).support, ∀ t,
      ((schnorr ι (2 : ZMod 11)).commit key.1 key.2).map Prod.fst t ≤ (11 : ℝ≥0)⁻¹ := by
    intro key _ t
    rw [ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat]
    exact schnorr_commit_map_fst_le (ι := ι) (by decide : (2 : ZMod 11) ≠ 0) key.1 key.2 t
  have h := succProbability_eufCmaGame_le extendedHashPoint
    (fun _ h => mem_support_schnorrKeyGen h)
    (schnorr_specialSoundness.specialSoundOn (schnorrKeyGen 2)) schnorr_specialHVZK
    hcommit 0 extendedForger extendedForger_bound
  simpa only [Nat.cast_zero, Nat.cast_ofNat] using h

-- An intentionally rejecting protocol forces the fork to fail. The supplied result is returned
-- literally, with no witness-relation premise and no hidden choice of a different value.
private noncomputable def rejecting : SigmaProtocol ℕ Unit Unit Bool Unit where
  State := Unit
  commit _ _ := PMF.pure ((), ())
  respond _ _ _ _ := ()
  verify _ _ _ _ := false

private noncomputable def emptyForger : Forger Unit Unit (Unit × Unit) (Unit × Unit) Bool where
  Coins := Unit
  coins := PMF.pure ()
  forge _ _ := pure ((), (), ())

private theorem reduction_rejecting (fallback : ℕ) :
    FiatShamir.reduction (Function.Embedding.refl _) rejecting
      (fun _ _ => PMF.pure ((), ())) (fun _ _ _ _ _ _ => 0) fallback emptyForger 0 0 () =
      PMF.pure fallback := by
  simp [FiatShamir.reduction, FiatShamir.coins, Forking.fork, OracleComp.forkingAlgorithm,
    FiatShamir.forkingProgram, FiatShamir.finish, FiatShamir.verdict, emptyForger,
    rejecting, OracleComp.validIndex, OracleComp.forkNamedPosition,
    OracleComp.runWithAnswersOutput, PMF.iid]

example :
    FiatShamir.reduction (Function.Embedding.refl _) rejecting
      (fun _ _ => PMF.pure ((), ())) (fun _ _ _ _ _ _ => 0) 2 emptyForger 0 0 () ≠
    FiatShamir.reduction (Function.Embedding.refl _) rejecting
      (fun _ _ => PMF.pure ((), ())) (fun _ _ _ _ _ _ => 0) 7 emptyForger 0 0 () := by
  simp only [reduction_rejecting]
  intro h
  have hprob := congrArg (fun law : PMF ℕ => law 2) h
  norm_num [PMF.pure_apply] at hprob

end ComplexityTests.Crypto.FiatShamir

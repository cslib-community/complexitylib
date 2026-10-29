/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Protocols.MAC.CarterWegman
import Complexity.Tactic.PPT
import Complexity.Tactic.PolyTime
import Mathlib.Algebra.Field.ZMod

/-!
# Tests for Carter–Wegman MACs from Δ-universal hashing

Checks concrete tag generation and verification for `xpolyHash` over `ZMod 7` and Boolean-matrix
linear hashing over `BitString 2`, instantiates `OneTimeForger`, `CounterForger`, `NonceForger`,
`RandomNonceForger`, `NonceMACForger`, and `Forger` on multi-query adaptive programs, and exercises
the one-time, multi-query counter, nonce-based, randomized, and computational (`NonceMACScheme` and
`MACScheme`) security bounds of `Complexity.Crypto.Protocols.MAC.CarterWegman`.
-/

namespace ComplexityTests.Crypto.CarterWegman

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols.CarterWegman Turing.MultiTapeTM
open scoped ENNReal

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

-- Concrete polynomial Carter–Wegman sign and verify over `ZMod 7`:
-- `polyHash 3 [2, 4] = ((1 * 3 + 2) * 3 + 4) = 19 ≡ 5 (mod 7)`,
-- `xpolyHash 3 [2, 4] = 3 * 5 = 15 ≡ 1 (mod 7)`,
-- `sign xpolyHash 3 4 [2, 4] = 1 + 4 = 5 (mod 7)`.
example : sign (xpolyHash (F := ZMod 7)) 3 4 [2, 4] = 5 := by decide

example : verify (xpolyHash (F := ZMod 7)) 3 4 [2, 4] 5 = true := by decide

example : verify (xpolyHash (F := ZMod 7)) 3 4 [2, 4] 6 = false := by decide

-- Concrete pad reconstruction: `-xpolyHash 3 [2, 4] + 5 = -1 + 5 = 4 (mod 7)`.
example : -xpolyHash (F := ZMod 7) 3 [2, 4] + 5 = 4 := by decide

-- Concrete `checkCounterSlot`, `checkCounterEUF`, and `checkCounterSUF` checks on a two-slot
-- pad log.
example :
    checkCounterSlot (xpolyHash (F := ZMod 7)) 3 [([2, 4], 4), ([1], 2)] (0, [2, 4], 5) =
      false := by decide

example :
    checkCounterSUF (xpolyHash (F := ZMod 7)) 3 [([2, 4], 4), ([1], 2)] (0, [2, 4], 5) =
      false := by decide

-- Out-of-bounds counter slot is rejected.
example :
    checkCounterSlot (xpolyHash (F := ZMod 7)) 3 [([2, 4], 4)] (1, [1], 0) = false := by decide

/-- Concrete adaptive one-time forger over `ZMod 7` messages of length at most `2`:
queries `[1, 2]` and outputs `([2, 1], t + 1)`. -/
noncomputable def sampleOneTimeForger :
    OneTimeForger {m : List (ZMod 7) // m.length ≤ 2} (ZMod 7) where
  query := PMF.pure ⟨[1, 2], by decide⟩
  forge _ t := PMF.pure (⟨[2, 1], by decide⟩, t + 1)

/-- Concrete two-query adaptive counter forger over `ZMod 7` messages of length at most `2`:
queries `m₀ = [1, 2]` (receiving `t₀`), queries `m₁ = [2, 1]` (receiving `t₁`), and outputs a
forgery attempt `(0, [0, 3], t₀ + t₁)` against counter slot `0`. -/
noncomputable def sampleCounterForger :
    CounterForger {m : List (ZMod 7) // m.length ≤ 2} (ZMod 7) where
  Coins := Unit
  coins := PMF.pure ()
  forge _ := do
    let t₀ ← OracleComp.query (spec := fun _ : {m : List (ZMod 7) // m.length ≤ 2} => ZMod 7)
      ⟨[1, 2], by decide⟩
    let t₁ ← OracleComp.query (spec := fun _ : {m : List (ZMod 7) // m.length ≤ 2} => ZMod 7)
      ⟨[2, 1], by decide⟩
    return (0, ⟨[0, 3], by decide⟩, t₀ + t₁)

-- Concrete instantiation of one-time, two-query adaptive counter, and zero-query polynomial
-- Carter–Wegman security over `ZMod 7` (`ℓ = 2`).
example :
    oneTimeGame (PMF.uniformOfFintype (ZMod 7))
      (fun k (m : {m : List (ZMod 7) // m.length ≤ 2}) => xpolyHash k m)
      sampleOneTimeForger true ≤ (2 + 1) / Fintype.card (ZMod 7) ∧
    counterGame (PMF.uniformOfFintype (ZMod 7))
      (fun k (m : {m : List (ZMod 7) // m.length ≤ 2}) => xpolyHash k m)
      sampleCounterForger true ≤ (2 + 1) / Fintype.card (ZMod 7) ∧
    counterStrongGame (PMF.uniformOfFintype (ZMod 7))
      (fun k (m : {m : List (ZMod 7) // m.length ≤ 2}) => xpolyHash k m)
      sampleCounterForger true ≤ (2 + 1) / Fintype.card (ZMod 7) ∧
    zeroQueryGame (PMF.uniformOfFintype (ZMod 7)) (xpolyHash (F := ZMod 7))
      (PMF.pure ([1, 2], 5)) true = (Fintype.card (ZMod 7) : ℝ≥0∞)⁻¹ :=
  ⟨oneTimeGame_xpolyHash_le 2 sampleOneTimeForger,
   counterGame_xpolyHash_le 2 sampleCounterForger,
   counterStrongGame_xpolyHash_le 2 sampleCounterForger,
   zeroQueryGame_apply_true _ _ _⟩

-- Concrete instantiation of the pseudorandom-pad hybrid bound over `ZMod 7`.
example (padDist : PMF (ZMod 7)) :
    (maskedOneTimeGame (PMF.uniformOfFintype (ZMod 7)) padDist
      (fun k (m : {m : List (ZMod 7) // m.length ≤ 2}) => xpolyHash k m)
      sampleOneTimeForger true).toReal ≤
      (((2 : ℝ≥0∞) + 1) / Fintype.card (ZMod 7)).toReal +
        |((padDist.bind (padDistinguisher (PMF.uniformOfFintype (ZMod 7))
            (fun k (m : {m : List (ZMod 7) // m.length ≤ 2}) => xpolyHash k m)
            sampleOneTimeForger)) true).toReal -
          (((PMF.uniformOfFintype (ZMod 7)).bind (padDistinguisher (PMF.uniformOfFintype (ZMod 7))
            (fun k (m : {m : List (ZMod 7) // m.length ≤ 2}) => xpolyHash k m)
            sampleOneTimeForger)) true).toReal| := by
  refine maskedOneTimeGame_toReal_le (isDeltaUniversalHash_xpolyHash 2) ?_ padDist
    sampleOneTimeForger
  exact ENNReal.div_ne_top (by simp) (by simp)

-- Concrete `ProbComp` one-time forger and PRF-masked Carter–Wegman bound over `BitString 2`.
noncomputable def sampleBitStringQuery : ProbComp (BitString 2) :=
  pure (fun _ => false)

noncomputable def sampleBitStringForge (_ : BitString 2) (t : BitString 2) :
    ProbComp (BitString 2 × BitString 2) :=
  pure (fun _ => true, t)

example (family : List Bool → List Bool → List Bool) :
    (prfOneTimeGame (ProbComp.eval (ProbComp.uniform (Fin 2 → BitString 2)))
      family 2 BitString.LinearHash.hash
      (OneTimeForger.ofProbComp sampleBitStringQuery sampleBitStringForge) true).toReal ≤
      (((Fintype.card (BitString 2) : ℝ≥0∞))⁻¹).toReal +
        (Game.advantage
          (ProbComp.eval (prfRealGame family
            (prfPadDistinguisher fun _ r =>
              probPadTest (ProbComp.uniform (Fin 2 → BitString 2))
                BitString.LinearHash.hash sampleBitStringQuery sampleBitStringForge
                (BitString.ofList 2 (List.ofFn r))) 2))
          (ProbComp.eval (prfIdealGame
            (prfPadDistinguisher fun _ r =>
              probPadTest (ProbComp.uniform (Fin 2 → BitString 2))
                BitString.LinearHash.hash sampleBitStringQuery sampleBitStringForge
                (BitString.ofList 2 (List.ofFn r))) 2)) : ℝ) := by
  refine prfOneTimeGame_ofProbComp_le ?_ (by simp) family
    sampleBitStringQuery sampleBitStringForge
  simpa only [ProbComp.eval_uniform] using BitString.LinearHash.isDeltaUniversalHash 2 2

example (family : List Bool → List Bool → List Bool) :
    (prfOneTimeStrongGame (ProbComp.eval (ProbComp.uniform (Fin 2 → BitString 2)))
      family 2 BitString.LinearHash.hash
      (OneTimeForger.ofProbComp sampleBitStringQuery sampleBitStringForge) true).toReal ≤
      (((Fintype.card (BitString 2) : ℝ≥0∞))⁻¹).toReal +
        (Game.advantage
          (ProbComp.eval (prfRealGame family
            (prfPadDistinguisher fun _ r =>
              probPadTest (ProbComp.uniform (Fin 2 → BitString 2))
                BitString.LinearHash.hash sampleBitStringQuery sampleBitStringForge
                (BitString.ofList 2 (List.ofFn r))) 2))
          (ProbComp.eval (prfIdealGame
            (prfPadDistinguisher fun _ r =>
              probPadTest (ProbComp.uniform (Fin 2 → BitString 2))
                BitString.LinearHash.hash sampleBitStringQuery sampleBitStringForge
                (BitString.ofList 2 (List.ofFn r))) 2)) : ℝ) := by
  refine prfOneTimeStrongGame_ofProbComp_le ?_ (by simp) family
    sampleBitStringQuery sampleBitStringForge
  simpa only [ProbComp.eval_uniform] using BitString.LinearHash.isDeltaUniversalHash 2 2

/-- Constant (insecure) PRF family that ignores its key and echoes the query word (so on the fixed
nonce `List.replicate n false` it always returns `0ⁿ`). -/
def insecureZeroFamily (_key query : List Bool) : List Bool := query

-- Concrete semantic check: under `insecureZeroFamily`, `prfPadDist` collapses to a point mass.
theorem prfPadDist_insecureZeroFamily (n : ℕ) :
    prfPadDist insecureZeroFamily n =
      PMF.pure (BitString.ofList n (List.replicate n false)) :=
  PMF.map_const (BitString.uniformList n) (BitString.ofList n (List.replicate n false))

-- Concrete semantic check: a pad test that checks whether the pad equals the fixed all-false pad
-- succeeds with probability `1` in `prfRealGame` against `insecureZeroFamily`.
example :
    ProbComp.eval
      (prfRealGame insecureZeroFamily
        (prfPadDistinguisher fun k (r : BitString k) =>
          pure (decide (r = BitString.ofList k (List.replicate k false)))) 2)
      true = 1 := by
  rw [eval_prfRealGame_prfPadDistinguisher, prfPadDist_insecureZeroFamily]
  simp

-- Concrete semantic check: when the PRF pad is fixed (`insecureZeroFamily`) and the hash is
-- `fun _ _ => 0`, a forger querying `fun _ => false` and forging `(fun _ => true, pad)` wins
-- `prfOneTimeGame` with certainty (`PMF.pure true`).
example :
    prfOneTimeGame (PMF.pure ()) insecureZeroFamily 2
      (fun (_ : Unit) (_ : BitString 2) => (0 : BitString 2))
      (OneTimeForger.ofProbComp sampleBitStringQuery sampleBitStringForge) =
      PMF.pure true := by
  rw [prfOneTimeGame, maskedOneTimeGame_eq_bind_padDistinguisher, prfPadDist_insecureZeroFamily]
  simp only [padDistinguisher, OneTimeForger.ofProbComp, sampleBitStringQuery, sampleBitStringForge,
    sign, verify, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind, ProbComp.eval_pure]
  congr 1

-- Concrete `IsOraclePPT` admissibility check for `wordProbPadTest` and `prfPadDistinguisher`.
example :
    IsOraclePPT Turing.MultiTapeTM.encBool
      (prfPadDistinguisher
        (wordProbPadTest
          (fun n => BitString.sampleList n)
          (fun _ k _ => k)
          (fun _ => pure [])
          (fun _ _ t => pure ([true], t)))) :=
  isOraclePPT_prfPadDistinguisher_wordProbPadTest (by ppt) (by polytime) (by ppt) (by ppt)

/-- Two-slot `n`-bit nonce schedule: slot `0` has leading bit `false` and slot `1` has leading bit
`true`, padded with `n - 1` `false` bits. For every `n ≥ 1`, both nonces have length `n` and are
distinct on `{0, 1}`. -/
def twoSlotNonce (n i : ℕ) : List Bool :=
  decide (i = 1) :: List.replicate (n - 1) false

/-- Trivial counter forger that makes `0 ≤ 2` signing queries and outputs `(0, (0, 0))`. -/
noncomputable def zeroQueryCounterForger (n : ℕ) :
    CounterForger (BitString n) (BitString n) where
  Coins := Unit
  coins := PMF.pure ()
  forge _ := pure (0, (0, 0))

-- Concrete `IsOraclePPT` admissibility check for `prfMultiPadDistinguisher` with `twoSlotNonce`.
example :
    IsOraclePPT Turing.MultiTapeTM.encBool
      (prfMultiPadDistinguisher (fun _ => 2) twoSlotNonce (fun _ _ => pure false)) :=
  isOraclePPT_prfMultiPadDistinguisher (by polytime) (by unfold twoSlotNonce; polytime) (by ppt)

-- End-to-end check of `PseudorandomFunction.negligible_prfCounterGame` with `twoSlotNonce`,
-- exercising `hforger`, `hnonce_len`, `hnonce_inj`, `htest_eval`, `hQ`, `hnonce`, and `htest_ppt`.
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    {ε : ℕ → NNReal}
    (hh : ∀ n, IsDeltaUniversalHash
      (PMF.uniformOfFintype (Fin n → BitString n)) (BitString.LinearHash.hash (n := n) (m := n))
      (ε n))
    (hε : Negligible ε) :
    Negligible (fun n =>
      Game.succProbability
        (prfCounterGame (PMF.uniformOfFintype (Fin n → BitString n)) family n (twoSlotNonce n)
          BitString.LinearHash.hash (zeroQueryCounterForger n))) := by
  refine hprf.negligible_prfCounterGame hh hε (Q := fun _ => 2) (nonce := twoSlotNonce)
    zeroQueryCounterForger
    (Filter.Eventually.of_forall fun _ _ => .pure _ _)
    ?_ ?_ (fun _ _ => pure false) ?_
    (by polytime) (by unfold twoSlotNonce; polytime) (by ppt)
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn i _
    simp [twoSlotNonce]
    omega
  · filter_upwards [Filter.eventually_ge_atTop 1] with n _ i hi j hj heq
    have hhead : decide (i = 1) = decide (j = 1) := List.cons.inj heq |>.1
    by_cases hi1 : i = 1 <;> by_cases hj1 : j = 1 <;> simp_all
    omega
  · intro n padSeq
    simp [counterPadSeqDistinguisher, zeroQueryCounterForger, checkCounterSlot]

-- Concrete `checkNonceSUF` and `checkRandomNonceSUF` checks over `ZMod 7`:
-- issued nonce `0` with `m₀ = [2, 4]`, `t₀ = 5`, pad function `fun x => if x = 0 then 4 else 1`.
-- Unissued nonce `1` with `m' = [2, 4]` and `t' = xpolyHash 3 [2, 4] + 1 = 1 + 1 = 2` is accepted
-- by `checkNonceSUF` and `checkRandomNonceSUF`.
example :
    checkNonceSUF (xpolyHash (F := ZMod 7)) 3 (fun x : ZMod 7 => if x = 0 then 4 else 1)
      [((([2, 4], 0), 5))] (([2, 4], 1), 2) = true := by decide

-- Repeated nonce in transcript (`0` used twice) is rejected by `checkNonceSUF`.
example :
    checkNonceSUF (xpolyHash (F := ZMod 7)) 3 (fun _ : ZMod 7 => 4)
      [((([2, 4], 0), 5)), ((([1], 0), 0))] (([2, 4], 1), 5) = false := by decide

example :
    checkRandomNonceSUF (xpolyHash (F := ZMod 7)) 3 (fun x : ZMod 7 => if x = 0 then 4 else 1)
      [((([2, 4], 0), 5))] (([2, 4], 1), 2) = true := by decide

/-- Concrete two-query adaptive nonce-based forger over `ZMod 7` messages of length at most `2`:
queries `(m₀ = [1, 2], x₀ = 0)` (receiving `t₀`), queries `(m₁ = [2, 1], x₁ = 1)` (receiving `t₁`),
and outputs a forgery attempt `(([0, 3], 2), t₀ + t₁)` at an unissued nonce `x' = 2`. -/
noncomputable def sampleNonceForger :
    NonceForger {m : List (ZMod 7) // m.length ≤ 2} (ZMod 7) (ZMod 7) where
  Coins := Unit
  coins := PMF.pure ()
  forge _ := do
    let t₀ ← OracleComp.query
      (spec := fun _ : {m : List (ZMod 7) // m.length ≤ 2} × ZMod 7 => ZMod 7)
      (⟨[1, 2], by decide⟩, 0)
    let t₁ ← OracleComp.query
      (spec := fun _ : {m : List (ZMod 7) // m.length ≤ 2} × ZMod 7 => ZMod 7)
      (⟨[2, 1], by decide⟩, 1)
    return ((⟨[0, 3], by decide⟩, 2), t₀ + t₁)

-- Concrete instantiation of two-query adaptive nonce-based Carter–Wegman security over `ZMod 7`
-- (`ℓ = 2`): forgery probability (even at an unissued nonce `x' = 2`) is at most `3 / 7`.
example :
    nonceStrongGame (PMF.uniformOfFintype (ZMod 7))
      (fun k (m : {m : List (ZMod 7) // m.length ≤ 2}) => xpolyHash k m)
      sampleNonceForger true ≤ (2 + 1) / Fintype.card (ZMod 7) ∧
    nonceGame (PMF.uniformOfFintype (ZMod 7))
      (fun k (m : {m : List (ZMod 7) // m.length ≤ 2}) => xpolyHash k m)
      sampleNonceForger true ≤ (2 + 1) / Fintype.card (ZMod 7) :=
  ⟨nonceStrongGame_xpolyHash_le 2 sampleNonceForger,
   nonceGame_xpolyHash_le 2 sampleNonceForger⟩

/-- Concrete two-query adaptive randomized Carter–Wegman forger over `ZMod 7` messages of length at
most `2`: queries `m₀ = [1, 2]` (receiving `(x₀, t₀)`), queries `m₁ = [2, 1]` (receiving
`(x₁, t₁)`), and outputs `(([0, 3], x₀), t₀ + t₁)`. -/
noncomputable def sampleRandomNonceForger :
    RandomNonceForger {m : List (ZMod 7) // m.length ≤ 2} (ZMod 7) (ZMod 7) where
  Coins := Unit
  coins := PMF.pure ()
  forge _ := do
    let p₀ ← OracleComp.query
      (spec := fun _ : {m : List (ZMod 7) // m.length ≤ 2} => ZMod 7 × ZMod 7)
      ⟨[1, 2], by decide⟩
    let p₁ ← OracleComp.query
      (spec := fun _ : {m : List (ZMod 7) // m.length ≤ 2} => ZMod 7 × ZMod 7)
      ⟨[2, 1], by decide⟩
    return ((⟨[0, 3], by decide⟩, p₀.1), p₀.2 + p₁.2)

theorem isQueryBounded_sampleRandomNonceForger (s : sampleRandomNonceForger.Coins) :
    (sampleRandomNonceForger.forge s).IsQueryBounded 2 :=
  .liftBind _ _ 1 fun _ => .liftBind _ _ 0 fun _ => .pure _ 0

-- Concrete instantiation of two-query adaptive randomized Carter–Wegman security over `ZMod 7`
-- (`ℓ = 2`, `Q = 2`): forgery probability is at most `2^2 / (2 * 7) + 1 / 7 + 3 / 7`.
example :
    randomNonceStrongGame (PMF.uniformOfFintype (ZMod 7))
      (fun k (m : {m : List (ZMod 7) // m.length ≤ 2}) => xpolyHash k m)
      sampleRandomNonceForger true ≤
      (2 : ℝ≥0∞) ^ 2 / (2 * Fintype.card (ZMod 7)) + (Fintype.card (ZMod 7) : ℝ≥0∞)⁻¹ +
        (2 + 1) / Fintype.card (ZMod 7) :=
  randomNonceStrongGame_xpolyHash_le 2 isQueryBounded_sampleRandomNonceForger

/-- Smoke-test nonce-based forger over `BitString n` that queries `(0, 0)` twice at the same
nonce `0` (so `Nodup` fails and `checkNonceSUF = false`, giving a trivial distinguisher
`nonceFnDistinguisher = fun _ => PMF.pure false`). -/
noncomputable def repeatedNonceForger (n : ℕ) :
    NonceForger (BitString n) (BitString n) (BitString n) where
  Coins := Unit
  coins := PMF.pure ()
  forge _ := do
    let _ ← OracleComp.query (0, 0)
    let t ← OracleComp.query (0, 0)
    return ((0, 0), t)

@[simp]
theorem nonceFnDistinguisher_repeatedNonceForger {K : Type} (seed : PMF K) (n : ℕ)
    (hash : K → BitString n → BitString n) :
    nonceFnDistinguisher seed hash (repeatedNonceForger n) = fun _ => PMF.pure false := by
  funext padFn
  simp only [nonceFnDistinguisher, repeatedNonceForger, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.pure_bind,
    OracleComp.run_interpret_bind, OracleComp.run_interpret_query, OracleComp.run_interpret_pure]
  simp [nonceFnHandler, checkNonceSUF]

-- Smoke test of `PseudorandomFunction.negligible_prfNonceStrongGame`: instantiates the asymptotic
-- wrapper theorem on the trivial always-losing forger `repeatedNonceForger` matched against a
-- constant-`false` `prfPadDistinguisher`.
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    {ε : ℕ → NNReal}
    (hh : ∀ n, IsDeltaUniversalHash
      (PMF.uniformOfFintype (Fin n → BitString n)) (BitString.LinearHash.hash (n := n) (m := n))
      (ε n))
    (hε : Negligible ε) :
    Negligible (fun n =>
      Game.succProbability
        (prfNonceStrongGame (PMF.uniformOfFintype (Fin n → BitString n)) family n
          BitString.LinearHash.hash (repeatedNonceForger n))) := by
  refine hprf.negligible_prfNonceStrongGame hh hε repeatedNonceForger
    (prfPadDistinguisher (fun _ _ => pure false)) (isOraclePPT_prfPadDistinguisher (by ppt))
    (Filter.Eventually.of_forall fun n => ?_)
    (Filter.Eventually.of_forall fun n => ?_)
  · rw [eval_prfRealGame_prfPadDistinguisher]
    simp
  · rw [eval_prfIdealGame_prfPadDistinguisher]
    simp

/-- Smoke-test single-query randomized forger over `BitString n` that queries `0`, receives
`(x, t)`, and echoes the issued pair `((0, x), t)` (so `!tr.contains out = false` and
`checkRandomNonceSUF = false`, giving a trivial distinguisher
`randomNonceFnDistinguisher = fun _ => PMF.pure false`). -/
noncomputable def echoRandomNonceForger (n : ℕ) :
    RandomNonceForger (BitString n) (BitString n) (BitString n) where
  Coins := Unit
  coins := PMF.pure ()
  forge _ := do
    let p ← OracleComp.query 0
    return ((0, p.1), p.2)

@[simp]
theorem randomNonceFnDistinguisher_echoRandomNonceForger {K : Type} (seed : PMF K) (n : ℕ)
    (hash : K → BitString n → BitString n) :
    randomNonceFnDistinguisher seed hash (echoRandomNonceForger n) = fun _ => PMF.pure false := by
  funext padFn
  simp only [randomNonceFnDistinguisher, echoRandomNonceForger, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.pure_bind,
    OracleComp.run_interpret_bind, OracleComp.run_interpret_query, OracleComp.run_interpret_pure]
  simp [randomNonceFnHandler, checkRandomNonceSUF, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]

-- Smoke test of `PseudorandomFunction.negligible_prfRandomNonceStrongGame`: instantiates the
-- asymptotic wrapper theorem on the trivial always-losing forger `echoRandomNonceForger` matched
-- against a constant-`false` `prfPadDistinguisher`.
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    {ε : ℕ → NNReal}
    (hh : ∀ n, IsDeltaUniversalHash
      (PMF.uniformOfFintype (Fin n → BitString n)) (BitString.LinearHash.hash (n := n) (m := n))
      (ε n))
    (hε : Negligible ε) :
    Negligible (fun n =>
      Game.succProbability
        (prfRandomNonceStrongGame (PMF.uniformOfFintype (Fin n → BitString n)) family n
          BitString.LinearHash.hash (echoRandomNonceForger n))) := by
  refine hprf.negligible_prfRandomNonceStrongGame hh hε (Q := fun _ => 1)
    (PolynomiallyBounded.const 1) echoRandomNonceForger
    (Filter.Eventually.of_forall fun _ _ => .liftBind _ _ 0 fun _ => .pure _ 0)
    (prfPadDistinguisher (fun _ _ => pure false)) (isOraclePPT_prfPadDistinguisher (by ppt))
    (Filter.Eventually.of_forall fun n => ?_)
    (Filter.Eventually.of_forall fun n => ?_)
  · rw [eval_prfRealGame_prfPadDistinguisher]
    simp
  · rw [eval_prfIdealGame_prfPadDistinguisher]
    simp

/-! ### Computational `NonceMACScheme` and `MACScheme` Carter–Wegman tests -/

/-- Identity schedule `id : ℕ → ℕ` is computable in plain polynomial time in unary. -/
theorem computableInPolyTime_id : ComputableInPolyTime (id : ℕ → ℕ) encUnary encUnary := by
  polytime

/-- Two-query adaptive `NonceMACForger` that queries `0^n` at nonce `0^n` (receiving `t₀`),
then queries `1^n` at nonce `true :: 0^(n-1)` (receiving `t₁`), and outputs a candidate forgery
`((0^n, true :: 0^(n-1)), BitString.listXor n [t₀, t₁])`. -/
def twoQueryNonceMACForger : NonceMACForger :=
  fun n _ => do
    let t₀ ← List.take n <$>
      ProbOracleComp.query
        ((), encPair encBits encBits (List.replicate n false, List.replicate n false))
    let t₁ ← List.take n <$>
      ProbOracleComp.query
        ((), encPair encBits encBits
          (List.replicate n true, true :: List.replicate (n - 1) false))
    return ((List.replicate n false, true :: List.replicate (n - 1) false),
      BitString.listXor n [t₀, t₁])

/-- `twoQueryNonceMACForger` is uniformly strict oracle-PPT. -/
theorem isOraclePPT_twoQueryNonceMACForger :
    IsOraclePPT (encPair (encPair encBits encBits) encBits) twoQueryNonceMACForger := by
  have hq0 : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun p : ℕ × List Bool =>
        List.take p.1 <$>
          ProbOracleComp.query
            ((), encPair encBits encBits (List.replicate p.1 false, List.replicate p.1 false))) :=
    IsOraclePPTOn.query_take () (by polytime) (by polytime)
  have hq1 : IsOraclePPTOn (encPair (encPair encUnary encBits) encBits) encBits
      (fun q : (ℕ × List Bool) × List Bool =>
        List.take q.1.1 <$>
          ProbOracleComp.query
            ((), encPair encBits encBits
              (List.replicate q.1.1 true, true :: List.replicate (q.1.1 - 1) false))) :=
    IsOraclePPTOn.query_take () (by polytime) (by polytime)
  have hstep1 := hq1.map_with
    (output := encPair (encPair encBits encBits) encBits)
    (f := fun (q : (ℕ × List Bool) × List Bool) t₁ =>
      ((List.replicate q.1.1 false, true :: List.replicate (q.1.1 - 1) false),
        BitString.listXor q.1.1 [q.2, t₁]))
    (by polytime)
  unfold twoQueryNonceMACForger
  exact (hq0.bind_with hstep1).isOraclePPT

-- Concrete `IsOraclePPT` admissibility check for `prfNonceToPrfDistinguisher` on the two-query
-- adaptive `NonceMACForger` and `BitString.LinearHash.wordHash`.
example :
    IsOraclePPT encBool
      (prfNonceToPrfDistinguisher id
        (fun n => BitString.sampleList (n * id n))
        BitString.LinearHash.wordHash
        twoQueryNonceMACForger) :=
  isOraclePPT_prfNonceToPrfDistinguisher
    computableInPolyTime_id
    (isPPTOn_linearHashSeed computableInPolyTime_id)
    computableInPolyTime_linearHashWordHash
    isOraclePPT_twoQueryNonceMACForger

-- End-to-end asymptotic `NonceMACScheme.SUFCMA` and `NonceMACScheme.EUFCMA` checks for
-- `linearHashNonceMAC`, plus quantitative SUF-CMA bound instantiated on `twoQueryNonceMACForger`.
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    (linearHashNonceMAC id family computableInPolyTime_id hprf.polyTime).SUFCMA ∧
    (linearHashNonceMAC id family computableInPolyTime_id hprf.polyTime).EUFCMA :=
  ⟨hprf.sufCma_linearHashNonceMAC computableInPolyTime_id,
   hprf.eufCma_linearHashNonceMAC computableInPolyTime_id⟩

example {family : List Bool → List Bool → List Bool}
    (hfamily : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) (n : ℕ) :
    (ProbComp.eval
      ((linearHashNonceMAC id family computableInPolyTime_id hfamily).sufCmaGame
        twoQueryNonceMACForger n) true).toReal ≤
      ((2 : ℝ) ^ n)⁻¹ + ((2 : ℝ) ^ n)⁻¹ +
        (Game.advantage
          (ProbComp.eval
            (prfRealGame family
              (prfNonceToPrfDistinguisher id (fun k => BitString.sampleList (k * id k))
                BitString.LinearHash.wordHash twoQueryNonceMACForger) n))
          (ProbComp.eval
            (prfIdealGame
              (prfNonceToPrfDistinguisher id (fun k => BitString.sampleList (k * id k))
                BitString.LinearHash.wordHash twoQueryNonceMACForger) n)) : ℝ) :=
  sufCmaGame_linearHashNonceMAC_toReal_le
    computableInPolyTime_id hfamily n twoQueryNonceMACForger

/-- Two-query adaptive `Forger` for randomized Carter–Wegman (`MACScheme`): queries `0^n`
(receiving encoded `(nonce₀, tag₀)` of length at most `2 * n + 2`), queries `1^n` (receiving
encoded `(nonce₁, tag₁)`), and outputs `(0^n, raw₁)` as its candidate forgery. -/
def twoQueryRandomMACForger : Forger :=
  fun n _ => do
    let _ ← List.take (2 * n + 2) <$>
      ProbOracleComp.query ((), List.replicate n false)
    let raw₁ ← List.take (2 * n + 2) <$>
      ProbOracleComp.query ((), List.replicate n true)
    return (List.replicate n false, raw₁)

/-- `twoQueryRandomMACForger` is uniformly strict oracle-PPT. -/
theorem isOraclePPT_twoQueryRandomMACForger :
    IsOraclePPT (encPair encBits encBits) twoQueryRandomMACForger := by
  have hq0 : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun p : ℕ × List Bool =>
        List.take (2 * p.1 + 2) <$>
          ProbOracleComp.query ((), List.replicate p.1 false)) :=
    IsOraclePPTOn.query_take () (by polytime) (by polytime)
  have hq1 : IsOraclePPTOn (encPair (encPair encUnary encBits) encBits) encBits
      (fun q : (ℕ × List Bool) × List Bool =>
        List.take (2 * q.1.1 + 2) <$>
          ProbOracleComp.query ((), List.replicate q.1.1 true)) :=
    IsOraclePPTOn.query_take () (by polytime) (by polytime)
  have hstep1 := hq1.map_with
    (output := encPair encBits encBits)
    (f := fun (q : (ℕ × List Bool) × List Bool) raw₁ =>
      (List.replicate q.1.1 false, raw₁))
    (by polytime)
  unfold twoQueryRandomMACForger
  exact (hq0.bind_with hstep1).isOraclePPT

/-- `twoQueryRandomMACForger` makes at most `2` signing queries. -/
theorem isQueryBounded_twoQueryRandomMACForger (k : ℕ) :
    (twoQueryRandomMACForger k []).IsQueryBounded 2 := by
  unfold twoQueryRandomMACForger
  refine OracleComp.IsCostBounded.bind (n := 1) (m := 1) ?_ fun _ => ?_
  · rw [OracleComp.isCostBounded_map_iff]
    exact ProbOracleComp.IsQueryBounded.query ((), List.replicate k false)
  · refine OracleComp.IsCostBounded.bind (n := 1) (m := 0) ?_ fun _ => ?_
    · rw [OracleComp.isCostBounded_map_iff]
      exact ProbOracleComp.IsQueryBounded.query ((), List.replicate k true)
    · exact OracleComp.IsCostBounded.pure _ 0

-- Concrete `IsOraclePPT` admissibility check for `prfRandomNonceToPrfDistinguisher` on the
-- two-query adaptive `Forger` and `BitString.LinearHash.wordHash`.
example :
    IsOraclePPT encBool
      (prfRandomNonceToPrfDistinguisher id
        (fun n => BitString.sampleList (n * id n))
        BitString.LinearHash.wordHash
        twoQueryRandomMACForger) :=
  isOraclePPT_prfRandomNonceToPrfDistinguisher
    computableInPolyTime_id
    (isPPTOn_linearHashSeed computableInPolyTime_id)
    computableInPolyTime_linearHashWordHash
    isOraclePPT_twoQueryRandomMACForger

-- End-to-end asymptotic `MACScheme.SUFCMA`, `MACScheme.EUFCMA`, and `MACScheme.OneTimeEUFCMA`
-- checks for `linearHashRandomMAC`, plus quantitative SUF-CMA bound instantiated on
-- `twoQueryRandomMACForger`.
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    (linearHashRandomMAC id family computableInPolyTime_id hprf.polyTime).SUFCMA ∧
    (linearHashRandomMAC id family computableInPolyTime_id hprf.polyTime).EUFCMA ∧
    (linearHashRandomMAC id family computableInPolyTime_id hprf.polyTime).OneTimeEUFCMA :=
  ⟨hprf.sufCma_linearHashRandomMAC computableInPolyTime_id,
   hprf.eufCma_linearHashRandomMAC computableInPolyTime_id,
   hprf.oneTimeEUFCMA_linearHashRandomMAC computableInPolyTime_id⟩

example {family : List Bool → List Bool → List Bool}
    (hfamily : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) (n : ℕ) :
    (ProbComp.eval
      ((linearHashRandomMAC id family computableInPolyTime_id hfamily).sufCmaGame
        twoQueryRandomMACForger n) true).toReal ≤
      (2 : ℝ) ^ 2 / (2 * (2 : ℝ) ^ n) + ((2 : ℝ) ^ n)⁻¹ + ((2 : ℝ) ^ n)⁻¹ +
        (Game.advantage
          (ProbComp.eval
            (prfRealGame family
              (prfRandomNonceToPrfDistinguisher id
                (fun k => BitString.sampleList (k * id k))
                BitString.LinearHash.wordHash twoQueryRandomMACForger) n))
          (ProbComp.eval
            (prfIdealGame
              (prfRandomNonceToPrfDistinguisher id
                (fun k => BitString.sampleList (k * id k))
                BitString.LinearHash.wordHash twoQueryRandomMACForger) n)) : ℝ) :=
  sufCmaGame_linearHashRandomMAC_toReal_le
    computableInPolyTime_id hfamily (isQueryBounded_twoQueryRandomMACForger n)

end ComplexityTests.Crypto.CarterWegman

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.DiffieHellman
import Complexity.Crypto.Computational.Encryption.CCA
import Complexity.Crypto.Computational.PseudorandomFunction
import Complexity.Probability.Product
import Complexity.Crypto.Negligible.Basic
import Complexity.Tactic.PPT

/-!
# The group, encryption and pseudorandom-function assumptions are not vacuous

Each security definition below fails for an obviously insecure instance, so none of them holds
for every candidate. The negative instances for one-way functions, symmetric IND-CPA,
pseudorandom generators and hard-core predicates are elsewhere.

* **Discrete logarithm, CDH and DDH.** For every prime-order group family `F` and every fixed
  description `d`, the constant setup `fun _ => PMF.pure d` satisfies none of `F.DiscreteLog`,
  `F.CDH` and `F.DDH`. Guessing the exponent `0` solves the discrete logarithm with probability
  `1 / q`. Testing whether the first and third elements are both the identity has advantage
  `1 / q - 1 / q²` against DDH. These are constant because the group does not grow with the
  security parameter.
* **IND-CPA and IND-CCA2.** Sending the plaintext bit as the ciphertext is neither `INDCPA` nor
  `INDCCA2`: copying the ciphertext guesses the challenge bit with advantage `1`.
* **Pseudorandom functions.** The family answering every query with zeros has answers of the
  declared width but is not a `PseudorandomFunction`: asking for the first answer bit at the zero
  word has advantage `1 / 2` at every positive parameter.
-/

namespace ComplexityTests.Crypto.AssumptionNonvacuity

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM
open scoped NNReal ENNReal

variable (F : PrimeOrderGroupFamily) (d : F.Desc)

/-! ### Discrete logarithm and CDH -/

/-- Always guess the exponent `0`. -/
noncomputable def guessZero : ℕ → F.Desc × List Bool → ProbComp (List Bool) :=
  fun _ _ => pure []

theorem guessZero_isPPT : IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) encBits
    (fun input => guessZero F input.1 input.2) :=
  (ComputableInPolyTime.const _).isPPTOn

/-- A uniform element of a group of order `q` is a given one with probability `1 / q`. -/
theorem uniform_eq_apply (α₀ : ZMod (F.order d)) :
    (do let α ← PMF.uniformOfFintype (ZMod (F.order d)); return decide (α₀ = α) : PMF Bool) true =
      (F.order d : ℝ≥0∞)⁻¹ := by
  rw [PMF.monad_bind_eq_bind, PMF.bind_apply, tsum_fintype]
  simp [PMF.uniformOfFintype_apply, PMF.pure_apply]

/-- Guessing `0` against a fixed group of order `q` succeeds with probability exactly `1 / q`. -/
theorem succProbability_discreteLogGame_guessZero (n : ℕ) :
    Game.succProbability (F.discreteLogGame (fun _ => PMF.pure d) (guessZero F) n) =
      (F.order d : ℝ≥0)⁻¹ := by
  have h := uniform_eq_apply F d 0
  simp only [discreteLogGame, guessZero, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.pure_bind] at h ⊢
  simp only [ofBits, List.foldr_nil, Nat.cast_zero]
  rw [Game.succProbability, h, ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast]

/-- **The discrete-logarithm assumption fails for a fixed group.** -/
theorem not_discreteLog_const : ¬ F.DiscreteLog fun _ => PMF.pure d := by
  intro h
  have hneg := h (guessZero F) (guessZero_isPPT F)
  simp only [succProbability_discreteLogGame_guessZero] at hneg
  exact not_negligible_const (inv_ne_zero (Nat.cast_ne_zero.mpr (F.prime_order d).ne_zero)) hneg

/-- **CDH fails for a fixed group**, since it implies the discrete-logarithm assumption. -/
theorem not_cdh_const : ¬ F.CDH fun _ => PMF.pure d :=
  fun h => not_discreteLog_const F d h.discreteLog

/-! ### DDH -/

/-- Accept when the first and third elements are both the identity of the fixed group `d`. -/
noncomputable def identityTest :
    ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool :=
  fun _ input => pure (decide (input.2.1 = F.encode d 0 ∧ input.2.2.2 = F.encode d 0))

theorem identityTest_isPPT :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => identityTest F d input.1 input.2) := by
  unfold identityTest
  ppt

/-- An encoded multiple of the generator is the identity exactly for the exponent `0`. -/
theorem encode_smul_eq_zero_iff (α : ZMod (F.order d)) :
    F.encode d (α • F.generator d) = F.encode d 0 ↔ α = 0 := by
  rw [(F.encode_injective d).eq_iff, ← zero_smul (ZMod (F.order d)) (F.generator d),
    (F.smul_generator_injective d).eq_iff]

/-- In the real game, the test succeeds exactly when `α = 0`, with probability `1 / q`. -/
theorem succProbability_ddhRealGame_identityTest (n : ℕ) :
    Game.succProbability (F.ddhRealGame (fun _ => PMF.pure d) (identityTest F d) n) =
      (F.order d : ℝ≥0)⁻¹ := by
  have h := uniform_eq_apply F d 0
  simp only [ddhRealGame, identityTest, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.pure_bind, encode_smul_eq_zero_iff, mul_eq_zero] at h ⊢
  simp only [and_or_left, and_self, or_iff_left_of_imp And.left, PMF.bind_const,
    eq_comm (a := (0 : ZMod _))] at h ⊢
  rw [Game.succProbability, h, ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast]

/-- In the ideal game, the test succeeds exactly when `α = γ = 0`, with probability `1 / q²`. -/
theorem succProbability_ddhIdealGame_identityTest (n : ℕ) :
    Game.succProbability (F.ddhIdealGame (fun _ => PMF.pure d) (identityTest F d) n) =
      (F.order d : ℝ≥0)⁻¹ ^ 2 := by
  simp only [ddhIdealGame, identityTest, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
    PMF.pure_bind, encode_smul_eq_zero_iff, PMF.bind_const]
  rw [Game.succProbability, ← ENNReal.toNNReal_natCast, ← ENNReal.toNNReal_inv,
    ← ENNReal.toNNReal_pow]
  congr 1
  simp [PMF.bind_apply, tsum_fintype, PMF.uniformOfFintype_apply, PMF.pure_apply, ite_and,
    Finset.sum_ite_eq', sq]

/-- **DDH fails for a fixed group.** -/
theorem not_ddh_const : ¬ F.DDH fun _ => PMF.pure d := by
  intro h
  have hneg := h (identityTest F d) (identityTest_isPPT F d)
  simp only [Game.advantage, succProbability_ddhRealGame_identityTest,
    succProbability_ddhIdealGame_identityTest] at hneg
  refine not_negligible_const ?_ hneg
  rw [ne_eq, nndist_eq_zero]
  intro heq
  have hq : (2 : ℝ) ≤ F.order d := by exact_mod_cast (F.prime_order d).two_le
  have hr : ((F.order d : ℝ))⁻¹ = ((F.order d : ℝ))⁻¹ ^ 2 := by
    simpa using congrArg (fun x : ℝ≥0 => (x : ℝ)) heq
  field_simp at hr
  nlinarith

/-! ### IND-CPA and IND-CCA2 -/

/-- The empty key pair. -/
noncomputable def emptyKeys : ℕ → ProbComp (List Bool × List Bool) := fun _ => pure ([], [])

/-- Send the plaintext bit as the ciphertext. -/
noncomputable def plaintext : ℕ → List Bool → Bool → ProbComp (List Bool) := fun _ _ b => pure [b]

/-- Challenge with `false` and `true`, and output the ciphertext's bit. -/
noncomputable def copyCiphertext : Encryption.Adversary where
  choose _ _ := pure ((false, true), [])
  guess _ _ c := pure (c.headD false)

theorem copyCiphertext_isPPT : copyCiphertext.IsPPT where
  choose := (ComputableInPolyTime.const _).isPPTOn
  guess := by
    unfold copyCiphertext
    ppt

/-- Copying the ciphertext recovers the challenge bit. -/
theorem eval_game_copyCiphertext (bit : Bool) (n : ℕ) :
    ProbComp.eval (Encryption.game emptyKeys plaintext copyCiphertext bit n) = PMF.pure bit := by
  cases bit <;>
    simp [Encryption.game, Encryption.gameOn, emptyKeys, plaintext, copyCiphertext]

/-- **Sending the plaintext is not IND-CPA.** -/
theorem not_indcpa_plaintext : ¬ Encryption.INDCPA emptyKeys plaintext := by
  intro h
  have hneg := h copyCiphertext copyCiphertext_isPPT
  simp only [eval_game_copyCiphertext] at hneg
  refine not_negligible_const ?_ hneg
  simp [Game.advantage, Game.succProbability]

/-- **Sending the plaintext is not IND-CCA2**, for any decryption, since IND-CCA2 implies
IND-CPA. -/
theorem not_indcca2_plaintext (decrypt : ℕ → List Bool → List Bool → Option Bool) :
    ¬ Encryption.INDCCA2 emptyKeys plaintext decrypt :=
  fun h => not_indcpa_plaintext h.indcpa

/-! ### Pseudorandom functions -/

/-- The all-zero family: every query gets the zero word of its own length. -/
def zeroFamily : List Bool → List Bool → List Bool :=
  fun _ query => List.replicate query.length false

/-- Query the zero word and accept when the first answer bit is `false`. -/
noncomputable def firstBitZero : OracleDistinguisher := fun n _ => do
  let reply ← List.take n <$> ProbOracleComp.query ((), List.replicate n false)
  return !(reply.headD true)

theorem firstBitZero_isOraclePPT : IsOraclePPT encBool firstBitZero := by
  have hq : ComputableInPolyTime (fun p : ℕ × List Bool => List.replicate p.1 false)
      (encPair encUnary encBits) encBits := by
    polytime
  have hlim : ComputableInPolyTime (fun p : ℕ × List Bool => p.1)
      (encPair encUnary encBits) encUnary := by
    fun_prop
  have hout : ComputableInPolyTime (fun p : (ℕ × List Bool) × List Bool => !(p.2.headD true))
      (encPair (encPair encUnary encBits) encBits) encBool := by
    polytime
  unfold firstBitZero
  exact ((IsOraclePPTOn.query_take' () hq hlim).bind_with hout.isOraclePPTOn).isOraclePPT

theorem eval_prfRealGame_firstBitZero (n : ℕ) :
    ProbComp.eval (prfRealGame zeroFamily firstBitZero (n + 1)) = PMF.pure true := by
  simp only [prfRealGame, firstBitZero, zeroFamily, prfOracle, List.replicate_succ,
    List.headD_eq_head?_getD, bind_pure_comp, Functor.map_map, OracleComp.interpret_map,
    ProbOracleComp.interpret_query, List.length_cons, List.length_replicate, ↓reduceIte, map_pure,
    ProbComp.eval_map, BitString.eval_sampleList]
  exact PMF.map_const _ _

theorem eval_prfIdealGame_firstBitZero (n : ℕ) :
    ProbComp.eval (prfIdealGame firstBitZero (n + 1)) = PMF.uniformOfFintype Bool := by
  simp only [prfIdealGame, firstBitZero, randomFunctionOracle, List.ofFn_succ,
    List.headD_eq_head?_getD, bind_pure_comp, Functor.map_map, OracleComp.interpret_map,
    ProbOracleComp.interpret_query, List.length_replicate, ↓reduceIte, map_pure,
    List.take_succ_cons, List.head?_cons, Option.getD_some, ProbComp.eval_map,
    ProbComp.eval_uniform]
  have h1 : (PMF.uniformOfFintype (BitString (n + 1) → BitString (n + 1))).map
      (fun table => table (BitString.ofList (n + 1) (List.replicate (n + 1) false))) =
        PMF.uniformOfFintype (BitString (n + 1)) := by
    rw [← Cslib.Probability.PMF.pi_uniformOfFintype, Cslib.Probability.PMF.pi_map_eval]
  have h2 : (PMF.uniformOfFintype (BitString (n + 1))).map (fun word => word 0) =
      PMF.uniformOfFintype Bool := by
    rw [← Cslib.Probability.PMF.pi_uniformOfFintype, Cslib.Probability.PMF.pi_map_eval]
  have h3 : (PMF.uniformOfFintype Bool).map Bool.not = PMF.uniformOfFintype Bool := by
    ext b
    cases b <;> simp [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply]
  rw [← h3, ← h2, ← h1, PMF.map_comp, PMF.map_comp]
  rfl

/-- **The all-zero family is not a pseudorandom function**: at every positive parameter the real
experiment always accepts and the ideal one accepts with probability `1 / 2`. -/
theorem not_pseudorandomFunction_zeroFamily : ¬ PseudorandomFunction zeroFamily := by
  intro h
  have hneg := h.secure firstBitZero firstBitZero_isOraclePPT
  have hshift : Negligible fun n => Game.advantage
      (ProbComp.eval (prfRealGame zeroFamily firstBitZero (n + 1)))
      (ProbComp.eval (prfIdealGame firstBitZero (n + 1))) :=
    hneg.comp_of_polynomial_bound (bound := fun m => m) (Filter.tendsto_add_atTop_nat 1)
      (by fun_prop) (Filter.Eventually.of_forall fun n => by lia)
  simp only [eval_prfRealGame_firstBitZero, eval_prfIdealGame_firstBitZero] at hshift
  refine not_negligible_const ?_ hshift
  norm_num [Game.advantage, Game.succProbability, PMF.uniformOfFintype_apply,
    ENNReal.toNNReal_ofNat]

end ComplexityTests.Crypto.AssumptionNonvacuity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Protocols.SigmaProtocol.Basic
import Complexity.Crypto.Computational.LWE.Basic
import Complexity.Crypto.Computational.Encryption.Authenticated
import Complexity.Crypto.Computational.OneWay
import Complexity.Crypto.Primitives.PRG.NextBit
import Complexity.Crypto.Negligible.Basic
import Complexity.Tactic.PPT

/-!
# Σ-protocol, LWE, IND-CCA, one-way-permutation and next-bit definitions are not vacuous

Each definition below fails for an obviously insecure instance, so none of them holds for every
candidate.

* **Special soundness.** The protocol that accepts every conversation is not special sound for a
  relation with a statement that has no witness: two accepting conversations on that statement
  exist, and no extractor can return a witness for it.
* **Special honest-verifier zero knowledge.** The protocol whose commitment is the witness has no
  simulator for a statement with two witnesses: the simulator would have to reproduce both honest
  transcripts, which differ.
* **Decision LWE.** With no secret coordinates and zero noise, a real sample is the zero residue,
  while a uniform residue modulo `2` is zero half of the time. Testing whether the first bit is
  `false` has advantage `1 / 2`.
* **Symmetric IND-CCA.** No symmetric cipher without ciphertext expansion is `INDCCA`: the two
  encryption queries of `detCPAAdversary`, sent through the CCA oracle's encryption channel, have
  advantage `1` (`not_indcca_of_ciphertext_length_eq`). Sending the plaintext is such a cipher.
  The library has no symmetric CCA-implies-CPA lemma to derive this from
  `SymmetricCipher.not_indcpa_of_ciphertext_length_eq`.
* **One-way permutations.** Flipping every bit preserves lengths and is a bijection, but flipping
  again inverts it, so it is not a `OneWayPermutation`.
* **Next-bit unpredictability.** The one-bit generator that always outputs `false` is predicted
  with probability `1` by guessing `false`, so it is not `Generator.Unpredictable` at any error
  below `1 / 2`.
-/

namespace ComplexityTests.Crypto.SigmaLWECCANonvacuity

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Special soundness -/

/-- The protocol with one-bit witnesses, statements, commitments and challenges that accepts every
conversation. -/
noncomputable def acceptAll : SigmaProtocol Bool Bool Unit Bool Unit where
  State := Unit
  commit _ _ := PMF.pure ((), ())
  respond _ _ _ _ := ()
  verify _ _ _ _ := true

/-- The statement `y` has a witness exactly when `y = true`. -/
def trueOnly (_ : Bool) (y : Bool) : Prop := y = true

/-- **Accepting every conversation is not special sound** for `trueOnly`: on the statement
`false`, which has no witness, the conversations with challenges `false` and `true` both
accept. -/
theorem not_specialSoundness_acceptAll (extract : Bool → Unit → Bool → Unit → Bool → Unit → Bool) :
    ¬ acceptAll.SpecialSoundness trueOnly extract := by
  intro h
  have := h false () false () true () Bool.false_ne_true rfl rfl
  exact Bool.false_ne_true this

/-- The accepting-everything protocol is still complete, so special soundness is what fails. -/
example : acceptAll.Complete trueOnly := fun _ _ _ _ _ _ => rfl

/-! ### Special honest-verifier zero knowledge -/

/-- The protocol whose commitment is the witness. -/
noncomputable def revealWitness : SigmaProtocol Bool Unit Bool Bool Unit where
  State := Unit
  commit x _ := PMF.pure (x, ())
  respond _ _ _ _ := ()
  verify _ _ _ _ := true

/-- **Revealing the witness is not special HVZK** for a statement with the two witnesses `false`
and `true`: a simulator at the challenge `false` would equal both honest transcripts, the point
masses at `(false, ())` and at `(true, ())`. -/
theorem not_specialHVZK_revealWitness (simulate : Unit → Bool → PMF (Bool × Unit)) :
    ¬ revealWitness.SpecialHVZK (fun _ _ => True) simulate := by
  intro h
  have h₀ := h.transcript_eq false () trivial false
  have h₁ := h.transcript_eq true () trivial false
  have heq : (PMF.pure (false, ()) : PMF (Bool × Unit)) = PMF.pure (true, ()) := by
    simpa [SigmaProtocol.transcript, revealWitness, PMF.pure_map] using h₀.symm.trans h₁
  have := congrArg (fun μ : PMF (Bool × Unit) => μ (false, ())) heq
  simp [PMF.pure_apply] at this

/-- The witness-revealing protocol is complete, so zero knowledge is what fails. -/
example : revealWitness.Complete (fun _ _ => True) := fun _ _ _ _ _ _ => rfl

/-! ### Decision LWE -/

/-- Zero noise for one-bit residues. -/
noncomputable def zeroNoise : (security : ℕ) → PMF (ZMod (2 ^ (fun _ : ℕ => 1) security)) :=
  fun _ => PMF.pure 0

/-- Accept exactly when the first bit is `false`. -/
def firstBitFalse : Distinguisher := fun _ word => pure (!(word.headD true))

theorem firstBitFalse_ppt : IsPPT encBool firstBitFalse := by
  unfold firstBitFalse
  ppt

/-- With no secret coordinates and zero noise, every real sample is the word of the zero
residue. -/
theorem eq_of_mem_support_realEnsemble {security : ℕ} {word : List Bool}
    (h : word ∈ (LWE.realEnsemble (fun _ => 0) (fun _ => 1) (fun _ => 1) zeroNoise
      security).support) : word = [false] := by
  obtain ⟨A, hA, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  simp only [LWE.publicMatrixLaw, zeroNoise, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hA
  obtain ⟨t, -, B, -, e, he, rfl⟩ := hA
  have he0 : e 0 = 0 := by
    exact (PMF.mem_support_pure_iff _ _).mp ((PMF.mem_support_pi_iff _ _).mp he 0)
  simp [Matrix.toBinary_eq, LWE.publicMatrix, Matrix.mulVec, dotProduct, he0]

/-- The real experiment accepts with probability `1`. -/
theorem distinguishingGame_realEnsemble (security : ℕ) :
    distinguishingGame (LWE.realEnsemble (fun _ => 0) (fun _ => 1) (fun _ => 1) zeroNoise
      security) (firstBitFalse security) = PMF.pure true := by
  unfold distinguishingGame
  rw [PMF.monad_bind_eq_bind]
  trans (LWE.realEnsemble (fun _ => 0) (fun _ => 1) (fun _ => 1) zeroNoise security).bind
    fun _ => PMF.pure true
  · refine PMF.bind_congr_on_support _ _ _ fun word hword => ?_
    rw [eq_of_mem_support_realEnsemble hword]
    simp [firstBitFalse]
  · exact PMF.bind_const _ _

/-- The uniform experiment accepts with probability `1 / 2`. -/
theorem distinguishingGame_uniformEnsemble_apply (security : ℕ) :
    distinguishingGame (LWE.uniformEnsemble (fun _ => 0) (fun _ => 1) (fun _ => 1) security)
      (firstBitFalse security) true = 2⁻¹ := by
  simp only [distinguishingGame, LWE.uniformEnsemble, firstBitFalse, PMF.monad_bind_eq_bind,
    PMF.bind_map, Function.comp_def, ProbComp.eval_pure, PMF.bind_apply, tsum_fintype,
    PMF.uniformOfFintype_apply, PMF.pure_apply]
  rw [← Finset.mul_sum]
  have hcard : Fintype.card (Matrix (Fin 1) (Fin (0 + 1)) (ZMod (2 ^ 1))) = 2 := by
    decide
  have hfilter : (Finset.univ.filter fun A : Matrix (Fin 1) (Fin (0 + 1)) (ZMod (2 ^ 1)) =>
      (Matrix.toBinary A).head?.getD true = false).card = 1 := by
    decide
  beta_reduce
  simp only [hcard]
  norm_num
  rw [hfilter]
  simp

/-- **Decision LWE fails without secret coordinates and noise**: testing the first bit has
advantage `1 / 2`. -/
theorem not_decisionLWE_zeroNoise :
    ¬ DecisionLWE (fun _ => 0) (fun _ => 1) (fun _ => 1) zeroNoise := by
  intro h
  have hneg := h firstBitFalse firstBitFalse_ppt
  have hadv (security : ℕ) : Game.advantage
      (distinguishingGame (LWE.realEnsemble (fun _ => 0) (fun _ => 1) (fun _ => 1) zeroNoise
        security) (firstBitFalse security))
      (distinguishingGame (LWE.uniformEnsemble (fun _ => 0) (fun _ => 1) (fun _ => 1) security)
        (firstBitFalse security)) = 2⁻¹ := by
    rw [Game.advantage, distinguishingGame_realEnsemble, Game.succProbability,
      Game.succProbability, distinguishingGame_uniformEnsemble_apply]
    rw [PMF.pure_apply_self, ENNReal.toNNReal_one, ENNReal.toNNReal_inv, ENNReal.toNNReal_ofNat]
    apply NNReal.eq
    rw [coe_nndist, NNReal.dist_eq]
    norm_num
  have hc : Negligible (fun _ : ℕ => (2⁻¹ : ℝ≥0)) := hneg.congr hadv
  exact not_negligible_const (by norm_num) hc

/-! ### Symmetric IND-CCA -/

namespace SymmetricCipher

open Cslib.Crypto.SymmetricCipher

/-- The two-query attack of `detCPAAdversary` through the encryption channel of the CCA oracle:
encrypt the pair `(0ⁿ, 1ⁿ)`, then `(0ⁿ, 0ⁿ)`, and report whether the answers agree. -/
def detCCAAdversary : CCAAdversary :=
  fun n _ => do
    let m0 := List.replicate n false
    let m1 := List.replicate n true
    let c₁ ← List.take n <$> ProbOracleComp.query (false, encPair encBits encBits (m0, m1))
    let c₂ ← List.take n <$> ProbOracleComp.query (false, encPair encBits encBits (m0, m0))
    return (c₁ == c₂)

theorem isOraclePPT_detCCAAdversary : IsOraclePPT encBool detCCAAdversary := by
  have hq1 : ComputableInPolyTime
      (fun p : ℕ × List Bool =>
        encPair encBits encBits (List.replicate p.1 false, List.replicate p.1 true))
      (encPair encUnary encBits) encBits := by
    polytime
  have hlim1 : ComputableInPolyTime
      (fun p : ℕ × List Bool => p.1) (encPair encUnary encBits) encUnary := by
    fun_prop
  have hq2 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool =>
        encPair encBits encBits (List.replicate p.1.1 false, List.replicate p.1.1 false))
      (encPair (encPair encUnary encBits) encBits) encBits := by
    polytime
  have hlim2 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => p.1.1)
      (encPair (encPair encUnary encBits) encBits) encUnary := by
    fun_prop
  have hout : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × List Bool => p.1.2 == p.2)
      (encPair (encPair (encPair encUnary encBits) encBits) encBits) encBool := by
    polytime
  unfold detCCAAdversary
  exact ((IsOraclePPTOn.query_take' false hq1 hlim1).bind_with
    ((IsOraclePPTOn.query_take' false hq2 hlim2).bind_with
      hout.isOraclePPTOn)).isOraclePPT

theorem unframe_dropFrame_pair (a b : List Bool) :
    unframe (encPair encBits encBits (a, b)) = a ∧
      dropFrame (encPair encBits encBits (a, b)) = b := by
  simp [encPair_apply, unframe_frame_append, dropFrame_frame_append]

/-- In Experiment `false`, both queries encrypt `0ⁿ`; without ciphertext expansion the answers
agree, so the adversary outputs `true`. -/
theorem eval_ccaGame_detCCAAdversary_false (E : SymmetricCipher) (n : ℕ)
    (hctLen : ∀ ke ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg : List Bool, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n) :
    ProbComp.eval (E.ccaGame detCCAAdversary false n) = PMF.pure true := by
  simp only [ccaGame, detCCAAdversary, OracleComp.interpret_bind, OracleComp.interpret_map,
    OracleComp.interpret_pure, ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map,
    StateT.run_pure, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
  have hpair1 := unframe_dropFrame_pair (List.replicate n false) (List.replicate n true)
  have hpair2 := unframe_dropFrame_pair (List.replicate n false) (List.replicate n false)
  trans (ProbComp.eval (E.keyGen n)).bind (fun _ => PMF.pure true)
  · refine PMF.bind_congr_on_support _ _ _ fun ke hke => ?_
    unfold ccaOracle
    dsimp only [StateT.run]
    simp only [hpair1.1, hpair1.2, hpair2.1, hpair2.2, List.length_replicate, beq_self_eq_true,
      Bool.and_self, ↓reduceIte, Bool.false_eq_true, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map, PMF.bind_bind, PMF.pure_bind]
    trans (ProbComp.eval (E.encrypt n ke (List.replicate n false))).bind (fun _ => PMF.pure true)
    · refine PMF.bind_congr_on_support _ _ _ fun c₁ hc₁ => ?_
      trans (ProbComp.eval (E.encrypt n ke (List.replicate n false))).bind (fun _ => PMF.pure true)
      · refine PMF.bind_congr_on_support _ _ _ fun c₂ hc₂ => ?_
        have heq : c₁ = c₂ :=
          E.encrypt_eq_of_ciphertext_length_eq hke (hctLen ke hke) (List.length_replicate) hc₁ hc₂
        simp [heq]
      · exact PMF.bind_const _ _
    · exact PMF.bind_const _ _
  · exact PMF.bind_const _ _

/-- In Experiment `true` with `n ≥ 1`, the queries encrypt `1ⁿ` and then `0ⁿ`; by correctness the
answers differ, so the adversary outputs `false`. -/
theorem eval_ccaGame_detCCAAdversary_true (E : SymmetricCipher) {n : ℕ} (hn : 1 ≤ n)
    (hctLen : ∀ ke ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg : List Bool, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n) :
    ProbComp.eval (E.ccaGame detCCAAdversary true n) = PMF.pure false := by
  simp only [ccaGame, detCCAAdversary, OracleComp.interpret_bind, OracleComp.interpret_map,
    OracleComp.interpret_pure, ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map,
    StateT.run_pure, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
  have hpair1 := unframe_dropFrame_pair (List.replicate n false) (List.replicate n true)
  have hpair2 := unframe_dropFrame_pair (List.replicate n false) (List.replicate n false)
  have hneMsg : List.replicate n true ≠ List.replicate n false := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : n ≠ 0)
    simp
  trans (ProbComp.eval (E.keyGen n)).bind (fun _ => PMF.pure false)
  · refine PMF.bind_congr_on_support _ _ _ fun ke hke => ?_
    unfold ccaOracle
    dsimp only [StateT.run]
    simp only [hpair1.1, hpair1.2, hpair2.1, hpair2.2, List.length_replicate, beq_self_eq_true,
      Bool.and_self, ↓reduceIte, Bool.false_eq_true, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map, PMF.bind_bind, PMF.pure_bind]
    trans (ProbComp.eval (E.encrypt n ke (List.replicate n true))).bind (fun _ => PMF.pure false)
    · refine PMF.bind_congr_on_support _ _ _ fun c₁ hc₁ => ?_
      have hc₁Len : c₁.length = n :=
        hctLen ke hke (List.replicate n true) (List.length_replicate) c₁ hc₁
      trans (ProbComp.eval (E.encrypt n ke (List.replicate n false))).bind (fun _ => PMF.pure false)
      · refine PMF.bind_congr_on_support _ _ _ fun c₂ hc₂ => ?_
        have hc₂Len : c₂.length = n :=
          hctLen ke hke (List.replicate n false) (List.length_replicate) c₂ hc₂
        have hne : c₁ ≠ c₂ := by
          intro hEq
          have hdec1 := E.decrypt_encrypt n ke hke (List.replicate n true)
            (List.length_replicate) c₁ hc₁
          have hdec2 := E.decrypt_encrypt n ke hke (List.replicate n false)
            (List.length_replicate) c₂ hc₂
          rw [hEq, hdec2] at hdec1
          exact hneMsg (Option.some.inj hdec1).symm
        rw [List.take_of_length_le hc₁Len.le, List.take_of_length_le hc₂Len.le]
        simp [beq_eq_false_iff_ne.mpr hne]
      · exact PMF.bind_const _ _
    · exact PMF.bind_const _ _
  · exact PMF.bind_const _ _

/-- **No zero-expansion symmetric cipher is CCA-secure**: the two-query attack through the
encryption channel has advantage `1` at every positive parameter. This is the CCA counterpart of
`SymmetricCipher.not_indcpa_of_ciphertext_length_eq`. -/
theorem not_indcca_of_ciphertext_length_eq (E : SymmetricCipher)
    (hctLen : ∀ n, ∀ ke ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg : List Bool, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n) :
    ¬ E.INDCCA := by
  intro hcca
  have hneg := hcca detCCAAdversary isOraclePPT_detCCAAdversary
  have hcomp : Negligible (fun n =>
      Game.advantage (ProbComp.eval (E.ccaGame detCCAAdversary false (n + 1)))
        (ProbComp.eval (E.ccaGame detCCAAdversary true (n + 1)))) :=
    hneg.comp_of_polynomial_bound (bound := fun m => m) (Filter.tendsto_add_atTop_nat 1)
      (by fun_prop) (Filter.Eventually.of_forall fun n => by lia)
  have hcongr : Negligible (fun _ : ℕ => (1 : ℝ≥0)) := hcomp.congr fun n => by
    rw [eval_ccaGame_detCCAAdversary_false E (n + 1) (hctLen (n + 1)),
      eval_ccaGame_detCCAAdversary_true E (by lia) (hctLen (n + 1)), Game.advantage]
    simp [Game.succProbability]
  exact not_negligible_const one_ne_zero hcongr

/-- The cipher that sends the plaintext as its ciphertext. -/
noncomputable def echoCipher : SymmetricCipher where
  keyGen _ := pure []
  encrypt _ _ msg := pure msg
  decrypt _ _ ct := some ct
  keyGen_ppt := by ppt
  encrypt_ppt := by ppt
  decrypt_polyTime := by polytime
  decrypt_encrypt := by
    intro _ _ _ msg _ ct hct
    rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hct
    subst hct
    rfl

/-- **Sending the plaintext is not IND-CCA.** -/
theorem not_indcca_echoCipher : ¬ echoCipher.INDCCA := by
  refine not_indcca_of_ciphertext_length_eq echoCipher fun n _ _ msg hmsg c hc => ?_
  change c ∈ (ProbComp.eval (pure msg)).support at hc
  rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hc
  subst hc
  exact hmsg

end SymmetricCipher

/-! ### One-way permutations -/

/-- Flipping every bit is a length-preserving bijection. -/
theorem flip_length_eq (word : List Bool) : (word.map not).length = word.length :=
  List.length_map _

theorem flip_bijective : Function.Bijective (List.map not) :=
  Function.Involutive.bijective fun word => by simp [Function.comp_def]

/-- **Flipping every bit is not a one-way permutation**: it has the two structural properties,
and flipping again inverts it. -/
theorem not_oneWayPermutation_flip : ¬ OneWayPermutation (List.map not) := fun h =>
  not_oneWay_of_inverse _ (fun _ y => y.map not) (by ppt) (fun x => by simp) h.oneWay

/-! ### Next-bit unpredictability -/

/-- The one-bit generator that always outputs `false`. -/
def constFalse : PRG.Generator Unit (Fin 1 → Bool) := ⟨fun _ _ => false⟩

/-- Guessing `false` predicts the bit of `constFalse` with probability `1`. -/
theorem predictionExperiment_constFalse :
    constFalse.predictionExperiment 0 (fun _ => PMF.pure false) = PMF.pure true := by
  simp [PRG.Generator.predictionExperiment, PRG.Generator.outputDist, constFalse,
    PMF.monad_bind_eq_bind, PMF.pure_map, Function.comp_def, PMF.bind_const]

/-- **A constant generator is not next-bit unpredictable** at any error below `1 / 2`. -/
theorem not_unpredictable_constFalse {δ : ℝ≥0} (hδ : δ < 1 / 2) :
    ¬ constFalse.Unpredictable (fun _ _ => True) δ := by
  intro h
  have hle := h 0 (fun _ => PMF.pure false) trivial
  rw [PRG.Generator.predictionAdvantage, predictionExperiment_constFalse, PMF.pure_apply_self,
    ENNReal.toReal_one] at hle
  have : (1 / 2 : ℝ) ≤ δ := by norm_num at hle ⊢; linarith [hle]
  have hδ' : (δ : ℝ) < 1 / 2 := by exact_mod_cast hδ
  linarith

end ComplexityTests.Crypto.SigmaLWECCANonvacuity

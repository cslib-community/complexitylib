/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import CslibFrontier.Crypto.Computational.OneWayToPRG
import CslibFrontier.Crypto.Computational.SchnorrProtocol
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Protocols.SigmaProtocol.Computational
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Tactic.PPT
import CslibFrontierTests.EfficientSimulators
import CslibFrontierTests.UnboundedSimulators

/-!
# Computational special HVZK and `Game.advantage`/`CloseTo` bridges

Checks of `CslibFrontier.Crypto.Game.CloseTo`, `CslibFrontier.Computability.Interactive.Security`'s
`CloseTo` calculus, and `SigmaProtocol.ComputationalSpecialHVZK` ([BonehShoup2023], Section 20.4.2,
Attack Game 20.4 and Definition 20.6, p. 840) on concrete instances and two-sided separations:

* **Boolean and infinite-type `CloseTo`/`Game` bridges.** Check `Game.closeTo_iff_advantage_le` on
  concrete `PMF Bool` laws and `Game.advantage_bind_le_of_closeTo` across `PMF ℕ` without
  `Fintype`.
* **Schnorr in `schnorrGroups`.** Instantiate
  `PrimeOrderGroupFamily.computationalSpecialHVZK_schnorr` with exact zero acceptance error
  (`δ = fun _ => 0`), exercising both `accepts_schnorrSimulateWord` and Attack Game 20.4
  indistinguishability.
* **`SpecialHVZK` does not imply `ComputationalSpecialHVZK` (under discrete log).** The protocol
  `sendWitnessFamily F` is perfectly `SpecialHVZK` at every index (`specialHVZK_sendWitness`), yet
  under `F.DiscreteLog setup` it fails `ComputationalSpecialHVZK` for *every* simulator `sim` and
  *every* acceptance-error parameter `δ` (even `δ = fun _ => ⊤`, without invoking `accepts`),
  because Attack Game 20.4's `indistinguishable` obligation alone forces `sim` to invert discrete
  logarithms (`not_computationalSpecialHVZK_sendWitness`).
* **`ComputationalSpecialHVZK` does not imply `SpecialHVZK` or `EfficientSpecialHVZK` (from any PRG
  or OWF).** For any stretching `PseudorandomGenerator generator length`, the protocol family
  `prgWitnessSigma generator length` commits to `generator seed` when the witness bit is `false` and
  to a uniform `length n`-bit string when the witness bit is `true`. Its word simulator samples a
  uniform `length n`-bit commitment, achieving `ComputationalSpecialHVZK` with exact zero acceptance
  error (`computationalSpecialHVZK_prgWitnessSigma`), whereas the `2 ^ n`-element generator image
  covers at most half of `{0, 1} ^ (length n)`, ruling out `SpecialHVZK`, `EfficientSpecialHVZK` for
  every `δ`, and even unbounded statistical transcript simulation below error `1 / 4`
  (`not_specialHVZK_prgWitnessSigma`, `not_efficientSpecialHVZK_prgWitnessSigma`,
  `not_statistical_hvzk_prgWitnessSigma`, `exists_computationalSpecialHVZK_and_not_specialHVZK`).
-/

namespace CslibFrontierTests.ComputationalSpecialHVZK

open Cslib Cslib.Crypto Cslib.Crypto.Protocols Cslib.Crypto.Protocols.SigmaProtocol
  Cslib.Interactive Probability Turing.MultiTapeTM
  CslibFrontierTests.UnboundedSimulators.Sigma CslibFrontierTests.EfficientSimulators
open scoped ENNReal NNReal

/-! ### `Game.advantage` and `CloseTo` bridges -/

/-- A point mass and a fair coin have advantage `1 / 2`, so `CloseTo` holds at `1 / 2` and fails at
`1 / 4`. -/
example : CloseTo (PMF.pure true) (PMF.uniformOfFintype Bool) ((1 / 2 : ℝ≥0) : ℝ≥0∞) ∧
    ¬ CloseTo (PMF.pure true) (PMF.uniformOfFintype Bool) ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
  have hadv : Game.advantage (PMF.pure true) (PMF.uniformOfFintype Bool) = 1 / 2 := by
    apply NNReal.eq
    rw [Game.coe_guessingAdvantage]
    simp only [Game.succProbability, PMF.pure_apply, ↓reduceIte, ENNReal.toNNReal_one,
      NNReal.coe_one]
    norm_num
  rw [Game.closeTo_iff_advantage_le, Game.closeTo_iff_advantage_le, hadv]
  exact ⟨le_rfl, by norm_num⟩

/-- `Game.advantage_bind_le_of_closeTo` bounds randomized Boolean distinguishers on `PMF ℕ` without
any `Fintype` assumption. -/
example (μ ν : PMF ℕ) (h : CloseTo μ ν ((1 / 8 : ℝ≥0) : ℝ≥0∞)) (test : ℕ → Game) :
    Game.advantage (μ.bind test) (ν.bind test) ≤ 1 / 8 :=
  Game.advantage_bind_le_of_closeTo h test

/-! ### Schnorr in `schnorrGroups` -/

/-- Schnorr's Sigma protocol in `schnorrGroups` satisfies `ComputationalSpecialHVZK` with exact zero
acceptance error (`δ = fun _ => 0`) for any group-description setup `setup`. -/
example (setup : ℕ → PMF schnorrGroups.Desc) :
    ComputationalSpecialHVZK schnorrGroups.schnorrFamily
      (fun i α u => α • schnorrGroups.generator i.2 = u)
      schnorrGroups.schnorrEncoding (fun i => schnorrGroups.encScalar i.2)
      (fun n => (setup n).map (n, ·)) schnorrGroups.schnorrSimulateWord (fun _ => 0) :=
  schnorrGroups.computationalSpecialHVZK_schnorr setup

/-! ### `SpecialHVZK` does not imply `ComputationalSpecialHVZK` -/

section DiscreteLogSeparation

variable {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}

/-- Attack Game 20.4 adversary against `sendWitnessFamily F`: sample `s ← F.sampleExp n d`, submit
the valid discrete-logarithm pair `((s mod q).bits, F.encode d (s • g))` while saving
`state = (s mod q).bits`, and check whether the challenger's commitment word equals `state`. -/
noncomputable def sendWitnessAdversary (F : PrimeOrderGroupFamily) :
    CHVZKAdversary (ℕ × F.Desc) where
  choose n idx :=
    let ⟨_, d⟩ := idx
    do
      let s ← F.sampleExp n d
      let xw := (s % F.order d).bits
      return ((xw, F.smul (d, s, F.encode d (F.generator d))), xw)
  guess _ state conv :=
    let ⟨tw, _, _⟩ := conv
    pure (tw == state)

theorem isPPT_sendWitnessAdversary (F : PrimeOrderGroupFamily) :
    CHVZKAdversary.IsPPT (sendWitnessEncoding F).index (sendWitnessAdversary F) where
  choose := by
    let encIdx := (sendWitnessEncoding F).index
    let encIn := encPair encUnary encIdx
    have hn : ComputableInPolyTime (fun p : ℕ × ℕ × F.Desc => p.1) encIn encUnary := by fun_prop
    have hp2 : ComputableInPolyTime (fun p : ℕ × ℕ × F.Desc => p.2) encIn encIdx := by fun_prop
    have hd : ComputableInPolyTime (fun (⟨_, _, d⟩ : ℕ × ℕ × F.Desc) => d) encIn F.encDesc :=
      (ComputableInPolyTime.snd encUnary F.encDesc).comp hp2
    change IsPPTOn encIn _ fun ⟨n, _, d⟩ => F.sampleExp n d >>= fun s =>
      pure (((s % F.order d).bits,
        F.smul (d, s, F.encode d (F.generator d))), (s % F.order d).bits)
    refine (F.isPPTOn_sampleExp hn hd).bind_with ?_
    let encMid := encPair encIn encNat
    have hp1 : ComputableInPolyTime (fun q : (ℕ × ℕ × F.Desc) × ℕ => q.1) encMid encIn := by
      fun_prop
    have hd' : ComputableInPolyTime (fun (⟨⟨_, _, d⟩, _⟩ : (ℕ × ℕ × F.Desc) × ℕ) => d)
        encMid F.encDesc :=
      hd.comp hp1
    have hs : ComputableInPolyTime (fun q : (ℕ × ℕ × F.Desc) × ℕ => q.2) encMid encNat := by
      fun_prop
    have hq := F.computableInPolyTime_order.comp hd'
    have hmod : ComputableInPolyTime
        (fun (⟨⟨_, _, d⟩, s⟩ : (ℕ × ℕ × F.Desc) × ℕ) => s % F.order d) encMid encNat :=
      ComputableInPolyTime.binary_mod.comp (hs.prod hq)
    have hbits : ComputableInPolyTime Nat.bits encNat encBits :=
      (by fun_prop : ComputableInPolyTime id encNat encNat).of_enc_eq fun _ => rfl
    have hxw := hbits.comp hmod
    have hg := F.computableInPolyTime_generator.comp hd'
    have hyw := F.computableInPolyTime_smul.comp (hd'.prod (hs.prod hg))
    exact ((hxw.prod hyw).prod hxw).isPPTOn
  guess := by
    let encConv := encPair encBits (encPair encBits encBits)
    let encRest := encPair encBits encConv
    let encIn := encPair encUnary encRest
    have hrest : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool × List Bool × List Bool => p.2) encIn encRest := by
      fun_prop
    have hst : ComputableInPolyTime
        (fun (⟨_, st, _⟩ : ℕ × List Bool × List Bool × List Bool × List Bool) => st)
        encIn encBits :=
      (ComputableInPolyTime.fst encBits encConv).comp hrest
    have hconv : ComputableInPolyTime
        (fun (⟨_, _, conv⟩ : ℕ × List Bool × List Bool × List Bool × List Bool) => conv)
        encIn encConv :=
      (ComputableInPolyTime.snd encBits encConv).comp hrest
    have htw : ComputableInPolyTime
        (fun (⟨_, _, tw, _⟩ : ℕ × List Bool × List Bool × List Bool × List Bool) => tw)
        encIn encBits :=
      (ComputableInPolyTime.fst encBits (encPair encBits encBits)).comp hconv
    have hbeq : ComputableInPolyTime (fun q : List Bool × List Bool => q.1 == q.2)
        (encPair encBits encBits) encBool := by fun_prop
    exact (hbeq.comp (htw.prod hst)).isPPTOn

/-- **Sending the witness is not computationally special HVZK** under the discrete-logarithm
assumption, for *any* simulator `sim` and *any* acceptance-error function `δ` (without using the
`accepts` field): Attack Game 20.4 indistinguishability on `(x, x • g)` forces `sim` to invert
discrete logarithms. -/
theorem not_computationalSpecialHVZK_sendWitness (hDL : F.DiscreteLog setup)
    (sim : (ℕ × F.Desc) × List Bool × List Bool → ProbComp (List Bool × List Bool))
    (δ : ℕ × F.Desc → ℝ≥0∞) :
    ¬ ComputationalSpecialHVZK (sendWitnessFamily F) (dlRel F) (sendWitnessEncoding F)
      (fun i => F.encScalar i.2) (fun n => (setup n).map (n, ·)) sim δ := by
  intro h
  let dlAdv : ℕ → F.Desc × List Bool → ProbComp (List Bool) := fun n input => do
    let c ← ProbComp.uniform Bool
    Prod.fst <$> sim ((n, input.1), input.2, encBool c)
  have hdlAdv : IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) encBits
      (fun input => dlAdv input.1 input.2) := by
    let encIn := encPair encUnary (encPair F.encDesc encBits)
    have hn : ComputableInPolyTime (fun p : ℕ × F.Desc × List Bool => p.1) encIn encUnary := by
      fun_prop
    have hp2 : ComputableInPolyTime (fun p : ℕ × F.Desc × List Bool => p.2)
        encIn (encPair F.encDesc encBits) := by fun_prop
    have hd := (ComputableInPolyTime.fst F.encDesc encBits).comp hp2
    have hu := (ComputableInPolyTime.snd F.encDesc encBits).comp hp2
    have hcoin : IsPPTOn encIn encBool (fun _ => ProbComp.uniform Bool) := by ppt
    refine hcoin.bind_with ?_
    let encMid := encPair encIn encBool
    have hp1 : ComputableInPolyTime (fun q : (ℕ × F.Desc × List Bool) × Bool => q.1)
        encMid encIn := by fun_prop
    have hc : ComputableInPolyTime (fun q : (ℕ × F.Desc × List Bool) × Bool => encBool q.2)
        encMid encBits := by fun_prop
    have hprep := ((hn.comp hp1).prod (hd.comp hp1)).prod ((hu.comp hp1).prod hc)
    exact (h.ppt.preprocess hprep).map (ComputableInPolyTime.fst encBits encBits)
  have hreal (n : ℕ) :
      chvzkRealGame (sendWitnessFamily F) (dlRel F) (sendWitnessEncoding F)
        (fun i => F.encScalar i.2) (fun m => (setup m).map (m, ·))
        (sendWitnessAdversary F) n = PMF.pure true := by
    have hchoose (d : F.Desc) : (sendWitnessAdversary F).choose n (n, d) =
        (F.sampleExp n d >>= fun s =>
          pure (((s % F.order d).bits, F.smul (d, s, F.encode d (F.generator d))),
            (s % F.order d).bits)) := rfl
    simp only [chvzkRealGame, chvzkGameWith, PMF.monad_bind_eq_bind, PMF.bind_map,
      Function.comp_def, hchoose, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind,
      PMF.pure_bind]
    have hstep (d : F.Desc) (s : ℕ) :
        chvzkBranch (dlRel F) (sendWitnessEncoding F) (fun i => F.encScalar i.2)
          (encodedConversation (sendWitnessFamily F) (sendWitnessEncoding F))
          (sendWitnessAdversary F) n (n, d)
          ((s % F.order d).bits) (F.smul (d, s, F.encode d (F.generator d)))
          ((s % F.order d).bits) = PMF.pure true := by
      let α : ZMod (F.order d) := (s : ZMod (F.order d))
      have hx : F.encScalar d α = (s % F.order d).bits := by
        simp only [PrimeOrderGroupFamily.encScalar, Function.Embedding.coeFn_mk, encNat_apply, α,
          ZMod.val_natCast]
      have hy : (sendWitnessEncoding F).statement (n, d) (α • F.generator d) =
          F.smul (d, s, F.encode d (F.generator d)) := by
        simp only [sendWitnessEncoding, PrimeOrderGroupFamily.encodeEmbedding,
          Function.Embedding.coeFn_mk, F.smul_encode, α]
      rw [← hx, ← hy, chvzkBranch_valid _ _ _ _ (rfl : dlRel F (n, d) α (α • F.generator d))]
      simp only [encodedConversation, sendWitnessAdversary, PMF.bind_map, Function.comp_def]
      rw [← PMF.bind_const ((sendWitnessFamily F (n, d)).conversation α (α • F.generator d))
        (PMF.pure true)]
      refine PMF.bind_congr_on_support _ _ _ fun tcz htcz => ?_
      rcases tcz with ⟨t, c, z⟩
      have ht : t = α := sendWitnessSigma_conversation_fst (dlRel F (n, d)) α _ htcz
      subst ht
      simp only [sendWitnessEncoding, beq_self_eq_true, ProbComp.eval_pure]
    have hbind : (setup n).bind (fun d => (ProbComp.eval (F.sampleExp n d)).bind fun s =>
        chvzkBranch (dlRel F) (sendWitnessEncoding F) (fun i => F.encScalar i.2)
          (encodedConversation (sendWitnessFamily F) (sendWitnessEncoding F))
          (sendWitnessAdversary F) n (n, d)
          ((s % F.order d).bits) (F.smul (d, s, F.encode d (F.generator d)))
          ((s % F.order d).bits)) = PMF.pure true := by
      simp_rw [hstep, PMF.bind_const]
    exact hbind
  have hsim_bound (n : ℕ) :
      Game.succProbability
        (chvzkSimGame (dlRel F) (sendWitnessEncoding F) (fun i => F.encScalar i.2)
          (fun m => (setup m).map (m, ·)) sim (sendWitnessAdversary F) n) ≤
        (1 / 2 : ℝ≥0) ^ n + Game.succProbability (F.discreteLogGame setup dlAdv n) := by
    let simTest (d : F.Desc) (α : ZMod (F.order d)) : Game :=
      (simulatedConversation (sendWitnessEncoding F) sim (n, d) (α • F.generator d)).bind
        fun conv =>
          let ⟨tw, _, _⟩ := conv
          PMF.pure (tw == F.encScalar d α)
    have hsim_eq :
        chvzkSimGame (dlRel F) (sendWitnessEncoding F) (fun i => F.encScalar i.2)
          (fun m => (setup m).map (m, ·)) sim (sendWitnessAdversary F) n =
          (setup n).bind fun d =>
            (((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d)))).bind
              (simTest d) := by
      simp only [chvzkSimGame, chvzkGameWith, sendWitnessAdversary, PMF.monad_bind_eq_bind,
        PMF.bind_map, Function.comp_def, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind,
        PMF.pure_bind]
      congr 1
      funext d
      congr 1
      funext s
      let α : ZMod (F.order d) := (s : ZMod (F.order d))
      have hx : F.encScalar d α = (s % F.order d).bits := by
        simp only [PrimeOrderGroupFamily.encScalar, Function.Embedding.coeFn_mk, encNat_apply, α,
          ZMod.val_natCast]
      have hy : (sendWitnessEncoding F).statement (n, d) (α • F.generator d) =
          F.smul (d, s, F.encode d (F.generator d)) := by
        simp only [sendWitnessEncoding, PrimeOrderGroupFamily.encodeEmbedding,
          Function.Embedding.coeFn_mk, F.smul_encode, α]
      rw [← hx, ← hy, chvzkBranch_valid _ _ _ _ (rfl : dlRel F (n, d) α (α • F.generator d))]
      rfl
    let unifGame : Game :=
      (setup n).bind fun d => (PMF.uniformOfFintype (ZMod (F.order d))).bind (simTest d)
    have hadv_exp : Game.advantage
        ((setup n).bind fun d =>
          (((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d)))).bind
            (simTest d))
        unifGame ≤ (1 / 2 : ℝ≥0) ^ n := by
      refine Game.advantage_bind_le_nnreal (setup n) _ _ fun d => ?_
      rw [Game.advantage_comm, one_div_pow]
      exact Game.advantage_bind_le_of_closeTo (F.closeTo_uniform_sampleExp n d) (simTest d)
    have hunif_le : unifGame true ≤ F.discreteLogGame setup dlAdv n true := by
      simp only [unifGame, PrimeOrderGroupFamily.discreteLogGame, simTest, simulatedConversation,
        dlAdv, sendWitnessEncoding, PrimeOrderGroupFamily.encodeEmbedding,
        Function.Embedding.coeFn_mk, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_map,
        PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map,
        Function.comp_def, PMF.bind_bind, PMF.pure_bind, PMF.bind_apply]
      refine tsum_le_tsum fun d => mul_le_mul_of_nonneg_left (tsum_le_tsum fun α =>
        mul_le_mul_of_nonneg_left ?_ zero_le) zero_le
      refine tsum_le_tsum fun c => mul_le_mul_of_nonneg_left (tsum_le_tsum fun out =>
        mul_le_mul_of_nonneg_left ?_ zero_le) zero_le
      by_cases htw : out.1 = F.encScalar d α
      · have hcast : (ofBits (F.encScalar d α) : ZMod (F.order d)) = α := by
          change ((ofBits (encNat α.val) : ℕ) : ZMod (F.order d)) = α
          rw [encNat_apply, ofBits, Nat.foldr_bit_bits, ZMod.natCast_zmod_val]
        simp [htw, hcast]
      · simp [htw]
    have hunif_succ : Game.succProbability unifGame ≤
        Game.succProbability (F.discreteLogGame setup dlAdv n) :=
      ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) hunif_le
    rw [hsim_eq]
    calc
      Game.succProbability
          ((setup n).bind fun d =>
            (((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d)))).bind
              (simTest d))
        ≤ unifGame.succProbability + Game.advantage
            ((setup n).bind fun d =>
              (((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d)))).bind
                (simTest d))
            unifGame := by
          refine tsub_le_iff_left.mp ?_
          rw [Game.advantage, NNReal.nndist_eq]
          exact le_max_left _ _
      _ ≤ Game.succProbability (F.discreteLogGame setup dlAdv n) + (1 / 2 : ℝ≥0) ^ n :=
          add_le_add hunif_succ hadv_exp
      _ = (1 / 2 : ℝ≥0) ^ n + Game.succProbability (F.discreteLogGame setup dlAdv n) :=
          add_comm _ _
  have h1_le (n : ℕ) : (1 : ℝ≥0) ≤
      Game.advantage
        (chvzkRealGame (sendWitnessFamily F) (dlRel F) (sendWitnessEncoding F)
          (fun i => F.encScalar i.2) (fun m => (setup m).map (m, ·))
          (sendWitnessAdversary F) n)
        (chvzkSimGame (dlRel F) (sendWitnessEncoding F) (fun i => F.encScalar i.2)
          (fun m => (setup m).map (m, ·)) sim (sendWitnessAdversary F) n) +
      ((1 / 2 : ℝ≥0) ^ n + Game.succProbability (F.discreteLogGame setup dlAdv n)) := by
    have hreal_succ :
        Game.succProbability
          (chvzkRealGame (sendWitnessFamily F) (dlRel F) (sendWitnessEncoding F)
            (fun i => F.encScalar i.2) (fun m => (setup m).map (m, ·))
            (sendWitnessAdversary F) n) = 1 := by
      simp [hreal n, Game.succProbability]
    calc
      (1 : ℝ≥0) = Game.succProbability
          (chvzkRealGame (sendWitnessFamily F) (dlRel F) (sendWitnessEncoding F)
            (fun i => F.encScalar i.2) (fun m => (setup m).map (m, ·))
            (sendWitnessAdversary F) n) := hreal_succ.symm
      _ ≤ Game.succProbability
            (chvzkSimGame (dlRel F) (sendWitnessEncoding F) (fun i => F.encScalar i.2)
              (fun m => (setup m).map (m, ·)) sim (sendWitnessAdversary F) n) +
          Game.advantage
            (chvzkRealGame (sendWitnessFamily F) (dlRel F) (sendWitnessEncoding F)
              (fun i => F.encScalar i.2) (fun m => (setup m).map (m, ·))
              (sendWitnessAdversary F) n)
            (chvzkSimGame (dlRel F) (sendWitnessEncoding F) (fun i => F.encScalar i.2)
              (fun m => (setup m).map (m, ·)) sim (sendWitnessAdversary F) n) := by
          refine tsub_le_iff_left.mp ?_
          rw [Game.advantage, NNReal.nndist_eq]
          exact le_max_left _ _
      _ ≤ ((1 / 2 : ℝ≥0) ^ n + Game.succProbability (F.discreteLogGame setup dlAdv n)) +
          Game.advantage
            (chvzkRealGame (sendWitnessFamily F) (dlRel F) (sendWitnessEncoding F)
              (fun i => F.encScalar i.2) (fun m => (setup m).map (m, ·))
              (sendWitnessAdversary F) n)
            (chvzkSimGame (dlRel F) (sendWitnessEncoding F) (fun i => F.encScalar i.2)
              (fun m => (setup m).map (m, ·)) sim (sendWitnessAdversary F) n) :=
          add_le_add (hsim_bound n) le_rfl
      _ = _ := add_comm _ _
  have hnegl := (h.indistinguishable (sendWitnessAdversary F)
    (isPPT_sendWitnessAdversary F)).add
      ((negligible_geometric (ratio := 1 / 2) (by norm_num)).add (hDL dlAdv hdlAdv))
  exact not_negligible_const (c := 1) one_ne_zero (negligible_of_le hnegl h1_le)

end DiscreteLogSeparation

/-! ### `ComputationalSpecialHVZK` does not imply `SpecialHVZK` or `EfficientSpecialHVZK` -/

section PRGSeparation

/-- Witness-dependent PRG commitment Sigma protocol for the total relation `fun _ _ => True` on
`Bool × Unit`: witness `false` commits to `generator seed` for a uniform `n`-bit seed, witness
`true` commits to a truly uniform `length n`-bit word, and the verifier checks that the commitment
has length `length n`. -/
noncomputable def prgWitnessSigma (generator : List Bool → List Bool) (length : ℕ → ℕ) (n : ℕ) :
    SigmaProtocol Bool Unit (List Bool) Bool Unit where
  State := Unit
  commit x _ :=
    if x then
      (BitString.uniformList (length n)).map (·, ())
    else
      (generatorEnsemble generator n).map (·, ())
  respond _ _ _ _ := ()
  verify _ t _ _ := decide (t.length = length n)

/-- Word encodings of `prgWitnessSigma`: unary security parameter, trivial statement/response, and
raw bit-word commitment. -/
def prgWitnessEncoding :
    Encoding ℕ (fun _ => Unit) (fun _ => List Bool) (fun _ => Bool) (fun _ => Unit) where
  index := encUnary
  statement _ := encUnit
  commitment _ := encBits
  challenge _ := encBool
  response _ := encUnit

/-- Simulator for `prgWitnessSigma`: ignore the statement and challenge, sample a uniform
`length n`-bit commitment, and return `(t, encUnit ())`. -/
noncomputable def prgWitnessSim (length : ℕ → ℕ) :
    ℕ × List Bool × List Bool → ProbComp (List Bool × List Bool)
  | (n, _, _) => do
    let t ← BitString.sampleList (length n)
    return (t, encUnit ())

theorem complete_prgWitnessSigma {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hlen : ∀ word, (generator word).length = length word.length) (n : ℕ) :
    (prgWitnessSigma generator length n).Complete (fun _ _ => True) := by
  intro x _ _ c tz htz
  cases x
  · simp only [SigmaProtocol.transcript, prgWitnessSigma, Bool.false_eq_true, ↓reduceIte,
      generatorEnsemble, PMF.map_comp, PMF.mem_support_map_iff] at htz
    obtain ⟨seed, hseed, rfl⟩ := htz
    simp [SigmaProtocol.Accepts, prgWitnessSigma, hlen,
      BitString.length_of_mem_support_uniformList hseed]
  · simp only [SigmaProtocol.transcript, prgWitnessSigma, ↓reduceIte, PMF.map_comp,
      PMF.mem_support_map_iff] at htz
    obtain ⟨t, ht, rfl⟩ := htz
    simp [SigmaProtocol.Accepts, prgWitnessSigma, BitString.length_of_mem_support_uniformList ht]

/-- **Every stretching `PseudorandomGenerator` makes `prgWitnessSigma` computationally special
HVZK** with exact zero acceptance error (`δ = fun _ => 0`). -/
theorem computationalSpecialHVZK_prgWitnessSigma
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hPRG : PseudorandomGenerator generator length) :
    ComputationalSpecialHVZK (prgWitnessSigma generator length) (fun _ _ _ => True)
      prgWitnessEncoding (fun _ => encBool) PMF.pure (prgWitnessSim length) (fun _ => 0) where
  ppt := by
    have hlen := hPRG.polyTime_length
    let encIn := encPair encUnary (encPair encBits encBits)
    have hn : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => length p.1)
        encIn encUnary := hlen.comp (by fun_prop)
    change IsPPTOn encIn (encPair encBits encBits) fun p =>
      BitString.sampleList (length p.1) >>= fun t => pure (t, encUnit ())
    have hsample : IsPPTOn encIn encBits (fun p => BitString.sampleList (length p.1)) := by ppt
    refine hsample.bind_with ?_
    exact ((ComputableInPolyTime.snd encIn encBits).prod
      (ComputableInPolyTime.const (encUnit ()))).isPPTOn
  accepts := by
    rintro n ⟨⟩ c
    dsimp only [prgWitnessEncoding]
    have heq : (ProbComp.eval (prgWitnessSim length (n, encUnit (), encBool c))).toOuterMeasure
        {w | ∃ t z, w = (encBits t, encUnit z) ∧
          (prgWitnessSigma generator length n).Accepts () t c z} = 1 := by
      simp only [prgWitnessSim, ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure]
      rw [show (fun a : List Bool => PMF.pure (a, encUnit ())) =
          PMF.pure ∘ fun a => (a, encUnit ()) from rfl,
        PMF.bind_pure_comp, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_eq_one_iff]
      intro t ht
      refine ⟨t, (), rfl, ?_⟩
      simp [SigmaProtocol.Accepts, prgWitnessSigma, BitString.length_of_mem_support_uniformList ht]
    simpa only [tsub_zero] using heq.ge
  indistinguishable adversary hadv := by
    have hlen := hPRG.polyTime_length
    let D : Distinguisher := fun n word => do
      let choice ← adversary.choose n n
      let ⟨⟨xw, yw⟩, state⟩ := choice
      if yw == encUnit () then
        if xw == encBool false then
          let c ← ProbComp.uniform Bool
          adversary.guess n state (word, encBool c, encUnit ())
        else if xw == encBool true then
          let t ← BitString.sampleList (length n)
          let c ← ProbComp.uniform Bool
          adversary.guess n state (t, encBool c, encUnit ())
        else
          return false
      else
        return false
    have hD : Probability.IsPPT encBool D := by
      have hchoose := hadv.choose
      have hguess := hadv.guess
      let encD := encPair encUnary encBits
      have hn : ComputableInPolyTime (fun p : ℕ × List Bool => p.1) encD encUnary := by fun_prop
      have hnn : ComputableInPolyTime (fun p : ℕ × List Bool => (p.1, p.1))
          encD (encPair encUnary encUnary) := hn.prod hn
      change IsPPTOn encD encBool fun p =>
        adversary.choose p.1 p.1 >>= fun ⟨⟨xw, yw⟩, state⟩ =>
          if yw == encUnit () then
            if xw == encBool false then
              ProbComp.uniform Bool >>= fun c =>
                adversary.guess p.1 state (p.2, encBool c, encUnit ())
            else if xw == encBool true then
              BitString.sampleList (length p.1) >>= fun t =>
                ProbComp.uniform Bool >>= fun c =>
                  adversary.guess p.1 state (t, encBool c, encUnit ())
            else
              pure false
          else
            pure false
      refine (hchoose.preprocess hnn).bind_with ?_
      ppt
    have hgame (n : ℕ) :
        Game.advantage
          (chvzkRealGame (prgWitnessSigma generator length) (fun _ _ _ => True)
            prgWitnessEncoding (fun _ => encBool) PMF.pure adversary n)
          (chvzkSimGame (fun _ _ _ => True) prgWitnessEncoding (fun _ => encBool)
            PMF.pure (prgWitnessSim length) adversary n) =
        Game.advantage
          (distinguishingGame (generatorEnsemble generator n) (D n))
          (distinguishingGame (BitString.uniformList (length n)) (D n)) := by
      have hreal_eq :
          chvzkRealGame (prgWitnessSigma generator length) (fun _ _ _ => True)
            prgWitnessEncoding (fun _ => encBool) PMF.pure adversary n =
          distinguishingGame (generatorEnsemble generator n) (D n) := by
        simp only [chvzkRealGame, chvzkGameWith, distinguishingGame, D, PMF.monad_bind_eq_bind,
          PMF.pure_bind, ProbComp.eval_bind]
        rw [PMF.bind_comm (generatorEnsemble generator n) (ProbComp.eval (adversary.choose n n))]
        refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨xw, yw⟩, state⟩ _ => ?_
        by_cases hy : yw = encUnit ()
        · subst hy
          by_cases hxf : xw = encBool false
          · subst hxf
            simp only [beq_self_eq_true, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_uniform]
            rw [show encBool false = (fun _ : ℕ => encBool) n false from rfl,
              show encUnit () = prgWitnessEncoding.statement n () from rfl,
              chvzkBranch_valid _ _ _ _ trivial]
            simp only [encodedConversation, SigmaProtocol.conversation, prgWitnessSigma,
              prgWitnessEncoding, Bool.false_eq_true, ↓reduceIte, PMF.monad_bind_eq_bind,
              PMF.monad_pure_eq_pure, PMF.map_bind, PMF.bind_map, PMF.pure_map, PMF.bind_bind,
              PMF.pure_bind, Function.comp_def]
            rfl
          · by_cases hxt : xw = encBool true
            · subst hxt
              have htf : (encBool true == encBool false) = false := by decide
              simp only [beq_self_eq_true, htf, Bool.false_eq_true, ↓reduceIte,
                ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_uniform,
                PMF.bind_const]
              rw [show encBool true = (fun _ : ℕ => encBool) n true from rfl,
                show encUnit () = prgWitnessEncoding.statement n () from rfl,
                chvzkBranch_valid _ _ _ _ trivial]
              simp only [encodedConversation, SigmaProtocol.conversation, prgWitnessSigma,
                prgWitnessEncoding, ↓reduceIte, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
                PMF.map_bind, PMF.bind_map, PMF.pure_map, PMF.bind_bind, PMF.pure_bind,
                Function.comp_def]
              rfl
            · have hinv : ¬ ∃ p : Bool × Unit,
                  encBool p.1 = xw ∧ prgWitnessEncoding.statement n p.2 = encUnit () ∧ True := by
                rintro ⟨⟨b, ⟨⟩⟩, hb, -, -⟩
                cases b
                · exact hxf hb.symm
                · exact hxt hb.symm
              have hxf' : (xw == encBool false) = false := beq_false_of_ne hxf
              have hxt' : (xw == encBool true) = false := beq_false_of_ne hxt
              simp only [beq_self_eq_true, hxf', hxt', Bool.false_eq_true, ↓reduceIte,
                ProbComp.eval_pure, PMF.bind_const]
              exact chvzkBranch_invalid (R := fun _ _ _ => True) (enc := prgWitnessEncoding)
                (encW := fun _ => encBool) _ _ _ _ _ hinv
        · have hinv : ¬ ∃ p : Bool × Unit,
              encBool p.1 = xw ∧ prgWitnessEncoding.statement n p.2 = yw ∧ True := by
            rintro ⟨⟨_, ⟨⟩⟩, -, hy', -⟩
            exact hy hy'.symm
          have hy' : (yw == encUnit ()) = false := beq_false_of_ne hy
          simp only [hy', Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.bind_const]
          exact chvzkBranch_invalid (R := fun _ _ _ => True) (enc := prgWitnessEncoding)
            (encW := fun _ => encBool) _ _ _ _ _ hinv
      have hsim_eq :
          chvzkSimGame (fun _ _ _ => True) prgWitnessEncoding (fun _ => encBool)
            PMF.pure (prgWitnessSim length) adversary n =
          distinguishingGame (BitString.uniformList (length n)) (D n) := by
        simp only [chvzkSimGame, chvzkGameWith, distinguishingGame, D, PMF.monad_bind_eq_bind,
          PMF.pure_bind, ProbComp.eval_bind]
        rw [PMF.bind_comm (BitString.uniformList (length n)) (ProbComp.eval (adversary.choose n n))]
        refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨xw, yw⟩, state⟩ _ => ?_
        by_cases hy : yw = encUnit ()
        · subst hy
          by_cases hxf : xw = encBool false
          · subst hxf
            simp only [beq_self_eq_true, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_uniform]
            rw [show encBool false = (fun _ : ℕ => encBool) n false from rfl,
              show encUnit () = prgWitnessEncoding.statement n () from rfl,
              chvzkBranch_valid _ _ _ _ trivial]
            simp only [simulatedConversation, prgWitnessSim, prgWitnessEncoding,
              ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure,
              PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
            rw [PMF.bind_comm (PMF.uniformOfFintype Bool) (BitString.uniformList (length n))]
          · by_cases hxt : xw = encBool true
            · subst hxt
              have htf : (encBool true == encBool false) = false := by decide
              simp only [beq_self_eq_true, htf, Bool.false_eq_true, ↓reduceIte,
                ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_uniform,
                PMF.bind_const]
              rw [show encBool true = (fun _ : ℕ => encBool) n true from rfl,
                show encUnit () = prgWitnessEncoding.statement n () from rfl,
                chvzkBranch_valid _ _ _ _ trivial]
              simp only [simulatedConversation, prgWitnessSim, prgWitnessEncoding,
                ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure,
                PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
              rw [PMF.bind_comm (PMF.uniformOfFintype Bool) (BitString.uniformList (length n))]
            · have hinv : ¬ ∃ p : Bool × Unit,
                  encBool p.1 = xw ∧ prgWitnessEncoding.statement n p.2 = encUnit () ∧ True := by
                rintro ⟨⟨b, ⟨⟩⟩, hb, -, -⟩
                cases b
                · exact hxf hb.symm
                · exact hxt hb.symm
              have hxf' : (xw == encBool false) = false := beq_false_of_ne hxf
              have hxt' : (xw == encBool true) = false := beq_false_of_ne hxt
              simp only [beq_self_eq_true, hxf', hxt', Bool.false_eq_true, ↓reduceIte,
                ProbComp.eval_pure, PMF.bind_const]
              exact chvzkBranch_invalid (R := fun _ _ _ => True) (enc := prgWitnessEncoding)
                (encW := fun _ => encBool) _ _ _ _ _ hinv
        · have hinv : ¬ ∃ p : Bool × Unit,
              encBool p.1 = xw ∧ prgWitnessEncoding.statement n p.2 = yw ∧ True := by
            rintro ⟨⟨_, ⟨⟩⟩, -, hy', -⟩
            exact hy hy'.symm
          have hy' : (yw == encUnit ()) = false := beq_false_of_ne hy
          simp only [hy', Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.bind_const]
          exact chvzkBranch_invalid (R := fun _ _ _ => True) (enc := prgWitnessEncoding)
            (encW := fun _ => encBool) _ _ _ _ _ hinv
      rw [hreal_eq, hsim_eq]
    exact (hPRG.indistinguishable D hD).congr fun n => (hgame n).symm

/-- The honest commitment laws for `x = false` and `x = true` in `prgWitnessSigma` have total
variation distance at least `1 / 2` whenever `n < length n`: `generatorEnsemble` puts mass `1` on
the `2 ^ n`-element generator image while `uniformList (length n)` puts mass at most `1 / 2` on
it. -/
theorem not_statistical_hvzk_prgWitnessSigma
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hstretch : ∀ n, n < length n) (n : ℕ)
    (simulate : Unit → Bool → PMF (List Bool × Unit))
    {ε : ℝ≥0∞} (hε : ε < 1 / 4) :
    ¬ ∀ x : Bool,
      CloseTo ((prgWitnessSigma generator length n).transcript x () false)
        (simulate () false) ε := by
  classical
  intro h
  have hclose : CloseTo
      ((prgWitnessSigma generator length n).transcript false () false)
      ((prgWitnessSigma generator length n).transcript true () false) (ε + ε) :=
    (h false).trans (h true).symm
  let imgFinset : Finset (List Bool) :=
    (Finset.univ : Finset (Fin n → Bool)).image fun r => generator (List.ofFn r)
  let event : Set (List Bool × Unit) := {tz | tz.1 ∈ (imgFinset : Set (List Bool))}
  have h1 : ((prgWitnessSigma generator length n).transcript false () false).toOuterMeasure event =
      1 := by
    simp only [SigmaProtocol.transcript, prgWitnessSigma, Bool.false_eq_true, ↓reduceIte,
      generatorEnsemble, BitString.uniformList, PMF.map_comp]
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_eq_one_iff]
    intro r _
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)
  have h2 : ((prgWitnessSigma generator length n).transcript true () false).toOuterMeasure event ≤
      1 / 2 := by
    simp only [SigmaProtocol.transcript, prgWitnessSigma, ↓reduceIte, PMF.map_comp,
      Function.comp_def]
    rw [PMF.toOuterMeasure_map_apply]
    have hpre : ((fun t : List Bool => (t, ())) ⁻¹' event) = (imgFinset : Set (List Bool)) := by
      ext t; rfl
    rw [hpre]
    have hcard : (imgFinset.card : ℝ≥0∞) ≤ 2 ^ n := by
      have hc : imgFinset.card ≤ 2 ^ n := by
        simpa [Fintype.card_bool, Fintype.card_fin] using
          (Finset.card_image_le (s := (Finset.univ : Finset (Fin n → Bool)))
            (f := fun r => generator (List.ofFn r)))
      exact_mod_cast hc
    have hpow : (2 : ℝ≥0∞) ^ (n + 1) ≤ 2 ^ length n :=
      pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt (hstretch n))
    have htwo_top : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
    calc
      (BitString.uniformList (length n)).toOuterMeasure imgFinset
        ≤ imgFinset.card * (1 / 2 ^ length n) :=
          BitString.toOuterMeasure_uniformList_finset_le (length n) imgFinset
      _ ≤ 2 ^ n * (1 / 2 ^ (n + 1)) := by
          gcongr
      _ = 1 / 2 := by
          rw [pow_succ, one_div, ENNReal.mul_inv (Or.inl (pow_ne_zero n two_ne_zero))
            (Or.inl (ENNReal.pow_ne_top htwo_top)), ← mul_assoc,
            ENNReal.mul_inv_cancel (pow_ne_zero n two_ne_zero)
              (ENNReal.pow_ne_top htwo_top), one_mul, one_div]
  have hineq := hclose event
  rw [h1] at hineq
  have hlt : (1 / 2 : ℝ≥0∞) + (ε + ε) < 1 := by
    have htwo_top : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
    have hadd : ε + ε < 1 / 4 + 1 / 4 := ENNReal.add_lt_add hε hε
    have hquarter : (1 / 4 : ℝ≥0∞) + 1 / 4 = 1 / 2 := by
      rw [← two_mul, show (4 : ℝ≥0∞) = 2 * 2 by norm_num, one_div,
        ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl htwo_top), ← mul_assoc,
        ENNReal.mul_inv_cancel two_ne_zero htwo_top, one_mul, one_div]
    rw [hquarter] at hadd
    have hhalf : (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 := by
      rw [← two_mul, one_div, ENNReal.mul_inv_cancel two_ne_zero htwo_top]
    exact (ENNReal.add_lt_add_left (by norm_num) hadd).trans_eq hhalf
  exact (not_le_of_gt (lt_of_le_of_lt (add_le_add h2 le_rfl) hlt)) hineq

/-- `prgWitnessSigma` fails `SpecialHVZK` at *every* parameter `n` and for *every* unbounded
simulator `simulate`. -/
theorem not_specialHVZK_prgWitnessSigma
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hstretch : ∀ n, n < length n) (n : ℕ)
    (simulate : Unit → Bool → PMF (List Bool × Unit)) :
    ¬ (prgWitnessSigma generator length n).SpecialHVZK (fun _ _ => True) simulate := by
  intro h
  refine not_statistical_hvzk_prgWitnessSigma (generator := generator) hstretch n simulate
    (ε := 0) (by norm_num) fun x => ?_
  rw [← h.transcript_eq x () trivial false]
  exact CloseTo.refl _

/-- `prgWitnessSigma` fails `EfficientSpecialHVZK` for *every* simulator family and *every*
realization error `δ` (including `δ = fun _ => ⊤`). -/
theorem not_efficientSpecialHVZK_prgWitnessSigma
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hstretch : ∀ n, n < length n)
    (simulate : ∀ _ : ℕ, Unit → Bool → PMF (List Bool × Unit))
    (δ : ℕ → ℝ≥0∞) :
    ¬ EfficientSpecialHVZK (prgWitnessSigma generator length) (fun _ _ _ => True)
      prgWitnessEncoding simulate δ := fun h =>
  not_specialHVZK_prgWitnessSigma hstretch 0 (simulate 0) (h.specialHVZK 0)

/-- **Any uniform one-way function yields an explicit complete Sigma protocol family that satisfies
`ComputationalSpecialHVZK` (with exact zero acceptance error) while failing `SpecialHVZK` (and
statistical HVZK with error `< 1 / 4`) at every security parameter.** -/
theorem exists_computationalSpecialHVZK_and_not_specialHVZK
    {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ (P : ∀ _ : ℕ, SigmaProtocol Bool Unit (List Bool) Bool Unit)
      (sim : ℕ × List Bool × List Bool → ProbComp (List Bool × List Bool)),
      (∀ n, (P n).Complete (fun _ _ => True)) ∧
      ComputationalSpecialHVZK P (fun _ _ _ => True) prgWitnessEncoding
        (fun _ => encBool) PMF.pure sim (fun _ => 0) ∧
      (∀ n simulate, ¬ (P n).SpecialHVZK (fun _ _ => True) simulate) := by
  obtain ⟨generator, hPRG⟩ := hf.exists_pseudorandomGenerator
  exact ⟨prgWitnessSigma generator (fun n => n + 1), prgWitnessSim (fun n => n + 1),
    complete_prgWitnessSigma hPRG.length_eq,
    computationalSpecialHVZK_prgWitnessSigma hPRG,
    not_specialHVZK_prgWitnessSigma hPRG.stretch⟩

end PRGSeparation

end CslibFrontierTests.ComputationalSpecialHVZK

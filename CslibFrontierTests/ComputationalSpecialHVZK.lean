/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import CslibFrontier.Crypto.Computational.OneWayToPRG
import CslibFrontier.Crypto.Computational.SchnorrProtocol
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Crypto.Game.Order
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
  (`δ = fun _ => 0`), exercising both `accepts_schnorrSimulator` and Attack Game 20.4
  indistinguishability.
* **`SpecialHVZK` does not imply `ComputationalSpecialHVZK` (under discrete log).** The protocol
  `sendWitnessFamily F` is perfectly `SpecialHVZK` at every index (`specialHVZK_sendWitness`), yet
  under `F.DiscreteLog setup` it fails computational special HVZK for *every* word simulator
  program, including programs whose output does not decode, and *every* acceptance-error parameter
  `δ` (even `δ = fun _ => ⊤`, without invoking `accepts`), because Attack Game 20.4's
  `indistinguishable` obligation alone forces the simulator to invert discrete logarithms
  (`not_wordComputationalSpecialHVZK_sendWitness`, over the word-simulator definition
  `WordComputationalSpecialHVZK`). Every typed simulator gives such a program
  (`exists_wordComputationalSpecialHVZK`), so `ComputationalSpecialHVZK` fails for every typed `sim`
  (`not_computationalSpecialHVZK_sendWitness`).
* **`ComputationalSpecialHVZK` does not imply `SpecialHVZK` or `EfficientSpecialHVZK` (from any PRG
  or OWF).** For any stretching `PseudorandomGenerator generator length`, the protocol family
  `prgWitnessSigma generator length` commits to `generator seed` when the witness bit is `false` and
  to a uniform `length n`-bit string when the witness bit is `true`. Its simulator samples a
  uniform `length n`-bit commitment, achieving `ComputationalSpecialHVZK` with exact zero acceptance
  error (`computationalSpecialHVZK_prgWitnessSigma`), whereas the `2 ^ n`-element generator image
  covers at most half of `{0, 1} ^ (length n)`, ruling out `SpecialHVZK`, `EfficientSpecialHVZK` for
  every `δ`, and even unbounded statistical transcript simulation below error `1 / 4`
  (`not_specialHVZK_prgWitnessSigma`, `not_efficientSpecialHVZK_prgWitnessSigma`,
  `not_statistical_hvzk_prgWitnessSigma`, `exists_computationalSpecialHVZK_and_not_specialHVZK`).
* **Word-level adversaries.** The word-level Attack Game 20.4 of `main` before the typed games is
  `chvzkExperiment` at word types with the encoded relation `wordRelation`; the generic bound gives
  its statistical producer statement for every word program within `δ` of the encoded perfect
  simulator, as `SimulatorRealizedBy.exists_word` extracts from a typed simulator
  (`advantage_wordChvzkExperiment_le`, `negligible_wordChvzkGame`). A guessing stage written for
  the earlier word layout is PPT on `encCHVZKGuessInput`, which adds only the index.
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
      (fun n => (setup n).map (n, ·)) schnorrGroups.schnorrSimulator (fun _ => 0) :=
  schnorrGroups.computationalSpecialHVZK_schnorr setup

/-! ### Word simulators -/

section WordSimulator

variable {I : Type} {X Y T C Z : I → Type} [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)] {σ : Type}

open Classical in
/-- Attack Game 20.4 at one index with a conversation law that may fail to produce a conversation,
as for a word simulator whose output does not decode: the experiment outputs `false` on failure. -/
noncomputable def optionChvzkExperiment {X' Y' T' C' Z' : Type} (R : X' → Y' → Prop)
    (conv : X' → Y' → PMF (Option (T' × C' × Z')))
    (A : TwoStage Unit (X' × Y') (T' × C' × Z') Bool σ) : Game := do
  let ((x, y), state) ← A.choose ()
  if R x y then
    match ← conv x y with
    | some conversation => A.guess state conversation
    | none => return false
  else
    return false

/-- Decode a word simulator's commitment and response words at index `i` and challenge `c`. -/
noncomputable def decodeWords (enc : Encoding I Y T C Z) (i : I) (c : C i)
    (words : List Bool × List Bool) : Option (T i × C i × Z i) :=
  (Function.partialInv (enc.commitment i) words.1).bind fun t =>
    (Function.partialInv (enc.response i) words.2).map fun z => (t, c, z)

/-- The decoded conversation of a word simulator `program` on `(i, y)`: sample a uniform challenge,
run `program` on the index and the encoded statement and challenge, and decode its words. -/
noncomputable def decodedSimConversation (enc : Encoding I Y T C Z)
    (program : I × List Bool × List Bool → ProbComp (List Bool × List Bool)) (i : I) (y : Y i) :
    PMF (Option (T i × C i × Z i)) :=
  (PMF.uniformOfFintype (C i)).bind fun c =>
    (ProbComp.eval (program (i, enc.statement i y, enc.challenge i c))).map (decodeWords enc i c)

/-- Experiment 1 of Attack Game 20.4 with a word simulator `program`: a run whose simulator output
does not decode outputs `false`. -/
noncomputable def wordChvzkSimGame (R : ∀ i, X i → Y i → Prop) (enc : Encoding I Y T C Z)
    (setup : ℕ → PMF I) (program : I × List Bool × List Bool → ProbComp (List Bool × List Bool))
    (A : CHVZKAdversary I X Y T C Z σ) (n : ℕ) : Game := do
  let i ← setup n
  optionChvzkExperiment (R i) (fun _ y => decodedSimConversation enc program i y) (A n i)

/-- Computational special HVZK with a word simulator `program`, the definition before typed
simulators: `program` is uniform strict PPT on `encSimulatorWordInput`, outputs the words of an
accepting conversation with probability at least `1 - δ i`, and its decoded conversations are
indistinguishable from honest ones (`wordChvzkSimGame`). It admits programs whose output does not
decode, so it is weaker than `ComputationalSpecialHVZK` (`exists_wordComputationalSpecialHVZK`). -/
structure WordComputationalSpecialHVZK (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    (R : ∀ i, X i → Y i → Prop) (enc : Encoding I Y T C Z) (encW : ∀ i, X i ↪ List Bool)
    (setup : ℕ → PMF I) (program : I × List Bool × List Bool → ProbComp (List Bool × List Bool))
    (δ : I → ℝ≥0∞) : Prop where
  /-- The word simulator is uniform strict PPT. -/
  ppt : IsPPTOn (encSimulatorWordInput enc.index) (encPair encBits encBits) program
  /-- The word simulator outputs an encoded accepting conversation with probability at least
  `1 - δ i`. -/
  accepts : ∀ i (y : Y i) (c : C i), 1 - δ i ≤
    (ProbComp.eval (program (i, enc.statement i y, enc.challenge i c))).toOuterMeasure
      {w | ∃ t z, w = (enc.commitment i t, enc.response i z) ∧ (P i).Accepts y t c z}
  /-- Honest and decoded simulated conversations are computationally indistinguishable. -/
  indistinguishable : ∀ {σ : Type} (encσ : σ ↪ List Bool),
    Game.Indistinguishable (chvzkRealGame P R setup (σ := σ))
      (wordChvzkSimGame R enc setup program) (CHVZKAdversary.IsPPT enc encW encσ)

/-- The word program of a typed simulator (`Simulator.IsPPT.exists_word`) satisfies the
word-simulator definition with the same acceptance error: on encoded inputs its words decode to the
typed simulator's conversation. -/
theorem exists_wordComputationalSpecialHVZK
    {P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i)} {R : ∀ i, X i → Y i → Prop}
    {enc : Encoding I Y T C Z} {encW : ∀ i, X i ↪ List Bool} {setup : ℕ → PMF I}
    {sim : Simulator I Y T C Z} {δ : I → ℝ≥0∞}
    (h : ComputationalSpecialHVZK P R enc encW setup sim δ) :
    ∃ program, WordComputationalSpecialHVZK P R enc encW setup program δ := by
  obtain ⟨program, hprog, hword⟩ := h.ppt.exists_word
  have hconv (i : I) (y : Y i) :
      decodedSimConversation enc program i y = (simulatedConversation sim i y).map some := by
    simp only [decodedSimConversation, simulatedConversation, ← hword, ProbComp.liftM_eq_eval,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.map_comp, PMF.pure_map]
    congr 1 with c : 1
    congr 1 with tz : 1
    simp [decodeWords, Function.partialInv_left (enc.commitment i).injective,
      Function.partialInv_left (enc.response i).injective]
  refine ⟨program, hprog, fun i y c => ?_, ?_⟩
  · rw [← hword, PMF.toOuterMeasure_map_apply]
    exact (h.accepts i y c).trans
      (MeasureTheory.measure_mono fun tz htz => ⟨tz.1, tz.2, rfl, htz⟩)
  · intro σ encσ A hA
    have hgame (n : ℕ) :
        wordChvzkSimGame R enc setup program A n = chvzkSimGame R setup sim A n := by
      simp only [wordChvzkSimGame, chvzkSimGame, optionChvzkExperiment, chvzkExperiment, hconv,
        PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]
    simpa only [hgame] using h.indistinguishable encσ A hA

omit [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)] in
/-- A word simulator's decoded commitment is the one its commitment word encodes. -/
theorem commitment_eq_of_decodeWords_eq_some {enc : Encoding I Y T C Z} {i : I} {c : C i}
    {words : List Bool × List Bool} {conv : T i × C i × Z i}
    (h : decodeWords enc i c words = some conv) : enc.commitment i conv.1 = words.1 := by
  simp only [decodeWords, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨t, ht, z, -, rfl⟩ := h
  exact ((enc.commitment i).injective.isPartialInv t words.1).mp ht

end WordSimulator

/-! ### `SpecialHVZK` does not imply `ComputationalSpecialHVZK` -/

section DiscreteLogSeparation

variable {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}

/-- Attack Game 20.4 adversary against `sendWitnessFamily F`: sample `s ← F.sampleExp n d`, submit
the valid discrete-logarithm pair `(α, α • g)` for `α = s mod q` while saving the word of `α`, and
check whether the challenger's commitment has that word. -/
noncomputable def sendWitnessAdversary (F : PrimeOrderGroupFamily) :
    CHVZKAdversary (ℕ × F.Desc) (fun i => ZMod (F.order i.2)) (fun i => F.Carrier i.2)
      (fun i => ZMod (F.order i.2)) (fun _ => Bool) (fun i => ZMod (F.order i.2)) (List Bool) :=
  fun n i =>
    { choose := fun _ => do
        let s ← F.sampleExp n i.2
        let α : ZMod (F.order i.2) := s
        return ((α, α • F.generator i.2), F.encScalar i.2 α)
      guess := fun state conversation => pure (F.encScalar i.2 conversation.1 == state) }

theorem isPPT_sendWitnessAdversary (F : PrimeOrderGroupFamily) :
    CHVZKAdversary.IsPPT (sendWitnessEncoding F) (fun i => F.encScalar i.2) encBits
      (sendWitnessAdversary F) where
  choose := by
    let encIdx := (sendWitnessEncoding F).index
    let encIn := encPair encUnary encIdx
    have hn : ComputableInPolyTime (fun p : ℕ × ℕ × F.Desc => p.1) encIn encUnary := by fun_prop
    have hp2 : ComputableInPolyTime (fun p : ℕ × ℕ × F.Desc => p.2) encIn encIdx := by fun_prop
    have hd : ComputableInPolyTime (fun (⟨_, _, d⟩ : ℕ × ℕ × F.Desc) => d) encIn F.encDesc :=
      (ComputableInPolyTime.snd encUnary F.encDesc).comp hp2
    have hword : IsPPTOn encIn (encPair (encPair encBits encBits) encBits)
        fun (⟨n, _, d⟩ : ℕ × ℕ × F.Desc) => F.sampleExp n d >>= fun s =>
          pure (((s % F.order d).bits, F.smul (d, s, F.encode d (F.generator d))),
            (s % F.order d).bits) := by
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
    refine hword.congr fun ⟨n, m, d⟩ => congrArg ProbComp.eval ?_
    have hx (s : ℕ) : F.encScalar d (s : ZMod (F.order d)) = (s % F.order d).bits := by
      simp only [PrimeOrderGroupFamily.encScalar, Function.Embedding.coeFn_mk, encNat_apply,
        ZMod.val_natCast]
    have hy (s : ℕ) : (sendWitnessEncoding F).statement (m, d)
        ((s : ZMod (F.order d)) • F.generator d) = F.smul (d, s, F.encode d (F.generator d)) := by
      simp only [sendWitnessEncoding, PrimeOrderGroupFamily.encodeEmbedding,
        Function.Embedding.coeFn_mk, F.smul_encode]
    simp only [sendWitnessAdversary, map_bind, map_pure, hx, hy]
  guess := by
    have hg : ComputableInPolyTime (fun g : CHVZKGuessInput (ℕ × F.Desc)
        (fun i => ZMod (F.order i.2)) (fun _ => Bool) (fun i => ZMod (F.order i.2)) (List Bool) =>
          g) (encCHVZKGuessInput (sendWitnessEncoding F) encBits)
          (encCHVZKGuessInput (sendWitnessEncoding F) encBits) := ComputableInPolyTime.id'
    have ht := encCHVZKGuessInput_commitment_polyTime _ _ hg
    have hst := encCHVZKGuessInput_state_polyTime _ _ hg
    have hbeq : ComputableInPolyTime (fun q : List Bool × List Bool => q.1 == q.2)
        (encPair encBits encBits) encBool := by fun_prop
    exact (hbeq.comp (ht.prod hst)).isPPTOn

/-- **Sending the witness is not computationally special HVZK with a word simulator** under the
discrete-logarithm assumption, for *any* word program `program`, including programs whose output
does not decode, and *any* acceptance-error function `δ` (without using the `accepts` field): Attack
Game 20.4 indistinguishability on `(α, α • g)` forces `program` to invert discrete logarithms. -/
theorem not_wordComputationalSpecialHVZK_sendWitness (hDL : F.DiscreteLog setup)
    (program : (ℕ × F.Desc) × List Bool × List Bool → ProbComp (List Bool × List Bool))
    (δ : ℕ × F.Desc → ℝ≥0∞) :
    ¬ WordComputationalSpecialHVZK (sendWitnessFamily F) (dlRel F) (sendWitnessEncoding F)
      (fun i => F.encScalar i.2) (fun n => (setup n).map (n, ·)) program δ := by
  intro h
  have hprog := h.ppt
  let dlAdv : ℕ → F.Desc × List Bool → ProbComp (List Bool) := fun n input => do
    let c ← ProbComp.uniform Bool
    Prod.fst <$> program ((n, input.1), input.2, encBool c)
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
    exact (hprog.preprocess hprep).map (ComputableInPolyTime.fst encBits encBits)
  let A := sendWitnessAdversary F
  let realGame := chvzkRealGame (sendWitnessFamily F) (dlRel F) (fun m => (setup m).map (m, ·)) A
  let simGame := wordChvzkSimGame (dlRel F) (sendWitnessEncoding F) (fun m => (setup m).map (m, ·))
    program A
  have hreal (n : ℕ) : realGame n = PMF.pure true := by
    simp only [realGame, chvzkRealGame, PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def,
      chvzkExperiment, ProbComp.liftM_eq_eval]
    refine (PMF.bind_congr_on_support _ _ _ fun d _ => ?_).trans (PMF.bind_const _ _)
    simp only [A, sendWitnessAdversary, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
    refine (PMF.bind_congr_on_support _ _ _ fun s _ => ?_).trans (PMF.bind_const _ _)
    simp only [↓reduceIte]
    refine (PMF.bind_congr_on_support _ _ _ fun tcz htcz => ?_).trans (PMF.bind_const _ _)
    rw [sendWitnessSigma_conversation_fst (dlRel F (n, d)) _ _ htcz]
    simp only [beq_self_eq_true]
  have hsim_bound (n : ℕ) :
      Game.succProbability (simGame n) ≤
        Game.succProbability (F.discreteLogGame setup dlAdv n) + (1 / 2 : ℝ≥0) ^ n := by
    let simTest (d : F.Desc) (α : ZMod (F.order d)) : Game :=
      optionChvzkExperiment (dlRel F (n, d))
        (fun _ y => decodedSimConversation (sendWitnessEncoding F) program (n, d) y)
        { choose := fun _ => pure ((α, α • F.generator d), F.encScalar d α)
          guess := (A n (n, d)).guess }
    have hsim_eq : simGame n = (setup n).bind fun d =>
        (ProbComp.eval (F.sampleExp n d)).bind fun s => simTest d s := by
      simp only [simGame, wordChvzkSimGame, PMF.monad_bind_eq_bind, PMF.bind_map,
        Function.comp_def]
      refine congrArg _ (funext fun d => ?_)
      simp only [simTest, optionChvzkExperiment, A, sendWitnessAdversary, ProbComp.liftM_eq_eval,
        ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        PMF.bind_bind, PMF.pure_bind]
    let unifGame : Game :=
      (setup n).bind fun d => (PMF.uniformOfFintype (ZMod (F.order d))).bind (simTest d)
    have hadv : Game.advantage (simGame n) unifGame ≤ (1 / 2 : ℝ≥0) ^ n := by
      rw [hsim_eq, one_div_pow]
      exact Game.advantage_bind_le_nnreal (setup n) _ _ fun d =>
        F.advantage_bind_sampleExp_le n d (simTest d)
    have hunif_le : unifGame true ≤ F.discreteLogGame setup dlAdv n true := by
      simp only [unifGame, PrimeOrderGroupFamily.discreteLogGame, PMF.monad_bind_eq_bind,
        PMF.monad_pure_eq_pure]
      refine PMF.bind_apply_mono_on_support _ _ fun d _ =>
        PMF.bind_apply_mono_on_support _ _ fun α _ => ?_
      simp only [simTest, optionChvzkExperiment, decodedSimConversation, dlAdv, A,
        sendWitnessAdversary, ProbComp.liftM_eq_eval, ProbComp.eval_pure, ProbComp.eval_bind,
        ProbComp.eval_map, ProbComp.eval_uniform, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        PMF.pure_bind, PMF.bind_bind, PMF.bind_map, Function.comp_def, ↓reduceIte]
      refine PMF.bind_apply_mono_on_support _ _ fun c _ =>
        PMF.bind_apply_mono_on_support _ _ fun ⟨tw, zw⟩ _ => ?_
      cases hdec : decodeWords (sendWitnessEncoding F) (n, d) c (tw, zw) with
      | none => simp
      | some conv =>
        have htw : F.encScalar d conv.1 = tw := commitment_eq_of_decodeWords_eq_some hdec
        by_cases ht : conv.1 = α
        · have hcast : (ofBits tw : ZMod (F.order d)) = α := by
            rw [← htw, ht]
            change ((ofBits (encNat α.val) : ℕ) : ZMod (F.order d)) = α
            rw [encNat_apply, ofBits, Nat.foldr_bit_bits, ZMod.natCast_zmod_val]
          simp [hcast, ht]
        · have hne : (F.encScalar d conv.1 == F.encScalar d α) = false :=
            beq_false_of_ne fun h => ht ((F.encScalar d).injective h)
          simp [hne]
    calc Game.succProbability (simGame n)
        ≤ Game.succProbability unifGame + (1 / 2 : ℝ≥0) ^ n :=
          Game.succProbability_le_add_of_advantage_le hadv
      _ ≤ Game.succProbability (F.discreteLogGame setup dlAdv n) + (1 / 2 : ℝ≥0) ^ n :=
          add_le_add (Game.succProbability_mono hunif_le) le_rfl
  have h1_le (n : ℕ) : (1 : ℝ≥0) ≤ Game.advantage (realGame n) (simGame n) +
      ((1 / 2 : ℝ≥0) ^ n + Game.succProbability (F.discreteLogGame setup dlAdv n)) := by
    have hreal_succ : Game.succProbability (realGame n) = 1 := by
      simp [hreal n, Game.succProbability]
    calc (1 : ℝ≥0) = Game.succProbability (realGame n) := hreal_succ.symm
      _ ≤ Game.succProbability (simGame n) + Game.advantage (realGame n) (simGame n) :=
          Game.succProbability_le_add_of_advantage_le le_rfl
      _ ≤ _ := by
          rw [add_comm (Game.advantage _ _)]
          exact add_le_add ((hsim_bound n).trans_eq (add_comm _ _)) le_rfl
  have hnegl := (h.indistinguishable encBits A (isPPT_sendWitnessAdversary F)).add
    ((negligible_geometric (ratio := 1 / 2) (by norm_num)).add (hDL dlAdv hdlAdv))
  exact not_negligible_const (c := 1) one_ne_zero (negligible_of_le hnegl h1_le)

/-- **Sending the witness is not computationally special HVZK** under the discrete-logarithm
assumption, for *any* typed simulator `sim` and *any* acceptance-error function `δ`: the word
program of `sim` would contradict `not_wordComputationalSpecialHVZK_sendWitness`. -/
theorem not_computationalSpecialHVZK_sendWitness (hDL : F.DiscreteLog setup)
    (sim : Simulator (ℕ × F.Desc) (fun i => F.Carrier i.2) (fun i => ZMod (F.order i.2))
      (fun _ => Bool) (fun i => ZMod (F.order i.2)))
    (δ : ℕ × F.Desc → ℝ≥0∞) :
    ¬ ComputationalSpecialHVZK (sendWitnessFamily F) (dlRel F) (sendWitnessEncoding F)
      (fun i => F.encScalar i.2) (fun n => (setup n).map (n, ·)) sim δ := fun h =>
  let ⟨program, hword⟩ := exists_wordComputationalSpecialHVZK h
  not_wordComputationalSpecialHVZK_sendWitness hDL program δ hword

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
`length n`-bit commitment, and return it with the trivial response. -/
noncomputable def prgWitnessSim (length : ℕ → ℕ) :
    Simulator ℕ (fun _ => Unit) (fun _ => List Bool) (fun _ => Bool) (fun _ => Unit) :=
  fun n _ _ => do
    let t ← BitString.sampleList (length n)
    return (t, ())

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
    have hsample : IsPPTOn encIn encBits (fun p => BitString.sampleList (length p.1)) := by ppt
    refine Simulator.IsPPT.of_word (hsample.bind_with (second := fun _ t => pure (t, encUnit ()))
      ((ComputableInPolyTime.snd encIn encBits).prod
        (ComputableInPolyTime.const (encUnit ()))).isPPTOn) fun n _ _ => ?_
    rw [← ProbComp.eval_map]
    simp only [prgWitnessSim, map_bind, map_pure]
    rfl
  accepts := by
    rintro n ⟨⟩ c
    have heq : (ProbComp.eval (prgWitnessSim length n () c)).toOuterMeasure
        {tz | (prgWitnessSigma generator length n).Accepts () tz.1 c tz.2} = 1 := by
      simp only [prgWitnessSim, ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure]
      rw [show (fun a : List Bool => PMF.pure (a, ())) = PMF.pure ∘ fun a => (a, ()) from rfl,
        PMF.bind_pure_comp, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_eq_one_iff]
      intro t ht
      simp [SigmaProtocol.Accepts, prgWitnessSigma, BitString.length_of_mem_support_uniformList ht]
    simpa only [tsub_zero] using heq.ge
  indistinguishable {σ} encσ adversary hadv := by
    have hlen := hPRG.polyTime_length
    -- The PRG distinguisher runs the adversary with the challenge word as the commitment when the
    -- adversary's witness bit is `false`, and with a fresh uniform commitment when it is `true`.
    let D : Distinguisher := fun n word => do
      let ((x, _), state) ← (adversary n n).choose ()
      let t ← if x then BitString.sampleList (length n) else pure word
      let c ← ProbComp.uniform Bool
      (adversary n n).guess state (t, c, ())
    have hD : Probability.IsPPT encBool D := by
      let encD := encPair encUnary encBits
      let encW := encPair (encPair encBits encBits) encσ
      let encT := encPair encD encW
      have hn : ComputableInPolyTime (fun p : ℕ × List Bool => p.1) encD encUnary := by fun_prop
      have hchoose : IsPPTOn encD encW fun p =>
          (fun out => ((encBool out.1.1, encUnit out.1.2), out.2)) <$>
            (adversary p.1 p.1).choose () :=
        hadv.choose.preprocess (hn.prod hn)
      have hlen' : ComputableInPolyTime
          (fun q : (ℕ × List Bool) × (List Bool × List Bool) × σ => length q.1.1) encT encUnary :=
        hlen.comp (by fun_prop)
      -- The guessing stage on the run's data: the security parameter, the saved state, the
      -- commitment word and the challenge bit.
      have hguess : IsPPTOn (encPair (encPair encT encBits) encBool) encBool
          (fun q : (((ℕ × List Bool) × (List Bool × List Bool) × σ) × List Bool) × Bool =>
            (adversary q.1.1.1.1 q.1.1.1.1).guess q.1.1.2.2 (q.1.2, q.2, ())) := by
        refine hadv.guess.preprocess (prepare :=
          fun q : (((ℕ × List Bool) × (List Bool × List Bool) × σ) × List Bool) × Bool =>
            ⟨q.1.1.1.1, q.1.1.2.2, q.1.1.1.1, q.1.2, q.2, ()⟩) ?_
        exact encCHVZKGuessInput_mk_polyTime _ _ (by fun_prop) (by fun_prop) (by fun_prop)
          (by simpa only [prgWitnessEncoding] using (by fun_prop : ComputableInPolyTime
            (fun q : (((ℕ × List Bool) × (List Bool × List Bool) × σ) × List Bool) × Bool =>
              encBits q.1.2) _ encBits))
          (by simpa only [prgWitnessEncoding] using (by fun_prop : ComputableInPolyTime
            (fun q : (((ℕ × List Bool) × (List Bool × List Bool) × σ) × List Bool) × Bool =>
              encBool q.2) _ encBits))
          (by simpa only [prgWitnessEncoding] using (ComputableInPolyTime.const (encUnit ()) :
            ComputableInPolyTime
              (fun _ : (((ℕ × List Bool) × (List Bool × List Bool) × σ) × List Bool) × Bool =>
                encUnit ()) _ encBits))
      -- `D` on encoded choices: branch on the witness word.
      have hrun : IsPPTOn encD encBool fun p =>
          ((fun out => ((encBool out.1.1, encUnit out.1.2), out.2)) <$>
            (adversary p.1 p.1).choose ()) >>= fun out =>
          (if out.1.1 == encBool true then BitString.sampleList (length p.1) else pure p.2) >>=
            fun t => ProbComp.uniform Bool >>= fun c =>
              (adversary p.1 p.1).guess out.2 (t, c, ()) := by
        refine hchoose.bind_with ?_
        refine IsPPTOn.bind_with (left := encBits) ?_ ?_
        · exact IsPPTOn.cond' (by fun_prop) (by ppt) (by fun_prop)
        refine IsPPTOn.bind_with (left := encBool) (by ppt) ?_
        exact hguess
      refine hrun.congr fun ⟨n, word⟩ => congrArg ProbComp.eval ?_
      simp only [D, bind_map_left]
      refine bind_congr fun ⟨⟨x, u⟩, state⟩ => ?_
      cases x <;> rfl
    have hgame (n : ℕ) :
        Game.advantage
          (chvzkRealGame (prgWitnessSigma generator length) (fun _ _ _ => True) PMF.pure
            adversary n)
          (chvzkSimGame (fun _ _ _ => True) PMF.pure (prgWitnessSim length) adversary n) =
        Game.advantage
          (distinguishingGame (generatorEnsemble generator n) (D n))
          (distinguishingGame (BitString.uniformList (length n)) (D n)) := by
      have hreal_eq :
          chvzkRealGame (prgWitnessSigma generator length) (fun _ _ _ => True) PMF.pure
            adversary n = distinguishingGame (generatorEnsemble generator n) (D n) := by
        simp only [chvzkRealGame, chvzkExperiment, ProbComp.liftM_eq_eval,
          distinguishingGame_eq_bind, D, PMF.monad_bind_eq_bind, PMF.pure_bind, ProbComp.eval_bind]
        rw [PMF.bind_comm (generatorEnsemble generator n)]
        refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨x, ⟨⟩⟩, state⟩ _ => ?_
        cases x
        · simp only [↓reduceIte, SigmaProtocol.conversation, prgWitnessSigma, Bool.false_eq_true,
            ProbComp.eval_pure, ProbComp.eval_bind, ProbComp.eval_uniform, PMF.monad_bind_eq_bind,
            PMF.monad_pure_eq_pure, PMF.bind_map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
        · simp only [↓reduceIte, SigmaProtocol.conversation, prgWitnessSigma,
            ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_uniform,
            PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map, PMF.bind_bind,
            PMF.pure_bind, PMF.bind_const, Function.comp_def]
      have hconv : simulatedConversation (prgWitnessSim length) n () =
          (PMF.uniformOfFintype Bool).bind fun c =>
            (BitString.uniformList (length n)).bind fun t => PMF.pure (t, c, ()) := by
        simp only [simulatedConversation, prgWitnessSim, ProbComp.liftM_eq_eval, ProbComp.eval_bind,
          BitString.eval_sampleList, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
          PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
      have hsim_eq :
          chvzkSimGame (fun _ _ _ => True) PMF.pure (prgWitnessSim length) adversary n =
            distinguishingGame (BitString.uniformList (length n)) (D n) := by
        simp only [chvzkSimGame, chvzkExperiment, hconv, ProbComp.liftM_eq_eval,
          distinguishingGame_eq_bind, D, PMF.monad_bind_eq_bind, PMF.pure_bind, ProbComp.eval_bind]
        rw [PMF.bind_comm (BitString.uniformList (length n))]
        refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨x, ⟨⟩⟩, state⟩ _ => ?_
        cases x
        · simp only [↓reduceIte, Bool.false_eq_true, ProbComp.eval_pure, ProbComp.eval_bind,
            ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
          rw [PMF.bind_comm (PMF.uniformOfFintype Bool)]
        · simp only [↓reduceIte, ProbComp.eval_bind, BitString.eval_sampleList,
            ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind, PMF.bind_const]
          rw [PMF.bind_comm (PMF.uniformOfFintype Bool)]
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
      (sim : Simulator ℕ (fun _ => Unit) (fun _ => List Bool) (fun _ => Bool) (fun _ => Unit)),
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

/-! ### Word-level adversaries -/

section WordLevel

variable {I : Type} {X Y T C Z : I → Type}
  {P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i)} [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
  {R : ∀ i, X i → Y i → Prop} {enc : Encoding I Y T C Z} {encW : ∀ i, X i ↪ List Bool}
  {simulate : ∀ i, Y i → C i → PMF (T i × Z i)}
  {program : I × List Bool × List Bool → ProbComp (List Bool × List Bool)} {δ : I → ℝ≥0∞}

variable (R enc encW) in
/-- The relation of the word-level Attack Game 20.4 on `main` before the typed games: a pair of
words is valid when it encodes a pair in `R i`. -/
def wordRelation (i : I) (xw yw : List Bool) : Prop :=
  ∃ p : X i × Y i, encW i p.1 = xw ∧ enc.statement i p.2 = yw ∧ R i p.1 p.2

open Classical in
variable (P R enc encW) in
/-- The honest encoded conversation on a valid pair of words, decoded by choice. The experiment
samples it only on valid pairs; elsewhere it is an arbitrary fixed point mass. -/
noncomputable def wordRealConversation (i : I) (xw yw : List Bool) :
    PMF (List Bool × List Bool × List Bool) :=
  if h : wordRelation R enc encW i xw yw then
    ((P i).conversation h.choose.1 h.choose.2).map fun tcz =>
      (enc.commitment i tcz.1, enc.challenge i tcz.2.1, enc.response i tcz.2.2)
  else
    PMF.pure ([], [], [])

variable (enc program) in
/-- The simulated encoded conversation on a statement word: the word program's commitment and
response words, with the encoded uniform challenge. -/
noncomputable def wordSimConversation (i : I) (yw : List Bool) :
    PMF (List Bool × List Bool × List Bool) :=
  (PMF.uniformOfFintype (C i)).bind fun c =>
    (ProbComp.eval (program (i, yw, enc.challenge i c))).map fun words =>
      (words.1, enc.challenge i c, words.2)

/-- **The word-level Attack Game 20.4 bound is a corollary.** At word types, with the encoded
relation `wordRelation`, the word-level games of `main` before the typed games are
`chvzkExperiment` with the conversation laws `wordRealConversation` and `wordSimConversation`. A
word program within `δ i ≤ ε` of a perfect special HVZK simulator on encodings (as
`SimulatorRealizedBy.exists_word` extracts from an efficient typed simulator) bounds their advantage
by `ε` against every word-level adversary, by the generic `advantage_chvzkExperiment_le`. -/
theorem advantage_wordChvzkExperiment_le (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (h : WordSimulatorRealizedBy enc simulate program δ)
    (i : I) {ε : ℝ≥0} (hδ : δ i ≤ ε) {σ : Type}
    (A : TwoStage Unit (List Bool × List Bool) (List Bool × List Bool × List Bool) Bool σ) :
    Game.advantage
        (chvzkExperiment (wordRelation R enc encW i) (wordRealConversation P R enc encW i) A)
        (chvzkExperiment (wordRelation R enc encW i)
          (fun _ yw => wordSimConversation enc program i yw) A) ≤ ε := by
  refine advantage_chvzkExperiment_le (fun xw yw hp => ?_) A
  simp only [wordRealConversation, hp, ↓reduceDIte]
  let out (c : C i) (words : List Bool × List Bool) : List Bool × List Bool × List Bool :=
    (words.1, enc.challenge i c, words.2)
  have henc : ((P i).conversation hp.choose.1 hp.choose.2).map (fun tcz =>
        (enc.commitment i tcz.1, enc.challenge i tcz.2.1, enc.response i tcz.2.2)) =
      (PMF.uniformOfFintype (C i)).bind fun c =>
        ((simulate i hp.choose.2 c).map (Prod.map (enc.commitment i) (enc.response i))).map
          (out c) := by
    rw [(hS i).conversation_eq hp.choose_spec.2.2]
    simp only [pmf_norm]
    rfl
  have hclose := CloseTo.bind_right (PMF.uniformOfFintype (C i)) fun c _ =>
    (h i hp.choose.2 c).map (out c)
  rw [← henc, hp.choose_spec.2.1] at hclose
  exact hclose.mono hδ

/-- The family form: when `δ` is bounded by a negligible function along `setup`, every word-level
adversary family, PPT or not, has negligible advantage in the word-level games. -/
theorem negligible_wordChvzkGame (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (h : WordSimulatorRealizedBy enc simulate program δ)
    {setup : ℕ → PMF I}
    (hnegl : ∃ ε : ℕ → ℝ≥0, Negligible ε ∧ ∀ n, ∀ i ∈ (setup n).support, δ i ≤ ε n) {σ : Type}
    (A : ℕ → I →
      TwoStage Unit (List Bool × List Bool) (List Bool × List Bool × List Bool) Bool σ) :
    Negligible fun n => Game.advantage
      ((setup n).bind fun i =>
        chvzkExperiment (wordRelation R enc encW i) (wordRealConversation P R enc encW i) (A n i))
      ((setup n).bind fun i =>
        chvzkExperiment (wordRelation R enc encW i)
          (fun _ yw => wordSimConversation enc program i yw) (A n i)) := by
  obtain ⟨ε, hε, hle⟩ := hnegl
  exact negligible_of_le hε fun n => Game.advantage_bind_le_of_support (setup n) _ _ fun i hi =>
    advantage_wordChvzkExperiment_le hS h i (hle n i hi) (A n i)

/-- A guessing stage written for the word layout of `main` before the typed games (unary security
parameter, state word, commitment, challenge and response words) gives a typed guessing stage that
is PPT on `encCHVZKGuessInput`: the typed layout only adds the index, which it may ignore. -/
example (guess : ℕ → List Bool → List Bool × List Bool × List Bool → ProbComp Bool)
    (hguess : IsPPTOn
      (encPair encUnary (encPair encBits (encPair encBits (encPair encBits encBits)))) encBool
      fun ⟨n, state, conv⟩ => guess n state conv) :
    IsPPTOn (encCHVZKGuessInput enc encBits) encBool fun g =>
      guess g.secParam g.state (enc.commitment g.index g.commitment,
        enc.challenge g.index g.challenge, enc.response g.index g.response) := by
  have hg : ComputableInPolyTime (fun g : CHVZKGuessInput I T C Z (List Bool) => g)
      (encCHVZKGuessInput enc encBits) (encCHVZKGuessInput enc encBits) := ComputableInPolyTime.id'
  exact hguess.preprocess ((encCHVZKGuessInput_secParam_polyTime _ _ hg).prod
    ((encCHVZKGuessInput_state_polyTime _ _ hg).prod
      ((encCHVZKGuessInput_commitment_polyTime _ _ hg).prod
        ((encCHVZKGuessInput_challenge_polyTime _ _ hg).prod
          (encCHVZKGuessInput_response_polyTime _ _ hg)))))

end WordLevel

end CslibFrontierTests.ComputationalSpecialHVZK

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Rompel
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Tactic.PPT

/-!
# Tests for Rompel target collision-resistant hashing and digital signatures

Checks concrete schedule identities, unconditional pigeonhole step-collision extraction for
`rompelCandidateEval` (`exists_rompelCascadeInput_collision`), plain `IsPPT` certification and
concrete loss bounds for `rompelCompressionInverter` and `rompelCompression`, unrestricted digest
widths for `rompelHash`, behavioral separation between `WordSignatureScheme.EUFCMA` and
`SignatureScheme.EUFCMA` (`leakNonNScheme`), concrete multi-length verification for
`TCRSignature.wordScheme` and adaptive multi-query replay for `TCRSignature.replayCfg` /
`TCRSignature.queryOf`, and the full signature sufficiency and equivalence endpoints in
`CslibFrontier.Crypto.Computational.Rompel` (`OneWay.exists_indexedEUFCMA_two`,
`OneWay.exists_counterEUFCMA_two`, `OneWay.exists_eufCMA`, `OneWay.exists_wordEUFCMA`,
`exists_oneWay_iff_exists_signature`, `exists_oneTimeSignature_iff_exists_signature`,
`exists_oneWay_iff_exists_wordSignature`, `exists_oneTimeSignature_iff_exists_wordSignature`).
-/

namespace CslibFrontierTests.Crypto.Rompel

open Cslib Cslib.Crypto Cslib.Probability
open _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapePTM
  _root_.Turing.MultiTapeTM
open scoped NNReal

/-! ### 1. Schedule, block-width, and key-width checks -/

example (G : ShrinkingCollisionGrid) (n : ℕ) :
    1 ≤ rompelCascadeSteps G n ∧
      G.outLen n + rompelCascadeSteps G n = 2 * rompelBlockLen G n ∧
      n ≤ rompelBlockLen G n :=
  ⟨rompelCascadeSteps_pos G n, outLen_add_rompelCascadeSteps G n, le_rompelBlockLen G n⟩

/-- Concrete parameter check when `G.gridCount n = 2` and `G.outLen n = 3` (`G.inLen n = 4`):
each candidate folds `3 * 3 = 9` shifted `4 → 3` steps, compressing `12` bits to `3` bits, and
concatenating both candidates yields a `12 → 6` `KeyedCompressionFamily` with `36`-bit key. -/
theorem rompel_schedule_two_three (G : ShrinkingCollisionGrid) {n : ℕ}
    (hk : G.gridCount n = 2) (hout : G.outLen n = 3) :
    rompelCascadeSteps G n = 9 ∧ rompelBlockLen G n = 6 ∧ rompelKeyLen G n = 36 := by
  have hin : G.inLen n = 4 := by
    have h1 := G.outLen_add_one n
    omega
  simp only [rompelCascadeSteps, rompelBlockLen, rompelKeyLen, hk, hout, hin]
  decide

example (G : ShrinkingCollisionGrid) (n : ℕ) (K msg : List Bool)
    (hK : K.length = (rompelHash G).keyLen n) :
    ((rompelHash G).eval n K msg).length = rompelBlockLen G n :=
  (rompelHash G).length_eq n K msg hK

/-! ### 2. Unconditional pigeonhole non-vacuity of `exists_rompelCascadeInput_collision` -/

/-- For every `ShrinkingCollisionGrid` `G`, security parameter `n`, candidate `q`, and key `K`,
strict compression `G.outLen n < 2 * rompelBlockLen G n` guarantees distinct
`2 * rompelBlockLen G n`-bit inputs `x₀ ≠ x₁` colliding under `rompelCandidateEval G n q K`, from
which `exists_rompelCascadeInput_collision` extracts an in-range step collision
`i < rompelCascadeSteps G n` under `rompelShiftedStep`. -/
theorem exists_rompelCandidateEval_step_collision (G : ShrinkingCollisionGrid)
    (n q : ℕ) (K : List Bool) :
    ∃ (x₀ x₁ : List Bool) (i : ℕ),
      x₀.length = 2 * rompelBlockLen G n ∧
      x₁.length = 2 * rompelBlockLen G n ∧
      x₀ ≠ x₁ ∧
      i < rompelCascadeSteps G n ∧
      rompelCascadeInput G n q i K x₀ ≠ rompelCascadeInput G n q i K x₁ ∧
      rompelShiftedStep G n q (BitString.listRow (G.inLen n) i K)
          (rompelCascadeInput G n q i K x₀) =
        rompelShiftedStep G n q (BitString.listRow (G.inLen n) i K)
          (rompelCascadeInput G n q i K x₁) := by
  let M := 2 * rompelBlockLen G n
  let L := G.outLen n
  have hlt : L < M := by
    have hpos := rompelCascadeSteps_pos G n
    have hsum := outLen_add_rompelCascadeSteps G n
    omega
  let evalFin : BitString M → BitString L :=
    fun b => BitString.ofList L (rompelCandidateEval G n q K (List.ofFn b))
  have hcard : Fintype.card (BitString L) < Fintype.card (BitString M) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) hlt
  obtain ⟨b₀, b₁, hb_ne, hmap⟩ := Fintype.exists_ne_map_eq_of_card_lt evalFin hcard
  let x₀ := List.ofFn b₀
  let x₁ := List.ofFn b₁
  have hx₀ : x₀.length = M := List.length_ofFn
  have hx₁ : x₁.length = M := List.length_ofFn
  have hne : x₀ ≠ x₁ := fun h => hb_ne (List.ofFn_injective h)
  have hcol : rompelCandidateEval G n q K x₀ = rompelCandidateEval G n q K x₁ := by
    rw [← BitString.ofFn_ofList (length_rompelCandidateEval G n q K x₀),
      ← BitString.ofFn_ofList (length_rompelCandidateEval G n q K x₁)]
    exact congrArg List.ofFn hmap
  obtain ⟨i, hi, hw_ne, hw_col⟩ := exists_rompelCascadeInput_collision G hx₀ hx₁ hne hcol
  exact ⟨x₀, x₁, i, hx₀, hx₁, hne, hi, hw_ne, hw_col⟩

/-! ### 3. Concrete strict-PPT adversary and `rompelCompressionInverter` checks -/

/-- Explicit two-stage strict-PPT `TargetCollisionFinder` against `rompelCompression G`: Stage 1
commits to `0^{2 * rompelBlockLen G n}` and Stage 2 outputs `1 0^{2 * rompelBlockLen G n - 1}`. -/
def zeroFlipFinder (G : ShrinkingCollisionGrid) : TargetCollisionFinder where
  choose n := pure (List.replicate (2 * rompelBlockLen G n) false, [])
  find n _ _ := pure ([true] ++ List.replicate (2 * rompelBlockLen G n - 1) false)

theorem isPPT_zeroFlipFinder (G : ShrinkingCollisionGrid) : (zeroFlipFinder G).IsPPT where
  choose := by
    dsimp only [zeroFlipFinder]
    ppt
  find := by
    dsimp only [zeroFlipFinder]
    ppt

example (G : ShrinkingCollisionGrid) :
    IsPPT encBits (rompelCompressionInverter G (zeroFlipFinder G)) :=
  isPPT_rompelCompressionInverter G (isPPT_zeroFlipFinder G)

example (G : ShrinkingCollisionGrid) (n : ℕ) :
    Game.succProbability
      (ProbComp.eval
        (targetCollisionGame (rompelCompression G).keyLen (rompelCompression G).eval
          (rompelCompression G).validInput (zeroFlipFinder G) n)) ≤
      (dyadicSize (G.gridCount n) * dyadicSize (rompelCascadeSteps G n) : ℝ≥0) *
        Game.succProbability
          (ProbComp.eval
            (randomCollisionGame (fun k => G.evalGrid k 0) G.inLen
              (rompelCompressionInverter G (zeroFlipFinder G)) n)) :=
  succProbability_targetCollisionGame_rompelCompression_le G (zeroFlipFinder G) (G.gridCount_pos n)

/-! ### 4. Target collision-resistant hashing and Rompel signature endpoints -/

example (G : ShrinkingCollisionGrid) :
    (rompelCompression G).TargetCollisionResistant ∧ (rompelHash G).TargetCollisionResistant :=
  ⟨G.targetCollisionResistant_rompelCompression, G.targetCollisionResistant_rompelHash⟩

example {f : List Bool → List Bool} (hf : OneWay f) :
    (∃ C : KeyedCompressionFamily, C.TargetCollisionResistant) ∧
      ∃ H : KeyedHashFamily, H.TargetCollisionResistant :=
  ⟨hf.exists_targetCollisionResistant_keyedCompressionFamily,
    hf.exists_targetCollisionResistant_keyedHashFamily⟩

example {f : List Bool → List Bool} (hf : OneWay f) :
    (∃ S : IndexedSignatureScheme, (∀ n, S.capacity n = 2) ∧ S.IndexedEUFCMA) ∧
      ∃ S : IndexedSignatureScheme, (∀ n, S.capacity n = 2) ∧ S.CounterEUFCMA :=
  ⟨hf.exists_indexedEUFCMA_two, hf.exists_counterEUFCMA_two⟩

example {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ S : SignatureScheme, S.EUFCMA :=
  hf.exists_eufCMA

example : (∃ f, OneWay f) ↔ ∃ S : SignatureScheme, S.EUFCMA :=
  exists_oneWay_iff_exists_signature

example : (∃ S : SignatureScheme, S.OneTimeEUFCMA) ↔ ∃ S : SignatureScheme, S.EUFCMA :=
  exists_oneTimeSignature_iff_exists_signature

/-- Converse non-vacuity check: if no uniform `OneWay` function exists, no `SignatureScheme` can
satisfy `EUFCMA`. -/
theorem not_exists_eufCMA_of_forall_not_oneWay (hno : ∀ f, ¬ OneWay f)
    (S : SignatureScheme) : ¬ S.EUFCMA := by
  intro hS
  obtain ⟨f, hf⟩ := exists_oneWay_iff_exists_signature.mpr ⟨S, hS⟩
  exact hno f hf

/-! ### 5. Separation between `WordSignatureScheme.EUFCMA` and `SignatureScheme.EUFCMA` -/

/-- Wrap any `SignatureScheme` `S` into a `WordSignatureScheme` that tags `n` into `pk`, delegates
`n`-bit verification to `S.verify`, and accepts every signature on messages of length `≠ n`. -/
noncomputable def leakNonNScheme (S : SignatureScheme) : WordSignatureScheme where
  keyGen n := (fun keys => (encPair encUnary encBits (n, keys.1), keys.2)) <$> S.keyGen n
  sign := S.sign
  verify pk msg sig :=
    let parsed := TCRSignature.keyDecoder.decode pk
    if msg.length == parsed.1 then S.verify parsed.2 msg sig else true
  keyGen_ppt := by
    let KIn := ℕ × (List Bool × List Bool)
    let encKIn : KIn ↪ List Bool := encPair encUnary (encPair encBits encBits)
    have hpost : ComputableInPolyTime
        (fun q : KIn => (encPair encUnary encBits (q.1, q.2.1), q.2.2))
        encKIn (encPair encBits encBits) := by
      have henc : ComputableInPolyTime (encPair encUnary encBits)
          (encPair encUnary encBits) encBits := .of_eq fun _ => rfl
      have hqN := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
      have hqKeys := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
      have hfst := (hqN.prod hqKeys.fst').trans henc
      exact (hfst.prod hqKeys.snd').of_enc_eq fun _ => rfl
    exact S.keyGen_ppt.map_with
      (f := fun n keys => (encPair encUnary encBits (n, keys.1), keys.2)) hpost
  sign_ppt := S.sign_ppt
  verify_polyTime := by
    let VIn := List Bool × List Bool × List Bool
    let encVIn : VIn ↪ List Bool := encPair encBits (encPair encBits encBits)
    have hpk : ComputableInPolyTime (fun q : VIn => q.1) encVIn encBits :=
      ComputableInPolyTime.fst _ _
    have hmsg : ComputableInPolyTime (fun q : VIn => q.2.1) encVIn encBits :=
      (ComputableInPolyTime.snd _ _).fst'
    have hsig : ComputableInPolyTime (fun q : VIn => q.2.2) encVIn encBits :=
      (ComputableInPolyTime.snd _ _).snd'
    have hparsed := hpk.trans TCRSignature.keyDecoder.computableInPolyTime
    have hmsgLen := ComputableInPolyTime.length_bits.comp hmsg
    have hcond := ComputableInPolyTime.unary_beq' hmsgLen hparsed.fst'
    have hyes := S.verify_polyTime.comp (hparsed.snd'.prod (hmsg.prod hsig))
    have hno : ComputableInPolyTime (fun _ : VIn => true) encVIn encBool := .const true
    exact (hcond.ite hyes hno).of_enc_eq fun _ => rfl
  verify_sign n pk sk hkeys msg sig hsig := by
    simp only [ProbComp.eval_map, PMF.mem_support_map_iff] at hkeys
    obtain ⟨⟨innerPk, innerSk⟩, hinner, hEq⟩ := hkeys
    rcases Prod.mk.inj hEq.symm with ⟨rfl, rfl⟩
    simp only [TCRSignature.keyDecoder.decode_enc]
    by_cases hlen : msg.length = n
    · simp only [hlen, beq_self_eq_true, ↓reduceIte]
      exact S.verify_sign n (innerPk, sk) hinner msg hlen sig hsig
    · have hbeq : (msg.length == n) = false := beq_eq_false_iff_ne.mpr hlen
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]

/-- Zero-query strict oracle-PPT forger outputting the `(n + 1)`-bit message `0^{n+1}` and empty
signature `[]`. -/
def longMsgForger : Forger :=
  fun n _ => pure (List.replicate (n + 1) false, [])

theorem isOraclePPT_longMsgForger : IsOraclePPT (encPair encBits encBits) longMsgForger := by
  apply IsOraclePPTOn.isOraclePPT
  have hn1 := (ComputableInPolyTime.fst encUnary encBits).unary_add' (.const 1)
  have hmsg := hn1.trans (ComputableInPolyTime.bitsReplicate false)
  exact ((hmsg.prod (.const [])).of_enc_eq fun _ => rfl).isOraclePPTOn

/-- `longMsgForger` wins `(leakNonNScheme S).eufCmaGame` with probability `1` at every `n` without
any signing query, yet wins `(leakNonNScheme S).toSignatureScheme.eufCmaGame` with probability `0`
because `(n + 1 == n) = false`. -/
theorem succProbability_leakNonNScheme_longMsgForger (S : SignatureScheme) (n : ℕ) :
    Game.succProbability (ProbComp.eval ((leakNonNScheme S).eufCmaGame longMsgForger n)) = 1 ∧
      Game.succProbability
        (ProbComp.eval ((leakNonNScheme S).toSignatureScheme.eufCmaGame longMsgForger n)) = 0 := by
  have hne : (List.replicate (n + 1) false).length ≠ n := by simp
  have hbeq : ((List.replicate (n + 1) false).length == n) = false :=
    beq_eq_false_iff_ne.mpr hne
  constructor
  · have heval : ProbComp.eval ((leakNonNScheme S).eufCmaGame longMsgForger n) = PMF.pure true := by
      simp only [WordSignatureScheme.eufCmaGame, leakNonNScheme, longMsgForger,
        OracleComp.interpret_pure, StateT.run_pure, ProbComp.eval_bind, ProbComp.eval_map,
        ProbComp.eval_pure, PMF.bind_map, PMF.pure_bind, Function.comp_def, List.contains_nil,
        Bool.not_false, Bool.true_and, TCRSignature.keyDecoder.decode_enc, hbeq,
        Bool.false_eq_true, ↓reduceIte, PMF.bind_const]
    rw [heval]
    simp [Game.succProbability]
  · have heval :
        ProbComp.eval ((leakNonNScheme S).toSignatureScheme.eufCmaGame longMsgForger n) =
          PMF.pure false := by
      simp only [SignatureScheme.eufCmaGame, WordSignatureScheme.toSignatureScheme_keyGen,
        WordSignatureScheme.toSignatureScheme_signingOracle,
        WordSignatureScheme.toSignatureScheme_verify, leakNonNScheme, longMsgForger,
        OracleComp.interpret_pure, StateT.run_pure, ProbComp.eval_bind, ProbComp.eval_map,
        ProbComp.eval_pure, PMF.pure_bind, hbeq, Bool.false_and, PMF.bind_const]
    rw [heval]
    simp [Game.succProbability]

theorem not_eufCMA_leakNonNScheme (S : SignatureScheme) : ¬ (leakNonNScheme S).EUFCMA := by
  intro hsec
  have hneg := hsec.negligible longMsgForger isOraclePPT_longMsgForger
  have hone : ∀ n, Game.succProbability
      (ProbComp.eval ((leakNonNScheme S).eufCmaGame longMsgForger n)) = 1 :=
    fun n => (succProbability_leakNonNScheme_longMsgForger S n).1
  exact not_negligible_const (one_ne_zero : (1 : ℝ≥0) ≠ 0) (by simpa only [hone] using hneg)

/-- Whenever `S` is `SignatureScheme.EUFCMA`, `(leakNonNScheme S).toSignatureScheme` is also
`SignatureScheme.EUFCMA`, separating `WordSignatureScheme.EUFCMA` from `SignatureScheme.EUFCMA`. -/
theorem eufCMA_toSignatureScheme_leakNonNScheme {S : SignatureScheme} (hS : S.EUFCMA) :
    (leakNonNScheme S).toSignatureScheme.EUFCMA := by
  apply SignatureScheme.EUFCMA.of_negligible
  intro adversary hadversary
  let wrapped : Forger := fun n pk => adversary n (encPair encUnary encBits (n, pk))
  have hwrapped : IsOraclePPT (encPair encBits encBits) wrapped := by
    apply IsOraclePPTOn.isOraclePPT
    have henc : ComputableInPolyTime (encPair encUnary encBits)
        (encPair encUnary encBits) encBits := .of_eq fun _ => rfl
    have hprep : ComputableInPolyTime
        (fun p : ℕ × List Bool => (p.1, encPair encUnary encBits (p.1, p.2)))
        (encPair encUnary encBits) (encPair encUnary encBits) :=
      (ComputableInPolyTime.fst _ _).prod henc
    exact hadversary.on.preprocess' hprep
  have heq : ∀ n,
      ProbComp.eval ((leakNonNScheme S).toSignatureScheme.eufCmaGame adversary n) =
        ProbComp.eval (S.eufCmaGame wrapped n) := by
    intro n
    simp only [SignatureScheme.eufCmaGame, WordSignatureScheme.toSignatureScheme_keyGen,
      WordSignatureScheme.toSignatureScheme_signingOracle,
      WordSignatureScheme.toSignatureScheme_verify, leakNonNScheme, wrapped, ProbComp.eval_bind,
      ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_map, Function.comp_def]
    congr 1 with keys : 1
    congr 1 with out : 1
    simp only [TCRSignature.keyDecoder.decode_enc]
    cases out.1.1.length == n <;> simp
  simpa only [heq] using hS.negligible wrapped hwrapped

/-- Assuming any `OneWay` function, there exists a `WordSignatureScheme` whose `n`-bit restriction
satisfies `SignatureScheme.EUFCMA` while failing `WordSignatureScheme.EUFCMA`. -/
theorem exists_toSignatureScheme_eufCMA_and_not_wordEUFCMA {f : List Bool → List Bool}
    (hf : OneWay f) :
    ∃ W : WordSignatureScheme, W.toSignatureScheme.EUFCMA ∧ ¬ W.EUFCMA := by
  obtain ⟨S, hS⟩ := hf.exists_eufCMA
  exact ⟨leakNonNScheme S, eufCMA_toSignatureScheme_leakNonNScheme hS, not_eufCMA_leakNonNScheme S⟩

/-! ### 6. Concrete `TCRSignature.wordScheme` and adaptive multi-query `replayCfg` checks -/

/-- Constant `KeyedHashFamily` with `keyLen n = n` and `digestLen n = n + 1` for concrete checks. -/
def testHash : KeyedHashFamily where
  keyLen n := n
  digestLen n := n + 1
  eval n _ _ := List.replicate (n + 1) false
  keyLen_polyTime := .id'
  digestLen_polyTime := ComputableInPolyTime.id'.unary_add' (.const 1)
  le_digestLen _ := Nat.le_succ _
  polyTime :=
    (((ComputableInPolyTime.fst encUnary (encPair encBits encBits)).unary_add' (.const 1)).trans
      (ComputableInPolyTime.bitsReplicate false)).of_enc_eq fun _ => rfl
  length_eq _ _ _ _ := List.length_replicate

/-- Toy deterministic `SignatureScheme` checking `pk.length == msg.length` and
`sig.length == msg.length`. -/
noncomputable def testFixedSig : SignatureScheme where
  keyGen n := pure (List.replicate n false, List.replicate n false)
  sign _ msg := pure msg
  verify pk msg sig := (pk.length == msg.length) && (sig.length == msg.length)
  keyGen_ppt :=
    (((ComputableInPolyTime.bitsReplicate false).prod
      (ComputableInPolyTime.bitsReplicate false)).of_enc_eq fun _ => rfl).isPPTOn
  sign_ppt := (ComputableInPolyTime.snd encBits encBits).isPPTOn
  verify_polyTime := by
    let encRest := encPair encBits encBits
    have hpkLen :=
      (ComputableInPolyTime.fst encBits encRest).trans ComputableInPolyTime.length_bits
    have hrest := ComputableInPolyTime.snd encBits encRest
    have hmsgLen := hrest.fst'.trans ComputableInPolyTime.length_bits
    have hsigLen := hrest.snd'.trans ComputableInPolyTime.length_bits
    exact ((ComputableInPolyTime.unary_beq' hpkLen hmsgLen).bool_and'
      (ComputableInPolyTime.unary_beq' hsigLen hmsgLen)).of_enc_eq fun _ => rfl
  verify_sign n keys hkeys msg hmsg sig hsig := by
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hkeys hsig
    subst hkeys
    subst hsig
    simp [hmsg]

def sampleWordPk : List Bool :=
  encPair encUnary encBits (2, List.replicate (TCRSignature.otsParam testHash 2) false)

def sampleWordSig : List Bool :=
  let m := TCRSignature.otsMsg testHash 2 [true, false] [false, false, false]
  encPair encBits encBits ([true, false], m)

-- `TCRSignature.wordScheme` verifies 0-bit, 1-bit, and 5-bit messages at `n = 2`, and rejects
-- malformed hash-key lengths:
example :
    (TCRSignature.wordScheme testFixedSig testHash).verify sampleWordPk [] sampleWordSig = true ∧
    (TCRSignature.wordScheme testFixedSig testHash).verify sampleWordPk [true] sampleWordSig =
      true ∧
    (TCRSignature.wordScheme testFixedSig testHash).verify sampleWordPk
      [true, false, true, true, false] sampleWordSig = true ∧
    (TCRSignature.wordScheme testFixedSig testHash).verify sampleWordPk [true]
      (encPair encBits encBits
        ([true], TCRSignature.otsMsg testHash 2 [true, false] [false, false, false])) = false := by
  decide +kernel

/-- Control states for a concrete 2-query adaptive `MultiTapePTM` whose second query copies the
first bit of the first query's reply tape. -/
inductive AdaptiveQueryState where
  | writeFirst | queryFirst | writeSecond | querySecond | done
  deriving DecidableEq

/-- Concrete 0-work-tape `MultiTapePTM` issuing `[true]` as its first external query, then reading
the head of the installed reply tape and submitting that bit as its second external query. -/
def adaptiveTwoQueryMachine : MultiTapePTM 0 Bool AdaptiveQueryState Unit where
  initial := .writeFirst
  tr state _ _ ans _ :=
    match state with
    | .writeFirst =>
      .step { inputTape := 0, workTapes := Fin.elim0, output := none, state := some .queryFirst }
        (fun _ => some true) (fun _ => 0)
    | .queryFirst => .query () .writeSecond
    | .writeSecond =>
      .step { inputTape := 0, workTapes := Fin.elim0, output := none, state := some .querySecond }
        (fun _ => some ((ans ()).getD false)) (fun _ => 0)
    | .querySecond => .query () .done
    | .done =>
      .step { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }
        (fun _ => none) (fun _ => 0)

-- Step-by-step adaptive multi-query check:
-- 1. After step 0, `queryOf` extracts the first query `some [true]`.
-- 2. When step 1 replies with `(k₁ = [], ots₁ = [])` (`encPair` starts with `false`), step 3's
--    `queryOf` extracts `some [false]`.
-- 3. When step 1 replies with `(k₁ = [true], ots₁ = [])` (`encPair` starts with `true`), step 3's
--    `queryOf` extracts `some [true]`.
example :
    TCRSignature.queryOf adaptiveTwoQueryMachine
      (TCRSignature.replayCfg adaptiveTwoQueryMachine 10 [] [(false, [], [])]) false =
        some [true] ∧
    TCRSignature.queryOf adaptiveTwoQueryMachine
      (TCRSignature.replayCfg adaptiveTwoQueryMachine 10 []
        [(false, [], []), (false, [], []), (false, [], [])]) false =
        some [false] ∧
    TCRSignature.queryOf adaptiveTwoQueryMachine
      (TCRSignature.replayCfg adaptiveTwoQueryMachine 10 []
        [(false, [], []), (false, [true], []), (false, [], [])]) false =
        some [true] := by
  decide +kernel

/-! ### 7. Unrestricted-message (`WordSignatureScheme`) Rompel and Naor–Yung endpoints -/

example {S : SignatureScheme} (hS : S.EUFCMA) {H : KeyedHashFamily}
    (hH : H.TargetCollisionResistant) :
    (TCRSignature.wordScheme S H).EUFCMA :=
  hS.eufCMA_wordScheme hH

example {W : WordSignatureScheme} (hW : W.EUFCMA) :
    W.toSignatureScheme.EUFCMA ∧ ∃ f, OneWay f :=
  ⟨hW.toSignatureScheme, hW.exists_oneWay⟩

example {f : List Bool → List Bool} (hf : OneWay f) {H : KeyedHashFamily}
    (hH : H.TargetCollisionResistant) :
    ∃ W : WordSignatureScheme, W.EUFCMA :=
  hf.exists_wordEUFCMA_of_targetCollisionResistant hH

example {f : List Bool → List Bool} (hf : OneWayPermutation f) :
    ∃ W : WordSignatureScheme, W.EUFCMA :=
  hf.exists_wordEUFCMA

example {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ W : WordSignatureScheme, W.EUFCMA :=
  hf.exists_wordEUFCMA

example : (∃ f, OneWay f) ↔ ∃ W : WordSignatureScheme, W.EUFCMA :=
  exists_oneWay_iff_exists_wordSignature

example : (∃ S : SignatureScheme, S.OneTimeEUFCMA) ↔ ∃ W : WordSignatureScheme, W.EUFCMA :=
  exists_oneTimeSignature_iff_exists_wordSignature

/-- Converse non-vacuity check for `WordSignatureScheme`: if no uniform `OneWay` function exists,
no `WordSignatureScheme` can satisfy `EUFCMA`. -/
theorem not_exists_wordEUFCMA_of_forall_not_oneWay (hno : ∀ f, ¬ OneWay f)
    (W : WordSignatureScheme) : ¬ W.EUFCMA := by
  intro hW
  obtain ⟨f, hf⟩ := exists_oneWay_iff_exists_wordSignature.mpr ⟨W, hW⟩
  exact hno f hf

end CslibFrontierTests.Crypto.Rompel

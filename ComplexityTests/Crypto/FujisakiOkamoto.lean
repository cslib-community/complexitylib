/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module

public import Complexity.Crypto.Protocols.KEM.FujisakiOkamoto
public import Complexity.Crypto.Protocols.KEM.FujisakiOkamoto.Security

/-!
# HHK17 Fujisaki–Okamoto KEM Transform Tests

Exercises the HHK17 modular Fujisaki–Okamoto transforms (`T`, `FO^⊥`, `FO-notbot`),
`δ`-correctness, `γ`-spreadness, and two-message `IND-CPA` advantage on concrete
`ExplicitCoinPKE` schemes:

1. **Concrete `Fin 8` masked-shift `ExplicitCoinPKE`**: `0`-correctness via
   `ExplicitCoinPKE.deltaCorrect_zero_of_perfect`, honest decryption and decapsulation recovery
   for `T`, `FO^⊥`, and `FO-notbot`, and rejection of a valid underlying PKE ciphertext encrypted
   under
   non-canonical coins (`c = (1, 6)` decrypts to `some 2` under PKE, yet `decapsBot` rejects with
   `none` and `decapsNotBot` returns the domain-separated fallback key `H(true, fallback, c)`).
2. **Positive and negative witnesses for `DeltaCorrect` (including `δ > 0` tight and non-tight
   bounds)**: `identityPKE` (`DeltaCorrect 0`), `alwaysZeroDecPKE` (`¬ DeltaCorrect 0`), and
   `noisyCoinPKE` whose decryptor fails on coin `r = 1` with probability `1 / 2`, satisfying
   `DeltaCorrect (1 / 2)` (tight) and `DeltaCorrect (3 / 4)` (non-tight via `DeltaCorrect.mono`)
   while refuting `DeltaCorrect (1 / 4)`.
3. **Positive and negative witnesses for `GammaSpread` and `indCpaAdvantage`**: `identityPKE`
   satisfies `GammaSpread 0`, refutes `GammaSpread 1`, and admits a distinguisher with
   `indCpaAdvantage 0 1 = 1`.
4. **ROM IND-CCA games, simulator hit probability, and CPA reduction witnesses**:
   `queryCiphertextGAdv` satisfies `ROQueryBounds queryCiphertextGAdv 1 0`, achieves
   `simHitProb = 1` on diagonal message pairs `(m, m)` and `simHitProb = 0` on `(0, 1)`,
   yields `indCpaAdvantage 0 1 (romCpaReduction queryCiphertextGAdv 0 1) = 1`, and instantiates
   eager/lazy ROM IND-CCA equivalence and the OW-to-CPA averaging bound on `maskedShiftScheme`.
5. **Axiom audit**: `#print axioms` confirms the choice-free algebraic transform theorems
   (`decT_encT_eq_some`, `encT_of_decT_eq_some`, `Scheme.decapsBot_encT_eq_some`,
   `Scheme.decapsNotBot_encT_eq`) depend only on `[propext]`.
-/

public section

namespace ComplexityTests.Crypto.FujisakiOkamoto

open Cslib Cslib.Crypto Cslib.Crypto.Protocols Cslib.Crypto.Protocols.FujisakiOkamoto
open Cslib.Probability
open scoped NNReal ENNReal

/-! ### 1. Concrete `Fin 8` Masked-Shift `ExplicitCoinPKE` -/

/-- Explicit-coin PKE over `Fin 8`: `Enc(pk, m; r) = (r, m + pk + r)` and
`Dec(sk, (r, y)) = some (y - sk - r)`. -/
def maskedShiftPKE : ExplicitCoinPKE (Fin 8) (Fin 8) (Fin 8) (Fin 8) (Fin 8 × Fin 8) where
  keyGen := do
    let k ← ProbComp.unifFin 7
    return (k, k)
  sampleCoins := ProbComp.unifFin 7
  encDet pk m r := (r, m + pk + r)
  dec sk c := some (c.2 - sk - c.1)

/-- `maskedShiftPKE` has zero decryption error on every supported key pair, message, and coin. -/
theorem maskedShiftPKE_deltaCorrect_zero : maskedShiftPKE.DeltaCorrect 0 := by
  refine maskedShiftPKE.deltaCorrect_zero_of_perfect fun pk sk hkeys m r _ => ?_
  simp only [maskedShiftPKE, ProbComp.eval_bind, ProbComp.eval_pure,
    _root_.PMF.mem_support_bind_iff, _root_.PMF.mem_support_pure_iff, Prod.mk.injEq] at hkeys
  obtain ⟨k, -, rfl, rfl⟩ := hkeys
  have hcancel : ∀ a b c : Fin 8, b + a + c - a - c = b := by decide
  exact congrArg some (hcancel sk m r)

/-- HHK17 FO parameter bundle wrapping `maskedShiftPKE` with uniform `Fin 8` messages and `Fin 16`
shared keys. -/
def maskedShiftScheme : Scheme (Fin 8) (Fin 8) (Fin 8) (Fin 8) (Fin 8 × Fin 8) (Fin 16) where
  pke := maskedShiftPKE
  sampleMsg := ProbComp.unifFin 7
  sampleKey := ProbComp.unifFin 15

/-- Deterministic test functions `G` and `H` for `FO^⊥` and `FO-notbot` unit tests. -/
def testG : Fin 8 → Fin 8 := fun _ => 0

/-- Domain-separated test hash returning `15` on fallback inputs (`true`) and casting `m` into
`Fin 16` on valid inputs (`false`). -/
def testH : Bool × Fin 8 × (Fin 8 × Fin 8) → Fin 16 :=
  fun x => if x.1 then 15 else x.2.1.castLE (by decide)

/-- Honest `T`, `FO^⊥`, and `FO-notbot` recovery on `maskedShiftScheme` at `pk = sk = 3`,
`m = 2`. -/
example :
    decT maskedShiftPKE testG 3 3 (encT maskedShiftPKE testG 3 2) = some 2 ∧
    maskedShiftScheme.decapsBot testG testH 3 3 (encT maskedShiftPKE testG 3 2) =
      some (2 : Fin 16) ∧
    maskedShiftScheme.decapsNotBot testG testH ⟨3, 3, 7⟩ (encT maskedShiftPKE testG 3 2) =
      (2 : Fin 16) := by
  refine ⟨decT_encT_eq_some maskedShiftPKE testG 3 3 2 (by decide), ?_, ?_⟩
  · exact (maskedShiftScheme.decapsBot_encT_eq_some testG testH 3 3 2 (by decide)).trans rfl
  · exact (maskedShiftScheme.decapsNotBot_encT_eq testG testH ⟨3, 3, 7⟩ 2 (by decide)).trans rfl

/-- Ciphertext `(1, 6)` decrypts to `some 2` under `maskedShiftPKE` (`pk = sk = 3`, non-canonical
coin `r = 1 ≠ testG 2 = 0`), yet `FO^⊥` rejects with `none` and `FO-notbot` outputs the fallback
key `testH (true, 7, (1, 6)) = 15`. -/
example :
    maskedShiftPKE.dec 3 (1, 6) = some 2 ∧
    maskedShiftScheme.decapsBot testG testH 3 3 (1, 6) = none ∧
    maskedShiftScheme.decapsNotBot testG testH ⟨3, 3, 7⟩ (1, 6) = 15 := by
  have hbad : ∀ m', maskedShiftPKE.dec 3 (1, 6) = some m' →
      encT maskedShiftPKE testG 3 m' ≠ (1, 6) := by decide
  exact ⟨by decide,
    maskedShiftScheme.decapsBot_eq_none_of_reencrypt_ne testG testH 3 3 (1, 6) hbad,
    maskedShiftScheme.decapsNotBot_of_reencrypt_ne testG testH ⟨3, 3, 7⟩ (1, 6) hbad⟩

/-! ### 2. `DeltaCorrect` Witnesses (Zero-Error, Tight Non-Zero `δ > 0`, Non-Tight, and Negative) -/

/-- Insecure deterministic identity PKE on `Fin 4`: `Enc((), m; ()) = m`, `Dec((), c) = some c`. -/
def identityPKE : ExplicitCoinPKE Unit Unit (Fin 4) Unit (Fin 4) where
  keyGen := pure ((), ())
  sampleCoins := pure ()
  encDet _ m _ := m
  dec _ c := some c

theorem identityPKE_deltaCorrect_zero : identityPKE.DeltaCorrect 0 := by
  refine identityPKE.deltaCorrect_zero_of_perfect ?_
  intro _ _ _ _ _ _
  rfl

/-- Toy PKE on `Fin 2` whose decryption always outputs `some 0`, failing on message `1`. -/
def alwaysZeroDecPKE : ExplicitCoinPKE Unit Unit (Fin 2) Unit (Fin 2) where
  keyGen := pure ((), ())
  sampleCoins := pure ()
  encDet _ m _ := m
  dec _ _ := some 0

/-- Negative `DeltaCorrect` witness: `alwaysZeroDecPKE` fails on `m = 1` with probability `1`,
so it is not `0`-correct. -/
theorem not_alwaysZeroDecPKE_deltaCorrect_zero : ¬ alwaysZeroDecPKE.DeltaCorrect 0 := by
  intro h
  have hkg : alwaysZeroDecPKE.keyGen = pure ((), ()) := rfl
  have hnonneg := alwaysZeroDecPKE.keyPairMaxFailProb_nonneg () ()
  have h0 : alwaysZeroDecPKE.keyPairMaxFailProb () () ≤ 0 := by
    simpa [ExplicitCoinPKE.DeltaCorrect, hkg, ENNReal.toReal_ofReal hnonneg] using h
  have h1 : (1 : ℝ) ≤ alwaysZeroDecPKE.keyPairMaxFailProb () () := by
    refine le_trans ?_ (alwaysZeroDecPKE.msgFailProb_le_keyPairMaxFailProb () () 1)
    simp [ExplicitCoinPKE.msgFailProb, alwaysZeroDecPKE]
  linarith

/-- Explicit-coin PKE on `Fin 2` with coin space `Fin 2` whose decryptor succeeds on coin `r = 0`
and fails (`none`) on coin `r = 1`, incurring decryption failure probability `1 / 2` on every
message. -/
def noisyCoinPKE : ExplicitCoinPKE Unit Unit (Fin 2) (Fin 2) (Fin 2 × Fin 2) where
  keyGen := pure ((), ())
  sampleCoins := ProbComp.unifFin 1
  encDet _ m r := (r, m)
  dec _ c := if c.1 = 0 then some c.2 else none

theorem noisyCoinPKE_msgFailProb (m : Fin 2) :
    noisyCoinPKE.msgFailProb () () m = 1 / 2 := by
  rw [ExplicitCoinPKE.msgFailProb, PMF.toOuterMeasure_apply_toReal, Fin.sum_univ_two]
  simp [noisyCoinPKE, ProbComp.eval_unifFin, PMF.uniformOfFintype_apply]

theorem noisyCoinPKE_keyPairMaxFailProb :
    noisyCoinPKE.keyPairMaxFailProb () () = 1 / 2 := by
  apply le_antisymm
  · rw [ExplicitCoinPKE.keyPairMaxFailProb, Finset.sup'_le_iff]
    intro m _
    exact le_of_eq (noisyCoinPKE_msgFailProb m)
  · exact le_trans (le_of_eq (noisyCoinPKE_msgFailProb 0).symm)
      (noisyCoinPKE.msgFailProb_le_keyPairMaxFailProb () () 0)

/-- Positive `δ > 0` witness (tight): `noisyCoinPKE` is `(1 / 2)`-correct. -/
theorem noisyCoinPKE_deltaCorrect_half : noisyCoinPKE.DeltaCorrect (1 / 2) := by
  have hkg : noisyCoinPKE.keyGen = pure ((), ()) := rfl
  simp [ExplicitCoinPKE.DeltaCorrect, hkg, noisyCoinPKE_keyPairMaxFailProb]

/-- Positive `δ > 0` witness (non-tight): `noisyCoinPKE` is `(3 / 4)`-correct. -/
theorem noisyCoinPKE_deltaCorrect_three_quarters : noisyCoinPKE.DeltaCorrect (3 / 4) :=
  noisyCoinPKE_deltaCorrect_half.mono (by norm_num)

/-- Negative witness: `noisyCoinPKE` is not `(1 / 4)`-correct. -/
theorem not_noisyCoinPKE_deltaCorrect_quarter : ¬ noisyCoinPKE.DeltaCorrect (1 / 4) := by
  intro h
  have hkg : noisyCoinPKE.keyGen = pure ((), ()) := rfl
  simp only [ExplicitCoinPKE.DeltaCorrect, hkg, ProbComp.expect_pure,
    noisyCoinPKE_keyPairMaxFailProb] at h
  norm_num at h

/-! ### 3. `GammaSpread` and `indCpaAdvantage` Witnesses -/

/-- Positive `GammaSpread` witness: `identityPKE` is `0`-spread (`2 ^ (-0) = 1`). -/
theorem identityPKE_gammaSpread_zero : identityPKE.GammaSpread 0 := by
  intro pk sk _ m c
  rw [neg_zero, Real.rpow_zero, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top (PMF.toOuterMeasure_le_one _ _)

/-- Negative `GammaSpread` witness: `identityPKE` is not `1`-spread (`1 > 2 ^ (-1)`). -/
theorem not_identityPKE_gammaSpread_one : ¬ identityPKE.GammaSpread 1 := by
  intro h
  have h0 := h () () (by simp [identityPKE]) 0 0
  simp only [identityPKE, ProbComp.eval_pure, _root_.PMF.toOuterMeasure_pure_apply,
    Set.mem_ofPred_eq, ↓reduceIte, ENNReal.toReal_one] at h0
  norm_num at h0

/-- Distinguisher against `identityPKE` that checks whether the challenge ciphertext equals `1`
achieves two-message IND-CPA advantage `1` on challenge messages `(0, 1)`. -/
theorem identityPKE_indCpaAdvantage_eq_one :
    (identityPKE.indCpaAdvantage 0 1 (fun _ c => pure (decide (c = 1))) : ℝ) = 1 := by
  rw [ExplicitCoinPKE.indCpaAdvantage, Game.coe_advantage, Game.coe_succProbability,
    Game.coe_succProbability]
  simp [ExplicitCoinPKE.indCpaGame, ExplicitCoinPKE.encrypt, identityPKE]

/-! ### 4. ROM IND-CCA Games, Simulator Hit Probability, and CPA Reduction Witnesses -/

/-- HHK17 FO scheme wrapping `identityPKE` with uniform `Fin 4` messages and `Fin 2` keys. -/
def identityScheme : Scheme Unit Unit (Fin 4) Unit (Fin 4) (Fin 2) where
  pke := identityPKE
  sampleMsg := ProbComp.unifFin 3
  sampleKey := pure 0

/-- ROM adversary against `identityScheme` that queries `G` on the challenge ciphertext `cStar`
(which equals the plaintext message in `identityPKE`), queries punctured decapsulation on `cStar`,
and outputs `true`. -/
def queryCiphertextGAdv : ROAdversary Unit (Fin 4) Unit (Fin 4) (Fin 2) :=
  fun (_, cStar, _) => do
    let _ ← OracleComp.query (ROQuery.G cStar)
    let _ ← OracleComp.query (ROQuery.decaps cStar)
    return true

/-- `queryCiphertextGAdv` makes at most `1` query to `G` and `0` queries to `H`. -/
theorem queryCiphertextGAdv_bounds : ROQueryBounds queryCiphertextGAdv 1 0 := by
  intro ⟨_, cStar, _⟩
  refine ⟨?_, ?_⟩
  · exact (OracleComp.IsCostBounded.query (ROQuery.G cStar)).bind
      (fun _ => (OracleComp.IsCostBounded.query (ROQuery.decaps cStar)).bind
        fun _ => OracleComp.IsCostBounded.pure true 0)
  · exact (OracleComp.IsCostBounded.query (ROQuery.G cStar)).bind
      (fun _ => (OracleComp.IsCostBounded.query (ROQuery.decaps cStar)).bind
        fun _ => OracleComp.IsCostBounded.pure true 0)

/-- Positive hit-probability witness: when `m₀ = m₁`, `queryCiphertextGAdv` queries `G(m₁)` with
probability `1`. -/
theorem identityScheme_simHitProb_diag (m : Fin 4) :
    identityScheme.simHitProb queryCiphertextGAdv m m = 1 := by
  simp [-bind_pure_comp, -_root_.PMF.bind_apply,
    Scheme.simHitProb, Scheme.romCpaReduction, queryCiphertextGAdv,
    identityScheme, identityPKE, ExplicitCoinPKE.indCpaGame, ExplicitCoinPKE.encrypt,
    Scheme.simHandler, simHashG, OracleComp.interpret_bind, OracleComp.interpret_query,
    OracleComp.interpret_pure]
  simp [-_root_.PMF.bind_apply, StateT.run, RandomOracle.zoomStateT,
    memoize_of_none _ m [] rfl]

/-- Negative hit-probability witness: when `m₀ = 0` and `m₁ = 1`, `queryCiphertextGAdv` queries
only `G(0)` and never `G(1)`, so `simHitProb = 0`. -/
theorem identityScheme_simHitProb_zero_one :
    identityScheme.simHitProb queryCiphertextGAdv 0 1 = 0 := by
  simp [-bind_pure_comp, -_root_.PMF.bind_apply,
    Scheme.simHitProb, Scheme.romCpaReduction, queryCiphertextGAdv,
    identityScheme, identityPKE, ExplicitCoinPKE.indCpaGame, ExplicitCoinPKE.encrypt,
    Scheme.simHandler, simHashG, OracleComp.interpret_bind, OracleComp.interpret_query,
    OracleComp.interpret_pure]
  simp [-_root_.PMF.bind_apply, StateT.run, RandomOracle.zoomStateT,
    memoize_of_none _ (0 : Fin 4) [] rfl]

/-- The HHK17 CPA reduction `romCpaReduction` built from `queryCiphertextGAdv` achieves
IND-CPA advantage `1` on challenge messages `(0, 1)`. -/
theorem identityScheme_indCpaAdvantage_romCpaReduction_eq_one :
    (identityPKE.indCpaAdvantage 0 1
      (identityScheme.romCpaReduction queryCiphertextGAdv 0 1) : ℝ) = 1 := by
  change (identityScheme.pke.indCpaAdvantage 0 1
    (identityScheme.romCpaReduction queryCiphertextGAdv 0 1) : ℝ) = 1
  rw [identityScheme.indCpaAdvantage_romCpaReduction,
    identityScheme_simHitProb_zero_one, identityScheme_simHitProb_diag]
  norm_num

/-- Variant of `identityScheme` with `sampleMsg := pure 0` and uniform `Fin 2` keys
(`ProbComp.unifFin 1`), used to witness positive `indCcaRomAdvantage`. -/
def identityUnifKeyScheme : Scheme Unit Unit (Fin 4) Unit (Fin 4) (Fin 2) where
  pke := identityPKE
  sampleMsg := pure 0
  sampleKey := ProbComp.unifFin 1

/-- ROM adversary that queries `H(false, cStar, cStar)` and checks whether the returned key equals
the challenge key `kStar`. -/
def checkKeyHAdv : ROAdversary Unit (Fin 4) Unit (Fin 4) (Fin 2) :=
  fun (_, cStar, kStar) => do
    let k ← OracleComp.query (ROQuery.H (false, cStar, cStar))
    return decide (k = kStar)

/-- Positive-advantage witness for `indCcaRomAdvantage`: `checkKeyHAdv` distinguishes real from
random keys in `identityUnifKeyScheme` with advantage `1 / 2`. -/
theorem identityUnifKeyScheme_indCcaRomAdvantage_eq_half :
    (identityUnifKeyScheme.indCcaRomAdvantage checkKeyHAdv : ℝ) = 1 / 2 := by
  have hgame (b : Bool) :
      identityUnifKeyScheme.roIndCcaGame checkKeyHAdv b =
        (do
          let kReal ← ProbComp.unifFin 1
          let kRand ← ProbComp.unifFin 1
          return decide (kReal = if b then kRand else kReal)) := by
    simp [-bind_pure_comp, Scheme.roIndCcaGame, Scheme.keyGenNotBot,
      identityUnifKeyScheme, identityPKE, checkKeyHAdv, Scheme.roHandler, roHashH,
      OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_pure]
    simp [StateT.run, RandomOracle.zoomStateT,
      memoize_of_some _ (false, (0 : Fin 4), (0 : Fin 4)) [((false, 0, 0), _)] _ rfl]
  rw [Scheme.indCcaRomAdvantage, hgame false, hgame true, Game.coe_advantage,
    Game.coe_succProbability, Game.coe_succProbability]
  simp only [Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.bind_apply_toReal_tsum, tsum_fintype, ProbComp.eval_unifFin,
    PMF.uniformOfFintype_apply, Fintype.card_fin, _root_.PMF.pure_apply]
  rw [Fin.sum_univ_two]
  simp [Fin.sum_univ_two]
  norm_num

/-- Instantiating eager/lazy ROM IND-CCA equivalence and the OW-to-CPA averaging bound on
`maskedShiftScheme`. -/
example (A : ROAdversary (Fin 8) (Fin 8) (Fin 8) (Fin 8 × Fin 8) (Fin 16))
    (qG qH : ℕ) (hA : ROQueryBounds A qG qH) :
    maskedShiftScheme.indCcaRomAdvantage A =
      Game.advantage (maskedShiftScheme.eagerIndCcaGame A false)
        (maskedShiftScheme.eagerIndCcaGame A true) ∧
    ∃ m₀ m₁ : Fin 8, m₀ ≠ m₁ ∧
      (∑ m : Fin 8, maskedShiftScheme.simHitProb A m m) / (Fintype.card (Fin 8) : ℝ) ≤
      (maskedShiftPKE.indCpaAdvantage m₀ m₁
        (maskedShiftScheme.romCpaReduction A m₀ m₁) : ℝ) +
      ((qG : ℝ) + (qH : ℝ)) / (Fintype.card (Fin 8) : ℝ) :=
  ⟨maskedShiftScheme.indCcaRomAdvantage_eq_eager A,
    maskedShiftScheme.avg_simHitProb_le_indCpaAdvantage_romCpaReduction A (by decide) hA⟩

/-! ### 5. Axiom Hygiene Guards for Choice-Free Results -/

/--
info: 'Cslib.Crypto.Protocols.FujisakiOkamoto.decT_encT_eq_some' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Protocols.FujisakiOkamoto.decT_encT_eq_some

/--
info: 'Cslib.Crypto.Protocols.FujisakiOkamoto.encT_of_decT_eq_some' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Protocols.FujisakiOkamoto.encT_of_decT_eq_some

/--
info: 'Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.decapsBot_encT_eq_some' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.decapsBot_encT_eq_some

/--
info: 'Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.decapsNotBot_encT_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.decapsNotBot_encT_eq

end ComplexityTests.Crypto.FujisakiOkamoto

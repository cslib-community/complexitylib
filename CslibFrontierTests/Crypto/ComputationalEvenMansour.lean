/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.EvenMansour
import Mathlib.Data.ZMod.Basic

/-!
# Tests for word-level Even–Mansour and randomized ideal-permutation PRP security

Exercises `CslibFrontier/Crypto/Computational/EvenMansour.lean`:
* concrete evaluation and inversion of `evenMansourPreKeyWord`, `evenMansourPostKeyWord`,
  `splitTwoKeys`, `evenMansourEncryptWord`, `evenMansourDecryptWord`,
  `singleKeyEvenMansourEncryptWord`, and `singleKeyEvenMansourDecryptWord`;
* concrete `BlockCipher` instantiations of `evenMansourCipher` and `singleKeyEvenMansourCipher`,
  together with `permEquiv_evenMansourCipher` and `permEquiv_singleKeyEvenMansourCipher`;
* concrete randomized (`ProbOracleComp`) two-sided distinguisher with private coin flips and proved
  `IsProbCallBounded _ 1 1` budget over `ZMod 7` and `BitString n`, instantiating the coin-fixing
  equalities, quantitative `2 * Q_e * Q_π / |G|` and `2 * Q_e * Q_π / 2 ^ n` bounds, and asymptotic
  `Negligible` theorems;
* concrete word-oracle (`EvenMansourDistinguisher`) instantiations and axiom-footprint guards.
-/

namespace CslibFrontierTests.Crypto.ComputationalEvenMansour

open Cslib Cslib.Crypto Cslib.Crypto.EvenMansour Cslib.Probability Turing.MultiTapeTM

/-! ### Concrete word-level Even–Mansour operations -/

example : evenMansourPreKeyWord [true, false, true, false] [false, false, true, true] =
    [true, false, false, true] := by decide

example : evenMansourPostKeyWord [true, true, false, false] [true, false, false, true] =
    [false, true, false, true] := by decide

example : splitTwoKeys 2 [true, false, false, true] = ([true, false], [false, true]) := by decide

example :
    let P : List Bool → List Bool := List.map Bool.not
    let k₁ := [true, false, true, false]
    let k₂ := [false, true, false, true]
    let x := [true, true, false, false]
    evenMansourDecryptWord P k₁ k₂ (evenMansourEncryptWord P k₁ k₂ x) = x ∧
      singleKeyEvenMansourDecryptWord P k₁ (singleKeyEvenMansourEncryptWord P k₁ x) = x := by
  decide

/-! ### Concrete `BlockCipher` instantiations -/

/-- Identity word family `(n, block) ↦ block`, used as a concrete polynomial-time permutation
family to instantiate `evenMansourCipher` and `singleKeyEvenMansourCipher`. -/
def idWordFamily (_ : ℕ) (block : List Bool) : List Bool := block

theorem computableInPolyTime_idWordFamily :
    ComputableInPolyTime (fun p : ℕ × List Bool => idWordFamily p.1 p.2)
      (encPair encUnary encBits) encBits := by
  unfold idWordFamily
  polytime

/-- Concrete two-key Even–Mansour `BlockCipher` built from `idWordFamily`. -/
def idEvenMansourCipher : BlockCipher :=
  evenMansourCipher idWordFamily idWordFamily
    computableInPolyTime_idWordFamily computableInPolyTime_idWordFamily
    (fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

/-- Concrete single-key Even–Mansour `BlockCipher` built from `idWordFamily`. -/
def idSingleKeyEvenMansourCipher : BlockCipher :=
  singleKeyEvenMansourCipher idWordFamily idWordFamily
    computableInPolyTime_idWordFamily computableInPolyTime_idWordFamily
    (fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

-- Concrete evaluation of `idEvenMansourCipher` and `idSingleKeyEvenMansourCipher` on 2-bit blocks,
-- including rejection of malformed queries.
example : idEvenMansourCipher.prpOracle 2 [true, false, false, true] [true, true] =
    [false, false] := by decide

example : idEvenMansourCipher.strongPRPOracle 2 [true, false, false, true] (true, [false, false]) =
    [true, true] := by decide

example : idEvenMansourCipher.prpOracle 2 [true, false, false, true] [true] = [] := by decide

example : idSingleKeyEvenMansourCipher.prpOracle 2 [true, false] [true, true] =
    [true, true] := by decide

example (n : ℕ) (key : List Bool) (hkey : key.length = 2 * n) :
    idEvenMansourCipher.permEquiv n key hkey =
      evenMansourEquiv
        (permOfWordFamily idWordFamily idWordFamily
          (fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ => rfl) (fun _ _ _ => rfl) n)
        (BitString.ofList n (splitTwoKeys n key).1)
        (BitString.ofList n (splitTwoKeys n key).2) :=
  permEquiv_evenMansourCipher idWordFamily idWordFamily
    computableInPolyTime_idWordFamily computableInPolyTime_idWordFamily
    (fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ => rfl) (fun _ _ _ => rfl) n key hkey

example (n : ℕ) (key : List Bool) (hkey : key.length = n) :
    idSingleKeyEvenMansourCipher.permEquiv n key hkey =
      singleKeyEvenMansourEquiv
        (permOfWordFamily idWordFamily idWordFamily
          (fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ => rfl) (fun _ _ _ => rfl) n)
        (BitString.ofList n key) :=
  permEquiv_singleKeyEvenMansourCipher idWordFamily idWordFamily
    computableInPolyTime_idWordFamily computableInPolyTime_idWordFamily
    (fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ => rfl) (fun _ _ _ => rfl) n key hkey

/-! ### Randomized (`ProbOracleComp`) two-sided distinguisher and security bounds -/

/-- A randomized distinguisher over an arbitrary group `G`: flips a fair coin (`unifFin 1`),
queries the cipher forward on `0`, queries the primitive permutation inverse on the ciphertext `y`,
and tests whether the result equals `0` (or `y = 0` on the other coin branch). -/
def sampleProbDistinguisher (G : Type) [Zero G] [DecidableEq G] :
    ProbOracleComp (EvenMansourSpec G) Bool := do
  let c ← ProbOracleComp.sample (ProbComp.unifFin 1)
  let y ← ProbOracleComp.query (spec := EvenMansourSpec G) (Sum.inl (.forward 0))
  let u ← ProbOracleComp.query (spec := EvenMansourSpec G) (Sum.inr (.inverse y))
  return if c = 0 then decide (u = 0) else decide (y = 0)

theorem isProbCallBounded_sampleProbDistinguisher (G : Type) [Zero G] [DecidableEq G] :
    IsProbCallBounded (sampleProbDistinguisher G) 1 1 := by
  constructor
  · simpa [sampleProbDistinguisher, cipherCost] using
      (ProbOracleComp.isCostBounded_sample cipherCost (ProbComp.unifFin 1)).bind fun _ =>
        (ProbOracleComp.isCostBounded_query (spec := EvenMansourSpec G) cipherCost
          (Sum.inl (.forward (0 : G)))).bind fun (y : G) =>
          (ProbOracleComp.isCostBounded_query (spec := EvenMansourSpec G) cipherCost
            (Sum.inr (.inverse y))).bind fun _ =>
            OracleComp.IsCostBounded.pure _ 0
  · simpa [sampleProbDistinguisher, permCost] using
      (ProbOracleComp.isCostBounded_sample permCost (ProbComp.unifFin 1)).bind fun _ =>
        (ProbOracleComp.isCostBounded_query (spec := EvenMansourSpec G) permCost
          (Sum.inl (.forward (0 : G)))).bind fun (y : G) =>
          (ProbOracleComp.isCostBounded_query (spec := EvenMansourSpec G) permCost
            (Sum.inr (.inverse y))).bind fun _ =>
            OracleComp.IsCostBounded.pure _ 0

-- Concrete instantiation of the coin-fixing decomposition and randomized Even–Mansour bounds over
-- `ZMod 7` and `BitString 4`.
example :
    evenMansourProbRealGame (sampleProbDistinguisher (ZMod 7)) =
      ((ProbOracleComp.coinLaw (sampleProbDistinguisher (ZMod 7))).bind fun ω =>
        evenMansourRealGame (ProbOracleComp.fixCoins (sampleProbDistinguisher (ZMod 7)) ω)) ∧
    (Game.advantage (evenMansourProbRealGame (sampleProbDistinguisher (ZMod 7)))
      (evenMansourProbIdealGame (sampleProbDistinguisher (ZMod 7))) : ℝ) ≤
      2 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / (Fintype.card (ZMod 7) : ℝ) ∧
    (Game.advantage (singleKeyEvenMansourProbRealGame (sampleProbDistinguisher (ZMod 7)))
      (evenMansourProbIdealGame (sampleProbDistinguisher (ZMod 7))) : ℝ) ≤
      2 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / (Fintype.card (ZMod 7) : ℝ) ∧
    (Game.advantage (evenMansourProbRealGame (sampleProbDistinguisher (BitString 4)))
      (evenMansourProbIdealGame (sampleProbDistinguisher (BitString 4))) : ℝ) ≤
      2 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / (2 : ℝ) ^ 4 ∧
    (Game.advantage (singleKeyEvenMansourProbRealGame (sampleProbDistinguisher (BitString 4)))
      (evenMansourProbIdealGame (sampleProbDistinguisher (BitString 4))) : ℝ) ≤
      2 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / (2 : ℝ) ^ 4 :=
  ⟨evenMansourProbRealGame_eq_coinLaw_bind (sampleProbDistinguisher (ZMod 7)),
   advantage_evenMansourProbRealGame_evenMansourProbIdealGame_le
     (isProbCallBounded_sampleProbDistinguisher (ZMod 7)),
   advantage_singleKeyEvenMansourProbRealGame_evenMansourProbIdealGame_le
     (isProbCallBounded_sampleProbDistinguisher (ZMod 7)),
   advantage_evenMansourProbRealGame_bitString_le
     (isProbCallBounded_sampleProbDistinguisher (BitString 4)),
   advantage_singleKeyEvenMansourProbRealGame_bitString_le
     (isProbCallBounded_sampleProbDistinguisher (BitString 4))⟩

-- Concrete instantiation of the asymptotic `Negligible` theorems for the randomized distinguisher
-- family `fun n => sampleProbDistinguisher (BitString n)`.
example :
    Negligible (fun n =>
      Game.advantage (evenMansourProbRealGame (sampleProbDistinguisher (BitString n)))
        (evenMansourProbIdealGame (sampleProbDistinguisher (BitString n)))) ∧
    Negligible (fun n =>
      Game.advantage (singleKeyEvenMansourProbRealGame (sampleProbDistinguisher (BitString n)))
        (evenMansourProbIdealGame (sampleProbDistinguisher (BitString n)))) :=
  ⟨negligible_advantage_evenMansourProbRealGame
     (PolynomiallyBounded.const 1) (PolynomiallyBounded.const 1)
     (fun n => isProbCallBounded_sampleProbDistinguisher (BitString n)),
   negligible_advantage_singleKeyEvenMansourProbRealGame
     (PolynomiallyBounded.const 1) (PolynomiallyBounded.const 1)
     (fun n => isProbCallBounded_sampleProbDistinguisher (BitString n))⟩

/-! ### Word-oracle (`EvenMansourDistinguisher`) checks -/

/-- A concrete word-oracle distinguisher that queries cipher encryption on `0^n` and primitive
inverse on the returned ciphertext, and checks whether the result is `0^n`. -/
def sampleWordDistinguisher : EvenMansourDistinguisher := fun n _ => do
  let z := List.replicate n false
  let y ← ProbOracleComp.query ((false, false), z)
  let u ← ProbOracleComp.query ((true, true), y)
  return decide (u = z)

theorem isWordCallBounded_sampleWordDistinguisher (n : ℕ) :
    IsWordCallBounded (sampleWordDistinguisher n []) 1 1 := by
  constructor
  · simpa [sampleWordDistinguisher, wordCipherCost] using
      (ProbOracleComp.isCostBounded_query (spec := fun _ => List Bool) wordCipherCost
        ((false, false), List.replicate n false)).bind fun (y : List Bool) =>
        (ProbOracleComp.isCostBounded_query (spec := fun _ => List Bool) wordCipherCost
          ((true, true), y)).bind fun _ =>
          OracleComp.IsCostBounded.pure _ 0
  · simpa [sampleWordDistinguisher, wordPermCost] using
      (ProbOracleComp.isCostBounded_query (spec := fun _ => List Bool) wordPermCost
        ((false, false), List.replicate n false)).bind fun (y : List Bool) =>
        (ProbOracleComp.isCostBounded_query (spec := fun _ => List Bool) wordPermCost
          ((true, true), y)).bind fun _ =>
          OracleComp.IsCostBounded.pure _ 0

example (n : ℕ) :
    (Game.advantage (ProbComp.eval (evenMansourWordRealGame sampleWordDistinguisher n))
      (ProbComp.eval (evenMansourWordIdealGame sampleWordDistinguisher n)) : ℝ) ≤
      2 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / (2 : ℝ) ^ n ∧
    (Game.advantage (ProbComp.eval (singleKeyEvenMansourWordRealGame sampleWordDistinguisher n))
      (ProbComp.eval (evenMansourWordIdealGame sampleWordDistinguisher n)) : ℝ) ≤
      2 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / (2 : ℝ) ^ n :=
  ⟨advantage_evenMansourWordRealGame_evenMansourWordIdealGame_le
     sampleWordDistinguisher n 1 1 (isWordCallBounded_sampleWordDistinguisher n),
   advantage_singleKeyEvenMansourWordRealGame_evenMansourWordIdealGame_le
     sampleWordDistinguisher n 1 1 (isWordCallBounded_sampleWordDistinguisher n)⟩

example :
    Game.Indistinguishable
      (fun adversary n => (evenMansourWordRealGame adversary n).eval)
      (fun adversary n => (evenMansourWordIdealGame adversary n).eval)
      (IsOraclePPT encBool) ∧
    Game.Indistinguishable
      (fun adversary n => (singleKeyEvenMansourWordRealGame adversary n).eval)
      (fun adversary n => (evenMansourWordIdealGame adversary n).eval)
      (IsOraclePPT encBool) :=
  ⟨indistinguishable_evenMansourWordRealGame_evenMansourWordIdealGame,
   indistinguishable_singleKeyEvenMansourWordRealGame_evenMansourWordIdealGame⟩

/-! ### Axiom guards for headline results -/

/--
info: 'Cslib.Crypto.evenMansourDecryptWord_evenMansourEncryptWord' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms evenMansourDecryptWord_evenMansourEncryptWord

/--
info: 'Cslib.Crypto.advantage_evenMansourProbRealGame_evenMansourProbIdealGame_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms advantage_evenMansourProbRealGame_evenMansourProbIdealGame_le

/--
info: 'Cslib.Crypto.negligible_advantage_evenMansourProbRealGame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms negligible_advantage_evenMansourProbRealGame

/--
info: 'Cslib.Crypto.indistinguishable_evenMansourWordRealGame_evenMansourWordIdealGame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms indistinguishable_evenMansourWordRealGame_evenMansourWordIdealGame

end CslibFrontierTests.Crypto.ComputationalEvenMansour

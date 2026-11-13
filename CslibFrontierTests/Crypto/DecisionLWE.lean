/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.LWE.Basic

/-!
Regression clients for typed decision LWE: the `[b | A]` layout, the encoded input words, which
are the words the encoded ensembles sample, and both directions of `decisionLWE_iff_encoded`.
-/

namespace CslibFrontierTests.DecisionLWE

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.LWE Turing.MultiTapeTM
open scoped Matrix

private def toyA : Matrix (Fin 2) (Fin 1) (ZMod (2 ^ 2)) := !![3; 1]
private def toyS : Fin 1 → ZMod (2 ^ 2) := ![2]
private def toyE : Fin 2 → ZMod (2 ^ 2) := ![1, 3]

-- `[b | A]` puts the target first in each row.
example : augmentedMatrix toyA ![0, 2] = !![0, 3; 2, 1] := by decide

-- The real experiment's sample `(A, A s + e)` is the key generator's public matrix
-- `[A t + e | A]`: here `3 * 2 + 1 = 3` and `1 * 2 + 3 = 1` modulo 4.
example : publicMatrix toyA toyS toyE = augmentedMatrix toyA (toyA *ᵥ toyS + toyE) := rfl
example : publicMatrix toyA toyS toyE = !![3, 3; 1, 1] := by decide

-- Encoded words are unchanged: a distinguisher machine reads the framed unary security parameter
-- followed by the binary word of `[b | A]`, which is what `realEnsemble` samples.
example (n m w : ℕ → ℕ) (x : Input n m w) :
    encInput n m w x = encPair encUnary encBits
      (x.secParam, Matrix.toBinary (augmentedMatrix x.matrix x.target)) := rfl

-- A distinguisher that ignores its input has no advantage in the fixed-instance experiments.
example (s : Fin 1 → ZMod 4) (e : Fin 2 → ZMod 4) :
    Experiment.advantage (realExperiment s e fun _ _ => pure true)
      (randomExperiment (R := ZMod 4) (n := 1) (m := 2) fun _ _ => pure true) = 0 := by
  simp

-- The same holds for the games with any secret and error laws.
example (secretLaw : PMF (Fin 1 → ZMod 4)) (errorLaw : PMF (Fin 2 → ZMod 4)) :
    LWE.advantage secretLaw errorLaw (fun _ _ => pure true) = 0 := by
  simp [LWE.advantage, realGame, randomGame]

-- Typed to word: clients reducing on encoded matrices use `DecisionLWE.encoded`.
example {n m w : ℕ → ℕ} {noise : (κ : ℕ) → PMF (ZMod (2 ^ w κ))} (h : DecisionLWE n m w noise)
    (W : Crypto.Distinguisher) (hW : IsPPT encBool W) :
    Negligible fun κ => Game.advantage (distinguishingGame (realEnsemble n m w noise κ) (W κ))
      (distinguishingGame (uniformEnsemble n m w κ) (W κ)) :=
  h.encoded W hW

-- Word to typed: the word-level assumption bounds every typed PPT distinguisher's advantage with
-- a uniform secret and independent errors.
example {n m w : ℕ → ℕ} {noise : (κ : ℕ) → PMF (ZMod (2 ^ w κ))}
    (h : ComputationallyIndistinguishable (realEnsemble n m w noise) (uniformEnsemble n m w))
    (D : LWE.Distinguisher n m w) (hD : D.IsPPT) :
    Negligible fun κ => LWE.advantage (PMF.uniformOfFintype (Fin (n κ) → ZMod (2 ^ w κ)))
      (PMF.pi fun _ : Fin (m κ) => noise κ) (D κ) :=
  (decisionLWE_iff_encoded n m w noise).mpr h D hD

end CslibFrontierTests.DecisionLWE

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.LWE.Module

/-!
Regression clients for typed decision Module-LWE: a concrete sample over `ℤ_5[X] / (X^2 + 1)`,
the encoded input words, which are the words the encoded ensembles sample, the bridge to LWE over
`Negacyclic (ZMod q) n`, and both directions of `decisionModuleLWE_iff_encoded`.
-/

namespace CslibFrontierTests.DecisionModuleLWE

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM
open scoped Matrix

-- Over `ℤ_5[X] / (X^2 + 1)`: `X · (1 + X) + 1 = 1 + X + X^2 = X`, since `X^2 = -1`.
example : ModuleLWE.sample (!![![0, 1]] : Matrix (Fin 1) (Fin 1) (Fin 2 → ZMod 5)) ![![1, 1]]
    ![![1, 0]] = ![![0, 1]] := by
  decide

-- Encoded words are unchanged: a distinguisher machine reads the framed unary security parameter
-- followed by the encoded pair `(A, b)`, which is what `realEnsemble` samples.
example (m d n q : ℕ → ℕ) [∀ κ, NeZero (q κ)] (x : ModuleLWE.Input m d n q) :
    ModuleLWE.encInput m d n q x =
      encPair encUnary encBits (x.secParam, ModuleLWE.encodeSample (x.matrix, x.target)) := rfl

-- A distinguisher that ignores its input has no advantage, for any secret and error laws.
example (secretLaw : PMF (Fin 1 → Fin 2 → ZMod 5)) (errorLaw : PMF (Fin 2 → Fin 2 → ZMod 5)) :
    ModuleLWE.advantage secretLaw errorLaw (fun _ _ => pure true) = 0 := by
  simp [ModuleLWE.advantage, ModuleLWE.realGame, ModuleLWE.randomGame]

-- A bound on LWE over the negacyclic ring bounds Module-LWE with the coefficientwise laws.
example {m d n q : ℕ} [NeZero q] (ε : NNReal) (secretLaw : PMF (Fin d → Fin n → ZMod q))
    (errorLaw : PMF (Fin m → Fin n → ZMod q))
    (h : ∀ D, LWE.advantage (secretLaw.map (Negacyclic.ofCoeffs ∘ ·))
      (errorLaw.map (Negacyclic.ofCoeffs ∘ ·)) D ≤ ε)
    (D : Matrix (Fin m) (Fin d) (Fin n → ZMod q) → (Fin m → Fin n → ZMod q) → ProbComp Bool) :
    ModuleLWE.advantage secretLaw errorLaw D ≤ ε :=
  ModuleLWE.advantage_eq_lweAdvantage secretLaw errorLaw D ▸ h _

-- Typed to word: clients reducing on encoded samples use `DecisionModuleLWE.encoded`.
example {m d n q : ℕ → ℕ} [∀ κ, NeZero (q κ)] {noise : (κ : ℕ) → PMF (Fin (n κ) → ZMod (q κ))}
    (h : DecisionModuleLWE m d n q noise) (W : Crypto.Distinguisher) (hW : IsPPT encBool W) :
    Negligible fun κ => Game.advantage
      (distinguishingGame (ModuleLWE.realEnsemble m d n q noise κ) (W κ))
      (distinguishingGame (ModuleLWE.uniformEnsemble m d n q κ) (W κ)) :=
  h.encoded W hW

-- Word to typed: the word-level assumption bounds every typed PPT distinguisher's advantage with
-- a uniform secret and independent polynomial errors.
example {m d n q : ℕ → ℕ} [∀ κ, NeZero (q κ)] {noise : (κ : ℕ) → PMF (Fin (n κ) → ZMod (q κ))}
    (h : ComputationallyIndistinguishable (ModuleLWE.realEnsemble m d n q noise)
      (ModuleLWE.uniformEnsemble m d n q))
    (D : ModuleLWE.Distinguisher m d n q) (hD : D.IsPPT) :
    Negligible fun κ =>
      ModuleLWE.advantage (PMF.uniformOfFintype (Fin (d κ) → Fin (n κ) → ZMod (q κ)))
        (PMF.pi fun _ : Fin (m κ) => noise κ) (D κ) :=
  (decisionModuleLWE_iff_encoded m d n q noise).mpr h D hD

end CslibFrontierTests.DecisionModuleLWE

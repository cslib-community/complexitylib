/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.LWE.Module
import CslibFrontier.Probability.PMF.Uniform

/-!
Regression clients for typed decision Module-LWE: a concrete sample over `ℤ_5[X] / (X^2 + 1)`,
the encoded input words, which are the words the encoded ensembles sample, the bridge to LWE over
`Negacyclic (ZMod q) n`, both directions of `decisionModuleLWEWith_iff_encoded`, the uniform-secret
case `DecisionModuleLWE`, and a satisfying instance of `DecisionModuleLWEWith`.
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

-- Typed to word: clients reducing on encoded samples use `DecisionModuleLWEWith.encoded`.
example {m d n q : ℕ → ℕ} [∀ κ, NeZero (q κ)]
    {secret : (κ : ℕ) → PMF (Fin (d κ) → Fin (n κ) → ZMod (q κ))}
    {error : (κ : ℕ) → PMF (Fin (m κ) → Fin (n κ) → ZMod (q κ))}
    (h : DecisionModuleLWEWith m d n q secret error) (W : Crypto.Distinguisher)
    (hW : IsPPT encBool W) :
    Negligible fun κ => Game.advantage
      (distinguishingGame (ModuleLWE.realEnsemble m d n q secret error κ) (W κ))
      (distinguishingGame (ModuleLWE.uniformEnsemble m d n q κ) (W κ)) :=
  h.encoded W hW

-- Word to typed: the word-level assumption bounds every typed PPT distinguisher's advantage for
-- the same secret and error laws.
example {m d n q : ℕ → ℕ} [∀ κ, NeZero (q κ)]
    {secret : (κ : ℕ) → PMF (Fin (d κ) → Fin (n κ) → ZMod (q κ))}
    {error : (κ : ℕ) → PMF (Fin (m κ) → Fin (n κ) → ZMod (q κ))}
    (h : ComputationallyIndistinguishable (ModuleLWE.realEnsemble m d n q secret error)
      (ModuleLWE.uniformEnsemble m d n q))
    (D : ModuleLWE.Distinguisher m d n q) (hD : D.IsPPT) :
    Negligible fun κ => ModuleLWE.advantage (secret κ) (error κ) (D κ) :=
  (decisionModuleLWEWith_iff_encoded m d n q secret error).mpr h D hD

-- The uniform-secret assumption is the law-general one at a uniform secret and product errors, so
-- its clients use the law-general API directly.
example {m d n q : ℕ → ℕ} [∀ κ, NeZero (q κ)] {noise : (κ : ℕ) → PMF (Fin (n κ) → ZMod (q κ))}
    (h : DecisionModuleLWE m d n q noise) (D : ModuleLWE.Distinguisher m d n q) (hD : D.IsPPT) :
    Negligible fun κ =>
      ModuleLWE.advantage (PMF.uniformOfFintype (Fin (d κ) → Fin (n κ) → ZMod (q κ)))
        (PMF.pi fun _ : Fin (m κ) => noise κ) (D κ) :=
  (decisionModuleLWE_iff_decisionModuleLWEWith m d n q noise).mp h D hD

example {m d n q : ℕ → ℕ} [∀ κ, NeZero (q κ)] {noise : (κ : ℕ) → PMF (Fin (n κ) → ZMod (q κ))}
    (h : DecisionModuleLWE m d n q noise) :
    ComputationallyIndistinguishable
      (ModuleLWE.realEnsemble m d n q
        (fun κ => PMF.uniformOfFintype (Fin (d κ) → Fin (n κ) → ZMod (q κ)))
        fun κ => PMF.pi fun _ : Fin (m κ) => noise κ)
      (ModuleLWE.uniformEnsemble m d n q) :=
  h.encoded

/-- With uniform errors the real game is the random game, for every secret law: `A · s + e` is
uniform and independent of `(A, s)`. -/
theorem realGame_uniform_error_eq_randomGame {m d n q : ℕ} [NeZero q]
    (secretLaw : PMF (Fin d → Fin n → ZMod q))
    (D : Matrix (Fin m) (Fin d) (Fin n → ZMod q) → (Fin m → Fin n → ZMod q) → ProbComp Bool) :
    ModuleLWE.realGame secretLaw (PMF.uniformOfFintype _) D = ModuleLWE.randomGame D := by
  simp only [ModuleLWE.realGame, ModuleLWE.randomGame, ModuleLWE.eval_realExperiment,
    ModuleLWE.eval_randomExperiment, PMF.monad_bind_eq_bind]
  refine Eq.trans ?_ (PMF.bind_const secretLaw _)
  congr 1 with s : 1
  rw [PMF.bind_comm (PMF.uniformOfFintype (Fin m → Fin n → ZMod q))]
  congr 1 with A : 1
  exact PMF.uniformOfFintype_bind_equiv (Equiv.addLeft (moduleSISMap A s))
    fun b => ProbComp.eval (D A b)

/-- **`DecisionModuleLWEWith` is satisfiable**: with uniform errors every distinguisher has
advantage `0`, whatever the secret law and parameters. -/
theorem decisionModuleLWEWith_uniform_error (m d n q : ℕ → ℕ) [∀ κ, NeZero (q κ)]
    (secret : (κ : ℕ) → PMF (Fin (d κ) → Fin (n κ) → ZMod (q κ))) :
    DecisionModuleLWEWith m d n q secret
      fun κ => PMF.uniformOfFintype (Fin (m κ) → Fin (n κ) → ZMod (q κ)) := by
  intro D _
  simp only [realGame_uniform_error_eq_randomGame, Game.advantage_self]
  exact negligible_zero

end CslibFrontierTests.DecisionModuleLWE

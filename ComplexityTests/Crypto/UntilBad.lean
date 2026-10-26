/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.PMF.Uniform
import Complexity.Crypto.Game.UntilBad
import Complexity.Probability.PMF

/-!
# Tests for identical-until-bad hops

One handler answers a fair bit and raises a flag when the bit is `true`; the other draws the same
bit for the flag but always answers `false`. They agree until the flag is raised. For the program
that asks once and returns the answer, the difference lemma is tight: the success probabilities
are `1 / 2` and `0`, and the flag is raised with probability `1 / 2` under both handlers.
-/

namespace ComplexityTests.Crypto.UntilBad

open Cslib Cslib.Probability Cslib.OracleComp

/-- Answer a fair bit, raising the flag when it is `true`. -/
noncomputable def honest (_ : Unit) : StateT Bool PMF Bool := fun s =>
  (PMF.uniformOfFintype Bool).map fun b => (b, s || b)

/-- Answer `false`, raising the flag on a fair bit. -/
noncomputable def silent (_ : Unit) : StateT Bool PMF Bool := fun s =>
  (PMF.uniformOfFintype Bool).map fun b => (false, s || b)

/-- The two handlers agree until the flag is raised. -/
theorem identicalUntilBad :
    IdenticalUntilBad (spec := fun _ : Unit => Bool) honest silent fun s => s = true where
  agree q s hs a s' hs' := by
    simp only [Bool.not_eq_true] at hs hs'
    subst hs hs'
    cases a <;> simp [honest, silent, PMF.uniformOfFintype_apply]
  absorb_first q s hs x hx := by
    obtain ⟨b, -, rfl⟩ := (_root_.PMF.mem_support_map_iff _ _ _).mp hx
    simp [hs]
  absorb_second q s hs x hx := by
    obtain ⟨b, -, rfl⟩ := (_root_.PMF.mem_support_map_iff _ _ _).mp hx
    simp [hs]

/-- Ask once and return the answer. -/
abbrev askOnce : OracleComp (fun _ : Unit => Bool) Bool := query ()

/-- The flag is raised with probability `1 / 2`. -/
theorem toOuterMeasure_bad :
    ((interpret honest askOnce).run false).toOuterMeasure {x | x.2 = true} = 1 / 2 := by
  classical
  rw [askOnce, interpret_query]
  change ((honest ()) false).toOuterMeasure {x | x.2 = true} = 1 / 2
  rw [honest, _root_.PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_uniformOfFintype]
  norm_num
  rw [Finset.card_eq_one.mpr ⟨true, by ext a; cases a <;> simp⟩]
  simp

/-- The difference lemma is tight here: success `1 / 2` against `0`, with bad probability `1 / 2`
under both handlers. -/
example : |(((interpret honest askOnce).run false).bind (fun x => PMF.pure x.1) true).toReal -
    (((interpret silent askOnce).run false).bind (fun x => PMF.pure x.1) true).toReal| ≤ 1 / 2 := by
  have h := identicalUntilBad.abs_sub_le askOnce false (fun x => PMF.pure x.1) true
  rwa [toOuterMeasure_bad, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at h

example : ((interpret silent askOnce).run false).toOuterMeasure {x | x.2 = true} = 1 / 2 := by
  rw [← identicalUntilBad.bad_eq, toOuterMeasure_bad]

open Cslib.Crypto Cslib.Crypto.Game
open scoped NNReal ENNReal

example (o : List Bool → List Bool) (b : Bool) :
    runStatelessOracle o (pure b) PMF.pure = PMF.pure b :=
  runStatelessOracle_pure o b PMF.pure

example {α β : Type} (μ : PMF β) (o : List Bool → List Bool)
    (prog : WordOracleComp Unit α) (next : β → α → Game) :
    (μ.bind fun b => runStatelessOracle o prog (next b)) =
      runStatelessOracle o prog (fun a => μ.bind fun b => next b a) :=
  bind_runStatelessOracle_comm μ o prog next

example {q : ℕ} [NeZero q] (x₀ : ZMod q)
    (g₁ g₂ : ZMod q → Game) (heq : ∀ x ≠ x₀, g₁ x = g₂ x) :
    Game.advantage
      ((PMF.uniformOfFintype (ZMod q)).bind g₁)
      ((PMF.uniformOfFintype (ZMod q)).bind g₂) ≤ 1 / (q : ℝ≥0) :=
  advantage_uniform_bind_of_eq_of_ne x₀ g₁ g₂ heq

example {T α : Type} (μ : PMF T)
    (o₁ : T → List Bool → List Bool) (o₂ : List Bool → List Bool)
    (isBad : T → List Bool → Bool) (next : T → α → Game)
    {Q q : ℕ} [NeZero q]
    {prog : WordOracleComp Unit α} (hq : prog.IsQueryBounded Q)
    (hagree : ∀ τ req, isBad τ req = false → o₁ τ req = o₂ req)
    (hbad : ∀ req, (∑' τ, μ τ * if isBad τ req then (1 : ℝ≥0∞) else 0) ≤ (q : ℝ≥0∞)⁻¹) :
    Game.advantage
      (μ.bind fun τ => runStatelessOracle (o₁ τ) prog (next τ))
      (μ.bind fun τ => runStatelessOracle o₂ prog (next τ)) ≤
      (Q : ℝ≥0) / (q : ℝ≥0) :=
  advantage_runStatelessOracle_bind_le μ o₁ o₂ isBad next hq hagree hbad

end ComplexityTests.Crypto.UntilBad

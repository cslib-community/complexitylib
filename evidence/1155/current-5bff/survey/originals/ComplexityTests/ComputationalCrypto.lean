/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.OneWay
import Complexity.Crypto.Computational.Basic
import Complexity.Crypto.Negligible.Basic
import Complexity.Crypto.Primitives.PRG.Game
import Complexity.Tactic.PPT

/-! Tests of uniform parameterized programs and the one-way-function experiment. -/

namespace ComplexityTests.ComputationalCrypto

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

example {ε δ : ℕ → ℝ≥0} (hε : Negligible ε) (hδ : Negligible δ) :
    Negligible (fun n => (n ^ 3 + 2 : ℕ) * ε n + δ n) := by fun_prop

example : ¬ Negligible (fun _ => (1 : ℝ≥0)) := not_negligible_const one_ne_zero

-- The explicit decay criterion constructs a bound and exposes thresholds for a nonzero family.
example : Negligible (fun _ => (0 : ℝ≥0)) := by
  apply (negligible_iff _).mpr
  intro k δ hδ
  exact ⟨0, fun n _ => by simpa only [mul_zero] using hδ⟩

example (k : ℕ) (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ m : ℕ, ∀ n ≥ m, n ^ k * (1 / 4 : ℝ≥0) ^ n < δ :=
  (negligible_iff _).mp (negligible_geometric (by norm_num : (1 / 4 : ℝ≥0) < 1)) k δ hδ

example : IsPPT encBits (fun _ input => pure input) := by ppt

example : IsPPT encBits (fun n _ => BitString.sampleList (n * n)) := by ppt

example (adversary : Inverter) (ha : IsPPT encBits adversary) :
    IsPPT encBool (fun n input => do
      let seed ← BitString.sampleList (n + input.length)
      let candidate ← adversary (n + 1) (input ++ seed)
      return candidate.length ≤ n) := by ppt

example (f : List Bool → List Bool) (hf : ComputableTidilyInPolyTime f encBits encBits)
    (adversary : Inverter) (ha : IsPPT encBits adversary) :
    IsPPT encBool (fun n _ => inversionGame f adversary n) := by ppt

section

attribute [local irreducible] inversionGame

-- A sampler with no auxiliary argument uses its unary certificate when the parameter changes.
example (f : List Bool → List Bool) (hf : ComputableTidilyInPolyTime f encBits encBits)
    (adversary : Inverter) (ha : IsPPT encBits adversary) :
    IsPPT encBool (fun n input => inversionGame f adversary (n + input.length)) := by ppt

end

private noncomputable def sampleWithPrefix (n : ℕ) (input : List Bool) :
    ProbComp (List Bool) := do
  let seed ← BitString.sampleList n
  return seed ++ input

@[program_certificate]
private theorem sampleWithPrefix_ppt : IsPPT encBits sampleWithPrefix := by
  unfold sampleWithPrefix
  ppt

attribute [irreducible] sampleWithPrefix

section

-- A local re-registration of an existing certificate has an independent auxiliary theorem.
attribute [local program_certificate] sampleWithPrefix_ppt

example : IsPPT encBits sampleWithPrefix := by ppt

end

-- Registered parameterized routines stay folded during composition in either tactic.
example : IsPPT encBits (fun n input => sampleWithPrefix (n + 1) (input ++ input)) := by ppt

example : IsPPTOn (encPair encUnary encBits) encBits
    (fun input => sampleWithPrefix (input.1 + 1) (input.2 ++ input.2)) := by fun_prop

example : IsPPT encBits (fun n input => sampleWithPrefix (n + 1) (input ++ input)) := by fun_prop

private def guardedIdentity (bound : ℕ) (_n : ℕ) (input : List Bool) : ProbComp (List Bool) :=
  pure (if bound = 0 then input else List.replicate (2 ^ input.length) true)

-- Lean ordinarily gives this sole premise the parent's tag; the certificate retains its name.
@[program_certificate hbound]
private theorem guardedIdentity_ppt (bound : ℕ) (hbound : bound = 0) :
    IsPPT encBits (guardedIdentity bound) := by
  subst bound
  unfold guardedIdentity
  ppt

attribute [irreducible] guardedIdentity

example : IsPPT encBits (guardedIdentity 0) := by ppt

-- A false eager premise must fail, rather than admit the side condition during nested search.
example : True := by
  fail_if_success
    suffices IsPPT encBits (guardedIdentity 1) by trivial
    ppt
  trivial

-- Semantic tests are admissible only through a uniform program realization.
example (adversary : Distinguisher) (ha : IsPPT encBool adversary) :
    IsPPTTest (fun n word => ProbComp.eval (adversary n word)) := isPPTTest_eval.mpr ha

example (X : ℕ → PMF (List Bool)) : ComputationallyIndistinguishable X X := .refl _

example {X Y : ℕ → PMF (List Bool)} (h : ComputationallyIndistinguishable X Y) :
    ComputationallyIndistinguishable
      (fun n => (X n).bind (fun word => ProbComp.eval (sampleWithPrefix n word)))
      (fun n => (Y n).bind (fun word => ProbComp.eval (sampleWithPrefix n word))) :=
  h.bind sampleWithPrefix_ppt

-- The finite PRG bridge holds for arbitrary whole-family admissibility restrictions.
example {Seed Output : ℕ → Type}
    [∀ n, Fintype (Seed n)] [∀ n, Nonempty (Seed n)]
    [∀ n, Fintype (Output n)] [∀ n, Nonempty (Output n)]
    (G : PRG.Family Seed Output) (Admissible : (∀ n, PRG.Adversary (Output n)) → Prop)
    (h : G.Secure Admissible) :
    Game.Indistinguishable (fun adversary n => (G n).realExperiment (adversary n))
      (fun adversary n => PRG.Generator.idealExperiment (adversary n)) Admissible :=
  (G.secure_iff_indistinguishable Admissible).mp h

-- A many-to-one function accepts a different preimage, even one of a different length.
example (n : ℕ) :
    ProbComp.eval (inversionGame (fun _ => [true]) (fun _ _ => pure []) n) = PMF.pure true :=
  eval_inversionGame_of_rightInverse _ (fun _ _ => []) (fun _ => rfl) n

example : ¬ OneWay (fun word => word) :=
  not_oneWay_of_inverse _ (fun _ y => y) (by ppt) (fun _ => rfl)

example (word : List Bool) : ¬ OneWay (fun _ => word) := not_oneWay_const word

-- Length-preserving permutations have exactly the claimed ideal output law, without assuming OWPs.
example (n : ℕ) :
    (BitString.uniformList n).bind (fun word =>
      (Cslib.Probability.PMF.uniformOfFintype Bool).map (fun bit => word ++ [bit])) =
        BitString.uniformList (n + 1) := (BitString.uniformList_snoc n).symm

end ComplexityTests.ComputationalCrypto

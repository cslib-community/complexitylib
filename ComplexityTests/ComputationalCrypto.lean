/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.OneWay
import Complexity.Crypto.Computational.Basic
import Complexity.Crypto.Computational.HardCore
import Complexity.Crypto.Negligible.Basic
import Complexity.Crypto.Negligible.Dyadic
import Complexity.Crypto.Primitives.PRG.Game
import Complexity.Tactic.PPT

/-! Tests of uniform parameterized programs and the one-way-function experiment, and checks that
the PPT, pseudorandom-generator and hard-core definitions are not vacuous. -/

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

example : IsPPT encBool (fun n _ =>
    inversionGame (fun x => x ++ [false]) (fun _ y => pure (y.take (y.length - 1))) n) := by ppt

section

attribute [local irreducible] inversionGame

-- A sampler with no auxiliary argument uses its unary certificate when the parameter changes.
example (f : List Bool → List Bool) (hf : ComputableInPolyTime f encBits encBits)
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
example : IsPPTTest (fun n (word : List Bool) =>
    ProbComp.eval ((fun m w => pure (w.length == m)) n word)) :=
  isPPTTest_eval.mpr (by ppt)

example {X Y : ℕ → PMF (List Bool)} (h : ComputationallyIndistinguishable X Y) :
    ComputationallyIndistinguishable
      (fun n => (X n).bind (fun word => ProbComp.eval (sampleWithPrefix n word)))
      (fun n => (Y n).bind (fun word => ProbComp.eval (sampleWithPrefix n word))) :=
  h.bind sampleWithPrefix_ppt

-- The finite PRG bridge holds for arbitrary whole-family admissibility restrictions.
example :
    PRG.Family.Secure (Seed := fun _ => Bool) (Output := fun _ => Bool)
      (fun _ : ℕ => ⟨id⟩) (fun _ => True) := by
  rw [PRG.Family.secure_iff_indistinguishable]
  intro adversary _
  simpa only [PRG.Generator.realExperiment, PRG.Generator.outputDist, PRG.Generator.coe_mk,
    PRG.Generator.idealExperiment, PMF.map_id, Game.advantage_self] using negligible_zero

-- A many-to-one function accepts a different preimage, even one of a different length.
example (n : ℕ) :
    ProbComp.eval (inversionGame (fun _ => [true]) (fun _ _ => pure []) n) = PMF.pure true :=
  eval_inversionGame_of_rightInverse _ (fun _ _ => []) (fun _ => rfl) n

example : ¬ OneWay (fun word => word) :=
  not_oneWay_of_inverse _ (fun _ y => y) (by ppt) (fun _ => rfl)

example : ¬ OneWay (fun _ => [true, false]) := not_oneWay_const [true, false]

-- Appending an independent uniform bit gives this three-bit word its exact uniform probability.
example :
    ((BitString.uniformList 2).bind (fun word =>
      (Cslib.Probability.PMF.uniformOfFintype Bool).map (fun bit => word ++ [bit])))
      [true, false, true] = (1 : ENNReal) / 8 := by
  rw [(BitString.uniformList_snoc 2).symm]
  have h := BitString.uniformList_map_apply id 3 [true, false, true]
  simp only [PMF.map_id, id_eq] at h
  rw [h]
  have hcount : (Finset.univ.filter fun r : Fin 3 → Bool =>
      List.ofFn r = [true, false, true]).card = 1 := by decide
  rw [hcount]
  norm_num

/-! ### Nonvacuity of the efficiency and security definitions

A program with exponentially long output is not PPT, so `IsPPT` is a real restriction. Prepending a
constant bit is not a pseudorandom generator, and the first seed bit is not hard-core for the
identity: the obvious PPT adversaries break them with constant advantage. These rule out a security
definition that holds for every candidate. -/

/-- A program whose output is exponentially long in the unary parameter is not PPT. -/
example : ¬ IsPPT encBits
    (fun n (_ : List Bool) => (pure (List.replicate (2 ^ n) true) : ProbComp (List Bool))) := by
  intro h
  obtain ⟨c, d, hle⟩ := h.on.length_le
  have hbound (n : ℕ) : 2 ^ n ≤ c * (2 * n + 2) ^ d := by
    simpa using hle (n, []) (List.replicate (2 ^ n) true) (by simp)
  obtain ⟨m, hm⟩ := (negligible_iff _).1 (negligible_const_div_two_pow (c * 4 ^ d)) d 1 one_pos
  have hlt := hm (m + 1) (by omega)
  have hnat : 2 ^ (m + 1) ≤ (m + 1) ^ d * (c * 4 ^ d) :=
    calc 2 ^ (m + 1) ≤ c * (2 * (m + 1) + 2) ^ d := hbound (m + 1)
      _ ≤ c * (4 ^ d * (m + 1) ^ d) := by
        rw [← mul_pow]; exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d)
      _ = (m + 1) ^ d * (c * 4 ^ d) := by ring
  have hreal : ((2 : ℝ≥0) ^ (m + 1)) ≤ ((m + 1 : ℕ) : ℝ≥0) ^ d * ((c * 4 ^ d : ℕ) : ℝ≥0) := by
    exact_mod_cast hnat
  rw [mul_div_assoc', div_lt_one (by positivity)] at hlt
  exact absurd hreal (not_le.mpr hlt)

/-- Accept exactly when the first bit is `false`. -/
private def firstBitFalse : Distinguisher := fun _ w => pure (!(w.headD true))

private theorem firstBitFalse_ppt : IsPPT encBool firstBitFalse := by
  unfold firstBitFalse
  ppt

/-- Prepending `false` to a uniform seed is not a pseudorandom generator: the generated words
always start with `false`, uniform words only half of the time. -/
example : ¬ PseudorandomGenerator (fun w => false :: w) (· + 1) := by
  intro h
  have hreal (n : ℕ) :
      distinguishingGame (generatorEnsemble (fun w => false :: w) n) (firstBitFalse n) =
        PMF.pure true := by
    simp [distinguishingGame, generatorEnsemble, firstBitFalse, PMF.bind_map, Function.comp_def]
  have hideal (n : ℕ) :
      distinguishingGame (BitString.uniformList (n + 1)) (firstBitFalse n) =
        PMF.uniformOfFintype Bool := by
    rw [BitString.uniformList_succ]
    simp only [distinguishingGame, firstBitFalse, PMF.monad_bind_eq_bind, PMF.bind_bind,
      PMF.bind_map, Function.comp_def, List.headD_cons, ProbComp.eval_pure, PMF.bind_const]
    ext b
    cases b <;> simp [PMF.bind_apply, PMF.uniformOfFintype_apply]
  have hneg := h.indistinguishable firstBitFalse firstBitFalse_ppt
  simp only [hreal, hideal] at hneg
  refine not_negligible_const ?_ hneg
  rw [Game.advantage, ne_eq, nndist_eq_zero]
  intro heq
  norm_num [Game.succProbability, PMF.uniformOfFintype_apply, ENNReal.toNNReal_ofNat] at heq

/-- Copy the first bit of the input. -/
private def copyFirst : Distinguisher := fun _ w => pure (w.headD false)

private theorem copyFirst_ppt : IsPPT encBool copyFirst := by
  unfold copyFirst
  ppt

/-- The first seed bit is not hard-core for the identity: copying it predicts it always. -/
example : ¬ HardCore id (fun w => w.headD false) := by
  intro h
  have hgame (n : ℕ) :
      ProbComp.eval (predictionGame id (fun w => w.headD false) copyFirst n) = PMF.pure true := by
    simp only [predictionGame, copyFirst, id, ProbComp.eval_bind, ProbComp.eval_pure,
      BitString.eval_sampleList]
    simp
  have hneg := h.unpredictable copyFirst copyFirst_ppt
  have hfun : predictionAdvantage id (fun w => w.headD false) copyFirst =
      fun _ => Game.guessingAdvantage (PMF.pure true) := by
    funext n
    rw [predictionAdvantage, hgame]
  rw [hfun] at hneg
  refine not_negligible_const ?_ hneg
  rw [Game.guessingAdvantage, Game.advantage, ne_eq, nndist_eq_zero]
  intro heq
  norm_num [Game.succProbability, PMF.uniformOfFintype_apply, ENNReal.toNNReal_ofNat] at heq

end ComplexityTests.ComputationalCrypto

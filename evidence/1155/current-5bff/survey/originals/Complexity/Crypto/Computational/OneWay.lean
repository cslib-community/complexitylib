/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Probabilistic.Parameter
public import Complexity.Crypto.Game
public import Complexity.Languages.Probabilistic.BitString
import Complexity.Probability.PMF.Bind
import Complexity.Crypto.Negligible.Basic
import Complexity.Probability.PMF
import Complexity.Tactic.PPT

/-!
# One-way functions and permutations

A polynomial-time function on binary words is one-way when, given its value on a uniform
`n`-bit input and the unary parameter `n`, every uniform PPT inverter has negligible probability
of finding **any** preimage. Recovering the sampled input is not required, and the inverter's
answer is not restricted to the sampled input's length.

`OneWayPermutation` additionally requires a length-preserving bijection. Its inverse exists as a
mathematical function; no efficiency of that inverse is assumed. Such a permutation preserves
the uniform distribution at every input length. These are definitions, not assertions that
one-way functions or permutations exist.

## Main definitions

* `Cslib.Crypto.inversionGame`: sample a challenge and test the inverter's candidate preimage.
* `Cslib.Crypto.OneWay`, `Cslib.Crypto.OneWayPermutation`: uniform computational assumptions.

## Main results

* `Cslib.Crypto.isPPT_inversionGame`: the inversion experiment is uniformly strict PPT.
* `Cslib.Crypto.OneWay.inversion_negligible`: negligible success for each efficient inverter.
* `Cslib.Crypto.OneWayPermutation.uniformList_append_bit`: the ideal one-bit extension is uniform.
* `Cslib.Crypto.not_oneWay_of_le_succProbability`: inverting with probability bounded away from
  zero at every length refutes one-wayness.
* `Cslib.Crypto.not_oneWay_of_inverse`, `not_oneWay_const`: efficient preimages refute one-wayness.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 9.2.

Adapted from Crypto/Computational/OneWay.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using finite fair-bit programs, tidy deterministic
certificates and the upstream nonnegative game API.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- An inverter receives the unary parameter and the image of the sampled input. -/
abbrev Inverter := ℕ → List Bool → ProbComp (List Bool)

/-- The inversion experiment accepts any preimage of its challenge. -/
noncomputable def inversionGame (f : List Bool → List Bool) (adversary : Inverter) (n : ℕ) :
    ProbComp Bool := do
  let input ← BitString.sampleList n
  let candidate ← adversary n (f input)
  return f candidate == f input

/-- Run the complete inversion experiment on its unary parameter. -/
@[program_certificate]
theorem isPPTOn_inversionGame {f : List Bool → List Bool} {adversary : Inverter}
    (hf : ComputableInPolyTime f encBits encBits) (ha : IsPPT encBits adversary) :
    IsPPTOn encUnary encBool (inversionGame f adversary) := by
  unfold inversionGame
  ppt

/-- The inversion experiment is uniformly PPT, independently of the unused auxiliary input. -/
@[program_certificate]
theorem isPPT_inversionGame {f : List Bool → List Bool} {adversary : Inverter}
    (hf : ComputableInPolyTime f encBits encBits) (ha : IsPPT encBits adversary) :
    IsPPT encBool (fun n _ => inversionGame f adversary n) := by ppt

/-- One plain polynomial-time algorithm evaluates the function. Every uniform strict PPT inverter
has negligible success over the uniform input and its own independent random coins. -/
structure OneWay (f : List Bool → List Bool) : Prop where
  /-- A deterministic polynomial-time algorithm evaluates the function. -/
  polyTime : ComputableInPolyTime f encBits encBits
  /-- Inversion is indistinguishable from certain failure in the common game calculus. -/
  secure : Game.Indistinguishable (fun adversary n => ProbComp.eval (inversionGame f adversary n))
    (fun _ _ => PMF.pure false) (IsPPT encBits)

/-- The shared game definition gives the usual negligible inversion probability. -/
theorem OneWay.inversion_negligible {f : List Bool → List Bool} (h : OneWay f)
    (adversary : Inverter) (hPPT : IsPPT encBits adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (inversionGame f adversary n))) := by
  simpa only [Game.advantage_pure_false] using h.secure adversary hPPT

/-- Establish one-wayness by bounding every efficient inverter's success probability. -/
theorem OneWay.of_inversion_negligible {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits)
    (h : ∀ adversary : Inverter, IsPPT encBits adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (inversionGame f adversary n)))) :
    OneWay f := by
  refine ⟨hf, fun adversary hPPT => ?_⟩
  simpa only [Game.advantage_pure_false] using h adversary hPPT

/-- A length-preserving permutation that is one-way against every uniform PPT inverter. -/
structure OneWayPermutation (f : List Bool → List Bool) : Prop where
  /-- Evaluation is polynomial time, and inversion has negligible success. -/
  oneWay : OneWay f
  /-- The permutation acts separately on words of each length. -/
  length_eq : ∀ word, (f word).length = word.length
  /-- Every word has exactly one preimage; finding it need not be efficient. -/
  bijective : Function.Bijective f

/-- A one-way permutation preserves the uniform distribution at each input length. -/
theorem OneWayPermutation.uniformList_map {f : List Bool → List Bool}
    (hf : OneWayPermutation f) (n : ℕ) :
    (BitString.uniformList n).map f = BitString.uniformList n :=
  BitString.uniformList_map_of_bijective f hf.bijective hf.length_eq n

/-- A permuted uniform seed followed by an independent fair bit is exactly uniform at the
expanded length. Security is needed when replacing the independent bit by a hard-core predicate. -/
theorem OneWayPermutation.uniformList_append_bit {f : List Bool → List Bool}
    (hf : OneWayPermutation f) (n : ℕ) :
    (BitString.uniformList n).bind (fun word =>
      (PMF.uniformOfFintype Bool).map (fun bit => f word ++ [bit])) =
        BitString.uniformList (n + 1) := by
  change (BitString.uniformList n).bind
    ((fun word => (PMF.uniformOfFintype Bool).map (fun bit => word ++ [bit])) ∘ f) = _
  rw [← PMF.bind_map, hf.uniformList_map]
  exact (BitString.uniformList_snoc n).symm

/-- For an injective function, accepting any preimage is equivalent to recovering the sampled
input. The general inversion experiment does not make this assumption. -/
theorem inversionGame_eq_of_injective (f : List Bool → List Bool) (hf : Function.Injective f)
    (adversary : Inverter) (n : ℕ) :
    inversionGame f adversary n = (do
      let input ← BitString.sampleList n
      let candidate ← adversary n (f input)
      return candidate == input) := by
  have heq (candidate input : List Bool) : (f candidate == f input) = (candidate == input) := by
    simp only [beq_eq_decide, hf.eq_iff]
  simp only [inversionGame, heq]

/-- An inverter that, told the input length, always returns a preimage makes the experiment
always succeed. -/
theorem eval_inversionGame_of_rightInverse (f : List Bool → List Bool)
    (inverse : ℕ → List Bool → List Bool) (h : ∀ x, f (inverse x.length (f x)) = f x) (n : ℕ) :
    ProbComp.eval (inversionGame f (fun n y => pure (inverse n y)) n) = PMF.pure true := by
  have hgame : ProbComp.eval (inversionGame f (fun n y => pure (inverse n y)) n) =
      (BitString.uniformList n).map fun x => f (inverse n (f x)) == f x := by
    simp [inversionGame]
  rw [hgame, ← PMF.bind_pure_comp, PMF.bind_congr_on_support _ _ (fun _ => PMF.pure true)
    fun x hx => by
      rw [Function.comp_apply, ← BitString.length_of_mem_support_uniformList hx, h,
        beq_self_eq_true],
    PMF.bind_const]

/-- **Inverting with probability bounded away from zero refutes one-wayness**: an efficient
inverter whose success probability is at least a fixed `c > 0` at every length. -/
theorem not_oneWay_of_le_succProbability {f : List Bool → List Bool} {c : ℝ≥0} (hc : c ≠ 0)
    (inverter : Inverter) (hPPT : IsPPT encBits inverter)
    (h : ∀ n, c ≤ Game.succProbability (ProbComp.eval (inversionGame f inverter n))) :
    ¬ OneWay f := fun hf =>
  not_negligible_const hc (negligible_of_le (hf.inversion_negligible inverter hPPT) h)

/-- Efficiently finding any preimage, told the input length, contradicts one-wayness. -/
theorem not_oneWay_of_inverse (f : List Bool → List Bool) (inverse : ℕ → List Bool → List Bool)
    (hPPT : IsPPT encBits (fun n y => pure (inverse n y)))
    (hinv : ∀ x, f (inverse x.length (f x)) = f x) : ¬ OneWay f :=
  not_oneWay_of_le_succProbability one_ne_zero _ hPPT fun n => by
    rw [Game.succProbability, eval_inversionGame_of_rightInverse f inverse hinv n,
      PMF.pure_apply_self, ENNReal.toNNReal_one]

/-- Constant functions are not one-way: the empty word is always a preimage. -/
theorem not_oneWay_const (word : List Bool) : ¬ OneWay (fun _ => word) :=
  not_oneWay_of_inverse _ (fun _ _ => [])
    (ComputableTidilyInPolyTime.const []).isPPT (fun _ => rfl)

end Cslib.Crypto

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Nonuniform.Basic
public import Complexity.Crypto.Computational.ZeroKnowledge
import Complexity.Tactic.PPT

/-!
# Auxiliary-input zero knowledge from a nonuniform generator

`GMW.AdvicePRG enc generator length` is the security premise of the auxiliary-input
Goldreich–Micali–Wigderson theorem
`PseudorandomGenerator.exists_auxiliaryInputZeroKnowledge_of_mem_NP`: a test reading an instance,
a witness and an auxiliary input from arbitrary polynomially bounded families cannot distinguish
the generator's output at seed length `n + 7` from uniform. A nonuniform pseudorandom generator
satisfies it: the three families form one advice value under the pair encoding, which the test
reads without decoding, and the parameter shift by `7` is polynomial-time preprocessing.

This discharges the premise from `NonuniformPRG`. It does not derive a nonuniform generator from a
(nonuniform) one-way function; that is milestone M2 of [#2316].

## Main results

* `Cslib.Crypto.NonuniformPRG.advicePRG`: a nonuniform PRG satisfies `GMW.AdvicePRG`.
* `Cslib.Crypto.NonuniformPRG.exists_auxiliaryInputZeroKnowledge_of_mem_NP`: given a nonuniform
  PRG with stretch at least `3 * k + 1`, every language in `NP` has an auxiliary-input
  zero-knowledge proof system.

## References

* [O. Goldreich, S. Micali, A. Wigderson, *Proofs that Yield Nothing but Their Validity or All
  Languages in NP Have Zero-Knowledge Proof Systems*][GoldreichMicaliWigderson1991]

[#2316]: https://github.com/cslib-community/complexitylib/issues/2316
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Complexity Turing.MultiTapeTM

/-- A **nonuniform PRG satisfies the GMW advice premise** for every instance encoding: the
instance, witness and auxiliary-input families together are one polynomially bounded advice
family, and the test runs at parameter `n + 7` on the advice for `n`. -/
theorem NonuniformPRG.advicePRG {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : NonuniformPRG generator length) {α : Type} (enc : α ↪ List Bool) :
    GMW.AdvicePRG enc generator length := by
  refine ⟨h.polyTime, h.length_eq, fun test htest a w z ha hw hz => ?_⟩
  let encAdvice := encPair enc (encPair encBits encBits)
  have hshift : IsPPTOn (encPair (encPair encUnary encAdvice) encBits) encBool
      (fun input : (ℕ × (α × (List Bool × List Bool))) × List Bool =>
        test ((input.1.1 - 7, input.1.2), input.2)) :=
    htest.preprocess (by fun_prop)
  have hsub : PolynomiallyBounded (fun m => m - 7) := PolynomiallyBounded.id.tsub _
  have ha' := ha.comp hsub
  have hw' := hw.comp hsub
  have hz' := hz.comp hsub
  have hadvice : PolynomiallyBounded (fun m =>
      (encAdvice (a (m - 7), w (m - 7), z (m - 7))).length) := by
    simp only [encAdvice, length_encPair, encBits, Function.Embedding.coe_refl, id]
    fun_prop
  have hneg := ((h.secure _ hadvice).negligible_encoded hshift).shift 7
  refine hneg.congr' (Filter.Eventually.of_forall fun n => ?_)
  simp only [Nat.add_sub_cancel, eval_bind_eq_distinguishingGame, ProbComp.eval_map,
    BitString.eval_sampleList, generatorEnsemble]

/-- **Auxiliary-input GMW zero knowledge from a nonuniform PRG.** Given a nonuniform
pseudorandom generator with stretch at least `3 * k + 1`, every language `A ∈ NP enc` has a
computational zero-knowledge interactive proof system satisfying auxiliary-input zero knowledge
(`ZeroKnowledgeProof.AuxiliaryInputZeroKnowledge`). Soundness error is the constant of
`ZeroKnowledgeProof`, not negligible. -/
theorem NonuniformPRG.exists_auxiliaryInputZeroKnowledge_of_mem_NP
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : NonuniformPRG generator length) (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (hA : A ∈ NP enc) :
    ∃ zk : ZeroKnowledgeProof enc A, zk.AuxiliaryInputZeroKnowledge :=
  h.toPRG.exists_auxiliaryInputZeroKnowledge_of_mem_NP hstretch (h.advicePRG enc) hA

end Cslib.Crypto

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Nonuniform.Basic
public import CslibFrontier.Crypto.Computational.ZeroKnowledge
public import CslibFrontier.Crypto.Computational.ZeroKnowledge.Levin
public import CslibFrontier.Crypto.Computational.ZeroKnowledge.Amplification
import CslibFrontier.Tactic.PPT

/-!
# Auxiliary-input zero knowledge from a nonuniform generator or one-way function

`GMW.AdvicePRG enc generator length` is the security premise of the auxiliary-input
Goldreich–Micali–Wigderson theorems
`PseudorandomGenerator.exists_auxiliaryInputZeroKnowledge_of_mem_NP` and
`PseudorandomGenerator.exists_auxiliaryInputZKProof_of_mem_NP`: a test reading an instance,
a witness and an auxiliary input from arbitrary polynomially bounded families cannot distinguish
the generator's output at seed length `n + 7` from uniform. A nonuniform pseudorandom generator
satisfies it: the three families form one advice value under the pair encoding, which the test
reads without decoding, and the parameter shift by `7` is polynomial-time preprocessing.

Composing this bridge with `NonuniformOneWay.exists_nonuniformPRG_three_mul` derives
auxiliary-input zero knowledge (`AuxiliaryInputZeroKnowledge`, and hence the unbounded-`z` and
instance-indexed forms in `CslibFrontier.Crypto.Computational.ZeroKnowledge.AuxClock`) for every
language and relation in `NP` from any nonuniform one-way function, both at the single-session GMW
soundness error `1 / 3` (`ZeroKnowledgeProof`) and at negligible soundness `(1 / 3) ^ (n + 1)` via
`(n + 1)`-fold sequential repetition (`ZKProof`, `ZKProof.NegligibleSoundness`).

## Main results

* `Cslib.Crypto.NonuniformPRG.advicePRG`: a nonuniform PRG satisfies `GMW.AdvicePRG`.
* `Cslib.Crypto.NonuniformPRG.exists_auxiliaryInputZeroKnowledge_of_mem_NP`,
  `Cslib.Crypto.NonuniformPRG.exists_auxiliaryInputZeroKnowledge_of_npRelation`: single-session
  auxiliary-input zero knowledge from any nonuniform PRG.
* `Cslib.Crypto.NonuniformOneWay.exists_auxiliaryInputZeroKnowledge_of_mem_NP`,
  `Cslib.Crypto.NonuniformOneWay.exists_auxiliaryInputZeroKnowledge_of_npRelation`: single-session
  auxiliary-input zero knowledge from any nonuniform one-way function.
* `Cslib.Crypto.NonuniformPRG.exists_zkProof_of_mem_NP`,
  `Cslib.Crypto.NonuniformPRG.exists_zkProof_of_npRelation`: soundness-amplified
  (`(1 / 3) ^ (n + 1)`, `ZKProof.NegligibleSoundness`) auxiliary-input zero knowledge from a
  nonuniform PRG.
* `Cslib.Crypto.NonuniformOneWay.exists_zkProof_of_mem_NP`,
  `Cslib.Crypto.NonuniformOneWay.exists_zkProof_of_npRelation`: **Goldreich–Micali–Wigderson
  theorem in full** — every nonuniform one-way function yields an auxiliary-input zero-knowledge
  proof system with negligible soundness `(1 / 3) ^ (n + 1)` for every language in `NP` and for
  every NP relation using the relation's own witnesses (and hence
  `ZKProof.UnboundedAuxiliaryInputZeroKnowledge` and
  `ZKProof.InstanceAuxiliaryInputZeroKnowledge`).

## References

* [O. Goldreich, S. Micali, A. Wigderson, *Proofs that Yield Nothing but Their Validity or All
  Languages in NP Have Zero-Knowledge Proof Systems*][GoldreichMicaliWigderson1991]
* [O. Goldreich, *Foundations of Cryptography: Volume 1, Basic Tools*][Goldreich2001],
  Sections 4.3–4.4.

[#2316]: https://github.com/cslib-community/cslib-frontier/issues/2316
-/

public section

namespace Cslib.Crypto

open Probability Complexity Turing.MultiTapeTM
open scoped ENNReal

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
    htest.preprocess
      (prepare := fun input : (ℕ × (α × (List Bool × List Bool))) × List Bool =>
        ((input.1.1 - 7, input.1.2), input.2))
      (by dsimp only [encAdvice]; fun_prop)
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

/-- Truncating any nonuniform PRG to one bit of stretch and amplifying gives the GMW length
`3 * n + 1`. -/
private theorem NonuniformPRG.exists_three_mul {generator : List Bool → List Bool}
    {length : ℕ → ℕ} (h : NonuniformPRG generator length) :
    ∃ generator' : List Bool → List Bool, NonuniformPRG generator' (fun n => 3 * n + 1) :=
  ⟨_, (h.truncate (fun n => n + 1) (by fun_prop) h.stretch fun n => n.lt_succ_self).amplify
    (fun n => 3 * n + 1) (by fun_prop) fun n => by omega⟩

/-- **Auxiliary-input GMW zero knowledge from a nonuniform PRG.** Given any nonuniform
pseudorandom generator, every language `A ∈ NP enc` has a computational zero-knowledge
interactive proof system satisfying auxiliary-input zero knowledge
(`ZeroKnowledgeProof.AuxiliaryInputZeroKnowledge`). The proof first stretches the generator to
length `3 * k + 1`. Soundness error is the constant of `ZeroKnowledgeProof`, not negligible. -/
theorem NonuniformPRG.exists_auxiliaryInputZeroKnowledge_of_mem_NP
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : NonuniformPRG generator length) (hA : A ∈ NP enc) :
    ∃ zk : ZeroKnowledgeProof enc A, zk.AuxiliaryInputZeroKnowledge := by
  obtain ⟨_, h⟩ := h.exists_three_mul
  exact h.toPRG.exists_auxiliaryInputZeroKnowledge_of_mem_NP (fun _ => le_rfl) (h.advicePRG enc) hA

/-- **Auxiliary-input GMW zero knowledge for NP relations from a nonuniform PRG.** Given any
nonuniform pseudorandom generator, every NP relation `R` has a computational zero-knowledge
interactive proof system whose honest prover uses `R`'s own witnesses and satisfies
auxiliary-input zero knowledge (`ZeroKnowledgeProof.AuxiliaryInputZeroKnowledge`). -/
theorem NonuniformPRG.exists_auxiliaryInputZeroKnowledge_of_npRelation
    {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : NonuniformPRG generator length) (R : NPRelation enc) :
    ∃ zk : ZeroKnowledgeProof enc R.language,
      (∀ a w, zk.isWitness a w = true ↔ R.IsWitness a w) ∧ zk.AuxiliaryInputZeroKnowledge := by
  obtain ⟨_, h⟩ := h.exists_three_mul
  exact h.toPRG.exists_auxiliaryInputZeroKnowledge_of_npRelation (fun _ => le_rfl)
    (h.advicePRG enc) R

/-- **Auxiliary-input GMW zero knowledge from a nonuniform one-way function.** If a nonuniform
one-way function exists, every language `A ∈ NP enc` has a computational zero-knowledge interactive
proof system satisfying auxiliary-input zero knowledge
(`ZeroKnowledgeProof.AuxiliaryInputZeroKnowledge`, and hence
`ZeroKnowledgeProof.UnboundedAuxiliaryInputZeroKnowledge` and
`ZeroKnowledgeProof.InstanceAuxiliaryInputZeroKnowledge`). Soundness error is the constant `1 / 3`
of `ZeroKnowledgeProof`; negligible soundness is established by sequential repetition. -/
theorem NonuniformOneWay.exists_auxiliaryInputZeroKnowledge_of_mem_NP
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {f : List Bool → List Bool} (hf : NonuniformOneWay f) (hA : A ∈ NP enc) :
    ∃ zk : ZeroKnowledgeProof enc A, zk.AuxiliaryInputZeroKnowledge := by
  obtain ⟨generator, hgenerator⟩ := hf.exists_nonuniformPRG_three_mul
  exact hgenerator.exists_auxiliaryInputZeroKnowledge_of_mem_NP hA

/-- **Auxiliary-input GMW zero knowledge for NP relations from a nonuniform one-way function.** If
a nonuniform one-way function exists, every NP relation `R` has a computational zero-knowledge
interactive proof system whose honest prover uses `R`'s own witnesses and satisfies auxiliary-input
zero knowledge (`ZeroKnowledgeProof.AuxiliaryInputZeroKnowledge`). -/
theorem NonuniformOneWay.exists_auxiliaryInputZeroKnowledge_of_npRelation
    {α : Type} {enc : α ↪ List Bool}
    {f : List Bool → List Bool} (hf : NonuniformOneWay f) (R : NPRelation enc) :
    ∃ zk : ZeroKnowledgeProof enc R.language,
      (∀ a w, zk.isWitness a w = true ↔ R.IsWitness a w) ∧ zk.AuxiliaryInputZeroKnowledge := by
  obtain ⟨generator, hgenerator⟩ := hf.exists_nonuniformPRG_three_mul
  exact hgenerator.exists_auxiliaryInputZeroKnowledge_of_npRelation R

/-- **Soundness-amplified auxiliary-input GMW zero knowledge from a nonuniform PRG.** Given any
nonuniform pseudorandom generator, every language `A ∈ NP enc` has a computational zero-knowledge
interactive proof system with negligible soundness `(1 / 3) ^ (n + 1)`
(`ZKProof.NegligibleSoundness`) and general auxiliary-input zero knowledge
(`ZKProof.AuxiliaryInputZeroKnowledge`, and hence `ZKProof.UnboundedAuxiliaryInputZeroKnowledge` and
`ZKProof.InstanceAuxiliaryInputZeroKnowledge`). -/
theorem NonuniformPRG.exists_zkProof_of_mem_NP
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : NonuniformPRG generator length) (hA : A ∈ NP enc) :
    ∃ zk : ZKProof enc A (fun n => (1 / 3 : ENNReal) ^ (n + 1)),
      zk.NegligibleSoundness ∧ zk.AuxiliaryInputZeroKnowledge := by
  obtain ⟨_, h⟩ := h.exists_three_mul
  exact h.toPRG.exists_auxiliaryInputZKProof_of_mem_NP (fun _ => le_rfl) (h.advicePRG enc) hA

/-- **Soundness-amplified auxiliary-input GMW zero knowledge for NP relations from a nonuniform
PRG.** Given any nonuniform pseudorandom generator, every NP relation `R` has a computational
zero-knowledge interactive proof system with negligible soundness `(1 / 3) ^ (n + 1)` and general
auxiliary-input zero knowledge whose honest prover uses `R`'s own witnesses. -/
theorem NonuniformPRG.exists_zkProof_of_npRelation
    {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : NonuniformPRG generator length) (R : NPRelation enc) :
    ∃ zk : ZKProof enc R.language (fun n => (1 / 3 : ENNReal) ^ (n + 1)),
      (∀ a w, zk.isWitness a w = true ↔ R.IsWitness a w) ∧
      zk.NegligibleSoundness ∧ zk.AuxiliaryInputZeroKnowledge := by
  obtain ⟨_, h⟩ := h.exists_three_mul
  exact h.toPRG.exists_auxiliaryInputZKProof_of_npRelation (fun _ => le_rfl) (h.advicePRG enc) R

/-- **Goldreich–Micali–Wigderson theorem in full (from a nonuniform one-way function).** If a
nonuniform one-way function exists, every language `A ∈ NP enc` has a computational zero-knowledge
interactive proof system with negligible soundness `(1 / 3) ^ (n + 1)` against computationally
unbounded stateful provers (`ZKProof.NegligibleSoundness`) and general auxiliary-input zero
knowledge (`ZKProof.AuxiliaryInputZeroKnowledge`, and hence
`ZKProof.UnboundedAuxiliaryInputZeroKnowledge` and
`ZKProof.InstanceAuxiliaryInputZeroKnowledge`). -/
theorem NonuniformOneWay.exists_zkProof_of_mem_NP
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {f : List Bool → List Bool} (hf : NonuniformOneWay f) (hA : A ∈ NP enc) :
    ∃ zk : ZKProof enc A (fun n => (1 / 3 : ENNReal) ^ (n + 1)),
      zk.NegligibleSoundness ∧ zk.AuxiliaryInputZeroKnowledge := by
  obtain ⟨generator, hgenerator⟩ := hf.exists_nonuniformPRG_three_mul
  exact hgenerator.exists_zkProof_of_mem_NP hA

/-- **Goldreich–Micali–Wigderson theorem in full for NP relations (from a nonuniform one-way
function).** If a nonuniform one-way function exists, every NP relation `R` has a computational
zero-knowledge interactive proof system whose honest prover uses `R`'s own witnesses, with
negligible soundness `(1 / 3) ^ (n + 1)` (`ZKProof.NegligibleSoundness`) and general auxiliary-input
zero knowledge (`ZKProof.AuxiliaryInputZeroKnowledge`, and hence
`ZKProof.UnboundedAuxiliaryInputZeroKnowledge` and
`ZKProof.InstanceAuxiliaryInputZeroKnowledge`). -/
theorem NonuniformOneWay.exists_zkProof_of_npRelation
    {α : Type} {enc : α ↪ List Bool}
    {f : List Bool → List Bool} (hf : NonuniformOneWay f) (R : NPRelation enc) :
    ∃ zk : ZKProof enc R.language (fun n => (1 / 3 : ENNReal) ^ (n + 1)),
      (∀ a w, zk.isWitness a w = true ↔ R.IsWitness a w) ∧
      zk.NegligibleSoundness ∧ zk.AuxiliaryInputZeroKnowledge := by
  obtain ⟨generator, hgenerator⟩ := hf.exists_nonuniformPRG_three_mul
  exact hgenerator.exists_zkProof_of_npRelation R

end Cslib.Crypto

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.ZeroKnowledge
public import CslibFrontier.Computability.Complexity.CookLevin.Levin
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Families
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
import CslibFrontier.Computability.Probabilistic.PPT.Composition

/-!
# Zero knowledge for NP relations through Levin reductions

`Cslib.Crypto.PseudorandomGenerator.levinZeroKnowledgeProof` is the
Goldreich–Micali–Wigderson zero-knowledge proof system for the language of an NP relation `R`,
given a Levin reduction `r` of `R` to the NP relation of 3SAT. Its bundled witness check is `R`'s
own (`decide (R.IsWitness a w)`): the honest prover receives a witness of `R` and maps it through
the forward witness map of `r` to a 3SAT witness for the reduced formula `r.toFun a`, on which it
runs the masked-3SAT protocol. The verifier, the simulator and the soundness argument are those of
the Karp-reduction construction `Cslib.Crypto.PseudorandomGenerator.zeroKnowledgeProofOfReduction`
for the instance map of `r`.

Zero knowledge carries over because the mapped witnesses stay in the families that the
definitions quantify over: a polynomial-time-generable witness family remains
polynomial-time-generable after the forward map (`GenerableZeroKnowledge`), and a polynomially
bounded one remains polynomially bounded (`AuxiliaryInputZeroKnowledge`, under
`Cslib.Crypto.GMW.AdvicePRG`).

With `Cslib.Complexity.CookLevin.ThreeSAT_levinHard`, every NP relation gets such a proof system,
complete for the relation's own witnesses
(`Cslib.Crypto.PseudorandomGenerator.exists_zeroKnowledgeProof_of_npRelation`,
`Cslib.Crypto.OneWay.exists_zeroKnowledgeProof_of_npRelation`). Soundness stays the constant
`1 / 3` of `Cslib.Crypto.ZeroKnowledgeProof`, and the auxiliary-input form stays conditional on
`Cslib.Crypto.GMW.AdvicePRG`; amplification and the nonuniform premise are separate milestones of
the GMW objective.

## Main definitions

* `Cslib.Crypto.PseudorandomGenerator.levinZeroKnowledgeProof`: the GMW proof system
  for the language of an NP relation, with the relation's own witnesses.

## Main results

* `Cslib.Crypto.PseudorandomGenerator.auxiliaryInputZeroKnowledge_levinZeroKnowledgeProof`:
  auxiliary-input zero knowledge under the advice-PRG premise.
* `Cslib.Crypto.PseudorandomGenerator.exists_zeroKnowledgeProof_of_npRelation`,
  `Cslib.Crypto.PseudorandomGenerator.exists_auxiliaryInputZeroKnowledge_of_npRelation`,
  `Cslib.Crypto.OneWay.exists_zeroKnowledgeProof_of_npRelation`: every NP relation has a
  zero-knowledge proof whose honest prover uses the relation's own witnesses.

## References

* [O. Goldreich, S. Micali, A. Wigderson, *Proofs that Yield Nothing But Their Validity, or All
  Languages in NP Have Zero-Knowledge Proof Systems*][GoldreichMicaliWigderson1991]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2008], Exercise
  2.28 (numbering of the author's online draft of 30 December 2006).
-/

public section

namespace Cslib.Crypto

open Probability Complexity Logic.PL Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {R : NPRelation enc}

/-- Deciding the relation of an NP relation is polynomial-time: compare the certificate length
with the prescribed one and run the verifier. -/
theorem _root_.Cslib.Complexity.NPRelation.computableInPolyTime_decide_isWitness
    (R : NPRelation enc) :
    ComputableInPolyTime (fun p : α × List Bool => decide (R.IsWitness p.1 p.2))
      (encPair enc encBits) encBool := by
  have hV := R.computableInPolyTime_verifier
  have henc := ComputableInPolyTime.encoding_comp (ComputableInPolyTime.fst enc encBits)
  have heq (p : α × List Bool) : decide (R.IsWitness p.1 p.2) =
      (decide (p.2.length = R.certLength.eval (enc p.1).length) && R.verifier p) := by
    simp only [NPRelation.isWitness_iff, Bool.decide_and, Bool.decide_eq_true]
  simp only [heq]
  fun_prop

/-- **GMW zero knowledge with the relation's own witnesses.** The Goldreich–Micali–Wigderson
proof system for the language of the NP relation `R`, from a pseudorandom generator with stretch
at least `3 * k + 1` and a Levin reduction `r` of `R` to the NP relation of 3SAT. The honest
prover maps a witness `w` of `R` for `a` to the 3SAT witness `r.forwardWitness (a, w)` of
`r.toFun a`; the bundled witness check is `decide (R.IsWitness a w)`. -/
noncomputable def PseudorandomGenerator.levinZeroKnowledgeProof
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (r : LevinReduction R ThreeSAT.npRelation) :
    ZeroKnowledgeProof enc R.language where
  verifier := GMW.gmwVerifier generator length r.toFun
  prover n a w :=
    GMW.gmwProver generator (n + 7) (length (n + 7)) (r.toFun a) (r.forwardWitness (a, w))
  isWitness a w := decide (R.IsWitness a w)
  polyTime_isWitness := R.computableInPolyTime_decide_isWitness
  mem_iff_exists_witness a := by simp [NPRelation.mem_language]
  isOraclePPT_verifier :=
    GMW.isOraclePPTOn_gmwVerifier hG.polyTime hG.length_eq r.computableInPolyTime_toFun
  interact n a w prog :=
    GMW.gmwInteract generator (n + 7) (length (n + 7)) (r.toFun a) (r.forwardWitness (a, w)) prog
  eval_interact n a w prog :=
    GMW.eval_gmwInteract generator (n + 7) (length (n + 7)) (r.toFun a) _ prog
  isPPT_interact _ hV :=
    (GMW.isPPTOn_gmwInteract hG.polyTime hG.length_eq r.computableInPolyTime_toFun hV).preprocess
      (prepare := fun x : ℕ × α × List Bool × List Bool =>
        (x.1, x.2.1, r.forwardWitness (x.2.1, x.2.2.1), x.2.2.2))
      (by have := r.computableInPolyTime_forwardWitness; fun_prop)
  complete n a w hw :=
    GMW.acceptProb_gmwVerifier_gmwProver hG.length_eq r.toFun n a
      (r.isWitness_forwardWitness a w (of_decide_eq_true hw)).2
  sound n a ha P :=
    GMW.acceptProb_gmwVerifier_le hG.length_eq hstretch r.toFun n a
      (by rw [← ThreeSAT.language_npRelation]; exact mt (r.mem_language_iff a).2 ha) P
  zero_knowledge Vstar hV :=
    ⟨GMW.gmwSimulator generator length r.toFun Vstar,
      GMW.isPPTOn_gmwSimulator hG.polyTime hG.length_eq r.computableInPolyTime_toFun hV,
      fun _ _ _ ha hw hz hsat =>
        GMW.gmwView_indistinguishable_gmwSimulator hG r.computableInPolyTime_toFun hV ha
          (r.computableInPolyTime_forwardWitness.comp (ha.prod hw)) hz
          fun n => (r.isWitness_forwardWitness _ _ (of_decide_eq_true (hsat n))).2⟩

/-- The bundled witness check of the Levin-reduction proof system is the relation itself. -/
@[simp]
theorem PseudorandomGenerator.isWitness_levinZeroKnowledgeProof
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length) (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (r : LevinReduction R ThreeSAT.npRelation) (a : α) (w : List Bool) :
    (hG.levinZeroKnowledgeProof hstretch r).isWitness a w = true ↔ R.IsWitness a w :=
  decide_eq_true_iff

/-- Under the explicit advice-PRG premise `GMW.AdvicePRG enc generator length`, the Levin-reduction
proof system satisfies general auxiliary-input zero knowledge: polynomially bounded witness
families of `R` map to polynomially bounded 3SAT witness families. -/
theorem PseudorandomGenerator.auxiliaryInputZeroKnowledge_levinZeroKnowledgeProof
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length) (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (r : LevinReduction R ThreeSAT.npRelation) (hAdv : GMW.AdvicePRG enc generator length) :
    (hG.levinZeroKnowledgeProof hstretch r).AuxiliaryInputZeroKnowledge := by
  intro Vstar hV
  exact ⟨GMW.gmwSimulator generator length r.toFun Vstar,
    GMW.isPPTOn_gmwSimulator hG.polyTime hG.length_eq r.computableInPolyTime_toFun hV,
    fun _ _ _ _ ha hw hz hz' hsat _ hadv =>
      hAdv.gmwView_negligible r.computableInPolyTime_toFun hV hadv ha
        (by simpa using
          r.computableInPolyTime_forwardWitness.polynomiallyBounded_length_prod ha hw)
        hz hz' fun n => (r.isWitness_forwardWitness _ _ (of_decide_eq_true (hsat n))).2⟩

/-- **GMW for NP relations (from a pseudorandom generator).** Every NP relation has a
computational zero-knowledge proof system for its language whose bundled witness check is the
relation itself, so that its honest prover is complete for the relation's own witnesses. -/
theorem PseudorandomGenerator.exists_zeroKnowledgeProof_of_npRelation
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length) (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (R : NPRelation enc) :
    ∃ zk : ZeroKnowledgeProof enc R.language, ∀ a w, zk.isWitness a w = true ↔ R.IsWitness a w :=
  let ⟨r⟩ := CookLevin.ThreeSAT_levinHard enc R
  ⟨hG.levinZeroKnowledgeProof hstretch r,
    hG.isWitness_levinZeroKnowledgeProof hstretch r⟩

/-- **GMW for NP relations under an explicit advice-PRG premise.** Every NP relation has a
computational zero-knowledge proof system with the relation's own witnesses that satisfies general
auxiliary-input zero knowledge. The premise `GMW.AdvicePRG` is a hypothesis, not derived here. -/
theorem PseudorandomGenerator.exists_auxiliaryInputZeroKnowledge_of_npRelation
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length) (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (hAdv : GMW.AdvicePRG enc generator length) (R : NPRelation enc) :
    ∃ zk : ZeroKnowledgeProof enc R.language,
      (∀ a w, zk.isWitness a w = true ↔ R.IsWitness a w) ∧ zk.AuxiliaryInputZeroKnowledge :=
  let ⟨r⟩ := CookLevin.ThreeSAT_levinHard enc R
  ⟨hG.levinZeroKnowledgeProof hstretch r,
    hG.isWitness_levinZeroKnowledgeProof hstretch r,
    hG.auxiliaryInputZeroKnowledge_levinZeroKnowledgeProof hstretch r hAdv⟩

/-- **GMW for NP relations (from a one-way function).** If a one-way function exists, every NP
relation has a computational zero-knowledge proof system for its language, in the
polynomial-time-generable sense of `GenerableZeroKnowledge`, whose honest prover uses the
relation's own witnesses. -/
theorem OneWay.exists_zeroKnowledgeProof_of_npRelation {f : List Bool → List Bool}
    (hf : OneWay f) (R : NPRelation enc) :
    ∃ zk : ZeroKnowledgeProof enc R.language, ∀ a w, zk.isWitness a w = true ↔ R.IsWitness a w :=
  let ⟨_, hG⟩ := hf.exists_pseudorandomGenerator_three_mul
  hG.exists_zeroKnowledgeProof_of_npRelation (fun _ => le_rfl) R

end Cslib.Crypto

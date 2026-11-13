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

`Cslib.Crypto.PseudorandomGenerator.levinSingleZKProof` is the
Goldreich–Micali–Wigderson zero-knowledge proof system for the language of an NP relation `R`,
given a Levin reduction `r` of `R` to the NP relation of 3SAT. Its bundled witness check is `R`'s
own (`decide (R.IsWitness a w)`): the honest prover receives a witness of `R` and maps it through
the forward witness map of `r` to a 3SAT witness for the reduced formula `r.toFun a`, on which it
runs the masked-3SAT protocol. The verifier, the simulator and the soundness argument are those of
the Karp-reduction construction `Cslib.Crypto.PseudorandomGenerator.singleZKProofOfReduction`
for the instance map of `r`.

The change of witnesses is one generic step, `Cslib.Crypto.ZKProof.withRelationWitness`, which
applies to any proof system for `R.language` and any Levin reduction whose mapped witnesses pass
the system's witness check. The sequential system of
`CslibFrontier.Crypto.Computational.ZeroKnowledge.Amplification` uses the same step. Zero knowledge
carries over because the mapped witnesses stay in the families that the definitions quantify over:
a polynomial-time-generable witness family remains polynomial-time-generable after the forward map
(`GenerableZeroKnowledge`), and a polynomially bounded one remains polynomially bounded
(`AuxiliaryInputZeroKnowledge`).

This single-session system has soundness `1 / 3`. Its sequential repetition with negligible
soundness, and the existence theorems for every NP relation through
`Cslib.Complexity.CookLevin.ThreeSAT_levinHard`, are in
`CslibFrontier.Crypto.Computational.ZeroKnowledge.Amplification`. The auxiliary-input form stays
conditional on `Cslib.Crypto.GMW.AdvicePRG`.

## Main definitions

* `Cslib.Crypto.ZKProof.withRelationWitness`: a proof system for `R.language` with the witnesses
  of `R`, through the forward witness map of a Levin reduction.
* `Cslib.Crypto.PseudorandomGenerator.levinSingleZKProof`: the single-session GMW proof system for
  the language of an NP relation, with the relation's own witnesses.

## Main results

* `Cslib.Crypto.ZKProof.isWitness_withRelationWitness`,
  `Cslib.Crypto.PseudorandomGenerator.isWitness_levinSingleZKProof`: the bundled witness check is
  the relation itself.
* `Cslib.Crypto.ZKProof.AuxiliaryInputZeroKnowledge.withRelationWitness`,
  `Cslib.Crypto.PseudorandomGenerator.auxiliaryInputZeroKnowledge_levinSingleZKProof`:
  auxiliary-input zero knowledge carries over (the latter under the advice-PRG premise).
* `Cslib.Complexity.LevinReduction.mem_language_iff_mem_threeSAT`: membership through a Levin
  reduction to 3SAT.

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

/-- Through the instance map of a Levin reduction `r` of `R` to the NP relation of 3SAT, an
instance is in the language of `R` exactly when its image is in `ThreeSAT`. -/
theorem _root_.Cslib.Complexity.LevinReduction.mem_language_iff_mem_threeSAT
    (r : LevinReduction R ThreeSAT.npRelation) (a : α) :
    a ∈ R.language ↔ r.toFun a ∈ ThreeSAT := by
  rw [r.mem_language_iff, ThreeSAT.language_npRelation]

/-! ### Changing the witnesses of a proof system along a Levin reduction -/

namespace ZKProof

variable {β : Type} {encB : β ↪ List Bool} {S : NPRelation encB} {soundness : ℕ → ENNReal}

/-- A zero-knowledge proof system `zk` for `R.language` whose honest prover is fed witnesses of `R`
mapped by the forward witness map of a Levin reduction `r` of `R` to `S`. Its bundled witness check
is `decide (R.IsWitness a w)`; the verifier, the soundness bound and the simulators are those of
`zk`. The hypothesis `hw` says that mapped witnesses pass the witness check of `zk`. -/
noncomputable def withRelationWitness (zk : ZKProof enc R.language soundness)
    (r : LevinReduction R S)
    (hw : ∀ a w, R.IsWitness a w → zk.isWitness a (r.forwardWitness (a, w)) = true) :
    ZKProof enc R.language soundness where
  verifier := zk.verifier
  prover n a w := zk.prover n a (r.forwardWitness (a, w))
  isWitness a w := decide (R.IsWitness a w)
  polyTime_isWitness := R.computableInPolyTime_decide_isWitness
  mem_iff_exists_witness a := by simp [NPRelation.mem_language]
  isOraclePPT_verifier := zk.isOraclePPT_verifier
  interact n a w := zk.interact n a (r.forwardWitness (a, w))
  eval_interact n a w := zk.eval_interact n a _
  isPPT_interact _ hV :=
    (zk.isPPT_interact _ hV).preprocess
      (prepare := fun x : ℕ × α × List Bool × List Bool =>
        (x.1, x.2.1, r.forwardWitness (x.2.1, x.2.2.1), x.2.2.2))
      (by have := r.computableInPolyTime_forwardWitness; fun_prop)
  complete n a w h := zk.complete n a _ (hw a w (of_decide_eq_true h))
  sound := zk.sound
  zero_knowledge Vstar hV :=
    let ⟨S, hS, hzk⟩ := zk.zero_knowledge Vstar hV
    ⟨S, hS, fun _ _ _ ha hwit hz hsat =>
      hzk _ _ _ ha (r.computableInPolyTime_forwardWitness.comp (ha.prod hwit)) hz
        fun n => hw _ _ (of_decide_eq_true (hsat n))⟩

/-- The bundled witness check of `zk.withRelationWitness r hw` is the relation `R` itself. -/
@[simp]
theorem isWitness_withRelationWitness (zk : ZKProof enc R.language soundness)
    (r : LevinReduction R S)
    (hw : ∀ a w, R.IsWitness a w → zk.isWitness a (r.forwardWitness (a, w)) = true)
    (a : α) (w : List Bool) :
    (zk.withRelationWitness r hw).isWitness a w = true ↔ R.IsWitness a w :=
  decide_eq_true_iff

/-- General auxiliary-input zero knowledge carries over to `zk.withRelationWitness r hw`:
polynomially bounded witness families of `R` map to polynomially bounded witness families of
`zk`. -/
theorem AuxiliaryInputZeroKnowledge.withRelationWitness {zk : ZKProof enc R.language soundness}
    (h : zk.AuxiliaryInputZeroKnowledge) (r : LevinReduction R S)
    (hw : ∀ a w, R.IsWitness a w → zk.isWitness a (r.forwardWitness (a, w)) = true) :
    (zk.withRelationWitness r hw).AuxiliaryInputZeroKnowledge := by
  intro Vstar hV
  obtain ⟨S, hS, hzk⟩ := h Vstar hV
  exact ⟨S, hS, fun _ _ _ _ ha hwit hz hz' hsat _ hadv =>
    hzk _ _ _ _ ha
      (by simpa using r.computableInPolyTime_forwardWitness.polynomiallyBounded_length_prod ha hwit)
      hz hz' (fun n => hw _ _ (of_decide_eq_true (hsat n))) _ hadv⟩

end ZKProof

/-! ### The single-session system -/

/-- **GMW zero knowledge with the relation's own witnesses.** The single-session
Goldreich–Micali–Wigderson proof system, with soundness `1 / 3`, for the language of the NP relation
`R`, from a pseudorandom generator with stretch at least `3 * k + 1` and a Levin reduction `r` of
`R` to the NP relation of 3SAT: `PseudorandomGenerator.singleZKProofOfReduction` for the instance
map of `r`, with witnesses changed by `ZKProof.withRelationWitness`. The honest prover maps a
witness `w` of `R` for `a` to the 3SAT witness `r.forwardWitness (a, w)` of `r.toFun a`; the
bundled witness check is `decide (R.IsWitness a w)`. -/
noncomputable def PseudorandomGenerator.levinSingleZKProof
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (r : LevinReduction R ThreeSAT.npRelation) :
    ZKProof enc R.language (fun _ => 1 / 3) :=
  (hG.singleZKProofOfReduction hstretch r.computableInPolyTime_toFun
      r.mem_language_iff_mem_threeSAT).withRelationWitness r
    fun a w h => (r.isWitness_forwardWitness a w h).2

/-- The bundled witness check of the Levin-reduction proof system is the relation itself. -/
@[simp]
theorem PseudorandomGenerator.isWitness_levinSingleZKProof
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length) (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (r : LevinReduction R ThreeSAT.npRelation) (a : α) (w : List Bool) :
    (hG.levinSingleZKProof hstretch r).isWitness a w = true ↔ R.IsWitness a w :=
  ZKProof.isWitness_withRelationWitness _ _ _ a w

/-- Under the explicit advice-PRG premise `GMW.AdvicePRG enc generator length`, the Levin-reduction
proof system satisfies general auxiliary-input zero knowledge: polynomially bounded witness
families of `R` map to polynomially bounded 3SAT witness families. -/
theorem PseudorandomGenerator.auxiliaryInputZeroKnowledge_levinSingleZKProof
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length) (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (r : LevinReduction R ThreeSAT.npRelation) (hAdv : GMW.AdvicePRG enc generator length) :
    (hG.levinSingleZKProof hstretch r).AuxiliaryInputZeroKnowledge :=
  (hG.auxiliaryInputZeroKnowledge_singleZKProofOfReduction hstretch
    r.computableInPolyTime_toFun r.mem_language_iff_mem_threeSAT hAdv).withRelationWitness r _

end Cslib.Crypto

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.ZeroKnowledge.Soundness
public import CslibFrontier.Crypto.Computational.ZeroKnowledge.Levin
public import CslibFrontier.Crypto.Computational.GMW.Sequential.Simulator
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Families
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# Soundness-amplified GMW zero-knowledge proof systems for NP

This module packages the `k n`-fold sequential repetition of the Goldreich–Micali–Wigderson
masked-3SAT protocol from `CslibFrontier.Crypto.Computational.GMW.Sequential` and its witness-free
simulator from `CslibFrontier.Crypto.Computational.GMW.Sequential.Simulator` into `ZKProof` systems
with soundness error `(1 / 3) ^ (k n)`:

* `Cslib.Crypto.PseudorandomGenerator.zkProofOfReduction`: for any polynomial-time Karp reduction
  `f : α → CNF ℕ` to `ThreeSAT` and any polynomial-time repetition schedule `k : ℕ → ℕ`, a
  `ZKProof enc A (fun n => (1 / 3) ^ (k n))` with perfect completeness, soundness `(1 / 3) ^ (k n)`
  against computationally unbounded stateful provers, and `GenerableZeroKnowledge`. Under
  `GMW.AdvicePRG enc generator length`, it satisfies `ZKProof.AuxiliaryInputZeroKnowledge`
  (`PseudorandomGenerator.auxiliaryInputZeroKnowledge_zkProofOfReduction`).
* `Cslib.Crypto.PseudorandomGenerator.zkProofThreeSAT`: specialization to `ThreeSAT` at repetition
  schedule `k n := n + 1`, with soundness `(1 / 3) ^ (n + 1)` (`ZKProof.NegligibleSoundness`).
* `Cslib.Crypto.PseudorandomGenerator.levinZKProof`: for any NP relation `R` and Levin reduction
  `r : LevinReduction R ThreeSAT.npRelation`, a `ZKProof enc R.language (fun n => (1 / 3) ^ (k n))`
  whose honest prover uses `R`'s own witnesses (`isWitness a w := decide (R.IsWitness a w)`),
  satisfying `ZKProof.AuxiliaryInputZeroKnowledge` under `GMW.AdvicePRG`.
* `Cslib.Crypto.PseudorandomGenerator.exists_zkProof_of_mem_NP`,
  `Cslib.Crypto.PseudorandomGenerator.exists_auxiliaryInputZKProof_of_mem_NP`,
  `Cslib.Crypto.PseudorandomGenerator.exists_zkProof_of_npRelation`,
  `Cslib.Crypto.PseudorandomGenerator.exists_auxiliaryInputZKProof_of_npRelation`,
  `Cslib.Crypto.OneWay.exists_zkProof_of_mem_NP`, and
  `Cslib.Crypto.OneWay.exists_zkProof_of_npRelation`: existential endpoints at schedule
  `k n := n + 1` with `ZKProof.NegligibleSoundness`.

## References

* [O. Goldreich, S. Micali, A. Wigderson, *Proofs that Yield Nothing But Their Validity, or All
  Languages in NP Have Zero-Knowledge Proof Systems*][GoldreichMicaliWigderson1991]
* [O. Goldreich, *Foundations of Cryptography: Volume 1, Basic Tools*][Goldreich2001],
  Sections 4.3–4.4.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Complexity Logic.PL Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- **Sequentially amplified GMW zero-knowledge proof system via a Karp reduction to `ThreeSAT`.**
Given a pseudorandom generator with stretch at least `3 * m + 1`, a polynomial-time reduction
`f : α → CNF ℕ` from `A` to `ThreeSAT`, and a polynomial-time repetition schedule `k : ℕ → ℕ`, this
constructs a `ZKProof enc A (fun n => (1 / 3) ^ (k n))` running `k n` sequential sessions of the
3-copy masked-3SAT protocol. -/
noncomputable def PseudorandomGenerator.zkProofOfReduction
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {generator : List Bool → List Bool} {length k : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ m, 3 * m + 1 ≤ length m)
    {f : α → CNF ℕ} (hf : ComputableInPolyTime f enc encCNF)
    (hred : ∀ a, a ∈ A ↔ f a ∈ ThreeSAT)
    (hk : ComputableInPolyTime k encUnary encUnary) :
    ZKProof enc A (fun n => (1 / 3 : ENNReal) ^ (k n)) where
  verifier := GMW.gmwSeqVerifier generator length f k
  prover n a w := GMW.gmwSeqProver generator (n + 7) (length (n + 7)) (f a) w (k n)
  isWitness a w := ThreeSAT.verifier (f a, w)
  polyTime_isWitness := (hG.singleZKProofOfReduction hstretch hf hred).polyTime_isWitness
  mem_iff_exists_witness :=
    (hG.singleZKProofOfReduction hstretch hf hred).mem_iff_exists_witness
  isOraclePPT_verifier := GMW.isOraclePPTOn_gmwSeqVerifier hG.polyTime hG.length_eq hf hk
  interact n a w prog := GMW.gmwSeqInteract generator (n + 7) (length (n + 7)) (f a) w (k n) prog
  eval_interact n a w prog :=
    GMW.eval_gmwSeqInteract generator (n + 7) (length (n + 7)) (f a) w (k n) prog
  isPPT_interact _ hV := GMW.isPPTOn_gmwSeqInteract hG.polyTime hG.length_eq hf hk hV
  complete n a _ hw := GMW.acceptProb_gmwSeqVerifier_gmwSeqProver hG.length_eq f k n a hw
  sound n a ha P :=
    GMW.acceptProb_gmwSeqVerifier_le hG.length_eq hstretch f k n a (mt (hred a).mpr ha) P
  zero_knowledge Vstar hV :=
    ⟨GMW.gmwSeqSimulator enc generator length f k Vstar,
      GMW.isPPTOn_gmwSeqSimulator hG.polyTime hG.length_eq hf hk hV,
      fun _ _ _ ha hw_comp hz hw_sat =>
        GMW.gmwSeqView_indistinguishable_gmwSeqSimulator hG hf hk hV ha hw_comp hz hw_sat⟩

/-- When `∀ n, n ≤ k n`, `hG.zkProofOfReduction hstretch hf hred hk` has negligible soundness. -/
theorem PseudorandomGenerator.negligibleSoundness_zkProofOfReduction
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {generator : List Bool → List Bool} {length k : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ m, 3 * m + 1 ≤ length m)
    {f : α → CNF ℕ} (hf : ComputableInPolyTime f enc encCNF)
    (hred : ∀ a, a ∈ A ↔ f a ∈ ThreeSAT)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hk_ge : ∀ n, n ≤ k n) :
    (hG.zkProofOfReduction hstretch hf hred hk).NegligibleSoundness :=
  ZKProof.negligibleSoundness_one_third_pow _ hk_ge

/-- Under `GMW.AdvicePRG enc generator length`, the sequentially amplified GMW proof system
`hG.zkProofOfReduction hstretch hf hred hk` satisfies general auxiliary-input zero knowledge
(`ZKProof.AuxiliaryInputZeroKnowledge`). -/
theorem PseudorandomGenerator.auxiliaryInputZeroKnowledge_zkProofOfReduction
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {generator : List Bool → List Bool} {length k : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ m, 3 * m + 1 ≤ length m)
    {f : α → CNF ℕ} (hf : ComputableInPolyTime f enc encCNF)
    (hred : ∀ a, a ∈ A ↔ f a ∈ ThreeSAT)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hAdv : GMW.AdvicePRG enc generator length) :
    (hG.zkProofOfReduction hstretch hf hred hk).AuxiliaryInputZeroKnowledge := by
  intro Vstar hV
  exact ⟨GMW.gmwSeqSimulator enc generator length f k Vstar,
    GMW.isPPTOn_gmwSeqSimulator hG.polyTime hG.length_eq hf hk hV,
    fun _ _ _ _ ha hw hz hz' hw_sat _ hadv =>
      hAdv.gmwSeqView_negligible hf hk hV hadv ha hw hz hz' hw_sat⟩

/-- The sequentially amplified GMW zero-knowledge proof system for `ThreeSAT` at repetition
schedule `k n := n + 1`, with soundness bound `(1 / 3) ^ (n + 1)`. -/
noncomputable def PseudorandomGenerator.zkProofThreeSAT
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ m, 3 * m + 1 ≤ length m) :
    ZKProof encCNF ThreeSAT (fun n => (1 / 3 : ENNReal) ^ (n + 1)) :=
  hG.zkProofOfReduction hstretch (by fun_prop) (fun _ => Iff.rfl) (by fun_prop)

/-- `hG.zkProofThreeSAT hstretch` has negligible soundness `(1 / 3) ^ (n + 1)`. -/
theorem PseudorandomGenerator.negligibleSoundness_zkProofThreeSAT
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ m, 3 * m + 1 ≤ length m) :
    (hG.zkProofThreeSAT hstretch).NegligibleSoundness :=
  hG.negligibleSoundness_zkProofOfReduction hstretch (by fun_prop) (fun _ => Iff.rfl) (by fun_prop)
    Nat.le_succ

/-- Under `GMW.AdvicePRG encCNF generator length`, `hG.zkProofThreeSAT hstretch` satisfies general
auxiliary-input zero knowledge (`ZKProof.AuxiliaryInputZeroKnowledge`). -/
theorem PseudorandomGenerator.auxiliaryInputZeroKnowledge_zkProofThreeSAT
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ m, 3 * m + 1 ≤ length m)
    (hAdv : GMW.AdvicePRG encCNF generator length) :
    (hG.zkProofThreeSAT hstretch).AuxiliaryInputZeroKnowledge :=
  hG.auxiliaryInputZeroKnowledge_zkProofOfReduction hstretch (by fun_prop) (fun _ => Iff.rfl)
    (by fun_prop) hAdv

/-- **Sequentially amplified GMW zero knowledge with an NP relation's own witnesses.**
Given a pseudorandom generator with stretch at least `3 * m + 1`, a Levin reduction `r` from an NP
relation `R` to `ThreeSAT.npRelation`, and a polynomial-time repetition schedule `k : ℕ → ℕ`, this
is `zkProofOfReduction` for the instance map of `r` with witnesses changed by
`ZKProof.withRelationWitness`: a `ZKProof enc R.language (fun n => (1 / 3) ^ (k n))` whose honest
prover maps an `R`-witness `w` to `r.forwardWitness (a, w)` and whose bundled witness check is
`decide (R.IsWitness a w)`. -/
noncomputable def PseudorandomGenerator.levinZKProof
    {α : Type} {enc : α ↪ List Bool} {R : NPRelation enc}
    {generator : List Bool → List Bool} {length k : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ m, 3 * m + 1 ≤ length m)
    (r : LevinReduction R ThreeSAT.npRelation)
    (hk : ComputableInPolyTime k encUnary encUnary) :
    ZKProof enc R.language (fun n => (1 / 3 : ENNReal) ^ (k n)) :=
  (hG.zkProofOfReduction hstretch r.computableInPolyTime_toFun r.mem_language_iff_mem_threeSAT
      hk).withRelationWitness r
    fun a w h => (r.isWitness_forwardWitness a w h).2

/-- The bundled witness check of `levinZKProof` is the NP relation `R.IsWitness` itself. -/
@[simp]
theorem PseudorandomGenerator.isWitness_levinZKProof
    {α : Type} {enc : α ↪ List Bool} {R : NPRelation enc}
    {generator : List Bool → List Bool} {length k : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ m, 3 * m + 1 ≤ length m)
    (r : LevinReduction R ThreeSAT.npRelation)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (a : α) (w : List Bool) :
    (hG.levinZKProof hstretch r hk).isWitness a w = true ↔ R.IsWitness a w :=
  ZKProof.isWitness_withRelationWitness _ _ _ a w

/-- When `∀ n, n ≤ k n`, `hG.levinZKProof hstretch r hk` has negligible soundness. -/
theorem PseudorandomGenerator.negligibleSoundness_levinZKProof
    {α : Type} {enc : α ↪ List Bool} {R : NPRelation enc}
    {generator : List Bool → List Bool} {length k : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ m, 3 * m + 1 ≤ length m)
    (r : LevinReduction R ThreeSAT.npRelation)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hk_ge : ∀ n, n ≤ k n) :
    (hG.levinZKProof hstretch r hk).NegligibleSoundness :=
  ZKProof.negligibleSoundness_one_third_pow _ hk_ge

/-- Under `GMW.AdvicePRG enc generator length`, `hG.levinZKProof hstretch r hk` satisfies general
auxiliary-input zero knowledge (`ZKProof.AuxiliaryInputZeroKnowledge`). -/
theorem PseudorandomGenerator.auxiliaryInputZeroKnowledge_levinZKProof
    {α : Type} {enc : α ↪ List Bool} {R : NPRelation enc}
    {generator : List Bool → List Bool} {length k : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ m, 3 * m + 1 ≤ length m)
    (r : LevinReduction R ThreeSAT.npRelation)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hAdv : GMW.AdvicePRG enc generator length) :
    (hG.levinZKProof hstretch r hk).AuxiliaryInputZeroKnowledge :=
  (hG.auxiliaryInputZeroKnowledge_zkProofOfReduction hstretch r.computableInPolyTime_toFun
    r.mem_language_iff_mem_threeSAT hk hAdv).withRelationWitness r _

/-- **Soundness-amplified GMW theorem (from a pseudorandom generator).** Given a pseudorandom
generator with stretch at least `3 * m + 1`, every language `A ∈ NP enc` has a computational
zero-knowledge interactive proof system with negligible soundness `(1 / 3) ^ (n + 1)` against
unbounded provers and `GenerableZeroKnowledge`. -/
theorem PseudorandomGenerator.exists_zkProof_of_mem_NP
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ m, 3 * m + 1 ≤ length m)
    (hA : A ∈ NP enc) :
    ∃ zk : ZKProof enc A (fun n => (1 / 3 : ENNReal) ^ (n + 1)),
      zk.NegligibleSoundness := by
  obtain ⟨f, hf, hred⟩ := ThreeSAT_npHard enc A hA
  exact ⟨hG.zkProofOfReduction hstretch hf hred (by fun_prop),
    hG.negligibleSoundness_zkProofOfReduction hstretch hf hred (by fun_prop) Nat.le_succ⟩

/-- **Soundness-amplified GMW theorem under `GMW.AdvicePRG`.** Given a pseudorandom generator with
stretch at least `3 * m + 1` satisfying `GMW.AdvicePRG enc generator length`, every language
`A ∈ NP enc` has a computational zero-knowledge interactive proof system with negligible soundness
`(1 / 3) ^ (n + 1)` and general auxiliary-input zero knowledge
(`ZKProof.AuxiliaryInputZeroKnowledge`). -/
theorem PseudorandomGenerator.exists_auxiliaryInputZKProof_of_mem_NP
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ m, 3 * m + 1 ≤ length m)
    (hAdv : GMW.AdvicePRG enc generator length)
    (hA : A ∈ NP enc) :
    ∃ zk : ZKProof enc A (fun n => (1 / 3 : ENNReal) ^ (n + 1)),
      zk.NegligibleSoundness ∧ zk.AuxiliaryInputZeroKnowledge := by
  obtain ⟨f, hf, hred⟩ := ThreeSAT_npHard enc A hA
  exact ⟨hG.zkProofOfReduction hstretch hf hred (by fun_prop),
    hG.negligibleSoundness_zkProofOfReduction hstretch hf hred (by fun_prop) Nat.le_succ,
    hG.auxiliaryInputZeroKnowledge_zkProofOfReduction hstretch hf hred (by fun_prop) hAdv⟩

/-- **Soundness-amplified GMW for NP relations (from a pseudorandom generator).** Given a
pseudorandom generator with stretch at least `3 * m + 1`, every NP relation `R` has a computational
zero-knowledge interactive proof system with negligible soundness `(1 / 3) ^ (n + 1)` whose honest
prover uses `R`'s own witnesses. -/
theorem PseudorandomGenerator.exists_zkProof_of_npRelation
    {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ m, 3 * m + 1 ≤ length m)
    (R : NPRelation enc) :
    ∃ zk : ZKProof enc R.language (fun n => (1 / 3 : ENNReal) ^ (n + 1)),
      (∀ a w, zk.isWitness a w = true ↔ R.IsWitness a w) ∧ zk.NegligibleSoundness := by
  let ⟨r⟩ := CookLevin.ThreeSAT_levinHard enc R
  exact ⟨hG.levinZKProof hstretch r (by fun_prop),
    hG.isWitness_levinZKProof hstretch r (by fun_prop),
    hG.negligibleSoundness_levinZKProof hstretch r (by fun_prop) Nat.le_succ⟩

/-- **Soundness-amplified GMW for NP relations under `GMW.AdvicePRG`.** Given a pseudorandom
generator with stretch at least `3 * m + 1` satisfying `GMW.AdvicePRG enc generator length`, every
NP relation `R` has a computational zero-knowledge interactive proof system with negligible
soundness `(1 / 3) ^ (n + 1)` and general auxiliary-input zero knowledge whose honest prover uses
`R`'s own witnesses. -/
theorem PseudorandomGenerator.exists_auxiliaryInputZKProof_of_npRelation
    {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ m, 3 * m + 1 ≤ length m)
    (hAdv : GMW.AdvicePRG enc generator length)
    (R : NPRelation enc) :
    ∃ zk : ZKProof enc R.language (fun n => (1 / 3 : ENNReal) ^ (n + 1)),
      (∀ a w, zk.isWitness a w = true ↔ R.IsWitness a w) ∧
      zk.NegligibleSoundness ∧ zk.AuxiliaryInputZeroKnowledge := by
  let ⟨r⟩ := CookLevin.ThreeSAT_levinHard enc R
  exact ⟨hG.levinZKProof hstretch r (by fun_prop),
    hG.isWitness_levinZKProof hstretch r (by fun_prop),
    hG.negligibleSoundness_levinZKProof hstretch r (by fun_prop) Nat.le_succ,
    hG.auxiliaryInputZeroKnowledge_levinZKProof hstretch r (by fun_prop) hAdv⟩

/-- **Soundness-amplified GMW theorem (from a one-way function).** If a one-way function exists,
every language `A ∈ NP enc` has a computational zero-knowledge interactive proof system with
negligible soundness `(1 / 3) ^ (n + 1)` and `GenerableZeroKnowledge`. -/
theorem OneWay.exists_zkProof_of_mem_NP
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {f : List Bool → List Bool} (hf : OneWay f) (hA : A ∈ NP enc) :
    ∃ zk : ZKProof enc A (fun n => (1 / 3 : ENNReal) ^ (n + 1)),
      zk.NegligibleSoundness := by
  obtain ⟨_, hG⟩ := hf.exists_pseudorandomGenerator_three_mul
  exact hG.exists_zkProof_of_mem_NP (fun _ => le_rfl) hA

/-- **Soundness-amplified GMW for NP relations (from a one-way function).** If a one-way function
exists, every NP relation `R` has a computational zero-knowledge interactive proof system with
negligible soundness `(1 / 3) ^ (n + 1)` and `GenerableZeroKnowledge` whose honest prover uses
`R`'s own witnesses. -/
theorem OneWay.exists_zkProof_of_npRelation
    {α : Type} {enc : α ↪ List Bool}
    {f : List Bool → List Bool} (hf : OneWay f) (R : NPRelation enc) :
    ∃ zk : ZKProof enc R.language (fun n => (1 / 3 : ENNReal) ^ (n + 1)),
      (∀ a w, zk.isWitness a w = true ↔ R.IsWitness a w) ∧ zk.NegligibleSoundness := by
  obtain ⟨_, hG⟩ := hf.exists_pseudorandomGenerator_three_mul
  exact hG.exists_zkProof_of_npRelation (fun _ => le_rfl) R

end Cslib.Crypto

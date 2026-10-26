/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Complexity.Classes.IP
public import Complexity.Crypto.Computational.GMW.Simulator
public import Complexity.Crypto.Computational.GMW.Soundness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Logics.Propositional.CNF.PolyTime

/-!
# Computational zero-knowledge interactive proofs for NP

Goldreich, Micali, and Wigderson [GoldreichMicaliWigderson1991] proved that if one-way functions
exist, then every language in `NP` has a computational zero-knowledge interactive proof system.
This module defines computational zero-knowledge interactive proofs (`ZeroKnowledgeProof`) together
with explicit public API predicates distinguishing restricted polynomial-time-generable
zero-knowledge (`GenerableZeroKnowledge`) from general auxiliary-input zero-knowledge over
arbitrary polynomially bounded valid families (`AuxiliaryInputZeroKnowledge`), and constructs a
proof system for `ThreeSAT` and hence for every language in `NP` via `ThreeSAT_npHard` and Naor's
bit commitment scheme [Naor1991] (`Complexity.Crypto.Computational.Commitment`).

### Protocol design and source credit

While the theorem that every language in `NP` has a computational zero-knowledge interactive proof
system from one-way functions is due to Goldreich, Micali, and Wigderson
[GoldreichMicaliWigderson1991] using Naor's commitment scheme [Naor1991], the concrete underlying
`ThreeSAT` protocol formalized in `Complexity.Crypto.Computational.GMW` is a direct **3-copy
masked-3SAT truth-table commitment protocol** rather than GMW's original 3-coloring protocol:
each of 3 parallel copies commits to a random variable mask, the XOR-masked assignment, and the
8-entry masked truth table of each clause, and a random 3-bit challenge selects for each copy
whether to open the mask and full truth tables or the masked assignment and the active truth-table
entries.

### Restricted versus general auxiliary-input zero-knowledge and witness conventions

* **Restricted polynomial-time-generable zero-knowledge (`GenerableZeroKnowledge`,
  `ZeroKnowledgeProof.zero_knowledge`, `ZeroKnowledgeProof.generableZeroKnowledge`).**
  Matching the library's uniform strict-PPT cryptographic conventions
  (`ComputationallyIndistinguishable`), `GenerableZeroKnowledge` quantifies over uniform strict
  oracle PPT malicious verifiers `Vstar` (producing one efficient witness-free simulator `S` per
  `Vstar` before the choice of families) and deterministic polynomial-time-generable families of
  instances `a : ℕ → α`, valid witnesses `w : ℕ → List Bool` (`∀ n, isWitness (a n) (w n) = true`),
  and auxiliary inputs `z : ℕ → List Bool` (`ComputableInPolyTime · encUnary _`). Fixed-instance
  zero-knowledge (`ZeroKnowledgeProof.zero_knowledge_const`) is an immediate corollary for constant
  families `fun _ => a` and `fun _ => w`.
* **General auxiliary-input zero-knowledge (`AuxiliaryInputZeroKnowledge`,
  `ZeroKnowledgeProof.AuxiliaryInputZeroKnowledge`).**
  Quantifies over the same uniform strict oracle PPT malicious verifiers `Vstar` and chooses one
  efficient witness-free simulator `S` per `Vstar` before the choice of families, then ranges over
  arbitrary polynomially bounded families of instances `a : ℕ → α`, valid witnesses
  `w : ℕ → List Bool`, and auxiliary inputs `z : ℕ → List Bool` (`PolynomiallyBounded`), against
  all full-input uniform strict PPT distinguishers `adversary` charged for the complete encoded
  input `((1^n, (a n, z n)), view)`. Every system satisfying `AuxiliaryInputZeroKnowledge`
  satisfies `GenerableZeroKnowledge` (`AuxiliaryInputZeroKnowledge.generableZeroKnowledge`).
  Under the explicit advice-PRG premise `GMW.AdvicePRG`
  (from `GMW.gmwView_negligible_of_advice_prg`), the GMW proof systems satisfy
  `ZeroKnowledgeProof.AuxiliaryInputZeroKnowledge`
  (`PseudorandomGenerator.auxiliaryInputZeroKnowledge_zeroKnowledgeProofOfReduction`,
  `PseudorandomGenerator.auxiliaryInputZeroKnowledge_zeroKnowledgeProofThreeSAT`); this module does
  not derive `GMW.AdvicePRG` from uniform PRG or one-way function assumptions.
* **Bundled witness relation (`ZeroKnowledgeProof.isWitness`).** `ZeroKnowledgeProof` bundles its
  own polynomial-time witness predicate `isWitness : α → List Bool → Bool` characterizing `A`
  (`mem_iff_exists_witness`). No witness-length bound is imposed, so `isWitness` by itself need not
  be an `NP` relation; membership in `IP` (`mem_IP`) does not need one, and in `zero_knowledge`
  the witness family `w : ℕ → List Bool` is polynomial-time-generable in `1^n`. In
  `PseudorandomGenerator.zeroKnowledgeProofOfReduction` and
  `PseudorandomGenerator.exists_zeroKnowledgeProof_of_mem_NP`, the bundled predicate
  `isWitness a w := ThreeSAT.verifier (f a, w)` checks a `ThreeSAT` witness for the Karp-reduced
  formula `f a` rather than a witness for the original `NP` verifier of `A`.

## Main definitions

* `Cslib.Crypto.GenerableZeroKnowledge`: uniform computational zero-knowledge over deterministic
  polynomial-time-generable instance, valid-witness, and auxiliary-input families.
* `Cslib.Crypto.AuxiliaryInputZeroKnowledge`,
  `Cslib.Crypto.ZeroKnowledgeProof.AuxiliaryInputZeroKnowledge`: general auxiliary-input
  computational zero-knowledge over arbitrary polynomially bounded valid families against
  full-input uniform strict PPT distinguishers.
* `Cslib.Crypto.ZeroKnowledgeProof`: a computational zero-knowledge interactive proof system for a
  language `A`, bundling a uniform strict oracle PPT verifier, an honest prover with a uniform
  strict PPT interaction realization, perfect completeness, soundness `1 / 3` against unbounded
  provers, and `GenerableZeroKnowledge`.
* `Cslib.Crypto.PseudorandomGenerator.zeroKnowledgeProofOfReduction`,
  `Cslib.Crypto.PseudorandomGenerator.zeroKnowledgeProofThreeSAT`: GMW zero-knowledge proof
  systems for any language Karp-reducible to `ThreeSAT` and for `ThreeSAT` itself.

## Main results

* `Cslib.Crypto.AuxiliaryInputZeroKnowledge.generableZeroKnowledge`,
  `Cslib.Crypto.ZeroKnowledgeProof.AuxiliaryInputZeroKnowledge.generableZeroKnowledge`:
  general auxiliary-input zero-knowledge implies poly-time-generable zero-knowledge.
* `Cslib.Crypto.ZeroKnowledgeProof.isInteractiveProof`, `Cslib.Crypto.ZeroKnowledgeProof.mem_IP`:
  every language with a `ZeroKnowledgeProof` belongs to `IP`.
* `Cslib.Crypto.ZeroKnowledgeProof.zero_knowledge_const`,
  `Cslib.Crypto.ZeroKnowledgeProof.AuxiliaryInputZeroKnowledge.zero_knowledge_const`:
  fixed-instance computational zero-knowledge.
* `Cslib.Crypto.PseudorandomGenerator.exists_zeroKnowledgeProof_of_mem_NP`,
  `Cslib.Crypto.OneWay.exists_zeroKnowledgeProof_of_mem_NP`: GMW zero-knowledge proof systems for
  every language in `NP` from any pseudorandom generator (with stretch `3 * k + 1`) or one-way
  function, establishing `GenerableZeroKnowledge`.
* `Cslib.Crypto.PseudorandomGenerator.auxiliaryInputZeroKnowledge_zeroKnowledgeProofOfReduction`,
  `Cslib.Crypto.PseudorandomGenerator.auxiliaryInputZeroKnowledge_zeroKnowledgeProofThreeSAT`,
  `Cslib.Crypto.PseudorandomGenerator.exists_auxiliaryInputZeroKnowledge_of_mem_NP`:
  general `AuxiliaryInputZeroKnowledge` for the GMW proof systems under the explicit advice-PRG
  premise `GMW.AdvicePRG`.

## References

* [O. Goldreich, S. Micali, A. Wigderson, *Proofs that Yield Nothing But Their Validity, or All
  Languages in NP Have Zero-Knowledge Proof Systems*][GoldreichMicaliWigderson1991]
* [M. Naor, *Bit Commitment Using Pseudorandomness*][Naor1991]
* [O. Goldreich, *Foundations of Cryptography: Volume 1, Basic Tools*][Goldreich2001], Chapter 4.
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 9.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Complexity Logic.PL Turing.MultiTapeTM ComputableTidilyInPolyTime
open scoped NNReal ENNReal

/-! ### Restricted versus general auxiliary-input zero-knowledge predicates -/

/-- **Uniform computational zero-knowledge with polynomial-time-generable families.**
For every uniform strict oracle PPT malicious verifier `Vstar` (taking security parameter `n`,
instance `a`, and auxiliary input `z`, charged for the complete encoded input `(1^n, (a, z))`),
there exists a single uniform strict PPT witness-free simulator `S` (chosen before the families and
charged for `(1^n, (a, z))`) whose output ensemble is computationally indistinguishable from the
real interaction output across all deterministic polynomial-time-generable families of instances
`a : ℕ → α`, valid witnesses `w : ℕ → List Bool` (`∀ n, isWitness (a n) (w n) = true`), and
auxiliary inputs `z : ℕ → List Bool` (`ComputableInPolyTime · encUnary _`). -/
def GenerableZeroKnowledge {α : Type} (enc : α ↪ List Bool)
    (prover : ℕ → α → List Bool → Prover Unit)
    (isWitness : α → List Bool → Bool) : Prop :=
  ∀ Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool),
    IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p : ℕ × α × List Bool => Vstar p.1 p.2.1 p.2.2) →
    ∃ S : ℕ → α → List Bool → ProbComp (List Bool),
      IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
        (fun p : ℕ × α × List Bool => S p.1 p.2.1 p.2.2) ∧
      ∀ (a : ℕ → α) (w z : ℕ → List Bool),
        ComputableInPolyTime a encUnary enc →
        ComputableInPolyTime w encUnary encBits →
        ComputableInPolyTime z encUnary encBits →
        (∀ n, isWitness (a n) (w n) = true) →
        ComputationallyIndistinguishable
          (fun n => ((prover n (a n) (w n)).run (Vstar n (a n) (z n))
            (prover n (a n) (w n)).init).map Prod.fst)
          (fun n => ProbComp.eval (S n (a n) (z n)))

/-- **General auxiliary-input computational zero-knowledge for arbitrary polynomially bounded
valid families.**
For every uniform strict oracle PPT malicious verifier `Vstar` (charged for its complete encoded
input `(1^n, (a, z))`), there exists a single uniform strict PPT witness-free simulator `S`
(chosen before the families and distinguisher, and charged for `(1^n, (a, z))`) such that for all
arbitrary polynomially bounded families of instances `a : ℕ → α`, valid witnesses
`w : ℕ → List Bool` (`∀ n, isWitness (a n) (w n) = true`), and auxiliary inputs
`z : ℕ → List Bool`, and for every uniform strict PPT distinguisher `adversary` (charged for its
complete encoded input `((1^n, (a, z)), view)`), the distinguishing advantage between the real
interaction view and the simulated view is negligible. -/
def AuxiliaryInputZeroKnowledge {α : Type} (enc : α ↪ List Bool)
    (prover : ℕ → α → List Bool → Prover Unit)
    (isWitness : α → List Bool → Bool) : Prop :=
  ∀ Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool),
    IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p : ℕ × α × List Bool => Vstar p.1 p.2.1 p.2.2) →
    ∃ S : ℕ → α → List Bool → ProbComp (List Bool),
      IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
        (fun p : ℕ × α × List Bool => S p.1 p.2.1 p.2.2) ∧
      ∀ (a : ℕ → α) (w z : ℕ → List Bool),
        PolynomiallyBounded (fun n => (enc (a n)).length) →
        PolynomiallyBounded (fun n => (w n).length) →
        PolynomiallyBounded (fun n => (z n).length) →
        (∀ n, isWitness (a n) (w n) = true) →
        ∀ adversary : ℕ → α → List Bool → List Bool → ProbComp Bool,
          IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) encBits) encBool
            (fun p => adversary p.1.1 p.1.2.1 p.1.2.2 p.2) →
          Negligible (fun n => Game.advantage
            (distinguishingGame
              (((prover n (a n) (w n)).run (Vstar n (a n) (z n))
                (prover n (a n) (w n)).init).map Prod.fst)
              (adversary n (a n) (z n)))
            (distinguishingGame
              (ProbComp.eval (S n (a n) (z n)))
              (adversary n (a n) (z n))))

/-- **General auxiliary-input zero-knowledge implies poly-time-generable zero-knowledge.**
Every deterministic polynomial-time-generable family has polynomially bounded encoded output length,
and every unary-indexed `ComputationallyIndistinguishable` distinguisher lifts to a full-input
distinguisher by ignoring the extra `(a, z)` component. -/
theorem AuxiliaryInputZeroKnowledge.generableZeroKnowledge {α : Type} {enc : α ↪ List Bool}
    {prover : ℕ → α → List Bool → Prover Unit} {isWitness : α → List Bool → Bool}
    (h : AuxiliaryInputZeroKnowledge enc prover isWitness) :
    GenerableZeroKnowledge enc prover isWitness := by
  intro Vstar hV
  obtain ⟨S, hS_ppt, hS_zk⟩ := h Vstar hV
  refine ⟨S, hS_ppt, fun a w z ha hw hz hw_sat adversary hadversary => ?_⟩
  have ha_poly : PolynomiallyBounded (fun n => (enc (a n)).length) :=
    ((encoding_length enc).comp ha.tidy).polynomiallyBounded
  have hw_poly : PolynomiallyBounded (fun n => (w n).length) :=
    ((encoding_length encBits).comp hw.tidy).polynomiallyBounded
  have hz_poly : PolynomiallyBounded (fun n => (z n).length) :=
    ((encoding_length encBits).comp hz.tidy).polynomiallyBounded
  have htest : IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) encBits) encBool
      (fun p => adversary p.1.1 p.2) :=
    hadversary.preprocess (by fun_prop) (by fun_prop)
  exact hS_zk a w z ha_poly hw_poly hz_poly hw_sat (fun n _ _ view => adversary n view) htest

/-- Under `GenerableZeroKnowledge`, any full-input uniform strict PPT distinguisher
`adversary n (a n) (z n)` also has negligible distinguishing advantage on deterministic
polynomial-time-generable families `a, w, z`, since `(a n, z n)` can be recomputed from `1^n`. -/
theorem GenerableZeroKnowledge.advantage_negligible {α : Type} {enc : α ↪ List Bool}
    {prover : ℕ → α → List Bool → Prover Unit} {isWitness : α → List Bool → Bool}
    (h : GenerableZeroKnowledge enc prover isWitness)
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p : ℕ × α × List Bool => Vstar p.1 p.2.1 p.2.2)) :
    ∃ S : ℕ → α → List Bool → ProbComp (List Bool),
      IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
        (fun p : ℕ × α × List Bool => S p.1 p.2.1 p.2.2) ∧
      ∀ (a : ℕ → α) (w z : ℕ → List Bool),
        ComputableInPolyTime a encUnary enc →
        ComputableInPolyTime w encUnary encBits →
        ComputableInPolyTime z encUnary encBits →
        (∀ n, isWitness (a n) (w n) = true) →
        ∀ adversary : ℕ → α → List Bool → List Bool → ProbComp Bool,
          IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) encBits) encBool
            (fun p => adversary p.1.1 p.1.2.1 p.1.2.2 p.2) →
          Negligible (fun n => Game.advantage
            (distinguishingGame
              (((prover n (a n) (w n)).run (Vstar n (a n) (z n))
                (prover n (a n) (w n)).init).map Prod.fst)
              (adversary n (a n) (z n)))
            (distinguishingGame
              (ProbComp.eval (S n (a n) (z n)))
              (adversary n (a n) (z n)))) := by
  obtain ⟨S, hS_ppt, hS_zk⟩ := h Vstar hV
  refine ⟨S, hS_ppt, fun a w z ha hw hz hw_sat adversary hadversary => ?_⟩
  have ha_tidy := ha.tidy
  have hz_tidy := hz.tidy
  have hD : IsPPT encBool (fun n view => adversary n (a n) (z n) view) :=
    hadversary.preprocess
      (input := encPair encUnary encBits)
      (prepare := fun p => ((p.1, a p.1, z p.1), p.2))
      (by fun_prop)
  exact hS_zk a w z ha hw hz hw_sat (fun n view => adversary n (a n) (z n) view) hD

/-! ### Bundled computational zero-knowledge proof systems -/

/-- A computational zero-knowledge interactive proof system for a language `A : Set α` (with
instance encoding `enc : α ↪ List Bool`), indexed by a security parameter `n : ℕ` [Goldreich,
Micali, and Wigderson][GoldreichMicaliWigderson1991].

* `verifier n a`: the honest verifier's interactive program on security parameter `n` and
  instance `a`, certified uniform strict oracle PPT in `(1^n, a)` by `isOraclePPT_verifier`.
* `prover n a w`: the honest prover strategy on security parameter `n`, instance `a`, and
  witness `w`, certified efficient by `interact`, `eval_interact`, and `isPPT_interact`.
* `isWitness a w`: the bundled polynomial-time witness predicate characterizing membership in `A`
  (`mem_iff_exists_witness`). No witness-length bound is imposed, so `isWitness` by itself need
  not be an `NP` relation (in `zero_knowledge`, `w` is polynomial-time-generable in `1^n`). When
  constructed via a Karp reduction `f : α → CNF ℕ` to `ThreeSAT`
  (`PseudorandomGenerator.zeroKnowledgeProofOfReduction`),
  `isWitness a w` is `ThreeSAT.verifier (f a, w)`, checking a `ThreeSAT` witness for `f a`.
* `complete` and `sound`: completeness `1` for valid witnesses and soundness error at most `1 / 3`
  against all computationally unbounded stateful provers `P : Prover Unit`.
* `zero_knowledge`: **uniform zero-knowledge with poly-time-generable families**
  (`GenerableZeroKnowledge enc prover isWitness`). For every uniform strict oracle PPT malicious
  verifier `Vstar` (taking security parameter `n`, instance `a`, and auxiliary input `z`), there is
  a uniform strict PPT simulator `S` (taking `(1^n, a, z)` without any witness) whose output
  ensemble is computationally indistinguishable from the real interaction output across all
  deterministic polynomial-time-generable families of instances `a : ℕ → α`, valid witnesses
  `w : ℕ → List Bool`, and auxiliary inputs `z : ℕ → List Bool`
  (`ComputableInPolyTime · encUnary _`). The stronger general auxiliary-input property over
  arbitrary polynomially bounded valid families is stated separately as
  `ZeroKnowledgeProof.AuxiliaryInputZeroKnowledge`. -/
structure ZeroKnowledgeProof {α : Type} (enc : α ↪ List Bool) (A : Set α) where
  /-- The honest verifier, indexed by security parameter `n` and instance `a`. -/
  verifier : ℕ → α → WordOracleComp Unit Bool
  /-- The honest prover strategy, taking security parameter `n`, instance `a`, and witness `w`. -/
  prover : ℕ → α → List Bool → Prover Unit
  /-- The polynomial-time witness check used by the honest prover. -/
  isWitness : α → List Bool → Bool
  /-- `isWitness` is computable in plain polynomial time. -/
  polyTime_isWitness :
    ComputableInPolyTime (fun p : α × List Bool => isWitness p.1 p.2)
      (encPair enc encBits) encBool
  /-- `a ∈ A` if and only if some witness `w` satisfies `isWitness a w = true`. -/
  mem_iff_exists_witness : ∀ a, a ∈ A ↔ ∃ w, isWitness a w = true
  /-- The honest verifier is uniform strict oracle PPT in `(1^n, a)`. -/
  isOraclePPT_verifier :
    IsOraclePPTOn (encPair encUnary enc) encBool (fun p : ℕ × α => verifier p.1 p.2)
  /-- The PPT program realizing the honest prover's interaction with a verifier program. -/
  interact : ℕ → α → List Bool → WordOracleComp Unit (List Bool) → ProbComp (List Bool)
  /-- `interact` has the exact output distribution of `prover.run`. -/
  eval_interact : ∀ n a w prog,
    ProbComp.eval (interact n a w prog) =
      ((prover n a w).run prog (prover n a w).init).map Prod.fst
  /-- Running any uniform strict oracle PPT verifier against the honest prover is uniform strict
  PPT in `(1^n, a, w, z)`. -/
  isPPT_interact :
    ∀ Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool),
      IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
        (fun p : ℕ × α × List Bool => Vstar p.1 p.2.1 p.2.2) →
      IsPPTOn (encPair encUnary (encPair enc (encPair encBits encBits))) encBits
        (fun p : ℕ × α × List Bool × List Bool =>
          interact p.1 p.2.1 p.2.2.1 (Vstar p.1 p.2.1 p.2.2.2))
  /-- Perfect completeness: for every valid witness `w` of `a`, the honest prover convinces the
  honest verifier with probability `1`. -/
  complete : ∀ n a w, isWitness a w = true → acceptProb (verifier n a) (prover n a w) = 1
  /-- Soundness: for every `a ∉ A` and every computationally unbounded stateful prover `P`, the
  verifier accepts with probability at most `1 / 3`. -/
  sound : ∀ n, ∀ a ∉ A, ∀ P : Prover Unit, acceptProb (verifier n a) P ≤ 1 / 3
  /-- Uniform computational zero-knowledge with poly-time-generable auxiliary input against all
  uniform strict oracle PPT malicious verifiers, quantified over polynomial-time-generable
  families of instances `a`, valid witnesses `w`, and auxiliary inputs `z`. -/
  zero_knowledge : GenerableZeroKnowledge enc prover isWitness

private theorem ZeroKnowledgeProof.polyTime_isWitness_tidy {α : Type} {enc : α ↪ List Bool}
    {A : Set α} (h : ZeroKnowledgeProof enc A) :
    ComputableTidilyInPolyTime (fun p : α × List Bool => h.isWitness p.1 p.2)
      (encPair enc encBits) encBool := by
  simpa only [← computableInPolyTime_iff_computableTidilyInPolyTime] using h.polyTime_isWitness

private theorem ZeroKnowledgeProof.zero_knowledge_tidy {α : Type} {enc : α ↪ List Bool}
    {A : Set α} (h : ZeroKnowledgeProof enc A) :
    ∀ Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool),
      IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
        (fun p : ℕ × α × List Bool => Vstar p.1 p.2.1 p.2.2) →
      ∃ S : ℕ → α → List Bool → ProbComp (List Bool),
        IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
          (fun p : ℕ × α × List Bool => S p.1 p.2.1 p.2.2) ∧
        ∀ (a : ℕ → α) (w z : ℕ → List Bool),
          ComputableTidilyInPolyTime a encUnary enc →
          ComputableTidilyInPolyTime w encUnary encBits →
          ComputableTidilyInPolyTime z encUnary encBits →
          (∀ n, h.isWitness (a n) (w n) = true) →
          ComputationallyIndistinguishable
            (fun n => ((h.prover n (a n) (w n)).run (Vstar n (a n) (z n))
              (h.prover n (a n) (w n)).init).map Prod.fst)
            (fun n => ProbComp.eval (S n (a n) (z n))) := by
  simpa only [GenerableZeroKnowledge, ← computableInPolyTime_iff_computableTidilyInPolyTime]
    using h.zero_knowledge

namespace ZeroKnowledgeProof

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- Named projection for the restricted polynomial-time-generable zero-knowledge property bundled by
`ZeroKnowledgeProof`. -/
theorem generableZeroKnowledge (zk : ZeroKnowledgeProof enc A) :
    GenerableZeroKnowledge enc zk.prover zk.isWitness :=
  zk.zero_knowledge

/-- General auxiliary-input computational zero-knowledge for a bundled `ZeroKnowledgeProof` system,
ranging over arbitrary polynomially bounded instance, valid-witness, and auxiliary-input
families. -/
def AuxiliaryInputZeroKnowledge (zk : ZeroKnowledgeProof enc A) : Prop :=
  Cslib.Crypto.AuxiliaryInputZeroKnowledge enc zk.prover zk.isWitness

/-- General auxiliary-input zero-knowledge for `zk` implies the bundled restricted
`GenerableZeroKnowledge` guarantee. -/
theorem AuxiliaryInputZeroKnowledge.generableZeroKnowledge {zk : ZeroKnowledgeProof enc A}
    (h : zk.AuxiliaryInputZeroKnowledge) :
    GenerableZeroKnowledge enc zk.prover zk.isWitness :=
  Cslib.Crypto.AuxiliaryInputZeroKnowledge.generableZeroKnowledge h

/-- Fixed-instance auxiliary-input zero-knowledge under `zk.AuxiliaryInputZeroKnowledge`: for any
fixed instance `a`, valid witness `w`, and arbitrary polynomially bounded auxiliary-input family
`z : ℕ → List Bool`, the real and simulated views have negligible distinguishing advantage against
every full-input uniform strict PPT distinguisher. -/
theorem AuxiliaryInputZeroKnowledge.zero_knowledge_const {zk : ZeroKnowledgeProof enc A}
    (h : zk.AuxiliaryInputZeroKnowledge)
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p : ℕ × α × List Bool => Vstar p.1 p.2.1 p.2.2)) :
    ∃ S : ℕ → α → List Bool → ProbComp (List Bool),
      IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
        (fun p : ℕ × α × List Bool => S p.1 p.2.1 p.2.2) ∧
      ∀ a w (z : ℕ → List Bool),
        zk.isWitness a w = true →
        PolynomiallyBounded (fun n => (z n).length) →
        ∀ adversary : ℕ → α → List Bool → List Bool → ProbComp Bool,
          IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) encBits) encBool
            (fun p => adversary p.1.1 p.1.2.1 p.1.2.2 p.2) →
          Negligible (fun n => Game.advantage
            (distinguishingGame
              (((zk.prover n a w).run (Vstar n a (z n))
                (zk.prover n a w).init).map Prod.fst)
              (adversary n a (z n)))
            (distinguishingGame
              (ProbComp.eval (S n a (z n)))
              (adversary n a (z n)))) := by
  obtain ⟨S, hS_ppt, hS_zk⟩ := h Vstar hV
  exact ⟨S, hS_ppt, fun a w z hw hz adversary hadv =>
    hS_zk (fun _ => a) (fun _ => w) z (.const _) (.const _) hz (fun _ => hw) adversary hadv⟩

/-- At every security parameter `n`, the honest verifier of a zero-knowledge proof system is an
interactive proof for `A` with completeness `2 / 3` and soundness `1 / 3`. -/
theorem isInteractiveProof (zk : ZeroKnowledgeProof enc A) (n : ℕ) :
    IsInteractiveProof (zk.verifier n) A (2 / 3) (1 / 3) where
  complete a ha := by
    obtain ⟨w, hw⟩ := (zk.mem_iff_exists_witness a).mp ha
    refine ⟨zk.prover n a w, ?_⟩
    rw [zk.complete n a w hw]
    exact ENNReal.div_le_of_le_mul (by norm_num)
  sound a ha P := zk.sound n a ha P

/-- Every language with a zero-knowledge interactive proof system belongs to `IP`. -/
theorem mem_IP (zk : ZeroKnowledgeProof enc A) : A ∈ IP enc := by
  refine ⟨zk.verifier 0, ?_, zk.isInteractiveProof 0⟩
  have h := zk.isOraclePPT_verifier
  fun_prop

/-- Fixed-instance computational zero-knowledge: for every fixed instance `a` and valid witness `w`
(`zk.isWitness a w = true`), and every polynomial-time auxiliary input family `z : ℕ → List Bool`,
the real interaction output and simulator output are computationally indistinguishable. -/
theorem zero_knowledge_const (zk : ZeroKnowledgeProof enc A)
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p : ℕ × α × List Bool => Vstar p.1 p.2.1 p.2.2)) :
    ∃ S : ℕ → α → List Bool → ProbComp (List Bool),
      IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
        (fun p : ℕ × α × List Bool => S p.1 p.2.1 p.2.2) ∧
      ∀ a w (z : ℕ → List Bool),
        zk.isWitness a w = true →
        ComputableInPolyTime z encUnary encBits →
        ComputationallyIndistinguishable
          (fun n => ((zk.prover n a w).run (Vstar n a (z n))
            (zk.prover n a w).init).map Prod.fst)
          (fun n => ProbComp.eval (S n a (z n))) := by
  obtain ⟨S, hS_ppt, hS_zk⟩ := zk.zero_knowledge_tidy Vstar hV
  exact ⟨S, hS_ppt, fun a w z hw hz =>
    hS_zk (fun _ => a) (fun _ => w) z (const a) (const w) hz.tidy (fun _ => hw)⟩

end ZeroKnowledgeProof

/-! ### GMW zero-knowledge proof systems -/

/-- Construct the Goldreich–Micali–Wigderson zero-knowledge proof system for any language `A` with
a polynomial-time many-one reduction `f : α → CNF ℕ` to `ThreeSAT`, using a pseudorandom generator
with stretch at least `3 * k + 1` and the 3-copy masked-3SAT commitment protocol in
`Cslib.Crypto.GMW`. The bundled witness check `isWitness a w` is `ThreeSAT.verifier (f a, w)` on
the reduced formula `f a`. -/
noncomputable def PseudorandomGenerator.zeroKnowledgeProofOfReduction
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    {f : α → CNF ℕ} (hf : ComputableInPolyTime f enc encCNF)
    (hred : ∀ a, a ∈ A ↔ f a ∈ ThreeSAT) :
    ZeroKnowledgeProof enc A where
  verifier := GMW.gmwVerifier generator length f
  prover n a w := GMW.gmwProver generator (n + 7) (length (n + 7)) (f a) w
  isWitness a w := ThreeSAT.verifier (f a, w)
  polyTime_isWitness := by
    have := hf.tidy
    fun_prop
  mem_iff_exists_witness a := by
    rw [hred a]
    refine ⟨fun ha => ?_, fun ⟨w, hw⟩ => ?_⟩
    · obtain ⟨w, _, hw⟩ := (ThreeSAT.isVerifier (f a)).mp ha
      exact ⟨w, hw⟩
    · simp only [ThreeSAT.verifier, SAT.verifier, Bool.and_eq_true, List.all_eq_true,
        decide_eq_true_eq] at hw
      exact ⟨hw.1, SAT.assignment (f a) w, hw.2⟩
  isOraclePPT_verifier := GMW.isOraclePPTOn_gmwVerifier hG.polyTime hG.length_eq hf
  interact n a w prog := GMW.gmwInteract generator (n + 7) (length (n + 7)) (f a) w prog
  eval_interact n a w prog := GMW.eval_gmwInteract generator (n + 7) (length (n + 7)) (f a) w prog
  isPPT_interact _ hV := GMW.isPPTOn_gmwInteract hG.polyTime hG.length_eq hf hV
  complete n a _ hw := GMW.acceptProb_gmwVerifier_gmwProver hG.length_eq f n a hw
  sound n a ha P :=
    GMW.acceptProb_gmwVerifier_le hG.length_eq hstretch f n a (mt (hred a).mpr ha) P
  zero_knowledge Vstar hV :=
    ⟨GMW.gmwSimulator generator length f Vstar,
      GMW.isPPTOn_gmwSimulator hG.polyTime hG.length_eq hf hV,
      fun _ _ _ ha hw_comp hz hw_sat =>
        GMW.gmwView_indistinguishable_gmwSimulator hG hf hV ha hw_comp hz
          hw_sat⟩

/-- Under the explicit advice-PRG premise `GMW.AdvicePRG enc generator length`, the GMW proof
system `hG.zeroKnowledgeProofOfReduction hstretch hf hred` satisfies general auxiliary-input
zero-knowledge (`ZeroKnowledgeProof.AuxiliaryInputZeroKnowledge`) across all arbitrary polynomially
bounded valid instance, witness, and auxiliary-input families. -/
theorem PseudorandomGenerator.auxiliaryInputZeroKnowledge_zeroKnowledgeProofOfReduction
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    {f : α → CNF ℕ} (hf : ComputableInPolyTime f enc encCNF)
    (hred : ∀ a, a ∈ A ↔ f a ∈ ThreeSAT)
    (hAdv : GMW.AdvicePRG enc generator length) :
    (hG.zeroKnowledgeProofOfReduction hstretch hf hred).AuxiliaryInputZeroKnowledge := by
  intro Vstar hV
  exact ⟨GMW.gmwSimulator generator length f Vstar,
    GMW.isPPTOn_gmwSimulator hG.polyTime hG.length_eq hf hV,
    fun _ _ _ ha hw hz hw_sat _ hadv =>
      hAdv.gmwView_negligible hf hV hadv ha hw hz hw_sat⟩

/-- The Goldreich–Micali–Wigderson computational zero-knowledge proof system for `ThreeSAT`, built
from any pseudorandom generator with stretch at least `3 * k + 1` via the 3-copy masked-3SAT
commitment protocol in `Cslib.Crypto.GMW`. -/
noncomputable def PseudorandomGenerator.zeroKnowledgeProofThreeSAT
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k) :
    ZeroKnowledgeProof encCNF ThreeSAT :=
  hG.zeroKnowledgeProofOfReduction hstretch (by fun_prop) (fun _ => Iff.rfl)

/-- Under the explicit advice-PRG premise `GMW.AdvicePRG encCNF generator length`, the GMW proof
system `hG.zeroKnowledgeProofThreeSAT hstretch` satisfies general auxiliary-input zero-knowledge
(`ZeroKnowledgeProof.AuxiliaryInputZeroKnowledge`). -/
theorem PseudorandomGenerator.auxiliaryInputZeroKnowledge_zeroKnowledgeProofThreeSAT
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (hAdv : GMW.AdvicePRG encCNF generator length) :
    (hG.zeroKnowledgeProofThreeSAT hstretch).AuxiliaryInputZeroKnowledge :=
  hG.auxiliaryInputZeroKnowledge_zeroKnowledgeProofOfReduction hstretch (by fun_prop)
    (fun _ => Iff.rfl) hAdv

/-- **Goldreich–Micali–Wigderson theorem (from a pseudorandom generator).** Given a pseudorandom
generator with stretch at least `3 * k + 1` (such as `fun k => 3 * k + 1`), every language
`A ∈ NP enc` has a computational zero-knowledge interactive proof system
[Goldreich, Micali, and Wigderson][GoldreichMicaliWigderson1991] in the uniform
polynomial-time-generable sense (`GenerableZeroKnowledge`). -/
theorem PseudorandomGenerator.exists_zeroKnowledgeProof_of_mem_NP
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (hA : A ∈ NP enc) :
    Nonempty (ZeroKnowledgeProof enc A) := by
  obtain ⟨f, hf, hred⟩ := ThreeSAT_npHard enc A hA
  exact ⟨hG.zeroKnowledgeProofOfReduction hstretch hf hred⟩

/-- **Goldreich–Micali–Wigderson theorem under an explicit advice-PRG premise.** Given a
pseudorandom generator with stretch at least `3 * k + 1` that also satisfies the advice-supplied
premise `GMW.AdvicePRG enc generator length`, every language `A ∈ NP enc` has a computational
zero-knowledge interactive proof system satisfying general auxiliary-input zero-knowledge
(`ZeroKnowledgeProof.AuxiliaryInputZeroKnowledge`) across all polynomially bounded valid families.
This theorem takes `GMW.AdvicePRG` as an explicit hypothesis rather than deriving it from uniform
`PseudorandomGenerator` or `OneWay` security. -/
theorem PseudorandomGenerator.exists_auxiliaryInputZeroKnowledge_of_mem_NP
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (hAdv : GMW.AdvicePRG enc generator length)
    (hA : A ∈ NP enc) :
    ∃ zk : ZeroKnowledgeProof enc A, zk.AuxiliaryInputZeroKnowledge := by
  obtain ⟨f, hf, hred⟩ := ThreeSAT_npHard enc A hA
  exact ⟨hG.zeroKnowledgeProofOfReduction hstretch hf hred,
    hG.auxiliaryInputZeroKnowledge_zeroKnowledgeProofOfReduction hstretch hf hred hAdv⟩

/-- **Goldreich–Micali–Wigderson theorem (from a one-way function).** If a one-way function exists,
then every language `A ∈ NP enc` has a computational zero-knowledge interactive proof system
[Goldreich, Micali, and Wigderson][GoldreichMicaliWigderson1991], in the uniform-family sense of
`GenerableZeroKnowledge` (`ZeroKnowledgeProof.zero_knowledge`): instances, witnesses and auxiliary
inputs range over polynomial-time-generable families rather than arbitrary ones. -/
theorem OneWay.exists_zeroKnowledgeProof_of_mem_NP
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {f : List Bool → List Bool} (hf : OneWay f) (hA : A ∈ NP enc) :
    Nonempty (ZeroKnowledgeProof enc A) := by
  obtain ⟨G, hG⟩ := hf.exists_pseudorandomGenerator_three_mul
  exact hG.exists_zeroKnowledgeProof_of_mem_NP (fun _ => le_rfl) hA

end Cslib.Crypto

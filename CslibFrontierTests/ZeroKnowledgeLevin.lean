/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import CslibFrontier.Crypto.Computational.ZeroKnowledge.Levin

/-!
# Zero knowledge with the relation's own witnesses

Checked clients of `Cslib.Crypto.OneWay.exists_zeroKnowledgeProof_of_npRelation` and of the
Levin-reduction proof system: the honest prover convinces the verifier with probability `1` from
a witness of the original NP relation.
-/

public section

namespace ComplexityTests.ZeroKnowledgeLevin

open Cslib.Complexity Cslib.Crypto Cslib.Probability

/-- From a one-way function, the GMW proof system for an NP relation accepts the honest prover
running on any witness of the relation with probability `1`. -/
example {f : List Bool → List Bool} (hf : OneWay f) {α : Type} {enc : α ↪ List Bool}
    (R : NPRelation enc) :
    ∃ zk : ZeroKnowledgeProof enc R.language, ∀ n a w, R.IsWitness a w →
      acceptProb (zk.verifier n a) (zk.prover n a w) = 1 := by
  obtain ⟨zk, hzk⟩ := hf.exists_zeroKnowledgeProof_of_npRelation R
  exact ⟨zk, fun n a w hw => zk.complete n a w ((hzk a w).2 hw)⟩

/-- The Levin-reduction proof system for SAT's own relation, through the explicit SAT → 3SAT
reduction: its witnesses are SAT certificates, and its honest prover runs on their 3SAT images. -/
example {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length) (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (φ : Cslib.Logic.PL.CNF ℕ) (w : List Bool) (hw : SAT.npRelation.IsWitness φ w) (n : ℕ) :
    acceptProb ((hG.levinZeroKnowledgeProof hstretch toThreeSATLevinReduction).verifier n φ)
      ((hG.levinZeroKnowledgeProof hstretch toThreeSATLevinReduction).prover n φ w) = 1 :=
  (hG.levinZeroKnowledgeProof hstretch toThreeSATLevinReduction).complete n φ w
    ((hG.isWitness_levinZeroKnowledgeProof hstretch _ φ w).2 hw)

end ComplexityTests.ZeroKnowledgeLevin

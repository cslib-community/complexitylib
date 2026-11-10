/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.IP.Repetition
import CslibFrontier.Crypto.Computational.ZeroKnowledge.Amplification
import CslibFrontier.Tactic.PPT

/-! Tests for Naor's bit commitment scheme and the Goldreich–Micali–Wigderson
computational zero-knowledge interactive proof system for `NP`. -/

namespace CslibFrontierTests.Crypto.ZeroKnowledge

open Cslib Cslib.Crypto Cslib.Complexity Cslib.Probability Cslib.Logic.PL Turing.MultiTapeTM

private def tripleGen (s : List Bool) : List Bool :=
  s ++ s ++ s ++ [false]

private theorem length_tripleGen (s : List Bool) :
    (tripleGen s).length = 3 * s.length + 1 := by
  simp only [tripleGen, List.length_append, List.length_cons, List.length_nil]
  omega

-- Concrete completeness check for Naor's commitment scheme on a 2-bit seed.
example (r : List Bool) (b : Bool) :
    naorVerify tripleGen 2 r
      (naorCommit tripleGen r b [true, false]) b [true, false] = true :=
  naorVerify_naorCommit r b (by decide)

-- Concrete soundness check for Naor's statistical binding bound.
-- (We do not attempt an unconditional `BitCommitmentScheme` instance: statistically binding,
-- computationally hiding commitments against stateful PPT receivers imply one-way functions,
-- whose existence is open. Instead we test `naorVerify` and `naorBindingProb` unconditionally
-- and instantiate `naorBitCommitment` from a PRG / OWF below.)
example (n : ℕ) :
    naorBindingProb tripleGen (fun k => 3 * k + 1) n ≤ (1 / 2 : ENNReal) ^ (n + 1) :=
  naorBindingProb_le_of_three_mul_add_one length_tripleGen n le_rfl

/-- Unconditional non-vacuity instance of `ZeroKnowledgeProof` for the empty language `∅`. -/
noncomputable def emptyZeroKnowledgeProof : ZeroKnowledgeProof encBits (∅ : Set (List Bool)) where
  verifier _ _ := pure false
  prover _ _ _ :=
    { State := ℕ × List Bool
      init := (0, [false, false, false])
      respond := fun q s => PMF.pure (GMW.twoRoundStep (fun _ => []) (fun _ => []) q.2 s) }
  isWitness _ _ := false
  polyTime_isWitness := by fun_prop
  mem_iff_exists_witness a := by simp
  isOraclePPT_verifier := by fun_prop
  interact _ _ _ prog :=
    Prod.fst <$> GMW.runTwoRound (fun _ => []) (fun _ => []) prog (0, [false, false, false])
  eval_interact _ _ _ prog :=
    (ProbComp.eval_map _ _).trans
      (congrArg (PMF.map Prod.fst)
        (GMW.eval_runTwoRound (fun _ => []) (fun _ => []) prog (0, [false, false, false])))
  isPPT_interact {Vstar} hV := by
    have hrun := GMW.isPPTOn_runTwoRound hV
      (input := encPair encUnary (encPair encBits (encPair encBits encBits)))
      (prepare := fun p : ℕ × List Bool × List Bool × List Bool => (p.1, p.2.1, p.2.2.2))
      (reply1 := fun _ => []) (reply2 := fun _ => []) (bound := fun _ => 0)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    exact hrun.map (by fun_prop)
  complete _ _ _ hw := Bool.noConfusion hw
  sound _ _ _ P := by simp [acceptProb, Prover.run]
  zero_knowledge {_} _ :=
    ⟨fun _ _ _ => pure [], by ppt, fun _ _ _ _ _ _ hw => Bool.noConfusion (hw 0)⟩

/-- Unconditional instance of `ZeroKnowledgeProof` for the full language `Set.univ`, in which
every witness is valid. The verifier always accepts, the prover sends empty replies, and the
simulator runs `Vstar` against that same silent prover, so the zero-knowledge quantifiers range over
satisfiable witness families. -/
noncomputable def univZeroKnowledgeProof :
    ZeroKnowledgeProof encBits (Set.univ : Set (List Bool)) where
  verifier _ _ := pure true
  prover _ _ _ :=
    { State := ℕ × List Bool
      init := (0, [false, false, false])
      respond := fun q s => PMF.pure (GMW.twoRoundStep (fun _ => []) (fun _ => []) q.2 s) }
  isWitness _ _ := true
  polyTime_isWitness := by fun_prop
  mem_iff_exists_witness a := by simp
  isOraclePPT_verifier := by fun_prop
  interact _ _ _ prog :=
    Prod.fst <$> GMW.runTwoRound (fun _ => []) (fun _ => []) prog (0, [false, false, false])
  eval_interact _ _ _ prog :=
    (ProbComp.eval_map _ _).trans
      (congrArg (PMF.map Prod.fst)
        (GMW.eval_runTwoRound (fun _ => []) (fun _ => []) prog (0, [false, false, false])))
  isPPT_interact {Vstar} hV := by
    have hrun := GMW.isPPTOn_runTwoRound hV
      (input := encPair encUnary (encPair encBits (encPair encBits encBits)))
      (prepare := fun p : ℕ × List Bool × List Bool × List Bool => (p.1, p.2.1, p.2.2.2))
      (reply1 := fun _ => []) (reply2 := fun _ => []) (bound := fun _ => 0)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    exact hrun.map (by fun_prop)
  complete _ _ _ _ := by simp [acceptProb, Prover.run]
  sound _ _ ha := absurd (Set.mem_univ _) ha
  zero_knowledge {Vstar} hV := by
    refine ⟨fun n a z => Prod.fst <$>
      GMW.runTwoRound (fun _ => []) (fun _ => []) (Vstar n a z) (0, [false, false, false]),
      ?_, fun _ _ _ _ _ _ _ => ?_⟩
    · have hrun := GMW.isPPTOn_runTwoRound hV
        (input := encPair encUnary (encPair encBits encBits))
        (prepare := fun p : ℕ × List Bool × List Bool => p)
        (reply1 := fun _ => []) (reply2 := fun _ => []) (bound := fun _ => 0)
        (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
        (fun _ _ => le_rfl) (fun _ _ => le_rfl)
      exact hrun.map (by fun_prop)
    · convert ComputationallyIndistinguishable.refl _ using 2 with n
      exact (ProbComp.eval_map _ _).trans
        (congrArg (PMF.map Prod.fst)
          (GMW.eval_runTwoRound (fun _ => []) (fun _ => []) _ (0, [false, false, false])))

/-- Unconditional general auxiliary-input zero-knowledge for `univZeroKnowledgeProof` across all
arbitrary polynomially bounded valid instance, witness, and auxiliary-input families. -/
theorem univZeroKnowledgeProof_auxiliaryInputZeroKnowledge :
    univZeroKnowledgeProof.AuxiliaryInputZeroKnowledge := by
  intro Vstar hV
  refine ⟨fun n a z => Prod.fst <$>
    GMW.runTwoRound (fun _ => []) (fun _ => []) (Vstar n a z) (0, [false, false, false]),
    ?_, fun a w z _ _ _ _ _ _ _ _ => ?_⟩
  · have hrun := GMW.isPPTOn_runTwoRound hV
      (input := encPair encUnary (encPair encBits encBits))
      (prepare := fun p : ℕ × List Bool × List Bool => p)
      (reply1 := fun _ => []) (reply2 := fun _ => []) (bound := fun _ => 0)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    exact hrun.map (by fun_prop)
  · convert negligible_zero using 2 with n
    have heq :
        ProbComp.eval (Prod.fst <$> GMW.runTwoRound (fun _ => []) (fun _ => [])
          (Vstar n (a n) (z n)) (0, [false, false, false])) =
        ((univZeroKnowledgeProof.prover n (a n) (w n)).run (Vstar n (a n) (z n))
          (univZeroKnowledgeProof.prover n (a n) (w n)).init).map Prod.fst :=
      (ProbComp.eval_map _ _).trans
        (congrArg (PMF.map Prod.fst)
          (GMW.eval_runTwoRound (fun _ => []) (fun _ => []) _ (0, [false, false, false])))
    rw [heq, Game.advantage_self]

-- The stronger-to-restricted bridge recovers `GenerableZeroKnowledge` from
-- `AuxiliaryInputZeroKnowledge`.
example : GenerableZeroKnowledge encBits univZeroKnowledgeProof.prover
    univZeroKnowledgeProof.isWitness :=
  univZeroKnowledgeProof_auxiliaryInputZeroKnowledge.generableZeroKnowledge

-- Concrete satisfiable 3CNF formula and witness check.
private def satFormula : CNF ℕ := [[(0, true), (1, false)]]

private theorem satFormula_verified :
    ThreeSAT.verifier (satFormula, [true, false]) = true := by
  decide

-- Concrete completeness of the GMW verifier against the honest GMW prover on `satFormula`.
example (n : ℕ) :
    acceptProb
      (GMW.gmwVerifier tripleGen (fun k => 3 * k + 1) id n satFormula)
      (GMW.gmwProver tripleGen (n + 7) (3 * (n + 7) + 1) satFormula [true, false]) = 1 :=
  GMW.acceptProb_gmwVerifier_gmwProver length_tripleGen id n satFormula satFormula_verified

-- Concrete soundness of the GMW verifier on the unsatisfiable formula `[[]]` against all provers.
private theorem unsatFormula_not_mem_ThreeSAT : ([] :: [] : CNF ℕ) ∉ ThreeSAT := by
  rintro ⟨_, τ, hτ⟩
  cases hτ

example (n : ℕ) (P : Prover Unit) :
    acceptProb
      (GMW.gmwVerifier tripleGen (fun k => 3 * k + 1) id n ([[]] : CNF ℕ)) P ≤ 1 / 3 :=
  GMW.acceptProb_gmwVerifier_le length_tripleGen (fun _ => le_rfl) id n [[]]
    unsatFormula_not_mem_ThreeSAT P

-- Every language with a zero-knowledge interactive proof system belongs to `IP`.
example : (∅ : Set (List Bool)) ∈ IP encBits :=
  emptyZeroKnowledgeProof.mem_IP

example : (Set.univ : Set (List Bool)) ∈ IP encBits :=
  univZeroKnowledgeProof.mem_IP

-- `ThreeSAT` has a computational zero-knowledge proof system from any one-way function.
example {f : List Bool → List Bool} (hf : OneWay f) :
    Nonempty (ZeroKnowledgeProof encCNF ThreeSAT) :=
  hf.exists_zeroKnowledgeProof_of_mem_NP ThreeSAT.mem_NP

-- Under an explicit advice-PRG premise, every NP language has a GMW zero-knowledge proof system
-- satisfying general `AuxiliaryInputZeroKnowledge`.
example {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (hAdv : GMW.AdvicePRG encCNF generator length) :
    ∃ zk : ZeroKnowledgeProof encCNF ThreeSAT, zk.AuxiliaryInputZeroKnowledge :=
  hG.exists_auxiliaryInputZeroKnowledge_of_mem_NP hstretch hAdv ThreeSAT.mem_NP

-- Machine-level input-tape prefix locality: a `fuel`-step run on `u ++ v` depends only on
-- `u ++ v.take fuel`.
example {k : ℕ} {State : Type} (machine : Turing.MultiTapePTM k Bool State)
    (fuel : ℕ) (u v : List Bool) :
    machine.runClosed fuel (u ++ v.take fuel) = machine.runClosed fuel (u ++ v) :=
  machine.runClosed_append_take fuel u v

example {k : ℕ} {State Operation : Type} [DecidableEq Operation]
    (machine : Turing.MultiTapePTM k Bool State Operation)
    (fuel : ℕ) (u v : List Bool) :
    machine.runOracle fuel (u ++ v.take fuel) = machine.runOracle fuel (u ++ v) :=
  machine.runOracle_append_take fuel u v

-- Non-vacuity of `IsPPTWithAux` and `IsOraclePPTWithAux` via `of_machine`, together with their
-- bridges to `IsPPTOn` and `IsOraclePPTOn`.
private def haltClosedMachine : Turing.MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ _ := .step ⟨0, Fin.elim0, none, none⟩ (fun _ => none) (fun _ => 0)

private def haltOracleMachine : Turing.MultiTapePTM 0 Bool Unit Unit where
  initial := ()
  tr _ _ _ _ _ := .step ⟨0, Fin.elim0, none, none⟩ (fun _ => none) (fun _ => 0)

example :
    IsPPTWithAux encBits encBits
      (fun a z =>
        haltClosedMachine.runClosed (1 * ((encBits a).length + 1) ^ 1)
          (encPair encBits encBits (a, z))) :=
  IsPPTWithAux.of_machine haltClosedMachine 1 1

example :
    IsPPTOn (encPair encBits encBits) encBits
      (fun (a, z) =>
        haltClosedMachine.runClosed (1 * ((encBits a).length + 1) ^ 1)
          (encPair encBits encBits (a, z))) :=
  (IsPPTWithAux.of_machine (input := encBits) haltClosedMachine 1 1).isPPTOn

example :
    IsOraclePPTWithAux encBits encBits
      (fun a z =>
        haltOracleMachine.runOracle (1 * ((encBits a).length + 1) ^ 1)
          (encPair encBits encBits (a, z))) :=
  IsOraclePPTWithAux.of_machine haltOracleMachine 1 1

example :
    IsOraclePPTOn (encPair encBits encBits) encBits
      (fun (a, z) =>
        haltOracleMachine.runOracle (1 * ((encBits a).length + 1) ^ 1)
          (encPair encBits encBits (a, z))) :=
  (IsOraclePPTWithAux.of_machine (input := encBits) haltOracleMachine 1 1).isOraclePPTOn

-- Truncating the auxiliary input of an `IsPPTOn` / `IsOraclePPTOn` program to a polynomial in the
-- primary input length upgrades it to `IsPPTWithAux` / `IsOraclePPTWithAux`.
example {program : List Bool → List Bool → ProbComp (List Bool)}
    (h : IsPPTOn (encPair encBits encBits) encBits (fun (a, z) => program a z)) :
    IsPPTWithAux encBits encBits
      (fun a z => program a (z.take (2 * ((encBits a).length + 1) ^ 3))) :=
  h.isPPTWithAux_take 2 3

example {program : List Bool → List Bool → WordOracleComp Unit (List Bool)}
    (h : IsOraclePPTOn (encPair encBits encBits) encBits (fun (a, z) => program a z)) :
    IsOraclePPTWithAux encBits encBits
      (fun a z => program a (z.take (2 * ((encBits a).length + 1) ^ 3))) :=
  h.isOraclePPTWithAux_take 2 3

-- Unconditional non-vacuity of `UnboundedAuxiliaryInputZeroKnowledge` and
-- `InstanceAuxiliaryInputZeroKnowledge` for `univZeroKnowledgeProof`.
example : univZeroKnowledgeProof.UnboundedAuxiliaryInputZeroKnowledge :=
  univZeroKnowledgeProof_auxiliaryInputZeroKnowledge.unboundedAuxiliaryInputZeroKnowledge

example : univZeroKnowledgeProof.InstanceAuxiliaryInputZeroKnowledge :=
  let hub := univZeroKnowledgeProof_auxiliaryInputZeroKnowledge.unboundedAuxiliaryInputZeroKnowledge
  hub.instanceAuxiliaryInputZeroKnowledge

example : univZeroKnowledgeProof.InstanceAuxiliaryInputZeroKnowledge :=
  univZeroKnowledgeProof_auxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge

-- Under `GMW.AdvicePRG`, the GMW `ThreeSAT` proof system satisfies both
-- `UnboundedAuxiliaryInputZeroKnowledge` and Goldreich-style `InstanceAuxiliaryInputZeroKnowledge`.
example {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (hAdv : GMW.AdvicePRG encCNF generator length) :
    (hG.zeroKnowledgeProofThreeSAT hstretch).UnboundedAuxiliaryInputZeroKnowledge ∧
      (hG.zeroKnowledgeProofThreeSAT hstretch).InstanceAuxiliaryInputZeroKnowledge :=
  let hzk := hG.auxiliaryInputZeroKnowledge_zeroKnowledgeProofThreeSAT hstretch hAdv
  ⟨hzk.unboundedAuxiliaryInputZeroKnowledge, hzk.instanceAuxiliaryInputZeroKnowledge⟩

-- Polynomial-count sequential repetition of any strict oracle PPT verifier is strict oracle PPT.
example {round : ℕ × List Bool → WordOracleComp Unit Bool}
    (hround : IsOraclePPTOn (encPair encUnary encBits) encBool round) :
    IsOraclePPTOn (encPair encUnary encBits) encBool
      (fun (n, a) => sequentialRepeat (n + 1) (round (n, a))) :=
  hround.sequentialRepeat_count (by fun_prop)

-- Sequentially repeating `emptyZeroKnowledgeProof`'s verifier `n + 1` times yields a `ZKProof`
-- with soundness `(1 / 3) ^ (n + 1)` and `NegligibleSoundness`.
private noncomputable def amplifiedEmptyZKProof :
    ZKProof encBits (∅ : Set (List Bool)) (fun n => (1 / 3 : ENNReal) ^ (n + 1)) where
  verifier n a := sequentialRepeat (n + 1) (emptyZeroKnowledgeProof.verifier n a)
  prover := emptyZeroKnowledgeProof.prover
  isWitness := emptyZeroKnowledgeProof.isWitness
  polyTime_isWitness := emptyZeroKnowledgeProof.polyTime_isWitness
  mem_iff_exists_witness := emptyZeroKnowledgeProof.mem_iff_exists_witness
  isOraclePPT_verifier :=
    emptyZeroKnowledgeProof.isOraclePPT_verifier.sequentialRepeat_count (by fun_prop)
  interact := emptyZeroKnowledgeProof.interact
  eval_interact := emptyZeroKnowledgeProof.eval_interact
  isPPT_interact := emptyZeroKnowledgeProof.isPPT_interact
  complete _ _ _ hw := Bool.noConfusion hw
  sound n a ha P :=
    acceptProb_sequentialRepeat_le (emptyZeroKnowledgeProof.sound n a ha) (n + 1) P
  zero_knowledge := emptyZeroKnowledgeProof.zero_knowledge

example : amplifiedEmptyZKProof.NegligibleSoundness :=
  amplifiedEmptyZKProof.negligibleSoundness_one_third_pow (fun n => Nat.le_succ n)

example (a : ℕ → List Bool) (P : ℕ → Prover Unit) :
    Negligible (fun n => (acceptProb (amplifiedEmptyZKProof.verifier n (a n)) (P n)).toNNReal) :=
  (amplifiedEmptyZKProof.negligibleSoundness_one_third_pow
    (fun n => Nat.le_succ n)).acceptProb_toNNReal_negligible (fun _ => Set.notMem_empty _) P

example : (∅ : Set (List Bool)) ∈ IP encBits :=
  (amplifiedEmptyZKProof.negligibleSoundness_one_third_pow (fun n => Nat.le_succ n)).mem_IP

-- Negative guard: constant `1 / 3` soundness (`toZKProof`) is not `NegligibleSoundness`.
example : ¬ univZeroKnowledgeProof.toZKProof.NegligibleSoundness := by
  intro h
  refine not_negligible_const (c := ((1 / 3 : ENNReal).toNNReal)) ?_ h.2
  rw [ENNReal.toNNReal_div, ENNReal.toNNReal_one, ENNReal.toNNReal_ofNat]
  norm_num

-- Concrete completeness and soundness of the sequentially amplified GMW protocol (`gmwSeqVerifier`
-- and `gmwSeqProver`).
example (n : ℕ) :
    acceptProb
      (GMW.gmwSeqVerifier tripleGen (fun k => 3 * k + 1) id (fun m => m + 1) n satFormula)
      (GMW.gmwSeqProver tripleGen (n + 7) (3 * (n + 7) + 1) satFormula [true, false] (n + 1)) = 1 :=
  GMW.acceptProb_gmwSeqVerifier_gmwSeqProver length_tripleGen id (fun m => m + 1) n satFormula
    satFormula_verified

example (n : ℕ) (P : Prover Unit) :
    acceptProb
      (GMW.gmwSeqVerifier tripleGen (fun k => 3 * k + 1) id (fun m => m + 1) n ([[]] : CNF ℕ)) P ≤
      (1 / 3 : ENNReal) ^ (n + 1) :=
  GMW.acceptProb_gmwSeqVerifier_le length_tripleGen (fun _ => le_rfl) id (fun m => m + 1) n [[]]
    unsatFormula_not_mem_ThreeSAT P

-- Soundness-amplified `ZKProof` for `ThreeSAT` and every NP relation from any one-way function or
-- advice-PRG.
example {f : List Bool → List Bool} (hf : OneWay f) :
    (∃ zk : ZKProof encCNF ThreeSAT (fun n => (1 / 3 : ENNReal) ^ (n + 1)),
      zk.NegligibleSoundness) ∧
    (∃ zk : ZKProof encCNF ThreeSAT.npRelation.language (fun n => (1 / 3 : ENNReal) ^ (n + 1)),
      (∀ a w, zk.isWitness a w = true ↔ ThreeSAT.npRelation.IsWitness a w) ∧
      zk.NegligibleSoundness) :=
  ⟨hf.exists_zkProof_of_mem_NP ThreeSAT.mem_NP,
    hf.exists_zkProof_of_npRelation ThreeSAT.npRelation⟩

example {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (hAdv : GMW.AdvicePRG encCNF generator length) :
    (hG.zkProofThreeSAT hstretch).NegligibleSoundness ∧
    (hG.zkProofThreeSAT hstretch).AuxiliaryInputZeroKnowledge ∧
    (hG.zkProofThreeSAT hstretch).UnboundedAuxiliaryInputZeroKnowledge ∧
    (hG.zkProofThreeSAT hstretch).InstanceAuxiliaryInputZeroKnowledge := by
  have hzk := hG.auxiliaryInputZeroKnowledge_zkProofThreeSAT hstretch hAdv
  exact ⟨hG.negligibleSoundness_zkProofThreeSAT hstretch,
    hzk, hzk.unboundedAuxiliaryInputZeroKnowledge, hzk.instanceAuxiliaryInputZeroKnowledge⟩

end CslibFrontierTests.Crypto.ZeroKnowledge

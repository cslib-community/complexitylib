/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.IP.GraphNonIsomorphism
import Complexity.Computability.Complexity.Classes.IP.PSPACE
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-! Interactive proofs: concrete graphs, honest and cheating provers, class inclusions, and the
polynomial-space evaluation of the optimal prover. -/

namespace ComplexityTests.InteractiveProofs

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

/-! ### Concrete graphs -/

/-- A path on three vertices. -/
private def path : Graph := ([0, 1, 2], [(0, 1), (1, 2)])

/-- A triangle. -/
private def triangle : Graph := ([0, 1, 2], [(0, 1), (1, 2), (2, 0)])

/-- The path with other labels, a repeated vertex entry, and an edge to an undeclared vertex. -/
private def path' : Graph := ([7, 5, 9, 5], [(9, 5), (5, 7), (7, 100)])

-- Repeated entries are dropped; the order of first occurrences is kept.
example : path'.distinctVertices = [7, 5, 9] := by decide

-- Duplicate vertex entries do not change the graph: one vertex is one vertex.
example : ((([1, 1], []), ([1], [])) : Graph × Graph) ∈ GraphIsomorphism := by
  rw [mem_GraphIsomorphism_iff]
  decide

-- Relabeling, repetition and an edge leaving the declared vertices preserve the isomorphism type.
example : (path, path') ∈ GraphIsomorphism := by
  rw [mem_GraphIsomorphism_iff]
  decide

-- A path and a triangle are not isomorphic.
theorem path_triangle : (path, triangle) ∈ GraphNonIsomorphism := by
  rw [GraphNonIsomorphism, Set.mem_compl_iff, mem_GraphIsomorphism_iff]
  decide

-- The empty graph and a single vertex are not isomorphic.
example : ((([], []), ([3], [])) : Graph × Graph) ∈ GraphNonIsomorphism := by
  rw [GraphNonIsomorphism, Set.mem_compl_iff, mem_GraphIsomorphism_iff]
  decide

/-! ### `GraphIsomorphism ∈ NP` -/

-- The certificate decoding `[7, 5, 9]` (positions `0, 1, 2` of `path'.1 = [7, 5, 9, 5]` in unary
-- blocks of width `4`) maps positions `0, 1, 2` of `path` to `7, 5, 9` and is accepted.
example : GraphIsomorphism.verifier ((path, path'),
    [false, false, false, false, true, false, false, false, true, true, false, false]) = true := by
  decide

-- Mapping the end vertex `0` to the middle vertex `5` (`[5, 7, 9]`) breaks an edge and is rejected.
example : GraphIsomorphism.verifier ((path, path'),
    [true, false, false, false, false, false, false, false, true, true, false, false]) = false := by
  decide

-- A decoded list with a duplicate vertex (`[7, 7, 9]`) is rejected.
example : GraphIsomorphism.verifier ((path, path'),
    [false, false, false, false, false, false, false, false, true, true, false, false]) =
      false := by
  decide

-- Graphs with different numbers of distinct vertices are rejected.
example : GraphIsomorphism.verifier (((([1, 2], []), ([1], [])) : Graph × Graph), []) = false := by
  decide

example : GraphIsomorphism ∈ IP (encPair encGraph encGraph) :=
  NP_subset_IP _ GraphIsomorphism.mem_NP

/-! ### The protocol for `GraphNonIsomorphism` -/

-- The honest prover convinces the verifier of the non-isomorphism of a path and a triangle.
example : acceptProb (GraphNonIsomorphism.verifier (path, triangle))
    (GraphNonIsomorphism.prover (path, triangle)) = 1 :=
  GraphNonIsomorphism.acceptProb_verifier_prover path_triangle

/-- The cheating prover that always names the second graph. -/
private noncomputable def alwaysSecond : Prover Unit := Prover.const [true]

private theorem guessProb_alwaysSecond (m : List Bool) (b : Bool) :
    alwaysSecond.guessProb alwaysSecond.init m b = if b = true then 1 else 0 := by
  cases b <;> simp [Prover.guessProb, alwaysSecond, Prover.const, StateT.run]

/-- The cheating prover passes every guessing round with probability exactly one half. -/
private theorem acceptProb_guessingRound_alwaysSecond (message : Bool → ProbComp (List Bool)) :
    acceptProb (guessingRound message) alwaysSecond = 1 / 2 := by
  simp only [acceptProb_guessingRound, guessProb_alwaysSecond, Bool.false_eq_true, ↓reduceIte,
    mul_zero, tsum_zero, zero_add, mul_one, PMF.tsum_coe]

-- Naming the second graph regardless of the message wins exactly half of the rounds, for every
-- pair of graphs: the bound `1 / 2 + 1 / 32` of one round is nearly attained.
theorem acceptProb_round_alwaysSecond (x : Graph × Graph) :
    acceptProb (GraphNonIsomorphism.round x) alwaysSecond = 1 / 2 :=
  acceptProb_guessingRound_alwaysSecond _

-- On the isomorphic pair `(path, path')` every prover, the cheating one included, passes both
-- rounds with probability at most `(17 / 32) ^ 2 < 1 / 3`.
example : acceptProb (GraphNonIsomorphism.verifier (path, path')) alwaysSecond ≤
    (17 / 32) ^ 2 :=
  GraphNonIsomorphism.acceptProb_verifier_le (by rw [mem_GraphIsomorphism_iff]; decide) _

-- The verifier exchanges polynomially many messages of polynomial length.
example : ∃ verifier : Graph × Graph → WordOracleComp Unit Bool,
    IsOraclePPTOn (encPair encGraph encGraph) encBool verifier ∧
      IsInteractiveProof verifier GraphNonIsomorphism (2 / 3) (1 / 3) ∧ ∃ c d : ℕ, ∀ x,
        (verifier x).IsQueryBounded (c * ((encPair encGraph encGraph x).length + 1) ^ d) ∧
          (verifier x).QueriesSatisfy fun message =>
            message.2.length ≤ c * ((encPair encGraph encGraph x).length + 1) ^ d :=
  exists_queryBounds_of_mem_IP GraphNonIsomorphism.mem_IP

/-! ### Class inclusions and repetition -/

-- The one-message verifier accepts the empty certificate of a trivial verifier with certificates
-- of length zero.
example (a : List Bool) :
    acceptProb (npVerifier encBits 0 (fun _ => true) a) (Prover.const []) = 1 := by
  rw [acceptProb_npVerifier_const (by simp)]
  rfl

example : (∅ : Set (List Bool)) ∈ IP encBits :=
  BPP_subset_IP _ ⟨0, fun _ => false, .const false, fun _ => ⟨fun h => h.elim, fun _ => by
    simp only [BoundedErrorAt, Polynomial.eval_zero, pow_zero, mul_one]
    exact le_trans (by norm_num : 2 ≤ 3 * 1)
      (Nat.mul_le_mul_left 3 (Finset.card_pos.2
        ⟨fun _ => false, Finset.mem_filter.2 ⟨Finset.mem_univ _, trivial⟩⟩))⟩⟩

-- A guessing round whose message does not depend on the secret bit is passed with probability at
-- most one half by every prover, and the cheating prover attains it.
example (P : Prover Unit) :
    acceptProb (guessingRound fun _ => pure [true]) P ≤ 1 / 2 ∧
    acceptProb (guessingRound fun _ => pure [true]) alwaysSecond = 1 / 2 :=
  ⟨acceptProb_guessingRound_le_half rfl P, acceptProb_guessingRound_alwaysSecond _⟩

-- Zero repetitions accept every prover.
example (round : WordOracleComp Unit Bool) (P : Prover Unit) :
    acceptProb (sequentialRepeat 0 round) P = 1 := by
  simp [sequentialRepeat, acceptProb]

/-! ### `IP ⊆ PSPACE` -/

-- Graph non-isomorphism and graph isomorphism are in polynomial space through interactive proofs.
example :
    GraphNonIsomorphism ∈ PSPACE (encPair encGraph encGraph) ∧
    GraphIsomorphism ∈ PSPACE (encPair encGraph encGraph) :=
  ⟨IP_subset_PSPACE _ GraphNonIsomorphism.mem_IP,
   IP_subset_PSPACE _ (NP_subset_IP _ GraphIsomorphism.mem_NP)⟩

example : (∅ : Set (List Bool)) ∈ PSPACE encBits :=
  IP_subset_PSPACE _ (BPP_subset_IP _ ⟨0, fun _ => false, .const false,
    fun _ => ⟨fun h => h.elim, fun _ => by
      simp only [BoundedErrorAt, Polynomial.eval_zero, pow_zero, mul_one]
      exact le_trans (by norm_num : 2 ≤ 3 * 1)
        (Nat.mul_le_mul_left 3 (Finset.card_pos.2
          ⟨fun _ => false, Finset.mem_filter.2 ⟨Finset.mem_univ _, trivial⟩⟩))⟩⟩)

-- The binary counter counts, least significant bit first, and wraps around.
example : BitString.increment [true, true, false] = [false, false, true] ∧
    BitString.increment^[5] [false, false, false] = [true, false, true] ∧
    BitString.increment [true, true] = [false, false] ∧
    BitString.lsbValue [true, false, true] = 5 :=
  ⟨rfl, rfl, rfl, rfl⟩

-- Polynomial space is closed under composition and contains polynomial time, through `fun_prop`.
example : ComputableInPolySpace (fun w => BitString.increment (BitString.increment w))
    encBits encBits :=
  have h : ComputableInPolySpace BitString.increment encBits encBits := .of_polyTime (by fun_prop)
  h.comp h

-- A Boolean function computable within polynomial space decides a problem in `PSPACE`.
example : {w : List Bool | w.headD false = true} ∈ PSPACE encBits :=
  mem_PSPACE_of_computableInPolySpace (f := fun w => w.headD false)
    (.of_polyTime (ComputableInPolyTime.headD false)) fun _ => Iff.rfl

-- The seven codes of length `3` decode to the seven words of length at most `2`, each once.
example : (List.range (Interaction.codeCount 2)).map (fun i =>
    Interaction.decodeWord (BitString.increment^[i] (Interaction.firstCode 2))) =
      [[false, false], [false], [true, false], [], [false, true], [true], [true, true]] := by
  decide

example : Interaction.encodeWord 3 [true] = [false, false, true, true] := rfl

-- A game tree with two messages and two replies, of depth one: the root has leaf value `1`, and
-- the child reached by the message `i` and the reply `j` has leaf value `2 * i + j`, so the value
-- is `1 + max 0 1 + max 2 3 = 5` (or `4` when capped at `4`). The evaluator returns `5` after
-- `GameTree.time 2 1 = 9` steps.
private def treeLeaf : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (i, j) :: _ => 2 * i + j

example : GameTree.value 2 100 0 Nat.succ treeLeaf 1 [] = 5 ∧
    GameTree.value 2 4 0 Nat.succ treeLeaf 1 [] = 4 := by decide

example : (GameTree.step 1 100 0 Nat.succ (fun i => decide (i = 1)) treeLeaf)^[GameTree.time 2 1]
    ([], none) = ([], some 5) := by decide

example : (GameTree.step 1 100 0 Nat.succ (fun i => decide (i = 1)) treeLeaf)^[GameTree.time 2 1]
    ([], none) = ([], some 5) := by
  rw [GameTree.iterate_step_eval (by norm_num) (fun i hi => by interval_cases i <;> rfl) le_rfl]
  decide

-- A verifier with two coin values that accepts without sending a message is a bounded family with
-- no rounds; its value is the number of coin values, and no prover can do better.
private def acceptAll : Fin 2 → WordQueryComp Unit Bool := fun _ => pure true

private theorem isBounded_acceptAll : Interaction.IsBounded acceptAll 0 0 where
  rounds r h m hm := by cases h <;> simp [Interaction.outcome, acceptAll] at hm
  message r h m hm := by cases h <;> simp [Interaction.outcome, acceptAll] at hm
  reply r h m y e := by cases h <;> rfl

example (P : Prover Unit) :
    Interaction.value acceptAll 0 0 [] = 2 ∧
      ∑ r, Interaction.acceptFrom P P.init (some (acceptAll r)) ≤ 2 := by
  have hval : Interaction.value acceptAll 0 0 [] = 2 := by
    have h (r : Fin 2) : Interaction.outcome (acceptAll r) [] = .done true := rfl
    simp [Interaction.value, Interaction.accepted, h]
  refine ⟨hval, (Interaction.sum_acceptFrom_le_value isBounded_acceptAll P).trans_eq ?_⟩
  exact_mod_cast hval

end ComplexityTests.InteractiveProofs

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Computability.Complexity.Classes.Oracle.Closure
import Complexity.Computability.Complexity.Classes.Sparse.Kadin

/-! # Kadin's theorem: census, binary search and the collapse -/

namespace ComplexityTests.SparseKadin

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- The words consisting only of `true`s, a sparse language. -/
private def unary : Set (List Bool) := {w | ∀ b ∈ w, b = true}

-- A list attaining the census of the short members lists them all: the three all-`true` words of
-- length at most `2`, in any order, agree with `unary` on every word of length at most `2`.
example : [false] ∉ [[true, true], [], [true]] := by
  have := mem_iff_of_length_eq_length_shortMembers (S := unary) (n := 2)
    (ℓ := [[true, true], [], [true]]) (by decide)
    (fun s hs => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl <;> simp [unary])
    (by
      have hset : ∀ w : List Bool, w ∈ shortMembers unary 2 ↔
          w ∈ ({[], [true], [true, true]} : Finset (List Bool)) := by
        intro w
        simp only [mem_shortMembers, unary, Set.mem_ofPred_eq, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨hw, hlen⟩
          match w, hlen with
          | [], _ => simp
          | [a], _ => simp [hw a (by simp)]
          | [a, b], _ => simp [hw a (by simp), hw b (by simp)]
        · rintro (rfl | rfl | rfl) <;> simp
      rw [← List.toFinset_card_of_nodup (nodup_shortMembers unary 2),
        show (shortMembers unary 2).toFinset = {[], [true], [true, true]} from
          Finset.ext fun w => by rw [List.mem_toFinset, hset]]
      rfl) (s := [false]) (by simp)
  simp only [this, unary, Set.mem_ofPred_eq, List.mem_singleton, forall_eq]
  decide

-- Binary search finds the threshold `5` of `k ≤ 5` in `[0, 10]` with four rounds.
example : ((KadinCensus.searchStep fun k => decide (k ≤ 5))^[4] (0, 10)).1 = 5 :=
  KadinCensus.fst_iterate_searchStep (by norm_num) (by norm_num)

example : (KadinCensus.searchStep fun k => decide (k ≤ 5))^[4] (0, 10) = (5, 5) := by
  decide

-- The algorithm, run against the oracle of the words of length at most `3` with requests
-- `true ^ k`, finds the threshold `3` and accepts; it makes at most five requests.
open Classical in
example : OracleComp.interpret (m := Id) (languageOracle {w : List Bool | w.length ≤ 3})
    (KadinCensus.program (fun x : Unit × ℕ => List.replicate x.2 true)
      (fun x => List.replicate x.2 true) (fun _ => 10) (fun _ => 4) ()) = true := by
  have key : ((KadinCensus.searchStep fun k => decide (k ≤ 3))^[4] (0, 10)).1 = 3 :=
    KadinCensus.fst_iterate_searchStep (by norm_num) (by norm_num)
  rw [KadinCensus.interpret_program]
  simp only [Set.mem_ofPred_eq, List.length_replicate]
  convert key.le using 4
  exact decide_eq_true_iff

example (answer : Unit × List Bool → List Bool) :
    (OracleComp.queriesWith answer (KadinCensus.program (fun x : Unit × ℕ => List.replicate x.2 true)
      (fun x => List.replicate x.2 true) (fun _ => 10) (fun _ => 4) ())).length ≤ 5 :=
  KadinCensus.length_queriesWith_program_le answer _ _ _ _ ()

-- With the empty sparse set, the census is `0`: the request `(a, 0, false)` holds and
-- `(a, 1, false)` does not.
private theorem empty_mem_NP : (∅ : Set (List Bool)) ∈ NP encBits :=
  P_subset_NP ⟨fun _ => false, ComputableInPolyTime.const false, fun _ => by simp⟩

example (G : (List Bool × List Bool) × List (List Bool) → Bool) (a : List Bool) :
    (a, 0, false) ∈ KadinCensus.language ∅ encBits 1 1 G ∧
      (a, 1, false) ∉ KadinCensus.language ∅ encBits 1 1 G := by
  rw [KadinCensus.mem_language_false_iff, KadinCensus.mem_language_false_iff]
  have h0 : KadinCensus.census (∅ : Set (List Bool)) encBits 1 a = 0 := by
    simp [KadinCensus.census, List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]
  omega

-- The requests are in `NP`, for the sparse `NP` set `∅` and any polynomial-time `G`.
example : KadinCensus.language ∅ encBits 1 1
    (fun _ : (List Bool × List Bool) × List (List Bool) => false) ∈
      NP (encPair encBits (encPair encUnary encBool)) :=
  KadinCensus.language_mem_NP empty_mem_NP Set.finite_empty.mem_SPARSE
    (ComputableInPolyTime.const false)

-- The hypotheses of Kadin's theorem hold if `SAT ∈ P`, with the empty sparse set.
example (h : SAT ∈ P encCNF) : PH encBits ⊆ PNPLog encBits :=
  PH_subset_PNPLog_of_sparse Set.finite_empty.mem_SPARSE empty_mem_NP
    (P_subset_PWithOracle ∅ encCNF h) encBits

end ComplexityTests.SparseKadin

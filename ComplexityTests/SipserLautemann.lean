/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.PH.SipserLautemann
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain

/-!
# Tests for the Sipser–Lautemann theorem

Non-vacuity, boundary and runtime-automation checks for
`Complexity.Computability.Complexity.Classes.PH.SipserLautemann` and the complement closure of
`Cslib.Complexity.BPP`.
-/

namespace Cslib.Complexity.Tests.SipserLautemann

open Cslib.Complexity Cslib.Complexity.SipserLautemann Turing.MultiTapeTM

/-! ### Parameter and boundary sanity checks -/

example : halfRuns 0 = 48 ∧ runs 0 = 96 ∧ shifts 0 = 96 ∧ seedLen 0 = 0 ∧ witnessLen 0 = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

example : halfRuns 1 = 54 ∧ runs 1 = 108 ∧ shifts 1 = 108 ∧ seedLen 1 = 108 ∧
    witnessLen 1 = 11664 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- Zero-length seed and malformed/short certificate strings evaluate cleanly: missing bits read
-- as `false` and extra bits are ignored.
example : trialSeed 0 [] 0 0 = [] ∧ trialSeed 2 [] 0 0 = [false, false] ∧
    trialSeed 2 [true] 0 0 = [true, false] :=
  ⟨rfl, rfl, rfl⟩

-- Strict majority tie convention: exactly `halfRuns m` accepting runs is a rejection;
-- `halfRuns m + 1` accepting runs is an acceptance.
example : ¬ majorityAccepts (m := 1) (fun s => s 0) (fun j _ => decide (j.1 < halfRuns 1)) := by
  simp only [majorityAccepts, not_lt]
  have hsub : (Finset.univ.filter fun j : Fin (runs 1) => decide (j.1 < halfRuns 1) = true) =
      Finset.univ.filter fun j : Fin (runs 1) => j.1 < halfRuns 1 := by
    ext j
    simp
  rw [hsub]
  decide

example : majorityAccepts (m := 1) (fun s => s 0) (fun j _ => decide (j.1 ≤ halfRuns 1)) := by
  simp only [majorityAccepts]
  decide

-- Zero-length seed completeness and soundness on `m = 0`.
example : ∃ tests : Fin (shifts 0) → Seed 0, ∀ r : Seed 0, ∃ i,
    majorityAccepts (fun _ => true) (r + tests i) :=
  exists_shifts_majorityAccepts (by decide)

example (tests : Fin (shifts 0) → Seed 0) :
    ∃ r : Seed 0, ∀ i, ¬ majorityAccepts (fun _ => false) (r + tests i) :=
  exists_seed_not_majorityAccepts (by decide) tests

/-! ### Non-vacuous randomized BPP decision problem with two-sided error 1/4 -/

/-- A randomized verifier for `{x : List Bool | x.headD false = true}` that reads 2 random bits
and flips the true answer when both random bits are `true` (error probability `1 / 4 ≤ 1 / 3`). -/
def noisyHeadVerifier (p : List Bool × List Bool) : Bool :=
  p.1.headD false ^^ (p.2.getD 0 false && p.2.getD 1 false)

@[fun_prop]
theorem noisyHeadVerifier_polyTime :
    ComputableTidilyInPolyTime noisyHeadVerifier (encPair encBits encBits) encBool := by
  unfold noisyHeadVerifier
  fun_prop

theorem noisyHeadVerifier_decides :
    DecidesWithBoundedError encBits (Polynomial.C 2) noisyHeadVerifier
      {x : List Bool | x.headD false = true} := by
  intro a
  dsimp only [DecidesWithBoundedError, PromiseProblem.SolvesWithBoundedError, BoundedErrorAt]
  generalize hm : (Polynomial.C 2).eval (encBits a).length = m
  have hm2 : m = 2 := by rw [← hm, Polynomial.eval_C]
  subst hm2
  change (a.headD false = true → _) ∧ (¬ a.headD false = true → _)
  cases h : a.headD false
  · refine ⟨by simp, fun _ => ?_⟩
    have heq : (Finset.univ.filter fun r : Fin 2 → Bool =>
        noisyHeadVerifier (a, List.ofFn r) = false) =
        Finset.univ.filter fun r : Fin 2 → Bool => (r 0 && r 1) = false := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, noisyHeadVerifier, h]
      revert r
      decide
    rw [heq]
    decide
  · refine ⟨fun _ => ?_, by simp⟩
    have heq : (Finset.univ.filter fun r : Fin 2 → Bool =>
        noisyHeadVerifier (a, List.ofFn r) = true) =
        Finset.univ.filter fun r : Fin 2 → Bool => (r 0 && r 1) = false := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, noisyHeadVerifier, h]
      revert r
      decide
    rw [heq]
    decide

theorem noisyHead_mem_BPP : {x : List Bool | x.headD false = true} ∈ BPP encBits :=
  ⟨Polynomial.C 2, noisyHeadVerifier, .of_tidy noisyHeadVerifier_polyTime,
    noisyHeadVerifier_decides⟩

theorem noisyHead_mem_SigmaP_two : {x : List Bool | x.headD false = true} ∈ SigmaP 2 encBits :=
  BPP_subset_SigmaP_two noisyHead_mem_BPP

theorem noisyHead_mem_PiP_two : {x : List Bool | x.headD false = true} ∈ PiP 2 encBits :=
  BPP_subset_PiP_two noisyHead_mem_BPP

theorem noisyHead_mem_PH : {x : List Bool | x.headD false = true} ∈ PH encBits :=
  BPP_subset_PH noisyHead_mem_BPP

attribute [local fun_prop] ComputableInPolySpace.tidy in
attribute [local fun_prop] ComputableInPolyTime.tidy in
-- Direct `fun_prop` synthesis on the Sipser-Lautemann matrix verifier for `noisyHeadVerifier`.
example : ComputableInPolyTime
    (verifier encBits (Polynomial.C 2) noisyHeadVerifier)
    (encPair encBits encBits) encBool := by
  fun_prop

-- Short/malformed certificate behavior on the concrete matrix verifier:
-- when `w = []`, every trial reads all-`false` shifted seeds, so `noisyHeadVerifier` returns
-- `a.headD false` on every trial.
example : verifier encBits (Polynomial.C 2) noisyHeadVerifier ([], []) = false := by
  have hts (i j : ℕ) : trialSeed 2 [] i j = [false, false] := by
    simp [trialSeed, Cslib.BitString.listRow]
  have hnh : noisyHeadVerifier ([], [false, false]) = false := rfl
  simp [verifier, shiftAccepts, hts, hnh]

example : verifier encBits (Polynomial.C 2) noisyHeadVerifier ([true], []) = true := by
  have hts (i j : ℕ) : trialSeed 2 [] i j = [false, false] := by
    simp [trialSeed, Cslib.BitString.listRow]
  have hnh : noisyHeadVerifier ([true], [false, false]) = true := rfl
  simp only [verifier, shiftAccepts, Polynomial.eval_C, hts, hnh]
  simp only [shifts, runs, halfRuns, List.countP_true, List.length_range, List.any_eq_true,
    List.mem_range]
  exact ⟨0, by decide, by decide⟩

/-- Plain `fun_prop` uses the plain matrix-verifier certificate from a plain hypothesis. -/
example {α : Type} {enc : α ↪ List Bool} {p : Polynomial ℕ} {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    ComputableInPolyTime (fun x => !verifier enc p V x) (encPair enc encBits) encBool := by
  fun_prop

end Cslib.Complexity.Tests.SipserLautemann

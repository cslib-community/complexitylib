/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature.View

@[expose] public section

open Cslib Cslib.Probability Cslib.Probability.PMF
open Cslib.Crypto.Protocols.SigmaProtocol
open scoped ENNReal _root_.Matrix

namespace LyubashevskyViewTests

def A : Matrix (Fin 1) (Fin 2) (ZMod 17) := Matrix.of fun _ j => if j = 0 then 1 else 0

def secret : Matrix (Fin 2) (Fin 1) ℤ := Matrix.of fun i _ => if i = 1 then 1 else 0

def key : Matrix (Fin 1) (Fin 2) (ZMod 17) × Matrix (Fin 1) (Fin 1) (ZMod 17) := (A, 0)

noncomputable def P := lyubashevsky 1 2 1 17 3 1

def challenge (w : Fin 1 → ZMod 17) : BitString 1 := fun _ => decide (w 0 = 0)

theorem zero_valid : lyubashevskyRelation 1 0 key := by
  constructor
  · simp [key]
  · intro i j
    norm_num

theorem secret_valid : lyubashevskyRelation 1 secret key := by
  constructor
  · ext i j
    simp [key, A, secret, Matrix.mul_apply]
  · intro i j
    simp only [secret, Matrix.of_apply]
    split_ifs <;> norm_num

example : secret ≠ 0 := by
  intro h
  have hi := congrArg (fun S : Matrix (Fin 2) (Fin 1) ℤ => S 1 0) h
  norm_num [secret] at hi

example : challenge 0 0 = true ∧ challenge 1 0 = false := by decide

/-- The two witnesses yield the same law even when the commitment chooses the challenge. -/
example :
    ((P.commit 0 key).map fun ts => (ts.1, P.respond 0 key ts.2 (challenge ts.1))) =
    (P.commit secret key).map fun ts => (ts.1, P.respond secret key ts.2 (challenge ts.1)) :=
  lyubashevsky_attempt_view_eq (by decide) (by decide) zero_valid secret_valid challenge

/-- A nonzero commitment is retained on an aborted attempt with positive probability. -/
example : 0 < ((P.commit 0 key).map fun ts =>
    (ts.1, P.respond 0 key ts.2 (challenge ts.1))) (1, none) := by
  apply (PMF.apply_pos_iff _ _).mpr
  simp only [P, lyubashevsky, PMF.map_comp, Function.comp_def]
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨![1, 3], (mem_support_uniformOfFinset_iff _ _).mpr ?_, ?_⟩
  · rw [mem_intBox]
    intro i
    fin_cases i <;> norm_num
  · norm_num [key, A, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mem_intBox,
      Fin.forall_fin_two]
    funext i
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Successful responses also have positive probability in the same fixture. -/
example : 0 < ((P.commit 0 key).map fun ts =>
    (ts.1, P.respond 0 key ts.2 (challenge ts.1))) (0, some 0) := by
  apply (PMF.apply_pos_iff _ _).mpr
  simp only [P, lyubashevsky, PMF.map_comp, Function.comp_def]
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨0, (mem_support_uniformOfFinset_iff _ _).mpr (zero_mem_intBox 3), ?_⟩
  norm_num
  funext i
  simp [Matrix.mulVec, dotProduct]

example :
    fsAbortSignBounded P (fun pair : Unit × (Fin 1 → ZMod 17) => challenge pair.2) 3 0 key () =
      fsAbortSignBounded P (fun pair : Unit × (Fin 1 → ZMod 17) => challenge pair.2)
        3 secret key () :=
  lyubashevskySignBounded_witness_eq (by decide) (by decide) zero_valid secret_valid _ () 3

end LyubashevskyViewTests

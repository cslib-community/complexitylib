/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.PH.Collapse
import CslibFrontier.Computability.Complexity.Classes.PH.OracleNP

/-! # `P^NP ⊆ Σ₂ ∩ Π₂`: transcript certificates and the projection lemma -/

namespace CslibFrontierTests.PHOracleNP

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

variable {k : ℕ} {Control Operation : Type} [DecidableEq Operation]
  (machine : MultiTapePTM k Bool Control Operation)

-- The empty transcript is the canonical transcript of length `0`.
example (g : List Bool → Bool) (input : List Bool) : [] = machine.oracleReplies g 0 input :=
  (machine.eq_oracleReplies_iff g input []).mpr fun _ hi => absurd hi (Nat.not_lt_zero _)

-- The empty transcript is certified for every oracle.
example (A : Set (List Bool)) (a : List Bool) :
    (a, []) ∈ oracleTranscriptYes machine encBits A ∩ oracleTranscriptNo machine encBits A :=
  ⟨mem_oracleTranscriptYes.mpr fun _ hi => absurd hi (Nat.not_lt_zero _),
    mem_oracleTranscriptNo.mpr fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

-- A `true` reply is never certified for the empty oracle, so such a transcript is not canonical.
example (a : List Bool) : (a, [true]) ∉ oracleTranscriptYes machine encBits ∅ := fun h =>
  (mem_oracleTranscriptYes.mp h 0 (by simp) rfl).2

example (a : List Bool) :
    [true] ≠ machine.oracleReplies (fun q => decide (q ∈ (∅ : Set (List Bool)))) 1 a := by
  intro h
  have hmem := mem_oracleTranscriptYes_inter_oracleTranscriptNo (machine := machine)
    (enc := encBits) (A := ∅) (x := (a, [true]))
  exact (mem_oracleTranscriptYes.mp (hmem.mpr (by convert h; rfl)).1 0 (by simp) rfl).2

-- `Σₖ` is closed under polynomially bounded projection, here at level `1`.
example {B : Set (List Bool × List Bool)} (hB : B ∈ SigmaP 1 (encPair encBits encBits)) :
    {a | ∃ w : List Bool, w.length = (Polynomial.X : Polynomial ℕ).eval (encBits a).length ∧
      (a, w) ∈ B} ∈ SigmaP 1 encBits :=
  mem_SigmaP_of_exists le_rfl hB _

-- An `NP` problem and its complement both lie in `Σ₂ ∩ Π₂`, through `P^A` with `A` itself.
example {A : Set (List Bool)} (hA : A ∈ NP encBits) : A ∈ SigmaP 2 encBits ∩ PiP 2 encBits :=
  PWithOracle_subset_SigmaP_two_inter_PiP_two hA (mem_PWithOracle_self A)

example {A : Set (List Bool)} (hA : A ∈ NP encBits) : Aᶜ ∈ SigmaP 2 encBits :=
  PWithOracle_subset_SigmaP_two hA (compl_mem_PWithOracle (mem_PWithOracle_self A))

-- `P^{NP[O(log n)]}` is inside the polynomial hierarchy, for any instance encoding.
example {α : Type} (enc : α ↪ List Bool) : PNPLog enc ⊆ PH enc :=
  PNPLog_subset_PH enc

end CslibFrontierTests.PHOracleNP

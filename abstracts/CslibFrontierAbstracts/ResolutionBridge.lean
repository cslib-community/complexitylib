/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import CslibFrontierAbstracts.Check
import CslibFrontier.Logics.Propositional.Resolution.Pigeonhole

/-!
# Bridge for Haken's resolution formal abstract

The elementary recursive proof predicate is equivalent to the library's inductive list proof,
with no weakening rule and with input lines counted. The pigeonhole formula is definitionally
unchanged. The bound concerns proof size, not solver runtime.
-/

namespace CslibFrontierTests.Abstracts.ResolutionBridge

/-- A resolution proof, listed with the last line first. -/
def IsProof {V : Type} [DecidableEq V] (φ : List (List (V × Bool))) :
    List (List (V × Bool)) → Prop
  | [] => True
  | c :: ls => IsProof φ ls ∧ (c ∈ φ ∨ ∃ v c₁ c₂,
      c₁ ∈ ls ∧ c₂ ∈ ls ∧ (v, true) ∈ c₁ ∧ (v, false) ∈ c₂ ∧
      c = c₁.filter (· ≠ (v, true)) ++ c₂.filter (· ≠ (v, false)))

theorem isProof_iff {V : Type} [DecidableEq V] (φ ls : List (List (V × Bool))) :
    IsProof φ ls ↔ Cslib.Logic.PL.CNF.IsProof φ ls := by
  induction ls with
  | nil => exact ⟨fun _ => .nil, fun _ => trivial⟩
  | cons c ls ih =>
    constructor
    · rintro ⟨h, hc | ⟨v, c₁, c₂, h₁, h₂, hv₁, hv₂, rfl⟩⟩
      · exact (ih.mp h).mem hc
      · exact (ih.mp h).resolvent v h₁ h₂ hv₁ hv₂
    · intro h
      cases h with
      | mem h hc => exact ⟨ih.mpr h, Or.inl hc⟩
      | resolvent v h h₁ h₂ hv₁ hv₂ =>
        exact ⟨ih.mpr h, Or.inr ⟨v, _, _, h₁, h₂, hv₁, hv₂, rfl⟩⟩

/-- Refutability within a number of lines. -/
def RefutableInSize {V : Type} [DecidableEq V] (φ : List (List (V × Bool))) (s : ℕ) : Prop :=
  ∃ ls, IsProof φ ls ∧ [] ∈ ls ∧ ls.length ≤ s

theorem refutableInSize_iff {V : Type} [DecidableEq V] (φ : List (List (V × Bool))) (s : ℕ) :
    RefutableInSize φ s ↔ Cslib.Logic.PL.CNF.RefutableInSize φ s := by
  simp only [RefutableInSize, Cslib.Logic.PL.CNF.RefutableInSize, isProof_iff]

/-- Satisfiability stated using ordinary quantifiers. -/
def Satisfiable {V : Type} (φ : List (List (V × Bool))) : Prop :=
  ∃ σ : V → Bool, ∀ c ∈ φ, ∃ l ∈ c, σ l.1 = l.2

theorem satisfiable_iff {V : Type} (φ : List (List (V × Bool))) :
    Satisfiable φ ↔ Cslib.Logic.PL.CNF.Satisfiable φ := by
  simp only [Satisfiable, Cslib.Logic.PL.CNF.Satisfiable,
    Cslib.Logic.PL.CNF.eval_eq_true_iff, Cslib.Logic.PL.Clause.eval_eq_true_iff]

/-- Every pigeon chooses a hole; distinct pigeons cannot choose the same hole. -/
def pigeonhole (m n : ℕ) : List (List ((Fin m × Fin n) × Bool)) :=
  (List.finRange m).map (fun i => (List.finRange n).map fun j => ((i, j), true)) ++
    (List.finRange n).flatMap fun j => (List.finRange m).flatMap fun i =>
      ((List.finRange m).filter (i < ·)).map fun i' => [((i, j), false), ((i', j), false)]

theorem pigeonhole_satisfiable (m n : ℕ) : Satisfiable (pigeonhole m n) ↔ m ≤ n :=
  (satisfiable_iff _).trans Cslib.Logic.PL.CNF.satisfiable_pigeonhole_iff

/-- Haken's lower bound, via the Beame–Pitassi bottleneck argument. -/
theorem haken {n s : ℕ} (hs : RefutableInSize (pigeonhole (n + 1) n) s) :
    2 ^ (n / 24) ≤ s :=
  Cslib.Logic.PL.CNF.two_pow_le_of_refutableInSize_pigeonhole
    ((refutableInSize_iff _ s).mp hs)

/-- Equational presentation of the recursive proof predicate, for a fresh abstract definition. -/
def ProofRules {V : Type} [DecidableEq V]
    (P : List (List (V × Bool)) → List (List (V × Bool)) → Prop) : Prop :=
  (∀ φ, P φ [] ↔ True) ∧ ∀ φ c ls, P φ (c :: ls) ↔
    P φ ls ∧ (c ∈ φ ∨ ∃ v c₁ c₂,
      c₁ ∈ ls ∧ c₂ ∈ ls ∧ (v, true) ∈ c₁ ∧ (v, false) ∈ c₂ ∧
      c = c₁.filter (· ≠ (v, true)) ++ c₂.filter (· ≠ (v, false)))

theorem proof_iff_of_rules {V : Type} [DecidableEq V]
    (P : List (List (V × Bool)) → List (List (V × Bool)) → Prop) (hP : ProofRules P)
    (φ ls : List (List (V × Bool))) : P φ ls ↔ IsProof φ ls := by
  induction ls with
  | nil => exact hP.1 φ
  | cons c ls ih => rw [hP.2 φ c ls, IsProof, ih]

/-- Transfer Haken's bound through the elementary recursive equations. -/
theorem haken_of_rules {n s : ℕ}
    (P : List (List ((Fin (n + 1) × Fin n) × Bool)) →
      List (List ((Fin (n + 1) × Fin n) × Bool)) → Prop) (hP : ProofRules P)
    (hs : ∃ ls, P (pigeonhole (n + 1) n) ls ∧ [] ∈ ls ∧ ls.length ≤ s) :
    2 ^ (n / 24) ≤ s := by
  apply haken
  simpa only [RefutableInSize, proof_iff_of_rules P hP] using hs

-- The proof predicate is inhabited at the input-empty-clause and zero-hole boundaries.
example : RefutableInSize ([[]] : List (List (ℕ × Bool))) 1 :=
  ⟨[[]], ⟨trivial, Or.inl (by simp)⟩, by simp, by decide⟩

example : RefutableInSize (pigeonhole 1 0) 1 := by
  change RefutableInSize ([[]] : List (List ((Fin 1 × Fin 0) × Bool))) 1
  exact ⟨[[]], ⟨trivial, Or.inl (by simp)⟩, by simp, by decide⟩

end CslibFrontierTests.Abstracts.ResolutionBridge

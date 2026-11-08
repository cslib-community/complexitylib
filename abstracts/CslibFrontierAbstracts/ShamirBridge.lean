/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import CslibFrontierAbstracts.TQBFBridge
import CslibFrontier.Computability.Complexity.Classes.IP.Shamir

/-! # Transfer of Shamir's theorem with full native oracle and prover quantifiers -/

namespace CslibFrontierTests.Abstracts.ShamirBridge

/-- A Boolean is encoded by a single bit. -/
def encBool : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; injection h⟩

/-- Word-query programs with fresh private random bits. This foundational program type is an
explicit trusted model boundary, not a definition of an efficiency or complexity class. -/
abbrev InteractiveProgram (β : Type) :=
  Cslib.ProbOracleComp (fun _ : Unit × List Bool => List Bool) β

/-- One fixed finite fair-coin machine and one polynomial clock realize the entire joint law
of the program's encoded result and the oracle's final state, against every stateful oracle.
The clock charges constructing requests and reading replies; oracle computation is external. -/
def StrictOraclePPT {α β : Type} (enc : α ↪ List Bool) (out : β ↪ List Bool)
    (program : α → InteractiveProgram β) : Prop :=
  ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : Turing.MultiTapePTM k Bool Control Unit) (c d : ℕ),
    ∀ a (State : Type)
      (oracle : Unit × List Bool → StateT State PMF (List Bool)) s,
      Cslib.ProbOracleComp.runWith oracle (out <$> program a) s =
        Cslib.ProbOracleComp.runWith oracle
          (machine.runOracle (c * ((enc a).length + 1) ^ d) (enc a)) s

/-- Acceptance probability against a prover with arbitrary private state and probabilistic
responses. The response function sees the message and its own state, not the verifier's coins. -/
noncomputable def acceptProbability (program : InteractiveProgram Bool)
    (State : Type)
    (respond : Unit × List Bool → StateT State PMF (List Bool)) (initial : State) : ENNReal :=
  (Cslib.ProbOracleComp.runWith respond program initial).map Prod.fst true

/-- Private-coin interactive proofs: strict polynomial verifier, completeness at least 2/3
for some unbounded prover on each member, soundness at most 1/3 against every unbounded stateful
randomized prover on every nonmember. The efficiency clock is uniform over all those provers. -/
def IP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ verifier : α → InteractiveProgram Bool, StrictOraclePPT enc encBool verifier ∧
    (∀ a ∈ A, ∃ (State : Type) (initial : State)
      (respond : Unit × List Bool → StateT State PMF (List Bool)),
      (2 / 3 : ENNReal) ≤ acceptProbability (verifier a) State respond initial) ∧
    ∀ a ∉ A, ∀ (State : Type) (initial : State)
      (respond : Unit × List Bool → StateT State PMF (List Bool)),
      acceptProbability (verifier a) State respond initial ≤ (1 / 3 : ENNReal)}

/-- Total deterministic polynomial-space decision, using plain upstream Turing machines.
The input is read-only, output write-only and the time bound is unrestricted. -/
def PSPACE {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (f : α → Bool) (t : α → ℕ) (s : ℕ → ℕ), Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpace f enc encBool t (fun a => s (enc a).length) ∧
    ∀ a, a ∈ A ↔ f a = true}

theorem strict_iff {α β : Type} {enc : α ↪ List Bool} {out : β ↪ List Bool}
    {program : α → InteractiveProgram β} :
    StrictOraclePPT enc out program ↔ Cslib.Probability.IsOraclePPTOn enc out program :=
  ⟨fun h => ⟨inferInstance, h⟩, fun h => h.2⟩

theorem ip_eq {α : Type} (enc : α ↪ List Bool) : IP enc = Cslib.Complexity.IP enc := by
  ext A
  constructor
  · rintro ⟨V, hV, hc, hs⟩
    refine ⟨V, strict_iff.mp hV, ⟨?_, ?_⟩⟩
    · intro a ha
      obtain ⟨State, initial, respond, h⟩ := hc a ha
      exact ⟨⟨State, initial, respond⟩, h⟩
    · intro a ha P
      exact hs a ha P.State P.init P.respond
  · rintro ⟨V, hV, hc, hs⟩
    refine ⟨V, strict_iff.mpr hV, ?_, ?_⟩
    · intro a ha
      obtain ⟨P, h⟩ := hc a ha
      exact ⟨P.State, P.init, P.respond, h⟩
    · intro a ha State initial respond
      exact hs a ha ⟨State, initial, respond⟩

theorem ip_eq_pspace {α : Type} (enc : α ↪ List Bool) : IP enc = PSPACE enc := by
  rw [ip_eq]
  exact (Cslib.Complexity.IP_eq_PSPACE enc).trans (Set.ext fun _ => TQBFBridge.mem_PSPACE_iff.symm)

end CslibFrontierTests.Abstracts.ShamirBridge

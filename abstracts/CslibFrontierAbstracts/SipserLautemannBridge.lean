/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

-- upstream: local-only (formal abstract proof bridge)

import CslibFrontierAbstracts.CookLevinBridge
import CslibFrontier.Computability.Complexity.Classes.PH.SipserLautemann

/-! # Proof bridge for the Sipser–Lautemann formal abstract

Transfer bounded-error computation and two polynomial quantifier blocks to native deterministic
Turing-machine bounds. The public abstract states all class semantics explicitly.
-/

namespace CslibFrontierAbstracts.SipserLautemannBridge

open CslibFrontierTests.Abstracts
open Turing.MultiTapeTM

/-- The framed encoding of an instance followed by a seed or quantified certificate. -/
def encInput : (List Bool × List Bool) ↪ List Bool :=
  CookLevinBridge.encPair (Function.Embedding.refl _) (Function.Embedding.refl _)

/-- A Boolean answer occupies one bit. -/
def encAnswer : Bool ↪ List Bool :=
  ⟨fun b => [b], by intro a b h; injection h⟩

/-- Total polynomial-time predicates, using plain upstream machine bounds. -/
def PolyTimePredicate (V : List Bool × List Bool → Bool) : Prop :=
  ∃ t s : ℕ → ℕ, Cslib.PolynomiallyBounded t ∧ Cslib.PolynomiallyBounded s ∧
    ComputableInTimeAndSpaceOfLength V encInput encAnswer t s

/-- Bounded-error computation with fair binary seeds. -/
def BPP : Set (Set (List Bool)) :=
  {A | ∃ (p : Polynomial ℕ) (V : List Bool × List Bool → Bool),
    PolyTimePredicate V ∧ ∀ x,
      (x ∈ A → 2 * 2 ^ p.eval x.length ≤
        3 * (Finset.univ.filter fun r : Fin (p.eval x.length) → Bool =>
          V (x, List.ofFn r) = true).card) ∧
      (x ∉ A → 2 * 2 ^ p.eval x.length ≤
        3 * (Finset.univ.filter fun r : Fin (p.eval x.length) → Bool =>
          V (x, List.ofFn r) = false).card)}

/-- A polynomial existential block followed by a polynomial universal block. -/
def SigmaTwo : Set (Set (List Bool)) :=
  {A | ∃ (p q : Polynomial ℕ) (V : List Bool × List Bool → Bool),
    PolyTimePredicate V ∧ ∀ x, x ∈ A ↔
      ∃ u : List Bool, u.length = p.eval x.length ∧
        ∀ v : List Bool, v.length = q.eval x.length → V (x, u ++ v) = true}

/-- A polynomial universal block followed by a polynomial existential block. -/
def PiTwo : Set (Set (List Bool)) :=
  {A | ∃ (p q : Polynomial ℕ) (V : List Bool × List Bool → Bool),
    PolyTimePredicate V ∧ ∀ x, x ∈ A ↔
      ∀ u : List Bool, u.length = p.eval x.length →
        ∃ v : List Bool, v.length = q.eval x.length ∧ V (x, u ++ v) = true}

private theorem polyTimePredicate_iff {V : List Bool × List Bool → Bool} :
    PolyTimePredicate V ↔ ComputableInPolyTime V
      (encPair encBits encBits) encBool :=
  Iff.rfl

private theorem mem_BPP_iff {A : Set (List Bool)} :
    A ∈ BPP ↔ A ∈ Cslib.Complexity.BPP encBits := by
  simp only [BPP, Set.mem_ofPred_eq, Cslib.Complexity.BPP,
    Cslib.Complexity.DecidesWithBoundedError, polyTimePredicate_iff]
  rfl

private theorem sigmaTwo_of_mem {A : Set (List Bool)}
    (hA : A ∈ Cslib.Complexity.SigmaP 2 encBits) : A ∈ SigmaTwo := by
  obtain ⟨ps, V, hlen, hV, hA⟩ := hA
  obtain ⟨p, q, rfl⟩ := List.length_eq_two.mp hlen
  refine ⟨p, q, V, polyTimePredicate_iff.mpr hV, ?_⟩
  simpa only [Cslib.Complexity.IsAlternatingVerifier, List.map_cons, List.map_nil,
    Cslib.Complexity.alternation_true_cons, Cslib.Complexity.alternation_false_cons,
    Cslib.Complexity.alternation_nil, List.append_nil, encBits,
    Function.Embedding.refl_apply] using hA

private theorem piTwo_of_mem {A : Set (List Bool)}
    (hA : A ∈ Cslib.Complexity.PiP 2 encBits) : A ∈ PiTwo := by
  obtain ⟨ps, V, hlen, hV, hA⟩ := hA
  obtain ⟨p, q, rfl⟩ := List.length_eq_two.mp hlen
  refine ⟨p, q, V, polyTimePredicate_iff.mpr hV, ?_⟩
  simpa only [Cslib.Complexity.IsAlternatingVerifier, List.map_cons, List.map_nil,
    Cslib.Complexity.alternation_true_cons, Cslib.Complexity.alternation_false_cons,
    Cslib.Complexity.alternation_nil, List.append_nil, encBits,
    Function.Embedding.refl_apply] using hA

/-- The Sipser–Gács–Lautemann containment, with both quantifier prefixes exposed. -/
theorem sipserLautemann : BPP ⊆ SigmaTwo ∩ PiTwo := by
  intro A hA
  have h := Cslib.Complexity.BPP_subset_SigmaP_two_inter_PiP_two (mem_BPP_iff.mp hA)
  exact ⟨sigmaTwo_of_mem h.1, piTwo_of_mem h.2⟩

end CslibFrontierAbstracts.SipserLautemannBridge

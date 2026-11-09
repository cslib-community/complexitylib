/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Equality
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Projection
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary
import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Polymorphism
import Mathlib.Tactic.FinCases

/-!
# Internally realized disequality for selfdual languages missing a constant

The minimum-arity descent of [DvorakKupec2015], Lemma 3, printed pp. 437–438, is applied
only to actual original-language gadgets with supplied checked boundaries. Every descent
step uses the proved projection or adjacent-equality constructor. Common complement rules
out the unary-pin outcome. The result supplies the original-language body and its full
numerical ordered certificate internally, without assuming arbitrary pp planar closure.

The semantic descent adapts `RelationMinor`'s existing constants argument by Erik Demaine;
the actual-body closure and certificate reconstruction are original. This static existence
result makes no uniform preprocessing, bare recognition or geometric-planarity assertion.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.RelationMinor

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}

/-- A common complement and failure of the false constant operation supply an actual
original-language disequality gadget with an internally realized ordered numerical boundary.
The alphabet need not be finite, and neither an enabling pin nor a pp/embedding oracle is
assumed. The failed constant itself supplies a nonempty original relation. -/
theorem exists_disequality_of_common_not
    (hnot : HasPolymorphism arity sem (fun a : Fin 1 → Bool => !(a 0)))
    (hfalse : ¬HasPolymorphism arity sem (fun _ : Fin 1 → Bool => false)) :
    ∃ g : PPGadget arity sem disequality, Nonempty (GadgetWitness g) := by
  classical
  rw [hasPolymorphism_const_iff] at hfalse
  simp only [not_forall] at hfalse
  obtain ⟨r, hr, hz⟩ := hfalse
  let Q (n : ℕ) := ∃ (S : Set (Fin n → Bool)) (g : PPGadget arity sem S),
    Nonempty (GadgetWitness g) ∧ S.Nonempty ∧ (0 : Fin n → Bool) ∉ S
  have hex : ∃ n, Q n := ⟨arity r, booleanRelation arity sem r, PPGadget.atom r,
    ⟨Witness.atom arity sem r⟩, hr, hz⟩
  obtain ⟨S, g, ⟨w⟩, ⟨a, ha⟩, hz⟩ := Nat.find_spec hex
  have hn : Nat.find hex ≠ 0 := by
    intro hn
    have he : a = 0 := by
      funext i
      exact (by have hi := i.isLt; omega : False).elim
    exact hz (he ▸ ha)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hn
  generalize hk : Nat.find hex = k at *
  have hfind : Nat.find hex = n + 1 := hk.trans hn
  clear hk
  subst k
  have hp (j : Fin (n + 1)) : (0 : Fin n → Bool) ∈ project S j := by
    by_contra hzero
    have hnew : Q n := ⟨project S j, g.project j, ⟨w.project j⟩,
      ⟨j.removeNth a, remove_mem_project ha j⟩, hzero⟩
    exact (Nat.find_min hex (by omega : n < Nat.find hex)) hnew
  have hu (j : Fin (n + 1)) : Pi.single j true ∈ S :=
    single_mem_of_zero_mem_project hz j (hp j)
  have hn2 : n + 1 ≤ 2 := by
    by_contra hh
    obtain ⟨k, he⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    subst n
    let i : Fin (k + 2 + 1) := ⟨2, by omega⟩
    have hunit : (Pi.single i true : Fin (k + 2 + 1) → Bool) ∈ S := hu i
    have heq : Fin.cons ((Fin.tail (Pi.single i true : Fin (k + 2 + 1) → Bool)) 0 ^^ false)
        (Fin.tail (Pi.single i true : Fin (k + 2 + 1) → Bool)) =
          (Pi.single i true : Fin (k + 2 + 1) → Bool) := by
      rw [Bool.xor_false]
      have he0 : (Fin.tail (Pi.single i true : Fin (k + 2 + 1) → Bool)) 0 =
          (Pi.single i true : Fin (k + 2 + 1) → Bool) 0 := by
        simp [i, Fin.tail, Fin.ext_iff]
      rw [he0, Fin.cons_self_tail]
    have hne : (adjacent S false).Nonempty :=
      ⟨Fin.tail (Pi.single i true : Fin (k + 2 + 1) → Bool), by
      change Fin.cons _ _ ∈ S
      rwa [heq]⟩
    have hzero : (0 : Fin (k + 2) → Bool) ∉ adjacent S false := by
      intro hm
      apply hz
      change Fin.cons (false ^^ false) (0 : Fin (k + 2) → Bool) ∈ S at hm
      rwa [show Fin.cons (false ^^ false) (0 : Fin (k + 2) → Bool) =
        (0 : Fin (k + 2 + 1) → Bool) from Fin.cons_self_tail (0 : Fin (k + 2 + 1) → Bool)] at hm
    have hnew : Q (k + 2) := ⟨adjacent S false, g.equalDrop, ⟨w.equalDrop⟩, hne, hzero⟩
    exact (Nat.find_min hex (by omega : k + 2 < Nat.find hex)) hnew
  have hself := g.isPolymorphism hnot
  have hn1 : n = 1 := by
    by_cases hn0 : n = 0
    · subst n
      have hh := hself (fun _ => Pi.single (0 : Fin 1) true) (fun _ => hu 0)
      have he : (fun i : Fin 1 => !((Pi.single (0 : Fin 1) true : Fin 1 → Bool) i)) = 0 := by
        decide
      exact (hz (he ▸ hh)).elim
    · omega
  subst n
  have hones : (fun _ : Fin 2 => true) ∉ S := by
    intro hm
    have hh := hself (fun _ => fun _ => true) (fun _ => hm)
    exact hz hh
  have hff : (![false, false] : Fin 2 → Bool) ∉ S := by
    simpa only [show (![false, false] : Fin 2 → Bool) = 0 by decide] using hz
  have htt : (![true, true] : Fin 2 → Bool) ∉ S := by
    simpa only [show (![true, true] : Fin 2 → Bool) = (fun _ => true) by decide] using hones
  have htf : (![true, false] : Fin 2 → Bool) ∈ S := by
    simpa only [show (Pi.single (0 : Fin 2) true) = ![true, false] by decide] using hu 0
  have hft : (![false, true] : Fin 2 → Bool) ∈ S := by
    simpa only [show (Pi.single (1 : Fin 2) true) = ![false, true] by decide] using hu 1
  have he : S = disequality := by
    ext x
    have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
    rw [hx]
    cases x 0 <;> cases x 1 <;> simp [disequality, hff, htt, htf, hft]
  subst S
  exact ⟨g, ⟨w⟩⟩

end Cslib.Complexity.CSP.OrderedBoundary

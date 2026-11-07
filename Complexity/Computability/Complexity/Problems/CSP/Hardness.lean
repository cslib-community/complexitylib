/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.SelfDualThreeSAT
public import Complexity.Computability.PolyTime.CSP.Gadget
public import Complexity.Logics.Polymorphism.BooleanClone

/-!
# The hard branch of Boolean Schaefer

For a fixed finite Boolean language lacking the six common Schaefer polymorphisms, the proved
Boolean clone classification implies preservation of every self-dual relation. Apply the proved
canonical primitive-positive construction to the eight reference-lifted ternary clause relations:
each is nonempty and separates its columns. Their native NP-complete problem then reduces by
certified fixed-gadget replacement to the language's exact-arity CSP.

This proves the hard branch of [Chen2006CSP], Theorem 3.20 (arXiv v1, p. 12), using Theorem 5.1
and Lemma 5.2 (pp. 17–18). The reference lift avoids a general equality-elimination theorem.
Empty/nullary language relations are permitted; input variable labels use binary encoding.

## Main results

* `Cslib.Complexity.CSPSAT.npComplete_of_not_hasSchaeferPolymorphism`: unconditional native
  NP-completeness outside the six cases, with no solver or classification hypothesis.
-/

public section

namespace Cslib.Complexity.CSPSAT

open Cslib.Logic Cslib.Logic.PL Turing.MultiTapeTM

variable {Rel : Type}

/-- **The hard branch of Boolean Schaefer's dichotomy**, for arbitrary fixed relation arities.
The language is fixed, so noncomputable finite gadget selection makes no uniform preprocessing
claim. The instance reduction has a native polynomial-time certificate under binary labels. -/
theorem npComplete_of_not_hasSchaeferPolymorphism [Finite Rel]
    (encRel : Rel ↪ List Bool) (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (h : ¬ CSP.HasSchaeferPolymorphism arity sem) :
    NPComplete (encCSP encRel encNat) (CSPSAT arity sem) := by
  classical
  have hrel : ∃ r : Rel, True := by
    by_contra he
    apply h
    left
    intro r
    exact (he ⟨r, trivial⟩).elim
  obtain ⟨r, _⟩ := hrel
  have hg (s : SelfDualThreeSAT.SignPattern) :
      Nonempty (CSP.PPGadget arity sem
        (CSP.booleanRelation SelfDualThreeSAT.arity SelfDualThreeSAT.sem s)) :=
    CSP.exists_ppGadget_of_polymorphisms arity sem _
      (SelfDualThreeSAT.relation_nonempty s) (SelfDualThreeSAT.separates_coordinates s)
      (fun _ hn _ hf => CSP.isPolymorphism_selfDual_of_not_hasSchaeferPolymorphism
        arity sem h hn hf _ (fun a ha => (SelfDualThreeSAT.relation_not_iff s a).mpr ha))
  let gadgets := fun s => Classical.choice (hg s)
  let B := Finset.univ.sup (fun s => (gadgets s).numAux)
  have hB (s) : (gadgets s).numAux ≤ B :=
    Finset.le_sup (f := fun s => (gadgets s).numAux) (Finset.mem_univ s)
  let reject := CSP.malformedReject arity r
  have hr : ¬ (CSP.WellFormed arity reject ∧ reject.Satisfiable sem) :=
    fun hf => CSP.not_wellFormed_malformedReject arity r hf.1
  have red : PolyTimeReducible SelfDualThreeSAT.enc (encCSP encRel encNat)
      SelfDualThreeSAT (CSPSAT arity sem) := by
    refine ⟨CSP.replaceGadgetsGuarded SelfDualThreeSAT.arity B
      (fun s => (gadgets s).template) reject, ?_, ?_⟩
    · exact CSP.computableInPolyTime_replaceGadgetsGuarded
        SelfDualThreeSAT.encSign encRel SelfDualThreeSAT.arity B _ reject
    · intro F
      exact (CSP.wellFormed_satisfiable_replaceGadgetsGuarded_iff gadgets B hB
        reject hr F).symm
  exact ⟨mem_NP encRel arity sem, SelfDualThreeSAT.npComplete.2.trans red⟩

end Cslib.Complexity.CSPSAT

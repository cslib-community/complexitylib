/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.SelfDualThreeSAT
public import CslibFrontier.Computability.PolyTime.CSP.Gadget.Size
public import CslibFrontier.Logics.Polymorphism.BooleanClone
import CslibFrontier.Computability.PolyTime.CSP.Gadget

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
* `Cslib.Complexity.CSPSAT.exists_linear_size_reduction_from_threeSAT`: a native reduction whose
  distinct output variables plus constraints are bounded by a fixed constant times the number
  of input clauses, hence also by that constant times input variables plus clauses.
-/

public section

namespace Cslib.Complexity.CSPSAT

open Cslib.Logic Cslib.Logic.PL Turing.MultiTapeTM

variable {Rel : Type}

/-- Fixed-gadget Schaefer hardness has linear combinatorial size. The constant depends on the
fixed language and gadgets, not the input or its binary variable names. -/
theorem exists_linear_size_reduction_from_selfDualThreeSAT [Finite Rel]
    (encRel : Rel ↪ List Bool) (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (h : ¬ CSP.HasSchaeferPolymorphism arity sem) :
    ∃ (f : CSP SelfDualThreeSAT.SignPattern ℕ → CSP Rel ℕ) (C : ℕ),
      ComputableInPolyTime f SelfDualThreeSAT.enc (encCSP encRel encNat) ∧
      (∀ F, F ∈ SelfDualThreeSAT ↔ f F ∈ CSPSAT arity sem) ∧
      (∀ F, (f F).numVars + (f F).length ≤ C * F.length) := by
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
  obtain ⟨C, hC⟩ := CSP.exists_linear_bound_replaceGadgetsGuarded
    SelfDualThreeSAT.arity B (fun s => (gadgets s).template) reject
  refine ⟨CSP.replaceGadgetsGuarded SelfDualThreeSAT.arity B
    (fun s => (gadgets s).template) reject, C, ?_, ?_, hC⟩
  · exact CSP.computableInPolyTime_replaceGadgetsGuarded
      SelfDualThreeSAT.encSign encRel SelfDualThreeSAT.arity B _ reject
  · intro F
    exact (CSP.wellFormed_satisfiable_replaceGadgetsGuarded_iff gadgets B hB
      reject hr F).symm

/-- **Linear-size 3SAT hardness in the hard Schaefer cases.** The same witness is a native
polynomial-time reduction under binary encodings and satisfies `n' + m' ≤ C * m`, stronger
than `n' + m' ≤ C * (n + m)`. Counts mean distinct occurring variables and clauses/constraints,
not encoded bit length. The bound and correctness hold for every raw CNF input. -/
theorem exists_linear_size_reduction_from_threeSAT [Finite Rel]
    (encRel : Rel ↪ List Bool) (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (h : ¬ CSP.HasSchaeferPolymorphism arity sem) :
    ∃ (f : CNF ℕ → CSP Rel ℕ) (C : ℕ),
      ComputableInPolyTime f encCNF (encCSP encRel encNat) ∧
      (∀ φ, φ ∈ ThreeSAT ↔ f φ ∈ CSPSAT arity sem) ∧
      (∀ φ, (f φ).numVars + (f φ).length ≤ C * φ.length) := by
  obtain ⟨g, C, hg, hm, hs⟩ :=
    exists_linear_size_reduction_from_selfDualThreeSAT encRel arity sem h
  refine ⟨fun φ => g (SelfDualThreeSAT.ofExactThreeSAT (toExactThreeSAT φ)), C,
    hg.comp (SelfDualThreeSAT.computableInPolyTime_ofExactThreeSAT.comp
      computableInPolyTime_toExactThreeSAT), ?_, ?_⟩
  · intro φ
    rw [← hm, SelfDualThreeSAT.ofExactThreeSAT_mem_iff,
      mem_ExactThreeSAT_toExactThreeSAT_iff]
  · intro φ
    calc
      _ ≤ C * (SelfDualThreeSAT.ofExactThreeSAT (toExactThreeSAT φ)).length := hs _
      _ ≤ C * (toExactThreeSAT φ).length :=
        Nat.mul_le_mul_left C (SelfDualThreeSAT.length_ofExactThreeSAT_le _)
      _ = C * φ.length := by simp [toExactThreeSAT]

/-- **The hard branch of Boolean Schaefer's dichotomy**, for arbitrary fixed relation arities.
The language is fixed, so noncomputable finite gadget selection makes no uniform preprocessing
claim. The actual native reduction from 3SAT has the linear combinatorial bound above. -/
theorem npComplete_of_not_hasSchaeferPolymorphism [Finite Rel]
    (encRel : Rel ↪ List Bool) (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (h : ¬ CSP.HasSchaeferPolymorphism arity sem) :
    NPComplete (encCSP encRel encNat) (CSPSAT arity sem) := by
  obtain ⟨f, _, hp, hm, _⟩ := exists_linear_size_reduction_from_threeSAT encRel arity sem h
  exact ⟨mem_NP encRel arity sem, ThreeSAT_npHard.trans ⟨f, hp, hm⟩⟩

end Cslib.Complexity.CSPSAT

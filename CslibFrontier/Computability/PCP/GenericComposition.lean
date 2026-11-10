/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.LocalTest
public import Mathlib.Data.Fin.VecNotation
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Linarith

/-!
# Composition with a binary-constraint assignment tester

An `AssignmentTester` reads two encoded input labels and an auxiliary proof. Its construction is
separate from perfect completeness and soundness relative to a supplied decoder. The latter asks
only that a violated decoded constraint causes rejection with probability at least `δ`; it is not
the stronger distance-soundness contract of an assignment tester for arbitrary circuits.

Composition shares each vertex's input table between all incident testers and gives each edge its
own auxiliary table. The existing local-test graph construction then loses a factor `|Q| / δ` in
value, independently of the particular encoding, decoder, and tester. No executable construction
or efficiency assertion is included in this mathematical interface.

## Main definitions

* `Cslib.PCP.AssignmentTester`: a tester, an input encoding, and honest auxiliary proofs.
* `Cslib.PCP.AssignmentTester.IsComplete`, `Cslib.PCP.AssignmentTester.Sound`: its certificates.
* `Cslib.PCP.AssignmentTester.compose`: the composed constraint graph.

## Main results

* `Cslib.PCP.AssignmentTester.unsatVal_compose_le`: quantitative perfect completeness.
* `Cslib.PCP.AssignmentTester.mul_unsatFrac_decodeLabelling_le`: weighted soundness.
* `Cslib.PCP.AssignmentTester.le_unsatVal_compose`: composition loses at most `|Q| / δ`.
* `Cslib.PCP.AssignmentTester.satisfiable_compose_iff`: preservation of satisfiability.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 22][AroraBarak09]
-/

@[expose] public section

namespace Cslib.PCP

open Finset
open scoped BigOperators

namespace ConstraintGraph

variable {V E α : Type*} (G : ConstraintGraph V E α)

/-- The two ends of an edge: the first one at `0`, the second one at `1`. -/
def ends (e : E) : Fin 2 → V :=
  ![G.src e, G.dst e]

@[simp]
theorem ends_zero (e : E) : G.ends e 0 = G.src e :=
  rfl

@[simp]
theorem ends_one (e : E) : G.ends e 1 = G.dst e :=
  rfl

end ConstraintGraph

/-- Data for testing binary constraints on `α`, with input positions `I`, auxiliary positions
`P`, coins `R`, queries `Q`, and proof symbols `Γ`. Correctness is supplied separately. -/
structure AssignmentTester (α I P R Q Γ : Type*) where
  /-- The local test for a binary constraint. -/
  test : (α → α → Prop) → LocalTest ((Fin 2 × I) ⊕ P) R Q Γ
  /-- The input table of a label. -/
  encode : α → I → Γ
  /-- The honest auxiliary table for a constraint and two input labels. -/
  auxiliary : (α → α → Prop) → (Fin 2 → α) → P → Γ

namespace AssignmentTester

variable {α I P R Q Γ V E : Type*} (T : AssignmentTester α I P R Q Γ)

/-- The two honest input tables together with the honest auxiliary table. -/
def honestProof (C : α → α → Prop) (σ : Fin 2 → α) : (Fin 2 × I) ⊕ P → Γ :=
  Sum.elim (fun p => T.encode (σ p.1) p.2) (T.auxiliary C σ)

/-- Every satisfied constraint accepts its honest proof for every random string. -/
def IsComplete : Prop :=
  ∀ {C : α → α → Prop} {σ : Fin 2 → α}, C (σ 0) (σ 1) →
    ∀ r, (T.test C).Passes (T.honestProof C σ) r

/-- A constraint violated by the decoded input tables is rejected with probability at least `δ`.
The decoder need not be computable; it is used only in the soundness argument. -/
def Sound [Fintype R] (decode : (I → Γ) → α) (δ : ℝ) : Prop :=
  ∀ (C : α → α → Prop) (π : (Fin 2 × I) ⊕ P → Γ),
    ¬ C (decode fun i => π (.inl (0, i))) (decode fun i => π (.inl (1, i))) →
      δ ≤ 1 - (T.test C).acceptProb π

/-- Shared vertex input tables and separate edge auxiliary tables. -/
abbrev ComposePos (V E I P : Type*) := (V × I) ⊕ (E × P)

/-- The part of a composed proof read by the tester of an edge. -/
def testerPos (G : ConstraintGraph V E α) (e : E) : (Fin 2 × I) ⊕ P → ComposePos V E I P :=
  Sum.elim (fun p => .inl (G.ends e p.1, p.2)) (fun p => .inr (e, p))

/-- Run the tester of a uniformly random edge on its input and auxiliary tables. -/
def composeTest (G : ConstraintGraph V E α) : LocalTest (ComposePos V E I P) (E × R) Q Γ :=
  LocalTest.mix fun e => (T.test (G.rel e)).map (testerPos G e)

/-- The constraint graph of the composed local test. -/
def compose (G : ConstraintGraph V E α) :
    ConstraintGraph (ComposePos V E I P ⊕ E × R) ((E × R) × Q) (Γ × (Q → Γ)) :=
  (T.composeTest G).toConstraintGraph

/-- Encode every vertex label and fill every edge's auxiliary table honestly. -/
def composeProof (G : ConstraintGraph V E α) (σ : V → α) : ComposePos V E I P → Γ :=
  Sum.elim (fun p => T.encode (σ p.1) p.2)
    (fun p => T.auxiliary (G.rel p.1) (fun b => σ (G.ends p.1 b)) p.2)

/-- A local tester reads the honest proof of its endpoint labels. -/
theorem composeProof_comp_testerPos (G : ConstraintGraph V E α) (σ : V → α) (e : E) :
    T.composeProof G σ ∘ testerPos G e = T.honestProof (G.rel e) (fun b => σ (G.ends e b)) := by
  funext p
  rcases p with ⟨b, i⟩ | p <;> rfl

variable {T}

/-- A satisfied edge's tester accepts the honest composed proof. -/
theorem passes_composeTest_composeProof (hcomplete : T.IsComplete) (G : ConstraintGraph V E α)
    {σ : V → α} {e : E} (he : G.Satisfies σ e) (r : R) :
    (T.composeTest G).Passes (T.composeProof G σ) (e, r) := by
  rw [composeTest, LocalTest.passes_mix, LocalTest.passes_map, composeProof_comp_testerPos]
  exact hcomplete he r

/-- Perfect completeness of composition. -/
theorem satisfiable_compose [Nonempty Γ] (hcomplete : T.IsComplete)
    {G : ConstraintGraph V E α} (h : G.Satisfiable) : (T.compose G).Satisfiable := by
  obtain ⟨σ, hσ⟩ := h
  exact LocalTest.satisfiable_toConstraintGraph fun r =>
    passes_composeTest_composeProof hcomplete G (hσ r.1) r.2

variable [Fintype R] [Fintype Q] [Nonempty R] [Nonempty Q]

/-- Honest composition violates no greater fraction of edges than the original labelling. -/
theorem unsatFrac_compose_labellingOf_le [Fintype E] (hcomplete : T.IsComplete)
    (G : ConstraintGraph V E α) (σ : V → α) (γ : Γ) :
    (T.compose G).unsatFrac ((T.composeTest G).labellingOf (T.composeProof G σ) γ) ≤
      G.unsatFrac σ := by
  classical
  rcases isEmpty_or_nonempty E with hE | hE
  · simp [ConstraintGraph.unsatFrac]
  rw [compose, LocalTest.unsatFrac_labellingOf, composeTest,
    LocalTest.acceptProb_mix, ← G.expect_mem_unsatEdges]
  conv_lhs => rw [← Fintype.expect_const (ι := E) (1 : ℝ), ← expect_sub_distrib]
  refine expect_le_expect fun e _ => ?_
  by_cases he : G.Satisfies σ e
  · have ha : ((T.test (G.rel e)).map (testerPos G e)).acceptProb (T.composeProof G σ) = 1 :=
      (LocalTest.acceptProb_eq_one_iff _).mpr fun r =>
        passes_composeTest_composeProof hcomplete G he r
    simp [ConstraintGraph.mem_unsatEdges, he, ha]
  · simpa only [ConstraintGraph.mem_unsatEdges, he, not_false_eq_true, ite_true, sub_le_self_iff]
      using LocalTest.acceptProb_nonneg _ _

/-- Quantitative perfect completeness: composition does not increase the value. -/
theorem unsatVal_compose_le [Fintype E] [Nonempty α] [Nonempty Γ]
    (hcomplete : T.IsComplete) (G : ConstraintGraph V E α) :
    (T.compose G).unsatVal ≤ G.unsatVal := by
  obtain ⟨σ, hσ⟩ := G.exists_unsatFrac_eq_unsatVal
  rw [← hσ]
  exact ((T.compose G).unsatVal_le _).trans
    (unsatFrac_compose_labellingOf_le hcomplete G σ (Classical.arbitrary Γ))

/-- Decode the shared input table of each vertex. -/
def decodeLabelling (decode : (I → Γ) → α) (π : ComposePos V E I P → Γ) (v : V) : α :=
  decode fun i => π (.inl (v, i))

/-- Weighted soundness: every violated decoded edge contributes `δ` rejection probability, and
each rejecting local test contributes at least one of its `|Q|` edges. -/
theorem mul_unsatFrac_decodeLabelling_le [Fintype E]
    {decode : (I → Γ) → α} {δ : ℝ} (hsound : T.Sound decode δ)
    (G : ConstraintGraph V E α) (A : ComposePos V E I P ⊕ E × R → Γ × (Q → Γ)) :
    δ * G.unsatFrac (decodeLabelling decode (LocalTest.proofOf A)) ≤
      Fintype.card Q * (T.compose G).unsatFrac A := by
  classical
  rcases isEmpty_or_nonempty E with hE | hE
  · simp [ConstraintGraph.unsatFrac]
  refine le_trans ?_ (LocalTest.one_sub_acceptProb_le_card_mul_unsatFrac A)
  rw [composeTest, LocalTest.acceptProb_mix, ← G.expect_mem_unsatEdges, mul_expect]
  conv_rhs => rw [← Fintype.expect_const (ι := E) (1 : ℝ), ← expect_sub_distrib]
  refine expect_le_expect fun e _ => ?_
  rw [LocalTest.acceptProb_map]
  split_ifs with he
  · simpa only [mul_one] using
      hsound (G.rel e) (LocalTest.proofOf A ∘ testerPos G e)
        (ConstraintGraph.mem_unsatEdges.1 he)
  · simpa only [mul_zero] using sub_nonneg.2 (LocalTest.acceptProb_le_one _ _)

/-- Soundness of composition: the value decreases by at most the factor `|Q| / δ`. -/
theorem le_unsatVal_compose [Fintype E] [Nonempty Γ]
    {decode : (I → Γ) → α} {δ : ℝ} (hsound : T.Sound decode δ) (hδ : 0 < δ)
    (G : ConstraintGraph V E α) :
    G.unsatVal / (Fintype.card Q / δ) ≤ (T.compose G).unsatVal := by
  obtain ⟨A, hA⟩ := (T.compose G).exists_unsatFrac_eq_unsatVal
  have h := (mul_le_mul_of_nonneg_left (G.unsatVal_le _) hδ.le).trans
    (mul_unsatFrac_decodeLabelling_le hsound G A)
  rw [hA] at h
  have hQ : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ (div_pos hQ hδ), ← mul_div_assoc, le_div_iff₀ hδ]
  nlinarith [h]

omit [Fintype Q] in
/-- A positive rejection bound and perfect completeness preserve satisfiability. -/
theorem satisfiable_compose_iff [Finite E] [Finite Q] [Nonempty α] [Nonempty Γ]
    (hcomplete : T.IsComplete) {decode : (I → Γ) → α} {δ : ℝ}
    (hsound : T.Sound decode δ) (hδ : 0 < δ) (G : ConstraintGraph V E α) :
    (T.compose G).Satisfiable ↔ G.Satisfiable := by
  let := Fintype.ofFinite E
  let := Fintype.ofFinite Q
  refine ⟨fun h => ?_, satisfiable_compose hcomplete⟩
  rw [← ConstraintGraph.unsatVal_eq_zero_iff] at h ⊢
  have hb := le_unsatVal_compose hsound hδ G
  rw [h] at hb
  have hQ : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
  have hzero := (div_le_iff₀ (div_pos hQ hδ)).mp hb
  exact le_antisymm (by simpa only [zero_mul] using hzero) G.unsatVal_nonneg

end AssignmentTester

end Cslib.PCP

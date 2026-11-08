/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.PrimitivePositive
public import Complexity.Foundations.Data.BitString.CyclicDifference
import Mathlib.Tactic.FinCases

/-!
# Finite crossover gadgets

This module verifies the conjunctions in [DvorakKupec2015], §4, printed pp. 440–441,
Figure 1. Ports `0,1,2,3` correspond to the cyclic boundary order `v₁,v₂,v₃,v₄`.
Figure 1(a) uses `R(m,v₃,v₄,v₁)`, `R(v₃,m̄,v₁,v̄₂)`, `N(m,m̄)`, `N(v̄₂,v₂)`;
Figure 1(b) uses `NEAR-CROSS(v₁,v₂,m,v₄)`, `NEAR-CROSS(v₃,v₄,m,v₂)`.
These are actual `CSP.PPGadget` bodies, with exact scope widths and existential auxiliaries.

Only finite relation semantics is proved here: no embedding, planar substitution, normalization
from non-delta-matroids (the source's Lemma 6, stated without proof), hardness or runtime
certificate is supplied. No expressibility theorem is assumed.

## Main definitions

* `Cslib.BitString.cross`, `Cslib.BitString.nearCross`: ordered four-port relations.
* `Cslib.BitString.IsStandardizedInconsistent`: the hypothesis on Figure 1(a)'s relation.
* `Cslib.BitString.standardizedRelation`: all eight possible standardized relations.
* `Cslib.Logic.PL.CSP.Crossover.figureOneA`: Figure 1(a) as a primitive-positive gadget.
* `Cslib.Logic.PL.CSP.Crossover.figureOneB`: Figure 1(b) as a primitive-positive gadget.

## Main results

* `Cslib.BitString.isStandardizedInconsistent_iff`: exhaustive three-bit classification.
* `Cslib.Logic.PL.CSP.Crossover.figureOneA_target`: the first target is CROSS or NEAR-CROSS.
-/

public section

namespace Cslib.BitString

/-- CROSS connects opposite ports in cyclic order: `0=2` and `1=3`. -/
@[expose] def cross : Set (Fin 4 → Bool) := {x | x 0 = x 2 ∧ x 1 = x 3}

instance : DecidablePred (· ∈ cross) := fun _ =>
  inferInstanceAs (Decidable (_ = _ ∧ _ = _))

/-- NEAR-CROSS adds `0001` and `1110` to CROSS, in the same cyclic port order. -/
@[expose] def nearCross : Set (Fin 4 → Bool) :=
  {x | x ∈ cross ∨ (x 0 = x 1 ∧ x 1 = x 2 ∧ x 2 ≠ x 3)}

instance : DecidablePred (· ∈ nearCross) := fun _ =>
  inferInstanceAs (Decidable (_ ∈ cross ∨ (_ = _ ∧ _ = _ ∧ _ ≠ _)))

/-- Standardized inconsistency in [DvorakKupec2015], §4, printed p. 440.
The relation is self-complementary, contains CROSS, and has only the specified tuples. -/
@[expose] def IsStandardizedInconsistent (R : Set (Fin 4 → Bool)) : Prop :=
  IsSelfComplementary R ∧ cross ⊆ R ∧
    ∀ x ∈ R, x 0 = x 1 ∨ (x 0 = x 2 ∧ x 0 ≠ x 1 ∧ x 1 = x 3)

/-- The eight standardized relations. Bits `p,q,r` select the complementary pairs
`0001/1110`, `0010/1101`, `0011/1100`, respectively, in addition to CROSS. -/
@[expose] def standardizedRelation (p q r : Bool) : Set (Fin 4 → Bool) :=
  {x | x ∈ cross ∨ (x 0 = x 1 ∧
    ((x 2 = x 0 ∧ x 3 ≠ x 0 ∧ p = true) ∨
     (x 2 ≠ x 0 ∧ x 3 = x 0 ∧ q = true) ∨
     (x 2 ≠ x 0 ∧ x 3 ≠ x 0 ∧ r = true)))}

instance instDecidableStandardizedRelation (p q r : Bool) :
    DecidablePred (· ∈ standardizedRelation p q r) := fun _ => by
  unfold standardizedRelation
  infer_instance

private theorem tuple_eq (x : Fin 4 → Bool) : x = ![x 0, x 1, x 2, x 3] := by
  ext i
  fin_cases i <;> rfl

private theorem complement_tuple (a b c d : Bool) :
    (fun i => !(![a, b, c, d] i)) = ![!a, !b, !c, !d] := by
  ext i
  fin_cases i <;> rfl

/-- The three optional complementary pairs exhaust the standardized condition. -/
theorem isStandardizedInconsistent_iff (R : Set (Fin 4 → Bool)) :
    IsStandardizedInconsistent R ↔ ∃ p q r, R = standardizedRelation p q r := by
  classical
  constructor
  · rintro ⟨hc, hin, hout⟩
    refine ⟨decide (![false, false, false, true] ∈ R),
      decide (![false, false, true, false] ∈ R),
      decide (![false, false, true, true] ∈ R), ?_⟩
    have hcomp (a b c d : Bool) :
        ![a, b, c, d] ∈ R ↔ ![!a, !b, !c, !d] ∈ R := by
      simpa only [complement_tuple] using hc ![a, b, c, d]
    have h1 := hcomp false false false true
    have h2 := hcomp false false true false
    have h3 := hcomp false false true true
    clear hc hcomp
    ext x
    rw [tuple_eq x]
    generalize x 0 = a, x 1 = b, x 2 = c, x 3 = d
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp_all only [standardizedRelation, cross, Set.mem_ofPred_eq,
        Matrix.cons_val, Fin.isValue, decide_eq_true_eq,
        Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false,
        ne_eq, not_false_eq_true, not_true_eq_false, eq_self, true_and, false_and,
        and_true, and_false, or_false,
        false_or, iff_true, iff_false] <;>
      first
      | exact hin (by decide)
      | intro h; have hh := hout _ h; simp at hh
  · rintro ⟨p, q, r, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rw [tuple_eq x, complement_tuple]
      generalize x 0 = a, x 1 = b, x 2 = c, x 3 = d
      cases a <;> cases b <;> cases c <;> cases d <;>
        simp [standardizedRelation, cross]
    · intro x hx
      exact Or.inl hx
    · intro x hx
      rcases hx with hx | ⟨h, _⟩
      · by_cases h : x 0 = x 1
        · exact Or.inl h
        · exact Or.inr ⟨hx.1, h, hx.2⟩
      · exact Or.inl h

end Cslib.BitString

namespace Cslib.Logic.PL.CSP.Crossover

open Cslib.BitString

/-- The alphabet for Figure 1(a): the given four-ary relation and binary disequality. -/
inductive Symbol where
  /-- The standardized relation. -/
  | relation
  /-- Boolean disequality. -/
  | disequality
  deriving DecidableEq

/-- Declared widths of the two Figure 1(a) symbols. -/
@[expose] def arity : Symbol → ℕ
  | .relation => 4
  | .disequality => 2

/-- Width-guarded interpretation of the given relation and Boolean disequality. -/
@[expose] def sem (R : Set (Fin 4 → Bool)) [DecidablePred (· ∈ R)] :
    Symbol → List Bool → Bool
  | .relation, [a, b, c, d] => decide (![a, b, c, d] ∈ R)
  | .disequality, [a, b] => decide (a ≠ b)
  | _, _ => false

/-- Figure 1(a)'s four constraints. Auxiliary indices `0,1,2` are `m,m̄,v̄₂`.
The order inside each scope is the numbered order in the figure. -/
@[expose] def figureOneABody : CSP Symbol (Fin 4 ⊕ Fin 3) :=
  [(.relation, [.inr 0, .inl 2, .inl 3, .inl 0]),
   (.relation, [.inl 2, .inr 1, .inl 0, .inr 2]),
   (.disequality, [.inr 0, .inr 1]),
   (.disequality, [.inr 2, .inl 1])]

/-- Figure 1(a)'s existential boundary relation, using the existing CSP evaluator. -/
@[expose] def figureOneARelation (R : Set (Fin 4 → Bool)) [DecidablePred (· ∈ R)] :
    Set (Fin 4 → Bool) :=
  {a | ∃ b, figureOneABody.eval (sem R) (Sum.elim a b) = true}

instance (R : Set (Fin 4 → Bool)) [DecidablePred (· ∈ R)] :
    DecidablePred (· ∈ figureOneARelation R) := fun _ =>
  inferInstanceAs (Decidable (∃ _, _ = true))

/-- The first figure as a well-formed primitive-positive gadget for its boundary relation. -/
@[expose] def figureOneA (R : Set (Fin 4 → Bool)) [DecidablePred (· ∈ R)] :
    PPGadget arity (sem R) (figureOneARelation R) where
  numAux := 3
  body := figureOneABody
  wellFormed := by decide
  correct _ := Iff.rfl

/-- Exhaustive finite semantics of Figure 1(a). The third optional pair has no effect;
either of the first two optional pairs produces precisely NEAR-CROSS. -/
theorem figureOneARelation_standardized (p q r : Bool) :
    figureOneARelation (standardizedRelation p q r) =
      if p || q then nearCross else cross := by
  cases p <;> cases q <;> cases r <;>
    simp only [Bool.false_or, Bool.true_or, Bool.false_eq_true, eq_self,
      ite_false, ite_true] <;>
    ext a <;> rw [tuple_eq a] <;>
    generalize a 0 = w, a 1 = x, a 2 = y, a 3 = z <;>
    cases w <;> cases x <;> cases y <;> cases z <;> decide

/-- Under exactly the standardized hypothesis, the actual first figure defines CROSS
or NEAR-CROSS. No planar expressibility premise or conclusion is used. -/
theorem figureOneA_target (R : Set (Fin 4 → Bool)) [inst : DecidablePred (· ∈ R)]
    (h : IsStandardizedInconsistent R) :
    figureOneARelation R = cross ∨ figureOneARelation R = nearCross := by
  obtain ⟨p, q, r, rfl⟩ := (isStandardizedInconsistent_iff R).mp h
  have hi : inst = instDecidableStandardizedRelation p q r := Subsingleton.elim _ _
  have he := congrArg (@figureOneARelation (standardizedRelation p q r)) hi
  have ht := he.trans (figureOneARelation_standardized p q r)
  cases p <;> cases q
  · exact Or.inl ht
  · exact Or.inr ht
  · exact Or.inr ht
  · exact Or.inr ht

/-- The exact first target can be selected by inspecting only `0001` and `0010` in `R`. -/
theorem figureOneARelation_eq (R : Set (Fin 4 → Bool)) [inst : DecidablePred (· ∈ R)]
    (h : IsStandardizedInconsistent R) :
    figureOneARelation R =
      if decide (![false, false, false, true] ∈ R ∨ ![false, false, true, false] ∈ R)
      then nearCross else cross := by
  obtain ⟨p, q, r, rfl⟩ := (isStandardizedInconsistent_iff R).mp h
  have hi : inst = instDecidableStandardizedRelation p q r := Subsingleton.elim _ _
  have he := congrArg (@figureOneARelation (standardizedRelation p q r)) hi
  rw [he.trans (figureOneARelation_standardized p q r)]
  cases p <;> cases q <;> simp [standardizedRelation, cross]

/-- Figure 1(a) with its explicitly identified CROSS or NEAR-CROSS target.
The body still has exactly the four constraints displayed in the source. -/
@[expose] def figureOneAStandardized (R : Set (Fin 4 → Bool)) [DecidablePred (· ∈ R)]
    (h : IsStandardizedInconsistent R) :
    PPGadget arity (sem R)
      (if decide (![false, false, false, true] ∈ R ∨ ![false, false, true, false] ∈ R)
       then nearCross else cross) where
  numAux := 3
  body := figureOneABody
  wellFormed := by decide
  correct a := by
    rw [← figureOneARelation_eq R h]
    rfl

/-- The width-guarded NEAR-CROSS interpretation for Figure 1(b)'s single symbol. -/
@[expose] def nearSem : Unit → List Bool → Bool
  | _, [a, b, c, d] => decide (![a, b, c, d] ∈ nearCross)
  | _, _ => false

/-- Figure 1(b)'s two constraints; its one auxiliary is `m`. -/
@[expose] def figureOneBBody : CSP Unit (Fin 4 ⊕ Fin 1) :=
  [((), [.inl 0, .inl 1, .inr 0, .inl 3]),
   ((), [.inl 2, .inl 3, .inr 0, .inl 1])]

/-- Figure 1(b) defines precisely CROSS, with existential `m`. -/
theorem figureOneB_correct (a : Fin 4 → Bool) :
    a ∈ cross ↔ ∃ b, figureOneBBody.eval nearSem (Sum.elim a b) = true := by
  rw [tuple_eq a]
  generalize a 0 = w, a 1 = x, a 2 = y, a 3 = z
  cases w <;> cases x <;> cases y <;> cases z <;> decide

/-- The actual Figure 1(b) primitive-positive gadget from NEAR-CROSS to CROSS. -/
@[expose] def figureOneB : PPGadget (fun _ : Unit => 4) nearSem cross where
  numAux := 1
  body := figureOneBBody
  wellFormed := by decide
  correct := figureOneB_correct

end Cslib.Logic.PL.CSP.Crossover

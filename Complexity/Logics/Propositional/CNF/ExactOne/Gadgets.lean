/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ExactOne

/-!
# Parsimonious exact-one clause gadgets

The disjunction gadget is the four-clause construction of
[Hunt, Marathe, Radhakrishnan and Stearns, Theorem 3.8, Figure 3.4(a)]
[HuntMaratheRadhakrishnanStearns1998]. It admits exactly one auxiliary assignment for each
satisfying assignment of the three source literals. The positive constant gadget is their
Lemma 3.6; it forces one designated variable false and has a unique assignment to all four
variables. Attaching that constant to a positive ternary clause gives a parsimonious complement
constraint, as in their Figure 3.5.

## Main definitions

* `disjunctionClauses`: four exact-three clauses replacing one ordinary disjunction.
* `forceFalseClauses`: three positive clauses forcing a designated variable false.
* `complementClauses`: four positive clauses enforcing opposite terminal values.

## Main results

* `disjunctionHolds_iff`: disjunction correctness and the unique five auxiliary values.
* `evalOne_disjunctionClauses_iff`: the corresponding formula-level characterization.
* `evalOne_forceFalseClauses_iff`, `evalOne_complementClauses_iff`: unique constant and
  complement extensions.

## References

* [Hunt, Marathe, Radhakrishnan and Stearns][HuntMaratheRadhakrishnanStearns1998],
  Theorem 3.8, Figures 3.4–3.5 and Lemma 3.6.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.ExactOneGadget

variable {V : Type*}

/-- Exactly one of three Boolean values is true. -/
def One (a b c : Bool) : Prop := [a, b, c].count true = 1

instance (a b c : Bool) : Decidable (One a b c) :=
  inferInstanceAs (Decidable ([a, b, c].count true = 1))

/-- The four scalar exact-one constraints in the parsimonious disjunction gadget. -/
def DisjunctionHolds (p q r u v w t x : Bool) : Prop :=
  One p u v ∧ One (!q) u w ∧ One v w t ∧ One (!r) v x

instance (p q r u v w t x : Bool) : Decidable (DisjunctionHolds p q r u v w t x) :=
  inferInstanceAs (Decidable (One p u v ∧ One (!q) u w ∧ One v w t ∧ One (!r) v x))

private theorem beq_true (b : Bool) : (b == true) = b := by cases b <;> rfl

/-- The first auxiliary value of the disjunction gadget. -/
def firstAux (p q : Bool) : Bool := !p && q

/-- The second auxiliary value of the disjunction gadget. -/
def secondAux (p q : Bool) : Bool := !p && !q

/-- The third auxiliary value of the disjunction gadget. -/
def thirdAux (p q : Bool) : Bool := p && q

/-- The fourth auxiliary value of the disjunction gadget. -/
def fourthAux (p q : Bool) : Bool := !(secondAux p q || thirdAux p q)

/-- The fifth auxiliary value of the disjunction gadget. -/
def fifthAux (p q r : Bool) : Bool := r && (p || q)

/-- Every satisfying source triple has exactly the displayed auxiliary extension, and the
all-false source triple has none. -/
theorem disjunctionHolds_iff (p q r u v w t x : Bool) :
    DisjunctionHolds p q r u v w t x ↔
      (p || q || r) = true ∧ u = firstAux p q ∧ v = secondAux p q ∧
        w = thirdAux p q ∧ t = fourthAux p q ∧ x = fifthAux p q r := by
  cases p <;> cases q <;> cases r <;> cases u <;> cases v <;> cases w <;> cases t <;>
    cases x <;> decide

/-- The canonical auxiliary values satisfy the gadget exactly on satisfying source triples. -/
theorem disjunctionHolds_canonical_iff (p q r : Bool) :
    DisjunctionHolds p q r (firstAux p q) (secondAux p q) (thirdAux p q)
      (fourthAux p q) (fifthAux p q r) ↔ (p || q || r) = true := by
  simp [disjunctionHolds_iff]

/-- Replace a signed three-literal disjunction by four exact-three clauses. Auxiliary literals
are positive, while the second and third source literals are negated. -/
def disjunctionClauses (p q r : Literal V) (u v w t x : V) : CNF V :=
  [[p, (u, true), (v, true)],
    [Std.Sat.Literal.negate q, (u, true), (w, true)],
    [(v, true), (w, true), (t, true)],
    [Std.Sat.Literal.negate r, (v, true), (x, true)]]

/-- A positive three-clause gadget with one true auxiliary and three false variables. The
first variable is the false terminal and has two internal occurrences. -/
def forceFalseClauses (c d e f : V) : CNF V :=
  [[(c, true), (d, true), (e, true)],
    [(c, true), (e, true), (f, true)],
    [(d, true), (e, true), (f, true)]]

/-- Opposite terminal values, enforced using a uniquely determined positive false gadget. -/
def complementClauses (p q c d e f : V) : CNF V :=
  [(p, true), (q, true), (c, true)] :: forceFalseClauses c d e f

/-- The fixed disjunction gadget with source variables `0, 1, 2` and auxiliaries `3` through
`7`. Its incidence drawing is independent of the literal polarities. -/
def disjunction : CNF ℕ := disjunctionClauses (0, true) (1, true) (2, true) 3 4 5 6 7

/-- The fixed positive false gadget, with false terminal `0`. -/
def forceFalse : CNF ℕ := forceFalseClauses 0 1 2 3

/-- The fixed positive complement gadget, with terminals `0, 1` and auxiliaries `2` through
`5`. -/
def complement : CNF ℕ := complementClauses 0 1 2 3 4 5

/-- The scalar exact-one predicate is the evaluation of three literals. -/
theorem evalOne_triple_iff (σ : V → Bool) (a b c : Literal V) :
    Clause.evalOne σ [a, b, c] = true ↔
      One (Literal.eval σ a) (Literal.eval σ b) (Literal.eval σ c) := by
  simp only [Clause.evalOne, List.countP_cons, List.countP_nil, beq_iff_eq]
  cases Literal.eval σ a <;> cases Literal.eval σ b <;> cases Literal.eval σ c <;>
    decide

/-- Formula evaluation recovers the four scalar constraints. -/
theorem evalOne_disjunctionClauses_iff (σ : V → Bool) (p q r : Literal V)
    (u v w t x : V) :
    CNF.evalOne σ (disjunctionClauses p q r u v w t x) = true ↔
      DisjunctionHolds (Literal.eval σ p) (Literal.eval σ q) (Literal.eval σ r)
        (σ u) (σ v) (σ w) (σ t) (σ x) := by
  simp only [disjunctionClauses, CNF.evalOne, List.all_cons, List.all_nil,
    Bool.and_eq_true, and_true, evalOne_triple_iff, Literal.eval_negate, Literal.eval_mk,
    beq_true, DisjunctionHolds]

/-- The formula has precisely the canonical disjunction extension. -/
theorem evalOne_disjunctionClauses_iff_canonical (σ : V → Bool) (p q r : Literal V)
    (u v w t x : V) :
    CNF.evalOne σ (disjunctionClauses p q r u v w t x) = true ↔
      (Literal.eval σ p || Literal.eval σ q || Literal.eval σ r) = true ∧
        σ u = firstAux (Literal.eval σ p) (Literal.eval σ q) ∧
        σ v = secondAux (Literal.eval σ p) (Literal.eval σ q) ∧
        σ w = thirdAux (Literal.eval σ p) (Literal.eval σ q) ∧
        σ t = fourthAux (Literal.eval σ p) (Literal.eval σ q) ∧
        σ x = fifthAux (Literal.eval σ p) (Literal.eval σ q) (Literal.eval σ r) :=
  (evalOne_disjunctionClauses_iff σ p q r u v w t x).trans
    (disjunctionHolds_iff _ _ _ _ _ _ _ _)

/-- The positive false gadget has exactly the values `(false, false, true, false)`. -/
theorem evalOne_forceFalseClauses_iff (σ : V → Bool) (c d e f : V) :
    CNF.evalOne σ (forceFalseClauses c d e f) = true ↔
      σ c = false ∧ σ d = false ∧ σ e = true ∧ σ f = false := by
  simp only [forceFalseClauses, CNF.evalOne, List.all_cons, List.all_nil,
    Bool.and_eq_true, and_true, evalOne_triple_iff, Literal.eval_mk, beq_true]
  cases σ c <;> cases σ d <;> cases σ e <;> cases σ f <;> decide

/-- The positive complement gadget forces opposite terminals and uniquely fixes every
auxiliary variable. -/
theorem evalOne_complementClauses_iff (σ : V → Bool) (p q c d e f : V) :
    CNF.evalOne σ (complementClauses p q c d e f) = true ↔
      σ p = !σ q ∧ σ c = false ∧ σ d = false ∧ σ e = true ∧ σ f = false := by
  change (Clause.evalOne σ [(p, true), (q, true), (c, true)] &&
    CNF.evalOne σ (forceFalseClauses c d e f)) = true ↔ _
  rw [Bool.and_eq_true, evalOne_triple_iff, evalOne_forceFalseClauses_iff]
  simp only [Literal.eval_mk, beq_true]
  cases σ p <;> cases σ q <;> cases σ c <;> cases σ d <;> cases σ e <;> cases σ f <;>
    decide

/-- The disjunction gadget has four clauses. -/
theorem length_disjunctionClauses (p q r : Literal V) (u v w t x : V) :
    (disjunctionClauses p q r u v w t x).length = 4 := rfl

/-- The positive false gadget has three clauses. -/
theorem length_forceFalseClauses (c d e f : V) :
    (forceFalseClauses c d e f).length = 3 := rfl

/-- The positive complement gadget has four clauses. -/
theorem length_complementClauses (p q c d e f : V) :
    (complementClauses p q c d e f).length = 4 := rfl

/-- The disjunction gadget has twelve literal occurrences. -/
theorem length_vars_disjunctionClauses (p q r : Literal V) (u v w t x : V) :
    (disjunctionClauses p q r u v w t x).vars.length = 12 := rfl

/-- The positive false gadget has nine literal occurrences. -/
theorem length_vars_forceFalseClauses (c d e f : V) :
    (forceFalseClauses c d e f).vars.length = 9 := rfl

/-- The positive complement gadget has twelve literal occurrences. -/
theorem length_vars_complementClauses (p q c d e f : V) :
    (complementClauses p q c d e f).vars.length = 12 := rfl

/-- Every clause of a disjunction gadget is ternary. -/
theorem width_disjunctionClauses (p q r : Literal V) (u v w t x : V) :
    ∀ c ∈ disjunctionClauses p q r u v w t x, c.length = 3 := by
  simp [disjunctionClauses]

/-- Every clause of a false gadget is ternary. -/
theorem width_forceFalseClauses (c d e f : V) :
    ∀ a ∈ forceFalseClauses c d e f, a.length = 3 := by
  simp [forceFalseClauses]

/-- Every clause of a complement gadget is ternary. -/
theorem width_complementClauses (p q c d e f : V) :
    ∀ a ∈ complementClauses p q c d e f, a.length = 3 := by
  simp [complementClauses, forceFalseClauses]

/-- The false gadget contains only positive literals. -/
theorem positive_forceFalseClauses (c d e f : V) :
    ∀ a ∈ forceFalseClauses c d e f, ∀ l ∈ a, l.2 = true := by
  simp [forceFalseClauses]

/-- The complement gadget contains only positive literals. -/
theorem positive_complementClauses (p q c d e f : V) :
    ∀ a ∈ complementClauses p q c d e f, ∀ l ∈ a, l.2 = true := by
  simp [complementClauses, forceFalseClauses]

/-- Occurrence counts of every variable in the fixed disjunction gadget. -/
theorem disjunction_occurrences :
    disjunction.vars.count 0 = 1 ∧ disjunction.vars.count 1 = 1 ∧
      disjunction.vars.count 2 = 1 ∧ disjunction.vars.count 3 = 2 ∧
      disjunction.vars.count 4 = 3 ∧ disjunction.vars.count 5 = 2 ∧
      disjunction.vars.count 6 = 1 ∧ disjunction.vars.count 7 = 1 := by decide

/-- The false port has degree two; no variable in the fixed false gadget exceeds degree three. -/
theorem forceFalse_occurrences :
    forceFalse.vars.count 0 = 2 ∧ forceFalse.vars.count 1 = 2 ∧
      forceFalse.vars.count 2 = 3 ∧ forceFalse.vars.count 3 = 2 := by decide

/-- Each complement terminal has degree one, leaving its original incidence capacity intact. -/
theorem complement_occurrences :
    complement.vars.count 0 = 1 ∧ complement.vars.count 1 = 1 ∧
      complement.vars.count 2 = 3 ∧ complement.vars.count 3 = 2 ∧
      complement.vars.count 4 = 3 ∧ complement.vars.count 5 = 2 := by decide

end Cslib.Logic.PL.CNF.ExactOneGadget

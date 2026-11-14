/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space.TQBF.PolyTime
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# TAUTOLOGY is coNP-complete

A *Boolean formula* is built from variables, the constants, negation, conjunction and disjunction
[Arora and Barak, Section 2.3][AroraBarak09]. These are the quantifier-free formulas of
`Cslib.Logic.PL.QBF` (`Cslib.Logic.PL.QBF.QuantifierFree`), encoded by their tokens in prefix
order (`Cslib.Complexity.encQBF`). `TAUTOLOGY` is the set of quantifier-free formulas over variables
numbered by natural numbers that are true under every assignment
[Arora and Barak, Example 2.23][AroraBarak07]. A formula with a quantifier is not in `TAUTOLOGY`;
this is a total language on `QBF ℕ`, not a promise problem. Restricting to formulas in conjunctive
normal form would make the problem polynomial-time, so general formulas are essential.

A quantifier-free formula is evaluated by one scan of its tokens from right to left, with a stack
of truth values (`Cslib.Logic.PL.QBF.evalStep`): a variable or a constant pushes its value, a
negation negates the top value, and a binary connective combines the two values on top. On the
tokens of a quantifier-free formula the scan pushes its value (`Cslib.Logic.PL.QBF.foldl_evalStep`),
in polynomial time when the assignment is the indicator of a list of variables
(`Cslib.Complexity.computableInPolyTime_evalTokens`). The scan and its polynomial-time proof
are adapted from Samuel Schlesinger's free-variable scan in
`CslibFrontier.Computability.Complexity.Problems.TQBF.Closed`, with truth values in place of lists
of variables.

A formula is not a tautology when it has a quantifier or some assignment falsifies it, and a
falsifying assignment is the set of its true variables among the variables of the formula, a
subset witness (`Cslib.Complexity.mem_NP_of_subsetWitness`). So `TAUTOLOGY ∈ coNP`
(`Cslib.Complexity.TAUTOLOGY_mem_coNP`). Negation reduces `UNSAT` to `TAUTOLOGY`
(`Cslib.Complexity.UNSAT_reducible_TAUTOLOGY`), so `TAUTOLOGY` is coNP-complete by the Cook–Levin
theorem (`Cslib.Complexity.TAUTOLOGY_coNPComplete`).

## Main definitions

* `Cslib.Logic.PL.QBF.QuantifierFree`: Boolean formulas among quantified Boolean formulas.
* `Cslib.Logic.PL.QBF.evalStep`: the scan of the tokens of a quantifier-free formula.
* `Cslib.Complexity.TAUTOLOGY`: the quantifier-free formulas true under every assignment.

## Main results

* `Cslib.Logic.PL.QBF.quantifierFree_iff_tokens`: quantifier-freeness on the tokens.
* `Cslib.Logic.PL.QBF.foldl_evalStep`: the scan evaluates a quantifier-free formula.
* `Cslib.Complexity.computableInPolyTime_decide_quantifierFree`,
  `Cslib.Complexity.computableInPolyTime_evalTokens`: both in polynomial time.
* `Cslib.Complexity.TAUTOLOGY_mem_coNP`, `Cslib.Complexity.UNSAT_reducible_TAUTOLOGY`,
  `Cslib.Complexity.TAUTOLOGY_coNPHard`, `Cslib.Complexity.TAUTOLOGY_coNPComplete`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, 2007 draft][AroraBarak07]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Logic.PL.QBF

variable {V : Type*}

/-- A formula is *quantifier-free*, a Boolean formula, when it has no quantifier. -/
def QuantifierFree : QBF V → Prop
  | .var _ => True
  | .top => True
  | .bot => True
  | .not φ => φ.QuantifierFree
  | .and φ ψ => φ.QuantifierFree ∧ ψ.QuantifierFree
  | .or φ ψ => φ.QuantifierFree ∧ ψ.QuantifierFree
  | .ex _ _ => False
  | .all _ _ => False

@[simp] theorem quantifierFree_var (v : V) : (var v).QuantifierFree := trivial

@[simp] theorem quantifierFree_top : (top : QBF V).QuantifierFree := trivial

@[simp] theorem quantifierFree_bot : (bot : QBF V).QuantifierFree := trivial

@[simp] theorem quantifierFree_not {φ : QBF V} : φ.not.QuantifierFree ↔ φ.QuantifierFree :=
  Iff.rfl

@[simp] theorem quantifierFree_and {φ ψ : QBF V} :
    (φ.and ψ).QuantifierFree ↔ φ.QuantifierFree ∧ ψ.QuantifierFree := Iff.rfl

@[simp] theorem quantifierFree_or {φ ψ : QBF V} :
    (φ.or ψ).QuantifierFree ↔ φ.QuantifierFree ∧ ψ.QuantifierFree := Iff.rfl

@[simp] theorem not_quantifierFree_ex (v : V) (φ : QBF V) : ¬(ex v φ).QuantifierFree := id

@[simp] theorem not_quantifierFree_all (v : V) (φ : QBF V) : ¬(all v φ).QuantifierFree := id

/-- A formula is quantifier-free exactly when none of its tokens is a quantifier. -/
theorem quantifierFree_iff_tokens {φ : QBF ℕ} :
    φ.QuantifierFree ↔ ∀ t ∈ φ.tokens, t.1.isQuantifier = false := by
  induction φ with
  | var v => simp [QuantifierFree, tokens, Kind.isQuantifier]
  | top => simp [QuantifierFree, tokens, Kind.isQuantifier]
  | bot => simp [QuantifierFree, tokens, Kind.isQuantifier]
  | not φ ih => simp [QuantifierFree, tokens, Kind.isQuantifier, ih]
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [QuantifierFree, tokens, ihφ, ihψ, List.mem_cons, List.mem_append]
    refine ⟨fun ⟨h₁, h₂⟩ t ht => ?_, fun h => ⟨fun t ht => h t (.inr (.inl ht)),
      fun t ht => h t (.inr (.inr ht))⟩⟩
    rcases ht with rfl | ht | ht
    exacts [rfl, h₁ t ht, h₂ t ht]
  | ex v φ => simp [QuantifierFree, tokens, Kind.isQuantifier]
  | all v φ => simp [QuantifierFree, tokens, Kind.isQuantifier]

instance : DecidablePred (QuantifierFree : QBF ℕ → Prop) := fun _ =>
  decidable_of_iff _ quantifierFree_iff_tokens.symm

/-- A free variable of a formula occurs as a variable token. -/
theorem mem_tokens_of_mem_freeVars {φ : QBF ℕ} {x : ℕ} (hx : x ∈ φ.freeVars) :
    (Kind.var, x) ∈ φ.tokens := by
  induction φ with
  | var v => simp_all [tokens]
  | top => simp at hx
  | bot => simp at hx
  | not φ ih => exact List.mem_cons_of_mem _ (ih hx)
  | and φ ψ ihφ ihψ =>
    rw [freeVars_and, Finset.mem_union] at hx
    simp only [tokens, List.mem_cons, List.mem_append]
    exact .inr (hx.imp ihφ ihψ)
  | or φ ψ ihφ ihψ =>
    rw [freeVars_or, Finset.mem_union] at hx
    simp only [tokens, List.mem_cons, List.mem_append]
    exact .inr (hx.imp ihφ ihψ)
  | ex v φ ih => exact List.mem_cons_of_mem _ (ih (Finset.mem_of_mem_erase hx))
  | all v φ ih => exact List.mem_cons_of_mem _ (ih (Finset.mem_of_mem_erase hx))

/-- One step of the evaluating scan of the tokens from right to left, for a token of kind `k` and
variable `v`, on the stack of the values of the subformulas read so far. Quantifiers leave the
stack unchanged; the scan is meant for quantifier-free formulas. -/
def evalStepAt (σ : ℕ → Bool) : Kind → ℕ → List Bool → List Bool
  | .var, v, stack => σ v :: stack
  | .top, _, stack => true :: stack
  | .bot, _, stack => false :: stack
  | .not, _, stack => (!stack.headD false) :: stack.tail
  | .and, _, stack => (stack.headD false && stack.tail.headD false) :: stack.tail.tail
  | .or, _, stack => (stack.headD false || stack.tail.headD false) :: stack.tail.tail
  | .ex, _, stack => stack
  | .all, _, stack => stack

/-- One step of the evaluating scan of the tokens from right to left. -/
def evalStep (σ : ℕ → Bool) (stack : List Bool) (t : Kind × ℕ) : List Bool :=
  evalStepAt σ t.1 t.2 stack

/-- **The scan of the tokens** of a quantifier-free formula pushes its value. -/
theorem foldl_evalStep {φ : QBF ℕ} (hφ : φ.QuantifierFree) (σ : ℕ → Bool) (stack : List Bool) :
    φ.tokens.reverse.foldl (evalStep σ) stack = φ.eval σ :: stack := by
  induction φ generalizing stack with
  | var v => rfl
  | top => rfl
  | bot => rfl
  | not φ ih =>
    simp only [tokens, List.reverse_cons, List.foldl_append, ih hφ, List.foldl_cons,
      List.foldl_nil]
    rfl
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [tokens, List.reverse_cons, List.reverse_append, List.foldl_append, ihψ hφ.2,
      ihφ hφ.1, List.foldl_cons, List.foldl_nil]
    rfl
  | ex v φ => exact hφ.elim
  | all v φ => exact hφ.elim

end Cslib.Logic.PL.QBF

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM Cslib.Logic.PL ComputableInPolyTime TQBF

/-- **TAUTOLOGY**: the Boolean formulas, over variables numbered by natural numbers, that are true
under every assignment [Arora and Barak, Example 2.23][AroraBarak07]. Formulas with quantifiers
are not members. -/
def TAUTOLOGY : Set (QBF ℕ) := {φ | φ.QuantifierFree ∧ ∀ σ : ℕ → Bool, φ.eval σ = true}

theorem mem_TAUTOLOGY {φ : QBF ℕ} :
    φ ∈ TAUTOLOGY ↔ φ.QuantifierFree ∧ ∀ σ : ℕ → Bool, φ.eval σ = true := Iff.rfl

/-- The negation of a formula in conjunctive normal form is a tautology exactly when the formula
is unsatisfiable. -/
theorem not_ofCNF_mem_TAUTOLOGY_iff {φ : CNF ℕ} : (QBF.ofCNF φ).not ∈ TAUTOLOGY ↔ φ ∈ UNSAT := by
  have hqf : (QBF.ofCNF φ).QuantifierFree := by
    have hc (c : Clause ℕ) : (QBF.ofClause c).QuantifierFree := by
      induction c with
      | nil => trivial
      | cons l c ih => exact ⟨by cases l.2 <;> trivial, ih⟩
    induction φ with
    | nil => trivial
    | cons c φ ih => exact ⟨hc c, ih⟩
  simp [mem_TAUTOLOGY, QBF.QuantifierFree, hqf, mem_UNSAT, CNF.Satisfiable]

/-- Deciding quantifier-freeness is polynomial-time. -/
theorem computableInPolyTime_decide_quantifierFree :
    ComputableInPolyTime (fun φ : QBF ℕ => decide φ.QuantifierFree) encQBF encBool := by
  have h (φ : QBF ℕ) : decide φ.QuantifierFree = φ.tokens.all fun t => !t.1.isQuantifier := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, QBF.quantifierFree_iff_tokens, List.all_eq_true]
    simp
  simp only [h]
  have hk : ComputableInPolyTime (fun p : QBF ℕ × (QBF.Kind × ℕ) => !p.2.1.isQuantifier)
      (encPair encQBF encToken) encBool :=
    (of_finite (encIn := encKind) (encOut := encBool) fun k : QBF.Kind => !k.isQuantifier).comp
      (by fun_prop)
  fun_prop

/-- A step of the scan for a fixed kind of token, with the indicator of a list of variables as the
assignment, is polynomial-time. -/
private theorem evalStepAt_pt (k : QBF.Kind) :
    ComputableInPolyTime (fun p : (List ℕ × List Bool) × (QBF.Kind × ℕ) =>
      QBF.evalStepAt (fun v => p.1.1.contains v) k p.2.2 p.1.2)
      (encFoldStep (encList encNat) (encList encBool) encToken) (encList encBool) := by
  cases k <;> simp only [QBF.evalStepAt] <;> fun_prop

/-- A step of the scan is polynomial-time. -/
private theorem evalStep_pt :
    ComputableInPolyTime (fun p : (List ℕ × List Bool) × (QBF.Kind × ℕ) =>
      QBF.evalStep (fun v => p.1.1.contains v) p.1.2 p.2)
      (encFoldStep (encList encNat) (encList encBool) encToken) (encList encBool) :=
  finite_cases (tagEncoding := encKind)
    (tag := fun p : (List ℕ × List Bool) × (QBF.Kind × ℕ) => p.2.1)
    (branch := fun k p => QBF.evalStepAt (fun v => p.1.1.contains v) k p.2.2 p.1.2)
    (by fun_prop) evalStepAt_pt

/-- One step of the scan adds at most one value to the stack. -/
private theorem length_evalStep_le (σ : ℕ → Bool) (stack : List Bool) (t : QBF.Kind × ℕ) :
    (encList encBool (QBF.evalStep σ stack t)).length ≤ (encList encBool stack).length + 4 := by
  obtain ⟨k, v⟩ := t
  simp only [QBF.evalStep]
  cases k <;> simp only [QBF.evalStepAt] <;>
    rcases stack with _ | ⟨a, _ | ⟨b, stack⟩⟩ <;>
    simp only [encList_cons, List.length_append, length_frame, encList_nil, List.length_nil,
      List.headD_nil, List.headD_cons, List.tail_nil, List.tail_cons, encBool_apply,
      List.length_singleton] <;> omega

/-- **Evaluating a formula from its tokens is polynomial-time**, under the assignment making
exactly the listed variables true. On a quantifier-free formula the scan returns its value
(`Cslib.Logic.PL.QBF.foldl_evalStep`). -/
theorem computableInPolyTime_evalTokens :
    ComputableInPolyTime (fun p : QBF ℕ × List ℕ =>
      (p.1.tokens.reverse.foldl (QBF.evalStep fun v => p.2.contains v) []).headD false)
      (encPair encQBF (encList encNat)) encBool := by
  have hfold : ComputableInPolyTime (fun p : QBF ℕ × List ℕ =>
      p.1.tokens.reverse.foldl (QBF.evalStep fun v => p.2.contains v) [])
      (encPair encQBF (encList encNat)) (encList encBool) :=
    foldlWith_of_bounded_growth (encA := encToken) (encL := encList encToken)
      (step := fun (l : List ℕ) => QBF.evalStep fun v => l.contains v)
      (par := Prod.snd) (by fun_prop) (by fun_prop) (const []) evalStep_pt
      (growth := fun _ => 4) (.const 4) fun _ stack t _ => length_evalStep_le _ stack t
  fun_prop

/-- The complement of `TAUTOLOGY` as a subset problem: a formula is not a tautology exactly when
it has a quantifier or the set of its true variables, among the variables of its tokens, makes
it false. -/
private theorem compl_TAUTOLOGY_eq :
    TAUTOLOGYᶜ = {φ | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ φ.tokens.map Prod.snd) ∧
      (¬φ.QuantifierFree ∨ φ.eval (fun v => decide (v ∈ S)) = false)} := by
  ext φ
  simp only [Set.mem_compl_iff, mem_TAUTOLOGY, not_and_or, not_forall, Bool.not_eq_true,
    Set.mem_ofPred_eq]
  constructor
  · rintro (h | ⟨σ, hσ⟩)
    · exact ⟨∅, by simp, .inl h⟩
    · refine ⟨((φ.tokens.map Prod.snd).filter σ).toFinset, fun v hv => ?_, .inr ?_⟩
      · exact List.mem_of_mem_filter (List.mem_toFinset.1 hv)
      · rw [← hσ]
        refine QBF.eval_congr fun w hw => ?_
        have hmem : w ∈ φ.tokens.map Prod.snd :=
          List.mem_map.2 ⟨_, QBF.mem_tokens_of_mem_freeVars hw, rfl⟩
        by_cases h : σ w <;> simp [h, hmem]
  · rintro ⟨S, -, h | h⟩
    · exact .inl h
    · exact .inr ⟨_, h⟩

/-- **TAUTOLOGY is in coNP:** a non-tautology has a quantifier or a falsifying assignment, given by
its true variables. -/
theorem TAUTOLOGY_mem_coNP : TAUTOLOGY ∈ coNP encQBF := by
  rw [mem_coNP, compl_TAUTOLOGY_eq]
  refine mem_NP_of_subsetWitness (encγ := encNat) (vs := fun φ : QBF ℕ => φ.tokens.map Prod.snd)
    (check := fun p : QBF ℕ × List ℕ => !decide p.1.QuantifierFree ||
      !(p.1.tokens.reverse.foldl (QBF.evalStep fun v => p.2.contains v) []).headD false)
    (by fun_prop) ?_ fun φ l _ _ => ?_
  · have h₁ : ComputableInPolyTime (fun p : QBF ℕ × List ℕ => decide p.1.QuantifierFree)
        (encPair encQBF (encList encNat)) encBool :=
      computableInPolyTime_decide_quantifierFree.comp (fst _ _)
    have h₂ := computableInPolyTime_evalTokens
    fun_prop
  · by_cases hφ : φ.QuantifierFree
    · simp [hφ, QBF.foldl_evalStep hφ]
    · simp [hφ]

/-- **UNSAT reduces to TAUTOLOGY** by negation. -/
theorem UNSAT_reducible_TAUTOLOGY : PolyTimeReducible encCNF encQBF UNSAT TAUTOLOGY :=
  ⟨fun φ => (QBF.ofCNF φ).not, by unfold encCNF; fun_prop,
    fun _ => not_ofCNF_mem_TAUTOLOGY_iff.symm⟩

/-- TAUTOLOGY is coNP-hard. -/
theorem TAUTOLOGY_coNPHard : coNPHard encQBF TAUTOLOGY :=
  CookLevin.UNSAT_coNPComplete.2.trans UNSAT_reducible_TAUTOLOGY

/-- **TAUTOLOGY is coNP-complete** [Arora and Barak, Example 2.23][AroraBarak07]. -/
theorem TAUTOLOGY_coNPComplete : coNPComplete encQBF TAUTOLOGY :=
  ⟨TAUTOLOGY_mem_coNP, TAUTOLOGY_coNPHard⟩

end Cslib.Complexity

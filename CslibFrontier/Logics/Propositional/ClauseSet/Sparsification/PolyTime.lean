/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.ClauseSet.Sparsification.List
public import CslibFrontier.Logics.Propositional.ClauseSet.Sparsification.Bounds
public import CslibFrontier.Logics.Propositional.CNF.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Sparsification -- the step is polynomial-time

The list-level sparsification step (`Cslib.Logic.PL.CNF.Sparsification.next`), the test for
sparseness (`Cslib.Logic.PL.CNF.Sparsification.isSparse`) and normalization
(`Cslib.Logic.PL.CNF.Sparsification.normalize`) are polynomial-time on the framed encoding of
formulas (`Cslib.Logic.PL.encCNFOver`), for any encoding of the variables. The width `k` is fixed,
so a clause has a constant number of candidate hearts; the thresholds enter only through
comparisons `θ j ≤ n`, which must themselves be polynomial-time in unary. They are for the
explicit thresholds (`Cslib.Logic.PL.ClauseSet.Sparsification.computableInPolyTime_threshold_le`).

The thresholds may also be read from a runtime parameter `p`, as `θ p`: the `…With` certificates
take the parameter as part of the input and charge its encoding, so one machine serves every
parameter value. The certificates for fixed thresholds are their specializations to a constant
parameter.

## Main definitions

* `Cslib.Logic.PL.CNF.Sparsification.encUnaryComparison`: the input of a threshold comparison,
  with a runtime parameter.
* `Cslib.Logic.PL.CNF.Sparsification.encCandidate`: a candidate pair of a clause size and a heart.

## Main results

* `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_nextWith`,
  `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_next`: the step, for runtime and fixed
  thresholds.
* `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_isSparseWith`,
  `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_isSparse`: the test for sparseness.
* `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_heavyWith`,
  `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_choiceWith`: the heavy-heart test and the
  choice, for runtime thresholds.
* `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_childAtChoiceWith`: a child at the
  computed choice, for runtime thresholds; shared with the counting step.
* `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_normalize`: normalization.
* `Cslib.Logic.PL.ClauseSet.Sparsification.computableInPolyTime_threshold_le`: comparisons
  with the explicit thresholds.

## References

* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
-/

@[expose] public section

open Turing.MultiTapeTM ComputableInPolyTime

namespace Cslib.Logic.PL.ClauseSet.Sparsification

/-- Comparing the explicit thresholds with a number is polynomial-time in unary. -/
theorem computableInPolyTime_threshold_le (k α : ℕ) :
    ComputableInPolyTime (fun p : ℕ × ℕ => decide (threshold k α p.1 ≤ p.2))
      (encPair encUnary encUnary) encBool := by
  have h : (fun p : ℕ × ℕ => decide (threshold k α p.1 ≤ p.2)) = fun p =>
      if p.1 = 0 then decide (1 ≤ p.2) else decide (α * base k α ^ (2 * p.1 - 1) ≤ p.2) := by
    funext p
    unfold threshold
    split_ifs <;> rfl
  rw [h]
  fun_prop

end Cslib.Logic.PL.ClauseSet.Sparsification

namespace Cslib.Logic.PL.CNF.Sparsification

/-- The input `(p, j, n)` of a threshold comparison `θ p j ≤ n`, with `j` and `n` in unary: the
framed runtime parameter `p`, then the framed `j`, then `n`. -/
abbrev encUnaryComparison {P : Type} (encP : P ↪ List Bool) : P × ℕ × ℕ ↪ List Bool :=
  encPair encP (encPair encUnary encUnary)

/-- A candidate `(c, H)` of a clause size and a heart, with `c` in unary: the framed `c`, then the
heart `H` as a clause (`encClause encV`). -/
abbrev encCandidate {V : Type} (encV : V ↪ List Bool) : ℕ × Clause V ↪ List Bool :=
  encPair encUnary (encClause encV)

variable {V : Type} [DecidableEq V] (encV : V ↪ List Bool)

/-- The framed encoding of clauses. -/
local notation "encC" => encClause encV

/-- The framed encoding of formulas. -/
local notation "encF" => encCNFOver encV

/-- The list-level reduction is polynomial-time. -/
theorem computableInPolyTime_reduce :
    ComputableInPolyTime (reduce (V := V)) encF encF := by
  unfold reduce subclause
  fun_prop

/-- Removing duplicate clauses with identical literal sets is polynomial-time. -/
theorem computableInPolyTime_dedupClauses :
    ComputableInPolyTime (dedupClauses (V := V)) encF encF := by
  unfold dedupClauses subclause
  fun_prop

/-- Computing the flower of a clause size and heart is polynomial-time. -/
theorem computableInPolyTime_flower :
    ComputableInPolyTime (fun p : CNF V × (ℕ × Clause V) => flower p.1 p.2.1 p.2.2)
      (encPair encF (encCandidate encV)) encF := by
  unfold flower subclause
  fun_prop

/-- **Testing a candidate against runtime thresholds.** Testing whether a candidate `(c, H)` is
heavy for thresholds `θ p` read from a runtime parameter `p` is polynomial-time, charging the
encoding of `p`. -/
theorem computableInPolyTime_heavyWith {P : Type} {encP : P ↪ List Bool} {θ : P → ℕ → ℕ}
    (hθ : ComputableInPolyTime (fun x : P × ℕ × ℕ => decide (θ x.1 x.2.1 ≤ x.2.2))
      (encUnaryComparison encP) encBool) :
    ComputableInPolyTime (fun x : P × (CNF V × (ℕ × Clause V)) => heavy (θ x.1) x.2.1 x.2.2)
      (encPair encP (encPair encF (encCandidate encV))) encBool := by
  have := computableInPolyTime_flower encV
  have h₁ : ComputableInPolyTime (fun x : P × (CNF V × (ℕ × Clause V)) =>
      decide (1 ≤ x.2.2.2.length) && decide (x.2.2.2.length < x.2.2.1))
      (encPair encP (encPair encF (encPair encUnary encC))) encBool := by
    fun_prop
  have h₂ : ComputableInPolyTime (fun x : P × (CNF V × (ℕ × Clause V)) =>
      (x.1, (x.2.2.1 - x.2.2.2.length, (flower x.2.1 x.2.2.1 x.2.2.2).length)))
      (encPair encP (encPair encF (encPair encUnary encC)))
      (encPair encP (encPair encUnary encUnary)) := by
    fun_prop
  exact bool_and.comp (h₁.prod (hθ.comp h₂))

/-- A fixed threshold comparison, read through a constant runtime parameter. This specializes the
`…With` certificates to fixed thresholds. -/
theorem computableInPolyTime_const_threshold {θ : ℕ → ℕ}
    (hθ : ComputableInPolyTime (fun p : ℕ × ℕ => decide (θ p.1 ≤ p.2))
      (encPair encUnary encUnary) encBool) :
    ComputableInPolyTime (fun x : ℕ × ℕ × ℕ => decide ((fun _ : ℕ => θ) x.1 x.2.1 ≤ x.2.2))
      (encUnaryComparison encUnary) encBool :=
  hθ.comp (snd encUnary (encPair encUnary encUnary))

/-- Testing whether a candidate `(c, H)` is heavy is polynomial-time. -/
theorem computableInPolyTime_heavy {θ : ℕ → ℕ}
    (hθ : ComputableInPolyTime (fun p : ℕ × ℕ => decide (θ p.1 ≤ p.2))
      (encPair encUnary encUnary) encBool) :
    ComputableInPolyTime (fun p : CNF V × (ℕ × Clause V) => heavy θ p.1 p.2)
      (encPair encF (encCandidate encV)) encBool := by
  have h := computableInPolyTime_heavyWith encV (P := ℕ) (encP := encUnary) (θ := fun _ => θ)
    (computableInPolyTime_const_threshold hθ)
  simpa only [Function.comp_def] using h.comp ((const (encOut := encUnary) 0).prod id')

omit [DecidableEq V] in
/-- Listing the candidate pairs `(c, H)` of a formula is polynomial-time. -/
theorem computableInPolyTime_candidates (k : ℕ) :
    ComputableInPolyTime (candidates (V := V) k) encF (encList (encCandidate encV)) := by
  have : ComputableInPolyTime (hearts (V := V) k) encC (encList encC) := by
    unfold hearts
    refine mapWithInput (const (encOut := encList (encList encUnary)) _) ?_
    fun_prop
  unfold candidates
  fun_prop

/-- **The choice for runtime thresholds** is polynomial-time, charging the encoding of the
parameter. -/
theorem computableInPolyTime_choiceWith {P : Type} {encP : P ↪ List Bool} {θ : P → ℕ → ℕ}
    (hθ : ComputableInPolyTime (fun x : P × ℕ × ℕ => decide (θ x.1 x.2.1 ≤ x.2.2))
      (encUnaryComparison encP) encBool) (k : ℕ) :
    ComputableInPolyTime (fun x : P × CNF V => choice (θ x.1) k x.2)
      (encPair encP encF) (encCandidate encV) := by
  have hheavy := computableInPolyTime_heavyWith encV hθ
  have hc : ComputableInPolyTime
      (fun x : P × CNF V => (candidates k x.2).filter (heavy (θ x.1) x.2))
      (encPair encP encF) (encList (encPair encUnary encC)) :=
    filterWithInput ((computableInPolyTime_candidates encV k).comp (snd _ _))
      (hheavy.comp ((fst _ _).fst'.prod ((fst _ _).snd'.prod (snd _ _))))
  have hr : ComputableInPolyTime (fun x : ℕ × Clause V => rank k x) (encPair encUnary encC)
      encUnary := by
    unfold rank
    fun_prop
  have hb : ComputableInPolyTime (fun x : P × CNF V =>
      (List.range ((k + 1) * (k + 1) + 1)).flatMap fun r =>
        ((candidates k x.2).filter (heavy (θ x.1) x.2)).filter fun x => rank k x == r)
      (encPair encP encF) (encList (encPair encUnary encC)) :=
    flatMapWithInput (const (encOut := encList encUnary) _)
      (filterWithInput (hc.comp (fst _ _)) ((hr.comp (snd _ _)).beq (fst _ _).snd'))
  exact optionGetDWithInput ((head? (encPair encUnary encC)
    (encL := encList (encPair encUnary encC))).comp hb) (const (0, []))

/-- The computed choice is polynomial-time. -/
theorem computableInPolyTime_choice {θ : ℕ → ℕ}
    (hθ : ComputableInPolyTime (fun p : ℕ × ℕ => decide (θ p.1 ≤ p.2))
      (encPair encUnary encUnary) encBool) (k : ℕ) :
    ComputableInPolyTime (choice (V := V) θ k) encF (encCandidate encV) := by
  have h := computableInPolyTime_choiceWith encV (P := ℕ) (encP := encUnary) (θ := fun _ => θ)
    (computableInPolyTime_const_threshold hθ) k
  simpa only [Function.comp_def] using h.comp ((const (encOut := encUnary) 0).prod id')

/-- **The test for sparseness against runtime thresholds** is polynomial-time, charging the
encoding of the parameter. -/
theorem computableInPolyTime_isSparseWith {P : Type} {encP : P ↪ List Bool} {θ : P → ℕ → ℕ}
    (hθ : ComputableInPolyTime (fun x : P × ℕ × ℕ => decide (θ x.1 x.2.1 ≤ x.2.2))
      (encUnaryComparison encP) encBool) (k : ℕ) :
    ComputableInPolyTime (fun x : P × CNF V => isSparse (θ x.1) k x.2)
      (encPair encP encF) encBool := by
  have hheavy := computableInPolyTime_heavyWith encV hθ
  unfold isSparse
  exact bool_not.comp (anyWithInput ((computableInPolyTime_candidates encV k).comp (snd _ _))
    (hheavy.comp ((fst _ _).fst'.prod ((fst _ _).snd'.prod (snd _ _)))))

/-- The list-level test for sparseness is polynomial-time. -/
theorem computableInPolyTime_isSparse {θ : ℕ → ℕ}
    (hθ : ComputableInPolyTime (fun p : ℕ × ℕ => decide (θ p.1 ≤ p.2))
      (encPair encUnary encUnary) encBool) (k : ℕ) :
    ComputableInPolyTime (isSparse (V := V) θ k) encF encBool := by
  have h := computableInPolyTime_isSparseWith encV (P := ℕ) (encP := encUnary) (θ := fun _ => θ)
    (computableInPolyTime_const_threshold hθ) k
  simpa only [Function.comp_def] using h.comp ((const (encOut := encUnary) 0).prod id')

/-- **A step at the computed choice for runtime thresholds** is polynomial-time: if computing a
child `f ψ c H b` of a node for a supplied choice `(c, H)` is polynomial-time, then so is computing
the child for the computed choice `choice (θ p) k ψ`, charging the encoding of the parameter `p`.
This is shared by the step `next` and the counting step `countingNext`. -/
theorem computableInPolyTime_childAtChoiceWith {P : Type} {encP : P ↪ List Bool}
    {θ : P → ℕ → ℕ}
    (hθ : ComputableInPolyTime (fun x : P × ℕ × ℕ => decide (θ x.1 x.2.1 ≤ x.2.2))
      (encUnaryComparison encP) encBool) (k : ℕ) {f : CNF V → ℕ → Clause V → Bool → CNF V}
    (hf : ComputableInPolyTime
      (fun x : CNF V × ((ℕ × Clause V) × Bool) => f x.1 x.2.1.1 x.2.1.2 x.2.2)
      (encPair encF (encPair (encCandidate encV) encBool)) encF) :
    ComputableInPolyTime
      (fun x : P × (CNF V × Bool) =>
        f x.2.1 (choice (θ x.1) k x.2.1).1 (choice (θ x.1) k x.2.1).2 x.2.2)
      (encPair encP (encPair encF encBool)) encF := by
  have hchoice : ComputableInPolyTime
      (fun x : P × (CNF V × Bool) => choice (θ x.1) k x.2.1)
      (encPair encP (encPair encF encBool)) (encCandidate encV) := by
    simpa only [Function.comp_def] using (computableInPolyTime_choiceWith encV hθ k).comp
      ((fst encP (encPair encF encBool)).prod (snd encP (encPair encF encBool)).fst')
  simpa only [Function.comp_def] using hf.comp ((snd encP (encPair encF encBool)).fst'.prod
    (hchoice.prod (snd encP (encPair encF encBool)).snd'))

/-- A child of a branching node, for a supplied choice, is polynomial-time. -/
private theorem computableInPolyTime_child :
    ComputableInPolyTime
      (fun x : CNF V × ((ℕ × Clause V) × Bool) => child x.1 x.2.1.1 x.2.1.2 x.2.2)
      (encPair encF (encPair (encCandidate encV) encBool)) encF := by
  have := computableInPolyTime_reduce encV
  have := computableInPolyTime_flower encV
  unfold child intro petals
  fun_prop

/-- **The list-level step for runtime thresholds** is polynomial-time, charging the encoding of the
parameter. -/
theorem computableInPolyTime_nextWith {P : Type} {encP : P ↪ List Bool} {θ : P → ℕ → ℕ}
    (hθ : ComputableInPolyTime (fun x : P × ℕ × ℕ => decide (θ x.1 x.2.1 ≤ x.2.2))
      (encUnaryComparison encP) encBool) (k : ℕ) :
    ComputableInPolyTime (fun x : P × (CNF V × Bool) => next (θ x.1) k x.2.1 x.2.2)
      (encPair encP (encPair encF encBool)) encF :=
  computableInPolyTime_childAtChoiceWith encV hθ k (f := child) (computableInPolyTime_child encV)

/-- **The list-level step is polynomial-time.** -/
theorem computableInPolyTime_next {θ : ℕ → ℕ}
    (hθ : ComputableInPolyTime (fun p : ℕ × ℕ => decide (θ p.1 ≤ p.2))
      (encPair encUnary encUnary) encBool) (k : ℕ) :
    ComputableInPolyTime (fun p : CNF V × Bool => next θ k p.1 p.2)
      (encPair encF encBool) encF := by
  have h := computableInPolyTime_nextWith encV (P := ℕ) (encP := encUnary) (θ := fun _ => θ)
    (computableInPolyTime_const_threshold hθ) k
  simpa only [Function.comp_def] using h.comp ((const (encOut := encUnary) 0).prod id')

/-- Normalization is polynomial-time. -/
theorem computableInPolyTime_normalize :
    ComputableInPolyTime (normalize (V := V)) encF encF := by
  have := computableInPolyTime_reduce encV
  have := computableInPolyTime_dedupClauses encV
  have hdedup : ComputableInPolyTime (dedup (V := V)) encC encC := by
    unfold dedup
    fun_prop
  unfold normalize
  fun_prop

end Cslib.Logic.PL.CNF.Sparsification

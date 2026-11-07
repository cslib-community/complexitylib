/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SharpDNF.KarpLubyMadras
public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.Repeat
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Logics.Propositional.CNF.PolyTime
import Mathlib.Data.List.GetD

/-!
# The Karp–Luby–Madras estimator runs in probabilistic polynomial time

Formulas in disjunctive normal form over variables numbered by `ℕ` are encoded as lists of terms,
each a list of literals with the variable in binary (`Cslib.Complexity.encDNF`, the same encoding
as `Cslib.Complexity.encCNF` for formulas in conjunctive normal form). On this encoding:

* every deterministic ingredient of a trial is polynomial-time: term widths and consistency, the
  minimum width of a consistent term, the padding of a term (all in unary), and the acceptance
  test, which reads the padding coins and evaluates the formula under the forced assignment;
* one trial (`Cslib.Complexity.KarpLubyMadras.isPPTOn_trial`) is a strict probabilistic
  polynomial-time program: a dyadic index, then a unary number of fair coins;
* the estimator (`Cslib.Complexity.KarpLubyMadras.isPPTOn_estimate`) is a strict probabilistic
  polynomial-time program on the formula and the unary parameters `p` and `t`: it runs
  `dyadicSize m * 3 (t + 1) p ^ 2` trials and writes its estimate in binary.

## Main results

* `Cslib.Complexity.KarpLubyMadras.computableInPolyTime_minWidth`,
  `Cslib.Complexity.KarpLubyMadras.computableInPolyTime_accepts`: the deterministic parts.
* `Cslib.Complexity.KarpLubyMadras.isPPTOn_trial`: one trial.
* `Cslib.Complexity.KarpLubyMadras.isPPTOn_estimate`: the estimator.
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Terms over natural-number variables: lists of literals, a variable in binary and a sign. -/
abbrev encTerm : Term ℕ ↪ List Bool := encList (encPair encNat encBool)

/-- Formulas in disjunctive normal form over natural-number variables: lists of terms. -/
abbrev encDNF : DNF ℕ ↪ List Bool := encList encTerm

namespace KarpLubyMadras

open Cslib.Probability

/-! ### Forced evaluation -/

/-- The data of a forced assignment: a term, a list of variables and a word. -/
private abbrev Ctx := (Term ℕ × List ℕ) × List Bool

private abbrev encCtx : Ctx ↪ List Bool := encPair (encPair encTerm (encList encNat)) encBits

private def ctxValue (c : Ctx) (v : ℕ) : Bool :=
  c.1.1.force (wordAssignment c.1.2 c.2) v

private theorem computableInPolyTime_ctxValue : ComputableInPolyTime
    (fun p : Ctx × ℕ => ctxValue p.1 p.2) (encPair encCtx encNat) encBool := by
  unfold ctxValue Term.force wordAssignment
  fun_prop

attribute [local fun_prop] computableInPolyTime_ctxValue

private def litValue (c : Ctx) (l : Literal ℕ) : Bool := Literal.eval (ctxValue c) l
private def termValue (c : Ctx) (t : Term ℕ) : Bool := Term.eval (ctxValue c) t
private def dnfValue (c : Ctx) (φ : DNF ℕ) : Bool := DNF.eval (ctxValue c) φ

private theorem computableInPolyTime_litValue : ComputableInPolyTime
    (fun p : Ctx × Literal ℕ => litValue p.1 p.2) (encPair encCtx (encPair encNat encBool))
    encBool := by
  unfold litValue Literal.eval
  fun_prop

attribute [local fun_prop] computableInPolyTime_litValue

private theorem computableInPolyTime_termValue : ComputableInPolyTime
    (fun p : Ctx × Term ℕ => termValue p.1 p.2) (encPair encCtx encTerm) encBool := by
  have : (fun p : Ctx × Term ℕ => termValue p.1 p.2) = fun p => p.2.all (litValue p.1) := rfl
  rw [this]
  fun_prop

attribute [local fun_prop] computableInPolyTime_termValue

private theorem computableInPolyTime_dnfValue : ComputableInPolyTime
    (fun p : Ctx × DNF ℕ => dnfValue p.1 p.2) (encPair encCtx encDNF) encBool := by
  have : (fun p : Ctx × DNF ℕ => dnfValue p.1 p.2) = fun p => p.2.any (termValue p.1) := rfl
  rw [this]
  fun_prop

attribute [local fun_prop] computableInPolyTime_dnfValue

/-- The context of term `i` of `φ` on the word `w`. -/
private def context (q : DNF ℕ × ℕ × List Bool) : Ctx :=
  ((q.1.getD q.2.1 [], CNF.distinctVars q.1), q.2.2)

private theorem computableInPolyTime_context : ComputableInPolyTime context
    (encPair encDNF (encPair encUnary encBits)) encCtx := by
  unfold context
  fun_prop

attribute [local fun_prop] computableInPolyTime_context

private theorem computableInPolyTime_firstHit_proj : ComputableInPolyTime
    (fun q : DNF ℕ × ℕ × List Bool => firstHit q.1 q.2.1 q.2.2)
    (encPair encDNF (encPair encUnary encBits)) encBool := by
  have : (fun q : DNF ℕ × ℕ × List Bool => firstHit q.1 q.2.1 q.2.2) = fun q =>
      termValue (context q) (q.1.getD q.2.1 []) && !dnfValue (context q) (q.1.take q.2.1) := rfl
  rw [this]
  fun_prop

attribute [local fun_prop] computableInPolyTime_firstHit_proj

/-- Testing for the first satisfied term is polynomial-time, with the index in unary. -/
theorem computableInPolyTime_firstHit : ComputableInPolyTime
    (Function.uncurry fun φ : DNF ℕ => Function.uncurry (firstHit φ))
    (encPair encDNF (encPair encUnary encBits)) encBool :=
  computableInPolyTime_firstHit_proj

/-! ### Widths and padding -/

/-- The width of a term, in unary. -/
theorem computableInPolyTime_width :
    ComputableInPolyTime (Term.width (V := ℕ)) encTerm encUnary := by
  have : (Term.width (V := ℕ)) = fun t => CNF.numVars [t] := by
    funext t
    simp [Term.width, CNF.numVars, CNF.vars]
  rw [this]
  have h := CNF.computableInPolyTime_numVars encNat
  fun_prop

attribute [local fun_prop] computableInPolyTime_width

/-- Consistency of a term. -/
theorem computableInPolyTime_consistent :
    ComputableInPolyTime (Term.consistent (V := ℕ)) encTerm encBool := by
  unfold Term.consistent
  fun_prop

attribute [local fun_prop] computableInPolyTime_consistent

private def belowWidths (φ : DNF ℕ) (k : ℕ) : Bool :=
  φ.all fun t => !t.consistent || decide (k < t.width)

private theorem computableInPolyTime_belowWidths : ComputableInPolyTime
    (fun p : DNF ℕ × ℕ => belowWidths p.1 p.2) (encPair encDNF encUnary) encBool := by
  unfold belowWidths
  fun_prop

attribute [local fun_prop] computableInPolyTime_belowWidths

/-- The minimum width of a consistent term, in unary. -/
theorem computableInPolyTime_minWidth :
    ComputableInPolyTime (minWidth (V := ℕ)) encDNF encUnary := by
  have : (minWidth (V := ℕ)) = fun φ => (List.range (CNF.numVars φ)).countP (belowWidths φ) := rfl
  rw [this]
  have h := CNF.computableInPolyTime_numVars encNat
  fun_prop

attribute [local fun_prop] computableInPolyTime_minWidth

/-- The padding of term `i`, in unary. -/
theorem computableInPolyTime_padding : ComputableInPolyTime
    (fun p : DNF ℕ × ℕ => padding p.1 p.2) (encPair encDNF encUnary) encUnary := by
  unfold padding
  fun_prop

attribute [local fun_prop] computableInPolyTime_padding

private theorem computableInPolyTime_accepts_proj : ComputableInPolyTime
    (fun q : DNF ℕ × ℕ × List Bool => accepts q.1 q.2.1 q.2.2)
    (encPair encDNF (encPair encUnary encBits)) encBool := by
  have : (fun q : DNF ℕ × ℕ × List Bool => accepts q.1 q.2.1 q.2.2) = fun q =>
      !(q.2.2.take (padding q.1 q.2.1)).any id &&
        firstHit q.1 q.2.1 (q.2.2.drop (padding q.1 q.2.1)) := rfl
  rw [this]
  have hpad : ComputableInPolyTime (fun q : DNF ℕ × ℕ × List Bool => padding q.1 q.2.1)
      (encPair encDNF (encPair encUnary encBits)) encUnary := by fun_prop
  have hlist : ComputableInPolyTime
      (fun q : DNF ℕ × ℕ × List Bool => q.2.2.take (padding q.1 q.2.1))
      (encPair encDNF (encPair encUnary encBits)) encBits := by fun_prop
  have htake : ComputableInPolyTime
      (fun q : DNF ℕ × ℕ × List Bool => (q.2.2.take (padding q.1 q.2.1)).any id)
      (encPair encDNF (encPair encUnary encBits)) encBool :=
    ComputableInPolyTime.bitsAnyWithInput (test := fun _ b => b) hlist
      (ComputableInPolyTime.snd _ _)
  have hdrop : ComputableInPolyTime
      (fun q : DNF ℕ × ℕ × List Bool => (q.1, q.2.1, q.2.2.drop (padding q.1 q.2.1)))
      (encPair encDNF (encPair encUnary encBits)) (encPair encDNF (encPair encUnary encBits)) := by
    fun_prop
  have hhit := computableInPolyTime_firstHit_proj.comp hdrop
  fun_prop

attribute [local fun_prop] computableInPolyTime_accepts_proj

/-- The acceptance test of one trial, with the index in unary. -/
theorem computableInPolyTime_accepts : ComputableInPolyTime
    (Function.uncurry fun φ : DNF ℕ => Function.uncurry (accepts φ))
    (encPair encDNF (encPair encUnary encBits)) encBool :=
  computableInPolyTime_accepts_proj

/-! ### Probabilistic polynomial time -/

private theorem computableInPolyTime_accepts_pair : ComputableInPolyTime
    (fun r : (DNF ℕ × ℕ) × List Bool => accepts r.1.1 r.1.2 r.2)
    (encPair (encPair encDNF encUnary) encBits) encBool := by
  have hreshape : ComputableInPolyTime
      (fun r : (DNF ℕ × ℕ) × List Bool => (r.1.1, r.1.2, r.2))
      (encPair (encPair encDNF encUnary) encBits) (encPair encDNF (encPair encUnary encBits)) := by
    fun_prop
  exact ComputableInPolyTime.comp
    (f := fun q : DNF ℕ × ℕ × List Bool => accepts q.1 q.2.1 q.2.2)
    (g := fun r : (DNF ℕ × ℕ) × List Bool => (r.1.1, r.1.2, r.2))
    computableInPolyTime_accepts_proj hreshape

private theorem isPPTOn_branch : IsPPTOn (encPair encDNF encUnary) encBool (fun q : DNF ℕ × ℕ =>
    if q.2 < q.1.length then
      accepts q.1 q.2 <$> BitString.sampleList (padding q.1 q.2 + CNF.numVars q.1)
    else pure false) := by
  have hcond : ComputableInPolyTime (fun q : DNF ℕ × ℕ => decide (q.2 < q.1.length))
      (encPair encDNF encUnary) encBool := by fun_prop
  have hcount : ComputableInPolyTime (fun q : DNF ℕ × ℕ => padding q.1 q.2 + CNF.numVars q.1)
      (encPair encDNF encUnary) encUnary := by
    have h := CNF.computableInPolyTime_numVars encNat
    fun_prop
  exact IsPPTOn.ite' (condition := fun q : DNF ℕ × ℕ => q.2 < q.1.length) hcond
    (IsPPTOn.of_seeded (f := fun r : (DNF ℕ × ℕ) × List Bool => accepts r.1.1 r.1.2 r.2) hcount
      computableInPolyTime_accepts_pair)
    (ComputableInPolyTime.const false).isPPTOn

/-- **One trial is a strict probabilistic polynomial-time program.** -/
theorem isPPTOn_trial : IsPPTOn encDNF encBool (trial (V := ℕ)) :=
  IsPPTOn.bind_with (first := fun φ : DNF ℕ => ProbComp.sampleDyadicIndex φ.length)
    (second := fun φ i => if i < φ.length then
      accepts φ i <$> BitString.sampleList (padding φ i + CNF.numVars φ) else pure false)
    (isPPTOn_sampleDyadicIndex (CNF.computableInPolyTime_length ComputableInPolyTime.id'))
    isPPTOn_branch

private theorem computableInPolyTime_trialBudget_proj : ComputableInPolyTime
    (fun x : DNF ℕ × ℕ × ℕ => trialBudget x.1 x.2.1 x.2.2)
    (encPair encDNF (encPair encUnary encUnary)) encUnary := by
  unfold trialBudget
  have hlen : ComputableInPolyTime (fun x : DNF ℕ × ℕ × ℕ => x.1.length)
      (encPair encDNF (encPair encUnary encUnary)) encUnary :=
    CNF.computableInPolyTime_length (ComputableInPolyTime.fst _ _)
  fun_prop

/-- The number of trials, in unary. -/
theorem computableInPolyTime_trialBudget : ComputableInPolyTime
    (Function.uncurry fun φ : DNF ℕ => Function.uncurry (trialBudget φ))
    (encPair encDNF (encPair encUnary encUnary)) encUnary :=
  computableInPolyTime_trialBudget_proj

/-- **The Karp–Luby–Madras estimator is a strict probabilistic polynomial-time program** on the
formula and the unary parameters `p` and `t`, with the estimate written in binary. -/
theorem isPPTOn_estimate : IsPPTOn (encPair encDNF (encPair encUnary encUnary))
    (encPair encNat encNat) (Function.uncurry fun φ : DNF ℕ => Function.uncurry (estimate φ)) := by
  have hcount : IsPPTOn (encPair encDNF (encPair encUnary encUnary)) encUnary
      (fun x : DNF ℕ × ℕ × ℕ => OracleComp.countTrue (trialBudget x.1 x.2.1 x.2.2) (trial x.1)) :=
    IsPPTOn.countTrue (program := fun x : DNF ℕ × ℕ × ℕ => trial x.1)
      (IsPPTOn.preprocess (program := trial) (prepare := fun x : DNF ℕ × ℕ × ℕ => x.1)
        isPPTOn_trial (ComputableInPolyTime.fst _ _)) computableInPolyTime_trialBudget_proj
  have hout : ComputableInPolyTime
      (fun r : (DNF ℕ × ℕ × ℕ) × ℕ =>
        (r.2 * 2 ^ (CNF.numVars r.1.1 - minWidth r.1.1), 3 * (r.1.2.2 + 1) * r.1.2.1 ^ 2))
      (encPair (encPair encDNF (encPair encUnary encUnary)) encUnary)
      (encPair encNat encNat) := by
    have hnv := CNF.computableInPolyTime_numVars encNat
    have hub : ComputableInPolyTime (fun n : ℕ => n) encUnary encNat :=
      .of_tidy ComputableTidilyInPolyTime.unary_to_binary
    fun_prop
  exact IsPPTOn.map_with (program := fun x : DNF ℕ × ℕ × ℕ =>
      OracleComp.countTrue (trialBudget x.1 x.2.1 x.2.2) (trial x.1))
    (f := fun x s => (s * 2 ^ (CNF.numVars x.1 - minWidth x.1), 3 * (x.2.2 + 1) * x.2.1 ^ 2))
    hcount hout

end KarpLubyMadras

end Cslib.Complexity

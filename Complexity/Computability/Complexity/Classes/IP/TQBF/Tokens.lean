/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP.TQBF.Protocol
import Complexity.Probability.PMF.Bind
import Mathlib.Algebra.Polynomial.Roots

/-!
# The interactive proof for quantified Boolean formulas, on a stream of tokens

A machine running the verifier of `Cslib.Complexity.QBFProtocol.verify` reads the arithmetic
formula as a list of tokens in prefix order (`Cslib.Logic.PL.ArithQBF.tokens`): the claims it has
still to check form a stack, and the claim on top of the stack is about the subformula whose tokens
start the remaining list. The arithmetization of a quantified Boolean formula `φ` has as tokens
those of `φ`, with the linearizations of the variables of `xs` inserted before every quantifier
(`Cslib.Logic.PL.QBF.tokens_arithmetize`).

This file gives the recursive form of that machine (`Cslib.Complexity.QBFProtocol.verifyAt`).
It differs from `Cslib.Complexity.QBFProtocol.verify` in two ways: it reads the same number
`D + 1` of coefficients in every round, so that it need not compute the degree of each body, and
its queries also carry the tokens that follow the current subformula, so that they determine the
remaining list of tokens of the machine. Its soundness bound uses the uniform degree: if the
syntactic largest round degree `maxRoundDegree e` is at most `D`, every prover is accepted on a
false claim with probability at most `ops e * D * ε` instead of `roundDegree e * ε`
(`Cslib.Complexity.QBFProtocol.acceptProb_verifyAt_le`), with `ops e` the number of operators. A
stateless prover whose replies agree with the true values and restrictions on every query about a
subformula all of whose variables lie in a list `xs` is accepted with certainty on every true
claim about a formula whose variables lie in `xs` and whose largest round degree
`maxRoundDegree e` is at most `D` (`Cslib.Complexity.QBFProtocol.run_verifyAt_of_agreesAt`).

## Main definitions

* `Cslib.Logic.PL.ArithQBF.Kind`, `Cslib.Logic.PL.ArithQBF.tokens`: the tokens of an arithmetic
  formula.
* `Cslib.Logic.PL.QBF.expandToken`: the tokens of the arithmetization for a token of a formula.
* `Cslib.Complexity.QBFProtocol.verifyAt`: the verifier with uniform degree and contextual queries.
* `Cslib.Complexity.QBFProtocol.honestReplyAt`: the honest replies.

## Main results

* `Cslib.Logic.PL.ArithQBF.tokens_append_inj`: tokens in prefix order determine the formula.
* `Cslib.Logic.PL.QBF.tokens_arithmetize`: the tokens of the arithmetization.
* `Cslib.Complexity.QBFProtocol.acceptProb_verifyAt_le`: soundness.
* `Cslib.Complexity.QBFProtocol.run_verifyAt_of_agreesAt`: perfect completeness.

## References

* [A. Shamir, *IP = PSPACE*][Shamir1992]
* [A. Shen, *IP = SPACE: simplified proof*][Shen1992]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Logic.PL

/-! ### Tokens -/

/-- The kinds of nodes of an arithmetic formula. -/
inductive ArithQBF.Kind where
  /-- A variable. -/
  | var
  /-- The constant `1`. -/
  | top
  /-- The constant `0`. -/
  | bot
  /-- Negation. -/
  | not
  /-- Conjunction. -/
  | and
  /-- Disjunction. -/
  | or
  /-- Existential quantification. -/
  | ex
  /-- Universal quantification. -/
  | all
  /-- Linearization. -/
  | lin
  deriving DecidableEq

instance : Fintype ArithQBF.Kind :=
  ⟨{.var, .top, .bot, .not, .and, .or, .ex, .all, .lin}, fun k => by cases k <;> simp⟩

namespace ArithQBF

/-- The tokens of an arithmetic formula in prefix order: the kind of each node, with its variable
for variables and operators, and `0` for the other nodes. -/
def tokens : ArithQBF ℕ → List (Kind × ℕ)
  | .var v => [(.var, v)]
  | .top => [(.top, 0)]
  | .bot => [(.bot, 0)]
  | .not e => (.not, 0) :: tokens e
  | .bin .and e₁ e₂ => (.and, 0) :: (tokens e₁ ++ tokens e₂)
  | .bin .or e₁ e₂ => (.or, 0) :: (tokens e₁ ++ tokens e₂)
  | .op .ex v e => (.ex, v) :: tokens e
  | .op .all v e => (.all, v) :: tokens e
  | .op .lin v e => (.lin, v) :: tokens e

/-- **Tokens in prefix order determine the formula**, and what follows them. -/
theorem tokens_append_inj {e e' : ArithQBF ℕ} {r r' : List (Kind × ℕ)}
    (h : e.tokens ++ r = e'.tokens ++ r') : e = e' ∧ r = r' := by
  induction e generalizing e' r r' with
  | var v =>
    rcases e' with _ | _ | _ | _ | ⟨_ | _, _, _⟩ | ⟨_ | _ | _, _, _⟩ <;> simp_all [tokens]
  | top =>
    rcases e' with _ | _ | _ | _ | ⟨_ | _, _, _⟩ | ⟨_ | _ | _, _, _⟩ <;> simp_all [tokens]
  | bot =>
    rcases e' with _ | _ | _ | _ | ⟨_ | _, _, _⟩ | ⟨_ | _ | _, _, _⟩ <;> simp_all [tokens]
  | not e ih =>
    rcases e' with _ | _ | _ | _ | ⟨_ | _, _, _⟩ | ⟨_ | _ | _, _, _⟩ <;>
      simp only [tokens, List.cons_append, List.cons.injEq, Prod.mk.injEq, reduceCtorEq,
        false_and] at h
    obtain ⟨-, h⟩ := h
    obtain ⟨rfl, rfl⟩ := ih h
    exact ⟨rfl, rfl⟩
  | bin o e₁ e₂ ih₁ ih₂ =>
    rcases o with _ | _ <;>
    rcases e' with _ | _ | _ | _ | ⟨_ | _, _, _⟩ | ⟨_ | _ | _, _, _⟩ <;>
      simp only [tokens, List.cons_append, List.cons.injEq, Prod.mk.injEq, reduceCtorEq,
        false_and, List.append_assoc] at h <;>
    · obtain ⟨-, h⟩ := h
      obtain ⟨rfl, h'⟩ := ih₁ h
      obtain ⟨rfl, rfl⟩ := ih₂ h'
      exact ⟨rfl, rfl⟩
  | op o v e ih =>
    rcases o with _ | _ | _ <;>
    rcases e' with _ | _ | _ | _ | ⟨_ | _, _, _⟩ | ⟨_ | _ | _, _, _⟩ <;>
      simp only [tokens, List.cons_append, List.cons.injEq, Prod.mk.injEq, reduceCtorEq,
        false_and, true_and] at h <;>
    · obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl⟩

/-- Linearizations come first in prefix order. -/
private theorem tokens_lins (xs : List ℕ) (e : ArithQBF ℕ) :
    (lins xs e).tokens = xs.map (fun x => (Kind.lin, x)) ++ e.tokens := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [lins_cons, tokens, ih, List.map_cons, List.cons_append]

end ArithQBF

namespace QBF

/-- The kind of the node of the arithmetization for a node of a quantified Boolean formula. -/
def Kind.arith : Kind → ArithQBF.Kind
  | .var => .var
  | .top => .top
  | .bot => .bot
  | .not => .not
  | .and => .and
  | .or => .or
  | .ex => .ex
  | .all => .all

/-- Whether a kind of nodes is a quantifier. -/
def Kind.isQuantifier : Kind → Bool
  | .ex => true
  | .all => true
  | _ => false

/-- The tokens of the arithmetization for a token of a formula: a quantifier is preceded by the
linearizations of the variables of `xs`. -/
def expandToken (xs : List ℕ) (t : Kind × ℕ) : List (ArithQBF.Kind × ℕ) :=
  (if t.1.isQuantifier then xs.map fun x => (ArithQBF.Kind.lin, x) else []) ++ [(t.1.arith, t.2)]

/-- **The tokens of the arithmetization** are those of the formula, with the linearizations of
the variables of `xs` inserted before every quantifier. -/
theorem tokens_arithmetize (xs : List ℕ) (φ : QBF ℕ) :
    (φ.arithmetize xs).tokens = φ.tokens.flatMap (expandToken xs) := by
  induction φ with
  | var v => rfl
  | top => rfl
  | bot => rfl
  | not φ ih => simp [arithmetize, ArithQBF.tokens, tokens, ih, expandToken, Kind.isQuantifier,
      Kind.arith]
  | and φ ψ ihφ ihψ => simp [arithmetize, ArithQBF.tokens, tokens, ihφ, ihψ, expandToken,
      Kind.isQuantifier, Kind.arith]
  | or φ ψ ihφ ihψ => simp [arithmetize, ArithQBF.tokens, tokens, ihφ, ihψ, expandToken,
      Kind.isQuantifier, Kind.arith]
  | ex v φ ih => simp [arithmetize, ArithQBF.tokens_lins, ArithQBF.tokens, tokens, ih,
      expandToken, Kind.isQuantifier, Kind.arith]
  | all v φ ih => simp [arithmetize, ArithQBF.tokens_lins, ArithQBF.tokens, tokens, ih,
      expandToken, Kind.isQuantifier, Kind.arith]

end QBF

end Cslib.Logic.PL

namespace Cslib.Complexity.QBFProtocol

open Cslib.Logic.PL Polynomial
open Cslib.ProbOracleComp (runWith acceptProbWith)
open scoped ENNReal

variable {F : Type}

/-! ### The verifier on a stream of tokens -/

/-- A query of the verifier on a stream of tokens: the current subformula, the tokens that follow
it, and the current point. -/
abbrev QueryAt (F : Type) := ArithQBF ℕ × List (ArithQBF.Kind × ℕ) × (ℕ → F)

variable [CommRing F] [DecidableEq F] (sampler : ProbComp F) (D : ℕ)

/-- **The verifier on a stream of tokens**, checking the claim that `e`, followed by the tokens
`rest`, has value `c` at `r`. It is `Cslib.Complexity.QBFProtocol.verify` with `D + 1`
coefficients read in every round and with the tokens `rest` sent along with every query. -/
def verifyAt : ArithQBF ℕ → List (ArithQBF.Kind × ℕ) → (ℕ → F) → F →
    ProbOracleComp (fun _ : QueryAt F => List F) Bool
  | .var v, _, r, c => pure (decide (r v = c))
  | .top, _, _, c => pure (decide (c = 1))
  | .bot, _, _, c => pure (decide (c = 0))
  | .not e, rest, r, c => verifyAt e rest r (1 - c)
  | .bin o e₁ e₂, rest, r, c => do
    let l ← ProbOracleComp.query (spec := fun _ : QueryAt F => List F) (.bin o e₁ e₂, rest, r)
    if o.apply (l.getD 0 0) (l.getD 1 0) = c then
      let b ← verifyAt e₁ (e₂.tokens ++ rest) r (l.getD 0 0)
      if b then verifyAt e₂ rest r (l.getD 1 0) else pure false
    else pure false
  | .op o v e, rest, r, c => do
    let l ← ProbOracleComp.query (spec := fun _ : QueryAt F => List F) (.op o v e, rest, r)
    let s := l.take (D + 1)
    if o.apply (r v) (evalCoeffList 0 s) (evalCoeffList 1 s) = c then
      let z ← ProbOracleComp.sample sampler
      verifyAt e rest (Function.update r v z) (evalCoeffList z s)
    else pure false

/-! ### Soundness -/

private theorem acceptProb_verifyAt_bin_le {ε : ℝ≥0∞} {S : Type}
    (respond : QueryAt F → StateT S PMF (List F)) (o : ArithQBF.Connective) (e₁ e₂ : ArithQBF ℕ)
    {rest : List (ArithQBF.Kind × ℕ)} {r : ℕ → F} {c : F}
    (hc : (ArithQBF.bin o e₁ e₂).eval r ≠ c)
    (ih₁ : ∀ {rest r c}, e₁.eval r ≠ c → ∀ s,
      acceptProbWith respond (verifyAt sampler D e₁ rest r c) s ≤ (e₁.ops * D : ℕ) * ε)
    (ih₂ : ∀ {rest r c}, e₂.eval r ≠ c → ∀ s,
      acceptProbWith respond (verifyAt sampler D e₂ rest r c) s ≤ (e₂.ops * D : ℕ) * ε)
    (s : S) :
    acceptProbWith respond (verifyAt sampler D (.bin o e₁ e₂) rest r c) s ≤
      ((ArithQBF.bin o e₁ e₂).ops * D : ℕ) * ε := by
  rw [verifyAt, ProbOracleComp.acceptProbWith_query_bind]
  refine Probability.PMF.tsum_mul_le_of_forall_le _ fun x => ?_
  split_ifs with hcheck
  · by_cases h₁ : e₁.eval r = x.1.getD 0 0
    · have h₂ : e₂.eval r ≠ x.1.getD 1 0 := fun h₂ =>
        hc (by rw [ArithQBF.eval_bin, h₁, h₂, hcheck])
      rw [ProbOracleComp.acceptProbWith_bind]
      refine (Probability.PMF.tsum_mul_le_of_forall_le (B := ((e₂.ops * D : ℕ) : ℝ≥0∞) * ε) _
        fun y => ?_).trans ?_
      · cases y.1
        · simp only [Bool.false_eq_true, ↓reduceIte, ProbOracleComp.acceptProbWith_pure]
          exact zero_le
        · simp only [↓reduceIte]
          exact ih₂ h₂ _
      · rw [ArithQBF.ops, Nat.add_mul, Nat.cast_add, add_mul]
        exact le_add_self
    · refine (ProbOracleComp.acceptProbWith_bind_ite_le respond _ _ _).trans ((ih₁ h₁ _).trans ?_)
      rw [ArithQBF.ops, Nat.add_mul, Nat.cast_add, add_mul]
      exact le_self_add
  · rw [ProbOracleComp.acceptProbWith_pure]
    exact zero_le

private theorem acceptProb_verifyAt_op_le [IsDomain F] {ε : ℝ≥0∞}
    (hsampler : ∀ z, ProbComp.eval sampler z ≤ ε) {S : Type}
    (respond : QueryAt F → StateT S PMF (List F)) (o : ArithQBF.Operator) (v : ℕ) (e : ArithQBF ℕ)
    (hdeg_e : e.degBound v ≤ D)
    {rest : List (ArithQBF.Kind × ℕ)} {r : ℕ → F} {c : F}
    (hc : (ArithQBF.op o v e).eval r ≠ c)
    (ih : ∀ {rest r c}, e.eval r ≠ c → ∀ s,
      acceptProbWith respond (verifyAt sampler D e rest r c) s ≤ (e.ops * D : ℕ) * ε)
    (s : S) :
    acceptProbWith respond (verifyAt sampler D (.op o v e) rest r c) s ≤
      ((ArithQBF.op o v e).ops * D : ℕ) * ε := by
  rw [verifyAt, ProbOracleComp.acceptProbWith_query_bind]
  refine Probability.PMF.tsum_mul_le_of_forall_le _ fun x => ?_
  dsimp only
  split_ifs with hcheck
  · rw [ProbOracleComp.acceptProbWith_sample_bind]
    set g := e.restrict r v
    set p := ofCoeffList (x.1.take (D + 1))
    have hp (z : F) : evalCoeffList z (x.1.take (D + 1)) = p.eval z := (eval_ofCoeffList z _).symm
    have hg (z : F) : g.eval z = e.eval (Function.update r v z) := e.eval_restrict r v z
    have hne : p - g ≠ 0 := fun h =>
      hc (by rw [ArithQBF.eval_op, ← hg, ← hg, ← sub_eq_zero.1 h, ← hp, ← hp, hcheck])
    have hdeg : (p - g).natDegree ≤ D :=
      (natDegree_sub_le _ _).trans (max_le ((natDegree_ofCoeffList_le _).trans (by
        rw [List.length_take]; omega)) ((e.natDegree_restrict_le r v).trans hdeg_e))
    classical
    have hcard : ((p - g).roots.toFinset.card : ℝ≥0∞) ≤ D := by
      exact_mod_cast (Multiset.toFinset_card_le _).trans ((card_roots' _).trans hdeg)
    refine (Probability.PMF.tsum_mul_le_card_mul_add _ hsampler (p - g).roots.toFinset
      (B := ((e.ops * D : ℕ) : ℝ≥0∞) * ε) fun z => ?_).trans ?_
    · by_cases hz : p.eval z = g.eval z
      · have : z ∈ (p - g).roots.toFinset := by
          rw [Multiset.mem_toFinset, mem_roots hne, IsRoot, eval_sub, hz, sub_self]
        simp only [this, ↓reduceIte]
        exact (ProbOracleComp.acceptProbWith_le_one _ _ _).trans le_self_add
      · rw [hp]
        exact (ih (fun h => hz (by rw [hg, h])) _).trans le_add_self
    · rw [ArithQBF.ops, Nat.add_mul, Nat.one_mul, Nat.cast_add, add_mul, add_comm]
      gcongr
  · rw [ProbOracleComp.acceptProbWith_pure]
    exact zero_le

/-- **Soundness of the verifier on a stream of tokens**: if the sampler gives every element
probability at most `ε` and the body of every operator of `e` has degree at most `D` in its
variable, every prover is accepted on a false claim with probability at most `ops e * D * ε`. -/
theorem acceptProb_verifyAt_le [IsDomain F] {ε : ℝ≥0∞}
    (hsampler : ∀ z, ProbComp.eval sampler z ≤ ε) {S : Type}
    (respond : QueryAt F → StateT S PMF (List F)) (e : ArithQBF ℕ) (hD : e.maxRoundDegree ≤ D)
    {rest : List (ArithQBF.Kind × ℕ)} {r : ℕ → F} {c : F} (hc : e.eval r ≠ c) (s : S) :
    acceptProbWith respond (verifyAt sampler D e rest r c) s ≤ (e.ops * D : ℕ) * ε := by
  induction e generalizing rest r c s with
  | var v =>
    rw [verifyAt, decide_eq_false (show r v ≠ c from hc), ProbOracleComp.acceptProbWith_pure]
    exact zero_le
  | top =>
    rw [verifyAt, decide_eq_false (show c ≠ 1 from Ne.symm hc), ProbOracleComp.acceptProbWith_pure]
    exact zero_le
  | bot =>
    rw [verifyAt, decide_eq_false (show c ≠ 0 from Ne.symm hc), ProbOracleComp.acceptProbWith_pure]
    exact zero_le
  | not e ih =>
    rw [verifyAt, ArithQBF.ops]
    exact ih hD (fun h => hc (by rw [ArithQBF.eval_not, h, sub_sub_cancel])) s
  | bin o e₁ e₂ ih₁ ih₂ =>
    rw [ArithQBF.maxRoundDegree, max_le_iff] at hD
    exact acceptProb_verifyAt_bin_le sampler D respond o e₁ e₂ hc (ih₁ hD.1) (ih₂ hD.2) s
  | op o v e ih =>
    rw [ArithQBF.maxRoundDegree, max_le_iff] at hD
    exact acceptProb_verifyAt_op_le sampler D hsampler respond o v e hD.1 hc (ih hD.2) s

/-! ### Completeness -/

/-- The honest reply to a query about `e` at `r`: the values of the two arguments of a binary
connective, and the `D + 1` first coefficients of the restriction of the body of an operator. -/
noncomputable def honestReplyAt (e : ArithQBF ℕ) (r : ℕ → F) : List F :=
  match e with
  | .bin _ e₁ e₂ => [e₁.eval r, e₂.eval r]
  | .op _ v e => coeffsBelow (e.restrict r v) (D + 1)
  | _ => []

/-- A reply agrees with the honest reply to a query about `e` at `r` on what the verifier reads:
the first two entries for a binary connective, the first `D + 1` for an operator. -/
def AgreesAt (l : List F) (e : ArithQBF ℕ) (r : ℕ → F) : Prop :=
  match e with
  | .bin _ e₁ e₂ => l.getD 0 0 = e₁.eval r ∧ l.getD 1 0 = e₂.eval r
  | .op _ v e => l.take (D + 1) = coeffsBelow (e.restrict r v) (D + 1)
  | _ => True

omit [DecidableEq F] in
theorem agreesAt_honestReplyAt (e : ArithQBF ℕ) (r : ℕ → F) :
    AgreesAt D (honestReplyAt D e r) e r := by
  cases e with
  | bin o e₁ e₂ => exact ⟨rfl, rfl⟩
  | op o v e => exact List.take_of_length_le (by rw [honestReplyAt, length_coeffsBelow])
  | _ => trivial

/-- **Perfect completeness of the verifier on a stream of tokens.** A stateless prover whose reply
to every query about a subformula all of whose variables lie in `xs` agrees with the honest reply
makes the verifier accept with certainty every true claim about a formula whose variables lie in
`xs` and whose operators have bodies of degree at most `D` in their variable. -/
theorem run_verifyAt_of_agreesAt (f : QueryAt F → List F) (xs : List ℕ)
    (hf : ∀ e' rest' r', (∀ w ∈ e'.vars, w ∈ xs) → AgreesAt D (f (e', rest', r')) e' r')
    (e : ArithQBF ℕ) (he : ∀ w ∈ e.vars, w ∈ xs) (hD : e.maxRoundDegree ≤ D)
    (rest : List (ArithQBF.Kind × ℕ)) (r : ℕ → F) (s : Unit) :
    runWith (fun q s => PMF.pure (f q, s)) (verifyAt sampler D e rest r (e.eval r)) s =
      PMF.pure (true, s) := by
  induction e generalizing rest r with
  | var v => simp only [verifyAt, ArithQBF.eval_var, decide_true, ProbOracleComp.runWith_pure]
  | top => simp only [verifyAt, ArithQBF.eval_top, decide_true, ProbOracleComp.runWith_pure]
  | bot => simp only [verifyAt, ArithQBF.eval_bot, decide_true, ProbOracleComp.runWith_pure]
  | not e ih => rw [verifyAt, ArithQBF.eval_not, sub_sub_cancel, ih he hD]
  | bin o e₁ e₂ ih₁ ih₂ =>
    rw [ArithQBF.maxRoundDegree, max_le_iff] at hD
    have he₁ : ∀ w ∈ e₁.vars, w ∈ xs := fun w hw => he w (List.mem_append_left _ hw)
    have he₂ : ∀ w ∈ e₂.vars, w ∈ xs := fun w hw => he w (List.mem_append_right _ hw)
    obtain ⟨h₁, h₂⟩ := hf (.bin o e₁ e₂) rest r he
    rw [verifyAt, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query]
    simp only [PMF.pure_bind, h₁, h₂, ArithQBF.eval_bin, ↓reduceIte]
    rw [ProbOracleComp.runWith_bind, ih₁ he₁ hD.1, PMF.pure_bind]
    exact ih₂ he₂ hD.2 _ r
  | op o v e ih =>
    rw [ArithQBF.maxRoundDegree, max_le_iff] at hD
    have he' : ∀ w ∈ e.vars, w ∈ xs := fun w hw => he w (List.mem_cons_of_mem v hw)
    have hlist : (f (.op o v e, rest, r)).take (D + 1) = coeffsBelow (e.restrict r v) (D + 1) :=
      hf (.op o v e) rest r he
    rw [verifyAt, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query]
    have hval (z : F) : evalCoeffList z (coeffsBelow (e.restrict r v) (D + 1)) =
        e.eval (Function.update r v z) := by
      rw [← eval_ofCoeffList, ofCoeffList_coeffsBelow (Nat.lt_succ_of_le
        ((e.natDegree_restrict_le r v).trans hD.1)), ArithQBF.eval_restrict]
    simp only [PMF.pure_bind, hlist, hval, ArithQBF.eval_op, ↓reduceIte]
    rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample, PMF.bind_map]
    simp only [Function.comp_def, ih he' hD.2]
    exact PMF.bind_const _ _

end Cslib.Complexity.QBFProtocol

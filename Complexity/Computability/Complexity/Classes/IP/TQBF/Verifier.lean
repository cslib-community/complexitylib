/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP
public import Complexity.Computability.Complexity.Classes.IP.TQBF.Words
public import Complexity.Computability.Complexity.Problems.TQBF.Closed
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import Complexity.Languages.Probabilistic.Iteration
public import Complexity.Languages.Probabilistic.Oracle.Support
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Prime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Search
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Probabilistic.Oracle.Composition
import Mathlib.NumberTheory.Bertrand

/-!
# The machine verifier for quantified Boolean formulas

The verifier of the interactive proof for `TQBF` as a program with fair coins and word messages,
realized by a strict oracle PPT machine (`Cslib.Complexity.QBFProtocol.isOraclePPTOn_verifier`).
On a formula `ψ` it rejects when `ψ` has a free variable. Otherwise it computes the list `xs` of
the variable components of all the tokens of `ψ`, with multiplicity and with `0` for the tokens
without a variable (`Cslib.Complexity.QBFProtocol.linVars`), which contains every variable of
`ψ`; the degree bound `D = 2 * size ψ`; and the greatest prime `p` at most `2 * B` for
`B = 12 * size ψ ^ 2 * (size ψ + 1)`, found by trial division
(`Cslib.Complexity.QBFProtocol.modulus`); by Bertrand's postulate `B < p`. It then runs a stack
machine over the tokens of the arithmetization of `ψ` that linearizes the variables of `xs` after
every quantifier (`Cslib.Complexity.QBFProtocol.Machine.loop`), one token per step
(`Cslib.Complexity.QBFProtocol.Machine.step`), checking the claim that the arithmetization has
value `1` at the origin over `ZMod p`:

* a state holds the remaining tokens, the stack of pending claims, each a point and a value, and
  whether every check so far passed;
* a variable or a constant checks the claim on top of the stack, and a negation replaces its value
  `c` by `1 - c`;
* a binary connective or an operator sends the remaining tokens and the point of the top claim,
  reads `D + 1` rows of `width p` bits of the reply, and proceeds as
  `Cslib.Complexity.QBFProtocol.verifyAt`; an operator draws its random point by
  `Cslib.Complexity.QBFProtocol.sampleMod`.

Points and values are rebuilt modulo `p` on the variables of `xs` whenever they are pushed, so that
every step adds at most a polynomial amount of storage
(`Cslib.Complexity.QBFProtocol.Machine.length_encVState_le_of_mem_support_step`).

## Main definitions

* `Cslib.Complexity.QBFProtocol.Machine.step`, `Cslib.Complexity.QBFProtocol.Machine.loop`: the
  stack machine.
* `Cslib.Complexity.QBFProtocol.loopInput`: the parameters and tokens computed from a formula.
* `Cslib.Complexity.QBFProtocol.verifier`: the verifier.

## Main results

* `Cslib.Complexity.QBFProtocol.lt_modulus`, `Cslib.Complexity.QBFProtocol.prime_modulus`: the
  modulus is a prime above the bound.
* `Cslib.Complexity.QBFProtocol.isOraclePPTOn_verifier`: the verifier is strict oracle PPT.

## References

* [A. Shamir, *IP = PSPACE*][Shamir1992]
* [A. Shen, *IP = SPACE: simplified proof*][Shen1992]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 8.3][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.QBFProtocol

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.Probability

namespace Machine

/-! ### States -/

instance : FinEnum ArithQBF.Kind :=
  FinEnum.ofList [.var, .top, .bot, .not, .and, .or, .ex, .all, .lin]
    fun k => by cases k <;> decide

/-- Tokens of arithmetic formulas, the kind framed before the variable in binary. -/
abbrev encArithToken : ArithQBF.Kind × ℕ ↪ List Bool :=
  encPair (encFinEnum ArithQBF.Kind) encNat

/-- Points as lists of pairs of a variable, in binary, and a value, in unary. -/
abbrev encPt : List (ℕ × ℕ) ↪ List Bool := encList (encPair encNat encUnary)

/-- The parameters of the machine: the variables `xs` linearized after every quantifier, the
modulus less one, so that the modulus is positive, and the degree bound `D` of every round. -/
abbrev Params := List ℕ × ℕ × ℕ

/-- The encoding of the parameters, the numbers in unary. -/
private abbrev encParams : Params ↪ List Bool :=
  encPair (encList encNat) (encPair encUnary encUnary)

/-- The input of the loop: the parameters and the tokens of the arithmetic formula. -/
abbrev LoopInput := Params × List (ArithQBF.Kind × ℕ)

/-- The encoding of the input of the loop. -/
private abbrev encLoopInput : LoopInput ↪ List Bool :=
  encPair encParams (encList encArithToken)

/-- A pending claim: a point and a value. -/
abbrev Claim := List (ℕ × ℕ) × ℕ

/-- The encoding of a claim, its value in unary. -/
abbrev encClaim : Claim ↪ List Bool := encPair encPt encUnary

/-- A state of the machine: the remaining tokens, the stack of pending claims, and whether every
check so far passed. -/
abbrev VState := List (ArithQBF.Kind × ℕ) × List Claim × Bool

/-- The encoding of the states. -/
abbrev encVState : VState ↪ List Bool :=
  encPair (encList encArithToken) (encPair (encList encClaim) encBool)

/-- The data of a step: the input of the loop and the current state. -/
abbrev StepData := LoopInput × VState

/-- The encoding of the data of a step. -/
private abbrev encStepData : StepData ↪ List Bool := encPair encLoopInput encVState

namespace StepData

/-- The variables linearized after every quantifier. -/
def xs (a : StepData) : List ℕ := a.1.1.1

/-- The modulus, which is positive. -/
def modulus (a : StepData) : ℕ := a.1.1.2.1 + 1

instance (a : StepData) : NeZero a.modulus := ⟨Nat.succ_ne_zero _⟩

/-- The degree bound of every round. -/
def degree (a : StepData) : ℕ := a.1.1.2.2

/-- The next token. -/
def head (a : StepData) : ArithQBF.Kind × ℕ := a.2.1.headD (.top, 0)

/-- The claim on top of the stack. -/
def top (a : StepData) : Claim := a.2.2.1.headD ([], 0)

/-- The claims below the top of the stack. -/
def below (a : StepData) : List Claim := a.2.2.1.tail

end StepData

/-! ### The step -/

/-- The message of a step: the remaining tokens and the point of the claim on top of the stack. -/
def message (a : StepData) : List Bool :=
  encPair (encList encArithToken) encPt (a.2.1, a.top.1)

/-- The state after a failed check: the token and the claim are dropped. -/
def reject (a : StepData) : VState := (a.2.1.tail, a.below, false)

/-- The reply of a step, read as `D + 1` residues. -/
def replyOf (a : StepData) (word : List Bool) : List ℕ := decodeReply a.modulus a.degree word

/-- The state after the reply `word` to a binary connective `o`: the claimed values of the two
arguments are checked against the top claim, then pushed in its place. -/
def binNext (o : ArithQBF.Connective) (a : StepData) (word : List Bool) : VState :=
  if connectiveMod a.modulus o ((replyOf a word).getD 0 0) ((replyOf a word).getD 1 0) %
      a.modulus = a.top.2 % a.modulus then
    (a.2.1.tail, (normPt a.modulus a.xs a.top.1, (replyOf a word).getD 0 0) ::
      (normPt a.modulus a.xs a.top.1, (replyOf a word).getD 1 0) :: a.below, true)
  else reject a

/-- Whether the reply `word` to an operator `o` passes the check against the top claim. -/
def opCheck (o : ArithQBF.Operator) (a : StepData) (word : List Bool) : Bool :=
  decide (operatorMod a.modulus o (lookupPt a.top.1 a.head.2 % a.modulus)
    (hornerMod a.modulus 0 (replyOf a word)) (hornerMod a.modulus 1 (replyOf a word)) %
      a.modulus = a.top.2 % a.modulus)

/-- The state after the reply `word` to an operator and the random point `z`: the claim that the
body has the value of the reply at `z`, with the variable set to `z`. -/
def opNext (a : StepData) (word : List Bool) (z : ℕ) : VState :=
  (a.2.1.tail, (updatePt a.modulus a.xs a.top.1 a.head.2 z,
    hornerMod a.modulus z (replyOf a word)) :: a.below, true)

/-- The reply to the message of a step, of which `D + 1` rows are read. -/
noncomputable def ask (a : StepData) : WordOracleComp Unit (List Bool) :=
  List.take (replyLimit a.modulus a.degree) <$>
    ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), message a)

/-- The continuation of a step on an operator after the reply `word`. -/
noncomputable def opCont (o : ArithQBF.Operator) (a : StepData) (word : List Bool) :
    WordOracleComp Unit VState :=
  if opCheck o a word then
    (fun z => opNext a word z) <$> ProbOracleComp.sample (sampleMod a.modulus)
  else pure (reject a)

/-- A step on a token of kind `k`. -/
noncomputable def stepAt : ArithQBF.Kind → StepData → WordOracleComp Unit VState
  | .var, a => pure (a.2.1.tail, a.below,
      decide (lookupPt a.top.1 a.head.2 % a.modulus = a.top.2 % a.modulus))
  | .top, a => pure (a.2.1.tail, a.below, decide (1 % a.modulus = a.top.2 % a.modulus))
  | .bot, a => pure (a.2.1.tail, a.below, decide (0 % a.modulus = a.top.2 % a.modulus))
  | .not, a => pure (a.2.1.tail,
      (normPt a.modulus a.xs a.top.1, subMod a.modulus 1 a.top.2) :: a.below, true)
  | .and, a => do
      let word ← ask a
      return binNext .and a word
  | .or, a => do
      let word ← ask a
      return binNext .or a word
  | .ex, a => do
      let word ← ask a
      opCont .ex a word
  | .all, a => do
      let word ← ask a
      opCont .all a word
  | .lin, a => do
      let word ← ask a
      opCont .lin a word

/-- **One step of the machine**: while every check passed and tokens remain, process the next
token; otherwise stay put. -/
noncomputable def step (I : LoopInput) (st : VState) : WordOracleComp Unit VState :=
  if st.2.2 && !st.1.isEmpty then stepAt (st.1.headD (.top, 0)).1 (I, st) else pure st

/-- The initial state: all the tokens, and the claim that the formula has value `1` at the
origin. -/
def init (I : LoopInput) : VState := (I.2, [(I.1.1.map fun x => (x, 0), 1)], true)

/-- The machine runs one step per token. -/
noncomputable def loop (I : LoopInput) : WordOracleComp Unit VState :=
  OracleComp.iterate I.2.length (step I) (init I)

/-! ### The step in polynomial time -/

section PolyTime

open ComputableInPolyTime

private lemma listTail_pt {α γ : Type} {enc : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {list : γ → List α} (hlist : ComputableInPolyTime list encIn (encList enc)) :
    ComputableInPolyTime (fun x => (list x).tail) encIn (encList enc) := by
  simpa only [Function.comp_def, List.drop_one] using
    (dropUnary (encA := enc)).comp (hlist.prod (const 1))

private lemma listIsEmpty_pt {α γ : Type} {enc : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {list : γ → List α} (hlist : ComputableInPolyTime list encIn (encList enc)) :
    ComputableInPolyTime (fun x => (list x).isEmpty) encIn encBool := by
  have heq : (fun x => (list x).isEmpty) = fun x => decide ((list x).length = 0) := by
    funext x
    cases list x <;> rfl
  rw [heq]
  exact ((length_list enc).comp hlist).decide_eq' (const 0)

private lemma listHeadD_pt {α γ : Type} {enc : α ↪ List Bool} {encIn : γ ↪ List Bool}
    (fallback : α) {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList enc)) :
    ComputableInPolyTime (fun x => (list x).headD fallback) encIn enc :=
  (headD fallback).comp hlist

private lemma unary_mod'_pt {γ : Type} {encIn : γ ↪ List Bool} {a b : γ → ℕ}
    (ha : ComputableInPolyTime a encIn encUnary)
    (hb : ComputableInPolyTime b encIn encUnary) :
    ComputableInPolyTime (fun x => a x % b x) encIn encUnary :=
  unary_mod.comp (ha.prod hb)

private lemma unary_decide_eq_pt {γ : Type} {encIn : γ ↪ List Bool} {a b : γ → ℕ}
    (ha : ComputableInPolyTime a encIn encUnary)
    (hb : ComputableInPolyTime b encIn encUnary) :
    ComputableInPolyTime (fun x => decide (a x = b x)) encIn encBool :=
  ha.decide_eq' hb

attribute [local fun_prop] ComputableInPolyTime.bool_and' listTail_pt listIsEmpty_pt listHeadD_pt
  unary_mod'_pt unary_decide_eq_pt computableInPolyTime_connectiveMod
  computableInPolyTime_operatorMod

private lemma xs_pt :
    ComputableInPolyTime StepData.xs encStepData (encList encNat) := by
  unfold StepData.xs
  fun_prop

private lemma modulus_pt :
    ComputableInPolyTime StepData.modulus encStepData encUnary := by
  unfold StepData.modulus
  fun_prop

private lemma degree_pt :
    ComputableInPolyTime StepData.degree encStepData encUnary := by
  unfold StepData.degree
  fun_prop

private lemma tokens_pt :
    ComputableInPolyTime (fun a : StepData => a.2.1) encStepData (encList encArithToken) := by
  fun_prop

attribute [local fun_prop] xs_pt modulus_pt degree_pt tokens_pt

private lemma head_pt :
    ComputableInPolyTime StepData.head encStepData encArithToken := by
  unfold StepData.head
  fun_prop

private lemma top_pt :
    ComputableInPolyTime StepData.top encStepData encClaim := by
  unfold StepData.top
  fun_prop

private lemma below_pt :
    ComputableInPolyTime StepData.below encStepData (encList encClaim) := by
  unfold StepData.below
  fun_prop

attribute [local fun_prop] head_pt top_pt below_pt

private lemma message_pt :
    ComputableInPolyTime message encStepData encBits := by
  unfold message
  exact encoding_comp (by fun_prop)

private lemma reject_pt :
    ComputableInPolyTime reject encStepData encVState := by
  unfold reject
  fun_prop

private lemma replyOf_pt :
    ComputableInPolyTime (fun pair : StepData × List Bool => replyOf pair.1 pair.2)
      (encPair encStepData encBits) (encList encUnary) := by
  unfold replyOf
  fun_prop

attribute [local fun_prop] message_pt reject_pt replyOf_pt

private lemma binNext_pt (o : ArithQBF.Connective) :
    ComputableInPolyTime (fun pair : StepData × List Bool => binNext o pair.1 pair.2)
      (encPair encStepData encBits) encVState := by
  have h0 : ComputableInPolyTime
      (fun pair : StepData × List Bool => (replyOf pair.1 pair.2).getD 0 0)
      (encPair encStepData encBits) encUnary :=
    listGetDWithInput replyOf_pt (const 0) 0
  have h1 : ComputableInPolyTime
      (fun pair : StepData × List Bool => (replyOf pair.1 pair.2).getD 1 0)
      (encPair encStepData encBits) encUnary :=
    listGetDWithInput replyOf_pt (const 1) 0
  unfold binNext
  fun_prop

private lemma opCheck_pt (o : ArithQBF.Operator) :
    ComputableInPolyTime (fun pair : StepData × List Bool => opCheck o pair.1 pair.2)
      (encPair encStepData encBits) encBool := by
  unfold opCheck
  fun_prop

private lemma opNext_pt :
    ComputableInPolyTime (fun q : (StepData × List Bool) × ℕ => opNext q.1.1 q.1.2 q.2)
      (encPair (encPair encStepData encBits) encUnary) encVState := by
  unfold opNext
  fun_prop

private lemma ask_pt : IsOraclePPTOn encStepData encBits ask :=
  IsOraclePPTOn.query_take' () message_pt (by fun_prop)

private lemma opCont_pt (o : ArithQBF.Operator) :
    IsOraclePPTOn (encPair encStepData encBits) encVState (fun pair => opCont o pair.1 pair.2) := by
  unfold opCont
  have hsample : IsOraclePPTOn (Operation := Unit) (encPair encStepData encBits) encUnary
      (fun pair : StepData × List Bool => ProbOracleComp.sample (sampleMod pair.1.modulus)) :=
    (isPPTOn_sampleMod (by fun_prop)).isOraclePPTOn
  exact IsOraclePPTOn.cond' (opCheck_pt o) (hsample.map_with' opNext_pt)
    ((ComputableInPolyTime.isOraclePPTOn (f := fun pair : StepData × List Bool =>
      reject pair.1) (by fun_prop)))

private lemma stepAt_pt (k : ArithQBF.Kind) :
    IsOraclePPTOn encStepData encVState (stepAt k) := by
  cases k
  · exact ComputableInPolyTime.isOraclePPTOn (f := fun a : StepData => (a.2.1.tail, a.below,
      decide (lookupPt a.top.1 a.head.2 % a.modulus = a.top.2 % a.modulus))) (by fun_prop)
  · exact ComputableInPolyTime.isOraclePPTOn (f := fun a : StepData => (a.2.1.tail, a.below,
      decide (1 % a.modulus = a.top.2 % a.modulus))) (by fun_prop)
  · exact ComputableInPolyTime.isOraclePPTOn (f := fun a : StepData => (a.2.1.tail, a.below,
      decide (0 % a.modulus = a.top.2 % a.modulus))) (by fun_prop)
  · exact ComputableInPolyTime.isOraclePPTOn (f := fun a : StepData => (a.2.1.tail,
      (normPt a.modulus a.xs a.top.1, subMod a.modulus 1 a.top.2) :: a.below, true))
      (by fun_prop)
  · exact ask_pt.bind_with (binNext_pt .and).isOraclePPTOn
  · exact ask_pt.bind_with (binNext_pt .or).isOraclePPTOn
  · exact ask_pt.bind_with (opCont_pt .ex)
  · exact ask_pt.bind_with (opCont_pt .all)
  · exact ask_pt.bind_with (opCont_pt .lin)

/-- **A step of the machine is strict oracle PPT** in the encoded input and state. -/
private theorem isOraclePPTOn_step :
    IsOraclePPTOn encStepData encVState (fun a : StepData => step a.1 a.2) := by
  unfold step
  exact IsOraclePPTOn.cond' (by fun_prop)
    (IsOraclePPTOn.finite_cases' (tagEncoding := encFinEnum ArithQBF.Kind)
      (tag := fun a : StepData => a.head.1) (branch := stepAt) (by fun_prop) stepAt_pt)
    (ComputableInPolyTime.isOraclePPTOn (f := fun a : StepData => a.2) (by fun_prop))

end PolyTime

/-! ### The storage of the machine -/

/-- A bound on the encodings of the claims the machine pushes: points on the variables of `xs`
with values below the modulus, and a value below the modulus. -/
def claimBound (I : LoopInput) : ℕ :=
  2 * (encList encNat I.1.1).length * (2 * I.1.2.1 + 3) + I.1.2.1 + 1

private theorem length_encPt_map_le (xs : List ℕ) (f : ℕ → ℕ) {q : ℕ} (hf : ∀ x, f x ≤ q) :
    (encPt (xs.map fun x => (x, f x))).length ≤ (encList encNat xs).length * (2 * q + 3) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, encList_cons, List.length_append, length_frame, encPair_apply,
      encUnary_apply, List.length_replicate, Nat.add_mul] at ih ⊢
    have := hf x
    nlinarith

private theorem length_encClaim_map_le (I : LoopInput) (f : ℕ → ℕ)
    (hf : ∀ x, f x < I.1.2.1 + 1) (v : ℕ) (hv : v < I.1.2.1 + 1) :
    (encClaim (I.1.1.map fun x => (x, f x), v)).length ≤ claimBound I := by
  have := length_encPt_map_le I.1.1 f (q := I.1.2.1) fun x => Nat.le_of_lt_succ (hf x)
  simp only [encClaim, length_encPair, encUnary_apply, List.length_replicate, claimBound]
  nlinarith

private theorem length_encList_tail_le {α : Type} (enc : α ↪ List Bool) (l : List α) :
    (encList enc l.tail).length ≤ (encList enc l).length := by
  cases l <;> simp

/-- Replacing the next token and the top claim by at most two claims of bounded encodings adds at
most a bounded amount of storage. -/
private theorem length_encVState_push_le (st : VState) (entries : List Claim) (b : Bool) {B : ℕ}
    (hlen : entries.length ≤ 2) (hentries : ∀ e ∈ entries, (encClaim e).length ≤ B) :
    (encVState (st.1.tail, entries ++ st.2.1.tail, b)).length ≤
      (encVState st).length + (8 * B + 8) := by
  have htok := length_encList_tail_le encArithToken st.1
  have hstk := length_encList_tail_le encClaim st.2.1
  have hentry : (encList encClaim entries).length ≤ 2 * (2 * B + 1) := by
    rw [length_encList]
    calc (entries.map fun e => 2 * (encClaim e).length + 1).sum
        ≤ (entries.map fun _ => 2 * B + 1).sum :=
          List.sum_le_sum fun e he => by have := hentries e he; omega
      _ = entries.length * (2 * B + 1) := by simp
      _ ≤ 2 * (2 * B + 1) := Nat.mul_le_mul_right _ hlen
  simp only [encVState, length_encPair, encList_append, List.length_append, encBool_apply,
    List.length_singleton]
  omega

/-- **Every step adds a bounded amount of storage**, polynomial in the input of the loop. -/
theorem length_encVState_le_of_mem_support_step (I : LoopInput) (st : VState) {next : VState}
    (h : next ∈ OracleComp.support (step I st)) :
    (encVState next).length ≤ (encVState st).length + (8 * claimBound I + 8) := by
  have : NeZero (I.1.2.1 + 1) := ⟨Nat.succ_ne_zero _⟩
  have hq : 0 < I.1.2.1 + 1 := Nat.succ_pos _
  have hrej :
      (encVState (reject (I, st))).length ≤ (encVState st).length + (8 * claimBound I + 8) :=
    length_encVState_push_le st [] false (B := claimBound I) (by simp) (by simp)
  have hnorm (pt : List (ℕ × ℕ)) (v : ℕ) (hv : v < I.1.2.1 + 1) :
      (encClaim (normPt (I.1.2.1 + 1) I.1.1 pt, v)).length ≤ claimBound I :=
    length_encClaim_map_le I _ (fun x => Nat.mod_lt _ hq) v hv
  have hreply (word : List Bool) (i : ℕ) :
      (decodeReply (I.1.2.1 + 1) I.1.2.2 word).getD i 0 < I.1.2.1 + 1 := by
    rw [List.getD_eq_getElem?_getD]
    rcases hget : (decodeReply (I.1.2.1 + 1) I.1.2.2 word)[i]? with _ | a
    · exact hq
    · exact lt_of_mem_decodeReply (List.mem_of_getElem? hget)
  have hbin (o : ArithQBF.Connective) (hnext : next ∈ OracleComp.support
      (ask (I, st) >>= fun word => pure (binNext o (I, st) word))) :
      (encVState next).length ≤ (encVState st).length + (8 * claimBound I + 8) := by
    obtain ⟨word, -, hword⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
    rw [OracleComp.eq_of_mem_supportWith_pure hword]
    unfold binNext
    split_ifs
    · refine length_encVState_push_le st [_, _] true (by simp) ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hnorm _ _ (hreply word 0), hnorm _ _ (hreply word 1)⟩
    · exact hrej
  have hop (o : ArithQBF.Operator) (hnext : next ∈ OracleComp.support
      (ask (I, st) >>= opCont o (I, st))) :
      (encVState next).length ≤ (encVState st).length + (8 * claimBound I + 8) := by
    obtain ⟨word, -, hword⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
    unfold opCont at hword
    split_ifs at hword
    · obtain ⟨z, hz, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hword
      refine length_encVState_push_le st [_] true (by simp) ?_
      simp only [List.mem_singleton, forall_eq]
      exact length_encClaim_map_le I _ (fun x => by split_ifs <;> exact Nat.mod_lt _ hq) _
        (hornerMod_lt _ _)
    · rw [OracleComp.eq_of_mem_supportWith_pure hword]
      exact hrej
  unfold step at h
  split_ifs at h with hactive
  · generalize hk : (st.1.headD (.top, 0)).1 = k at h
    cases k
    · rw [OracleComp.eq_of_mem_supportWith_pure h]
      exact length_encVState_push_le st [] _ (by simp) (by simp)
    · rw [OracleComp.eq_of_mem_supportWith_pure h]
      exact length_encVState_push_le st [] _ (by simp) (by simp)
    · rw [OracleComp.eq_of_mem_supportWith_pure h]
      exact length_encVState_push_le st [] _ (by simp) (by simp)
    · rw [OracleComp.eq_of_mem_supportWith_pure h]
      refine length_encVState_push_le st [_] true (by simp) ?_
      simp only [List.mem_singleton, forall_eq]
      exact hnorm _ _ (subMod_lt _ _)
    · exact hbin .and h
    · exact hbin .or h
    · exact hop .ex h
    · exact hop .all h
    · exact hop .lin h
  · rw [OracleComp.eq_of_mem_supportWith_pure h]
    omega

/-! ### The machine in polynomial time -/

section LoopPolyTime

open ComputableInPolyTime

private lemma init_pt : ComputableInPolyTime init encLoopInput encVState := by
  unfold init
  fun_prop

private lemma growth_polyBounded :
    PolyBounded (fun I => (encLoopInput I).length) (fun I => 8 * claimBound I + 8) := by
  refine PolyBounded.of_forall_le 64 2 fun I => ?_
  have hxs : (encList encNat I.1.1).length ≤ (encLoopInput I).length :=
    (length_le_encPair_left _ _ I.1).trans (length_le_encPair_left _ _ I)
  have hq : I.1.2.1 ≤ (encLoopInput I).length := by
    have h₁ : (encUnary I.1.2.1).length ≤ (encPair encUnary encUnary I.1.2).length :=
      length_le_encPair_left _ _ I.1.2
    have h₂ : (encPair encUnary encUnary I.1.2).length ≤ (encParams I.1).length :=
      length_le_encPair_right _ _ I.1
    have h₃ : (encParams I.1).length ≤ (encLoopInput I).length := length_le_encPair_left _ _ I
    simp only [encUnary_apply, List.length_replicate] at h₁
    omega
  unfold claimBound
  nlinarith

/-- **The machine is strict oracle PPT** in its encoded input. -/
private theorem isOraclePPTOn_loop : IsOraclePPTOn encLoopInput encVState loop := by
  unfold loop
  exact IsOraclePPTOn.iterateWith_of_bounded_growth' (count := fun I => I.2.length) (by fun_prop)
    init_pt isOraclePPTOn_step growth_polyBounded
    fun I st _ h => length_encVState_le_of_mem_support_step I st h

end LoopPolyTime

end Machine

open Machine

/-! ### Parameters of a formula -/

/-- The variable components of the tokens of a formula, in prefix order, with multiplicity and with
`0` for the tokens without a variable. Every variable of the formula occurs in it. -/
def linVars (ψ : QBF ℕ) : List ℕ := ψ.tokens.map Prod.snd

/-- The degree bound of every round: twice the size of the formula. -/
def degreeBound (ψ : QBF ℕ) : ℕ := 2 * ψ.tokens.length

/-- The modulus must exceed `12 * size ^ 2 * (size + 1)`. -/
def primeBound (ψ : QBF ℕ) : ℕ := 12 * ψ.tokens.length ^ 2 * (ψ.tokens.length + 1)

/-- The modulus: the greatest prime at most twice the bound. -/
def modulus (ψ : QBF ℕ) : ℕ := Nat.findGreatest Nat.Prime (2 * primeBound ψ)

/-- The parameters and tokens of the machine for a formula. -/
def loopInput (ψ : QBF ℕ) : LoopInput :=
  ((linVars ψ, modulus ψ - 1, degreeBound ψ), ψ.tokens.flatMap (QBF.expandToken (linVars ψ)))

/-- **The verifier**: reject a formula with a free variable, and otherwise run the machine on the
arithmetization and accept when every check passed. -/
noncomputable def verifier (ψ : QBF ℕ) : WordOracleComp Unit Bool :=
  if decide ψ.Closed then (fun st => st.2.2) <$> loop (loopInput ψ) else pure false

/-- By Bertrand's postulate, the modulus is a prime above the bound. -/
theorem prime_modulus (ψ : QBF ℕ) : (modulus ψ).Prime ∧ primeBound ψ < modulus ψ := by
  have hB : primeBound ψ ≠ 0 := by
    have := QBF.tokens_ne_nil ψ
    have : 0 < ψ.tokens.length := List.length_pos_of_ne_nil this
    unfold primeBound
    positivity
  obtain ⟨q, hq, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (primeBound ψ) hB
  have hge : q ≤ modulus ψ := Nat.le_findGreatest hle hq
  exact ⟨Nat.findGreatest_spec hle hq, hlt.trans_le hge⟩

theorem lt_modulus (ψ : QBF ℕ) : primeBound ψ < modulus ψ := (prime_modulus ψ).2

/-! ### The verifier in polynomial time -/

section VerifierPolyTime

open ComputableInPolyTime TQBF

private lemma cond_pt {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {c : α → Bool} {f g : α → β}
    (hc : ComputableInPolyTime c encIn encBool)
    (hf : ComputableInPolyTime f encIn encOut)
    (hg : ComputableInPolyTime g encIn encOut) :
    ComputableInPolyTime (fun x => if c x then f x else g x) encIn encOut :=
  ite hc hf hg

private lemma qbf_tokens_pt : ComputableInPolyTime QBF.tokens encQBF (encList encToken) :=
  computableInPolyTime_tokens

private lemma isQuantifier_pt :
    ComputableInPolyTime QBF.Kind.isQuantifier encKind encBool := of_finite _

private lemma arith_pt :
    ComputableInPolyTime QBF.Kind.arith encKind (encFinEnum ArithQBF.Kind) := of_finite _

private lemma lin_pt {α : Type} {enc : α ↪ List Bool} :
    ComputableInPolyTime (fun _ : α => ArithQBF.Kind.lin) enc (encFinEnum ArithQBF.Kind) :=
  const _

attribute [local fun_prop] cond_pt qbf_tokens_pt isQuantifier_pt arith_pt lin_pt

private lemma linVars_pt : ComputableInPolyTime linVars encQBF (encList encNat) := by
  unfold linVars
  fun_prop

private lemma modulus_qbf_pt : ComputableInPolyTime modulus encQBF encUnary := by
  have hbnd : ComputableInPolyTime (fun ψ => 2 * primeBound ψ) encQBF encUnary := by
    unfold primeBound
    fun_prop
  unfold modulus
  exact ComputableInPolyTime.findGreatest hbnd
    (ComputableInPolyTime.unary_decide_prime.comp (.snd _ _))

private lemma loopInput_pt : ComputableInPolyTime loopInput encQBF encLoopInput := by
  have hexpand : ComputableInPolyTime (fun p : QBF ℕ × (QBF.Kind × ℕ) =>
      QBF.expandToken (linVars p.1) p.2) (encPair encQBF encToken) (encList encArithToken) := by
    have := linVars_pt
    unfold QBF.expandToken
    fun_prop
  have := linVars_pt
  have := modulus_qbf_pt
  unfold loopInput degreeBound
  fun_prop

/-- **The verifier is strict oracle PPT**: one fair-coin oracle machine with a polynomial clock
realizes it against every stateful prover. -/
theorem isOraclePPTOn_verifier : IsOraclePPTOn encQBF encBool verifier := by
  unfold verifier
  exact IsOraclePPTOn.cond' computableInPolyTime_decide_closed
    ((isOraclePPTOn_loop.preprocess' loopInput_pt).map' (by fun_prop))
    (ComputableInPolyTime.isOraclePPTOn (f := fun _ : QBF ℕ => false) (const false))

end VerifierPolyTime

end Cslib.Complexity.QBFProtocol

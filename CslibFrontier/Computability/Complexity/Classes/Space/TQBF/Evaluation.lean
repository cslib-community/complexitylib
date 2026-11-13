/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.TQBF
import CslibFrontier.Foundations.Logic.Function.Iterate

/-!
# Evaluating quantified Boolean formulas with an explicit stack

A formula is evaluated by reading its tokens in prefix order (`Cslib.Logic.PL.QBF.tokens`) with an
explicit stack of frames. A frame records an operator whose operands are being evaluated: its
token, the value of its first operand once it has returned, and the tokens following the operator.
One total step function (`Cslib.Complexity.TQBF.step`) either reads a token or returns a value:

* a variable, `top` or `bot` is a value: a variable takes the value given by the innermost
  quantifier frame over it, and clears the flag `ok` when there is none;
* an operator pushes a frame, and the tokens of its first operand follow it;
* a value returned into a negation is negated; a value returned into the first operand of a
  conjunction or disjunction is recorded, and the tokens of the second operand follow it;
* a value returned into the first pass of a quantifier over `v`, which ran with `v` false, is
  recorded, and the reading rewinds to the body of the quantifier for a second pass with `v` true;
* a value returned into the second operand or pass is combined with the first, and the frame is
  popped; an empty stack holding a value is a fixed point.

So the stack is the call stack of the recursive evaluation, and the environment of the recursion is
read off the quantifier frames (`Cslib.Complexity.TQBF.assignment`): during its first pass a
quantifier over `v` sets `v` to `false`, during its second pass to `true`. Every token of the
formula is read at least once, so the flag records whether every variable occurrence is bound.

A call on a formula `φ` returns to the same stack, with the value of `φ` under the assignment of
the stack and the flag updated by the closedness of `φ` relative to the stack, within
`Cslib.Complexity.TQBF.callSteps φ < 4 ^ φ.tokens.length` steps
(`Cslib.Complexity.TQBF.exists_iterate_step_call`). The evaluator
(`Cslib.Complexity.TQBF.evaluate`) runs the machine from the empty stack for `2 ^ (encQBF φ).length`
steps and decides `TQBF` (`Cslib.Complexity.TQBF.evaluate_eq_true_iff`).

Along every run, the input is a suffix of the tokens of the formula, every frame stores a token of
the formula and a suffix of its tokens, and the suffixes stored in the stack are strictly nested,
so the stack is no deeper than the number of tokens (`Cslib.Complexity.TQBF.Good`,
`Cslib.Complexity.TQBF.good_iterate_step`). The time and space of the evaluator on multi-tape
machines are in `CslibFrontier.Computability.Complexity.Classes.Space.TQBF.Membership`.

## Main definitions

* `Cslib.Complexity.TQBF.Frame`, `Cslib.Complexity.TQBF.State`, `Cslib.Complexity.TQBF.step`: the
  stack machine.
* `Cslib.Complexity.TQBF.assignment`, `Cslib.Complexity.TQBF.closedIn`: the assignment of a stack,
  and closedness relative to a stack.
* `Cslib.Complexity.TQBF.callSteps`: the number of steps of a call.
* `Cslib.Complexity.TQBF.evaluate`: the evaluator.
* `Cslib.Complexity.TQBF.Good`: the invariant of the runs.

## Main results

* `Cslib.Complexity.TQBF.exists_iterate_step_call`: every call returns its value.
* `Cslib.Complexity.TQBF.evaluate_eq`, `Cslib.Complexity.TQBF.evaluate_eq_true_iff`: the evaluator
  decides `TQBF`.
* `Cslib.Complexity.TQBF.good_iterate_step`, `Cslib.Complexity.TQBF.Good.length_stack_le`: the
  states of a run are small.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.9][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Theorem 4.13][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.TQBF

open Cslib.Logic.PL

/-! ### The stack machine -/

/-- A frame of the stack: an operator token whose operands are being evaluated, the value of its
first operand (for a quantifier, of its first pass) once it has returned, and the tokens following
the operator; for a quantifier, these are its body followed by the rest of the input, to which the
second pass rewinds. -/
structure Frame where
  /-- The operator. -/
  token : QBF.Kind × ℕ
  /-- The value of the first operand or pass, once it has returned. -/
  first : Option Bool
  /-- The tokens following the operator. -/
  rest : List (QBF.Kind × ℕ)
  deriving Inhabited

/-- The state of the machine. -/
structure State where
  /-- The tokens still to be read. -/
  input : List (QBF.Kind × ℕ)
  /-- The frames of the operators in progress, the innermost first. -/
  stack : List Frame
  /-- The value being returned, or `none` when the next token is to be read. -/
  value : Option Bool
  /-- Whether every variable read so far was bound by a quantifier frame. -/
  ok : Bool
  deriving Inhabited

/-- Whether a frame is a quantifier over `v`. -/
def Frame.binds (v : ℕ) (f : Frame) : Bool :=
  (f.token.1 == .ex || f.token.1 == .all) && f.token.2 == v

/-- The value of `v` given by the innermost quantifier frame over `v`: `false` during its first
pass, `true` during its second; `none` when no frame quantifies over `v`. -/
def lookup (stack : List Frame) (v : ℕ) : Option Bool :=
  (stack.find? (Frame.binds v)).map fun f => f.first.isSome

/-- The assignment of a stack, `false` on the variables it does not bind. -/
def assignment (stack : List Frame) (v : ℕ) : Bool := (lookup stack v).getD false

/-- **One step of the evaluator.** See the module docstring for the cases. -/
def step (s : State) : State :=
  match s.value with
  | none =>
    match s.input with
    | [] => ⟨[], s.stack, some false, s.ok⟩
    | (k, v) :: input =>
      match k with
      | .var => ⟨input, s.stack, some (assignment s.stack v), s.ok && (lookup s.stack v).isSome⟩
      | .top => ⟨input, s.stack, some true, s.ok⟩
      | .bot => ⟨input, s.stack, some false, s.ok⟩
      | .not | .and | .or | .ex | .all => ⟨input, ⟨(k, v), none, input⟩ :: s.stack, none, s.ok⟩
  | some b =>
    match s.stack with
    | [] => s
    | f :: stack =>
      match f.token.1, f.first with
      | .not, _ => ⟨s.input, stack, some !b, s.ok⟩
      | .and, none | .or, none => ⟨s.input, { f with first := some b } :: stack, none, s.ok⟩
      | .ex, none | .all, none => ⟨f.rest, { f with first := some b } :: stack, none, s.ok⟩
      | .and, some a | .all, some a => ⟨s.input, stack, some (a && b), s.ok⟩
      | .or, some a | .ex, some a => ⟨s.input, stack, some (a || b), s.ok⟩
      | .var, _ | .top, _ | .bot, _ => ⟨s.input, stack, some b, s.ok⟩

/-- Whether every free variable of `φ` is bound by a quantifier frame of the stack. -/
def closedIn (stack : List Frame) (φ : QBF ℕ) : Bool :=
  decide (∀ v ∈ φ.freeVars, (lookup stack v).isSome = true)

/-- The number of steps of a call on a formula: one step to read each token, and one step to
return into each operator for each of its operands or passes. -/
def callSteps : QBF ℕ → ℕ
  | .var _ => 1
  | .top => 1
  | .bot => 1
  | .not φ => callSteps φ + 2
  | .and φ ψ => callSteps φ + callSteps ψ + 3
  | .or φ ψ => callSteps φ + callSteps ψ + 3
  | .ex _ φ => 2 * callSteps φ + 3
  | .all _ φ => 2 * callSteps φ + 3

/-! ### The assignment of a stack -/

/-- A frame that is not a quantifier does not change the values of the stack. -/
private theorem lookup_cons_of_binds_eq_false {f : Frame} (h : ∀ v, f.binds v = false)
    (stack : List Frame) (v : ℕ) : lookup (f :: stack) v = lookup stack v := by
  simp [lookup, h v]

/-- A quantifier frame over `x` gives `x` its value. -/
private theorem lookup_cons_quant {f : Frame} {k : QBF.Kind} {x : ℕ} (hk : k = .ex ∨ k = .all)
    (hf : f.token = (k, x)) (stack : List Frame) (v : ℕ) :
    lookup (f :: stack) v = if v = x then some f.first.isSome else lookup stack v := by
  have hb : f.binds v = true ↔ v = x := by
    have hq : (k == .ex || k == .all) = true := by rcases hk with rfl | rfl <;> rfl
    simp only [Frame.binds, hf, hq, Bool.true_and, beq_iff_eq]
    exact eq_comm
  by_cases hv : v = x
  · rw [lookup, List.find?_cons_of_pos (hb.mpr hv)]
    simp [hv]
  · rw [lookup, List.find?_cons_of_neg (fun h => hv (hb.mp h))]
    simp [hv, lookup]

/-- A frame that is not a quantifier does not change the assignment. -/
private theorem assignment_cons_of_binds_eq_false {f : Frame} (h : ∀ v, f.binds v = false)
    (stack : List Frame) : assignment (f :: stack) = assignment stack := by
  funext v
  simp only [assignment, lookup_cons_of_binds_eq_false h]

/-- A quantifier frame over `x` sets `x` to `false` during its first pass and to `true` during its
second. -/
private theorem assignment_cons_quant {f : Frame} {k : QBF.Kind} {x : ℕ} (hk : k = .ex ∨ k = .all)
    (hf : f.token = (k, x)) (stack : List Frame) :
    assignment (f :: stack) = Function.update (assignment stack) x f.first.isSome := by
  funext v
  simp only [assignment, lookup_cons_quant hk hf, Function.update_apply]
  split_ifs <;> rfl

/-- A frame that is not a quantifier does not change closedness. -/
private theorem closedIn_cons_of_binds_eq_false {f : Frame} (h : ∀ v, f.binds v = false)
    (stack : List Frame) (φ : QBF ℕ) : closedIn (f :: stack) φ = closedIn stack φ := by
  simp only [closedIn, lookup_cons_of_binds_eq_false h]

/-- Under a quantifier frame over `x`, a formula is closed exactly when quantifying it over `x`
gives a formula closed relative to the rest of the stack. -/
private theorem closedIn_cons_quant {f : Frame} {k : QBF.Kind} {x : ℕ} (hk : k = .ex ∨ k = .all)
    (hf : f.token = (k, x)) (stack : List Frame) (φ : QBF ℕ) :
    closedIn (f :: stack) φ = closedIn stack (.ex x φ) := by
  simp only [closedIn, lookup_cons_quant hk hf, QBF.freeVars_ex]
  refine Bool.decide_congr ⟨fun h v hv => ?_, fun h v hv => ?_⟩
  · obtain ⟨hvx, hv⟩ := Finset.mem_erase.mp hv
    simpa [hvx] using h v hv
  · by_cases hvx : v = x
    · simp [hvx]
    · simpa [hvx] using h v (Finset.mem_erase.mpr ⟨hvx, hv⟩)

/-- Closedness of a variable. -/
private theorem closedIn_var (stack : List Frame) (v : ℕ) :
    closedIn stack (.var v) = (lookup stack v).isSome := by
  simp [closedIn]

/-- Closedness of a negation. -/
theorem closedIn_not (stack : List Frame) (φ : QBF ℕ) :
    closedIn stack φ.not = closedIn stack φ := rfl

/-- Closedness of a conjunction. -/
private theorem closedIn_and (stack : List Frame) (φ ψ : QBF ℕ) :
    closedIn stack (φ.and ψ) = (closedIn stack φ && closedIn stack ψ) := by
  simp only [closedIn, QBF.freeVars_and, Finset.mem_union, or_imp, forall_and, Bool.decide_and]

/-- Closedness of a disjunction. -/
private theorem closedIn_or (stack : List Frame) (φ ψ : QBF ℕ) :
    closedIn stack (φ.or ψ) = (closedIn stack φ && closedIn stack ψ) := by
  simp only [closedIn, QBF.freeVars_or, Finset.mem_union, or_imp, forall_and, Bool.decide_and]

/-- A universal quantifier and an existential one have the same free variables. -/
private theorem closedIn_all (stack : List Frame) (x : ℕ) (φ : QBF ℕ) :
    closedIn stack (.all x φ) = closedIn stack (.ex x φ) := rfl

/-- The empty stack gives every variable the value `false`. -/
private theorem assignment_nil : assignment [] = fun _ => false := rfl

/-- Relative to the empty stack, closedness is closedness. -/
private theorem closedIn_nil (φ : QBF ℕ) : closedIn [] φ = decide φ.Closed := by
  simp only [closedIn, lookup, List.find?_nil, Option.map_none, Option.isSome_none,
    Bool.false_eq_true, imp_false, QBF.Closed]
  exact Bool.decide_congr ⟨fun h => Finset.eq_empty_of_forall_notMem h,
    fun h v hv => by simp [h] at hv⟩

/-! ### Every call returns its value -/

/-- **Every call returns its value.** From the tokens of `φ` followed by `input`, the machine
returns to the same stack, having read the tokens of `φ`, the value of `φ` under the assignment of
the stack, and the flag updated by the closedness of `φ` relative to the stack, within
`callSteps φ` steps. -/
theorem exists_iterate_step_call (φ : QBF ℕ) (input : List (QBF.Kind × ℕ)) (stack : List Frame)
    (ok : Bool) : ∃ T ≤ callSteps φ, step^[T] ⟨φ.tokens ++ input, stack, none, ok⟩ =
      ⟨input, stack, some (φ.eval (assignment stack)), ok && closedIn stack φ⟩ := by
  induction φ generalizing input stack ok with
  | var v => exact ⟨1, le_rfl, by simp [step, QBF.tokens, closedIn_var, assignment]⟩
  | top => exact ⟨1, le_rfl, by simp [step, QBF.tokens, closedIn]⟩
  | bot => exact ⟨1, le_rfl, by simp [step, QBF.tokens, closedIn]⟩
  | not φ ih =>
    obtain ⟨T, hT, h⟩ := ih input (⟨(.not, 0), none, φ.tokens ++ input⟩ :: stack) ok
    rw [assignment_cons_of_binds_eq_false (fun _ => rfl),
      closedIn_cons_of_binds_eq_false (fun _ => rfl)] at h
    exact ⟨1 + (T + 1), by simp only [callSteps]; omega,
      Function.iterate_trans (Function.iterate_trans rfl h) rfl⟩
  | and φ ψ ihφ ihψ =>
    have e : (φ.and ψ).tokens ++ input = (.and, 0) :: (φ.tokens ++ (ψ.tokens ++ input)) := by
      simp [QBF.tokens]
    obtain ⟨T₁, hT₁, h₁⟩ := ihφ (ψ.tokens ++ input)
      (⟨(.and, 0), none, φ.tokens ++ (ψ.tokens ++ input)⟩ :: stack) ok
    obtain ⟨T₂, hT₂, h₂⟩ := ihψ input
      (⟨(.and, 0), some (φ.eval (assignment stack)), φ.tokens ++ (ψ.tokens ++ input)⟩ :: stack)
      (ok && closedIn stack φ)
    rw [assignment_cons_of_binds_eq_false (fun _ => rfl),
      closedIn_cons_of_binds_eq_false (fun _ => rfl)] at h₁ h₂
    refine ⟨1 + (T₂ + (1 + (T₁ + 1))), by simp only [callSteps]; omega, ?_⟩
    rw [e]
    refine Function.iterate_trans
      (Function.iterate_trans (Function.iterate_trans (Function.iterate_trans rfl h₁) rfl) h₂) ?_
    simp only [Function.iterate_one, step, closedIn_and, Bool.and_assoc, QBF.eval_and]
  | or φ ψ ihφ ihψ =>
    have e : (φ.or ψ).tokens ++ input = (.or, 0) :: (φ.tokens ++ (ψ.tokens ++ input)) := by
      simp [QBF.tokens]
    obtain ⟨T₁, hT₁, h₁⟩ := ihφ (ψ.tokens ++ input)
      (⟨(.or, 0), none, φ.tokens ++ (ψ.tokens ++ input)⟩ :: stack) ok
    obtain ⟨T₂, hT₂, h₂⟩ := ihψ input
      (⟨(.or, 0), some (φ.eval (assignment stack)), φ.tokens ++ (ψ.tokens ++ input)⟩ :: stack)
      (ok && closedIn stack φ)
    rw [assignment_cons_of_binds_eq_false (fun _ => rfl),
      closedIn_cons_of_binds_eq_false (fun _ => rfl)] at h₁ h₂
    refine ⟨1 + (T₂ + (1 + (T₁ + 1))), by simp only [callSteps]; omega, ?_⟩
    rw [e]
    refine Function.iterate_trans
      (Function.iterate_trans (Function.iterate_trans (Function.iterate_trans rfl h₁) rfl) h₂) ?_
    simp only [Function.iterate_one, step, closedIn_or, Bool.and_assoc, QBF.eval_or]
  | ex x φ ih =>
    have hq : QBF.Kind.ex = .ex ∨ QBF.Kind.ex = .all := .inl rfl
    obtain ⟨T₁, hT₁, h₁⟩ := ih input (⟨(.ex, x), none, φ.tokens ++ input⟩ :: stack) ok
    obtain ⟨T₂, hT₂, h₂⟩ := ih input
      (⟨(.ex, x), some (φ.eval (Function.update (assignment stack) x false)), φ.tokens ++ input⟩ ::
        stack) (ok && closedIn stack (.ex x φ))
    rw [assignment_cons_quant hq rfl, closedIn_cons_quant hq rfl] at h₁ h₂
    refine ⟨1 + (T₂ + (1 + (T₁ + 1))), by simp only [callSteps]; omega, ?_⟩
    refine Function.iterate_trans
      (Function.iterate_trans (Function.iterate_trans (Function.iterate_trans rfl h₁) rfl) h₂) ?_
    simp [step]
  | all x φ ih =>
    have hq : QBF.Kind.all = .ex ∨ QBF.Kind.all = .all := .inr rfl
    obtain ⟨T₁, hT₁, h₁⟩ := ih input (⟨(.all, x), none, φ.tokens ++ input⟩ :: stack) ok
    obtain ⟨T₂, hT₂, h₂⟩ := ih input
      (⟨(.all, x), some (φ.eval (Function.update (assignment stack) x false)), φ.tokens ++ input⟩ ::
        stack) (ok && closedIn stack (.ex x φ))
    rw [assignment_cons_quant hq rfl, closedIn_cons_quant hq rfl] at h₁ h₂
    refine ⟨1 + (T₂ + (1 + (T₁ + 1))), by simp only [callSteps]; omega, ?_⟩
    refine Function.iterate_trans
      (Function.iterate_trans (Function.iterate_trans (Function.iterate_trans rfl h₁) rfl) h₂) ?_
    simp [step, closedIn_all]

/-- An empty stack holding a value is a fixed point. -/
private theorem iterate_step_done (input : List (QBF.Kind × ℕ)) (b ok : Bool) (n : ℕ) :
    step^[n] ⟨input, [], some b, ok⟩ = ⟨input, [], some b, ok⟩ :=
  Function.iterate_fixed rfl n

/-- The number of steps of a call is less than `4` to the number of tokens. -/
private theorem callSteps_lt (φ : QBF ℕ) : callSteps φ < 4 ^ φ.tokens.length := by
  induction φ with
  | var v => simp [callSteps, QBF.tokens]
  | top => simp [callSteps, QBF.tokens]
  | bot => simp [callSteps, QBF.tokens]
  | not φ ih =>
    simp only [callSteps, QBF.tokens, List.length_cons, pow_succ]
    omega
  | and φ ψ ihφ ihψ =>
    simp only [callSteps, QBF.tokens, List.length_cons, List.length_append, pow_succ, pow_add]
    have := Nat.one_le_pow φ.tokens.length 4 (by norm_num)
    have := Nat.one_le_pow ψ.tokens.length 4 (by norm_num)
    nlinarith
  | or φ ψ ihφ ihψ =>
    simp only [callSteps, QBF.tokens, List.length_cons, List.length_append, pow_succ, pow_add]
    have := Nat.one_le_pow φ.tokens.length 4 (by norm_num)
    have := Nat.one_le_pow ψ.tokens.length 4 (by norm_num)
    nlinarith
  | ex x φ ih =>
    simp only [callSteps, QBF.tokens, List.length_cons, pow_succ]
    omega
  | all x φ ih =>
    simp only [callSteps, QBF.tokens, List.length_cons, pow_succ]
    omega

/-- The evaluator runs the machine long enough: `2 ^ (encQBF φ).length` steps. -/
theorem callSteps_le (φ : QBF ℕ) : callSteps φ ≤ 2 ^ (encQBF φ).length := by
  have h₁ := callSteps_lt φ
  have h₂ := three_mul_length_tokens_le φ
  have h₃ : 4 ^ φ.tokens.length ≤ 2 ^ (encQBF φ).length := by
    rw [show 4 = 2 ^ 2 by rfl, ← pow_mul]
    exact Nat.pow_le_pow_right two_pos (by omega)
  omega

/-! ### The evaluator -/

/-- The initial state on a formula: its tokens, the empty stack, nothing to return, no unbound
variable met. -/
def init (φ : QBF ℕ) : State := ⟨φ.tokens, [], none, true⟩

/-- The answer held by a state: whether no unbound variable was met and the value returned is
`true`. -/
def State.answer (s : State) : Bool := s.ok && s.value.getD false

/-- **The evaluator**: run the machine from the initial state for `2 ^ (encQBF φ).length` steps
and read the answer. -/
def evaluate (φ : QBF ℕ) : Bool := (step^[2 ^ (encQBF φ).length] (init φ)).answer

/-- **The evaluator computes closedness and the value.** -/
theorem evaluate_eq (φ : QBF ℕ) : evaluate φ = (decide φ.Closed && φ.eval fun _ => false) := by
  obtain ⟨T, hT, h⟩ := exists_iterate_step_call φ [] [] true
  have hN := callSteps_le φ
  rw [List.append_nil] at h
  rw [evaluate, init, show 2 ^ (encQBF φ).length = 2 ^ (encQBF φ).length - T + T by omega,
    Function.iterate_add_apply, h, iterate_step_done, State.answer, closedIn_nil, assignment_nil]
  simp

/-- **The evaluator decides `TQBF`.** -/
theorem evaluate_eq_true_iff {φ : QBF ℕ} : evaluate φ = true ↔ φ ∈ TQBF := by
  rw [evaluate_eq, Bool.and_eq_true, decide_eq_true_iff, mem_TQBF]

/-! ### The states of a run -/

/-- The suffixes stored in a stack are strictly nested above a bound: the input, of length at most
`r`, is no longer than the suffix of the top frame, which is shorter than the suffix of the frame
below, and so on, and the suffix of the bottom frame is shorter than `n`. -/
def Nested (n : ℕ) : ℕ → List Frame → Prop
  | r, [] => r ≤ n
  | r, f :: stack => r ≤ f.rest.length ∧ Nested n (f.rest.length + 1) stack

/-- Nesting is preserved by a shorter input. -/
theorem Nested.mono {n : ℕ} : ∀ {r r' : ℕ} {stack : List Frame}, Nested n r stack → r' ≤ r →
    Nested n r' stack
  | _, _, [], h, hr => le_trans hr h
  | _, _, _ :: _, h, hr => ⟨le_trans hr h.1, h.2⟩

/-- A nested stack holds at most `n - r` frames. -/
private theorem Nested.length_le {n : ℕ} : ∀ {r : ℕ} {stack : List Frame}, Nested n r stack →
    r + stack.length ≤ n
  | _, [], h => h
  | _, _ :: _, h => by
    have := h.2.length_le
    have := h.1
    simp only [List.length_cons]
    omega

/-- **The invariant of the runs** on the formula `φ`: the input is a suffix of the tokens of `φ`,
each frame stores a token of `φ` followed by a suffix of the tokens of `φ`, and the stored suffixes
are nested. -/
structure Good (φ : QBF ℕ) (s : State) : Prop where
  /-- The input is a suffix of the tokens. -/
  input : s.input <:+ φ.tokens
  /-- Each frame stores a suffix of the tokens. -/
  frames : ∀ f ∈ s.stack, f.token :: f.rest <:+ φ.tokens
  /-- The stored suffixes are nested. -/
  nested : Nested φ.tokens.length s.input.length s.stack

/-- The initial state satisfies the invariant. -/
private theorem good_init (φ : QBF ℕ) : Good φ (init φ) :=
  ⟨List.suffix_refl _, fun _ hf => by simp [init] at hf, le_refl _⟩

/-- The step preserves the invariant. -/
private theorem Good.step {φ : QBF ℕ} {s : State} (h : Good φ s) : Good φ (step s) := by
  obtain ⟨input, stack, value, ok⟩ := s
  obtain ⟨hin, hframes, hnest⟩ := h
  dsimp only at hin hframes hnest
  rcases value with _ | b
  · rcases input with _ | ⟨⟨k, v⟩, input⟩
    · exact ⟨hin, hframes, hnest⟩
    · have htail : input <:+ φ.tokens := (List.suffix_cons _ _).trans hin
      have hnest' : Nested φ.tokens.length input.length stack :=
        hnest.mono (by simp)
      cases k
      case var | top | bot => exact ⟨htail, hframes, hnest'⟩
      all_goals
        refine ⟨htail, fun f hf => ?_, ⟨le_refl _, by simpa using hnest⟩⟩
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hin
        · exact hframes f hf
  · rcases stack with _ | ⟨f, stack⟩
    · exact ⟨hin, hframes, hnest⟩
    · have hf := hframes f (by simp)
      have hrest : f.rest <:+ φ.tokens := (List.suffix_cons _ _).trans hf
      have hbelow : ∀ g ∈ stack, g.token :: g.rest <:+ φ.tokens := fun g hg =>
        hframes g (List.mem_cons_of_mem _ hg)
      obtain ⟨hle, hnest₂⟩ := hnest
      have hpop : Nested φ.tokens.length input.length stack := hnest₂.mono (by omega)
      have hkeep : ∀ g ∈ { f with first := some b } :: stack, g.token :: g.rest <:+ φ.tokens := by
        grind
      obtain ⟨⟨k, x⟩, first, rest⟩ := f
      cases k <;> cases first <;>
        first
        | exact ⟨hin, hbelow, hpop⟩
        | exact ⟨hin, hkeep, ⟨hle, hnest₂⟩⟩
        | exact ⟨hrest, hkeep, ⟨le_refl _, hnest₂⟩⟩

/-- **Every state of a run satisfies the invariant.** -/
theorem good_iterate_step (φ : QBF ℕ) (n : ℕ) : Good φ (step^[n] (init φ)) := by
  induction n with
  | zero => exact good_init φ
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.step

/-- A state satisfying the invariant has at most as many frames as the formula has tokens. -/
theorem Good.length_stack_le {φ : QBF ℕ} {s : State} (h : Good φ s) :
    s.stack.length ≤ φ.tokens.length := by
  have := h.nested.length_le
  omega

end Cslib.Complexity.TQBF

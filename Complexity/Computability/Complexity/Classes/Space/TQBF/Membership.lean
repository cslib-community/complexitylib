/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Space
public import Complexity.Computability.Complexity.Classes.Space.TQBF.Evaluation
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain

/-!
# `TQBF` is in polynomial space

The evaluator of `Cslib.Computability.Complexity.Classes.Space.TQBF.Evaluation` runs its stack
machine for `2 ^ L` steps on a formula whose encoding has length `L`. This file bounds its time
and space in the quantitative calculus of tidy computability
(`Turing.MultiTapeTM.ComputableTidilyInO`), charging every stored frame, the input, the counter of
the rounds and every copy.

The states of the machine are encoded by framed tuples (`Cslib.Complexity.TQBF.encState`). A step
is polynomial-time in the encoded state (`Cslib.Complexity.TQBF.computableInPolyTime_step`):
it branches on whether a value is being returned, on the kind of the next token or of the top
frame, and looks variables up in the stack. Along a run on a formula with encoding of length `L`,
the stack holds at most `L` frames, each storing a token and a suffix of the tokens of the formula,
so every state has an encoding of length `O((L + 1) ^ 2)`
(`Cslib.Complexity.TQBF.length_encState_le`). The rounds are counted by a binary counter of
`L + 1` digits, from `2 ^ L` written in linear time
(`Turing.MultiTapeTM.ComputableTidilyInDegree.two_pow_length`), so the evaluator runs in space
polynomial in `L` and in time `2 ^ L` times a polynomial in `L`
(`Cslib.Complexity.TQBF.exists_computableInO_evaluate`). Hence `TQBF ∈ PSPACE`
[Sipser, Theorem 8.9][Sipser2013] [Arora and Barak, Theorem 4.13][AroraBarak09].

## Main definitions

* `Cslib.Complexity.TQBF.encFrame`, `Cslib.Complexity.TQBF.encState`: the encoded states.

## Main results

* `Cslib.Complexity.TQBF.computableInPolyTime_step`: a step is polynomial-time.
* `Cslib.Complexity.TQBF.length_encState_le`: the states of a run are of quadratic size.
* `Cslib.Complexity.TQBF.exists_computableInO_evaluate`: the time and space of the evaluator.
* `Cslib.Complexity.TQBF_mem_PSPACE`: `TQBF` is in polynomial space.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.9][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Theorem 4.13][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.TQBF

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Encodings -/

/-- The fields of a frame. -/
def Frame.fields (f : Frame) : (QBF.Kind × ℕ) × Option Bool × List (QBF.Kind × ℕ) :=
  (f.token, f.first, f.rest)

/-- The encoding of the fields of a frame. -/
abbrev encFrameFields : (QBF.Kind × ℕ) × Option Bool × List (QBF.Kind × ℕ) ↪ List Bool :=
  encPair encToken (encPair (encOption encBool) (encList encToken))

/-- Frames encoded by their fields. -/
def encFrame : Frame ↪ List Bool :=
  ⟨fun f => encFrameFields f.fields, fun f g h => by
    obtain ⟨⟩ := f
    obtain ⟨⟩ := g
    simpa [Frame.fields] using encFrameFields.injective h⟩

/-- The fields of a state. -/
def State.fields (s : State) : List (QBF.Kind × ℕ) × List Frame × Option Bool × Bool :=
  (s.input, s.stack, s.value, s.ok)

/-- The encoding of the fields of a state. -/
abbrev encStateFields : List (QBF.Kind × ℕ) × List Frame × Option Bool × Bool ↪ List Bool :=
  encPair (encList encToken) (encPair (encList encFrame) (encPair (encOption encBool) encBool))

/-- States encoded by their fields. -/
def encState : State ↪ List Bool :=
  ⟨fun s => encStateFields s.fields, fun s t h => by
    obtain ⟨⟩ := s
    obtain ⟨⟩ := t
    simpa [State.fields] using encStateFields.injective h⟩

/-! ### The step in polynomial time -/

section Step

open ComputableTidilyInPolyTime

/-- The fields of a state, the identity on encoded values. -/
@[local fun_prop] private lemma fields_pt :
    ComputableTidilyInPolyTime State.fields encState encStateFields :=
  of_eq fun _ => rfl

/-- A state from its fields, the identity on encoded values. -/
@[local fun_prop] private lemma stateMk_pt :
    ComputableTidilyInPolyTime
      (fun p : List (QBF.Kind × ℕ) × List Frame × Option Bool × Bool =>
        State.mk p.1 p.2.1 p.2.2.1 p.2.2.2) encStateFields encState :=
  of_eq fun _ => rfl

/-- The fields of a frame, the identity on encoded values. -/
@[local fun_prop] private lemma frameFields_pt :
    ComputableTidilyInPolyTime Frame.fields encFrame encFrameFields :=
  of_eq fun _ => rfl

/-- A frame from its fields, the identity on encoded values. -/
@[local fun_prop] private lemma frameMk_pt :
    ComputableTidilyInPolyTime
      (fun p : (QBF.Kind × ℕ) × Option Bool × List (QBF.Kind × ℕ) => Frame.mk p.1 p.2.1 p.2.2)
      encFrameFields encFrame :=
  of_eq fun _ => rfl

@[local fun_prop] private lemma input_pt :
    ComputableTidilyInPolyTime State.input encState (encList encToken) :=
  (fst _ _).comp fields_pt

@[local fun_prop] private lemma stack_pt :
    ComputableTidilyInPolyTime State.stack encState (encList encFrame) :=
  ((fst _ _).comp (snd _ _)).comp fields_pt

@[local fun_prop] private lemma value_pt :
    ComputableTidilyInPolyTime State.value encState (encOption encBool) :=
  ((fst _ _).comp ((snd _ _).comp (snd _ _))).comp fields_pt

@[local fun_prop] private lemma ok_pt : ComputableTidilyInPolyTime State.ok encState encBool :=
  ((snd _ _).comp ((snd _ _).comp (snd _ _))).comp fields_pt

@[local fun_prop] private lemma token_pt :
    ComputableTidilyInPolyTime Frame.token encFrame encToken :=
  (fst _ _).comp frameFields_pt

@[local fun_prop] private lemma first_pt :
    ComputableTidilyInPolyTime Frame.first encFrame (encOption encBool) :=
  ((fst _ _).comp (snd _ _)).comp frameFields_pt

@[local fun_prop] private lemma rest_pt :
    ComputableTidilyInPolyTime Frame.rest encFrame (encList encToken) :=
  ((snd _ _).comp (snd _ _)).comp frameFields_pt

/-- The next token, or `(top, 0)` when the input is empty. -/
private def State.head (s : State) : QBF.Kind × ℕ := s.input.headD (.top, 0)

/-- The top frame, or a frame of `top` when the stack is empty. -/
private def State.top (s : State) : Frame := s.stack.headD ⟨(.top, 0), none, []⟩

/-- The value being returned, or `false`. -/
private def State.ret (s : State) : Bool := s.value.getD false

/-- A step reading a token of kind `k`. -/
private def readStep (k : QBF.Kind) (s : State) : State :=
  match k with
  | .var => ⟨s.input.tail, s.stack, some (assignment s.stack s.head.2),
      s.ok && (lookup s.stack s.head.2).isSome⟩
  | .top => ⟨s.input.tail, s.stack, some true, s.ok⟩
  | .bot => ⟨s.input.tail, s.stack, some false, s.ok⟩
  | .not | .and | .or | .ex | .all =>
    ⟨s.input.tail, ⟨s.head, none, s.input.tail⟩ :: s.stack, none, s.ok⟩

/-- A step returning a value into a frame of kind `k`, during its second operand or pass when
`second` holds. -/
private def retStep (k : QBF.Kind) (second : Bool) (s : State) : State :=
  match k, second with
  | .not, _ => ⟨s.input, s.stack.tail, some !s.ret, s.ok⟩
  | .and, false | .or, false =>
    ⟨s.input, { s.top with first := some s.ret } :: s.stack.tail, none, s.ok⟩
  | .ex, false | .all, false =>
    ⟨s.top.rest, { s.top with first := some s.ret } :: s.stack.tail, none, s.ok⟩
  | .and, true | .all, true => ⟨s.input, s.stack.tail, some (s.top.first.getD false && s.ret), s.ok⟩
  | .or, true | .ex, true => ⟨s.input, s.stack.tail, some (s.top.first.getD false || s.ret), s.ok⟩
  | .var, _ | .top, _ | .bot, _ => ⟨s.input, s.stack.tail, some s.ret, s.ok⟩

/-- The step as a case distinction on Boolean tests and finite tags. -/
private theorem step_eq (s : State) : step s =
    if s.value.isSome then
      (if s.stack.isEmpty then s else retStep s.top.token.1 s.top.first.isSome s)
    else if s.input.isEmpty then ⟨s.input, s.stack, some false, s.ok⟩ else readStep s.head.1 s := by
  obtain ⟨input, stack, value, ok⟩ := s
  rcases value with _ | b
  · rcases input with _ | ⟨⟨k, v⟩, input⟩
    · rfl
    · cases k <;> rfl
  · rcases stack with _ | ⟨⟨⟨k, x⟩, first, rest⟩, stack⟩
    · rfl
    · cases k <;> cases first <;> rfl

/-- Whether a variable is bound, by a search of the stack. -/
private theorem isSome_lookup (stack : List Frame) (v : ℕ) :
    (lookup stack v).isSome = (stack.find? (Frame.binds v)).isSome := by
  simp [lookup]

/-- The value of a variable, by a search of the stack. -/
private theorem assignment_eq (stack : List Frame) (v : ℕ) :
    assignment stack v = (stack.find? (Frame.binds v)).elim false fun f => f.first.isSome := by
  simp only [assignment, lookup]
  cases stack.find? (Frame.binds v) <;> rfl

@[local fun_prop] private lemma head_pt :
    ComputableTidilyInPolyTime State.head encState encToken := by
  unfold State.head
  fun_prop

@[local fun_prop] private lemma top_pt :
    ComputableTidilyInPolyTime State.top encState encFrame := by
  unfold State.top
  fun_prop

@[local fun_prop] private lemma ret_pt : ComputableTidilyInPolyTime State.ret encState encBool := by
  unfold State.ret
  fun_prop

/-- Whether a frame quantifies over a variable is polynomial-time. -/
@[local fun_prop] private lemma binds_pt :
    ComputableTidilyInPolyTime (fun p : ℕ × Frame => Frame.binds p.1 p.2)
      (encPair encNat encFrame) encBool := by
  unfold Frame.binds
  have hk : ComputableTidilyInPolyTime (fun k : QBF.Kind => (k == .ex || k == .all)) encKind
      encBool := of_finite _
  fun_prop

/-- Whether the next variable is bound, by a search of the stack. -/
@[local fun_prop] private lemma bound_pt :
    ComputableTidilyInPolyTime (fun s : State => (lookup s.stack s.head.2).isSome) encState
      encBool := by
  simp only [isSome_lookup]
  have h : ComputableTidilyInPolyTime (fun p : State × Frame => Frame.binds p.1.head.2 p.2)
      (encPair encState encFrame) encBool :=
    binds_pt.comp (g := fun p : State × Frame => (p.1.head.2, p.2)) (by fun_prop)
  exact optionIsSome (findWithInput stack_pt h)

/-- The value of the next variable, by a search of the stack. -/
@[local fun_prop] private lemma assignment_pt :
    ComputableTidilyInPolyTime (fun s : State => assignment s.stack s.head.2) encState encBool := by
  simp only [assignment_eq]
  have h : ComputableTidilyInPolyTime (fun p : State × Frame => Frame.binds p.1.head.2 p.2)
      (encPair encState encFrame) encBool :=
    binds_pt.comp (g := fun p : State × Frame => (p.1.head.2, p.2)) (by fun_prop)
  exact optionElimWithInput (findWithInput stack_pt h) (const false) (by fun_prop)

/-- A step reading a token is polynomial-time. -/
private lemma readStep_pt (k : QBF.Kind) :
    ComputableTidilyInPolyTime (readStep k) encState encState := by
  cases k <;> unfold readStep <;> fun_prop

/-- A step returning a value is polynomial-time. -/
private lemma retStep_pt (k : QBF.Kind) (second : Bool) :
    ComputableTidilyInPolyTime (retStep k second) encState encState := by
  cases k <;> cases second <;> unfold retStep <;> fun_prop

/-- **A step of the evaluator is polynomial-time** in the encoded state. -/
theorem computableInPolyTime_step : ComputableInPolyTime step encState encState := by
  refine .of_tidy ?_
  rw [show step = _ from funext step_eq]
  refine cond (optionIsSome value_pt) (cond (listIsEmpty' encFrame |>.comp stack_pt) id' ?_)
    (cond (listIsEmpty' encToken |>.comp input_pt) (by fun_prop) ?_)
  · exact finite_cases (tagEncoding := encPair encKind encBool)
      (tag := fun s => (s.top.token.1, s.top.first.isSome))
      (branch := fun t => retStep t.1 t.2) (by fun_prop) fun t => retStep_pt t.1 t.2
  · exact finite_cases (tagEncoding := encKind) (tag := fun s => s.head.1) (branch := readStep)
      (by fun_prop) readStep_pt

/-- The initial state is polynomial-time: its encoding frames the encoded formula. -/
private lemma init_pt : ComputableTidilyInPolyTime init encQBF encState := by
  have h : ComputableTidilyInPolyTime QBF.tokens encQBF (encList encToken) := of_eq fun _ => rfl
  unfold init
  fun_prop

/-- The answer of a state is polynomial-time. -/
private lemma answer_pt : ComputableTidilyInPolyTime State.answer encState encBool := by
  unfold State.answer
  fun_prop

end Step

/-! ### The size of the states of a run -/

/-- A suffix has a shorter encoding. -/
private theorem length_encList_le_of_suffix {l l' : List (QBF.Kind × ℕ)} (h : l <:+ l') :
    (encList encToken l).length ≤ (encList encToken l').length := by
  obtain ⟨p, rfl⟩ := h
  rw [encList_append, List.length_append]
  omega

/-- A frame storing a token of `φ` followed by a suffix of its tokens is no longer than the
encoding of `φ`, up to its value. -/
private theorem length_encFrame_le {φ : QBF ℕ} {f : Frame} (h : f.token :: f.rest <:+ φ.tokens) :
    (encFrame f).length ≤ (encQBF φ).length + 5 := by
  have hs := length_encList_le_of_suffix h
  have hfirst : (encOption encBool f.first).length ≤ 2 := by cases f.first <;> simp [encOption]
  change (encFrameFields f.fields).length ≤ _
  rw [encQBF_apply]
  simp only [Frame.fields, length_encPair, encList_cons, List.length_append, length_frame] at hs ⊢
  omega

/-- **The states of a run are of quadratic size**: a state satisfying the invariant on `φ` has an
encoding of length at most `16 * ((encQBF φ).length + 1) ^ 2`. -/
theorem length_encState_le {φ : QBF ℕ} {s : State} (h : Good φ s) :
    (encState s).length ≤ 16 * ((encQBF φ).length + 1) ^ 2 := by
  have hin := length_encList_le_of_suffix h.input
  rw [← encQBF_apply] at hin
  have hstack : (encList encFrame s.stack).length ≤
      s.stack.length * (2 * ((encQBF φ).length + 5) + 1) :=
    length_encList_le encFrame s.stack fun f hf => length_encFrame_le (h.frames f hf)
  have hdepth : s.stack.length ≤ (encQBF φ).length :=
    h.length_stack_le.trans (by have := three_mul_length_tokens_le φ; omega)
  have hval : (encOption encBool s.value).length ≤ 2 := by cases s.value <;> simp [encOption]
  have hmul := Nat.mul_le_mul_right (2 * ((encQBF φ).length + 5) + 1) hdepth
  change (encStateFields s.fields).length ≤ _
  simp only [State.fields, length_encPair, encBool_apply, List.length_singleton]
  nlinarith

/-! ### The evaluator in polynomial space -/

/-- `x ^ a ≤ x ^ b` for `1 ≤ x` and `a ≤ b`. -/
private theorem pow_le_pow_of_le {x a b : ℕ} (hx : 1 ≤ x) (hab : a ≤ b) : x ^ a ≤ x ^ b :=
  Nat.pow_le_pow_right hx hab

/-- **The evaluator in polynomial space.** On a formula whose encoding has length `L`, the
evaluator is computable within time `O(2 ^ L * (L + 1) ^ e)` and space `O((L + 1) ^ e)`, for
some fixed `e`. The space charges the input, the stack of at most `L` frames, each storing a token
and a suffix of the tokens, the value, the flag, the counter of the `2 ^ L` rounds in binary, and
the polynomial space of a step; the time charges every round
[Sipser, Theorem 8.9][Sipser2013] [Arora and Barak, Theorem 4.13][AroraBarak09]. -/
theorem exists_computableInO_evaluate : ∃ e, ComputableInO evaluate encQBF encBool
    (fun φ => 2 ^ (encQBF φ).length * ((encQBF φ).length + 1) ^ e)
    fun φ => ((encQBF φ).length + 1) ^ e := by
  have this : ∃ e, ComputableTidilyInO evaluate encQBF encBool
      (fun φ => 2 ^ (encQBF φ).length * ((encQBF φ).length + 1) ^ e) fun φ =>
      ((encQBF φ).length + 1) ^ e := by
    obtain ⟨d, e, hstep⟩ := computableInPolyTime_step.tidy.exists_degree
    obtain ⟨d₀, e₀, hinit⟩ := init_pt.exists_degree
    obtain ⟨d₁, e₁, hans⟩ := answer_pt.exists_degree
    have hn := (ComputableTidilyInDegree.two_pow_length encQBF).inO_one
    have hiter := ComputableTidilyInO.iterate hn hinit.inO hstep.inO
      (R := fun φ => (16 * ((encQBF φ).length + 1) ^ 2 + 1) ^ d)
      (Q := fun φ => (16 * ((encQBF φ).length + 1) ^ 2 + 1) ^ d)
      (B := fun φ => 16 * ((encQBF φ).length + 1) ^ 2)
      (fun φ k _ => Nat.pow_le_pow_left (Nat.add_le_add_right
        (length_encState_le (good_iterate_step φ k)) 1) d)
      (fun φ k _ => Nat.pow_le_pow_left (Nat.add_le_add_right
        (length_encState_le (good_iterate_step φ k)) 1) d)
      (fun φ k _ => length_encState_le (good_iterate_step φ k))
    have h := hans.inO.comp hiter
    refine ⟨2 * (d + d₀ + d₁) + 2, ?_⟩
    refine (h.mono (17 ^ (d + d₁) * 64) (fun φ => ?_) fun φ => ?_).of_enc_eq fun φ => rfl
    all_goals
      simp only [encNat_two_pow, List.length_append, List.length_replicate,
        List.length_singleton]
      have hgood := length_encState_le (good_iterate_step φ (2 ^ (encQBF φ).length))
      generalize step^[2 ^ (encQBF φ).length] (init φ) = s at hgood ⊢
      generalize (encQBF φ).length = L at hgood ⊢
      set E := 2 * (d + d₀ + d₁) + 2
      have hP : 1 ≤ L + 1 := by omega
      have hpow (a : ℕ) (ha : a ≤ E / 2) :
          (16 * (L + 1) ^ 2 + 1) ^ a ≤ 17 ^ a * (L + 1) ^ E := by
        calc (16 * (L + 1) ^ 2 + 1) ^ a ≤ (17 * (L + 1) ^ 2) ^ a :=
              Nat.pow_le_pow_left (by nlinarith [Nat.one_le_pow 2 (L + 1) hP]) a
          _ = 17 ^ a * (L + 1) ^ (2 * a) := by rw [Nat.mul_pow, ← pow_mul]
          _ ≤ 17 ^ a * (L + 1) ^ E := Nat.mul_le_mul_left _ (pow_le_pow_of_le hP (by omega))
      have hR := hpow d (by omega)
      have hA : ((encState s).length + 1) ^ d₁ ≤ 17 ^ d₁ * (L + 1) ^ E :=
        (Nat.pow_le_pow_left (by omega) d₁).trans (hpow d₁ (by omega))
      have hM1 : L + 1 ≤ (L + 1) ^ E := by
        simpa using pow_le_pow_of_le hP (show 1 ≤ E by omega)
      have hM2 : (L + 1) ^ 2 ≤ (L + 1) ^ E := pow_le_pow_of_le hP (by omega)
      have hM0 : (L + 1) ^ d₀ ≤ (L + 1) ^ E := pow_le_pow_of_le hP (by omega)
      have hK : 17 ^ d ≤ 17 ^ (d + d₁) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hK₁ : 17 ^ d₁ ≤ 17 ^ (d + d₁) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hN : 1 ≤ 2 ^ L := Nat.one_le_two_pow
      have hsq : (L + 1 + 1) ^ 2 ≤ 4 * (L + 1) ^ 2 := by nlinarith
      generalize (16 * (L + 1) ^ 2 + 1) ^ d = X at *
      generalize ((encState s).length + 1) ^ d₁ = A at *
      generalize (L + 1) ^ E = M at *
      generalize (L + 1) ^ 2 = Q at *
      generalize (L + 1) ^ d₀ = D at *
      generalize 17 ^ (d + d₁) = K at *
      generalize 2 ^ L = N at *
      have hX : X ≤ K * M := hR.trans (Nat.mul_le_mul_right _ hK)
      have hA' : A ≤ K * M := hA.trans (Nat.mul_le_mul_right _ hK₁)
      have hK1 : 1 ≤ K := le_trans (Nat.one_le_pow _ _ (by norm_num)) hK
      have hKM : M ≤ K * M := Nat.le_mul_of_pos_left _ hK1
    · have hround : X + 16 * Q + (L + 1 + 1) ^ 2 ≤ 21 * (K * M) := by omega
      have hrounds := Nat.mul_le_mul_left (N + 1) hround
      have hNM : K * M ≤ N * (K * M) := Nat.le_mul_of_pos_left _ hN
      nlinarith
    · have : K * 64 * (M + 1) = 64 * (K * M) + 64 * K := by ring
      omega
  simpa only [computableInO_iff_computableTidilyInO] using this

end Cslib.Complexity.TQBF

namespace Cslib.Complexity

open Turing.MultiTapeTM

attribute [local fun_prop] ComputableInPolySpace.tidy in
attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- **`TQBF` is in polynomial space** [Sipser, Theorem 8.9][Sipser2013]
[Arora and Barak, Theorem 4.13][AroraBarak09]: the explicit-stack evaluator decides it within
space polynomial in the length of the encoded formula. -/
theorem TQBF_mem_PSPACE : TQBF ∈ PSPACE encQBF := by
  obtain ⟨e, c, h, -⟩ := TQBF.exists_computableInO_evaluate
  refine ⟨TQBF.evaluate, ⟨_, _, ?_, h⟩,
    fun φ => TQBF.evaluate_eq_true_iff.symm⟩
  refine PolyBounded.of_forall_le (2 * c) e fun φ => ?_
  have := Nat.one_le_pow e ((encQBF φ).length + 1) (by omega)
  nlinarith

end Cslib.Complexity

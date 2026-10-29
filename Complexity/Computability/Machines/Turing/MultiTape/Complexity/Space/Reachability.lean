/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Reachability.Savitch
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.IterateWhile
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# Savitch's algorithm in the space of its stack

Savitch's algorithm (`Cslib.Reachability.savitch`) runs the midpoint recursion on an explicit
stack, for `Cslib.Reachability.Savitch.steps w d` steps. This file bounds its time and space in the
quantitative calculus (`Turing.MultiTapeTM.ComputableInO`), charging every stored frame, counter,
returned value and copy.

The states are encoded by framed pairs, options and lists, with the levels in unary
(`Cslib.Reachability.Savitch.encState`). The edge test may depend on a parameter, which a round of
the iteration keeps in its state together with the width of the midpoints
(`Cslib.Reachability.Savitch.roundStep`). A round takes time quadratic and space linear in its
encoded state, plus the cost of the edge test on the endpoints of a call at level `0`
(`Cslib.Reachability.Savitch.computableInO_roundStep`). Every state of a run from a call at
level `d` holds at most `d` frames of size `O(d + w)`, so iterating the rounds with a binary
counter takes space `O((d + 1) * (d + w + 1))`, plus the parameter and the space of the edge test
on the worst endpoints (`Cslib.Reachability.edgeMax`), and exponential time
(`Cslib.Reachability.computableInO_savitch`). With an edge test and inputs computable in
polynomial time, the space is polynomial (`Cslib.Reachability.exists_polyBounded_space_savitch`).

## Main definitions

* `Cslib.Reachability.encArgs`: the encoding of the inputs of Savitch's algorithm.
* `Cslib.Reachability.edgeMax`: the cost of the edge test on the worst endpoints.
* `Cslib.Reachability.Savitch.encFrame`, `Cslib.Reachability.Savitch.encReg`,
  `Cslib.Reachability.Savitch.encState`: the encoded states of the machine.
* `Cslib.Reachability.Savitch.roundStep`, `Cslib.Reachability.Savitch.encRound`: a step carrying
  the parameter of the edge test and the width, and its encoding.

## Main results

* `Cslib.Reachability.Savitch.computableInO_roundStep`: the time and space of a round.
* `Cslib.Reachability.computableInO_savitch`: the time and space of Savitch's algorithm.
* `Cslib.Reachability.exists_polyBounded_space_savitch`: Savitch's algorithm in polynomial space.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.5][Sipser2013]
* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Section 4.2][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Reachability

open Turing.MultiTapeTM
open Cslib.BitString (enumList mem_enumList increment length_increment)

variable {π : Type} {encP : π ↪ List Bool}

/-! ### The inputs and the cost of the edge test -/

/-- The encoding of the inputs of Savitch's algorithm: the parameter of the edge test, the width and
the depth in unary, and the endpoints. -/
abbrev encArgs (encP : π ↪ List Bool) : π × ℕ × ℕ × List Bool × List Bool ↪ List Bool :=
  encPair encP (encPair encUnary (encPair encUnary (encPair encBits encBits)))

/-- The largest value of `T` on the parameter `p` and two words of width `w`. -/
def edgeMax (T : π × List Bool × List Bool → ℕ) (p : π) (w : ℕ) : ℕ :=
  listMax (fun u => listMax (fun v => T (p, u, v)) (enumList w)) (enumList w)

/-- `edgeMax` bounds `T` on all words of width `w`. -/
theorem le_edgeMax (T : π × List Bool × List Bool → ℕ) (p : π) {w : ℕ} {u v : List Bool}
    (hu : u.length = w) (hv : v.length = w) : T (p, u, v) ≤ edgeMax T p w :=
  (le_listMax (f := fun v => T (p, u, v)) (mem_enumList.mpr hv)).trans
    (le_listMax (f := fun u => listMax (fun v => T (p, u, v)) (enumList w)) (mem_enumList.mpr hu))

namespace Savitch

/-! ### Encodings -/

/-- The fields of a frame. -/
def Frame.fields (f : Frame) : ℕ × List Bool × List Bool × List Bool × Bool :=
  (f.level, f.src, f.dst, f.mid, f.phase)

/-- The encoding of the fields of a frame: the level in unary, the words as themselves. -/
abbrev encFrameFields : ℕ × List Bool × List Bool × List Bool × Bool ↪ List Bool :=
  encPair encUnary (encPair encBits (encPair encBits (encPair encBits encBool)))

/-- Frames encoded by their fields. -/
def encFrame : Frame ↪ List Bool :=
  ⟨fun f => encFrameFields f.fields, fun f g h => by
    obtain ⟨⟩ := f
    obtain ⟨⟩ := g
    simpa [Frame.fields] using encFrameFields.injective h⟩

/-- The register as a pending call, if any, and the returned value, `false` during a call. -/
def Reg.toPair : Reg → Option (ℕ × List Bool × List Bool) × Bool
  | .call i u v => (some (i, u, v), false)
  | .ret b => (none, b)

/-- The encoding of the arguments of a call: the level in unary, the words as themselves. -/
abbrev encCall : ℕ × List Bool × List Bool ↪ List Bool := encPair encUnary (encPair encBits encBits)

/-- Registers encoded by `Reg.toPair`. -/
def encReg : Reg ↪ List Bool :=
  ⟨fun r => encPair (encOption encCall) encBool r.toPair, fun r r' h => by
    have := (encPair (encOption encCall) encBool).injective h
    cases r <;> cases r' <;> simp_all [Reg.toPair]⟩

/-- States encoded as the list of their frames followed by their register. -/
def encState : State ↪ List Bool :=
  ⟨fun s => encPair (encList encFrame) encReg (s.stack, s.reg), fun s s' h => by
    obtain ⟨⟩ := s
    obtain ⟨⟩ := s'
    simpa using (encPair (encList encFrame) encReg).injective h⟩

/-! ### The step in linear time, apart from the edge test -/

section Certificates

open ComputableTidilyInDegree

/-- The counter overflows on the word of all ones, and otherwise increments. -/
private theorem next_eq (u : List Bool) :
    next u = if u.all id then none else some (increment u) := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    cases b
    · rfl
    · simp only [next, ih, List.all_cons, id, Bool.true_and]
      split_ifs <;> rfl

/-- The transducer testing whether all bits are ones. -/
@[simps q₀ step final]
private def allT : Transducer Bool Bool where
  q₀ := true
  step a b := (a && b, [])
  final a := [a]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

/-- The transducer `allT` tests whether all bits are ones. -/
private theorem allT_run (a : Bool) (u : List Bool) : allT.run a u = [a && u.all id] := by
  induction u generalizing a with
  | nil => simp [allT_final]
  | cons b u ih => simp [allT_step, ih, Bool.and_assoc]

/-- The transducer writing a zero for every symbol. -/
@[simps q₀ step final]
private def zeroT : Transducer Bool Unit where
  q₀ := ()
  step _ _ := ((), [false])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

/-- The transducer `zeroT` writes the word of all zeros of the same width. -/
private theorem zeroT_run (u : List Bool) : zeroT.run () u = List.replicate u.length false := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [zeroT_step, ih, List.replicate_succ]

attribute [local fun_prop] ComputableTidilyInDegree.increment

/-- The test for the word of all ones, in linear time. -/
@[local fun_prop] private lemma all_deg :
    ComputableTidilyInDegree (fun u : List Bool => u.all id) encBits encBool 1 1 :=
  of_linear (allT.computableTidilyInLinearTimeAndSpace fun u => by simp [allT_run])

/-- The word of all zeros of width `w`, from `w` in unary, in linear time. -/
@[local fun_prop] private lemma replicate_deg :
    ComputableTidilyInDegree (fun n => List.replicate n false) encUnary encBits 1 1 :=
  of_linear (zeroT.computableTidilyInLinearTimeAndSpace fun n => by simp [zeroT_run])

/-- Conjunction. -/
@[local fun_prop] private lemma and_deg :
    ComputableTidilyInDegree (fun p : Bool × Bool => p.1 && p.2) (encPair encBool encBool) encBool
      1 0 :=
  of_finite _

/-- Disjunction. -/
@[local fun_prop] private lemma or_deg :
    ComputableTidilyInDegree (fun p : Bool × Bool => p.1 || p.2) (encPair encBool encBool) encBool
      1 0 :=
  of_finite _

/-- Negation. -/
@[local fun_prop] private lemma not_deg :
    ComputableTidilyInDegree (fun b : Bool => !b) encBool encBool 1 0 :=
  of_finite _

/-- The predecessor in unary. -/
@[local fun_prop] private lemma pred_deg :
    ComputableTidilyInDegree (fun n : ℕ => n - 1) encUnary encUnary 1 1 :=
  unary_pred

/-- Whether a call is pending. -/
@[local fun_prop] private lemma isSome_deg :
    ComputableTidilyInDegree (fun o : Option (ℕ × List Bool × List Bool) => o.isSome)
      (encOption encCall) encBool 1 0 :=
  isSome encCall

/-- The stack of a state. -/
@[local fun_prop] private lemma stack_deg :
    ComputableTidilyInDegree State.stack encState (encList encFrame) 1 1 :=
  of_linear (.of_unframe fun s => by simp [encState])

/-- The register of a state. -/
@[local fun_prop] private lemma reg_deg : ComputableTidilyInDegree State.reg encState encReg 1 1 :=
  of_linear (.of_dropFrame fun s => by simp [encState])

/-- The register as a pair, the identity on encoded values. -/
@[local fun_prop] private lemma toPair_deg :
    ComputableTidilyInDegree Reg.toPair encReg (encPair (encOption encCall) encBool) 1 1 :=
  of_eq fun _ => rfl

/-- The fields of a frame, the identity on encoded values. -/
private lemma fields_deg : ComputableTidilyInDegree Frame.fields encFrame encFrameFields 1 1 :=
  of_eq fun _ => rfl

/-- The level of a frame. -/
@[local fun_prop] private lemma level_deg :
    ComputableTidilyInDegree Frame.level encFrame encUnary 1 1 :=
  fields_deg.fst'

/-- The source of a frame. -/
@[local fun_prop] private lemma src_deg : ComputableTidilyInDegree Frame.src encFrame encBits 1 1 :=
  fields_deg.snd'.fst'.mono

/-- The target of a frame. -/
@[local fun_prop] private lemma dst_deg : ComputableTidilyInDegree Frame.dst encFrame encBits 1 1 :=
  fields_deg.snd'.snd'.fst'.mono

/-- The midpoint of a frame. -/
@[local fun_prop] private lemma mid_deg : ComputableTidilyInDegree Frame.mid encFrame encBits 1 1 :=
  fields_deg.snd'.snd'.snd'.fst'.mono

/-- The phase of a frame. -/
@[local fun_prop] private lemma phase_deg :
    ComputableTidilyInDegree Frame.phase encFrame encBool 1 1 :=
  fields_deg.snd'.snd'.snd'.snd'.mono

/-- A state from its stack and register, the identity on encoded values. -/
@[local fun_prop] private lemma stateMk_deg :
    ComputableTidilyInDegree (fun p : List Frame × Reg => State.mk p.1 p.2)
      (encPair (encList encFrame) encReg) encState 1 1 :=
  of_eq fun _ => rfl

/-- A frame from its fields, the identity on encoded values. -/
@[local fun_prop] private lemma frameMk_deg :
    ComputableTidilyInDegree
      (fun p : ℕ × List Bool × List Bool × List Bool × Bool =>
        Frame.mk p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) encFrameFields encFrame 1 1 :=
  of_eq fun _ => rfl

/-- A pending call from its arguments. -/
@[local fun_prop] private lemma call_deg :
    ComputableTidilyInDegree (fun c : ℕ × List Bool × List Bool => Reg.call c.1 c.2.1 c.2.2)
      encCall encReg 1 1 :=
  (((optionSome (enc₁ := encCall)).prod (const false)).mono).of_enc_eq fun _ => rfl

/-- A returned value. -/
@[local fun_prop] private lemma ret_deg : ComputableTidilyInDegree Reg.ret encBool encReg 1 1 :=
  (((const (encMid := encOption encCall) none).prod (of_eq fun _ => rfl)).mono).of_enc_eq
    fun _ => rfl

/-- The arguments of the pending call, if any. -/
private def State.args (s : State) : ℕ × List Bool × List Bool := s.reg.toPair.1.getD default

/-- The top frame, if any. -/
private def State.top (s : State) : Frame := s.stack.headD default

/-- The arguments of the pending call. -/
@[local fun_prop] private lemma args_deg :
    ComputableTidilyInDegree State.args encState encCall 1 1 := by
  unfold State.args
  fun_prop (disch := first | apply le_refl | lia)

/-- The top frame. -/
@[local fun_prop] private lemma top_deg :
    ComputableTidilyInDegree State.top encState encFrame 1 1 := by
  unfold State.top
  fun_prop (disch := first | apply le_refl | lia)

/-- Whether the register holds a call at level `0`. -/
private def State.isBase (s : State) : Bool := s.reg.toPair.1.isSome && decide (s.args.1 = 0)

/-- The step on a call at level `0`. -/
private def baseStep (edge : List Bool → List Bool → Bool) (s : State) : State :=
  ⟨s.stack, .ret (decide (s.args.2.1 = s.args.2.2) || edge s.args.2.1 s.args.2.2)⟩

/-- The step on the other states, as a case distinction on Boolean tests. -/
private def restStep (w : ℕ) (s : State) : State :=
  if s.reg.toPair.1.isSome then
    ⟨⟨s.args.1 - 1, s.args.2.1, s.args.2.2, List.replicate w false, false⟩ :: s.stack,
      .call (s.args.1 - 1) s.args.2.1 (List.replicate w false)⟩
  else if s.stack.isEmpty then s
  else if s.reg.toPair.2 && !s.top.phase then
    ⟨{ s.top with phase := true } :: s.stack.tail, .call s.top.level s.top.mid s.top.dst⟩
  else if s.reg.toPair.2 || s.top.mid.all id then ⟨s.stack.tail, s.reg⟩
  else
    ⟨{ s.top with mid := increment s.top.mid, phase := false } :: s.stack.tail,
      .call s.top.level s.top.src (increment s.top.mid)⟩

/-- The step, as a case distinction on whether the register holds a call at level `0`. -/
private theorem step_eq (edge : List Bool → List Bool → Bool) (w : ℕ) (s : State) :
    step edge w s = if s.isBase then baseStep edge s else restStep w s := by
  obtain ⟨stack, (⟨_ | i, u, v⟩ | b)⟩ := s
  · rfl
  · rfl
  · have hb : State.isBase ⟨stack, .ret b⟩ = false := rfl
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rcases stack with _ | ⟨⟨i, u, v, m, ph⟩, stack⟩
    · rfl
    · cases b <;> cases ph <;> cases hm : m.all id <;>
        simp [step, restStep, next_eq, hm, State.top, Reg.toPair]

/-- The step on the states other than calls at level `0`, in linear time. -/
@[local fun_prop] private lemma restStep_deg :
    ComputableTidilyInDegree (fun r : ℕ × State => restStep r.1 r.2) (encPair encUnary encState)
      encState 1 1 := by
  unfold restStep
  fun_prop (disch := first | apply le_refl | lia)

/-- The test for a call at level `0`, in linear time. -/
@[local fun_prop] private lemma isBase_deg :
    ComputableTidilyInDegree State.isBase encState encBool 1 1 := by
  have h₁ : ComputableTidilyInDegree (fun s : State => s.reg.toPair.1.isSome) encState encBool
      1 1 := by
    fun_prop (disch := first | apply le_refl | lia)
  have h₂ : ComputableTidilyInDegree (fun s : State => s.args.1) encState encUnary 1 1 := by
    fun_prop (disch := first | apply le_refl | lia)
  exact (and_deg.comp (h₁.prod (unary_isZero.comp h₂))).mono

/-! ### Sizes of encoded states -/

/-- The length of an encoded frame. -/
theorem length_encFrame (f : Frame) :
    (encFrame f).length =
      2 * f.level + 2 * f.src.length + 2 * f.dst.length + 2 * f.mid.length + 5 := by
  change (encFrameFields f.fields).length = _
  simp only [Frame.fields, length_encPair, encUnary_apply, encBits_apply, encBool_apply,
    List.length_replicate, List.length_singleton]
  omega

/-- The length of an encoded pending call. -/
theorem length_encReg_call (i : ℕ) (u v : List Bool) :
    (encReg (.call i u v)).length = 4 * i + 4 * u.length + 2 * v.length + 8 := by
  change (encPair (encOption encCall) encBool (some (i, u, v), false)).length = _
  simp only [length_encPair, encOption_some, List.length_cons, encUnary_apply, encBits_apply,
    encBool_apply, List.length_replicate, List.length_nil]
  omega

/-- The length of an encoded returned value. -/
theorem length_encReg_ret (b : Bool) : (encReg (.ret b)).length = 2 := rfl

/-- The length of an encoded state. -/
theorem length_encState (s : State) :
    (encState s).length = 2 * (encList encFrame s.stack).length + 1 + (encReg s.reg).length := by
  simp [encState]

/-! ### A step carrying the parameter of the edge test -/

/-- A round of the iteration of Savitch's algorithm: a step of the machine for the edge test
`edge q.1.1` and the width `q.1.2`, keeping both. -/
def roundStep (edge : π → List Bool → List Bool → Bool) (q : (π × ℕ) × State) : (π × ℕ) × State :=
  (q.1, step (edge q.1.1) q.1.2 q.2)

/-- The encoding of the states of the iteration, with the width in unary. -/
abbrev encRound (encP : π ↪ List Bool) : (π × ℕ) × State ↪ List Bool :=
  encPair (encPair encP encUnary) encState

/-- The cost `T` of the edge test, with the parameter `p`, on the endpoints of the pending call, if
any. -/
def Reg.edgeCost (T : π × List Bool × List Bool → ℕ) (p : π) : Reg → ℕ
  | .call _ u v => T (p, u, v)
  | .ret _ => 0

/-- A round, as a case distinction on whether the register holds a call at level `0`. -/
private theorem roundStep_eq (edge : π → List Bool → List Bool → Bool) (q : (π × ℕ) × State) :
    roundStep edge q = if q.2.isBase then (q.1, baseStep (edge q.1.1) q.2)
      else (q.1, restStep q.1.2 q.2) := by
  rw [roundStep, step_eq]
  split_ifs <;> rfl

/-- A register passing the test for a call at level `0` holds a call. -/
private theorem eq_call_of_isBase {s : State} (h : s.isBase = true) :
    s.reg = .call s.args.1 s.args.2.1 s.args.2.2 := by
  obtain ⟨stack, (⟨i, u, v⟩ | b)⟩ := s
  · rfl
  · simp [State.isBase, Reg.toPair] at h

/-- **A round within the time and space of the edge test, plus quadratic time and linear
space.** A call at level `0` compares its endpoints, in quadratic time, and runs the edge test on
them; the other cases copy and rearrange the encoded state, in linear time. -/
private theorem computableTidilyInO_roundStep {edge : π → List Bool → List Bool → Bool}
    {Te Se : π × List Bool × List Bool → ℕ}
    (hedge : ComputableTidilyInO (fun q : π × List Bool × List Bool => edge q.1 q.2.1 q.2.2)
      (encPair encP (encPair encBits encBits)) encBool Te Se) :
    ComputableTidilyInO (roundStep edge) (encRound encP) (encRound encP)
      (fun q => ((encRound encP q).length + 1) ^ 2 + q.2.reg.edgeCost Te q.1.1)
      (fun q => (encRound encP q).length + q.2.reg.edgeCost Se q.1.1) := by
  have hc : ComputableTidilyInDegree (fun q : (π × ℕ) × State => q.2.isBase) (encRound encP)
      encBool 1 1 := by
    fun_prop (disch := first | apply le_refl | lia)
  have hrest : ComputableTidilyInDegree (fun q : (π × ℕ) × State => (q.1, restStep q.1.2 q.2))
      (encRound encP) (encRound encP) 1 1 := by
    fun_prop (disch := first | apply le_refl | lia)
  have hargs : ComputableTidilyInDegree
      (fun q : (π × ℕ) × State => (q.1.1, q.2.args.2.1, q.2.args.2.2)) (encRound encP)
      (encPair encP (encPair encBits encBits)) 1 1 := by
    fun_prop (disch := first | apply le_refl | lia)
  have hends : ComputableTidilyInDegree
      (fun q : (π × ℕ) × State => (q.2.args.2.1, q.2.args.2.2)) (encRound encP)
      (encPair encBits encBits) 1 1 := by
    fun_prop (disch := first | apply le_refl | lia)
  have hkeep : ComputableTidilyInDegree (fun q : (π × ℕ) × State => q.1) (encRound encP)
      (encPair encP encUnary) 1 1 := by
    fun_prop (disch := first | apply le_refl | lia)
  have hstack : ComputableTidilyInDegree (fun q : (π × ℕ) × State => q.2.stack) (encRound encP)
      (encList encFrame) 1 1 := by
    fun_prop (disch := first | apply le_refl | lia)
  have hval := or_deg.inO_one.comp_linear
    ((ComputableInO.eqWords.tidy.comp hends.inO_one).prod (hedge.comp hargs.inO_one))
  have hbase := hkeep.inO_one.prod (stateMk_deg.inO_one.comp_linear
    (hstack.inO_one.prod (ret_deg.inO_one.comp_linear hval)))
  refine ((hc.inO_one.ite hbase hrest.inO_one).mono 8 (fun q => ?_) fun q => ?_).of_enc_eq
    fun q => by rw [roundStep_eq]; split_ifs <;> rfl
  all_goals
    have hE : (encReg q.2.reg).length ≤ (encRound encP q).length := by
      have h₁ : (encState q.2).length ≤ (encRound encP q).length := length_le_encPair_right _ _ q
      have := length_encState q.2
      omega
  · split_ifs with hq
    · have hreg := eq_call_of_isBase hq
      rw [hreg, length_encReg_call] at hE
      rw [hreg, Reg.edgeCost]
      have := Nat.mul_le_mul (show q.2.args.2.1.length + 1 ≤ (encRound encP q).length + 1 by omega)
        (show q.2.args.2.1.length + q.2.args.2.2.length + 1 ≤ (encRound encP q).length + 1 by
          omega)
      nlinarith
    · nlinarith
  · dsimp only
    split_ifs with hq
    · have hreg := eq_call_of_isBase hq
      rw [hreg, length_encReg_call] at hE
      rw [hreg, Reg.edgeCost]
      omega
    · omega

/-- **A round within the time and space of the edge test, plus quadratic time and linear
space.** A call at level `0` compares its endpoints, in quadratic time, and runs the edge test on
them; the other cases copy and rearrange the encoded state, in linear time. -/
theorem computableInO_roundStep {edge : π → List Bool → List Bool → Bool}
    {Te Se : π × List Bool × List Bool → ℕ}
    (hedge : ComputableInO (fun q : π × List Bool × List Bool => edge q.1 q.2.1 q.2.2)
      (encPair encP (encPair encBits encBits)) encBool Te Se) :
    ComputableInO (roundStep edge) (encRound encP) (encRound encP)
      (fun q => ((encRound encP q).length + 1) ^ 2 + q.2.reg.edgeCost Te q.1.1)
      (fun q => (encRound encP q).length + q.2.reg.edgeCost Se q.1.1) :=
  (computableTidilyInO_roundStep hedge.tidy).computableInO

/-! ### The states of a run -/

/-- The rounds keep the parameter and the width, and run the machine. -/
theorem roundStep_iterate (edge : π → List Bool → List Bool → Bool) (p : π) (w : ℕ) (s : State)
    (k : ℕ) : (roundStep edge)^[k] ((p, w), s) = ((p, w), (step (edge p) w)^[k] s) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']; rfl

/-- The frames of a run from a call at level `d` with words of width `w`: a frame with `n` frames
below it is at a level below `d - n`, and its words have width `w`. -/
private def StackOk (w d : ℕ) : List Frame → Prop
  | [] => True
  | f :: stack => f.level + 1 + stack.length ≤ d ∧ f.src.length = w ∧ f.dst.length = w ∧
      f.mid.length = w ∧ StackOk w d stack

/-- The states of a run from a call at level `d` with words of width `w`. -/
private def Invariant (w d : ℕ) (s : State) : Prop :=
  StackOk w d s.stack ∧
    ∀ i u v, s.reg = .call i u v → i + s.stack.length ≤ d ∧ u.length = w ∧ v.length = w

/-- The counter keeps the width. -/
private theorem length_of_next {u m : List Bool} (h : next u = some m) : m.length = u.length := by
  rw [next_eq] at h
  split_ifs at h
  cases h
  exact length_increment u

/-- The step keeps the invariant of a run. -/
private theorem invariant_step (edge : List Bool → List Bool → Bool) {w d : ℕ} {s : State}
    (h : Invariant w d s) : Invariant w d (step edge w s) := by
  obtain ⟨hst, hreg⟩ := h
  obtain ⟨stack, (⟨_ | i, u, v⟩ | b)⟩ := s
  · exact ⟨hst, fun _ _ _ h => by cases h⟩
  · obtain ⟨hi, hu, hv⟩ := hreg _ _ _ rfl
    refine ⟨⟨by dsimp only at hi ⊢; omega, hu, hv, List.length_replicate, hst⟩,
      fun i' u' v' h => ?_⟩
    obtain ⟨rfl, rfl, rfl⟩ := Reg.call.inj h
    exact ⟨by simp only [step, List.length_cons] at hi ⊢; omega, hu, List.length_replicate⟩
  · rcases stack with _ | ⟨f, stack⟩
    · exact ⟨hst, hreg⟩
    · obtain ⟨hl, hs, hd, hm, hst⟩ := hst
      cases b
      · cases hn : next f.mid with
        | none =>
          simp only [step, hn]
          exact ⟨hst, fun _ _ _ h => by cases h⟩
        | some m =>
          have hm' := length_of_next hn
          simp only [step, hn]
          refine ⟨⟨hl, hs, hd, by dsimp only; omega, hst⟩, fun i u v h => ?_⟩
          obtain ⟨rfl, rfl, rfl⟩ := Reg.call.inj h
          exact ⟨by simp only [List.length_cons]; omega, hs, by omega⟩
      · cases hph : f.phase
        · simp only [step, hph, Bool.false_eq_true, ↓reduceIte]
          refine ⟨⟨hl, hs, hd, hm, hst⟩, fun i u v h => ?_⟩
          obtain ⟨rfl, rfl, rfl⟩ := Reg.call.inj h
          exact ⟨by simp only [List.length_cons]; omega, hm, hd⟩
        · simp only [step, hph, ↓reduceIte]
          exact ⟨hst, fun _ _ _ h => by cases h⟩

/-- Every state of a run keeps the invariant. -/
private theorem invariant_iterate (edge : List Bool → List Bool → Bool) {w d : ℕ} {s : State}
    (h : Invariant w d s) (k : ℕ) : Invariant w d ((step edge w)^[k] s) := by
  induction k with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply']; exact invariant_step edge ih

/-- A run from a call at level `d` holds at most `d` frames. -/
private theorem StackOk.length_le {w d : ℕ} :
    ∀ {stack : List Frame}, StackOk w d stack → stack.length ≤ d
  | [], _ => Nat.zero_le _
  | _ :: _, h => by have := h.1; simp only [List.length_cons]; omega

/-- The frames of a run from a call at level `d` are below level `d`, with words of width
`w`. -/
private theorem StackOk.mem {w d : ℕ} :
    ∀ {stack : List Frame}, StackOk w d stack → ∀ f ∈ stack,
      f.level < d ∧ f.src.length = w ∧ f.dst.length = w ∧ f.mid.length = w
  | [], _, _, hf => by simp at hf
  | g :: _, h, f, hf => by
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨by have := h.1; omega, h.2.1, h.2.2.1, h.2.2.2.1⟩
    · exact h.2.2.2.2.mem f hf

/-- The states of a run from a call at level `d`, with words of width `w`, are of size
`O((d + 1) * (d + w + 1))`: at most `d` frames of size `O(d + w)`, and a call of size
`O(d + w)`. -/
private theorem length_encState_le {w d : ℕ} {s : State} (h : Invariant w d s) :
    (encState s).length ≤ 24 * (d + 1) * (d + w + 1) := by
  obtain ⟨hst, hreg⟩ := h
  have hlist : (encList encFrame s.stack).length ≤ d * (2 * (2 * d + 6 * w + 5) + 1) := by
    refine (length_encList_le encFrame s.stack fun f hf => ?_).trans
      (Nat.mul_le_mul_right _ hst.length_le)
    obtain ⟨hl, hs, hd, hm⟩ := hst.mem f hf
    rw [length_encFrame]
    omega
  have hr : (encReg s.reg).length ≤ 4 * d + 6 * w + 8 := by
    rcases hs : s.reg with ⟨i, u, v⟩ | b
    · obtain ⟨hi, hu, hv⟩ := hreg i u v hs
      rw [length_encReg_call]
      omega
    · rw [length_encReg_ret]
      omega
  rw [length_encState]
  nlinarith

/-- A bound on the encoded states of the iteration, for an encoded parameter of length `P`. -/
private def stateBound (P w d : ℕ) : ℕ := 4 * P + 27 * ((d + 1) * (d + w + 1))

/-- The rounds of a run from a call at level `d` are of size `stateBound`. -/
private theorem length_encRound_le {p : π} {w d : ℕ} {s : State} (h : Invariant w d s) :
    (encRound encP ((p, w), s)).length ≤ stateBound (encP p).length w d := by
  have := length_encState_le h
  simp only [encRound, length_encPair, encUnary_apply, List.length_replicate, stateBound]
  nlinarith

/-- The edge test of a round of a run runs on words of width `w`. -/
private theorem edgeCost_le (T : π × List Bool × List Bool → ℕ) (p : π) {w d : ℕ} {s : State}
    (h : Invariant w d s) : s.reg.edgeCost T p ≤ edgeMax T p w := by
  rcases hs : s.reg with ⟨i, u, v⟩ | b
  · obtain ⟨-, hu, hv⟩ := h.2 i u v hs
    exact le_edgeMax T p hu hv
  · exact Nat.zero_le _

/-! ### The number of rounds, in binary -/

/-- `2 ^ K - 1` in binary is `K` ones. -/
private theorem bits_two_pow_sub_one (K : ℕ) : Nat.bits (2 ^ K - 1) = List.replicate K true := by
  induction K with
  | zero => exact Nat.zero_bits
  | succ K ih =>
    have := Nat.one_le_two_pow (n := K)
    rw [show 2 ^ (K + 1) - 1 = 2 * (2 ^ K - 1) + 1 by rw [pow_succ]; omega, Nat.bit1_bits, ih,
      List.replicate_succ]

/-- The number of rounds in binary is `(w + 2) * (d + 1)` ones. -/
private theorem encNat_steps (w d : ℕ) :
    encNat (steps w d) = List.replicate ((w + 2) * (d + 1)) true := by
  rw [encNat_apply, steps, bits_two_pow_sub_one]

/-- A round of writing the number of rounds: `p` more ones. -/
private def countStep (p : ℕ) (acc : List Bool) (_ : Bool) : List Bool :=
  acc ++ List.replicate p true

/-- Writing the number of rounds, `p` ones at a time. -/
private theorem foldl_countStep (p n : ℕ) (acc : List Bool) :
    (List.replicate n true).foldl (countStep p) acc = acc ++ List.replicate (n * p) true := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons, ih, countStep, List.append_assoc,
      ← List.replicate_add]
    congr 2
    ring

/-- The number of rounds, `(w + 2) * (d + 1)` ones in binary, from `w` and `d` in unary. -/
private theorem steps_inO :
    ComputableTidilyInO (fun t : ℕ × ℕ => steps t.1 t.2) (encPair encUnary encUnary)
      encNat (fun t => (t.2 + 2) * ((t.1 + 2) * (t.2 + 1))) fun t => (t.1 + 2) * (t.2 + 1) := by
  have hpar : ComputableTidilyInDegree (fun t : ℕ × ℕ => t.1 + 2) (encPair encUnary encUnary)
      encUnary 1 1 :=
    (unary_succ.comp (unary_succ.comp (fst encUnary encUnary))).mono
  have hlist : ComputableTidilyInDegree (fun t : ℕ × ℕ => List.replicate (t.2 + 1) true)
      (encPair encUnary encUnary) encBits 1 1 :=
    ((unary_succ.comp (snd encUnary encUnary)).mono).of_enc_eq fun _ => rfl
  have hstep : ComputableTidilyInDegree
      (fun r : (ℕ × List Bool) × Bool => countStep r.1.1 r.1.2 r.2)
      (encPair (encPair encUnary encBits) encBool) encBits 1 1 :=
    (((snd encUnary encBits).comp (fst (encPair encUnary encBits) encBool)).append
      ((fst encUnary encBits).comp (fst (encPair encUnary encBits) encBool))
      (enc₂ := encUnary) fun _ => rfl).mono
  have hacc (t : ℕ × ℕ) (i : ℕ) : (((List.replicate (t.2 + 1) true).take i).foldl
      (countStep (t.1 + 2)) []).length ≤ (t.1 + 2) * (t.2 + 1) := by
    rw [List.take_replicate, foldl_countStep, List.nil_append, List.length_replicate]
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (min_le_right _ _)
  have hfold := (ComputableInO.foldlWith (encL := encBits) (encB := encBits)
    hpar.inO_one.computableInO hlist.inO_one.computableInO
    (ComputableTidilyInO.const []).computableInO hstep.inO_one.computableInO
    (R := fun t => 6 * ((t.1 + 2) * (t.2 + 1)) + 4)
    (Q := fun t => 6 * ((t.1 + 2) * (t.2 + 1)) + 4)
    (B := fun t => (t.1 + 2) * (t.2 + 1))
    (fun t i _ => by
      have := hacc t i
      simp only [length_encPair, encUnary_apply, encBits_apply, encBool_apply,
        List.length_replicate, List.length_singleton]
      nlinarith)
    (fun t i _ => by
      have := hacc t i
      simp only [length_encPair, encUnary_apply, encBits_apply, encBool_apply,
        List.length_replicate, List.length_singleton]
      nlinarith)
    (fun t i _ => by simpa using hacc t i)).tidy
  refine (hfold.mono 32 (fun t => ?_) fun t => ?_).of_enc_eq fun t => ?_
  all_goals
    have hK : t.1 + t.2 + 2 ≤ (t.1 + 2) * (t.2 + 1) := by nlinarith
  · simp only [length_encPair, encUnary_apply, encBits_apply, List.length_replicate]
    generalize (t.1 + 2) * (t.2 + 1) = K at hK ⊢
    nlinarith
  · simp only [length_encPair, encUnary_apply, encBits_apply, List.length_replicate]
    generalize (t.1 + 2) * (t.2 + 1) = K at hK ⊢
    nlinarith
  · rw [encNat_steps, foldl_countStep, List.nil_append, encBits_apply, Nat.mul_comm]

/-! ### The first round and the answer -/

/-- The first round, from the arguments, in linear time. -/
private lemma init_deg : ComputableTidilyInDegree
    (fun t : π × ℕ × ℕ × List Bool × List Bool =>
      ((t.1, t.2.1), State.mk [] (.call t.2.2.1 t.2.2.2.1 t.2.2.2.2)))
    (encArgs encP) (encRound encP) 1 1 := by
  fun_prop (disch := first | apply le_refl | lia)

/-- The width and the depth, from the arguments, in linear time. -/
private lemma widthDepth_deg : ComputableTidilyInDegree
    (fun t : π × ℕ × ℕ × List Bool × List Bool => (t.2.1, t.2.2.1)) (encArgs encP)
    (encPair encUnary encUnary) 1 1 := by
  fun_prop (disch := first | apply le_refl | lia)

/-- The answer, from a round, in linear time. -/
private lemma answer_deg : ComputableTidilyInDegree
    (fun q : (π × ℕ) × State => q.2.reg.toPair.2) (encRound encP) encBool 1 1 := by
  fun_prop (disch := first | apply le_refl | lia)

/-- The answer is the second component of the register as a pair. -/
private theorem answer_eq (r : Reg) : r.answer = r.toPair.2 := by
  cases r <;> rfl

/-- There are `2 ^ ((w + 2) * (d + 1))` states in a run, counting the first. -/
private theorem steps_add_one (w d : ℕ) :
    steps w d + 1 = 2 ^ ((w + 2) * (d + 1)) :=
  Nat.sub_add_cancel Nat.one_le_two_pow

/-- The counter of the rounds has `(w + 2) * (d + 1)` digits. -/
private theorem length_encNat_steps (w d : ℕ) :
    (encNat (steps w d)).length = (w + 2) * (d + 1) := by
  rw [encNat_steps, List.length_replicate]

/-- The arithmetic of the bounds of `computableTidilyInO_savitch`, where `S₀ = (d + 1) *
(d + w + 1) + P` bounds the stack and the parameter. -/
private theorem savitch_bounds (P w d : ℕ) :
    stateBound P w d + 1 ≤ 27 * ((d + 1) * (d + w + 1) + P + 1) ∧
      (w + 2) * (d + 1) + 1 ≤ 2 * ((d + 1) * (d + w + 1) + P + 1) ∧
      d + 2 ≤ (d + 1) * (d + w + 1) + P + 1 := by
  simp only [stateBound]
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

end Certificates

end Savitch

/-! ### Savitch's algorithm in the space of its stack -/

open Savitch in
/-- **Savitch's algorithm in the space of its stack.** Let the edge test `edge p` be tidily
computable within time `O(Te)` and space `O(Se)`, and let the parameter, the width `w` and depth
`d` in unary, and endpoints of width `w` be computable from `x` within time `O(Tin)` and space
`O(Sin)`. Then Savitch's algorithm is tidily computable within time
`O(Tin + 2 ^ ((w + 2) * (d + 1)) * (S₀ ^ 2 + Te))` and space `O(Sin + S₀ + Se)`, with
`S₀ = (d + 1) * (d + w + 1) + |p|` and `Te`, `Se` at the worst endpoints of width `w`
(`Cslib.Reachability.edgeMax`). The space charges the stack of at most `d` frames, each with a
level and three words, the register, the parameter, the width, and the counter of the rounds; the
time charges every round, which copies the state [Sipser, Theorem 8.5][Sipser2013]
[Arora and Barak, Section 4.2][AroraBarak09]. -/
private theorem computableTidilyInO_savitch {γ : Type} {encIn : γ ↪ List Bool}
    {edge : π → List Bool → List Bool → Bool} {Te Se : π × List Bool × List Bool → ℕ}
    (hedge : ComputableTidilyInO (fun q : π × List Bool × List Bool => edge q.1 q.2.1 q.2.2)
      (encPair encP (encPair encBits encBits)) encBool Te Se)
    {par : γ → π} {width depth : γ → ℕ} {src dst : γ → List Bool} {Tin Sin : γ → ℕ}
    (hin : ComputableTidilyInO (fun x => (par x, width x, depth x, src x, dst x)) encIn
      (encArgs encP) Tin Sin)
    (hsrc : ∀ x, (src x).length = width x) (hdst : ∀ x, (dst x).length = width x) :
    ComputableTidilyInO (fun x => savitch (edge (par x)) (width x) (depth x) (src x) (dst x))
      encIn encBool
      (fun x => Tin x + 2 ^ ((width x + 2) * (depth x + 1)) *
        (((depth x + 1) * (depth x + width x + 1) + (encP (par x)).length + 1) ^ 2 +
          edgeMax Te (par x) (width x)))
      fun x => Sin x + (depth x + 1) * (depth x + width x + 1) + (encP (par x)).length +
        edgeMax Se (par x) (width x) := by
  rcases isEmpty_or_nonempty γ with hγ | ⟨⟨x₀⟩⟩
  · exact ((ComputableTidilyInO.const (encMid := encBool) false).mono 0 (fun x => isEmptyElim x)
      fun x => isEmptyElim x).of_enc_eq fun x => isEmptyElim x
  have : Inhabited π := ⟨par x₀⟩
  have hn := steps_inO.comp (widthDepth_deg.inO_one.comp_linear hin)
  have hinit := init_deg.inO_one.comp_linear hin
  -- every state of the run is a state of a run from a call at level `depth x`
  have hinv (x : γ) (k : ℕ) : Invariant (width x) (depth x)
      ((step (edge (par x)) (width x))^[k] ⟨[], .call (depth x) (src x) (dst x)⟩) :=
    invariant_iterate (w := width x) (d := depth x)
      (s := ⟨[], .call (depth x) (src x) (dst x)⟩) _ ⟨trivial, fun i u v h => by
        obtain ⟨rfl, rfl, rfl⟩ := Reg.call.inj h
        exact ⟨by simp, hsrc x, hdst x⟩⟩ k
  have hiter := (ComputableInO.iterate hn.computableInO hinit.computableInO
    (computableInO_roundStep hedge.computableInO)
    (R := fun x => (stateBound (encP (par x)).length (width x) (depth x) + 1) ^ 2 +
      edgeMax Te (par x) (width x))
    (Q := fun x => stateBound (encP (par x)).length (width x) (depth x) +
      edgeMax Se (par x) (width x))
    (B := fun x => stateBound (encP (par x)).length (width x) (depth x))
    (fun x k _ => by
      simp only [Function.comp_apply, roundStep_iterate]
      exact Nat.add_le_add (Nat.pow_le_pow_left (Nat.add_le_add_right
        (length_encRound_le (hinv x k)) 1) 2) (edgeCost_le Te _ (hinv x k)))
    (fun x k _ => by
      simp only [Function.comp_apply, roundStep_iterate]
      exact Nat.add_le_add (length_encRound_le (hinv x k)) (edgeCost_le Se _ (hinv x k)))
    (fun x k _ => by
      simp only [Function.comp_apply, roundStep_iterate]
      exact length_encRound_le (hinv x k))).tidy
  refine ((answer_deg.inO_one.comp_linear hiter).mono 900 (fun x => ?_) fun x => ?_).of_enc_eq
    fun x => ?_
  all_goals simp only [Function.comp_apply]
  · rw [steps_add_one, length_encNat_steps]
    obtain ⟨h₁, h₂, h₃⟩ := savitch_bounds (encP (par x)).length (width x) (depth x)
    generalize stateBound (encP (par x)).length (width x) (depth x) = B at h₁ ⊢
    generalize (depth x + 1) * (depth x + width x + 1) + (encP (par x)).length = S at h₁ h₂ h₃ ⊢
    generalize (width x + 2) * (depth x + 1) = K at h₂ ⊢
    generalize edgeMax Te (par x) (width x) = E
    have hM : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    generalize 2 ^ K = M at hM ⊢
    have hB := Nat.pow_le_pow_left h₁ 2
    have hK := Nat.pow_le_pow_left h₂ 2
    have hdK := Nat.mul_le_mul h₃ (show K ≤ 2 * (S + 1) by omega)
    rw [Nat.mul_pow] at hB hK
    have hround : (B + 1) ^ 2 + E + B + (K + 1) ^ 2 ≤ 760 * (S + 1) ^ 2 + E := by nlinarith
    have := Nat.mul_le_mul_left M hround
    have : (S + 1) ^ 2 ≤ M * (S + 1) ^ 2 := Nat.le_mul_of_pos_left _ hM
    nlinarith
  · rw [length_encNat_steps]
    obtain ⟨h₁, h₂, -⟩ := savitch_bounds (encP (par x)).length (width x) (depth x)
    simp only [stateBound] at h₁ ⊢
    nlinarith
  · rw [roundStep_iterate, savitch, answer_eq]

/-- **Savitch's algorithm in the space of its stack.** If the edge test is computable with time
`Te` and space `Se`, and the parameter, the width and depth in unary, and endpoints of width `w`
are computable from `x` with time `Tin` and space `Sin`, then Savitch's algorithm is computable
within space `O(Sin + (d + 1) * (d + w + 1) + |par| + edgeMax Se)` and exponential time. -/
theorem computableInO_savitch {γ : Type} {encIn : γ ↪ List Bool}
    {edge : π → List Bool → List Bool → Bool} {Te Se : π × List Bool × List Bool → ℕ}
    (hedge : ComputableInO (fun q : π × List Bool × List Bool => edge q.1 q.2.1 q.2.2)
      (encPair encP (encPair encBits encBits)) encBool Te Se)
    {par : γ → π} {width depth : γ → ℕ} {src dst : γ → List Bool} {Tin Sin : γ → ℕ}
    (hin : ComputableInO (fun x => (par x, width x, depth x, src x, dst x)) encIn
      (encArgs encP) Tin Sin)
    (hsrc : ∀ x, (src x).length = width x) (hdst : ∀ x, (dst x).length = width x) :
    ComputableInO (fun x => savitch (edge (par x)) (width x) (depth x) (src x) (dst x))
      encIn encBool
      (fun x => Tin x + 2 ^ ((width x + 2) * (depth x + 1)) *
        (((depth x + 1) * (depth x + width x + 1) + (encP (par x)).length + 1) ^ 2 +
          edgeMax Te (par x) (width x)))
      fun x => Sin x + (depth x + 1) * (depth x + width x + 1) + (encP (par x)).length +
        edgeMax Se (par x) (width x) :=
  (computableTidilyInO_savitch hedge.tidy hin.tidy hsrc hdst).computableInO

/-- **Savitch's algorithm in polynomial space.** If the edge test is computable in polynomial time,
and the parameter, the width and depth in unary, and endpoints of width `w` are computable from `x`
in polynomial time, then Savitch's algorithm is computable within space polynomial in the length of
the encoded input; the time is exponential, see `Cslib.Reachability.computableInO_savitch`. The
width and the depth are polynomial since they are computed in unary
[Sipser, Theorem 8.5][Sipser2013]. -/
theorem exists_polyBounded_space_savitch {γ : Type} {encIn : γ ↪ List Bool}
    {edge : π → List Bool → List Bool → Bool}
    (hedge : ComputableInPolyTime (fun q : π × List Bool × List Bool => edge q.1 q.2.1 q.2.2)
      (encPair encP (encPair encBits encBits)) encBool)
    {par : γ → π} {width depth : γ → ℕ} {src dst : γ → List Bool}
    (hin : ComputableInPolyTime (fun x => (par x, width x, depth x, src x, dst x)) encIn
      (encArgs encP))
    (hsrc : ∀ x, (src x).length = width x) (hdst : ∀ x, (dst x).length = width x) :
    ∃ t s, PolyBounded (fun x => (encIn x).length) s ∧
      ComputableInTimeAndSpace
        (fun x => savitch (edge (par x)) (width x) (depth x) (src x) (dst x)) encIn encBool t
        s := by
  have hlen := hin.tidy.polyBounded_length
  obtain ⟨_, se, -, hse, hedgeO⟩ := hedge.exists_computableInO
  obtain ⟨_, si, -, hsi, hinO⟩ := hin.exists_computableInO
  obtain ⟨cs, ds, hcs⟩ := hse.exists_le
  obtain ⟨c, h, -⟩ := computableInO_savitch hedgeO hinO hsrc hdst
  refine ⟨_, _, ?_, h⟩
  -- the stack, the parameter and the edge test are polynomial in the encoded arguments
  set L := fun x => (encArgs encP (par x, width x, depth x, src x, dst x)).length
  have hL (x : γ) : depth x ≤ L x ∧ width x ≤ L x ∧ (encP (par x)).length ≤ L x := by
    simp only [L, encArgs, length_encPair, encUnary_apply, List.length_replicate]
    omega
  have hE (x : γ) : edgeMax se (par x) (width x) ≤ cs * (5 * L x + 3) ^ ds :=
    listMax_le fun u hu => listMax_le fun v hv => by
      refine (hcs _).trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left ?_ ds))
      have := hL x
      simp only [length_encPair, encBits_apply, mem_enumList.mp hu, mem_enumList.mp hv]
      omega
  have hpoly : Cslib.PolynomiallyBounded
      fun n => (n + 1) * (2 * n + 1) + n + cs * (5 * n + 3) ^ ds + 1 := by
    fun_prop
  have hg : PolyBounded (fun x => (encIn x).length)
      fun x => (L x + 1) * (2 * L x + 1) + L x + cs * (5 * L x + 3) ^ ds + 1 :=
    PolyBounded.comp (size' := id) (g := L) (PolyBounded.of_polynomiallyBounded id hpoly) hlen
  refine ((PolyBounded.const c).mul (hsi.add hg)).mono fun x => ?_
  obtain ⟨hd, hw, hP⟩ := hL x
  have := Nat.mul_le_mul (show depth x + 1 ≤ L x + 1 by omega)
    (show depth x + width x + 1 ≤ 2 * L x + 1 by omega)
  dsimp only
  exact Nat.mul_le_mul_left c (by have := hE x; omega)

end Cslib.Reachability

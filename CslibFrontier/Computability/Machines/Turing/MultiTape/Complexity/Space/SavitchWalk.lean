/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.SavitchWalk
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.ZipTransducer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeUnaryPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Tactic.EncLen
import Mathlib.Tactic.Linarith

/-!
# Following a walk in the space of its stack

The walk of `Cslib.Reachability.Walk.step` visits the vertices of a path, one per step, holding a
stack of pending targets. This file bounds the work space of a step on multi-tape machines, in the
plain space calculus (`Turing.MultiTapeTM.ComputableInSpace`).

The midpoint of a call at level `i + 1` between words of width `w`
(`Cslib.Reachability.Walk.midpoint`) streams the candidates through a binary counter, `2 ^ w`
rounds from the word of zeros, and runs Savitch's algorithm twice on each candidate
(`Cslib.Reachability.computableInO_savitch`); it never writes down the list of the words of width
`w`. Its work space is that of the arguments, the counter and one run of Savitch's algorithm:
`O(|args| + (i + 1) * (i + w + 1) + |p| + edgeMax Se p w)`, where `p` is the parameter of the edge
test and `Se` its space (`Cslib.Reachability.Walk.computableInSpace_midpoint`).

A round of the walk (`Cslib.Reachability.Walk.roundStep`) carries the parameter of the edge test
and the width together with the state, whose stack holds the targets with their levels in unary
(`Cslib.Reachability.Walk.encState`). It takes work space linear in the encoded round, plus
`(ℓ + 1) * (ℓ + w + 1)` for the level `ℓ` of the next target, plus the space of the edge test on
words of width `w` (`Cslib.Reachability.Walk.computableInSpace_roundStep`). The states of a run
from a target at level `d` have size `O((d + 1) * (d + w + 1))`
(`Cslib.Reachability.Walk.length_encState_le`), so every round of such a run takes work space
`O((d + 1) * (d + w + 1) + |p| + edgeMax Se p w)`: the `O(d * w)` bits of Savitch's algorithm.
Iterating the rounds under a binary counter of steps, the state after any number `n` of steps
costs the same work space, plus that of the inputs and `O(log n)` for the counter
(`Cslib.Reachability.Walk.computableInSpace_run`).

## Main definitions

* `Cslib.Reachability.Walk.encEdgeArgs`: the input of an edge test.
* `Cslib.Reachability.Walk.encEntry`, `Cslib.Reachability.Walk.encState`: the encoded states.
* `Cslib.Reachability.Walk.roundStep`, `Cslib.Reachability.Walk.encRound`: a step carrying the
  parameter of the edge test and the width, and its encoding.
* `Cslib.Reachability.Walk.topLevel`: the level of the next target.

## Main results

* `Cslib.Reachability.Walk.computableInSpace_midpoint`: the work space of a midpoint.
* `Cslib.Reachability.Walk.computableInSpace_roundStep`: the work space of a round.
* `Cslib.Reachability.Walk.roundStep_iterate`: rounds run the walk.
* `Cslib.Reachability.Walk.length_encState_le`, `Cslib.Reachability.Walk.topLevel_le`: the size of
  the states of a run.
* `Cslib.Reachability.Walk.computableInSpace_run`: the work space of a run of `n` steps.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.5][Sipser2013]
* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Section 4.2][AroraBarak09]
-/

public section

namespace Cslib.Reachability.Walk

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

variable {π : Type} {encP : π ↪ List Bool}

/-- The input of an edge test: its parameter and two words. -/
abbrev encEdgeArgs (encP : π ↪ List Bool) : π × List Bool × List Bool ↪ List Bool :=
  encPair encP (encPair encBits encBits)

/-! ### Words of a given width -/

/-- Reads a width in unary next to a word: keeps a digit of the word for every digit of the width,
and writes `false` once the word is exhausted. -/
private def fitZip : ZipTransducer Unit where
  q₀ := ()
  step _ x := ((), if x.1.isSome then [x.2.getD false] else [])
  final _ := []
  length_step_le _ x := by split_ifs <;> simp
  length_final_le _ := by simp

private theorem fitZip_step (x : Option Bool × Option Bool) :
    fitZip.step () x = ((), if x.1.isSome then [x.2.getD false] else []) := rfl

private theorem fitZip_final : fitZip.final () = [] := rfl

private theorem fitZip_run_nil (u : List Bool) : fitZip.run () [] u = [] := by
  induction u with
  | nil => exact (fitZip.run_nil_nil ()).trans fitZip_final
  | cons a u ih => simp only [ZipTransducer.run_nil_cons, fitZip_step, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, List.nil_append, ih]

private theorem fitZip_run (w : ℕ) (u : List Bool) :
    fitZip.run () (List.replicate w true) u = u.takeD w false := by
  induction w generalizing u with
  | zero => exact fitZip_run_nil u
  | succ w ih =>
    cases u with
    | nil => simp [List.replicate_succ, fitZip_step, ih]
    | cons a u => simp [List.replicate_succ, fitZip_step, ih]

/-- **A word fitted to a width**, by keeping or padding its digits, in linear space. -/
private theorem fit_inSpace :
    ComputableInSpace (fun q : ℕ × List Bool => q.2.takeD q.1 false) (encPair encUnary encBits)
      encBits fun q => (encPair encUnary encBits q).length :=
  of_inO (ZipTransducer.computableInDegree fitZip fun q => by
    rw [encBits_apply, encUnary_apply, encBits_apply, fitZip_run]).inO_one

/-- Reads a width in unary next to a word, and tells whether they have the same length. -/
private def widthZip : ZipTransducer Bool where
  q₀ := true
  step b x := (b && (x.1.isSome == x.2.isSome), [])
  final b := [b]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private theorem widthZip_step (b : Bool) (x : Option Bool × Option Bool) :
    widthZip.step b x = (b && (x.1.isSome == x.2.isSome), []) := rfl

private theorem widthZip_final (b : Bool) : widthZip.final b = [b] := rfl

private theorem widthZip_run_nil (u : List Bool) (b : Bool) :
    widthZip.run b [] u = [b && decide (u.length = 0)] := by
  induction u generalizing b with
  | nil => simp [widthZip_final]
  | cons a u ih => simp [widthZip_step, ih]

private theorem widthZip_run (w : ℕ) (u : List Bool) (b : Bool) :
    widthZip.run b (List.replicate w true) u = [b && decide (u.length = w)] := by
  induction w generalizing u b with
  | zero => exact widthZip_run_nil u b
  | succ w ih =>
    cases u with
    | nil => simp [List.replicate_succ, widthZip_step, ih]
    | cons a u => simp [List.replicate_succ, widthZip_step, ih]

/-- **Whether a word has a given width**, in linear space. -/
private theorem width_inSpace :
    ComputableInSpace (fun q : ℕ × List Bool => decide (q.2.length = q.1))
      (encPair encUnary encBits) encBool fun q => (encPair encUnary encBits q).length :=
  of_inO (ZipTransducer.computableInDegree widthZip fun q => by
    rw [encBool_apply, encUnary_apply, encBits_apply, show widthZip.q₀ = true from rfl,
      widthZip_run, Bool.true_and]).inO_one

/-- Writes `false` for every digit of a width in unary, then `true` if `top` holds. -/
private def zerosT (top : Bool) : Transducer Bool Unit where
  q₀ := ()
  step _ _ := ((), [false])
  final _ := if top then [true] else []
  length_step_le _ _ := by simp
  length_final_le _ := by split_ifs <;> simp

private theorem zerosT_run (top : Bool) (w : ℕ) (q : Unit) :
    (zerosT top).run q (List.replicate w true) =
      List.replicate w false ++ if top then [true] else [] := by
  induction w generalizing q with
  | zero => rfl
  | succ w ih => exact congrArg (false :: ·) (ih ())

/-- **The word of zeros of a width**, in linear space. -/
private theorem zeros_inSpace :
    ComputableInSpace (fun w => List.replicate w false) encUnary encBits
      fun w => (encUnary w).length :=
  of_inO (ComputableInDegree.of_transducer (zerosT false) fun w => by
    rw [encBits_apply, encUnary_apply, zerosT_run]
    simp).inO_one

/-- `2 ^ w` in binary is `w` zeros and a one. -/
private theorem bits_two_pow (w : ℕ) : Nat.bits (2 ^ w) = List.replicate w false ++ [true] := by
  induction w with
  | zero => exact Nat.one_bits
  | succ w ih =>
    rw [pow_succ, mul_comm, Nat.bit0_bits _ (pow_ne_zero w two_ne_zero), ih]
    rfl

/-- **`2 ^ w` in binary, from `w` in unary**, in linear space. -/
private theorem twoPow_inSpace :
    ComputableInSpace (fun w => 2 ^ w) encUnary encNat fun w => (encUnary w).length :=
  of_inO (ComputableInDegree.of_transducer (zerosT true) fun w => by
    rw [encNat_apply, bits_two_pow, encUnary_apply, zerosT_run]
    rfl).inO_one

/-- **The binary counter**, in linear space. -/
private theorem increment_inSpace :
    ComputableInSpace BitString.increment encBits encBits fun m => (encBits m).length :=
  of_inO ComputableTidilyInDegree.increment.inO_one.computableInO

/-- The identity, in linear space. -/
private theorem id_inSpace {α : Type} {enc : α ↪ List Bool} :
    ComputableInSpace (fun a : α => a) enc enc fun a => (enc a).length :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

/-! ### The midpoint, by a counter and Savitch's algorithm -/

/-- The arguments of a midpoint: the parameter of the edge test, the width and the level in unary,
and the endpoints. -/
private abbrev Args (π : Type) : Type := π × ℕ × ℕ × List Bool × List Bool

/-- Whether a candidate passes, by Savitch's algorithm on the words fitted to the width: the
first endpoint reaches it and it reaches the second endpoint. -/
private def loopTest (edge : π → List Bool → List Bool → Bool) (a : Args π) (m : List Bool) :
    Bool :=
  savitch (edge a.1) a.2.1 a.2.2.1 (a.2.2.2.1.takeD a.2.1 false) (m.takeD a.2.1 false) &&
    savitch (edge a.1) a.2.1 a.2.2.1 (m.takeD a.2.1 false) (a.2.2.2.2.takeD a.2.1 false)

/-- A round of the search for a midpoint, keeping the arguments. -/
private def loopStep (edge : π → List Bool → List Bool → Bool) (s : Args π × List Bool) :
    Args π × List Bool :=
  (s.1, if loopTest edge s.1 s.2 then s.2 else BitString.increment s.2)

private theorem iterate_loopStep (edge : π → List Bool → List Bool → Bool) (a : Args π)
    (m : List Bool) (k : ℕ) :
    (loopStep edge)^[k] (a, m) = (a, (searchStep (loopTest edge a))^[k] m) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']; rfl

/-- The midpoint by `2 ^ w` rounds of the search from the word of zeros, when the endpoints have
width `w`. -/
private def midLoop (edge : π → List Bool → List Bool → Bool) (a : Args π) : List Bool :=
  if decide (a.2.2.2.1.length = a.2.1) && decide (a.2.2.2.2.length = a.2.1) then
    ((loopStep edge)^[2 ^ a.2.1] (a, List.replicate a.2.1 false)).2
  else List.replicate a.2.1 false

private theorem takeD_of_length_eq {u : List Bool} {w : ℕ} (h : u.length = w) :
    u.takeD w false = u := by
  rw [List.takeD_eq_take _ h.ge, List.take_of_length_le h.le]

private theorem midLoop_eq (edge : π → List Bool → List Bool → Bool) (p : π) (w i : ℕ)
    (u v : List Bool) : midLoop edge (p, w, i, u, v) = midpoint (edge p) w i u v := by
  by_cases h : u.length = w ∧ v.length = w
  · obtain ⟨hu, hv⟩ := h
    simp only [midLoop, midpoint, hu, hv, decide_true, Bool.and_self, and_self, ↓reduceIte,
      iterate_loopStep]
    refine search_congr fun m hm => ?_
    simp only [loopTest, takeD_of_length_eq hu, takeD_of_length_eq hv, takeD_of_length_eq hm,
      savitch_eq]
  · have hf : (decide (u.length = w) && decide (v.length = w)) = false := by
      simpa only [Bool.and_eq_false_iff, decide_eq_false_iff_not, ← not_and_or] using h
    rw [midLoop, midpoint, ite_eq_right h]
    simp only [hf, Bool.false_eq_true, ↓reduceIte]

/-- The encoded state of the search: the arguments and the candidate. -/
private abbrev encLoop (encP : π ↪ List Bool) : Args π × List Bool ↪ List Bool :=
  encPair (encArgs encP) encBits

/-- The work space of a midpoint: the arguments, and Savitch's algorithm at width `w` and level
`i`. -/
private def loopSpace (encP : π ↪ List Bool) (Se : π × List Bool × List Bool → ℕ) (a : Args π) :
    ℕ :=
  (encArgs encP a).length + (a.2.2.1 + 1) * (a.2.2.1 + a.2.1 + 1) + (encP a.1).length +
    edgeMax Se a.1 a.2.1

/-- **The midpoint in the space of the arguments and of Savitch's algorithm.** -/
private theorem midLoop_inSpace [Inhabited π] {edge : π → List Bool → List Bool → Bool}
    {Te Se : π × List Bool × List Bool → ℕ}
    (hedge : ComputableInO (fun q : π × List Bool × List Bool => edge q.1 q.2.1 q.2.2)
      (encEdgeArgs encP) encBool Te Se) :
    ComputableInSpace (midLoop edge) (encArgs encP) encBits (loopSpace encP Se) := by
  -- the rounds of the search, within the encoded round and Savitch's algorithm
  let Bl : Args π × List Bool → ℕ := fun s => (encLoop encP s).length + loopSpace encP Se s.1
  have hBl : (fun s => (encLoop encP s).length) ≼ Bl := .of_le fun _ => Nat.le_add_right _ _
  have hid : ComputableInSpace (fun s : Args π × List Bool => s) (encLoop encP) (encLoop encP)
      Bl := id_inSpace.weaken hBl
  have ha := fst' hid
  have hm := snd' hid
  have hp := fst' ha
  have hw := fst' (snd' ha)
  have hi := fst' (snd' (snd' ha))
  have hu := fst' (snd' (snd' (snd' ha)))
  have hv := snd' (snd' (snd' (snd' ha)))
  have hfit {g : Args π × List Bool → List Bool}
      (hg : ComputableInSpace g (encLoop encP) encBits Bl) :
      ComputableInSpace (fun s => (g s).takeD s.1.2.1 false) (encLoop encP) encBits Bl :=
    budget_comp_linear fit_inSpace (budget_prod hw hg)
  have hsav {g₁ g₂ : Args π × List Bool → List Bool}
      (h₁ : ComputableInSpace g₁ (encLoop encP) encBits Bl)
      (h₂ : ComputableInSpace g₂ (encLoop encP) encBits Bl) :
      ComputableInSpace (fun s => savitch (edge s.1.1) s.1.2.1 s.1.2.2.1
        ((g₁ s).takeD s.1.2.1 false) ((g₂ s).takeD s.1.2.1 false)) (encLoop encP) encBool Bl := by
    have hin := budget_prod hp (budget_prod hw (budget_prod hi (budget_prod (hfit h₁) (hfit h₂))))
    obtain ⟨Tin, hinO⟩ := hin.exists_inO
    refine (of_inO (computableInO_savitch (edge := edge) hedge hinO
      (fun _ => List.takeD_length ..) fun _ => List.takeD_length ..)).weaken
      (.of_le_linear 2 0 fun s => ?_)
    have h₁ : (encP s.1.1).length ≤ (encArgs encP s.1).length := length_le_encPair_left _ _ _
    have h₂ : (encArgs encP s.1).length ≤ (encLoop encP s).length := length_le_encPair_left _ _ _
    simp only [Bl, loopSpace]
    omega
  have htest : ComputableInSpace (fun s => loopTest edge s.1 s.2) (encLoop encP) encBool Bl :=
    budget_finite (fun b : Bool × Bool => b.1 && b.2) (budget_prod (hsav hu hm) (hsav hm hv))
  have hstep : ComputableInSpace (loopStep edge) (encLoop encP) (encLoop encP) Bl :=
    budget_prod ha (budget_ite htest hm (budget_comp_linear increment_inSpace hm))
  -- the iteration, `2 ^ w` rounds from the word of zeros
  have hidA : ComputableInSpace (fun a : Args π => a) (encArgs encP) (encArgs encP)
      fun a => (encArgs encP a).length := id_inSpace
  have hwA := fst' (snd' hidA)
  have huA := fst' (snd' (snd' (snd' hidA)))
  have hvA := snd' (snd' (snd' (snd' hidA)))
  have hn := budget_comp_linear twoPow_inSpace hwA
  have hinit : ComputableInSpace (fun a : Args π => (a, List.replicate a.2.1 false)) (encArgs encP)
      (encLoop encP) fun a => (encArgs encP a).length :=
    budget_prod hidA (budget_comp_linear zeros_inSpace hwA)
  have hlen (a : Args π) (k : ℕ) :
      (encLoop encP ((loopStep edge)^[k] (a, List.replicate a.2.1 false))).length =
        2 * (encArgs encP a).length + 1 + a.2.1 := by
    rw [iterate_loopStep, length_encPair, encBits_apply, length_iterate_searchStep,
      List.length_replicate]
  have hbound (a : Args π) (k : ℕ) :
      Bl ((loopStep edge)^[k] (a, List.replicate a.2.1 false)) ≤ 4 * loopSpace encP Se a + 1 ∧
        (encLoop encP ((loopStep edge)^[k] (a, List.replicate a.2.1 false))).length ≤
          4 * loopSpace encP Se a + 1 := by
    have hwl : a.2.1 ≤ (encArgs encP a).length := by
      obtain ⟨p, w, i, u, v⟩ := a
      enc_len
    have hfst : ((loopStep edge)^[k] (a, List.replicate a.2.1 false)).1 = a := by
      rw [iterate_loopStep]
    have hB : Bl ((loopStep edge)^[k] (a, List.replicate a.2.1 false)) =
        2 * (encArgs encP a).length + 1 + a.2.1 + loopSpace encP Se a := by
      simp only [Bl]
      rw [hfst, hlen]
    rw [hB, hlen]
    simp only [loopSpace]
    constructor <;> omega
  have hiter := iterate hn hinit hstep (Q := fun a => 4 * loopSpace encP Se a + 1)
    (B := fun a => 4 * loopSpace encP Se a + 1) (fun a k _ => (hbound a k).1)
    fun a k _ => (hbound a k).2
  -- the guard on the widths of the endpoints
  have hguard : ComputableInSpace
      (fun a : Args π => decide (a.2.2.2.1.length = a.2.1) && decide (a.2.2.2.2.length = a.2.1))
      (encArgs encP) encBool fun a => (encArgs encP a).length :=
    budget_finite (fun b : Bool × Bool => b.1 && b.2)
      (budget_prod (budget_comp_linear width_inSpace (budget_prod hwA huA))
        (budget_comp_linear width_inSpace (budget_prod hwA hvA)))
  have hL : (fun a => (encArgs encP a).length) ≼ loopSpace encP Se :=
    .of_le fun a => by simp only [loopSpace]; omega
  have hiterL := (snd' hiter).weaken (S₁ := loopSpace encP Se) (.of_le_linear 11 3 fun a => by
    have hn : (encNat (2 ^ a.2.1)).length = a.2.1 + 1 := by
      rw [encNat_apply, bits_two_pow, List.length_append, List.length_replicate,
        List.length_singleton]
    have hwl : a.2.1 ≤ (encArgs encP a).length := by
      obtain ⟨p, w, i, u, v⟩ := a
      enc_len
    simp only [hn, loopSpace]
    omega)
  exact budget_ite (hguard.weaken hL) hiterL ((budget_comp_linear zeros_inSpace hwA).weaken hL)

/-- **The midpoint in the space of Savitch's algorithm.** Let the edge test `edge p` be computable
within time `O(Te)` and space `O(Se)`, and let the parameter, the width `w` and the level `i` in
unary, and the endpoints be computable from `x` within space `O(Sin)`. Then the midpoint of the call
at level `i + 1` is computable within space `O(Sin + (i + 1) * (i + w + 1) + |p| + edgeMax Se p w)`:
the candidates stream through a binary counter, and each is tested by two runs of Savitch's
algorithm [Sipser, Theorem 8.5][Sipser2013]. -/
theorem computableInSpace_midpoint {γ : Type} {encIn : γ ↪ List Bool}
    {edge : π → List Bool → List Bool → Bool} {Te Se : π × List Bool × List Bool → ℕ}
    (hedge : ComputableInO (fun (p, u, v) => edge p u v) (encEdgeArgs encP) encBool Te Se)
    {par : γ → π} {width level : γ → ℕ} {src dst : γ → List Bool} {Sin : γ → ℕ}
    (hin : ComputableInSpace (fun x => (par x, width x, level x, src x, dst x)) encIn
      (encArgs encP) Sin) :
    ComputableInSpace (fun x => midpoint (edge (par x)) (width x) (level x) (src x) (dst x))
      encIn encBits fun x => Sin x + (level x + 1) * (level x + width x + 1) +
        (encP (par x)).length + edgeMax Se (par x) (width x) := by
  rcases isEmpty_or_nonempty γ with hγ | ⟨⟨x₀⟩⟩
  · exact ((const (encB := encBits) []).mono_le (fun x => isEmptyElim x)).of_enc_eq
      fun x => isEmptyElim x
  have : Inhabited π := ⟨par x₀⟩
  have hA : (fun x => (encArgs encP (par x, width x, level x, src x, dst x)).length) ≼
      fun x => Sin x + (level x + 1) * (level x + width x + 1) + (encP (par x)).length +
        edgeMax Se (par x) (width x) := hin.length_le.trans_le fun x => by omega
  have hR : (fun x => (level x + 1) * (level x + width x + 1) + (encP (par x)).length +
      edgeMax Se (par x) (width x)) ≼ fun x => Sin x + (level x + 1) * (level x + width x + 1) +
        (encP (par x)).length + edgeMax Se (par x) (width x) := .of_le fun x => by omega
  refine (((midLoop_inSpace (edge := edge) hedge).comp hin).weaken (.add (.of_le fun x => by omega)
    ((BigOLe.of_le fun x => ?_).trans (hA.add hR)))).of_enc_eq fun x => by rw [midLoop_eq]
  simp only [loopSpace]
  omega

/-! ### A round of the walk -/

/-- A pending target encoded as the word followed by its level in unary. -/
abbrev encEntry : List Bool × ℕ ↪ List Bool := encPair encBits encUnary

/-- A state of the walk encoded as the current vertex followed by the list of pending targets. -/
abbrev encState : State ↪ List Bool := encPair encBits (encList encEntry)

/-- **A round of the walk**, carrying the parameter of the edge test and the width with the
state. -/
@[expose] def roundStep (edge : π → List Bool → List Bool → Bool) :
    (π × ℕ) × State → (π × ℕ) × State
  | ((p, w), s) => ((p, w), step (edge p) w s)

/-- A round encoded as the parameter, the width in unary and the state. -/
abbrev encRound (encP : π ↪ List Bool) : (π × ℕ) × State ↪ List Bool :=
  encPair (encPair encP encUnary) encState

/-- The level of the next target, and `0` for an empty stack. -/
@[expose] def topLevel : State → ℕ
  | (_, []) => 0
  | (_, (_, ℓ) :: _) => ℓ

/-- The rounds keep the parameter and the width, and run the walk. -/
theorem roundStep_iterate (edge : π → List Bool → List Bool → Bool) (p : π) (w : ℕ) (s : State)
    (k : ℕ) : (roundStep edge)^[k] ((p, w), s) = ((p, w), (step (edge p) w)^[k] s) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']; rfl

/-- A round as a case distinction on the head of the stack. -/
private def stepIf (edge : π → List Bool → List Bool → Bool) (q : (π × ℕ) × State) :
    (π × ℕ) × State :=
  (q.1, if q.2.2.isEmpty then q.2
    else if decide ((q.2.2.headD default).2 = 0) then ((q.2.2.headD default).1, q.2.2.tail)
    else (q.2.1, (midpoint (edge q.1.1) q.1.2 ((q.2.2.headD default).2 - 1) q.2.1
        (q.2.2.headD default).1, (q.2.2.headD default).2 - 1) ::
      ((q.2.2.headD default).1, (q.2.2.headD default).2 - 1) :: q.2.2.tail))

private theorem stepIf_eq (edge : π → List Bool → List Bool → Bool) (q : (π × ℕ) × State) :
    stepIf edge q = roundStep edge q := by
  obtain ⟨⟨p, w⟩, cur, _ | ⟨⟨t, _ | i⟩, rest⟩⟩ := q <;> rfl

private theorem headD_snd (s : State) : (s.2.headD default).2 = topLevel s := by
  obtain ⟨cur, _ | ⟨⟨t, ℓ⟩, rest⟩⟩ := s <;> rfl

/-- The work space of a round: the encoded round, and Savitch's algorithm at the level of the next
target. -/
private def roundSpace (encP : π ↪ List Bool) (Se : π × List Bool × List Bool → ℕ)
    (q : (π × ℕ) × State) : ℕ :=
  (encRound encP q).length + (topLevel q.2 + 1) * (topLevel q.2 + q.1.2 + 1) +
    edgeMax Se q.1.1 q.1.2

/-- **A round of the walk in the space of the encoded round and of Savitch's algorithm.** Let the
edge test `edge p` be computable within time `O(Te)` and space `O(Se)`. Then a round is computable
within space `O(|round| + (ℓ + 1) * (ℓ + w + 1) + edgeMax Se p w)`, where `ℓ` is the level of the
next target: splitting a target at level `ℓ` finds a midpoint with Savitch's algorithm at level
`ℓ - 1` (`Cslib.Reachability.Walk.computableInSpace_midpoint`); the other cases rearrange the
encoded state. -/
theorem computableInSpace_roundStep {edge : π → List Bool → List Bool → Bool}
    {Te Se : π × List Bool × List Bool → ℕ}
    (hedge : ComputableInO (fun (p, u, v) => edge p u v) (encEdgeArgs encP) encBool Te Se) :
    ComputableInSpace (roundStep edge) (encRound encP) (encRound encP)
      fun ((p, w), s) => (encRound encP ((p, w), s)).length +
        (topLevel s + 1) * (topLevel s + w + 1) + edgeMax Se p w := by
  rcases isEmpty_or_nonempty π with hπ | ⟨⟨p₀⟩⟩
  · exact ((id_inSpace (enc := encRound encP)).mono_le fun q => isEmptyElim q.1.1).of_enc_eq
      fun q => isEmptyElim q.1.1
  have : Inhabited π := ⟨p₀⟩
  let Br := roundSpace encP Se
  have hid : ComputableInSpace (fun q : (π × ℕ) × State => q) (encRound encP) (encRound encP)
      Br := id_inSpace.weaken (.of_le fun _ => by simp only [Br, roundSpace]; omega)
  have hpw := fst' hid
  have hp := fst' hpw
  have hw := snd' hpw
  have hs := snd' hid
  have hcur := fst' hs
  have hstack := snd' hs
  have hhead := budget_headD default hstack
  have ht := fst' hhead
  have hl := snd' hhead
  have hl' := budget_comp_linear (of_inO ComputableInDegree.unary_pred.inO_one) hl
  have htail := budget_tail hstack
  -- the midpoint of the next target and the current vertex
  have hargs := budget_prod hp (budget_prod hw (budget_prod hl' (budget_prod hcur ht)))
  have hmid := (computableInSpace_midpoint (edge := edge) hedge hargs).weaken
    (S₁ := Br) (.add (.add (.add (.refl _) (.of_le fun q => ?_)) (.of_le fun q => ?_))
      (.of_le fun q => ?_))
  rotate_left
  · rw [headD_snd]
    simp only [Br, roundSpace]
    have := Nat.mul_le_mul (show topLevel q.2 - 1 + 1 ≤ topLevel q.2 + 1 by omega)
      (show topLevel q.2 - 1 + q.1.2 + 1 ≤ topLevel q.2 + q.1.2 + 1 by omega)
    omega
  · have : (encP q.1.1).length ≤ (encRound encP q).length :=
      (length_le_encPair_left _ _ _).trans (length_le_encPair_left _ _ _)
    simp only [Br, roundSpace]
    omega
  · simp only [Br, roundSpace]
    omega
  have hsplit := budget_prod hcur (budget_cons (budget_prod hmid hl')
    (budget_cons (budget_prod ht hl') htail))
  have hpop := budget_prod ht htail
  have hzero := budget_comp_linear (of_inO ComputableInDegree.unary_isZero.inO_one) hl
  have hround : ComputableInSpace (stepIf edge) (encRound encP) (encRound encP) Br :=
    budget_prod hpw (budget_ite (budget_isEmpty hstack) hs (budget_ite hzero hpop hsplit))
  exact (hround.of_enc_eq fun q => by rw [stepIf_eq]).mono_le fun ⟨⟨p, w⟩, s⟩ => le_rfl

/-- **The states of a run from a target at level `d` have size `O((d + 1) * (d + w + 1))`**: the
current vertex and at most `d + 1` targets, each a word of width `w` and a level at most `d`. -/
theorem length_encState_le {w d : ℕ} {s : State} (hw : Width w s) (hd : LevelsLE d s.2) :
    (encState s).length ≤ 6 * ((d + 1) * (d + w + 1)) := by
  obtain ⟨cur, stack⟩ := s
  obtain ⟨hc, hst⟩ := hw
  have hlist : (encList encEntry stack).length ≤ stack.length * (2 * (2 * w + 1 + d) + 1) :=
    length_encList_le encEntry stack fun e he => by
      have := hd.le_of_mem e he
      rw [length_encPair, encBits_apply, encUnary_apply, List.length_replicate, hst e he]
      omega
  have hlen := Nat.mul_le_mul_right (2 * (2 * w + 1 + d) + 1) hd.length_le
  rw [length_encPair, encBits_apply, hc]
  nlinarith

/-- The next target of a stack within depth `d` is at a level at most `d`. -/
theorem topLevel_le {d : ℕ} {s : State} (h : LevelsLE d s.2) : topLevel s ≤ d := by
  obtain ⟨cur, _ | ⟨⟨t, ℓ⟩, rest⟩⟩ := s
  · exact Nat.zero_le d
  · exact (Nat.le_add_right ℓ rest.length).trans h.1

/-- **Following a walk in the space of its stack.** Let the edge test `edge p` be computable within
time `O(Te)` and space `O(Se)`, let the parameter, the width `w` and the depth `d` in unary, and
endpoints of width `w` be computable from `x` within space `O(Sin)`, and let the number `n` of steps
be computable in binary within space `O(Sn)`. Then the state of the walk after `n` steps from the
first endpoint towards the second, a target at level `d`, is computable within space
`O(Sin + Sn + log n + (d + 1) * (d + w + 1) + |p| + edgeMax Se p w)`: the stack holds at most
`d + 1` targets of size `O(d + w)`, and a step runs at most one search for a midpoint
(`Cslib.Reachability.Walk.computableInSpace_roundStep`). -/
theorem computableInSpace_run {γ : Type} {encIn : γ ↪ List Bool}
    {edge : π → List Bool → List Bool → Bool} {Te Se : π × List Bool × List Bool → ℕ}
    (hedge : ComputableInO (fun (p, u, v) => edge p u v) (encEdgeArgs encP) encBool Te Se)
    {par : γ → π} {width depth : γ → ℕ} {src dst : γ → List Bool} {steps : γ → ℕ}
    {Sin Sn : γ → ℕ}
    (hin : ComputableInSpace (fun x => (par x, width x, depth x, src x, dst x)) encIn
      (encArgs encP) Sin)
    (hn : ComputableInSpace steps encIn encNat Sn)
    (hsrc : ∀ x, (src x).length = width x) (hdst : ∀ x, (dst x).length = width x) :
    ComputableInSpace
      (fun x => (step (edge (par x)) (width x))^[steps x] (src x, [(dst x, depth x)])) encIn
      encState fun x => Sin x + Sn x + (encNat (steps x)).length +
        (depth x + 1) * (depth x + width x + 1) + (encP (par x)).length +
        edgeMax Se (par x) (width x) := by
  rcases isEmpty_or_nonempty γ with hγ | ⟨⟨x₀⟩⟩
  · exact ((const (encB := encState) default).mono_le (fun x => isEmptyElim x)).of_enc_eq
      fun x => isEmptyElim x
  have : Inhabited π := ⟨par x₀⟩
  -- the first round, from the arguments
  have hidA : ComputableInSpace (fun a : Args π => a) (encArgs encP) (encArgs encP)
      fun a => (encArgs encP a).length := id_inSpace
  have hinit₀ : ComputableInSpace
      (fun a : Args π => ((a.1, a.2.1), (a.2.2.2.1, [(a.2.2.2.2, a.2.2.1)]))) (encArgs encP)
      (encRound encP) fun a => (encArgs encP a).length :=
    budget_prod (budget_prod (fst' hidA) (fst' (snd' hidA)))
      (budget_prod (fst' (snd' (snd' (snd' hidA))))
        (budget_cons (budget_prod (snd' (snd' (snd' (snd' hidA)))) (fst' (snd' (snd' hidA))))
          (budget_const [] (.refl _))))
  have hinit : ComputableInSpace (fun x => ((par x, width x), (src x, [(dst x, depth x)])))
      encIn (encRound encP) Sin := budget_comp_linear hinit₀ hin
  -- every state of the run has width `w` and at most `d + 1` targets
  have hrun (x : γ) (k : ℕ) :=
    roundStep_iterate edge (par x) (width x) (src x, [(dst x, depth x)]) k
  let B : γ → ℕ := fun x =>
    4 * (encP (par x)).length + 2 * width x + 3 + 6 * ((depth x + 1) * (depth x + width x + 1))
  have hbound (x : γ) (k : ℕ) :
      (encRound encP ((par x, width x),
        (step (edge (par x)) (width x))^[k] (src x, [(dst x, depth x)]))).length ≤ B x ∧
      topLevel ((step (edge (par x)) (width x))^[k] (src x, [(dst x, depth x)])) ≤ depth x := by
    have hw := width_iterate (edge (par x)) (s := (src x, [(dst x, depth x)]))
      ⟨hsrc x, by simp [hdst x]⟩ k
    have hd := levelsLE_iterate (edge (par x)) (width x) (s := (src x, [(dst x, depth x)]))
      (levelsLE_singleton (depth x) (dst x)) k
    refine ⟨?_, topLevel_le hd⟩
    have := length_encState_le hw hd
    have h₁ := length_le_encPair_right (encPair encP encUnary) encState
      ((par x, width x), (step (edge (par x)) (width x))^[k] (src x, [(dst x, depth x)]))
    simp only [length_encPair, encUnary_apply, List.length_replicate, B] at this h₁ ⊢
    omega
  have hiter := iterate hn hinit (computableInSpace_roundStep (edge := edge) hedge)
    (Q := fun x => B x + (depth x + 1) * (depth x + width x + 1) + edgeMax Se (par x) (width x))
    (B := B)
    (fun x k _ => by
      obtain ⟨hB, htop⟩ := hbound x k
      have := Nat.mul_le_mul (Nat.add_le_add_right htop 1)
        (Nat.add_le_add_right (Nat.add_le_add_right htop (width x)) 1)
      simp only [hrun]
      omega)
    fun x k _ => by simp only [hrun]; exact (hbound x k).1
  refine ((snd' hiter).weaken (.of_le_linear 23 0 fun x => ?_)).of_enc_eq fun x => by rw [hrun]
  have hD := Nat.mul_le_mul (Nat.le_add_left 1 (depth x))
    (show width x + 1 ≤ depth x + width x + 1 by omega)
  rw [Nat.one_mul] at hD
  simp only [B]
  omega

end Cslib.Reachability.Walk

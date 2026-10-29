/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming
public import Mathlib.Tactic.FunProp
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OLoops

/-!
# Quantitative computability rules

`fun_prop (disch := lia)` composes degree certificates without replacing output-size bounds by
runtime bounds. Computation premises determine the intermediate encodings and degrees before the
arithmetic obligations compare the resulting degrees with the requested ones. The same `fun_prop`
interface recognizes ordinary finite-state bit folds with linear time and constant work space.
For nested projections with inferred degrees, `disch := first | apply le_refl | lia` first
instantiates a missing degree with the derived bound, then checks arithmetic inequalities.
Framed-list and option rules infer the payload encoding from the representation explicitly.

## Main results

* `Turing.MultiTapeTM.ComputableInO.comp_enc`: reuse a bit-word computation on encoded
  instances, with bounds evaluated on their encodings.
* `Turing.MultiTapeTM.ComputableInO.lengthUnary`: compute bit-word length in unary within
  linear time and space.
* `Turing.MultiTapeTM.ComputableInO.unary_two_pow`: compute `2 ^ n` from unary `n` within
  time `O((n + 1) * 2 ^ n)` and space `O(2 ^ n)`.
* `Turing.MultiTapeTM.ComputableTidilyInDegree.comp_le`: composition at requested degrees.
* `Turing.MultiTapeTM.ComputableTidilyInDegree.prod_le`: pairing at requested degrees, retaining
  the components' output-size bounds.
* `Turing.MultiTapeTM.ComputableTidilyInDegree.bitsReverse`,
  `Turing.MultiTapeTM.ComputableTidilyInDegree.bitsDropLast`,
  `Turing.MultiTapeTM.ComputableTidilyInDegree.bitsGetLast?ToList`,
  `Turing.MultiTapeTM.ComputableTidilyInDegree.bitsGetLast?`,
  `Turing.MultiTapeTM.ComputableTidilyInDegree.optionBoolToList`,
  `Turing.MultiTapeTM.ComputableTidilyInDegree.bitsAppend`,
  `Turing.MultiTapeTM.ComputableTidilyInDegree.unaryAdd`: degree rules for raw bit-list reversal,
  prefix, last-bit extraction, concatenation, and unary addition.

## References

Uses Christian Reitwiessner's degree calculus and streaming backend; see the source markers in
`Degree.lean` and `Complexity/Computability/Machines/Turing/MultiTape/Encodings/StreamFold.lean`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

universe u

attribute [fun_prop] ComputableTidilyInDegree ComputableTidilyInO
attribute [fun_prop] ComputableTidilyInTimeAndSpace
attribute [fun_prop] ComputableTidilyInDegree.const ComputableTidilyInDegree.fst
  ComputableTidilyInDegree.snd ComputableTidilyInDegree.comp ComputableTidilyInDegree.prod
  ComputableTidilyInDegree.fst' ComputableTidilyInDegree.snd'
  ComputableTidilyInDegree.cons ComputableTidilyInDegree.snoc
  ComputableTidilyInDegree.listAppend ComputableTidilyInDegree.isSome
  ComputableTidilyInDegree.unary_succ ComputableTidilyInDegree.unary_pred
  ComputableTidilyInDegree.unary_sub ComputableTidilyInDegree.unary_min
  ComputableTidilyInDegree.int_succ ComputableTidilyInDegree.int_pred
  ComputableTidilyInO.foldl_bits_finite ComputableTidilyInTimeAndSpace.map_bits
  ComputableTidilyInTimeAndSpace.reverse_bits ComputableTidilyInTimeAndSpace.dropLast_bits
  ComputableTidilyInTimeAndSpace.length_bits ComputableTidilyInTimeAndSpace.getLast?_toList_bits
  ComputableTidilyInTimeAndSpace.getLast?_bits

namespace ComputableTidilyInDegree

/-- The result encoding fixes the element encoding, without reversing `ListEncoding` inference. -/
@[fun_prop]
theorem listTail {α : Type*} (enc : α ↪ List Bool) :
    ComputableTidilyInDegree List.tail (encList enc) (encList enc) 1 1 :=
  tail (enc₁ := enc)

/-- The framed input list determines the encoding of its head, including a fixed fallback. -/
@[fun_prop]
theorem listHeadD {α : Type*} (enc : α ↪ List Bool) (fallback : α) :
    ComputableTidilyInDegree (fun l => l.headD fallback) (encList enc) enc 1 1 :=
  headD (enc₁ := enc) fallback

/-- Testing a framed list for emptiness. -/
@[fun_prop]
theorem listIsEmpty {α : Type*} (enc : α ↪ List Bool) :
    ComputableTidilyInDegree List.isEmpty (encList enc) encBool 1 1 :=
  isEmpty (enc₁ := enc)

/-- The option encoding determines the encoding used for the payload and fallback. -/
@[fun_prop]
theorem optionGetD {α : Type*} (enc : α ↪ List Bool) (fallback : α) :
    ComputableTidilyInDegree (fun o => o.getD fallback) (encOption enc) enc 1 1 :=
  getD (enc₁ := enc) fallback

/-- Copy an encoded value. This identity rule also lets `fun_prop` retain a shared let binding. -/
@[fun_prop]
theorem id' {α : Type*} {enc : α ↪ List Bool} :
    ComputableTidilyInDegree (fun x : α => x) enc enc 1 1 :=
  of_eq fun _ => rfl

/-- Reverse a raw bit list in linear time and linear output size. -/
@[fun_prop]
theorem bitsReverse :
    ComputableTidilyInDegree List.reverse encBits encBits 1 1 :=
  of_bounds ⟨2, fun _ => by simp; omega⟩ ⟨0, fun _ => by simp⟩
    ComputableTidilyInTimeAndSpace.reverse_bits

/-- Drop the last bit of a raw bit list in linear time and linear output size. -/
@[fun_prop]
theorem bitsDropLast :
    ComputableTidilyInDegree List.dropLast encBits encBits 1 1 :=
  of_bounds ⟨8, fun _ => by simp; omega⟩ ⟨0, fun _ => by simp⟩
    ComputableTidilyInTimeAndSpace.dropLast_bits

/-- Extract the last bit of a raw bit list as a 0-or-1-element list in linear time and constant
output size. -/
@[fun_prop]
theorem bitsGetLast?ToList :
    ComputableTidilyInDegree (fun l : List Bool => l.getLast?.toList) encBits encBits 1 0 :=
  ⟨⟨_, _, ⟨8, fun _ => by simp; omega⟩, ⟨0, fun _ => by simp⟩,
    ComputableTidilyInTimeAndSpace.getLast?_toList_bits⟩,
    ⟨1, fun l => by simp [Option.length_toList_le]⟩⟩

/-- Extract the last bit of a raw bit list as an `Option Bool` in linear time and constant output
size. -/
@[fun_prop]
theorem bitsGetLast? :
    ComputableTidilyInDegree (List.getLast? (α := Bool)) encBits (encOption encBool) 1 0 :=
  ⟨⟨_, _, ⟨8, fun _ => by simp; omega⟩, ⟨0, fun _ => by simp⟩,
    ComputableTidilyInTimeAndSpace.getLast?_bits⟩,
    ⟨2, fun l => by cases h : l.getLast? <;> simp [h]⟩⟩

/-- Convert an `Option Bool` to a 0-or-1-element bit list in linear time and linear output size. -/
@[fun_prop]
theorem optionBoolToList :
    ComputableTidilyInDegree (Option.toList (α := Bool)) (encOption encBool) encBits 1 1 :=
  of_linear (.of_tail fun o => by cases o <;> rfl)

/-- Concatenate two raw bit lists while preserving their time and output degrees independently. -/
@[fun_prop]
theorem bitsAppend {α : Type*} {encIn : α ↪ List Bool} {f g : α → List Bool}
    {df ef dg eg d e : ℕ}
    (hf : ComputableTidilyInDegree f encIn encBits df ef)
    (hg : ComputableTidilyInDegree g encIn encBits dg eg)
    (hd : max df dg ≤ d) (he : max ef eg ≤ e) :
    ComputableTidilyInDegree (fun x => f x ++ g x) encIn encBits d e :=
  (hf.append hg fun _ => rfl).mono hd he

/-- Add two unary natural numbers while preserving their time and output degrees independently. -/
@[fun_prop]
theorem unaryAdd {α : Type*} {encIn : α ↪ List Bool} {f g : α → ℕ}
    {df ef dg eg d e : ℕ}
    (hf : ComputableTidilyInDegree f encIn encUnary df ef)
    (hg : ComputableTidilyInDegree g encIn encUnary dg eg)
    (hd : max df dg ≤ d) (he : max ef eg ≤ e) :
    ComputableTidilyInDegree (fun x => f x + g x) encIn encUnary d e :=
  (hf.append hg fun _ => List.replicate_add _ _ true).mono hd he

/-- Compose using the intermediate output size. The computation premises determine the degrees
before arithmetic compares them with the requested bound. -/
@[fun_prop]
theorem comp_le {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {f : β → γ} {g : α → β} {df ef dg eg d e : ℕ}
    (hg : ComputableTidilyInDegree g encIn encMid dg eg)
    (hf : ComputableTidilyInDegree f encMid encOut df ef)
    (hd : max dg (eg * df) ≤ d) (he : eg * ef ≤ e) :
    ComputableTidilyInDegree (fun x => f (g x)) encIn encOut d e :=
  (hf.comp hg).mono hd he

/-- Pair two results while preserving their output degrees independently of computation time. -/
@[fun_prop]
theorem prod_le {α β γ : Type u} {encIn : α ↪ List Bool} {encF : β ↪ List Bool}
    {encG : γ ↪ List Bool} {f : α → β} {g : α → γ} {df ef dg eg d e : ℕ}
    (hf : ComputableTidilyInDegree f encIn encF df ef)
    (hg : ComputableTidilyInDegree g encIn encG dg eg)
    (hd : max df dg ≤ d) (he : max ef eg ≤ e) :
    ComputableTidilyInDegree (fun x => (f x, g x)) encIn (encPair encF encG) d e :=
  (hf.prod hg).mono hd he

/-- Branching on a computed Boolean, retaining each branch's output degree. -/
@[fun_prop]
theorem ite_le {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {condition : α → Bool} {f g : α → β} {dc ec df ef dg eg d e : ℕ}
    (hc : ComputableTidilyInDegree condition encIn encBool dc ec)
    (hf : ComputableTidilyInDegree f encIn encOut df ef)
    (hg : ComputableTidilyInDegree g encIn encOut dg eg)
    (hd : max dc (max df dg) ≤ d) (he : max ef eg ≤ e) :
    ComputableTidilyInDegree (fun x => if condition x then f x else g x) encIn encOut d e :=
  (hc.ite (hf.restrict _) (hg.restrict _)).mono hd he

end ComputableTidilyInDegree

namespace ComputableInO

variable {α β : Type} {encOut : β ↪ List Bool}

/-- A function of bit words computed within given bounds is computed by the same machine on encoded
instances. -/
theorem comp_enc {f : List Bool → β} {T S : List Bool → ℕ}
    (h : ComputableInO f encBits encOut T S) (enc : α ↪ List Bool) :
    ComputableInO (fun a => f (enc a)) enc encOut (fun a => T (enc a)) fun a => S (enc a) :=
  h.of_encIn_eq enc fun _ => rfl

/-- The length of a bit word in unary, within linear time and space, by the streaming machine of
`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.length_bits`. -/
theorem lengthUnary : ComputableInO (fun l : List Bool => l.length) encBits encUnary
    (fun l => l.length) fun l => l.length :=
  .of_bounds ComputableTidilyInTimeAndSpace.length_bits.computableInTimeAndSpace 8
    (fun l => by omega) (fun _ => Nat.zero_le _)
    fun l => by simp only [encUnary_apply, List.length_replicate]; omega

/-- Doubling `m` once for each element of a list of length `n` multiplies it by `2 ^ n`. -/
private theorem foldl_double (n m : ℕ) :
    (List.replicate n true).foldl (fun m _ => m + m) m = m * 2 ^ n := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons, ih]
    ring

/-- **`2 ^ n` in unary**, by doubling `n` times, within time `O((n + 1) * 2 ^ n)` and space
`O(2 ^ n)`. -/
theorem unary_two_pow : ComputableInO (fun n : ℕ => 2 ^ n) encUnary encUnary
    (fun n => (n + 1) * 2 ^ n) fun n => 2 ^ n := by
  have hstep : ComputableInO (fun p : ℕ × Bool => p.1 + p.1) (encPair encUnary encBool)
      encUnary (fun p => (encPair encUnary encBool p).length)
      fun p => (encPair encUnary encBool p).length :=
    (ComputableTidilyInDegree.unaryAdd (ComputableTidilyInDegree.fst encUnary encBool)
      (ComputableTidilyInDegree.fst encUnary encBool) le_rfl le_rfl).inO_one.computableInO
  have hstate (n i : ℕ) : (encUnary (((List.replicate n true).take i).foldl
      (fun m _ => m + m) 1)).length ≤ 2 ^ n := by
    rw [List.take_replicate, foldl_double, encUnary_apply, List.length_replicate, one_mul]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.min_le_right _ _)
  have h := foldl (encA := encBool) (encL := encBits) (encB := encUnary)
    (list := fun n : ℕ => List.replicate n true) (init := fun _ => 1)
    (step := fun m _ => m + m)
    (of_linear (.of_eq (f := fun n : ℕ => List.replicate n true) (encIn := encUnary)
      (encMid := encBits) fun _ => rfl)) (const 1) hstep
    (R := fun n => 2 * 2 ^ n + 2) (Q := fun n => 2 * 2 ^ n + 2) (B := fun n => 2 ^ n)
    (fun n i _ => by
      have := hstate n i
      simp only [length_encPair, encBool_apply, List.length_singleton]
      omega)
    (fun n i _ => by
      have := hstate n i
      simp only [length_encPair, encBool_apply, List.length_singleton]
      omega)
    fun n i _ => hstate n i
  refine (h.mono 8 (fun n => ?_) fun n => ?_).of_enc_eq fun n => ?_
  · have h₁ : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    have h₂ := Nat.mul_le_mul_left (n + 1) h₁
    simp only [encUnary_apply, encBits_apply, List.length_replicate]
    nlinarith
  · have h₁ : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    simp only [encUnary_apply, encBits_apply, List.length_replicate]
    omega
  · rw [foldl_double, one_mul]

end ComputableInO

end Turing.MultiTapeTM

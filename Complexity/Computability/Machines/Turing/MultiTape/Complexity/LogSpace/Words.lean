/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Append
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Ite
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm

/-!
# Word operations and pairing in logarithmic space

The word operations underlying the encodings of pairs, options and lists — framing, reading and
dropping the first frame, prepending `true`, dropping or keeping the first symbol, testing for
emptiness, mapping a Boolean function over a bit word, and folding a finite-state transition
function over an encoded word — are computed by finite-state transducers, without work tapes
(`Turing.MultiTapeTM.Transducer.computableInLogSpace`). They are therefore computable in
logarithmic space, as are the projections of pairs.

Concatenating or pairing two logspace functions of the same input runs both machines one after the
other; the work space is the sum of the two
(`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.append`). Case distinctions run the condition
test and then the selected branch (`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.ite`).
Together with word concatenation, these give logspace operations on options, lists, bit words, and
unary numbers, as well as bounded-count batch evaluation (`map_range_const`, `map_range_of_le`,
`mapToBits_range_const`, `mapToBits_range_of_le`).

## Main results

* `Turing.MultiTapeTM.ComputableInLogSpace.of_frame`, `.of_unframe`, `.of_dropFrame`,
  `.of_cons_true`, `.of_tail`, `.of_drop`, `.of_take_one`, `.of_isEmpty`, `.of_foldl_bool`:
  word operations.
* `Turing.MultiTapeTM.ComputableInLogSpace.restrict`, `.ite_subtype`, `.ite`, `.of_isEmpty_ite`:
  restriction and case distinctions.
* `Turing.MultiTapeTM.ComputableInLogSpace.append`,
  `Turing.MultiTapeTM.ComputableInLogSpace.fst`, `Turing.MultiTapeTM.ComputableInLogSpace.snd`,
  `Turing.MultiTapeTM.ComputableInLogSpace.pair`: concatenation and pairing.
* `Turing.MultiTapeTM.ComputableInLogSpace.optionSome`, `.optionGetD`: option operations.
* `Turing.MultiTapeTM.ComputableInLogSpace.listSingleton`, `.listCons`, `.listAppend`,
  `.listHeadD`, `.listLength`: framed-list operations.
* `Turing.MultiTapeTM.ComputableInLogSpace.bitsAppend`, `.bitsHeadD`, `.bitsMap`, `.bitsFoldl`,
  `.bitsAll`, `.bitsAny`: bit-word operations.
* `Turing.MultiTapeTM.ComputableInLogSpace.unaryAdd`, `.unaryMulConst`, `.unaryLeConst`,
  `.unaryBoundedMap`: unary-number operations.
* `Turing.MultiTapeTM.ComputableInLogSpace.map_range_const`, `.map_range_of_le`,
  `.mapToBits_range_const`, `.mapToBits_range_of_le`: bounded-count batch evaluation.
* `Turing.MultiTapeTM.ComputableInLogSpace.fst'`, `.snd'`, `.bool_and`, `.bool_or`,
  `.ite_decide`: projections of a computed pair, Boolean connectives and case distinctions on
  decidable propositions, in the form used by `fun_prop`, with which the closure rules and word
  operations above are registered.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.5][Sipser2013]
-/

public section

namespace Turing.MultiTapeTM.ComputableInLogSpace

open Encodings Internal.FrameMachines

variable {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}

/-- Framing an encoded value. -/
theorem of_frame (h : ∀ a, encOut (f a) = frame (encIn a)) :
    ComputableInLogSpace f encIn encOut :=
  frameT.computableInLogSpace fun a => by rw [h, frameT_run]

/-- Reading the word framed at the start of an encoded value. -/
theorem of_unframe (h : ∀ a, encOut (f a) = unframe (encIn a)) :
    ComputableInLogSpace f encIn encOut :=
  (readFrameT true).computableInLogSpace fun a => (h a).trans (readFrameT_run_true _).symm

/-- Dropping the frame at the start of an encoded value. -/
theorem of_dropFrame (h : ∀ a, encOut (f a) = dropFrame (encIn a)) :
    ComputableInLogSpace f encIn encOut :=
  (readFrameT false).computableInLogSpace fun a => (h a).trans (readFrameT_run_false _).symm

/-- Prepending `true` to an encoded value. -/
theorem of_cons_true (h : ∀ a, encOut (f a) = true :: encIn a) :
    ComputableInLogSpace f encIn encOut :=
  (headT none).computableInLogSpace fun a => by rw [h, headT_none_run]

/-- Dropping the first symbol of an encoded value. -/
theorem of_tail (h : ∀ a, encOut (f a) = (encIn a).tail) : ComputableInLogSpace f encIn encOut :=
  (headT (some false)).computableInLogSpace fun a => by rw [h, headT_some_false_run]

/-- Dropping the first `k` symbols of an encoded value. -/
theorem of_drop (k : ℕ) (h : ∀ a, encOut (f a) = (encIn a).drop k) :
    ComputableInLogSpace f encIn encOut := by
  induction k generalizing β encOut f with
  | zero => exact of_eq h
  | succ k ih =>
    exact ((of_tail (encIn := encBits) (encOut := encBits) (f := List.tail) fun _ => rfl).comp
      (ih (encOut := encBits) (f := fun a => (encIn a).drop k) fun _ => rfl)).congr
      fun a => by rw [h, ← List.tail_drop]; rfl

/-- Keeping just the first symbol of an encoded value. -/
theorem of_take_one (h : ∀ a, encOut (f a) = (encIn a).take 1) :
    ComputableInLogSpace f encIn encOut :=
  (headT (some true)).computableInLogSpace fun a => by rw [h, headT_some_true_run]

/-- Testing an encoded value for emptiness. -/
theorem of_isEmpty {f : α → Bool} (h : ∀ a, f a = (encIn a).isEmpty) :
    ComputableInLogSpace f encIn encBool :=
  isEmptyT.computableInLogSpace fun a => by rw [h, isEmptyT_run]; rfl

/-- A function computable in logarithmic space on all inputs is computable in logarithmic space on
the inputs satisfying `p`, by the same machine. -/
theorem restrict (h : ComputableInLogSpace f encIn encOut) (p : α → Prop) :
    ComputableInLogSpace (f ∘ Subtype.val) ((Function.Embedding.subtype p).trans encIn) encOut :=
  let ⟨t, c, k, S, hS, tm, htm⟩ := h
  ⟨t ∘ Subtype.val, c, k, S, hS, tm, fun x => htm x⟩

/-- Case distinctions in logarithmic space, with each branch certified on the inputs where it is
taken. -/
theorem ite_subtype {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    (hc : ComputableInLogSpace c encIn encC)
    (hf : ComputableInLogSpace (f ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = true)).trans encIn) encOut)
    (hg : ComputableInLogSpace (g ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = false)).trans encIn) encOut) :
    ComputableInLogSpace (fun a => if c a then f a else g a) encIn encOut := by
  classical
  obtain ⟨tc, cc, hc⟩ := hc
  obtain ⟨tf, cf, hf⟩ := hf
  obtain ⟨tg, cg, hg⟩ := hg
  obtain ⟨dc, hc⟩ := hc.exists_computableTidilyInTimeAndSpace
  obtain ⟨df, hf⟩ := hf.exists_computableTidilyInTimeAndSpace
  obtain ⟨dg, hg⟩ := hg.exists_computableTidilyInTimeAndSpace
  let tf' (a : α) : ℕ :=
    if h : c a = true then
      2 * tf ⟨a, h⟩ + 3 * (cf * ((encIn a).length.log2 + 1)) + df
    else 0
  let sf' (a : α) : ℕ := df * (cf * ((encIn a).length.log2 + 1) + 1)
  let tg' (a : α) : ℕ :=
    if h : c a = false then
      2 * tg ⟨a, h⟩ + 3 * (cg * ((encIn a).length.log2 + 1)) + dg
    else 0
  let sg' (a : α) : ℕ := dg * (cg * ((encIn a).length.log2 + 1) + 1)
  have hf' : ComputableTidilyInTimeAndSpace (f ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = true)).trans encIn) encOut
      (tf' ∘ Subtype.val) (sf' ∘ Subtype.val) :=
    hf.mono (fun x => by simp [tf', x.2]) fun _ => le_rfl
  have hg' : ComputableTidilyInTimeAndSpace (g ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = false)).trans encIn) encOut
      (tg' ∘ Subtype.val) (sg' ∘ Subtype.val) :=
    hg.mono (fun x => by simp [tg', x.2]) fun _ => le_rfl
  obtain ⟨k, h⟩ := hc.ite hf' hg'
  refine ⟨_, dc * (cc + 1) + df * (cf + 1) + dg * (cg + 1) + k,
    h.computableInTimeAndSpace.mono (fun _ => le_rfl) fun a => ?_⟩
  simp only [sf', sg']
  generalize Nat.log2 (encIn a).length = l
  cases c a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    nlinarith [Nat.zero_le l, Nat.zero_le (dc * cc * l), Nat.zero_le (df * cf * l),
      Nat.zero_le (dg * cg * l)]

/-- **Case distinction**: if `c`, `f` and `g` are computable in logarithmic space on a common
input, so is `fun a => if c a then f a else g a`. -/
theorem ite {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    (hc : ComputableInLogSpace c encIn encC) (hf : ComputableInLogSpace f encIn encOut)
    (hg : ComputableInLogSpace g encIn encOut) :
    ComputableInLogSpace (fun a => if c a then f a else g a) encIn encOut :=
  ite_subtype hc (hf.restrict _) (hg.restrict _)

/-- A function with a fixed value `d` on the input encoded by the empty word, and computable in
logarithmic space on the other inputs. -/
theorem of_isEmpty_ite (d : β) (hd : ∀ a, encIn a = [] → f a = d)
    (h : ComputableInLogSpace (f ∘ Subtype.val)
      ((Function.Embedding.subtype fun a => (encIn a).isEmpty = false).trans encIn) encOut) :
    ComputableInLogSpace f encIn encOut := by
  convert ite_subtype (c := fun a => (encIn a).isEmpty) (of_isEmpty fun _ => rfl)
    ((const d).restrict _) h using 1
  funext a
  split_ifs with ha <;> simp_all

variable {β₁ β₂ : Type} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}

/-- **Word concatenation**: if `f₁` and `f₂` are computable in logarithmic space on a common input
and `encOut (g a) = enc₁ (f₁ a) ++ enc₂ (f₂ a)` for all `a`, then `g` is computable in logarithmic
space. -/
theorem append {f₁ : α → β₁} {f₂ : α → β₂} {g : α → β}
    (h₁ : ComputableInLogSpace f₁ encIn enc₁) (h₂ : ComputableInLogSpace f₂ encIn enc₂)
    (hg : ∀ a, encOut (g a) = enc₁ (f₁ a) ++ enc₂ (f₂ a)) :
    ComputableInLogSpace g encIn encOut := by
  obtain ⟨t₁, c₁, h₁⟩ := h₁
  obtain ⟨t₂, c₂, h₂⟩ := h₂
  obtain ⟨d₁, h₁⟩ := h₁.exists_computableTidilyInTimeAndSpace
  obtain ⟨d₂, h₂⟩ := h₂.exists_computableTidilyInTimeAndSpace
  obtain ⟨k, h⟩ := h₁.append h₂ hg
  refine ⟨_, d₁ * (c₁ + 1) + d₂ * (c₂ + 1) + k, h.computableInTimeAndSpace.mono
    (fun _ => le_rfl) fun a => ?_⟩
  generalize Nat.log2 (encIn a).length = l
  nlinarith [Nat.zero_le l, Nat.zero_le (d₁ * c₁ * l), Nat.zero_le (d₂ * c₂ * l)]

/-- The first component of a pair. -/
theorem fst (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInLogSpace Prod.fst (encPair enc₁ enc₂) enc₁ :=
  of_unframe fun p => by simp

/-- The second component of a pair. -/
theorem snd (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInLogSpace Prod.snd (encPair enc₁ enc₂) enc₂ :=
  of_dropFrame fun p => by simp

/-- **Pairing**: the values of two logspace functions of the same input, framed first value
followed by the second, are computed in logarithmic space. -/
theorem pair {f₁ : α → β₁} {f₂ : α → β₂} (h₁ : ComputableInLogSpace f₁ encIn enc₁)
    (h₂ : ComputableInLogSpace f₂ encIn enc₂) :
    ComputableInLogSpace (fun a => (f₁ a, f₂ a)) encIn (encPair enc₁ enc₂) :=
  append
    ((of_frame (encIn := enc₁) (encOut := encFramed enc₁) (f := fun b => b) fun _ => rfl).comp h₁)
    h₂ fun _ => rfl

/-! ### Options, framed lists, bit words, and unary numbers -/

/-- Wrapping a value in `some` in logarithmic space. -/
theorem optionSome :
    ComputableInLogSpace (some : β → Option β) encOut (encOption encOut) :=
  of_cons_true fun _ => rfl

/-- Unwrapping an option with a default value `d` in logarithmic space. -/
theorem optionGetD (d : β) :
    ComputableInLogSpace (fun o : Option β => o.getD d) (encOption encOut) encOut :=
  of_isEmpty_ite d (fun o ho => by cases o <;> simp_all)
    (of_tail fun ⟨o, ho⟩ => by cases o <;> simp at ho ⊢)

/-- Forming a singleton framed list in logarithmic space. -/
theorem listSingleton :
    ComputableInLogSpace (fun b : β => [b]) encOut (encList encOut) :=
  of_frame fun b => by simp [encList_cons, encList_nil]

/-- Prepending a computed element to a computed framed list in logarithmic space. -/
theorem listCons {f₁ : α → β} {f₂ : α → List β} (h₁ : ComputableInLogSpace f₁ encIn encOut)
    (h₂ : ComputableInLogSpace f₂ encIn (encList encOut)) :
    ComputableInLogSpace (fun a => f₁ a :: f₂ a) encIn (encList encOut) :=
  append
    ((of_frame (encIn := encOut) (encOut := encFramed encOut) (f := fun b => b)
      fun _ => rfl).comp h₁)
    h₂ fun _ => rfl

/-- Concatenating two framed lists computed in logarithmic space from a common input. -/
theorem listAppend {f₁ f₂ : α → List β}
    (h₁ : ComputableInLogSpace f₁ encIn (encList encOut))
    (h₂ : ComputableInLogSpace f₂ encIn (encList encOut)) :
    ComputableInLogSpace (fun a => f₁ a ++ f₂ a) encIn (encList encOut) :=
  append h₁ h₂ fun a => by
    change (f₁ a ++ f₂ a).flatMap (frame ∘ encOut) =
      (f₁ a).flatMap (frame ∘ encOut) ++ (f₂ a).flatMap (frame ∘ encOut)
    exact List.flatMap_append

/-- Reading the head of a framed list with a default value `d` in logarithmic space. -/
theorem listHeadD (d : β) :
    ComputableInLogSpace (fun l : List β => l.headD d) (encList encOut) encOut :=
  of_isEmpty_ite d (fun l hl => by cases l <;> simp_all)
    (of_unframe fun ⟨l, hl⟩ => by cases l <;> simp at hl ⊢)

/-- The transducer counting the frames of a word in unary: in state `false` it reads a marker, and
emits `true` at an end marker; in state `true` it skips the bit after a `true` marker. -/
private def frameCountT : Transducer Bool Bool where
  q₀ := false
  step
    | false, true => (true, [])
    | false, false => (false, [true])
    | true, _ => (false, [])
  final _ := []
  length_step_le q a := by cases q <;> cases a <;> simp
  length_final_le _ := by simp

private theorem frameCountT_run_frame (w rest : List Bool) :
    frameCountT.run false (frame w ++ rest) = true :: frameCountT.run false rest := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [frame_cons, Transducer.run_cons, frameCountT] using ih

/-- The length of a framed list, in unary, in logarithmic space. -/
theorem listLength : ComputableInLogSpace (fun l : List β => l.length) (encList encOut) encUnary :=
  frameCountT.computableInLogSpace fun l => by
    induction l with
    | nil => rfl
    | cons b l ih =>
      change _ = frameCountT.run false _ at ih ⊢
      rw [encList_cons, frameCountT_run_frame, ← ih]
      simp [List.replicate_succ]

/-- Concatenating two bit words computed in logarithmic space from a common input. -/
theorem bitsAppend {f₁ f₂ : α → List Bool}
    (h₁ : ComputableInLogSpace f₁ encIn encBits)
    (h₂ : ComputableInLogSpace f₂ encIn encBits) :
    ComputableInLogSpace (fun a => f₁ a ++ f₂ a) encIn encBits :=
  append h₁ h₂ fun _ => rfl

/-- Reading the head of a bit word with a default value `d` in logarithmic space. -/
theorem bitsHeadD (d : Bool) :
    ComputableInLogSpace (fun l : List Bool => l.headD d) encBits encBool :=
  of_isEmpty_ite d (fun l hl => by simp_all)
    (of_take_one fun ⟨l, hl⟩ => by cases l; exacts [by simp at hl, rfl])

/-- A transducer that applies `g` to each bit of its input. -/
@[simps q₀ step final]
private def mapT (g : Bool → Bool) : Transducer Bool Unit where
  q₀ := ()
  step _ b := ((), [g b])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private lemma mapT_run (g : Bool → Bool) (v : List Bool) :
    (mapT g).run () v = v.map g := by
  induction v <;> simp [*]

/-- Mapping a Boolean function over a bit word is computable in logarithmic space. -/
theorem bitsMap (g : Bool → Bool) :
    ComputableInLogSpace (List.map g) encBits encBits :=
  (mapT g).computableInLogSpace fun v => (mapT_run g v).symm

/-- A transducer that folds `step` over its input from `q₀` and emits `final` of the final
state at the end of the input. -/
@[simps q₀ step final]
private def foldlT {Q : Type} (q₀ : Q) (step : Q → Bool → Q) (final : Q → List Bool)
    (hfinal : ∀ q, (final q).length ≤ 2) : Transducer Bool Q where
  q₀ := q₀
  step q b := (step q b, [])
  final := final
  length_step_le _ _ := by simp
  length_final_le := hfinal

private lemma foldlT_run {Q : Type} (q₀ : Q) (step : Q → Bool → Q) (final : Q → List Bool)
    (hfinal : ∀ q, (final q).length ≤ 2) (q : Q) (v : List Bool) :
    (foldlT q₀ step final hfinal).run q v = final (v.foldl step q) := by
  induction v generalizing q <;> simp [*]

/-- Folding a finite-state transition function over an encoded word and projecting the final state
to a Boolean is computable in logarithmic space. -/
theorem of_foldl_bool {Q : Type} [Finite Q] (q₀ : Q) (step : Q → Bool → Q) (out : Q → Bool)
    {f : α → Bool} (h : ∀ a, f a = out ((encIn a).foldl step q₀)) :
    ComputableInLogSpace f encIn encBool :=
  (foldlT q₀ step (fun q => encBool (out q))
    (fun q => by cases out q <;> decide)).computableInLogSpace
    fun a => by rw [h, foldlT_q₀, foldlT_run]

/-- Folding a binary Boolean operation over a bit word is computable in logarithmic space. -/
theorem bitsFoldl (op : Bool → Bool → Bool) (init : Bool) :
    ComputableInLogSpace (fun xs : List Bool => xs.foldl op init) encBits encBool :=
  of_foldl_bool init op _root_.id fun _ => rfl

private lemma foldl_and_eq_all (p : Bool → Bool) (acc : Bool) (xs : List Bool) :
    xs.foldl (fun a b => a && p b) acc = (acc && xs.all p) := by
  induction xs generalizing acc <;> simp [Bool.and_assoc, *]

private lemma foldl_or_eq_any (p : Bool → Bool) (acc : Bool) (xs : List Bool) :
    xs.foldl (fun a b => a || p b) acc = (acc || xs.any p) := by
  induction xs generalizing acc <;> simp [Bool.or_assoc, *]

/-- Testing whether all bits of a word satisfy `p` is computable in logarithmic space. -/
theorem bitsAll (p : Bool → Bool) :
    ComputableInLogSpace (fun xs : List Bool => xs.all p) encBits encBool :=
  of_foldl_bool true (fun a b => a && p b) _root_.id fun xs => by
    simpa using (foldl_and_eq_all p true xs).symm

/-- Testing whether any bit of a word satisfies `p` is computable in logarithmic space. -/
theorem bitsAny (p : Bool → Bool) :
    ComputableInLogSpace (fun xs : List Bool => xs.any p) encBits encBool :=
  of_foldl_bool false (fun a b => a || p b) _root_.id fun xs => by
    simpa using (foldl_or_eq_any p false xs).symm

/-- Adding two unary-encoded natural numbers computed in logarithmic space from a common input. -/
theorem unaryAdd {f₁ f₂ : α → ℕ}
    (h₁ : ComputableInLogSpace f₁ encIn encUnary)
    (h₂ : ComputableInLogSpace f₂ encIn encUnary) :
    ComputableInLogSpace (fun a => f₁ a + f₂ a) encIn encUnary :=
  append h₁ h₂ fun a => by
    change List.replicate (f₁ a + f₂ a) true =
      List.replicate (f₁ a) true ++ List.replicate (f₂ a) true
    exact List.replicate_add (f₁ a) (f₂ a) true

/-- Multiplying a unary-encoded natural number by a fixed constant `k` in logarithmic space. -/
theorem unaryMulConst {f : α → ℕ} (k : ℕ) (hf : ComputableInLogSpace f encIn encUnary) :
    ComputableInLogSpace (fun a => f a * k) encIn encUnary := by
  induction k with
  | zero => exact const 0
  | succ k ih => simpa [Nat.mul_succ] using unaryAdd ih hf

/-- Testing whether a unary-encoded natural number is at most a fixed constant `k`. -/
theorem unaryLeConst (k : ℕ) {r : α → ℕ} (hr : ComputableInLogSpace r encIn encUnary) :
    ComputableInLogSpace (fun a => decide (r a ≤ k)) encIn encBool := by
  refine ((of_isEmpty (encIn := encBits) (f := List.isEmpty) fun _ => rfl).comp
    ((of_drop k (encIn := encUnary) (encOut := encBits)
      (f := fun n => (encUnary n).drop k) fun _ => rfl).comp hr)).congr_fun fun a => ?_
  change decide (r a ≤ k) = ((List.replicate (r a) true).drop k).isEmpty
  simp [List.drop_replicate, Nat.sub_eq_zero_iff_le]

/-- Evaluating any function `g : ℕ → β` on a unary input clamped at a fixed constant `M` is
computable in logarithmic space. -/
theorem unaryBoundedMap (M : ℕ) (g : ℕ → β) :
    ComputableInLogSpace (fun n => g (min n M)) encUnary encOut := by
  induction M with
  | zero => exact (const (g 0)).congr_fun fun n => by simp
  | succ M ih =>
    refine (ite (unaryLeConst M .id) ih (const (g (M + 1)))).congr_fun fun n => ?_
    by_cases h : n ≤ M
    · simp [h, Nat.min_eq_left (Nat.le_succ_of_le h)]
    · have h' : M + 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_not_le h)
      simp [h, Nat.min_eq_right h']

/-! ### Bounded-count batch evaluation -/

/-- Evaluating a logspace family `f : α × ℕ → β` at the first `k` indices `0, …, k - 1`, for a
fixed constant `k`, is computable in logarithmic space. -/
theorem map_range_const (k : ℕ) {f : α × ℕ → β}
    (hf : ComputableInLogSpace f (encPair encIn encUnary) encOut) :
    ComputableInLogSpace (fun a => (List.range k).map fun i => f (a, i)) encIn
      (encList encOut) := by
  induction k with
  | zero => exact const []
  | succ k ih =>
    have hk : ComputableInLogSpace (fun a => [f (a, k)]) encIn (encList encOut) :=
      (listSingleton.comp hf).comp (pair .id (const k))
    refine (listAppend ih hk).congr_fun fun a => ?_
    simp [List.range_succ]

/-- Evaluating a logspace family `f : α × ℕ → β` at indices `0, …, r a - 1`, where `r : α → ℕ` is
computable in logarithmic space and bounded by a constant `k`, is computable in logarithmic
space. -/
theorem map_range_of_le (k : ℕ) {r : α → ℕ} {f : α × ℕ → β}
    (hr : ComputableInLogSpace r encIn encUnary) (hrk : ∀ a, r a ≤ k)
    (hf : ComputableInLogSpace f (encPair encIn encUnary) encOut) :
    ComputableInLogSpace (fun a => (List.range (r a)).map fun i => f (a, i)) encIn
      (encList encOut) := by
  induction k generalizing α encIn r f with
  | zero =>
    refine (const []).congr_fun fun a => ?_
    have : r a = 0 := Nat.le_zero.mp (hrk a)
    simp [this]
  | succ k ih =>
    have hle := unaryLeConst k hr
    have htrue : ComputableInLogSpace
        ((fun a => (List.range (r a)).map fun i => f (a, i)) ∘ Subtype.val)
        ((Function.Embedding.subtype (fun a => decide (r a ≤ k) = true)).trans encIn)
        (encList encOut) :=
      ih (hr.restrict _) (fun ⟨a, ha⟩ => of_decide_eq_true ha)
        (hf.comp (pair (fst _ _) (snd _ _)))
    have hfalse : ComputableInLogSpace
        ((fun a => (List.range (r a)).map fun i => f (a, i)) ∘ Subtype.val)
        ((Function.Embedding.subtype (fun a => decide (r a ≤ k) = false)).trans encIn)
        (encList encOut) := by
      refine ((map_range_const (k + 1) hf).restrict _).congr_fun fun ⟨a, ha⟩ => ?_
      have hgt : ¬ r a ≤ k := of_decide_eq_false ha
      have heq : r a = k + 1 := Nat.le_antisymm (hrk a) (Nat.not_le.mp hgt)
      simp [heq]
    refine (ite_subtype hle htrue hfalse).congr_fun fun a => ?_
    split_ifs <;> rfl

/-- Evaluating a logspace Boolean family `f : α × ℕ → Bool` at the first `k` indices
`0, …, k - 1`, for a fixed constant `k`, is computable in logarithmic space. -/
theorem mapToBits_range_const (k : ℕ) {f : α × ℕ → Bool}
    (hf : ComputableInLogSpace f (encPair encIn encUnary) encBool) :
    ComputableInLogSpace (fun a => (List.range k).map fun i => f (a, i)) encIn encBits := by
  induction k with
  | zero => exact const []
  | succ k ih =>
    have hk : ComputableInLogSpace (fun a => [f (a, k)]) encIn encBits :=
      ((of_finite (encIn := encBool) fun b : Bool => [b]).comp hf).comp (pair .id (const k))
    refine (bitsAppend ih hk).congr_fun fun a => ?_
    simp [List.range_succ]

/-- Evaluating a logspace Boolean family `f : α × ℕ → Bool` at indices `0, …, r a - 1`, where
`r : α → ℕ` is computable in logarithmic space and bounded by a constant `k`, is computable in
logarithmic space. -/
theorem mapToBits_range_of_le (k : ℕ) {r : α → ℕ} {f : α × ℕ → Bool}
    (hr : ComputableInLogSpace r encIn encUnary) (hrk : ∀ a, r a ≤ k)
    (hf : ComputableInLogSpace f (encPair encIn encUnary) encBool) :
    ComputableInLogSpace (fun a => (List.range (r a)).map fun i => f (a, i)) encIn encBits := by
  induction k generalizing α encIn r f with
  | zero =>
    refine (const []).congr_fun fun a => ?_
    have : r a = 0 := Nat.le_zero.mp (hrk a)
    simp [this]
  | succ k ih =>
    have hle := unaryLeConst k hr
    have htrue : ComputableInLogSpace
        ((fun a => (List.range (r a)).map fun i => f (a, i)) ∘ Subtype.val)
        ((Function.Embedding.subtype (fun a => decide (r a ≤ k) = true)).trans encIn)
        encBits :=
      ih (hr.restrict _) (fun ⟨a, ha⟩ => of_decide_eq_true ha)
        (hf.comp (pair (fst _ _) (snd _ _)))
    have hfalse : ComputableInLogSpace
        ((fun a => (List.range (r a)).map fun i => f (a, i)) ∘ Subtype.val)
        ((Function.Embedding.subtype (fun a => decide (r a ≤ k) = false)).trans encIn)
        encBits := by
      refine ((mapToBits_range_const (k + 1) hf).restrict _).congr_fun fun ⟨a, ha⟩ => ?_
      have hgt : ¬ r a ≤ k := of_decide_eq_false ha
      have heq : r a = k + 1 := Nat.le_antisymm (hrk a) (Nat.not_le.mp hgt)
      simp [heq]
    refine (ite_subtype hle htrue hfalse).congr_fun fun a => ?_
    split_ifs <;> rfl

/-! ### Automation

The closure rules for pairing, projections and case distinctions, and the word operations, are
registered with `fun_prop`. Projections are stated for a computed pair, so the pair certificate
fixes the encodings of the components. -/

/-- The first component of a computed pair, in the form used by `fun_prop`. -/
@[fun_prop]
theorem fst' {f : α → β₁ × β₂} (hf : ComputableInLogSpace f encIn (encPair enc₁ enc₂)) :
    ComputableInLogSpace (fun a => (f a).1) encIn enc₁ :=
  (fst enc₁ enc₂).comp hf

/-- The second component of a computed pair, in the form used by `fun_prop`. -/
@[fun_prop]
theorem snd' {f : α → β₁ × β₂} (hf : ComputableInLogSpace f encIn (encPair enc₁ enc₂)) :
    ComputableInLogSpace (fun a => (f a).2) encIn enc₂ :=
  (snd enc₁ enc₂).comp hf

/-- The conjunction of two computed Booleans. -/
@[fun_prop]
theorem bool_and {c₁ c₂ : α → Bool} (h₁ : ComputableInLogSpace c₁ encIn encBool)
    (h₂ : ComputableInLogSpace c₂ encIn encBool) :
    ComputableInLogSpace (fun a => c₁ a && c₂ a) encIn encBool :=
  (of_finite (encIn := encPair encBool encBool) fun p : Bool × Bool => p.1 && p.2).comp'
    (pair h₁ h₂)

/-- The disjunction of two computed Booleans. -/
@[fun_prop]
theorem bool_or {c₁ c₂ : α → Bool} (h₁ : ComputableInLogSpace c₁ encIn encBool)
    (h₂ : ComputableInLogSpace c₂ encIn encBool) :
    ComputableInLogSpace (fun a => c₁ a || c₂ a) encIn encBool :=
  (of_finite (encIn := encPair encBool encBool) fun p : Bool × Bool => p.1 || p.2).comp'
    (pair h₁ h₂)

/-- A case distinction on a decidable proposition whose truth value is computed. -/
@[fun_prop]
theorem ite_decide {encC : Bool ↪ List Bool} {p : α → Prop} {_ : DecidablePred p} {f g : α → β}
    (hp : ComputableInLogSpace (fun a => decide (p a)) encIn encC)
    (hf : ComputableInLogSpace f encIn encOut) (hg : ComputableInLogSpace g encIn encOut) :
    ComputableInLogSpace (fun a => if p a then f a else g a) encIn encOut :=
  (ite hp hf hg).congr_fun fun a => by by_cases h : p a <;> simp [h]

attribute [fun_prop] pair ite optionSome optionGetD listSingleton listCons listAppend listHeadD
  listLength
  bitsAppend bitsHeadD bitsMap bitsFoldl bitsAll bitsAny unaryAdd unaryMulConst unaryLeConst

end Turing.MultiTapeTM.ComputableInLogSpace

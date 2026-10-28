/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Native
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.IterateWhile
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum

/-!
# Compositional combinators for native resource certificates

These combinators assemble `NativeCertificate` witnesses for tuples, branches, retained-input
option elimination, sum tags, and clocked binary-counter iteration while tracking arbitrary
input-dependent time and space bounds. Linear postprocessing is absorbed into the producer's
bounds via its output-length guarantee; no polynomiality assumption or `ofPolyTime` selection is
used in the certificate constructors, while companion `*_isPolynomial` lemmas show that all
combinators preserve `NativeCertificate.IsPolynomial`.

## Main definitions

* `NativeCertificate.linear`, `.const`, `.prod`, `.post`: basic linear, literal, pair, and
  postprocessing combinators.
* `NativeCertificate.branch`, `.option`: selected-branch conditional and retained-input option
  elimination.
* `NativeCertificate.fst`, `.snd`, `.some`, `.inl`, `.inr`, `.congr`, `.pull`, `.payload`:
  projections, constructors, and retained-input helpers.
* `NativeCertificate.maxRoundTime`, `.maxRoundSpace`, `.maxStateLength`, `.iterate`: clocked
  binary-counter iteration with trajectory-maximum bounds.

## Main results

* `NativeCertificate.linear_isPolynomial`..`NativeCertificate.iterate_isPolynomial`: polynomiality
  preservation across all certificate combinators.

## References

Uses Christian Reitwiessner's native machine calculus and the parameterized option/sum resource
lemmas.
-/

@[expose] public section

namespace Cslib.GenericRAM.NativeCertificate

open Turing.MultiTapeTM

variable {α β γ δ : Type} {ei : α ↪ List Bool} {em : β ↪ List Bool}
  {eo : γ ↪ List Bool} {ed : δ ↪ List Bool} {f : α → β} {g : α → γ}

@[simp] theorem comp_time {g : β → γ} (d : NativeCertificate g em eo)
    (c : NativeCertificate f ei em) (a : α) :
    (d.comp c).time a = c.time a + d.time (f a) := rfl

@[simp] theorem comp_space {g : β → γ} (d : NativeCertificate g em eo)
    (c : NativeCertificate f ei em) (a : α) :
    (d.comp c).space a = c.space a + d.space (f a) := rfl

/-- Package a native linear-time/space implementation with its explicit input-length bound. -/
def linear (h : ComputableInO f ei em
    (fun a => (ei a).length) (fun a => (ei a).length)) : NativeCertificate f ei em :=
  ⟨fun a => (ei a).length, fun a => (ei a).length, h⟩

@[simp] theorem linear_time (h : ComputableInO f ei em
    (fun a => (ei a).length) (fun a => (ei a).length)) (a : α) :
    (linear h).time a = (ei a).length := rfl

@[simp] theorem linear_space (h : ComputableInO f ei em
    (fun a => (ei a).length) (fun a => (ei a).length)) (a : α) :
    (linear h).space a = (ei a).length := rfl

/-- A fixed literal, charged by the full input length. -/
def const (b : β) : NativeCertificate (fun _ : α => b) ei em :=
  linear (ComputableInO.const b)

@[simp] theorem const_time (b : β) (a : α) :
    (const (ei := ei) (em := em) b).time a = (ei a).length := rfl

@[simp] theorem const_space (b : β) (a : α) :
    (const (ei := ei) (em := em) b).space a = (ei a).length := rfl

/-- Construct a framed pair, adding the two producer bounds. -/
def prod (c : NativeCertificate f ei em) (d : NativeCertificate g ei eo) :
    NativeCertificate (fun a => (f a, g a)) ei (encPair em eo) :=
  ⟨fun a => c.time a + d.time a, fun a => c.space a + d.space a,
    c.computes.prod d.computes⟩

@[simp] theorem prod_time (c : NativeCertificate f ei em) (d : NativeCertificate g ei eo) (a : α) :
    (prod c d).time a = c.time a + d.time a := rfl

@[simp] theorem prod_space (c : NativeCertificate f ei em) (d : NativeCertificate g ei eo) (a : α) :
    (prod c d).space a = c.space a + d.space a := rfl

/-- Linear postprocessing is absorbed using the producer output-length guarantee. -/
def post {g : β → γ} (c : NativeCertificate f ei em)
    (h : ComputableInO g em eo
      (fun b => (em b).length) (fun b => (em b).length)) :
    NativeCertificate (g ∘ f) ei eo :=
  ⟨c.time, c.space, h.comp_linear c.computes⟩

@[simp] theorem post_time {g : β → γ} (c : NativeCertificate f ei em)
    (h : ComputableInO g em eo
      (fun b => (em b).length) (fun b => (em b).length)) :
    (post c h).time = c.time := rfl

@[simp] theorem post_space {g : β → γ} (c : NativeCertificate f ei em)
    (h : ComputableInO g em eo
      (fun b => (em b).length) (fun b => (em b).length)) :
    (post c h).space = c.space := rfl

/-- Charge the Boolean test and only the selected branch. -/
def branch {condition : α → Bool} {f g : α → β}
    (test : NativeCertificate condition ei encBool)
    (yes : NativeCertificate f ei em) (no : NativeCertificate g ei em) :
    NativeCertificate (fun a => if condition a then f a else g a) ei em :=
  ⟨fun a => test.time a + if condition a then yes.time a else no.time a,
    fun a => test.space a + if condition a then yes.space a else no.space a,
    test.computes.ite yes.computes no.computes⟩

@[simp] theorem branch_time {condition : α → Bool} {f g : α → β}
    (test : NativeCertificate condition ei encBool)
    (yes : NativeCertificate f ei em) (no : NativeCertificate g ei em) (a : α) :
    (branch test yes no).time a =
      test.time a + if condition a then yes.time a else no.time a := rfl

@[simp] theorem branch_space {condition : α → Bool} {f g : α → β}
    (test : NativeCertificate condition ei encBool)
    (yes : NativeCertificate f ei em) (no : NativeCertificate g ei em) (a : α) :
    (branch test yes no).space a =
      test.space a + if condition a then yes.space a else no.space a := rfl

/-- Retain the original input across option elimination; charge duplication and selected branch. -/
def option {value : α → Option β} {fallback : α → γ} {body : α × β → γ}
    (c : NativeCertificate value ei (encOption em))
    (no : NativeCertificate fallback ei eo)
    (yes : NativeCertificate body (encPair ei em) eo) :
    NativeCertificate (fun a => (value a).elim (fallback a) (fun b => body (a, b))) ei eo :=
  ⟨fun a => 2 * c.time a + (ei a).length +
      (value a).elim (no.time a) (fun b => yes.time (a, b)),
    fun a => 2 * c.space a + (ei a).length +
      (value a).elim (no.space a) (fun b => yes.space (a, b)),
    by
      rcases isEmpty_or_nonempty β with h | h
      · have hv : ∀ a, value a = none := by
          intro a
          cases value a with
          | none => rfl
          | some b => exact isEmptyElim b
        simpa only [hv, Option.elim_none] using no.computes.mono_le
          (T' := fun a => 2 * c.time a + (ei a).length + no.time a)
          (S' := fun a => 2 * c.space a + (ei a).length + no.space a)
          (fun _ => by omega) (fun _ => by omega)
      · obtain ⟨b⟩ := h
        have hget := (ComputableInDegree.getD (enc₁ := em) (enc := encOption em) b).inO_one
          |>.comp_linear c.computes
        have htag := (ComputableInDegree.isSome em).inO_one.comp_linear c.computes
        have hid : ComputableInO (fun a : α => a) ei ei
            (fun a => (ei a).length) (fun a => (ei a).length) := .of_eq fun _ => rfl
        have h := htag.ite (yes.computes.comp (hid.prod hget)) no.computes
        have h' := h.mono_le
          (T' := fun a => 2 * c.time a + (ei a).length +
            (value a).elim (no.time a) (fun b => yes.time (a, b)))
          (S' := fun a => 2 * c.space a + (ei a).length +
            (value a).elim (no.space a) (fun b => yes.space (a, b)))
          (fun a => by
            cases hv : value a <;>
              simp only [Function.comp_def, hv, Option.isSome_none, Option.isSome_some,
                Option.getD_some, Option.elim_none, Option.elim_some, Bool.false_eq_true,
                ite_false, ite_true] <;> omega)
          (fun a => by
            cases hv : value a <;>
              simp only [Function.comp_def, hv, Option.isSome_none, Option.isSome_some,
                Option.getD_some, Option.elim_none, Option.elim_some, Bool.false_eq_true,
                ite_false, ite_true] <;> omega)
        convert h' using 1
        funext a
        change (value a).elim (fallback a) (fun b => body (a, b)) =
          if (value a).isSome then body (a, (value a).getD b) else fallback a
        cases value a <;> rfl⟩

@[simp] theorem option_time {value : α → Option β} {fallback : α → γ} {body : α × β → γ}
    (c : NativeCertificate value ei (encOption em))
    (no : NativeCertificate fallback ei eo)
    (yes : NativeCertificate body (encPair ei em) eo) (a : α) :
    (option c no yes).time a = 2 * c.time a + (ei a).length +
      (value a).elim (no.time a) (fun b => yes.time (a, b)) := rfl

@[simp] theorem option_space {value : α → Option β} {fallback : α → γ} {body : α × β → γ}
    (c : NativeCertificate value ei (encOption em))
    (no : NativeCertificate fallback ei eo)
    (yes : NativeCertificate body (encPair ei em) eo) (a : α) :
    (option c no yes).space a = 2 * c.space a + (ei a).length +
      (value a).elim (no.space a) (fun b => yes.space (a, b)) := rfl

/-- Project the first field, absorbing linear work in the producer bounds. -/
def fst {f : α → β × γ} (c : NativeCertificate f ei (encPair em eo)) :
    NativeCertificate (fun a => (f a).1) ei em :=
  post c (ComputableInO.fst em eo)

@[simp] theorem fst_time {f : α → β × γ} (c : NativeCertificate f ei (encPair em eo)) :
    (fst c).time = c.time := rfl

@[simp] theorem fst_space {f : α → β × γ} (c : NativeCertificate f ei (encPair em eo)) :
    (fst c).space = c.space := rfl

/-- Project the second field, absorbing linear work in the producer bounds. -/
def snd {f : α → β × γ} (c : NativeCertificate f ei (encPair em eo)) :
    NativeCertificate (fun a => (f a).2) ei eo :=
  post c (ComputableInO.snd em eo)

@[simp] theorem snd_time {f : α → β × γ} (c : NativeCertificate f ei (encPair em eo)) :
    (snd c).time = c.time := rfl

@[simp] theorem snd_space {f : α → β × γ} (c : NativeCertificate f ei (encPair em eo)) :
    (snd c).space = c.space := rfl

/-- Add an option tag, absorbing linear work in the producer bounds. -/
def some (c : NativeCertificate f ei em) :
    NativeCertificate (fun a => Option.some (f a)) ei (encOption em) :=
  post c ComputableInDegree.optionSome.inO_one

@[simp] theorem some_time (c : NativeCertificate f ei em) :
    (some c).time = c.time := rfl

@[simp] theorem some_space (c : NativeCertificate f ei em) :
    (some c).space = c.space := rfl

/-- Add a left sum tag, absorbing linear work in the producer bounds. -/
def inl (c : NativeCertificate f ei em) (right : γ ↪ List Bool) :
    NativeCertificate (fun a => Sum.inl (f a)) ei (encSum em right) :=
  post c (by
    have hid : ComputableInO (fun b : β => b) em em
        (fun b => (em b).length) (fun b => (em b).length) := .of_eq fun _ => rfl
    exact ((ComputableInO.const (encMid := encBool) false).append hid
      (fun _ => rfl)).mono 2 (fun _ => by omega) (fun _ => by omega))

@[simp] theorem inl_time (c : NativeCertificate f ei em) (right : γ ↪ List Bool) :
    (inl c right).time = c.time := rfl

@[simp] theorem inl_space (c : NativeCertificate f ei em) (right : γ ↪ List Bool) :
    (inl c right).space = c.space := rfl

/-- Add a right sum tag, absorbing linear work in the producer bounds. -/
def inr (left : γ ↪ List Bool) (c : NativeCertificate f ei em) :
    NativeCertificate (fun a => Sum.inr (f a)) ei (encSum left em) :=
  post c (by
    have hid : ComputableInO (fun b : β => b) em em
        (fun b => (em b).length) (fun b => (em b).length) := .of_eq fun _ => rfl
    exact ((ComputableInO.const (encMid := encBool) true).append hid
      (fun _ => rfl)).mono 2 (fun _ => by omega) (fun _ => by omega))

@[simp] theorem inr_time (left : γ ↪ List Bool) (c : NativeCertificate f ei em) :
    (inr left c).time = c.time := rfl

@[simp] theorem inr_space (left : γ ↪ List Bool) (c : NativeCertificate f ei em) :
    (inr left c).space = c.space := rfl

/-- Transport along pointwise equality without changing bounds. -/
def congr {g : α → β} (c : NativeCertificate f ei em) (h : ∀ a, f a = g a) :
    NativeCertificate g ei em :=
  ⟨c.time, c.space, c.computes.of_enc_eq (fun a => congrArg em (h a).symm)⟩

@[simp] theorem congr_time {g : α → β} (c : NativeCertificate f ei em) (h : ∀ a, f a = g a) :
    (congr c h).time = c.time := rfl

@[simp] theorem congr_space {g : α → β} (c : NativeCertificate f ei em) (h : ∀ a, f a = g a) :
    (congr c h).space = c.space := rfl

/-- Retain a producer on the first component of an extended input. -/
def pull (c : NativeCertificate f ei em) (other : δ ↪ List Bool) :
    NativeCertificate (fun a : α × δ => f a.1) (encPair ei other) em :=
  c.comp (linear (ComputableInO.fst ei other))

@[simp] theorem pull_time (c : NativeCertificate f ei em) (other : δ ↪ List Bool) (a : α × δ) :
    (pull c other).time a = (encPair ei other a).length + c.time a.1 := rfl

@[simp] theorem pull_space (c : NativeCertificate f ei em) (other : δ ↪ List Bool) (a : α × δ) :
    (pull c other).space a = (encPair ei other a).length + c.space a.1 := rfl

/-- Extract a retained-input continuation payload in linear time and space. -/
def payload (input : α ↪ List Bool) (out : β ↪ List Bool) :
    NativeCertificate (fun a : α × β => a.2) (encPair input out) out :=
  linear (ComputableInO.snd input out)

@[simp] theorem payload_time (input : α ↪ List Bool) (out : β ↪ List Bool) (a : α × β) :
    (payload input out).time a = (encPair input out a).length := rfl

@[simp] theorem payload_space (input : α ↪ List Bool) (out : β ↪ List Bool) (a : α × β) :
    (payload input out).space a = (encPair input out a).length := rfl

/-! ## Clocked iteration and polynomiality combinators for `NativeCertificate` -/

noncomputable section

variable {eb : β ↪ List Bool}

/-- Maximum single-round time along the first `m + 1` iterates from `b`. -/
def maxRoundTime {step : β → β} (cstep : NativeCertificate step eb eb) (m : ℕ) (b : β) : ℕ :=
  listMax (fun j => cstep.time (step^[j] b)) (List.range (m + 1))

/-- Maximum single-round space along the first `m + 1` iterates from `b`. -/
def maxRoundSpace {step : β → β} (cstep : NativeCertificate step eb eb) (m : ℕ) (b : β) : ℕ :=
  listMax (fun j => cstep.space (step^[j] b)) (List.range (m + 1))

/-- Maximum encoded state length along the first `m + 1` iterates from `b`. -/
def maxStateLength (eb : β ↪ List Bool) (step : β → β) (m : ℕ) (b : β) : ℕ :=
  listMax (fun j => (eb (step^[j] b)).length) (List.range (m + 1))

theorem le_maxRoundTime {step : β → β} (cstep : NativeCertificate step eb eb)
    {m j : ℕ} (hj : j ≤ m) (b : β) :
    cstep.time (step^[j] b) ≤ maxRoundTime cstep m b :=
  le_listMax (f := fun i => cstep.time (step^[i] b)) (List.mem_range.mpr (by omega))

theorem le_maxRoundSpace {step : β → β} (cstep : NativeCertificate step eb eb)
    {m j : ℕ} (hj : j ≤ m) (b : β) :
    cstep.space (step^[j] b) ≤ maxRoundSpace cstep m b :=
  le_listMax (f := fun i => cstep.space (step^[i] b)) (List.mem_range.mpr (by omega))

theorem le_maxStateLength (eb : β ↪ List Bool) (step : β → β)
    {m j : ℕ} (hj : j ≤ m) (b : β) :
    (eb (step^[j] b)).length ≤ maxStateLength eb step m b :=
  le_listMax (f := fun i => (eb (step^[i] b)).length) (List.mem_range.mpr (by omega))

theorem maxRoundTime_le {step : β → β} (cstep : NativeCertificate step eb eb)
    (m : ℕ) (b : β) {R : ℕ} (h : ∀ j ≤ m, cstep.time (step^[j] b) ≤ R) :
    maxRoundTime cstep m b ≤ R :=
  listMax_le fun j hj => h j (by have := List.mem_range.mp hj; omega)

theorem maxRoundSpace_le {step : β → β} (cstep : NativeCertificate step eb eb)
    (m : ℕ) (b : β) {Q : ℕ} (h : ∀ j ≤ m, cstep.space (step^[j] b) ≤ Q) :
    maxRoundSpace cstep m b ≤ Q :=
  listMax_le fun j hj => h j (by have := List.mem_range.mp hj; omega)

theorem maxStateLength_le (eb : β ↪ List Bool) (step : β → β)
    (m : ℕ) (b : β) {B : ℕ} (h : ∀ j ≤ m, (eb (step^[j] b)).length ≤ B) :
    maxStateLength eb step m b ≤ B :=
  listMax_le fun j hj => h j (by have := List.mem_range.mp hj; omega)

/-- Iterate `step` for `n a` rounds using a binary counter, charging the trajectory maxima over
`0 ≤ j ≤ n a` without requiring `[Inhabited β]` or pre-supplied polynomial bounds. -/
def iterate {n : α → ℕ} {init : α → β} {step : β → β}
    (cn : NativeCertificate n ei encNat)
    (cinit : NativeCertificate init ei eb)
    (cstep : NativeCertificate step eb eb) :
    NativeCertificate (fun a => step^[n a] (init a)) ei eb where
  time a := cn.time a + cinit.time a +
    (n a + 1) * (maxRoundTime cstep (n a) (init a) +
      maxStateLength eb step (n a) (init a) + ((encNat (n a)).length + 1) ^ 2)
  space a := cn.space a + cinit.space a +
    maxRoundSpace cstep (n a) (init a) +
    maxStateLength eb step (n a) (init a) + (encNat (n a)).length
  computes := by
    rcases isEmpty_or_nonempty β with h | ⟨⟨b₀⟩⟩
    · exact (cinit.computes.mono_le (fun _ => by omega)
        (fun _ => by omega)).of_enc_eq fun a => isEmptyElim (init a)
    · let : Inhabited β := ⟨b₀⟩
      exact ComputableInO.iterate cn.computes cinit.computes cstep.computes
        (fun a j hj => le_maxRoundTime cstep hj (init a))
        (fun a j hj => le_maxRoundSpace cstep hj (init a))
        (fun a j hj => le_maxStateLength eb step hj (init a))

@[simp] theorem iterate_time {n : α → ℕ} {init : α → β} {step : β → β}
    (cn : NativeCertificate n ei encNat)
    (cinit : NativeCertificate init ei eb)
    (cstep : NativeCertificate step eb eb) (a : α) :
    (iterate cn cinit cstep).time a = cn.time a + cinit.time a +
      (n a + 1) * (maxRoundTime cstep (n a) (init a) +
        maxStateLength eb step (n a) (init a) + ((encNat (n a)).length + 1) ^ 2) := rfl

@[simp] theorem iterate_space {n : α → ℕ} {init : α → β} {step : β → β}
    (cn : NativeCertificate n ei encNat)
    (cinit : NativeCertificate init ei eb)
    (cstep : NativeCertificate step eb eb) (a : α) :
    (iterate cn cinit cstep).space a = cn.space a + cinit.space a +
      maxRoundSpace cstep (n a) (init a) +
      maxStateLength eb step (n a) (init a) + (encNat (n a)).length := rfl

/-! ### Polynomiality preservation across certificate combinators -/

theorem polyBounded_pow_of_polyBounded {size u : α → ℕ} (hu : PolyBounded size u) (c d : ℕ) :
    PolyBounded size (fun a => c * (u a + 1) ^ d) :=
  (PolyBounded.of_forall_le (size := id) (u := fun x => c * (x + 1) ^ d)
    c d fun _ => le_rfl).comp hu

theorem linear_isPolynomial {f : α → β}
    (h : ComputableInO f ei eb (fun a => (ei a).length) (fun a => (ei a).length)) :
    (linear h).IsPolynomial :=
  ⟨.self, .self⟩

theorem const_isPolynomial (b : β) : (const (ei := ei) (em := eb) b).IsPolynomial :=
  ⟨.self, .self⟩

theorem prod_isPolynomial {f : α → β} {g : α → γ}
    (c : NativeCertificate f ei eb) (d : NativeCertificate g ei eo)
    (hc : c.IsPolynomial) (hd : d.IsPolynomial) :
    (prod c d).IsPolynomial :=
  ⟨hc.1.add hd.1, hc.2.add hd.2⟩

theorem post_isPolynomial {f : α → β} {g : β → γ}
    (c : NativeCertificate f ei eb)
    (h : ComputableInO g eb eo (fun b => (eb b).length) (fun b => (eb b).length))
    (hc : c.IsPolynomial) :
    (post c h).IsPolynomial := hc

theorem fst_isPolynomial {f : α → β × γ}
    (c : NativeCertificate f ei (encPair eb eo)) (hc : c.IsPolynomial) :
    (fst c).IsPolynomial := hc

theorem snd_isPolynomial {f : α → β × γ}
    (c : NativeCertificate f ei (encPair eb eo)) (hc : c.IsPolynomial) :
    (snd c).IsPolynomial := hc

theorem some_isPolynomial {f : α → β}
    (c : NativeCertificate f ei eb) (hc : c.IsPolynomial) :
    (some c).IsPolynomial := hc

theorem inl_isPolynomial {f : α → β}
    (c : NativeCertificate f ei eb) (right : γ ↪ List Bool) (hc : c.IsPolynomial) :
    (inl c right).IsPolynomial := hc

theorem inr_isPolynomial {f : α → β}
    (left : γ ↪ List Bool) (c : NativeCertificate f ei eb) (hc : c.IsPolynomial) :
    (inr left c).IsPolynomial := hc

theorem congr_isPolynomial {f g : α → β}
    (c : NativeCertificate f ei eb) (h : ∀ a, f a = g a) (hc : c.IsPolynomial) :
    (congr c h).IsPolynomial := hc

theorem pull_isPolynomial {f : α → β}
    (c : NativeCertificate f ei eb) (other : δ ↪ List Bool) (hc : c.IsPolynomial) :
    (pull c other).IsPolynomial :=
  comp_isPolynomial c (linear (ComputableInO.fst ei other)) hc ⟨.self, .self⟩

theorem payload_isPolynomial (input : α ↪ List Bool) (out : β ↪ List Bool) :
    (payload input out).IsPolynomial :=
  ⟨.self, .self⟩

theorem branch_isPolynomial {condition : α → Bool} {f g : α → β}
    (test : NativeCertificate condition ei encBool)
    (yes : NativeCertificate f ei eb) (no : NativeCertificate g ei eb)
    (ht : test.IsPolynomial) (hy : yes.IsPolynomial) (hn : no.IsPolynomial) :
    (branch test yes no).IsPolynomial := by
  refine ⟨(ht.1.add (hy.1.add hn.1)).mono fun a => ?_,
    (ht.2.add (hy.2.add hn.2)).mono fun a => ?_⟩ <;>
    (simp only [branch_time, branch_space]; split <;> omega)

theorem option_isPolynomial {value : α → Option β} {fallback : α → γ} {body : α × β → γ}
    (c : NativeCertificate value ei (encOption eb))
    (no : NativeCertificate fallback ei eo)
    (yes : NativeCertificate body (encPair ei eb) eo)
    (hc : c.IsPolynomial) (hno : no.IsPolynomial) (hyes : yes.IsPolynomial) :
    (option c no yes).IsPolynomial := by
  obtain ⟨ct, dt, hyt⟩ := hyes.1.exists_le
  obtain ⟨cs, ds, hys⟩ := hyes.2.exists_le
  have hlen : PolyBounded (fun a => (ei a).length)
      (fun a => 2 * (ei a).length + (encOption eb (value a)).length) :=
    ((PolyBounded.const 2).mul .self).add (c.polyTime hc).polyBounded_length
  have hbodyT : PolyBounded (fun a => (ei a).length)
      (fun a => ct * (2 * (ei a).length + (encOption eb (value a)).length + 1) ^ dt) :=
    polyBounded_pow_of_polyBounded hlen ct dt
  have hbodyS : PolyBounded (fun a => (ei a).length)
      (fun a => cs * (2 * (ei a).length + (encOption eb (value a)).length + 1) ^ ds) :=
    polyBounded_pow_of_polyBounded hlen cs ds
  refine ⟨((((PolyBounded.const 2).mul hc.1).add .self).add (hno.1.add hbodyT)).mono fun a => ?_,
    ((((PolyBounded.const 2).mul hc.2).add .self).add (hno.2.add hbodyS)).mono fun a => ?_⟩
  · simp only [option_time]
    cases hv : value a with
    | none => simp
    | some b =>
      have hb := hyt (a, b)
      have hpair : (encPair ei eb (a, b)).length =
          2 * (ei a).length + (encOption eb (Option.some b)).length := by
        simp; omega
      rw [hpair] at hb
      simp only [Option.elim_some]
      omega
  · simp only [option_space]
    cases hv : value a with
    | none => simp
    | some b =>
      have hb := hys (a, b)
      have hpair : (encPair ei eb (a, b)).length =
          2 * (ei a).length + (encOption eb (Option.some b)).length := by
        simp; omega
      rw [hpair] at hb
      simp only [Option.elim_some]
      omega

/-- Clocked iteration preserves polynomiality when the step count and reachable state lengths are
polynomially bounded in the encoded input length. -/
theorem iterate_isPolynomial {n : α → ℕ} {init : α → β} {step : β → β}
    (cn : NativeCertificate n ei encNat)
    (cinit : NativeCertificate init ei eb)
    (cstep : NativeCertificate step eb eb)
    (hcn : cn.IsPolynomial) (hcinit : cinit.IsPolynomial) (hcstep : cstep.IsPolynomial)
    (hn : PolyBounded (fun a => (ei a).length) n)
    {B : α → ℕ} (hB : PolyBounded (fun a => (ei a).length) B)
    (hstate : ∀ a, ∀ j ≤ n a, (eb (step^[j] (init a))).length ≤ B a) :
    (iterate cn cinit cstep).IsPolynomial := by
  obtain ⟨ct, dt, hst⟩ := hcstep.1.exists_le
  obtain ⟨cs, ds, hss⟩ := hcstep.2.exists_le
  have hlenN : PolyBounded (fun a => (ei a).length) (fun a => (encNat (n a)).length) :=
    (cn.polyTime hcn).polyBounded_length
  have hlenN2 : PolyBounded (fun a => (ei a).length)
      (fun a => 1 * ((encNat (n a)).length + 1) ^ 2) :=
    polyBounded_pow_of_polyBounded hlenN 1 2
  have hRT : PolyBounded (fun a => (ei a).length) (fun a => ct * (B a + 1) ^ dt) :=
    polyBounded_pow_of_polyBounded hB ct dt
  have hRS : PolyBounded (fun a => (ei a).length) (fun a => cs * (B a + 1) ^ ds) :=
    polyBounded_pow_of_polyBounded hB cs ds
  have hmaxB : ∀ a, maxStateLength eb step (n a) (init a) ≤ B a :=
    fun a => maxStateLength_le eb step (n a) (init a) (hstate a)
  have hmaxT : ∀ a, maxRoundTime cstep (n a) (init a) ≤ ct * (B a + 1) ^ dt :=
    fun a => maxRoundTime_le cstep (n a) (init a) fun j hj =>
      (hst _).trans (Nat.mul_le_mul_left ct
        (Nat.pow_le_pow_left (Nat.add_le_add_right (hstate a j hj) 1) dt))
  have hmaxS : ∀ a, maxRoundSpace cstep (n a) (init a) ≤ cs * (B a + 1) ^ ds :=
    fun a => maxRoundSpace_le cstep (n a) (init a) fun j hj =>
      (hss _).trans (Nat.mul_le_mul_left cs
        (Nat.pow_le_pow_left (Nat.add_le_add_right (hstate a j hj) 1) ds))
  refine ⟨((hcn.1.add hcinit.1).add
      ((hn.add (.const 1)).mul ((hRT.add hB).add hlenN2))).mono fun a => ?_,
    ((((hcn.2.add hcinit.2).add hRS).add hB).add hlenN).mono fun a => ?_⟩
  · simp only [iterate_time, one_mul]
    have h1 := hmaxT a
    have h2 := hmaxB a
    have h3 : maxRoundTime cstep (n a) (init a) + maxStateLength eb step (n a) (init a) +
        ((encNat (n a)).length + 1) ^ 2 ≤
        ct * (B a + 1) ^ dt + B a + ((encNat (n a)).length + 1) ^ 2 := by omega
    have h4 := Nat.mul_le_mul_left (n a + 1) h3
    omega
  · simp only [iterate_space]
    have h1 := hmaxS a
    have h2 := hmaxB a
    omega

end

end Cslib.GenericRAM.NativeCertificate
